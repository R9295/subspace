#![feature(variant_count)]
use core::mem;
use domain_runtime_primitives::BlockNumber as DomainBlockNumber;
use domain_runtime_primitives::opaque::Header as DomainHeader;
use frame_support::dispatch::{DispatchInfo, RawOrigin};
use frame_support::traits::fungible::InspectHold;
use frame_support::traits::{ConstU64, Currency, Hooks, VariantCount};
use frame_support::weights::constants::ParityDbWeight;
use frame_support::weights::{IdentityFee, Weight};
use frame_support::{PalletId, assert_ok, derive_impl, parameter_types};
use frame_system::mocking::MockUncheckedExtrinsic;
use frame_system::pallet_prelude::*;
use pallet_domains::block_tree::BlockTreeNode;
use pallet_domains::domain_registry::DomainConfigParams;
use pallet_domains::staking::{
    SharePrice, do_deregister_operator, do_mark_invalid_bundle_authors,
    do_mark_operators_as_slashed, do_nominate_operator, do_register_operator, do_reward_operators,
    do_unlock_funds, do_unlock_nominator, do_unmark_invalid_bundle_authors, do_withdraw_stake,
    mark_invalid_bundle_author, unmark_invalid_bundle_author,
};
use pallet_domains::staking_epoch::{do_finalize_domain_current_epoch, do_slash_operator};
use pallet_domains::{
    BalanceOf, BlockSlot, BlockTree, BlockTreeNodes, Config, DomainBlockNumberFor,
    DomainHashingFor, DomainStakingSummary, ExecutionReceiptOf, FungibleHoldId, HeadReceiptNumber,
    InvalidBundleAuthors, MAX_NOMINATORS_TO_SLASH, NominatorId, OperatorConfig, Operators,
    PendingSlashes, RawOrigin as DomainOrigin, SlashedReason, Withdrawals,
};
use pallet_subspace::NormalEraChange;
use parity_scale_codec::{Decode, Encode, MaxEncodedLen};
use scale_info::TypeInfo;
use sp_core::crypto::Pair;
use sp_core::{Get, H256};
use sp_domains::bundle::bundle_v0::{BundleHeaderV0, BundleV0, SealedBundleHeaderV0};
use sp_domains::bundle::{BundleVersion, InboxedBundle, OpaqueBundle};
use sp_domains::execution_receipt::execution_receipt_v0::ExecutionReceiptV0;
use sp_domains::execution_receipt::{ExecutionReceipt, ExecutionReceiptVersion};
use sp_domains::merkle_tree::MerkleTree;
use sp_domains::storage::RawGenesis;
use sp_domains::{
    BundleAndExecutionReceiptVersion, ChainId, DomainId, OperatorAllowList, OperatorId,
    OperatorPair, OperatorRewardSource, ProofOfElection, RuntimeType,
};
use sp_keystore::Keystore;
use sp_runtime::BuildStorage;
use sp_runtime::traits::{
    AccountIdConversion, BlockNumberProvider, ConstU16, Hash as HashT, IdentityLookup, One, Zero,
};
use sp_runtime::transaction_validity::TransactionValidityError;
use sp_version::{ApiId, RuntimeVersion, create_apis_vec};
use std::collections::{HashMap, HashSet};
use std::num::NonZeroU64;
use subspace_core_primitives::SlotNumber;
use subspace_core_primitives::pieces::Piece;
use subspace_core_primitives::segments::HistorySize;
use subspace_core_primitives::solutions::SolutionRange;
use subspace_runtime_primitives::{
    AI3, ConsensusEventSegmentSize, HoldIdentifier, Moment, StorageFee,
};

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct FuzzData {
    pub epochs: [Epoch; 10],
}

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct Epoch {
    /// 10 users = 10 actions
    actions: [FuzzAction; 10],
}

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
enum FuzzAction {
    RegisterOperator {
        amount: u16,
    },
    NominateOperator {
        operator_id: u8,
        amount: u16,
    },
    DeregisterOperator {
        operator_id: u64,
    },
    WithdrawStake {
        nominator_id: u8,
        operator_id: u8,
        shares: u16,
    },
    UnlockFunds {
        operator_id: u8,
        nominator_id: u8,
    },
    UnlockNominator {
        operator_id: u8,
        nominator_id: u8,
    },
    MarkOperatorsAsSlashed {
        operator_id: u8,
        slash_reason: u8, // 0 for InvalidBundle, 1 for BadExecutionReceipt
    },
    MarkInvalidBundleAuthors {
        operator_id: u8,
    },
    UnmarkInvalidBundleAuthors {
        operator_id: u8,
        er_id: u8,
    },
    Finalize,
    RewardOperator {
        operator_id: u8,
        amount: u16,
    },
    SlashOperator {
        operator_id: u8,
        slash_reason: u8,
    },
}

fn check_operator_state_consistency_invariant(operators: Vec<&OperatorId>) {
    for operator_id in operators {
        if let Some(operator) = Operators::<Test>::get(*operator_id) {
            // Check that minimum nominator stake is reasonable
            assert!(
                operator.current_total_stake > 0u128,
                "Operator {operator_id} has negative total_stake: {}",
                operator.current_total_stake
            );

            assert!(
                operator.current_total_shares > 0u128,
                "Operator {operator_id} has negative total_shares: {}",
                operator.current_total_shares
            );
        }
    }
}

fn check_share_price_invariant(
    operators: &[OperatorId],
    previous_share_prices: &mut HashMap<u64, SharePrice>,
    slashed_operators: &mut HashMap<u64, bool>,
) {
    for operator_id in operators {
        let operator_id = *operator_id as u64;
        if let Some(operator) = Operators::<Test>::get(operator_id) {
            // Calculate current share price
            let new_share_price = SharePrice::new::<Test>(
                operator.current_total_shares,
                operator.current_total_stake,
            )
            .unwrap();
        }
    }
}

fn check_slashing_invariant(operators: &[OperatorId], slashed_operators: &mut HashMap<u64, bool>) {
    for operator_id in operators {
        if let Some(operator) = Operators::<Test>::get(*operator_id) {
            let current_status = operator.status::<Test>(*operator_id);

            // Check if operator is currently slashed
            let is_currently_slashed = matches!(
                current_status,
                pallet_domains::staking::OperatorStatus::Slashed
            );

            // Update slashed operators tracking
            if is_currently_slashed {
                slashed_operators.insert(*operator_id, true);
            }

            // Invariant: Once slashed, an operator should remain slashed until deregistration
            if let Some(&was_slashed) = slashed_operators.get(&operator_id) {
                if was_slashed && !is_currently_slashed {
                    panic!(
                        "Invariant violation: Operator {} was previously slashed but is no longer slashed without deregistration",
                        operator_id
                    );
                }
            }
        }
    }
}
fn create_genesis(accounts: Vec<AccountId>) {
    RuntimeGenesisConfig {
        balances: BalancesConfig {
            balances: accounts
                .iter()
                .cloned()
                .map(|x| (x, 200_000 * AI3))
                .collect(),
        },
        system: SystemConfig::default(),
        subspace: SubspaceConfig::default(),
        domains: DomainsConfig::default(),
    };
}

fn fuzz(data: &FuzzData) {
    let accounts: Vec<AccountId> = (0..10).map(|i| (i as u128)).collect();
    for account in &accounts {
        <Test as Config>::Currency::make_free_balance_be(account, (u16::MAX as u128) * 2 * AI3);
    }
    let domain_id = register_genesis_domain(1, 1);
    let mut operators = HashMap::new();
    let mut nominators = HashMap::new();

    // Initialize invariant tracking state
    let mut previous_share_prices: HashMap<u64, SharePrice> = HashMap::new();
    let mut slashed_operators: HashMap<u64, bool> = HashMap::new();
    let mut invalid_er = Vec::new();
    for epoch in &data.epochs {
        for (index, action) in epoch.actions.iter().enumerate() {
            let user = accounts.get(index).unwrap();
            match action {
                FuzzAction::RegisterOperator { amount } => {
                    let res = register_operator(*user, *amount as u128);
                    if let Some(operator) = res {
                        operators.insert(user, operator);
                        nominators
                            .entry(*user)
                            .and_modify(|list: &mut Vec<u64>| list.push(operator))
                            .or_insert(vec![operator]);
                    }
                    #[cfg(not(feature = "fuzzing"))]
                    println!("Registering {user:?} as Operator with amount {amount:?}\n-->{res:?}");
                }
                FuzzAction::NominateOperator {
                    operator_id,
                    amount,
                } => {
                    if operators.len() == 0 {
                        continue;
                    }
                    let amount = *amount as u128 * AI3;
                    let amount = amount.max(21 * AI3);
                    // TODO:
                    let operator = operators
                        .iter()
                        .collect::<Vec<_>>()
                        .get(*operator_id as usize % operators.len())
                        .unwrap()
                        .1;
                    let res = do_nominate_operator::<Test>(*operator, *user, amount);
                    if let Ok(_) = res {
                        nominators
                            .entry(*user)
                            .and_modify(|list: &mut Vec<u64>| list.push(*operator))
                            .or_insert(vec![*operator]);
                    }
                    #[cfg(not(feature = "fuzzing"))]
                    println!(
                        "Nominating as Nominator {user:?} for Operator {operator:?} with amount {amount:?}\n-->{res:?}"
                    );
                }
                FuzzAction::DeregisterOperator { operator_id } => {
                    if operators.len() == 0 {
                        continue;
                    }
                    // TODO:
                    let (owner, operator) = operators
                        .iter()
                        .collect::<Vec<_>>()
                        .get(*operator_id as usize % operators.len())
                        .unwrap()
                        .clone();
                    let res = do_deregister_operator::<Test>(**owner, *operator);
                    #[cfg(not(feature = "fuzzing"))]
                    println!("de-registering Operator {operator:?} \n-->{res:?}");
                }
                FuzzAction::WithdrawStake {
                    nominator_id,
                    operator_id,
                    shares,
                } => {
                    if operators.len() == 0 {
                        continue;
                    }
                    // TODO:
                    let (nominator, operators) = nominators
                        .iter()
                        .collect::<Vec<_>>()
                        .get(*nominator_id as usize % nominators.len())
                        .unwrap()
                        .clone();
                    let operator = operators
                        .get(*operator_id as usize % operators.len())
                        .unwrap();
                    // TODO: make sure shares are actually u128
                    let res =
                        do_withdraw_stake::<Test>(*operator, *nominator, *shares as u128 * AI3);
                    #[cfg(not(feature = "fuzzing"))]
                    println!(
                        "Withdrawing stake from Operator {operator:?}  as Nominator {nominator:?} of shares {shares:?}\n-->{res:?}"
                    );
                }
                FuzzAction::UnlockFunds {
                    operator_id,
                    nominator_id,
                } => {
                    if operators.len() == 0 {
                        continue;
                    }
                    let (nominator, operators) = nominators
                        .iter()
                        .collect::<Vec<_>>()
                        .get(*nominator_id as usize % nominators.len())
                        .unwrap()
                        .clone();
                    let operator = operators
                        .get(*operator_id as usize % operators.len())
                        .unwrap();
                    let res = do_unlock_funds::<Test>(*operator, *nominator);
                    #[cfg(not(feature = "fuzzing"))]
                    println!(
                        "Unlocking funds as Nominator {nominator:?} from Operator {operator:?} \n-->{res:?}"
                    );
                }
                FuzzAction::UnlockNominator {
                    operator_id,
                    nominator_id,
                } => {
                    if operators.len() == 0 {
                        continue;
                    }
                    let (nominator, operators) = nominators
                        .iter()
                        .collect::<Vec<_>>()
                        .get(*nominator_id as usize % nominators.len())
                        .unwrap()
                        .clone();
                    let operator = operators
                        .get(*operator_id as usize % operators.len())
                        .unwrap();
                    let res = do_unlock_nominator::<Test>(*operator, *nominator);
                    #[cfg(not(feature = "fuzzing"))]
                    println!(
                        "Unlocking funds as Nominator {nominator:?} from Operator {operator:?} \n-->{res:?}"
                    );
                }
                FuzzAction::MarkOperatorsAsSlashed {
                    operator_id,
                    slash_reason,
                } => {
                    if operators.len() == 0 {
                        continue;
                    }
                    let operator = operators
                        .iter()
                        .collect::<Vec<_>>()
                        .get(*operator_id as usize % operators.len())
                        .unwrap()
                        .1;
                    let slash_reason = match slash_reason % 2 {
                        0 => SlashedReason::InvalidBundle(0),
                        _ => SlashedReason::BadExecutionReceipt(H256::from([0u8; 32])),
                    };
                    let res = do_mark_operators_as_slashed::<Test>(vec![*operator], slash_reason);
                    #[cfg(not(feature = "fuzzing"))]
                    println!("Marking {operator_id:?} as slashed\n-->{res:?}");
                }
                FuzzAction::SlashOperator {
                    operator_id,
                    slash_reason,
                } => {
                    if operators.len() == 0 {
                        continue;
                    }
                    let operator = operators
                        .iter()
                        .collect::<Vec<_>>()
                        .get(*operator_id as usize % operators.len())
                        .unwrap()
                        .1;
                    let res = do_slash_operator::<Test>(DOMAIN_ID, u32::MAX);
                    #[cfg(not(feature = "fuzzing"))]
                    println!("Slashing-->{res:?}");
                }
                FuzzAction::RewardOperator {
                    operator_id,
                    amount,
                } => {
                    if operators.len() == 0 {
                        continue;
                    }
                    let operator = operators
                        .iter()
                        .collect::<Vec<_>>()
                        .get(*operator_id as usize % operators.len())
                        .unwrap()
                        .1;
                    let reward_amount = *amount as u128 * AI3;
                    let res = do_reward_operators::<Test>(
                        domain_id,
                        OperatorRewardSource::Dummy,
                        vec![*operator as u64].into_iter(),
                        reward_amount,
                    )
                    .unwrap();
                    #[cfg(not(feature = "fuzzing"))]
                    println!("Rewarding operator {operator:?} with {reward_amount:?}\n-->{res:?}");
                }
                FuzzAction::Finalize => {
                    let res = do_finalize_domain_current_epoch::<Test>(domain_id);
                    assert!(res.is_ok());
                    #[cfg(not(feature = "fuzzing"))]
                    println!("Finalizing");
                }
                FuzzAction::MarkInvalidBundleAuthors { operator_id } => {
                    if operators.len() == 0 {
                        continue;
                    }
                    let operator = operators
                        .iter()
                        .collect::<Vec<_>>()
                        .get(*operator_id as usize % operators.len())
                        .unwrap()
                        .1;
                    let pending_slashes =
                        PendingSlashes::<Test>::get(DOMAIN_ID).unwrap_or_default();
                    let mut invalid_bundle_authors_in_epoch =
                        InvalidBundleAuthors::<Test>::get(DOMAIN_ID);
                    let mut stake_summary = DomainStakingSummary::<Test>::get(DOMAIN_ID).unwrap();

                    for operator_id in vec![*operator] {
                        if pending_slashes.contains(&operator_id) {
                            continue;
                        }
                        let er = H256::random();
                        invalid_er.push(er);
                        mark_invalid_bundle_author::<Test>(
                            *operator,
                            er,
                            &mut stake_summary,
                            &mut invalid_bundle_authors_in_epoch,
                        );
                    }

                    DomainStakingSummary::<Test>::insert(DOMAIN_ID, stake_summary);
                    InvalidBundleAuthors::<Test>::insert(
                        DOMAIN_ID,
                        invalid_bundle_authors_in_epoch,
                    );
                }
                FuzzAction::UnmarkInvalidBundleAuthors { operator_id, er_id } => {
                    if operators.len() == 0 {
                        continue;
                    }
                    if invalid_er.len() == 0 {return;}
                    let operator = operators
                        .iter()
                        .collect::<Vec<_>>()
                        .get(*operator_id as usize % operators.len())
                        .unwrap()
                        .1;
                    let er = invalid_er.get(*er_id as usize % invalid_er.len()).unwrap();
                    let pending_slashes = PendingSlashes::<Test>::get(domain_id).unwrap_or_default();
                    let mut invalid_bundle_authors_in_epoch = InvalidBundleAuthors::<Test>::get(domain_id);
                    let mut stake_summary = DomainStakingSummary::<Test>::get(DOMAIN_ID).unwrap();

                    for operator_id in vec![*operator] {
                        if pending_slashes.contains(&operator_id)
                            || pallet_domains::Pallet::<Test>::is_operator_pending_to_slash(DOMAIN_ID, operator_id)
                        {
                            continue;
                        }

                        unmark_invalid_bundle_author::<Test>(
                            *operator,
                            *er,
                            &mut stake_summary,
                            &mut invalid_bundle_authors_in_epoch,
                        );
                    }

                    DomainStakingSummary::<Test>::insert(domain_id, stake_summary);
                    InvalidBundleAuthors::<Test>::insert(domain_id, invalid_bundle_authors_in_epoch);
                }
            }

            // Run all invariant checks after each action
            check_operator_state_consistency_invariant(operators.values().collect::<Vec<_>>());

            // Collect operator accounts for invariant checks
            let operator_accounts: Vec<OperatorId> =
                operators.values().cloned().collect::<Vec<_>>();

            // Check share price and slashing invariants
            check_share_price_invariant(
                &operator_accounts,
                &mut previous_share_prices,
                &mut slashed_operators,
            );
            check_slashing_invariant(&operator_accounts, &mut slashed_operators);
        }
        let res = do_finalize_domain_current_epoch::<Test>(domain_id);
        assert!(res.is_ok());
    }
}

fn register_operator(operator: AccountId, amount: Balance) -> Option<OperatorId> {
    let minimum_nominator_stake = 20 * AI3;
    let pair = OperatorPair::from_seed(&[operator as u8; 32]);
    let config = OperatorConfig {
        signing_key: pair.public(),
        minimum_nominator_stake,
        nomination_tax: sp_runtime::Percent::from_percent(60),
    };
    let res = do_register_operator::<Test>(operator, DOMAIN_ID, amount * AI3, config);
    #[cfg(not(feature = "fuzzing"))]
    println!("{res:?}");
    if let Ok((id, _)) = res {
        Some(id)
    } else {
        None
    }
}

fn main() {
    ziggy::fuzz!(|data: &[u8]| {
        let Ok(data) = bincode::deserialize::<FuzzData>(data) else {
            return;
        };
        let mut ext = new_test_ext_with_extensions();
        ext.execute_with(|| {
            fuzz(&data);
        });
    });
}
type UncheckedExtrinsic = frame_system::mocking::MockUncheckedExtrinsic<Test>;
type Block = frame_system::mocking::MockBlockU32<Test>;
type Balance = u128;

// TODO: Remove when DomainRegistry is usable.
const DOMAIN_ID: DomainId = DomainId::new(0);

// Operator id used for testing
const OPERATOR_ID: OperatorId = 0u64;

// Core Api version ID and default APIs
// RuntimeVersion's Decode is handwritten to accommodate Backward Compatibility for very old
// RuntimeVersion that do not have TransactionVersion or SystemVersion.
// So the Decode function always assume apis being present, at least CoreApi,
// to derive the correct TransactionVersion and SystemVersion.
// So we should always add the TEST_RUNTIME_APIS to the RuntimeVersion to ensure it is decoded correctly.
// More here - https://github.com/paritytech/polkadot-sdk/blob/master/substrate/primitives/version/src/lib.rs#L637
pub(crate) const CORE_API_ID: [u8; 8] = [223, 106, 203, 104, 153, 7, 96, 155];
pub(crate) const TEST_RUNTIME_APIS: [(ApiId, u32); 1] = [(CORE_API_ID, 5)];

frame_support::construct_runtime!(
    pub struct Test {
        System: frame_system,
        Timestamp: pallet_timestamp,
        Balances: pallet_balances,
        Subspace: pallet_subspace,
        Domains: pallet_domains,
        DomainExecutive: domain_pallet_executive,
        BlockFees: pallet_block_fees,
        MockVersionStore: pallet_mock_version_store,
    }
);

type BlockNumber = u32;
type Hash = H256;
pub(crate) type AccountId = u128;

#[derive_impl(frame_system::config_preludes::TestDefaultConfig)]
impl frame_system::Config for Test {
    type Block = Block;
    type Hash = Hash;
    type AccountId = AccountId;
    type Lookup = IdentityLookup<Self::AccountId>;
    type AccountData = pallet_balances::AccountData<Balance>;
    type DbWeight = ParityDbWeight;
    type EventSegmentSize = ConsensusEventSegmentSize;
}

parameter_types! {
    pub const MaximumReceiptDrift: BlockNumber = 128;
    pub const InitialDomainTxRange: u64 = 3;
    pub const DomainTxRangeAdjustmentInterval: u64 = 100;
    pub const MaxDomainBlockSize: u32 = 1024 * 1024;
    pub const MaxDomainBlockWeight: Weight = Weight::from_parts(1024 * 1024, 0);
    pub const DomainInstantiationDeposit: Balance = 100;
    pub const MaxDomainNameLength: u32 = 16;
    pub const BlockTreePruningDepth: u32 = 16;
    pub const SlotProbability: (u64, u64) = (1, 6);
}

pub struct ConfirmationDepthK;

impl Get<BlockNumber> for ConfirmationDepthK {
    fn get() -> BlockNumber {
        10
    }
}

#[derive(
    PartialEq, Eq, Clone, Encode, Decode, TypeInfo, MaxEncodedLen, Ord, PartialOrd, Copy, Debug,
)]
pub struct HoldIdentifierWrapper(HoldIdentifier);

impl pallet_domains::HoldIdentifier<Test> for HoldIdentifierWrapper {
    fn staking_staked() -> FungibleHoldId<Test> {
        Self(HoldIdentifier::DomainStaking)
    }

    fn domain_instantiation_id() -> FungibleHoldId<Test> {
        Self(HoldIdentifier::DomainInstantiation)
    }

    fn storage_fund_withdrawal() -> Self {
        Self(HoldIdentifier::DomainStorageFund)
    }
}

impl VariantCount for HoldIdentifierWrapper {
    const VARIANT_COUNT: u32 = mem::variant_count::<HoldIdentifier>() as u32;
}

parameter_types! {
    pub const ExistentialDeposit: Balance = 1;
}

#[derive_impl(pallet_balances::config_preludes::TestDefaultConfig as pallet_balances::DefaultConfig)]
impl pallet_balances::Config for Test {
    type Balance = Balance;
    type ExistentialDeposit = ExistentialDeposit;
    type AccountStore = System;
    type RuntimeHoldReason = HoldIdentifierWrapper;
    type DustRemoval = ();
}

parameter_types! {
    pub const MinOperatorStake: Balance = 100 * AI3;
    pub const MinNominatorStake: Balance = AI3;
    pub const StakeWithdrawalLockingPeriod: DomainBlockNumber = 5;
    pub const StakeEpochDuration: DomainBlockNumber = 1;
    pub TreasuryAccount: u128 = PalletId(*b"treasury").into_account_truncating();
    pub const BlockReward: Balance = 10 * AI3;
    pub const MaxPendingStakingOperation: u32 = 512;
    pub const DomainsPalletId: PalletId = PalletId(*b"domains_");
    pub const DomainChainByteFee: Balance = 1;
    pub const MaxInitialDomainAccounts: u32 = 5;
    pub const MinInitialDomainAccountBalance: Balance = AI3;
    pub const BundleLongevity: u32 = 5;
    pub const WithdrawalLimit: u32 = 10;
    pub const CurrentBundleAndExecutionReceiptVersion: BundleAndExecutionReceiptVersion = BundleAndExecutionReceiptVersion {
        bundle_version: BundleVersion::V0,
        execution_receipt_version: ExecutionReceiptVersion::V0,
    };
}

pub struct MockRandomness;

impl frame_support::traits::Randomness<Hash, BlockNumber> for MockRandomness {
    fn random(_: &[u8]) -> (Hash, BlockNumber) {
        (Default::default(), Default::default())
    }
}

const SLOT_DURATION: u64 = 1000;

impl pallet_timestamp::Config for Test {
    /// A timestamp: milliseconds since the unix epoch.
    type Moment = Moment;
    type OnTimestampSet = ();
    type MinimumPeriod = ConstU64<{ SLOT_DURATION / 2 }>;
    type WeightInfo = ();
}

pub struct DummyStorageFee;

impl StorageFee<Balance> for DummyStorageFee {
    fn transaction_byte_fee() -> Balance {
        AI3
    }
    fn note_storage_fees(_fee: Balance) {}
}

pub struct DummyBlockSlot;

impl BlockSlot<Test> for DummyBlockSlot {
    fn future_slot(_block_number: BlockNumberFor<Test>) -> Option<sp_consensus_slots::Slot> {
        None
    }

    fn slot_produced_after(_slot: sp_consensus_slots::Slot) -> Option<BlockNumberFor<Test>> {
        Some(0u32)
    }
}

pub struct MockDomainsTransfersTracker;

impl sp_domains::DomainsTransfersTracker<Balance> for MockDomainsTransfersTracker {
    type Error = ();

    fn initialize_domain_balance(
        _domain_id: DomainId,
        _amount: Balance,
    ) -> Result<(), Self::Error> {
        Ok(())
    }

    fn note_transfer(
        _from_chain_id: ChainId,
        _to_chain_id: ChainId,
        _amount: Balance,
    ) -> Result<(), Self::Error> {
        Ok(())
    }

    fn confirm_transfer(
        _from_chain_id: ChainId,
        _to_chain_id: ChainId,
        _amount: Balance,
    ) -> Result<(), Self::Error> {
        Ok(())
    }

    fn claim_rejected_transfer(
        _from_chain_id: ChainId,
        _to_chain_id: ChainId,
        _amount: Balance,
    ) -> Result<(), Self::Error> {
        Ok(())
    }

    fn reject_transfer(
        _from_chain_id: ChainId,
        _to_chain_id: ChainId,
        _amount: Balance,
    ) -> Result<(), Self::Error> {
        Ok(())
    }

    fn reduce_domain_balance(_domain_id: DomainId, _amount: Balance) -> Result<(), Self::Error> {
        Ok(())
    }
}

impl pallet_domains::Config for Test {
    type RuntimeEvent = RuntimeEvent;
    type DomainHash = sp_core::H256;
    type Balance = Balance;
    type DomainHeader = DomainHeader;
    type ConfirmationDepthK = ConfirmationDepthK;
    type Currency = Balances;
    type Share = Balance;
    type HoldIdentifier = HoldIdentifierWrapper;
    type BlockTreePruningDepth = BlockTreePruningDepth;
    type ConsensusSlotProbability = SlotProbability;
    type MaxDomainBlockSize = MaxDomainBlockSize;
    type MaxDomainBlockWeight = MaxDomainBlockWeight;
    type MaxDomainNameLength = MaxDomainNameLength;
    type DomainInstantiationDeposit = DomainInstantiationDeposit;
    type WeightInfo = pallet_domains::weights::SubstrateWeight<Test>;
    type InitialDomainTxRange = InitialDomainTxRange;
    type DomainTxRangeAdjustmentInterval = DomainTxRangeAdjustmentInterval;
    type MinOperatorStake = MinOperatorStake;
    type MinNominatorStake = MinNominatorStake;
    type StakeWithdrawalLockingPeriod = StakeWithdrawalLockingPeriod;
    type StakeEpochDuration = StakeEpochDuration;
    type TreasuryAccount = TreasuryAccount;
    type MaxPendingStakingOperation = MaxPendingStakingOperation;
    type Randomness = MockRandomness;
    type PalletId = DomainsPalletId;
    type StorageFee = DummyStorageFee;
    type BlockTimestamp = pallet_timestamp::Pallet<Test>;
    type BlockSlot = DummyBlockSlot;
    type DomainsTransfersTracker = MockDomainsTransfersTracker;
    type MaxInitialDomainAccounts = MaxInitialDomainAccounts;
    type MinInitialDomainAccountBalance = MinInitialDomainAccountBalance;
    type BundleLongevity = BundleLongevity;
    type DomainBundleSubmitted = ();
    type OnDomainInstantiated = ();
    type MmrHash = H256;
    type MmrProofVerifier = ();
    type FraudProofStorageKeyProvider = ();
    type OnChainRewards = ();
    type WithdrawalLimit = WithdrawalLimit;
    type DomainOrigin = pallet_domains::EnsureDomainOrigin;
    type CurrentBundleAndExecutionReceiptVersion = CurrentBundleAndExecutionReceiptVersion;
}

pub struct ExtrinsicStorageFees;

impl domain_pallet_executive::ExtrinsicStorageFees<Test> for ExtrinsicStorageFees {
    fn extract_signer(_xt: MockUncheckedExtrinsic<Test>) -> (Option<AccountId>, DispatchInfo) {
        (None, DispatchInfo::default())
    }

    fn on_storage_fees_charged(
        _charged_fees: Balance,
        _tx_size: u32,
    ) -> Result<(), TransactionValidityError> {
        Ok(())
    }
}

impl domain_pallet_executive::Config for Test {
    type RuntimeEvent = RuntimeEvent;
    type WeightInfo = ();
    type Currency = Balances;
    type LengthToFee = IdentityFee<Balance>;
    type ExtrinsicStorageFees = ExtrinsicStorageFees;
}

impl pallet_block_fees::Config for Test {
    type Balance = Balance;
    type DomainChainByteFee = DomainChainByteFee;
}

pub const INITIAL_SOLUTION_RANGE: SolutionRange =
    u64::MAX / (1024 * 1024 * 1024 / Piece::SIZE as u64) * 3 / 10;

parameter_types! {
    pub const BlockAuthoringDelay: SlotNumber = 2;
    pub const PotEntropyInjectionInterval: BlockNumber = 5;
    pub const PotEntropyInjectionLookbackDepth: u8 = 2;
    pub const PotEntropyInjectionDelay: SlotNumber = 4;
    pub const EraDuration: u32 = 4;
    // 1GB
    pub const InitialSolutionRange: SolutionRange = INITIAL_SOLUTION_RANGE;
    pub const RecentSegments: HistorySize = HistorySize::new(NonZeroU64::new(5).unwrap());
    pub const RecentHistoryFraction: (HistorySize, HistorySize) = (
        HistorySize::new(NonZeroU64::new(1).unwrap()),
        HistorySize::new(NonZeroU64::new(10).unwrap()),
    );
    pub const MinSectorLifetime: HistorySize = HistorySize::new(NonZeroU64::new(4).unwrap());
    pub const RecordSize: u32 = 3840;
    pub const ExpectedVotesPerBlock: u32 = 9;
    pub const ReplicationFactor: u16 = 1;
    pub const ReportLongevity: u64 = 34;
    pub const ShouldAdjustSolutionRange: bool = false;
    pub const BlockSlotCount: u32 = 6;
}

impl pallet_subspace::Config for Test {
    type RuntimeEvent = RuntimeEvent;
    type SubspaceOrigin = pallet_subspace::EnsureSubspaceOrigin;
    type BlockAuthoringDelay = BlockAuthoringDelay;
    type PotEntropyInjectionInterval = PotEntropyInjectionInterval;
    type PotEntropyInjectionLookbackDepth = PotEntropyInjectionLookbackDepth;
    type PotEntropyInjectionDelay = PotEntropyInjectionDelay;
    type EraDuration = EraDuration;
    type InitialSolutionRange = InitialSolutionRange;
    type SlotProbability = SlotProbability;
    type ConfirmationDepthK = ConfirmationDepthK;
    type RecentSegments = RecentSegments;
    type RecentHistoryFraction = RecentHistoryFraction;
    type MinSectorLifetime = MinSectorLifetime;
    type ExpectedVotesPerBlock = ExpectedVotesPerBlock;
    type MaxPiecesInSector = ConstU16<1>;
    type ShouldAdjustSolutionRange = ShouldAdjustSolutionRange;
    type EraChangeTrigger = NormalEraChange;
    type WeightInfo = ();
    type BlockSlotCount = BlockSlotCount;
    type ExtensionWeightInfo = pallet_subspace::extensions::weights::SubstrateWeight<Self>;
}

#[derive(Debug, Decode, Encode, TypeInfo, PartialEq, Eq, Clone, Copy)]
pub enum MockBundleVersion {
    V0,
    V1,
    V2,
    V3,
}

#[derive(Debug, Decode, Encode, TypeInfo, PartialEq, Eq, Clone, Copy)]
pub enum MockExecutionReceiptVersion {
    V0,
    V1,
    V2,
    V3,
}

#[derive(Debug, Decode, Encode, TypeInfo, PartialEq, Eq, Clone, Copy)]
pub struct MockBundleAndExecutionReceiptVersion {
    pub bundle_version: MockBundleVersion,
    pub execution_receipt_version: MockExecutionReceiptVersion,
}

#[frame_support::pallet]
pub(crate) mod pallet_mock_version_store {
    use super::{BlockNumberFor, MockBundleAndExecutionReceiptVersion};
    use frame_support::pallet_prelude::*;
    use std::collections::BTreeMap;

    #[pallet::config]
    pub trait Config: frame_system::Config {}

    /// Pallet domain-id to store self domain id.
    #[pallet::pallet]
    #[pallet::without_storage_info]
    pub struct Pallet<T>(_);

    #[pallet::storage]
    pub type MockPreviousBundleAndExecutionReceiptVersions<T: Config> = StorageValue<
        _,
        BTreeMap<BlockNumberFor<T>, MockBundleAndExecutionReceiptVersion>,
        ValueQuery,
    >;
}

impl pallet_mock_version_store::Config for Test {}

pub(crate) fn new_test_ext() -> sp_io::TestExternalities {
    let t = frame_system::GenesisConfig::<Test>::default()
        .build_storage()
        .unwrap();

    t.into()
}

pub(crate) fn new_test_ext_with_extensions() -> sp_io::TestExternalities {
    let version = RuntimeVersion {
        spec_name: "test".into(),
        impl_name: Default::default(),
        authoring_version: 0,
        spec_version: 1,
        impl_version: 1,
        apis: create_apis_vec!(TEST_RUNTIME_APIS),
        transaction_version: 1,
        system_version: 2,
    };

    let mut ext = new_test_ext();
    ext.register_extension(sp_core::traits::ReadRuntimeVersionExt::new(
        ReadRuntimeVersion(version.encode()),
    ));
    ext
}

pub(crate) fn create_dummy_receipt(
    block_number: BlockNumber,
    consensus_block_hash: Hash,
    parent_domain_block_receipt_hash: H256,
    block_extrinsics_roots: Vec<H256>,
) -> ExecutionReceipt<BlockNumber, Hash, DomainBlockNumber, H256, u128> {
    let (execution_trace, execution_trace_root) = if block_number == 0 {
        (Vec::new(), Default::default())
    } else {
        let execution_trace = vec![H256::random(), H256::random()];
        let trace: Vec<[u8; 32]> = execution_trace
            .iter()
            .map(|r| r.encode().try_into().expect("H256 must fit into [u8; 32]"))
            .collect();
        let execution_trace_root = MerkleTree::from_leaves(trace.as_slice())
            .root()
            .expect("Compute merkle root of trace should success")
            .into();
        (execution_trace, execution_trace_root)
    };
    let inboxed_bundles = block_extrinsics_roots
        .into_iter()
        .map(InboxedBundle::dummy)
        .collect();
    ExecutionReceipt::V0(ExecutionReceiptV0 {
        domain_block_number: block_number as DomainBlockNumber,
        domain_block_hash: H256::random(),
        domain_block_extrinsic_root: Default::default(),
        parent_domain_block_receipt_hash,
        consensus_block_number: block_number,
        consensus_block_hash,
        inboxed_bundles,
        final_state_root: *execution_trace.last().unwrap_or(&Default::default()),
        execution_trace,
        execution_trace_root,
        block_fees: Default::default(),
        transfers: Default::default(),
    })
}

fn create_dummy_bundle(
    domain_id: DomainId,
    block_number: BlockNumber,
    consensus_block_hash: Hash,
) -> OpaqueBundle<BlockNumber, Hash, DomainHeader, u128> {
    let execution_receipt = create_dummy_receipt(
        block_number,
        consensus_block_hash,
        Default::default(),
        vec![],
    );
    create_dummy_bundle_with_receipts(
        domain_id,
        OPERATOR_ID,
        Default::default(),
        execution_receipt,
    )
}

pub(crate) fn create_dummy_bundle_with_receipts(
    domain_id: DomainId,
    operator_id: OperatorId,
    bundle_extrinsics_root: H256,
    receipt: ExecutionReceipt<BlockNumber, Hash, DomainBlockNumber, H256, u128>,
) -> OpaqueBundle<BlockNumber, Hash, DomainHeader, u128> {
    let pair = OperatorPair::from_seed(&[0; 32]);

    let header = BundleHeaderV0::<_, _, DomainHeader, _> {
        proof_of_election: ProofOfElection::dummy(domain_id, operator_id),
        receipt,
        estimated_bundle_weight: Default::default(),
        bundle_extrinsics_root,
    };

    let signature = pair.sign(header.hash().as_ref());

    OpaqueBundle::V0(BundleV0 {
        sealed_header: SealedBundleHeaderV0::new(header, signature),
        extrinsics: Vec::new(),
    })
}

pub(crate) struct ReadRuntimeVersion(pub Vec<u8>);

impl sp_core::traits::ReadRuntimeVersion for ReadRuntimeVersion {
    fn read_runtime_version(
        &self,
        _wasm_code: &[u8],
        _ext: &mut dyn sp_externalities::Externalities,
    ) -> Result<Vec<u8>, String> {
        Ok(self.0.clone())
    }
}

pub(crate) fn run_to_block<T: Config>(block_number: BlockNumberFor<T>, parent_hash: T::Hash) {
    // Finalize the previous block
    // on_finalize() does not run on the genesis block
    if block_number > One::one() {
        pallet_domains::Pallet::<T>::on_finalize(block_number - One::one());
    }
    frame_system::Pallet::<T>::finalize();

    // Initialize current block
    frame_system::Pallet::<T>::set_block_number(block_number);
    frame_system::Pallet::<T>::initialize(&block_number, &parent_hash, &Default::default());
    // on_initialize() does not run on the genesis block
    if block_number > Zero::zero() {
        pallet_domains::Pallet::<T>::on_initialize(block_number);
    }
}

pub(crate) fn register_genesis_domain(creator: u128, operator_number: usize) -> DomainId {
    let raw_genesis_storage = RawGenesis::dummy(vec![1, 2, 3, 4]).encode();
    assert_ok!(
        pallet_domains::Pallet::<Test>::set_permissioned_action_allowed_by(
            RawOrigin::Root.into(),
            sp_domains::PermissionedActionAllowedBy::Anyone
        )
    );
    assert_ok!(pallet_domains::Pallet::<Test>::register_domain_runtime(
        RawOrigin::Root.into(),
        "evm".to_owned(),
        RuntimeType::Evm,
        raw_genesis_storage,
    ));

    pallet_domains::Pallet::<Test>::instantiate_domain(
        RawOrigin::Signed(creator).into(),
        DomainConfigParams {
            domain_name: "evm-domain".to_owned(),
            runtime_id: 0,
            maybe_bundle_limit: None,
            bundle_slot_probability: (1, 1),
            operator_allow_list: OperatorAllowList::Anyone,
            initial_balances: Default::default(),
            domain_runtime_config: Default::default(),
        },
    )
    .unwrap();
    do_finalize_domain_current_epoch::<Test>(DOMAIN_ID).unwrap();
    DOMAIN_ID
}

// Submit new head receipt to extend the block tree from the genesis block
pub(crate) fn extend_block_tree_from_zero(
    domain_id: DomainId,
    operator_id: u64,
    to: DomainBlockNumberFor<Test>,
) -> ExecutionReceiptOf<Test> {
    let genesis_receipt = get_block_tree_node_at::<Test>(domain_id, 0)
        .unwrap()
        .execution_receipt;
    extend_block_tree(domain_id, operator_id, to, genesis_receipt)
}

// Submit new head receipt to extend the block tree
pub(crate) fn extend_block_tree(
    domain_id: DomainId,
    operator_id: u64,
    to: DomainBlockNumberFor<Test>,
    mut latest_receipt: ExecutionReceiptOf<Test>,
) -> ExecutionReceiptOf<Test> {
    let current_block_number = frame_system::Pallet::<Test>::current_block_number();
    assert!(current_block_number < to);

    for block_number in (current_block_number + 1)..to {
        // Finilize parent block and initialize block at `block_number`
        run_to_block::<Test>(block_number, *latest_receipt.consensus_block_hash());

        // Submit a bundle with the receipt of the last block
        let bundle_extrinsics_root = H256::random();
        let bundle = create_dummy_bundle_with_receipts(
            domain_id,
            operator_id,
            bundle_extrinsics_root,
            latest_receipt,
        );
        assert_ok!(pallet_domains::Pallet::<Test>::submit_bundle(
            DomainOrigin::ValidatedUnsigned.into(),
            bundle,
        ));

        // Construct a `NewHead` receipt of the just submitted bundle, which will be included in the next bundle
        let head_receipt_number = HeadReceiptNumber::<Test>::get(domain_id);
        let parent_block_tree_node =
            get_block_tree_node_at::<Test>(domain_id, head_receipt_number).unwrap();
        latest_receipt = create_dummy_receipt(
            block_number,
            H256::random(),
            parent_block_tree_node
                .execution_receipt
                .hash::<DomainHashingFor<Test>>(),
            vec![bundle_extrinsics_root],
        );
    }

    // Finilize parent block and initialize block at `to`
    run_to_block::<Test>(to, *latest_receipt.consensus_block_hash());

    latest_receipt
}

#[allow(clippy::type_complexity)]
pub(crate) fn get_block_tree_node_at<T: Config>(
    domain_id: DomainId,
    block_number: DomainBlockNumberFor<T>,
) -> Option<
    BlockTreeNode<BlockNumberFor<T>, T::Hash, DomainBlockNumberFor<T>, T::DomainHash, BalanceOf<T>>,
> {
    BlockTree::<T>::get(domain_id, block_number).and_then(BlockTreeNodes::<T>::get)
}
