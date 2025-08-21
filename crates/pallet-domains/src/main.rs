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
    do_deregister_operator, do_mark_invalid_bundle_authors, do_mark_operators_as_slashed,
    do_nominate_operator, do_register_operator, do_reward_operators, do_unlock_funds,
    do_unlock_nominator, do_unmark_invalid_bundle_authors, do_withdraw_stake,
};
use pallet_domains::staking_epoch::{do_finalize_domain_current_epoch, do_slash_operator};
use pallet_domains::{
    BalanceOf, BlockSlot, BlockTree, BlockTreeNodes, Config, DomainBlockNumberFor,
    DomainHashingFor, ExecutionReceiptOf, FungibleHoldId, HeadReceiptNumber,
    MAX_NOMINATORS_TO_SLASH, NominatorId, OperatorConfig, Operators, PendingSlashes,
    RawOrigin as DomainOrigin, SlashedReason, Withdrawals,
};
use pallet_domains::staking::SharePrice;
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
use std::collections::HashMap;
use std::num::NonZeroU64;
use subspace_core_primitives::SlotNumber;
use subspace_core_primitives::pieces::Piece;
use subspace_core_primitives::segments::HistorySize;
use subspace_core_primitives::solutions::SolutionRange;
use subspace_runtime_primitives::{
    AI3, ConsensusEventSegmentSize, HoldIdentifier, Moment, StorageFee,
};

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
enum FuzzAction {
    NominateOperator {
        operator_id: u8,
        nominator_id: u128,
        amount: u8,
    },
    WithdrawStake {
        operator_id: u8,
        nominator_id: u128,
        shares: u8,
    },
    UnlockFunds {
        operator_id: u64,
        nominator_id: u8,
    },
    UnlockNominator {
        operator_id: u64,
        nominator_id: u8,
    },
    DeregisterOperator {
        operator_id: u64,
    },
    MarkOperatorsAsSlashed {
        operator_ids: u64,
        slash_reason: u8, // 0 for InvalidBundle, 1 for BadExecutionReceipt
    },
    MarkInvalidBundleAuthors {
        operator_ids: Vec<u8>,
    },
    UnmarkInvalidBundleAuthors {
        operator_ids: Vec<u8>,
    },
    Finalize,
    RewardOperator {
        operator_id: u8,
    },
    SlashOperator {
        operator_id: u8,
        slash_reason: u8,
    },
}

fn check_operator_state_consistency_invariant(operators: &[AccountId]) {
    for operator_id in operators {
        if let Some(operator) = Operators::<Test>::get(*operator_id as u64) {
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

fn check_total_supply_invariant(all_accounts: &[AccountId], operators: &[AccountId]) {
    let mut total_free_balance = 0u128;
    let mut total_held_balance = 0u128;
    let mut total_operator_stakes = 0u128;

    // Sum all account balances
    for account in all_accounts {
        total_free_balance += <Test as Config>::Currency::free_balance(account);
        total_held_balance += <Test as Config>::Currency::total_balance_on_hold(account);
    }

    // Sum all operator total stakes
    for operator_id in operators {
        if let Some(operator) = Operators::<Test>::get(*operator_id as u64) {
            total_operator_stakes += operator.current_total_stake;
        }
    }

    let total_system_balance = total_free_balance + total_held_balance;

    // Verify total system balance is reasonable (not zero unless test setup is broken)
    assert!(
        total_system_balance > 0u128,
        "Total system balance is zero - this indicates a broken test setup"
    );

    // Verify no individual component is negative
    assert!(
        total_free_balance >= 0u128,
        "Total free balance is negative: {total_free_balance}"
    );

    assert!(
        total_held_balance >= 0u128,
        "Total held balance is negative: {total_held_balance}"
    );

    assert!(
        total_operator_stakes >= 0u128,
        "Total operator stakes is negative: {total_operator_stakes}"
    );
}

fn check_treasury_balance_invariant(previous_treasury_balance: Balance) {
    let treasury_account = TreasuryAccount::get();
    let current_treasury_balance = <Test as Config>::Currency::total_balance(&treasury_account);

    assert!(
        current_treasury_balance >= previous_treasury_balance,
        "Treasury balance decreased from {previous_treasury_balance} to {current_treasury_balance}"
    );
}

fn check_share_price_invariant(
    operators: &[AccountId],
    previous_share_prices: &mut HashMap<u64, SharePrice>,
    slashed_operators: &mut HashMap<u64, bool>,
) {
    for operator_id in operators {
        let operator_id = *operator_id as u64;
        if let Some(operator) = Operators::<Test>::get(operator_id) {
            let new_share_price = 
                SharePrice::new::<Test>(operator.current_total_shares, operator.current_total_stake)
                    .unwrap_or_else(|_| SharePrice::one());

            if let Some(previous_share_price) = previous_share_prices.get(&operator_id) {
                if !slashed_operators.get(&operator_id).unwrap_or(&false) {
                    assert!(
                        new_share_price.0 >= previous_share_price.0,
                        "Share price for operator {operator_id} decreased without slashing"
                    );
                }
            }
            previous_share_prices.insert(operator_id, new_share_price);
        }
    }
}

fn check_slashing_invariant(operators: &[AccountId], slashed_operators: &mut HashMap<u64, bool>) {
    for operator_id in operators {
        let operator_id = *operator_id as u64;
        if let Some(operator) = Operators::<Test>::get(operator_id) {
            if let pallet_domains::staking::OperatorStatus::Slashed = operator.status::<Test>(operator_id) {
                slashed_operators.insert(operator_id, true);
            }
        }
    }
}

fn main() {
    ziggy::fuzz!(|data: &[u8]| {
        let Ok(actions) = bincode::deserialize::<Vec<FuzzAction>>(data) else {
            return;
        };
        let mut ext = new_test_ext_with_extensions();
        let operators: Vec<AccountId> = (0..5).map(|i| (i as u128)).collect();
        let nominators: Vec<AccountId> = (5..10).map(|i| (i as u128)).collect();
        ext.execute_with(|| {
            for nominator in &nominators {
                <Test as Config>::Currency::make_free_balance_be(nominator, 1000 * AI3);
            }
            for operator in &operators {
                <Test as Config>::Currency::make_free_balance_be(operator, 10000 * AI3);
            }
            let domain_id = register_genesis_domain(1, 1);
            for operator_owner in &operators {
                let minimum_nominator_stake = 10 * AI3 + 10_u128 * AI3;
                let pair = OperatorPair::from_seed(&[*operator_owner as u8; 32]);
                let config = OperatorConfig {
                    signing_key: pair.public(),
                    minimum_nominator_stake,
                    nomination_tax: sp_runtime::Percent::from_percent(60),
                };
                let res = 
                    do_register_operator::<Test>(*operator_owner, 0.into(), 200 * AI3, config);
                assert!(res.is_ok());
                #[cfg(not(feature = "fuzzing"))]
                println!("{res:?}");
            }
            #[cfg(not(feature = "fuzzing"))]
            println!("Done with operators");
            let res = do_finalize_domain_current_epoch::<Test>(domain_id);
            #[cfg(not(feature = "fuzzing"))]
            println!("Finalizing\n {res:?}");
            assert!(res.is_ok());
            
            // Capture initial treasury balance
            let treasury_account = TreasuryAccount::get();
            let mut previous_treasury_balance = <Test as Config>::Currency::total_balance(&treasury_account);
            let mut previous_share_prices: HashMap<u64, SharePrice> = HashMap::new();
            let mut slashed_operators: HashMap<u64, bool> = HashMap::new();
            
            for action in actions.into_iter() {
                match action {
                    FuzzAction::Finalize => {
                        let res = do_finalize_domain_current_epoch::<Test>(domain_id);
                        #[cfg(not(feature = "fuzzing"))]
                        println!("Finalizing\n {res:?}");
                        assert!(res.is_ok());
                    }
                    FuzzAction::NominateOperator {
                        operator_id,
                        nominator_id,
                        amount,
                    } => {
                        let amount = amount as u128 * AI3;
                        let nominator = nominators
                            .get(nominator_id as usize % nominators.len())
                            .unwrap();
                        let operator = operators
                            .get(operator_id as usize % operators.len())
                            .unwrap();

                        let _ = 
                            do_nominate_operator::<Test>(*operator as u64, *nominator, amount);
                        #[cfg(not(feature = "fuzzing"))]
                        println!("Nominating as Nominator {nominator:?} for Operator {operator:?} with amount {amount:?}\n-->{res:?}");
                    }
                    FuzzAction::WithdrawStake {
                        operator_id,
                        nominator_id,
                        shares,
                    } => {
                        let shares = shares as u128;
                        let nominator = nominators
                            .get(nominator_id as usize % nominators.len())
                            .unwrap();
                        let operator = operators
                            .get(operator_id as usize % operators.len())
                            .unwrap();
                        let _ = do_withdraw_stake::<Test>(*operator as u64, *nominator, shares);
                        #[cfg(not(feature = "fuzzing"))]
                        println!("Withdrawing stake from Operator {operator:?}  as Nominator {nominator:?} of shares {shares:?}\n-->{res:?}");
                    }
                    FuzzAction::RewardOperator { operator_id } => {
                        let operator = operators
                            .get(operator_id as usize % operators.len())
                            .unwrap();
                        let reward_amount = 100 * AI3;
                        let _ = do_reward_operators::<Test>(
                            domain_id,
                            OperatorRewardSource::Dummy,
                            vec![*operator as u64].into_iter(),
                            reward_amount,
                        )
                        .unwrap();
                        #[cfg(not(feature = "fuzzing"))]
                        println!("Rewarding operator {operator:?} with {reward_amount:?}\n-->{res:?}");
                    }
                    FuzzAction::SlashOperator { operator_id, slash_reason } => {
                        let operator = operators
                            .get(operator_id as usize % operators.len())
                            .unwrap();
                        let slash_reason = match slash_reason % 2 {
                            0 => SlashedReason::InvalidBundle(0),
                            _ => SlashedReason::BadExecutionReceipt(H256::from([0u8; 32])),
                        };
                        let _ = do_mark_operators_as_slashed::<Test>(&vec![*operator as u64], slash_reason);
                        #[cfg(not(feature = "fuzzing"))]
                        println!("Marking {operator:?} as slashed\n-->{res:?}");
                        let _ = do_slash_operator::<Test>(DOMAIN_ID, MAX_NOMINATORS_TO_SLASH);
                        #[cfg(not(feature = "fuzzing"))]
                        println!("Slashing Operator {operator:?}\n-->{res:?}");
                    }
                    FuzzAction::UnlockFunds {
                        operator_id,
                        nominator_id,
                    } => {
                        let nominator = nominators
                            .get(nominator_id as usize % nominators.len())
                            .unwrap();
                        let operator = operators
                            .get(operator_id as usize % operators.len())
                            .unwrap();
                        let _ = do_unlock_funds::<Test>(*operator as u64, *nominator);
                        #[cfg(not(feature = "fuzzing"))]
                        println!("Unlocking funds as Nominator {nominator:?} from Operator {operator:?} \n-->{res:?}");
                    }
                    FuzzAction::UnlockNominator {
                        operator_id,
                        nominator_id,
                    } => {
                        let nominator = nominators
                            .get(nominator_id as usize % nominators.len())
                            .unwrap();
                        let operator = operators
                            .get(operator_id as usize % operators.len())
                            .unwrap();
                        let _ = do_unlock_nominator::<Test>(*operator as u64, *nominator);
                        #[cfg(not(feature = "fuzzing"))]
                        println!("Unlocking Nominator {nominator:?} from Operator {operator:?} \n-->{res:?}");
                    }
                    FuzzAction::DeregisterOperator { operator_id } => {
                        let operator = operators
                            .get(operator_id as usize % operators.len())
                            .unwrap();
                        let _ = do_deregister_operator::<Test>(*operator, *operator as u64);
                        #[cfg(not(feature = "fuzzing"))]
                        println!("de-registering Operator {operator:?} \n-->{res:?}");
                    }
                    FuzzAction::MarkOperatorsAsSlashed {
                        operator_ids,
                        slash_reason,
                    } => {
                        let slash_reason = match slash_reason % 2 {
                            0 => SlashedReason::InvalidBundle(0),
                            _ => SlashedReason::BadExecutionReceipt(H256::from([0u8; 32])),
                        };
                        let _ = 
                            do_mark_operators_as_slashed::<Test>(vec![operator_ids], slash_reason);
                        #[cfg(not(feature = "fuzzing"))]
                        println!("Marking {operator_ids:?} as slashed\n-->{res:?}");
                    }
                    FuzzAction::MarkInvalidBundleAuthors { operator_ids: _ } => {
                        /* let operators: Vec<u64> = 
                            operator_ids.into_iter().map(|id| id as u64).collect();
                        let res = do_mark_invalid_bundle_authors::<Test>(&operators);
                        #[cfg(not(feature = "fuzzing"))]
                        println!("Marking operators {:?} as invalid bundle authors\n-->{:?}", operators, res); */
                    }
                    FuzzAction::UnmarkInvalidBundleAuthors { operator_ids: _ } => {
                        /* let operators: Vec<u64> = 
                            operator_ids.into_iter().map(|id| id as u64).collect();
                        let res = do_unmark_invalid_bundle_authors::<Test>(&operators);
                        #[cfg(not(feature = "fuzzing"))]
                        println!("Unmarking operators {:?} as invalid bundle authors\n-->{:?}", operators, res); */
                    }
                }
                // Check invariants after each action  
                check_operator_state_consistency_invariant(&operators);
                let all_accounts: Vec<AccountId> = operators.iter().chain(nominators.iter()).chain(std::iter::once(&1u128)).cloned().collect();
                check_total_supply_invariant(&all_accounts, &operators);
                check_treasury_balance_invariant(previous_treasury_balance);
                check_share_price_invariant(&operators, &mut previous_share_prices, &mut slashed_operators);
                check_slashing_invariant(&operators, &mut slashed_operators);
                
                // Update treasury balance for next iteration
                previous_treasury_balance = <Test as Config>::Currency::total_balance(&treasury_account);
                    for operator in &operators {
                        if let Some(operator) = Operators::<Test>::get(*operator as u64) {
                            assert!(operator.current_total_stake > 100 * AI3);
                        }
                    }
            }
            let _ = do_finalize_domain_current_epoch::<Test>(DOMAIN_ID);
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
    pub const StakeEpochDuration: DomainBlockNumber = 5;
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
