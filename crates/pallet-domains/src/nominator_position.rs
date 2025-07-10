//! Nominator position calculation logic

use crate::pallet::{
    Config, Deposits, DomainStakingSummary, OperatorEpochSharePrice, Operators, Withdrawals,
};
use crate::{BalanceOf, DomainBlockNumberFor, ReceiptHashFor};
use alloc::vec::Vec;
use sp_domains::{EpochIndex, OperatorId};
use sp_runtime::traits::{Saturating, Zero};

/// Core data needed for nominator position calculation
struct PositionData<T: Config> {
    /// The nominator's deposit information including known and pending amounts
    pub deposit: crate::staking::Deposit<T::Share, BalanceOf<T>>,
    /// The operator's current state and configuration
    pub operator: crate::staking::Operator<
        BalanceOf<T>,
        T::Share,
        DomainBlockNumberFor<T>,
        ReceiptHashFor<T>,
    >,
    /// Current epoch index for determining deposit conversion eligibility
    pub current_epoch_index: EpochIndex,
    /// Current share price including pending rewards for instant valuation
    pub current_share_price: crate::staking::SharePrice,
}

/// Fetches and validates all core data needed for position calculation
fn fetch_position_data<T: Config>(
    operator_id: OperatorId,
    nominator_account: &T::AccountId,
) -> Option<PositionData<T>> {
    use crate::staking::current_share_price;

    // Get deposit information - early return if no position exists
    let deposit = Deposits::<T>::get(operator_id, nominator_account)?;

    // Get operator information
    let operator = Operators::<T>::get(operator_id)?;
    let domain_id = operator.current_domain_id;

    // Get current domain staking summary for epoch info and rewards
    let staking_summary = DomainStakingSummary::<T>::get(domain_id)?;
    let current_epoch_index = staking_summary.current_epoch_index;

    // Calculate current share price including pending rewards
    let current_share_price =
        current_share_price::<T>(operator_id, &operator, &staking_summary).ok()?;

    // Ensure operator has shares (avoid division by zero scenarios)
    if operator.current_total_shares.is_zero() {
        return None;
    }

    Some(PositionData {
        deposit,
        operator,
        current_epoch_index,
        current_share_price,
    })
}

/// Processes deposits to calculate total shares, storage fees, and pending deposits
fn process_deposits<T: Config>(
    position_data: &PositionData<T>,
    operator_id: OperatorId,
) -> (
    T::Share,
    BalanceOf<T>,
    Vec<sp_domains::PendingDeposit<BalanceOf<T>>>,
) {
    let mut total_shares = position_data.deposit.known.shares;
    let mut total_storage_fee_deposit = position_data.deposit.known.storage_fee_deposit;
    let mut pending_deposits = Vec::new();

    // Process pending deposit if it exists
    if let Some(pending_deposit) = &position_data.deposit.pending {
        // Always include storage fee regardless of conversion status
        total_storage_fee_deposit =
            total_storage_fee_deposit.saturating_add(pending_deposit.storage_fee_deposit);

        let (_, effective_epoch) = pending_deposit.effective_domain_epoch.deconstruct();

        // Try to convert pending deposit to shares if epoch has passed
        if effective_epoch < position_data.current_epoch_index {
            if let Some(epoch_share_price) = OperatorEpochSharePrice::<T>::get(
                operator_id,
                pending_deposit.effective_domain_epoch,
            ) {
                // Convert to shares using historical epoch price
                let pending_shares = epoch_share_price.stake_to_shares::<T>(pending_deposit.amount);
                total_shares = total_shares.saturating_add(pending_shares);
            } else {
                // Epoch passed but no share price available yet - keep as pending
                pending_deposits.push(sp_domains::PendingDeposit {
                    amount: pending_deposit.amount,
                    effective_epoch,
                });
            }
        } else {
            // Epoch hasn't passed yet - keep as pending
            pending_deposits.push(sp_domains::PendingDeposit {
                amount: pending_deposit.amount,
                effective_epoch,
            });
        }
    }

    (total_shares, total_storage_fee_deposit, pending_deposits)
}

/// Calculates adjusted storage fee deposit accounting for fund gains/losses
fn calculate_adjusted_storage_fee<T: Config>(
    operator_id: OperatorId,
    operator_total_storage_fee: BalanceOf<T>,
    nominator_storage_fee: BalanceOf<T>,
) -> BalanceOf<T> {
    use crate::bundle_storage_fund;

    let storage_fund_redeem_price = bundle_storage_fund::storage_fund_redeem_price::<T>(
        operator_id,
        operator_total_storage_fee,
    );

    storage_fund_redeem_price.redeem(nominator_storage_fee)
}

/// Processes pending withdrawals for the nominator
fn process_withdrawals<T: Config>(
    operator_id: OperatorId,
    nominator_account: &T::AccountId,
    current_share_price: &crate::staking::SharePrice,
) -> Vec<sp_domains::PendingWithdrawal<BalanceOf<T>, DomainBlockNumberFor<T>>> {
    let Some(withdrawal) = Withdrawals::<T>::get(operator_id, nominator_account) else {
        return Vec::new();
    };

    let mut pending_withdrawals = Vec::with_capacity(
        withdrawal.withdrawals.len()
            + if withdrawal.withdrawal_in_shares.is_some() {
                1
            } else {
                0
            },
    );

    // Process regular withdrawals
    pending_withdrawals.extend(withdrawal.withdrawals.into_iter().map(|w| {
        sp_domains::PendingWithdrawal {
            amount: w.amount_to_unlock,
            unlock_at_block: w.unlock_at_confirmed_domain_block_number,
        }
    }));

    // Process withdrawal in shares
    if let Some(withdrawal_in_shares) = withdrawal.withdrawal_in_shares {
        let withdrawal_amount =
            OperatorEpochSharePrice::<T>::get(operator_id, withdrawal_in_shares.domain_epoch)
                .map(|epoch_share_price| {
                    epoch_share_price.shares_to_stake::<T>(withdrawal_in_shares.shares)
                })
                .unwrap_or_else(|| {
                    current_share_price.shares_to_stake::<T>(withdrawal_in_shares.shares)
                });

        pending_withdrawals.push(sp_domains::PendingWithdrawal {
            amount: withdrawal_amount,
            unlock_at_block: withdrawal_in_shares.unlock_at_confirmed_domain_block_number,
        });
    }

    pending_withdrawals
}

/// Returns the complete nominator position for a given operator and account at the current block.
    ///
    /// This calculates the total position including:
    /// - Current stake value (converted from shares using instant share price including rewards)
    /// - Total storage fee deposits (known + pending)
    /// - Pending deposits (not yet converted to shares)
    /// - Pending withdrawals (with unlock timing)
    ///
    /// Note: Operator accounts are also nominator accounts, so this call will return the position
    /// for the operator account.
    ///
    /// Returns None if no position exists for the given operator and account at the current block.
pub fn nominator_position<T: Config>(
    operator_id: OperatorId,
    nominator_account: T::AccountId,
) -> Option<sp_domains::NominatorPosition<BalanceOf<T>, DomainBlockNumberFor<T>>> {
    use sp_domains::NominatorPosition;

    // Fetch core data needed for position calculation
    let position_data = fetch_position_data::<T>(operator_id, &nominator_account)?;

    // Calculate current shares and storage fees from deposits
    let (total_shares, total_storage_fee_deposit, pending_deposits) =
        process_deposits::<T>(&position_data, operator_id);

    // Calculate current staked value using instant share price
    let current_staked_value = position_data
        .current_share_price
        .shares_to_stake::<T>(total_shares);

    // Calculate adjusted storage fee deposit (accounts for fund performance)
    let adjusted_storage_fee_deposit = calculate_adjusted_storage_fee::<T>(
        operator_id,
        position_data.operator.total_storage_fee_deposit,
        total_storage_fee_deposit,
    );

    // Process pending withdrawals
    let pending_withdrawals = process_withdrawals::<T>(
        operator_id,
        &nominator_account,
        &position_data.current_share_price,
    );

    Some(NominatorPosition {
        current_staked_value,
        storage_fee_deposit: sp_domains::StorageFeeDeposit {
            total_deposited: total_storage_fee_deposit,
            current_value: adjusted_storage_fee_deposit,
        },
        pending_deposits,
        pending_withdrawals,
    })
}
#[cfg(test)]
mod tests {
    use super::*;
    use crate::tests::*;
    use frame_support::assert_ok;
    use frame_support::traits::Currency;
    use sp_core::Pair;
    use sp_domains::{DomainId, OperatorPair};
    use std::collections::BTreeMap;
    use subspace_runtime_primitives::AI3;

    // Test constants for consistent values across tests
    const DEFAULT_DOMAIN_ID: u32 = 0;
    const DEFAULT_OPERATOR_ACCOUNT: u128 = 1;
    const DEFAULT_NOMINATOR_ACCOUNT: u128 = 2;
    const DEFAULT_OPERATOR_FREE_BALANCE: u128 = 1500 * AI3;
    const DEFAULT_OPERATOR_STAKE: u128 = 1000 * AI3;
    const DEFAULT_NOMINATOR_FREE_BALANCE: u128 = 600 * AI3;
    const DEFAULT_NOMINATOR_STAKE: u128 = 500 * AI3;
    const DEFAULT_MIN_NOMINATOR_STAKE: u128 = 100 * AI3;
    const STAKING_PORTION_PERCENT: u128 = 80;
    const STORAGE_FEE_PERCENT: u128 = 20;
    const TOLERANCE: u128 = AI3 / 1_000_000_000; // 0.000000001 AI3 tolerance for precision differences

    /// Test setup configuration
    #[derive(Clone, Copy)]
    struct TestSetup {
        pub domain_id: DomainId,
        pub operator_account: u128,
        pub nominator_account: u128,
        pub operator_free_balance: u128,
        pub operator_stake: u128,
        pub nominator_free_balance: u128,
        pub nominator_stake: u128,
        pub min_nominator_stake: u128,
    }

    impl Default for TestSetup {
        fn default() -> Self {
            Self {
                domain_id: DomainId::new(DEFAULT_DOMAIN_ID),
                operator_account: DEFAULT_OPERATOR_ACCOUNT,
                nominator_account: DEFAULT_NOMINATOR_ACCOUNT,
                operator_free_balance: DEFAULT_OPERATOR_FREE_BALANCE,
                operator_stake: DEFAULT_OPERATOR_STAKE,
                nominator_free_balance: DEFAULT_NOMINATOR_FREE_BALANCE,
                nominator_stake: DEFAULT_NOMINATOR_STAKE,
                min_nominator_stake: DEFAULT_MIN_NOMINATOR_STAKE,
            }
        }
    }

    /// Helper function to set up a basic operator-nominator scenario
    fn setup_operator_with_nominator(setup: TestSetup) -> (OperatorId, DomainId) {
        let pair = OperatorPair::from_seed(&[0; 32]);

        let (operator_id, _) = crate::staking::tests::register_operator(
            setup.domain_id,
            setup.operator_account,
            setup.operator_free_balance,
            setup.operator_stake,
            setup.min_nominator_stake,
            pair.public(),
            BTreeMap::from_iter(vec![(
                setup.nominator_account,
                (setup.nominator_free_balance, setup.nominator_stake),
            )]),
        );
        (operator_id, setup.domain_id)
    }

    /// Helper function to perform epoch transition
    fn advance_epoch(domain_id: DomainId) {
        crate::staking_epoch::do_finalize_domain_current_epoch::<Test>(domain_id).unwrap();
    }

    /// Helper function to add rewards to an operator
    fn add_rewards(domain_id: DomainId, operator_id: OperatorId, reward_amount: u128) {
        crate::staking::do_reward_operators::<Test>(
            domain_id,
            sp_domains::OperatorRewardSource::Dummy,
            vec![operator_id].into_iter(),
            reward_amount,
        )
        .unwrap();
    }

    /// Helper function to calculate expected staking portion
    fn expected_staking_portion(nominator_stake: u128) -> u128 {
        nominator_stake * STAKING_PORTION_PERCENT / 100
    }

    /// Helper function to calculate expected storage fee
    fn expected_storage_fee(nominator_stake: u128) -> u128 {
        nominator_stake * STORAGE_FEE_PERCENT / 100
    }

    /// Helper function to make additional nomination
    fn make_additional_nomination(nominator_account: u128, operator_id: OperatorId, amount: u128) {
        Balances::make_free_balance_be(&nominator_account, DEFAULT_NOMINATOR_FREE_BALANCE);
        assert_ok!(crate::Pallet::<Test>::nominate_operator(
            frame_system::RawOrigin::Signed(nominator_account).into(),
            operator_id,
            amount,
        ));
    }

    /// Helper function to withdraw stake
    fn withdraw_stake(
        nominator_account: u128,
        operator_id: OperatorId,
        domain_id: DomainId,
        withdrawal_amount: u128,
    ) {
        let current_share_price = crate::staking::current_share_price::<Test>(
            operator_id,
            &crate::pallet::Operators::<Test>::get(operator_id).unwrap(),
            &crate::pallet::DomainStakingSummary::<Test>::get(domain_id).unwrap(),
        )
        .unwrap();
        let shares_to_withdraw = current_share_price.stake_to_shares::<Test>(withdrawal_amount);

        assert_ok!(crate::Pallet::<Test>::withdraw_stake(
            frame_system::RawOrigin::Signed(nominator_account).into(),
            operator_id,
            shares_to_withdraw,
        ));
    }

    /// Helper function to assert position invariants
    fn assert_position_invariants(
        position: &sp_domains::NominatorPosition<u128, u32>,
        expected_staked_value: u128,
        expected_storage_fee: u128,
        expected_pending_deposits: usize,
        expected_pending_withdrawals: usize,
    ) {
        assert_eq!(position.current_staked_value, expected_staked_value);
        assert_eq!(
            position.storage_fee_deposit.current_value,
            expected_storage_fee
        );
        assert_eq!(position.pending_deposits.len(), expected_pending_deposits);
        assert_eq!(
            position.pending_withdrawals.len(),
            expected_pending_withdrawals
        );
    }

    #[test]
    fn test_nominator_position_no_position() {
        let mut ext = new_test_ext_with_extensions();
        ext.execute_with(|| {
            let operator_id = 0;
            let nominator_account = 1;

            // Test: No position initially - should return None
            let position = nominator_position::<Test>(operator_id, nominator_account);
            assert_eq!(position, None);
        });
    }

    #[test]
    fn test_nominator_position_basic_staking() {
        let mut ext = new_test_ext_with_extensions();
        ext.execute_with(|| {
            let setup = TestSetup::default();
            let (operator_id, domain_id) = setup_operator_with_nominator(setup);

            // Test 1: Position with pending deposit (before epoch transition)
            let position =
                nominator_position::<Test>(operator_id, setup.nominator_account).unwrap();
            assert_position_invariants(
                &position,
                0, // No shares yet, all pending
                expected_storage_fee(setup.nominator_stake),
                1, // One pending deposit
                0, // No withdrawals
            );
            // Only the staking portion goes to pending deposit
            assert_eq!(
                position.pending_deposits[0].amount,
                expected_staking_portion(setup.nominator_stake)
            );
            assert_eq!(position.pending_deposits[0].effective_epoch, 1);
            assert_eq!(
                position.storage_fee_deposit.total_deposited,
                position.storage_fee_deposit.current_value
            );

            // Test 2: Position after epoch transition (pending becomes active)
            advance_epoch(domain_id);

            let position =
                nominator_position::<Test>(operator_id, setup.nominator_account).unwrap();
            assert_position_invariants(
                &position,
                expected_staking_portion(setup.nominator_stake),
                expected_storage_fee(setup.nominator_stake),
                0, // No more pending deposits
                0, // No withdrawals
            );
            assert_eq!(
                position.storage_fee_deposit.total_deposited,
                position.storage_fee_deposit.current_value
            );
        });
    }

    #[test]
    fn test_nominator_position_with_additional_nominations() {
        let mut ext = new_test_ext_with_extensions();
        ext.execute_with(|| {
            let initial_nominator_stake = 300 * AI3;
            let additional_nomination = 200 * AI3;
            let setup = TestSetup {
                nominator_stake: initial_nominator_stake,
                min_nominator_stake: 50 * AI3,
                nominator_free_balance: 1000 * AI3,
                ..TestSetup::default()
            };
            let (operator_id, domain_id) = setup_operator_with_nominator(setup);

            // Make additional nomination
            make_additional_nomination(setup.nominator_account, operator_id, additional_nomination);

            // Test: Position should show combined pending deposits
            let position =
                nominator_position::<Test>(operator_id, setup.nominator_account).unwrap();
            let total_stake = initial_nominator_stake + additional_nomination;
            assert_position_invariants(
                &position,
                0, // Still all pending
                expected_storage_fee(total_stake),
                1, // One combined pending deposit
                0, // No withdrawals
            );
            assert_eq!(
                position.pending_deposits[0].amount,
                expected_staking_portion(total_stake)
            );

            // After epoch transition, all should be active
            advance_epoch(domain_id);

            let position =
                nominator_position::<Test>(operator_id, setup.nominator_account).unwrap();
            assert_position_invariants(
                &position,
                expected_staking_portion(total_stake),
                expected_storage_fee(total_stake),
                0, // No more pending deposits
                0, // No withdrawals
            );
        });
    }

    #[test]
    fn test_nominator_position_with_rewards() {
        let mut ext = new_test_ext_with_extensions();
        ext.execute_with(|| {
            let setup = TestSetup::default();
            let (operator_id, domain_id) = setup_operator_with_nominator(setup);
            let rewards = 100 * AI3;

            // Epoch transition to activate staking
            advance_epoch(domain_id);

            let position_before =
                nominator_position::<Test>(operator_id, setup.nominator_account).unwrap();
            let initial_staked_value = expected_staking_portion(setup.nominator_stake);
            assert_eq!(position_before.current_staked_value, initial_staked_value);

            // Add rewards to increase share price
            add_rewards(domain_id, operator_id, rewards);

            // Test: Position value should increase due to rewards (using instant share price)
            let position_after =
                nominator_position::<Test>(operator_id, setup.nominator_account).unwrap();
            assert!(position_after.current_staked_value > position_before.current_staked_value);

            // Calculate reward increase
            let reward_increase =
                position_after.current_staked_value - position_before.current_staked_value;

            // Precise calculation based on actual behavior:
            // - Nominator active stake: 400 AI3 (80% of 500 AI3)
            // - Operator active stake: 800 AI3 (80% of 1000 AI3)
            // - Total active stake: 1200 AI3
            // - Nominator's proportional share: (400/1200) * 100 AI3 = 33.333... AI3
            // (Note: The actual reward distribution may work differently than expected)
            let expected_reward = 100 * AI3 / 3; // 33.333... AI3

            // Allow for precision differences due to rounding in the actual reward calculation
            let reward_range =
                (expected_reward.saturating_sub(TOLERANCE))..=(expected_reward + TOLERANCE);
            assert!(
                reward_range.contains(&reward_increase),
                "Reward increase {reward_increase} should be close to expected {expected_reward} (within range {reward_range:?})"
            );
        });
    }

    #[test]
    fn test_nominator_position_with_withdrawals() {
        let mut ext = new_test_ext_with_extensions();
        ext.execute_with(|| {
            let setup = TestSetup::default();
            let (operator_id, domain_id) = setup_operator_with_nominator(setup);

            // Epoch transition to activate staking
            advance_epoch(domain_id);

            let initial_position =
                nominator_position::<Test>(operator_id, setup.nominator_account).unwrap();
            let expected_initial_value = expected_staking_portion(setup.nominator_stake);
            assert_eq!(
                initial_position.current_staked_value,
                expected_initial_value
            );
            assert_eq!(initial_position.pending_withdrawals.len(), 0);

            // Request partial withdrawal
            let withdrawal_amount = 200 * AI3;
            withdraw_stake(
                setup.nominator_account,
                operator_id,
                domain_id,
                withdrawal_amount,
            );

            // Test: Position should show pending withdrawal
            let position =
                nominator_position::<Test>(operator_id, setup.nominator_account).unwrap();

            // The current staked value should be reduced by the shares withdrawn (converted to current value)
            // This might not exactly equal withdrawal_amount due to share price precision
            assert!(
                position.current_staked_value < initial_position.current_staked_value,
                "Current staked value should decrease after withdrawal"
            );
            assert_eq!(position.pending_withdrawals.len(), 1);

            // The pending withdrawal amount should be close to what was requested
            // Allow for small precision differences due to share price conversions
            let withdrawal_range =
                (withdrawal_amount.saturating_sub(TOLERANCE))..=(withdrawal_amount + TOLERANCE);
            assert!(
                withdrawal_range.contains(&position.pending_withdrawals[0].amount),
                "Pending withdrawal amount {} should be close to requested amount {withdrawal_amount}",
                position.pending_withdrawals[0].amount
            );

            // Should have a valid unlock block
            assert!(
                position.pending_withdrawals[0].unlock_at_block > 0,
                "Unlock block should be set for pending withdrawal"
            );
        });
    }

    #[test]
    fn test_nominator_position_operator_deregistered() {
        let mut ext = new_test_ext_with_extensions();
        ext.execute_with(|| {
            let setup = TestSetup::default();
            let (operator_id, domain_id) = setup_operator_with_nominator(setup);

            // Epoch transition to activate staking
            advance_epoch(domain_id);

            let position_before =
                nominator_position::<Test>(operator_id, setup.nominator_account).unwrap();
            let expected_staked_value = expected_staking_portion(setup.nominator_stake);
            assert_eq!(position_before.current_staked_value, expected_staked_value);

            // Deregister operator
            assert_ok!(crate::Pallet::<Test>::deregister_operator(
                frame_system::RawOrigin::Signed(setup.operator_account).into(),
                operator_id,
            ));

            // Test: Position should still exist even after operator deregistration
            let position_after =
                nominator_position::<Test>(operator_id, setup.nominator_account).unwrap();
            assert_eq!(position_after.current_staked_value, expected_staked_value);
            // Position should remain the same until nominator withdraws
        });
    }

    #[test]
    fn test_nominator_position_storage_fee_scenarios() {
        let mut ext = new_test_ext_with_extensions();
        ext.execute_with(|| {
            let setup = TestSetup::default();
            let (operator_id, _) = setup_operator_with_nominator(setup);

            // Test: Check storage fee is properly accounted for
            let position =
                nominator_position::<Test>(operator_id, setup.nominator_account).unwrap();
            let expected_storage_fee_value = expected_storage_fee(setup.nominator_stake);

            assert_eq!(
                position.storage_fee_deposit.current_value,
                expected_storage_fee_value
            );
            assert_eq!(
                position.storage_fee_deposit.total_deposited,
                expected_storage_fee_value
            ); // Should be equal initially
        });
    }

    #[test]
    fn test_nominator_position_epoch_boundary_pending_conversion() {
        let mut ext = new_test_ext_with_extensions();
        ext.execute_with(|| {
            let setup = TestSetup::default();
            let (operator_id, domain_id) = setup_operator_with_nominator(setup);

            // Check initial epoch state
            let domain_stake_summary =
                crate::pallet::DomainStakingSummary::<Test>::get(domain_id).unwrap();
            let initial_epoch = domain_stake_summary.current_epoch_index;

            // At this point we're in epoch 1, pending deposit is effective for epoch 1 (current epoch)
            let position_initial =
                nominator_position::<Test>(operator_id, setup.nominator_account).unwrap();

            // The deposit should be pending because we're in the same epoch it's effective for
            assert_position_invariants(
                &position_initial,
                0, // No shares yet
                expected_storage_fee(setup.nominator_stake),
                1, // One pending deposit
                0, // No withdrawals
            );
            assert_eq!(
                position_initial.pending_deposits[0].effective_epoch,
                initial_epoch
            );

            // Transition to next epoch - this makes the previous epoch's share price available
            // With the bug (<=), this would incorrectly try to convert a deposit effective for the current epoch
            // With the fix (<), only deposits from completed epochs get converted
            advance_epoch(domain_id);

            let domain_stake_summary =
                crate::pallet::DomainStakingSummary::<Test>::get(domain_id).unwrap();
            let next_epoch = domain_stake_summary.current_epoch_index;

            // Test: Now the deposit should be converted because effective_epoch (1) < current_epoch (2)
            let position_after_transition =
                nominator_position::<Test>(operator_id, setup.nominator_account).unwrap();

            // The deposit should now be converted to shares
            assert_eq!(
                position_after_transition.current_staked_value,
                expected_staking_portion(setup.nominator_stake)
            );
            assert_eq!(position_after_transition.pending_deposits.len(), 0); // No more pending deposits

            // Test the boundary condition: Make a new deposit in the current epoch
            let additional_nomination = 200 * AI3;
            make_additional_nomination(setup.nominator_account, operator_id, additional_nomination);

            // This new deposit should be pending (effective for current epoch = next_epoch)
            let position_new_deposit =
                nominator_position::<Test>(operator_id, setup.nominator_account).unwrap();

            // Should have 1 pending deposit effective for the current epoch
            assert_eq!(position_new_deposit.pending_deposits.len(), 1);
            assert_eq!(
                position_new_deposit.pending_deposits[0].effective_epoch,
                next_epoch
            );

            // Current value should remain the same (new deposit not converted yet)
            assert_eq!(
                position_new_deposit.current_staked_value,
                position_after_transition.current_staked_value
            );
        });
    }

    #[test]
    fn test_nominator_position_adjusted_storage_fee_deposit() {
        let mut ext = new_test_ext_with_extensions();
        ext.execute_with(|| {
            let setup = TestSetup::default();
            let (operator_id, domain_id) = setup_operator_with_nominator(setup);

            // Epoch transition to activate staking
            advance_epoch(domain_id);

            let position_initial =
                nominator_position::<Test>(operator_id, setup.nominator_account).unwrap();
            let initial_storage_fee_current_value =
                position_initial.storage_fee_deposit.current_value;
            let original_storage_fee_total_deposited =
                position_initial.storage_fee_deposit.total_deposited;
            let expected_storage_fee_value = expected_storage_fee(setup.nominator_stake);
            let storage_fund_balance_initial =
                crate::bundle_storage_fund::total_balance::<Test>(operator_id);

            // Storage fee should be 20% of the nominator stake initially
            assert_eq!(
                initial_storage_fee_current_value,
                expected_storage_fee_value
            );
            assert_eq!(
                original_storage_fee_total_deposited,
                expected_storage_fee_value
            ); // Original should match initial

            // Test 1: Storage fund breaks even - no change in value
            let position_breakeven =
                nominator_position::<Test>(operator_id, setup.nominator_account).unwrap();
            assert_eq!(
                position_breakeven.storage_fee_deposit.current_value,
                expected_storage_fee_value
            );
            assert_eq!(
                position_breakeven.storage_fee_deposit.total_deposited,
                expected_storage_fee_value
            ); // Original unchanged

            // Test 2: Storage fund loses money (charge more than refund)
            // Charge storage fees to simulate bundle submissions
            crate::bundle_storage_fund::charge_bundle_storage_fee::<Test>(
                operator_id,
                50, // 50 bytes at 1 AI3 per byte = 50 AI3 charged
            )
            .unwrap();

            let storage_fund_balance_after_charge =
                crate::bundle_storage_fund::total_balance::<Test>(operator_id);
            let position_after_charge =
                nominator_position::<Test>(operator_id, setup.nominator_account).unwrap();
            // Use the actual storage fund balance change to verify the calculation
            let storage_fund_change =
                storage_fund_balance_initial - storage_fund_balance_after_charge;

            // Calculate the nominator's proportional loss using Perquintill
            let nominator_storage_fee = expected_storage_fee(setup.nominator_stake);
            let nominator_proportion = sp_runtime::Perquintill::from_rational(
                nominator_storage_fee,
                storage_fund_balance_initial,
            );
            let expected_loss = nominator_proportion.mul_floor(storage_fund_change);

            let expected_value = expected_storage_fee_value - expected_loss;
            let expected_range =
                (expected_value.saturating_sub(TOLERANCE))..=(expected_value + TOLERANCE);
            assert!(
                expected_range.contains(&position_after_charge.storage_fee_deposit.current_value),
                "Storage fee value {} should be close to expected {expected_value} (within range {expected_range:?})",
                position_after_charge.storage_fee_deposit.current_value
            );

            // Storage fee deposit should be reduced proportionally
            //assert_eq!(position_after_charge.storage_fee_deposit.current_value, expected_storage_fee_value - expected_loss_after_charge);
            assert_eq!(
                position_after_charge.storage_fee_deposit.total_deposited,
                expected_storage_fee_value
            ); // Original unchanged

            // Test 3: Storage fund becomes profitable (refund more than charged)
            // Refund more storage fees to simulate domain users paying fees
            crate::bundle_storage_fund::refund_storage_fee::<Test>(
                200 * AI3,                                 // Refund 200 AI3 (more than the 50 AI3 charged)
                BTreeMap::from_iter([(operator_id, 100)]), // Operator contributed 100% of bundle storage
            )
            .unwrap();

            let storage_fund_balance_after_refund =
                crate::bundle_storage_fund::total_balance::<Test>(operator_id);
            let position_after_refund =
                nominator_position::<Test>(operator_id, setup.nominator_account).unwrap();

            // Use the actual storage fund balance change to verify the calculation
            let net_storage_fund_change =
                storage_fund_balance_after_refund - storage_fund_balance_initial;

            // Calculate the nominator's proportional gain using Perquintill
            let nominator_proportion = sp_runtime::Perquintill::from_rational(
                nominator_storage_fee,
                storage_fund_balance_initial,
            );
            let expected_gain = nominator_proportion.mul_floor(net_storage_fund_change);

            let expected_final_value = expected_storage_fee_value + expected_gain;
            let expected_range = (expected_final_value.saturating_sub(TOLERANCE))
                ..=(expected_final_value + TOLERANCE);
            assert!(
                expected_range.contains(&position_after_refund.storage_fee_deposit.current_value),
                "Storage fee value {} should be close to expected {expected_final_value} (within range {expected_range:?})",
                position_after_refund.storage_fee_deposit.current_value
            );

            // Verify original value never changes
            assert_eq!(
                position_after_charge.storage_fee_deposit.total_deposited,
                expected_storage_fee_value,
                "Original storage fee should never change"
            );
            assert_eq!(
                position_after_refund.storage_fee_deposit.total_deposited,
                expected_storage_fee_value,
                "Original storage fee should never change"
            );
        });
    }
}
