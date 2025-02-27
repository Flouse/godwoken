#![allow(clippy::mutable_key_type)]

use std::collections::{HashMap, HashSet};
use std::iter::FromIterator;
use std::sync::Arc;
use std::time::Duration;

use crate::testing_tool::chain::{
    build_sync_tx, construct_block, construct_block_with_timestamp, into_deposit_info_cell,
    produce_empty_block, setup_chain_with_config, ALWAYS_SUCCESS_CODE_HASH, ALWAYS_SUCCESS_PROGRAM,
    CUSTODIAN_LOCK_PROGRAM, DEFAULT_FINALITY_BLOCKS, STAKE_LOCK_PROGRAM,
    STATE_VALIDATOR_TYPE_PROGRAM, WITHDRAWAL_LOCK_PROGRAM,
};
use crate::testing_tool::mem_pool_provider::DummyMemPoolProvider;
use crate::testing_tool::verify_tx::{verify_tx, TxWithContext};

use async_trait::async_trait;
use gw_block_producer::produce_block::ProduceBlockResult;
use gw_block_producer::withdrawal_unlocker::{BuildUnlockWithdrawalToOwner, Guard};
use gw_chain::chain::{L1Action, L1ActionContext, SyncParam};
use gw_config::ContractsCellDep;
use gw_smt::smt::{SMT, SMTH256};
use gw_smt::smt_h256_ext::SMTH256Ext;
use gw_smt::sparse_merkle_tree::default_store::DefaultStore;
use gw_types::bytes::Bytes;
use gw_types::core::{AllowedEoaType, DepType, ScriptHashType, Timepoint};
use gw_types::h256::H256;
use gw_types::offchain::{
    CellInfo, CollectedCustodianCells, CompatibleFinalizedTimepoint, FinalizedCustodianCapacity,
    InputCellInfo,
};
use gw_types::packed::{
    self, AllowedTypeHash, BlockMerkleState, CellDep, CellInput, CellOutput, CustodianLockArgs,
    DepositRequest, GlobalState, OutPoint, RawWithdrawalRequest, RollupAction, RollupActionUnion,
    RollupConfig, RollupSubmitBlock, Script, StakeLockArgs, WithdrawalRequest,
    WithdrawalRequestExtra, WitnessArgs,
};
use gw_types::prelude::*;
use gw_utils::local_cells::LocalCellsManager;
use gw_utils::transaction_skeleton::TransactionSkeleton;
use gw_utils::RollupContext;

const CKB: u64 = 100000000;
const MAX_MEM_BLOCK_WITHDRAWALS: u8 = 50;

#[tokio::test(flavor = "multi_thread", worker_threads = 1)]
async fn test_build_unlock_to_owner_tx() {
    let _ = env_logger::builder().is_test(true).try_init();

    const CONTRACT_CELL_CAPACITY: u64 = 1000 * CKB;
    let always_type = random_always_success_script(None);
    let always_cell = CellInfo {
        out_point: OutPoint::new_builder()
            .tx_hash(rand::random::<[u8; 32]>().pack())
            .build(),
        output: CellOutput::new_builder()
            .capacity(CONTRACT_CELL_CAPACITY.pack())
            .type_(Some(always_type.clone()).pack())
            .build(),
        data: ALWAYS_SUCCESS_PROGRAM.clone(),
    };

    let sudt_script = Script::new_builder()
        .code_hash(always_type.hash().pack())
        .hash_type(ScriptHashType::Type.into())
        .args(vec![rand::random::<u8>(), 32].pack())
        .build();

    let withdrawal_lock_type = random_always_success_script(None);
    let withdrawal_lock_cell = CellInfo {
        out_point: OutPoint::new_builder()
            .tx_hash(rand::random::<[u8; 32]>().pack())
            .build(),
        output: CellOutput::new_builder()
            .capacity(CONTRACT_CELL_CAPACITY.pack())
            .type_(Some(withdrawal_lock_type.clone()).pack())
            .build(),
        data: WITHDRAWAL_LOCK_PROGRAM.clone(),
    };

    let stake_lock_type = random_always_success_script(None);
    let stake_lock_cell = CellInfo {
        out_point: OutPoint::new_builder()
            .tx_hash(rand::random::<[u8; 32]>().pack())
            .build(),
        output: CellOutput::new_builder()
            .capacity(CONTRACT_CELL_CAPACITY.pack())
            .type_(Some(stake_lock_type.clone()).pack())
            .build(),
        data: STAKE_LOCK_PROGRAM.clone(),
    };

    let deposit_lock_type = random_always_success_script(None);

    let custodian_lock_type = random_always_success_script(None);
    let custodian_lock_cell = CellInfo {
        out_point: OutPoint::new_builder()
            .tx_hash(rand::random::<[u8; 32]>().pack())
            .build(),
        output: CellOutput::new_builder()
            .capacity(CONTRACT_CELL_CAPACITY.pack())
            .type_(Some(custodian_lock_type.clone()).pack())
            .build(),
        data: CUSTODIAN_LOCK_PROGRAM.clone(),
    };

    let rollup_config = RollupConfig::new_builder()
        .stake_script_type_hash(stake_lock_type.hash().pack())
        .custodian_script_type_hash(custodian_lock_type.hash().pack())
        .withdrawal_script_type_hash(withdrawal_lock_type.hash().pack())
        .deposit_script_type_hash(deposit_lock_type.hash().pack())
        .l1_sudt_script_type_hash(always_type.hash().pack())
        .allowed_eoa_type_hashes(
            vec![AllowedTypeHash::new(
                AllowedEoaType::Eth,
                *ALWAYS_SUCCESS_CODE_HASH,
            )]
            .pack(),
        )
        .finality_blocks(1u64.pack())
        .build();
    let rollup_config_type = random_always_success_script(None);
    let rollup_config_cell = CellInfo {
        out_point: OutPoint::new_builder()
            .tx_hash(rand::random::<[u8; 32]>().pack())
            .build(),
        output: CellOutput::new_builder()
            .capacity(CONTRACT_CELL_CAPACITY.pack())
            .type_(Some(rollup_config_type).pack())
            .build(),
        data: rollup_config.as_bytes(),
    };

    let last_finalized_block_number = 100;
    let last_finalized_timepoint = Timepoint::from_block_number(last_finalized_block_number);
    let global_state = GlobalState::new_builder()
        .last_finalized_timepoint(last_finalized_timepoint.full_value().pack())
        .block(
            BlockMerkleState::new_builder()
                .count(
                    (1 + last_finalized_block_number + rollup_config.finality_blocks().unpack())
                        .pack(),
                )
                .build(),
        )
        .rollup_config_hash(rollup_config.hash().pack())
        .build();

    let state_validator_type = random_always_success_script(None);
    let state_validator_cell = CellInfo {
        out_point: OutPoint::new_builder()
            .tx_hash(rand::random::<[u8; 32]>().pack())
            .build(),
        output: CellOutput::new_builder()
            .capacity(CONTRACT_CELL_CAPACITY.pack())
            .type_(Some(state_validator_type.clone()).pack())
            .build(),
        data: STATE_VALIDATOR_TYPE_PROGRAM.clone(),
    };

    let rollup_type_script = Script::new_builder()
        .code_hash(state_validator_type.hash().pack())
        .hash_type(ScriptHashType::Type.into())
        .args(vec![1u8; 32].pack())
        .build();
    let rollup_script_hash: H256 = rollup_type_script.hash();
    let rollup_cell = CellInfo {
        data: global_state.as_bytes(),
        out_point: OutPoint::new_builder()
            .tx_hash(rand::random::<[u8; 32]>().pack())
            .build(),
        output: CellOutput::new_builder()
            .type_(Some(rollup_type_script.clone()).pack())
            .build(),
    };
    let mut chain =
        setup_chain_with_config(rollup_type_script.clone(), rollup_config.clone()).await;
    let rollup_context = RollupContext {
        rollup_script_hash,
        rollup_config: rollup_config.clone(),
        ..Default::default()
    };

    let contracts_dep = ContractsCellDep {
        withdrawal_cell_lock: CellDep::new_builder()
            .out_point(withdrawal_lock_cell.out_point.clone())
            .build()
            .into(),
        l1_sudt_type: CellDep::new_builder()
            .out_point(always_cell.out_point.clone())
            .build()
            .into(),
        custodian_cell_lock: CellDep::new_builder()
            .out_point(custodian_lock_cell.out_point.clone())
            .build()
            .into(),
        rollup_config: CellDep::new_builder()
            .out_point(rollup_config_cell.out_point.clone())
            .build()
            .into(),
        ..Default::default()
    };

    // Deposit random accounts
    const DEPOSIT_CAPACITY: u64 = 1000000 * CKB;
    const DEPOSIT_AMOUNT: u128 = 1000;
    let account_count = MAX_MEM_BLOCK_WITHDRAWALS;
    let accounts: Vec<_> = (0..account_count)
        .map(|_| {
            random_always_success_script(Some(&rollup_script_hash))
                .as_builder()
                .hash_type(ScriptHashType::Type.into())
                .build()
        })
        .collect();
    let deposits = accounts.iter().map(|account_script| {
        DepositRequest::new_builder()
            .capacity(DEPOSIT_CAPACITY.pack())
            .sudt_script_hash(sudt_script.hash().pack())
            .amount(DEPOSIT_AMOUNT.pack())
            .script(account_script.to_owned())
            .registry_id(gw_common::builtins::ETH_REGISTRY_ACCOUNT_ID.pack())
            .build()
    });
    let deposit_info_vec = deposits
        .map(|d| into_deposit_info_cell(&rollup_context, d).pack())
        .pack();

    let deposit_block_result = {
        let mem_pool = chain.mem_pool().as_ref().unwrap();
        let mut mem_pool = mem_pool.lock().await;
        construct_block(&chain, &mut mem_pool, deposit_info_vec.clone())
            .await
            .unwrap()
    };
    let apply_deposits = L1Action {
        context: L1ActionContext::SubmitBlock {
            l2block: deposit_block_result.block.clone(),
            deposit_info_vec,
            deposit_asset_scripts: Default::default(),
            withdrawals: Default::default(),
        },
        transaction: build_sync_tx(rollup_cell.output.clone(), deposit_block_result.clone()),
    };
    let param = SyncParam {
        updates: vec![apply_deposits],
        reverts: Default::default(),
    };
    chain.sync(param).await.unwrap();
    chain.notify_new_tip().await.unwrap();
    assert!(chain.last_sync_event().is_success());

    for _ in 0..DEFAULT_FINALITY_BLOCKS {
        produce_empty_block(&mut chain).await.unwrap();
    }

    let deposit_finalized_global_state = chain.local_state().last_global_state().clone();
    let input_rollup_cell = CellInfo {
        data: deposit_finalized_global_state.as_bytes(),
        out_point: OutPoint::new_builder()
            .tx_hash(rand::random::<[u8; 32]>().pack())
            .build(),
        output: CellOutput::new_builder()
            .type_(Some(rollup_type_script.clone()).pack())
            .lock(random_always_success_script(None))
            .build(),
    };

    // Generate random withdrawals(w/wo owner lock)
    const WITHDRAWAL_CAPACITY: u64 = 1000 * CKB;
    const WITHDRAWAL_AMOUNT: u128 = 100;
    let withdrawals_lock = {
        accounts.iter().map(|account_script| {
            let raw = RawWithdrawalRequest::new_builder()
                .capacity(WITHDRAWAL_CAPACITY.pack())
                .amount(WITHDRAWAL_AMOUNT.pack())
                .account_script_hash(account_script.hash().pack())
                .owner_lock_hash(account_script.hash().pack())
                .sudt_script_hash(sudt_script.hash().pack())
                .registry_id(gw_common::builtins::ETH_REGISTRY_ACCOUNT_ID.pack())
                .build();
            let req = WithdrawalRequest::new_builder().raw(raw).build();
            WithdrawalRequestExtra::new_builder()
                .request(req)
                .owner_lock(account_script.to_owned())
                .build()
        })
    };

    // Push withdrawals
    let finalized_custodians = FinalizedCustodianCapacity {
        capacity: ((accounts.len() as u128 + 1) * WITHDRAWAL_CAPACITY as u128),
        sudt: HashMap::from_iter([(
            sudt_script.hash(),
            (
                WITHDRAWAL_AMOUNT * (accounts.len() as u128 + 1),
                sudt_script.clone(),
            ),
        )]),
    };

    {
        let mem_pool = chain.mem_pool().as_ref().unwrap();
        let mut mem_pool = mem_pool.lock().await;
        let provider = DummyMemPoolProvider {
            deposit_cells: vec![],
            fake_blocktime: Duration::from_millis(0),
        };
        mem_pool.set_provider(Box::new(provider));

        for withdrawal in withdrawals_lock {
            mem_pool.push_withdrawal_request(withdrawal).await.unwrap();
        }

        mem_pool
            .reset_mem_block(&LocalCellsManager::default())
            .await
            .unwrap();
        assert_eq!(mem_pool.mem_block().withdrawals().len(), accounts.len());
    }

    const BLOCK_TIMESTAMP: u64 = 10000u64;
    let withdrawal_block_result = {
        let mem_pool = chain.mem_pool().as_ref().unwrap();
        let mut mem_pool = mem_pool.lock().await;
        construct_block_with_timestamp(
            &chain,
            &mut mem_pool,
            Default::default(),
            BLOCK_TIMESTAMP,
            true,
        )
        .await
        .unwrap()
    };
    assert_eq!(
        withdrawal_block_result.block.withdrawals().len(),
        accounts.len()
    );

    // Generate withdrawal cells
    let withdrawal_extras = {
        let withdrawals = withdrawal_block_result
            .withdrawal_extras
            .clone()
            .into_iter();
        withdrawals.map(|w| (w.hash(), w))
    };
    let generated_withdrawals = gw_block_producer::withdrawal::generate(
        &rollup_context,
        CollectedCustodianCells {
            cells_info: vec![Default::default()],
            capacity: finalized_custodians.capacity,
            sudt: finalized_custodians.sudt.clone(),
        },
        &withdrawal_block_result.block,
        &contracts_dep,
        &withdrawal_extras.collect(),
    )
    .expect("generate")
    .expect("some withdrawals cell");

    //  Check submit withdrawal cells pass state validator contract
    const STAKE_CAPACITY: u64 = 1000 * CKB;
    let input_stake_cell = {
        let mut lock_args = rollup_script_hash.as_slice().to_vec();
        lock_args.extend_from_slice(StakeLockArgs::default().as_slice());

        let stake_lock = Script::new_builder()
            .code_hash(stake_lock_type.hash().pack())
            .hash_type(ScriptHashType::Type.into())
            .args(lock_args.pack())
            .build();
        CellInfo {
            out_point: OutPoint::new_builder()
                .tx_hash(rand::random::<[u8; 32]>().pack())
                .build(),
            output: CellOutput::new_builder()
                .capacity(STAKE_CAPACITY.pack())
                .lock(stake_lock)
                .build(),
            data: Bytes::default(),
        }
    };
    let output_stake = {
        let stake_finalized_timepoint =
            Timepoint::from_block_number(withdrawal_block_result.block.raw().number().unpack());
        let stake_lock_args = StakeLockArgs::new_builder()
            .stake_finalized_timepoint(stake_finalized_timepoint.full_value().pack())
            .build();

        let mut lock_args = rollup_script_hash.as_slice().to_vec();
        lock_args.extend_from_slice(stake_lock_args.as_slice());

        let stake_lock = Script::new_builder()
            .code_hash(stake_lock_type.hash().pack())
            .hash_type(ScriptHashType::Type.into())
            .args(lock_args.pack())
            .build();

        let output = CellOutput::new_builder()
            .capacity(STAKE_CAPACITY.pack())
            .lock(stake_lock)
            .build();
        (output, Bytes::default())
    };

    let input_custodian_cell = {
        let mut lock_args = rollup_script_hash.as_slice().to_vec();
        lock_args.extend_from_slice(CustodianLockArgs::default().as_slice());

        let custodian_lock = Script::new_builder()
            .code_hash(custodian_lock_type.hash().pack())
            .hash_type(ScriptHashType::Type.into())
            .args(lock_args.pack())
            .build();

        let mut finalized_sudt = finalized_custodians.sudt.values().collect::<Vec<_>>();
        CellInfo {
            out_point: OutPoint::new_builder()
                .tx_hash(rand::random::<[u8; 32]>().pack())
                .build(),
            output: CellOutput::new_builder()
                .capacity((finalized_custodians.capacity as u64).pack())
                .type_(Some(sudt_script.clone()).pack())
                .lock(custodian_lock)
                .build(),
            data: finalized_sudt.pop().unwrap().0.pack().as_bytes(),
        }
    };

    let output_rollup_cell = (
        rollup_cell.output.clone(),
        withdrawal_block_result.global_state.as_bytes(),
    );
    let witness = {
        let rollup_action = RollupAction::new_builder()
            .set(RollupActionUnion::RollupSubmitBlock(
                RollupSubmitBlock::new_builder()
                    .block(withdrawal_block_result.block.clone())
                    .build(),
            ))
            .build();
        WitnessArgs::new_builder()
            .output_type(Some(rollup_action.as_bytes()).pack())
            .build()
    };

    let input_cell_deps = vec![
        into_input_cell(always_cell.clone()),
        into_input_cell(stake_lock_cell.clone()),
        into_input_cell(state_validator_cell.clone()),
        into_input_cell(custodian_lock_cell),
        into_input_cell(rollup_config_cell.clone()),
    ];
    let cell_deps = {
        let deps = input_cell_deps.iter();
        deps.map(|i| {
            CellDep::new_builder()
                .out_point(i.cell.out_point.to_owned())
                .dep_type(DepType::Code.into())
                .build()
        })
        .collect::<Vec<_>>()
    };

    const SINCE_BLOCK_TIMESTAMP_FLAG: u64 = 0x4000_0000_0000_0000;
    let block_since = {
        let input_timestamp = Duration::from_millis(BLOCK_TIMESTAMP).as_secs() + 1;
        SINCE_BLOCK_TIMESTAMP_FLAG | input_timestamp
    };
    let inputs = vec![
        into_input_cell_since(input_rollup_cell, block_since),
        into_input_cell(input_stake_cell.clone()),
        into_input_cell(input_custodian_cell),
    ];
    let mut outputs = vec![output_rollup_cell, output_stake];
    outputs.extend(generated_withdrawals.outputs.clone());

    let mut tx_skeleton = TransactionSkeleton::default();
    tx_skeleton.cell_deps_mut().extend(cell_deps);
    tx_skeleton.inputs_mut().extend(inputs.clone());
    tx_skeleton.witnesses_mut().push(witness);
    tx_skeleton.outputs_mut().extend(outputs);
    let tx = tx_skeleton.seal(&[], vec![]).unwrap().transaction;

    let tx_with_context = TxWithContext {
        tx,
        cell_deps: input_cell_deps,
        inputs,
    };
    verify_tx(tx_with_context, 700_000_000_u64).expect("pass");

    // Check unlock to owner tx
    let random_withdrawal_cells = {
        let outputs = generated_withdrawals.outputs.into_iter();
        outputs
            .map(|(output, data)| CellInfo {
                output,
                data,
                out_point: OutPoint::new_builder()
                    .tx_hash(rand::random::<[u8; 32]>().pack())
                    .build(),
            })
            .collect::<Vec<_>>()
    };

    let mut unlocker = DummyUnlocker {
        rollup_cell: rollup_cell.clone(),
        rollup_context: rollup_context.clone(),
        contracts_dep: Arc::new(contracts_dep.clone()),
        withdrawals: random_withdrawal_cells.clone(),
    };
    let cell_deps = vec![
        into_input_cell(rollup_config_cell.clone()),
        into_input_cell(rollup_cell.clone()),
        into_input_cell(always_cell.clone()),
        into_input_cell(withdrawal_lock_cell.clone()),
    ];

    let unlocked = Default::default();
    let (tx, to_unlock) = unlocker
        .query_and_unlock_to_owner(&unlocked)
        .await
        .expect("unlock")
        .expect("skip no owner lock");
    assert_eq!(to_unlock.len(), accounts.len());

    let inputs = {
        let cells = random_withdrawal_cells.clone().into_iter();
        cells.map(into_input_cell).collect()
    };
    let tx_with_context = TxWithContext {
        tx,
        cell_deps: cell_deps.clone(),
        inputs,
    };

    verify_tx(tx_with_context, 700_000_000_u64).expect("pass");

    // Simulate rpc client filter no owner lock withdrawal cells
    let finality_as_blocks = rollup_config.finality_blocks().unpack();
    let compatible_finalized_timepoint = CompatibleFinalizedTimepoint::from_block_number(
        withdrawal_block_result.block.raw().number().unpack() + finality_as_blocks,
        finality_as_blocks,
    );
    let unlockable_random_withdrawals: Vec<_> = random_withdrawal_cells
        .into_iter()
        .filter(|cell| {
            gw_rpc_client::withdrawal::verify_unlockable_to_owner(
                cell,
                &compatible_finalized_timepoint,
                &rollup_context.rollup_config.l1_sudt_script_type_hash(),
            )
            .is_ok()
        })
        .collect();
    assert_eq!(unlockable_random_withdrawals.len(), accounts.len());

    unlocker.withdrawals = unlockable_random_withdrawals.clone();
    let (tx, _to_unlock) = unlocker
        .query_and_unlock_to_owner(&unlocked)
        .await
        .expect("unlock")
        .expect("some withdrawals tx");

    let inputs = unlockable_random_withdrawals
        .clone()
        .into_iter()
        .map(into_input_cell)
        .collect();

    let tx_with_context = TxWithContext {
        tx,
        cell_deps,
        inputs,
    };

    verify_tx(tx_with_context, 700_000_000_u64).expect("pass");

    // Make sure revert withdrawal also work
    const BLOCK_TIMESTAMP2: u64 = BLOCK_TIMESTAMP * 2;
    let block_result = {
        let mem_pool = chain.mem_pool().as_ref().unwrap();
        let mut mem_pool = mem_pool.lock().await;
        // Reset finalized custodian should stale all withdrawals
        let provider = DummyMemPoolProvider::default();
        mem_pool.set_provider(Box::new(provider));

        let tip_block_number = chain.local_state().tip().raw().number().unpack();
        {
            let mut store_tx = chain.store().begin_transaction();
            store_tx
                .set_block_post_finalized_custodian_capacity(
                    tip_block_number,
                    &packed::FinalizedCustodianCapacity::default().as_reader(),
                )
                .unwrap();
            store_tx.commit().unwrap();
        }

        mem_pool
            .reset_mem_block(&LocalCellsManager::default())
            .await
            .unwrap();
        construct_block_with_timestamp(
            &chain,
            &mut mem_pool,
            Default::default(),
            BLOCK_TIMESTAMP2,
            true,
        )
        .await
        .unwrap()
    };
    assert_eq!(block_result.block.withdrawals().len(), 0);

    let smt_store = DefaultStore::default();
    let mut reverted_block_smt = SMT::new(SMTH256::zero(), smt_store);
    // Revert previous withdrawal block result
    reverted_block_smt
        .update(withdrawal_block_result.block.hash().into(), SMTH256::one())
        .unwrap();

    // Update reverted block smt root
    let block_result = ProduceBlockResult {
        global_state: block_result
            .global_state
            .as_builder()
            .reverted_block_root(H256::from(*reverted_block_smt.root()).pack())
            .build(),
        ..block_result
    };

    let input_rollup_cell = {
        let global_state = {
            let builder = deposit_finalized_global_state.as_builder();
            builder.reverted_block_root(H256::from(*reverted_block_smt.root()).pack())
        };
        CellInfo {
            data: global_state.build().as_bytes(),
            out_point: OutPoint::new_builder()
                .tx_hash(rand::random::<[u8; 32]>().pack())
                .build(),
            output: CellOutput::new_builder()
                .type_(Some(rollup_type_script).pack())
                .lock(random_always_success_script(None))
                .build(),
        }
    };
    let output_rollup_cell = (rollup_cell.output, block_result.global_state.as_bytes());

    let output_stake = {
        let stake_finalized_timepoint =
            Timepoint::from_block_number(block_result.block.raw().number().unpack());
        let stake_lock_args = StakeLockArgs::new_builder()
            .stake_finalized_timepoint(stake_finalized_timepoint.full_value().pack())
            .build();

        let mut lock_args = rollup_script_hash.as_slice().to_vec();
        lock_args.extend_from_slice(stake_lock_args.as_slice());

        let stake_lock = Script::new_builder()
            .code_hash(stake_lock_type.hash().pack())
            .hash_type(ScriptHashType::Type.into())
            .args(lock_args.pack())
            .build();
        let output = CellOutput::new_builder()
            .capacity(STAKE_CAPACITY.pack())
            .lock(stake_lock)
            .build();
        (output, Bytes::default())
    };

    // Withdrawal cell to revert
    let revert_count = (rand::random::<u8>() as usize % unlockable_random_withdrawals.len()) + 1;
    assert!(revert_count >= 1);

    let withdrawals_to_revert = unlockable_random_withdrawals
        .into_iter()
        .take(revert_count)
        .collect();
    let reverted_withdrawals = gw_block_producer::withdrawal::revert(
        &rollup_context,
        &contracts_dep,
        withdrawals_to_revert,
    )
    .expect("revert")
    .expect("one custodian");

    let input_cell_deps = vec![
        into_input_cell(always_cell),
        into_input_cell(stake_lock_cell),
        into_input_cell(state_validator_cell),
        into_input_cell(withdrawal_lock_cell),
        into_input_cell(rollup_config_cell),
    ];
    let cell_deps = {
        let deps = input_cell_deps.iter();
        deps.map(|i| {
            CellDep::new_builder()
                .out_point(i.cell.out_point.to_owned())
                .dep_type(DepType::Code.into())
                .build()
        })
        .collect::<Vec<_>>()
    };
    let block_since = {
        let input_timestamp = Duration::from_millis(BLOCK_TIMESTAMP2).as_secs() + 1;
        SINCE_BLOCK_TIMESTAMP_FLAG | input_timestamp
    };
    let mut inputs = vec![
        into_input_cell_since(input_rollup_cell, block_since),
        into_input_cell(input_stake_cell),
    ];
    inputs.extend(reverted_withdrawals.inputs);

    let mut outputs = vec![output_rollup_cell, output_stake];
    outputs.extend(reverted_withdrawals.outputs);

    let reverted_block_hash = withdrawal_block_result.block.hash();
    let reverted_block_proof = {
        let keys: Vec<SMTH256> = vec![reverted_block_hash.into()];
        let merkle_proof = reverted_block_smt.merkle_proof(keys.clone()).unwrap();
        merkle_proof.compile(keys).unwrap()
    };

    let rollup_witness = {
        let rollup_action = RollupAction::new_builder()
            .set(RollupActionUnion::RollupSubmitBlock(
                RollupSubmitBlock::new_builder()
                    .block(block_result.block)
                    .reverted_block_hashes(vec![reverted_block_hash.pack()].pack())
                    .reverted_block_proof(reverted_block_proof.0.pack())
                    .build(),
            ))
            .build();
        WitnessArgs::new_builder()
            .output_type(Some(rollup_action.as_bytes()).pack())
            .build()
    };
    let mut witnesses = vec![rollup_witness, Default::default()]; // One default for input stake cell
    witnesses.extend(reverted_withdrawals.witness_args);

    let mut tx_skeleton = TransactionSkeleton::default();
    tx_skeleton.cell_deps_mut().extend(cell_deps);
    tx_skeleton.inputs_mut().extend(inputs.clone());
    tx_skeleton.witnesses_mut().extend(witnesses);
    tx_skeleton.outputs_mut().extend(outputs);
    let tx = tx_skeleton.seal(&[], vec![]).unwrap().transaction;

    let tx_with_context = TxWithContext {
        tx,
        cell_deps: input_cell_deps,
        inputs,
    };
    verify_tx(tx_with_context, 700_000_000_u64).expect("pass");
}

struct DummyUnlocker {
    rollup_cell: CellInfo,
    rollup_context: RollupContext,
    contracts_dep: Arc<ContractsCellDep>,
    withdrawals: Vec<CellInfo>,
}

#[async_trait]
impl BuildUnlockWithdrawalToOwner for DummyUnlocker {
    fn rollup_config(&self) -> &RollupConfig {
        &self.rollup_context.rollup_config
    }

    fn contracts_dep(&self) -> Guard<Arc<ContractsCellDep>> {
        Guard::from_inner(Arc::clone(&self.contracts_dep))
    }

    async fn query_rollup_cell(&self) -> anyhow::Result<Option<CellInfo>> {
        Ok(Some(self.rollup_cell.clone()))
    }

    async fn query_unlockable_withdrawals(
        &self,
        _last_finalized_timepoint: &CompatibleFinalizedTimepoint,
        _unlocked: &HashSet<OutPoint>,
    ) -> anyhow::Result<Vec<CellInfo>> {
        Ok(self.withdrawals.clone())
    }

    async fn complete_tx(
        &self,
        tx_skeleton: TransactionSkeleton,
    ) -> anyhow::Result<gw_types::packed::Transaction> {
        Ok(tx_skeleton.seal(&[], vec![])?.transaction)
    }
}

fn into_input_cell(cell: CellInfo) -> InputCellInfo {
    InputCellInfo {
        input: CellInput::new_builder()
            .previous_output(cell.out_point.clone())
            .build(),
        cell,
    }
}

fn into_input_cell_since(cell: CellInfo, since: u64) -> InputCellInfo {
    InputCellInfo {
        input: CellInput::new_builder()
            .previous_output(cell.out_point.clone())
            .since(since.pack())
            .build(),
        cell,
    }
}

fn random_always_success_script(opt_rollup_script_hash: Option<&H256>) -> Script {
    let random_bytes: [u8; 20] = rand::random();
    Script::new_builder()
        .code_hash(ALWAYS_SUCCESS_CODE_HASH.clone().pack())
        .hash_type(ScriptHashType::Data.into())
        .args({
            let mut args = opt_rollup_script_hash
                .map(|h| h.as_slice().to_vec())
                .unwrap_or_default();
            args.extend_from_slice(&random_bytes);
            args.pack()
        })
        .build()
}
