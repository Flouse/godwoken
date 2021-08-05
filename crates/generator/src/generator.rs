use crate::{
    account_lock_manage::AccountLockManage,
    backend_manage::BackendManage,
    constants::{L2TX_MAX_CYCLES, MAX_READ_DATA_BYTES_LIMIT, MAX_WRITE_DATA_BYTES_LIMIT},
    error::{TransactionValidateError, WithdrawalError},
    vm_cost_model::instruction_cycles,
};
use crate::{
    backend_manage::Backend,
    error::{Error, TransactionError},
    sudt::build_l2_sudt_script,
};
use crate::{error::AccountError, syscalls::L2Syscalls};
use crate::{error::LockAlgorithmError, traits::StateExt};
use gw_common::{
    builtins::CKB_SUDT_ACCOUNT_ID,
    error::Error as StateError,
    h256_ext::H256Ext,
    state::{build_account_field_key, to_short_address, State, GW_ACCOUNT_NONCE_TYPE},
    H256,
};
use gw_traits::{ChainStore, CodeStore};
use gw_types::{
    bytes::Bytes,
    core::{ChallengeTargetType, ScriptHashType},
    offchain::{RollupContext, RunResult},
    packed::{
        AccountMerkleState, BlockInfo, CellOutput, ChallengeTarget, DepositRequest, L2Block,
        L2Transaction, RawL2Block, RawL2Transaction, Script, TxReceipt, WithdrawalLockArgs,
        WithdrawalReceipt, WithdrawalRequest,
    },
    prelude::*,
};

// use gw_types::bytes::Bytes;
use ckb_vm::{
    machine::asm::{AsmCoreMachine, AsmMachine},
    CoreMachine, DefaultMachineBuilder, Machine, Register, SupportMachine,
};
use core::ops::Deref;
use std::rc::Rc;

pub struct StateTransitionArgs {
    pub l2block: L2Block,
    pub deposit_requests: Vec<DepositRequest>,
}

pub enum StateTransitionResult {
    Success {
        withdrawal_receipts: Vec<WithdrawalReceipt>,
        prev_txs_state: AccountMerkleState,
        tx_receipts: Vec<TxReceipt>,
        offchain_used_cycles: u64,
    },
    Challenge {
        target: ChallengeTarget,
        error: Error,
    },
    Error(Error),
}

pub struct Generator {
    backend_manage: BackendManage,
    account_lock_manage: AccountLockManage,
    rollup_context: RollupContext,
}

impl Generator {
    pub fn new(
        backend_manage: BackendManage,
        account_lock_manage: AccountLockManage,
        rollup_context: RollupContext,
    ) -> Self {
        Generator {
            backend_manage,
            account_lock_manage,
            rollup_context,
        }
    }

    pub fn rollup_context(&self) -> &RollupContext {
        &self.rollup_context
    }

    pub fn account_lock_manage(&self) -> &AccountLockManage {
        &self.account_lock_manage
    }

    /// Verify withdrawal request
    /// Notice this function do not perform signature check
    pub fn verify_withdrawal_request<S: State + CodeStore>(
        &self,
        state: &S,
        withdrawal_request: &WithdrawalRequest,
        asset_script: Option<Script>,
    ) -> Result<(), Error> {
        let raw = withdrawal_request.raw();
        let account_script_hash: H256 = raw.account_script_hash().unpack();
        let sudt_script_hash: H256 = raw.sudt_script_hash().unpack();
        let amount: u128 = raw.amount().unpack();
        let capacity: u64 = raw.capacity().unpack();
        let fee = raw.fee();
        let fee_sudt_id: u32 = fee.sudt_id().unpack();
        let fee_amount: u128 = fee.amount().unpack();
        let account_short_address = to_short_address(&account_script_hash);

        // check capacity (use dummy block hash and number)
        let rollup_context = self.rollup_context();
        if let Err(min_capacity) = Self::build_withdrawal_cell_output(
            rollup_context,
            withdrawal_request,
            &H256::one(),
            1,
            asset_script,
        ) {
            return Err(AccountError::InsufficientCapacity {
                expected: min_capacity,
                actual: capacity,
            }
            .into());
        }

        // find user account
        let id = state
            .get_account_id_by_script_hash(&account_script_hash)?
            .ok_or(AccountError::UnknownAccount)?; // find Simple UDT account

        // check CKB balance
        let ckb_balance = state.get_sudt_balance(CKB_SUDT_ACCOUNT_ID, account_short_address)?;
        let required_ckb_capacity = {
            let mut required_capacity = capacity as u128;
            // Count withdrawal fee
            if fee_sudt_id == CKB_SUDT_ACCOUNT_ID {
                required_capacity = required_capacity.saturating_add(fee_amount);
            }
            required_capacity
        };
        if required_ckb_capacity > ckb_balance {
            return Err(WithdrawalError::Overdraft.into());
        }
        let l2_sudt_script_hash =
            build_l2_sudt_script(&self.rollup_context, &sudt_script_hash).hash();
        let sudt_id = state
            .get_account_id_by_script_hash(&l2_sudt_script_hash.into())?
            .ok_or(AccountError::UnknownSUDT)?;
        // The sUDT id must not be equals to the CKB sUDT id if amount isn't 0
        if sudt_id != CKB_SUDT_ACCOUNT_ID {
            // check SUDT balance
            // user can't withdrawal 0 SUDT when non-CKB sudt_id exists
            if amount == 0 {
                return Err(WithdrawalError::NonPositiveSUDTAmount.into());
            }
            let mut required_amount = amount;
            if sudt_id == fee_sudt_id {
                required_amount = required_amount.saturating_add(fee_amount);
            }
            let balance = state.get_sudt_balance(sudt_id, account_short_address)?;
            if required_amount > balance {
                return Err(WithdrawalError::Overdraft.into());
            }
        } else if amount != 0 {
            // user can't withdrawal CKB token via SUDT fields
            return Err(WithdrawalError::WithdrawFakedCKB.into());
        }

        // check fees if it isn't been cheked yet
        if fee_sudt_id != CKB_SUDT_ACCOUNT_ID && fee_sudt_id != sudt_id && fee_amount > 0 {
            let balance = state.get_sudt_balance(fee_sudt_id, account_short_address)?;
            if fee_amount > balance {
                return Err(WithdrawalError::Overdraft.into());
            }
        }

        // check nonce
        let expected_nonce = state.get_nonce(id)?;
        let actual_nonce: u32 = raw.nonce().unpack();
        if actual_nonce != expected_nonce {
            return Err(WithdrawalError::Nonce {
                expected: expected_nonce,
                actual: actual_nonce,
            }
            .into());
        }
        Ok(())
    }

    /// Check withdrawal request signature
    pub fn check_withdrawal_request_signature<S: State + CodeStore>(
        &self,
        state: &S,
        withdrawal_request: &WithdrawalRequest,
    ) -> Result<(), Error> {
        let raw = withdrawal_request.raw();
        let account_script_hash: [u8; 32] = raw.account_script_hash().unpack();

        // check signature
        let account_script = state
            .get_script(&account_script_hash.into())
            .ok_or(StateError::MissingKey)?;
        let lock_code_hash: [u8; 32] = account_script.code_hash().unpack();
        let lock_algo = self
            .account_lock_manage
            .get_lock_algorithm(&lock_code_hash.into())
            .ok_or(LockAlgorithmError::UnknownAccountLock)?;

        let message = raw.calc_message(&self.rollup_context.rollup_script_hash);
        let valid_signature = lock_algo.verify_message(
            account_script.args().unpack(),
            withdrawal_request.signature().unpack(),
            message,
        )?;

        if !valid_signature {
            return Err(LockAlgorithmError::InvalidSignature.into());
        }

        Ok(())
    }

    /// verify transaction
    /// Notice this function do not perform signature check
    pub fn verify_transaction<S: State + CodeStore>(
        &self,
        state: &S,
        tx: &L2Transaction,
    ) -> Result<(), TransactionValidateError> {
        let raw_tx = tx.raw();
        let sender_id: u32 = raw_tx.from_id().unpack();

        // verify nonce
        let account_nonce: u32 = state.get_nonce(sender_id)?;
        let nonce: u32 = raw_tx.nonce().unpack();
        if nonce != account_nonce {
            return Err(TransactionError::Nonce {
                expected: account_nonce,
                actual: nonce,
            }
            .into());
        }

        Ok(())
    }

    // Check transaction signature
    pub fn check_transaction_signature<S: State + CodeStore>(
        &self,
        state: &S,
        tx: &L2Transaction,
    ) -> Result<(), TransactionValidateError> {
        let raw_tx = tx.raw();
        let sender_id: u32 = raw_tx.from_id().unpack();
        let receiver_id: u32 = raw_tx.to_id().unpack();

        // verify signature
        let script_hash = state.get_script_hash(sender_id)?;
        if script_hash.is_zero() {
            return Err(AccountError::ScriptNotFound {
                account_id: sender_id,
            }
            .into());
        }
        let script = state.get_script(&script_hash).expect("get script");
        let lock_code_hash: [u8; 32] = script.code_hash().unpack();

        let receiver_script_hash = state.get_script_hash(receiver_id)?;
        if receiver_script_hash.is_zero() {
            return Err(AccountError::ScriptNotFound {
                account_id: receiver_id,
            }
            .into());
        }
        let receiver_script = state
            .get_script(&receiver_script_hash)
            .expect("get receiver script");

        let lock_algo = self
            .account_lock_manage()
            .get_lock_algorithm(&lock_code_hash.into())
            .ok_or(LockAlgorithmError::UnknownAccountLock)?;
        let valid_signature =
            lock_algo.verify_tx(&self.rollup_context, script, receiver_script, &tx)?;
        if !valid_signature {
            return Err(LockAlgorithmError::InvalidSignature.into());
        }
        Ok(())
    }

    /// Apply l2 state transition
    pub fn verify_and_apply_state_transition<S: State + CodeStore, C: ChainStore>(
        &self,
        chain: &C,
        state: &mut S,
        args: StateTransitionArgs,
    ) -> StateTransitionResult {
        let raw_block = args.l2block.raw();
        let block_info = get_block_info(&raw_block);

        // apply withdrawal to state
        let withdrawal_requests: Vec<_> = args.l2block.withdrawals().into_iter().collect();
        let block_hash = raw_block.hash();
        let block_producer_id: u32 = block_info.block_producer_id().unpack();

        let mut withdrawal_receipts = Vec::with_capacity(withdrawal_requests.len());
        for (wth_idx, request) in withdrawal_requests.into_iter().enumerate() {
            if let Err(error) = self.check_withdrawal_request_signature(state, &request) {
                let target = build_challenge_target(
                    block_hash.into(),
                    ChallengeTargetType::Withdrawal,
                    wth_idx as u32,
                );

                return StateTransitionResult::Challenge { target, error };
            }

            match state.apply_withdrawal_request(&self.rollup_context, block_producer_id, &request)
            {
                Ok(withdrawal_receipt) => withdrawal_receipts.push(withdrawal_receipt),
                Err(err) => return StateTransitionResult::Error(err),
            }
        }

        // apply deposition to state
        if let Err(err) = state.apply_deposit_requests(&self.rollup_context, &args.deposit_requests)
        {
            return StateTransitionResult::Error(err);
        }

        let prev_txs_state = {
            let (account_root, account_count) =
                match (|| Ok((state.calculate_root()?, state.get_account_count()?)))() {
                    Err(err) => return StateTransitionResult::Error(err),
                    Ok((root, count)) => (root, count),
                };

            AccountMerkleState::new_builder()
                .merkle_root(account_root.pack())
                .count(account_count.pack())
                .build()
        };

        // handle transactions
        let mut offchain_used_cycles: u64 = 0;
        let mut tx_receipts = Vec::with_capacity(args.l2block.transactions().len());
        for (tx_index, tx) in args.l2block.transactions().into_iter().enumerate() {
            if let Err(err) = self.check_transaction_signature(state, &tx) {
                let target = build_challenge_target(
                    block_hash.into(),
                    ChallengeTargetType::TxSignature,
                    tx_index as u32,
                );

                return StateTransitionResult::Challenge {
                    target,
                    error: err.into(),
                };
            }

            // check nonce
            let raw_tx = tx.raw();
            let expected_nonce = match state.get_nonce(raw_tx.from_id().unpack()) {
                Err(err) => return StateTransitionResult::Error(Error::from(err)),
                Ok(nonce) => nonce,
            };
            let actual_nonce: u32 = raw_tx.nonce().unpack();
            if actual_nonce != expected_nonce {
                return StateTransitionResult::Challenge {
                    target: build_challenge_target(
                        block_hash.into(),
                        ChallengeTargetType::TxExecution,
                        tx_index as u32,
                    ),
                    error: Error::Transaction(TransactionError::Nonce {
                        expected: expected_nonce,
                        actual: actual_nonce,
                    }),
                };
            }

            // build call context
            // NOTICE users only allowed to send HandleMessage CallType txs
            let run_result =
                match self.execute_transaction(chain, state, &block_info, &raw_tx, L2TX_MAX_CYCLES)
                {
                    Ok(run_result) => run_result,
                    Err(err) => {
                        let target = build_challenge_target(
                            block_hash.into(),
                            ChallengeTargetType::TxExecution,
                            tx_index as u32,
                        );

                        return StateTransitionResult::Challenge {
                            target,
                            error: Error::Transaction(err),
                        };
                    }
                };

            let apply_result = || -> Result<(), Error> {
                state.apply_run_result(&run_result)?;

                let used_cycles = run_result.used_cycles;
                let post_state = state.merkle_state()?;
                let tx_receipt =
                    TxReceipt::build_receipt(tx.witness_hash().into(), run_result, post_state);

                tx_receipts.push(tx_receipt);
                offchain_used_cycles = offchain_used_cycles.saturating_add(used_cycles);
                Ok(())
            };

            if let Err(err) = apply_result() {
                return StateTransitionResult::Error(err);
            }
        }

        StateTransitionResult::Success {
            withdrawal_receipts,
            prev_txs_state,
            tx_receipts,
            offchain_used_cycles,
        }
    }

    fn load_backend<S: State + CodeStore>(&self, state: &S, script_hash: &H256) -> Option<Backend> {
        log::debug!(
            "load_backend for script_hash: {}",
            hex::encode(script_hash.as_slice())
        );
        state
            .get_script(&script_hash)
            .and_then(|script| {
                // only accept type script hash type for now
                if script.hash_type() == ScriptHashType::Type.into() {
                    let code_hash: [u8; 32] = script.code_hash().unpack();
                    log::debug!("load_backend by code_hash: {}", hex::encode(code_hash));
                    self.backend_manage.get_backend(&code_hash.into())
                } else {
                    log::error!(
                        "Found a invalid account script which hash_type is data: {:?}",
                        script
                    );
                    None
                }
            })
            .cloned()
    }

    /// execute a layer2 tx
    pub fn execute_transaction<S: State + CodeStore, C: ChainStore>(
        &self,
        chain: &C,
        state: &S,
        block_info: &BlockInfo,
        raw_tx: &RawL2Transaction,
        max_cycles: u64,
    ) -> Result<RunResult, TransactionError> {
        let sender_id: u32 = raw_tx.from_id().unpack();
        let nonce_before_execution = state.get_nonce(sender_id)?;

        let mut run_result = RunResult::default();
        // let used_cycles;
        {
            // let core_machine = AsmCoreMachine::new_with_max_cycles(L2TX_MAX_CYCLES);
            let core_machine = AsmCoreMachine::new(
                ckb_vm::ISA_IMC | ckb_vm::ISA_B | ckb_vm::ISA_MOP,
                ckb_vm::machine::VERSION1,
                u64::MAX,
            );

            let machine_builder = DefaultMachineBuilder::new(core_machine)
                .syscall(Box::new(L2Syscalls {
                    chain,
                    state,
                    block_info,
                    raw_tx,
                    rollup_context: &self.rollup_context,
                    account_lock_manage: &self.account_lock_manage,
                    result: &mut run_result,
                    code_store: state,
                }))
                .instruction_cycle_func(Box::new(instruction_cycles));

            let asm_machine = AsmMachine::new(machine_builder.build(), None);
            let mut machine = PProfMachine::new(asm_machine);

            let account_id = raw_tx.to_id().unpack();
            let script_hash = state.get_script_hash(account_id)?;
            let backend = self
                .load_backend(state, &script_hash)
                .ok_or(TransactionError::BackendNotFound { script_hash })?;

            // machine.load_program(&backend.generator, &[])?;
            machine.load_program(
                &ckb_vm::Bytes::copy_from_slice(backend.generator.deref()),
                &[],
            )?;
            let code = machine.run()?;

            // pprof_logger
            let mut output = std::fs::File::create(format!(
                "target/pprof{}_{}",
                nonce_before_execution, account_id
            ))
            .expect("can't create file");
            machine
                .pprof_logger
                .unwrap()
                .tree_root
                .borrow()
                .display_flamegraph("", &mut output);

            if code != 0 {
                return Err(TransactionError::InvalidExitCode(code));
            }
            // used_cycles = machine.machine.cycles();
        }
        // record used cycles
        // run_result.used_cycles = used_cycles;

        // check nonce is increased by backends
        let nonce_after_execution = {
            let nonce_raw_key = build_account_field_key(sender_id, GW_ACCOUNT_NONCE_TYPE);
            let value = run_result
                .write_values
                .get(&nonce_raw_key)
                .expect("Backend must update nonce");
            value.to_u32()
        };
        assert!(
            nonce_after_execution > nonce_before_execution,
            "nonce should increased by backends"
        );

        // check write data bytes
        let write_data_bytes: usize = run_result.write_data.values().map(|data| data.len()).sum();
        if write_data_bytes > MAX_WRITE_DATA_BYTES_LIMIT {
            return Err(TransactionError::ExceededMaxWriteData {
                max_bytes: MAX_WRITE_DATA_BYTES_LIMIT,
                used_bytes: write_data_bytes,
            });
        }
        // check read data bytes
        let read_data_bytes: usize = run_result.read_data.values().map(Vec::len).sum();
        if read_data_bytes > MAX_READ_DATA_BYTES_LIMIT {
            return Err(TransactionError::ExceededMaxReadData {
                max_bytes: MAX_READ_DATA_BYTES_LIMIT,
                used_bytes: read_data_bytes,
            });
        }

        Ok(run_result)
    }

    pub fn build_withdrawal_cell_output(
        rollup_context: &RollupContext,
        req: &WithdrawalRequest,
        block_hash: &H256,
        block_number: u64,
        asset_script: Option<Script>,
    ) -> Result<(CellOutput, Bytes), u128> {
        let withdrawal_capacity: u64 = req.raw().capacity().unpack();
        let lock_args: Bytes = {
            let withdrawal_lock_args = WithdrawalLockArgs::new_builder()
                .account_script_hash(req.raw().account_script_hash())
                .withdrawal_block_hash(Into::<[u8; 32]>::into(*block_hash).pack())
                .withdrawal_block_number(block_number.pack())
                .sudt_script_hash(req.raw().sudt_script_hash())
                .sell_amount(req.raw().sell_amount())
                .sell_capacity(withdrawal_capacity.pack())
                .owner_lock_hash(req.raw().owner_lock_hash())
                .payment_lock_hash(req.raw().payment_lock_hash())
                .build();

            let rollup_type_hash = rollup_context.rollup_script_hash.as_slice().iter();
            rollup_type_hash
                .chain(withdrawal_lock_args.as_slice().iter())
                .cloned()
                .collect()
        };

        let lock = Script::new_builder()
            .code_hash(rollup_context.rollup_config.withdrawal_script_type_hash())
            .hash_type(ScriptHashType::Type.into())
            .args(lock_args.pack())
            .build();

        let (type_, data) = match asset_script {
            Some(type_) => (Some(type_).pack(), req.raw().amount().as_bytes()),
            None => (None::<Script>.pack(), Bytes::new()),
        };

        let output = CellOutput::new_builder()
            .capacity(withdrawal_capacity.pack())
            .type_(type_)
            .lock(lock)
            .build();

        match output.occupied_capacity(data.len()) {
            Ok(min_capacity) if min_capacity > withdrawal_capacity => {
                return Err(min_capacity as u128)
            }
            Err(err) => {
                log::debug!("calculate withdrawal capacity {}", err); // Overflow
                return Err(u64::MAX as u128 + 1);
            }
            _ => (),
        }

        Ok((output, data))
    }
}

fn get_block_info(l2block: &RawL2Block) -> BlockInfo {
    BlockInfo::new_builder()
        .block_producer_id(l2block.block_producer_id())
        .number(l2block.number())
        .timestamp(l2block.timestamp())
        .build()
}

fn build_challenge_target(
    block_hash: H256,
    target_type: ChallengeTargetType,
    target_index: u32,
) -> ChallengeTarget {
    let target_type: u8 = target_type.into();
    ChallengeTarget::new_builder()
        .block_hash(block_hash.pack())
        .target_index(target_index.pack())
        .target_type(target_type.into())
        .build()
}

// Use tree structure to store ckb vm's runtime data. At present, we care about cycles, but we may add other things in
// the future, for example, the number of times a certain instruction appears.
#[derive(Clone, Debug)]
struct PProfRecordTreeNode {
    name: String, // FILENAME + FUNCTION_NAME as expected.
    parent: Option<Rc<std::cell::RefCell<PProfRecordTreeNode>>>,
    childs: Vec<Rc<std::cell::RefCell<PProfRecordTreeNode>>>,
    cycles: u64,
}

impl PProfRecordTreeNode {
    // Create a new PProfRecordTreeNode with a user defined name(e.g. Function name).
    fn root() -> Self {
        Self {
            name: String::from("??:??"),
            parent: None,
            childs: vec![],
            cycles: 0,
        }
    }

    fn display_flamegraph(&self, prefix: &str, writer: &mut impl std::io::Write) {
        let prefix_name = prefix.to_owned() + self.name.as_str();
        writer
            .write_all(format!("{} {}\n", prefix_name, self.cycles).as_bytes())
            .unwrap();
        for e in &self.childs {
            e.borrow()
                .display_flamegraph(&(prefix_name.as_str().to_owned() + "; "), writer);
        }
    }
}

fn sprint_loc_file(loc: &Option<addr2line::Location>) -> String {
    if let Some(ref loc) = *loc {
        let file = loc.file.as_ref().unwrap();
        let path = std::path::Path::new(file);
        path.display().to_string()
    } else {
        String::from("??")
    }
}

fn sprint_fun(
    mut frame_iter: addr2line::FrameIter<
        addr2line::gimli::EndianReader<addr2line::gimli::RunTimeEndian, std::rc::Rc<[u8]>>,
    >,
) -> String {
    let mut stack: Vec<String> = vec![String::from("??")];
    loop {
        let frame = frame_iter.next().unwrap();
        if frame.is_none() {
            break;
        }
        let frame = frame.unwrap();
        let function = frame.function.unwrap();
        // TODO(clippy::useless_conversion): consider removing `std::borrow::Cow::from()`: `function.raw_name().unwrap()`
        let function_name = String::from(addr2line::demangle_auto(
            std::borrow::Cow::from(function.raw_name().unwrap()),
            function.language,
        ));

        stack.push(function_name)
    }
    stack.last().unwrap().to_string()
}

// Main handler.
pub struct PProfLogger {
    atsl_context: addr2line::Context<
        addr2line::gimli::EndianReader<addr2line::gimli::RunTimeEndian, std::rc::Rc<[u8]>>,
    >,
    tree_root: Rc<std::cell::RefCell<PProfRecordTreeNode>>,
    tree_node: Rc<std::cell::RefCell<PProfRecordTreeNode>>,
    ra_dict: std::collections::HashMap<u64, Rc<std::cell::RefCell<PProfRecordTreeNode>>>,
    // output_filename: String,
}

impl PProfLogger {
    pub fn from_path(filename: String) -> Result<Self, Box<dyn std::error::Error>> {
        let file = std::fs::File::open(filename)?;
        let mmap = unsafe { memmap::Mmap::map(&file)? };
        let object = object::File::parse(&*mmap)?;
        let ctx = addr2line::Context::new(&object)?;
        let tree_root = Rc::new(std::cell::RefCell::new(PProfRecordTreeNode::root()));
        Ok(Self {
            atsl_context: ctx,
            tree_root: tree_root.clone(),
            tree_node: tree_root,
            ra_dict: std::collections::HashMap::new(),
        })
    }
    pub fn from_data(program: &ckb_vm::Bytes) -> Result<Self, Box<dyn std::error::Error>> {
        let object = object::File::parse(&program)?;
        let ctx = addr2line::Context::new(&object)?;
        let tree_root = Rc::new(std::cell::RefCell::new(PProfRecordTreeNode::root()));
        Ok(Self {
            atsl_context: ctx,
            tree_root: tree_root.clone(),
            tree_node: tree_root,
            ra_dict: std::collections::HashMap::new(),
        })
    }
}

impl PProfLogger {
    fn on_step_old<'a>(&mut self, machine: &mut AsmMachine<'a>) {
        let pc = machine.machine.pc().to_u64();
        let mut decoder = ckb_vm::decoder::build_decoder::<u64>(machine.machine.isa());
        let inst = decoder.decode(machine.machine.memory_mut(), pc).unwrap();
        let inst_length = ckb_vm::instructions::instruction_length(inst) as u64;
        let opcode = ckb_vm::instructions::extract_opcode(inst);
        let cycles = machine
            .machine
            .instruction_cycle_func()
            .as_ref()
            .map(|f| f(inst))
            .unwrap_or(0);
        self.tree_node.borrow_mut().cycles += cycles;

        let call = |s: &mut Self, addr: u64, link: u64| {
            let loc = s.atsl_context.find_location(addr).unwrap();
            let loc_string = sprint_loc_file(&loc);
            let frame_iter = s.atsl_context.find_frames(addr).unwrap();
            let fun_string = sprint_fun(frame_iter);
            let tag_string = format!("{}:{}", loc_string, fun_string);
            let chd = Rc::new(std::cell::RefCell::new(PProfRecordTreeNode {
                name: tag_string,
                parent: Some(s.tree_node.clone()),
                childs: vec![],
                cycles: 0,
            }));
            s.tree_node.borrow_mut().childs.push(chd.clone());
            s.ra_dict.insert(link, s.tree_node.clone());
            s.tree_node = chd;
        };

        if opcode == ckb_vm::instructions::insts::OP_JAL {
            let inst = ckb_vm::instructions::Utype(inst);
            // The standard software calling convention uses x1 as the return address register and x5 as an alternate
            // link register.
            if inst.rd() == ckb_vm::registers::RA || inst.rd() == ckb_vm::registers::T0 {
                let addr = pc.wrapping_add(inst.immediate_s() as u64) & 0xfffffffffffffffe;
                let link = pc + inst_length;
                call(self, addr, link);
            }
        };
        if opcode == ckb_vm::instructions::insts::OP_JALR {
            let inst = ckb_vm::instructions::Itype(inst);
            let base = machine.machine.registers()[inst.rs1()].to_u64();
            let addr = base.wrapping_add(inst.immediate_s() as u64) & 0xfffffffffffffffe;
            let link = pc + inst_length;
            if self.ra_dict.contains_key(&addr) {
                self.tree_node = self.ra_dict.get(&addr).unwrap().clone();
            } else {
                call(self, addr, link);
            }
        };
        if opcode == ckb_vm::instructions::insts::OP_FAR_JUMP_ABS {
            let inst = ckb_vm::instructions::Utype(inst);
            let addr = (inst.immediate_s() as u64) & 0xfffffffffffffffe;
            let link = pc + inst_length;
            if self.ra_dict.contains_key(&addr) {
                self.tree_node = self.ra_dict.get(&addr).unwrap().clone();
            } else {
                call(self, addr, link);
            }
        }
        if opcode == ckb_vm::instructions::insts::OP_FAR_JUMP_REL {
            let inst = ckb_vm::instructions::Utype(inst);
            let addr = pc.wrapping_add(inst.immediate_s() as u64) & 0xfffffffffffffffe;
            let link = pc + inst_length;
            if self.ra_dict.contains_key(&addr) {
                self.tree_node = self.ra_dict.get(&addr).unwrap().clone();
            } else {
                call(self, addr, link);
            }
        }
    }
}

/// ckb-vm-pprof-machine
pub struct PProfMachine<'a> {
    pub machine: AsmMachine<'a>,
    pprof_logger: Option<PProfLogger>,
}

impl CoreMachine for PProfMachine<'_> {
    type REG = u64;
    type MEM = Box<AsmCoreMachine>;

    fn pc(&self) -> &Self::REG {
        &self.machine.machine.pc()
    }

    fn update_pc(&mut self, pc: Self::REG) {
        self.machine.machine.update_pc(pc)
    }

    fn commit_pc(&mut self) {
        self.machine.machine.commit_pc()
    }

    fn memory(&self) -> &Self::MEM {
        self.machine.machine.memory()
    }

    fn memory_mut(&mut self) -> &mut Self::MEM {
        self.machine.machine.memory_mut()
    }

    fn registers(&self) -> &[Self::REG] {
        self.machine.machine.registers()
    }

    fn set_register(&mut self, idx: usize, value: Self::REG) {
        self.machine.machine.set_register(idx, value)
    }

    fn isa(&self) -> u8 {
        self.machine.machine.isa()
    }

    fn version(&self) -> u32 {
        self.machine.machine.version()
    }
}

impl Machine for PProfMachine<'_> {
    fn ecall(&mut self) -> Result<(), ckb_vm::Error> {
        self.machine.machine.ecall()
    }

    fn ebreak(&mut self) -> Result<(), ckb_vm::Error> {
        self.machine.machine.ebreak()
    }
}

impl<'a> PProfMachine<'a> {
    pub fn new(machine: AsmMachine<'a>) -> Self {
        Self {
            machine,
            pprof_logger: None,
        }
    }

    pub fn load_program(
        &mut self,
        program: &ckb_vm::Bytes,
        args: &[ckb_vm::Bytes],
    ) -> Result<u64, ckb_vm::Error> {
        self.pprof_logger =
            Some(PProfLogger::from_data(program).or(Err(ckb_vm::Error::ParseError))?);
        self.machine.load_program(program, args)
    }

    pub fn run(&mut self) -> Result<i8, ckb_vm::Error> {
        let mut decoder = ckb_vm::decoder::build_decoder::<u64>(self.isa());
        self.machine.machine.set_running(true);
        if let Some(pprof_logger) = self.pprof_logger.as_mut() {
            while self.machine.machine.running() {
                pprof_logger.on_step_old(&mut self.machine);
                self.machine.step(&mut decoder)?;
            }
        } else {
            unreachable!();
        }
        Ok(self.machine.machine.exit_code())
    }
}
