use std::collections::HashSet;
use std::iter::FromIterator;
use std::ops::Sub;
use std::path::Path;
use std::str::FromStr;

use anyhow::{anyhow, Context, Result};
use ckb_types::bytes::{BufMut, BytesMut};
use gw_jsonrpc_types::JsonCalcHash;
use gw_rpc_client::ckb_client::CkbClient;
use tempfile::NamedTempFile;

use crate::utils::sdk::{
    constants::{MIN_SECP_CELL_CAPACITY, ONE_CKB},
    traits::DefaultCellDepResolver,
    util::get_max_mature_number,
    Address, AddressPayload, HumanCapacity,
};
use ckb_fixed_hash::H256;
use ckb_hash::new_blake2b;
use ckb_jsonrpc_types as rpc_types;
use ckb_resource::CODE_HASH_SECP256K1_DATA;
use ckb_types::{
    bytes::Bytes,
    core::{BlockView, Capacity, DepType, ScriptHashType, TransactionBuilder, TransactionView},
    packed as ckb_packed,
};
use gw_config::GenesisConfig;
use gw_generator::genesis::build_genesis;
use gw_types::{
    core::{AllowedContractType, AllowedEoaType},
    packed as gw_packed,
    packed::RollupConfig,
    prelude::{Pack as CKBPack, Unpack as CKBUnpack, *},
};

use crate::types::{
    OmniLockConfig, RollupDeploymentResult, ScriptsDeploymentResult, UserRollupConfig,
};
use crate::utils::transaction::{get_network_type, run_cmd};

use std::time::{SystemTime, UNIX_EPOCH};

struct GenesisInfo(DefaultCellDepResolver);

struct DeployContext<'a> {
    privkey_path: &'a Path,
    owner_address: &'a Address,
    genesis_info: &'a GenesisInfo,
    deployment_result: &'a ScriptsDeploymentResult,
    ckb_client: &'a CkbClient,
}

impl<'a> DeployContext<'a> {
    async fn deploy(
        &mut self,
        mut outputs: Vec<ckb_packed::CellOutput>,
        mut outputs_data: Vec<Bytes>,
        mut deps: Vec<ckb_packed::CellDep>,
        first_cell_input: Option<&ckb_packed::CellInput>,
        witness_0: ckb_packed::WitnessArgs,
    ) -> Result<H256> {
        let tx_fee = ONE_CKB;
        let total_output_capacity: u64 = outputs
            .iter()
            .map(|output| {
                let value: u64 = CKBUnpack::unpack(&output.capacity());
                value
            })
            .sum();
        let total_capacity = total_output_capacity + tx_fee;
        let tip_number = self.ckb_client.get_tip_block_number().await?;
        let max_mature_number = get_max_mature_number(self.ckb_client).await?;
        let (inputs, total_input_capacity) = collect_live_cells(
            self.ckb_client.url(),
            self.owner_address.to_string().as_str(),
            max_mature_number,
            tip_number.into(),
            total_capacity,
        )?;
        if let Some(first_input) = first_cell_input {
            if inputs[0].as_slice() != first_input.as_slice() {
                return Err(anyhow!("first input cell changed"));
            }
        }
        // collect_live_cells will ensure `total_input_capacity >= total_capacity`.
        let rest_capacity = total_input_capacity - total_capacity;
        let max_tx_fee_str = if rest_capacity >= MIN_SECP_CELL_CAPACITY {
            outputs.push(
                ckb_packed::CellOutput::new_builder()
                    .lock(ckb_packed::Script::from(self.owner_address.payload()))
                    .capacity(CKBPack::pack(&rest_capacity))
                    .build(),
            );
            outputs_data.push(Default::default());
            "1.0"
        } else {
            "62.0"
        };
        let outputs_data: Vec<ckb_packed::Bytes> = outputs_data.iter().map(CKBPack::pack).collect();
        deps.extend_from_slice(&[
            self.deployment_result
                .state_validator
                .cell_dep
                .clone()
                .into(),
            self.genesis_info
                .0
                .sighash_dep()
                .context("genesis sighash dep")?
                .0
                .to_owned(),
        ]);
        let tx: TransactionView = TransactionBuilder::default()
            .cell_deps(deps)
            .set_inputs(inputs)
            .set_outputs(outputs)
            .set_outputs_data(outputs_data)
            .set_witnesses(vec![CKBPack::pack(&witness_0.as_bytes())])
            .build();

        // 7. build ckb-cli tx and sign
        let tx_file = NamedTempFile::new()?;
        let tx_path_str = tx_file.path().to_str().unwrap();
        let _output = run_cmd(&[
            "--url",
            self.ckb_client.url(),
            "tx",
            "init",
            "--tx-file",
            tx_path_str,
        ])?;
        let tx_json = rpc_types::Transaction::from(tx.data());
        let tx_body: serde_json::Value = serde_json::to_value(&tx_json).unwrap();
        let cli_tx_content = std::fs::read_to_string(tx_path_str).unwrap();
        let mut cli_tx: serde_json::Value = serde_json::from_str(&cli_tx_content).unwrap();
        cli_tx["transaction"] = tx_body;
        let cli_tx_content = serde_json::to_string_pretty(&cli_tx).unwrap();
        std::fs::write(tx_path_str, cli_tx_content.as_bytes())?;
        let _output = run_cmd(&[
            "--url",
            self.ckb_client.url(),
            "tx",
            "sign-inputs",
            "--privkey-path",
            self.privkey_path.to_str().expect("non-utf8 file path"),
            "--tx-file",
            tx_path_str,
            "--add-signatures",
        ])?;

        // 8. send and then wait for tx
        let send_output = run_cmd(&[
            "--url",
            self.ckb_client.url(),
            "tx",
            "send",
            "--tx-file",
            tx_path_str,
            "--max-tx-fee",
            max_tx_fee_str,
            "--skip-check",
        ])?;
        let tx_hash = H256::from_str(send_output.trim().trim_start_matches("0x"))?;
        log::info!("tx_hash: {:#x}", tx_hash);
        self.ckb_client
            .wait_tx_committed_with_timeout_and_logging(tx_hash.0, 600)
            .await?;
        Ok(tx_hash)
    }
}

pub struct DeployRollupCellArgs<'a> {
    pub privkey_path: &'a Path,
    pub ckb_rpc_url: &'a str,
    pub scripts_result: &'a ScriptsDeploymentResult,
    pub user_rollup_config: &'a UserRollupConfig,
    pub omni_lock_config: &'a OmniLockConfig,
    pub timestamp: Option<u64>,
    pub skip_config_check: bool,
}

pub async fn deploy_rollup_cell(args: DeployRollupCellArgs<'_>) -> Result<RollupDeploymentResult> {
    let DeployRollupCellArgs {
        privkey_path,
        ckb_rpc_url,
        scripts_result,
        user_rollup_config,
        omni_lock_config,
        timestamp,
        skip_config_check,
    } = args;

    let burn_lock_hash: H256 = user_rollup_config.burn_lock.hash();
    // check config
    if !skip_config_check {
        let expected_burn_lock_script = ckb_packed::Script::new_builder()
            .code_hash(CKBPack::pack(&[0u8; 32]))
            .hash_type(ScriptHashType::Data.into())
            .build();
        let expected_burn_lock_hash: H256 = expected_burn_lock_script.calc_script_hash().unpack();
        if expected_burn_lock_hash != burn_lock_hash {
            return Err(anyhow!(
                "The burn lock hash: 0x{:x} is not default, we suggest to use default burn lock \
                0x{:x} (code_hash: 0x, hash_type: Data, args: empty)",
                burn_lock_hash,
                expected_burn_lock_hash
            ));
        }
    }

    let ckb_client = gw_rpc_client::ckb_client::CkbClient::with_url(ckb_rpc_url)?;
    let network_type = get_network_type(&ckb_client).await?;
    let privkey_string = std::fs::read_to_string(privkey_path)?
        .split_whitespace()
        .next()
        .map(ToOwned::to_owned)
        .ok_or_else(|| anyhow!("File is empty"))?;
    let privkey_data = H256::from_str(privkey_string.trim().trim_start_matches("0x"))?;
    let privkey = secp256k1::SecretKey::from_slice(privkey_data.as_bytes())
        .map_err(|err| anyhow!("Invalid secp256k1 secret key format, error: {}", err))?;
    let pubkey = secp256k1::PublicKey::from_secret_key(&secp256k1::Secp256k1::new(), &privkey);
    let owner_address_payload = AddressPayload::from_pubkey(&pubkey);
    let owner_address = Address::new(network_type, owner_address_payload.clone(), true);
    let owner_address_string = owner_address.to_string();
    let max_mature_number = get_max_mature_number(&ckb_client).await?;
    let genesis_block: BlockView = ckb_client
        .get_block_by_number(0.into())
        .await?
        .context("get genesis block")?
        .into();
    let genesis_info = GenesisInfo(
        DefaultCellDepResolver::from_genesis(&genesis_block).map_err(anyhow::Error::msg)?,
    );

    // deploy rollup config cell
    let allowed_contract_type_hashes: Vec<gw_packed::AllowedTypeHash> = {
        let meta_hash = Pack::pack(&scripts_result.meta_contract_validator.script_type_hash);
        let meta = gw_packed::AllowedTypeHash::new_builder()
            .type_(AllowedContractType::Meta.into())
            .hash(meta_hash)
            .build();

        let sudt_hash = Pack::pack(&scripts_result.l2_sudt_validator.script_type_hash);
        let sudt = gw_packed::AllowedTypeHash::new_builder()
            .type_(AllowedContractType::Sudt.into())
            .hash(sudt_hash)
            .build();

        let polyjuice_hash = Pack::pack(&scripts_result.polyjuice_validator.script_type_hash);
        let polyjuice = gw_packed::AllowedTypeHash::new_builder()
            .type_(AllowedContractType::Polyjuice.into())
            .hash(polyjuice_hash)
            .build();
        let eth_addr_reg_validator_hash =
            Pack::pack(&scripts_result.eth_addr_reg_validator.script_type_hash);
        let eth_addr_reg_validator = gw_packed::AllowedTypeHash::new_builder()
            .type_(AllowedContractType::EthAddrReg.into())
            .hash(eth_addr_reg_validator_hash)
            .build();

        let mut type_hashes = vec![meta, sudt, polyjuice, eth_addr_reg_validator];
        let builtin_hashes = vec![
            &scripts_result.meta_contract_validator.script_type_hash,
            &scripts_result.l2_sudt_validator.script_type_hash,
            &scripts_result.polyjuice_validator.script_type_hash,
            &scripts_result.eth_addr_reg_validator.script_type_hash,
        ];

        let user_hashes: HashSet<_> =
            HashSet::from_iter(&user_rollup_config.allowed_contract_type_hashes);
        for user_hash in user_hashes {
            if builtin_hashes.contains(&user_hash) {
                continue;
            }

            type_hashes.push(gw_packed::AllowedTypeHash::from_unknown(user_hash.0));
        }
        type_hashes
    };

    // EOA scripts
    let allowed_eoa_type_hashes: Vec<gw_packed::AllowedTypeHash> = {
        let eth_hash = Pack::pack(&scripts_result.eth_account_lock.script_type_hash);
        let eth = gw_packed::AllowedTypeHash::new_builder()
            .type_(AllowedEoaType::Eth.into())
            .hash(eth_hash)
            .build();

        let mut type_hashes = vec![eth];
        let builtin_hashes = vec![&scripts_result.eth_account_lock.script_type_hash];

        let user_hashes: HashSet<_> =
            HashSet::from_iter(&user_rollup_config.allowed_eoa_type_hashes);
        for user_hash in user_hashes {
            if builtin_hashes.contains(&user_hash) {
                continue;
            }

            type_hashes.push(gw_packed::AllowedTypeHash::from_unknown(user_hash.0));
        }
        type_hashes
    };

    // composite rollup config
    let rollup_config = RollupConfig::new_builder()
        .l1_sudt_script_type_hash(Pack::pack(&user_rollup_config.l1_sudt_script_type_hash))
        .custodian_script_type_hash(Pack::pack(&scripts_result.custodian_lock.script_type_hash))
        .deposit_script_type_hash(Pack::pack(&scripts_result.deposit_lock.script_type_hash))
        .withdrawal_script_type_hash(Pack::pack(&scripts_result.withdrawal_lock.script_type_hash))
        .challenge_script_type_hash(Pack::pack(&scripts_result.challenge_lock.script_type_hash))
        .stake_script_type_hash(Pack::pack(&scripts_result.stake_lock.script_type_hash))
        .l2_sudt_validator_script_type_hash(Pack::pack(
            &scripts_result.l2_sudt_validator.script_type_hash,
        ))
        .burn_lock_hash(Pack::pack(&burn_lock_hash))
        .required_staking_capacity(Pack::pack(&user_rollup_config.required_staking_capacity))
        .challenge_maturity_blocks(Pack::pack(&user_rollup_config.challenge_maturity_blocks))
        .finality_blocks(Pack::pack(&user_rollup_config.finality_blocks))
        .reward_burn_rate(user_rollup_config.reward_burn_rate.into())
        .chain_id(Pack::pack(&user_rollup_config.chain_id))
        .allowed_eoa_type_hashes(PackVec::pack(allowed_eoa_type_hashes))
        .allowed_contract_type_hashes(PackVec::pack(allowed_contract_type_hashes))
        .build();
    let (secp_data, secp_data_dep) = get_secp_data(&ckb_client).await?;
    let mut deploy_context = DeployContext {
        privkey_path,
        owner_address: &owner_address,
        genesis_info: &genesis_info,
        deployment_result: scripts_result,
        ckb_client: &ckb_client,
    };

    let (rollup_config_output, rollup_config_data): (ckb_packed::CellOutput, Bytes) = {
        let data = rollup_config.as_bytes();
        let output = ckb_packed::CellOutput::new_builder()
            .lock(user_rollup_config.cells_lock.clone().into())
            .build();
        let output = fit_output_capacity(output, data.len());
        (output, data)
    };
    let rollup_config_cell_dep = {
        let tx_hash = deploy_context
            .deploy(
                vec![rollup_config_output],
                vec![rollup_config_data],
                Default::default(),
                None,
                Default::default(),
            )
            .await?;
        let out_point = ckb_packed::OutPoint::new_builder()
            .tx_hash(CKBPack::pack(&tx_hash))
            .index(CKBPack::pack(&0u32))
            .build();

        ckb_packed::CellDep::new_builder()
            .out_point(out_point)
            .dep_type(DepType::Code.into())
            .build()
    };

    // millisecond
    let timestamp = timestamp.unwrap_or_else(|| {
        // New created CKB dev chain's may out of sync with real world time,
        // So we using an earlier time to get around this issue.
        SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("timestamp")
            .sub(core::time::Duration::from_secs(3600))
            .as_millis() as u64
    });

    let first_cell_input: ckb_packed::CellInput = get_live_cells(
        ckb_rpc_url,
        owner_address_string.as_str(),
        max_mature_number,
        None,
        None,
        Some(1),
    )?
    .into_iter()
    .next()
    .map(|(input, _)| input)
    .ok_or_else(|| anyhow!("No live cell found for address: {}", owner_address_string))?;

    let rollup_cell_type_id: Bytes = calculate_type_id(&first_cell_input, 0);
    // calculate by: blake2b_hash(firstInput + rullupCell.outputIndex)
    let rollup_type_script = ckb_packed::Script::new_builder()
        .code_hash(CKBPack::pack(
            &scripts_result.state_validator.script_type_hash,
        ))
        .hash_type(ScriptHashType::Type.into())
        .args(CKBPack::pack(&rollup_cell_type_id))
        .build();
    let rollup_script_hash: H256 = CKBUnpack::unpack(&rollup_type_script.calc_script_hash());
    log::info!("rollup_script_hash: {:#x}", rollup_script_hash);

    // 1. build genesis block
    let genesis_config = GenesisConfig {
        timestamp,
        meta_contract_validator_type_hash: scripts_result
            .meta_contract_validator
            .script_type_hash
            .clone(),
        eth_registry_validator_type_hash: scripts_result
            .eth_addr_reg_validator
            .script_type_hash
            .clone(),
        rollup_type_hash: rollup_script_hash.clone(),
        rollup_config: rollup_config.clone().into(),
        secp_data_dep,
    };
    let genesis_with_global_state = build_genesis(&genesis_config, secp_data)?;

    // 2. build rollup cell (with type id)
    const OMNI_LOCK_IDENTITY_FLAGS_PUBKEY_HASH: u8 = 0;
    const OMNI_LOCK_FLAG_OWNER_PUBKEY_HASH_ONLY: u8 = 0;
    let (rollup_output, rollup_data): (ckb_packed::CellOutput, Bytes) = {
        let data = genesis_with_global_state.global_state.as_bytes();
        let omni_lock = {
            let pubkey_h160 = match omni_lock_config.pubkey_h160.as_ref() {
                Some(h160) => Bytes::copy_from_slice(h160.as_bytes()),
                // Use pubkey from deploy privkey
                None => ckb_packed::Script::from(&owner_address_payload)
                    .args()
                    .unpack(),
            };
            let args = {
                let mut buf = BytesMut::new();
                buf.put_u8(OMNI_LOCK_IDENTITY_FLAGS_PUBKEY_HASH);
                buf.put(pubkey_h160.as_ref());
                buf.put_u8(OMNI_LOCK_FLAG_OWNER_PUBKEY_HASH_ONLY);
                CKBPack::pack(&buf.freeze())
            };
            ckb_packed::Script::new_builder()
                .code_hash(CKBPack::pack(&omni_lock_config.script_type_hash))
                .hash_type(ScriptHashType::Type.into())
                .args(args)
                .build()
        };
        let output = ckb_packed::CellOutput::new_builder()
            .lock(omni_lock)
            .type_(CKBPack::pack(&Some(rollup_type_script.clone())))
            .build();
        let output = fit_output_capacity(output, data.len());
        (output, data)
    };

    // 3. put genesis block in rollup cell witness
    let witness_0: ckb_packed::WitnessArgs = {
        let output_type = genesis_with_global_state.genesis.as_bytes();
        ckb_packed::WitnessArgs::new_builder()
            .output_type(CKBPack::pack(&Some(output_type)))
            .build()
    };

    // 4. deploy genesis rollup cell
    let outputs_data = vec![rollup_data];
    let outputs = vec![rollup_output];
    let tx_hash = deploy_context
        .deploy(
            outputs,
            outputs_data,
            vec![rollup_config_cell_dep.clone()],
            Some(&first_cell_input),
            witness_0,
        )
        .await?;

    // 5. write genesis deployment result
    let rollup_result = RollupDeploymentResult {
        tx_hash,
        timestamp,
        rollup_type_hash: rollup_script_hash,
        rollup_type_script: rollup_type_script.into(),
        rollup_config: rollup_config.into(),
        rollup_config_cell_dep: rollup_config_cell_dep.into(),
        genesis_config,
        layer2_genesis_hash: genesis_with_global_state.genesis.hash().into(),
    };
    Ok(rollup_result)
}

fn calculate_type_id(first_cell_input: &ckb_packed::CellInput, first_output_index: u64) -> Bytes {
    let mut blake2b = new_blake2b();
    blake2b.update(first_cell_input.as_slice());
    blake2b.update(&first_output_index.to_le_bytes());
    let mut ret = [0; 32];
    blake2b.finalize(&mut ret);
    Bytes::from(ret.to_vec())
}

fn fit_output_capacity(output: ckb_packed::CellOutput, data_size: usize) -> ckb_packed::CellOutput {
    let data_capacity = Capacity::bytes(data_size).expect("data capacity");
    let capacity = output
        .occupied_capacity(data_capacity)
        .expect("occupied_capacity");
    output
        .as_builder()
        .capacity(CKBPack::pack(&capacity.as_u64()))
        .build()
}

fn collect_live_cells(
    rpc_client_url: &str,
    owner_address_str: &str,
    max_mature_number: u64,
    tip_number: u64,
    total_capacity: u64,
) -> Result<(Vec<ckb_packed::CellInput>, u64)> {
    let number_step = 10000;
    let limit = Some(usize::max_value());
    let mut from_number = 0;
    let mut to_number = from_number + number_step - 1;
    let mut total_input_capacity = 0;
    let mut inputs = Vec::new();
    while total_input_capacity < total_capacity {
        if from_number > tip_number {
            return Err(anyhow!(
                "not enough capacity from {}, expected: {}, found: {}",
                owner_address_str,
                HumanCapacity(total_capacity),
                HumanCapacity(total_input_capacity),
            ));
        }
        let new_cells = get_live_cells(
            rpc_client_url,
            owner_address_str,
            max_mature_number,
            Some(from_number),
            Some(to_number),
            limit,
        )?;
        for (new_input, new_capacity) in new_cells {
            total_input_capacity += new_capacity;
            inputs.push(new_input);
            if total_input_capacity >= total_capacity {
                break;
            }
        }
        from_number += number_step;
        to_number += number_step;
    }
    Ok((inputs, total_input_capacity))
}

// NOTE: This is an inefficient way to collect cells
fn get_live_cells(
    rpc_client_url: &str,
    owner_address_str: &str,
    max_mature_number: u64,
    from_number: Option<u64>,
    to_number: Option<u64>,
    limit: Option<usize>,
) -> Result<Vec<(ckb_packed::CellInput, u64)>> {
    let from_number_string = from_number.map(|value| value.to_string());
    let to_number_string = to_number.map(|value| value.to_string());
    let mut actual_limit = limit.unwrap_or(20);
    let mut cells = Vec::new();
    while cells.is_empty() {
        let limit_string = actual_limit.to_string();
        // wallet get-live-cells --address {address} --fast-mode --limit {limit} --from {from-number} --to {to-number}
        let mut args: Vec<&str> = vec![
            "--output-format",
            "json",
            "--url",
            rpc_client_url,
            "wallet",
            "get-live-cells",
            "--address",
            owner_address_str,
            "--fast-mode",
        ];
        if let Some(from_number) = from_number_string.as_ref() {
            args.push("--from");
            args.push(from_number.as_str());
        };
        if let Some(to_number) = to_number_string.as_ref() {
            args.push("--to");
            args.push(to_number.as_str());
        };
        args.push("--limit");
        args.push(limit_string.as_str());

        let live_cells_output = run_cmd(args)?;
        let live_cells: serde_json::Value = serde_json::from_str(&live_cells_output)?;
        cells = live_cells["live_cells"]
            .as_array()
            .expect("josn live cells")
            .iter()
            .filter_map(|live_cell| {
                /*
                    {
                    "capacity": "1200.0 (CKB)",
                    "data_bytes": 968,
                    "index": {
                    "output_index": 0,
                    "tx_index": 1
                },
                    "lock_hash": "0x1cdeae55a5768fe14b628001c6247ae84c70310a7ddcfdc73ac68494251e46ec",
                    "mature": true,
                    "number": 6617,
                    "output_index": 0,
                    "tx_hash": "0x0d0d63184973ccdaf2c972783e1ed5f984a3e31b971e3294b092e54fe1d86961",
                    "type_hashes": null
                }
                     */
                let tx_index = live_cell["index"]["tx_index"]
                    .as_u64()
                    .expect("live cell tx_index");
                let number = live_cell["number"].as_u64().expect("live cell number");
                let data_bytes = live_cell["data_bytes"]
                    .as_u64()
                    .expect("live cell data_bytes");
                let type_is_null = live_cell["type_hashes"].is_null();
                if !type_is_null
                    || data_bytes > 0
                    || !is_mature(number, tx_index, max_mature_number)
                {
                    log::debug!(
                        "has type: {}, data not empty: {}, immature: {}, number: {}, tx_index: {}",
                        !type_is_null,
                        data_bytes > 0,
                        !is_mature(number, tx_index, max_mature_number),
                        number,
                        tx_index,
                    );
                    return None;
                }

                let input_tx_hash = H256::from_str(
                    live_cell["tx_hash"]
                        .as_str()
                        .expect("live cell tx hash")
                        .trim_start_matches("0x"),
                )
                .expect("convert to h256");
                let input_index = live_cell["output_index"]
                    .as_u64()
                    .expect("live cell output index") as u32;
                let capacity = HumanCapacity::from_str(
                    live_cell["capacity"]
                        .as_str()
                        .expect("live cell capacity")
                        .split(' ')
                        .next()
                        .expect("capacity"),
                )
                .map(|human_capacity| human_capacity.0)
                .expect("parse capacity");
                let out_point =
                    ckb_packed::OutPoint::new(CKBPack::pack(&input_tx_hash), input_index);
                let input = ckb_packed::CellInput::new(out_point, 0);
                Some((input, capacity))
            })
            .collect();
        if actual_limit > u32::max_value() as usize / 2 {
            log::debug!("Can not find live cells for {}", owner_address_str);
            break;
        }
        actual_limit *= 2;
    }
    Ok(cells)
}

pub fn is_mature(number: u64, tx_index: u64, max_mature_number: u64) -> bool {
    // Not cellbase cell
    tx_index > 0
    // Live cells in genesis are all mature
        || number == 0
        || number <= max_mature_number
}

pub async fn get_secp_data(
    rpc_client: &CkbClient,
) -> Result<(Bytes, gw_jsonrpc_types::ckb_jsonrpc_types::CellDep)> {
    let mut cell_dep = None;
    rpc_client
        .get_block_by_number(0.into())
        .await?
        .context("get CKB genesis block")?
        .transactions
        .iter()
        .for_each(|tx| {
            tx.inner
                .outputs_data
                .iter()
                .enumerate()
                .for_each(|(output_index, data)| {
                    let data_hash = ckb_types::packed::CellOutput::calc_data_hash(data.as_bytes());
                    if data_hash.as_slice() == CODE_HASH_SECP256K1_DATA.as_bytes() {
                        let out_point = gw_jsonrpc_types::blockchain::OutPoint {
                            tx_hash: tx.hash.clone(),
                            index: (output_index as u32).into(),
                        };
                        cell_dep = Some((
                            data.clone().into_bytes(),
                            gw_jsonrpc_types::blockchain::CellDep {
                                out_point,
                                dep_type: gw_jsonrpc_types::blockchain::DepType::Code,
                            },
                        ));
                    }
                });
        });
    cell_dep.ok_or_else(|| anyhow!("Can not found secp data cell in CKB genesis block"))
}
