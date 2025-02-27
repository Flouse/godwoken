use std::path::Path;

use anyhow::{anyhow, Context, Result};
use ckb_jsonrpc_types::{CellDep, JsonBytes};
use ckb_types::prelude::{Builder, Entity};
use gw_builtin_binaries::Resource;
use gw_config::{
    BackendConfig, BackendForkConfig, BlockProducerConfig, ChainConfig, ChallengerConfig, Config,
    Consensus, ForkConfig, GenesisConfig, NodeMode, P2PNetworkConfig, RPCClientConfig,
    RPCServerConfig, RegistryAddressConfig, RegistryType, SUDTProxyConfig, StoreConfig,
    SystemTypeScriptConfig, WalletConfig,
};
use gw_jsonrpc_types::{godwoken::L2BlockCommittedInfo, JsonCalcHash};
use gw_rpc_client::ckb_client::CkbClient;
use gw_types::{core::ScriptHashType, packed::Script, prelude::*};
use gw_utils::checksum::file_checksum;

use crate::{
    deploy_genesis::get_secp_data,
    setup::get_wallet_info,
    types::{
        BuildScriptsResult, OmniLockConfig, RollupDeploymentResult, ScriptsDeploymentResult,
        UserRollupConfig,
    },
};

pub struct GenerateNodeConfigArgs<'a> {
    pub rollup_result: &'a RollupDeploymentResult,
    pub scripts_deployment: &'a ScriptsDeploymentResult,
    pub privkey_path: &'a Path,
    pub ckb_url: String,
    pub indexer_url: Option<String>,
    pub build_scripts_result: &'a BuildScriptsResult,
    pub server_url: String,
    pub user_rollup_config: &'a UserRollupConfig,
    pub omni_lock_config: &'a OmniLockConfig,
    pub node_mode: NodeMode,
    pub block_producer_address: Vec<u8>,
    pub p2p_listen: Option<String>,
    pub p2p_dial: Vec<String>,
}

pub async fn generate_node_config(args: GenerateNodeConfigArgs<'_>) -> Result<Config> {
    let GenerateNodeConfigArgs {
        rollup_result,
        scripts_deployment,
        privkey_path,
        ckb_url,
        indexer_url,
        build_scripts_result,
        server_url,
        user_rollup_config,
        omni_lock_config,
        node_mode,
        block_producer_address,
        p2p_listen,
        p2p_dial,
    } = args;

    let rpc_client = CkbClient::with_url(&ckb_url)?;
    let tx_with_status = rpc_client
        .get_transaction(rollup_result.tx_hash.clone(), 2.into())
        .await?
        .context("can't find genesis block transaction")?;
    let block_hash = tx_with_status.tx_status.block_hash.ok_or_else(|| {
        anyhow!(
            "the genesis transaction haven't been packaged into chain, please retry after a while"
        )
    })?;
    let number = rpc_client
        .get_header(block_hash.clone())
        .await?
        .ok_or_else(|| anyhow!("can't find block"))?
        .inner
        .number;

    // build configuration
    let node_wallet_info = get_wallet_info(privkey_path);
    let code_hash: [u8; 32] = {
        let mut hash = [0u8; 32];
        hex::decode_to_slice(
            node_wallet_info
                .block_assembler_code_hash
                .trim_start_matches("0x"),
            &mut hash as &mut [u8],
        )?;
        hash
    };
    let args = hex::decode(node_wallet_info.lock_arg.trim_start_matches("0x"))?;
    let lock = Script::new_builder()
        .code_hash(code_hash.pack())
        .hash_type(ScriptHashType::Type.into())
        .args(args.pack())
        .build()
        .into();

    let rollup_config = rollup_result.rollup_config.clone();
    let rollup_type_hash = rollup_result.rollup_type_hash.clone();
    let meta_contract_validator_type_hash = scripts_deployment
        .meta_contract_validator
        .script_type_hash
        .clone();
    let eth_registry_validator_type_hash = scripts_deployment
        .eth_addr_reg_validator
        .script_type_hash
        .clone();
    let rollup_type_script = rollup_result.rollup_type_script.clone();
    let rollup_config_cell_dep = rollup_result.rollup_config_cell_dep.clone();
    let (_data, secp_data_dep) = get_secp_data(&rpc_client).await.context("get secp data")?;

    let system_type_scripts = query_contracts_script(
        &rpc_client,
        scripts_deployment,
        user_rollup_config,
        omni_lock_config,
    )
    .await
    .map_err(|err| anyhow!("query contracts script {}", err))?;

    let challenger_config = ChallengerConfig {
        rewards_receiver_lock: user_rollup_config.reward_lock.clone(),
    };

    let wallet_config: WalletConfig = WalletConfig {
        privkey_path: privkey_path.into(),
        lock,
    };

    let backends: Vec<BackendConfig> = vec![
        {
            let generator_path =
                build_scripts_result.built_scripts["meta_contract_generator"].clone();
            let generator = Resource::file_system(generator_path.clone());
            let generator_checksum = file_checksum(&generator_path)?.into();
            BackendConfig {
                generator,
                generator_checksum,
                validator_script_type_hash: scripts_deployment
                    .meta_contract_validator
                    .script_type_hash
                    .clone(),
                backend_type: gw_config::BackendType::Meta,
            }
        },
        {
            let generator_path = build_scripts_result.built_scripts["l2_sudt_generator"].clone();
            let generator = Resource::file_system(generator_path.clone());
            let generator_checksum = file_checksum(&generator_path)?.into();
            BackendConfig {
                generator,
                generator_checksum,
                validator_script_type_hash: scripts_deployment
                    .l2_sudt_validator
                    .script_type_hash
                    .clone(),
                backend_type: gw_config::BackendType::Sudt,
            }
        },
        {
            let generator_path = build_scripts_result.built_scripts["polyjuice_generator"].clone();
            let generator = Resource::file_system(generator_path.clone());
            let generator_checksum = file_checksum(&generator_path)?.into();
            BackendConfig {
                generator,
                generator_checksum,
                validator_script_type_hash: scripts_deployment
                    .polyjuice_validator
                    .script_type_hash
                    .clone(),
                backend_type: gw_config::BackendType::Polyjuice,
            }
        },
        {
            let generator_path =
                build_scripts_result.built_scripts["eth_addr_reg_generator"].clone();
            let generator = Resource::file_system(generator_path.clone());
            let generator_checksum = file_checksum(&generator_path)?.into();
            BackendConfig {
                generator,
                generator_checksum,
                validator_script_type_hash: scripts_deployment
                    .eth_addr_reg_validator
                    .script_type_hash
                    .clone(),
                backend_type: gw_config::BackendType::EthAddrReg,
            }
        },
    ];
    let backend_forks = vec![BackendForkConfig {
        fork_height: 0,
        sudt_proxy: Some(SUDTProxyConfig {
            permit_sudt_transfer_from_dangerous_contract: true,
            address_list: Vec::new(),
        }),
        backends,
    }];

    let genesis_committed_info = L2BlockCommittedInfo {
        block_hash,
        number,
        transaction_hash: rollup_result.tx_hash.clone(),
    };

    let chain: ChainConfig = ChainConfig {
        genesis_committed_info,
        rollup_type_script,
        skipped_invalid_block_list: Default::default(),
        burn_lock: {
            let lock: ckb_types::packed::Script = user_rollup_config.burn_lock.clone().into();
            let lock = gw_types::packed::Script::new_unchecked(lock.as_bytes());
            lock.into()
        },
        // cell deps
        rollup_config_cell_dep,
    };

    let genesis: GenesisConfig = GenesisConfig {
        timestamp: rollup_result.timestamp,
        rollup_type_hash,
        meta_contract_validator_type_hash,
        eth_registry_validator_type_hash,
        rollup_config,
        secp_data_dep,
    };

    let fork = ForkConfig {
        backend_forks,
        increase_max_l2_tx_cycles_to_500m: None,
        upgrade_global_state_version_to_v2: Some(0),
        genesis,
        chain,
        system_type_scripts,
    };

    let store = StoreConfig {
        path: "./gw-db".into(),
        options_file: None,
        cache_size: None,
    };
    let rpc_client: RPCClientConfig = RPCClientConfig {
        indexer_url,
        ckb_url,
    };
    let rpc_server = RPCServerConfig {
        listen: server_url,
        ..Default::default()
    };
    let block_producer: Option<BlockProducerConfig> = Some(BlockProducerConfig {
        block_producer: RegistryAddressConfig {
            address_type: RegistryType::Eth,
            address: JsonBytes::from_vec(block_producer_address),
        },
        challenger_config,
        wallet_config: Some(wallet_config),
        ..Default::default()
    });
    let p2p_network_config = if !p2p_dial.is_empty() || p2p_listen.is_some() {
        Some(P2PNetworkConfig {
            listen: p2p_listen,
            dial: p2p_dial,
            ..Default::default()
        })
    } else {
        None
    };

    let config: Config = Config {
        consensus: Consensus::Config {
            config: Box::new(fork),
        },
        rpc_client,
        rpc_server,
        block_producer,
        node_mode,
        store,
        p2p_network_config,
        ..Default::default()
    };

    Ok(config)
}

async fn query_contracts_script(
    ckb_client: &CkbClient,
    deployment: &ScriptsDeploymentResult,
    user_rollup_config: &UserRollupConfig,
    omni_lock_config: &OmniLockConfig,
) -> Result<SystemTypeScriptConfig> {
    let query = |contract: &'static str, cell_dep: CellDep| -> _ {
        ckb_client.query_type_script(contract, cell_dep)
    };

    let state_validator = query(
        "state validator",
        deployment.state_validator.cell_dep.clone(),
    )
    .await?;
    assert_eq!(
        state_validator.hash(),
        deployment.state_validator.script_type_hash
    );

    let deposit_lock = query("deposit", deployment.deposit_lock.cell_dep.clone()).await?;
    assert_eq!(
        deposit_lock.hash(),
        deployment.deposit_lock.script_type_hash
    );

    let stake_lock = query("stake", deployment.stake_lock.cell_dep.clone()).await?;
    assert_eq!(stake_lock.hash(), deployment.stake_lock.script_type_hash);

    let custodian_lock = query("custodian", deployment.custodian_lock.cell_dep.clone()).await?;
    assert_eq!(
        custodian_lock.hash(),
        deployment.custodian_lock.script_type_hash
    );

    let withdrawal_lock = query("withdrawal", deployment.withdrawal_lock.cell_dep.clone()).await?;
    assert_eq!(
        withdrawal_lock.hash(),
        deployment.withdrawal_lock.script_type_hash
    );

    let challenge_lock = query("challenge", deployment.challenge_lock.cell_dep.clone()).await?;
    assert_eq!(
        challenge_lock.hash(),
        deployment.challenge_lock.script_type_hash
    );

    let l1_sudt = query("l1 sudt", user_rollup_config.l1_sudt_cell_dep.clone()).await?;
    assert_eq!(l1_sudt.hash(), user_rollup_config.l1_sudt_script_type_hash);

    // Allowed eoa script deps
    let eth_account_lock =
        query("eth account", deployment.eth_account_lock.cell_dep.clone()).await?;
    assert_eq!(
        eth_account_lock.hash(),
        deployment.eth_account_lock.script_type_hash
    );

    // Allowed contract script deps
    let meta_validator = query("meta", deployment.meta_contract_validator.cell_dep.clone()).await?;
    assert_eq!(
        meta_validator.hash(),
        deployment.meta_contract_validator.script_type_hash
    );

    let l2_sudt_validator = query("l2 sudt", deployment.l2_sudt_validator.cell_dep.clone()).await?;
    assert_eq!(
        l2_sudt_validator.hash(),
        deployment.l2_sudt_validator.script_type_hash
    );

    let polyjuice_validator =
        query("polyjuice", deployment.polyjuice_validator.cell_dep.clone()).await?;
    assert_eq!(
        polyjuice_validator.hash(),
        deployment.polyjuice_validator.script_type_hash
    );

    let eth_addr_reg_validator = query(
        "eth_addr_reg_validator",
        deployment.eth_addr_reg_validator.cell_dep.clone(),
    )
    .await?;
    assert_eq!(
        eth_addr_reg_validator.hash(),
        deployment.eth_addr_reg_validator.script_type_hash
    );

    let allowed_eoa_scripts = vec![eth_account_lock];

    let allowed_contract_scripts = vec![
        meta_validator,
        l2_sudt_validator,
        polyjuice_validator,
        eth_addr_reg_validator,
    ];

    let omni_lock = query("omni lock", omni_lock_config.cell_dep.clone()).await?;
    assert_eq!(omni_lock.hash(), omni_lock_config.script_type_hash);

    Ok(SystemTypeScriptConfig {
        state_validator,
        deposit_lock,
        stake_lock,
        custodian_lock,
        withdrawal_lock,
        challenge_lock,
        l1_sudt,
        omni_lock,
        allowed_eoa_scripts,
        allowed_contract_scripts,
    })
}
