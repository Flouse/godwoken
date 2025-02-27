//! For for implement offchain operations or for testing purpose

use std::collections::HashMap;

use ckb_types::{
    bytes::Bytes,
    core::{HeaderView, TransactionView},
    packed::{Byte32, CellDep, CellOutput, OutPoint, Script},
    prelude::*,
    H256,
};

use crate::utils::sdk::traits::{
    CellDepResolver, HeaderDepResolver, TransactionDependencyError, TransactionDependencyProvider,
};
use crate::utils::sdk::types::ScriptId;
use anyhow::anyhow;

/// A offchain cell_dep resolver
#[derive(Default, Clone)]
pub struct OffchainCellDepResolver {
    pub items: HashMap<ScriptId, (CellDep, String)>,
}
impl CellDepResolver for OffchainCellDepResolver {
    fn resolve(&self, script: &Script) -> Option<CellDep> {
        let script_id = ScriptId::from(script);
        self.items
            .get(&script_id)
            .map(|(cell_dep, _)| cell_dep.clone())
    }
}

#[derive(Default, Clone)]
pub struct OffchainHeaderDepResolver {
    pub by_tx_hash: HashMap<H256, HeaderView>,
    pub by_number: HashMap<u64, HeaderView>,
}

impl HeaderDepResolver for OffchainHeaderDepResolver {
    fn resolve_by_tx(&self, tx_hash: &Byte32) -> Result<Option<HeaderView>, anyhow::Error> {
        let tx_hash: H256 = tx_hash.unpack();
        Ok(self.by_tx_hash.get(&tx_hash).cloned())
    }
    fn resolve_by_number(&self, number: u64) -> Result<Option<HeaderView>, anyhow::Error> {
        Ok(self.by_number.get(&number).cloned())
    }
}

/// offchain transaction dependency provider
#[derive(Default, Clone)]
pub struct OffchainTransactionDependencyProvider {
    pub txs: HashMap<H256, TransactionView>,
    pub cells: HashMap<(H256, u32), (CellOutput, Bytes)>,
    pub headers: HashMap<H256, HeaderView>,
}

impl TransactionDependencyProvider for OffchainTransactionDependencyProvider {
    // For verify certain cell belong to certain transaction
    fn get_transaction(
        &self,
        tx_hash: &Byte32,
    ) -> Result<TransactionView, TransactionDependencyError> {
        let tx_hash: H256 = tx_hash.unpack();
        self.txs
            .get(&tx_hash)
            .cloned()
            .ok_or_else(|| TransactionDependencyError::Other(anyhow!("offchain get_transaction")))
    }
    // For get the output information of inputs or cell_deps, those cell should be live cell
    fn get_cell(&self, out_point: &OutPoint) -> Result<CellOutput, TransactionDependencyError> {
        let tx_hash: H256 = out_point.tx_hash().unpack();
        let index: u32 = out_point.index().unpack();
        self.cells
            .get(&(tx_hash, index))
            .map(|(output, _)| output.clone())
            .ok_or_else(|| TransactionDependencyError::Other(anyhow!("offchain get_cell")))
    }
    // For get the output data information of inputs or cell_deps
    fn get_cell_data(&self, out_point: &OutPoint) -> Result<Bytes, TransactionDependencyError> {
        let tx_hash: H256 = out_point.tx_hash().unpack();
        let index: u32 = out_point.index().unpack();
        self.cells
            .get(&(tx_hash, index))
            .map(|(_, data)| data.clone())
            .ok_or_else(|| TransactionDependencyError::Other(anyhow!("offchain get_cell_data")))
    }
    // For get the header information of header_deps
    fn get_header(&self, block_hash: &Byte32) -> Result<HeaderView, TransactionDependencyError> {
        let block_hash: H256 = block_hash.unpack();
        self.headers
            .get(&block_hash)
            .cloned()
            .ok_or_else(|| TransactionDependencyError::Other(anyhow!("offchain get_header")))
    }
}
