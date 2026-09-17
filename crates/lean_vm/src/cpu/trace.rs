//! The trace: one [`Row`] per executed instruction, emitted during execution and
//! grouped by table, plus what the run leaves behind for the finalize blocks.
//!
//! A row carries what its accesses saw, its clock, and per access what the memory
//! argument needs ([`Access`]). Everything else comes back from the program's entry
//! at `index`.

use primitives::field::F64;

/// One access to a read-write array, as the memory argument sees it (§sec:memchan).
#[derive(Clone, Copy)]
pub(crate) struct Access {
    /// `g^x`, the timestamp of the cell's previous access. Zero on a padding row.
    pub(crate) x: F64,
    /// `y - x - 1` for this access's timestamp `y`: what the two range reads certify
    /// to be below `2^32`.
    pub(crate) gap: u32,
    /// The read counts of the two range-array entries the gap's chunks name.
    pub(crate) count_lo: F64,
    pub(crate) count_hi: F64,
}

pub(crate) struct Row {
    /// The entry executed.
    pub(crate) index: u32,
    /// The row's clock `g^{4·cycle}`, zero on a padding row.
    pub(crate) ts: F64,
    pub(crate) v1: u64,
    pub(crate) v2: u64,
    /// What the class computed.
    pub(crate) out: u64,
    pub(crate) taken: bool,
    /// What the destination register held before the write.
    pub(crate) vd_old: u64,
    /// `rs1`, `rs2`, `rd`.
    pub(crate) acc: [Access; 3],
    pub(crate) bytecode_read: F64,
}

pub(crate) struct Trace {
    /// Per table, in [`crate::tables::CLASSES`] order.
    pub(crate) rows: [Vec<Row>; crate::tables::N_TABLES],
    /// The registers after the run, and each one's last timestamp `g^y`, `g^0` if
    /// never touched.
    pub(crate) reg_fin: Vec<F64>,
    pub(crate) reg_ts: Vec<F64>,
    pub(crate) bytecode_count: Vec<F64>, // per-pc running execution count g^{count}; final = g^{A[pc]}
    /// Final read counts of the two range arrays' entries.
    pub(crate) range_lo_count: Vec<F64>,
    pub(crate) range_hi_count: Vec<F64>,
    /// The clock `g^{4·cycle}` the run ended on: the final state's timestamp.
    pub(crate) ts_final: F64,
}

impl Trace {
    /// Rows per instruction table.
    pub(crate) fn row_counts(&self) -> [usize; crate::tables::N_TABLES] {
        std::array::from_fn(|t| self.rows[t].len())
    }
}
