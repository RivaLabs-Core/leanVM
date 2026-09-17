//! leanVM: a minimal zkVM. A [`Program`] is assembled from its instructions
//! ([`Program::from_body`]), [`prove`] runs it and proves the run, [`verify`] checks the
//! proof against the program and its public input.
//!
//! End to end in [`tests/api.rs`](https://github.com/leanEthereum/leanVM/blob/main/tests/api.rs).

pub use lean_vm::{
    cpu::{CpuError, DerefMode, Op, Program, Proof, Stats, prove, verify},
    pcs::{MAX_LOG_INV_RATE, MIN_LOG_INV_RATE},
};
pub use primitives::field::{F64, g_pow};

/// Call once before [`verify`]. Idempotent, and [`setup_prover`] does it for you.
pub fn setup_verifier() {
    lean_vm::init_prover_pool();
}

/// Call once before [`prove`].
///
/// There is one arena per process, so only one [`prove`] call may run at a
/// time in a process: to prove in parallel, use separate processes.
pub fn setup_prover() {
    zk_alloc::enable_arena();
    setup_prover_without_arena();
}

/// [`setup_prover`] for a machine with small memory.
pub fn setup_prover_without_arena() {
    setup_verifier();
}
