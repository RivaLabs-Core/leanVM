//! leanVM: a minimal zkVM for RISC-V (rv64im). A [`Program`] is built from its text
//! ([`Program::new`], with [`asm`] for writing one by hand), [`prove`] runs it and
//! proves the run on a public input, RAM's first four words, [`verify`] checks the proof
//! against the program, that input and the output the run claims: `a0..a3` when it
//! called `exit`.
//!
//! End to end in [`tests/api.rs`](https://github.com/leanEthereum/leanVM/blob/main/tests/api.rs).

pub use lean_vm::{
    cpu::{CpuError, Program, Proof, Stats, prove, verify},
    pcs::{MAX_LOG_INV_RATE, MIN_LOG_INV_RATE},
    rv::{RAM_BASE, TEXT_BASE, Trap, asm},
};

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
    setup_verifier();
}

/// [`setup_prover`] for a machine with small memory.
pub fn setup_prover_without_arena() {
    setup_verifier();
}
