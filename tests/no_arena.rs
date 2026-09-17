//! The no-arena path, in its own binary: `enable_arena` is a process-wide
//! one-way opt-in, so a test that must not have it cannot share a process with
//! `tests/api.rs`.

use lean_vm::hash_flock::{FINAL_FLAG, IV, PINNED_T, metadata};
use lean_vm::vmhash::compress;
use leanvm::*;

/// A BLAKE2s hash chain from the zero block, each digest compressed onto the state it
/// came from, then published into `m[0..4]`.
fn hash_chain(steps: usize) -> Program {
    const STATE: u32 = 4;
    const CV: u32 = 8;
    const MD: u32 = 12;
    const ONE: u32 = 14;
    let set = |o: u32, k: F64| Op::Set { o, k };
    let mut body: Vec<Op> = IV
        .iter()
        .enumerate()
        .map(|(k, &word)| set(CV + k as u32, word))
        .collect();
    let md = metadata(PINNED_T, FINAL_FLAG, 0);
    body.extend([set(MD, md[0]), set(MD + 1, md[1]), set(ONE, F64::ONE)]);
    body.extend(std::iter::repeat_n(
        Op::Blake2s {
            ins: [STATE, STATE + 2, STATE, STATE + 2],
            cv: CV,
            out: STATE,
            md: MD,
        },
        steps,
    ));
    body.extend((0..4).map(|k| Op::Mul64 {
        a: STATE + k,
        b: ONE,
        c: k,
    }));
    Program::from_body(body, 16)
}

#[test]
fn blake2s_hash_chain_without_the_arena() {
    setup_prover_without_arena();
    assert!(!zk_alloc::is_enabled(), "this path must leave the arena disengaged");

    let steps = std::env::var("LEANVM_HASH_N")
        .ok()
        .and_then(|value| value.parse().ok())
        .unwrap_or(8);
    let mut public_input = [F64::ZERO; 4];
    for _ in 0..steps {
        public_input = compress(public_input, public_input);
    }

    let program = hash_chain(steps);
    let (proof, stats) = prove(&program, public_input, MIN_LOG_INV_RATE);
    verify(&program, &public_input, &proof).expect("hash-chain proof verifies");
    assert_eq!(stats.base_counts[5], steps, "one BLAKE2S row per compression");

    let mut wrong_input = public_input;
    wrong_input[0] += F64::ONE;
    assert!(verify(&program, &wrong_input, &proof).is_err());
}
