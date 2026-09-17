//! The no-arena path, in its own binary: `enable_arena` is a process-wide
//! one-way opt-in, so a test that must not have it cannot share a process with
//! `tests/api.rs`.

use lean_vm::vmhash::compress;
use leanvm::*;

/// An unrolled BLAKE2s hash chain from the zero block, the digest published into `m[0..4]`.
fn chain_source(steps: usize, unroll: usize) -> String {
    assert!(
        unroll >= 1 && steps.is_multiple_of(unroll),
        "N must be a positive multiple of UNROLL"
    );
    let blocks = steps / unroll;
    let result_cell = 4 * blocks;

    let mut body = String::new();
    body.push_str("        b = i ** 4\n");
    body.push_str("        h0 = StackBuf(4)\n");
    body.push_str("        h0[0:4] = buff[b:b + 4]\n");
    for step in 1..=unroll {
        body.push_str(&format!("        h{step} = StackBuf(4)\n"));
        body.push_str(&format!(
            "        blake2s(h{previous}, h{previous}, h{step})\n",
            previous = step - 1
        ));
    }
    body.push_str("        nxt = b * GEN ** 4\n");
    body.push_str(&format!("        buff[nxt:nxt + 4] = h{unroll}\n"));

    format!(
        "def main():\n\
        \x20   buff = HeapBuf({size})\n\
        \x20   buff[0:4] = [0, 0, 0, 0]\n\
        \x20   for i in mul_range(1, GEN ** {blocks}):\n\
        {body}\
        \x20   output = 1\n\
        \x20   output[0:4] = buff[{result_cell}:{result_cell} + 4]\n\
        \x20   return\n",
        size = result_cell + 4,
    )
}

#[test]
fn blake2s_hash_chain_without_the_arena() {
    setup_prover_without_arena();
    assert!(!zk_alloc::is_enabled(), "this path must leave the arena disengaged");

    let env_usize = |key: &str, default: usize| {
        std::env::var(key)
            .ok()
            .and_then(|value| value.parse().ok())
            .unwrap_or(default)
    };
    let unroll = env_usize("LEANVM_HASH_UNROLL", 4);
    let steps = env_usize("LEANVM_HASH_N", 8);

    let mut public_input = [F64::ZERO; 4];
    for _ in 0..steps {
        public_input = compress(public_input, public_input);
    }

    let program = compile(&parse(&chain_source(steps, unroll)).expect("parse"));
    let (proof, stats) = prove(&program, public_input, MIN_LOG_INV_RATE);
    verify(&program, &public_input, &proof).expect("hash-chain proof verifies");
    assert_eq!(stats.base_counts[5], steps, "one BLAKE2S row per compression");

    let mut wrong_input = public_input;
    wrong_input[0] += F64::ONE;
    assert!(verify(&program, &wrong_input, &proof).is_err());
}
