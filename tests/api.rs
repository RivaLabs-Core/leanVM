use leanvm::*;

const STEPS: usize = 1000;

/// Fibonacci in the exponent: `fib[g^k] = g^{F_k}`, the result published into `m[0]`.
fn fibonacci() -> (Program, [F64; 4]) {
    let source = format!(
        "def main():\n\
        \x20   fib = HeapBuf({size})\n\
        \x20   fib[1] = 1\n\
        \x20   fib[GEN] = GEN\n\
        \x20   for i in mul_range(1, GEN ** {STEPS}):\n\
        \x20       fib[i * GEN * GEN] = fib[i] * fib[i * GEN]\n\
        \x20   p = 1\n\
        \x20   p[1] = fib[GEN ** {last}]\n\
        \x20   return\n",
        size = STEPS + 2,
        last = STEPS + 1,
    );
    let (mut previous, mut current) = (F64::ONE, g_pow(1));
    for _ in 0..STEPS {
        (previous, current) = (current, previous * current);
    }
    (
        compile(&parse(&source).unwrap()),
        [current, F64::ZERO, F64::ZERO, F64::ZERO],
    )
}

#[test]
fn public_api_end_to_end() {
    setup_prover();
    let (program, public_input) = fibonacci();

    // 1. Prove, then onto the wire and back to a receiver.
    let (proof, _) = prove(&program, public_input, MIN_LOG_INV_RATE);
    let bytes = bincode::serialize(&proof).unwrap();
    let received: Proof = bincode::deserialize(&bytes).unwrap();
    verify(&program, &public_input, &received).unwrap();

    // 2. The proof is about this public input and no other.
    let mut wrong_input = public_input;
    wrong_input[0] += F64::ONE;
    assert!(verify(&program, &wrong_input, &received).is_err());

    // 3. One proof is one arena phase: the first proof outlives the second's phase.
    let (second, _) = prove(&program, public_input, MIN_LOG_INV_RATE);
    verify(&program, &public_input, &second).unwrap();
    verify(&program, &public_input, &received).unwrap();
    let stats = zk_alloc::stats();
    assert!(stats.phases >= 2, "expected one phase per proof, got {stats:?}");
    assert!(stats.peak_bytes > 0, "no buffer reached the arena: {stats:?}");
    assert_eq!(
        stats.overflow, 0,
        "a slab overflowed into the system allocator: {stats:?}"
    );
}
