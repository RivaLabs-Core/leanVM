use leanvm::*;

const STEPS: usize = 1000;

/// Fibonacci in the exponent, in place: `(a, b) ← (a·b, a·b²)` is two steps of the
/// recurrence, and `g^{F(STEPS)}` is published into `m[0]`.
fn fibonacci() -> (Program, [F64; 4]) {
    const A: u32 = 4;
    const B: u32 = 5;
    const ONE: u32 = 6;
    let mut body = vec![
        Op::Set { o: A, k: F64::ONE },
        Op::Set { o: B, k: g_pow(1) },
        Op::Set { o: ONE, k: F64::ONE },
    ];
    for _ in 0..STEPS / 2 {
        body.extend([Op::Mul64 { a: A, b: B, c: A }, Op::Mul64 { a: A, b: B, c: B }]);
    }
    body.push(Op::Mul64 { a: A, b: ONE, c: 0 });

    let (mut a, mut b) = (F64::ONE, g_pow(1));
    for _ in 0..STEPS / 2 {
        a *= b;
        b *= a;
    }
    (Program::from_body(body, 8), [a, F64::ZERO, F64::ZERO, F64::ZERO])
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
