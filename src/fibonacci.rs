//! Fibonacci in the exponent: the demo benchmark. Two cells hold `g^{F(k)}` and
//! `g^{F(k+1)}`, and one `MUL64` onto either of them is one step of the recurrence.

use leanvm::{F64, Op, Program, g_pow, prove, verify};
use primitives::{bench::Plan, pretty_f64, pretty_integer};

/// Prove and verify `n` steps of Fibonacci in the exponent, binding `g^{F(n)}` as the
/// public input. Prints the benchmark report. Proving runs one discarded warmup pass
/// followed by `plan.repeat` measured passes (see [`primitives::bench`]).
pub fn run_fibonacci(n: usize, log_inv_rate: usize, plan: Plan) {
    let trace_span = tracing::info_span!("Fibonacci", n, log_inv_rate).entered();

    let (program, pi) = fibonacci_program(n);

    // Only the final measured pass of each stage is traced.
    let ((proof, stats), prove_time) = plan.warm_then_measure(|last| {
        let _quiet = (!last).then(primitives::suppress_tracing);
        prove(&program, pi, log_inv_rate)
    });
    let (_, verify_time) = Plan::new(plan.repeat, 0).measure_quiet(|last| {
        let _quiet = (!last).then(primitives::suppress_tracing);
        verify(&program, &pi, &proof).unwrap()
    });

    // tracing-forest renders its tree only when the root span closes, so the
    // complete trace has to be flushed above the report.
    drop(trace_span);

    println!(
        "Fibonacci (in the exponent, i.e. modulo 2^64 - 1), N = {}",
        pretty_integer(n)
    );
    println!("  cycles (VM steps)           : {}", pretty_integer(stats.cycles));
    println!("    details                   : {}", stats.details());
    let proof_bytes = bincode::serialized_size(&proof).expect("proof is serializable");
    println!("  proof size                  : {:.1} KiB", proof_bytes as f64 / 1024.0);
    let cycles_per_second = (stats.cycles as f64 / prove_time.mean()).round() as u64;
    println!(
        "  proving                     : {} s{}   {} cycles/s      peak memory {} GiB",
        pretty_f64(prove_time.mean()),
        prove_time.spread(),
        pretty_integer(cycles_per_second),
        pretty_f64(primitives::bench::peak_rss_bytes() as f64 / (1u64 << 30) as f64)
    );
    println!(
        "  verifying                   : {} ms",
        pretty_f64(verify_time.mean() * 1000.0)
    );
}

/// The demo program and its public input `[g^{F(n)}, 0, 0, 0]`: a loop whose body is
/// `UNROLL` recurrence steps in place, `a ← a·b` then `b ← a·b`, so that a step is one
/// instruction and the loop's own three are paid once per `UNROLL`.
fn fibonacci_program(fib_n: usize) -> (Program, [F64; 4]) {
    const UNROLL: usize = 1000;
    assert!(
        fib_n >= UNROLL && fib_n.is_multiple_of(UNROLL),
        "fib_n must be a positive multiple of {UNROLL}"
    );
    // The frame, past the four public words.
    const A: u32 = 4;
    const B: u32 = 5;
    const I: u32 = 6;
    const GEN: u32 = 7;
    const END: u32 = 8;
    const COND: u32 = 9;
    const LOOP_PC: u32 = 10;
    const FRAME: u32 = 11;
    const ONE: u32 = 12;

    let set = |o: u32, k: F64| Op::Set { o, k };
    let mut body = vec![
        set(A, F64::ONE),
        set(B, g_pow(1)),
        set(I, F64::ONE),
        set(GEN, g_pow(1)),
        set(END, g_pow(fib_n / UNROLL)),
        set(FRAME, F64::ONE),
        set(ONE, F64::ONE),
    ];
    let top = body.len() + 1;
    body.push(set(LOOP_PC, g_pow(top)));
    for _ in 0..UNROLL / 2 {
        body.extend([Op::Mul64 { a: A, b: B, c: A }, Op::Mul64 { a: A, b: B, c: B }]);
    }
    body.extend([
        // The loop counter lives in the exponent, stepped in place.
        Op::Mul64 { a: I, b: GEN, c: I },
        Op::Xor64 { a: I, b: END, c: COND },
        Op::Jump {
            oc: COND,
            od: LOOP_PC,
            of: FRAME,
        },
        // Publish `a` into the first public word.
        Op::Mul64 { a: A, b: ONE, c: 0 },
    ]);

    let (mut a, mut b) = (F64::ONE, g_pow(1));
    for _ in 0..fib_n / 2 {
        a *= b;
        b *= a;
    }
    (Program::from_body(body, 16), [a, F64::ZERO, F64::ZERO, F64::ZERO])
}

#[cfg(test)]
mod tests {
    #[test]
    fn fibonacci() {
        super::run_fibonacci(
            200_000,
            lean_vm::pcs::TEST_LOG_INV_RATE,
            primitives::bench::Plan::default(),
        );
    }
}
