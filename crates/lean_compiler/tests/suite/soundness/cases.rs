//! Layer 1: perturbation. Each case is one program with one valid trial and a
//! table of single-cell pokes that must break it.
//!
//! Coverage is by *lowering*, not by feature list: every case exercises a
//! construct whose lowering could plausibly drop the check it stands for, and
//! every poke names one constraint. A poke that is accepted says which one is
//! missing.
//!
//! The pokes lean on witness streams rather than the public input, because four
//! public words is all there is and because the streams are where a real guest's
//! untrusted data actually enters.

use super::{Case, Trial, check_case, g, k, limbs, pi, wit};
use lean_vm::vmhash::compress;
use primitives::field::{F64, F192};

/// `XOR64`/`MUL64` relations, both assert forms, and the division back-solve. The
/// quotient cell is written by nothing but the back-solve, so this case also
/// pins the one legitimate way a cell may be read before any instruction writes
/// it.
#[test]
fn arithmetic_and_asserts() {
    check_case(&Case {
        name: "arithmetic_and_asserts",
        src: "\
def main():
    v = StackBuf(3)
    hint_witness(v, \"w\")
    assert v[0] * v[1] == v[2]
    assert v[0] != v[1]
    q = v[2] / v[0]
    assert q == v[1]
    p = GEN ** 0
    p[1] = v[2]
    p[GEN] = v[0] + v[1]
    return
",
        valid: Trial::new(&[g(8), g(3) + g(5)]).stream("w", vec![vec![g(3), g(5), g(8)]]),
        pokes: vec![
            // Each of the three hinted cells breaks the product relation.
            wit("w", 0, g(4)),
            wit("w", 1, g(6)),
            wit("w", 2, g(9)),
            // Equal operands: the product relation would still need v[2] = g^10,
            // but this is the poke that `assert !=` exists for.
            wit("w", 0, g(5)),
            // Both published words.
            pi(0, g(9)),
            pi(1, g(3) + g(6)),
        ],
    });
}

/// The same relations over 192-bit runs: `MUL192`, both 192-bit assert forms, and
/// the `div192` back-solve, whose quotient run is written by nothing else. A
/// second quotient lands on a hinted run, so a claimed quotient is checked by the
/// product rather than trusted: the pokes on `q` are a forged quotient.
#[test]
fn arithmetic192_and_asserts() {
    let a = F192::new(g(3).0, 11, 13);
    let b = F192::new(g(5).0, 11, 13);
    let c = a * b;
    let w: Vec<F64> = [limbs(a), limbs(b), limbs(c)].concat();
    let sum = limbs(a + b);
    let bump = |x: u64| F64(x) + F64::ONE;
    check_case(&Case {
        name: "arithmetic192_and_asserts",
        src: "\
def main():
    v = StackBuf(9)
    hint_witness(v, \"w\")
    assert_eq192(mul192(v[0:3], v[3:6]), v[6:9])
    assert_ne192(v[0:3], v[3:6])
    q = div192(v[6:9], v[0:3])
    assert_eq192(q, v[3:6])
    claimed = StackBuf(3)
    hint_witness(claimed, \"q\")
    claimed[0:3] = div192(v[6:9], v[3:6])
    p = GEN ** 0
    p[0:3] = add192(v[0:3], v[3:6])
    p[GEN ** 3] = v[6]
    return
",
        valid: Trial::new(&[sum[0], sum[1], sum[2], F64(c.c0)])
            .stream("w", vec![w])
            .stream("q", vec![limbs(a).to_vec()]),
        pokes: vec![
            // Either factor, and the product's unpublished limbs.
            wit("w", 1, bump(a.c1)),
            wit("w", 5, bump(b.c2)),
            wit("w", 7, bump(c.c1)),
            wit("w", 8, bump(c.c2)),
            // Equal operands, the poke `assert_ne192` exists for.
            wit("w", 3, g(3)),
            // A forged quotient, one limb at a time.
            wit("q", 0, bump(a.c0)),
            wit("q", 1, bump(a.c1)),
            wit("q", 2, bump(a.c2)),
            // The published sum and product limb.
            pi(0, bump(sum[0].0)),
            pi(2, bump(sum[2].0)),
            pi(3, bump(c.c0)),
        ],
    });
}

/// The exponent range check and `match` dispatch. The dispatch is only
/// sound because the matched value was range-checked first (doc §Match
/// statements), so a poke past the bound must be caught by the check rather than
/// land at an attacker-chosen arm.
#[test]
fn range_check_and_dispatch() {
    check_case(&Case {
        name: "range_check_and_dispatch",
        src: "\
def main():
    v = StackBuf(2)
    hint_witness(v, \"w\")
    assert log(v[0]) < 8
    r = match(log(v[0]), range(0, 8), lambda i: sq(i))
    assert r == v[1]
    p = GEN ** 0
    p[1] = v[0]
    p[GEN] = r
    return


def sq(x):
    return x * x
",
        // Arm 3 runs: sq(3) = 3·3 in K = (x+1)^2 = x^2+1 = 5.
        valid: Trial::new(&[g(3), k(5)]).stream("w", vec![vec![g(3), k(5)]]),
        pokes: vec![
            // Past the bound: the range check's complement DEREF must catch it.
            wit("w", 0, g(8)),
            wit("w", 0, g(63)),
            // A different arm runs, so the claimed square is wrong.
            wit("w", 0, g(4)),
            // The claimed square itself.
            wit("w", 1, k(6)),
            pi(0, g(4)),
            pi(1, k(6)),
        ],
    });
}

/// `if`/`else` communicating through a write-once heap cell: only one arm runs,
/// so both may write it and the join reads it back. A lowering that lets the
/// join read anything other than the taken arm's value shows up as a poke that
/// selects the other arm and is still accepted.
#[test]
fn branch_join() {
    check_case(&Case {
        name: "branch_join",
        src: "\
def main():
    v = StackBuf(2)
    hint_witness(v, \"w\")
    assert log(v[0]) < 4
    r = HeapBuf(1)
    if v[0] == GEN ** 2:
        r[1] = v[1] * GEN
    else:
        r[1] = v[1] * GEN ** 3
    p = GEN ** 0
    p[1] = r[1]
    p[GEN] = v[0]
    return
",
        valid: Trial::new(&[g(6), g(2)]).stream("w", vec![vec![g(2), g(5)]]),
        pokes: vec![
            // Takes the else arm, which multiplies by g^3 instead of g.
            wit("w", 0, g(1)),
            wit("w", 0, g(3)),
            // Past the bound.
            wit("w", 0, g(4)),
            // The value the taken arm shifts.
            wit("w", 1, g(4)),
            pi(0, g(7)),
            pi(1, g(3)),
        ],
    });
}

/// A `mul_range` loop with a runtime bound and heap-carried state. The bound is
/// hinted, so the loop terminates only because its log was checked first; the
/// pokes cover both a bound that changes the trip count and one past the check.
#[test]
fn loop_with_runtime_bound() {
    check_case(&Case {
        name: "loop_with_runtime_bound",
        src: "\
def main():
    v = StackBuf(1)
    hint_witness(v, \"n\")
    assert log(v[0]) < 8
    acc = HeapBuf(16)
    acc[1] = GEN ** 0
    for i in mul_range(1, v[0]):
        acc[i * GEN] = acc[i] * GEN ** 2
    p = GEN ** 0
    p[1] = acc[v[0]]
    p[GEN] = v[0]
    return
",
        // n = g^5: five iterations, acc[j] = g^{2j}, so acc[5] = g^10.
        valid: Trial::new(&[g(10), g(5)]).stream("n", vec![vec![g(5)]]),
        pokes: vec![
            // Fewer and more iterations: acc[n] is then g^8 and g^12.
            wit("n", 0, g(4)),
            wit("n", 0, g(6)),
            // Past the bound.
            wit("n", 0, g(8)),
            pi(0, g(11)),
            pi(1, g(4)),
        ],
    });
}

/// The digest-as-verification idiom: a hinted preimage, hashed, and the result
/// pinned against a hinted digest through a heap run store. This is the shape a
/// signature verifier has, so it is the one that most needs a regression test.
#[test]
fn digest_pins_its_preimage() {
    let d = digest_5_7();
    check_case(&Case {
        name: "digest_pins_its_preimage",
        src: "\
def main():
    m = StackBuf(8)
    hint_witness(m, \"msg\")
    d = StackBuf(4)
    blake2s(m[0:4], m[4:8], d)
    e = HeapBuf(4)
    hint_witness(e[0:4], \"dig\")
    e[0:4] = d
    p = GEN ** 0
    p[1] = m[0]
    p[GEN] = m[1]
    return
",
        valid: Trial::new(&[k(5), k(7)])
            .stream("msg", vec![vec![k(5), k(7), k(0), k(0), k(0), k(0), k(0), k(0)]])
            .stream("dig", vec![d.to_vec()]),
        pokes: vec![
            // A different preimage hashes to something else, published or not.
            wit("msg", 0, k(6)),
            wit("msg", 1, k(8)),
            wit("msg", 2, k(1)),
            wit("msg", 7, k(1)),
            // A wrong digest is what the write-once store has to catch.
            wit("dig", 0, F64::ZERO),
            wit("dig", 3, F64::ZERO),
            wit("dig", 1, d[1] + F64::ONE),
            wit("dig", 2, d[2] + F64::ONE),
            // The published preimage words.
            pi(0, k(6)),
            pi(1, k(8)),
        ],
    });
}

/// BLAKE2s of the 64-byte block whose eight words are `(5, 7, 0, 0, 0, 0, 0, 0)`,
/// from the reference compression: what a case tests is that a *wrong* digest is
/// rejected, and for that the honest value only has to be honest.
pub fn digest_5_7() -> [F64; 4] {
    compress([k(5), k(7), k(0), k(0)], [k(0); 4])
}

/// The fused `match` path must reject a call that binds more names than
/// the callee returns, exactly as the non-fused path does. Before this check the
/// surplus name `DEREF`ed a callee-frame offset nothing on the taken path wrote,
/// and since the shared frame is sized to the largest callee that offset exists,
/// so the name bound a prover-chosen word.
///
/// Fusion needs every arm to be a call to the same function with identical
/// runtime arguments, so the two programs below are the fused shape: one over
/// mixed-arity callees, one over a single over-bound callee. The mixed arms are
/// caught by the shared-layout check, which compares the return shapes before any
/// count is read; the over-bound callee has one layout and reaches the count.
#[test]
#[should_panic(expected = "does not take and return the same shapes")]
fn dispatched_call_rejects_a_mixed_arity_arm() {
    super::build(
        "\
def main():
    x = GEN ** 2
    a, b, c = match(log(x), range(0, 2), lambda i: three(x, i), range(2, 4), lambda i: one(x, i))
    p = GEN ** 0
    p[1] = b
    p[GEN] = c
    return


def three(v, k: Const):
    q = v * GEN ** k
    return q, q * q, q * q * q


def one(v, k: Const):
    return v * GEN ** k
",
    );
}

#[test]
#[should_panic(expected = "dispatched call binds")]
fn dispatched_call_rejects_an_over_bound_callee() {
    super::build(
        "\
def main():
    x = GEN ** 1
    a, b = match(log(x), range(0, 4), lambda i: one(x, i))
    p = GEN ** 0
    p[1] = a
    p[GEN] = b
    return


def one(v, k: Const):
    return v * GEN ** k
",
    );
}

/// A local whose name collides with a top-level constant array must be rejected.
/// `zkDSL.md` §Global constants reserves the name; a scalar constant enforces that
/// by construction (the parser substitutes its value, so the shadowing binding
/// becomes a literal and fails loudly), but a constant array was carried to
/// lowering, where `const_array_elem` resolved `NAME[i]` against it without
/// consulting the scope and `expr` folded it before the local could be seen.
///
/// The consequence was the catastrophic direction for a hint: the range check
/// below ran against the baked constant `g^3` and passed, while the actual witness
/// `g^40` was never bounded and never read.
#[test]
#[should_panic(expected = "reserved")]
fn a_local_may_not_shadow_a_constant_array() {
    super::build(
        "\
Q = [8, 32]


def main():
    Q = StackBuf(2)
    hint_witness(Q, \"w\")
    assert log(Q[0]) < 8
    p = GEN ** 0
    p[1] = Q[0]
    p[GEN] = Q[1]
    return
",
    );
}

/// Same rule for a parameter, which is the other half of what the doc reserves.
#[test]
#[should_panic(expected = "reserved")]
fn a_parameter_may_not_shadow_a_constant_array() {
    super::build(
        "\
Q = [8, 32]


def main():
    r = pick(GEN ** 2)
    p = GEN ** 0
    p[1] = r
    p[GEN] = r
    return


def pick(Q):
    return Q * GEN
",
    );
}

/// A `StackBuf` target's index is bounds-checked. The arms write their return
/// straight into that cell, so an unchecked index puts a callee's return into
/// whatever buffer follows: with the check removed, a program that never assigns
/// `b[0]` publishes a value from the arms and PROVES IT, which is the shape
/// `copy_alias` had before its own bounds check went in.
#[test]
#[should_panic(expected = "out of bounds")]
fn a_stackbuf_target_index_is_bounds_checked() {
    super::build(
        "\
def main():
    a = StackBuf(2)
    b = StackBuf(2)
    a[0] = 0
    a[1] = 0
    x = GEN ** 1
    a[2], e = match(log(x), range(0, 2), lambda i: two(x, i))
    p = GEN ** 0
    p[1] = b[0]
    p[GEN] = e
    return


def two(v, k: Const):
    return v * GEN ** k, GEN ** k
",
    );
}

/// A `blake2s` input operand written as a list is the same hash as gathering the
/// words into a buffer, so hashing one way and the other must agree.
///
/// Self-comparing on purpose: an equivalence pair cannot check this, because a
/// trial that must be ACCEPTED has to name the digest, and asserting the two
/// digests equal needs no digest at all. The list spells every chunk shape the
/// lowering distinguishes: a run element whose two words are used in place, a
/// reversed pair that has to be copied, a constant pair, and a pair mixing a cell
/// and a constant. The operands are DIFFERENT words so that reordering within a
/// list is visible.
#[test]
fn a_blake2s_word_list_hashes_like_the_buffer_it_replaces() {
    check_case(&Case {
        name: "a_blake2s_word_list_hashes_like_the_buffer_it_replaces",
        src: "\
def main():
    v = StackBuf(4)
    hint_witness(v, \"w\")
    named = StackBuf(4)
    blake2s([v[0:2], v[3], v[2]], [5, 7, v[1], 9], named)
    l = StackBuf(4)
    l[0] = v[0]
    l[1] = v[1]
    l[2] = v[3]
    l[3] = v[2]
    r = StackBuf(4)
    r[0] = 5
    r[1] = 7
    r[2] = v[1]
    r[3] = 9
    gathered = StackBuf(4)
    blake2s(l, r, gathered)
    assert named[0] == gathered[0]
    assert named[1] == gathered[1]
    assert named[2] == gathered[2]
    assert named[3] == gathered[3]
    p = GEN ** 0
    p[0:4] = v
    return
",
        valid: Trial::new(&[k(11), k(22), k(33), k(44)]).stream("w", vec![vec![k(11), k(22), k(33), k(44)]]),
        pokes: vec![
            wit("w", 0, k(12)),
            wit("w", 1, k(23)),
            wit("w", 2, k(34)),
            wit("w", 3, k(45)),
        ],
    });
}

/// A frame STORE's index is bounds-checked, like a read's and a target's.
///
/// The three callers of `frame_cell` each need their own case: with the check
/// removed at the store site alone, all 148 tests still passed, and `a[2] = …` on
/// a `StackBuf(2)` wrote the next buffer's first cell, published it, and the proof
/// VERIFIED. That is the `copy_alias` bug reappearing at a different caller.
#[test]
#[should_panic(expected = "out of bounds")]
fn a_frame_store_index_is_bounds_checked() {
    super::build(
        "\
def main():
    a = StackBuf(2)
    b = StackBuf(2)
    a[0] = 0
    a[1] = 0
    b[1] = 0
    a[2] = GEN ** 7
    p = GEN ** 0
    p[1] = b[0]
    p[GEN] = b[1]
    return
",
    );
}

/// One spelling of a heap index must not name two different cells.
///
/// A heap index is a g-power: `buf[GEN ** k]` is cell `k`, and a plain integer is
/// rejected because `buf[4]` reads as cell 2 (`4 = g^2`) while the slice
/// `buf[4:4+2]` reads as cells 4 and 5. Only a LITERAL carries that g-power
/// reading, and briefly `const(...)` and `len(...)` carried it too, so
/// `buf[const(8)]` on a `HeapBuf(4)` compiled and aliased cell 3 while the bare
/// `buf[8]` it means was rejected. The golden digests cannot see this: the guest's
/// only `const(...)` uses are blake2s operands, not indexes.
#[test]
fn an_integer_heap_index_is_rejected_however_it_is_spelled() {
    for idx in ["8", "const(8)", "const(4 + 4)", "len(EIGHT)", "GEN * const(4)"] {
        let src = format!(
            "EIGHT = [0, 0, 0, 0, 0, 0, 0, 0]\n\ndef main():\n    buf = HeapBuf(4)\n    buf[{idx}] = 9\n    p = GEN ** 0\n    p[1] = GEN ** 0\n    p[GEN] = GEN ** 0\n    return\n"
        );
        let Err(err) = std::panic::catch_unwind(|| super::build(&src)) else {
            panic!("`buf[{idx}]` was accepted as a heap index");
        };
        let msg = err.downcast_ref::<String>().map(String::as_str).unwrap_or("");
        assert!(
            msg.contains("plain integer naming cell") || msg.contains("not a g-power"),
            "`{idx}`: wanted the ambiguity guard, got `{msg}`"
        );
    }
}

/// A large `**` exponent costs its LOG, not its value.
///
/// The field reading of `b ** k` is computed whether or not the caller wants it,
/// and `field_pow` multiplied `k` times, so this program (which compiles: the
/// index is `1`) took 39 seconds. Square-and-multiply makes it under a
/// millisecond, and a test that would otherwise hang is the way to keep it so.
#[test]
fn a_large_exponent_does_not_cost_its_value() {
    let src = "def main():\n    sa = StackBuf(2)\n    sa[1 ** 4294967295] = 7\n    p = GEN ** 0\n    p[1] = sa[0]\n    p[GEN] = GEN ** 0\n    return\n";
    let started = std::time::Instant::now();
    let _ = super::build(src);
    let took = started.elapsed();
    assert!(
        took < std::time::Duration::from_secs(2),
        "a u32::MAX exponent took {took:?}: field_pow is multiplying k times again"
    );
}
