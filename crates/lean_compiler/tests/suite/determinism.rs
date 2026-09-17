//! One source compiles to one program, always, and the same program it compiled
//! to yesterday.
//!
//! The bytecode digest leads the Fiat--Shamir transcript, so two builds of one
//! source that disagree are two incompatible proof systems, and the symptom is a
//! proof that stops verifying rather than a crash.
//!
//! Two different properties, and only the first is about determinism:
//!
//! * *Within a process*, compiling twice is a real perturbation rather than a
//!   repeat, since `RandomState` bumps its seed once per map, so the second
//!   compilation hashes with different keys than the first.
//! * *Across commits*, `GOLDEN` is a SNAPSHOT of the compiler's output. It does
//!   not prove determinism (nothing iterating a hash container reaches the
//!   bytecode today, and deliberately reversing the branch-output order at a join
//!   moves no digest). It earns its place a different way: a codegen change that
//!   was not intended shows up here and nowhere else, and every entry that moved
//!   this far was a change someone then had to justify.
//!
//! So a moved digest is a question, not a chore: update `GOLDEN` in the same
//! commit and say in the message which change moved it.

use std::collections::BTreeMap;
use std::fs;

use lean_compiler::{compile, parse};
use lean_vm::cpu::Program;

/// `tests/programs/<name>.py` against the digest of the bytecode it compiles to.
/// The list is closed: a new program must be added here, so one cannot be added
/// without a digest.
#[rustfmt::skip]
const GOLDEN: &[(&str, &str)] = &[
    ("conditionals", "edfb33d8f77319329356f1e608f0c9623fbb6222ffb663d74d167d5038f8342f"),
    ("const_params", "7f1147ac3108a3a779743b5c55f85e42ce8f2a46e2246a33ca3feb5f48e5e01e"),
    ("fibonacci", "ce2a648745803b0c5113b087cb56045ff5b11ff80ad73cfd62d66a57432fd03e"),
    ("hash_heap_chain", "49b69e568fb7c34dbc47ec662f0cde837b5abef5a078aa1a95604112c850e19a"),
    ("hash_slices", "b9dcbfc93ff15d13bb46154d9c12a1fc6ef2a0846159957b7d23ec89acc5272a"),
    ("heapbuf_dyn", "3e73dee3438dfc4b7942ba6288df24078dfbc67eb2b07e22e4eb60763c336ec1"),
    ("hint", "ffb265d8c0eb6ff2cb4fb63dfb40a77d2f59a5572fb278f2e176a6a2e89a3024"),
    ("identities", "e084756d25543ec55584ad14dadcb8c41bdd39be75826c112c6f86a4fc6fdb41"),
    ("match", "8d17f58edd00cbc8ded2e1399c4eb913adf5e68dd21d93543fa75cc65b3973d7"),
    ("match_arms", "cc8c2fe759bd67e52d462c9115c1f93a93be97e62703a9a9cb0e0e9030532d89"),
    ("nested", "e2793ec7509a40968e60d764c5b034bcc2f7e019dd908f66604d96a046c21a78"),
    ("runtime_loop", "7127a8e15dafb2b1b939fba674f82afe00afa73b1d29d04070c7c06aec7a7317"),
    ("scoping", "e7de8a8592dc03dc88cb437e71d50de23b00bc0d2ffcd2908d999f3b098084e8"),
    ("u64", "bc57b6323a753bc50f7035d6b2d2d77fc7f0614d5d7399089dab14641e52b26b"),
    ("unroll", "1e0566b710e4dfb3e5da82eca677dfea2b92ba8dc47ffa7490304e9108ff4332"),
    ("wots_walk", "8bda1098ad5dac6b4da82f2e6c696d5cfc47ab9e34a2da498c153463869de2df"),
];

fn digest(p: &Program) -> String {
    primitives::hash::hash(format!("{:?}", p.prog).as_bytes())
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect()
}

/// Every program in `tests/programs/`, compiled twice.
#[test]
fn bytecode_is_reproducible() {
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/programs");
    let mut paths: Vec<_> = fs::read_dir(dir)
        .expect("tests/programs")
        .map(|e| e.expect("dir entry").path())
        .filter(|p| p.extension().is_some_and(|x| x == "py"))
        .collect();
    paths.sort();
    assert!(!paths.is_empty(), "no .py programs found");

    let mut actual: Vec<(String, String)> = Vec::new();
    for path in &paths {
        let name = path.file_stem().expect("file stem").to_string_lossy().into_owned();
        let src = fs::read_to_string(path).unwrap_or_else(|e| panic!("{name}: read: {e}"));
        let one = compile(&parse(&src).unwrap_or_else(|e| panic!("{name}: parse: {e}")));
        let two = compile(&parse(&src).unwrap_or_else(|e| panic!("{name}: parse: {e}")));
        assert_eq!(
            digest(&one),
            digest(&two),
            "{name}: two compilations of one source produced different bytecode, \
             so the compiler is reading a hash seed"
        );
        actual.push((name, digest(&one)));
    }

    let want: BTreeMap<&str, &str> = GOLDEN.iter().copied().collect();
    let moved: Vec<&str> = actual
        .iter()
        .filter(|(n, d)| want.get(n.as_str()) != Some(&d.as_str()))
        .map(|(n, _)| n.as_str())
        .collect();
    let dropped: Vec<&str> = want
        .keys()
        .copied()
        .filter(|n| !actual.iter().any(|(a, _)| a == n))
        .collect();
    assert!(
        dropped.is_empty(),
        "GOLDEN names a program that no longer exists: {dropped:?}"
    );
    if !moved.is_empty() {
        let table: String = actual
            .iter()
            .map(|(n, d)| format!("    (\"{n}\", \"{d}\"),\n"))
            .collect();
        panic!("bytecode changed for {moved:?}\n\nif that was intended, GOLDEN is now:\n{table}");
    }
}
