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
    ("conditionals", "403f17d0ce5316049962b07eaa74c9f55c7c94add1d14978697a3487e3d54912"),
    ("const_params", "f0816c2457b66413300192aabab590726e605bc551115c9252f26269d8ddd532"),
    ("fibonacci", "ea71300abd23765da4f368175d4d0857b7b1175e121bccae42bd39d2dbb682cc"),
    ("field192", "30d6d705f008a775a5e619a2ee3011bf8f39ea0244eaa10fc668d66c5a26ae02"),
    ("hash_heap_chain", "7f19d09176d36956983a684b021c1b9c7897cafe3ec34fecfcc440c6203a60b5"),
    ("hash_slices", "821c3206c7f5ce9cf37dff51bf8d2bd42c480e855d8ee120d465bc615abfc0fe"),
    ("heapbuf_dyn", "cc6ac06781d7b71d7bbee5cb55d56dd4b7dee30ff45e433ae7fae5a26715690d"),
    ("hint", "743fd1ba4dbe1bca619ef3b790681f14f3e3e5eb750c242be663373be8c266e9"),
    ("identities", "b9e28816fcc5465c3d18801934d89d1cd0e39af798278ba29ddc313716f8d111"),
    ("match", "f561aad705e79b8fa1ab304234aea570df0097d413451334b6d4b3cd22c3a3f7"),
    ("match_arms", "bad6c31b086d81fb8d31e7e3207188f0331d598dab498ddbd1511fb7616d6149"),
    ("nested", "b24339ff465c09e2f3efd0c8c349ee8b9d21ef74a7a5c64d01898b4c35bef48d"),
    ("runtime_loop", "18435f31c81f25baaa40e72964746a4d95f441f1c4854599d89f1d641053d378"),
    ("scoping", "0c37e2e4f7d5481b041752c2b0a5f737477cc57c8ec4d19acf4061ed572e0248"),
    ("unroll", "28af13b92d23587254ddd72d1c66f5320417b84c280d07ba8787d79688360409"),
    ("wots_walk", "1711401e58484c9158ae987e4c32342bdc0cf48cfbed2f85981ab1aad8f9b5f0"),
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
