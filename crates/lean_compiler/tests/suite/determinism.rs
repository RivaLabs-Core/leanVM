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
    ("conditionals", "24a1d24fe5eeb7d1ec419d94f29963020ffbf9fb12a9332e6360f6e56f844725"),
    ("const_params", "7b35f31c0a0a0be01c4f6720c9bd276989541feb880eab3a2317d5c4b5d2183e"),
    ("fibonacci", "48b216045533859168acc81e8b4462608e478cdc4bd52ff2556003c327281e6e"),
    ("hash_heap_chain", "27ab2e2ffa76dc241f84e47766109d8aba72320480d9cf6b01dfbd0523930b76"),
    ("hash_slices", "163c88ca144d9afc324ccf61aadb5fcd1b52ac5f69dd8cef280a1785bcafd4ec"),
    ("heapbuf_dyn", "356e83040d827295a28bcd971039bdc57bf4f029ff23c9a7dba9d944fdd27a0a"),
    ("hint", "e5c81e7100c495db1dfe5d7c36322df2d5b40dd8e8e3df3731bff17169cbc7cd"),
    ("identities", "e00d45595ef738523cbeb4c8a9c5e011688810b2fb957eb9d3ecce4fa5ef7b20"),
    ("match", "3c022d6025e72302c5bb37ffcce828e183acc2515a4864b6368feb457f3cb522"),
    ("match_arms", "771cc426d596e9868a2577cee192495a962b17ce4b5d3ef7ae52d6f3688b6cb8"),
    ("nested", "ccb1d023e35cd72e502daf588171a7b09c757500e772d2dcdc0dfa8a5f195e0a"),
    ("runtime_loop", "33930720a6e6fc5b8296c1cbf3701010c61d1950f1e72707f63869671a2c416a"),
    ("scoping", "4679f159f9b1c4c3bc2c4054de91c90087e941684355bece40580e4c58465457"),
    ("unroll", "2de58fc734f2858b339005996c88546a4cee8068f34f75ee09ba542f611a2acf"),
    ("wots_walk", "d279e6f7b487ef12de47a4fa37c7b65f16772c4de4e60337fdd4f25fcb4cdc71"),
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
