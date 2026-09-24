//! Aggregate a handful of SPHINCS+ signatures into one proof, then verify it.
//!
//! ```sh
//! N_SPHINCS=80 cargo run --release --example sphincs_aggregation
//! ```

use leanvm::*;

const LOG_INV_RATE: usize = 2; // 1 = bigger proof, faster proving. 4 = smaller proof, slower proving.

fn main() {
    setup_prover();
    let rng = &mut rand::rng();

    let n_signers: usize = std::env::var("N_SPHINCS").map_or(8, |n| n.parse().expect("N_SPHINCS is a number"));

    let signatures: Vec<_> = (0..n_signers)
        .map(|i| {
            let (secret_key, public_key) = sphincs::key_gen(rng);
            let message = [i as u8; sphincs::MESSAGE_LEN];
            let signature = sphincs::sign(&secret_key, &message);
            sphincs::verify(&public_key, &message, &signature).unwrap();
            (public_key, message, signature)
        })
        .collect();

    // What the proof will claim: each (public key, message) pair, sorted.
    let mut claims: Vec<SphincsClaim> = signatures.iter().map(|(pk, message, _)| (*pk, *message)).collect();
    claims.sort();

    let time = std::time::Instant::now();
    let proof = aggregate(&[], vec![], signatures, &[], None, LOG_INV_RATE).unwrap_or_else(|e| {
        eprintln!("aggregation failed: {e}");
        std::process::exit(1)
    });
    let aggregation_time = time.elapsed();
    println!(
        "Aggregation took: {:?} ({:.1} sphincs / s)",
        aggregation_time,
        n_signers as f64 / aggregation_time.as_secs_f64()
    );

    let bytes = proof.to_bytes();
    let received = EthereumProof::from_bytes(&bytes).unwrap();

    let time = std::time::Instant::now();
    received.verify().unwrap(); // verify the snark is valid
    println!("Verification took: {:?}", time.elapsed());

    // sanity check:
    assert_eq!(received.sphincs_signers(), claims);

    let kib = |bytes: usize| bytes as f64 / 1024.0;
    println!(
        "{n_signers} SPHINCS+ signatures ({n_signers} x {:.1} KiB = {:.1} KiB) aggregated into a {:.1} KiB proof",
        kib(sphincs::SIG_SIZE),
        kib(n_signers * sphincs::SIG_SIZE),
        kib(bytes.len())
    );
}
