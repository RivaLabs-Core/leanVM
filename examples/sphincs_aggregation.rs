//! Aggregate a handful of SPHINCS+ signatures into one proof, then verify it.
//!
//! ```sh
//! cargo run --release --example sphincs_aggregation
//! ```

use leanvm::*;

const N_SIGNERS: usize = 8;
const LOG_INV_RATE: usize = 2; // 1 = bigger proof, faster proving. 4 = smaller proof, slower proving.

fn main() {
    setup_prover();
    let rng = &mut rand::rng();

    let signatures: Vec<_> = (0..N_SIGNERS)
        .map(|i| {
            let (secret_key, public_key) = sphincs::key_gen(rng);
            let message = [i as u8; sphincs::MESSAGE_LEN];
            let signature = sphincs::sign(&secret_key, &message);
            sphincs::verify(&public_key, &message, &signature).unwrap();
            (public_key, message, signature)
        })
        .collect();

    let proof = aggregate(&[], vec![], signatures, &[], None, LOG_INV_RATE).unwrap();

    let bytes = proof.to_bytes();
    let received = EthereumProof::from_bytes(&bytes).unwrap();
    received.verify().unwrap(); // verify the snark is valid

    let n = received.sphincs_signers().len();
    let kib = |bytes: usize| bytes as f64 / 1024.0;
    println!(
        "{n} SPHINCS+ signatures ({n} x {:.1} KiB = {:.1} KiB) aggregated into a {:.1} KiB proof",
        kib(sphincs::SIG_SIZE),
        kib(n * sphincs::SIG_SIZE),
        kib(bytes.len())
    );
}
