# SPHINCS security in Lean 4

[Scheme.lean](SphincsSecurity/Scheme.lean) defines the scheme with a 32-byte master seed: parameters, hash inputs, key generation, signing, and verification. [Statement.lean](SphincsSecurity/Statement.lean) defines the SUF-CMA game in the classical random-oracle model, with at most `2^24` signing requests per key.

[Completeness.lean](SphincsSecurity/Completeness.lean) states the other side. Correctness, for every hash function: a signature the signer produces verifies. Completeness, against the same random oracle: the sum over all messages of the probability that sampling a seed, generating a key, signing and verifying fails is at most $2^{-256}$, where failing means the signer returned no signature or the verifier rejected it. This is the union-bound budget for one key signing every message. `sphincs_is_correct` and `sphincs_is_complete` prove the two statements; [PROOF.md](PROOF.md#completeness) outlines the route.

Messages are 256-bit values. The adversary is terminating and adaptive, with private randomness and no fixed time or memory bound. The probability is over the master seed, the shared consistent random oracle and the adversary's private randomness. [Accounting.lean](SphincsSecurity/Proof/Adversary/Accounting.lean) proves that erasing the counters recovers the uncounted game and preserves its winning probability.

`sphincs_has_127_bits_of_classical_security` proves that every adversary with budget `q ≥ 1` forges with probability at most `q / 2^127`. [PROOF.md](PROOF.md) explains the reduction and query accounting.

## Build and audit

Use the pinned Lean toolchain and VCVio revision:

```sh
cd formal/sphincs
lake exe cache get
lake build
```

The cache command is needed on initial setup. The root module uses `#guard_msgs` to check that the audited proofs depend only on `propext`, `Classical.choice` and `Quot.sound`. Running `lake env lean scripts/Reach.lean` writes `reach.txt`, listing each local declaration, its source range and whether the proofs listed in [scripts/Reach.lean](scripts/Reach.lean) use it.

## Where to work

[PROOF.md](PROOF.md) explains the route, the constants, the component facades that seal each component's parameters, and which modules must change if a component changes. The proof is split by component:

| Entry | Purpose |
| --- | --- |
| [SphincsSecurity.lean](SphincsSecurity.lean) | The public theorems. |
| [Completeness](SphincsSecurity/Completeness) | Correctness and completeness: recovery, the reduction of failure to signing returning `none`, and the bounds on signing's four searches. |
| [Proof/Deterministic](SphincsSecurity/Proof/Deterministic) | Seed derivation, coupling to independent secrets, and the final security bound. |
| [Proof/Adversary/Security.lean](SphincsSecurity/Proof/Adversary/Security.lean) | Combines both budget ranges into the public security theorem. |
| [Proof/Base](SphincsSecurity/Proof/Base) | Scheme-independent tooling: uniform tables and their exact adaptive posteriors, query caps, pauses and traces, oracle query charges, moment bounds. |
| [Proof/Scheme](SphincsSecurity/Proof/Scheme) | The concrete game over a query cache, honest computation and witness extraction from an accepting signature. |
| [Proof/Hypertree](SphincsSecurity/Proof/Hypertree) | The canonical graph of honest hash inputs, frontier oracles, structural matches, layer and hypertree witnesses. |
| [Proof/Chains](SphincsSecurity/Proof/Chains) | Abstract chain tables and their adaptive query bounds, independent of the scheme. |
| [Proof/Ots](SphincsSecurity/Proof/Ots) | The one-time signature: prefix simulation, contacts, encoding neighbors, markers and matches on the concrete chains, the OTS verifier witness. |
| [Proof/Fts](SphincsSecurity/Proof/Fts) | The few-time signature and message digest: target certificates, the banked monitor, proposal words, the terminal certificate price, cache exceptions. |
| [Proof/Reference](SphincsSecurity/Proof/Reference) | The reference experiment: sampled reference family, forgery source, verifier classification, primitive-event union, query allocation, certificate coverage. |
| [Proof/Residual](SphincsSecurity/Proof/Residual) | The retained residual monitor on the original game and the large-budget theorem. |
| [Proof/Forced](SphincsSecurity/Proof/Forced) | The secret-guess interpreter, the forced FTS games, their monitored runs and the small-budget arithmetic. |
