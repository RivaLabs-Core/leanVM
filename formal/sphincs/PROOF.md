# The 127-bit proof

`sphincs_has_127_bits_of_classical_security` proves the SUF-CMA statement in [Statement.lean](SphincsSecurity/Statement.lean): every adversary with hash budget $q\ge1$ forges with probability at most $q/2^{127}$. All parties share one consistent random oracle, and successful executions contain at most $2^{24}$ signing requests. The root module checks that the proof uses only `propext`, `Classical.choice` and `Quot.sound`.

[Adversary/Accounting.lean](SphincsSecurity/Proof/Adversary/Accounting.lean) proves that erasing the counters preserves the game and its winning probability. [Deterministic/InterfaceReference.lean](SphincsSecurity/Proof/Deterministic/InterfaceReference.lean) reduces seed derivation to independent secrets with loss at most $q/2^{256}$, preserving the query budget. Repeated signing requests use their first response, including failures. Honest derivation calls are handled by presampling and cache coupling inside the proof.

Write $N=2^{128}$, $x=q/N$, $\delta=11/65536$, $r_{\rm cache}=1023/2^{186}+2^{-170}$ and $C=2^{64}$. The proof splits at $q_0=3\cdot2^{114}$. The constant $C$ bounds the honest hash work in the certificate monitors. [Adversary/Security.lean](SphincsSecurity/Proof/Adversary/Security.lean) combines both ranges and the seed loss into the public theorem.

## Layout

| Entry | Role |
| --- | --- |
| [Scheme.lean](SphincsSecurity/Scheme.lean) | Parameters, byte layouts, key generation, signing and verification. |
| [Statement.lean](SphincsSecurity/Statement.lean) | The public SUF game and its query budget. |
| [Proof/Adversary](SphincsSecurity/Proof/Adversary) | Public-game accounting and the final security theorem. |
| [Proof/Deterministic](SphincsSecurity/Proof/Deterministic), [Proof/Seeded](SphincsSecurity/Proof/Seeded) | Seed derivation, memoized signing, cache coupling and budget transfer. |
| [Proof/Base](SphincsSecurity/Proof/Base) | Uniform tables, adaptive posteriors, query caps, traces and probability bounds. |
| [Proof/Scheme](SphincsSecurity/Proof/Scheme), [Proof/Hypertree](SphincsSecurity/Proof/Hypertree) | Honest computations, canonical hash graphs, frontier oracles and verifier witnesses. |
| [Proof/Chains](SphincsSecurity/Proof/Chains), [Proof/Ots](SphincsSecurity/Proof/Ots) | Chain contacts, encoding neighbors, markers and one-time forgery bounds. |
| [Proof/Fts](SphincsSecurity/Proof/Fts) | Registered targets, certificate monitors, proposal words and cache exceptions. |
| [Proof/Reference](SphincsSecurity/Proof/Reference) | The reference experiment, verifier classification and query allocation. |
| [Proof/Residual](SphincsSecurity/Proof/Residual) | The retained residual monitor and large-budget bound. |
| [Proof/Forced](SphincsSecurity/Proof/Forced) | Forced secret guesses, near certificates and the small-budget bound. |

## Large budgets

[Residual/CappedExceptionBound.lean](SphincsSecurity/Proof/Residual/CappedExceptionBound.lean) bounds the independent-secret forgery probability by

$$2x-x^2+(q+C)\frac{\delta}{N}+\frac{C}{N}+(q+C)r_{\rm cache}+2^{-700}.$$

The primitive-event potential bounds the probability of a stop in terms of $q$. Truncating signing after $2^{24}$ requests preserves every successful execution because success requires a valid signing log. The certificate monitor uses the resulting total-work bound $q+C$. A live strong forgery yields a full target certificate unless a cache or proposal-prefix exception occurs.

[Residual/InterfaceLargeBudget.lean](SphincsSecurity/Proof/Residual/InterfaceLargeBudget.lean) absorbs the honest-work terms and seed loss into the $q/2^{160}$ reserve of the closing inequality. This proves the public bound for $q_0\le q\le2^{127}$. For larger budgets, probability at most one suffices.

## Small budgets

[Forced/InterfaceSmallBudget.lean](SphincsSecurity/Proof/Forced/InterfaceSmallBudget.lean) bounds the independent-secret forgery probability by

$$\frac74x+\delta x+2^{-700}+4q r_{\rm cache}+\frac{x^2}{2(1-x)^2}+\frac{1}{N-q}\sum_{j<q}\Pr[F_j].$$

The primitive terms use the allocation of $q$ among prefix, encoding, structural and message queries. The full-certificate bound registers targets only when the adversary or verifier queries them; signing updates existing targets. The certificate bound depends on the number of registered message queries. Two distinct FTS secret guesses contribute $x^2/[2(1-x)^2]$. The event $F_j$ is a near certificate in the game forcing the $j$th eligible secret test to hit.

[Forced/InterfaceNearBound.lean](SphincsSecurity/Proof/Forced/InterfaceNearBound.lean) proves

$$\Pr[F_j]\le\operatorname{nearCertificateBound}(q+C)=557\frac{q+C}{N}+14\bigl((q+C)r_{\rm cache}+2^{-700}\bigr).$$

The forced game is truncated after $2^{24}$ signing requests. Every original near-certificate success survives; truncation may add successes, which is harmless for an upper bound. [Forced/FtsGuessTruncatedBudget.lean](SphincsSecurity/Proof/Forced/FtsGuessTruncatedBudget.lean) proves its total-work bound on the original finite oracle input set. This includes verification of the fallback forgery. [Forced/InterfaceSmallArithmetic.lean](SphincsSecurity/Proof/Forced/InterfaceSmallArithmetic.lean) absorbs the extra near-certificate allowance, shared-cache exception and seed loss into the $q/2^{160}$ reserve, then closes the bound for $1\le q\le q_0$.

## Component facades

Each component's code-specific facts and derived constants sit in a facade module that seals them with `irreducible_def`, so neither the elaborator nor the kernel sees a value outside it. The rest of the proof uses the names and the lemmas the facade proves about them. The equations that expose the code or a numeric constant (their generated `_def` lemmas, and `unitNeighborBound_eq` and `neighborBound_eq`) are used only in the facades and in the closers that check numbers, which [scripts/Taint.lean](scripts/Taint.lean) records. The hash costs are sealed formulas instead: the cost evaluation in [Reference/BoundaryHashEvaluation.lean](SphincsSecurity/Proof/Reference/BoundaryHashEvaluation.lean) and [Reference/SigningBoundaryHashCost.lean](SphincsSecurity/Proof/Reference/SigningBoundaryHashCost.lean) unfolds them to match the algorithms, and the accounting only adds and compares them.

| Facade | Sealed names and facts | Used with their values by |
| --- | --- | --- |
| [Ots/Code.lean](SphincsSecurity/Proof/Ots/Code.lean) | `OtsCode.Valid` and `OtsCode.decode` with `decode_valid`, `decode_some_injective` and `eq_of_le_of_valid` (two valid words are incomparable); a valid `defaultWord`; `signingSteps`; the unit neighbors of a word and their counts `unitNeighborBound` and `neighborBound`; the chain tweak arithmetic; `encodeAttempt` and `otsLeafAttempt` over the sealed decoder, with `encode_eq` and `otsLeaf_eq` identifying them with the statement. | `primitive_rates_small` |
| [Hypertree/Parameters.lean](SphincsSecurity/Proof/Hypertree/Parameters.lean) | `oneTimeKeyHashCost`, `treeNodeHashCost` with its recursion, `keygenHashCost`. | No closer. |
| [Fts/Parameters.lean](SphincsSecurity/Proof/Fts/Parameters.lean) | `ftsOpenHashCost` and `ftsKeyHashCost` with the comparisons the signing budget needs, `fixedProposalLength`, `proposalPrefixSlack`, `fullCertificateExcessRate`, `nearCertificatePrice`, `proposalPrefixExceptionBound`. | The few-time closers below and the closing arithmetic. |
| [ClosingParameters.lean](SphincsSecurity/Proof/ClosingParameters.lean) | `budgetSplit`, `primitiveCoefficient`. | `primitive_rates_small`, the absorption of $r_{\rm cache}$ into `primitiveCoefficient` in [Fts/OriginalCacheExceptionBound.lean](SphincsSecurity/Proof/Fts/OriginalCacheExceptionBound.lean), `small_bound_le_security127` and `native_bound_le_security127`. |

`certificateCacheExceptionRate` is defined with the cache exception analysis in [Fts/CertificateCacheExceptionGrowth.lean](SphincsSecurity/Proof/Fts/CertificateCacheExceptionGrowth.lean) and consumed by name; `certificateCacheExceptionRate_le` gives the closers $r_{\rm cache}\le2^{-169}$.

## Component dependencies

`lake env lean scripts/Taint.lean` writes `taint.txt`, recording each declaration's direct and transitive dependencies on the one-time signature, few-time signature and hypertree definitions, including equations exposing sealed constants. `lake env lean scripts/Reach.lean` writes `reach.txt`, showing which declarations the three public theorems use. These audits identify the affected proof modules when changing a component.

## Why the proof has this shape

Write $x=q/2^{128}$. Each adversary or verifier query carries at most two unit hazards. A query at a hidden coordinate with a candidate value either equals the secret, with probability about $1/2^{128}$ over the remaining candidates, or its fresh output equals the known next chain value, with probability $1/2^{128}$; either outcome gives the adversary a lower digit. The crude route, everything under [Residual](SphincsSecurity/Proof/Residual), charges each adversary or verifier query these two hazards through the potential $1-(1-1/2^{128})^2$ per query and pays the certificate bank out of the same potential, which is why it stops at $2x-x^2$ and then has only $x^2$ left to absorb the certificate excess $\delta x$, the rate at which some index collects eleven or more signatures. Below $q\approx2^{115}$ that excess is larger than $x^2$, and no accounting of the crude kind can help, because any additive term must fit under $x^2$.

The refined route recovers the last bit by showing that a single contact is not a forgery. A one-time forgery needs a two-edge completion, two distinct contacts, or a contact together with an encoding marker, and the first of these is the only first-order event, at $(3/2+4x+2x^2)/(1-x)$ per prefix query. That analysis is [Chains](SphincsSecurity/Proof/Chains) and most of [Ots](SphincsSecurity/Proof/Ots); the forced games of [Forced](SphincsSecurity/Proof/Forced) do the same for the few-time secret guess. Its second-order terms, $557x^2/(1-x)$ for a near certificate followed by a guess and $x^2/[2(1-x)^2]$ for two guesses, grow past the budget above $q\approx3\cdot2^{114}$, so the refined route cannot replace the crude one either. With the target $2x$ and this proof strategy, both routes are needed.

## Changing a component

The rest of the proof consumes the one-time signature through two results.

- **The primitive-event bound.** `referenceGraphContextGame_primitive_small_budget` in [Reference/ReferencePrimitiveBound.lean](SphincsSecurity/Proof/Reference/ReferencePrimitiveBound.lean): on the reference law, the union of the OTS events with the equal-encoding and structural matches plus $(7/4)\mathbb E_R A_{\rm msg}/N$ is at most $(7/4)x$ for $q\le q_0$. Its inputs are the per-event estimates in [Ots](SphincsSecurity/Proof/Ots): two-edge $(3/2+4x+2x^2)\mathbb E Q/N$, distinct contacts $4x\mathbb E Q/[(1-x)^2N]$, marker and contact $(2b_1x\mathbb E Q+2b_2x\mathbb E A_{\rm enc})/[(1-x)N]$ with $b_1$ = `unitNeighborBound` and $b_2$ = `neighborBound`, and equal encoding $\mathbb E A_{\rm enc}/N$. None of these depends on the chain length or on how the code is defined; `primitive_rates_small` checks them against `primitiveCoefficient`, and the closing arithmetic absorbs a total primitive coefficient of up to about $1.88$ in place of $7/4$.
- **The layer witness.** `layer_reference_classification` in [Ots/ReferenceLayerWitness.lean](SphincsSecurity/Proof/Ots/ReferenceLayerWitness.lean) with `otsLeaf_classification` in [Ots/OtsVerifierWitness.lean](SphincsSecurity/Proof/Ots/OtsVerifierWitness.lean): an accepting layer whose recovered root is canonical either fixes the reference opening or exhibits one of the primitive events on the actual verifier trace. `verify_classification` in [Reference/VerifierWitnessClassification.lean](SphincsSecurity/Proof/Reference/VerifierWitnessClassification.lean) composes it through the hypertree and the FTS layer.

**A different chain code.** A change of `winternitzBits`, `numChains`, the target sum or the encoding itself touches `Scheme.lean` and [Ots/Code.lean](SphincsSecurity/Proof/Ots/Code.lean): the decoder's validity and injectivity, the incomparability of valid words, a valid default word, the unit-neighbor counts and the chain tweak arithmetic. The two results above then hold unchanged, and `primitive_rates_small` rechecks the rates with the new counts. If the signature layout changes too, for example a code that needs no counter, the statement bridges [SignatureLayout.lean](SphincsSecurity/Proof/SignatureLayout.lean), [Scheme/StatementLemmas.lean](SphincsSecurity/Proof/Scheme/StatementLemmas.lean) and [Seeded/AlgorithmErasure.lean](SphincsSecurity/Proof/Seeded/AlgorithmErasure.lean) follow it.

**Different few-time parameters.** `ftsTreeHeight`, `ftsTrees`, `signatureLimit` and `digestAttemptLimit` enter through `Scheme.lean` and [Fts/Parameters.lean](SphincsSecurity/Proof/Fts/Parameters.lean). Reference, Residual, Forced, Hypertree and Ots use the few-time constants by name only. The few-time analysis checks the values in its closers:

- the proposal-word moments at rate $19/50$ and the terminal price: [Base/StirlingMomentBounds.lean](SphincsSecurity/Proof/Base/StirlingMomentBounds.lean), [Fts/FixedProposalMoments.lean](SphincsSecurity/Proof/Fts/FixedProposalMoments.lean), [Fts/FixedCertificateCoverage.lean](SphincsSecurity/Proof/Fts/FixedCertificateCoverage.lean), [Fts/UnitCertificateCoverage.lean](SphincsSecurity/Proof/Fts/UnitCertificateCoverage.lean) for $\delta$ and [Fts/NearCertificateBound.lean](SphincsSecurity/Proof/Fts/NearCertificateBound.lean) for $557$;
- the digest cache exceptions, with admissibility $2^{-10}$ and thresholds $2^{83}$ and $2^{80}$: [Fts/CertificateCacheExceptionGrowth.lean](SphincsSecurity/Proof/Fts/CertificateCacheExceptionGrowth.lean), [Fts/CertificateCacheExceptionPotential.lean](SphincsSecurity/Proof/Fts/CertificateCacheExceptionPotential.lean), the `MessageDeficit*` and `MessageAdmissibleDeficit` modules and the `CachedIndex*` modules;
- the arrival rate $2^{-36}$ and the proposal overhead $1537/1024$: [Scheme/RawQueryMomentBound.lean](SphincsSecurity/Proof/Scheme/RawQueryMomentBound.lean), [Fts/RawProposalMomentBound.lean](SphincsSecurity/Proof/Fts/RawProposalMomentBound.lean), [Fts/UniformProposalMoments.lean](SphincsSecurity/Proof/Fts/UniformProposalMoments.lean), [Fts/TerminalProposalEnvelope.lean](SphincsSecurity/Proof/Fts/TerminalProposalEnvelope.lean), [Fts/SigningProposalRecord.lean](SphincsSecurity/Proof/Fts/SigningProposalRecord.lean) and [Fts/DigestSelectionIndex.lean](SphincsSecurity/Proof/Fts/DigestSelectionIndex.lean);
- the prefix exception $2^{-700}$: [Fts/ProposalPrefixExponential.lean](SphincsSecurity/Proof/Fts/ProposalPrefixExponential.lean).

**Different hypertree heights.** Layer heights enter the accounting only through [Hypertree/Parameters.lean](SphincsSecurity/Proof/Hypertree/Parameters.lean). The number of layers is fixed by the statement's three-layer sequencing, which the layer arithmetic of `StatementLemmas`, `Descent` and the verifier witnesses follows.

In every case the closing arithmetic in [Forced/InterfaceSmallArithmetic.lean](SphincsSecurity/Proof/Forced/InterfaceSmallArithmetic.lean) and [Residual/InterfaceLargeBudget.lean](SphincsSecurity/Proof/Residual/InterfaceLargeBudget.lean), together with their underlying inequalities, rechecks the bound with the new values. The honest-work bounds in [Reference/HonestHashAllowance.lean](SphincsSecurity/Proof/Reference/HonestHashAllowance.lean) and [Reference/VerificationHashAllowance.lean](SphincsSecurity/Proof/Reference/VerificationHashAllowance.lean) also depend on the concrete parameters.

## Query accounting

[Accounting.lean](SphincsSecurity/Proof/Adversary/Accounting.lean) proves that erasing the query counters recovers the uncounted game. [CountedTrace.lean](SphincsSecurity/Proof/Adversary/CountedTrace.lean) identifies the budget in [Statement.lean](SphincsSecurity/Statement.lean) with the hash count on the adversary and final-verification trace, before signing requests are expanded.

[RegisteredTargets.lean](SphincsSecurity/Proof/Fts/RegisteredTargets.lean) restricts the FTS certificate forecast to targets registered by the adversary or verifier. Signing updates existing targets. [RegisteredTargetMonitor.lean](SphincsSecurity/Proof/Fts/RegisteredTargetMonitor.lean) bounds the number of registered targets by the hash-query count.

[RegisteredTargetSource.lean](SphincsSecurity/Proof/Fts/RegisteredTargetSource.lean) proves that every admissible cached message digest is registered or was processed by signing. This includes failed signing calls. [RegisteredForgerySource.lean](SphincsSecurity/Proof/Reference/RegisteredForgerySource.lean) excludes processed inputs for canonical strong forgeries: replay would reproduce the forgery as the recorded signing response. Thus this source argument requires no signing-failure exception.

[RegisteredCacheException.lean](SphincsSecurity/Proof/Fts/RegisteredCacheException.lean) bounds the probability of a shared-cache exception at any point while the signing log is valid by $4q\cdot\texttt{certificateCacheExceptionRate}$. The proof tracks cache entries created by adversary and verifier queries. Signing adds at most one unregistered admissible digest per request and at most $2^{32}$ message-hash entries per request. These bounds control the moments of the shared cache.

[RegisteredProposalBound.lean](SphincsSecurity/Proof/Fts/RegisteredProposalBound.lean) derives the signer reuse bound and proposal acceptance cap outside that cache exception. It uses a bound on cached randomizers for each message. [RegisteredProposalExecution.lean](SphincsSecurity/Proof/Fts/RegisteredProposalExecution.lean) constructs the proposal process, proves that its completed proposal word is uniform, and proves that erasing the proposal bookkeeping recovers the registered-target experiment.

[RegisteredCertificateRates.lean](SphincsSecurity/Proof/Fts/RegisteredCertificateRates.lean) proves the full- and near-certificate bounds for registered targets, including the proposal-prefix and shared-cache stopping probabilities. The full-certificate bound charges its main term to adversary and verifier message queries. [RegisteredCertificateCoverage.lean](SphincsSecurity/Proof/Reference/RegisteredCertificateCoverage.lean) applies the adaptive bound to canonical certificates.

[InterfaceReference.lean](SphincsSecurity/Proof/Deterministic/InterfaceReference.lean) reduces the public experiment to the independent-secret experiment, preserving the query budget and adding at most $q/2^{256}$ for seed guessing. Repeated signing requests are memoized, including failures. The small- and large-budget closing inequalities allow an additional $q/2^{160}$ error term. [RegisteredGameBudget.lean](SphincsSecurity/Proof/Reference/RegisteredGameBudget.lean) transfers the public budget to the certificate monitor after key generation. [ReferenceInterfaceBudget.lean](SphincsSecurity/Proof/Reference/ReferenceInterfaceBudget.lean) transfers it to the reference game and proves that its prefix, encoding, other structural and message query counts sum to at most $q$. [ReferenceCanonicalCertificate.lean](SphincsSecurity/Proof/Reference/ReferenceCanonicalCertificate.lean) connects canonical strong forgeries to registered certificates. [InterfacePrimitiveBound.lean](SphincsSecurity/Proof/Reference/InterfacePrimitiveBound.lean) and [InterfaceNearBound.lean](SphincsSecurity/Proof/Forced/InterfaceNearBound.lean) prove the primitive and forced-query bounds under the query budget.

## Completeness

`sphincs_is_correct` and `sphincs_is_complete` in [SphincsSecurity.lean](SphincsSecurity.lean) prove the two claims of [Completeness.lean](SphincsSecurity/Completeness.lean); the proofs are under [Completeness](SphincsSecurity/Completeness). `SphincsCorrectnessStatement`: for every hash function, a signature the signer produces for a generated key verifies; this is `verify_of_sign`, the recovery argument of `doc/sphincs` §sec:ver. `SphincsCompletenessStatement`: the sum over all messages of the probability that the honest experiment against the security game's random oracle fails is at most $2^{-256}$, where failing means signing returned $\bot$ or verification rejected. This is the union-bound budget for the theorem in `doc/sphincs` §sec:completeness, with the failure event widened to rejection. The proof takes from the security development only byte-layout lemmas, the replay lemmas for the lazy oracle, and two probabilities of a fresh answer.

Unlike the security proof, completeness needs a lower bound on the size of the one-time code, so [Completeness/Code.lean](SphincsSecurity/Completeness/Code.lean) and [Completeness/Encoding.lean](SphincsSecurity/Completeness/Encoding.lean) use the target-sum code and its values directly, as a closer does. A different code means recounting there; the rest of the completeness proof reads the code only through the statement's algorithms.

| File | Role |
| --- | --- |
| [Completeness/Assembly.lean](SphincsSecurity/Completeness/Assembly.lean) | Combines key generation, the signing bound and the closing arithmetic into `complete`. |
| [Completeness/Recovery.lean](SphincsSecurity/Completeness/Recovery.lean) | `verify_of_sign`: under any answer function, a signature the signer produced verifies. |
| [Completeness/Game.lean](SphincsSecurity/Completeness/Game.lean) | Pulls the seed out of the experiment; recovery then charges failure to signing returning `none`. |
| [Completeness/Signing.lean](SphincsSecurity/Completeness/Signing.lean) | Union bound through `sign`: the randomizer search and three counter searches, each counter search starting on uncached inputs. |
| [Completeness/Fresh.lean](SphincsSecurity/Completeness/Fresh.lean), [Completeness/Keygen.lean](SphincsSecurity/Completeness/Keygen.lean) | Domain separation: key generation and every earlier signing step avoid the inputs a later search hashes. |
| [Completeness/Search.lean](SphincsSecurity/Completeness/Search.lean), [Completeness/Counter.lean](SphincsSecurity/Completeness/Counter.lean) | A search over fresh distinct inputs exhausts $n$ trials with probability at most its rejection share to the $n$; the counter search is one. |
| [Completeness/Digest.lean](SphincsSecurity/Completeness/Digest.lean) | The randomizer search, whose digest query repeats when a randomizer does: the set of drawn randomizers charges at most $2^{32}/2^{128}$ per trial. |
| [Completeness/Code.lean](SphincsSecurity/Completeness/Code.lean), [Completeness/Encoding.lean](SphincsSecurity/Completeness/Encoding.lean) | At least $2^{114}$ of the $2^{128}$ digests decode, counted as one big-number division in the kernel, so one counter trial rejects at most $1-2^{-14}$. |
| [Completeness/Decay.lean](SphincsSecurity/Completeness/Decay.lean) | $(1-1/m)^m\le1/2$, and the closing sum below $2^{-256}$. |
