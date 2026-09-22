import SphincsSecurity.Scheme

/-!
# SPHINCS: correctness and completeness

Correctness and completeness of the scheme in `Scheme.lean`. The public theorems are in `SphincsSecurity.lean`.
-/

open OracleComp OracleSpec ENNReal

namespace SphincsSecurity

/-- Every returned signature verifies under the same hash function and generated key pair. -/
abbrev SphincsCorrectnessStatement : Prop :=
  ∀ (hash : QueryImpl HashSpec Id) (seed : MasterSeed) (message : Message) (signature : Signature),
    let keys := evalWithAnswerFn hash (Seeded.keygenFromSeed seed)
    evalWithAnswerFn hash (Seeded.sign keys.2 message : OracleComp HashSpec (Option Signature)) = some signature →
    evalWithAnswerFn hash (Concrete.verify keys.1 message signature : OracleComp HashSpec Bool) = true

namespace Completeness

/-- The honest run: sample the master seed, generate a key, sign, and verify. -/
noncomputable def gameCore (message : Message) : OracleComp OracleWorld Bool := do
  let seed ← liftM sampleMasterSeed
  let (pk, sk) ← liftM (Seeded.keygenFromSeed seed)
  let some signature ← liftM (Seeded.sign sk message : OracleComp HashSpec (Option Signature))
    | return false
  liftM (Concrete.verify pk message signature : OracleComp HashSpec Bool)

/-- Private sampling and a shared random oracle. -/
noncomputable def romImpl : QueryImpl OracleWorld (StateT (QueryCache HashSpec) ProbComp) :=
  unifFwdImpl HashSpec + (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))

noncomputable def experiment (message : Message) : ProbComp Bool :=
  (simulateQ romImpl (gameCore message)).run' ∅

end Completeness

/-- The sum of honest-run failure probabilities over all messages is at most `2⁻²⁵⁶`. -/
abbrev SphincsCompletenessStatement : Prop :=
  ∑' message : Message, Pr[= false | Completeness.experiment message]
    ≤ ((2 ^ 256 : Nat) : ℝ≥0∞)⁻¹

end SphincsSecurity
