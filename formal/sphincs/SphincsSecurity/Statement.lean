import SphincsSecurity.Scheme
import VCVio.OracleComp.QueryTracking.WriterCost
import SphincsSecurity.Proof.Base.QueryCap

/-!
# SPHINCS security statement

Strong unforgeability under chosen-message attacks (SUF-CMA) in the classical random-oracle model for the scheme in `Scheme.lean`.
-/

open OracleComp OracleSpec ENNReal

namespace SphincsSecurity

/-! ## The security experiment -/

/-- A claimed forgery: a message and a signature. -/
structure Forgery where
  message : Message
  signature : Signature
deriving DecidableEq

/-- A signing request returns a signature or `none`. -/
abbrev SigningSpec := Message →ₒ Option Signature

namespace SigningTranscript

/-- At most `signatureLimit` signing requests, including repeats and failures. -/
def Valid (log : QueryLog SigningSpec) : Prop := log.length ≤ signatureLimit

instance (log : QueryLog SigningSpec) : Decidable (Valid log) :=
  inferInstanceAs (Decidable (log.length ≤ signatureLimit))

/-- The signer returned this exact message-signature pair. -/
def Contains (log : QueryLog SigningSpec) (forgery : Forgery) : Prop :=
  ∃ entry ∈ log, entry.1 = forgery.message ∧ entry.2 = some forgery.signature

instance (log : QueryLog SigningSpec) (forgery : Forgery) : Decidable (Contains log forgery) :=
  inferInstanceAs
    (Decidable (∃ entry ∈ log, entry.1 = forgery.message ∧ entry.2 = some forgery.signature))

end SigningTranscript

namespace Security

/-- A terminating adaptive adversary with private randomness, hashing and signing. -/
structure Adversary where
  main : PublicKey → OracleComp (OracleWorld + SigningSpec) Forgery

/-- Record each signing request and its answer. -/
def signingOracle (sk : Seeded.SecretKey) :
    QueryImpl SigningSpec (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) :=
  QueryImpl.withLogging fun request => liftM (Seeded.sign sk request : OracleComp HashSpec _)

/-- Sample the master seed, then run all parties with one shared hash oracle. -/
noncomputable def gameCore (adversary : Adversary) : OracleComp OracleWorld Bool := do
  let seed ← liftM sampleMasterSeed
  let (pk, sk) ← liftM (Seeded.keygenFromSeed seed)
  let ((forgery, log) : Forgery × QueryLog SigningSpec) ←
    (simulateQ (QueryImpl.ofLift OracleWorld (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) + signingOracle sk) (adversary.main pk)).run
  let verified ← liftM (Concrete.verify pk forgery.message forgery.signature : OracleComp HashSpec Bool)
  return decide (SigningTranscript.Valid log ∧ ¬SigningTranscript.Contains log forgery) && verified

/-- A hash query made by the adversary. -/
def IsAdversaryHash : (OracleWorld + SigningSpec).Domain → Prop
  | .inl (.inr _) => True
  | _ => False

instance : DecidablePred IsAdversaryHash := fun input => by
  cases input with
  | inl input => cases input <;> simp only [IsAdversaryHash] <;> infer_instance
  | inr _ => simp only [IsAdversaryHash]; infer_instance

def IsHash : OracleWorld.Domain → Prop
  | .inl _ => False
  | .inr _ => True

instance : DecidablePred IsHash := fun input => by
  cases input <;> simp only [IsHash] <;> infer_instance

/-- Hash calls by the adversary and final verifier, including cache hits. -/
structure HashQueries where
  adversary : Nat
  verification : Nat
deriving DecidableEq

def HashQueries.total (queries : HashQueries) : Nat :=
  queries.adversary + queries.verification

noncomputable def countAdversary {α : Type} (sign : QueryImpl SigningSpec (OracleComp OracleWorld))
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    OracleComp OracleWorld ((α × Nat) × QueryLog SigningSpec) :=
  (simulateQ (QueryImpl.ofLift OracleWorld (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) +
    QueryImpl.withLogging sign) (QueryCap.counted IsAdversaryHash computation)).run

/-- Record the signing transcript and hash-query counts. -/
noncomputable def countedGameCore (adversary : Adversary) : OracleComp OracleWorld (Bool × HashQueries) := do
  let seed ← liftM sampleMasterSeed
  let (pk, sk) ← liftM (Seeded.keygenFromSeed seed)
  let ((forgery, queries), log) ←
    countAdversary (fun request => liftM (Seeded.sign sk request : OracleComp HashSpec _)) (adversary.main pk)
  let (verified, verification) ← QueryCap.counted IsHash
    (liftM (Concrete.verify pk forgery.message forgery.signature : OracleComp HashSpec Bool))
  return (decide (SigningTranscript.Valid log ∧ ¬SigningTranscript.Contains log forgery) && verified,
    ⟨queries, verification⟩)

/-- Run the SUF game against a shared random oracle. -/
noncomputable def experiment (adversary : Adversary) : ProbComp (Bool × HashQueries) :=
  (simulateQ (unifFwdImpl HashSpec +
    (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp)))
    (countedGameCore adversary)).run' ∅

/-- The probability of a successful forgery. -/
noncomputable def forgeAdvantage (adversary : Adversary) : ℝ≥0∞ :=
  Pr[fun result => result.1 = true | experiment adversary]

/-- Worst-case hash-query bound over executions of the experiment. -/
def HasHashQueryBound (adversary : Adversary) (q : Nat) : Prop :=
  ∀ result ∈ support (experiment adversary), result.2.total ≤ q

/-- SUF advantage at most `q / 2^bits` for every query budget `q ≥ 1`. -/
def HasClassicalSecurityBits (bits : Nat) : Prop :=
  ∀ q, 1 ≤ q → ∀ adversary, HasHashQueryBound adversary q →
    forgeAdvantage adversary ≤ q / ((2 ^ bits : Nat) : ℝ≥0∞)

end Security

/-- The security claim. -/
abbrev SphincsSecurityStatement : Prop := Security.HasClassicalSecurityBits 127

end SphincsSecurity
