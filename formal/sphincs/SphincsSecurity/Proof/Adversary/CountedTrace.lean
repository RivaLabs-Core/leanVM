import SphincsSecurity.Proof.Adversary.Embedding
import SphincsSecurity.Proof.Fts.FtsProbeAdversary

namespace SphincsSecurity.Security

open OracleComp OracleSpec
open Concrete.FtsProbeSimulation

set_option backward.isDefEq.respectTransparency false

noncomputable def expandSigning (sign : QueryImpl SigningSpec (OracleComp OracleWorld)) :
    QueryImpl (OracleWorld + SigningSpec) (OracleComp OracleWorld) :=
  QueryImpl.id' OracleWorld + sign

theorem countAdversary_eq_trace {α : Type} (sign : QueryImpl SigningSpec (OracleComp OracleWorld))
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    countAdversary sign computation =
      simulateQ (expandSigning sign) (signingTraceComputation (QueryCap.counted IsAdversaryHash computation)) := by
  rw [countAdversary, ← simulateQ_withTraceAppend_run_eq_signingTraceComputation]
  congr 2
  funext input
  cases input <;> rfl

theorem signingTrace_map {α β : Type} (computation : OracleComp (OracleWorld + SigningSpec) α) (f : α → β) :
    signingTraceComputation (f <$> computation) =
      (fun result => (f result.1, result.2)) <$> signingTraceComputation computation := by
  have h := congrArg WriterT.run (simulateQ_map (impl :=
    QueryImpl.withTraceAppend (QueryImpl.id' (OracleWorld + SigningSpec)) signingLogFragment) computation f)
  simpa only [simulateQ_withTraceAppend_run_eq_signingTraceComputation, simulateQ_id', WriterT.run_map, Prod.map] using h

theorem counted_signingTrace {α : Type} (computation : OracleComp (OracleWorld + SigningSpec) α) :
    QueryCap.counted IsAdversaryHash (signingTraceComputation computation) =
      (fun result => ((result.1.1, result.2), result.1.2)) <$>
        signingTraceComputation (QueryCap.counted IsAdversaryHash computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
      change QueryCap.counted IsAdversaryHash (do
        let answer ← liftM ((OracleWorld + SigningSpec).query input)
        let result ← signingTraceComputation (next answer)
        pure (result.1, signingLogFragment input answer ++ result.2)) = _
      rw [QueryCap.counted_query_bind, QueryCap.counted_query_bind]
      change _ = (fun result => ((result.1.1, result.2), result.1.2)) <$> (do
        let answer ← liftM ((OracleWorld + SigningSpec).query input)
        let result ← signingTraceComputation (do
          let result ← QueryCap.counted IsAdversaryHash (next answer)
          pure (result.1, (if IsAdversaryHash input then 1 else 0) + result.2))
        pure (result.1, signingLogFragment input answer ++ result.2))
      simp only [bind_pure_comp, QueryCap.counted_map, ih, signingTrace_map,
        map_bind, Functor.map_map]

theorem counted_liftOracleWorldLeft {α : Type} (computation : OracleComp OracleWorld α) :
    QueryCap.counted IsAdversaryHash (liftOracleWorldLeft computation) =
      liftOracleWorldLeft (QueryCap.counted IsHash computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
      change QueryCap.counted IsAdversaryHash (do
        let answer ← liftM ((OracleWorld + SigningSpec).query (.inl input))
        liftOracleWorldLeft (next answer)) = _
      rw [QueryCap.counted_query_bind, QueryCap.counted_query_bind]
      simp only [liftOracleWorldLeft] at ih
      simp only [liftOracleWorldLeft, liftM_bind, liftM_pure, ih]
      cases input <;> rfl

theorem simulateQ_expandSigning_lift (sign : QueryImpl SigningSpec (OracleComp OracleWorld))
    {α : Type} (computation : OracleComp OracleWorld α) :
    simulateQ (expandSigning sign) (liftOracleWorldLeft computation) = computation := by
  rw [expandSigning, simulateQ_liftOracleWorldLeft, simulateQ_id']

theorem counted_tracedGameRest (adversary : Adversary) (pk : PublicKey)
    (sign : QueryImpl SigningSpec (OracleComp OracleWorld)) :
    simulateQ (expandSigning sign) (QueryCap.counted IsAdversaryHash
      (tracedGameRestComputation (embed adversary) pk)) = (do
        let ((forgery, queries), log) ← countAdversary sign (adversary.main pk)
        let (verified, verification) ← QueryCap.counted IsHash
          (liftM (Concrete.verify pk forgery.message forgery.signature : OracleComp HashSpec Bool))
        return (decide (SigningTranscript.Valid log ∧ ¬SigningTranscript.Contains log forgery) && verified,
          queries + verification)) := by
  simp only [tracedGameRestComputation, QueryCap.counted_bind, counted_signingTrace,
    simulateQ_bind, ← countAdversary_eq_trace, bind_map_left,
    QueryCap.counted_pure, counted_liftOracleWorldLeft, simulateQ_expandSigning_lift,
    simulateQ_pure, pure_bind, Nat.add_zero, bind_assoc]
  rfl

theorem countedGameCore_eq_trace (adversary : Adversary) :
    (fun result => (result.1, result.2.total)) <$> countedGameCore adversary = (do
      let seed ← liftM sampleMasterSeed
      let (pk, sk) ← liftM (Seeded.keygenFromSeed seed)
      simulateQ (expandSigning (fun request => liftM (Seeded.sign sk request : OracleComp HashSpec _)))
        (QueryCap.counted IsAdversaryHash (tracedGameRestComputation (embed adversary) pk))) := by
  simp only [countedGameCore, map_bind, map_pure, counted_tracedGameRest, HashQueries.total]

theorem experiment_countedTrace (adversary : Adversary) :
    (fun result => (result.1, result.2.total)) <$> experiment adversary =
      (simulateQ romImpl (do
        let seed ← liftM sampleMasterSeed
        let (pk, sk) ← liftM (Seeded.keygenFromSeed seed)
        simulateQ (expandSigning (fun request => liftM (Seeded.sign sk request : OracleComp HashSpec _)))
          (QueryCap.counted IsAdversaryHash (tracedGameRestComputation (embed adversary) pk)))).run' ∅ := by
  rw [← countedGameCore_eq_trace, simulateQ_map, StateT.run'_eq, StateT.run_map]
  simp only [experiment, StateT.run'_eq, Functor.map_map]
  rfl

theorem hasHashQueryBound_iff_trace (adversary : Adversary) (q : Nat) :
    HasHashQueryBound adversary q ↔
      ∀ result ∈ support ((simulateQ romImpl (do
        let seed ← liftM sampleMasterSeed
        let (pk, sk) ← liftM (Seeded.keygenFromSeed seed)
        simulateQ (expandSigning (fun request => liftM (Seeded.sign sk request : OracleComp HashSpec _)))
          (QueryCap.counted IsAdversaryHash (tracedGameRestComputation (embed adversary) pk)))).run' ∅),
        result.2 ≤ q := by
  rw [← experiment_countedTrace]
  simp only [HasHashQueryBound, support_map, Set.forall_mem_image]

end SphincsSecurity.Security
