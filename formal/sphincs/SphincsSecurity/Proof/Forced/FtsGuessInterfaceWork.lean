import SphincsSecurity.Proof.Forced.FtsGuessWork
namespace SphincsSecurity.Concrete.FtsGuessHash

open OracleComp OracleSpec OtsContactTrace
open FtsGuessSigning (Coordinate)
open SecretGuessObservation (State Environment fixedRun runWith)
set_option backward.isDefEq.respectTransparency false
variable {Memory : Type}

private theorem map_nonzero {First Result : Type} (function : First → Result) (law : SPMF First) (result : Result) :
    (function <$> law) result ≠ 0 ↔ ∃ first, law first ≠ 0 ∧ result = function first := by
  simp only [map_eq_bind_pure_comp, RetainedObservation.bind_nonzero, Function.comp_def,
    ne_eq, SPMF.pure_apply_eq_zero_iff, not_not]

private theorem two_writers_external_probes {Source Result ω₁ ω₂ : Type} {spec : OracleSpec Source} [Monoid ω₁] [Monoid ω₂]
    (environment : Environment Auxiliary Coordinate Digest Memory) (secrets : Coordinate → Digest)
    (implementation : QueryImpl spec (WriterT ω₁ (WriterT ω₂ (OracleComp World))))
    (cost : ω₂ → Nat) (hzero : cost 1 = 0) (hmul : ∀ first second, cost (first * second) = cost first + cost second)
    (hquery : ∀ input state result, fixedRun environment secrets ((implementation input).run).run state result ≠ 0 →
      result.2.probes ≤ state.probes + cost result.1.2)
    (computation : OracleComp spec Result) (state : State Coordinate Digest Memory)
    (result : ((Result × ω₁) × ω₂) × State Coordinate Digest Memory)
    (hr : fixedRun environment secrets ((simulateQ implementation computation).run).run state result ≠ 0) :
    result.2.probes ≤ state.probes + cost result.1.2 := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [simulateQ_pure, WriterT.run_pure, fixedRun, SecretGuessObservation.runWith_pure,
        ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
      subst result
      simp only [hzero, Nat.add_zero, le_refl]
  | query_bind input next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, WriterT.run_bind, WriterT.run_map,
        fixedRun, runWith_bind, runWith_map, RetainedObservation.bind_nonzero, map_nonzero] at hr
      obtain ⟨middle, hm, outer, ⟨tail, ht, rfl⟩, rfl⟩ := hr
      have hhead := hquery input state middle hm
      have htail := ih middle.1.1.1 middle.2 tail ht
      simp only [hmul]
      omega

theorem fixed_adversaryRun_external_probes {Result : Type} (environment : Environment Auxiliary Coordinate Digest Memory)
    (secrets : Coordinate → Digest) (parameter : PublicParameter) (labels : CanonicalGraphLabels)
    (computation : OracleComp (OracleWorld + SigningSpec) Result) (state : State Coordinate Digest Memory)
    (result : (((Result × QueryLog SigningSpec) × SigningBoundaryTrace) × Trace) × State Coordinate Digest Memory)
    (hr : fixedRun environment secrets (adversaryRun parameter labels computation) state result ≠ 0) :
    result.2.probes ≤ state.probes + result.1.2.toList.length := by
  apply two_writers_external_probes environment secrets (adversaryImpl parameter labels) (fun trace => trace.toList.length) rfl
    (fun first second => by simp only [FreeMonoid.toList_mul, List.length_append]) _ (OtsPrefix.logged computation) state result hr
  intro input state result hr
  cases input with
  | inl input =>
      simp only [adversaryImpl, WriterT.run_mk, fixedRun, runWith_map, map_nonzero] at hr
      obtain ⟨answer, ha, rfl⟩ := hr
      have h := fixed_worldProgram_probes environment secrets parameter labels input state answer ha
      cases input <;> simpa only [signingBoundaryTrace_hashCalls_eq, hashObservationTrace,
        FreeMonoid.toList_of, List.length_singleton, FreeMonoid.toList_one, List.length_nil, Bool.false_eq_true, if_false, if_true] using h
  | inr message =>
      simp only [adversaryImpl, WriterT.run_mk, fixedRun, runWith_map, map_nonzero] at hr
      obtain ⟨record, hr, rfl⟩ := hr
      rw [fixed_signingProgram_probes environment secrets message state record hr]
      exact le_rfl

private theorem traced_map {First Result : Type} (function : First → Result) (computation : OracleComp OracleWorld First) :
    QueryPause.traced hashObservationTrace (function <$> computation) =
      (fun result => (function result.1, result.2)) <$> QueryPause.traced hashObservationTrace computation := by
  simp only [QueryPause.traced, simulateQ_map, WriterT.run_map]

theorem fixed_tracedBoundary_external_probes {Result : Type} (environment : Environment Auxiliary Coordinate Digest Memory)
    (secrets : Coordinate → Digest) (parameter : PublicParameter) (labels : CanonicalGraphLabels)
    (computation : OracleComp OracleWorld Result) (state : State Coordinate Digest Memory)
    (result : ((Result × SigningBoundaryTrace) × Trace) × State Coordinate Digest Memory)
    (hr : fixedRun environment secrets (simulateQ (worldProgram parameter labels)
      (QueryPause.traced hashObservationTrace (boundaryComputation parameter computation))) state result ≠ 0) :
    result.2.probes ≤ state.probes + result.1.2.toList.length := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [boundaryComputation, simulateQ_pure, WriterT.run_pure, QueryPause.traced_pure,
        fixedRun, SecretGuessObservation.runWith_pure, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
      subst result
      exact le_rfl
  | query_bind input next ih =>
      simp only [ResidualByteFrontend.boundaryComputation_query_bind, QueryPause.traced_query_bind, traced_map,
        simulateQ_bind, simulateQ_spec_query, simulateQ_map, fixedRun, runWith_bind, runWith_map,
        RetainedObservation.bind_nonzero, map_nonzero] at hr
      obtain ⟨middle, hm, outer, ⟨tail, ht, rfl⟩, rfl⟩ := hr
      have hhead := fixed_worldProgram_probes environment secrets parameter labels input state middle hm
      have htail := ih middle.1 middle.2 tail ht
      have hstep : (hashObservationTrace input middle.1).toList.length =
          (signingBoundaryTrace parameter input middle.1).hashCalls := by
        cases input <;> simp only [signingBoundaryTrace_hashCalls_eq, hashObservationTrace,
          FreeMonoid.toList_of, List.length_singleton, FreeMonoid.toList_one, List.length_nil, Bool.false_eq_true, if_false, if_true]
      simp only [FreeMonoid.toList_mul, List.length_append, hstep]
      omega

theorem fixed_verifyProgram_external_probes (environment : Environment Auxiliary Coordinate Digest Memory)
    (secrets : Coordinate → Digest) (parameter : PublicParameter) (root : Digest) (labels : CanonicalGraphLabels)
    (forgery : Forgery) (state : State Coordinate Digest Memory)
    (result : ((Bool × SigningBoundaryTrace) × Trace) × State Coordinate Digest Memory)
    (hr : fixedRun environment secrets (verifyProgram parameter root labels forgery) state result ≠ 0) :
    result.2.probes ≤ state.probes + result.1.2.toList.length :=
  fixed_tracedBoundary_external_probes environment secrets parameter labels _ state result hr

def completedExternalWork (result : Completed) : Nat :=
  result.1.2.toList.length + result.2.2.toList.length

theorem fixed_completedRun_external_probes (environment : Environment Auxiliary Coordinate Digest Memory)
    (secrets : Coordinate → Digest) (parameter : PublicParameter) (root : Digest) (labels : CanonicalGraphLabels)
    (adversary : Adversary) (state : State Coordinate Digest Memory) (result : Completed × State Coordinate Digest Memory)
    (hr : fixedRun environment secrets (completedRun parameter root labels adversary) state result ≠ 0) :
    result.2.probes ≤ state.probes + completedExternalWork result.1 := by
  simp only [completedRun, fixedRun, runWith_bind, SecretGuessObservation.runWith_pure,
    RetainedObservation.bind_nonzero, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
  obtain ⟨before, hb, checked, hc, rfl⟩ := hr
  have hbefore := fixed_adversaryRun_external_probes environment secrets parameter labels _ state before hb
  have hchecked := fixed_verifyProgram_external_probes environment secrets parameter root labels _ before.2 checked hc
  simp only [completedExternalWork]
  omega

end SphincsSecurity.Concrete.FtsGuessHash
