import SphincsSecurity.Proof.Residual.InterfaceResources
import SphincsSecurity.Proof.Reference.InterfaceFixedBudget

namespace SphincsSecurity.Concrete.RetainedResidual
open OracleComp OracleSpec CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
attribute [local instance] Classical.propDecidable
attribute [local irreducible] hashInputs sourceInputs canonicalEncodingInputs canonicalGraphInputs
set_option backward.isDefEq.respectTransparency false

private theorem counted_query_bound {ι α : Type} {spec : OracleSpec ι}
    (selected : ι → Prop) [DecidablePred selected] (impl : QueryImpl spec ProbComp)
    (input : ι) (next : spec.Range input → OracleComp spec α) (q : Nat)
    (hbound : ∀ result ∈ support (simulateQ impl (QueryCap.counted selected (liftM (spec.query input) >>= next))), result.2 ≤ q)
    (answer : spec.Range input) (hanswer : answer ∈ support (impl input)) :
    (if selected input then 1 else 0) ≤ q ∧
      ∀ result ∈ support (simulateQ impl (QueryCap.counted selected (next answer))),
        result.2 ≤ q - (if selected input then 1 else 0) := by
  have hsum : ∀ result ∈ support (simulateQ impl (QueryCap.counted selected (next answer))),
      (if selected input then 1 else 0) + result.2 ≤ q := by
    intro result hresult
    apply hbound (result.1, (if selected input then 1 else 0) + result.2)
    simp only [QueryCap.counted_query_bind, bind_pure_comp, simulateQ_bind, simulateQ_spec_query,
      simulateQ_map, mem_support_bind_iff, support_map]
    exact ⟨answer, hanswer, result, hresult, rfl⟩
  obtain ⟨result, hresult⟩ := probComp_support_nonempty (simulateQ impl (QueryCap.counted selected (next answer)))
  exact ⟨by have := hsum result hresult; omega, fun result hresult => by have := hsum result hresult; omega⟩

noncomputable def Context.interfaceImpl {inputs : Finset HashInput} (context : Context inputs) :
    QueryImpl (OracleWorld + SigningSpec) ProbComp :=
  (fixedHashWorld context.oracle).compose (Security.expandSigning (sign context.key))

theorem fixedHashStep_interfaceHashes_le (parameter : PublicParameter) (words : OtsReferenceWords) (selections : ReferenceFamily)
    (routing : InterleavedResidual.Routing) (actual : Labels) (oracle : QueryImpl HashSpec Id) (input : HashInput) (memory : Memory) :
    (fixedHashStep parameter words selections routing actual oracle input memory).2.interfaceHashes ≤ memory.interfaceHashes + 1 := by
  have hh := fixedHashStep_hashCalls parameter words selections routing actual oracle input memory
  have ho : (fixedHashStep parameter words selections routing actual oracle input memory).2.honestHashes = memory.honestHashes :=
    honestHashes_afterReply parameter memory input _ _
  simp only [Memory.interfaceHashes, hh, ho]
  omega

theorem fixedSourceImpl_interface_step {inputs : Finset HashInput} (context : Context inputs)
    (input : (OracleWorld + SigningSpec).Domain) (memory : Memory)
    (result : Option ((OracleWorld + SigningSpec).Range input) × Memory)
    (hresult : (fixedSourceImpl context input).run.run memory result ≠ 0) :
    result.2.interfaceHashes ≤ memory.interfaceHashes + (if Security.IsAdversaryHash input then 1 else 0) ∧
      ∃ answer ∈ support (context.interfaceImpl input), ∀ value, result.1 = some value → value = answer := by
  cases input with
  | inl input =>
    simp only [fixedSourceImpl, OptionT.run_mk, StateT.run_mk, fixedByteRun, simulateQ_spec_query] at hresult
    cases input with
    | inl sample =>
      simp only [fixedByteImpl, OptionT.run_mk, StateT.run_mk, RetainedObservation.bind_nonzero] at hresult
      obtain ⟨value, hv, hresult⟩ := hresult
      simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
      subst result
      refine ⟨le_rfl, value, ?_, fun answer heq => (Option.some.inj heq).symm⟩
      change value ∈ support (liftM (unifSpec.query sample) : ProbComp _)
      exact mem_support_query sample value
    | inr input =>
      simp only [fixedByteImpl, OptionT.run_mk, StateT.run_mk, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
      subst result
      refine ⟨fixedHashStep_interfaceHashes_le _ _ _ _ _ _ _ _, context.oracle input, ?_, ?_⟩
      · change context.oracle input ∈ support (pure (context.oracle input) : ProbComp _)
        simp only [mem_support_pure_iff]
      · intro answer heq
        rcases fixedHashStep_answer context input memory with hstop | hlive
        · rw [hstop] at heq; contradiction
        · rw [hlive] at heq
          exact (Option.some.inj heq).symm
  | inr message =>
    simp only [fixedSourceImpl, OptionT.run_mk, StateT.run_mk, map_eq_bind_pure_comp, RetainedObservation.bind_nonzero] at hresult
    obtain ⟨record, hr, hresult⟩ := hresult
    simp only [Function.comp_def, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
    subst result
    refine ⟨?_, record.1.1, ?_, fun answer heq => (Option.some.inj heq).symm⟩
    · rw [interfaceHashes_signing]
      exact le_rfl
    · change record.1.1 ∈ support (simulateQ (fixedHashWorld context.oracle) (sign context.key message))
      rw [← signWithView_fst, simulateQ_map, ← fixedBoundaryRun_forget context.key.parameter, support_map]
      refine ⟨record.1, ?_, rfl⟩
      rw [support_map]
      exact ⟨record, (mem_support_iff_evalDist_apply_ne_zero _ _).mpr hr, rfl⟩

theorem fixedSourceRun_interfaceHashes_le {Result : Type} {inputs : Finset HashInput} (context : Context inputs)
    (computation : OracleComp (OracleWorld + SigningSpec) Result) (q : Nat)
    (hbound : ∀ result ∈ support (simulateQ context.interfaceImpl (QueryCap.counted Security.IsAdversaryHash computation)), result.2 ≤ q)
    (memory : Memory) (result : Option Result × Memory) (hresult : fixedSourceRun context computation memory result ≠ 0) :
    result.2.interfaceHashes ≤ memory.interfaceHashes + q := by
  induction computation using OracleComp.inductionOn generalizing q memory result with
  | pure value =>
    simp only [fixedSourceRun_pure, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
    subst result
    exact Nat.le_add_right _ _
  | query_bind input next ih =>
    rw [fixedSourceRun_query_bind, RetainedObservation.bind_nonzero] at hresult
    obtain ⟨⟨answer, middle⟩, hmiddle, hresult⟩ := hresult
    obtain ⟨hpaid, value, hv, hvalue⟩ := fixedSourceImpl_interface_step context input memory (answer, middle) hmiddle
    obtain ⟨hcost, hnext⟩ := counted_query_bound Security.IsAdversaryHash context.interfaceImpl input next q hbound value hv
    cases answer with
    | none =>
      simp only [Option.elim_none, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
      subst result
      exact hpaid.trans (Nat.add_le_add_left hcost _)
    | some answer =>
      have heq := hvalue answer rfl
      subst answer
      have h := ih value (q - (if Security.IsAdversaryHash input then 1 else 0)) hnext middle result hresult
      dsimp only at hpaid
      omega

theorem observedRun_source_interfaceHashes_le {Result : Type} {inputs : Finset HashInput} (context : Context inputs)
    (computation : OracleComp (OracleWorld + SigningSpec) Result) (hinputs : sourceInputs context.key computation ⊆ inputs)
    (q : Nat)
    (hbound : ∀ result ∈ support (simulateQ context.interfaceImpl (QueryCap.counted Security.IsAdversaryHash computation)), result.2 ≤ q)
    (state : State inputs) (hcovered : ResidualByteFrontend.RowsCovered inputs (project state))
    (hcompatible : Compatible context state.memory) (result : Option Result × State inputs)
    (hresult : observedRun context.environment context.actual context.auxiliary.seed
      (simulateQ (adversaryImpl inputs context.key.parameter context.key.root context.words context.auxiliary.selections) computation) state result ≠ 0) :
    result.2.memory.interfaceHashes ≤ state.memory.interfaceHashes + q := by
  have h := map_nonzero _ forgetState result hresult
  rw [observedRun_source_memory context computation hinputs state hcovered hcompatible] at h
  exact fixedSourceRun_interfaceHashes_le context computation q hbound state.memory (forgetState result) h

theorem Context.interface_bound {inputs : Finset HashInput} (context : Context inputs)
    (hroot : context.key.root = canonicalGraphRoot context.graph)
    (original : Security.Adversary) (q : Nat) (hsmall : q < 2 ^ 256)
    (hbound : Security.HasHashQueryBound original q) :
    ∀ result ∈ support (simulateQ context.interfaceImpl (QueryCap.counted Security.IsAdversaryHash
      (FtsProbeSimulation.unloggedRetainedRestComputation (Seeded.memoAdversary (Security.embed original))
        ⟨context.key.root, context.key.parameter⟩))), result.2 ≤ q := by
  have hcomputed : context.key.root = evalWithAnswerFn context.oracle
      (treeRoot context.key.parameter topLayer rootTree (context.key.otsSecret topLayer rootTree)) := by
    rw [hroot, ← canonicalGraphLabels_root context.key.parameter context.key.otsSecret context.key.ftsSecret context.oracle]
    congr 1
    exact (canonicalGraphLabels_programmedHash context.key.parameter context.key.otsSecret context.key.ftsSecret context.graph _).symm
  have h := fixedInterface_retained_budget original q hsmall hbound context.key.parameter context.key.otsSecret context.key.ftsSecret context.oracle
  rw [← hcomputed] at h
  have hkey : (⟨context.key.parameter, context.key.root, context.key.otsSecret, context.key.ftsSecret⟩ : SecretKey) = context.key := rfl
  simp only [hkey] at h
  have heq : (fun result : FtsProbeSimulation.RetainedRestResult => (result.1.1, result.2)) <$>
      FtsProbeSimulation.retainedGameRestComputation (Seeded.memoAdversary (Security.embed original))
        ⟨context.key.root, context.key.parameter⟩ =
      FtsProbeSimulation.unloggedRetainedRestComputation (Seeded.memoAdversary (Security.embed original))
        ⟨context.key.root, context.key.parameter⟩ := by
    rw [FtsProbeSimulation.retainedGameRestComputation_eq_signingTrace, Functor.map_map]
    exact FtsProbeSimulation.signingTraceComputation_fst _
  intro result hresult
  rw [Context.interfaceImpl, QueryImpl.simulateQ_compose, ← heq, QueryCap.counted_map,
    simulateQ_map, simulateQ_map, support_map] at hresult
  obtain ⟨full, hfull, rfl⟩ := hresult
  exact h full hfull


end SphincsSecurity.Concrete.RetainedResidual
