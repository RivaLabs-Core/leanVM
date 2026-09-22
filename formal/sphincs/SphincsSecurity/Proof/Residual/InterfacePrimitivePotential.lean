import SphincsSecurity.Proof.Residual.InterfaceQueryPotential

namespace SphincsSecurity.Concrete.RetainedResidual
open OracleComp OracleSpec CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
open InterleavedResidual (Routing SigningRecord)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] hashInputs sourceInputs canonicalEncodingInputs canonicalGraphInputs instFintypePosition
set_option backward.isDefEq.respectTransparency false

noncomputable def interfaceContinuation (budget : Nat) (memory : Memory) : ENNReal :=
  ENNReal.ofReal (PrimitiveMessagePotential.value (2 ^ digestBits) memory.external.probes
    ((budget : ℝ) - memory.interfaceHashes))

noncomputable def interfaceLivePotential (budget : Nat) (memory : Memory) : ENNReal :=
  (memory.interfaceMessages : ENNReal) / 2 ^ digestBits + interfaceContinuation budget memory

noncomputable def interfaceResultPotential {Result : Type} {inputs : Finset HashInput}
    (budget : Nat) (result : Option Result × State inputs) : ENNReal :=
  (result.2.memory.interfaceMessages : ENNReal) / 2 ^ digestBits +
    result.1.elim 1 (fun _ => interfaceContinuation budget result.2.memory)

theorem interfaceLivePotential_signing (budget : Nat) (memory : Memory) (message : Message) (record : SigningRecord) :
    interfaceLivePotential budget ((memory.applyBoundary record.2).recordSigning message record) =
      interfaceLivePotential budget memory := by
  simp only [interfaceLivePotential, interfaceContinuation, interfaceHashes_signing, interfaceMessages_signing]
  rfl

private theorem expected_indicator_value_le {Result : Type} (law : SPMF Result) (event : Result → Prop) [DecidablePred event]
    (cost value : ENNReal) :
    (∑' result, Pr[= result | law] * (cost + if event result then 1 else value)) ≤
      cost + Pr[event | law] + (1 - Pr[event | law]) * value := by
  have hcomplement : Pr[fun result => ¬event result | law] ≤ 1 - Pr[event | law] := by
    apply ENNReal.le_sub_of_add_le_left probEvent_ne_top
    rw [probEvent_compl]
    exact tsub_le_self
  have hsplit : (∑' result, Pr[= result | law] * (if event result then 1 else value)) =
      Pr[event | law] + Pr[fun result => ¬event result | law] * value := by
    rw [probEvent_eq_tsum_ite, probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
    apply tsum_congr
    intro result
    by_cases he : event result <;> simp [he]
  simp only [mul_add, ENNReal.tsum_add]
  rw [hsplit, ENNReal.tsum_mul_right, ← add_assoc]
  exact add_le_add (add_le_add (mul_le_of_le_one_left' tsum_probOutput_le_one) le_rfl)
    (mul_le_mul' hcomplement le_rfl)

private theorem ennreal_mixture_le (probability : ENNReal) (hprobability : probability ≤ 1)
    (value bound : ℝ) (hvalue : 0 ≤ value) (hbound : 0 ≤ bound)
    (h : probability.toReal + (1 - probability.toReal) * value ≤ bound) :
    probability + (1 - probability) * ENNReal.ofReal value ≤ ENNReal.ofReal bound := by
  have hp : probability ≠ ⊤ := ne_top_of_le_ne_top (by simp) hprobability
  have hs : 1 - probability ≠ ⊤ := ne_top_of_le_ne_top (by simp) tsub_le_self
  apply (ENNReal.toReal_le_toReal (ENNReal.add_ne_top.mpr ⟨hp, ENNReal.mul_ne_top hs ENNReal.ofReal_ne_top⟩)
    ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_add hp (ENNReal.mul_ne_top hs ENNReal.ofReal_ne_top), ENNReal.toReal_mul,
    ENNReal.toReal_sub_of_le hprobability (by simp), ENNReal.toReal_one,
    ENNReal.toReal_ofReal hvalue, ENNReal.toReal_ofReal hbound]
  exact h

variable (parameter : PublicParameter) (inputs : Finset HashInput)
  (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (words : OtsReferenceWords)
  (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily) (rows : CanonicalEncodingRows)

theorem lazyByteRun_hash_interfacePotential (routing : Routing) (input : HashInput) (hin : input ∈ inputs)
    (state : State inputs) (budget : Nat)
    (hselect : ∀ position, FirstSuccessTable.select decodeEncodingOutput (fun counter => rows (position, counter)) = selections position)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state))
    (hcandidates : ResidualByteFrontend.HiddenCandidateBound words routing.disclosed (project state))
    (hclean : ResidualByteFrontend.ReplyClean
      (PublicEncodingMatch.Match parameter (knownEncodingMessage routing.known) words selections) state.memory.external.cache)
    (hresources : InterfaceResources state.memory) (hquery : state.memory.interfaceHashes + 1 ≤ budget)
    (hbudget : 2 * budget ≤ 2 ^ digestBits) :
    (∑' result, Pr[= result | lazyByteRun parameter inputs hencoding words publicReplies selections rows routing
        (liftM (OracleWorld.query (.inr input))) state] * interfaceResultPotential budget result) ≤
      interfaceLivePotential budget state.memory := by
  let law := lazyByteRun parameter inputs hencoding words publicReplies selections rows routing
    (liftM (OracleWorld.query (.inr input))) state
  let afterProbes := (charge parameter words routing.disclosed routing.known input state.memory.external).probes
  let nextValue := PrimitiveMessagePotential.value (2 ^ digestBits) afterProbes
    ((budget : ℝ) - (state.memory.interfaceHashes + 1))
  let increment : ℝ := if FtsProbeSimulation.MessageHashInput parameter input then (2 ^ digestBits : ℝ)⁻¹ else 0
  have hlaw : law = lazyRun (environment parameter inputs hencoding words publicReplies selections rows)
      (simulateQ (embed inputs routing)
        (ResidualByteFrontend.checkedHashQuery
          (PublicEncodingMatch.Match parameter (knownEncodingMessage routing.known) words selections) ⟨input, hin⟩)) state := by
    simp only [law, lazyByteRun, simulateQ_spec_query, ResidualByteFrontend.checkedTranslate, dif_pos hin]
  have hp : (state.memory.external.probes : ℝ) ≤ state.memory.interfaceHashes := by
    exact_mod_cast (show state.memory.external.probes ≤ state.memory.interfaceHashes from
      (Nat.le_add_right _ _).trans hresources.2.2)
  have hc : (state.memory.interfaceHashes : ℝ) + 1 ≤ budget := by exact_mod_cast hquery
  have hb : 2 * (budget : ℝ) ≤ 2 ^ digestBits := by exact_mod_cast hbudget
  have hs : (0 : ℝ) < 2 ^ digestBits := by positivity
  have hap : (afterProbes : ℝ) ≤ state.memory.external.probes + 1 := by
    exact_mod_cast charge_probes_le parameter words routing.disclosed routing.known input state.memory.external
  have hn : 0 ≤ nextValue := (PrimitiveMessagePotential.bounds (2 ^ digestBits) afterProbes
    ((budget : ℝ) - (state.memory.interfaceHashes + 1)) (by linarith) (by linarith)).1
  have hi : 0 ≤ increment := by unfold increment; split <;> positivity
  have hbefore := (PrimitiveMessagePotential.bounds (2 ^ digestBits) state.memory.external.probes
    ((budget : ℝ) - state.memory.interfaceHashes) (by linarith) (by linarith)).1
  have hscalar := checkedHashQuery_interface_payment parameter inputs hencoding words publicReplies selections rows routing
    ⟨input, hin⟩ state budget hselect ha hcovered hcandidates hclean hresources hquery hbudget
  dsimp only at hscalar
  rw [← hlaw] at hscalar
  change (Pr[fun result => result.1 = none | law]).toReal +
    (1 - (Pr[fun result => result.1 = none | law]).toReal) * (increment + nextValue) ≤ _ at hscalar
  have hpayment := ennreal_mixture_le (Pr[fun result => result.1 = none | law]) probEvent_le_one _ _
    (add_nonneg hi hn) hbefore hscalar
  change (∑' result, Pr[= result | law] * interfaceResultPotential budget result) ≤ _
  calc
    _ ≤ ∑' result, Pr[= result | law] *
        ((state.memory.interfaceMessages : ENNReal) / 2 ^ digestBits +
          if result.1 = none then 1 else ENNReal.ofReal (increment + nextValue)) := by
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hr : Pr[= result | law] = 0
      · simp only [hr, zero_mul, le_refl]
      · apply mul_le_mul' le_rfl
        obtain ⟨actual, seed, heq⟩ := lazyByteRun_hash_result parameter inputs hencoding words publicReplies selections rows
          routing input hin state ha result hr
        have hhash := checkedHashResult_interfaceHashes parameter inputs hencoding words publicReplies selections rows routing actual seed ⟨input, hin⟩ state hresources
        have hprobes := checkedHashResult_probes parameter inputs hencoding words publicReplies selections rows routing actual seed ⟨input, hin⟩ state
        have hmemory := checkedHashResult_memory parameter inputs hencoding words publicReplies selections rows routing actual seed ⟨input, hin⟩ state
        rw [← heq] at hhash hprobes hmemory
        have hmessages := congrArg (fun memory : Memory => memory.interfaceMessages) hmemory
        rw [afterReply_interfaceMessages parameter state.memory input result.1 result.2.memory.external hresources] at hmessages
        by_cases hnone : result.1 = none
        · simp only [hnone, Option.elim_none, Nat.add_zero] at hmessages
          simp only [interfaceResultPotential, hnone, Option.elim_none, hmessages, if_pos, le_refl]
        · obtain ⟨answer, hanswer⟩ := Option.ne_none_iff_exists'.mp hnone
          simp only [hanswer, Option.elim_some] at hmessages
          simp only [interfaceResultPotential, hanswer, Option.elim_some, reduceCtorEq, if_false,
            interfaceContinuation, hhash, Nat.cast_add, Nat.cast_one, hprobes]
          by_cases hm : FtsProbeSimulation.MessageHashInput parameter input
          · simp only [if_pos hm] at hmessages
            rw [hmessages, Nat.cast_add, Nat.cast_one, ENNReal.add_div, add_assoc]
            unfold increment
            rw [if_pos hm, ENNReal.ofReal_add (by positivity) hn]
            simp only [one_div, ENNReal.ofReal_inv_of_pos hs,
              ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat, nextValue, afterProbes, le_refl]
          · simp only [if_neg hm, Nat.add_zero] at hmessages
            rw [hmessages]
            simp only [increment, if_neg hm, zero_add, nextValue, afterProbes, le_refl]
    _ ≤ (state.memory.interfaceMessages : ENNReal) / 2 ^ digestBits +
        (Pr[fun result => result.1 = none | law] +
          (1 - Pr[fun result => result.1 = none | law]) * ENNReal.ofReal (increment + nextValue)) := by
      simpa only [add_assoc] using expected_indicator_value_le law (fun result => result.1 = none)
        ((state.memory.interfaceMessages : ENNReal) / 2 ^ digestBits) (ENNReal.ofReal (increment + nextValue))
    _ ≤ _ := add_le_add le_rfl hpayment

omit parameter hencoding in
theorem lazyRun_signingProgram_interfacePotential (key : SecretKey)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (message : Message)
    (hinputs : hashInputs (signWithView key message) ⊆ inputs) (state : State inputs) (budget : Nat)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state)) :
    (∑' result, Pr[= result | lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
        (signingProgram inputs key.parameter key.root words selections message) state] * interfaceResultPotential budget result) ≤
      interfaceLivePotential budget state.memory := by
  calc
    _ ≤ ∑' result, Pr[= result | lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
        (signingProgram inputs key.parameter key.root words selections message) state] * interfaceLivePotential budget state.memory := by
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hr : Pr[= result | lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
          (signingProgram inputs key.parameter key.root words selections message) state] = 0
      · simp only [hr, zero_mul, le_refl]
      · apply mul_le_mul' le_rfl
        rw [SPMF.probOutput_eq_apply] at hr
        rw [lazyRun_signingProgram key inputs hencoding words publicReplies selections rows message state,
          map_eq_bind_pure_comp] at hr
        obtain ⟨raw, hraw, hr⟩ := (RetainedObservation.bind_nonzero _ _ _).mp hr
        have hloop := (ResidualByteFrontend.hashInputs_publicSigningWork_subset_signWithView key
          state.memory.routing.known words selections message).trans hinputs
        rw [ResidualByteFrontend.hashInputs_publicSigningWork] at hloop
        obtain ⟨record, hrecord, hmemory⟩ := lazyRun_jointSigningProgram_memory_trace key.parameter inputs hencoding words publicReplies selections rows
          state.memory.routing key.root message hloop state ha hcovered raw hraw
        simp only [Function.comp_def, hrecord, Option.elim_some, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
        subst result
        change interfaceLivePotential budget (raw.2.memory.recordSigning message record) ≤ _
        rw [hmemory]
        exact (interfaceLivePotential_signing budget state.memory message record).le
    _ ≤ _ := by
      rw [ENNReal.tsum_mul_right]
      exact mul_le_of_le_one_left' tsum_probOutput_le_one

theorem lazyByteRun_world_interfacePotential (routing : Routing) (input : OracleWorld.Domain)
    (hinputs : hashInputs (liftM (OracleWorld.query input)) ⊆ inputs) (state : State inputs) (budget : Nat)
    (hselect : ∀ position, FirstSuccessTable.select decodeEncodingOutput (fun counter => rows (position, counter)) = selections position)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state))
    (hcandidates : ResidualByteFrontend.HiddenCandidateBound words routing.disclosed (project state))
    (hclean : ResidualByteFrontend.ReplyClean
      (PublicEncodingMatch.Match parameter (knownEncodingMessage routing.known) words selections) state.memory.external.cache)
    (hresources : InterfaceResources state.memory)
    (hquery : state.memory.interfaceHashes + (if input matches .inr _ then 1 else 0) ≤ budget)
    (hbudget : 2 * budget ≤ 2 ^ digestBits) :
    (∑' result, Pr[= result | lazyByteRun parameter inputs hencoding words publicReplies selections rows routing
        (liftM (OracleWorld.query input)) state] * interfaceResultPotential budget result) ≤
      interfaceLivePotential budget state.memory := by
  cases input with
  | inr input =>
      have hin : input ∈ inputs := hinputs (by
        simpa only [bind_pure] using mem_hashInputs_hash_bind input pure)
      exact lazyByteRun_hash_interfacePotential parameter inputs hencoding words publicReplies selections rows routing input hin state budget
        hselect ha hcovered hcandidates hclean hresources hquery hbudget
  | inl input =>
      rw [← bind_pure (liftM (OracleWorld.query (.inl input))), lazyByteRun_random_bind, tsum_probOutput_bind_mul]
      simp only [lazyByteRun_pure, tsum_probOutput_pure_mul, interfaceResultPotential, Option.elim_some]
      rw [ENNReal.tsum_mul_right]
      exact mul_le_of_le_one_left' tsum_probOutput_le_one


omit parameter hencoding in
theorem lazyRun_request_interfacePotential (key : SecretKey)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (input : (OracleWorld + SigningSpec).Domain)
    (hinputs : requestInputs key input ⊆ inputs) (state : State inputs) (budget : Nat)
    (hselect : ∀ position, FirstSuccessTable.select decodeEncodingOutput (fun counter => rows (position, counter)) = selections position)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state))
    (hcandidates : ResidualByteFrontend.HiddenCandidateBound words state.memory.routing.disclosed (project state))
    (hclean : ResidualByteFrontend.ReplyClean
      (PublicEncodingMatch.Match key.parameter (knownEncodingMessage state.memory.routing.known) words selections) state.memory.external.cache)
    (hresources : InterfaceResources state.memory) (hbudget : 2 * budget ≤ 2 ^ digestBits)
    (hcost : ∀ result, lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
      (adversaryImpl inputs key.parameter key.root words selections input) state result ≠ 0 →
        result.2.memory.interfaceHashes ≤ budget) :
    (∑' result, Pr[= result | lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
        (adversaryImpl inputs key.parameter key.root words selections input) state] * interfaceResultPotential budget result) ≤
      interfaceLivePotential budget state.memory := by
  cases input with
  | inr message =>
      exact lazyRun_signingProgram_interfacePotential inputs words publicReplies selections rows key hencoding message hinputs state budget
        ha hcovered
  | inl input =>
      obtain ⟨result, hr⟩ := lazyRun_supported_result key.parameter inputs hencoding words publicReplies selections rows
        (adversaryImpl inputs key.parameter key.root words selections (.inl input)) state ha
      have hc := hcost result hr
      change lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
        (externalProgram inputs key.parameter words selections (liftM (OracleWorld.query input))) state result ≠ 0 at hr
      rw [lazyRun_externalProgram] at hr
      have hh := lazyByteRun_world_interfaceHashes key.parameter inputs hencoding words publicReplies selections rows
        state.memory.routing input hinputs state ha hresources result hr
      rw [hh] at hc
      change (∑' result, Pr[= result | lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
        (externalProgram inputs key.parameter words selections (liftM (OracleWorld.query input))) state] * interfaceResultPotential budget result) ≤ _
      rw [lazyRun_externalProgram]
      exact lazyByteRun_world_interfacePotential key.parameter inputs hencoding words publicReplies selections rows state.memory.routing input
        hinputs state budget hselect ha hcovered hcandidates hclean hresources (by cases input <;> exact hc) hbudget

omit parameter hencoding in
theorem lazyRun_source_interfaceHashes_mono {Result : Type} (key : SecretKey)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs)
    (computation : OracleComp (OracleWorld + SigningSpec) Result) (hinputs : sourceInputs key computation ⊆ inputs)
    (state : State inputs) (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state)) (hresources : InterfaceResources state.memory) (result : Option Result × State inputs)
    (hresult : lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
      (simulateQ (adversaryImpl inputs key.parameter key.root words selections) computation) state result ≠ 0) :
    state.memory.interfaceHashes ≤ result.2.memory.interfaceHashes := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [simulateQ_pure, lazyRun, runWith_pure, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
      subst result
      exact le_rfl
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, lazyRun_bind, RetainedObservation.bind_nonzero] at hresult
      obtain ⟨middle, hmiddle, hresult⟩ := hresult
      have hm := (Nat.le_add_right state.memory.interfaceHashes (if Security.IsAdversaryHash input then 1 else 0)).trans_eq
        (lazyRun_request_interfaceHashes inputs words publicReplies selections rows key hencoding input
          ((requestInputs_subset key input next).trans hinputs) state ha hcovered hresources middle hmiddle).symm
      have hresources' := lazyRun_request_interfaceResources inputs words publicReplies selections rows key hencoding input
        ((requestInputs_subset key input next).trans hinputs) state ha hcovered hresources middle hmiddle
      have ha' := lazyRun_nonempty (environment key.parameter inputs hencoding words publicReplies selections rows) _ state ha middle hmiddle
      have hc' := lazyRun_rowsCovered key.parameter inputs hencoding words publicReplies selections rows _ state ha hcovered middle hmiddle
      rcases middle with ⟨answer, after⟩
      cases answer with
      | none =>
          simp only [Option.elim_none, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
          subst result
          exact hm
      | some answer =>
          exact hm.trans (ih answer ((sourceInputs_next_subset key input next answer).trans hinputs) after ha' hc' hresources' result hresult)

omit parameter hencoding in
theorem lazyRun_source_interfacePotential {Result : Type} (key : SecretKey)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs)
    (computation : OracleComp (OracleWorld + SigningSpec) Result) (hinputs : sourceInputs key computation ⊆ inputs)
    (state : State inputs) (budget : Nat)
    (hselect : ∀ position, FirstSuccessTable.select decodeEncodingOutput (fun counter => rows (position, counter)) = selections position)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state))
    (hcandidates : ResidualByteFrontend.HiddenCandidateBound words state.memory.routing.disclosed (project state))
    (hclean : ResidualByteFrontend.ReplyClean
      (PublicEncodingMatch.Match key.parameter (knownEncodingMessage state.memory.routing.known) words selections) state.memory.external.cache)
    (hresources : InterfaceResources state.memory) (hbudget : 2 * budget ≤ 2 ^ digestBits)
    (hcost : ∀ result, lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
      (simulateQ (adversaryImpl inputs key.parameter key.root words selections) computation) state result ≠ 0 →
        result.2.memory.interfaceHashes ≤ budget) :
    (∑' result, Pr[= result | lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
        (simulateQ (adversaryImpl inputs key.parameter key.root words selections) computation) state] * interfaceResultPotential budget result) ≤
      interfaceLivePotential budget state.memory := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value =>
      simp only [simulateQ_pure, lazyRun, runWith_pure, tsum_probOutput_pure_mul,
        interfaceResultPotential, Option.elim_some, interfaceLivePotential, le_refl]
  | query_bind input next ih =>
      have hin := (requestInputs_subset key input next).trans hinputs
      have hnext : ∀ answer, sourceInputs key (next answer) ⊆ inputs :=
        fun answer => (sourceInputs_next_subset key input next answer).trans hinputs
      have hjoined (middle : Option ((OracleWorld + SigningSpec).Range input) × State inputs)
          (hmiddle : lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
            (adversaryImpl inputs key.parameter key.root words selections input) state middle ≠ 0)
          (result : Option Result × State inputs)
          (hresult : middle.1.elim (pure (none, middle.2)) (fun answer =>
            lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
              (simulateQ (adversaryImpl inputs key.parameter key.root words selections) (next answer)) middle.2) result ≠ 0) :
          result.2.memory.interfaceHashes ≤ budget := by
        apply hcost result
        rw [simulateQ_bind, simulateQ_spec_query, lazyRun_bind, RetainedObservation.bind_nonzero]
        exact ⟨middle, hmiddle, hresult⟩
      have hstepcost (middle : Option ((OracleWorld + SigningSpec).Range input) × State inputs)
          (hmiddle : lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
            (adversaryImpl inputs key.parameter key.root words selections input) state middle ≠ 0) :
          middle.2.memory.interfaceHashes ≤ budget := by
        have ha' := lazyRun_nonempty (environment key.parameter inputs hencoding words publicReplies selections rows) _ state ha middle hmiddle
        have hc' := lazyRun_rowsCovered key.parameter inputs hencoding words publicReplies selections rows _ state ha hcovered middle hmiddle
        have hr' := lazyRun_request_interfaceResources inputs words publicReplies selections rows key hencoding input hin state
          ha hcovered hresources middle hmiddle
        rcases middle with ⟨answer, after⟩
        cases answer with
        | none => exact hjoined (none, after) hmiddle (none, after) (by simp)
        | some answer =>
            obtain ⟨result, hr⟩ := lazyRun_supported_result key.parameter inputs hencoding words publicReplies selections rows
              (simulateQ (adversaryImpl inputs key.parameter key.root words selections) (next answer)) after ha'
            exact (lazyRun_source_interfaceHashes_mono inputs words publicReplies selections rows key hencoding (next answer)
              (hnext answer) after ha' hc' hr' result hr).trans (hjoined (some answer, after) hmiddle result hr)
      apply le_trans ?_ (lazyRun_request_interfacePotential inputs words publicReplies selections rows key hencoding input hin state budget
        hselect ha hcovered hcandidates hclean hresources hbudget hstepcost)
      rw [simulateQ_bind, simulateQ_spec_query, lazyRun_bind, tsum_probOutput_bind_mul]
      apply ENNReal.tsum_le_tsum
      intro middle
      by_cases hm : Pr[= middle | lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
          (adversaryImpl inputs key.parameter key.root words selections input) state] = 0
      · simp only [hm, zero_mul, le_refl]
      · apply mul_le_mul' le_rfl
        have ha' := lazyRun_nonempty (environment key.parameter inputs hencoding words publicReplies selections rows) _ state ha middle hm
        have hc' := lazyRun_rowsCovered key.parameter inputs hencoding words publicReplies selections rows _ state ha hcovered middle hm
        have hp' := lazyRun_request_hiddenCandidateBound key inputs hencoding words publicReplies selections rows input hin state
          ha hcovered hcandidates middle hm
        have hr' := lazyRun_request_interfaceResources inputs words publicReplies selections rows key hencoding input hin state
          ha hcovered hresources middle hm
        rcases middle with ⟨answer, after⟩
        cases answer with
        | none => simp only [Option.elim_none, tsum_probOutput_pure_mul, interfaceResultPotential, Option.elim_none, le_refl]
        | some answer =>
            have he' := lazyRun_request_encodingClean inputs words publicReplies selections rows key hencoding input hin state
              ha hcovered hclean (some answer, after) hm (by simp)
            exact ih answer (hnext answer) after ha' hc' hp' he' hr' (hjoined (some answer, after) hm)

theorem stop_add_messages_le_expected_interfacePotential {Result : Type} {inputs : Finset HashInput}
    (budget : Nat) (law : SPMF (Option Result × State inputs)) :
    Pr[fun result => result.1 = none | law] +
      (∑' result, Pr[= result | law] * (result.2.memory.interfaceMessages : ENNReal)) / 2 ^ digestBits ≤
        ∑' result, Pr[= result | law] * interfaceResultPotential budget result := by
  rw [probEvent_eq_tsum_ite, div_eq_mul_inv, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro result
  rw [interfaceResultPotential, mul_add, div_eq_mul_inv, mul_assoc, add_comm]
  apply add_le_add le_rfl
  cases result.1 with
  | none => simp only [if_pos, Option.elim_none, mul_one, le_refl]
  | some answer => simp only [reduceCtorEq, if_false, zero_le]

theorem interfaceLivePotential_initial (inputs : Finset HashInput) (words : OtsReferenceWords)
    (exposed : InitialPublicLabels words) (budget : Nat) :
    interfaceLivePotential budget (initialState inputs words exposed).memory =
      ENNReal.ofReal (2 * ((budget : ℝ) / 2 ^ digestBits) - ((budget : ℝ) / 2 ^ digestBits) ^ 2) := by
  simp only [interfaceLivePotential, interfaceContinuation, Memory.interfaceHashes, Memory.interfaceMessages,
    Memory.honestHashes, Memory.honestMessages, initialState, initialMemory, List.map_nil, List.sum_nil,
    List.length_nil, Nat.add_zero, Nat.sub_self, Nat.cast_zero, ENNReal.zero_div, zero_add, sub_zero]
  rw [PrimitiveMessagePotential.initial _ _ (by positivity)]


end SphincsSecurity.Concrete.RetainedResidual
