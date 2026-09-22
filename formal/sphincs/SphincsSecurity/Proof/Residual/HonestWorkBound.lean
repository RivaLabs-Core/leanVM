import SphincsSecurity.Proof.Residual.SigningCap
import SphincsSecurity.Proof.Reference.HonestHashAllowance

namespace SphincsSecurity.Concrete.RetainedResidual
open OracleComp OracleSpec CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
attribute [local instance] Classical.propDecidable
attribute [local irreducible] hashInputs sourceInputs canonicalEncodingInputs canonicalGraphInputs instFintypePosition
  lazyRun environment
set_option backward.isDefEq.respectTransparency false

variable (key : SecretKey) (inputs : Finset HashInput)
  (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (words : OtsReferenceWords)
  (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily) (rows : CanonicalEncodingRows)

theorem lazyRun_request_honestHashes (input : (OracleWorld + SigningSpec).Domain)
    (hinputs : requestInputs key input ⊆ inputs) (state : State inputs)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state))
    (result : Option ((OracleWorld + SigningSpec).Range input) × State inputs)
    (hresult : lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
      (adversaryImpl inputs key.parameter key.root words selections input) state result ≠ 0) :
    result.2.memory.honestHashes ≤ state.memory.honestHashes +
      2 ^ 36 * (if IsSigningRequest input then 1 else 0) := by
  cases input with
  | inl input =>
      change lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
        (externalProgram inputs key.parameter words selections (liftM (OracleWorld.query input))) state result ≠ 0 at hresult
      rw [lazyRun_externalProgram] at hresult
      cases input with
      | inl sample =>
          rw [← bind_pure (liftM (OracleWorld.query (.inl sample))), lazyByteRun_random_bind, RetainedObservation.bind_nonzero] at hresult
          obtain ⟨answer, _, hresult⟩ := hresult
          rw [lazyByteRun_pure] at hresult
          simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
          subst result
          simp only [IsSigningRequest, if_false, Nat.mul_zero, Nat.add_zero, le_refl]
      | inr input =>
          have hin : input ∈ inputs := by
            apply hinputs
            change input ∈ hashInputs (liftM (OracleWorld.query (.inr input)))
            rw [← bind_pure (liftM (OracleWorld.query (.inr input)))]
            exact mem_hashInputs_hash_bind input pure
          obtain ⟨actual, seed, rfl⟩ := lazyByteRun_hash_result key.parameter inputs hencoding words publicReplies selections rows
            state.memory.routing input hin state ha result hresult
          rw [checkedHashResult_memory, honestHashes_afterReply]
          simp only [IsSigningRequest, if_false, Nat.mul_zero, Nat.add_zero, le_refl]
  | inr message =>
      change lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
        (signingProgram inputs key.parameter key.root words selections message) state result ≠ 0 at hresult
      rw [lazyRun_signingProgram key inputs hencoding words publicReplies selections rows message state,
        map_eq_bind_pure_comp, RetainedObservation.bind_nonzero] at hresult
      obtain ⟨raw, hraw, hresult⟩ := hresult
      have hloop := (ResidualByteFrontend.hashInputs_publicSigningWork_subset_signWithView key state.memory.routing.known words selections message).trans hinputs
      rw [ResidualByteFrontend.hashInputs_publicSigningWork] at hloop
      obtain ⟨record, hrecord, hmemory⟩ := lazyRun_jointSigningProgram_memory_trace key.parameter inputs hencoding words publicReplies selections rows
        state.memory.routing key.root message hloop state ha hcovered raw hraw
      obtain ⟨other, ho, hmax⟩ := lazyRun_jointSigningProgram_hashCalls_max key inputs hencoding words publicReplies selections rows
        state.memory.routing message (by simpa only [publicDigestLoop_eq] using hloop) state ha hcovered raw hraw
      have heq : other = record := Option.some.inj (ho.symm.trans hrecord)
      subst other
      simp only [Function.comp_def, hrecord, Option.elim_some, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
      subst result
      change (raw.2.memory.recordSigning message record).honestHashes ≤ _
      rw [hmemory, honestHashes_recordSigning]
      simp only [IsSigningRequest, if_true, Nat.mul_one]
      change state.memory.honestHashes + record.2.hashCalls ≤ state.memory.honestHashes + 2 ^ 36
      exact Nat.add_le_add_left hmax _

theorem lazyRun_source_honestHashes {α : Type} (computation : OracleComp (OracleWorld + SigningSpec) α)
    (hinputs : sourceInputs key computation ⊆ inputs) (cap : Nat)
    (hcap : computation.IsQueryBoundP IsSigningRequest cap)
    (state : State inputs) (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state))
    (result : Option α × State inputs)
    (hresult : lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
      (simulateQ (adversaryImpl inputs key.parameter key.root words selections) computation) state result ≠ 0) :
    result.2.memory.honestHashes ≤ state.memory.honestHashes + 2 ^ 36 * cap := by
  induction computation using OracleComp.inductionOn generalizing cap state result with
  | pure value =>
      simp only [simulateQ_pure, lazyRun, runWith_pure, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
      subst result
      exact Nat.le_add_right _ _
  | query_bind input next ih =>
      rw [isQueryBoundP_query_bind_iff] at hcap
      rw [simulateQ_bind, simulateQ_spec_query, lazyRun_bind, RetainedObservation.bind_nonzero] at hresult
      obtain ⟨middle, hmiddle, hresult⟩ := hresult
      have hm := lazyRun_request_honestHashes key inputs hencoding words publicReplies selections rows input
        ((requestInputs_subset key input next).trans hinputs) state ha hcovered middle hmiddle
      have ha' := lazyRun_nonempty (environment key.parameter inputs hencoding words publicReplies selections rows) _ state ha middle hmiddle
      have hc' := lazyRun_rowsCovered key.parameter inputs hencoding words publicReplies selections rows _ state ha hcovered middle hmiddle
      have hcost : (if IsSigningRequest input then 1 else 0) ≤ cap := by
        by_cases hs : IsSigningRequest input
        · have hp : 0 < cap := hcap.1.resolve_left (not_not.mpr hs)
          simpa only [if_pos hs] using (Nat.succ_le_of_lt hp)
        · simp only [if_neg hs, Nat.zero_le]
      rcases middle with ⟨answer, after⟩
      cases answer with
      | none =>
          simp only [Option.elim_none, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
          subst result
          exact hm.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ hcost) _)
      | some answer =>
          have ht := ih answer ((sourceInputs_next_subset key input next answer).trans hinputs) _ (hcap.2 answer)
            after ha' hc' result hresult
          by_cases hs : IsSigningRequest input <;> simp only [hs, reduceIte] at hcost hm ht <;> omega

theorem lazyRun_signingCap_honestHashes {α : Type} (computation : OracleComp (OracleWorld + SigningSpec) α)
    (hinputs : sourceInputs key computation ⊆ inputs)
    (exposed : InitialPublicLabels words)
    (result : Option (Option (α × Nat)) × State inputs)
    (hresult : lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
      (simulateQ (adversaryImpl inputs key.parameter key.root words selections) (signingCap computation))
      (initialState inputs words exposed) result ≠ 0) :
    result.2.memory.honestHashes ≤ 2 ^ 64 := by
  have h := lazyRun_source_honestHashes key inputs hencoding words publicReplies selections rows (signingCap computation)
    ((sourceInputs_queryCap_subset key IsSigningRequest computation signatureLimit).trans hinputs) signatureLimit
    (QueryCap.run_queryBound IsSigningRequest computation signatureLimit) (initialState inputs words exposed)
    (initialAllowed_nonempty words exposed) (initialState_rowsCovered inputs words exposed) result hresult
  have hk := keygenHashCost_le
  simp only [initialState, initialMemory, Memory.honestHashes, List.map_nil, List.sum_nil, Nat.add_zero] at h
  norm_num [signatureLimit] at h
  unfold Memory.honestHashes
  omega

end SphincsSecurity.Concrete.RetainedResidual
