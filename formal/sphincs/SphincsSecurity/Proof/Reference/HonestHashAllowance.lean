import SphincsSecurity.Proof.Hypertree.PublicGraphSigner
import SphincsSecurity.Proof.Residual.RetainedResidualWorkCost
import SphincsSecurity.Proof.Base.QueryCapAccounting

namespace SphincsSecurity.Concrete
open OracleComp OracleSpec CanonicalProbeRouting
set_option backward.isDefEq.respectTransparency false

theorem referenceSelectionResult_cost_le (selection : ReferenceSelection) :
    (referenceSelectionResult selection).2 ≤ encodingAttemptLimit := by
  cases selection with
  | none => exact le_rfl
  | some selected => exact Nat.succ_le_of_lt selected.1.isLt

theorem OtsCode.signingSteps_le (word : Encoding) : OtsCode.signingSteps word ≤ numChains * (chainLength - 1) := by
  unfold OtsCode.signingSteps
  calc
    _ ≤ ∑ _index : ChainIndex, (chainLength - 1) := Finset.sum_le_sum (fun index _ => Nat.le_sub_one_of_lt (word index).isLt)
    _ = _ := by simp

theorem authenticationHashCost_le (lay : Layer) : authenticationHashCost lay ≤ 2 ^ 24 := by
  fin_cases lay <;> simp only [authenticationHashCost, treeNodeHashCost_def, oneTimeKeyHashCost_def] <;> decide

theorem layerMessageHashCost_le (lay : Layer) : layerMessageHashCost lay ≤ 2 ^ 24 := by
  fin_cases lay <;> simp only [layerMessageHashCost, treeNodeHashCost_def, oneTimeKeyHashCost_def, ftsKeyHashCost_def] <;> decide

theorem keygenHashCost_le : keygenHashCost ≤ 2 ^ 24 := by
  rw [keygenHashCost_def, treeNodeHashCost_def, oneTimeKeyHashCost_def]
  decide

theorem publicSignLayer_cost_le (known : Labels) (words : OtsReferenceWords) (selections : ReferenceFamily)
    (index : Index) (lay : Layer) : (publicSignLayer known words selections index lay).2 ≤ 2 ^ 33 := by
  have hs := referenceSelectionResult_cost_le (selections ⟨lay, treeIndexAt index lay, leafIndexAt index lay⟩)
  have hm := layerMessageHashCost_le lay
  have ha := authenticationHashCost_le lay
  unfold publicSignLayer
  dsimp only
  split
  · dsimp only
    norm_num [encodingAttemptLimit] at hs ⊢
    omega
  · rename_i counter word h
    have hw := OtsCode.signingSteps_le word
    dsimp only
    norm_num [encodingAttemptLimit, numChains, chainLength, winternitzBits] at hs hw ⊢
    omega

theorem publicSignPlan_cost_le (known : Labels) (words : OtsReferenceWords) (selections : ReferenceFamily)
    (randomness : Randomness) (index : Index) (leaves : IndexGroup → FtsLeaf) :
    (publicSignPlan known words selections randomness index leaves).2 ≤ 2 ^ 35 := by
  have hb := publicSignLayer_cost_le known words selections index bottomLayer
  have hm := publicSignLayer_cost_le known words selections index middleLayer
  have ht := publicSignLayer_cost_le known words selections index topLayer
  have hk := keygenHashCost_le
  have hf : ftsOpenHashCost ≤ 2 ^ 24 := by rw [ftsOpenHashCost_def]; decide
  simp only [publicSignPlan, sequenceLayersHashCost]
  split_ifs <;> omega

private theorem unif_hash_bound {α : Type} (computation : ProbComp α) :
    (liftM computation : OracleComp OracleWorld α).IsQueryBoundP (fun input => input matches .inr _) 0 := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp only [liftM_pure, isQueryBoundP_pure]
  | query_bind input next ih =>
      rw [liftM_bind]
      change ((liftM (OracleWorld.query (.inl input)) >>= fun answer => liftM (next answer)) : OracleComp OracleWorld _).IsQueryBoundP (fun input => input matches .inr _) 0
      simp only [isQueryBoundP_query_bind_iff, Bool.false_eq_true, not_false_eq_true, true_or,
        if_false, true_and]
      exact ih

theorem signDigestLoop_hash_bound (attempts : Nat) (key : SecretKey) (message : Message) :
    (signDigestLoop attempts key message).IsQueryBoundP (fun input => input matches .inr _) attempts := by
  induction attempts with
  | zero => exact isQueryBoundP_pure _ _ _
  | succ attempts ih =>
      rw [signDigestLoop, ← Nat.zero_add (attempts + 1)]
      apply isQueryBoundP_bind (unif_hash_bound sampleRandomness)
      intro randomness _
      simp only [signAttempt, messageDigest, liftM_bind, bind_assoc, pure_bind]
      change ((liftM (OracleWorld.query (.inr (tweakableHashInput key.parameter .message
        (messageDigestPayload key.root message randomness)))) >>= _) : OracleComp OracleWorld _).IsQueryBoundP
          (fun input => input matches .inr _) (attempts + 1)
      simp only [isQueryBoundP_query_bind_iff,  not_true_eq_false, false_or,
        Nat.zero_lt_succ, if_true, Nat.add_sub_cancel, true_and]
      intro output
      split_ifs <;> simp only [liftM_pure, pure_bind]
      · exact isQueryBoundP_pure _ _ _
      · exact ih

theorem boundaryRun_signDigestLoop_cost_le (attempts : Nat) (key : SecretKey) (message : Message)
    (cache : QueryCache HashSpec)
    (result : (Option (Randomness × Index × (IndexGroup → FtsLeaf)) × SigningBoundaryTrace) × QueryCache HashSpec)
    (hr : result ∈ support (boundaryRun key.parameter (signDigestLoop attempts key message) cache)) :
    result.1.2.hashCalls ≤ attempts := by
  apply QueryCap.counted_le_of_queryBound _ _ attempts (signDigestLoop_hash_bound attempts key message)
    (result.1.1, result.1.2.hashCalls)
  apply support_simulateQ_run'_subset romImpl _ cache
  rw [StateT.run'_eq, support_map]
  refine ⟨((result.1.1, result.1.2.hashCalls), result.2), ?_, rfl⟩
  change ((result.1.1, result.1.2.hashCalls), result.2) ∈
    support ((simulateQ romImpl (countHashQueries (signDigestLoop attempts key message))).run cache)
  rw [← boundaryRun_count, support_map]
  exact ⟨result, hr, rfl⟩

end SphincsSecurity.Concrete

namespace SphincsSecurity.Concrete.RetainedResidual
open OracleComp OracleSpec CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] publicSignPlan lazyRun environment ResidualByteFrontend.jointSigningProgram

theorem publicSigningWork_hashCalls_max (key : SecretKey) (known : Labels) (words : OtsReferenceWords)
    (selections : ReferenceFamily) (message : Message) (cache : QueryCache HashSpec)
    (result : (PublicSigningRecord × Nat) × QueryCache HashSpec)
    (hr : result ∈ support ((simulateQ romImpl
      (ResidualByteFrontend.publicSigningWork key.parameter key.root known words selections message)).run cache)) :
    result.1.1.2.hashCalls ≤ 2 ^ 36 := by
  rw [publicSigningWork_eq_digestWork, simulateQ_map, StateT.run_map, support_map] at hr
  obtain ⟨loop, hloop, rfl⟩ := hr
  rw [publicDigestLoop_eq, simulateQ_boundaryComputation] at hloop
  have hc := boundaryRun_signDigestLoop_cost_le digestAttemptLimit key message cache loop hloop
  cases hs : loop.1.1 with
  | none =>
      simp only [digestWork, hs]
      norm_num [digestAttemptLimit] at hc ⊢
      omega
  | some selected =>
      obtain ⟨randomness, index, leaves⟩ := selected
      have hp := publicSignPlan_cost_le known words selections randomness index leaves
      simp only [digestWork, hs, SigningBoundaryTrace.hashCalls_mul, SigningBoundaryTrace.hashCalls_pow_none]
      norm_num [digestAttemptLimit] at hc ⊢
      omega

theorem lazyRun_jointSigningProgram_hashCalls_max (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (words : OtsReferenceWords)
    (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily) (rows : CanonicalEncodingRows)
    (routing : InterleavedResidual.Routing) (message : Message)
    (hinputs : hashInputs (signDigestLoop digestAttemptLimit key message) ⊆ inputs) (state : State inputs)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state))
    (result : Option InterleavedResidual.SigningRecord × State inputs)
    (hresult : lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
      (simulateQ (embed inputs routing)
        (ResidualByteFrontend.jointSigningProgram inputs key.parameter key.root routing.known words selections message)) state result ≠ 0) :
    ∃ record, result.1 = some record ∧ record.2.hashCalls ≤ 2 ^ 36 := by
  have h := map_nonzero _ cacheResult result hresult
  rw [lazyRun_jointSigningProgram_cache key.parameter inputs hencoding words publicReplies selections rows routing key.root message
    (by simpa only [publicDigestLoop_eq] using hinputs) state ha hcovered, RetainedObservation.bind_nonzero] at h
  obtain ⟨actual, _, h⟩ := h
  rw [map_eq_bind_pure_comp, RetainedObservation.bind_nonzero] at h
  obtain ⟨work, hwork, h⟩ := h
  simp only [Function.comp_def, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at h
  refine ⟨_, congrArg Prod.fst h, ?_⟩
  rw [completePublicSigningRecord_trace]
  exact publicSigningWork_hashCalls_max key routing.known words selections message state.memory.external.cache work
    ((mem_support_iff _ _).mpr hwork)

end SphincsSecurity.Concrete.RetainedResidual
