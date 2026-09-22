import SphincsSecurity.Proof.Forced.FtsGuessInterfaceWork
import SphincsSecurity.Proof.Forced.FtsGuessBudget
import SphincsSecurity.Proof.Reference.ReferenceInterfaceBudget

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec OtsContactTrace
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalGraphGameInputs canonicalEncodingInputs canonicalGraphInputs canonicalGraphLabels
  frontierRoot treeRoot honestNode hashInputs

theorem fixedTrace_count {α : Type} (f : QueryImpl HashSpec Id) (computation : OracleComp OracleWorld α) :
    (fun result : α × Trace => (result.1, result.2.toList.length)) <$> fixedTrace f computation =
      simulateQ (fixedHashWorld f) (QueryCap.counted Security.IsHash computation) := by
  rw [fixedTrace, ← simulateQ_map]
  congr 1
  apply QueryPause.traced_counted hashObservationTrace Security.IsHash (fun trace => trace.toList.length) rfl
  intro input answer trace
  cases input <;> simp only [hashObservationTrace, one_mul, Security.IsHash, if_false, if_true,
    Nat.zero_add, FreeMonoid.toList_mul, FreeMonoid.toList_of, List.length_append, List.length_singleton]

theorem referenceForgeryRest_interface_budget (original : Security.Adversary) (q : Nat)
    (hsmall : q < 2 ^ 256) (hbound : Security.HasHashQueryBound original q)
    (key : SecretKey) (f : QueryImpl HashSpec Id) (dummy : OtsReferenceWords) (before : AdversaryTrace)
    (hbefore : before ∈ support (referenceForgeryRest key f
      (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret f) (referenceTableSelection key f)
      dummy (Seeded.memoAdversary (Security.embed original)))) :
    let result := completedReferenceContact key.parameter f (referenceFamilyWords (referenceTableSelection key f) dummy)
      (canonicalGraphFrontier key.otsSecret (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret f)
        (referenceFamilyWords (referenceTableSelection key f) dummy)) before
    (result.before * result.after).toList.length ≤ q := by
  let result := completedReferenceContact key.parameter f (referenceFamilyWords (referenceTableSelection key f) dummy)
    (canonicalGraphFrontier key.otsSecret (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret f)
      (referenceFamilyWords (referenceTableSelection key f) dummy)) before
  have hm : (result.output, result.before * result.after) ∈ support (fixedTrace f
      (CausalFrontierProgram.game key.parameter f key.ftsSecret (referenceFamilyWords (referenceTableSelection key f) dummy)
        (canonicalGraphFrontier key.otsSecret (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret f)
          (referenceFamilyWords (referenceTableSelection key f) dummy)) (Seeded.memoAdversary (Security.embed original)))) := by
    rw [← referenceForgeryRest_trace, support_map]
    exact ⟨before, hbefore, rfl⟩
  have hc : (result.output, (result.before * result.after).toList.length) ∈ support
      (simulateQ (fixedHashWorld f) (QueryCap.counted Security.IsHash
        (CausalFrontierProgram.game key.parameter f key.ftsSecret (referenceFamilyWords (referenceTableSelection key f) dummy)
          (canonicalGraphFrontier key.otsSecret (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret f)
            (referenceFamilyWords (referenceTableSelection key f) dummy)) (Seeded.memoAdversary (Security.embed original))))) := by
    rw [← fixedTrace_count, support_map]
    exact ⟨(result.output, result.before * result.after), hm, rfl⟩
  rw [← QueryCap.recorded_counted, simulateQ_map, support_map] at hc
  obtain ⟨record, hrecord, heq⟩ := hc
  have h := referenceRecordedRest_interface_budget original q hsmall hbound key f dummy record hrecord
  have heq' : QueryCap.calls Security.IsHash record.2 = (result.before * result.after).toList.length := congrArg Prod.snd heq
  rw [heq'] at h
  exact h

namespace FtsGuessHash
open FtsGuessSigning (Coordinate)
open SecretGuessObservation (State Environment fixedRun)

theorem original_completedExternalWork_le (original : Security.Adversary) (q : Nat)
    (hsmall : q < 2 ^ 256) (hbound : Security.HasHashQueryBound original q)
    (dummy : OtsReferenceWords) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (labels : CanonicalGraphLabels)
    (auxiliary : ReferenceAuxiliary (canonicalGraphGameInputs (Seeded.memoAdversary (Security.embed original))))
    (hauxiliary : auxiliary ∈ (referenceAuxiliarySample (canonicalGraphGameInputs (Seeded.memoAdversary (Security.embed original)))).support)
    (result : Completed)
    (hr : 𝒟[simulateQ (fixedAnswers (originalAnswers dummy (Seeded.memoAdversary (Security.embed original)) parameter otsSecret labels auxiliary)
      (FtsGuessSigning.secretTable ftsSecret)) (completedRun parameter (canonicalGraphRoot labels) labels (Seeded.memoAdversary (Security.embed original)))] result ≠ 0) :
    completedExternalWork result ≤ q := by
  let key : SecretKey := ⟨parameter, 0, otsSecret, ftsSecret⟩
  rw [originalAnswers] at hr
  rw [fixed_reference_completedForgeryRest key _ _ labels auxiliary hauxiliary dummy, evalDist_map,
    map_eq_bind_pure_comp, RetainedObservation.bind_nonzero] at hr
  obtain ⟨before, hbefore, heq⟩ := hr
  simp only [Function.comp_def, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at heq
  subst result
  have hselected := referenceTableSelection_auxiliary key _ (canonicalEncodingInputs_subset_gameInputs _ parameter) labels auxiliary hauxiliary
  let f := programmedHash parameter otsSecret ftsSecret labels
    (finiteHashAnswer ∅ _ (canonicalReferenceResidual parameter _
      (canonicalEncodingInputs_subset_gameInputs (Seeded.memoAdversary (Security.embed original)) parameter)
        labels auxiliary.rows auxiliary.seed))
  have hb : before ∈ support (referenceForgeryRest key f
      (canonicalGraphLabels parameter otsSecret ftsSecret f) (referenceTableSelection key f)
      dummy (Seeded.memoAdversary (Security.embed original))) := by
    rw [show canonicalGraphLabels parameter otsSecret ftsSecret f = labels from
      canonicalGraphLabels_programmedHash _ _ _ _ _, hselected]
    exact (mem_support_iff_evalDist_apply_ne_zero _ _).mpr hbefore
  have h := referenceForgeryRest_interface_budget original q hsmall hbound key f dummy before hb
  dsimp only [f] at h
  rw [hselected, canonicalGraphLabels_programmedHash] at h
  have hroot := reference_root key labels (finiteHashAnswer ∅ _ (canonicalReferenceResidual parameter _
    (canonicalEncodingInputs_subset_gameInputs (Seeded.memoAdversary (Security.embed original)) parameter) labels auxiliary.rows auxiliary.seed))
      (referenceFamilyWords auxiliary.selections dummy)
  simpa only [key, completedExternalWork, completedAtRoot, completedReferenceContact, hroot,
    FreeMonoid.toList_mul, List.length_append] using h

theorem fixed_original_completedRun_interface_budget (original : Security.Adversary) (q : Nat) (hsmall : q < 2 ^ 256)
    (hbound : Security.HasHashQueryBound original q) (dummy : OtsReferenceWords) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest) (secrets : Coordinate → Digest)
    (labels : CanonicalGraphLabels) (auxiliary : ReferenceAuxiliary (canonicalGraphGameInputs (Seeded.memoAdversary (Security.embed original))))
    (hauxiliary : auxiliary ∈ (referenceAuxiliarySample (canonicalGraphGameInputs (Seeded.memoAdversary (Security.embed original)))).support)
    (state : State Coordinate Digest PUnit) (result : Completed × State Coordinate Digest PUnit)
    (hr : fixedRun (SecretGuessObservation.environment (originalAnswers dummy (Seeded.memoAdversary (Security.embed original)) parameter otsSecret labels auxiliary)) secrets
      (completedRun parameter (canonicalGraphRoot labels) labels (Seeded.memoAdversary (Security.embed original))) state result ≠ 0) :
    completedExternalWork result.1 ≤ q ∧ result.2.probes ≤ state.probes + completedExternalWork result.1 := by
  classical
  have hp : 𝒟[simulateQ (fixedAnswers (originalAnswers dummy (Seeded.memoAdversary (Security.embed original)) parameter otsSecret labels auxiliary) secrets)
      (completedRun parameter (canonicalGraphRoot labels) labels (Seeded.memoAdversary (Security.embed original)))] result.1 ≠ 0 := by
    rw [← SecretGuessObservation.fixedRun_projection _ secrets _ state,
      map_eq_bind_pure_comp, RetainedObservation.bind_nonzero]
    exact ⟨result, hr, by simp only [Function.comp_def, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not]⟩
  have hw := original_completedExternalWork_le original q hsmall hbound dummy parameter otsSecret (FtsGuessSigning.secretTable.symm secrets)
    labels auxiliary hauxiliary result.1 hp
  have hc := fixed_completedRun_external_probes
    (SecretGuessObservation.environment (originalAnswers dummy (Seeded.memoAdversary (Security.embed original)) parameter otsSecret labels auxiliary)) secrets
    parameter (canonicalGraphRoot labels) labels (Seeded.memoAdversary (Security.embed original)) state result hr
  exact ⟨hw, hc⟩

theorem lazy_original_completedRun_interface_budget (original : Security.Adversary) (q : Nat) (hsmall : q < 2 ^ 256)
    (hbound : Security.HasHashQueryBound original q) (dummy : OtsReferenceWords) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest) (labels : CanonicalGraphLabels)
    (auxiliary : ReferenceAuxiliary (canonicalGraphGameInputs (Seeded.memoAdversary (Security.embed original))))
    (hauxiliary : auxiliary ∈ (referenceAuxiliarySample (canonicalGraphGameInputs (Seeded.memoAdversary (Security.embed original)))).support)
    (result : Completed × State Coordinate Digest PUnit)
    (hr : SecretGuessObservation.lazyRun
      (SecretGuessObservation.environment (originalAnswers dummy (Seeded.memoAdversary (Security.embed original)) parameter otsSecret labels auxiliary))
      (completedRun parameter (canonicalGraphRoot labels) labels (Seeded.memoAdversary (Security.embed original))) (SecretGuessObservation.initialState PUnit.unit) result ≠ 0) :
    completedExternalWork result.1 ≤ q ∧ result.2.probes ≤ completedExternalWork result.1 := by
  rw [← SecretGuessObservation.run_erasure _ _ _ (fun _ => Finset.univ_nonempty), RetainedObservation.bind_nonzero] at hr
  obtain ⟨secrets, _, hr⟩ := hr
  have h := fixed_original_completedRun_interface_budget original q hsmall hbound dummy parameter otsSecret secrets labels auxiliary hauxiliary
    (SecretGuessObservation.initialState PUnit.unit) result hr
  simpa only [SecretGuessObservation.initialState, Nat.zero_add] using h

theorem lazy_original_completedRun_interface_probes (original : Security.Adversary) (q : Nat) (hsmall : q < 2 ^ 256)
    (hbound : Security.HasHashQueryBound original q) (dummy : OtsReferenceWords) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest) (labels : CanonicalGraphLabels)
    (auxiliary : ReferenceAuxiliary (canonicalGraphGameInputs (Seeded.memoAdversary (Security.embed original))))
    (hauxiliary : auxiliary ∈ (referenceAuxiliarySample (canonicalGraphGameInputs (Seeded.memoAdversary (Security.embed original)))).support)
    (result : Completed × State Coordinate Digest PUnit)
    (hr : SecretGuessObservation.lazyRun
      (SecretGuessObservation.environment (originalAnswers dummy (Seeded.memoAdversary (Security.embed original)) parameter otsSecret labels auxiliary))
      (completedRun parameter (canonicalGraphRoot labels) labels (Seeded.memoAdversary (Security.embed original))) (SecretGuessObservation.initialState PUnit.unit) result ≠ 0) :
    result.2.probes ≤ q := by
  obtain ⟨hw, hp⟩ := lazy_original_completedRun_interface_budget original q hsmall hbound dummy parameter otsSecret labels auxiliary hauxiliary result hr
  omega

end FtsGuessHash
end SphincsSecurity.Concrete
