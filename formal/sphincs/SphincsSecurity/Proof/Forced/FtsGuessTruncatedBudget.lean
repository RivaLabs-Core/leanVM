import SphincsSecurity.Proof.Forced.FtsGuessHonestAllowance

namespace SphincsSecurity.Concrete.FtsGuessHash
open OracleComp OracleSpec OtsContactTrace
open FtsGuessSigning (Coordinate)
open SecretGuessObservation (State fixedRun initialState)
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalGraphGameInputs canonicalEncodingInputs canonicalGraphInputs canonicalGraphLabels
  frontierRoot treeRoot honestNode hashInputs

theorem fixed_truncated_completed_work (original : Security.Adversary) (q : Nat)
    (hsmall : q < 2 ^ 256) (hbound : Security.HasHashQueryBound original q)
    (dummy : OtsReferenceWords) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (labels : CanonicalGraphLabels)
    (auxiliary : ReferenceAuxiliary (canonicalGraphGameInputs (Seeded.memoAdversary (Security.embed original))))
    (hauxiliary : auxiliary ∈ (referenceAuxiliarySample (canonicalGraphGameInputs (Seeded.memoAdversary (Security.embed original)))).support)
    (result : Completed)
    (hr : 𝒟[simulateQ (fixedAnswers (originalAnswers dummy (Seeded.memoAdversary (Security.embed original)) parameter otsSecret labels auxiliary)
      (FtsGuessSigning.secretTable ftsSecret)) (completedRun parameter (canonicalGraphRoot labels) labels
        (signingTruncatedAdversary (Seeded.memoAdversary (Security.embed original))))] result ≠ 0) :
    keygenHashCost + completedWork result ≤ q + 2 ^ 64 := by
  let key : SecretKey := ⟨parameter, 0, otsSecret, ftsSecret⟩
  have hh := fixed_reference_completed_honest_cost key (canonicalGraphRoot labels) _
    (canonicalEncodingInputs_subset_gameInputs _ parameter) labels auxiliary dummy
    (Seeded.memoAdversary (Security.embed original)) result
    ((mem_support_iff_evalDist_apply_ne_zero _ _).mpr hr)
  rw [originalAnswers, fixed_reference_completedForgeryRest key _ _ labels auxiliary hauxiliary dummy,
    evalDist_map, map_eq_bind_pure_comp, RetainedObservation.bind_nonzero] at hr
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
      dummy (signingTruncatedAdversary (Seeded.memoAdversary (Security.embed original)))) := by
    rw [show canonicalGraphLabels parameter otsSecret ftsSecret f = labels from
      canonicalGraphLabels_programmedHash _ _ _ _ _, hselected]
    exact (mem_support_iff_evalDist_apply_ne_zero _ _).mpr hbefore
  have hm := referenceForgeryRest_truncated_main_budget original q hsmall hbound key f dummy before hb
  have hk := keygenHashCost_le
  dsimp only [completedAtRoot] at hh ⊢
  norm_num [signatureLimit] at hh
  omega

theorem lazy_truncated_completed_work (original : Security.Adversary) (q : Nat)
    (hsmall : q < 2 ^ 256) (hbound : Security.HasHashQueryBound original q)
    (dummy : OtsReferenceWords) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest) (labels : CanonicalGraphLabels)
    (auxiliary : ReferenceAuxiliary (canonicalGraphGameInputs (Seeded.memoAdversary (Security.embed original))))
    (hauxiliary : auxiliary ∈ (referenceAuxiliarySample (canonicalGraphGameInputs (Seeded.memoAdversary (Security.embed original)))).support)
    (result : Completed × State Coordinate Digest PUnit)
    (hr : SecretGuessObservation.lazyRun
      (SecretGuessObservation.environment (originalAnswers dummy (Seeded.memoAdversary (Security.embed original)) parameter otsSecret labels auxiliary))
      (completedRun parameter (canonicalGraphRoot labels) labels (signingTruncatedAdversary (Seeded.memoAdversary (Security.embed original))))
      (initialState PUnit.unit) result ≠ 0) :
    keygenHashCost + completedWork result.1 ≤ q + 2 ^ 64 := by
  rw [← SecretGuessObservation.run_erasure _ _ _ (fun _ => Finset.univ_nonempty), RetainedObservation.bind_nonzero] at hr
  obtain ⟨secrets, _, hr⟩ := hr
  apply fixed_truncated_completed_work original q hsmall hbound dummy parameter otsSecret
    (FtsGuessSigning.secretTable.symm secrets) labels auxiliary hauxiliary result.1
  rw [Equiv.apply_symm_apply]
  rw [← SecretGuessObservation.fixedRun_projection _ secrets _ (initialState PUnit.unit),
    map_eq_bind_pure_comp, RetainedObservation.bind_nonzero]
  exact ⟨result, hr, by simp only [Function.comp_def, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not]⟩

theorem cached_truncated_completed_work (original : Security.Adversary) (q : Nat)
    (hsmall : q < 2 ^ 256) (hbound : Security.HasHashQueryBound original q)
    (dummy : OtsReferenceWords) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest) (labels : CanonicalGraphLabels)
    (auxiliary : ReferenceAuxiliary (canonicalGraphGameInputs (Seeded.memoAdversary (Security.embed original))))
    (hauxiliary : auxiliary ∈ (referenceAuxiliarySample (canonicalGraphGameInputs (Seeded.memoAdversary (Security.embed original)))).support)
    (slot : Nat) (result : Completed × CachedState)
    (hr : cachedForcedRun parameter (canonicalGraphRoot labels) otsSecret labels
      (canonicalGraphGameInputs (Seeded.memoAdversary (Security.embed original)))
      (canonicalEncodingInputs_subset_gameInputs _ parameter) auxiliary.selections auxiliary.rows dummy slot
      (completedRun parameter (canonicalGraphRoot labels) labels (signingTruncatedAdversary (Seeded.memoAdversary (Security.embed original))))
      (∅, initialState PUnit.unit) result ≠ 0) :
    keygenHashCost + completedWork result.1 ≤ q + 2 ^ 64 := by
  have hp : ((fun result => (result.1, result.2.2)) <$>
      cachedForcedRun parameter (canonicalGraphRoot labels) otsSecret labels
        (canonicalGraphGameInputs (Seeded.memoAdversary (Security.embed original)))
        (canonicalEncodingInputs_subset_gameInputs _ parameter) auxiliary.selections auxiliary.rows dummy slot
        (completedRun parameter (canonicalGraphRoot labels) labels (signingTruncatedAdversary (Seeded.memoAdversary (Security.embed original))))
        (∅, initialState PUnit.unit)) (result.1, result.2.2) ≠ 0 := by
    rw [map_eq_bind_pure_comp, RetainedObservation.bind_nonzero]
    exact ⟨result, hr, by simp only [Function.comp_def, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not]⟩
  rw [cachedForcedRun_deferred, ← forcedRun_seed_marginal, RetainedObservation.bind_nonzero] at hp
  obtain ⟨seed, _, hs⟩ := hp
  exact lazy_truncated_completed_work original q hsmall hbound dummy parameter otsSecret labels
    { auxiliary with seed := seed } (referenceAuxiliary_seed_support _ auxiliary hauxiliary seed) (result.1, result.2.2)
    (SecretGuessObservation.forcedRun_nonzero _ slot _ _ _ hs)

end SphincsSecurity.Concrete.FtsGuessHash
