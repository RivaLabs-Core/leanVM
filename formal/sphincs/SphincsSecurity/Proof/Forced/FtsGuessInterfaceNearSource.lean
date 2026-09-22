import SphincsSecurity.Proof.Forced.FtsGuessInterfacePair
import SphincsSecurity.Proof.Forced.FtsGuessNearSource

namespace SphincsSecurity.Concrete.FtsGuessHash
open OracleComp OracleSpec ENNReal UniformTableCompletion
open FtsGuessSigning (Coordinate)
open SecretGuessObservation (State lazyRun forcedRun initialState)
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs canonicalGraphGameInputs instFintypePosition
  frontierRoot maskOtsPrefixes frontierSigningRun boundaryEval honestNode canonicalGraphLabels

theorem lazy_original_near_event_le_interface (original : Security.Adversary) (budget : Nat) (hsmall : budget < 2 ^ 256)
    (hbudget : Security.HasHashQueryBound original budget) (dummy : OtsReferenceWords) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest) (labels : CanonicalGraphLabels)
    (auxiliary : ReferenceAuxiliary (canonicalGraphGameInputs (Seeded.memoAdversary (Security.embed original))))
    (hauxiliary : auxiliary ∈ (referenceAuxiliarySample (canonicalGraphGameInputs (Seeded.memoAdversary (Security.embed original)))).support) :
    Pr[fun result => result.2.guesses.Nonempty ∧ completedNearCertificate parameter (canonicalGraphRoot labels) result.1 |
      lazyRun (SecretGuessObservation.environment (originalAnswers dummy (Seeded.memoAdversary (Security.embed original)) parameter otsSecret labels auxiliary))
        (completedRun parameter (canonicalGraphRoot labels) labels (Seeded.memoAdversary (Security.embed original))) (initialState PUnit.unit)] ≤
      ((2 ^ 128 - budget : Nat) : ENNReal)⁻¹ *
        ∑ slot ∈ Finset.range budget, forcedNearProbability dummy (Seeded.memoAdversary (Security.embed original)) slot parameter otsSecret labels auxiliary := by
  have h := SecretGuessObservation.lazyRun_event_le_forced
    (SecretGuessObservation.environment (originalAnswers dummy (Seeded.memoAdversary (Security.embed original)) parameter otsSecret labels auxiliary))
    (completedRun parameter (canonicalGraphRoot labels) labels (Seeded.memoAdversary (Security.embed original))) PUnit.unit budget
    (fun result hr => lazy_original_completedRun_interface_probes original budget hsmall hbudget dummy parameter otsSecret labels auxiliary hauxiliary result hr)
    (fun result => result.2.guesses.Nonempty ∧ completedNearCertificate parameter (canonicalGraphRoot labels) result.1)
    (fun result => if completedNearCertificate parameter (canonicalGraphRoot labels) result.1 then 1 else 0)
    (fun _ _ he => ⟨he.1, by rw [if_pos he.2]⟩)
  simpa only [forcedNearProbability, probEvent_eq_tsum_ite, mul_ite, mul_one, mul_zero,
    show Fintype.card Digest = 2 ^ 128 by simp [digestBits]] using h

theorem referenceNearWitnessRest_initial_bound_interface (original : Security.Adversary) (budget : Nat) (hsmall : budget < 2 ^ 256)
    (hbudget : Security.HasHashQueryBound original budget) (dummy : OtsReferenceWords) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest) (labels : CanonicalGraphLabels)
    (auxiliary : ReferenceAuxiliary (canonicalGraphGameInputs (Seeded.memoAdversary (Security.embed original))))
    (hauxiliary : auxiliary ∈ (referenceAuxiliarySample (canonicalGraphGameInputs (Seeded.memoAdversary (Security.embed original)))).support) :
    Pr[fun hit => hit = true | 𝒟[sampleFtsSecrets] >>= fun ftsSecret =>
      𝒟[referenceNearWitnessRest ⟨parameter, 0, otsSecret, ftsSecret⟩
        (programmedHash parameter otsSecret ftsSecret labels
          (finiteHashAnswer ∅ (canonicalGraphGameInputs (Seeded.memoAdversary (Security.embed original)))
            (canonicalReferenceResidual parameter (canonicalGraphGameInputs (Seeded.memoAdversary (Security.embed original)))
              (canonicalEncodingInputs_subset_gameInputs (Seeded.memoAdversary (Security.embed original)) parameter) labels auxiliary.rows auxiliary.seed)))
        labels auxiliary.selections dummy (Seeded.memoAdversary (Security.embed original))]] ≤
      ((2 ^ 128 - budget : Nat) : ENNReal)⁻¹ *
        ∑ slot ∈ Finset.range budget, forcedNearProbability dummy (Seeded.memoAdversary (Security.embed original)) slot parameter otsSecret labels auxiliary := by
  have h := (initial_reference_near_witnesses parameter otsSecret (canonicalGraphGameInputs (Seeded.memoAdversary (Security.embed original)))
    (canonicalEncodingInputs_subset_gameInputs (Seeded.memoAdversary (Security.embed original)) parameter) labels auxiliary hauxiliary dummy (Seeded.memoAdversary (Security.embed original))).trans
    (lazy_original_near_event_le_interface original budget hsmall hbudget dummy parameter otsSecret labels auxiliary hauxiliary)
  have hprior := congrArg (fun law : SPMF (Coordinate → Digest) => law >>= fun secrets =>
      (fun result => (secrets, result)) <$> 𝒟[simulateQ
        (fixedAnswers (originalAnswers dummy (Seeded.memoAdversary (Security.embed original)) parameter otsSecret labels auxiliary) secrets)
        (completedRun parameter (canonicalGraphRoot labels) labels (Seeded.memoAdversary (Security.embed original)))]) FtsGuessSigning.sampleFtsSecrets_table
  rw [bind_map_left] at hprior
  simp only [originalAnswers] at hprior
  rw [← hprior] at h
  have hprogram (ftsSecret : Index → FtsTree → FtsLeaf → Digest) := referenceNearWitnessRest_program
    ⟨parameter, 0, otsSecret, ftsSecret⟩ (canonicalGraphGameInputs (Seeded.memoAdversary (Security.embed original)))
    (canonicalEncodingInputs_subset_gameInputs (Seeded.memoAdversary (Security.embed original)) parameter) labels auxiliary hauxiliary dummy (Seeded.memoAdversary (Security.embed original))
  simp only [hprogram, evalDist_map, probEvent_bind_eq_tsum, probEvent_map, Function.comp_def,
    Equiv.symm_apply_apply, decide_eq_true_eq] at h ⊢
  exact h

private theorem weighted_sum {Index First : Type} (indices : Finset Index) (law : SPMF First)
    (value : Index → First → ENNReal) (rate : ENNReal) :
    rate * (∑ index ∈ indices, ∑' first, Pr[= first | law] * value index first) =
      ∑' first, Pr[= first | law] * (rate * ∑ index ∈ indices, value index first) := by
  rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable), ← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro first
  rw [← Finset.mul_sum]
  ring

private theorem pmf_support_nonzero {Result : Type} (law : PMF Result) (result : Result) (hr : 𝒟[law] result ≠ 0) :
    result ∈ law.support := by
  simpa only [PMF.mem_support_iff, SPMF.liftM_apply] using hr

theorem referenceForgeryGame_near_guess_le_forced_interface (original : Security.Adversary) (budget : Nat) (hsmall : budget < 2 ^ 256)
    (hbudget : Security.HasHashQueryBound original budget) (dummy : OtsReferenceWords) :
    Pr[ReferenceForgerySample.nearGuess dummy | referenceForgeryGame (canonicalGraphGameInputs (Seeded.memoAdversary (Security.embed original)))
      (canonicalEncodingInputs_subset_gameInputs (Seeded.memoAdversary (Security.embed original))) dummy (Seeded.memoAdversary (Security.embed original))] ≤
      ((2 ^ 128 - budget : Nat) : ENNReal)⁻¹ *
        ∑ slot ∈ Finset.range budget, Pr[fun hit => hit = true | forcedNearGame dummy (Seeded.memoAdversary (Security.embed original)) slot] := by
  have hsource := referenceForgeryGame_bind_auxiliary (canonicalGraphGameInputs (Seeded.memoAdversary (Security.embed original)))
    (canonicalEncodingInputs_subset_gameInputs (Seeded.memoAdversary (Security.embed original))) (canonicalGraphInputs_subset_gameInputs (Seeded.memoAdversary (Security.embed original))) dummy (Seeded.memoAdversary (Security.embed original))
    (fun key f labels selections before => pure (decide (sourceNearWitness key f labels selections dummy before)))
  simp only [evalDist_pure, bind_pure_comp] at hsource
  have hprojected := congrArg (fun law : SPMF Bool => Pr[fun hit => hit = true | law]) hsource
  simp only [probEvent_map, Function.comp_def, decide_eq_true_eq] at hprojected
  change Pr[ReferenceForgerySample.nearGuess dummy | referenceForgeryGame (canonicalGraphGameInputs (Seeded.memoAdversary (Security.embed original)))
    (canonicalEncodingInputs_subset_gameInputs (Seeded.memoAdversary (Security.embed original))) dummy (Seeded.memoAdversary (Security.embed original))] = _ at hprojected
  rw [hprojected]
  simp_rw [forcedNearGame_probability, weighted_sum]
  rw [probEvent_bind_eq_tsum]
  apply ENNReal.tsum_le_tsum
  intro parameter
  apply mul_le_mul' le_rfl
  rw [probEvent_bind_eq_tsum]
  apply ENNReal.tsum_le_tsum
  intro otsSecret
  apply mul_le_mul' le_rfl
  rw [RetainedObservation.bind_comm 𝒟[sampleFtsSecrets] 𝒟[referenceAuxiliarySample (canonicalGraphGameInputs (Seeded.memoAdversary (Security.embed original)))],
    probEvent_bind_eq_tsum]
  apply ENNReal.tsum_le_tsum
  intro auxiliary
  by_cases hz : 𝒟[referenceAuxiliarySample (canonicalGraphGameInputs (Seeded.memoAdversary (Security.embed original)))] auxiliary = 0
  · simp only [SPMF.probOutput_eq_apply, hz, zero_mul, le_refl]
  apply mul_le_mul' le_rfl
  rw [RetainedObservation.bind_comm 𝒟[sampleFtsSecrets] 𝒟[PMF.uniformOfFintype CanonicalGraphLabels],
    probEvent_bind_eq_tsum]
  apply ENNReal.tsum_le_tsum
  intro labels
  apply mul_le_mul' le_rfl
  have h := referenceNearWitnessRest_initial_bound_interface original budget hsmall hbudget dummy parameter otsSecret labels auxiliary
    (pmf_support_nonzero _ auxiliary hz)
  simpa only [referenceNearWitnessRest, evalDist_map] using h

end SphincsSecurity.Concrete.FtsGuessHash
