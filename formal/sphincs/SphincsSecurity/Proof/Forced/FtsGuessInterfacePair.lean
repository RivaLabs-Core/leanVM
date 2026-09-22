import SphincsSecurity.Proof.Forced.FtsGuessInterfaceBudget
import SphincsSecurity.Proof.Forced.FtsGuessPairSource

namespace SphincsSecurity.Concrete.FtsGuessHash
open OracleComp OracleSpec ENNReal UniformTableCompletion
open FtsGuessSigning (Coordinate)
open SecretGuessObservation (State lazyRun initialState)
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs canonicalGraphGameInputs instFintypePosition
  frontierRoot maskOtsPrefixes frontierSigningRun boundaryEval honestNode canonicalGraphLabels

theorem lazy_original_two_guesses_interface (original : Security.Adversary) (budget : Nat) (hsmall : budget < 2 ^ 256)
    (hbudget : Security.HasHashQueryBound original budget) (dummy : OtsReferenceWords) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest) (labels : CanonicalGraphLabels)
    (auxiliary : ReferenceAuxiliary (canonicalGraphGameInputs (Seeded.memoAdversary (Security.embed original))))
    (hauxiliary : auxiliary ∈ (referenceAuxiliarySample (canonicalGraphGameInputs (Seeded.memoAdversary (Security.embed original)))).support) :
    Pr[fun result => 2 ≤ result.2.guesses.card | lazyRun
      (SecretGuessObservation.environment (originalAnswers dummy (Seeded.memoAdversary (Security.embed original)) parameter otsSecret labels auxiliary))
      (completedRun parameter (canonicalGraphRoot labels) labels (Seeded.memoAdversary (Security.embed original))) (initialState PUnit.unit)] ≤ pairRate budget := by
  have hbound := SecretGuessObservation.lazyRun_two_guesses
    (SecretGuessObservation.environment (originalAnswers dummy (Seeded.memoAdversary (Security.embed original)) parameter otsSecret labels auxiliary))
    (completedRun parameter (canonicalGraphRoot labels) labels (Seeded.memoAdversary (Security.embed original))) PUnit.unit budget
    (fun result hr => lazy_original_completedRun_interface_probes original budget hsmall hbudget dummy parameter otsSecret labels auxiliary hauxiliary result hr)
  simpa only [pairRate, show Fintype.card Digest = 2 ^ 128 by simp [digestBits]] using hbound

theorem initial_original_two_witnesses_interface (original : Security.Adversary) (budget : Nat) (hsmall : budget < 2 ^ 256)
    (hbudget : Security.HasHashQueryBound original budget) (dummy : OtsReferenceWords) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest) (labels : CanonicalGraphLabels)
    (auxiliary : ReferenceAuxiliary (canonicalGraphGameInputs (Seeded.memoAdversary (Security.embed original))))
    (hauxiliary : auxiliary ∈ (referenceAuxiliarySample (canonicalGraphGameInputs (Seeded.memoAdversary (Security.embed original)))).support) :
    let inputs := canonicalGraphGameInputs (Seeded.memoAdversary (Security.embed original))
    let hencoding := canonicalEncodingInputs_subset_gameInputs (Seeded.memoAdversary (Security.embed original)) parameter
    let residual := finiteHashAnswer ∅ inputs (canonicalReferenceResidual parameter inputs hencoding labels auxiliary.rows auxiliary.seed)
    Pr[fun result => completedTwoGuesses
      ⟨parameter, canonicalGraphRoot labels, otsSecret, FtsGuessSigning.secretTable.symm result.1⟩
      (programmedHash parameter otsSecret (FtsGuessSigning.secretTable.symm result.1) labels residual) result.2 |
      complete (fun _ : Coordinate => (Finset.univ : Finset Digest)) >>= fun secrets =>
        (fun value => (secrets, value)) <$> 𝒟[simulateQ
          (fixedAnswers (originalAnswers dummy (Seeded.memoAdversary (Security.embed original)) parameter otsSecret labels auxiliary) secrets)
          (completedRun parameter (canonicalGraphRoot labels) labels (Seeded.memoAdversary (Security.embed original)))]] ≤ pairRate budget := by
  exact (initial_reference_two_witnesses parameter (canonicalGraphRoot labels) otsSecret
    (canonicalGraphGameInputs (Seeded.memoAdversary (Security.embed original))) (canonicalEncodingInputs_subset_gameInputs (Seeded.memoAdversary (Security.embed original)) parameter)
    labels auxiliary hauxiliary dummy (Seeded.memoAdversary (Security.embed original))).trans
    (lazy_original_two_guesses_interface original budget hsmall hbudget dummy parameter otsSecret labels auxiliary hauxiliary)

theorem referenceTwoWitnessRest_initial_bound_interface (original : Security.Adversary) (budget : Nat) (hsmall : budget < 2 ^ 256)
    (hbudget : Security.HasHashQueryBound original budget) (dummy : OtsReferenceWords) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest) (labels : CanonicalGraphLabels)
    (auxiliary : ReferenceAuxiliary (canonicalGraphGameInputs (Seeded.memoAdversary (Security.embed original))))
    (hauxiliary : auxiliary ∈ (referenceAuxiliarySample (canonicalGraphGameInputs (Seeded.memoAdversary (Security.embed original)))).support) :
    Pr[fun hit => hit = true | 𝒟[sampleFtsSecrets] >>= fun ftsSecret =>
      𝒟[referenceTwoWitnessRest ⟨parameter, 0, otsSecret, ftsSecret⟩
        (programmedHash parameter otsSecret ftsSecret labels
          (finiteHashAnswer ∅ (canonicalGraphGameInputs (Seeded.memoAdversary (Security.embed original)))
            (canonicalReferenceResidual parameter (canonicalGraphGameInputs (Seeded.memoAdversary (Security.embed original)))
              (canonicalEncodingInputs_subset_gameInputs (Seeded.memoAdversary (Security.embed original)) parameter) labels auxiliary.rows auxiliary.seed)))
        labels auxiliary.selections dummy (Seeded.memoAdversary (Security.embed original))]] ≤ pairRate budget := by
  have h := initial_original_two_witnesses_interface original budget hsmall hbudget dummy parameter otsSecret labels auxiliary hauxiliary
  dsimp only at h
  have hprior := congrArg (fun law : SPMF (Coordinate → Digest) => law >>= fun secrets =>
      (fun result => (secrets, result)) <$> 𝒟[simulateQ
        (fixedAnswers (originalAnswers dummy (Seeded.memoAdversary (Security.embed original)) parameter otsSecret labels auxiliary) secrets)
        (completedRun parameter (canonicalGraphRoot labels) labels (Seeded.memoAdversary (Security.embed original)))]) FtsGuessSigning.sampleFtsSecrets_table
  rw [bind_map_left] at hprior
  rw [← hprior] at h
  have hprogram (ftsSecret : Index → FtsTree → FtsLeaf → Digest) := referenceTwoWitnessRest_program
    ⟨parameter, 0, otsSecret, ftsSecret⟩ (canonicalGraphGameInputs (Seeded.memoAdversary (Security.embed original)))
    (canonicalEncodingInputs_subset_gameInputs (Seeded.memoAdversary (Security.embed original)) parameter) labels auxiliary hauxiliary dummy (Seeded.memoAdversary (Security.embed original))
  simp only [hprogram, evalDist_map, probEvent_bind_eq_tsum, probEvent_map, Function.comp_def,
    Equiv.symm_apply_apply, decide_eq_true_eq] at h ⊢
  exact h

private theorem pmf_support {Result : Type} (law : PMF Result) (result : Result) (hr : result ∈ support 𝒟[law]) :
    result ∈ law.support := by
  simpa only [mem_support_iff, SPMF.probOutput_eq_apply, SPMF.liftM_apply, PMF.mem_support_iff] using hr

theorem referenceForgeryGame_two_guesses_interface (original : Security.Adversary) (budget : Nat) (hsmall : budget < 2 ^ 256)
    (hbudget : Security.HasHashQueryBound original budget) (dummy : OtsReferenceWords) :
    Pr[referenceTwoGuesses dummy | referenceForgeryGame (canonicalGraphGameInputs (Seeded.memoAdversary (Security.embed original)))
      (canonicalEncodingInputs_subset_gameInputs (Seeded.memoAdversary (Security.embed original))) dummy (Seeded.memoAdversary (Security.embed original))] ≤ pairRate budget := by
  have hsource := referenceForgeryGame_bind_auxiliary (canonicalGraphGameInputs (Seeded.memoAdversary (Security.embed original)))
    (canonicalEncodingInputs_subset_gameInputs (Seeded.memoAdversary (Security.embed original))) (canonicalGraphInputs_subset_gameInputs (Seeded.memoAdversary (Security.embed original))) dummy (Seeded.memoAdversary (Security.embed original))
    (fun key f labels selections before => pure (decide (sourceTwoWitnesses key f labels selections dummy before)))
  simp only [evalDist_pure, bind_pure_comp] at hsource
  have hprojected := congrArg (fun law : SPMF Bool => Pr[fun hit => hit = true | law]) hsource
  simp only [probEvent_map, Function.comp_def, decide_eq_true_eq] at hprojected
  change Pr[referenceTwoGuesses dummy | referenceForgeryGame (canonicalGraphGameInputs (Seeded.memoAdversary (Security.embed original)))
    (canonicalEncodingInputs_subset_gameInputs (Seeded.memoAdversary (Security.embed original))) dummy (Seeded.memoAdversary (Security.embed original))] = _ at hprojected
  rw [hprojected]
  apply probEvent_bind_le_of_forall_le
  intro parameter _
  apply probEvent_bind_le_of_forall_le
  intro otsSecret _
  rw [RetainedObservation.bind_comm 𝒟[sampleFtsSecrets] 𝒟[referenceAuxiliarySample (canonicalGraphGameInputs (Seeded.memoAdversary (Security.embed original)))]]
  apply probEvent_bind_le_of_forall_le
  intro auxiliary hauxiliary
  rw [RetainedObservation.bind_comm 𝒟[sampleFtsSecrets] 𝒟[PMF.uniformOfFintype CanonicalGraphLabels]]
  apply probEvent_bind_le_of_forall_le
  intro labels _
  have h := referenceTwoWitnessRest_initial_bound_interface original budget hsmall hbudget dummy parameter otsSecret labels auxiliary
    (pmf_support _ auxiliary hauxiliary)
  simpa only [referenceTwoWitnessRest, evalDist_map] using h

end SphincsSecurity.Concrete.FtsGuessHash
