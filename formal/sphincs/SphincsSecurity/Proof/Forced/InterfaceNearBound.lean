import SphincsSecurity.Proof.Forced.FtsGuessTruncatedBudget

namespace SphincsSecurity.Concrete.FtsGuessHash
open OracleComp OracleSpec ENNReal
open SecretGuessObservation (initialState)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs canonicalGraphGameInputs instFintypePosition

private theorem pmf_mem_of_evalDist {Result : Type} (law : PMF Result) (result : Result)
    (hr : result ∈ support 𝒟[law]) : result ∈ law.support := by
  change result ∈ (𝒟[law]).support at hr
  simpa only [PMF.evalDist_eq, SPMF.support_liftM] using hr

theorem forcedNearGame_interface_le (original : Security.Adversary) (q : Nat)
    (hbound : Security.HasHashQueryBound original q) (hbudget : q ≤ 2 ^ 127)
    (dummy : OtsReferenceWords) (slot : Nat) :
    Pr[fun hit => hit = true | forcedNearGame dummy (Seeded.memoAdversary (Security.embed original)) slot] ≤
      nearCertificateBound (q + 2 ^ 64) := by
  have hsmall : q < 2 ^ 256 := hbudget.trans_lt (by norm_num)
  let adversary := Seeded.memoAdversary (Security.embed original)
  rw [forcedNearGame_cached]
  unfold cachedNearGame
  refine probEvent_bind_le_of_forall_le fun parameter _ => ?_
  refine probEvent_bind_le_of_forall_le fun otsSecret _ => ?_
  refine probEvent_bind_le_of_forall_le fun selections hselections => ?_
  refine probEvent_bind_le_of_forall_le fun rows hrows => ?_
  refine probEvent_bind_le_of_forall_le fun labels _ => ?_
  rw [probEvent_map]
  have hsel := pmf_mem_of_evalDist _ _ hselections
  have hrow := pmf_mem_of_evalDist _ _ hrows
  have hauxiliary : ∀ seed : canonicalGraphGameInputs adversary → HashOutput,
      (⟨selections, Function.uncurry rows, seed⟩ : ReferenceAuxiliary (canonicalGraphGameInputs adversary)) ∈
        (referenceAuxiliarySample (canonicalGraphGameInputs adversary)).support :=
    fun seed => referenceAuxiliary_mem_support _ selections hsel rows hrow seed
  have hcovered : ∀ monitor, CoveredRun parameter (canonicalGraphRoot labels) otsSecret (canonicalGraphGameInputs adversary)
      ((signingTruncatedAdversary adversary).main ⟨canonicalGraphRoot labels, parameter⟩) ((∅, initialState PUnit.unit), monitor) :=
    fun _ secrets _ =>
      coveredInputs_signingTruncated_subset adversary ⟨parameter, canonicalGraphRoot labels, otsSecret, FtsGuessSigning.secretTable.symm secrets⟩
  have hwork : ∀ result : Completed × CachedState,
      nearLaw parameter (canonicalGraphRoot labels) otsSecret labels (canonicalGraphGameInputs adversary)
        (canonicalEncodingInputs_subset_gameInputs adversary parameter) selections (Function.uncurry rows) dummy slot
        (signingTruncatedAdversary adversary) result ≠ 0 →
        keygenHashCost + completedWork result.1 ≤ q + 2 ^ 64 := by
    intro result hresult
    exact cached_truncated_completed_work original q hsmall hbound dummy parameter otsSecret labels
      ⟨selections, Function.uncurry rows, fun _ => Classical.arbitrary _⟩ (hauxiliary _) slot result hresult
  have ht := nearLaw_signing_truncation parameter (canonicalGraphRoot labels) otsSecret labels
    (canonicalGraphGameInputs adversary) (canonicalEncodingInputs_subset_gameInputs adversary parameter)
    selections (Function.uncurry rows) dummy slot adversary
  have hb := nearLaw_certificate_le parameter (canonicalGraphRoot labels) otsSecret labels (canonicalGraphGameInputs adversary)
    (canonicalEncodingInputs_subset_gameInputs adversary parameter) selections (Function.uncurry rows) dummy slot hauxiliary
    (q + 2 ^ 64) (signingTruncatedAdversary adversary) (Nat.add_le_add_right hbudget _) hcovered hwork
  simpa only [Function.comp_def, decide_eq_true_eq] using ht.trans hb

end SphincsSecurity.Concrete.FtsGuessHash
