import SphincsSecurity.Proof.Residual.RetainedResidualExceptionClassification
import SphincsSecurity.Proof.Residual.CappedMonitoredGame
import SphincsSecurity.Proof.Residual.RetainedResidualCacheTail
namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition hashInputs sourceInputs gameInputs
set_option backward.isDefEq.respectTransparency false

noncomputable def initialCappedExceptionSource (key : SecretKey) (adversary : Adversary)
    (encoding : ReferenceEncodingAuxiliary) (dummy : OtsReferenceWords)
    (exposed : InitialPublicLabels (referenceFamilyWords encoding.selections dummy)) (high : CanonicalGraphHighHalves)
    (budget : Nat) : SPMF (Option (Option ((Forgery × Bool) × Nat)) × ExceptionHistoryState (gameInputs adversary)) :=
  exceptionHistoryRun key (gameInputs adversary) (canonicalEncodingInputs_subset_retainedGameInputs adversary key.parameter)
    (referenceFamilyWords encoding.selections dummy)
    (coordinateGraphLabels (initialKnown (referenceFamilyWords encoding.selections dummy) exposed) high)
    encoding.selections encoding.rows budget Finset.univ (proposalStop (fun _ _ _ _ => false))
    (signingCap (FtsProbeSimulation.unloggedRetainedRestComputation adversary ⟨key.root, key.parameter⟩))
    ((initialState (gameInputs adversary) (referenceFamilyWords encoding.selections dummy) exposed,
      initialCertificateMonitor keygenHashCost false), (false, false))

theorem initialCappedExceptionSource_erasure (key : SecretKey) (adversary : Adversary)
    (encoding : ReferenceEncodingAuxiliary) (dummy : OtsReferenceWords)
    (exposed : InitialPublicLabels (referenceFamilyWords encoding.selections dummy)) (high : CanonicalGraphHighHalves)
    (budget : Nat) :
    (fun result => (result.1, result.2.1)) <$> initialCappedExceptionSource key adversary encoding dummy exposed high budget =
      initialCappedMonitoredSource key adversary encoding dummy exposed high budget Finset.univ (proposalStop (fun _ _ _ _ => false)) false := by
  exact exceptionHistoryRun_erasure _ _ _ _ _ _ _ _ _ _ _ _

theorem initialCappedExceptionSource_exception (key : SecretKey) (adversary : Adversary)
    (encoding : ReferenceEncodingAuxiliary) (dummy : OtsReferenceWords)
    (exposed : InitialPublicLabels (referenceFamilyWords encoding.selections dummy)) (high : CanonicalGraphHighHalves)
    (budget : Nat)
    (hcost : ∀ result, initialCappedMonitoredSource key adversary encoding dummy exposed high budget Finset.univ
      (proposalStop (fun _ _ _ _ => false)) false result ≠ 0 → result.2.1.memory.external.hashCalls ≤ budget)
    (hbudget : budget ≤ 2 ^ 127 + 2 ^ 64)
    (result : Option (Option ((Forgery × Bool) × Nat)) × ExceptionHistoryState (gameInputs adversary))
    (hresult : initialCappedExceptionSource key adversary encoding dummy exposed high budget result ≠ 0)
    (hexception : CappedStrongException (result.1, result.2.1)) :
    result.2.2.1 = true ∨ result.2.2.2 = true := by
  by_contra hflags
  have hclean : result.2.2 = (false, false) := by
    rcases hf : result.2.2 with ⟨cache, proposals⟩
    cases cache <;> cases proposals <;> simp_all only [Bool.false_eq_true, or_self, not_false_eq_true, not_true_eq_false,
      or_true, true_or]
  obtain ⟨⟨value, hvalue, hwin⟩, hstop⟩ := hexception
  have hlive : result.1 ≠ none := by rw [hvalue]; exact Option.some_ne_none _
  have hlog : result.2.1.1.memory.log.length ≤ signatureLimit := by
    cases value with
    | none => exact False.elim hwin
    | some value =>
      simp only [cappedVerdict, Option.elim_some, sourceVerdict, Bool.and_eq_true, decide_eq_true_eq] at hwin
      exact hwin.1.1
  have hnative := map_nonzero _ (fun result => (result.1, result.2.1)) result hresult
  rw [initialCappedExceptionSource_erasure] at hnative
  have hbound := hcost (result.1, result.2.1) hnative
  have halive := exceptionHistoryRun_unstopped key (gameInputs adversary)
    (canonicalEncodingInputs_subset_retainedGameInputs adversary key.parameter)
    (referenceFamilyWords encoding.selections dummy)
    (coordinateGraphLabels (initialKnown (referenceFamilyWords encoding.selections dummy) exposed) high)
    encoding.selections encoding.rows budget Finset.univ _ _
    ⟨initialAllowed_nonempty _ exposed, initialState_rowsCovered _ _ exposed⟩
    (sourceInputs_capped_subset_gameInputs adversary key) (fun _ => rfl)
    (monitoredBankComplete_initial key (gameInputs adversary) (referenceFamilyWords encoding.selections dummy) Finset.univ exposed keygenHashCost false)
    (show CacheSizeBound (initialMemory (referenceFamilyWords encoding.selections dummy) exposed) from by
      change QueryCache.enncard (∅ : QueryCache HashSpec) ≤ (keygenHashCost : ENNReal)
      rw [QueryCache.enncard_empty]
      exact zero_le)
    (by intro entry hentry; cases hentry) rfl hbudget result hresult hlive hbound hlog hclean
  simp only [halive, Bool.false_eq_true] at hstop

theorem initialCappedExceptionSource_prefix_le (key : SecretKey) (adversary : Adversary)
    (encoding : ReferenceEncodingAuxiliary) (dummy : OtsReferenceWords)
    (exposed : InitialPublicLabels (referenceFamilyWords encoding.selections dummy)) (high : CanonicalGraphHighHalves) (budget : Nat) :
    Pr[fun result => result.2.2.2 = true | initialCappedExceptionSource key adversary encoding dummy exposed high budget] ≤ proposalPrefixExceptionBound := by
  apply le_trans (exceptionHistoryRun_prefix_le key (gameInputs adversary)
    (canonicalEncodingInputs_subset_retainedGameInputs adversary key.parameter)
    (referenceFamilyWords encoding.selections dummy)
    (coordinateGraphLabels (initialKnown (referenceFamilyWords encoding.selections dummy) exposed) high)
    encoding.selections encoding.rows budget Finset.univ (proposalStop (fun _ _ _ _ => false)) _ _
    ⟨initialAllowed_nonempty _ exposed, initialState_rowsCovered _ _ exposed⟩
    (sourceInputs_capped_subset_gameInputs adversary key) (Nat.zero_le _))
  exact proposalPrefixWeight_initial_le

theorem initialCappedExceptionSource_cache_le (key : SecretKey) (adversary : Adversary)
    (encoding : ReferenceEncodingAuxiliary) (dummy : OtsReferenceWords)
    (exposed : InitialPublicLabels (referenceFamilyWords encoding.selections dummy)) (high : CanonicalGraphHighHalves)
    (budget : Nat)
    (hcost : ∀ result, initialCappedMonitoredSource key adversary encoding dummy exposed high budget Finset.univ
      (proposalStop (fun _ _ _ _ => false)) false result ≠ 0 → result.2.1.memory.external.hashCalls ≤ budget) :
    Pr[fun result => result.2.2.1 = true | initialCappedExceptionSource key adversary encoding dummy exposed high budget] ≤
      (budget : ENNReal) * certificateCacheExceptionRate := by
  apply le_trans (exceptionHistoryRun_cache_le_budget key (gameInputs adversary)
    (canonicalEncodingInputs_subset_retainedGameInputs adversary key.parameter)
    (referenceFamilyWords encoding.selections dummy)
    (coordinateGraphLabels (initialKnown (referenceFamilyWords encoding.selections dummy) exposed) high)
    encoding.selections encoding.rows budget Finset.univ (proposalStop (fun _ _ _ _ => false))
    (signingCap (FtsProbeSimulation.unloggedRetainedRestComputation adversary ⟨key.root, key.parameter⟩))
    ((initialState (gameInputs adversary) (referenceFamilyWords encoding.selections dummy) exposed,
      initialCertificateMonitor keygenHashCost false), (false, false))
    ⟨initialAllowed_nonempty _ exposed, initialState_rowsCovered _ _ exposed⟩
    (sourceInputs_capped_subset_gameInputs adversary key)
    (show CacheSizeBound (initialMemory (referenceFamilyWords encoding.selections dummy) exposed) from by
      change QueryCache.enncard (∅ : QueryCache HashSpec) ≤ (keygenHashCost : ENNReal)
      rw [QueryCache.enncard_empty]
      exact zero_le)
    budget hcost)
  change certificateCacheExceptionWeight key (∅ : QueryCache HashSpec) + (budget : ENNReal) * certificateCacheExceptionRate ≤ _
  simp only [certificateCacheExceptionWeight_initial key ∅ (fun _ _ => rfl), zero_add, le_refl]


theorem initialCappedMonitoredSource_exception_le (key : SecretKey) (adversary : Adversary)
    (encoding : ReferenceEncodingAuxiliary) (dummy : OtsReferenceWords)
    (exposed : InitialPublicLabels (referenceFamilyWords encoding.selections dummy)) (high : CanonicalGraphHighHalves)
    (budget : Nat)
    (hcost : ∀ result, initialCappedMonitoredSource key adversary encoding dummy exposed high budget Finset.univ
      (proposalStop (fun _ _ _ _ => false)) false result ≠ 0 → result.2.1.memory.external.hashCalls ≤ budget)
    (hbudget : budget ≤ 2 ^ 127 + 2 ^ 64) :
    Pr[CappedStrongException | initialCappedMonitoredSource key adversary encoding dummy exposed high budget Finset.univ
      (proposalStop (fun _ _ _ _ => false)) false] ≤
      (budget : ENNReal) * certificateCacheExceptionRate + proposalPrefixExceptionBound := by
  have hflags : Pr[CappedStrongException | initialCappedMonitoredSource key adversary encoding dummy exposed high budget Finset.univ
      (proposalStop (fun _ _ _ _ => false)) false] ≤
      Pr[fun result => result.2.2.1 = true | initialCappedExceptionSource key adversary encoding dummy exposed high budget] +
        Pr[fun result => result.2.2.2 = true | initialCappedExceptionSource key adversary encoding dummy exposed high budget] := by
    rw [← initialCappedExceptionSource_erasure, probEvent_map]
    apply le_trans ?_ (probEvent_or_le _ _ _)
    apply probEvent_mono
    intro result hr he
    have hn := probOutput_ne_zero_of_mem_support hr
    rw [SPMF.probOutput_eq_apply] at hn
    exact initialCappedExceptionSource_exception key adversary encoding dummy exposed high budget hcost hbudget result hn he
  exact hflags.trans (add_le_add (initialCappedExceptionSource_cache_le key adversary encoding dummy exposed high budget hcost)
    (initialCappedExceptionSource_prefix_le key adversary encoding dummy exposed high budget))

theorem cappedMonitoredSourceGame_exception_le (dummy : OtsReferenceWords) (original : Security.Adversary)
    (budget : Nat) (hcost : Security.HasHashQueryBound original budget) (hbudget : budget ≤ 2 ^ 127) :
    Pr[CappedStrongException | cappedMonitoredSourceGame dummy (Seeded.memoAdversary (Security.embed original))
      (budget + 2 ^ 64) (fun _ _ _ _ => false)] ≤
      ((budget + 2 ^ 64 : Nat) : ENNReal) * certificateCacheExceptionRate + proposalPrefixExceptionBound := by
  unfold cappedMonitoredSourceGame
  apply probEvent_bind_le_of_forall_le
  intro parameter hparameter
  have hp : parameter ∈ support sampleParameter := (mem_support_iff_evalDist_apply_ne_zero _ _).mpr hparameter
  apply probEvent_bind_le_of_forall_le
  intro encoding hencoding
  have he : encoding ∈ referenceEncodingAuxiliarySample.support := by
    simpa only [PMF.evalDist_eq, SPMF.support_eq_support, SPMF.support_liftM] using hencoding
  apply probEvent_bind_le_of_forall_le
  intro high _
  apply probEvent_bind_le_of_forall_le
  intro exposed _
  unfold initialCappedMonitoredPrior
  apply probEvent_bind_le_of_forall_le
  intro labels _
  apply initialCappedMonitoredSource_exception_le
  · exact initialCappedMonitoredSource_hashCalls _ original encoding dummy exposed high (budget + 2 ^ 64) Finset.univ
      (proposalStop (fun _ _ _ _ => false)) false budget hp he rfl (hbudget.trans_lt (by norm_num)) hcost
  · exact Nat.add_le_add_right hbudget _

theorem forgeAdvantage_le_capped_native_bound (dummy : OtsReferenceWords)
    (hdummy : ∀ lay tree leaf, OtsCode.Valid (dummy lay tree leaf)) (original : Security.Adversary)
    (budget : Nat) (hcost : Security.HasHashQueryBound original budget) (hbudget : budget ≤ 2 ^ 127) :
    forgeAdvantage scheme (Seeded.memoAdversary (Security.embed original)) ≤
      ENNReal.ofReal (2 * ((budget : ℝ) / 2 ^ digestBits) - ((budget : ℝ) / 2 ^ digestBits) ^ 2) +
        ((budget + 2 ^ 64 : Nat) : ENNReal) * fullCertificateExcessRate + (2 ^ 64 : ENNReal) / 2 ^ 128 +
        (((budget + 2 ^ 64 : Nat) : ENNReal) * certificateCacheExceptionRate + proposalPrefixExceptionBound) :=
  (forgeAdvantage_le_capped_monitored_bound_add_exception dummy hdummy original budget (fun _ _ _ _ => false) hcost hbudget).trans
    (add_le_add le_rfl (cappedMonitoredSourceGame_exception_le dummy original budget hcost hbudget))

end SphincsSecurity.Concrete.RetainedResidual
