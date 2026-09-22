import SphincsSecurity.Proof.Residual.CappedCertificateBound
import SphincsSecurity.Proof.Residual.CappedSuccessTransfer
import SphincsSecurity.Proof.Residual.RetainedResidualCertificateTransfer

namespace SphincsSecurity.Concrete.RetainedResidual
open OracleComp OracleSpec CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem monitoredRun_queryCap_success {α : Type}
    (key : SecretKey) (inputs : Finset HashInput) (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs)
    (words : OtsReferenceWords) (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily) (rows : CanonicalEncodingRows)
    (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (cap : Nat)
    (before after : MonitoredState inputs) (value : α) (remaining : Nat)
    (hr : monitoredRun key inputs hencoding words publicReplies selections rows budget required stopAfter
      (QueryCap.run IsSigningRequest computation cap) before (some (some (value, remaining)), after) ≠ 0) :
    monitoredRun key inputs hencoding words publicReplies selections rows budget required stopAfter
      computation before (some value, after) ≠ 0 := by
  induction computation using OracleComp.inductionOn generalizing cap before with
  | pure value' =>
      simp only [QueryCap.run_pure, monitoredRun_pure, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not,
        Prod.mk.injEq, Option.some.injEq] at hr ⊢
      exact ⟨hr.1.1, hr.2⟩
  | query_bind input next ih =>
      rw [QueryCap.run_query_bind] at hr
      have step (count : Nat)
          (h : monitoredRun key inputs hencoding words publicReplies selections rows budget required stopAfter
            (liftM ((OracleWorld + SigningSpec).query input) >>= fun answer => QueryCap.run IsSigningRequest (next answer) count)
            before (some (some (value, remaining)), after) ≠ 0) :
          monitoredRun key inputs hencoding words publicReplies selections rows budget required stopAfter
            (liftM ((OracleWorld + SigningSpec).query input) >>= next) before (some value, after) ≠ 0 := by
        rw [monitoredRun_query_bind, RetainedObservation.bind_nonzero] at h ⊢
        obtain ⟨⟨answer, state⟩, hstep, htail⟩ := h
        cases answer with
        | none => simp only [Option.elim_none, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not,
            Prod.mk.injEq, reduceCtorEq, false_and] at htail
        | some answer => exact ⟨(some answer, state), hstep, ih answer count state htail⟩
      by_cases hs : IsSigningRequest input
      · rw [if_pos hs] at hr
        cases cap with
        | zero => simp only [monitoredRun_pure, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not,
            Prod.mk.injEq, Option.some.injEq, reduceCtorEq, false_and] at hr
        | succ cap => exact step cap hr
      · rw [if_neg hs] at hr
        exact step cap hr

def CappedStrongWin {inputs : Finset HashInput}
    (result : Option (Option ((Forgery × Bool) × Nat)) × MonitoredState inputs) : Prop :=
  ∃ value, result.1 = some value ∧ cappedVerdict value result.2.1.memory.log

def CappedStrongException {inputs : Finset HashInput}
    (result : Option (Option ((Forgery × Bool) × Nat)) × MonitoredState inputs) : Prop :=
  CappedStrongWin result ∧ result.2.2.stopped = true

theorem initialCappedMonitoredSource_strong_count (key : SecretKey) (adversary : Adversary)
    (encoding : ReferenceEncodingAuxiliary) (hencoding : encoding ∈ referenceEncodingAuxiliarySample.support)
    (dummy : OtsReferenceWords) (hdummy : ∀ lay tree leaf, OtsCode.Valid (dummy lay tree leaf))
    (exposed : InitialPublicLabels (referenceFamilyWords encoding.selections dummy)) (high : CanonicalGraphHighHalves)
    (hroot : key.root = knownRoot (initialKnown (referenceFamilyWords encoding.selections dummy) exposed))
    (budget : Nat) (stopAfter : CertificateStopRule) (stopped : Bool)
    (forgery : Forgery) (remaining : Nat) (after : MonitoredState (gameInputs adversary))
    (hresult : initialCappedMonitoredSource key adversary encoding dummy exposed high budget Finset.univ stopAfter stopped
      (some (some ((forgery, true), remaining)), after) ≠ 0)
    (hnew : ¬ SigningTranscript.Contains after.1.memory.log forgery) (halive : after.2.stopped = false) :
    1 ≤ certificateBankCount after.2.bank := by
  apply initialMonitoredSource_strong_count key adversary encoding hencoding dummy hdummy exposed high hroot
    budget stopAfter stopped forgery after _ hnew halive
  exact monitoredRun_queryCap_success _ _ _ _ _ _ _ _ _ _ _ signatureLimit _ after (forgery, true) remaining hresult

theorem initialCappedMonitoredSource_strong_le_count_add_exception (key : SecretKey) (adversary : Adversary)
    (encoding : ReferenceEncodingAuxiliary) (hencoding : encoding ∈ referenceEncodingAuxiliarySample.support)
    (dummy : OtsReferenceWords) (hdummy : ∀ lay tree leaf, OtsCode.Valid (dummy lay tree leaf))
    (exposed : InitialPublicLabels (referenceFamilyWords encoding.selections dummy)) (high : CanonicalGraphHighHalves)
    (hroot : key.root = knownRoot (initialKnown (referenceFamilyWords encoding.selections dummy) exposed))
    (budget : Nat) (stopAfter : CertificateStopRule) (stopped : Bool) :
    Pr[CappedStrongWin | initialCappedMonitoredSource key adversary encoding dummy exposed high budget Finset.univ stopAfter stopped] ≤
      (∑' result, Pr[= result | initialCappedMonitoredSource key adversary encoding dummy exposed high budget Finset.univ stopAfter stopped] *
        certificateBankCount result.2.2.bank) +
      Pr[CappedStrongException | initialCappedMonitoredSource key adversary encoding dummy exposed high budget Finset.univ stopAfter stopped] := by
  let law := initialCappedMonitoredSource key adversary encoding dummy exposed high budget Finset.univ stopAfter stopped
  have hcount : Pr[fun result => CappedStrongWin result ∧ result.2.2.stopped = false | law] ≤
      ∑' result, Pr[= result | law] * certificateBankCount result.2.2.bank := by
    apply probEvent_le_tsum_probOutput_mul_cost_of_mem_support
    rintro ⟨answer, after⟩ hsupport ⟨⟨value, hanswer, hwin⟩, halive⟩
    cases value with
    | none => exact False.elim hwin
    | some value =>
      rcases value with ⟨⟨forgery, checked⟩, remaining⟩
      simp only [cappedVerdict, Option.elim_some, sourceVerdict, Bool.and_eq_true, decide_eq_true_eq] at hwin
      obtain ⟨⟨_, hnew⟩, rfl⟩ := hwin
      dsimp only at hanswer halive hnew ⊢
      subst answer
      have hresult := probOutput_ne_zero_of_mem_support hsupport
      rw [SPMF.probOutput_eq_apply] at hresult
      exact initialCappedMonitoredSource_strong_count key adversary encoding hencoding dummy hdummy exposed high hroot
        budget stopAfter stopped forgery remaining after hresult hnew halive
  have hsplit : Pr[CappedStrongWin | law] ≤
      Pr[fun result => CappedStrongWin result ∧ result.2.2.stopped = false | law] + Pr[CappedStrongException | law] := by
    apply le_trans ?_ (probEvent_or_le law _ _)
    apply probEvent_mono
    intro result _ hwin
    cases hstop : result.2.2.stopped with
    | false => exact Or.inl ⟨hwin, rfl⟩
    | true => exact Or.inr ⟨hwin, hstop⟩
  exact hsplit.trans (add_le_add hcount le_rfl)

theorem initialCappedMonitoredSource_stop_add_strong_le (key : SecretKey) (original : Security.Adversary)
    (encoding : ReferenceEncodingAuxiliary) (dummy : OtsReferenceWords)
    (hdummy : ∀ lay tree leaf, OtsCode.Valid (dummy lay tree leaf))
    (exposed : InitialPublicLabels (referenceFamilyWords encoding.selections dummy)) (high : CanonicalGraphHighHalves)
    (budget : Nat) (stopAfter : CertificateStopRule) (stopped : Bool)
    (hparameter : key.parameter ∈ support sampleParameter)
    (hencoding : encoding ∈ referenceEncodingAuxiliarySample.support)
    (hroot : key.root = knownRoot (initialKnown (referenceFamilyWords encoding.selections dummy) exposed))
    (hcost : Security.HasHashQueryBound original budget) (hbudget : budget ≤ 2 ^ 127) :
    let adversary := Seeded.memoAdversary (Security.embed original)
    let law := initialCappedMonitoredSource key adversary encoding dummy exposed high (budget + 2 ^ 64)
      Finset.univ (proposalStop stopAfter) stopped
    Pr[fun result => result.1 = none | law] + Pr[CappedStrongWin | law] ≤
      ENNReal.ofReal (2 * ((budget : ℝ) / 2 ^ digestBits) - ((budget : ℝ) / 2 ^ digestBits) ^ 2) +
        ((budget + 2 ^ 64 : Nat) : ENNReal) * fullCertificateExcessRate + (2 ^ 64 : ENNReal) / 2 ^ 128 +
        Pr[CappedStrongException | law] := by
  dsimp only
  have hwin := initialCappedMonitoredSource_strong_le_count_add_exception key
    (Seeded.memoAdversary (Security.embed original)) encoding hencoding dummy hdummy exposed high hroot
    (budget + 2 ^ 64) (proposalStop stopAfter) stopped
  have hbound := initialCappedMonitoredSource_primitive_add_count_le key original encoding dummy exposed high budget stopAfter stopped
    hparameter hencoding hroot hcost hbudget
  exact (add_le_add le_rfl hwin).trans (by rw [← add_assoc]; exact add_le_add hbound le_rfl)

end SphincsSecurity.Concrete.RetainedResidual
