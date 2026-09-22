import SphincsSecurity.Proof.Fts.RegisteredCertificateExpectation
import SphincsSecurity.Proof.Fts.ProposalPrefixExponential

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
attribute [local irreducible] proposalPrefixWeight
set_option backward.isDefEq.respectTransparency false

noncomputable def registeredLedgerPrefixWeight (state : RegisteredCertificateLedgerState) : ENNReal :=
  proposalPrefixWeight state.2.proposals (signatureLimit - state.2.signatures)

def RegisteredLedgerPrefixExceptional (state : RegisteredCertificateLedgerState) : Prop :=
  ProposalPrefixExceptional state.2.proposals (signatureLimit - state.2.signatures)

theorem registeredLedgerImpl_signatures_le (key : SecretKey) (required : Finset FtsTree)
    (stopAfter : RegisteredCertificateStop) (input : (OracleWorld + SigningSpec).Domain)
    (state : List Index × RegisteredCertificateLedgerState)
    (result : (OracleWorld + SigningSpec).Range input × (List Index × RegisteredCertificateLedgerState))
    (hresult : result ∈ ((registeredLedgerImpl key required stopAfter input).run state).support) :
    result.2.2.2.signatures ≤ state.2.2.signatures := by
  obtain ⟨length, record, _, hstate⟩ := registeredProposalImpl_support key (registeredCertificateEnabled key)
    (registeredLedgerUpdate key required stopAfter) input state result hresult
  rw [hstate]
  unfold registeredProposalAdvance registeredLedgerUpdate
  split_ifs
  · exact Nat.sub_le _ _
  · exact le_rfl

theorem expected_registeredLedgerImpl_prefixWeight (key : SecretKey) (required : Finset FtsTree)
    (stopAfter : RegisteredCertificateStop) (input : (OracleWorld + SigningSpec).Domain)
    (state : List Index × RegisteredCertificateLedgerState) (hsignatures : state.2.2.signatures ≤ signatureLimit) :
    (∑' result, Pr[= result | (registeredLedgerImpl key required stopAfter input).run state] *
      registeredLedgerPrefixWeight result.2.2) = registeredLedgerPrefixWeight state.2 := by
  cases input with
  | inl world =>
    simp only [registeredLedgerImpl, registeredProposalImpl, proposalRecordImpl, registeredProposalActive,
      StateT.run_mk, Bool.false_eq_true, if_false]
    rw [← PMF.monad_map_eq_map, tsum_probOutput_map_mul]
    have hweight (record : ProposalExecutionRecord (.inl world)) :
        registeredLedgerPrefixWeight (registeredProposalAdvance (registeredLedgerUpdate key required stopAfter) (.inl world) state.2 0 record) =
          registeredLedgerPrefixWeight state.2 := by
      unfold registeredLedgerPrefixWeight registeredProposalAdvance registeredLedgerUpdate
      split_ifs <;> simp only [signingRequestCost, Nat.sub_zero, Nat.add_zero]
    simp only [hweight, ENNReal.tsum_mul_right, tsum_probOutput_of_liftM_PMF, one_mul]
  | inr message =>
    rw [registeredLedgerImpl_sign_run]
    by_cases hactive : RegisteredCertificateActive key (.inr message) state.2
    · rw [if_pos hactive, ← PMF.monad_map_eq_map, tsum_probOutput_map_mul]
      have hremaining : signatureLimit - (state.2.2.signatures - 1) = (signatureLimit - state.2.2.signatures) + 1 := by
        have hcost := hactive.2.2.2.2
        change 1 ≤ state.2.2.signatures at hcost
        omega
      have hcap : signatureLimit - state.2.2.signatures < signatureLimit := by
        have hcost := hactive.2.2.2.2
        change 1 ≤ state.2.2.signatures at hcost
        omega
      simp only [registeredLedgerPrefixWeight, registeredProposalAdvance, registeredLedgerUpdate, if_pos hactive,
        signingRequestCost, hremaining]
      have h := congrArg (fun law : PMF Nat => ∑' length, Pr[= length | law] *
          proposalPrefixWeight (state.2.2.proposals + length) ((signatureLimit - state.2.2.signatures) + 1))
        ((recordProposalBridge_length_record
          (originalProposalRecord key (.inr message) state.2.1.1.1) (registeredRejectedProposal key (.inr message) state.2)
          targetProposalAcceptance targetProposalAcceptance_ne_zero targetProposalAcceptance_lt_one.le) ▸
          recordLengthBridge_length (originalProposalRecord key (.inr message) state.2.1.1.1)
            targetProposalAcceptance targetProposalAcceptance_ne_zero targetProposalAcceptance_lt_one.le)
      simp only [← PMF.monad_map_eq_map, tsum_probOutput_map_mul] at h
      exact h.trans (by simpa only [PMF.probOutput_eq_apply] using
        expected_proposalPrefixWeight state.2.2.proposals (signatureLimit - state.2.2.signatures) hcap)
    · rw [if_neg hactive, ← PMF.monad_map_eq_map, tsum_probOutput_map_mul]
      simp only [registeredLedgerPrefixWeight, registeredProposalAdvance, registeredLedgerUpdate, if_neg hactive,
        ENNReal.tsum_mul_right, tsum_probOutput_of_liftM_PMF, one_mul]

theorem expected_registeredLedgerRun_prefixWeight {α : Type} (key : SecretKey) (required : Finset FtsTree)
    (stopAfter : RegisteredCertificateStop) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : List Index × RegisteredCertificateLedgerState) (hsignatures : state.2.2.signatures ≤ signatureLimit) :
    (∑' result, Pr[= result | (simulateQ (registeredLedgerImpl key required stopAfter) computation).run state] *
      registeredLedgerPrefixWeight result.2.2) = registeredLedgerPrefixWeight state.2 := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, tsum_probOutput_pure_mul]
  | query_bind input next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, tsum_probOutput_bind_mul]
    trans ∑' result, Pr[= result | (registeredLedgerImpl key required stopAfter input).run state] * registeredLedgerPrefixWeight result.2.2
    · apply tsum_congr
      intro result
      by_cases hr : result ∈ ((registeredLedgerImpl key required stopAfter input).run state).support
      · rw [ih result.1 result.2 ((registeredLedgerImpl_signatures_le key required stopAfter input state result hr).trans hsignatures)]
      · have hz : Pr[= result | (registeredLedgerImpl key required stopAfter input).run state] = 0 := by
          rw [PMF.probOutput_eq_apply, PMF.apply_eq_zero_iff]
          exact hr
        rw [hz, zero_mul, zero_mul]
    · exact expected_registeredLedgerImpl_prefixWeight key required stopAfter input state hsignatures

theorem registeredLedgerRun_prefix_probability_le {α : Type} (key : SecretKey) (required : Finset FtsTree)
    (stopAfter : RegisteredCertificateStop) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (cache : QueryCache HashSpec) (q : Nat) :
    Pr[fun result => RegisteredLedgerPrefixExceptional result.2.2 |
      (simulateQ (registeredLedgerImpl key required stopAfter) computation).run
        ([], ((cache, []), ∅), initialRegisteredCertificateLedger q)] ≤ proposalPrefixExceptionBound := by
  have hweight := expected_registeredLedgerRun_prefixWeight key required stopAfter computation
    ([], ((cache, []), ∅), initialRegisteredCertificateLedger q) le_rfl
  rw [registeredLedgerPrefixWeight, initialRegisteredCertificateLedger, Nat.sub_self] at hweight
  apply le_trans _ proposalPrefixWeight_initial_le
  rw [← hweight, probEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  intro result
  split_ifs with hbad
  · exact le_mul_of_one_le_right' (proposalPrefixWeight_bad _ _ (Nat.sub_le _ _) hbad)
  · exact zero_le

end SphincsSecurity.Concrete
