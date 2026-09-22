import SphincsSecurity.Proof.Fts.RegisteredCertificatePotential
import SphincsSecurity.Proof.Fts.CertificateProposalInvariant

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

structure RegisteredCertificateBounds (key : SecretKey) (q total : Nat)
    (state : List Index × RegisteredCertificateLedgerState) : Prop where
  queries_le : state.2.1.2.card + state.2.2.hashes ≤ q
  proposals_eq : state.2.2.proposals = state.1.length
  signatures_eq : state.2.2.signatures + state.2.1.1.2.length = signatureLimit
  counts_le : ∀ index : Index,
    (signingSlotsAtIndex (observedOptionalSigningViews
      (FtsProbeSimulation.messageAnswers key.parameter state.2.1.1.1) key.root state.2.1.1.2) index).card ≤ state.1.count index
  prefix_le : (state.1.length : ENNReal) ≤ targetProposalOverhead * state.2.1.1.2.length + (proposalPrefixSlack : ENNReal)
  total_le : fixedProposalLength ≤ total

theorem registeredLedgerPrice_le_terminal (key : SecretKey) (q total : Nat) (required : Finset FtsTree)
    (input : (OracleWorld + SigningSpec).Domain) (state : List Index × RegisteredCertificateLedgerState)
    (hq : q ≤ (2 ^ 127 + 2 ^ 64)) (hbounds : RegisteredCertificateBounds key q total state)
    (hactive : RegisteredCertificateActive key input state.2) :
    targetCreationPrice key nearUniformDigestReuseWeight (state.2.2.hashes - adversaryHashCost input)
      (state.2.2.signatures - signingRequestCost input) required state.2.1.1 ≤
        terminalProposalPotential (PMF.uniformOfFintype Index) total (terminalCertificatePrice required) state.1 := by
  have hsignatures : state.2.2.signatures = signatureLimit - state.2.1.1.2.length := by
    have h := hbounds.signatures_eq
    omega
  apply (targetCreationPrice_budget_mono key nearUniformDigestReuseWeight _ required state.2.1.1 (Nat.sub_le _ _)).trans
  apply (targetCreationPrice_signatures_mono key nearUniformDigestReuseWeight state.2.2.hashes required state.2.1.1
    (Nat.sub_le _ _)).trans
  rw [hsignatures]
  exact targetCreationPrice_le_terminalProposalPotential key state.2.1.2.card state.2.2.hashes
    state.2.1.1.2.length total state.2.1.1 required state.1 (hbounds.queries_le.trans hq) hactive.2.1.2.2.1
    (registeredCache_index_le key state.2.1 state.2.1.2.card hactive.2.1.1.2.1 le_rfl
      hactive.2.1.2.2.1 hactive.2.1.2.2.2) hbounds.counts_le hbounds.total_le hbounds.prefix_le

theorem terminalProposalPotential_le_baseline_excess (total : Nat) (payoff : List Index → ENNReal)
    (consumed : List Index) (baseline : ENNReal) :
    terminalProposalPotential (PMF.uniformOfFintype Index) total payoff consumed ≤ baseline +
      terminalProposalPotential (PMF.uniformOfFintype Index) total (fun word => payoff word - baseline) consumed := by
  unfold terminalProposalPotential
  calc
    _ ≤ ∑' word, Pr[= word | completeProposalWord (PMF.uniformOfFintype Index) total consumed] *
        (baseline + (payoff word - baseline)) := ENNReal.tsum_le_tsum (fun _ => mul_le_mul' le_rfl le_add_tsub)
    _ = (∑' word, Pr[= word | completeProposalWord (PMF.uniformOfFintype Index) total consumed]) * baseline +
        ∑' word, Pr[= word | completeProposalWord (PMF.uniformOfFintype Index) total consumed] * (payoff word - baseline) := by
      simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right]
    _ ≤ _ := add_le_add (mul_le_of_le_one_left' tsum_probOutput_le_one) le_rfl

theorem expected_registeredLedgerReservation_step_le_message (key : SecretKey) (required : Finset FtsTree)
    (stopAfter : RegisteredCertificateStop) (q total : Nat) (baseline : ENNReal)
    (input : (OracleWorld + SigningSpec).Domain) (state : List Index × RegisteredCertificateLedgerState)
    (hq : q ≤ (2 ^ 127 + 2 ^ 64))
    (hbounds : RegisteredCertificateActive key input state.2 → RegisteredCertificateBounds key q total state) :
    (∑' result, Pr[= result | (registeredLedgerImpl key required stopAfter input).run state] *
      registeredLedgerReservation key required total (fun word => terminalCertificatePrice required word - baseline) result.2) ≤
      registeredLedgerReservation key required total (fun word => terminalCertificatePrice required word - baseline) state +
        baseline * ((if RegisteredCertificateActive key input state.2 then registeredMessageCost key state.2.1 input else 0 : Nat) : ENNReal) := by
  apply expected_registeredLedgerReservation_step_le
  intro hactive
  exact (registeredLedgerPrice_le_terminal key q total required input state hq (hbounds hactive) hactive).trans
    (terminalProposalPotential_le_baseline_excess total (terminalCertificatePrice required) state.1 baseline)

end SphincsSecurity.Concrete
