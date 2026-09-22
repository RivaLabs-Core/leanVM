import SphincsSecurity.Proof.Fts.RegisteredProposalExecution
import SphincsSecurity.Proof.Fts.RegisteredCertificateBound

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

structure RegisteredCertificateLedger extends RegisteredCertificateMonitor where
  proposals : Nat
  messages : Nat

abbrev RegisteredCertificateLedgerState := RegisteredTargetState × RegisteredCertificateLedger

def RegisteredCertificateActive (key : SecretKey) (input : (OracleWorld + SigningSpec).Domain)
    (state : RegisteredCertificateLedgerState) : Prop :=
  state.2.stopped = false ∧ RegisteredProposalReady key state.1 ∧
    SigningDigestsCached key.parameter state.1.1.1 key.root state.1.1.2 ∧
    adversaryHashCost input ≤ state.2.hashes ∧ signingRequestCost input ≤ state.2.signatures

noncomputable def registeredCertificateEnabled (key : SecretKey) (message : Message)
    (state : RegisteredCertificateLedgerState) : Bool := decide (RegisteredCertificateActive key (.inr message) state)

abbrev RegisteredCertificateStop := (input : (OracleWorld + SigningSpec).Domain) →
  RegisteredCertificateLedgerState → Nat → ProposalExecutionRecord input → Bool

noncomputable def registeredMessageCost (key : SecretKey) (state : RegisteredTargetState) :
    (OracleWorld + SigningSpec).Domain → Nat
  | .inl world => freshWorldTargetHashCost key.parameter state.1.1 world
  | .inr _ => 0

noncomputable def registeredLedgerUpdate (key : SecretKey) (required : Finset FtsTree)
    (stopAfter : RegisteredCertificateStop) (input : (OracleWorld + SigningSpec).Domain)
    (state : RegisteredCertificateLedgerState) (length : Nat) (record : ProposalExecutionRecord input) :
    RegisteredCertificateLedger :=
  if RegisteredCertificateActive key input state then
    let after := registeredRecordNext input state.1 record
    { hashes := state.2.hashes - adversaryHashCost input
      signatures := state.2.signatures - signingRequestCost input
      bank := completedRegisteredTargets after.2 key required after.1 state.2.bank
      stopped := stopAfter input state length record
      proposals := state.2.proposals + length
      messages := state.2.messages + registeredMessageCost key state.1 input }
  else { state.2 with stopped := true }

noncomputable def registeredLedgerEnvelope (key : SecretKey) (required : Finset FtsTree)
    (state : RegisteredCertificateLedgerState) : ENNReal :=
  registeredTargetEnvelope state.1.2 key nearUniformDigestReuseWeight state.2.hashes state.2.signatures required
    state.1.1 state.2.bank state.2.stopped

noncomputable def registeredLedgerCharge (key : SecretKey) (required : Finset FtsTree)
    (input : (OracleWorld + SigningSpec).Domain) (state : RegisteredCertificateLedgerState) : ENNReal :=
  if RegisteredCertificateActive key input state then
    registeredTargetCharge key nearUniformDigestReuseWeight (state.2.hashes - adversaryHashCost input)
      (state.2.signatures - signingRequestCost input) required state.1.1 input
  else 0

noncomputable def registeredLedgerImpl (key : SecretKey) (required : Finset FtsTree)
    (stopAfter : RegisteredCertificateStop) :
    QueryImpl (OracleWorld + SigningSpec) (StateT (List Index × RegisteredCertificateLedgerState) PMF) :=
  registeredProposalImpl key (registeredCertificateEnabled key) (registeredLedgerUpdate key required stopAfter)

theorem expected_registeredLedgerEnvelope_step_le (key : SecretKey) (required : Finset FtsTree)
    (stopAfter : RegisteredCertificateStop) (input : (OracleWorld + SigningSpec).Domain)
    (state : List Index × RegisteredCertificateLedgerState) :
    (∑' result, Pr[= result | (registeredLedgerImpl key required stopAfter input).run state] *
      registeredLedgerEnvelope key required result.2.2) ≤
      registeredLedgerEnvelope key required state.2 + registeredLedgerCharge key required input state.2 := by
  let afterWeight : RegisteredTargetState → ENNReal := fun after =>
    if RegisteredCertificateActive key input state.2 then
      registeredTargetEnvelope after.2 key nearUniformDigestReuseWeight
        (state.2.2.hashes - adversaryHashCost input) (state.2.2.signatures - signingRequestCost input) required
        after.1 (completedRegisteredTargets after.2 key required after.1 state.2.2.bank) false
    else certificateBankCount state.2.2.bank
  have hproject := congrArg (fun law => ∑' result, Pr[= result | law] * afterWeight result.2)
    (registeredProposalImpl_step_original key (registeredCertificateEnabled key) (registeredLedgerUpdate key required stopAfter) input state)
  rw [tsum_probOutput_map_mul] at hproject
  have hle : (∑' result, Pr[= result | (registeredLedgerImpl key required stopAfter input).run state] *
      registeredLedgerEnvelope key required result.2.2) ≤
      ∑' result, Pr[= result | (registeredTargetImpl key input).run state.2.1] * afterWeight result.2 := by
    rw [← show (∑' result, Pr[= result | (liftM ((registeredTargetImpl key input).run state.2.1) : PMF _)] * afterWeight result.2) =
      ∑' result, Pr[= result | (registeredTargetImpl key input).run state.2.1] * afterWeight result.2 from rfl, ← hproject]
    apply ENNReal.tsum_le_tsum
    intro result
    by_cases hr : result ∈ ((registeredLedgerImpl key required stopAfter input).run state).support
    · obtain ⟨length, record, _, hstate⟩ := registeredProposalImpl_support key (registeredCertificateEnabled key)
        (registeredLedgerUpdate key required stopAfter) input state result hr
      apply mul_le_mul' le_rfl
      change registeredLedgerEnvelope key required result.2.2 ≤ afterWeight result.2.2.1
      rw [hstate]
      unfold registeredProposalAdvance registeredLedgerUpdate registeredLedgerEnvelope afterWeight
      split_ifs
      · exact bankedCacheWeight_discard_le _ _ _ _ _
      · simp only [registeredTargetEnvelope, bankedCacheWeight_stopped, le_refl]
    · have hzero : Pr[= result | (registeredLedgerImpl key required stopAfter input).run state] = 0 := by
        rw [PMF.probOutput_eq_apply, PMF.apply_eq_zero_iff]
        exact hr
      rw [hzero, zero_mul]
      exact zero_le
  apply hle.trans
  by_cases hactive : RegisteredCertificateActive key input state.2
  · have hconditions := hactive
    obtain ⟨hstopped, hready, hsigned, hhashes, hsignatures⟩ := hconditions
    simp only [afterWeight, if_pos hactive, registeredLedgerCharge, registeredLedgerEnvelope]
    have hstep := expected_registeredTargetImpl_le key nearUniformDigestReuseWeight
      (state.2.2.hashes - adversaryHashCost input) (state.2.2.signatures - signingRequestCost input)
      required state.2.1 state.2.2.bank input (fun _ => false) hready.1.1.1 hsigned (by
        intro message _
        exact registeredCache_reuse_le key state.2.1 state.2.1.2.card hready.1.2.2.1 hready.2.1
          le_rfl hready.2.2.1 hready.2.2.2 message)
    simpa only [Nat.sub_add_cancel hhashes, Nat.sub_add_cancel hsignatures, hstopped] using hstep
  · simp only [afterWeight, if_neg hactive, registeredLedgerCharge, add_zero, ENNReal.tsum_mul_right]
    exact (mul_le_of_le_one_left' tsum_probOutput_le_one).trans (certificateBankCount_le_bankedCacheWeight _ _ _ _ _)

theorem registeredMessageCost_le_hashCost (key : SecretKey) (state : RegisteredTargetState)
    (input : (OracleWorld + SigningSpec).Domain) : registeredMessageCost key state input ≤ adversaryHashCost input := by
  cases input with
  | inr message => simp [registeredMessageCost, adversaryHashCost, Security.IsAdversaryHash]
  | inl world =>
    cases world with
    | inl sample => simp [registeredMessageCost, freshWorldTargetHashCost, adversaryHashCost, Security.IsAdversaryHash]
    | inr query =>
      simp only [registeredMessageCost, freshWorldTargetHashCost, adversaryHashCost, Security.IsAdversaryHash, if_true]
      split_ifs <;> omega

theorem registeredTargetCharge_eq_messageCost (key : SecretKey) (reuse : ENNReal) (hashes signatures : Nat)
    (required : Finset FtsTree) (state : RegisteredTargetState) (input : (OracleWorld + SigningSpec).Domain) :
    registeredTargetCharge key reuse hashes signatures required state.1 input =
      registeredMessageCost key state input * targetCreationPrice key reuse hashes signatures required state.1 := by
  cases input <;> simp only [registeredTargetCharge, registeredMessageCost, Nat.cast_zero, zero_mul]

noncomputable def registeredLedgerReservation (key : SecretKey) (required : Finset FtsTree)
    (total : Nat) (payoff : List Index → ENNReal) (state : List Index × RegisteredCertificateLedgerState) : ENNReal :=
  registeredLedgerEnvelope key required state.2 + state.2.2.hashes *
    terminalProposalPotential (PMF.uniformOfFintype Index) total payoff state.1

theorem expected_registeredLedgerReservation_step_le (key : SecretKey) (required : Finset FtsTree)
    (stopAfter : RegisteredCertificateStop) (total : Nat) (payoff : List Index → ENNReal) (baseline : ENNReal)
    (input : (OracleWorld + SigningSpec).Domain) (state : List Index × RegisteredCertificateLedgerState)
    (hprice : RegisteredCertificateActive key input state.2 →
      targetCreationPrice key nearUniformDigestReuseWeight (state.2.2.hashes - adversaryHashCost input)
        (state.2.2.signatures - signingRequestCost input) required state.2.1.1 ≤ baseline +
          terminalProposalPotential (PMF.uniformOfFintype Index) total payoff state.1) :
    (∑' result, Pr[= result | (registeredLedgerImpl key required stopAfter input).run state] *
      registeredLedgerReservation key required total payoff result.2) ≤
      registeredLedgerReservation key required total payoff state +
        baseline * ((if RegisteredCertificateActive key input state.2 then registeredMessageCost key state.2.1 input else 0 : Nat) : ENNReal) := by
  let remaining := if RegisteredCertificateActive key input state.2 then state.2.2.hashes - adversaryHashCost input else state.2.2.hashes
  have hremaining : ∀ result ∈ ((registeredLedgerImpl key required stopAfter input).run state).support,
      result.2.2.2.hashes = remaining := by
    intro result hresult
    obtain ⟨length, record, _, hstate⟩ := registeredProposalImpl_support key (registeredCertificateEnabled key)
      (registeredLedgerUpdate key required stopAfter) input state result hresult
    rw [hstate]
    unfold registeredProposalAdvance registeredLedgerUpdate remaining
    split_ifs <;> rfl
  have hreserve : (∑' result, Pr[= result | (registeredLedgerImpl key required stopAfter input).run state] *
      (result.2.2.2.hashes * terminalProposalPotential (PMF.uniformOfFintype Index) total payoff result.2.1)) =
      remaining * terminalProposalPotential (PMF.uniformOfFintype Index) total payoff state.1 := by
    calc
      _ = ∑' result, Pr[= result | (registeredLedgerImpl key required stopAfter input).run state] *
          (remaining * terminalProposalPotential (PMF.uniformOfFintype Index) total payoff result.2.1) := by
        apply tsum_congr
        intro result
        by_cases hr : result ∈ ((registeredLedgerImpl key required stopAfter input).run state).support
        · rw [hremaining result hr]
        · have hzero : Pr[= result | (registeredLedgerImpl key required stopAfter input).run state] = 0 := by
            rw [PMF.probOutput_eq_apply, PMF.apply_eq_zero_iff]
            exact hr
          rw [hzero, zero_mul, zero_mul]
      _ = remaining * ∑' result, Pr[= result | (registeredLedgerImpl key required stopAfter input).run state] *
          terminalProposalPotential (PMF.uniformOfFintype Index) total payoff result.2.1 := by
        rw [← ENNReal.tsum_mul_left]
        exact tsum_congr (fun _ => mul_left_comm _ _ _)
      _ = _ := by rw [registeredLedgerImpl, expected_registeredProposalImpl_terminalPotential]
  simp only [registeredLedgerReservation, mul_add, ENNReal.tsum_add]
  rw [hreserve]
  apply (add_le_add (expected_registeredLedgerEnvelope_step_le key required stopAfter input state) le_rfl).trans
  by_cases hactive : RegisteredCertificateActive key input state.2
  · have hrestore := Nat.sub_add_cancel hactive.2.2.2.1
    have hcharge : registeredLedgerCharge key required input state.2 ≤
        (registeredMessageCost key state.2.1 input : ENNReal) * baseline +
        (adversaryHashCost input : ENNReal) * terminalProposalPotential (PMF.uniformOfFintype Index) total payoff state.1 := by
      rw [registeredLedgerCharge, if_pos hactive, registeredTargetCharge_eq_messageCost key _ _ _ _ state.2.1]
      apply (mul_le_mul' le_rfl (hprice hactive)).trans
      rw [mul_add]
      exact add_le_add le_rfl (mul_le_mul'
        (Nat.cast_le.mpr (registeredMessageCost_le_hashCost key state.2.1 input)) le_rfl)
    refine (add_le_add (add_le_add le_rfl hcharge) le_rfl).trans_eq ?_
    simp only [remaining, if_pos hactive]
    rw [show (state.2.2.hashes : ENNReal) = ((state.2.2.hashes - adversaryHashCost input : Nat) : ENNReal) +
      (adversaryHashCost input : ENNReal) by exact_mod_cast hrestore.symm]
    ring
  · simp only [registeredLedgerCharge, if_neg hactive, remaining, Nat.cast_zero, mul_zero, add_zero, le_refl]

end SphincsSecurity.Concrete
