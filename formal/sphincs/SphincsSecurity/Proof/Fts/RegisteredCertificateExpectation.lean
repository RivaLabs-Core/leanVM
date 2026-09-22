import SphincsSecurity.Proof.Fts.RegisteredCertificateInvariant
import SphincsSecurity.Proof.Fts.FixedCertificateCoverage

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def registeredLedgerFunds (key : SecretKey) (required : Finset FtsTree)
    (q total : Nat) (baseline : ENNReal) (state : List Index × RegisteredCertificateLedgerState) : ENNReal :=
  registeredLedgerReservation key required total (fun word => terminalCertificatePrice required word - baseline) state +
    baseline * ((q - state.2.2.messages : Nat) : ENNReal)

theorem registeredLedgerImpl_messages_hashes_le (key : SecretKey) (required : Finset FtsTree)
    (stopAfter : RegisteredCertificateStop) (input : (OracleWorld + SigningSpec).Domain)
    (state : List Index × RegisteredCertificateLedgerState)
    (result : (OracleWorld + SigningSpec).Range input × (List Index × RegisteredCertificateLedgerState))
    (hresult : result ∈ ((registeredLedgerImpl key required stopAfter input).run state).support) :
    result.2.2.2.messages + result.2.2.2.hashes ≤ state.2.2.messages + state.2.2.hashes := by
  obtain ⟨length, record, _, hstate⟩ := registeredProposalImpl_support key (registeredCertificateEnabled key)
    (registeredLedgerUpdate key required stopAfter) input state result hresult
  rw [hstate]
  unfold registeredProposalAdvance registeredLedgerUpdate
  split_ifs with hactive
  · have hcost := registeredMessageCost_le_hashCost key state.2.1 input
    have hhash := hactive.2.2.2.1
    dsimp only
    omega
  · exact le_rfl

theorem registeredLedgerImpl_messages (key : SecretKey) (required : Finset FtsTree)
    (stopAfter : RegisteredCertificateStop) (input : (OracleWorld + SigningSpec).Domain)
    (state : List Index × RegisteredCertificateLedgerState)
    (result : (OracleWorld + SigningSpec).Range input × (List Index × RegisteredCertificateLedgerState))
    (hresult : result ∈ ((registeredLedgerImpl key required stopAfter input).run state).support) :
    result.2.2.2.messages = state.2.2.messages +
      if RegisteredCertificateActive key input state.2 then registeredMessageCost key state.2.1 input else 0 := by
  obtain ⟨length, record, _, hstate⟩ := registeredProposalImpl_support key (registeredCertificateEnabled key)
    (registeredLedgerUpdate key required stopAfter) input state result hresult
  rw [hstate]
  unfold registeredProposalAdvance registeredLedgerUpdate
  split_ifs <;> simp only [Nat.add_zero]

theorem expected_registeredLedgerFunds_step_le (key : SecretKey) (required : Finset FtsTree)
    (stopAfter : RegisteredCertificateStop) (q total : Nat) (baseline : ENNReal)
    (input : (OracleWorld + SigningSpec).Domain) (state : List Index × RegisteredCertificateLedgerState)
    (hq : q ≤ (2 ^ 127 + 2 ^ 64)) (hinv : RegisteredCertificateInvariant key q total state)
    (hroom : state.2.2.messages + state.2.2.hashes ≤ q) :
    (∑' result, Pr[= result | (registeredLedgerImpl key required stopAfter input).run state] *
      registeredLedgerFunds key required q total baseline result.2) ≤
      registeredLedgerFunds key required q total baseline state := by
  let cost := if RegisteredCertificateActive key input state.2 then registeredMessageCost key state.2.1 input else 0
  have hcost : state.2.2.messages + cost ≤ q := by
    by_cases hactive : RegisteredCertificateActive key input state.2
    · have hmsg := registeredMessageCost_le_hashCost key state.2.1 input
      have hhash := hactive.2.2.2.1
      simp only [cost, if_pos hactive]
      omega
    · simp only [cost, if_neg hactive, Nat.add_zero]
      omega
  have hconstant : (∑' result, Pr[= result | (registeredLedgerImpl key required stopAfter input).run state] *
      (baseline * ((q - result.2.2.2.messages : Nat) : ENNReal))) ≤
      baseline * ((q - (state.2.2.messages + cost) : Nat) : ENNReal) := by
    calc
      _ = ∑' result, Pr[= result | (registeredLedgerImpl key required stopAfter input).run state] *
          (baseline * ((q - (state.2.2.messages + cost) : Nat) : ENNReal)) := by
        apply tsum_congr
        intro result
        by_cases hr : result ∈ ((registeredLedgerImpl key required stopAfter input).run state).support
        · rw [registeredLedgerImpl_messages key required stopAfter input state result hr]
        · have hzero : Pr[= result | (registeredLedgerImpl key required stopAfter input).run state] = 0 := by
            rw [PMF.probOutput_eq_apply, PMF.apply_eq_zero_iff]
            exact hr
          rw [hzero, zero_mul, zero_mul]
      _ ≤ _ := by rw [ENNReal.tsum_mul_right]; exact mul_le_of_le_one_left' tsum_probOutput_le_one
  simp only [registeredLedgerFunds, mul_add, ENNReal.tsum_add]
  apply (add_le_add (expected_registeredLedgerReservation_step_le_message key required stopAfter q total baseline input state hq
    (fun hactive => hinv hactive.1)) hconstant).trans_eq
  change (_ + baseline * (cost : ENNReal)) + baseline * ((q - (state.2.2.messages + cost) : Nat) : ENNReal) = _
  rw [add_assoc, ← mul_add, ← Nat.cast_add]
  congr 2
  exact_mod_cast (show cost + (q - (state.2.2.messages + cost)) = q - state.2.2.messages by omega)

theorem expected_registeredLedgerFunds_run_le {α : Type} (key : SecretKey) (required : Finset FtsTree)
    (stopAfter : RegisteredCertificateStop) (q total : Nat) (baseline : ENNReal)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : List Index × RegisteredCertificateLedgerState)
    (hq : q ≤ (2 ^ 127 + 2 ^ 64)) (hinv : RegisteredCertificateInvariant key q total state)
    (hroom : state.2.2.messages + state.2.2.hashes ≤ q) :
    (∑' result, Pr[= result | (simulateQ (registeredLedgerImpl key required
      (fun input state length record => registeredPrefixStop input state length record || stopAfter input state length record))
        computation).run state] * registeredLedgerFunds key required q total baseline result.2) ≤
      registeredLedgerFunds key required q total baseline state := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, tsum_probOutput_pure_mul, le_refl]
  | query_bind input next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, tsum_probOutput_bind_mul]
    apply le_trans _ (expected_registeredLedgerFunds_step_le key required
      (fun input state length record => registeredPrefixStop input state length record || stopAfter input state length record)
      q total baseline input state hq hinv hroom)
    apply ENNReal.tsum_le_tsum
    intro result
    by_cases hr : result ∈ ((registeredLedgerImpl key required
      (fun input state length record => registeredPrefixStop input state length record || stopAfter input state length record)
        input).run state).support
    · exact mul_le_mul' le_rfl (ih result.1 result.2
        (registeredLedgerImpl_invariant key q total required stopAfter input state hinv result hr)
        ((registeredLedgerImpl_messages_hashes_le key required _ input state result hr).trans hroom))
    · have hzero : Pr[= result | (registeredLedgerImpl key required
        (fun input state length record => registeredPrefixStop input state length record || stopAfter input state length record)
          input).run state] = 0 := by
        rw [PMF.probOutput_eq_apply, PMF.apply_eq_zero_iff]
        exact hr
      rw [hzero, zero_mul, zero_mul]

theorem registeredLedgerRun_messages_hashes_le {α : Type} (key : SecretKey) (required : Finset FtsTree)
    (stopAfter : RegisteredCertificateStop) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : List Index × RegisteredCertificateLedgerState)
    (result : α × (List Index × RegisteredCertificateLedgerState))
    (hresult : result ∈ ((simulateQ (registeredLedgerImpl key required stopAfter) computation).run state).support) :
    result.2.2.2.messages + result.2.2.2.hashes ≤ state.2.2.messages + state.2.2.hashes := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, PMF.monad_pure_eq_pure, PMF.support_pure, Set.mem_singleton_iff] at hresult
    subst result
    exact le_rfl
  | query_bind input next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff] at hresult
    obtain ⟨step, hstep, htail⟩ := hresult
    exact (ih step.1 step.2 result htail).trans (registeredLedgerImpl_messages_hashes_le key required stopAfter input state step hstep)

theorem expected_registeredCertificate_count_le_message_excess {α : Type} (key : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (cache : QueryCache HashSpec)
    (q total : Nat) (required : Finset FtsTree) (stopAfter : RegisteredCertificateStop)
    (hq : q ≤ (2 ^ 127 + 2 ^ 64)) (hpool : fixedProposalLength ≤ total) (baseline : ENNReal) (hbaseline : baseline ≠ ⊤) :
    let law := (simulateQ (registeredLedgerImpl key required
      (fun input state length record => registeredPrefixStop input state length record || stopAfter input state length record))
        computation).run ([], ((cache, []), ∅), initialRegisteredCertificateLedger q)
    (∑' result, Pr[= result | law] * certificateBankCount result.2.2.2.bank) ≤
      baseline * (∑' result, Pr[= result | law] * result.2.2.2.messages) +
        (q : ENNReal) * uniformWordAverage total (fun word => terminalCertificatePrice required word - baseline) := by
  dsimp only
  let law := (simulateQ (registeredLedgerImpl key required
    (fun input state length record => registeredPrefixStop input state length record || stopAfter input state length record))
      computation).run ([], ((cache, []), ∅), initialRegisteredCertificateLedger q)
  have hfund := expected_registeredLedgerFunds_run_le key required stopAfter q total baseline computation
    ([], ((cache, []), ∅), initialRegisteredCertificateLedger q) hq
    (registeredCertificateInvariant_initial key q total cache hpool) (by simp [initialRegisteredCertificateLedger])
  have hinitial : registeredLedgerFunds key required q total baseline
      ([], ((cache, []), ∅), initialRegisteredCertificateLedger q) =
        (q : ENNReal) * uniformWordAverage total (fun word => terminalCertificatePrice required word - baseline) + baseline * q := by
    unfold registeredLedgerFunds registeredLedgerReservation registeredLedgerEnvelope
    simp only [initialRegisteredCertificateLedger, registeredTargetEnvelope_empty, zero_add, Nat.sub_zero]
    rw [terminalProposalPotential, completeProposalWord_nil, ← uniformWordAverage_eq_independent]
  rw [hinitial] at hfund
  have hpoint : ∀ result ∈ law.support,
      certificateBankCount result.2.2.2.bank + baseline * (q : ENNReal) ≤
        registeredLedgerFunds key required q total baseline result.2 + baseline * result.2.2.2.messages := by
    intro result hresult
    have hroom := registeredLedgerRun_messages_hashes_le key required _ computation
      ([], ((cache, []), ∅), initialRegisteredCertificateLedger q) result hresult
    have hmessages : result.2.2.2.messages ≤ q := by
      simpa only [initialRegisteredCertificateLedger, Nat.zero_add] using (Nat.le_add_right _ _).trans hroom
    have hbank : certificateBankCount result.2.2.2.bank ≤
        registeredLedgerReservation key required total (fun word => terminalCertificatePrice required word - baseline) result.2 :=
      (certificateBankCount_le_bankedCacheWeight _ _ _ _ _).trans le_self_add
    calc
      _ ≤ registeredLedgerReservation key required total (fun word => terminalCertificatePrice required word - baseline) result.2 + baseline * q :=
        add_le_add hbank le_rfl
      _ = _ := by
        unfold registeredLedgerFunds
        rw [add_assoc, ← mul_add, ← Nat.cast_add, Nat.sub_add_cancel hmessages]
  have hexpect : (∑' result, Pr[= result | law] * certificateBankCount result.2.2.2.bank) + baseline * q ≤
      (∑' result, Pr[= result | law] * registeredLedgerFunds key required q total baseline result.2) +
        baseline * (∑' result, Pr[= result | law] * result.2.2.2.messages) := by
    have h := ENNReal.tsum_le_tsum (fun result => show
        Pr[= result | law] * (certificateBankCount result.2.2.2.bank + baseline * q) ≤
          Pr[= result | law] * (registeredLedgerFunds key required q total baseline result.2 + baseline * result.2.2.2.messages) from by
      by_cases hr : result ∈ law.support
      · exact mul_le_mul' le_rfl (hpoint result hr)
      · have hz : Pr[= result | law] = 0 := by rw [PMF.probOutput_eq_apply, PMF.apply_eq_zero_iff]; exact hr
        rw [hz, zero_mul, zero_mul])
    simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right] at h
    have hmass : (∑' result, Pr[= result | law]) = 1 := by simp
    rw [hmass, one_mul] at h
    have hswitch : (∑' result, Pr[= result | law] * (baseline * result.2.2.2.messages)) =
        baseline * (∑' result, Pr[= result | law] * result.2.2.2.messages) := by
      rw [← ENNReal.tsum_mul_left]
      exact tsum_congr (fun _ => mul_left_comm _ _ _)
    rwa [hswitch] at h
  apply ENNReal.le_of_add_le_add_right (a := baseline * (q : ENNReal)) (by finiteness)
  exact (hexpect.trans (add_le_add hfund le_rfl)).trans_eq (by dsimp only [law]; ac_rfl)

end SphincsSecurity.Concrete
