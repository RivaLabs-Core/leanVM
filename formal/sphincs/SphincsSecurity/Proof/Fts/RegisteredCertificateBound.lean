import SphincsSecurity.Proof.Fts.RegisteredTargetMonitor

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

structure RegisteredCertificateMonitor where
  hashes : Nat
  signatures : Nat
  bank : HashInput → Bool
  stopped : Bool

abbrev RegisteredCertificateState := RegisteredTargetState × RegisteredCertificateMonitor

def RegisteredCertificateReady (key : SecretKey) (reuse price : ENNReal) (required : Finset FtsTree)
    (input : (OracleWorld + SigningSpec).Domain) (state : RegisteredCertificateState) : Prop :=
  state.2.stopped = false ∧ TargetsCached state.1.2 state.1.1.1 ∧
    SigningDigestsCached key.parameter state.1.1.1 key.root state.1.1.2 ∧
    adversaryHashCost input ≤ state.2.hashes ∧ signingRequestCost input ≤ state.2.signatures ∧
    (∀ message, input = .inr message → exactDigestReuseWeight key message state.1.1.1 ≤ reuse) ∧
    targetCreationPrice key reuse (state.2.hashes - adversaryHashCost input)
      (state.2.signatures - signingRequestCost input) required state.1.1 ≤ price

noncomputable def registeredCertificateUpdate (key : SecretKey) (reuse price : ENNReal)
    (required : Finset FtsTree) (input : (OracleWorld + SigningSpec).Domain)
    (before : RegisteredTargetState) (_answer : (OracleWorld + SigningSpec).Range input)
    (after : RegisteredTargetState) (monitor : RegisteredCertificateMonitor) : RegisteredCertificateMonitor :=
  if RegisteredCertificateReady key reuse price required input (before, monitor) then
    { hashes := monitor.hashes - adversaryHashCost input
      signatures := monitor.signatures - signingRequestCost input
      bank := completedRegisteredTargets after.2 key required after.1 monitor.bank
      stopped := false }
  else { monitor with stopped := true }

noncomputable def registeredCertificateImpl (key : SecretKey) (reuse price : ENNReal)
    (required : Finset FtsTree) :
    QueryImpl (OracleWorld + SigningSpec) (StateT RegisteredCertificateState ProbComp) :=
  QueryImpl.extendState (registeredTargetImpl key) (registeredCertificateUpdate key reuse price required)

noncomputable def registeredCertificatePotential (key : SecretKey) (reuse price : ENNReal)
    (required : Finset FtsTree) (state : RegisteredCertificateState) : ENNReal :=
  registeredTargetEnvelope state.1.2 key reuse state.2.hashes state.2.signatures required
    state.1.1 state.2.bank state.2.stopped + price * state.2.hashes

theorem registeredCertificateImpl_forget {α : Type} (key : SecretKey) (reuse price : ENNReal)
    (required : Finset FtsTree) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : RegisteredCertificateState) :
    Prod.map id Prod.fst <$> (simulateQ (registeredCertificateImpl key reuse price required) computation).run state =
      (simulateQ (registeredTargetImpl key) computation).run state.1 :=
  extendState_run_proj_eq _ _ _ _ _

def RegisteredCertificateCovered (key : SecretKey) (required : Finset FtsTree)
    (state : RegisteredCertificateState) : Prop :=
  state.2.stopped = false → ∀ input ∈ state.1.2,
    TargetCertificateAt key required state.1.1 input → state.2.bank input = true

theorem registeredCertificate_step_covered (key : SecretKey) (reuse price : ENNReal)
    (required : Finset FtsTree) (input : (OracleWorld + SigningSpec).Domain)
    (state : RegisteredCertificateState)
    (result : (OracleWorld + SigningSpec).Range input × RegisteredCertificateState)
    (hresult : result ∈ support ((registeredCertificateImpl key reuse price required input).run state)) :
    RegisteredCertificateCovered key required result.2 := by
  rw [registeredCertificateImpl, QueryImpl.extendState_apply, bind_pure_comp, support_map] at hresult
  obtain ⟨step, _, rfl⟩ := hresult
  unfold RegisteredCertificateCovered registeredCertificateUpdate
  split_ifs with hready
  · intro _ query hquery hcertificate
    simp [completedRegisteredTargets, hquery, hcertificate]
  · simp

theorem registeredCertificate_run_covered {α : Type} (key : SecretKey) (reuse price : ENNReal)
    (required : Finset FtsTree) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : RegisteredCertificateState) (hcovered : RegisteredCertificateCovered key required state)
    (result : α × RegisteredCertificateState)
    (hresult : result ∈ support ((simulateQ (registeredCertificateImpl key reuse price required) computation).run state)) :
    RegisteredCertificateCovered key required result.2 := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hresult
      subst result
      exact hcovered
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hresult
      obtain ⟨step, hstep, htail⟩ := hresult
      exact ih step.1 step.2 (registeredCertificate_step_covered key reuse price required input state step hstep)
        result htail

theorem expected_registeredCertificate_step_le (key : SecretKey) (reuse price : ENNReal)
    (required : Finset FtsTree) (input : (OracleWorld + SigningSpec).Domain)
    (state : RegisteredCertificateState) :
    (∑' result, Pr[= result | (registeredCertificateImpl key reuse price required input).run state] *
      registeredCertificatePotential key reuse price required result.2) ≤
      registeredCertificatePotential key reuse price required state := by
  rw [registeredCertificateImpl, QueryImpl.extendState_apply, bind_pure_comp, tsum_probOutput_map_mul]
  by_cases hready : RegisteredCertificateReady key reuse price required input state
  · have hactive := hready
    obtain ⟨hstopped, hcached, hsigned, hhashes, hsignatures, hreuse, hprice⟩ := hready
    simp only [registeredCertificateUpdate, if_pos hactive, registeredCertificatePotential,
      mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right]
    have hstep := expected_registeredTargetImpl_le key reuse
      (state.2.hashes - adversaryHashCost input) (state.2.signatures - signingRequestCost input)
      required state.1 state.2.bank input (fun _ => false) hcached hsigned hreuse
    have hhash := Nat.sub_add_cancel hhashes
    have hsign := Nat.sub_add_cancel hsignatures
    rw [hhash, hsign] at hstep
    have hcharge : registeredTargetCharge key reuse (state.2.hashes - adversaryHashCost input)
        (state.2.signatures - signingRequestCost input) required state.1.1 input ≤
        price * adversaryHashCost input := by
      unfold registeredTargetCharge
      cases input with
      | inr message => simp [adversaryHashCost, Security.IsAdversaryHash]
      | inl world =>
          cases world with
          | inl sample => simp [freshWorldTargetHashCost, adversaryHashCost, Security.IsAdversaryHash]
          | inr query =>
              simp only [adversaryHashCost, Security.IsAdversaryHash, if_true, Nat.cast_one, mul_one]
              have hcost : (freshWorldTargetHashCost key.parameter state.1.1.1 (.inr query) : ENNReal) ≤ 1 := by
                simp only [freshWorldTargetHashCost]
                split_ifs <;> norm_num
              exact (mul_le_mul' hcost (by simpa [adversaryHashCost, Security.IsAdversaryHash] using hprice)).trans_eq
                (one_mul price)
    calc
      _ ≤ (registeredTargetEnvelope state.1.2 key reuse state.2.hashes state.2.signatures required
          state.1.1 state.2.bank false + price * adversaryHashCost input) +
          price * ((state.2.hashes - adversaryHashCost input : Nat) : ENNReal) :=
        add_le_add (hstep.trans (add_le_add le_rfl hcharge))
          (mul_le_of_le_one_left' tsum_probOutput_le_one)
      _ = registeredTargetEnvelope state.1.2 key reuse state.2.hashes state.2.signatures required
          state.1.1 state.2.bank state.2.stopped + price * state.2.hashes := by
        rw [hstopped, add_assoc, ← mul_add, ← Nat.cast_add, Nat.add_sub_of_le hhashes]
  · simp only [registeredCertificateUpdate, if_neg hready, registeredCertificatePotential,
      registeredTargetEnvelope, bankedCacheWeight_stopped, ENNReal.tsum_mul_right]
    apply (mul_le_of_le_one_left' tsum_probOutput_le_one).trans
    exact add_le_add (certificateBankCount_le_bankedCacheWeight _ _ _ _ _) le_rfl

theorem expected_registeredCertificate_run_le {α : Type} (key : SecretKey) (reuse price : ENNReal)
    (required : Finset FtsTree) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : RegisteredCertificateState) :
    (∑' result, Pr[= result | (simulateQ (registeredCertificateImpl key reuse price required) computation).run state] *
      registeredCertificatePotential key reuse price required result.2) ≤
      registeredCertificatePotential key reuse price required state := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, tsum_probOutput_pure_mul, le_refl]
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, tsum_probOutput_bind_mul]
      calc
        _ ≤ ∑' result, Pr[= result | (registeredCertificateImpl key reuse price required input).run state] *
            registeredCertificatePotential key reuse price required result.2 :=
          ENNReal.tsum_le_tsum fun result => mul_le_mul' le_rfl (ih result.1 result.2)
        _ ≤ _ := expected_registeredCertificate_step_le key reuse price required input state

/-- The expected certificate count is at most the hash budget times the target price. -/
theorem expected_registeredCertificate_count_le {α : Type} (key : SecretKey) (reuse price : ENNReal)
    (required : Finset FtsTree) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (cache : QueryCache HashSpec) (hashes signatures : Nat) :
    (∑' result, Pr[= result | (simulateQ (registeredCertificateImpl key reuse price required) computation).run
      (((cache, []), ∅), ⟨hashes, signatures, fun _ => false, false⟩)] *
      certificateBankCount result.2.2.bank) ≤ price * hashes := by
  have h := expected_registeredCertificate_run_le key reuse price required computation
    (((cache, []), ∅), ⟨hashes, signatures, fun _ => false, false⟩)
  rw [registeredCertificatePotential, registeredTargetEnvelope_empty, zero_add] at h
  refine le_trans ?_ h
  apply ENNReal.tsum_le_tsum
  intro result
  exact mul_le_mul' le_rfl ((certificateBankCount_le_bankedCacheWeight _ _ _ _ _).trans le_self_add)

theorem registeredCertificate_probability_le {α : Type} (key : SecretKey) (reuse price : ENNReal)
    (required : Finset FtsTree) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (cache : QueryCache HashSpec) (hashes signatures : Nat) :
    Pr[fun result => ∃ input, result.2.2.bank input = true |
      (simulateQ (registeredCertificateImpl key reuse price required) computation).run
        (((cache, []), ∅), ⟨hashes, signatures, fun _ => false, false⟩)] ≤ price * hashes := by
  refine le_trans ?_ (expected_registeredCertificate_count_le key reuse price required computation cache hashes signatures)
  apply probEvent_le_tsum_probOutput_mul_cost_of_mem_support
  rintro result _ ⟨input, hinput⟩
  exact one_le_certificateBankCount result.2.2.bank input hinput

end SphincsSecurity.Concrete
