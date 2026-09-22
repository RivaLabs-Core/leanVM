import SphincsSecurity.Proof.Fts.RegisteredLedgerCoverage

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def IsMessageQuery (parameter : PublicParameter) : (OracleWorld + SigningSpec).Domain → Prop
  | .inl (.inr input) => FtsProbeSimulation.MessageHashInput parameter input
  | _ => False

theorem registeredMessageCost_le_messageQuery (key : SecretKey) (state : RegisteredTargetState)
    (input : (OracleWorld + SigningSpec).Domain) :
    registeredMessageCost key state input ≤ if IsMessageQuery key.parameter input then 1 else 0 := by
  cases input with
  | inr message => simp [registeredMessageCost, IsMessageQuery]
  | inl world =>
    cases world with
    | inl sample => simp [registeredMessageCost, freshWorldTargetHashCost, IsMessageQuery]
    | inr input =>
      simp only [registeredMessageCost, freshWorldTargetHashCost, IsMessageQuery]
      split_ifs <;> simp_all

theorem registeredCacheLedgerRun_messages_le_counted {α : Type} (key : SecretKey) (required : Finset FtsTree)
    (stopAfter : RegisteredCertificateStop) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : RegisteredCacheLedgerState) (result : (α × Nat) × RegisteredCacheLedgerState)
    (hresult : result ∈ ((simulateQ (registeredCacheLedgerImpl key required stopAfter)
      (QueryCap.counted (IsMessageQuery key.parameter) computation)).run state).support) :
    result.2.1.2.2.messages ≤ state.1.2.2.messages + result.1.2 := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
    simp only [QueryCap.counted_pure, simulateQ_pure, StateT.run_pure, PMF.monad_pure_eq_pure,
      PMF.mem_support_pure_iff] at hresult
    subst result
    exact Nat.le_add_right _ _
  | query_bind input next ih =>
    rw [QueryCap.counted_query_bind, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
      PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff] at hresult
    obtain ⟨step, hstep, htail⟩ := hresult
    simp only [bind_pure_comp, simulateQ_map, StateT.run_map, PMF.monad_map_eq_map, PMF.mem_support_map_iff] at htail
    obtain ⟨tail, htail, rfl⟩ := htail
    have hnext := ih step.1 step.2 tail htail
    have hledger := (registeredCacheLedgerImpl_support key required stopAfter input state step hstep).2
    have hmessages := registeredLedgerImpl_messages key required stopAfter input state.1 _ hledger
    have hcost := registeredMessageCost_le_messageQuery key state.1.2.1 input
    dsimp only at hnext hmessages ⊢
    split_ifs at hmessages <;> omega

theorem expected_registeredMessages_le_counted {α : Type} (key : SecretKey) (required : Finset FtsTree)
    (stopAfter : RegisteredCertificateStop) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (cache : QueryCache HashSpec) (q : Nat) :
    (∑' result, Pr[= result | (simulateQ (registeredCacheLedgerImpl key required stopAfter) computation).run
      (([], ((cache, []), ∅), initialRegisteredCertificateLedger q), false)] * result.2.1.2.2.messages) ≤
    ∑' result, Pr[= result | (simulateQ (registeredTargetImpl key)
      (QueryCap.counted (IsMessageQuery key.parameter) computation)).run ((cache, []), ∅)] * result.1.2 := by
  let initial : RegisteredCacheLedgerState := (([], ((cache, []), ∅), initialRegisteredCertificateLedger q), false)
  let law := (simulateQ (registeredCacheLedgerImpl key required stopAfter)
    (QueryCap.counted (IsMessageQuery key.parameter) computation)).run initial
  have hforget : (fun r => (r.1.1, r.2)) <$> law =
      (simulateQ (registeredCacheLedgerImpl key required stopAfter) computation).run initial := by
    dsimp only [law]
    rw [← StateT.run_map, ← simulateQ_map, QueryCap.counted_forget]
  rw [← hforget, tsum_probOutput_map_mul]
  have hproject := congrArg (fun dist => ∑' result, Pr[= result | dist] * (result.1.2 : ENNReal))
    (simulateQ_registeredCacheLedgerImpl_original key required stopAfter
      (QueryCap.counted (IsMessageQuery key.parameter) computation) initial)
  rw [tsum_probOutput_map_mul] at hproject
  change (∑' result, Pr[= result | law] * (result.1.2 : ENNReal)) =
    ∑' result, Pr[= result | (simulateQ (registeredTargetImpl key)
      (QueryCap.counted (IsMessageQuery key.parameter) computation)).run ((cache, []), ∅)] * result.1.2 at hproject
  rw [← hproject]
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hr : result ∈ law.support
  · apply mul_le_mul' le_rfl
    have h := registeredCacheLedgerRun_messages_le_counted key required stopAfter computation initial result hr
    simp only [initial, initialRegisteredCertificateLedger, Nat.zero_add] at h
    exact_mod_cast h
  · have hz : Pr[= result | law] = 0 := by rw [PMF.probOutput_eq_apply, PMF.apply_eq_zero_iff]; exact hr
    simp only [hz, zero_mul, le_refl]

end SphincsSecurity.Concrete
