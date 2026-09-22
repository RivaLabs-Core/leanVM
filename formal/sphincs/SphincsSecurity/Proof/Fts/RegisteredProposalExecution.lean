import SphincsSecurity.Proof.Fts.RegisteredProposalBound
import SphincsSecurity.Proof.Fts.OriginalTerminalProposal

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

private theorem probCompLift_map {α β : Type} (computation : ProbComp α) (f : α → β) :
    (liftM computation : PMF α).map f = (liftM (f <$> computation) : PMF β) :=
  (liftM_map (m := ProbComp) (n := PMF) _ _).symm

noncomputable def registeredRecordNext (input : (OracleWorld + SigningSpec).Domain)
    (state : RegisteredTargetState) (record : ProposalExecutionRecord input) : RegisteredTargetState :=
  let after := (record.cache, state.1.2 ++ signingLogFragment input record.output)
  (after, registerFreshTarget input state.1 record.output after state.2)

theorem originalProposalRecord_registered (key : SecretKey) (input : (OracleWorld + SigningSpec).Domain)
    (state : RegisteredTargetState) :
    (originalProposalRecord key input state.1.1).map
      (fun record => (record.output, registeredRecordNext input state record)) =
      (liftM ((registeredTargetImpl key input).run state) : PMF _) := by
  have h := originalProposalRecord_project key input state.1.1
  have hbase : (originalAdversaryPMFImpl key input).run state.1.1 =
      (liftM ((unloggedMappedAdversaryImpl key input).run state.1.1) : PMF _) := by
    have hrun := simulateQ_originalAdversaryPMFImpl key (liftM ((OracleWorld + SigningSpec).query input)) state.1.1
    simpa only [simulateQ_spec_query] using hrun
  rw [hbase] at h
  have hmap := congrArg (fun law => law.map (fun result =>
    let after := (result.2, state.1.2 ++ signingLogFragment input result.1)
    (result.1, (after, registerFreshTarget input state.1 result.1 after state.2)))) h
  rw [PMF.map_comp, probCompLift_map] at hmap
  rw [registeredTargetImpl, QueryImpl.extendState_apply, bind_pure_comp,
    logTracedMappedAdversaryImpl_run_map, Functor.map_map]
  exact hmap

def RegisteredProposalReady (key : SecretKey) (state : RegisteredTargetState) : Prop :=
  RegisteredCacheInvariant key state ∧ state.2.card ≤ (2 ^ 127 + 2 ^ 64) ∧ state.1.2.length ≤ signatureLimit ∧
    ¬RegisteredCacheExceptional key state

theorem originalProposalRecord_registered_cap (key : SecretKey) (message : Message)
    (state : RegisteredTargetState) (hready : RegisteredProposalReady key state) (index : Index) :
    targetProposalAcceptance *
      ((originalProposalRecord key (.inr message) state.1.1).map (fun record => record.index)) index ≤
      PMF.uniformOfFintype Index index := by
  rw [originalProposalRecord_index]
  exact registeredCache_completedSigningRecord_cap (signingBoundaryTrace key.parameter) key state state.2.card
    hready.1 hready.2.1 le_rfl hready.2.2.1 hready.2.2.2 message index

noncomputable def registeredProposalActive {μ : Type} (key : SecretKey)
    (enabled : Message → RegisteredTargetState × μ → Bool) :
    (OracleWorld + SigningSpec).Domain → RegisteredTargetState × μ → Bool
  | .inl _, _ => false
  | .inr message, state => enabled message state && decide (RegisteredProposalReady key state.1)

noncomputable def registeredRejectedProposal {μ : Type} (key : SecretKey) :
    (OracleWorld + SigningSpec).Domain → RegisteredTargetState × μ → PMF Index
  | .inl _, _ => PMF.uniformOfFintype Index
  | .inr message, state =>
    if hready : RegisteredProposalReady key state.1 then
      proposalResidualLaw (PMF.uniformOfFintype Index)
        ((originalProposalRecord key (.inr message) state.1.1.1).map (fun record => record.index))
        targetProposalAcceptance targetProposalAcceptance_lt_one
        (originalProposalRecord_registered_cap key message state.1 hready)
    else PMF.uniformOfFintype Index

noncomputable def registeredProposalAdvance {μ : Type}
    (update : (input : (OracleWorld + SigningSpec).Domain) → RegisteredTargetState × μ →
      Nat → ProposalExecutionRecord input → μ)
    (input : (OracleWorld + SigningSpec).Domain) (state : RegisteredTargetState × μ)
    (length : Nat) (record : ProposalExecutionRecord input) : RegisteredTargetState × μ :=
  (registeredRecordNext input state.1 record, update input state length record)

noncomputable def registeredProposalImpl {μ : Type} (key : SecretKey)
    (enabled : Message → RegisteredTargetState × μ → Bool)
    (update : (input : (OracleWorld + SigningSpec).Domain) → RegisteredTargetState × μ →
      Nat → ProposalExecutionRecord input → μ) :
    QueryImpl (OracleWorld + SigningSpec) (StateT (List Index × (RegisteredTargetState × μ)) PMF) :=
  proposalRecordImpl (fun input state => originalProposalRecord key input state.1.1.1)
    (fun _ record => record.output) (registeredProposalAdvance update) (fun _ record => record.index)
    (registeredRejectedProposal key) (registeredProposalActive key enabled)
    targetProposalAcceptance targetProposalAcceptance_ne_zero targetProposalAcceptance_lt_one.le

noncomputable def registeredLengthImpl {μ : Type} (key : SecretKey)
    (enabled : Message → RegisteredTargetState × μ → Bool)
    (update : (input : (OracleWorld + SigningSpec).Domain) → RegisteredTargetState × μ →
      Nat → ProposalExecutionRecord input → μ) :
    QueryImpl (OracleWorld + SigningSpec) (StateT (RegisteredTargetState × μ) PMF) :=
  lengthRecordImpl (fun input state => originalProposalRecord key input state.1.1.1)
    (fun _ record => record.output) (registeredProposalAdvance update) (registeredProposalActive key enabled)
    targetProposalAcceptance targetProposalAcceptance_ne_zero targetProposalAcceptance_lt_one.le

theorem registeredProposalImpl_support {μ : Type} (key : SecretKey)
    (enabled : Message → RegisteredTargetState × μ → Bool)
    (update : (input : (OracleWorld + SigningSpec).Domain) → RegisteredTargetState × μ →
      Nat → ProposalExecutionRecord input → μ)
    (input : (OracleWorld + SigningSpec).Domain) (state : List Index × (RegisteredTargetState × μ))
    (result : (OracleWorld + SigningSpec).Range input × (List Index × (RegisteredTargetState × μ)))
    (hresult : result ∈ ((registeredProposalImpl key enabled update input).run state).support) :
    ∃ length record, result.1 = record.output ∧ result.2.2 = registeredProposalAdvance update input state.2 length record := by
  simp only [registeredProposalImpl, proposalRecordImpl, StateT.run_mk] at hresult
  split at hresult
  · rw [PMF.mem_support_map_iff] at hresult
    obtain ⟨source, _, rfl⟩ := hresult
    exact ⟨source.1.length + 1, source.2, rfl, rfl⟩
  · rw [PMF.mem_support_map_iff] at hresult
    obtain ⟨record, _, rfl⟩ := hresult
    exact ⟨0, record, rfl, rfl⟩

theorem registeredProposalImpl_complete {μ : Type} (key : SecretKey)
    (enabled : Message → RegisteredTargetState × μ → Bool)
    (update : (input : (OracleWorld + SigningSpec).Domain) → RegisteredTargetState × μ →
      Nat → ProposalExecutionRecord input → μ)
    (total : Nat) (input : (OracleWorld + SigningSpec).Domain)
    (state : List Index × (RegisteredTargetState × μ)) :
    ((registeredProposalImpl key enabled update input).run state).bind
      (fun result => completeProposalWord (PMF.uniformOfFintype Index) total result.2.1) =
        completeProposalWord (PMF.uniformOfFintype Index) total state.1 := by
  simp only [registeredProposalImpl, proposalRecordImpl, StateT.run_mk]
  by_cases hactive : registeredProposalActive key enabled input state.2 = true
  · rw [if_pos hactive, PMF.bind_map]
    cases input with
    | inl world => simp only [registeredProposalActive, Bool.false_eq_true] at hactive
    | inr message =>
      have hready : RegisteredProposalReady key state.2.1 := by
        by_contra hready
        simp [registeredProposalActive, hready] at hactive
      rw [registeredRejectedProposal, dif_pos hready]
      simpa only [cappedRecordProposalBridge, List.append_assoc, Function.comp_def] using
        complete_cappedRecordProposalBridge_prefix (PMF.uniformOfFintype Index)
          (originalProposalRecord key (.inr message) state.2.1.1.1) (fun record => record.index)
          targetProposalAcceptance targetProposalAcceptance_ne_zero targetProposalAcceptance_lt_one
          (originalProposalRecord_registered_cap key message state.2.1 hready) total state.1
  · rw [if_neg hactive, PMF.bind_map]
    simp only [Function.comp_def]
    exact PMF.bind_const _ _

theorem simulateQ_registeredProposalImpl_complete {μ α : Type} (key : SecretKey)
    (enabled : Message → RegisteredTargetState × μ → Bool)
    (update : (input : (OracleWorld + SigningSpec).Domain) → RegisteredTargetState × μ →
      Nat → ProposalExecutionRecord input → μ)
    (total : Nat) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : List Index × (RegisteredTargetState × μ)) :
    ((simulateQ (registeredProposalImpl key enabled update) computation).run state).bind
      (fun result => completeProposalWord (PMF.uniformOfFintype Index) total result.2.1) =
        completeProposalWord (PMF.uniformOfFintype Index) total state.1 := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, PMF.monad_pure_eq_pure, PMF.pure_bind]
  | query_bind input next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, PMF.monad_bind_eq_bind, PMF.bind_bind]
    simp_rw [ih]
    exact registeredProposalImpl_complete key enabled update total input state

theorem expected_registeredProposalImpl_terminalPotential {μ : Type} (key : SecretKey)
    (enabled : Message → RegisteredTargetState × μ → Bool)
    (update : (input : (OracleWorld + SigningSpec).Domain) → RegisteredTargetState × μ →
      Nat → ProposalExecutionRecord input → μ)
    (total : Nat) (payoff : List Index → ENNReal)
    (input : (OracleWorld + SigningSpec).Domain) (state : List Index × (RegisteredTargetState × μ)) :
    (∑' result, Pr[= result | (registeredProposalImpl key enabled update input).run state] *
      terminalProposalPotential (PMF.uniformOfFintype Index) total payoff result.2.1) =
        terminalProposalPotential (PMF.uniformOfFintype Index) total payoff state.1 := by
  have h := congrArg (fun law : PMF (List Index) => ∑' word, Pr[= word | law] * payoff word)
    (registeredProposalImpl_complete key enabled update total input state)
  rw [← PMF.monad_bind_eq_bind, tsum_probOutput_bind_mul] at h
  exact h

theorem simulateQ_registeredProposalImpl_original {μ α : Type} (key : SecretKey)
    (enabled : Message → RegisteredTargetState × μ → Bool)
    (update : (input : (OracleWorld + SigningSpec).Domain) → RegisteredTargetState × μ →
      Nat → ProposalExecutionRecord input → μ)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : List Index × (RegisteredTargetState × μ)) :
    (fun result => (result.1, result.2.2.1)) <$>
      (simulateQ (registeredProposalImpl key enabled update) computation).run state =
      (liftM ((simulateQ (registeredTargetImpl key) computation).run state.2.1) : PMF _) := by
  have hlength : Prod.map id Prod.snd <$>
      (simulateQ (registeredProposalImpl key enabled update) computation).run state =
      (simulateQ (registeredLengthImpl key enabled update) computation).run state.2 :=
    simulateQ_proposalRecordImpl_project _ _ _ _ _ _ _ _ _ computation state
  have hbase := simulateQ_lengthRecordImpl_project
    (fun input state => originalProposalRecord key input state.1.1.1)
    (fun _ record => record.output) (registeredProposalAdvance update) (registeredProposalActive key enabled)
    targetProposalAcceptance targetProposalAcceptance_ne_zero targetProposalAcceptance_lt_one.le
    (fun input => StateT.mk fun state => (liftM ((registeredTargetImpl key input).run state) : PMF _))
    Prod.fst (fun input state record => registeredRecordNext input state.1 record)
    (fun _ _ _ _ => rfl) (fun input state => originalProposalRecord_registered key input state.1) computation state.2
  rw [simulateQ_liftProbCompImpl_run] at hbase
  calc
    _ = Prod.map id Prod.fst <$> (Prod.map id Prod.snd <$>
        (simulateQ (registeredProposalImpl key enabled update) computation).run state) := by
      simp only [Functor.map_map]
      rfl
    _ = _ := by rw [hlength]; exact hbase

theorem registeredProposalImpl_step_original {μ : Type} (key : SecretKey)
    (enabled : Message → RegisteredTargetState × μ → Bool)
    (update : (input : (OracleWorld + SigningSpec).Domain) → RegisteredTargetState × μ →
      Nat → ProposalExecutionRecord input → μ)
    (input : (OracleWorld + SigningSpec).Domain) (state : List Index × (RegisteredTargetState × μ)) :
    (fun result => (result.1, result.2.2.1)) <$> (registeredProposalImpl key enabled update input).run state =
      (liftM ((registeredTargetImpl key input).run state.2.1) : PMF _) := by
  simpa only [simulateQ_spec_query] using simulateQ_registeredProposalImpl_original key enabled update
    (liftM ((OracleWorld + SigningSpec).query input)) state

end SphincsSecurity.Concrete
