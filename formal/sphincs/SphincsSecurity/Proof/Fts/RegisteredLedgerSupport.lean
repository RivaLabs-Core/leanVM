import SphincsSecurity.Proof.Fts.RegisteredCertificateCache

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def registeredCacheStop (key : SecretKey) : RegisteredCertificateStop :=
  fun input state _ record => decide (RegisteredCacheExceptional key (registeredRecordNext input state.1 record))

noncomputable def registeredSecurityLedgerImpl (key : SecretKey) (required : Finset FtsTree) :
    QueryImpl (OracleWorld + SigningSpec) (StateT RegisteredCacheLedgerState PMF) :=
  registeredCacheLedgerImpl key required (fun input state length record =>
    registeredPrefixStop input state length record || registeredCacheStop key input state length record)

theorem registeredCacheLedgerImpl_support (key : SecretKey) (required : Finset FtsTree)
    (stopAfter : RegisteredCertificateStop) (input : (OracleWorld + SigningSpec).Domain) (state : RegisteredCacheLedgerState)
    (result : (OracleWorld + SigningSpec).Range input × RegisteredCacheLedgerState)
    (hresult : result ∈ ((registeredCacheLedgerImpl key required stopAfter input).run state).support) :
    result.2.2 = (state.2 || decide (RegisteredCacheExceptional key result.2.1.2.1)) ∧
      (result.1, result.2.1) ∈ ((registeredLedgerImpl key required stopAfter input).run state.1).support := by
  rw [registeredCacheLedgerImpl, QueryCap.failureImpl, QueryImpl.extendState_apply, bind_pure_comp,
    PMF.monad_map_eq_map, PMF.mem_support_map_iff] at hresult
  obtain ⟨base, hbase, rfl⟩ := hresult
  exact ⟨rfl, hbase⟩

theorem registeredCacheLedgerImpl_base_support (key : SecretKey) (required : Finset FtsTree)
    (stopAfter : RegisteredCertificateStop) (input : (OracleWorld + SigningSpec).Domain) (state : RegisteredCacheLedgerState)
    (result : (OracleWorld + SigningSpec).Range input × RegisteredCacheLedgerState)
    (hresult : result ∈ ((registeredCacheLedgerImpl key required stopAfter input).run state).support) :
    (result.1, result.2.1.2.1) ∈ support ((registeredTargetImpl key input).run state.1.2.1) := by
  have hbase := (registeredCacheLedgerImpl_support key required stopAfter input state result hresult).2
  have h := (PMF.mem_support_map_iff (fun result => (result.1, result.2.2.1)) _ _).mpr
    ⟨(result.1, result.2.1), hbase, rfl⟩
  rw [← PMF.monad_map_eq_map, registeredLedgerImpl, registeredProposalImpl_step_original, probCompLift_support] at h
  exact h

theorem registeredCacheLedgerImpl_log_length (key : SecretKey) (required : Finset FtsTree)
    (stopAfter : RegisteredCertificateStop) (input : (OracleWorld + SigningSpec).Domain) (state : RegisteredCacheLedgerState)
    (result : (OracleWorld + SigningSpec).Range input × RegisteredCacheLedgerState)
    (hresult : result ∈ ((registeredCacheLedgerImpl key required stopAfter input).run state).support) :
    result.2.1.2.1.1.2.length = state.1.2.1.1.2.length + signingRequestCost input :=
  registeredTargetImpl_log_length key input state.1.2.1 _
    (registeredCacheLedgerImpl_base_support key required stopAfter input state result hresult)

theorem registeredCacheLedgerRun_log_mono {α : Type} (key : SecretKey) (required : Finset FtsTree)
    (stopAfter : RegisteredCertificateStop) (computation : OracleComp (OracleWorld + SigningSpec) α) (state : RegisteredCacheLedgerState)
    (result : α × RegisteredCacheLedgerState)
    (hresult : result ∈ ((simulateQ (registeredCacheLedgerImpl key required stopAfter) computation).run state).support) :
    state.1.2.1.1.2.length ≤ result.2.1.2.1.1.2.length := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, PMF.monad_pure_eq_pure, PMF.mem_support_pure_iff] at hresult
    subst result
    exact le_rfl
  | query_bind input next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff] at hresult
    obtain ⟨step, hstep, htail⟩ := hresult
    apply le_trans _ (ih step.1 step.2 result htail)
    rw [registeredCacheLedgerImpl_log_length key required stopAfter input state step hstep]
    omega

theorem registeredCacheLedgerRun_flag {α : Type} (key : SecretKey) (required : Finset FtsTree)
    (stopAfter : RegisteredCertificateStop) (computation : OracleComp (OracleWorld + SigningSpec) α) (state : RegisteredCacheLedgerState)
    (hflag : state.2 = true) (result : α × RegisteredCacheLedgerState)
    (hresult : result ∈ ((simulateQ (registeredCacheLedgerImpl key required stopAfter) computation).run state).support) :
    result.2.2 = true := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, PMF.monad_pure_eq_pure, PMF.mem_support_pure_iff] at hresult
    subst result
    exact hflag
  | query_bind input next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff] at hresult
    obtain ⟨step, hstep, htail⟩ := hresult
    apply ih step.1 step.2 _ result htail
    rw [(registeredCacheLedgerImpl_support key required stopAfter input state step hstep).1, hflag, Bool.true_or]

theorem registeredCacheLedgerImpl_stopped (key : SecretKey) (required : Finset FtsTree)
    (stopAfter : RegisteredCertificateStop) (input : (OracleWorld + SigningSpec).Domain) (state : RegisteredCacheLedgerState)
    (hstopped : state.1.2.2.stopped = true) (result : (OracleWorld + SigningSpec).Range input × RegisteredCacheLedgerState)
    (hresult : result ∈ ((registeredCacheLedgerImpl key required stopAfter input).run state).support) :
    result.2.1.2.2 = state.1.2.2 := by
  have hbase := (registeredCacheLedgerImpl_support key required stopAfter input state result hresult).2
  obtain ⟨length, record, _, hstate⟩ := registeredProposalImpl_support key (registeredCertificateEnabled key)
    (registeredLedgerUpdate key required stopAfter) input state.1 _ hbase
  have hinactive : ¬RegisteredCertificateActive key input state.1.2 := by
    intro h
    have hfalse := h.1
    rw [hstopped] at hfalse
    contradiction
  change (result.2.1.2).2 = state.1.2.2
  rw [hstate]
  simp only [registeredProposalAdvance, registeredLedgerUpdate, if_neg hinactive]
  rcases hledger : state.1.2.2 with ⟨⟨hashes, signatures, bank, stopped⟩, proposals, messages⟩
  simp_all

theorem registeredCacheLedgerRun_stopped {α : Type} (key : SecretKey) (required : Finset FtsTree)
    (stopAfter : RegisteredCertificateStop) (computation : OracleComp (OracleWorld + SigningSpec) α) (state : RegisteredCacheLedgerState)
    (hstopped : state.1.2.2.stopped = true) (result : α × RegisteredCacheLedgerState)
    (hresult : result ∈ ((simulateQ (registeredCacheLedgerImpl key required stopAfter) computation).run state).support) :
    result.2.1.2.2 = state.1.2.2 := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, PMF.monad_pure_eq_pure, PMF.mem_support_pure_iff] at hresult
    subst result
    rfl
  | query_bind input next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff] at hresult
    obtain ⟨step, hstep, htail⟩ := hresult
    have heq := registeredCacheLedgerImpl_stopped key required stopAfter input state hstopped step hstep
    exact (ih step.1 step.2 (heq ▸ hstopped) result htail).trans heq

theorem registeredCacheLedgerImpl_clean (key : SecretKey) (required : Finset FtsTree)
    (stopAfter : RegisteredCertificateStop) (input : (OracleWorld + SigningSpec).Domain) (state : RegisteredCacheLedgerState)
    (result : (OracleWorld + SigningSpec).Range input × RegisteredCacheLedgerState)
    (hresult : result ∈ ((registeredCacheLedgerImpl key required stopAfter input).run state).support)
    (hflag : result.2.2 = false) : ¬RegisteredCacheExceptional key result.2.1.2.1 := by
  have h := (registeredCacheLedgerImpl_support key required stopAfter input state result hresult).1
  rw [hflag, eq_comm, Bool.or_eq_false_iff] at h
  simpa only [decide_eq_false_iff_not] using h.2

theorem registeredSecurityLedgerImpl_hashes (key : SecretKey) (required : Finset FtsTree)
    (input : (OracleWorld + SigningSpec).Domain) (state : RegisteredCacheLedgerState)
    (hactive : RegisteredCertificateActive key input state.1.2)
    (result : (OracleWorld + SigningSpec).Range input × RegisteredCacheLedgerState)
    (hresult : result ∈ ((registeredSecurityLedgerImpl key required input).run state).support) :
    result.2.1.2.2.hashes = state.1.2.2.hashes - adversaryHashCost input := by
  have hbase := (registeredCacheLedgerImpl_support key required _ input state result hresult).2
  obtain ⟨length, record, _, hstate⟩ := registeredProposalImpl_support key (registeredCertificateEnabled key)
    (registeredLedgerUpdate key required _) input state.1 _ hbase
  change (result.2.1.2).2.hashes = _
  rw [hstate]
  simp only [registeredProposalAdvance, registeredLedgerUpdate, if_pos hactive]

theorem registeredSecurityLedgerImpl_stopped_prefix (key : SecretKey) (required : Finset FtsTree)
    (input : (OracleWorld + SigningSpec).Domain) (state : RegisteredCacheLedgerState)
    (hactive : RegisteredCertificateActive key input state.1.2)
    (hsignatures : state.1.2.2.signatures + state.1.2.1.1.2.length = signatureLimit)
    (result : (OracleWorld + SigningSpec).Range input × RegisteredCacheLedgerState)
    (hresult : result ∈ ((registeredSecurityLedgerImpl key required input).run state).support)
    (hflag : result.2.2 = false) (hstopped : result.2.1.2.2.stopped = true) :
    RegisteredLedgerPrefixExceptional result.2.1.2 := by
  have hclean := registeredCacheLedgerImpl_clean key required _ input state result hresult hflag
  have hbase := (registeredCacheLedgerImpl_support key required _ input state result hresult).2
  obtain ⟨length, record, _, hstate⟩ := registeredProposalImpl_support key (registeredCertificateEnabled key)
    (registeredLedgerUpdate key required
      (fun input state length record => registeredPrefixStop input state length record || registeredCacheStop key input state length record))
      input state.1 _ hbase
  change ¬RegisteredCacheExceptional key (result.2.1.2).1 at hclean
  rw [hstate] at hclean
  change ¬RegisteredCacheExceptional key (registeredRecordNext input state.1.2.1 record) at hclean
  have hprefix : registeredPrefixStop input state.1.2 length record = true := by
    change (result.2.1.2).2.stopped = true at hstopped
    rw [hstate] at hstopped
    simpa only [registeredProposalAdvance, registeredLedgerUpdate, if_pos hactive, registeredCacheStop,
      hclean, decide_false, Bool.or_false] using hstopped
  have hlog := registeredCacheLedgerImpl_log_length key required _ input state result hresult
  change (result.2.1.2).1.1.2.length = _ at hlog
  rw [hstate] at hlog
  have hcompleted : signatureLimit - (state.1.2.2.signatures - signingRequestCost input) =
      (registeredRecordNext input state.1.2.1 record).1.2.length := by
    have hcost := hactive.2.2.2.2
    change (registeredRecordNext input state.1.2.1 record).1.2.length = _ at hlog
    omega
  rw [hstate]
  unfold RegisteredLedgerPrefixExceptional registeredProposalAdvance registeredLedgerUpdate
  rw [if_pos hactive]
  change ProposalPrefixExceptional (state.1.2.2.proposals + length)
    (signatureLimit - (state.1.2.2.signatures - signingRequestCost input))
  rw [hcompleted]
  exact of_decide_eq_true hprefix

def RegisteredLedgerCovered (key : SecretKey) (required : Finset FtsTree)
    (state : RegisteredCertificateLedgerState) : Prop :=
  state.2.stopped = false → ∀ input ∈ state.1.2,
    TargetCertificateAt key required state.1.1 input → state.2.bank input = true

theorem registeredLedgerImpl_covered (key : SecretKey) (required : Finset FtsTree)
    (stopAfter : RegisteredCertificateStop) (input : (OracleWorld + SigningSpec).Domain)
    (state : List Index × RegisteredCertificateLedgerState)
    (result : (OracleWorld + SigningSpec).Range input × (List Index × RegisteredCertificateLedgerState))
    (hresult : result ∈ ((registeredLedgerImpl key required stopAfter input).run state).support) :
    RegisteredLedgerCovered key required result.2.2 := by
  obtain ⟨length, record, _, hstate⟩ := registeredProposalImpl_support key (registeredCertificateEnabled key)
    (registeredLedgerUpdate key required stopAfter) input state result hresult
  rw [hstate]
  unfold RegisteredLedgerCovered registeredProposalAdvance registeredLedgerUpdate
  split_ifs
  · intro _ query hquery hcertificate
    simp [completedRegisteredTargets, hquery, hcertificate]
  · simp

theorem registeredLedgerRun_covered {α : Type} (key : SecretKey) (required : Finset FtsTree)
    (stopAfter : RegisteredCertificateStop) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : List Index × RegisteredCertificateLedgerState) (hcovered : RegisteredLedgerCovered key required state.2)
    (result : α × (List Index × RegisteredCertificateLedgerState))
    (hresult : result ∈ ((simulateQ (registeredLedgerImpl key required stopAfter) computation).run state).support) :
    RegisteredLedgerCovered key required result.2.2 := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, PMF.monad_pure_eq_pure, PMF.mem_support_pure_iff] at hresult
    subst result
    exact hcovered
  | query_bind input next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff] at hresult
    obtain ⟨step, hstep, htail⟩ := hresult
    exact ih step.1 step.2 (registeredLedgerImpl_covered key required stopAfter input state step hstep) result htail

end SphincsSecurity.Concrete
