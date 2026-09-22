import SphincsSecurity.Proof.Fts.RegisteredLedgerSupport

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem registeredSecurityLedgerRun_stop_cases {α : Type} (key : SecretKey) (required : Finset FtsTree)
    (q total : Nat) (hq : q ≤ (2 ^ 127 + 2 ^ 64)) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : RegisteredCacheLedgerState) (hlive : state.1.2.2.stopped = false)
    (hpassive : RegisteredCacheInvariant key state.1.2.1)
    (hsigned : SigningDigestsCached key.parameter state.1.2.1.1.1 key.root state.1.2.1.1.2)
    (hclean : ¬RegisteredCacheExceptional key state.1.2.1)
    (hinvariant : RegisteredCertificateInvariant key q total state.1)
    (result : (α × Nat) × RegisteredCacheLedgerState)
    (hresult : result ∈ ((simulateQ (registeredSecurityLedgerImpl key required)
      (QueryCap.counted Security.IsAdversaryHash computation)).run state).support)
    (hbudget : result.1.2 ≤ state.1.2.2.hashes) (hvalid : result.2.1.2.1.1.2.length ≤ signatureLimit) :
    result.2.1.2.2.stopped = false ∨ RegisteredLedgerPrefixExceptional result.2.1.2 ∨ result.2.2 = true := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
    simp only [QueryCap.counted_pure, simulateQ_pure, StateT.run_pure, PMF.monad_pure_eq_pure,
      PMF.mem_support_pure_iff] at hresult
    subst result
    exact Or.inl hlive
  | query_bind input next ih =>
    rw [QueryCap.counted_query_bind, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
      PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff] at hresult
    obtain ⟨step, hstep, htail⟩ := hresult
    simp only [bind_pure_comp, simulateQ_map, StateT.run_map, PMF.monad_map_eq_map, PMF.mem_support_map_iff] at htail
    obtain ⟨tail, htail, rfl⟩ := htail
    dsimp only at hbudget hvalid ⊢
    have hbefore := hinvariant hlive
    have hlog := registeredCacheLedgerImpl_log_length key required _ input state step hstep
    have hlogFinal := registeredCacheLedgerRun_log_mono key required _
      (QueryCap.counted Security.IsAdversaryHash (next step.1)) step.2 tail htail
    have hhash : adversaryHashCost input ≤ state.1.2.2.hashes := by
      change (if Security.IsAdversaryHash input then 1 else 0) ≤ _
      omega
    have hsignatures : signingRequestCost input ≤ state.1.2.2.signatures := by
      have hbalance := hbefore.signatures_eq
      omega
    have hcard : state.1.2.1.2.card ≤ (2 ^ 127 + 2 ^ 64) := (Nat.le_add_right _ _).trans (hbefore.queries_le.trans hq)
    have hlogBefore : state.1.2.1.1.2.length ≤ signatureLimit := by
      have hbalance := hbefore.signatures_eq
      omega
    have hactive : RegisteredCertificateActive key input state.1.2 :=
      ⟨hlive, ⟨hpassive, hcard, hlogBefore, hclean⟩, hsigned, hhash, hsignatures⟩
    by_cases hflag : step.2.2 = true
    · exact Or.inr (Or.inr (registeredCacheLedgerRun_flag key required _
        (QueryCap.counted Security.IsAdversaryHash (next step.1)) step.2 hflag tail htail))
    · have hflagFalse : step.2.2 = false := Bool.eq_false_of_not_eq_true hflag
      by_cases hstopped : step.2.1.2.2.stopped = false
      · have hbase := registeredCacheLedgerImpl_base_support key required _ input state step hstep
        have hledger := (registeredCacheLedgerImpl_support key required _ input state step hstep).2
        have hsigned' := registeredTargetImpl_signingDigestsCached key (liftM ((OracleWorld + SigningSpec).query input))
          state.1.2.1 hsigned (step.1, step.2.1.2.1) (by simpa only [simulateQ_spec_query] using hbase)
        have hhashes := registeredSecurityLedgerImpl_hashes key required input state hactive step hstep
        apply ih step.1 step.2 hstopped (hpassive.step key input state.1.2.1 _ hbase) hsigned'
          (registeredCacheLedgerImpl_clean key required _ input state step hstep hflagFalse)
          (registeredLedgerImpl_invariant key q total required (registeredCacheStop key) input state.1 hinvariant _ hledger)
          tail htail _ hvalid
        rw [hhashes]
        change tail.1.2 ≤ state.1.2.2.hashes - (if Security.IsAdversaryHash input then 1 else 0)
        omega
      · have hstoppedTrue : step.2.1.2.2.stopped = true := Bool.eq_true_of_not_eq_false hstopped
        have hprefix := registeredSecurityLedgerImpl_stopped_prefix key required input state hactive
          hbefore.signatures_eq step hstep hflagFalse hstoppedTrue
        have hfinal := registeredCacheLedgerRun_stopped key required _
          (QueryCap.counted Security.IsAdversaryHash (next step.1)) step.2 hstoppedTrue tail htail
        apply Or.inr (Or.inl _)
        change ProposalPrefixExceptional tail.2.1.2.2.proposals (signatureLimit - tail.2.1.2.2.signatures)
        rw [hfinal]
        exact hprefix

end SphincsSecurity.Concrete
