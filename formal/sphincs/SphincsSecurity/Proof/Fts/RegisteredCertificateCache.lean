import SphincsSecurity.Proof.Fts.RegisteredCertificatePrefix

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

abbrev RegisteredCacheLedgerState := (List Index × RegisteredCertificateLedgerState) × Bool

noncomputable def registeredCacheLedgerImpl (key : SecretKey) (required : Finset FtsTree)
    (stopAfter : RegisteredCertificateStop) :
    QueryImpl (OracleWorld + SigningSpec) (StateT RegisteredCacheLedgerState PMF) :=
  QueryCap.failureImpl (registeredLedgerImpl key required stopAfter) (fun state => RegisteredCacheExceptional key state.2.1)

def registeredCacheLedgerProject (state : RegisteredCacheLedgerState) : RegisteredTargetState × Bool :=
  (state.1.2.1, state.2)

theorem registeredCacheLedgerImpl_project (key : SecretKey) (required : Finset FtsTree)
    (stopAfter : RegisteredCertificateStop) (input : (OracleWorld + SigningSpec).Domain) (state : RegisteredCacheLedgerState) :
    Prod.map id registeredCacheLedgerProject <$> (registeredCacheLedgerImpl key required stopAfter input).run state =
      (liftM ((QueryCap.failureImpl (registeredTargetImpl key) (RegisteredCacheExceptional key) input).run
        (registeredCacheLedgerProject state)) : PMF _) := by
  have h := congrArg (Functor.map (fun result => (result.1,
    (result.2, state.2 || decide (RegisteredCacheExceptional key result.2)))))
    (registeredProposalImpl_step_original key (registeredCertificateEnabled key) (registeredLedgerUpdate key required stopAfter) input state.1)
  simp only [Functor.map_map] at h
  unfold registeredCacheLedgerImpl QueryCap.failureImpl
  rw [QueryImpl.extendState_apply, bind_pure_comp, Functor.map_map, QueryImpl.extendState_apply, bind_pure_comp,
    liftM_map (m := ProbComp) (n := PMF)]
  exact h

theorem simulateQ_registeredCacheLedgerImpl_project {α : Type} (key : SecretKey) (required : Finset FtsTree)
    (stopAfter : RegisteredCertificateStop) (computation : OracleComp (OracleWorld + SigningSpec) α) (state : RegisteredCacheLedgerState) :
    Prod.map id registeredCacheLedgerProject <$>
      (simulateQ (registeredCacheLedgerImpl key required stopAfter) computation).run state =
      (liftM ((simulateQ (QueryCap.failureImpl (registeredTargetImpl key) (RegisteredCacheExceptional key)) computation).run
        (registeredCacheLedgerProject state)) : PMF _) := by
  rw [← simulateQ_liftProbCompImpl_run]
  exact map_run_simulateQ_eq_of_query_map_eq _ _ registeredCacheLedgerProject
    (registeredCacheLedgerImpl_project key required stopAfter) computation state

theorem simulateQ_registeredCacheLedgerImpl_forget {α : Type} (key : SecretKey) (required : Finset FtsTree)
    (stopAfter : RegisteredCertificateStop) (computation : OracleComp (OracleWorld + SigningSpec) α) (state : RegisteredCacheLedgerState) :
    Prod.map id Prod.fst <$> (simulateQ (registeredCacheLedgerImpl key required stopAfter) computation).run state =
      (simulateQ (registeredLedgerImpl key required stopAfter) computation).run state.1 :=
  extendState_run_proj_eq _ _ _ _ _

theorem registeredCacheLedger_probability_le {α : Type} (key : SecretKey) (required : Finset FtsTree)
    (stopAfter : RegisteredCertificateStop) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (cache : QueryCache HashSpec) (q : Nat) (hfinite : Finite cache)
    (hmessage : ∀ payload, cache (tweakableHashInput key.parameter .message payload) = none)
    (hbound : ∀ result ∈ support ((simulateQ (registeredTargetImpl key)
      (QueryCap.counted Security.IsAdversaryHash computation)).run ((cache, []), ∅)), result.1.2 ≤ q) :
    Pr[fun result => result.2.2 = true |
      (simulateQ (registeredCacheLedgerImpl key required stopAfter) computation).run
        (([], ((cache, []), ∅), initialRegisteredCertificateLedger q), false)] ≤
      4 * certificateCacheExceptionRate * q := by
  have h := registeredCacheException_ever_probability_le key computation cache q hfinite hmessage hbound
  have hproject := simulateQ_registeredCacheLedgerImpl_project key required stopAfter computation
    (([], ((cache, []), ∅), initialRegisteredCertificateLedger q), false)
  have hevent := congrArg (fun law => Pr[fun result => result.2.2 = true | law]) hproject
  rw [probEvent_map] at hevent
  exact hevent.le.trans h

end SphincsSecurity.Concrete
