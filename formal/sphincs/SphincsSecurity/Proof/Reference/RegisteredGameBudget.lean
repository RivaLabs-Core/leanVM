import SphincsSecurity.Proof.Deterministic.InterfaceReference
import SphincsSecurity.Proof.Fts.RegisteredCertificateRates

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

variable {α β : Type}

theorem registeredTargetImpl_run'_eq (key : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : RegisteredTargetState) :
    (simulateQ (registeredTargetImpl key) computation).run' state =
      (simulateQ romImpl (simulateQ (Security.expandSigning (sign key)) computation)).run' state.1.1 := by
  have htarget := congrArg (Functor.map Prod.fst) (registeredTargetImpl_forget key computation state)
  have hlog := congrArg (Functor.map Prod.fst)
    (extendState_run_proj_eq (unloggedMappedAdversaryImpl key) signingLogUpdate computation state.1.1 state.1.2)
  simp only [Functor.map_map, Prod.map_fst, id_eq] at htarget hlog
  change Prod.fst <$> (simulateQ (logTracedMappedAdversaryImpl key) computation).run state.1 =
    Prod.fst <$> (simulateQ (unloggedMappedAdversaryImpl key) computation).run state.1.1 at hlog
  have hexpand : unloggedMappedAdversaryImpl key = romImpl ∘ₛ Security.expandSigning (sign key) := by
    funext input
    cases input with
    | inl world => exact (simulateQ_spec_query (impl := romImpl) world).symm
    | inr message => rfl
  rw [StateT.run'_eq, htarget, hlog, hexpand, QueryImpl.simulateQ_compose]
  rfl

theorem registered_counted_budget_of_map (key : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (project : α → β)
    (cache : QueryCache HashSpec) (q : Nat)
    (hbound : ∀ result ∈ support ((simulateQ romImpl
      (simulateQ (Security.expandSigning (sign key))
        (QueryCap.counted Security.IsAdversaryHash (project <$> computation)))).run' cache), result.2 ≤ q) :
    ∀ result ∈ support ((simulateQ (registeredTargetImpl key)
      (QueryCap.counted Security.IsAdversaryHash computation)).run ((cache, []), ∅)), result.1.2 ≤ q := by
  intro result hresult
  apply hbound (project result.1.1, result.1.2)
  rw [QueryCap.counted_map, simulateQ_map, simulateQ_map, StateT.run'_map', support_map]
  refine ⟨result.1, ?_, rfl⟩
  rw [← registeredTargetImpl_run'_eq key _ ((cache, []), ∅), StateT.run'_eq, support_map]
  exact ⟨result, hresult, rfl⟩

theorem registeredGame_counted_budget (adversary : Security.Adversary) (q : Nat)
    (hsmall : q < 2 ^ 256) (hbound : Security.HasHashQueryBound adversary q)
    (parameter : PublicParameter) (otsSecret : Seeded.OtsSecrets) (ftsSecret : Seeded.FtsSecrets)
    (root : Digest × QueryCache HashSpec)
    (hroot : root ∈ support ((simulateQ randomOracle
      (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree))).run ∅)) :
    ∀ result ∈ support ((simulateQ (registeredTargetImpl ⟨parameter, root.1, otsSecret, ftsSecret⟩)
      (QueryCap.counted Security.IsAdversaryHash
        (FtsProbeSimulation.retainedGameRestComputation
          (Seeded.memoAdversary (Security.embed adversary)) ⟨root.1, parameter⟩))).run ((root.2, []), ∅)),
      result.1.2 ≤ q := by
  let verdict := fun result : FtsProbeSimulation.RetainedRestResult =>
    decide (SigningTranscript.Valid result.1.2 ∧ ¬SigningTranscript.Contains result.1.2 result.1.1) && result.2
  apply registered_counted_budget_of_map _ _ verdict root.2 q
  rw [show verdict <$> FtsProbeSimulation.retainedGameRestComputation
      (Seeded.memoAdversary (Security.embed adversary)) ⟨root.1, parameter⟩ =
      Seeded.sourceGame ⟨root.1, parameter⟩ (Seeded.memoAdversary (Security.embed adversary)) by
    rw [Seeded.sourceGame_eq_traced]
    exact FtsProbeSimulation.retainedGameRestComputation_verdict_projection _ _]
  intro result hresult
  apply Seeded.randomizedInterface_counted_budget adversary q hsmall hbound parameter otsSecret ftsSecret result
  rw [Seeded.randomizedInterfaceAfterSecrets, Seeded.run'_lift_hash_bind, mem_support_bind_iff]
  exact ⟨root, hroot, hresult⟩

theorem registeredGame_fullCertificate_le (adversary : Security.Adversary) (q : Nat)
    (hq : q ≤ 2 ^ 127) (hbound : Security.HasHashQueryBound adversary q)
    (parameter : PublicParameter) (otsSecret : Seeded.OtsSecrets) (ftsSecret : Seeded.FtsSecrets)
    (root : Digest × QueryCache HashSpec)
    (hroot : root ∈ support ((simulateQ randomOracle
      (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree))).run ∅)) :
    let key : SecretKey := ⟨parameter, root.1, otsSecret, ftsSecret⟩
    let computation := FtsProbeSimulation.retainedGameRestComputation
      (Seeded.memoAdversary (Security.embed adversary)) ⟨root.1, parameter⟩
    Pr[RegisteredCertificateEvent key Finset.univ |
      (simulateQ (registeredTargetImpl key) computation).run ((root.2, []), ∅)] ≤
      (2 ^ 128 : ENNReal)⁻¹ * registeredMessageQueryExpectation key computation root.2 +
      (q : ENNReal) * fullCertificateExcessRate + proposalPrefixExceptionBound +
      4 * certificateCacheExceptionRate * q := by
  have hfinite : Finite root.2 := finite_cache_of_mem_support
    (liftM (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree))) ∅ root.1 root.2
    (by rwa [simulateQ_romImpl_liftM]) finite_empty
  exact registeredFullCertificate_probability_le _ _ _ q (hq.trans (Nat.le_add_right _ _)) hfinite
    (treeRoot_cache_message_none parameter topLayer rootTree (otsSecret topLayer rootTree) root.1 root.2 hroot)
    (registeredGame_counted_budget adversary q (hq.trans_lt (by norm_num)) hbound parameter otsSecret ftsSecret root hroot)

end SphincsSecurity.Concrete
