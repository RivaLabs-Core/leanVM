import SphincsSecurity.Proof.Reference.RegisteredGameBudget
import SphincsSecurity.Proof.Reference.RegisteredCertificateCoverage
import SphincsSecurity.Proof.Fts.StoppedSigningLog
import SphincsSecurity.Proof.Residual.RetainedSigningTrace

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec FtsProbeSimulation
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalGraphInputs canonicalEncodingInputs Finset.univ treeRoot

variable {α : Type}

theorem registeredTargetImpl_cache (key : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : RegisteredTargetState) :
    (fun result => (result.1, result.2.1.1)) <$> (simulateQ (registeredTargetImpl key) computation).run state =
      (simulateQ (unloggedMappedAdversaryImpl key) computation).run state.1.1 := by
  have h := congrArg (Functor.map (fun result : α × CoverLogState => (result.1, result.2.1)))
    (registeredTargetImpl_forget key computation state)
  simp only [Functor.map_map, Prod.map_fst, Prod.map_snd, id_eq] at h
  rw [h]
  exact extendState_run_proj_eq (unloggedMappedAdversaryImpl key) signingLogUpdate computation state.1.1 state.1.2

theorem registeredTargetImpl_log_step (key : SecretKey) (input : (OracleWorld + SigningSpec).Domain)
    (state : RegisteredTargetState) (result : (OracleWorld + SigningSpec).Range input × RegisteredTargetState)
    (hresult : result ∈ support ((registeredTargetImpl key input).run state)) :
    result.2.1.2 = state.1.2 ++ signingLogFragment input result.1 := by
  rw [registeredTargetImpl, QueryImpl.extendState_apply, bind_pure_comp, support_map] at hresult
  obtain ⟨step, hstep, rfl⟩ := hresult
  rw [logTracedMappedAdversaryImpl_run_map, support_map] at hstep
  obtain ⟨base, _, rfl⟩ := hstep
  rfl

theorem registeredTargetImpl_withSigningLog (key : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : RegisteredTargetState)
    (result : (α × QueryLog SigningSpec) × RegisteredTargetState)
    (hresult : result ∈ support ((simulateQ (registeredTargetImpl key)
      (withSigningLog computation state.1.2)).run state)) : result.2.1.2 = result.1.2 := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
    simp only [withSigningLog_pure, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hresult
    subst result
    rfl
  | query_bind input next ih =>
    rw [withSigningLog_query_bind, simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hresult
    obtain ⟨step, hstep, htail⟩ := hresult
    rw [← registeredTargetImpl_log_step key input state step hstep] at htail
    exact ih step.1 step.2 result htail

theorem registeredTargetImpl_retained_log (key : SecretKey) (adversary : Adversary)
    (publicKey : PublicKey) (cache : QueryCache HashSpec) (targets : Finset HashInput)
    (result : RetainedRestResult × RegisteredTargetState)
    (hresult : result ∈ support ((simulateQ (registeredTargetImpl key)
      (retainedGameRestComputation adversary publicKey)).run ((cache, []), targets))) :
    result.2.1.2 = result.1.1.2 := by
  rw [retainedGameRestComputation_eq_signingTrace, simulateQ_map, StateT.run_map, support_map] at hresult
  obtain ⟨source, hsource, rfl⟩ := hresult
  apply registeredTargetImpl_withSigningLog key (unloggedRetainedRestComputation adversary publicKey)
    ((cache, []), targets) source
  simpa only [withSigningLog, List.nil_append, Prod.mk.eta, id_map'] using hsource

def NativeCanonicalCertificate (key : SecretKey) (dummy : OtsReferenceWords) (required : Finset FtsTree)
    (result : RetainedRestResult × QueryCache HashSpec) : Prop :=
  SigningTranscript.Valid result.1.1.2 ∧
    RegisteredCanonicalCertificate key dummy required (result.1.1.1, (result.2, result.1.1.2), ∅)

theorem nativeCanonicalCertificate_le_registered (key : SecretKey) (dummy : OtsReferenceWords)
    (required : Finset FtsTree) (adversary : Adversary) (cache : QueryCache HashSpec)
    (hmessage : ∀ payload, cache (tweakableHashInput key.parameter .message payload) = none) :
    Pr[NativeCanonicalCertificate key dummy required |
      (simulateQ (unloggedMappedAdversaryImpl key) (retainedGameRestComputation adversary ⟨key.root, key.parameter⟩)).run cache] ≤
      Pr[RegisteredCertificateEvent key required |
        (simulateQ (registeredTargetImpl key) (retainedGameRestComputation adversary ⟨key.root, key.parameter⟩)).run ((cache, []), ∅)] := by
  rw [← registeredTargetImpl_cache key _ ((cache, []), ∅), probEvent_map]
  apply _root_.probEvent_mono
  intro result hresult hcanonical
  have hlog := registeredTargetImpl_retained_log key adversary _ cache ∅ result hresult
  have hinvariant := RegisteredTargetInvariant.run key _ ((cache, []), ∅)
    (RegisteredTargetInvariant.initial key cache hmessage) result hresult
  refine ⟨by simpa only [hlog, SigningTranscript.Valid] using hcanonical.1, ?_⟩
  apply RegisteredCanonicalCertificate.registered key dummy required (result.1.1.1, result.2) hinvariant
  have hcert := hcanonical.2
  change RegisteredCanonicalCertificate key dummy required
    (result.1.1.1, (result.2.1.1, result.1.1.2), ∅) at hcert
  rw [← hlog] at hcert
  exact hcert

theorem nativeCanonicalCertificate_full_le (adversary : Security.Adversary) (q : Nat)
    (hq : q ≤ 2 ^ 127) (hbound : Security.HasHashQueryBound adversary q) (dummy : OtsReferenceWords)
    (parameter : PublicParameter) (otsSecret : Seeded.OtsSecrets) (ftsSecret : Seeded.FtsSecrets)
    (root : Digest × QueryCache HashSpec)
    (hroot : root ∈ support ((simulateQ randomOracle
      (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree))).run ∅)) :
    let key : SecretKey := ⟨parameter, root.1, otsSecret, ftsSecret⟩
    let computation := retainedGameRestComputation (Seeded.memoAdversary (Security.embed adversary)) ⟨root.1, parameter⟩
    Pr[NativeCanonicalCertificate key dummy Finset.univ |
      (simulateQ (unloggedMappedAdversaryImpl key) computation).run root.2] ≤
      (2 ^ 128 : ENNReal)⁻¹ * registeredMessageQueryExpectation key computation root.2 +
      (q : ENNReal) * fullCertificateExcessRate + proposalPrefixExceptionBound +
      4 * certificateCacheExceptionRate * q := by
  dsimp only
  exact (nativeCanonicalCertificate_le_registered ⟨parameter, root.1, otsSecret, ftsSecret⟩ dummy Finset.univ
    (Seeded.memoAdversary (Security.embed adversary)) root.2
    (treeRoot_cache_message_none parameter topLayer rootTree (otsSecret topLayer rootTree) root.1 root.2 hroot)).trans
    (registeredGame_fullCertificate_le adversary q hq hbound parameter otsSecret ftsSecret root hroot)

end SphincsSecurity.Concrete
