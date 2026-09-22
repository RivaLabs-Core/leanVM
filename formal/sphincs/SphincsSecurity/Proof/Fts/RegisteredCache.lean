import SphincsSecurity.Proof.Base.CountedFailure
import SphincsSecurity.Proof.Fts.RegisteredTargetMonitor
import SphincsSecurity.Proof.Fts.CertificateCacheExceptionGrowth

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def registeredCache (state : RegisteredTargetState) : QueryCache HashSpec :=
  fun input => if input ∈ state.2 then state.1.1 input else none

theorem registeredCache_finite (state : RegisteredTargetState) : Finite (registeredCache state) := by
  apply state.2.finite_toSet.subset
  intro input hinput
  by_contra hnot
  change input ∉ state.2 at hnot
  exact hinput (by simp [registeredCache, hnot])

theorem registeredCache_eq_of_cached (targets : Finset HashInput) (before after : CoverLogState)
    (hcached : TargetsCached targets before.1) (hcache : before.1 ≤ after.1) :
    registeredCache (after, targets) = registeredCache (before, targets) := by
  funext input
  by_cases hinput : input ∈ targets
  · obtain ⟨output, houtput⟩ := hcached input hinput
    simp only [registeredCache, if_pos hinput, houtput, hcache houtput]
  · simp only [registeredCache, if_neg hinput]

theorem registeredCache_insert (state : RegisteredTargetState) (input : HashInput) (output : HashOutput) :
    registeredCache ((state.1.1.cacheQuery input output, state.1.2), insert input state.2) =
      (registeredCache state).cacheQuery input output := by
  funext other
  by_cases heq : other = input
  · subst other
    simp [registeredCache]
  · simp [registeredCache, QueryCache.cacheQuery, heq]

theorem registeredCache_none (state : RegisteredTargetState) (input : HashInput)
    (hnone : state.1.1 input = none) : registeredCache state input = none := by
  simp [registeredCache, hnone]

theorem registeredCache_step_unchanged (key : SecretKey) (input : (OracleWorld + SigningSpec).Domain)
    (state : RegisteredTargetState) (hcached : TargetsCached state.2 state.1.1)
    (hfree : ¬ Security.IsAdversaryHash input)
    (result : (OracleWorld + SigningSpec).Range input × RegisteredTargetState)
    (hresult : result ∈ support ((registeredTargetImpl key input).run state)) :
    registeredCache result.2 = registeredCache state := by
  rw [registeredTargetImpl, QueryImpl.extendState_apply, bind_pure_comp, support_map] at hresult
  obtain ⟨step, hstep, rfl⟩ := hresult
  have hcache := logTracedMappedAdversaryImpl_cache_le key input state.1 step hstep
  have htargets : registerFreshTarget input state.1 step.1 step.2 state.2 = state.2 := by
    cases input with
    | inr message => rfl
    | inl world => cases world <;> simp_all [Security.IsAdversaryHash, registerFreshTarget]
  dsimp only
  rw [htargets]
  exact registeredCache_eq_of_cached state.2 state.1 step.2 hcached hcache

theorem expected_registeredCache_weight_step_le (key : SecretKey)
    (weight : QueryCache HashSpec → ENNReal) (rate : ENNReal)
    (hfresh : ∀ cache, Finite cache → ∀ input, cache input = none →
      (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] * weight (cache.cacheQuery input output)) ≤
        weight cache + rate)
    (input : (OracleWorld + SigningSpec).Domain) (state : RegisteredTargetState)
    (hcached : TargetsCached state.2 state.1.1) :
    (∑' result, Pr[= result | (registeredTargetImpl key input).run state] * weight (registeredCache result.2)) ≤
      weight (registeredCache state) + rate * adversaryHashCost input := by
  by_cases hhash : Security.IsAdversaryHash input
  · cases input with
    | inr message => exact False.elim hhash
    | inl world =>
        cases world with
        | inl sample => exact False.elim hhash
        | inr query =>
            rw [registeredTargetImpl, QueryImpl.extendState_apply, bind_pure_comp, tsum_probOutput_map_mul,
              logTracedMappedAdversaryImpl_run_map, tsum_probOutput_map_mul]
            change (∑' result, Pr[= result | (randomOracle (spec := HashSpec) query).run state.1.1] * _) ≤ _
            cases hquery : state.1.1 query with
            | none =>
                rw [QueryImpl.withCaching_run_none _ hquery, tsum_probOutput_map_mul]
                simpa only [registerFreshTarget, hquery, if_true, signingLogFragment, List.append_nil,
                  registeredCache_insert, uniformSampleImpl, adversaryHashCost, Security.IsAdversaryHash, if_true, Nat.cast_one, mul_one] using
                    hfresh (registeredCache state) (registeredCache_finite state) query (registeredCache_none state query hquery)
            | some output =>
                rw [QueryImpl.withCaching_run_some _ hquery, tsum_probOutput_pure_mul]
                simpa only [registerFreshTarget, hquery, reduceCtorEq, if_false, signingLogFragment, List.append_nil] using
                  (le_self_add : weight (registeredCache state) ≤ weight (registeredCache state) + rate * adversaryHashCost (.inl (.inr query)))
  · have heq : (∑' result, Pr[= result | (registeredTargetImpl key input).run state] * weight (registeredCache result.2)) =
        ∑' result, Pr[= result | (registeredTargetImpl key input).run state] * weight (registeredCache state) := by
      apply tsum_congr
      intro result
      by_cases hr : result ∈ support ((registeredTargetImpl key input).run state)
      · rw [registeredCache_step_unchanged key input state hcached hhash result hr]
      · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
    rw [heq, ENNReal.tsum_mul_right]
    simpa only [adversaryHashCost, if_neg hhash, Nat.cast_zero, mul_zero, add_zero] using
      (mul_le_of_le_one_left' tsum_probOutput_le_one :
        (∑' result, Pr[= result | (registeredTargetImpl key input).run state]) * weight (registeredCache state) ≤ _)

theorem expected_registeredCache_weight_run_le {α : Type} (key : SecretKey)
    (weight : QueryCache HashSpec → ENNReal) (rate : ENNReal)
    (hfresh : ∀ cache, Finite cache → ∀ input, cache input = none →
      (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] * weight (cache.cacheQuery input output)) ≤
        weight cache + rate)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : RegisteredTargetState)
    (hinvariant : RegisteredTargetInvariant key state) (q : Nat)
    (hbound : ∀ result ∈ support ((simulateQ (registeredTargetImpl key)
      (QueryCap.counted Security.IsAdversaryHash computation)).run state), result.1.2 ≤ q) :
    (∑' result, Pr[= result | (simulateQ (registeredTargetImpl key) computation).run state] *
      weight (registeredCache result.2)) ≤ weight (registeredCache state) + rate * q :=
  QueryCap.expected_potential_le (registeredTargetImpl key) (RegisteredTargetInvariant key)
    (fun input state hinvariant result hresult => hinvariant.step key input state result hresult)
    Security.IsAdversaryHash (fun state => weight (registeredCache state)) rate
    (fun input state hinvariant => expected_registeredCache_weight_step_le key weight rate hfresh input state hinvariant.1)
    computation state hinvariant q hbound

theorem registeredCache_exception_ever_probability_le {α : Type} (key : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (cache : QueryCache HashSpec) (q : Nat)
    (hmessage : ∀ payload, cache (tweakableHashInput key.parameter .message payload) = none)
    (hbound : ∀ result ∈ support ((simulateQ (registeredTargetImpl key)
      (QueryCap.counted Security.IsAdversaryHash computation)).run ((cache, []), ∅)), result.1.2 ≤ q) :
    Pr[fun result => result.2.2 = true |
      (simulateQ (QueryCap.failureImpl (registeredTargetImpl key)
        (fun state => CertificateCacheExceptional key (registeredCache state))) computation).run
          (((cache, []), ∅), false)] ≤ certificateCacheExceptionRate * q := by
  have h := QueryCap.failure_probability_le (registeredTargetImpl key) (RegisteredTargetInvariant key)
    (fun input state hinvariant result hresult => hinvariant.step key input state result hresult)
    Security.IsAdversaryHash (fun state => certificateCacheExceptionWeight key (registeredCache state))
    certificateCacheExceptionRate
    (fun input state hinvariant => expected_registeredCache_weight_step_le key (certificateCacheExceptionWeight key)
      certificateCacheExceptionRate (expected_certificateCacheExceptionWeight_le key) input state hinvariant.1)
    (fun state => CertificateCacheExceptional key (registeredCache state))
    (fun state _ hbad => certificateCacheExceptionWeight_bad key _ (registeredCache_finite state) hbad)
    computation ((cache, []), ∅) (RegisteredTargetInvariant.initial key cache hmessage) q hbound
  have hzero : certificateCacheExceptionWeight key (registeredCache ((cache, []), ∅)) = 0 := by
    apply certificateCacheExceptionWeight_initial
    intro input _
    simp [registeredCache]
  simpa only [hzero, zero_add] using h

theorem registeredCache_exception_probability_le {α : Type} (key : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (cache : QueryCache HashSpec) (q : Nat)
    (hmessage : ∀ payload, cache (tweakableHashInput key.parameter .message payload) = none)
    (hbound : ∀ result ∈ support ((simulateQ (registeredTargetImpl key)
      (QueryCap.counted Security.IsAdversaryHash computation)).run ((cache, []), ∅)), result.1.2 ≤ q) :
    Pr[fun result => CertificateCacheExceptional key (registeredCache result.2) |
      (simulateQ (registeredTargetImpl key) computation).run ((cache, []), ∅)] ≤
        certificateCacheExceptionRate * q := by
  have hweight := expected_registeredCache_weight_run_le key (certificateCacheExceptionWeight key)
    certificateCacheExceptionRate (expected_certificateCacheExceptionWeight_le key) computation ((cache, []), ∅)
    (RegisteredTargetInvariant.initial key cache hmessage) q hbound
  have hzero : certificateCacheExceptionWeight key (registeredCache ((cache, []), ∅)) = 0 := by
    apply certificateCacheExceptionWeight_initial
    intro input _
    simp [registeredCache]
  rw [hzero, zero_add] at hweight
  refine le_trans ?_ hweight
  apply probEvent_le_tsum_probOutput_mul_cost_of_mem_support
  intro result _ hbad
  exact certificateCacheExceptionWeight_bad key _ (registeredCache_finite result.2) hbad

end SphincsSecurity.Concrete
