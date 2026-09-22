import SphincsSecurity.Proof.Fts.SigningMessageCount
import SphincsSecurity.Proof.Reference.DirectQueryBudget
import SphincsSecurity.Proof.Scheme.FirstBad

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false

theorem registeredCache_le (state : RegisteredTargetState) : registeredCache state ≤ state.1.1 := by
  intro input output houtput
  by_cases hinput : input ∈ state.2
  · simpa only [registeredCache, if_pos hinput] using houtput
  · simp only [registeredCache, if_neg hinput, reduceCtorEq] at houtput

theorem cachedMessageEntryCountWhere_mono (key : SecretKey) (message : Message)
    (before after : QueryCache HashSpec) (hcache : before ≤ after) (P : FewTimeView → Prop) :
    cachedMessageEntryCountWhere before key.parameter key.root message P ≤
      cachedMessageEntryCountWhere after key.parameter key.root message P := by
  apply ENat.toENNReal_mono (Set.encard_le_encard _)
  rintro entry ⟨⟨hentry, hinput⟩, hgood⟩
  exact ⟨⟨QueryCache.toSet_mono hcache hentry, hinput⟩, hgood⟩

theorem messageDeficitScore_le_registered (key : SecretKey) (state : RegisteredTargetState)
    (hfinite : Finite state.1.1) (hbound : RegisteredMessageCountBound key state) (message : Message) :
    messageDeficitScore key.parameter key.root message state.1.1 ≤
      messageDeficitScore key.parameter key.root message (registeredCache state) +
        (state.1.2.length : ℝ) * digestAttemptLimit := by
  have hraw := (ENNReal.toReal_le_toReal
    (cachedMessageEntryCount_ne_top_of_finite _ _ _ _ hfinite)
    (ENNReal.add_ne_top.mpr ⟨cachedMessageEntryCount_ne_top_of_finite _ _ _ _ (registeredCache_finite state), by finiteness⟩)).mpr
      (hbound message)
  have hadmissible := (ENNReal.toReal_le_toReal
    (cachedMessageEntryCountWhere_ne_top_of_finite _ _ _ _ (registeredCache_finite state) _)
    (cachedMessageEntryCountWhere_ne_top_of_finite _ _ _ _ hfinite _)).mpr
      (cachedMessageEntryCountWhere_mono key message _ _ (registeredCache_le state) (fun _ => True))
  rw [ENNReal.toReal_add (cachedMessageEntryCount_ne_top_of_finite _ _ _ _ (registeredCache_finite state))
    (by finiteness), ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_natCast] at hraw
  unfold messageDeficitScore
  linarith

def RegisteredCacheExceptional (key : SecretKey) (state : RegisteredTargetState) : Prop :=
  state.1.2.length ≤ signatureLimit ∧
    (MessageDeficitExceptional key state.1.1 ∨ ∃ index,
      (QueryCache.enncard (registeredCache state)).toReal / 2 ^ 36 + 2 ^ 80 <
        (cachedIndexMultiplicity key.parameter state.1.1 index).toReal)

theorem registeredCacheExceptionWeight_bad (key : SecretKey) (state : RegisteredTargetState)
    (hfinite : Finite state.1.1) (hraw : RegisteredMessageCountBound key state)
    (hadmissible : unregisteredAdmissibleCount key state ≤ state.1.2.length)
    (hbad : RegisteredCacheExceptional key state) :
    1 ≤ 4 * certificateCacheExceptionWeight key (registeredCache state) := by
  obtain ⟨hlog, hbad⟩ := hbad
  rcases hbad with hdeficit | ⟨index, hindex⟩
  · obtain ⟨message, hmessage⟩ := hdeficit
    have hscaled : (2 : ENNReal) ^ 93 ≤ 1024 * messageAdmissibleDeficit key message state.1.1 := by
      calc
        _ = 1024 * ((2 ^ 83 : Nat) : ENNReal) := by norm_num
        _ ≤ _ := mul_le_mul' le_rfl hmessage.le
    rw [← messageDeficitScore_ofReal_eq key message state.1.1 hfinite] at hscaled
    have hscore : (2 : ℝ) ^ 93 ≤ messageDeficitScore key.parameter key.root message state.1.1 := by
      rcases ENNReal.ofReal_le_ofReal_iff'.mp (show ENNReal.ofReal ((2 : ℝ) ^ 93) ≤ _ by simpa using hscaled) with h | h
      · exact h
      · norm_num at h
    have hshift := messageDeficitScore_le_registered key state hfinite hraw message
    have hlength : (state.1.2.length : ℝ) ≤ 2 ^ 24 := by exact_mod_cast hlog
    have hlower : (2 : ℝ) ^ 92 ≤ messageDeficitScore key.parameter key.root message (registeredCache state) := by
      norm_num [digestAttemptLimit] at hshift hscore ⊢
      linarith
    have hmoment : (2 : ENNReal) ^ 184 ≤ messageDeficitMoment key.parameter key.root (registeredCache state) 2 := by
      have hpower : (2 : ℝ) ^ 184 ≤ max (messageDeficitScore key.parameter key.root message (registeredCache state)) 0 ^ 2 := by
        calc
          _ = ((2 : ℝ) ^ 92) ^ 2 := by rw [← pow_mul]
          _ ≤ _ := pow_le_pow_left₀ (by positivity) (hlower.trans (le_max_left _ _)) 2
      have h := ENNReal.ofReal_le_ofReal hpower
      rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_ofNat] at h
      exact h.trans (positiveScoreMoment_le_messageDeficitMoment _ _ _ _ message)
    calc
      1 = 4 * ((2 : ENNReal) ^ 184 / 2 ^ 186) := by
        apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
        norm_num [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_pow]
      _ ≤ 4 * (messageDeficitMoment key.parameter key.root (registeredCache state) 2 / 2 ^ 186) :=
        mul_le_mul' le_rfl (ENNReal.div_le_div_right hmoment _)
      _ ≤ _ := mul_le_mul' le_rfl le_self_add
  · have hcount := (cachedIndexMultiplicity_le_registered key state index).trans (add_le_add le_rfl hadmissible)
    have hreal := (ENNReal.toReal_le_toReal (cachedIndexMultiplicity_ne_top _ _ hfinite _)
      (ENNReal.add_ne_top.mpr ⟨cachedIndexMultiplicity_ne_top _ _ (registeredCache_finite state) _, by finiteness⟩)).mpr hcount
    rw [ENNReal.toReal_add (cachedIndexMultiplicity_ne_top _ _ (registeredCache_finite state) _) (by finiteness),
      ENNReal.toReal_natCast] at hreal
    have hlength : (state.1.2.length : ℝ) ≤ 2 ^ 24 := by exact_mod_cast hlog
    have hlower : (2 : ℝ) ^ 79 ≤ cachedIndexExcessScore key.parameter (registeredCache state) index := by
      unfold cachedIndexExcessScore
      norm_num at hindex ⊢
      linarith
    have hmoment : (2 : ENNReal) ^ 158 ≤ cachedIndexExcessMoment key.parameter (registeredCache state) := by
      have hpower : (2 : ℝ) ^ 158 ≤ max (cachedIndexExcessScore key.parameter (registeredCache state) index) 0 ^ 2 := by
        calc
          _ = ((2 : ℝ) ^ 79) ^ 2 := by rw [← pow_mul]
          _ ≤ _ := pow_le_pow_left₀ (by positivity) (hlower.trans (le_max_left _ _)) 2
      have h := ENNReal.ofReal_le_ofReal hpower
      rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_ofNat] at h
      exact h.trans (Finset.single_le_sum (s := Finset.univ)
        (f := fun index => positiveScoreMoment (cachedIndexExcessScore key.parameter (registeredCache state) index) 2)
        (fun _ _ => zero_le) (Finset.mem_univ index))
    calc
      1 = 4 * ((2 : ENNReal) ^ 158 / 2 ^ 160) := by
        apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
        norm_num [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_pow]
      _ ≤ 4 * (cachedIndexExcessMoment key.parameter (registeredCache state) / 2 ^ 160) :=
        mul_le_mul' le_rfl (ENNReal.div_le_div_right hmoment _)
      _ ≤ _ := mul_le_mul' le_rfl le_add_self

def RegisteredCacheInvariant (key : SecretKey) (state : RegisteredTargetState) : Prop :=
  RegisteredTargetInvariant key state ∧ Finite state.1.1 ∧ RegisteredMessageCountBound key state ∧
    unregisteredAdmissibleCount key state ≤ state.1.2.length

theorem registeredTargetImpl_finite (key : SecretKey) (input : (OracleWorld + SigningSpec).Domain)
    (state : RegisteredTargetState) (hfinite : Finite state.1.1)
    (result : (OracleWorld + SigningSpec).Range input × RegisteredTargetState)
    (hresult : result ∈ support ((registeredTargetImpl key input).run state)) : Finite result.2.1.1 := by
  rw [registeredTargetImpl, QueryImpl.extendState_apply, bind_pure_comp, support_map] at hresult
  obtain ⟨step, hstep, rfl⟩ := hresult
  rw [logTracedMappedAdversaryImpl_run_map, support_map] at hstep
  obtain ⟨base, hbase, rfl⟩ := hstep
  rw [unloggedMappedAdversaryImpl_eq_simulateQ_expanded] at hbase
  exact finite_cache_of_mem_support _ _ _ _ hbase hfinite

theorem RegisteredCacheInvariant.step (key : SecretKey) (input : (OracleWorld + SigningSpec).Domain)
    (state : RegisteredTargetState) (hinvariant : RegisteredCacheInvariant key state)
    (result : (OracleWorld + SigningSpec).Range input × RegisteredTargetState)
    (hresult : result ∈ support ((registeredTargetImpl key input).run state)) :
    RegisteredCacheInvariant key result.2 := by
  refine ⟨hinvariant.1.step key input state result hresult,
    registeredTargetImpl_finite key input state hinvariant.2.1 result hresult,
    hinvariant.2.2.1.step key input state hinvariant.1.1 result hresult, ?_⟩
  rw [registeredTargetImpl_log_length key input state result hresult, Nat.cast_add]
  exact (unregisteredAdmissibleCount_step_le key input state result hresult).trans (add_le_add hinvariant.2.2.2 le_rfl)

theorem RegisteredCacheInvariant.initial (key : SecretKey) (cache : QueryCache HashSpec)
    (hfinite : Finite cache)
    (hmessage : ∀ payload, cache (tweakableHashInput key.parameter .message payload) = none) :
    RegisteredCacheInvariant key ((cache, []), ∅) := by
  refine ⟨RegisteredTargetInvariant.initial key cache hmessage, hfinite,
    RegisteredMessageCountBound.initial key cache hmessage, ?_⟩
  unfold unregisteredAdmissibleCount
  simp only [List.length_nil, Nat.cast_zero]
  have hnone : ∀ input, FtsProbeSimulation.MessageHashInput key.parameter input → cache input = none := by
    rintro input ⟨payload, rfl⟩
    exact hmessage payload
  rw [cacheMessageWeight_of_no_message key.parameter _ cache hnone]

theorem registeredCacheException_ever_probability_le {α : Type} (key : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (cache : QueryCache HashSpec) (q : Nat)
    (hfinite : Finite cache)
    (hmessage : ∀ payload, cache (tweakableHashInput key.parameter .message payload) = none)
    (hbound : ∀ result ∈ support ((simulateQ (registeredTargetImpl key)
      (QueryCap.counted Security.IsAdversaryHash computation)).run ((cache, []), ∅)), result.1.2 ≤ q) :
    Pr[fun result => result.2.2 = true |
      (simulateQ (QueryCap.failureImpl (registeredTargetImpl key) (RegisteredCacheExceptional key)) computation).run
        (((cache, []), ∅), false)] ≤ 4 * certificateCacheExceptionRate * q := by
  have hstep : ∀ input state, RegisteredCacheInvariant key state →
      (∑' result, Pr[= result | (registeredTargetImpl key input).run state] *
        (4 * certificateCacheExceptionWeight key (registeredCache result.2))) ≤
      4 * certificateCacheExceptionWeight key (registeredCache state) +
        (4 * certificateCacheExceptionRate) * ((if Security.IsAdversaryHash input then 1 else 0 : Nat) : ENNReal) := by
    intro input state hinvariant
    have h := mul_le_mul' (le_refl (4 : ENNReal))
      (expected_registeredCache_weight_step_le key (certificateCacheExceptionWeight key)
        certificateCacheExceptionRate (expected_certificateCacheExceptionWeight_le key) input state hinvariant.1.1)
    simp only [mul_add, ← mul_assoc, adversaryHashCost] at h
    refine le_trans ?_ h
    rw [← ENNReal.tsum_mul_left]
    apply le_of_eq (tsum_congr _)
    intro result
    exact mul_left_comm _ _ _
  have h := QueryCap.failure_probability_le (registeredTargetImpl key) (RegisteredCacheInvariant key)
    (fun input state hinvariant result hresult => hinvariant.step key input state result hresult)
    Security.IsAdversaryHash (fun state => 4 * certificateCacheExceptionWeight key (registeredCache state))
    (4 * certificateCacheExceptionRate) hstep (RegisteredCacheExceptional key)
    (fun state hinvariant hbad => registeredCacheExceptionWeight_bad key state hinvariant.2.1
      hinvariant.2.2.1 hinvariant.2.2.2 hbad)
    computation ((cache, []), ∅) (RegisteredCacheInvariant.initial key cache hfinite hmessage) q hbound
  have hzero : certificateCacheExceptionWeight key (registeredCache ((cache, []), ∅)) = 0 := by
    apply certificateCacheExceptionWeight_initial
    intro input _
    simp [registeredCache]
  simpa only [hzero, mul_zero, zero_add] using h

end SphincsSecurity.Concrete
