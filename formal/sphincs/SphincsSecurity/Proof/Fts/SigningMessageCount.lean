import SphincsSecurity.Proof.Fts.RegisteredSigningCache
import SphincsSecurity.Proof.Fts.MessageCacheCountGrowth

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem cachedMessageEntryCount_messageAnswers_congr (key : SecretKey) (message : Message)
    (before after : QueryCache HashSpec)
    (hanswers : FtsProbeSimulation.messageAnswers key.parameter before =
      FtsProbeSimulation.messageAnswers key.parameter after) :
    cachedMessageEntryCount before key.parameter key.root message =
      cachedMessageEntryCount after key.parameter key.root message := by
  have hset : cachedMessageInputSet before key.parameter key.root message =
      cachedMessageInputSet after key.parameter key.root message := by
    ext entry
    constructor <;> rintro ⟨hentry, randomness, hinput⟩
    · refine ⟨?_, randomness, hinput⟩
      change after entry.1 = some entry.2
      change before entry.1 = some entry.2 at hentry
      rw [hinput] at hentry ⊢
      exact (congrFun hanswers _).symm.trans hentry
    · refine ⟨?_, randomness, hinput⟩
      change before entry.1 = some entry.2
      change after entry.1 = some entry.2 at hentry
      rw [hinput] at hentry ⊢
      exact (congrFun hanswers _).trans hentry
  exact congrArg (fun entries => ((entries.encard : ENat) : ENNReal)) hset

theorem signDigestLoop_cachedMessageEntryCount_le (attempts : Nat) (key : SecretKey)
    (signed tracked : Message) (before : QueryCache HashSpec) (result : DigestLoopRecord)
    (hresult : result ∈ support ((simulateQ romImpl (signDigestLoop attempts key signed)).run before)) :
    cachedMessageEntryCount result.2 key.parameter key.root tracked ≤
      cachedMessageEntryCount before key.parameter key.root tracked + attempts := by
  induction attempts generalizing before result with
  | zero =>
      simp only [signDigestLoop, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hresult
      subst result
      simp
  | succ attempts ih =>
      rw [signDigestLoop_run_succ_eq, mem_support_bind_iff] at hresult
      obtain ⟨randomness, _, hresult⟩ := hresult
      rw [mem_support_bind_iff] at hresult
      obtain ⟨step, hstep, htail⟩ := hresult
      rw [simulateQ_signAttempt_run_eq, mem_support_bind_iff] at hstep
      obtain ⟨query, hquery, hpure⟩ := hstep
      rw [mem_support_pure_iff] at hpure
      subst step
      have hgrowth := randomOracle_cachedMessageEntryCount_le key.parameter key.root tracked _ before query hquery
      unfold signDigestLoopContinuation at htail
      split at htail
      · rw [mem_support_pure_iff] at htail
        subst result
        exact hgrowth.trans (add_le_add le_rfl (by exact_mod_cast Nat.succ_pos attempts))
      · have h := (ih query.2 result htail).trans (add_le_add hgrowth le_rfl)
        simpa only [Nat.cast_add, Nat.cast_one, add_assoc, add_comm (1 : ENNReal)] using h

theorem sign_cachedMessageEntryCount_le (key : SecretKey) (signed tracked : Message)
    (before after : QueryCache HashSpec) (response : Option Signature)
    (hresult : (response, after) ∈ support ((simulateQ romImpl (sign key signed)).run before)) :
    cachedMessageEntryCount after key.parameter key.root tracked ≤
      cachedMessageEntryCount before key.parameter key.root tracked + digestAttemptLimit := by
  rw [← simulateQ_signWithView_fst_run, support_map] at hresult
  obtain ⟨viewed, hviewed, heq⟩ := hresult
  rw [signWithView_run_eq_digestCompletion, mem_support_bind_iff] at hviewed
  obtain ⟨loop, hloop, hfinish⟩ := hviewed
  have hcache : viewed.2 = after := congrArg Prod.snd heq
  rw [← hcache, cachedMessageEntryCount_messageAnswers_congr key tracked viewed.2 loop.2
    (originalDigestCompletion_preservesMessages key loop viewed hfinish).2]
  exact signDigestLoop_cachedMessageEntryCount_le digestAttemptLimit key signed tracked before loop hloop

def RegisteredMessageCountBound (key : SecretKey) (state : RegisteredTargetState) : Prop :=
  ∀ message, cachedMessageEntryCount state.1.1 key.parameter key.root message ≤
    cachedMessageEntryCount (registeredCache state) key.parameter key.root message +
      state.1.2.length * digestAttemptLimit

theorem RegisteredMessageCountBound.step (key : SecretKey) (input : (OracleWorld + SigningSpec).Domain)
    (state : RegisteredTargetState) (hcached : TargetsCached state.2 state.1.1)
    (hbound : RegisteredMessageCountBound key state)
    (result : (OracleWorld + SigningSpec).Range input × RegisteredTargetState)
    (hresult : result ∈ support ((registeredTargetImpl key input).run state)) :
    RegisteredMessageCountBound key result.2 := by
  have hlength := registeredTargetImpl_log_length key input state result hresult
  intro message
  by_cases hhash : Security.IsAdversaryHash input
  · rw [registeredTargetImpl, QueryImpl.extendState_apply, bind_pure_comp, support_map] at hresult
    obtain ⟨step, hstep, rfl⟩ := hresult
    rw [logTracedMappedAdversaryImpl_run_map, support_map] at hstep
    obtain ⟨base, hbase, rfl⟩ := hstep
    cases input with
    | inr signed => exact False.elim hhash
    | inl world =>
      cases world with
      | inl sample => exact False.elim hhash
      | inr query =>
        change base ∈ support ((randomOracle (spec := HashSpec) query).run state.1.1) at hbase
        cases hquery : state.1.1 query with
        | some output =>
          rw [QueryImpl.withCaching_run_some _ hquery, mem_support_pure_iff] at hbase
          subst base
          simpa only [registerFreshTarget, hquery, reduceCtorEq, if_false, signingLogFragment, List.append_nil] using hbound message
        | none =>
          rw [QueryImpl.withCaching_run_none _ hquery, support_map] at hbase
          obtain ⟨output, _, rfl⟩ := hbase
          simp only [registerFreshTarget, hquery, if_true, signingLogFragment, List.append_nil,
            registeredCache_insert, cachedMessageEntryCount_cacheQuery _ _ _ _ _ _ hquery,
            cachedMessageEntryCount_cacheQuery _ _ _ _ _ _ (registeredCache_none state query hquery)]
          exact (add_le_add (hbound message) le_rfl).trans_eq (by ac_rfl)
  · have hcache := registeredCache_step_unchanged key input state hcached hhash result hresult
    rw [hcache, hlength]
    rw [registeredTargetImpl, QueryImpl.extendState_apply, bind_pure_comp, support_map] at hresult
    obtain ⟨step, hstep, rfl⟩ := hresult
    rw [logTracedMappedAdversaryImpl_run_map, support_map] at hstep
    obtain ⟨base, hbase, rfl⟩ := hstep
    cases input with
    | inr signed =>
      have hgrowth := sign_cachedMessageEntryCount_le key signed message state.1.1 base.2 base.1 hbase
      exact (hgrowth.trans (add_le_add (hbound message) le_rfl)).trans_eq (by
        simp only [signingRequestCost, Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_assoc])
    | inl world =>
      cases world with
      | inl sample =>
        change base ∈ support ((fun answer => (answer, state.1.1)) <$>
          (liftM (unifSpec.query sample) : ProbComp _)) at hbase
        rw [support_map] at hbase
        obtain ⟨answer, _, rfl⟩ := hbase
        simpa only [signingRequestCost, Nat.add_zero] using hbound message
      | inr query => exact False.elim (hhash trivial)

theorem RegisteredMessageCountBound.initial (key : SecretKey) (cache : QueryCache HashSpec)
    (hmessage : ∀ payload, cache (tweakableHashInput key.parameter .message payload) = none) :
    RegisteredMessageCountBound key ((cache, []), ∅) := by
  intro message
  rw [cachedMessageEntryCount_zero_of_no_inputs key.parameter key.root cache hmessage message]
  exact zero_le

theorem registeredTargetImpl_messageCountBound {α : Type} (key : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : RegisteredTargetState)
    (hinvariant : RegisteredTargetInvariant key state) (hbound : RegisteredMessageCountBound key state)
    (result : α × RegisteredTargetState)
    (hresult : result ∈ support ((simulateQ (registeredTargetImpl key) computation).run state)) :
    RegisteredMessageCountBound key result.2 := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hresult
    subst result
    exact hbound
  | query_bind input next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hresult
    obtain ⟨step, hstep, htail⟩ := hresult
    exact ih step.1 step.2 (hinvariant.step key input state step hstep)
      (hbound.step key input state hinvariant.1 step hstep) result htail

end SphincsSecurity.Concrete
