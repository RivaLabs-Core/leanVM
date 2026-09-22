import SphincsSecurity.Proof.Fts.RegisteredTargetSource

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def registerFreshTarget (input : (OracleWorld + SigningSpec).Domain)
    (before : CoverLogState) (_answer : (OracleWorld + SigningSpec).Range input)
    (_after : CoverLogState) (targets : Finset HashInput) : Finset HashInput :=
  match input with
  | .inl (.inr query) => if before.1 query = none then insert query targets else targets
  | _ => targets

abbrev RegisteredTargetState := CoverLogState × Finset HashInput

noncomputable def registeredTargetImpl (key : SecretKey) :
    QueryImpl (OracleWorld + SigningSpec) (StateT RegisteredTargetState ProbComp) :=
  QueryImpl.extendState (logTracedMappedAdversaryImpl key) registerFreshTarget

theorem registeredTargetImpl_forget {α : Type} (key : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : RegisteredTargetState) :
    Prod.map id Prod.fst <$> (simulateQ (registeredTargetImpl key) computation).run state =
      (simulateQ (logTracedMappedAdversaryImpl key) computation).run state.1 :=
  extendState_run_proj_eq _ _ _ _ _

theorem registerFreshTarget_card_le (input : (OracleWorld + SigningSpec).Domain)
    (before : CoverLogState) (answer : (OracleWorld + SigningSpec).Range input)
    (after : CoverLogState) (targets : Finset HashInput) :
    (registerFreshTarget input before answer after targets).card ≤
      targets.card + if Security.IsAdversaryHash input then 1 else 0 := by
  cases input with
  | inr request => simp [registerFreshTarget, Security.IsAdversaryHash]
  | inl world =>
      cases world with
      | inl sample => simp [registerFreshTarget, Security.IsAdversaryHash]
      | inr query =>
          simp only [registerFreshTarget, Security.IsAdversaryHash, if_true]
          split_ifs
          · exact Finset.card_insert_le _ _
          · omega

theorem registeredTargetImpl_card_le (key : SecretKey) (input : (OracleWorld + SigningSpec).Domain)
    (state : RegisteredTargetState) (result : (OracleWorld + SigningSpec).Range input × RegisteredTargetState)
    (hresult : result ∈ support ((registeredTargetImpl key input).run state)) :
    result.2.2.card ≤ state.2.card + if Security.IsAdversaryHash input then 1 else 0 := by
  rw [registeredTargetImpl, QueryImpl.extendState_apply, bind_pure_comp, support_map] at hresult
  obtain ⟨step, _, rfl⟩ := hresult
  exact registerFreshTarget_card_le input state.1 step.1 step.2 state.2

/-- The number of added targets is bounded by the hash calls. -/
theorem registeredTargetImpl_card_le_counted {α : Type} (key : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : RegisteredTargetState) (result : (α × Nat) × RegisteredTargetState)
    (hresult : result ∈ support ((simulateQ (registeredTargetImpl key)
      (QueryCap.counted Security.IsAdversaryHash computation)).run state)) :
    result.2.2.card ≤ state.2.card + result.1.2 := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [QueryCap.counted_pure, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hresult
      subst result
      exact le_rfl
  | query_bind input next ih =>
      rw [QueryCap.counted_query_bind, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        mem_support_bind_iff] at hresult
      obtain ⟨step, hstep, htail⟩ := hresult
      simp only [bind_pure_comp, simulateQ_map, StateT.run_map, support_map] at htail
      obtain ⟨tail, htail, rfl⟩ := htail
      have hstepCost := registeredTargetImpl_card_le key input state step hstep
      have htailCost := ih step.1 step.2 tail htail
      dsimp
      omega

def RegisteredTargetInvariant (key : SecretKey) (state : RegisteredTargetState) : Prop :=
  TargetsCached state.2 state.1.1 ∧
    AdmissibleSources key state.2 state.1

theorem RegisteredTargetInvariant.initial (key : SecretKey) (cache : QueryCache HashSpec)
    (hmessage : ∀ payload, cache (tweakableHashInput key.parameter .message payload) = none) :
    RegisteredTargetInvariant key ((cache, []), ∅) := by
  constructor
  · intro input hinput
    exact False.elim (Finset.notMem_empty input hinput)
  · intro payload output houtput _
    simp only [hmessage, reduceCtorEq] at houtput

theorem TargetsCached.mono {targets : Finset HashInput} {before after : QueryCache HashSpec}
    (hcached : TargetsCached targets before) (hcache : before ≤ after) : TargetsCached targets after := by
  intro input hinput
  obtain ⟨output, houtput⟩ := hcached input hinput
  exact ⟨output, hcache houtput⟩

theorem RegisteredTargetInvariant.step (key : SecretKey) (input : (OracleWorld + SigningSpec).Domain)
    (state : RegisteredTargetState) (hinvariant : RegisteredTargetInvariant key state)
    (result : (OracleWorld + SigningSpec).Range input × RegisteredTargetState)
    (hresult : result ∈ support ((registeredTargetImpl key input).run state)) :
    RegisteredTargetInvariant key result.2 := by
  rw [registeredTargetImpl, QueryImpl.extendState_apply, bind_pure_comp, support_map] at hresult
  obtain ⟨step, hstep, rfl⟩ := hresult
  rw [logTracedMappedAdversaryImpl_run_map, support_map] at hstep
  obtain ⟨base, hbase, rfl⟩ := hstep
  obtain ⟨hcached, hsources⟩ := hinvariant
  have hcache := unloggedMappedAdversaryImpl_cache_le key input state.1.1 base hbase
  unfold RegisteredTargetInvariant
  cases input with
  | inr message =>
      simp only [registerFreshTarget, signingLogFragment]
      refine ⟨hcached.mono hcache, ?_⟩
      exact AdmissibleSources.after_sign key state.2 state.1.2 message state.1.1 base.2 base.1 hsources hbase
  | inl world =>
      simp only [signingLogFragment, List.append_nil]
      cases world with
      | inl sample =>
          change base ∈ support ((fun answer => (answer, state.1.1)) <$>
            (liftM (unifSpec.query sample) : ProbComp _)) at hbase
          rw [support_map] at hbase
          obtain ⟨answer, _, rfl⟩ := hbase
          exact ⟨hcached, hsources⟩
      | inr query =>
          change base ∈ support ((randomOracle (spec := HashSpec) query).run state.1.1) at hbase
          cases hquery : state.1.1 query with
          | some answer =>
              rw [QueryImpl.withCaching_run_some _ hquery, mem_support_pure_iff] at hbase
              subst base
              simpa only [registerFreshTarget, hquery, reduceCtorEq, if_false] using And.intro hcached hsources
          | none =>
              rw [QueryImpl.withCaching_run_none _ hquery, support_map] at hbase
              obtain ⟨answer, _, rfl⟩ := hbase
              simp only [registerFreshTarget, hquery, if_true]
              constructor
              · intro input hinput
                rcases Finset.mem_insert.mp hinput with rfl | hinput
                · exact ⟨answer, by simp⟩
                · exact hcached.mono hcache input hinput
              · intro payload output houtput hadmissible
                by_cases heq : tweakableHashInput key.parameter .message payload = query
                · exact Or.inl (by simp [heq])
                · have hbefore : state.1.1 (tweakableHashInput key.parameter .message payload) = some output := by
                    simpa [QueryCache.cacheQuery, heq] using houtput
                  exact (hsources payload output hbefore hadmissible).imp
                    (fun hmem => Finset.mem_insert_of_mem hmem)
                    (fun hsource => hsource.mono key _ _ _ hcache (fun _ h => h))

theorem RegisteredTargetInvariant.run {α : Type} (key : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : RegisteredTargetState) (hinvariant : RegisteredTargetInvariant key state)
    (result : α × RegisteredTargetState)
    (hresult : result ∈ support ((simulateQ (registeredTargetImpl key) computation).run state)) :
    RegisteredTargetInvariant key result.2 := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hresult
      subst result
      exact hinvariant
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hresult
      obtain ⟨step, hstep, htail⟩ := hresult
      exact ih step.1 step.2 (hinvariant.step key input state step hstep) result htail

theorem RegisteredTargetInvariant.forgery_registered (key : SecretKey) (state : RegisteredTargetState)
    (hinvariant : RegisteredTargetInvariant key state)
    (forgery : Forgery) (output : HashOutput)
    (houtput : state.1.1 (tweakableHashInput key.parameter .message
      (messageDigestPayload key.root forgery.message forgery.signature.randomness)) = some output)
    (hadmissible : Admissible (truncateMessageDigest output))
    (hnew : ¬ProcessedMessageInput key state.1 (tweakableHashInput key.parameter .message
      (messageDigestPayload key.root forgery.message forgery.signature.randomness))) :
    tweakableHashInput key.parameter .message
      (messageDigestPayload key.root forgery.message forgery.signature.randomness) ∈ state.2 :=
  (hinvariant.2 _ output houtput hadmissible).resolve_right hnew

theorem registeredTargetImpl_signingDigestsCached {α : Type} (key : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : RegisteredTargetState)
    (hsigned : SigningDigestsCached key.parameter state.1.1 key.root state.1.2)
    (result : α × RegisteredTargetState)
    (hresult : result ∈ support ((simulateQ (registeredTargetImpl key) computation).run state)) :
    SigningDigestsCached key.parameter result.2.1.1 key.root result.2.1.2 := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hresult
      subst result
      exact hsigned
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hresult
      obtain ⟨step, hstep, htail⟩ := hresult
      have hbase := hstep
      rw [registeredTargetImpl, QueryImpl.extendState_apply, bind_pure_comp, support_map] at hbase
      obtain ⟨base, hbase, heq⟩ := hbase
      have hcached := logTracedMappedAdversaryImpl_signingDigestsCached key input state.1 hsigned base hbase
      exact ih step.1 step.2 (heq ▸ hcached) result htail

def adversaryHashCost (input : (OracleWorld + SigningSpec).Domain) : Nat :=
  if Security.IsAdversaryHash input then 1 else 0

def signingRequestCost : (OracleWorld + SigningSpec).Domain → Nat
  | .inl _ => 0
  | .inr _ => 1

noncomputable def registeredTargetCharge (key : SecretKey) (reuse : ENNReal)
    (budget signatures : Nat) (required : Finset FtsTree) (state : CoverLogState) :
    (OracleWorld + SigningSpec).Domain → ENNReal
  | .inl world => (freshWorldTargetHashCost key.parameter state.1 world : ENNReal) *
      targetCreationPrice key reuse budget signatures required state
  | .inr _ => 0

/-- Only a fresh hash query incurs a target creation charge. -/
theorem expected_registeredTargetImpl_le (key : SecretKey) (reuse : ENNReal)
    (budget signatures : Nat) (required : Finset FtsTree) (state : RegisteredTargetState)
    (bank : HashInput → Bool) (input : (OracleWorld + SigningSpec).Domain)
    (stopped : (OracleWorld + SigningSpec).Range input × RegisteredTargetState → Bool)
    (hcached : TargetsCached state.2 state.1.1)
    (hsigned : SigningDigestsCached key.parameter state.1.1 key.root state.1.2)
    (hreuse : ∀ message, input = .inr message → exactDigestReuseWeight key message state.1.1 ≤ reuse) :
    (∑' result, Pr[= result | (registeredTargetImpl key input).run state] *
      registeredTargetEnvelope result.2.2 key reuse budget signatures required result.2.1
        (completedRegisteredTargets result.2.2 key required result.2.1 bank) (stopped result)) ≤
      registeredTargetEnvelope state.2 key reuse
        (budget + adversaryHashCost input) (signatures + signingRequestCost input) required state.1 bank false +
      registeredTargetCharge key reuse budget signatures required state.1 input := by
  rw [registeredTargetImpl, QueryImpl.extendState_apply, bind_pure_comp, tsum_probOutput_map_mul]
  unfold adversaryHashCost signingRequestCost registeredTargetCharge
  cases input with
  | inr message =>
      simpa only [registerFreshTarget, Security.IsAdversaryHash, if_false, Nat.add_zero, add_zero] using
        expected_logTraced_sign_registeredTarget_le state.2 key reuse budget signatures required state.1 bank message
          (fun result => stopped (result.1, result.2, state.2)) hcached hsigned (hreuse message rfl)
  | inl world =>
      cases world with
      | inl sample =>
          simpa only [registerFreshTarget, Security.IsAdversaryHash, if_false, Nat.add_zero,
            signingExecutionHashCost] using
            expected_logTraced_world_registeredTarget_le state.2 key reuse budget signatures required state.1 bank
              (.inl sample) (fun result => stopped (result.1, result.2, state.2)) hsigned
      | inr query =>
          by_cases hfresh : state.1.1 query = none
          · simpa only [registerFreshTarget, hfresh, if_true, Security.IsAdversaryHash, Nat.add_zero] using
              expected_logTraced_register_fresh_le state.2 key reuse budget signatures required state.1 bank query
                (fun result => stopped (result.1, result.2, insert query state.2)) hfresh hsigned
          · simpa only [registerFreshTarget, if_neg hfresh, Security.IsAdversaryHash, if_true, Nat.add_zero,
              signingExecutionHashCost] using
              expected_logTraced_world_registeredTarget_le state.2 key reuse budget signatures required state.1 bank
                (.inr query) (fun result => stopped (result.1, result.2, state.2)) hsigned

end SphincsSecurity.Concrete
