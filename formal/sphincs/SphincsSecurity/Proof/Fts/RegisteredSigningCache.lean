import SphincsSecurity.Proof.Fts.RegisteredCache

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def unregisteredAdmissibleCount (key : SecretKey) (state : RegisteredTargetState) : ENNReal :=
  cacheMessageWeight key.parameter (fun input _ => if input ∈ state.2 then 0 else 1) state.1.1

theorem sign_cacheMessageWeight_le (key : SecretKey) (message : Message)
    (before after : QueryCache HashSpec) (response : Option Signature)
    (hresult : (response, after) ∈ support ((simulateQ romImpl (sign key message)).run before))
    (weight : HashInput → FewTimeView → ENNReal) (hweight : ∀ input view, weight input view ≤ 1) :
    cacheMessageWeight key.parameter weight after ≤ cacheMessageWeight key.parameter weight before + 1 := by
  rw [← simulateQ_signWithView_fst_run, support_map] at hresult
  obtain ⟨viewed, hviewed, heq⟩ := hresult
  rw [signWithView_run_eq_digestCompletion, mem_support_bind_iff] at hviewed
  obtain ⟨loop, hloop, hfinish⟩ := hviewed
  have hcache : viewed.2 = after := congrArg Prod.snd heq
  rw [← hcache, digestCompletion_cacheMessageWeight_eq key message before loop hloop viewed
    (originalDigestCompletion_preservesMessages key loop viewed hfinish)]
  apply add_le_add le_rfl
  unfold selectedLoopInputWeight
  cases loop.1 with
  | none => exact zero_le
  | some selected =>
      dsimp only
      split_ifs
      · exact hweight _ _
      · exact zero_le

theorem unregisteredAdmissibleCount_insert (key : SecretKey) (state : RegisteredTargetState)
    (input : HashInput) (output : HashOutput) (hfresh : state.1.1 input = none) :
    unregisteredAdmissibleCount key ((state.1.1.cacheQuery input output, state.1.2), insert input state.2) =
      unregisteredAdmissibleCount key state := by
  apply tsum_congr
  intro other
  by_cases heq : other = input
  · subst other
    simp [cacheMessageEntryWeight, hfresh]
  · simp [cacheMessageEntryWeight, QueryCache.cacheQuery, heq]

theorem unregisteredAdmissibleCount_step_le (key : SecretKey) (input : (OracleWorld + SigningSpec).Domain)
    (state : RegisteredTargetState) (result : (OracleWorld + SigningSpec).Range input × RegisteredTargetState)
    (hresult : result ∈ support ((registeredTargetImpl key input).run state)) :
    unregisteredAdmissibleCount key result.2 ≤ unregisteredAdmissibleCount key state + signingRequestCost input := by
  rw [registeredTargetImpl, QueryImpl.extendState_apply, bind_pure_comp, support_map] at hresult
  obtain ⟨step, hstep, rfl⟩ := hresult
  rw [logTracedMappedAdversaryImpl_run_map, support_map] at hstep
  obtain ⟨base, hbase, rfl⟩ := hstep
  cases input with
  | inr message =>
      change base ∈ support ((simulateQ romImpl (sign key message)).run state.1.1) at hbase
      simpa only [unregisteredAdmissibleCount, registerFreshTarget, signingRequestCost, Nat.cast_one] using
        sign_cacheMessageWeight_le key message state.1.1 base.2 base.1 hbase
        (fun input _ => if input ∈ state.2 then 0 else 1) (by intro input _; split_ifs <;> simp)
  | inl world =>
      cases world with
      | inl sample =>
          change base ∈ support ((fun answer => (answer, state.1.1)) <$>
            (liftM (unifSpec.query sample) : ProbComp _)) at hbase
          rw [support_map] at hbase
          obtain ⟨answer, _, rfl⟩ := hbase
          simp [unregisteredAdmissibleCount, registerFreshTarget, signingRequestCost]
      | inr query =>
          change base ∈ support ((randomOracle (spec := HashSpec) query).run state.1.1) at hbase
          cases hquery : state.1.1 query with
          | some output =>
              rw [QueryImpl.withCaching_run_some _ hquery, mem_support_pure_iff] at hbase
              subst base
              simp [unregisteredAdmissibleCount, registerFreshTarget, hquery, signingRequestCost]
          | none =>
              rw [QueryImpl.withCaching_run_none _ hquery, support_map] at hbase
              obtain ⟨output, _, rfl⟩ := hbase
              simp only [registerFreshTarget, hquery, if_true, signingLogFragment, List.append_nil,
                unregisteredAdmissibleCount_insert key state query output hquery, signingRequestCost, Nat.cast_zero, add_zero, le_refl]

theorem registeredTargetImpl_log_length (key : SecretKey) (input : (OracleWorld + SigningSpec).Domain)
    (state : RegisteredTargetState) (result : (OracleWorld + SigningSpec).Range input × RegisteredTargetState)
    (hresult : result ∈ support ((registeredTargetImpl key input).run state)) :
    result.2.1.2.length = state.1.2.length + signingRequestCost input := by
  rw [registeredTargetImpl, QueryImpl.extendState_apply, bind_pure_comp, support_map] at hresult
  obtain ⟨step, hstep, rfl⟩ := hresult
  rw [logTracedMappedAdversaryImpl_run_map, support_map] at hstep
  obtain ⟨base, _, rfl⟩ := hstep
  cases input <;> simp [signingLogFragment, signingRequestCost]

theorem registeredTargetImpl_unregistered_le_log {α : Type} (key : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : RegisteredTargetState)
    (hinitial : unregisteredAdmissibleCount key state ≤ state.1.2.length)
    (result : α × RegisteredTargetState)
    (hresult : result ∈ support ((simulateQ (registeredTargetImpl key) computation).run state)) :
    unregisteredAdmissibleCount key result.2 ≤ result.2.1.2.length := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hresult
      subst result
      exact hinitial
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hresult
      obtain ⟨step, hstep, htail⟩ := hresult
      apply ih step.1 step.2 _ result htail
      rw [registeredTargetImpl_log_length key input state step hstep, Nat.cast_add]
      exact (unregisteredAdmissibleCount_step_le key input state step hstep).trans (add_le_add hinitial le_rfl)

theorem cacheMessageWeight_registered_partition (parameter : PublicParameter)
    (state : RegisteredTargetState) (weight : HashInput → FewTimeView → ENNReal) :
    cacheMessageWeight parameter weight state.1.1 =
      cacheMessageWeight parameter weight (registeredCache state) +
        cacheMessageWeight parameter (fun input view => if input ∈ state.2 then 0 else weight input view) state.1.1 := by
  unfold cacheMessageWeight
  rw [← ENNReal.tsum_add]
  apply tsum_congr
  intro input
  by_cases hinput : input ∈ state.2 <;>
    cases hcache : state.1.1 input <;> simp [registeredCache, cacheMessageEntryWeight, hinput, hcache]

theorem cachedIndexMultiplicity_le_registered (key : SecretKey) (state : RegisteredTargetState) (index : Index) :
    cachedIndexMultiplicity key.parameter state.1.1 index ≤
      cachedIndexMultiplicity key.parameter (registeredCache state) index + unregisteredAdmissibleCount key state := by
  unfold cachedIndexMultiplicity
  rw [cacheMessageWeight_registered_partition]
  apply add_le_add le_rfl
  apply cacheMessageWeight_mono
  intro input view
  split_ifs <;> simp_all

end SphincsSecurity.Concrete
