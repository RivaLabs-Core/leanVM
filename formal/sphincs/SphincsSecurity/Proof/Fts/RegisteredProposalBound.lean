import SphincsSecurity.Proof.Fts.RegisteredCacheException
import SphincsSecurity.Proof.Fts.MessageReuseFromCount
import SphincsSecurity.Proof.Fts.SigningProposalRecord

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem registeredCache_enncard_le (state : RegisteredTargetState) :
    QueryCache.enncard (registeredCache state) ≤ state.2.card := by
  rw [← (registeredCache_finite state).cachedInputs_ncard_toENNReal_eq_enncard]
  apply Nat.cast_le.mpr
  calc
    _ ≤ (state.2 : Set HashInput).ncard := by
      apply Set.ncard_le_ncard ?_ state.2.finite_toSet
      intro input hinput
      by_contra hnot
      change input ∉ state.2 at hnot
      exact hinput (by simp [registeredCache, hnot])
    _ = _ := Set.ncard_coe_finset state.2

theorem registered_message_count_lt (key : SecretKey) (state : RegisteredTargetState) (spent : Nat)
    (hraw : RegisteredMessageCountBound key state) (hspent : spent ≤ (2 ^ 127 + 2 ^ 64))
    (hcard : state.2.card ≤ spent) (hlog : state.1.2.length ≤ signatureLimit) (message : Message) :
    cachedMessageEntryCount state.1.1 key.parameter key.root message + digestAttemptLimit <
      ((2 ^ randomnessBits : Nat) : ENNReal) := by
  have hregistered := (cachedMessageEntryCount_le_enncard (registeredCache state) key.parameter key.root message).trans
    ((registeredCache_enncard_le state).trans (Nat.cast_le.mpr hcard))
  calc
    _ ≤ ((spent : ENNReal) + (signatureLimit : ENNReal) * digestAttemptLimit) + digestAttemptLimit :=
      add_le_add ((hraw message).trans (add_le_add hregistered (mul_le_mul' (Nat.cast_le.mpr hlog) le_rfl))) le_rfl
    _ ≤ (((((2 ^ 127 + 2 ^ 64) : Nat) : ENNReal)) + (signatureLimit : ENNReal) * digestAttemptLimit) + digestAttemptLimit :=
      add_le_add (add_le_add (Nat.cast_le.mpr hspent) le_rfl) le_rfl
    _ < _ := by norm_num [signatureLimit, digestAttemptLimit, randomnessBits]

theorem registeredCache_no_deficit (key : SecretKey) (state : RegisteredTargetState)
    (hlog : state.1.2.length ≤ signatureLimit) (hclean : ¬RegisteredCacheExceptional key state) :
    ¬MessageDeficitExceptional key state.1.1 := fun h => hclean ⟨hlog, Or.inl h⟩

theorem registeredCache_index_le (key : SecretKey) (state : RegisteredTargetState) (spent : Nat)
    (hfinite : Finite state.1.1) (hcard : state.2.card ≤ spent)
    (hlog : state.1.2.length ≤ signatureLimit) (hclean : ¬RegisteredCacheExceptional key state) (index : Index) :
    cachedIndexMultiplicity key.parameter state.1.1 index ≤
      (spent : ENNReal) * ((2 ^ 36 : Nat) : ENNReal)⁻¹ + ((2 ^ 80 : Nat) : ENNReal) := by
  have hindex : (cachedIndexMultiplicity key.parameter state.1.1 index).toReal ≤
      (QueryCache.enncard (registeredCache state)).toReal / 2 ^ 36 + 2 ^ 80 := by
    by_contra h
    exact hclean ⟨hlog, Or.inr ⟨index, lt_of_not_ge h⟩⟩
  have hsize : (QueryCache.enncard (registeredCache state)).toReal ≤ (spent : ℝ) := by
    exact_mod_cast ENNReal.toReal_mono (by finiteness)
      ((registeredCache_enncard_le state).trans (Nat.cast_le.mpr hcard))
  apply (ENNReal.toReal_le_toReal (cachedIndexMultiplicity_ne_top _ _ hfinite _) (by finiteness)).mp
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  norm_num [ENNReal.toReal_mul, ENNReal.toReal_inv] at hindex ⊢
  have hscaled := div_le_div_of_nonneg_right hsize (by positivity : (0 : ℝ) ≤ 2 ^ 36)
  norm_num at hscaled
  linarith

theorem registeredCache_reuse_le (key : SecretKey) (state : RegisteredTargetState) (spent : Nat)
    (hraw : RegisteredMessageCountBound key state) (hspent : spent ≤ (2 ^ 127 + 2 ^ 64))
    (hcard : state.2.card ≤ spent) (hlog : state.1.2.length ≤ signatureLimit)
    (hclean : ¬RegisteredCacheExceptional key state) (message : Message) :
    exactDigestReuseWeight key message state.1.1 ≤ nearUniformDigestReuseWeight := by
  apply exactDigestReuseWeight_le_near_uniform_of_deficit_of_count key message state.1.1
    (registered_message_count_lt key state spent hraw hspent hcard hlog message)
  by_contra h
  exact registeredCache_no_deficit key state hlog hclean ⟨message, lt_of_not_ge h⟩

theorem registeredCache_completedSigningRecord_cap {ω : Type} [Monoid ω]
    (trace : (input : OracleWorld.Domain) → OracleWorld.Range input → ω)
    (key : SecretKey) (state : RegisteredTargetState) (spent : Nat)
    (hinvariant : RegisteredCacheInvariant key state) (hspent : spent ≤ (2 ^ 127 + 2 ^ 64))
    (hcard : state.2.card ≤ spent) (hlog : state.1.2.length ≤ signatureLimit)
    (hclean : ¬RegisteredCacheExceptional key state) (message : Message) (index : Index) :
    targetProposalAcceptance * ((completedSigningRecord trace key message state.1.1).map Prod.snd) index ≤
      PMF.uniformOfFintype Index index := by
  apply targetProposalAcceptance_cap (completedSigningRecord trace key message state.1.1) Prod.snd _ index
  intro selected
  rw [completedSigningRecord_index, ← PMF.probOutput_eq_apply]
  change Pr[= selected | tracedSigningRun trace key message state.1.1 >>= fun result => completeSelectedIndex result.1.1.2] ≤ _
  rw [probOutput_tracedSigningIndex_eq_loop]
  apply (probOutput_completeSelectedLoopIndex_le key message state.1.1 selected).trans
  apply (add_le_add le_rfl (mul_le_mul'
    (registeredCache_reuse_le key state spent hinvariant.2.2.1 hspent hcard hlog hclean message) le_rfl)).trans
  simpa only [Nat.add_zero, Nat.cast_zero, zero_mul, add_zero] using
    targetProposalRate_of_cache_bound (cachedIndexMultiplicity key.parameter state.1.1 selected)
      spent 0 0 0 hspent (Nat.zero_le _) (Nat.zero_le _)
      (registeredCache_index_le key state spent hinvariant.2.1 hcard hlog hclean selected)

end SphincsSecurity.Concrete
