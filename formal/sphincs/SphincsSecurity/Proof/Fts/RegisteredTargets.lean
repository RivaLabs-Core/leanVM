import SphincsSecurity.Proof.Fts.BankedTargetEnvelope

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

/-- Every registered target has a cached answer. -/
def TargetsCached (targets : Finset HashInput) (cache : QueryCache HashSpec) : Prop :=
  ∀ input ∈ targets, ∃ output, cache input = some output

noncomputable def registeredTargetForecast (targets : Finset HashInput) (key : SecretKey)
    (reuse : ENNReal) (budget signatures : Nat) (required : Finset FtsTree)
    (state : CoverLogState) (input : HashInput) (target : FewTimeView) : ENNReal :=
  if input ∈ targets then targetCertificateForecast key reuse budget signatures required state input target else 0

noncomputable def registeredTargetEnvelope (targets : Finset HashInput) (key : SecretKey)
    (reuse : ENNReal) (budget signatures : Nat) (required : Finset FtsTree)
    (state : CoverLogState) (bank : HashInput → Bool) (stopped : Bool) : ENNReal :=
  bankedCacheWeight key.parameter
    (registeredTargetForecast targets key reuse budget signatures required state) bank stopped state.1

noncomputable def completedRegisteredTargets (targets : Finset HashInput) (key : SecretKey)
    (required : Finset FtsTree) (state : CoverLogState) (bank : HashInput → Bool) : HashInput → Bool :=
  fun input => bank input || decide (input ∈ targets ∧ TargetCertificateAt key required state input)

theorem registeredTargetForecast_le (targets : Finset HashInput) (key : SecretKey)
    (reuse : ENNReal) (budget signatures : Nat) (required : Finset FtsTree)
    (state : CoverLogState) (input : HashInput) (target : FewTimeView) :
    registeredTargetForecast targets key reuse budget signatures required state input target ≤
      targetCertificateForecast key reuse budget signatures required state input target := by
  unfold registeredTargetForecast
  split_ifs <;> first | exact le_rfl | exact zero_le

theorem registeredTargetEnvelope_empty (key : SecretKey) (reuse : ENNReal) (budget signatures : Nat)
    (required : Finset FtsTree) (state : CoverLogState) :
    registeredTargetEnvelope ∅ key reuse budget signatures required state (fun _ => false) false = 0 := by
  apply ENNReal.tsum_eq_zero.mpr
  intro input
  simp only [Bool.false_eq_true, if_false]
  unfold cacheMessageEntryWeight
  cases state.1 input <;> simp [registeredTargetForecast]

theorem registeredTargetForecast_entry (targets : Finset HashInput) (key : SecretKey)
    (reuse : ENNReal) (budget signatures : Nat) (required : Finset FtsTree)
    (state : CoverLogState) (input : HashInput) (hinput : input ∈ targets) :
    cacheMessageEntryWeight key.parameter
      (registeredTargetForecast targets key reuse budget signatures required state) state.1 input =
      cacheMessageEntryWeight key.parameter
        (targetCertificateForecast key reuse budget signatures required state) state.1 input := by
  unfold cacheMessageEntryWeight
  cases state.1 input <;> simp [registeredTargetForecast, hinput]

theorem one_le_registeredTargetEntry_of_certificate (targets : Finset HashInput) (key : SecretKey)
    (reuse : ENNReal) (budget signatures : Nat) (required : Finset FtsTree)
    (state : CoverLogState) (input : HashInput) (hinput : input ∈ targets)
    (hcertificate : TargetCertificateAt key required state input) :
    1 ≤ cacheMessageEntryWeight key.parameter
      (registeredTargetForecast targets key reuse budget signatures required state) state.1 input := by
  rw [registeredTargetForecast_entry targets key reuse budget signatures required state input hinput]
  exact one_le_targetCertificateEntry_of_certificate key reuse budget signatures required state input hcertificate

theorem registeredTargetForecast_no_new (targets : Finset HashInput) (key : SecretKey)
    (reuse : ENNReal) (budget signatures : Nat) (required : Finset FtsTree)
    (before : QueryCache HashSpec) (after : CoverLogState) (hcached : TargetsCached targets before) :
    cacheMessageWeight key.parameter (fun input target => if before input = none then
      registeredTargetForecast targets key reuse budget signatures required after input target else 0) after.1 = 0 := by
  apply ENNReal.tsum_eq_zero.mpr
  intro input
  unfold cacheMessageEntryWeight
  cases after.1 input with
  | none => rfl
  | some output =>
      by_cases hinput : input ∈ targets
      · obtain ⟨previous, hprevious⟩ := hcached input hinput
        simp [hprevious]
      · simp [registeredTargetForecast, hinput]

theorem registeredTargetEnvelope_insert_fresh (targets : Finset HashInput) (key : SecretKey)
    (reuse : ENNReal) (budget signatures : Nat) (required : Finset FtsTree)
    (state : CoverLogState) (bank : HashInput → Bool) (stopped : Bool)
    (input : HashInput) (hfresh : state.1 input = none) :
    registeredTargetEnvelope (insert input targets) key reuse budget signatures required state bank stopped =
      registeredTargetEnvelope targets key reuse budget signatures required state bank stopped := by
  apply tsum_congr
  intro other
  by_cases heq : other = input
  · subst other
    simp [cacheMessageEntryWeight, hfresh]
  · simp [cacheMessageEntryWeight, registeredTargetForecast, heq]

/-- A signing request spends one signing allowance and no adversary hash allowance. -/
theorem expected_logTraced_sign_registeredTarget_le (targets : Finset HashInput) (key : SecretKey)
    (reuse : ENNReal) (budget signatures : Nat) (required : Finset FtsTree)
    (state : CoverLogState) (bank : HashInput → Bool) (message : Message)
    (stopped : (OracleWorld + SigningSpec).Range (.inr message) × CoverLogState → Bool)
    (hcached : TargetsCached targets state.1)
    (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hreuse : exactDigestReuseWeight key message state.1 ≤ reuse) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inr message)).run state] *
      registeredTargetEnvelope targets key reuse budget signatures required result.2
        (completedRegisteredTargets targets key required result.2 bank) (stopped result)) ≤
      registeredTargetEnvelope targets key reuse budget (signatures + 1) required state bank false := by
  rw [← add_zero (registeredTargetEnvelope targets key reuse budget (signatures + 1) required state bank false)]
  apply expected_bankedCacheWeight_step_le
  · intro result hr
    exact logTracedMappedAdversaryImpl_cache_le key (.inr message) state result hr
  · intro result _ input hcompleted
    obtain ⟨hinput, hcertificate⟩ := of_decide_eq_true hcompleted
    exact one_le_registeredTargetEntry_of_certificate targets key reuse budget signatures required
      result.2 input hinput hcertificate
  · intro input target
    by_cases hinput : input ∈ targets
    · simp only [registeredTargetForecast, if_pos hinput, targetCertificateForecast,
        ← mul_assoc, ENNReal.tsum_mul_right]
      exact mul_le_mul' (expected_logTraced_sign_reuseTarget_le key reuse budget (payloadOf input) target
        signatures state hsigned message hreuse ∅ required ⟨by simp, by simp, by simp⟩) le_rfl
    · simp only [registeredTargetForecast, if_neg hinput, mul_zero, tsum_zero, le_refl]
  · simp only [registeredTargetForecast_no_new targets key reuse budget signatures required state.1 _ hcached,
      mul_zero, tsum_zero, le_refl]

theorem expected_logTraced_world_registeredTarget_le (targets : Finset HashInput) (key : SecretKey)
    (reuse : ENNReal) (budget signatures : Nat) (required : Finset FtsTree)
    (state : CoverLogState) (bank : HashInput → Bool) (input : OracleWorld.Domain)
    (stopped : (OracleWorld + SigningSpec).Range (.inl input) × CoverLogState → Bool)
    (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inl input)).run state] *
      registeredTargetEnvelope targets key reuse budget signatures required result.2
        (completedRegisteredTargets targets key required result.2 bank) (stopped result)) ≤
      registeredTargetEnvelope targets key reuse (budget + signingExecutionHashCost (.inl input)) signatures
        required state bank false +
      (freshWorldTargetHashCost key.parameter state.1 input : ENNReal) *
        targetCreationPrice key reuse budget signatures required state := by
  apply expected_bankedCacheWeight_step_le
  · intro result hr
    exact logTracedMappedAdversaryImpl_cache_le key (.inl input) state result hr
  · intro result _ query hcompleted
    obtain ⟨hquery, hcertificate⟩ := of_decide_eq_true hcompleted
    exact one_le_registeredTargetEntry_of_certificate targets key reuse budget signatures required
      result.2 query hquery hcertificate
  · intro query target
    by_cases hquery : query ∈ targets
    · simp only [registeredTargetForecast, if_pos hquery, targetCertificateForecast,
        ← mul_assoc, ENNReal.tsum_mul_right]
      exact mul_le_mul' (expected_logTraced_world_reuseTarget_le key reuse budget (payloadOf query) target
        signatures state input hsigned ∅ required ⟨by simp, by simp, by simp⟩) le_rfl
    · simp only [registeredTargetForecast, if_neg hquery, mul_zero, tsum_zero, le_refl]
  · calc
      _ ≤ ∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inl input)).run state] *
          cacheMessageWeight key.parameter (fun query target => if state.1 query = none then
            targetCertificateForecast key reuse budget signatures required result.2 query target else 0) result.2.1 := by
        apply ENNReal.tsum_le_tsum
        intro result
        apply mul_le_mul' le_rfl
        apply cacheMessageWeight_mono
        intro query target
        split_ifs
        · exact registeredTargetForecast_le targets key reuse budget signatures required result.2 query target
        · exact le_rfl
      _ ≤ _ := by
        have h := expected_logTraced_world_reuseNewTarget_le key reuse budget signatures state input hsigned
          ∅ required ⟨by simp, by simp, by simp⟩
        simpa only [newTargetCertificateForecast_eq, ← mul_assoc, ENNReal.tsum_mul_right, targetCreationPrice] using
          mul_le_mul' h (le_refl (targetCertificateScale required))

/-- Register a fresh adversarial query before seeing its answer. -/
theorem expected_logTraced_register_fresh_le (targets : Finset HashInput) (key : SecretKey)
    (reuse : ENNReal) (budget signatures : Nat) (required : Finset FtsTree)
    (state : CoverLogState) (bank : HashInput → Bool) (input : HashInput)
    (stopped : (OracleWorld + SigningSpec).Range (.inl (.inr input)) × CoverLogState → Bool)
    (hfresh : state.1 input = none)
    (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inl (.inr input))).run state] *
      registeredTargetEnvelope (insert input targets) key reuse budget signatures required result.2
        (completedRegisteredTargets (insert input targets) key required result.2 bank) (stopped result)) ≤
      registeredTargetEnvelope targets key reuse (budget + 1) signatures required state bank false +
      (freshWorldTargetHashCost key.parameter state.1 (.inr input) : ENNReal) *
        targetCreationPrice key reuse budget signatures required state := by
  have h := expected_logTraced_world_registeredTarget_le (insert input targets) key reuse budget signatures required
    state bank (.inr input) stopped hsigned
  simpa only [signingExecutionHashCost, registeredTargetEnvelope_insert_fresh _ _ _ _ _ _ _ _ _ input hfresh] using h

end SphincsSecurity.Concrete
