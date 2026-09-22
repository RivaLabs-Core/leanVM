import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Residual.RetainedResidualOriginalBudget
import SphincsSecurity.Proof.Residual.CappedSuccessTransfer
import SphincsSecurity.Proof.Residual.CappedMonitoredSource
import SphincsSecurity.Proof.Residual.RetainedResidualGameTransfer
namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
attribute [local instance] Classical.propDecidable
attribute [local irreducible] hashInputs sourceInputs canonicalEncodingInputs canonicalGraphInputs instFintypePosition
  signDigestLoop signAfterDigest sequenceFin chainWalk gameInputs
set_option backward.isDefEq.respectTransparency false

theorem observedInitialCappedSource_success (parameter : PublicParameter) (inputs : Finset HashInput)
    (hcanonical : canonicalEncodingInputs parameter ⊆ inputs)
    (encoding : ReferenceEncodingAuxiliary) (hencoding : encoding ∈ referenceEncodingAuxiliarySample.support)
    (seed : inputs → HashOutput) (dummy : OtsReferenceWords)
    (exposed : InitialPublicLabels (referenceFamilyWords encoding.selections dummy)) (high : CanonicalGraphHighHalves)
    (labels : Labels)
    (hlabels : UniformTableCompletion.complete (initialAllowed (referenceFamilyWords encoding.selections dummy) exposed) labels ≠ 0)
    (adversary : Adversary)
    (hinputs : ∀ key : SecretKey, sourceInputs key
      (signingCap (FtsProbeSimulation.unloggedRetainedRestComputation adversary ⟨key.root, key.parameter⟩)) ⊆ inputs) :
    Pr[fun result => result.1 = true |
      referenceFamilyFrontierRest ⟨parameter, 0, coordinateOtsSecrets labels, coordinateFtsSecrets labels⟩
        (programmedHash parameter (coordinateOtsSecrets labels) (coordinateFtsSecrets labels) (coordinateGraphLabels labels high)
          (finiteHashAnswer ∅ inputs (canonicalPrefixResidual parameter inputs hcanonical (coordinateGraphLabels labels high)
            encoding.selections encoding.rows seed)))
        (coordinateGraphLabels labels high) encoding.selections dummy adversary] ≤
      Pr[fun result => StoppedOr cappedVerdict (forgetState result) |
        observedRun
          (environment parameter inputs hcanonical (referenceFamilyWords encoding.selections dummy)
            (coordinateGraphLabels (initialKnown (referenceFamilyWords encoding.selections dummy) exposed) high)
            encoding.selections encoding.rows)
          labels seed
          (simulateQ (adversaryImpl inputs parameter (knownRoot (initialKnown (referenceFamilyWords encoding.selections dummy) exposed))
            (referenceFamilyWords encoding.selections dummy) encoding.selections)
            (signingCap (FtsProbeSimulation.unloggedRetainedRestComputation adversary
              ⟨knownRoot (initialKnown (referenceFamilyWords encoding.selections dummy) exposed), parameter⟩)))
          (initialState inputs (referenceFamilyWords encoding.selections dummy) exposed)] := by
  let auxiliary : ReferenceAuxiliary inputs := ⟨encoding.selections, encoding.rows, seed⟩
  have hauxiliary := referenceEncodingAuxiliary_support_seed inputs encoding hencoding seed
  let context := initialContext parameter inputs hcanonical auxiliary hauxiliary dummy exposed high labels
  have hroot : context.key.root = canonicalGraphRoot context.graph :=
    initialKnown_root (referenceFamilyWords encoding.selections dummy) exposed labels hlabels high
  have hcompatible : Compatible context (initialState inputs (referenceFamilyWords encoding.selections dummy) exposed).memory := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa only [context, auxiliary, Context.words, Context.actual, initialContext, coordinateGraphLabels_value,
        initialState, initialMemory] using initialKnown_agrees (referenceFamilyWords encoding.selections dummy) exposed labels hlabels
    · exact initialKnown_graphReplies (referenceFamilyWords encoding.selections dummy) exposed labels hlabels high
    · intro input answer hanswer; cases hanswer
    · intro input answer hanswer; cases hanswer
    · intro input answer hanswer; cases hanswer
  have h := prob_gameRest_le_capped_observed context adversary (hinputs context.key)
    (initialState inputs (referenceFamilyWords encoding.selections dummy) exposed) (initialState_rowsCovered _ _ exposed)
    hcompatible rfl
  rw [← context.frontierGame_original adversary hroot, probEvent_map] at h
  simpa only [context, auxiliary, Context.words, Context.actual, Context.oracle, Context.environment, initialContext,
    coordinateGraphLabels_value, referenceFamilyFrontierRest, Function.comp_def] using h

noncomputable def cappedSourceGame (dummy : OtsReferenceWords) (adversary : Adversary) :
    SPMF (Option (Option ((Forgery × Bool) × Nat)) × State (gameInputs adversary)) := do
  let parameter ← 𝒟[sampleParameter]
  let encoding ← 𝒟[referenceEncodingAuxiliarySample]
  let words := referenceFamilyWords encoding.selections dummy
  let high ← 𝒟[PMF.uniformOfFintype CanonicalGraphHighHalves]
  let exposed ← 𝒟[PMF.uniformOfFintype (InitialPublicLabels words)]
  lazyRun
    (environment parameter (gameInputs adversary) (canonicalEncodingInputs_subset_retainedGameInputs adversary parameter)
      words (coordinateGraphLabels (initialKnown words exposed) high) encoding.selections encoding.rows)
    (simulateQ (adversaryImpl (gameInputs adversary) parameter (knownRoot (initialKnown words exposed)) words encoding.selections)
      (signingCap (FtsProbeSimulation.unloggedRetainedRestComputation adversary ⟨knownRoot (initialKnown words exposed), parameter⟩)))
    (initialState (gameInputs adversary) words exposed)

private theorem probEvent_denotation {Result : Type} (computation : ProbComp Result) (event : Result → Prop) :
    Pr[event | 𝒟[computation]] = Pr[event | computation] := rfl

private theorem probEvent_bind_compare {A B C : Type} (law : SPMF A)
    (left : A → SPMF B) (right : A → SPMF C) (before : B → Prop) (after : C → Prop)
    (h : ∀ value, law value ≠ 0 → Pr[before | left value] ≤ Pr[after | right value]) :
    Pr[before | law >>= left] ≤ Pr[after | law >>= right] := by
  simp only [probEvent_bind_eq_tsum, SPMF.probOutput_eq_apply]
  apply ENNReal.tsum_le_tsum
  intro value
  by_cases hvalue : law value = 0
  · simp only [hvalue, zero_mul, le_refl]
  exact mul_le_mul' le_rfl (h value hvalue)

theorem forgeAdvantage_le_cappedSourceGame (dummy : OtsReferenceWords) (adversary : Adversary) :
    forgeAdvantage scheme adversary ≤
      Pr[fun result => StoppedOr cappedVerdict (forgetState result) |
        cappedSourceGame dummy adversary] := by
  rw [forgeAdvantage_eq_retainedPrefixPrior dummy adversary]
  rw [referencePrefixJointPriorGame, cappedSourceGame]
  apply probEvent_bind_compare
  intro parameter _
  apply probEvent_bind_compare
  intro encoding hencoding
  have hencoding' : encoding ∈ referenceEncodingAuxiliarySample.support := by
    apply (PMF.mem_support_iff _ _).mpr
    simpa only [PMF.evalDist_eq, SPMF.liftM_apply] using hencoding
  apply probEvent_bind_compare
  intro high _
  apply probEvent_bind_compare
  intro exposed _
  rw [← run_erasure _ _ (initialState (gameInputs adversary) (referenceFamilyWords encoding.selections dummy) exposed)
    (initialAllowed_nonempty _ exposed)]
  apply probEvent_bind_compare
  intro labels hlabels
  apply probEvent_bind_compare
  intro seed _
  simp only [bind_pure_comp, probEvent_map, Function.comp_def, probEvent_denotation]
  exact observedInitialCappedSource_success parameter (gameInputs adversary)
    (canonicalEncodingInputs_subset_retainedGameInputs adversary parameter) encoding hencoding' seed dummy exposed high labels
    hlabels adversary (sourceInputs_capped_subset_gameInputs adversary)

theorem forgeAdvantage_le_capped_source_stop_add_win (dummy : OtsReferenceWords) (adversary : Adversary) :
    forgeAdvantage scheme adversary ≤
      Pr[fun result => result.1 = none | cappedSourceGame dummy adversary] +
        Pr[fun result => ∃ value, result.1 = some value ∧ cappedVerdict value result.2.memory.log |
          cappedSourceGame dummy adversary] := by
  apply (forgeAdvantage_le_cappedSourceGame dummy adversary).trans
  apply le_trans _ (probEvent_or_le (cappedSourceGame dummy adversary) _ _)
  apply probEvent_mono
  rintro ⟨result, state⟩ _ hresult
  cases result with
  | none => exact Or.inl rfl
  | some value => exact Or.inr ⟨value, rfl, hresult⟩

end SphincsSecurity.Concrete.RetainedResidual
