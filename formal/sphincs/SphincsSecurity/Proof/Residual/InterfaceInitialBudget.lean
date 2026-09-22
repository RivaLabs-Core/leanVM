import SphincsSecurity.Proof.Residual.InterfaceFixedBudget
import SphincsSecurity.Proof.Residual.InterfacePrimitivePotential

namespace SphincsSecurity.Concrete.RetainedResidual
open OracleComp OracleSpec ENNReal CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
open FtsProbeSimulation (unloggedRetainedRestComputation liftOracleWorldLeft)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] hashInputs sourceInputs canonicalEncodingInputs canonicalGraphInputs instFintypePosition
  gameInputs initialAllowed initialKnown referenceFamilyWords
  simulateQ adversaryImpl unloggedRetainedRestComputation environment lazyRun
set_option backward.isDefEq.respectTransparency false

theorem observedInitialSource_interfaceHashes_le (parameter : PublicParameter) (_hparameter : parameter ∈ support sampleParameter)
    (inputs : Finset HashInput) (hcanonical : canonicalEncodingInputs parameter ⊆ inputs)
    (encoding : ReferenceEncodingAuxiliary) (hencoding : encoding ∈ referenceEncodingAuxiliarySample.support)
    (seed : inputs → HashOutput)
    (dummy : OtsReferenceWords) (exposed : InitialPublicLabels (referenceFamilyWords encoding.selections dummy))
    (high : CanonicalGraphHighHalves) (labels : Labels)
    (hlabels : UniformTableCompletion.complete (initialAllowed (referenceFamilyWords encoding.selections dummy) exposed) labels ≠ 0)
    (original : Security.Adversary)
    (hinputs : ∀ key : SecretKey, sourceInputs key (unloggedRetainedRestComputation (Seeded.memoAdversary (Security.embed original)) ⟨key.root, key.parameter⟩) ⊆ inputs)
    (q : Nat) (hsmall : q < 2 ^ 256) (hq : Security.HasHashQueryBound original q) (result : Option (Forgery × Bool) × State inputs)
    (hresult : observedRun
      (environment parameter inputs hcanonical (referenceFamilyWords encoding.selections dummy)
        (coordinateGraphLabels (initialKnown (referenceFamilyWords encoding.selections dummy) exposed) high) encoding.selections encoding.rows)
      labels seed
      (simulateQ (adversaryImpl inputs parameter (knownRoot (initialKnown (referenceFamilyWords encoding.selections dummy) exposed))
        (referenceFamilyWords encoding.selections dummy) encoding.selections)
        (unloggedRetainedRestComputation (Seeded.memoAdversary (Security.embed original)) ⟨knownRoot (initialKnown (referenceFamilyWords encoding.selections dummy) exposed), parameter⟩))
      (initialState inputs (referenceFamilyWords encoding.selections dummy) exposed) result ≠ 0) :
    result.2.memory.interfaceHashes ≤ q := by
  let auxiliary : ReferenceAuxiliary inputs := ⟨encoding.selections, encoding.rows, seed⟩
  have hauxiliary := referenceEncodingAuxiliary_support_seed inputs encoding hencoding seed
  let context := initialContext parameter inputs hcanonical auxiliary hauxiliary dummy exposed high labels
  have hroot : context.key.root = canonicalGraphRoot context.graph :=
    initialKnown_root (referenceFamilyWords encoding.selections dummy) exposed labels hlabels high
  have hsource := context.interface_bound hroot original q hsmall hq
  have hcompatible : Compatible context (initialState inputs (referenceFamilyWords encoding.selections dummy) exposed).memory := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa only [context, auxiliary, Context.words, Context.actual, initialContext, coordinateGraphLabels_value, initialState, initialMemory] using
        initialKnown_agrees (referenceFamilyWords encoding.selections dummy) exposed labels hlabels
    · exact initialKnown_graphReplies (referenceFamilyWords encoding.selections dummy) exposed labels hlabels high
    · intro input answer hanswer; cases hanswer
    · intro input answer hanswer; cases hanswer
    · intro input answer hanswer; cases hanswer
  have hrun : observedRun context.environment context.actual context.auxiliary.seed
      (simulateQ (adversaryImpl inputs context.key.parameter context.key.root context.words context.auxiliary.selections)
        (unloggedRetainedRestComputation (Seeded.memoAdversary (Security.embed original)) ⟨context.key.root, context.key.parameter⟩))
      (initialState inputs (referenceFamilyWords encoding.selections dummy) exposed) result ≠ 0 := by
    simpa only [context, auxiliary, Context.environment, Context.actual, Context.words, initialContext, coordinateGraphLabels_value] using hresult
  have h := observedRun_source_interfaceHashes_le context (unloggedRetainedRestComputation (Seeded.memoAdversary (Security.embed original)) ⟨context.key.root, context.key.parameter⟩)
    (hinputs context.key) q hsource
    (initialState inputs (referenceFamilyWords encoding.selections dummy) exposed) (initialState_rowsCovered _ _ exposed)
    hcompatible result hrun
  simpa only [initialState, initialMemory, Memory.interfaceHashes, Memory.honestHashes,
    List.map_nil, List.sum_nil, Nat.add_zero, Nat.sub_self, Nat.zero_add] using h

private theorem lazyRun_observed_support {Result : Type} (inputs : Finset HashInput)
    (runEnvironment : AdaptiveResidualLabels.Environment (ControlSpec inputs) CanonicalCoordinate inputs Memory)
    (computation : OracleComp (World inputs) Result) (state : State inputs)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty) (result : Option Result × State inputs)
    (hresult : lazyRun runEnvironment computation state result ≠ 0) :
    ∃ labels seed, UniformTableCompletion.complete state.candidates labels ≠ 0 ∧
      observedRun runEnvironment labels seed computation state result ≠ 0 := by
  rw [← run_erasure _ _ state ha, RetainedObservation.bind_nonzero] at hresult
  obtain ⟨labels, hlabels, hresult⟩ := hresult
  rw [RetainedObservation.bind_nonzero] at hresult
  obtain ⟨seed, _, hresult⟩ := hresult
  exact ⟨labels, seed, hlabels, hresult⟩

private theorem initialState_completion_interface (inputs : Finset HashInput) (words : OtsReferenceWords)
    (exposed : InitialPublicLabels words) :
    UniformTableCompletion.complete (initialState inputs words exposed).candidates =
      UniformTableCompletion.complete (initialAllowed words exposed) := rfl

theorem lazyInitialSource_interfaceHashes_le (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (inputs : Finset HashInput) (hcanonical : canonicalEncodingInputs parameter ⊆ inputs) (original : Security.Adversary)
    (hinputs : ∀ key : SecretKey, sourceInputs key (unloggedRetainedRestComputation (Seeded.memoAdversary (Security.embed original)) ⟨key.root, key.parameter⟩) ⊆ inputs)
    (encoding : ReferenceEncodingAuxiliary)
    (hencoding : encoding ∈ referenceEncodingAuxiliarySample.support) (dummy : OtsReferenceWords)
    (exposed : InitialPublicLabels (referenceFamilyWords encoding.selections dummy)) (high : CanonicalGraphHighHalves)
    (q : Nat) (hsmall : q < 2 ^ 256) (hq : Security.HasHashQueryBound original q)
    (result : Option (Forgery × Bool) × State inputs)
    (hresult : lazyRun
      (environment parameter inputs hcanonical
        (referenceFamilyWords encoding.selections dummy) (coordinateGraphLabels (initialKnown (referenceFamilyWords encoding.selections dummy) exposed) high)
        encoding.selections encoding.rows)
      (simulateQ (adversaryImpl inputs parameter (knownRoot (initialKnown (referenceFamilyWords encoding.selections dummy) exposed))
        (referenceFamilyWords encoding.selections dummy) encoding.selections)
        (unloggedRetainedRestComputation (Seeded.memoAdversary (Security.embed original)) ⟨knownRoot (initialKnown (referenceFamilyWords encoding.selections dummy) exposed), parameter⟩))
      (initialState inputs (referenceFamilyWords encoding.selections dummy) exposed) result ≠ 0) :
    result.2.memory.interfaceHashes ≤ q := by
  obtain ⟨labels, seed, hlabels, hresult⟩ := lazyRun_observed_support inputs _ _ _
    (initialAllowed_nonempty _ exposed) result hresult
  rw [initialState_completion_interface] at hlabels
  exact observedInitialSource_interfaceHashes_le parameter hparameter inputs
    hcanonical encoding hencoding seed dummy exposed high labels hlabels original hinputs q hsmall hq result hresult


end SphincsSecurity.Concrete.RetainedResidual
