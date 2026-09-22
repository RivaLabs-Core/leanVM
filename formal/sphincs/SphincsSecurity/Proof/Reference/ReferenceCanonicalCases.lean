import SphincsSecurity.Proof.Reference.ReferenceCertificateCoverage
import SphincsSecurity.Proof.Reference.RegisteredCertificateCoverage

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec OtsContactTrace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 100000
attribute [local instance] Classical.propDecidable
attribute [local irreducible] frontierRoot maskOtsPrefixes boundaryEval canonicalGraphInputs canonicalEncodingInputs
  canonicalGraphGameInputs canonicalGraphLabels Finset.univ instFintypePosition chainWalk sequenceFin honestNode

noncomputable def ReferenceForgerySample.canonical {inputs : Finset HashInput} (dummy : OtsReferenceWords)
    (sample : ReferenceForgerySample inputs) : Prop :=
  let f := finiteHashAnswer ∅ inputs sample.2.1.2
  let key := ReferenceVerifierWitness.rootedKey sample.1 f
  let forgery := sample.2.2.1.1.1
  let digest := truncateMessageDigest (f (RetainedResidual.signingInput key forgery.message forgery.signature))
  let result := (sample.context dummy).2.2.2
  ¬SigningTranscript.Contains sample.2.2.1.1.2 forgery ∧
    FullyHonestOpening f (recordedCache f (result.before * result.after)) key
      (digestIndex digest) (digestLeaves digest) forgery.signature ∧
    ∀ lay, OtsVerifierWitness.ReferenceLayerOpening f key (canonicalReferenceWords key f dummy)
      (referenceTableSelection key f) (digestIndex digest) forgery.signature lay

theorem referenceForgeryRest_success_witness (key : SecretKey) (f : QueryImpl HashSpec Id)
    (selections : ReferenceFamily) (dummy : OtsReferenceWords) (adversary : Adversary) (before : AdversaryTrace)
    (hselected : selections = referenceTableSelection key f)
    (hvalid : ∀ lay tree leaf, OtsCode.Valid (referenceFamilyWords selections dummy lay tree leaf))
    (hb : before ∈ support (referenceForgeryRest key f (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret f)
      selections dummy adversary))
    (hsuccess : (completedReferenceContact key.parameter f (referenceFamilyWords selections dummy)
      (canonicalGraphFrontier key.otsSecret (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret f)
        (referenceFamilyWords selections dummy)) before).output.1 = true) :
    ReferenceVerifierWitness.SuccessWitnessFor key f (ReferenceVerifierWitness.rootedKey key f).root
      (referenceFamilyWords selections dummy) selections adversary
      (completedReferenceContact key.parameter f (referenceFamilyWords selections dummy)
        (canonicalGraphFrontier key.otsSecret (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret f)
          (referenceFamilyWords selections dummy)) before) before := by
  dsimp only [referenceForgeryRest] at hb
  rw [ReferenceVerifierWitness.source_root] at hb
  simp only [completedReferenceContact, ReferenceVerifierWitness.source_root, boundaryEval_fst,
    Bool.and_eq_true, decide_eq_true_eq] at hsuccess
  apply ReferenceVerifierWitness.run_success_atRoot key f _ rfl selections dummy adversary _ before
    hselected hvalid hb hsuccess.1.1 hsuccess.1.2 hsuccess.2 rfl
  dsimp only [completedReferenceContact]
  rw [ReferenceVerifierWitness.source_root]

namespace ReferenceVerifierWitness

def CanonicalWitnessFor (key : SecretKey) (f : QueryImpl HashSpec Id) (root : Digest)
    (words : OtsReferenceWords) (selections : ReferenceFamily) (result : ContactResult) (before : AdversaryTrace) : Prop :=
  let actualKey : SecretKey := { key with root := root }
  let forgery := before.1.1.1
  let digest := truncateMessageDigest (f (RetainedResidual.signingInput actualKey forgery.message forgery.signature))
  ¬SigningTranscript.Contains before.1.1.2 forgery ∧
    FullyHonestOpening f (recordedCache f (result.before * result.after)) actualKey
      (digestIndex digest) (digestLeaves digest) forgery.signature ∧
    ∀ lay, OtsVerifierWitness.ReferenceLayerOpening f actualKey words selections
      (digestIndex digest) forgery.signature lay

theorem SuccessWitnessFor.canonical_classification {key : SecretKey} {f : QueryImpl HashSpec Id} {root : Digest}
    {words : OtsReferenceWords} {selections : ReferenceFamily} {adversary : Adversary}
    {result : ContactResult} {before : AdversaryTrace}
    (h : SuccessWitnessFor key f root words selections adversary result before) :
    (CanonicalWitnessFor key f root words selections result before ∧ SigningTranscript.Valid before.1.1.2 ∧
      ReferenceFtsCoverage.Outcome { key with root := root } f before.1.1.2 before.1.2
        (result.before * result.after) before.1.1.1) ∨
      ReferencePrimitiveWitness.Outcome { key with root := root } f words
        (canonicalGraphMessage (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret f)) selections result := by
  obtain ⟨_, hvalid, hnew, horigin, hfrontier, _, digest, hdigest, hrun, hadmissible, hcases⟩ := h
  have hd : digest = truncateMessageDigest (f (RetainedResidual.signingInput { key with root := root }
      before.1.1.1.message before.1.1.1.signature)) := hdigest.symm
  rcases hcases with ⟨hfull, hreference, hqueries, hpayload⟩ | hlayer | hfts
  · rw [hd] at hfull hreference hqueries hadmissible
    exact Or.inl ⟨⟨hnew, hfull, hreference⟩, hvalid,
      ReferenceFtsCoverage.classification { key with root := root } f _ _ _ _ horigin hpayload hrun hadmissible hqueries⟩
  · right
    apply ReferencePrimitiveWitness.layer_exception { key with root := root } f words _ _ result ?_ hlayer
    intro lay tree leaf chain
    rw [hfrontier, canonicalGraphLabels_frontier key.parameter key.otsSecret key.ftsSecret f _ root]
    rfl
  · exact Or.inr (Or.inr (Or.inl (ReferencePrimitiveWitness.fts_exception { key with root := root } f _ _ _ hfts)))

end ReferenceVerifierWitness

theorem referenceForgeryGame_canonical_cases (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs)
    (hgraph : ∀ parameter, canonicalGraphInputs parameter ⊆ inputs)
    (dummy : OtsReferenceWords) (hdummy : ∀ lay tree leaf, OtsCode.Valid (dummy lay tree leaf))
    (adversary : Adversary) (sample : ReferenceForgerySample inputs)
    (hsample : sample ∈ support (referenceForgeryGame inputs hencoding dummy adversary))
    (hsuccess : (sample.context dummy).2.2.2.output.1 = true) :
    (sample.canonical dummy ∧ sample.ftsOutcome dummy) ∨ GraphPrimitiveEvent dummy (sample.context dummy) := by
  obtain ⟨href, hb⟩ := referenceForgeryGame_support inputs hencoding dummy adversary sample hsample
  have hselected := referenceFamilyOracleSample_selections sample.1 inputs (hencoding sample.1.parameter)
    (hgraph sample.1.parameter) sample.2.1 href
  have h := (referenceForgeryRest_success_witness sample.1 (finiteHashAnswer ∅ inputs sample.2.1.2)
    sample.2.1.1 dummy adversary sample.2.2 hselected
    (referenceFamilyOracleSample_words_valid sample.1 inputs (hencoding sample.1.parameter)
      (hgraph sample.1.parameter) sample.2.1 href dummy hdummy) hb hsuccess).canonical_classification
  rcases h with ⟨hcanonical, hvalid, hfts⟩ | hprimitive
  · left
    refine ⟨?_, hvalid, hfts⟩
    have hw : referenceFamilyWords sample.2.1.1 dummy =
        canonicalReferenceWords (ReferenceVerifierWitness.rootedKey sample.1 (finiteHashAnswer ∅ inputs sample.2.1.2))
          (finiteHashAnswer ∅ inputs sample.2.1.2) dummy := by
      rw [hselected, referenceFamilyWords_selected]
      exact (ReferenceVerifierWitness.canonicalReferenceWords_root sample.1 _ _ dummy).symm
    obtain ⟨hnew, hfull, hreference⟩ := hcanonical
    refine ⟨hnew, hfull, ?_⟩
    rw [hw, hselected, ← ReferenceVerifierWitness.referenceTableSelection_root sample.1
      (finiteHashAnswer ∅ inputs sample.2.1.2)
      (ReferenceVerifierWitness.rootedKey sample.1 (finiteHashAnswer ∅ inputs sample.2.1.2)).root] at hreference
    exact hreference
  · right
    exact graphPrimitiveEvent_of_outcome_atRoot sample.1 _ _ sample.2.1.1 dummy _ hprimitive

theorem forgeAdvantage_le_canonical_cases (dummy : OtsReferenceWords)
    (hdummy : ∀ lay tree leaf, OtsCode.Valid (dummy lay tree leaf)) (adversary : Adversary) :
    forgeAdvantage scheme adversary ≤
      Pr[fun sample => sample.canonical dummy ∧ sample.fullCertificate dummy |
        referenceForgeryGame (canonicalGraphGameInputs adversary) (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] +
      Pr[fun sample => sample.canonical dummy ∧ sample.remainingFts dummy |
        referenceForgeryGame (canonicalGraphGameInputs adversary) (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] +
      Pr[GraphPrimitiveEvent dummy | referenceGraphContextGame contactObserver (canonicalGraphGameInputs adversary)
        (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] := by
  rw [forgeAdvantage_eq_referenceForgery dummy adversary, ← referenceForgeryGame_primitive]
  apply le_trans (_root_.probEvent_mono (q := fun sample =>
    ((sample.canonical dummy ∧ sample.fullCertificate dummy) ∨ (sample.canonical dummy ∧ sample.remainingFts dummy)) ∨
      GraphPrimitiveEvent dummy (sample.context dummy)) ?_)
  · exact (probEvent_or_le _ _ _).trans (add_le_add (probEvent_or_le _ _ _) le_rfl)
  · intro sample hsample hsuccess
    rcases referenceForgeryGame_canonical_cases _ _ (canonicalGraphInputs_subset_gameInputs adversary)
        dummy hdummy adversary sample hsample hsuccess with ⟨hcanonical, hfts⟩ | hprimitive
    · exact Or.inl ((sample.ftsOutcome_cases dummy hfts).imp (And.intro hcanonical) (And.intro hcanonical))
    · exact Or.inr hprimitive

end SphincsSecurity.Concrete
