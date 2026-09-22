import SphincsSecurity.Proof.Reference.InterfaceCertificateBound
import SphincsSecurity.Proof.Reference.ReferenceCanonicalCases
import SphincsSecurity.Proof.Reference.FiniteHashCache

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec OtsContactTrace OracleComp.DeferredSampling
open FtsProbeSimulation (RetainedRestResult retainedGameRestComputation)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 100000
attribute [local instance] Classical.propDecidable
attribute [local irreducible] scheme frontierRoot canonicalGraphLabels canonicalGraphInputs canonicalEncodingInputs
  canonicalGraphGameInputs hashInputs treeRoot honestNode

theorem referenceForgeryGame_oracleCertificateRecord (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs)
    (hgraph : ∀ parameter, canonicalGraphInputs parameter ⊆ inputs)
    (dummy : OtsReferenceWords) (adversary : Adversary) :
    (fun sample : ReferenceForgerySample inputs =>
      (finiteHashAnswer ∅ inputs sample.2.1.2, sample.certificateRecord)) <$> referenceForgeryGame inputs hencoding dummy adversary =
      𝒟[do
        let table ← sampleHashTable inputs
        (fun record => (finiteHashAnswer ∅ inputs table, record)) <$>
          fixedCertificateTraceGame (finiteHashAnswer ∅ inputs table) adversary] := by
  rw [referenceForgeryGame]
  simp only [map_bind, map_pure, fixedCertificateTraceGame]
  rw [evalDist_bind_comm, evalDist_bind]
  apply congrArg (𝒟[sampleParameter] >>= ·)
  funext parameter
  rw [evalDist_bind_comm, evalDist_bind]
  apply congrArg (𝒟[sampleOtsSecrets] >>= ·)
  funext otsSecret
  rw [evalDist_bind_comm, evalDist_bind]
  apply congrArg (𝒟[sampleFtsSecrets] >>= ·)
  funext ftsSecret
  simp only [ReferenceForgerySample.certificateRecord, bind_pure_comp, ← evalDist_map]
  trans 𝒟[do
    let table ← sampleHashTable inputs
    (fun record => (finiteHashAnswer ∅ inputs table, record)) <$>
      referenceCertificateRest ⟨parameter, 0, otsSecret, ftsSecret⟩ (finiteHashAnswer ∅ inputs table)
        (referenceTableSelection ⟨parameter, 0, otsSecret, ftsSecret⟩ (finiteHashAnswer ∅ inputs table)) dummy adversary]
  · simpa only [referenceCertificateRest, Functor.map_map] using
      referenceFamilyOracleSample_bind_selected ⟨parameter, 0, otsSecret, ftsSecret⟩ inputs (hencoding parameter) (hgraph parameter)
        (fun selections table => (fun record => (finiteHashAnswer ∅ inputs table, record)) <$>
          referenceCertificateRest ⟨parameter, 0, otsSecret, ftsSecret⟩ (finiteHashAnswer ∅ inputs table) selections dummy adversary)
  apply evalDist_bind_congr_left
  intro table
  rw [referenceCertificateRest_selected, Functor.map_map]

def CertificateTraceRecord.canonicalFull (dummy : OtsReferenceWords) (f : QueryImpl HashSpec Id)
    (record : CertificateTraceRecord) : Prop :=
  let key := record.1
  let forgery := record.2.1.1.1
  let digest := truncateMessageDigest (f (RetainedResidual.signingInput key forgery.message forgery.signature))
  SigningTranscript.Valid record.2.1.1.2 ∧
    ¬SigningTranscript.Contains record.2.1.1.2 forgery ∧
    (∃ cache, FullyHonestOpening f cache key (digestIndex digest) (digestLeaves digest) forgery.signature) ∧
    (∀ lay, OtsVerifierWitness.ReferenceLayerOpening f key (canonicalReferenceWords key f dummy)
      (referenceTableSelection key f) (digestIndex digest) forgery.signature lay) ∧
    TargetCertificateAt key Finset.univ (hashRowsCache record.2.2.messageCalls, record.2.1.1.2)
      (RetainedResidual.signingInput key forgery.message forgery.signature)

theorem referenceForgeryGame_canonicalFull_record (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs)
    (hgraph : ∀ parameter, canonicalGraphInputs parameter ⊆ inputs)
    (dummy : OtsReferenceWords) (adversary : Adversary) (sample : ReferenceForgerySample inputs)
    (hsample : sample ∈ support (referenceForgeryGame inputs hencoding dummy adversary))
    (hcanonical : sample.canonical dummy) (hfull : sample.fullCertificate dummy) :
    sample.certificateRecord.canonicalFull dummy (finiteHashAnswer ∅ inputs sample.2.1.2) := by
  obtain ⟨href, hb⟩ := referenceForgeryGame_support inputs hencoding dummy adversary sample hsample
  rw [referenceFamilyOracleSample_selections sample.1 inputs (hencoding sample.1.parameter)
    (hgraph sample.1.parameter) sample.2.1 href] at hb
  refine ⟨hfull.1, hcanonical.1, ⟨_, hcanonical.2.1⟩, hcanonical.2.2, ?_⟩
  exact referenceForgeryRest_certificate_atRoot sample.1 (finiteHashAnswer ∅ inputs sample.2.1.2) _ rfl
    dummy adversary sample.2.2 hb _ Finset.univ hfull.2

theorem originalCertificateTraceSource_record_cache (adversary : Adversary) :
    (fun result : OriginalCertificateTraceResult => (result.record, result.1.2.2)) <$>
      originalCertificateTraceSource adversary =
        (simulateQ romImpl (certificateTraceProgram adversary)).run ∅ := by
  simp only [originalCertificateTraceSource, certificateTraceProgram, simulateQ_bind, simulateQ_pure,
    StateT.run_bind, StateT.run_pure, map_bind, map_pure, OriginalCertificateTraceResult.record]
  apply bind_congr
  intro generated
  rw [simulateQ_boundaryComputation]
  simp only [bind_pure_comp]
  rfl

theorem certificateTraceProgram_messageCache_le (adversary : Adversary)
    (result : CertificateTraceRecord × QueryCache HashSpec)
    (hresult : result ∈ support ((simulateQ romImpl (certificateTraceProgram adversary)).run ∅)) :
    hashRowsCache result.1.2.2.messageCalls ≤ result.2 := by
  rw [← originalCertificateTraceSource_record_cache, support_map] at hresult
  obtain ⟨source, hsource, rfl⟩ := hresult
  exact originalCertificateTraceSource_messageCache_le adversary source hsource

theorem certificateTraceProgram_nativeCanonical (dummy : OtsReferenceWords) (adversary : Adversary) :
    Pr[fun result => NativeCanonicalCertificate result.1.1 dummy Finset.univ (result.1.2.1, result.2) |
      (simulateQ romImpl (certificateTraceProgram adversary)).run ∅] =
    Pr[fun result => NativeCanonicalCertificate result.1 dummy Finset.univ result.2 |
      originalCertificateSource adversary] := by
  rw [← originalCertificateTraceSource_record_cache, probEvent_map,
    ← originalCertificateTraceSource_original, probEvent_map]
  rfl

theorem fixedCertificateTraceGame_canonicalFull_le (dummy : OtsReferenceWords)
    (adversary : Adversary) (f : QueryImpl HashSpec Id) :
    Pr[CertificateTraceRecord.canonicalFull dummy f | fixedCertificateTraceGame f adversary] ≤
    Pr[fun result => NativeCanonicalCertificate result.1.1 dummy Finset.univ (result.1.2.1, result.2) |
      (simulateQ (fixedCacheWorld f) (certificateTraceProgram adversary)).run ∅] := by
  rw [← simulateQ_certificateTraceProgram, ← fixedCacheWorld_run_forget f _ ∅ (by intro input output h; cases h),
    StateT.run'_eq, probEvent_map]
  apply _root_.probEvent_mono
  intro result hresult hcanonical
  have hagrees := fixedCacheWorld_run_agrees f (certificateTraceProgram adversary) ∅ (by intro input output h; cases h) result hresult
  have hcache := certificateTraceProgram_messageCache_le adversary result
    (fixedCacheWorld_run_support f _ ∅ result hresult)
  exact ⟨hcanonical.1, hcanonical.2.1, f, hagrees, hcanonical.2.2.1, hcanonical.2.2.2.1,
    hcanonical.2.2.2.2.mono hcache⟩

private theorem finiteHash_event_transfer {α : Type} (computation : OracleComp OracleWorld α)
    (inputs : Finset HashInput) (hinputs : hashInputs computation ⊆ inputs)
    (event : QueryImpl HashSpec Id → α → Prop) (native : α × QueryCache HashSpec → Prop)
    (hbound : ∀ f, Pr[event f | simulateQ (fixedHashWorld f) computation] ≤
      Pr[native | (simulateQ (fixedCacheWorld f) computation).run ∅]) :
    Pr[fun result => event result.1 result.2 | do
      let table ← sampleHashTable inputs
      (fun value => (finiteHashAnswer ∅ inputs table, value)) <$>
        simulateQ (fixedHashWorld (finiteHashAnswer ∅ inputs table)) computation] ≤
    Pr[native | (simulateQ romImpl computation).run ∅] := by
  have hle : Pr[fun result => event result.1 result.2 | do
      let table ← sampleHashTable inputs
      (fun value => (finiteHashAnswer ∅ inputs table, value)) <$>
        simulateQ (fixedHashWorld (finiteHashAnswer ∅ inputs table)) computation] ≤
      Pr[native | do
        let table ← sampleHashTable inputs
        (simulateQ (fixedCacheWorld (finiteHashAnswer ∅ inputs table)) computation).run ∅] := by
    simp only [probEvent_bind_eq_tsum, probEvent_map]
    exact ENNReal.tsum_le_tsum (fun table => mul_le_mul' le_rfl (hbound _))
  exact hle.trans_eq (probEvent_congr' (fun _ _ => Iff.rfl)
    (evalDist_romRun_cache_eq_finiteHash computation inputs hinputs ∅).symm)

theorem finiteCertificateTraceGame_canonicalFull_le (dummy : OtsReferenceWords) (adversary : Adversary) :
    Pr[fun result => result.2.canonicalFull dummy result.1 | do
      let table ← sampleHashTable (canonicalGraphGameInputs adversary)
      (fun record => (finiteHashAnswer ∅ _ table, record)) <$>
        fixedCertificateTraceGame (finiteHashAnswer ∅ _ table) adversary] ≤
    Pr[fun result => NativeCanonicalCertificate result.1 dummy Finset.univ result.2 |
      originalCertificateSource adversary] := by
  simp_rw [← simulateQ_certificateTraceProgram]
  exact (finiteHash_event_transfer (certificateTraceProgram adversary) (canonicalGraphGameInputs adversary)
    (by rw [certificateTraceProgram_hashInputs]; exact hashInputs_subset_canonicalGraphGameInputs adversary)
    (CertificateTraceRecord.canonicalFull dummy)
    (fun result => NativeCanonicalCertificate result.1.1 dummy Finset.univ (result.1.2.1, result.2))
    (fun f => by rw [simulateQ_certificateTraceProgram]; exact fixedCertificateTraceGame_canonicalFull_le dummy adversary f)).trans_eq
      (certificateTraceProgram_nativeCanonical dummy adversary)

private theorem probEvent_le_project {Source Result : Type} (source : SPMF Source) (native : ProbComp Result)
    (projection : Source → Result) (event : Source → Prop) (nativeEvent : Result → Prop)
    (hlaw : projection <$> source = 𝒟[native])
    (hevent : ∀ sample ∈ support source, event sample → nativeEvent (projection sample)) :
    Pr[event | source] ≤ Pr[nativeEvent | native] := by
  calc
    _ ≤ Pr[nativeEvent ∘ projection | source] := _root_.probEvent_mono hevent
    _ = Pr[nativeEvent | projection <$> source] := (probEvent_map source projection nativeEvent).symm
    _ = Pr[nativeEvent | native] := by rw [hlaw]; rfl

theorem referenceForgeryGame_canonicalFull_le (dummy : OtsReferenceWords) (adversary : Adversary) :
    Pr[fun sample => sample.canonical dummy ∧ sample.fullCertificate dummy |
      referenceForgeryGame (canonicalGraphGameInputs adversary) (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] ≤
    Pr[fun result => NativeCanonicalCertificate result.1 dummy Finset.univ result.2 |
      originalCertificateSource adversary] := by
  apply le_trans _ (finiteCertificateTraceGame_canonicalFull_le dummy adversary)
  apply probEvent_le_project _ _
    (fun sample : ReferenceForgerySample (canonicalGraphGameInputs adversary) =>
      (finiteHashAnswer ∅ _ sample.2.1.2, sample.certificateRecord))
    (fun sample => sample.canonical dummy ∧ sample.fullCertificate dummy)
    (fun result => result.2.canonicalFull dummy result.1)
    (referenceForgeryGame_oracleCertificateRecord _ _ (canonicalGraphInputs_subset_gameInputs adversary) dummy adversary)
  intro sample hsample hcanonical
  exact referenceForgeryGame_canonicalFull_record _ _ (canonicalGraphInputs_subset_gameInputs adversary)
    dummy adversary sample hsample hcanonical.1 hcanonical.2

end SphincsSecurity.Concrete
