import SphincsSecurity.Proof.Reference.ReferenceInterfaceBudget
import SphincsSecurity.Proof.Reference.ReferenceContactGame

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalGraphInputs canonicalEncodingInputs canonicalGraphGameInputs canonicalGraphLabels

theorem contactObserver_counted (parameter : PublicParameter) (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (computation : OracleComp OracleWorld (Bool × SigningBoundaryTrace)) :
    (fun result : ContactResult => (result.output, (result.before * result.after).toList.length)) <$>
      contactObserver parameter words frontier computation = QueryCap.counted Security.IsHash computation := by
  have h := congrArg (Functor.map (fun result : (Bool × SigningBoundaryTrace) × OtsContactTrace.Trace =>
    (result.1, result.2.toList.length))) (OtsContactTrace.splitRun_trace parameter words frontier computation)
  simp only [Functor.map_map] at h
  rw [contactObserver, Functor.map_map]
  apply h.trans
  apply QueryPause.traced_counted hashObservationTrace Security.IsHash (fun trace => trace.toList.length) rfl
  intro input answer trace
  cases input <;> simp only [hashObservationTrace, one_mul, Security.IsHash, if_false, if_true,
    Nat.zero_add, FreeMonoid.toList_mul, FreeMonoid.toList_of, List.length_append, List.length_singleton]

theorem referenceContactGame_counted (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs)
    (dummy : OtsReferenceWords) (adversary : Adversary) :
    (fun result : InstrumentedResult ContactResult =>
      (result.1, result.2.1, result.2.2.output, (result.2.2.before * result.2.2.after).toList.length)) <$>
      referenceContactGame inputs hencoding dummy adversary =
    (fun result : ReferenceRecordedResult =>
      (result.1, result.2.1, result.2.2.1, QueryCap.calls Security.IsHash result.2.2.2)) <$>
      referenceRecordedGame inputs hencoding dummy adversary := by
  unfold referenceContactGame referenceInstrumentedGame referenceRecordedGame
  simp only [map_bind, map_pure]
  apply congrArg (𝒟[sampleParameter] >>= ·)
  funext parameter
  apply congrArg (𝒟[sampleOtsSecrets] >>= ·)
  funext otsSecret
  apply congrArg (𝒟[sampleFtsSecrets] >>= ·)
  funext ftsSecret
  apply congrArg (𝒟[referenceFamilyOracleSample _ inputs (hencoding parameter)] >>= ·)
  funext reference
  simp only [bind_pure_comp, ← evalDist_map, referenceInstrumentedRest, referenceRecordedRest,
    ← simulateQ_map]
  have h := contactObserver_counted parameter (referenceFamilyWords reference.1 dummy)
    (canonicalGraphFrontier otsSecret
      (canonicalGraphLabels parameter otsSecret ftsSecret (finiteHashAnswer ∅ inputs reference.2))
      (referenceFamilyWords reference.1 dummy))
    (CausalFrontierProgram.game parameter (finiteHashAnswer ∅ inputs reference.2) ftsSecret
      (referenceFamilyWords reference.1 dummy)
      (canonicalGraphFrontier otsSecret
        (canonicalGraphLabels parameter otsSecret ftsSecret (finiteHashAnswer ∅ inputs reference.2))
        (referenceFamilyWords reference.1 dummy)) adversary)
  rw [← QueryCap.recorded_counted Security.IsHash] at h
  simpa only [Functor.map_map] using congrArg (fun computation => 𝒟[simulateQ (fixedHashWorld (finiteHashAnswer ∅ inputs reference.2))
    ((fun result => (parameter, reference.1, result)) <$> computation)]) h

theorem referenceContactGame_interface_budget (adversary : Security.Adversary) (q : Nat)
    (hsmall : q < 2 ^ 256) (hbound : Security.HasHashQueryBound adversary q)
    (dummy : OtsReferenceWords) (result : InstrumentedResult ContactResult)
    (hresult : result ∈ support (referenceContactGame
      (canonicalGraphGameInputs (Seeded.memoAdversary (Security.embed adversary)))
      (canonicalEncodingInputs_subset_gameInputs _) dummy (Seeded.memoAdversary (Security.embed adversary)))) :
    (result.2.2.before * result.2.2.after).toList.length ≤ q := by
  have hm : (result.1, result.2.1, result.2.2.output, (result.2.2.before * result.2.2.after).toList.length) ∈ support
      ((fun result : InstrumentedResult ContactResult =>
        (result.1, result.2.1, result.2.2.output, (result.2.2.before * result.2.2.after).toList.length)) <$>
        referenceContactGame (canonicalGraphGameInputs (Seeded.memoAdversary (Security.embed adversary)))
          (canonicalEncodingInputs_subset_gameInputs _) dummy (Seeded.memoAdversary (Security.embed adversary))) := by
    rw [support_map]
    exact ⟨result, hresult, rfl⟩
  rw [referenceContactGame_counted, support_map] at hm
  obtain ⟨record, hrecord, heq⟩ := hm
  have hcount := congrArg (fun result : PrefixCountedResult => result.2.2.2) heq
  dsimp only at hcount
  rw [← hcount]
  exact referenceRecordedGame_interface_budget adversary q hsmall hbound dummy record hrecord

end SphincsSecurity.Concrete
