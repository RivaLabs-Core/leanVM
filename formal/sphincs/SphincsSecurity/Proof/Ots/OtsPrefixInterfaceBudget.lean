import SphincsSecurity.Proof.Reference.ReferenceInterfaceBudget
import SphincsSecurity.Proof.Ots.OtsPrefixObservedAllocation

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalGraphLabels canonicalEncodingInputs canonicalGraphInputs instFintypePosition

theorem prefixCountedObservedGame_interface_budget (address : OtsPrefix.ChainAddress)
    (dummy : OtsReferenceWords) (adversary : Security.Adversary) (q : Nat)
    (hsmall : q < 2 ^ 256) (hbound : Security.HasHashQueryBound adversary q)
    (result : PrefixCountedResult)
    (hresult : result ∈ support (prefixCountedObservedGame
      (canonicalGraphGameInputs (Seeded.memoAdversary (Security.embed adversary)))
      (canonicalEncodingInputs_subset_gameInputs _) (canonicalGraphInputs_subset_gameInputs _)
      address dummy (Seeded.memoAdversary (Security.embed adversary)))) : result.2.2.2 ≤ q := by
  rw [prefixCountedObservedGame_original, support_map] at hresult
  obtain ⟨record, hrecord, rfl⟩ := hresult
  apply le_trans _ (referenceRecordedGame_interface_budget adversary q hsmall hbound dummy record hrecord)
  apply QueryCap.calls_mono
  intro input hinput
  cases input with
  | inl sample => exact False.elim hinput
  | inr query => trivial

private theorem pmf_mem_evalDist {Result : Type} (law : PMF Result) (result : Result) (h : result ∈ law.support) :
    result ∈ support 𝒟[law] := by
  change result ∈ (𝒟[law]).support
  simpa only [PMF.evalDist_eq, SPMF.support_liftM] using h

private theorem probComp_mem_evalDist {Result : Type} (law : ProbComp Result) (result : Result)
    (h : result ∈ support law) : result ∈ support 𝒟[law] :=
  (mem_support_iff_of_evalDist_eq (mx := law) (mx' := 𝒟[law]) rfl result).mp h

private theorem ftsSecret_mem_evalDist (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    ftsSecret ∈ support 𝒟[sampleFtsSecrets] := by
  apply probComp_mem_evalDist
  unfold sampleFtsSecrets
  change ftsSecret ∈ support (@SampleableType.selectElem (Index → FtsTree → FtsLeaf → Digest) ftsSecretsSampleableType)
  exact ftsSecretsSampleableType.mem_support_selectElem ftsSecret

theorem prefixObservedRun_interface_budget (parameter : PublicParameter)
    (hparameter : parameter ∈ support sampleParameter) (ftsSecret : Seeded.FtsSecrets)
    (address : OtsPrefix.ChainAddress) (dummy : OtsReferenceWords) (adversary : Security.Adversary)
    (selections : ReferenceFamily)
    (hselections : selections ∈ (FirstSuccessFamily.selected decodeEncodingOutput encodingAttemptLimit).support)
    (q : Nat) (hsmall : q < 2 ^ 256) (hbound : Security.HasHashQueryBound adversary q) :
    let reduced := Seeded.memoAdversary (Security.embed adversary)
    let words := referenceFamilyWords selections dummy
    let segment := OtsPrefix.atAddress parameter words address
    let inputs := canonicalGraphGameInputs reduced
    let hencoding := canonicalEncodingInputs_subset_gameInputs reduced parameter
    let hgraph := canonicalGraphInputs_subset_gameInputs reduced parameter
    ∀ (other : segment.ErasedSecrets) (auxiliary : segment.ReferenceAuxSeed inputs hencoding hgraph),
      auxiliary ∈ (segment.referenceAuxSeedLaw inputs hencoding hgraph selections).support →
      ∀ result ∈ (PartialChainEndpoint.realRun (fun _ => OtsPrefix.uniformImpl)
        (fun endpoint => QueryCap.counted PartialChainEndpoint.IsPrefixQuery
          (segment.seedGame inputs hencoding hgraph auxiliary other.val ftsSecret words endpoint reduced))
        (fun _ _ => none)).support, result.2.1.2 ≤ q := by
  dsimp only
  intro other auxiliary hauxiliary result hresult
  apply prefixCountedObservedGame_interface_budget address dummy adversary q hsmall hbound
    (parameter, selections, result.2.1)
  unfold prefixCountedObservedGame
  refine (mem_support_bind_iff _ _ _).mpr ⟨parameter, probComp_mem_evalDist _ _ hparameter, ?_⟩
  refine (mem_support_bind_iff _ _ _).mpr ⟨ftsSecret, ftsSecret_mem_evalDist ftsSecret, ?_⟩
  refine (mem_support_bind_iff _ _ _).mpr ⟨selections, pmf_mem_evalDist _ _ hselections, ?_⟩
  refine (mem_support_bind_iff _ _ _).mpr ⟨other, pmf_mem_evalDist _ _ (PMF.mem_support_uniformOfFintype other), ?_⟩
  refine (mem_support_bind_iff _ _ _).mpr ⟨auxiliary, pmf_mem_evalDist _ _ hauxiliary, ?_⟩
  refine (mem_support_bind_iff _ _ _).mpr ⟨result.2.1, ?_, ?_⟩
  · apply pmf_mem_evalDist
    rw [PMF.mem_support_map_iff]
    exact ⟨result, hresult, rfl⟩
  · exact (mem_support_pure_iff _ _).mpr rfl

end SphincsSecurity.Concrete
