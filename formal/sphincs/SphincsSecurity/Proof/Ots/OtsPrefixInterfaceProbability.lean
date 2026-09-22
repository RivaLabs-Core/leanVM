import SphincsSecurity.Proof.Ots.OtsPrefixInterfaceBudget
import SphincsSecurity.Proof.Chains.AdaptiveChainCountedObservation
import SphincsSecurity.Proof.Ots.OtsPrefixContactProbability
import SphincsSecurity.Proof.Ots.OtsPrefixTwoEdgeProbability

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalGraphLabels canonicalEncodingInputs canonicalGraphInputs instFintypePosition
attribute [local instance] Classical.propDecidable

private theorem probComp_mem_of_evalDist {Result : Type} (computation : ProbComp Result) (result : Result)
    (hresult : result ∈ support 𝒟[computation]) : result ∈ support computation :=
  (mem_support_iff_of_evalDist_eq (mx := computation) (mx' := 𝒟[computation]) rfl result).mpr hresult

private theorem pmf_mem_of_evalDist {Result : Type} (law : PMF Result) (result : Result)
    (hresult : result ∈ support 𝒟[law]) : result ∈ law.support := by
  change result ∈ (𝒟[law]).support at hresult
  simpa only [PMF.evalDist_eq, SPMF.support_liftM] using hresult

theorem prefixIdealCostGame_lower_interface (address : OtsPrefix.ChainAddress) (dummy : OtsReferenceWords)
    (original : Security.Adversary) (q : Nat) (hbound : Security.HasHashQueryBound original q) (hsmall : q < 2 ^ 256) :
    let adversary := Seeded.memoAdversary (Security.embed original)
    (1 - (q : ENNReal) / Fintype.card Digest) *
        (∑' count, Pr[= count | prefixIdealCostGame (canonicalGraphGameInputs adversary)
          (canonicalEncodingInputs_subset_gameInputs adversary) (canonicalGraphInputs_subset_gameInputs adversary)
          address dummy adversary q] * (count : ENNReal)) ≤
      ∑' result : PrefixCountedResult, Pr[= result | prefixCountedObservedGame (canonicalGraphGameInputs adversary)
        (canonicalEncodingInputs_subset_gameInputs adversary) (canonicalGraphInputs_subset_gameInputs adversary)
        address dummy adversary] * (result.2.2.2 : ENNReal) := by
  dsimp only
  let adversary := Seeded.memoAdversary (Security.embed original)
  unfold prefixIdealCostGame prefixCountedObservedGame
  apply QueryCap.scaled_expectation_bind_le
  intro parameter hparameter
  apply QueryCap.scaled_expectation_bind_le
  intro ftsSecret _
  apply QueryCap.scaled_expectation_bind_le
  intro selections hselections
  apply QueryCap.scaled_expectation_bind_le
  intro other _
  apply QueryCap.scaled_expectation_bind_le
  intro auxiliary hauxiliary
  let words := referenceFamilyWords selections dummy
  let segment := OtsPrefix.atAddress parameter words address
  let inputs := canonicalGraphGameInputs adversary
  let hencoding := canonicalEncodingInputs_subset_gameInputs adversary parameter
  let hgraph := canonicalGraphInputs_subset_gameInputs adversary parameter
  let computation := fun endpoint => segment.seedGame inputs hencoding hgraph auxiliary other.val ftsSecret words endpoint adversary
  have hreal : ∀ result ∈ (PartialChainEndpoint.realRun (fun _ => OtsPrefix.uniformImpl)
    (fun endpoint => QueryCap.counted PartialChainEndpoint.IsPrefixQuery (computation endpoint)) (fun _ _ => none)).support,
      result.2.1.2 ≤ q :=
    prefixObservedRun_interface_budget parameter (probComp_mem_of_evalDist _ parameter hparameter) ftsSecret
      address dummy original selections (pmf_mem_of_evalDist _ selections hselections)
      q hsmall hbound other auxiliary (pmf_mem_of_evalDist _ auxiliary hauxiliary)
  have h := PartialChainEndpoint.idealRun_cap_spent_lower_of_counted (fun _ => OtsPrefix.uniformImpl) computation q hreal
  simpa only [tsum_probOutput_bind_mul, tsum_probOutput_pure_mul, ← PMF.monad_map_eq_map,
    evalDist_map, tsum_probOutput_map_mul, PMF.evalDist_eq, SPMF.probOutput_liftM, PMF.probOutput_eq_apply] using h

theorem prefixContactGame_le_interface (address : OtsPrefix.ChainAddress) (dummy : OtsReferenceWords)
    (original : Security.Adversary) (q : Nat) (hbound : Security.HasHashQueryBound original q) (hsmall : q < Fintype.card Digest) :
    let adversary := Seeded.memoAdversary (Security.embed original)
    Pr[= true | prefixContactGame (canonicalGraphGameInputs adversary)
      (canonicalEncodingInputs_subset_gameInputs adversary) (canonicalGraphInputs_subset_gameInputs adversary) address dummy adversary] ≤
      (2 / Fintype.card Digest) * ∑' count, Pr[= count | prefixIdealCostGame (canonicalGraphGameInputs adversary)
        (canonicalEncodingInputs_subset_gameInputs adversary) (canonicalGraphInputs_subset_gameInputs adversary)
        address dummy adversary q] * (count : ENNReal) := by
  dsimp only
  let adversary := Seeded.memoAdversary (Security.embed original)
  have h : 1 * (∑' result, Pr[= result | prefixContactGame (canonicalGraphGameInputs adversary)
      (canonicalEncodingInputs_subset_gameInputs adversary) (canonicalGraphInputs_subset_gameInputs adversary) address dummy adversary] *
        (if result = true then 1 else 0)) ≤
      ∑' count, Pr[= count | prefixIdealCostGame (canonicalGraphGameInputs adversary)
        (canonicalEncodingInputs_subset_gameInputs adversary) (canonicalGraphInputs_subset_gameInputs adversary)
        address dummy adversary q] * ((2 / Fintype.card Digest) * (count : ENNReal)) := by
    unfold prefixContactGame prefixIdealCostGame
    apply QueryCap.scaled_expectation_bind_le
    intro parameter hparameter
    apply QueryCap.scaled_expectation_bind_le
    intro ftsSecret _
    apply QueryCap.scaled_expectation_bind_le
    intro selections hselections
    apply QueryCap.scaled_expectation_bind_le
    intro other _
    apply QueryCap.scaled_expectation_bind_le
    intro auxiliary hauxiliary
    let words := referenceFamilyWords selections dummy
    let segment := OtsPrefix.atAddress parameter words address
    let inputs := canonicalGraphGameInputs adversary
    let hencoding := canonicalEncodingInputs_subset_gameInputs adversary parameter
    let hgraph := canonicalGraphInputs_subset_gameInputs adversary parameter
    let computation := fun endpoint => segment.seedGame inputs hencoding hgraph auxiliary other.val ftsSecret words endpoint adversary
    have hreal : ∀ result ∈ (PartialChainEndpoint.realRun (fun _ => OtsPrefix.uniformImpl)
      (fun endpoint => QueryCap.counted PartialChainEndpoint.IsPrefixQuery (computation endpoint)) (fun _ _ => none)).support,
        result.2.1.2 ≤ q :=
      prefixObservedRun_interface_budget parameter (probComp_mem_of_evalDist _ parameter hparameter) ftsSecret
        address dummy original selections (pmf_mem_of_evalDist _ selections hselections)
        q (hsmall.trans_le (by norm_num [digestBits])) hbound other auxiliary (pmf_mem_of_evalDist _ auxiliary hauxiliary)
    have hcontact := PartialChainEndpoint.realRun_contact_le_cap_cost_of_counted (fun _ => OtsPrefix.uniformImpl) computation q hreal hsmall
    simp only [one_mul, tsum_probOutput_bind_mul, tsum_probOutput_pure_mul]
    simpa only [PMF.evalDist_eq, SPMF.probOutput_liftM, PMF.probOutput_eq_apply, decide_eq_true_eq,
      probEvent_eq_tsum_ite, mul_ite, mul_one, mul_zero,
      mul_left_comm _ (2 / (Fintype.card Digest : ENNReal)), ENNReal.tsum_mul_left] using hcontact
  simpa only [one_mul, mul_ite, mul_one, mul_zero, tsum_ite_eq,
    mul_left_comm _ (2 / (Fintype.card Digest : ENNReal)), ENNReal.tsum_mul_left] using h

theorem prefixTwoEdgeGame_le_interface (address : OtsPrefix.ChainAddress) (dummy : OtsReferenceWords)
    (original : Security.Adversary) (q : Nat) (hbound : Security.HasHashQueryBound original q) (hsmall : q < Fintype.card Digest) :
    let adversary := Seeded.memoAdversary (Security.embed original)
    Pr[= true | prefixTwoEdgeGame (canonicalGraphGameInputs adversary)
      (canonicalEncodingInputs_subset_gameInputs adversary) (canonicalGraphInputs_subset_gameInputs adversary) address dummy adversary] ≤
      (prefixTwoEdgeRate q) * ∑' count, Pr[= count | prefixIdealCostGame (canonicalGraphGameInputs adversary)
        (canonicalEncodingInputs_subset_gameInputs adversary) (canonicalGraphInputs_subset_gameInputs adversary)
        address dummy adversary q] * (count : ENNReal) := by
  dsimp only
  let adversary := Seeded.memoAdversary (Security.embed original)
  have h : 1 * (∑' result, Pr[= result | prefixTwoEdgeGame (canonicalGraphGameInputs adversary)
      (canonicalEncodingInputs_subset_gameInputs adversary) (canonicalGraphInputs_subset_gameInputs adversary) address dummy adversary] *
        (if result = true then 1 else 0)) ≤
      ∑' count, Pr[= count | prefixIdealCostGame (canonicalGraphGameInputs adversary)
        (canonicalEncodingInputs_subset_gameInputs adversary) (canonicalGraphInputs_subset_gameInputs adversary)
        address dummy adversary q] * ((prefixTwoEdgeRate q) * (count : ENNReal)) := by
    unfold prefixTwoEdgeGame prefixIdealCostGame
    apply QueryCap.scaled_expectation_bind_le
    intro parameter hparameter
    apply QueryCap.scaled_expectation_bind_le
    intro ftsSecret _
    apply QueryCap.scaled_expectation_bind_le
    intro selections hselections
    apply QueryCap.scaled_expectation_bind_le
    intro other _
    apply QueryCap.scaled_expectation_bind_le
    intro auxiliary hauxiliary
    let words := referenceFamilyWords selections dummy
    let segment := OtsPrefix.atAddress parameter words address
    let inputs := canonicalGraphGameInputs adversary
    let hencoding := canonicalEncodingInputs_subset_gameInputs adversary parameter
    let hgraph := canonicalGraphInputs_subset_gameInputs adversary parameter
    let computation := fun endpoint => segment.seedGame inputs hencoding hgraph auxiliary other.val ftsSecret words endpoint adversary
    have hreal : ∀ result ∈ (PartialChainEndpoint.realRun (fun _ => OtsPrefix.uniformImpl)
      (fun endpoint => QueryCap.counted PartialChainEndpoint.IsPrefixQuery (computation endpoint)) (fun _ _ => none)).support,
        result.2.1.2 ≤ q :=
      prefixObservedRun_interface_budget parameter (probComp_mem_of_evalDist _ parameter hparameter) ftsSecret
        address dummy original selections (pmf_mem_of_evalDist _ selections hselections)
        q (hsmall.trans_le (by norm_num [digestBits])) hbound other auxiliary (pmf_mem_of_evalDist _ auxiliary hauxiliary)
    have htwoEdge := PartialChainEndpoint.realRun_twoEdgeEvent_le_cap_cost_of_counted (fun _ => OtsPrefix.uniformImpl) computation q hreal hsmall
    simp only [one_mul, tsum_probOutput_bind_mul, tsum_probOutput_pure_mul]
    simpa only [prefixTwoEdgeRate, PMF.evalDist_eq, SPMF.probOutput_liftM, PMF.probOutput_eq_apply, decide_eq_true_eq,
      probEvent_eq_tsum_ite, mul_ite, mul_one, mul_zero,
      PartialChainEndpoint.expectation_scale] using htwoEdge
  simpa only [one_mul, mul_ite, mul_one, mul_zero, tsum_ite_eq,
    mul_left_comm _ (prefixTwoEdgeRate q), ENNReal.tsum_mul_left] using h

end SphincsSecurity.Concrete
