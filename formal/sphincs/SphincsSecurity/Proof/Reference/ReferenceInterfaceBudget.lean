import SphincsSecurity.Proof.Reference.CausalInterfaceCount
import SphincsSecurity.Proof.Reference.ReferenceVerifierInstantiation
import SphincsSecurity.Proof.Reference.ReferenceQueryAllocation

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
attribute [local irreducible] canonicalGraphInputs canonicalEncodingInputs canonicalGraphGameInputs

theorem referenceRecordedRest_interface_budget (adversary : Security.Adversary) (q : Nat)
    (hsmall : q < 2 ^ 256) (hbound : Security.HasHashQueryBound adversary q)
    (key : SecretKey) (f : QueryImpl HashSpec Id) (dummy : OtsReferenceWords)
    (result : (Bool × SigningBoundaryTrace) × List OracleWorld.Domain)
    (hresult : result ∈ support (referenceRecordedRest key f
      (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret f)
      (referenceTableSelection key f) dummy (Seeded.memoAdversary (Security.embed adversary)))) :
    QueryCap.calls Security.IsHash result.2 ≤ q := by
  let root := evalWithAnswerFn f (treeRoot key.parameter topLayer rootTree (key.otsSecret topLayer rootTree))
  let rooted : SecretKey := { key with root := root }
  have hw : referenceFamilyWords (referenceTableSelection key f) dummy =
      canonicalReferenceWords rooted f dummy := by
    rw [referenceFamilyWords_selected]
    exact (ReferenceVerifierWitness.canonicalReferenceWords_root key f root dummy).symm
  rw [referenceRecordedRest, hw, canonicalGraphLabels_frontier key.parameter key.otsSecret key.ftsSecret f _ root] at hresult
  apply CausalFrontierProgram.fixed_game_counted_budget adversary q hsmall hbound rooted f rfl
    (canonicalReferenceWords rooted f dummy) (canonicalFrontierValues rooted f (canonicalReferenceWords rooted f dummy))
    (isSigningFrontier_canonical rooted f _) (frontierReferenceWord_canonical rooted f dummy)
    (result.1, QueryCap.calls Security.IsHash result.2)
  rw [← QueryCap.recorded_counted, simulateQ_map, support_map]
  exact ⟨result, hresult, rfl⟩

theorem referenceRecordedGame_interface_budget (adversary : Security.Adversary) (q : Nat)
    (hsmall : q < 2 ^ 256) (hbound : Security.HasHashQueryBound adversary q)
    (dummy : OtsReferenceWords) (result : ReferenceRecordedResult)
    (hresult : result ∈ support (referenceRecordedGame
      (canonicalGraphGameInputs (Seeded.memoAdversary (Security.embed adversary)))
      (canonicalEncodingInputs_subset_gameInputs _) dummy (Seeded.memoAdversary (Security.embed adversary)))) :
    QueryCap.calls Security.IsHash result.2.2.2 ≤ q := by
  simp only [referenceRecordedGame, mem_support_bind_iff] at hresult
  obtain ⟨parameter, _, otsSecret, _, ftsSecret, _, reference, hreference, output, houtput, hresult⟩ := hresult
  rw [mem_support_pure_iff] at hresult
  subst result
  have href : reference ∈ (referenceFamilyOracleSample ⟨parameter, 0, otsSecret, ftsSecret⟩
      (canonicalGraphGameInputs (Seeded.memoAdversary (Security.embed adversary)))
      (canonicalEncodingInputs_subset_gameInputs _ parameter)).support := by
    simpa only [PMF.evalDist_eq, SPMF.support_eq_support, SPMF.support_liftM] using hreference
  have hselected := referenceFamilyOracleSample_selections ⟨parameter, 0, otsSecret, ftsSecret⟩
    _ (canonicalEncodingInputs_subset_gameInputs _ parameter)
    (canonicalGraphInputs_subset_gameInputs _ parameter) reference href
  rw [hselected] at houtput
  apply referenceRecordedRest_interface_budget adversary q hsmall hbound ⟨parameter, 0, otsSecret, ftsSecret⟩
    _ dummy output
  exact (mem_support_iff_of_evalDist_eq (mx := referenceRecordedRest _ _ _ _ _ _) (mx' := 𝒟[referenceRecordedRest _ _ _ _ _ _])
    rfl output).mpr houtput

attribute [local instance] Classical.propDecidable

def IsInterfaceMessage (parameter : PublicParameter) (input : OracleWorld.Domain) : Prop :=
  Security.IsHash input ∧ ¬CausalFrontierProgram.NonmessageHash parameter input

noncomputable def ReferenceRecordedResult.interfaceMessageCalls (result : ReferenceRecordedResult) : Nat := by
  classical
  exact QueryCap.calls (IsInterfaceMessage result.1) result.2.2.2

theorem interface_hash_partition (parameter : PublicParameter) (inputs : List OracleWorld.Domain) :
    QueryCap.calls (CausalFrontierProgram.NonmessageHash parameter) inputs +
      QueryCap.calls (IsInterfaceMessage parameter) inputs =
      QueryCap.calls Security.IsHash inputs := by
  classical
  induction inputs with
  | nil => rfl
  | cons input inputs ih =>
    simp only [QueryCap.calls_cons]
    have hstep : (if CausalFrontierProgram.NonmessageHash parameter input then 1 else 0) +
        (if IsInterfaceMessage parameter input then 1 else 0) =
        if Security.IsHash input then 1 else 0 := by
      cases input with
      | inl sample => simp [IsInterfaceMessage, Security.IsHash, CausalFrontierProgram.NonmessageHash]
      | inr query =>
        by_cases hm : FtsProbeSimulation.MessageHashInput parameter query <;>
          simp [IsInterfaceMessage, Security.IsHash, CausalFrontierProgram.NonmessageHash, hm]
    omega

theorem referenceRecordedGame_interface_allocation (adversary : Security.Adversary) (q : Nat)
    (hsmall : q < 2 ^ 256) (hbound : Security.HasHashQueryBound adversary q)
    (dummy : OtsReferenceWords) (result : ReferenceRecordedResult)
    (hresult : result ∈ support (referenceRecordedGame
      (canonicalGraphGameInputs (Seeded.memoAdversary (Security.embed adversary)))
      (canonicalEncodingInputs_subset_gameInputs _) dummy (Seeded.memoAdversary (Security.embed adversary)))) :
    result.prefixCalls dummy + result.encodingCalls + result.otherCalls dummy + result.interfaceMessageCalls ≤ q := by
  have hpartition := QueryClass.allocation_calls result.1 (referenceFamilyWords result.2.1 dummy) result.2.2.2
  have hall := interface_hash_partition result.1 result.2.2.2
  have hbudget := referenceRecordedGame_interface_budget adversary q hsmall hbound dummy result hresult
  dsimp only [ReferenceRecordedResult.prefixCalls, ReferenceRecordedResult.encodingCalls,
    ReferenceRecordedResult.otherCalls, ReferenceRecordedResult.interfaceMessageCalls]
  omega

end SphincsSecurity.Concrete
