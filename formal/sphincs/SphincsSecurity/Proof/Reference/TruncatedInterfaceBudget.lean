import SphincsSecurity.Proof.Base.QueryTruncation
import SphincsSecurity.Proof.Reference.CausalInterfaceCount
import SphincsSecurity.Proof.Forced.FtsGuessTruncatedInputs
import SphincsSecurity.Proof.Forced.FtsGuessInterfaceBudget

namespace SphincsSecurity.Concrete
open OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

noncomputable def fixedSigningInterface (key : SecretKey) (f : QueryImpl HashSpec Id) :
    QueryImpl (OracleWorld + SigningSpec) ProbComp :=
  fixedHashWorld f ∘ₛ Security.expandSigning (sign key)

theorem fixed_main_interface_budget (original : Security.Adversary) (q : Nat)
    (hsmall : q < 2 ^ 256) (hbound : Security.HasHashQueryBound original q)
    (key : SecretKey) (f : QueryImpl HashSpec Id)
    (hroot : key.root = evalWithAnswerFn f (treeRoot key.parameter topLayer rootTree (key.otsSecret topLayer rootTree))) :
    ∀ result ∈ support (simulateQ (fixedSigningInterface key f) (QueryCap.counted Security.IsAdversaryHash
      ((Seeded.memoAdversary (Security.embed original)).main ⟨key.root, key.parameter⟩))), result.2 ≤ q := by
  have hg := fixedInterface_counted_budget original q hsmall hbound key.parameter key.otsSecret key.ftsSecret f
  dsimp only at hg
  rw [← hroot] at hg
  have hkey : (⟨key.parameter, key.root, key.otsSecret, key.ftsSecret⟩ : SecretKey) = key := by cases key; rfl
  rw [hkey] at hg
  have hlog : ∀ result ∈ support (simulateQ (fixedSigningInterface key f) (QueryCap.counted Security.IsAdversaryHash
      (DeterministicSigning.withRequestLog ((Seeded.memoAdversary (Security.embed original)).main ⟨key.root, key.parameter⟩)))), result.2 ≤ q := by
    apply QueryCap.counted_bind_first_bound Security.IsAdversaryHash (fixedSigningInterface key f) _
      (fun result => DeterministicSigning.baseLift (Seeded.finishGame ⟨key.root, key.parameter⟩ result)) q
    simpa only [fixedSigningInterface, QueryImpl.simulateQ_compose, Seeded.sourceGame] using hg
  intro result hr
  have heq := congrArg (fun computation => simulateQ (fixedSigningInterface key f)
    (QueryCap.counted Security.IsAdversaryHash computation))
    (DeterministicSigning.fst_withRequestLog ((Seeded.memoAdversary (Security.embed original)).main ⟨key.root, key.parameter⟩))
  rw [QueryCap.counted_map, simulateQ_map] at heq
  rw [← heq, support_map] at hr
  obtain ⟨before, hb, rfl⟩ := hr
  exact hlog before hb

theorem fixed_truncated_main_interface_budget (original : Security.Adversary) (q : Nat)
    (hsmall : q < 2 ^ 256) (hbound : Security.HasHashQueryBound original q)
    (key : SecretKey) (f : QueryImpl HashSpec Id)
    (hroot : key.root = evalWithAnswerFn f (treeRoot key.parameter topLayer rootTree (key.otsSecret topLayer rootTree))) :
    ∀ result ∈ support (simulateQ (fixedSigningInterface key f) (QueryCap.counted Security.IsAdversaryHash
      ((FtsGuessHash.signingTruncatedAdversary (Seeded.memoAdversary (Security.embed original))).main ⟨key.root, key.parameter⟩))),
      result.2 ≤ q :=
  QueryCap.counted_truncate_bound RetainedResidual.IsSigningRequest Security.IsAdversaryHash (fixedSigningInterface key f) _
    signatureLimit zeroForgery q (fixed_main_interface_budget original q hsmall hbound key f hroot)

theorem fixed_frontier_main_trace_count {α : Type} (key : SecretKey) (f : QueryImpl HashSpec Id)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (hfrontier : IsSigningFrontier key f words frontier)
    (hwords : ∀ index lay, FrontierReferenceWord key.parameter f key.ftsSecret words frontier index lay)
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    (fun result => (result.1.1.1, result.2.toList.length)) <$>
      OtsContactTrace.fixedTrace f (CausalFrontierProgram.adversaryRun key.parameter key.root f key.ftsSecret words frontier computation) =
      simulateQ (fixedSigningInterface key f) (QueryCap.counted Security.IsAdversaryHash computation) := by
  have ht := congrArg (Functor.map (fun result => (result.1.1.1, result.2)))
    (fixedTrace_count f (CausalFrontierProgram.adversaryRun key.parameter key.root f key.ftsSecret words frontier computation))
  simp only [Functor.map_map] at ht
  rw [ht]
  have hc := congrArg (Functor.map (fun result => (result.1.1, result.2)))
    (CausalFrontierProgram.fixed_counted_interface_forget key f words frontier hfrontier hwords (OtsPrefix.logged computation))
  simp only [Functor.map_map] at hc
  rw [CausalFrontierProgram.adversaryRun, hc]
  have hlog : Prod.fst <$> OtsPrefix.logged computation = computation := by
    rw [CausalFrontierProgram.logged_eq_signingTrace]
    exact FtsProbeSimulation.signingTraceComputation_fst computation
  have hm := congrArg (fun computation => simulateQ (fixedSigningInterface key f)
    (QueryCap.counted Security.IsAdversaryHash computation)) hlog
  rw [QueryCap.counted_map, simulateQ_map] at hm
  simpa only [fixedSigningInterface, QueryImpl.simulateQ_compose] using hm

attribute [local irreducible] canonicalGraphGameInputs canonicalGraphLabels frontierRoot maskOtsPrefixes
  canonicalReferenceWords canonicalFrontierValues

theorem referenceForgeryRest_truncated_main_budget (original : Security.Adversary) (q : Nat)
    (hsmall : q < 2 ^ 256) (hbound : Security.HasHashQueryBound original q)
    (key : SecretKey) (f : QueryImpl HashSpec Id) (dummy : OtsReferenceWords) (before : OtsContactTrace.AdversaryTrace)
    (hr : before ∈ support (referenceForgeryRest key f (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret f)
      (referenceTableSelection key f) dummy (FtsGuessHash.signingTruncatedAdversary (Seeded.memoAdversary (Security.embed original))))) :
    before.2.toList.length ≤ q := by
  let root := evalWithAnswerFn f (treeRoot key.parameter topLayer rootTree (key.otsSecret topLayer rootTree))
  let rooted : SecretKey := { key with root := root }
  have hw : referenceFamilyWords (referenceTableSelection key f) dummy = canonicalReferenceWords rooted f dummy := by
    rw [referenceFamilyWords_selected]
    exact (ReferenceVerifierWitness.canonicalReferenceWords_root key f root dummy).symm
  rw [referenceForgeryRest, hw, canonicalGraphLabels_frontier key.parameter key.otsSecret key.ftsSecret f _ root] at hr
  have hfrontier := isSigningFrontier_canonical rooted f (canonicalReferenceWords rooted f dummy)
  have hwords := frontierReferenceWord_canonical rooted f dummy
  have hroot : rooted.root = evalWithAnswerFn f (treeRoot rooted.parameter topLayer rootTree (rooted.otsSecret topLayer rootTree)) := rfl
  rw [← frontierRoot_eq_of_agree rooted.parameter (canonicalReferenceWords rooted f dummy) f
      (maskOtsPrefixes rooted.parameter (canonicalReferenceWords rooted f dummy) f)
      (maskOtsPrefixes_agrees rooted.parameter (canonicalReferenceWords rooted f dummy) f),
    frontierRoot_eq rooted f (canonicalReferenceWords rooted f dummy) _ hfrontier, ← hroot] at hr
  apply fixed_truncated_main_interface_budget original q hsmall hbound rooted f hroot (before.1.1.1, before.2.toList.length)
  rw [← fixed_frontier_main_trace_count rooted f (canonicalReferenceWords rooted f dummy) _ hfrontier hwords, support_map]
  exact ⟨before, hr, rfl⟩

end SphincsSecurity.Concrete
