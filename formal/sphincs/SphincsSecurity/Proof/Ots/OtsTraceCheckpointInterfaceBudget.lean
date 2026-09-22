import SphincsSecurity.Proof.Ots.OtsTraceCheckpointLaw
import SphincsSecurity.Proof.Ots.OtsPrefixVisibleAccounting
import SphincsSecurity.Proof.Chains.AdaptiveChainCountedBudget
import SphincsSecurity.Proof.Reference.InterfaceCounting
import SphincsSecurity.Proof.Base.QueryTraceInvariant
namespace SphincsSecurity.Concrete.OtsPrefix

open _root_.OracleComp OracleSpec PartialChainEndpoint
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalGraphLabels canonicalEncodingInputs canonicalGraphInputs instFintypePosition

theorem counted_eraseAux {Result : Type} (segment : OtsPrefix) (outside : QueryImpl HashSpec Id)
    (computation : OracleComp segment.VisibleWorld Result) :
    QueryCap.counted IsPrefixQuery (simulateQ (eraseAux outside) computation) =
      simulateQ (eraseAux outside) (QueryCap.counted IsPrefixQuery computation) := by
  apply QueryCap.counted_simulateQ
  intro input
  cases input with
  | inl world =>
    cases world with
    | inl sample => simp only [eraseAux, QueryCap.counted_query, IsPrefixQuery, if_false]; rfl
    | inr query => simp only [eraseAux, QueryCap.counted_pure, IsPrefixQuery, if_false, map_pure]
  | inr query => simp only [eraseAux, QueryCap.counted_query, IsPrefixQuery, if_true]; rfl

theorem visibleSeedGame_counted_real (segment : OtsPrefix) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs segment.parameter ⊆ inputs) (hgraph : canonicalGraphInputs segment.parameter ⊆ inputs)
    (auxiliary : segment.ReferenceAuxSeed inputs hencoding hgraph) (secrets : OtsFrontierValues)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords) (adversary : Adversary) :
    realRun (fun endpoint => extendAux uniformImpl
      (segment.seedOracle inputs hencoding hgraph auxiliary secrets ftsSecret words endpoint))
      (fun endpoint => QueryCap.counted IsPrefixQuery
        (segment.visibleSeedGame inputs hencoding hgraph auxiliary secrets ftsSecret words adversary endpoint)) (fun _ _ => none) =
    realRun (fun _ => uniformImpl)
      (fun endpoint => QueryCap.counted IsPrefixQuery
        (segment.seedGame inputs hencoding hgraph auxiliary secrets ftsSecret words endpoint adversary)) (fun _ _ => none) := by
  simpa only [← counted_eraseAux, erase_visibleSeedGame] using
    (realRun_eraseAux (fun _ => uniformImpl)
      (segment.seedOracle inputs hencoding hgraph auxiliary secrets ftsSecret words)
      (fun endpoint => QueryCap.counted IsPrefixQuery
        (segment.visibleSeedGame inputs hencoding hgraph auxiliary secrets ftsSecret words adversary endpoint)) (fun _ _ => none)).symm

variable (segment : OtsPrefix) (stop : FrontierStop)
  [∀ parameter words frontier, DecidablePred (stop parameter words frontier)] (inputs : Finset HashInput)
  (hencoding : canonicalEncodingInputs segment.parameter ⊆ inputs) (hgraph : canonicalGraphInputs segment.parameter ⊆ inputs)
  (auxiliary : segment.ReferenceAuxSeed inputs hencoding hgraph) (secrets : OtsFrontierValues)
  (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords) (adversary : Adversary)

theorem traceCheckpoint_budget_of_counted (budget : Nat)
    (hreal : ∀ result ∈ (realRun (fun _ => uniformImpl)
      (fun endpoint => QueryCap.counted IsPrefixQuery
        (segment.seedGame inputs hencoding hgraph auxiliary secrets ftsSecret words endpoint adversary)) (fun _ _ => none)).support,
      result.2.1.2 ≤ budget)
    (hsmall : budget < Fintype.card Digest) (endpoint : Digest)
    (middle : ((OtsContactTrace.Trace × OracleComp segment.VisibleWorld (Bool × SigningBoundaryTrace)) × Nat) ×
      (Fin segment.digit.val → Digest → Option Digest))
    (hmiddle : middle ∈ (lazyRun (extendAux uniformImpl (segment.seedOracle inputs hencoding hgraph auxiliary secrets ftsSecret words endpoint))
      (segment.traceCheckpointBefore stop inputs hencoding hgraph auxiliary secrets ftsSecret words adversary endpoint) (fun _ _ => none)).support)
    (result : (((Bool × SigningBoundaryTrace) × OtsContactTrace.Trace) × Nat) × (Fin segment.digit.val → Digest → Option Digest))
    (hresult : result ∈ (lazyRun (extendAux uniformImpl (segment.seedOracle inputs hencoding hgraph auxiliary secrets ftsSecret words endpoint))
      (QueryCap.counted IsPrefixQuery (QueryPause.traced (segment.visibleObservationTrace auxiliary.high) middle.1.1.2)) middle.2).support) :
    queryCount middle.2 + result.1.2 ≤ budget ∧ queryCount result.2 ≤ budget := by
  let aux := fun endpoint => extendAux uniformImpl (segment.seedOracle inputs hencoding hgraph auxiliary secrets ftsSecret words endpoint)
  let program := segment.visibleSeedGame inputs hencoding hgraph auxiliary secrets ftsSecret words adversary
  have hreal' : ∀ result ∈ (realRun aux (fun endpoint => QueryCap.counted IsPrefixQuery (program endpoint))
      (fun _ _ => none)).support, result.2.1.2 ≤ budget := by
    rw [segment.visibleSeedGame_counted_real inputs hencoding hgraph auxiliary secrets ftsSecret words adversary]
    exact hreal
  have hresult' : ((result.1.1.1, result.1.2), result.2) ∈
      (lazyRun (aux endpoint) (QueryCap.counted IsPrefixQuery middle.1.1.2) middle.2).support := by
    have hforget := congrArg (fun computation => lazyRun (aux endpoint) computation middle.2)
      (QueryPause.traced_counted_forget (segment.visibleObservationTrace auxiliary.high) IsPrefixQuery middle.1.1.2)
    rw [lazyRun_map] at hforget
    rw [← hforget, PMF.mem_support_map_iff]
    exact ⟨result, hresult, rfl⟩
  exact lazyRun_pause_budget_of_counted_real aux program budget hreal' hsmall endpoint
    (stop segment.parameter words (segment.seedFrontier inputs hencoding hgraph auxiliary secrets words endpoint))
    (fun input answer history => history * segment.visibleObservationTrace auxiliary.high input answer)
    1 middle hmiddle ((result.1.1.1, result.1.2), result.2) hresult'

end SphincsSecurity.Concrete.OtsPrefix
