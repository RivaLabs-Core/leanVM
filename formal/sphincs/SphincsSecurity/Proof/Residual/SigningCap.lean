import SphincsSecurity.Proof.Base.StatefulQueryCap
import SphincsSecurity.Proof.Residual.InterfaceInitialBudget

namespace SphincsSecurity.Concrete.RetainedResidual
open OracleComp OracleSpec CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] sourceInputs hashInputs

def IsSigningRequest : (OracleWorld + SigningSpec).Domain → Prop
  | .inl _ => False
  | .inr _ => True

noncomputable def signingCap {α : Type} (computation : OracleComp (OracleWorld + SigningSpec) α) :
    OracleComp (OracleWorld + SigningSpec) (Option (α × Nat)) :=
  QueryCap.run IsSigningRequest computation signatureLimit

theorem sourceInputs_queryCap_subset {α : Type} (key : SecretKey)
    (selected : (OracleWorld + SigningSpec).Domain → Prop) [DecidablePred selected]
    (computation : OracleComp (OracleWorld + SigningSpec) α) (cap : Nat) :
    sourceInputs key (QueryCap.run selected computation cap) ⊆ sourceInputs key computation := by
  induction computation using OracleComp.inductionOn generalizing cap with
  | pure value => simp only [QueryCap.run_pure, sourceInputs_pure, Finset.Subset.refl]
  | query_bind input next ih =>
      rw [QueryCap.run_query_bind]
      have step (remaining : Nat) :
          sourceInputs key (liftM ((OracleWorld + SigningSpec).query input) >>=
            fun answer => QueryCap.run selected (next answer) remaining) ⊆
              sourceInputs key (liftM ((OracleWorld + SigningSpec).query input) >>= next) := by
        rw [sourceInputs_query_bind, sourceInputs_query_bind]
        exact Finset.union_subset_union_right (Finset.biUnion_mono (fun answer _ => ih answer remaining))
      by_cases hs : selected input
      · rw [if_pos hs]
        cases cap with
        | zero => simp only [sourceInputs_pure, Finset.empty_subset]
        | succ cap => exact step cap
      · rw [if_neg hs]
        exact step cap

theorem Context.capped_interface_bound {inputs : Finset HashInput} (context : Context inputs)
    (hroot : context.key.root = canonicalGraphRoot context.graph) (original : Security.Adversary)
    (q : Nat) (hsmall : q < 2 ^ 256) (hq : Security.HasHashQueryBound original q) :
    ∀ result ∈ support (simulateQ context.interfaceImpl (QueryCap.counted Security.IsAdversaryHash
      (signingCap (FtsProbeSimulation.unloggedRetainedRestComputation
        (Seeded.memoAdversary (Security.embed original)) ⟨context.key.root, context.key.parameter⟩)))), result.2 ≤ q :=
  QueryCap.counted_run_bound IsSigningRequest Security.IsAdversaryHash context.interfaceImpl _ signatureLimit q
    (context.interface_bound hroot original q hsmall hq)

end SphincsSecurity.Concrete.RetainedResidual
