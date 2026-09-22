import SphincsSecurity.Proof.Forced.FtsGuessTruncation

namespace SphincsSecurity.Concrete.FtsGuessHash
open OracleComp OracleSpec
open RetainedResidual (IsSigningRequest)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] hashInputs coveredInputs canonicalGraphGameInputs
set_option backward.isDefEq.respectTransparency false

private theorem hashInputs_bind_subset {α β : Type} (first : OracleComp OracleWorld α)
    (next : α → OracleComp OracleWorld β) (inputs : Finset HashInput)
    (hf : hashInputs first ⊆ inputs) (hn : ∀ value ∈ support first, hashInputs (next value) ⊆ inputs) :
    hashInputs (first >>= next) ⊆ inputs := by
  induction first using OracleComp.inductionOn with
  | pure value =>
      rw [pure_bind]
      exact hn value (by simp)
  | query_bind input tail ih =>
      rw [hashInputs_query_bind] at hf
      rw [bind_assoc, hashInputs_query_bind]
      apply Finset.union_subset
      · cases input <;> exact (Finset.subset_union_left).trans hf
      · intro row hr
        obtain ⟨answer, _, hr⟩ := Finset.mem_biUnion.mp hr
        apply ih answer _ _ hr
        · exact (Finset.Subset.trans (Finset.subset_biUnion_of_mem _ (Finset.mem_univ answer)) Finset.subset_union_right).trans hf
        · intro value hv
          exact hn value ((mem_support_bind_iff _ _ _).mpr ⟨answer, mem_support_query _ _, hv⟩)

theorem coveredInputs_truncate_subset (key : SecretKey) (computation : OracleComp (OracleWorld + SigningSpec) Forgery)
    (cap : Nat) (fallback : Forgery) (inputs : Finset HashInput)
    (hcomp : coveredInputs key computation ⊆ inputs) (hf : coveredInputs key (pure fallback) ⊆ inputs) :
    coveredInputs key (QueryCap.truncate IsSigningRequest computation cap fallback) ⊆ inputs := by
  induction computation using OracleComp.inductionOn generalizing cap with
  | pure value => simpa only [QueryCap.truncate_pure] using hcomp
  | query_bind input next ih =>
      rw [QueryCap.truncate_query_bind]
      have step (remaining : Nat) : coveredInputs key
          (liftM ((OracleWorld + SigningSpec).query input) >>=
            fun answer => QueryCap.truncate IsSigningRequest (next answer) remaining fallback) ⊆ inputs := by
        rw [coveredInputs_query_bind] at hcomp ⊢
        apply hashInputs_bind_subset
        · exact (ResidualByteFrontend.hashInputs_left_subset _ _).trans hcomp
        · intro answer ha
          have hn : coveredInputs key (next answer) ⊆ inputs := by
            rw [coveredInputs]
            exact (hashInputs_bind_of_mem_support _ _ answer ha).trans hcomp
          simpa only [coveredInputs] using ih answer remaining hn
      by_cases hs : IsSigningRequest input
      · rw [if_pos hs]
        cases cap with
        | zero => exact hf
        | succ cap => exact step cap
      · rw [if_neg hs]
        exact step cap

theorem coveredInputs_signingTruncated_subset (adversary : Adversary) (key : SecretKey) :
    coveredInputs key ((signingTruncatedAdversary adversary).main ⟨key.root, key.parameter⟩) ⊆
      canonicalGraphGameInputs adversary := by
  apply coveredInputs_truncate_subset key _ signatureLimit zeroForgery _ (coveredInputs_main_subset adversary key)
  rw [coveredInputs_pure]
  exact zeroForgery_verify_inputs_subset adversary ⟨key.root, key.parameter⟩

end SphincsSecurity.Concrete.FtsGuessHash
