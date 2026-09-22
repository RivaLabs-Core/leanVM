import SphincsSecurity.Proof.Reference.HonestHashAllowance
import SphincsSecurity.Proof.Reference.VerifierTraceSource

namespace SphincsSecurity.Concrete
open OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false

private theorem sequenceFin_query_bound {α : Type} {n : Nat}
    (computation : Fin n → OracleComp HashSpec α) (cost : Nat)
    (h : ∀ index, (computation index).IsQueryBoundP (fun _ => True) cost) :
    (sequenceFin computation).IsQueryBoundP (fun _ => True) (n * cost) := by
  induction n with
  | zero => simp only [sequenceFin, Nat.zero_mul, isQueryBoundP_pure]
  | succ n ih =>
      rw [sequenceFin, show (n + 1) * cost = cost + n * cost by ring]
      apply isQueryBoundP_bind (h 0)
      intro head _
      simp only [bind_pure_comp, isQueryBoundP_map_iff]
      exact ih _ (fun index => h index.succ)

private theorem tweakableHash_query_bound (parameter : PublicParameter) (domain : HashDomain) (payload : HashInput) :
    (tweakableHash parameter domain payload : OracleComp HashSpec _).IsQueryBoundP (fun _ => True) 1 := by
  change ((liftM (HashSpec.query _) >>= fun output => pure (truncateHash output)) : OracleComp HashSpec _).IsQueryBoundP (fun _ => True) 1
  simp only [isQueryBoundP_query_bind_iff, not_true_eq_false, false_or, Nat.zero_lt_succ,
    if_true, Nat.sub_self, isQueryBoundP_pure, implies_true, and_self]

private theorem chainWalk_query_bound (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (chainIdx : ChainIndex) (start steps : Nat) (value : Digest) :
    (chainWalk parameter lay tree leaf chainIdx start steps value : OracleComp HashSpec _).IsQueryBoundP (fun _ => True) steps := by
  induction steps with
  | zero => simp only [chainWalk, isQueryBoundP_pure]
  | succ steps ih =>
      rw [chainWalk]
      apply isQueryBoundP_bind ih
      intro previous _
      split
      · exact tweakableHash_query_bound _ _ _
      · exact isQueryBoundP_pure _ _ _

private theorem treeFold_query_bound (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (path : Nat → Digest) (levels : Nat) (value : Digest) :
    (treeFold parameter lay tree leaf path levels value : OracleComp HashSpec _).IsQueryBoundP (fun _ => True) levels := by
  induction levels with
  | zero => simp only [treeFold, isQueryBoundP_pure]
  | succ levels ih =>
      rw [treeFold]
      apply isQueryBoundP_bind ih
      intro current _
      split <;> exact tweakableHash_query_bound _ _ _

private theorem ftsFold_query_bound (parameter : PublicParameter) (index : Index) (tree : FtsTree) (leaf : FtsLeaf)
    (path : Fin ftsTreeHeight → Digest) (levels : Nat) (value : Digest) :
    (ftsFold parameter index tree leaf path levels value : OracleComp HashSpec _).IsQueryBoundP (fun _ => True) levels := by
  induction levels with
  | zero => simp only [ftsFold, isQueryBoundP_pure]
  | succ levels ih =>
      rw [ftsFold]
      apply isQueryBoundP_bind ih
      intro current _
      dsimp only
      split <;> exact tweakableHash_query_bound _ _ _

private theorem otsLeaf_query_bound (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : Digest) (counter : Counter) (values : ChainIndex → Digest) :
    (otsLeaf parameter lay tree leaf message counter values : OracleComp HashSpec _).IsQueryBoundP (fun _ => True) 296 := by
  rw [otsLeaf, show 296 = 1 + 295 from rfl]
  apply isQueryBoundP_bind
  · simpa only [encode, bind_pure_comp, isQueryBoundP_map_iff] using
      tweakableHash_query_bound parameter (.encoding lay tree leaf) (bytesLE 16 message ++ bytesLE 4 counter)
  · intro encoded _
    cases encoded with
    | none => exact isQueryBoundP_pure _ _ _
    | some word =>
      change (sequenceFin (fun chainIdx => recoverChain parameter lay tree leaf chainIdx (word chainIdx) (values chainIdx)) >>=
        fun endpoints => pure <$> leafHash parameter lay tree leaf endpoints : OracleComp HashSpec _).IsQueryBoundP (fun _ => True) (294 + 1)
      apply isQueryBoundP_bind
      · apply sequenceFin_query_bound _ 7
        intro chainIdx
        exact (chainWalk_query_bound parameter lay tree leaf chainIdx _ _ _).mono (by
          norm_num [chainLength, winternitzBits])
      · intro endpoints _
        simp only [isQueryBoundP_map_iff]
        exact tweakableHash_query_bound _ _ _

private theorem ftsRecover_query_bound (parameter : PublicParameter) (index : Index) (leaves : IndexGroup → FtsLeaf)
    (secrets : FtsTree → Digest) (paths : FtsTree → Fin ftsTreeHeight → Digest) :
    (ftsRecover parameter index leaves secrets paths : OracleComp HashSpec _).IsQueryBoundP (fun _ => True) 155 := by
  rw [ftsRecover, show 155 = 154 + 1 from rfl]
  apply isQueryBoundP_bind
  · apply sequenceFin_query_bound _ 11
    intro tree
    dsimp only
    rw [ftsLeafHash, show 11 = 1 + 10 from rfl]
    apply isQueryBoundP_bind (tweakableHash_query_bound _ _ _)
    intro value _
    exact ftsFold_query_bound _ _ _ _ _ _ _
  · intro roots _
    exact tweakableHash_query_bound _ _ _

private theorem verifyLayers_query_bound (parameter : PublicParameter) (index : Index) (signature : Signature)
    (remaining : Nat) (message : Digest) :
    (verifyLayers parameter index signature remaining message : OracleComp HashSpec _).IsQueryBoundP (fun _ => True) (remaining * 512) := by
  induction remaining generalizing message with
  | zero => simp only [verifyLayers, Nat.zero_mul, isQueryBoundP_pure]
  | succ remaining ih =>
    rw [verifyLayers]
    split
    · rename_i hlayer
      apply IsQueryBoundP.mono (n := 296 + (12 + remaining * 512))
      · apply isQueryBoundP_bind (otsLeaf_query_bound _ _ _ _ _ _ _)
        intro leaf _
        cases leaf with
        | none => exact isQueryBoundP_pure _ _ _
        | some value =>
          apply isQueryBoundP_bind
          · exact (treeFold_query_bound _ _ _ _ _ _ _).mono (layerHeight_le _)
          · intro root _
            exact ih root
      · omega
    · exact isQueryBoundP_pure _ _ _

theorem verify_hash_query_bound (publicKey : PublicKey) (message : Message) (signature : Signature) :
    (verify publicKey message signature : OracleComp HashSpec _).IsQueryBoundP (fun _ => True) (2 ^ 16) := by
  rw [verify]
  apply IsQueryBoundP.mono (n := 1 + (155 + numLayers * 512))
  · apply isQueryBoundP_bind
    · change ((liftM (HashSpec.query _) >>= fun output => pure (truncateMessageDigest output)) : OracleComp HashSpec _).IsQueryBoundP (fun _ => True) 1
      simp only [isQueryBoundP_query_bind_iff, not_true_eq_false, false_or, Nat.zero_lt_succ,
        if_true, Nat.sub_self, isQueryBoundP_pure, implies_true, and_self]
    · intro digest _
      split
      · exact isQueryBoundP_pure _ _ _
      · apply isQueryBoundP_bind (ftsRecover_query_bound _ _ _ _ _)
        intro root _
        apply IsQueryBoundP.mono (n := numLayers * 512 + 0)
        · apply isQueryBoundP_bind (verifyLayers_query_bound _ _ _ _ _)
          intro checked _
          cases checked <;> exact isQueryBoundP_pure _ _ _
        · omega
  · decide

theorem boundaryEval_hashCalls_le_query_bound {α : Type} (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (computation : OracleComp HashSpec α) (q : Nat) (hq : computation.IsQueryBoundP (fun _ => True) q) :
    (boundaryEval parameter f computation).2.hashCalls ≤ q := by
  induction computation using OracleComp.inductionOn generalizing q with
  | pure value => simp only [boundaryEval_pure]; exact Nat.zero_le _
  | query_bind input next ih =>
    simp only [isQueryBoundP_query_bind_iff, not_true_eq_false, false_or, if_true] at hq
    rw [boundaryEval_bind, boundaryEval_hash_query]
    simp only [SigningBoundaryTrace.hashCalls_mul]
    rw [show evalWithAnswerFn f (liftM (HashSpec.query input) : OracleComp HashSpec _) = f input from rfl]
    have h := ih (f input) (q - 1) (hq.2 (f input))
    have hquery : (signingBoundaryTrace parameter (.inr input) (f input)).hashCalls = 1 := rfl
    rw [hquery]
    omega

theorem answerTrace_length_le_query_bound {α : Type} (f : QueryImpl HashSpec Id)
    (computation : OracleComp HashSpec α) (q : Nat) (hq : computation.IsQueryBoundP (fun _ => True) q) :
    (OtsContactTrace.answerTrace f computation).toList.length ≤ q := by
  simp only [OtsContactTrace.answerTrace, FreeMonoid.toList_ofList, List.length_map]
  induction computation using OracleComp.inductionOn generalizing q with
  | pure value => simp only [queriedInputs_pure, List.length_nil]; exact Nat.zero_le _
  | query_bind input next ih =>
    simp only [isQueryBoundP_query_bind_iff, not_true_eq_false, false_or, if_true] at hq
    rw [queriedInputs_query_bind, List.length_cons]
    have h := ih (f input) (q - 1) (hq.2 (f input))
    omega

end SphincsSecurity.Concrete
