import SphincsSecurity.Proof.Base.Uncharged
import SphincsSecurity.Proof.Deterministic.DerivationQueries
import SphincsSecurity.Proof.Deterministic.TableSigner

namespace SphincsSecurity.Seeded

open OracleComp OracleSpec Concrete
open QueryCap (Uncharged)
set_option backward.isDefEq.respectTransparency false

abbrev DerivationFree {α : Type} (computation : OracleComp HashSpec α) :=
  Uncharged (selected := IsDerivationQuery) computation

theorem derivationFree_tweakableHash (parameter : PublicParameter) (domain : HashDomain) (payload : HashInput) :
    DerivationFree (Concrete.tweakableHash parameter domain payload) := by
  unfold Concrete.tweakableHash Concrete.oracleHash
  apply Uncharged.bind (Uncharged.query_pure _ (not_isDerivationQuery_tweakable parameter domain payload))
  intro output
  exact .pure _

theorem derivationFree_sequenceFin {α : Type} {n : Nat} (computation : Fin n → OracleComp HashSpec α)
    (hcomputation : ∀ index, DerivationFree (computation index)) : DerivationFree (sequenceFin computation) := by
  induction n with
  | zero => exact .pure _
  | succ n ih =>
    rw [sequenceFin]
    apply Uncharged.bind (hcomputation 0)
    intro first
    apply Uncharged.bind (ih (fun index => computation index.succ) (fun index => hcomputation index.succ))
    intro rest
    exact .pure _

theorem derivationFree_chainWalk (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (chain : ChainIndex) (start steps : Nat) (value : Digest) :
    DerivationFree (chainWalk parameter lay tree leaf chain start steps value) := by
  induction steps generalizing start value with
  | zero => exact .pure _
  | succ steps ih =>
    rw [chainWalk]
    apply Uncharged.bind (ih start value)
    intro previous
    split
    · exact derivationFree_tweakableHash parameter _ _
    · exact .pure _

theorem derivationFree_oneTimePublicKey (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (secret : ChainIndex → Digest) : DerivationFree (Concrete.oneTimePublicKey parameter lay tree leaf secret) :=
  derivationFree_sequenceFin _ (fun chain => derivationFree_chainWalk parameter lay tree leaf chain _ _ _)

theorem derivationFree_treeNode (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainIndex → Digest) (level node : Nat) :
    DerivationFree (Concrete.treeNode parameter lay tree secret level node) := by
  induction level generalizing node with
  | zero =>
    rw [Concrete.treeNode_zero_eq]
    apply Uncharged.bind (derivationFree_oneTimePublicKey parameter lay tree _ _)
    intro endpoints
    exact derivationFree_tweakableHash parameter _ _
  | succ level ih =>
    rw [Concrete.treeNode_succ_eq]
    apply Uncharged.bind (ih _)
    intro left
    apply Uncharged.bind (ih _)
    intro right
    exact derivationFree_tweakableHash parameter _ _

theorem derivationFree_treeRoot (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainIndex → Digest) : DerivationFree (Concrete.treeRoot parameter lay tree secret) :=
  derivationFree_treeNode parameter lay tree secret _ _

theorem derivationFree_treePath (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainIndex → Digest) (leaf : LeafIndex) : DerivationFree (Concrete.treePath parameter lay tree secret leaf) := by
  apply derivationFree_sequenceFin
  intro level
  split
  · exact derivationFree_treeNode parameter lay tree secret _ _
  · exact .pure _

theorem derivationFree_encode (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (message : Digest) (counter : Counter) : DerivationFree (encodeAttempt parameter lay tree leaf message counter) := by
  rw [encodeAttempt]
  apply Uncharged.bind (derivationFree_tweakableHash parameter _ _)
  intro value
  exact .pure _

theorem derivationFree_otsSignFrom (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (secret : ChainIndex → Digest) (message : Digest) (attempts counter : Nat) :
    DerivationFree (Concrete.otsSignFrom parameter lay tree leaf secret message attempts counter) := by
  induction attempts generalizing counter with
  | zero => exact .pure _
  | succ attempts ih =>
    rw [Concrete.otsSignFrom]
    apply Uncharged.bind (derivationFree_encode parameter lay tree leaf message _)
    intro encoding
    cases encoding with
    | none => exact ih _
    | some encoding =>
      apply Uncharged.bind (derivationFree_sequenceFin _ (fun chain => derivationFree_chainWalk parameter lay tree leaf chain _ _ _))
      intro values
      exact .pure _

theorem derivationFree_ftsNode (parameter : PublicParameter) (index : Index) (tree : FtsTree)
    (secret : FtsLeaf → Digest) (level node : Nat) : DerivationFree (Concrete.ftsNode parameter index tree secret level node) := by
  induction level generalizing node with
  | zero =>
    rw [Concrete.ftsNode_zero_eq]
    exact derivationFree_tweakableHash parameter _ _
  | succ level ih =>
    rw [Concrete.ftsNode_succ_eq]
    apply Uncharged.bind (ih _)
    intro left
    apply Uncharged.bind (ih _)
    intro right
    exact derivationFree_tweakableHash parameter _ _

theorem derivationFree_ftsKey (parameter : PublicParameter) (index : Index) (secret : FtsTree → FtsLeaf → Digest) :
    DerivationFree (Concrete.ftsKey parameter index secret) := by
  rw [Concrete.ftsKey]
  apply Uncharged.bind (derivationFree_sequenceFin _ (fun tree => derivationFree_ftsNode parameter index tree (secret tree) _ _))
  intro roots
  exact derivationFree_tweakableHash parameter _ _

theorem derivationFree_ftsOpen (parameter : PublicParameter) (index : Index) (leaves : IndexGroup → FtsLeaf)
    (secret : FtsTree → FtsLeaf → Digest) : DerivationFree (Concrete.ftsOpen parameter index leaves secret) :=
  derivationFree_sequenceFin _ (fun tree => derivationFree_sequenceFin _
    (fun level => derivationFree_ftsNode parameter index tree (secret tree) level.val _))

theorem derivationFree_layerMessage (key : SphincsSecurity.SecretKey) (index : Index) (lay : Layer) :
    DerivationFree (Concrete.layerMessage key index lay) := by
  rw [Concrete.layerMessage]
  split
  · exact derivationFree_treeRoot _ _ _ _
  · exact derivationFree_ftsKey _ _ _

theorem derivationFree_signLayer (key : SphincsSecurity.SecretKey) (index : Index) (lay : Layer) :
    DerivationFree (Concrete.signLayer key index lay) := by
  rw [Concrete.signLayer]
  apply Uncharged.bind (derivationFree_layerMessage key index lay)
  intro message
  apply Uncharged.bind (derivationFree_otsSignFrom _ _ _ _ _ message _ _)
  intro signed
  cases signed with
  | none => exact .pure _
  | some parts =>
    apply Uncharged.bind (derivationFree_treePath _ _ _ _ _)
    intro path
    exact .pure _

theorem derivationFree_sequenceLayers {α : Layer → Type} (computation : (lay : Layer) → OracleComp HashSpec (Option (α lay)))
    (hcomputation : ∀ lay, DerivationFree (computation lay)) : DerivationFree (sequenceLayers computation) := by
  unfold sequenceLayers
  apply Uncharged.bind (hcomputation bottomLayer)
  intro bottom
  cases bottom with
  | none => exact .pure _
  | some bottom =>
    apply Uncharged.bind (hcomputation middleLayer)
    intro middle
    cases middle with
    | none => exact .pure _
    | some middle =>
      apply Uncharged.bind (hcomputation topLayer)
      intro top
      cases top <;> exact .pure _

theorem derivationFree_tableDigestLoop (randomizers : RandomizerOutputs) (key : SphincsSecurity.SecretKey)
    (message : Message) (attempts trial : Nat) : DerivationFree (tableDigestLoop randomizers key message attempts trial) := by
  induction attempts generalizing trial with
  | zero => exact .pure _
  | succ attempts ih =>
    rw [tableDigestLoop]
    apply Uncharged.bind
    · unfold Concrete.signAttempt Concrete.messageDigest Concrete.oracleHash
      simp only [bind_assoc, pure_bind]
      apply Uncharged.bind (Uncharged.query_pure _ (not_isDerivationQuery_tweakable key.parameter .message _))
      intro output
      split <;> exact .pure _
    intro attempt
    cases attempt with
    | none => exact ih _
    | some attempt => exact .pure _

theorem derivationFree_tableSign (randomizers : RandomizerOutputs) (key : SphincsSecurity.SecretKey) (message : Message) :
    DerivationFree (tableSign randomizers key message) := by
  rw [tableSign]
  apply Uncharged.bind (derivationFree_tableDigestLoop randomizers key message _ _)
  intro attempt
  cases attempt with
  | none => exact .pure _
  | some attempt =>
    rcases attempt with ⟨randomness, index, leaves⟩
    apply Uncharged.bind (derivationFree_ftsOpen key.parameter index leaves _)
    intro path
    apply Uncharged.bind (derivationFree_sequenceLayers _ (fun lay => derivationFree_signLayer key index lay))
    intro layers
    cases layers with
    | none => exact .pure _
    | some parts =>
      apply Uncharged.bind (derivationFree_treeRoot key.parameter topLayer Concrete.rootTree _)
      intro root
      exact .pure _


theorem DerivationFree.lift_world {α : Type} {computation : OracleComp HashSpec α} (h : DerivationFree computation) :
    Uncharged (selected := hashBad IsDerivationQuery) (liftM computation : OracleComp OracleWorld α) := by
  induction h with
  | pure value => simpa only [liftM_pure] using Uncharged.pure value
  | query input hfree next _ ih =>
    simp only [liftM_bind]
    exact Uncharged.query (spec := OracleWorld) (selected := hashBad IsDerivationQuery) (Sum.inr input) hfree _ ih

end SphincsSecurity.Seeded
