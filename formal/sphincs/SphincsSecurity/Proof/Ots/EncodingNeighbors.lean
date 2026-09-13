import SphincsSecurity.Proof.Scheme.Code
/-!
# Unit neighbors of a checksum encoding

A forgery that reuses a signed one-time key with a single backward chain step is a valid encoding one step below the signed encoding at one chain and nowhere else below it. Both checksum copies of a digit move together, so that chain is a message digit and the weighted digit sum forces the rest: either one other message digit rises by one, or both copies of the lowest checksum digit do. This bounds the neighbors of an encoding by 43 per lowered chain and by 1849 in total.
-/

namespace SphincsSecurity.Checksum

open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ

/-- `candidate` is a valid encoding one step below the valid `reference` at `lowered`, and nowhere else below it. -/
def UnitNeighborAt (reference candidate : Encoding) (lowered : ChainIndex) : Prop :=
  Valid reference ∧ Valid candidate ∧ (candidate lowered).val + 1 = (reference lowered).val ∧
    ∀ index, index ≠ lowered → (reference index).val ≤ (candidate index).val

theorem UnitNeighborAt.ne {reference candidate : Encoding} {lowered : ChainIndex}
    (h : UnitNeighborAt reference candidate lowered) : candidate ≠ reference := by
  intro he
  have hd := h.2.2.1
  rw [he] at hd
  omega

theorem UnitNeighborAt.lowered_unique {reference candidate : Encoding} {left right : ChainIndex}
    (hleft : UnitNeighborAt reference candidate left) (hright : UnitNeighborAt reference candidate right) : left = right := by
  by_contra hne
  have hle := hleft.2.2.2 right (Ne.symm hne)
  have hd := hright.2.2.1
  omega

/-- The other copy of a checksum digit. -/
theorem exists_copy (index : ChainIndex) (hindex : messageDigits ≤ index.val) :
    ∃ copy : ChainIndex, copy ≠ index ∧ ∀ x : Encoding, Repeated x → x copy = x index := by
  have hlt := index.isLt
  have hdigit : (index.val - messageDigits) / 2 < checksumDigits := by
    simp only [numChains] at hlt
    omega
  by_cases heven : index.val = messageDigits + 2 * ((index.val - messageDigits) / 2)
  · refine ⟨⟨messageDigits + 2 * ((index.val - messageDigits) / 2) + 1, by simp only [numChains] at hlt ⊢; omega⟩,
      fun he => ?_, fun x hx => ?_⟩
    · have hv := congrArg Fin.val he
      simp only at hv
      omega
    · exact (hx ⟨_, hdigit⟩).symm.trans (congrArg x (Fin.ext heven.symm))
  · refine ⟨⟨messageDigits + 2 * ((index.val - messageDigits) / 2), by simp only [numChains] at hlt ⊢; omega⟩,
      fun he => ?_, fun x hx => ?_⟩
    · exact heven (congrArg Fin.val he).symm
    · exact (hx ⟨_, hdigit⟩).trans (congrArg x (Fin.ext (by simp only; omega)))

theorem UnitNeighborAt.lowered_lt {reference candidate : Encoding} {lowered : ChainIndex}
    (h : UnitNeighborAt reference candidate lowered) : lowered.val < messageDigits := by
  by_contra hge
  obtain ⟨copy, hne, hcopy⟩ := exists_copy lowered (by omega)
  have hle := h.2.2.2 copy hne
  rw [hcopy reference h.1.2, hcopy candidate h.2.1.2] at hle
  have hd := h.2.2.1
  omega

private theorem two_terms_le_sum (f : ChainIndex → Nat) {left right : ChainIndex} (hne : left ≠ right) :
    f left + f right ≤ ∑ index, f index := by
  have h := Finset.sum_le_sum_of_subset_of_nonneg (f := f) (Finset.subset_univ ({left, right} : Finset ChainIndex))
    (fun _ _ _ => Nat.zero_le _)
  simpa only [Finset.sum_pair hne] using h

/-- The chain steps a unit neighbor gains weigh exactly as much as the step it loses. -/
theorem UnitNeighborAt.forward_sum {reference candidate : Encoding} {lowered : ChainIndex}
    (h : UnitNeighborAt reference candidate lowered) :
    ∑ index, weight index * ((candidate index).val - (reference index).val) = 2 := by
  have hlowered := h.lowered_lt
  obtain ⟨hreference, hcandidate, hlow, hup⟩ := h
  have hpoint : ∀ index : ChainIndex,
      weight index * (candidate index).val + weight index * ((reference index).val - (candidate index).val) =
        weight index * (reference index).val + weight index * ((candidate index).val - (reference index).val) := by
    intro index
    rw [← Nat.mul_add, ← Nat.mul_add]
    congr 1
    omega
  have hsum := congrArg (fun f : ChainIndex → Nat => ∑ index, f index) (funext hpoint)
  simp only [Finset.sum_add_distrib] at hsum
  have hback : ∑ index, weight index * ((reference index).val - (candidate index).val) = 2 := by
    rw [Finset.sum_eq_single lowered]
    · simp only [weight, if_pos hlowered]
      omega
    · intro index _ hne
      simp only [Nat.sub_eq_zero_of_le (hup index hne), Nat.mul_zero]
    · simp only [Finset.mem_univ, not_true_eq_false, false_implies]
  change sum candidate + _ = sum reference + _ at hsum
  rw [hcandidate.1, hreference.1, hback] at hsum
  omega

def lowChecksum : ChainIndex := ⟨messageDigits, by simp only [numChains, checksumDigits]; omega⟩

def lowChecksumCopy : ChainIndex := ⟨messageDigits + 1, by simp only [numChains, checksumDigits]; omega⟩

/-- The chains a unit neighbor raises, keyed by a message digit: that digit, or both copies of the lowest checksum digit when the key is the lowered chain itself. -/
def raisedAt (lowered : ChainIndex) (key : Fin messageDigits) : Finset ChainIndex :=
  if Fin.castLE (by simp only [numChains]; omega) key = lowered then {lowChecksum, lowChecksumCopy}
  else {Fin.castLE (by simp only [numChains]; omega) key}

/-- The digits of `reference` lowered once at `lowered` and raised once on `raised`. -/
def shift (reference : Encoding) (lowered : ChainIndex) (raised : Finset ChainIndex) (index : ChainIndex) : Nat :=
  if index = lowered then (reference index).val - 1
  else if index ∈ raised then (reference index).val + 1 else (reference index).val

theorem UnitNeighborAt.shape {reference candidate : Encoding} {lowered : ChainIndex}
    (h : UnitNeighborAt reference candidate lowered) :
    ∃ key, ∀ index, (candidate index).val = shift reference lowered (raisedAt lowered key) index := by
  have hlowered := h.lowered_lt
  have hforward := h.forward_sum
  obtain ⟨hreference, hcandidate, hlow, hup⟩ := h
  let step := fun index : ChainIndex => weight index * ((candidate index).val - (reference index).val)
  have hstep_le (index : ChainIndex) : step index ≤ 2 :=
    hforward ▸ Finset.single_le_sum (f := step) (fun _ _ => Nat.zero_le _) (Finset.mem_univ index)
  by_cases hraised : ∃ raised : ChainIndex, raised.val < messageDigits ∧ (reference raised).val < (candidate raised).val
  · obtain ⟨raised, hmessage, hlt⟩ := hraised
    have hne : raised ≠ lowered := by
      rintro rfl
      omega
    have hweight : weight raised = 2 := by simp only [weight, if_pos hmessage]
    have hone : (candidate raised).val = (reference raised).val + 1 := by
      have := hstep_le raised
      change weight raised * _ ≤ 2 at this
      rw [hweight] at this
      omega
    have hrest (index : ChainIndex) (hindex : index ≠ raised) : (candidate index).val - (reference index).val = 0 := by
      have hpair := two_terms_le_sum step (Ne.symm hindex)
      rw [hforward] at hpair
      change weight raised * _ + weight index * _ ≤ 2 at hpair
      rw [hweight] at hpair
      have hpos := weight_pos index
      rcases Nat.eq_zero_or_pos ((candidate index).val - (reference index).val) with hz | hz
      · exact hz
      · have := Nat.mul_le_mul_left (weight index) hz
        omega
    refine ⟨⟨raised.val, hmessage⟩, fun index => ?_⟩
    have hkey : (Fin.castLE (by simp only [numChains]; omega) (⟨raised.val, hmessage⟩ : Fin messageDigits) : ChainIndex) = raised :=
      Fin.ext rfl
    simp only [shift, raisedAt, hkey, if_neg hne, Finset.mem_singleton]
    split_ifs with hl hr
    · subst index
      omega
    · subst index
      exact hone
    · have := hrest index hr
      have := hup index hl
      omega
  · push Not at hraised
    have hmessage (index : ChainIndex) (hindex : index.val < messageDigits) :
        (candidate index).val - (reference index).val = 0 := by
      have := hraised index hindex
      omega
    have hhigh (index : ChainIndex) (hindex : messageDigits + 2 ≤ index.val) :
        (candidate index).val - (reference index).val = 0 := by
      have hweight : 8 ≤ weight index := by
        simp only [weight, if_neg (show ¬index.val < messageDigits by omega)]
        calc 8 = chainLength ^ 1 := by simp only [chainLength, winternitzBits]; norm_num
          _ ≤ chainLength ^ ((index.val - messageDigits) / 2) :=
            Nat.pow_le_pow_right (by simp only [chainLength, winternitzBits]; norm_num) (by omega)
      have := hstep_le index
      change weight index * _ ≤ 2 at this
      rcases Nat.eq_zero_or_pos ((candidate index).val - (reference index).val) with hz | hz
      · exact hz
      · have := Nat.mul_le_mul hweight hz
        omega
    have hcopies : lowChecksum ≠ lowChecksumCopy := by
      intro he
      have := congrArg Fin.val he
      simp only [lowChecksum, lowChecksumCopy] at this
      omega
    have hpair : step lowChecksum + step lowChecksumCopy = 2 := by
      rw [← hforward, Fintype.sum_eq_add lowChecksum lowChecksumCopy hcopies]
      intro index ⟨h1, h2⟩
      show weight index * ((candidate index).val - (reference index).val) = 0
      by_cases hindex : index.val < messageDigits
      · rw [hmessage index hindex, Nat.mul_zero]
      · have hv1 : index.val ≠ messageDigits := fun hv => h1 (Fin.ext hv)
        have hv2 : index.val ≠ messageDigits + 1 := fun hv => h2 (Fin.ext hv)
        rw [hhigh index (by omega), Nat.mul_zero]
    have hw1 : weight lowChecksum = 1 := by simp [weight, lowChecksum]
    have hw2 : weight lowChecksumCopy = 1 := by simp [weight, lowChecksumCopy]
    have hr : reference lowChecksum = reference lowChecksumCopy := hreference.2 ⟨0, by decide⟩
    have hc : candidate lowChecksum = candidate lowChecksumCopy := hcandidate.2 ⟨0, by decide⟩
    simp only [step, hw1, hw2, Nat.one_mul, hr, hc] at hpair
    refine ⟨⟨lowered.val, hlowered⟩, fun index => ?_⟩
    have hkey : (Fin.castLE (by simp only [numChains]; omega) (⟨lowered.val, hlowered⟩ : Fin messageDigits) : ChainIndex) = lowered :=
      Fin.ext rfl
    simp only [shift, raisedAt, hkey, if_true, Finset.mem_insert, Finset.mem_singleton]
    split_ifs with hl hr'
    · subst index
      omega
    · rcases hr' with rfl | rfl
      · rw [hc, hr]
        have := hup lowChecksumCopy (fun he => by
          have := congrArg Fin.val he
          simp only [lowChecksumCopy] at this
          omega)
        omega
      · have := hup lowChecksumCopy (fun he => by
          have := congrArg Fin.val he
          simp only [lowChecksumCopy] at this
          omega)
        omega
    · push Not at hr'
      have hzero : (candidate index).val - (reference index).val = 0 := by
        by_cases hindex : index.val < messageDigits
        · exact hmessage index hindex
        · have hv1 : index.val ≠ messageDigits := fun hv => hr'.1 (Fin.ext hv)
          have hv2 : index.val ≠ messageDigits + 1 := fun hv => hr'.2 (Fin.ext hv)
          exact hhigh index (by omega)
      have := hup index hl
      omega

noncomputable def unitNeighbors (reference : Encoding) (lowered : ChainIndex) : Finset Encoding :=
  Finset.univ.filter (fun candidate => UnitNeighborAt reference candidate lowered)

theorem mem_unitNeighbors {reference candidate : Encoding} {lowered : ChainIndex} :
    candidate ∈ unitNeighbors reference lowered ↔ UnitNeighborAt reference candidate lowered := by
  simp only [unitNeighbors, Finset.mem_filter, Finset.mem_univ, true_and]

theorem unitNeighbors_card_le (reference : Encoding) (lowered : ChainIndex) : (unitNeighbors reference lowered).card ≤ 43 := by
  have hinj : Set.InjOn (fun (candidate : Encoding) (index : ChainIndex) => (candidate index).val)
      (unitNeighbors reference lowered) := by
    intro left _ right _ he
    funext index
    exact Fin.ext (congrFun he index)
  rw [← Finset.card_image_of_injOn hinj]
  calc
    _ ≤ ((Finset.univ : Finset (Fin messageDigits)).image fun key => shift reference lowered (raisedAt lowered key)).card := by
      apply Finset.card_le_card
      intro values hvalues
      obtain ⟨candidate, hcandidate, rfl⟩ := Finset.mem_image.mp hvalues
      obtain ⟨key, hkey⟩ := (mem_unitNeighbors.mp hcandidate).shape
      exact Finset.mem_image.mpr ⟨key, Finset.mem_univ _, funext fun index => (hkey index).symm⟩
    _ ≤ (Finset.univ : Finset (Fin messageDigits)).card := Finset.card_image_le
    _ = 43 := by simp only [Finset.card_univ, Fintype.card_fin, messageDigits]

theorem unitNeighbors_eq_empty (reference : Encoding) {lowered : ChainIndex} (hlowered : messageDigits ≤ lowered.val) :
    unitNeighbors reference lowered = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro candidate hcandidate
  have := (mem_unitNeighbors.mp hcandidate).lowered_lt
  omega

noncomputable def allUnitNeighbors (reference : Encoding) : Finset Encoding :=
  Finset.univ.biUnion (unitNeighbors reference)

theorem mem_allUnitNeighbors {reference candidate : Encoding} :
    candidate ∈ allUnitNeighbors reference ↔ ∃ lowered, UnitNeighborAt reference candidate lowered := by
  simp only [allUnitNeighbors, Finset.mem_biUnion, Finset.mem_univ, true_and, mem_unitNeighbors]

theorem allUnitNeighbors_card_le (reference : Encoding) : (allUnitNeighbors reference).card ≤ 1849 := by
  calc
    _ ≤ ∑ lowered : ChainIndex, (unitNeighbors reference lowered).card := Finset.card_biUnion_le
    _ ≤ ∑ lowered : ChainIndex, if lowered.val < messageDigits then 43 else 0 := by
      apply Finset.sum_le_sum
      intro lowered _
      split_ifs with hlowered
      · exact unitNeighbors_card_le reference lowered
      · rw [unitNeighbors_eq_empty reference (by omega), Finset.card_empty]
    _ = 1849 := by
      change ∑ lowered : Fin (messageDigits + 2 * checksumDigits), _ = _
      rw [Fin.sum_univ_add]
      simp [messageDigits, checksumDigits]

end SphincsSecurity.Checksum
