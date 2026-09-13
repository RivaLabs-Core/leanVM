import SphincsSecurity.Proof.Ots.Interface
import SphincsSecurity.Proof.Base.Prelude

namespace SphincsSecurity.Checksum

/-- The positional weights of the checksum digits. Message digits have weight two. -/
def weight (i : ChainIndex) : Nat :=
  if i.val < messageDigits then 2 else chainLength ^ ((i.val - messageDigits) / 2)

def sum (x : Encoding) : Nat := ∑ i, weight i * (x i).val

/-- The chain steps a signer walks to reveal `x`. -/
def signingSteps (x : Encoding) : Nat := ∑ i, (x i).val

def Repeated (x : Encoding) : Prop :=
  ∀ j : Fin checksumDigits,
    x ⟨messageDigits + 2 * j.val, by have := j.isLt; unfold numChains; omega⟩ =
      x ⟨messageDigits + 2 * j.val + 1, by have := j.isLt; unfold numChains; omega⟩

instance (x : Encoding) : Decidable (Repeated x) := by
  unfold Repeated
  infer_instance

def Valid (x : Encoding) : Prop :=
  sum x = 2 * messageDigits * (chainLength - 1) ∧ Repeated x

instance : DecidablePred Valid := fun x => inferInstanceAs (Decidable (_ ∧ Repeated x))

abbrev digestEncoding := encode

theorem weight_pos (i : ChainIndex) : 0 < weight i := by
  unfold weight
  split
  · decide
  · exact Nat.pow_pos (Nat.two_pow_pos _)

theorem checksum_balance (digest : Digest) :
    value digest + (∑ i : Fin messageDigits, (messageDigit digest i).val) =
      messageDigits * (chainLength - 1) := by
  rw [value, ← Finset.sum_add_distrib]
  calc
    _ = ∑ _i : Fin messageDigits, (chainLength - 1) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Nat.sub_add_cancel
      have hi := (messageDigit digest i).isLt
      omega
    _ = _ := by simp

theorem encode_valid (digest : Digest) : Valid (encode digest) := by
  have balance := checksum_balance digest
  have bound : value digest < 512 := by
    norm_num [messageDigits, chainLength, winternitzBits] at balance
    omega
  constructor
  · unfold sum
    change (∑ i : Fin (messageDigits + 2 * checksumDigits), weight i * (encode digest i).val) = _
    rw [Fin.sum_univ_add]
    have head : (∑ i : Fin messageDigits,
        weight (Fin.castAdd (2 * checksumDigits) i) * (encode digest (Fin.castAdd (2 * checksumDigits) i)).val) =
        2 * ∑ i : Fin messageDigits, (messageDigit digest i).val := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp [weight, encode, i.isLt]
    rw [head]
    have tail : (∑ i : Fin (2 * checksumDigits),
        weight (Fin.natAdd messageDigits i) * (encode digest (Fin.natAdd messageDigits i)).val) = 2 * value digest := by
      change (∑ i : Fin 6, _) = _
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
      norm_num [weight, encode, messageDigits, chainLength, winternitzBits]
      omega
    rw [tail]
    norm_num [messageDigits, chainLength, winternitzBits] at balance ⊢
    omega
  · intro j
    apply Fin.ext
    have hj := j.isLt
    simp [encode, show ¬messageDigits + 2 * j.val < messageDigits by omega,
      show ¬messageDigits + 2 * j.val + 1 < messageDigits by omega,
      show messageDigits + 2 * j.val + 1 - messageDigits = 2 * j.val + 1 by omega,
      show (2 * j.val + 1) / 2 = j.val by omega]

theorem valid_of_decodeDigest_eq_some {digest : Digest} {encoding : Encoding}
    (hdecode : decodeDigest digest = some encoding) : Valid encoding := by
  rw [decodeDigest_eq] at hdecode
  cases Option.some.inj hdecode
  exact encode_valid digest

theorem decodeDigest_some_injective {left right : Digest} {encoding : Encoding}
    (hleft : decodeDigest left = some encoding) (hright : decodeDigest right = some encoding) : left = right := by
  rw [decodeDigest_eq] at hleft hright
  have he := (Option.some.inj hleft).trans (Option.some.inj hright).symm
  apply BitVec.eq_of_getLsbD_eq
  intro bit hbit
  have hd : bit / 3 < messageDigits := by
    norm_num [digestBits, messageDigits] at *
    omega
  let i : ChainIndex := ⟨bit / 3, by unfold numChains; omega⟩
  have hi := congrFun he i
  simp only [encode, i, dif_pos hd, messageDigit] at hi
  have hw := BitVec.toFin_injective hi
  have hb := congrArg (fun b : BitVec winternitzBits => b.getLsbD (bit % 3)) hw
  have hmod : bit % 3 < 3 := by omega
  simpa only [BitVec.getLsbD_extractLsb', winternitzBits, hmod, decide_true, Bool.true_and,
     show 3 * (bit / 3) + bit % 3 = bit by omega] using hb

theorem eq_of_le_of_sum_eq {x y : Encoding} (hle : ∀ i, (x i).val ≤ (y i).val)
    (hsum : sum x = sum y) : x = y := by
  funext i
  apply Fin.ext
  by_contra hne
  have hstrict : (x i).val < (y i).val := by have := hle i; omega
  have : sum x < sum y := by
    apply Finset.sum_lt_sum
    · intro j _
      exact Nat.mul_le_mul_left _ (hle j)
    · exact ⟨i, Finset.mem_univ i, Nat.mul_lt_mul_of_pos_left hstrict (weight_pos i)⟩
  omega

theorem eq_of_le_of_valid {x y : Encoding} (hx : Valid x) (hy : Valid y)
    (hle : ∀ i, (x i).val ≤ (y i).val) : x = y :=
  eq_of_le_of_sum_eq hle (hx.1.trans hy.1.symm)

end SphincsSecurity.Checksum
