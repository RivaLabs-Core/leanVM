import SphincsSecurity.Proof.Fts.MessageAdmissibleDeficit

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem messageDigestFreshRate_ne_zero_of_count (key : SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (hcount : cachedMessageEntryCount cache key.parameter key.root message + digestAttemptLimit <
      ((2 ^ randomnessBits : Nat) : ENNReal)) : messageDigestFreshRate key message cache ≠ 0 := by
  unfold messageDigestFreshRate
  apply mul_ne_zero _ (ENNReal.inv_ne_zero.mpr (by finiteness))
  apply ne_of_gt (tsub_pos_iff_lt.mpr _)
  exact (ENNReal.mul_lt_mul_left (a := (((2 ^ randomnessBits : Nat) : ENNReal))⁻¹)
    (ENNReal.inv_ne_zero.mpr (by finiteness)) (ENNReal.inv_ne_top.mpr (by positivity)) hcount) |>.trans_eq
    (ENNReal.mul_inv_cancel (by positivity) (by finiteness))

theorem messageDigestReuseWeight_ne_top_of_count (key : SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (hcount : cachedMessageEntryCount cache key.parameter key.root message + digestAttemptLimit <
      ((2 ^ randomnessBits : Nat) : ENNReal)) : messageDigestReuseWeight key message cache ≠ ⊤ := by
  unfold messageDigestReuseWeight
  exact ENNReal.div_ne_top (by finiteness) (messageDigestFreshRate_ne_zero_of_count key message cache hcount)

theorem exactDigestReuseWeight_le_fresh_mul_messageReuseWeight_of_count
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (hbudget : cachedMessageEntryCount cache key.parameter key.root message + digestAttemptLimit <
      ((2 ^ randomnessBits : Nat) : ENNReal)) :
    exactDigestReuseWeight key message cache ≤ freshDigestSelectionProbability key message cache * messageDigestReuseWeight key message cache := by
  have hcancel : messageDigestFreshRate key message cache * messageDigestReuseWeight key message cache =
      ((2 ^ randomnessBits : Nat) : ENNReal)⁻¹ := by
    unfold messageDigestReuseWeight
    rw [div_eq_mul_inv, mul_left_comm, ENNReal.mul_inv_cancel
      (messageDigestFreshRate_ne_zero_of_count key message cache hbudget) (messageDigestFreshRate_ne_top key message cache), mul_one]
  have h := mul_le_mul' (digestAttemptExpectation_mul_message_rate_le_freshSelection digestAttemptLimit key message cache cache le_rfl
    (cachedMessageEntryCount cache key.parameter key.root message + (digestAttemptLimit : ENNReal))
    (messageDigestFreshRate key message cache) le_rfl le_rfl) (le_refl (messageDigestReuseWeight key message cache))
  rw [mul_assoc, hcancel] at h
  exact h

theorem normalizedMessageReuseWeight_eq_inv_of_count (key : SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (hbudget : cachedMessageEntryCount cache key.parameter key.root message + digestAttemptLimit <
      ((2 ^ randomnessBits : Nat) : ENNReal)) :
    normalizedMessageReuseWeight key message cache =
      (cachedMessageEntryCountWhere cache key.parameter key.root message (fun _ => True) +
        messageDigestFreshRate key message cache * ((2 ^ randomnessBits : Nat) : ENNReal))⁻¹ := by
  let count := cachedMessageEntryCountWhere cache key.parameter key.root message (fun _ => True)
  let reuse := messageDigestReuseWeight key message cache
  have hreuseTop : reuse ≠ ⊤ := messageDigestReuseWeight_ne_top_of_count key message cache hbudget
  have hreuseZero : reuse ≠ 0 := by
    unfold reuse messageDigestReuseWeight
    rw [div_eq_mul_inv]
    exact mul_ne_zero (ENNReal.inv_ne_zero.mpr (by finiteness))
      (ENNReal.inv_ne_zero.mpr (messageDigestFreshRate_ne_top key message cache))
  have hinv : reuse⁻¹ = messageDigestFreshRate key message cache * ((2 ^ randomnessBits : Nat) : ENNReal) := by
    unfold reuse messageDigestReuseWeight
    rw [div_eq_mul_inv, ENNReal.mul_inv (Or.inl (ENNReal.inv_ne_zero.mpr (by finiteness)))
      (Or.inl (ENNReal.inv_ne_top.mpr (by positivity))), inv_inv, inv_inv, mul_comm]
  have hfactor : 1 + count * reuse = reuse * (count + reuse⁻¹) := by
    rw [mul_add, ENNReal.mul_inv_cancel hreuseZero hreuseTop]
    ring
  change reuse * (1 + count * reuse)⁻¹ = _
  rw [hfactor, ENNReal.mul_inv (Or.inl hreuseZero) (Or.inl hreuseTop), ← mul_assoc,
    ENNReal.mul_inv_cancel hreuseZero hreuseTop, one_mul, hinv]

theorem exactDigestReuseWeight_le_normalizedMessage_of_count (key : SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (hbudget : cachedMessageEntryCount cache key.parameter key.root message + digestAttemptLimit <
      ((2 ^ randomnessBits : Nat) : ENNReal)) :
    exactDigestReuseWeight key message cache ≤ normalizedMessageReuseWeight key message cache := by
  have hcount : cachedMessageEntryCountWhere cache key.parameter key.root message (fun _ => True) ≠ ⊤ := by
    have hle : cachedMessageEntryCountWhere cache key.parameter key.root message (fun _ => True) ≤
        cachedMessageEntryCount cache key.parameter key.root message :=
      ENat.toENNReal_mono (Set.encard_le_encard (fun _ h => h.1))
    exact ne_top_of_le_ne_top (by finiteness) (hle.trans (le_self_add.trans hbudget.le))
  have hreuse := messageDigestReuseWeight_ne_top_of_count key message cache hbudget
  have hmass : freshDigestSelectionProbability key message cache +
      cachedMessageEntryCountWhere cache key.parameter key.root message (fun _ => True) * exactDigestReuseWeight key message cache ≤ 1 :=
    le_self_add.trans_eq (freshSelection_add_count_exactWeight_add_exhaustion key message cache)
  unfold normalizedMessageReuseWeight
  apply (ENNReal.le_div_iff_mul_le (Or.inl (by positivity)) (Or.inl (by finiteness))).mpr
  calc
    _ = exactDigestReuseWeight key message cache +
        (cachedMessageEntryCountWhere cache key.parameter key.root message (fun _ => True) * exactDigestReuseWeight key message cache) *
          messageDigestReuseWeight key message cache := by ring
    _ ≤ freshDigestSelectionProbability key message cache * messageDigestReuseWeight key message cache +
        (cachedMessageEntryCountWhere cache key.parameter key.root message (fun _ => True) * exactDigestReuseWeight key message cache) *
          messageDigestReuseWeight key message cache :=
      add_le_add (exactDigestReuseWeight_le_fresh_mul_messageReuseWeight_of_count key message cache hbudget) le_rfl
    _ = (freshDigestSelectionProbability key message cache +
        cachedMessageEntryCountWhere cache key.parameter key.root message (fun _ => True) * exactDigestReuseWeight key message cache) *
          messageDigestReuseWeight key message cache := by rw [add_mul]
    _ ≤ _ := mul_le_of_le_one_left' hmass

theorem messageDigestFreshRate_balance_of_count (key : SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (hbudget : cachedMessageEntryCount cache key.parameter key.root message + digestAttemptLimit <
      ((2 ^ randomnessBits : Nat) : ENNReal)) :
    messageDigestFreshRate key message cache * ((2 ^ randomnessBits : Nat) : ENNReal) +
      (cachedMessageEntryCount cache key.parameter key.root message + (digestAttemptLimit : ENNReal)) *
        ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ = ((2 ^ 118 : Nat) : ENNReal) := by
  let count := cachedMessageEntryCount cache key.parameter key.root message + (digestAttemptLimit : ENNReal)
  let space : ENNReal := (2 ^ randomnessBits : Nat)
  let admissible : ENNReal := ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹
  have hcount : count ≤ space := hbudget.le
  have hzero : space ≠ 0 := by dsimp only [space]; positivity
  have htop : space ≠ ⊤ := by dsimp only [space]; finiteness
  have hfraction : count * space⁻¹ ≤ 1 :=
    (mul_le_mul' hcount le_rfl).trans_eq (ENNReal.mul_inv_cancel hzero htop)
  have hcancel : (count * space⁻¹) * (space * admissible) = count * admissible := by
    rw [mul_assoc, ← mul_assoc space⁻¹, ENNReal.inv_mul_cancel hzero htop, one_mul]
  change ((1 - count * space⁻¹) * admissible) * space + count * admissible = _
  calc
    _ = ((1 - count * space⁻¹) + count * space⁻¹) * (space * admissible) := by rw [← hcancel]; ring
    _ = space * admissible := by rw [tsub_add_cancel_of_le hfraction, one_mul]
    _ = _ := by
      apply (ENNReal.toReal_eq_toReal_iff' (by dsimp only [space, admissible]; finiteness) (by finiteness)).mp
      norm_num [space, admissible, ENNReal.toReal_mul, ENNReal.toReal_inv, randomnessBits, ftsTreeHeight]

theorem normalizedMessageReuseWeight_le_deficit_of_count (key : SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (hbudget : cachedMessageEntryCount cache key.parameter key.root message + digestAttemptLimit <
      ((2 ^ randomnessBits : Nat) : ENNReal)) :
    normalizedMessageReuseWeight key message cache ≤
      (((2 ^ 118 : Nat) : ENNReal) - ((digestAttemptLimit : ENNReal) * ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ +
        messageAdmissibleDeficit key message cache))⁻¹ := by
  rw [normalizedMessageReuseWeight_eq_inv_of_count key message cache hbudget]
  apply ENNReal.inv_le_inv.mpr
  apply tsub_le_iff_left.mpr
  rw [← messageDigestFreshRate_balance_of_count key message cache hbudget, add_mul]
  have hcount : cachedMessageEntryCount cache key.parameter key.root message * ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ ≤
      cachedMessageEntryCountWhere cache key.parameter key.root message (fun _ => True) + messageAdmissibleDeficit key message cache :=
    le_add_tsub
  have h := add_le_add (add_le_add (le_refl (messageDigestFreshRate key message cache * ((2 ^ randomnessBits : Nat) : ENNReal))) hcount)
    (le_refl ((digestAttemptLimit : ENNReal) * ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹))
  convert h using 1 <;> first | rfl | ring

theorem normalizedMessageReuseWeight_le_near_uniform_of_deficit_of_count
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (hbudget : cachedMessageEntryCount cache key.parameter key.root message + digestAttemptLimit <
      ((2 ^ randomnessBits : Nat) : ENNReal))
    (hdeficit : messageAdmissibleDeficit key message cache ≤ ((2 ^ 83 : Nat) : ENNReal)) :
    normalizedMessageReuseWeight key message cache ≤ (1025 / 1024 : ENNReal) * ((2 ^ 118 : Nat) : ENNReal)⁻¹ := by
  apply (normalizedMessageReuseWeight_le_deficit_of_count key message cache hbudget).trans
  apply (ENNReal.inv_le_inv.mpr (tsub_le_tsub_left (add_le_add le_rfl hdeficit) _)).trans
  have hsmall : (digestAttemptLimit : ENNReal) * ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ + ((2 ^ 83 : Nat) : ENNReal) <
      ((2 ^ 118 : Nat) : ENNReal) := by
    apply (ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)).mp
    rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
    norm_num [ENNReal.toReal_mul, ENNReal.toReal_inv, digestAttemptLimit, ftsTreeHeight]
  apply (ENNReal.toReal_le_toReal (ENNReal.inv_ne_top.mpr (ne_of_gt (tsub_pos_iff_lt.mpr hsmall))) (by finiteness)).mp
  rw [ENNReal.toReal_inv, ENNReal.toReal_sub_of_le hsmall.le (by finiteness)]
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  norm_num [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_div, digestAttemptLimit, ftsTreeHeight]

theorem exactDigestReuseWeight_le_near_uniform_of_deficit_of_count
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (hbudget : cachedMessageEntryCount cache key.parameter key.root message + digestAttemptLimit <
      ((2 ^ randomnessBits : Nat) : ENNReal))
    (hdeficit : messageAdmissibleDeficit key message cache ≤ ((2 ^ 83 : Nat) : ENNReal)) :
    exactDigestReuseWeight key message cache ≤ (1025 / 1024 : ENNReal) * ((2 ^ 118 : Nat) : ENNReal)⁻¹ :=
  (exactDigestReuseWeight_le_normalizedMessage_of_count key message cache hbudget).trans
    (normalizedMessageReuseWeight_le_near_uniform_of_deficit_of_count key message cache hbudget hdeficit)

end SphincsSecurity.Concrete
