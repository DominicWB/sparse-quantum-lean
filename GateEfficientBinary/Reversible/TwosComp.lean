import GateEfficientBinary.Reversible.Program
import Mathlib.Algebra.Order.Group.Unbundled.Int

/-!
# Two's complement arithmetic on registers

A register of width `w` holds a bit vector `y : BitVec w`, read as the integer `y.toInt` of the
signed range `[-2^(w-1), 2^(w-1))`. Register addition is integer addition followed by the
balanced reduction `Int.bmod · (2^w)`, which leaves the values of the signed range unchanged
(`bmod_two_pow_eq_self`).

The register operation `a + (b ^^^ fill s) + s` adds or subtracts `b` according to the sign
bit `s`: complementing every bit and adding one is negation (`xor_fill_add_ofBool`,
`toInt_add_xor_fill`).

Shifts by a constant amount need no gates, only wiring. Reading bit `min (i + k) (w - 1)` into
position `i` is the arithmetic right shift, whose value is the floor quotient by `2^k`
(`ofBits_shiftRight`, `toInt_ofBits_shiftRight`). Reading zeros below position `t` and the
sign-extended bits of a narrower input above it multiplies the input by `2^t`
(`toInt_ofBits_extend`); the same holds for a nonnegative register whose product stays in the
signed range (`toInt_ofBits_shiftLeft`).

Finally, the top bit of a register is its sign (`getLsbD_last_eq`), small natural constants
keep their value (`toInt_ofNat_of_lt`), the low `p` bits of a register hold its value modulo
`2^p` (`toNat_mod_eq_toInt_emod`), and the unsigned value of a bit vector is the sum of its bits
weighted by powers of two (`toNat_eq_sum`, `toNat_ofBits_single`).
-/

set_option autoImplicit false

namespace SparseHamiltonian.GateBinary

variable {w b : ℕ}

/-! ### Balanced reduction -/

/-- Balanced reduction modulo `2^w` fixes the signed range `[-2^(w-1), 2^(w-1))`. -/
theorem bmod_two_pow_of_le {v : ℤ} (hw : 0 < w) (h1 : -2 ^ (w - 1) ≤ v)
    (h2 : v < 2 ^ (w - 1)) : v.bmod (2 ^ w) = v := by
  obtain ⟨k, rfl⟩ : ∃ k, w = k + 1 := ⟨w - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at h1 h2
  apply Int.bmod_eq_of_le_mul_two
  · push_cast
    rw [pow_succ]
    omega
  · push_cast
    rw [pow_succ]
    omega

/-- Balanced reduction modulo `2^w` fixes `[0, 2^(w-1))`, also for `w = 0`. -/
theorem bmod_two_pow_of_nonneg {v : ℤ} (h0 : 0 ≤ v) (h : v < 2 ^ (w - 1)) :
    v.bmod (2 ^ w) = v := by
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · have hv : v = 0 := by
      simp only [Nat.zero_sub, pow_zero] at h
      omega
    subst hv
    simp
  · have hp : (0 : ℤ) < 2 ^ (w - 1) := Int.pow_pos (by decide)
    exact bmod_two_pow_of_le hw (by omega) h

/-- Balanced reduction leaves values of the signed range unchanged. -/
theorem bmod_two_pow_eq_self {v : ℤ} (hw : 0 < w) (h : |v| < 2 ^ (w - 1)) :
    v.bmod (2 ^ w) = v := by
  rw [abs_lt] at h
  exact bmod_two_pow_of_le hw h.1.le h.2

/-! ### Conditional negation -/

/-- XOR with the sign fill plus the sign bit negates conditionally. -/
theorem xor_fill_add_ofBool (y : BitVec w) (d : Bool) :
    (y ^^^ fill w d) + (BitVec.ofBool d).setWidth w = if d then -y else y := by
  cases d
  · simp [fill]
  · simp only [fill, if_true, BitVec.xor_allOnes, BitVec.ofBool_true]
    rw [BitVec.neg_eq_not_add]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp

/-- The register operation `a + (b ^^^ fill d) + d` in two's complement. -/
theorem toInt_add_xor_fill (a y : BitVec w) (d : Bool) :
    (a + (y ^^^ fill w d) + (BitVec.ofBool d).setWidth w).toInt =
      (a.toInt + (if d then -y.toInt else y.toInt)).bmod (2 ^ w) := by
  rw [BitVec.add_assoc, xor_fill_add_ofBool]
  cases d
  · simp
  · simp [BitVec.toInt_neg]

/-! ### The sign bit and arithmetic right shifts -/

/-- The sign bit of a register. -/
theorem getLsbD_last_eq (y : BitVec w) (hw : 0 < w) :
    y.getLsbD (w - 1) = decide (y.toInt < 0) := by
  obtain ⟨k, rfl⟩ : ∃ k, w = k + 1 := ⟨w - 1, (Nat.succ_pred_eq_of_pos hw).symm⟩
  rw [← BitVec.msb_eq_getLsbD_last, BitVec.msb_eq_toInt]

/-- An arithmetic right shift read by wiring. -/
theorem ofBits_shiftRight (y : BitVec w) (k : ℕ) (hw : 0 < w) :
    ofBits (fun i => y.getLsbD (min (i + k) (w - 1))) w = y.sshiftRight k := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_ofBits, BitVec.getLsbD_sshiftRight, BitVec.msb_eq_getLsbD_last]
  by_cases hk : k + i < w
  · rw [if_pos hk, min_eq_left (by omega), Nat.add_comm i k]
    simp [hi]
  · rw [if_neg hk, min_eq_right (by omega)]
    simp [hi]

/-- Its two's complement value is the floor quotient. -/
theorem toInt_ofBits_shiftRight (y : BitVec w) (k : ℕ) (hw : 0 < w) :
    (ofBits (fun i => y.getLsbD (min (i + k) (w - 1))) w).toInt = y.toInt / 2 ^ k := by
  rw [ofBits_shiftRight y k hw, BitVec.toInt_sshiftRight, Int.shiftRight_eq_div_pow]
  push_cast
  rfl

/-! ### Left shifts and sign extension -/

/-- A left shift multiplies the two's complement value by `2^t`, up to balanced reduction. -/
theorem toInt_shiftLeft_eq (x : BitVec w) (t : ℕ) :
    (x <<< t).toInt = (x.toInt * 2 ^ t).bmod (2 ^ w) := by
  rw [BitVec.toInt_shiftLeft, BitVec.toInt_eq_toNat_bmod x, Int.bmod_mul_bmod,
    Nat.shiftLeft_eq]
  push_cast
  rfl

/-- Sign extension of a `b`-bit input followed by a left shift by `t`, read by wiring. -/
theorem toInt_ofBits_extend (X : BitVec b) (hb : 0 < b) (t : ℕ) (h : b + t ≤ w) :
    (ofBits (fun i => if i < t then false else X.getLsbD (min (i - t) (b - 1))) w).toInt =
      X.toInt * 2 ^ t := by
  have hbits :
      ofBits (fun i => if i < t then false else X.getLsbD (min (i - t) (b - 1))) w =
        X.signExtend w <<< t := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [getLsbD_ofBits, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_signExtend,
      BitVec.msb_eq_getLsbD_last]
    by_cases hit : i < t
    · simp [hit]
    · by_cases hb' : i - t < b
      · rw [min_eq_left (by omega)]
        simp [hi, hit, hb', show i - t < w by omega]
      · rw [min_eq_right (by omega)]
        simp [hi, hit, hb', show i - t < w by omega]
  rw [hbits, toInt_shiftLeft_eq, BitVec.toInt_signExtend_of_le (by omega)]
  have hp : (2 : ℤ) ^ (b - 1) * 2 ^ t ≤ 2 ^ (w - 1) := by
    rw [← Int.pow_add]
    exact_mod_cast Nat.pow_le_pow_right (by decide) (by omega)
  have ht : (0 : ℤ) < 2 ^ t := Int.pow_pos (by decide)
  have h1 := Int.mul_le_mul_of_nonneg_right (BitVec.le_toInt X) ht.le
  rw [Int.neg_mul] at h1
  apply bmod_two_pow_of_le (by omega)
  · exact Int.le_trans (Int.neg_le_neg hp) h1
  · exact Int.lt_of_lt_of_le (Int.mul_lt_mul_of_pos_right BitVec.toInt_lt ht) hp

/-- A left shift of a nonnegative register, read by wiring. -/
theorem toInt_ofBits_shiftLeft (Z : BitVec w) (S : ℕ) (h0 : 0 ≤ Z.toInt)
    (h : Z.toInt * 2 ^ S < 2 ^ (w - 1)) :
    (ofBits (fun i => if i < S then false else Z.getLsbD (i - S)) w).toInt =
      Z.toInt * 2 ^ S := by
  have hbits : ofBits (fun i => if i < S then false else Z.getLsbD (i - S)) w = Z <<< S := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [getLsbD_ofBits, BitVec.getLsbD_shiftLeft]
    by_cases hiS : i < S <;> simp [hi, hiS]
  rw [hbits, toInt_shiftLeft_eq]
  exact bmod_two_pow_of_nonneg (Int.mul_nonneg h0 (Int.pow_nonneg (by decide))) h

/-! ### Constants, residues and unsigned values -/

/-- A small natural constant. -/
theorem toInt_ofNat_of_lt (c : ℕ) (h : c < 2 ^ (w - 1)) : (BitVec.ofNat w c).toInt = c := by
  rw [BitVec.toInt_ofNat']
  exact bmod_two_pow_of_nonneg (Int.natCast_nonneg c) (by exact_mod_cast h)

/-- The low `p` bits of a register are its value modulo `2^p`. -/
theorem toNat_mod_eq_toInt_emod (A : BitVec w) (p : ℕ) (hp : p ≤ w) :
    ((A.toNat % 2 ^ p : ℕ) : ℤ) = A.toInt % 2 ^ p := by
  rw [BitVec.toInt_eq_toNat_bmod]
  have hdvd : (2 : ℤ) ^ p ∣ ((2 ^ w : ℕ) : ℤ) := by
    push_cast
    exact pow_dvd_pow 2 hp
  rw [← Int.emod_emod_of_dvd _ hdvd, Int.bmod_emod, Int.emod_emod_of_dvd _ hdvd]
  push_cast
  rfl

/-- The unsigned value of the bit vector with bits `f 0, …, f (n - 1)`. -/
theorem toNat_ofBits_eq_sum (f : ℕ → Bool) (n : ℕ) :
    (ofBits f n).toNat = ∑ i ∈ Finset.range n, (if f i then 2 ^ i else 0) := by
  induction n generalizing f with
  | zero => simp [ofBits]
  | succ n ih =>
      rw [ofBits, BitVec.toNat_concat, ih, Finset.sum_range_succ', Finset.sum_mul]
      congr 1
      · apply Finset.sum_congr rfl
        intro i _
        split_ifs <;> simp [pow_succ]
      · cases f 0 <;> simp

/-- The value of a bit vector as a sum of its bits. -/
theorem toNat_eq_sum (v : BitVec w) :
    v.toNat = ∑ i ∈ Finset.range w, (if v.getLsbD i then 2 ^ i else 0) := by
  conv_lhs => rw [← ofBits_getLsbD v]
  exact toNat_ofBits_eq_sum _ _

/-- A single bit at position `p`. -/
theorem toNat_ofBits_single (p : ℕ) (hp : p < w) (d : Bool) :
    (ofBits (fun i => if i = p then d else false) w).toNat = if d then 2 ^ p else 0 := by
  cases d
  · have h0 : ofBits (fun i => if i = p then false else false) w = 0#w := by
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      simp [getLsbD_ofBits]
    rw [h0]
    simp
  · have h1 : ofBits (fun i => if i = p then true else false) w = BitVec.twoPow w p := by
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      rw [getLsbD_ofBits, BitVec.getLsbD_twoPow]
      by_cases hip : i = p
      · subst hip
        simp [hi]
      · simp [hip, Ne.symm hip]
    rw [h1, BitVec.toNat_twoPow, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hp)]
    simp

end SparseHamiltonian.GateBinary
