import GateEfficientBinaryODE.Program

/-!
# What the pre-processing program computes

Register values are bit vectors of width `w`, a commutative ring in which the two's complement
words `BitVec.ofInt w z` of integers `z` (modulo `2^w`) compute (`ofInt_add'`, `ofInt_mul'`,
`ofInt_neg'`). Every register operation `dst := a ± b` is a ring operation (`val_eq`,
`val_ofInt`), shifts are multiplications by powers of two (`readBV_shA`, `ofBits_shB`), and the
multiplication chain computes `2 M v` (`chain_last`). Ring identities hold without any bound on
the intermediate values; bounds are needed only where a sign bit is read (`msb_ofInt`) or where
the bits of a register are used as digits (`digits_ofInt`).

With these facts `ProgramVal` shows that on every input configuration the last registers of the
two component chains hold the integers `zx` and `zy` of `Program`, exactly, when the layout
bounds hold (`Lay.OK`; `v_xc`, `v_yc`).
-/

set_option autoImplicit false

namespace SparseHamiltonian.GateBinaryODE

open SparseHamiltonian.GateBinary
open GatePointerEncoding (wordValue)

/-! ### Integers as bit vectors -/

section Ring

variable {w : ℕ}

theorem ofInt_add' (a b : ℤ) : BitVec.ofInt w a + BitVec.ofInt w b = BitVec.ofInt w (a + b) :=
  (BitVec.ofInt_add a b).symm

theorem ofInt_mul' (a b : ℤ) : BitVec.ofInt w a * BitVec.ofInt w b = BitVec.ofInt w (a * b) :=
  (BitVec.ofInt_mul a b).symm

theorem ofInt_neg' (a : ℤ) : -BitVec.ofInt w a = BitVec.ofInt w (-a) := BitVec.ofInt_neg.symm

theorem ofInt_zero' : BitVec.ofInt w 0 = 0 := by
  apply BitVec.eq_of_toNat_eq
  simp

theorem twoPow_eq_ofInt (j : ℕ) : BitVec.twoPow w j = BitVec.ofInt w (2 ^ j) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_twoPow, show ((2 : ℤ) ^ j) = ((2 ^ j : ℕ) : ℤ) by push_cast; rfl,
    BitVec.ofInt_natCast, BitVec.toNat_ofNat]

theorem shiftLeft_eq_ofInt (x : BitVec w) (j : ℕ) : x <<< j = x * BitVec.ofInt w (2 ^ j) := by
  rw [BitVec.shiftLeft_eq_mul_twoPow, twoPow_eq_ofInt]

theorem ofInt_eq_iff (x : BitVec w) (z : ℤ) (hw : 0 < w) (hz : |z| < 2 ^ (w - 1)) :
    x = BitVec.ofInt w z ↔ x.toInt = z := by
  constructor
  · rintro rfl
    rw [BitVec.toInt_ofInt]
    exact bmod_two_pow_eq_self hw hz
  · intro h
    apply BitVec.eq_of_toInt_eq
    rw [h, BitVec.toInt_ofInt, bmod_two_pow_eq_self hw hz]

theorem toInt_ofInt_of (z : ℤ) (hw : 0 < w) (hz : |z| < 2 ^ (w - 1)) :
    (BitVec.ofInt w z).toInt = z := by
  rw [BitVec.toInt_ofInt]
  exact bmod_two_pow_eq_self hw hz

/-- The sign bit of a small integer. -/
theorem msb_ofInt (z : ℤ) (hw : 0 < w) (hz : |z| < 2 ^ (w - 1)) :
    (BitVec.ofInt w z).getLsbD (w - 1) = decide (z < 0) := by
  rw [getLsbD_last_eq _ hw, toInt_ofInt_of z hw hz]

/-- The bits of a small nonnegative integer are its binary digits. -/
theorem digits_ofInt (z : ℤ) (m : ℕ) (hm : m < w) (h0 : 0 ≤ z) (hz : z < 2 ^ m) :
    (∑ j ∈ Finset.range m, if (BitVec.ofInt w z).getLsbD j then (2 ^ j : ℤ) else 0) = z := by
  have hzw : z < 2 ^ w := lt_of_lt_of_le hz (pow_le_pow_right₀ (by norm_num) hm.le)
  have hnat : ((BitVec.ofInt w z).toNat : ℤ) = z := by
    rw [BitVec.toNat_ofInt, Int.toNat_of_nonneg (Int.emod_nonneg _ (by positivity))]
    exact Int.emod_eq_of_lt h0 (by exact_mod_cast hzw)
  have hlt : (BitVec.ofInt w z).toNat < 2 ^ m := by
    have : ((BitVec.ofInt w z).toNat : ℤ) < 2 ^ m := by rw [hnat]; exact hz
    exact_mod_cast this
  conv_rhs => rw [← hnat, toNat_eq_sum]
  push_cast
  have hsplit : Finset.range w = Finset.range m ∪ Finset.Ico m w := by
    ext j
    simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]
    omega
  rw [hsplit, Finset.sum_union (by
    rw [Finset.disjoint_left]
    intro j hj hj'
    simp only [Finset.mem_range] at hj
    simp only [Finset.mem_Ico] at hj'
    omega)]
  have hzero : (∑ j ∈ Finset.Ico m w,
      (if (BitVec.ofInt w z).getLsbD j then ((2 : ℤ) ^ j) else 0)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp only [Finset.mem_Ico] at hj
    have hb : (BitVec.ofInt w z).getLsbD j = false := by
      rw [← BitVec.testBit_toNat]
      exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hlt
        (Nat.pow_le_pow_right (by norm_num) hj.1))
    rw [hb]
    rfl
  rw [hzero, add_zero]

end Ring

/-! ### Reading registers, inputs and constants -/

section Read

variable {B : Type} {L : Lay}

theorem readBV_zA (x : B → Bool) (F : RO L → BitVec L.w) :
    readBV (zA : ℕ → PW B L) L.w (cfgOf x F) = BitVec.ofInt L.w 0 := by
  rw [ofInt_zero']
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_readBV]
  simp [zA, cfgOf]

theorem readBV_rA (x : B → Bool) (F : RO L → BitVec L.w) (r : RO L) :
    readBV (rA r : ℕ → PW B L) L.w (cfgOf x F) = F r :=
  readBV_regW x F r

theorem cfgOf_regW (x : B → Bool) (F : RO L → BitVec L.w) (r : RO L) {i : ℕ} (hi : i < L.w) :
    cfgOf x F (regW r i : PW B L) = (F r).getLsbD i := by
  rw [regW_of_lt r hi]
  rfl

theorem readBV_shA (x : B → Bool) (F : RO L → BitVec L.w) (r : RO L) (j : ℕ) :
    readBV (shA r j : ℕ → PW B L) L.w (cfgOf x F) = F r * BitVec.ofInt L.w (2 ^ j) := by
  rw [← shiftLeft_eq_ofInt]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_readBV, BitVec.getLsbD_shiftLeft]
  simp only [shA, hi, decide_true, Bool.true_and]
  by_cases hij : i < j
  · simp [hij, cfgOf]
  · simp only [hij, if_false, decide_false, Bool.not_false, Bool.true_and]
    rw [cfgOf_regW x F r (by omega)]

theorem ofBits_rB (x : B → Bool) (F : RO L → BitVec L.w) (r : RO L) :
    ofBits (fun i => (rB r i : BSrc (PW B L)).val (cfgOf x F)) L.w = F r := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_ofBits]
  simp only [rB, BSrc.val, beq_true, hi, decide_true, Bool.true_and]
  exact cfgOf_regW x F r hi

theorem ofBits_shB (x : B → Bool) (F : RO L → BitVec L.w) (r : RO L) (j : ℕ) :
    ofBits (fun i => (shB r j i : BSrc (PW B L)).val (cfgOf x F)) L.w =
      F r * BitVec.ofInt L.w (2 ^ j) := by
  rw [← readBV_shA x F r j]
  apply ofBits_congr
  intro i hi
  simp only [shB, shA]
  split_ifs
  · simp [BSrc.val, cfgOf]
  · simp [BSrc.val]

theorem ofBits_cB (x : B → Bool) (F : RO L → BitVec L.w) (c : ℕ) :
    ofBits (fun i => (cB c i : BSrc (PW B L)).val (cfgOf x F)) L.w =
      BitVec.ofInt L.w (c : ℤ) := by
  simp only [cB, BSrc.val]
  rw [ofBits_getLsbD, BitVec.ofInt_natCast]

/-- A signed `b`-bit input component, read with sign extension. -/
theorem readBV_inA (x : B → Bool) (F : RO L → BitVec L.w) (r : Fin L.b → B) (hb : 0 < L.b) :
    readBV (inA r : ℕ → PW B L) L.w (cfgOf x F) = BitVec.ofInt L.w (twos r x) := by
  have hbw : L.b + 0 ≤ L.w := by unfold Lay.w; omega
  have hw : 0 < L.w := by unfold Lay.w; omega
  set X : BitVec L.b := ofBits (fun j => if h : j < L.b then x (r ⟨j, h⟩) else false) L.b with hX
  have h1 := toInt_ofBits_extend X hb 0 hbw
  rw [pow_zero, mul_one] at h1
  have hread : readBV (inA r : ℕ → PW B L) L.w (cfgOf x F) =
      ofBits (fun i => if i < 0 then false else X.getLsbD (min (i - 0) (L.b - 1))) L.w := by
    apply ofBits_congr
    intro i _
    simp only [inA, hb, dif_pos, Nat.not_lt_zero, if_false, Nat.sub_zero, hX, getLsbD_ofBits]
    have hm : min i (L.b - 1) < L.b := by omega
    simp [hm, cfgOf]
  rw [hread, ofInt_eq_iff _ _ hw]
  · rw [h1]
    rfl
  · have h2 := BitVec.toInt_lt (x := X)
    have h3 := BitVec.le_toInt X
    have h4 : (2 : ℤ) ^ (L.b - 1) < 2 ^ (L.w - 1) :=
      pow_lt_pow_right₀ (by norm_num) (by unfold Lay.w; omega)
    change |X.toInt| < _
    rw [abs_lt]
    constructor <;> omega

/-- An unsigned input word, read with zero extension. -/
theorem readBV_uA (x : B → Bool) (F : RO L → BitVec L.w) {m : ℕ} (r : Fin m → B) (hm : m ≤ L.w) :
    readBV (uA r : ℕ → PW B L) L.w (cfgOf x F) =
      BitVec.ofInt L.w ((wordValue (fun j => x (r j)) : ℕ) : ℤ) := by
  apply BitVec.eq_of_toNat_eq
  have hlt := GatePointerEncoding.wordValue_lt_pow (fun j => x (r j))
  rw [readBV, toNat_ofBits_eq_sum, BitVec.ofInt_natCast, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by norm_num) hm))]
  unfold GatePointerEncoding.wordValue
  have hsplit : Finset.range L.w = Finset.range m ∪ Finset.Ico m L.w := by
    ext j
    simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]
    omega
  rw [hsplit, Finset.sum_union (by
    rw [Finset.disjoint_left]
    intro j hj hj'
    simp only [Finset.mem_range] at hj
    simp only [Finset.mem_Ico] at hj'
    omega)]
  have hzero : (∑ j ∈ Finset.Ico m L.w,
      (if cfgOf x F (uA r j : PW B L) then 2 ^ j else 0)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp only [Finset.mem_Ico] at hj
    simp [uA, show ¬ j < m by omega, cfgOf]
  rw [hzero, add_zero, Finset.sum_range]
  apply Finset.sum_congr rfl
  intro j _
  simp only [uA, j.isLt, dif_pos, cfgOf, GatePointerEncoding.bitValue, Fin.eta]
  rcases Bool.eq_false_or_eq_true (x (r j)) with h | h <;> simp [h]

theorem readBV_b0A (y : PW B L → Bool) (u : PW B L) (hw : 0 < L.w)
    (hz : y (.inr .zero) = false) :
    readBV (b0A u) L.w y = BitVec.ofInt L.w (if y u then 1 else 0) := by
  apply BitVec.eq_of_toNat_eq
  have h := toNat_ofBits_single 0 hw (y u)
  have hr : readBV (b0A u) L.w y = ofBits (fun i => if i = 0 then y u else false) L.w := by
    apply ofBits_congr
    intro i _
    simp only [b0A]
    split_ifs
    · rfl
    · exact hz
  rw [hr, h]
  have h1 : (1 : ℕ) < 2 ^ L.w := Nat.one_lt_two_pow hw.ne'
  cases y u
  · simp
  · simp only [if_true, pow_zero]
    rw [show ((1 : ℤ)) = ((1 : ℕ) : ℤ) from rfl, BitVec.ofInt_natCast, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt h1]

theorem ofBits_b0B (y : PW B L → Bool) (src : BSrc (PW B L)) (hw : 0 < L.w) :
    ofBits (fun i => (b0B src i).val y) L.w =
      BitVec.ofInt L.w (if src.val y then 1 else 0) := by
  apply BitVec.eq_of_toNat_eq
  have h := toNat_ofBits_single 0 hw (src.val y)
  have hr : ofBits (fun i => (b0B src i).val y) L.w =
      ofBits (fun i => if i = 0 then src.val y else false) L.w := by
    apply ofBits_congr
    intro i _
    simp only [b0B]
    split_ifs
    · rfl
    · rfl
  rw [hr, h]
  have h1 : (1 : ℕ) < 2 ^ L.w := Nat.one_lt_two_pow hw.ne'
  cases src.val y
  · simp
  · simp only [if_true, pow_zero]
    rw [show ((1 : ℤ)) = ((1 : ℕ) : ℤ) from rfl, BitVec.ofInt_natCast, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt h1]

theorem ofBits_inB (x : B → Bool) (F : RO L → BitVec L.w) (r : Fin L.b → B) (hb : 0 < L.b) :
    ofBits (fun i => (inB r i : BSrc (PW B L)).val (cfgOf x F)) L.w =
      BitVec.ofInt L.w (twos r x) := by
  rw [← readBV_inA x F r hb]
  apply ofBits_congr
  intro i _
  simp [inB, BSrc.val]

/-- The value of a register operation. -/
theorem val_eq (o : ROp B (RO L) L.w) (y : PW B L → Bool) :
    o.val y = readBV o.a L.w y +
      (if o.s.val y then -(ofBits (fun i => (o.b i).val y) L.w) else
        ofBits (fun i => (o.b i).val y) L.w) := by
  rw [ROp.val, BitVec.add_assoc, xor_fill_add_ofBool]

/-- The value of a register operation on integers. -/
theorem val_ofInt (o : ROp B (RO L) L.w) (y : PW B L → Bool) (α β : ℤ)
    (ha : readBV o.a L.w y = BitVec.ofInt L.w α)
    (hb : ofBits (fun i => (o.b i).val y) L.w = BitVec.ofInt L.w β) :
    o.val y = BitVec.ofInt L.w (α + (if o.s.val y then -β else β)) := by
  rw [val_eq, ha, hb]
  split_ifs
  · rw [ofInt_neg', ofInt_add']
  · rw [ofInt_add']

theorem msbO_val (x : B → Bool) (F : RO L → BitVec L.w) (r : RO L) (pol : Bool) :
    (BSrc.lit (msbO r) pol : BSrc (PW B L)).val (cfgOf x F) =
      ((F r).getLsbD (L.w - 1) == pol) := by
  simp only [BSrc.val, msbO]
  rw [cfgOf_regW x F r (by unfold Lay.w; omega)]

theorem inMsb_val (x : B → Bool) (F : RO L → BitVec L.w) (r : Fin L.b → B) (hb : 0 < L.b)
    (pol : Bool) :
    (inMsb r pol : BSrc (PW B L)).val (cfgOf x F) = (decide (twos r x < 0) == pol) := by
  simp only [inMsb, BSrc.val, inA, hb, dif_pos, cfgOf]
  congr 1
  unfold twos
  rw [← getLsbD_last_eq _ hb, getLsbD_ofBits]
  simp [show L.b - 1 < L.b by omega]

theorem lit_inl_val (y : PW B L → Bool) (u : B) (pol : Bool) :
    (BSrc.lit (.inl u) pol : BSrc (PW B L)).val y = (y (.inl u) == pol) := rfl

theorem negS_val (y : PW B L → Bool) (s : BSrc (PW B L)) : (negS s).val y = !(s.val y) := by
  cases s with
  | lit u p =>
      rcases Bool.eq_false_or_eq_true (y u) with h | h <;> cases p <;> simp [negS, BSrc.val, h]
  | const c => rfl

end Read

/-! ### The multiplication chain -/

section Chain

variable {B : Type} {L : Lay}

/-- **The multiplication chain.** If the operations of a chain hold in a register file and its
source register holds the integer `v`, its last register holds `2 M v` for the multiplier `M` of
the digits. -/
theorem chain_last {m : ℕ} (x : B → Bool) (F : RO L → BitVec L.w)
    (acc : Fin (m + 1) → RO L) (v : RO L) (dg : ℕ → BSrc (PW B L)) (vi : ℤ)
    (hv : F v = BitVec.ofInt L.w vi)
    (h : ∀ o ∈ chain acc v dg, F o.dst = o.val (cfgOf x F)) :
    F (acc (Fin.last m)) = BitVec.ofInt L.w (2 * (∑ j ∈ Finset.range m,
      if (dg j).val (cfgOf x F) then (2 ^ j : ℤ) else 0) * vi) := by
  have h0 := h _ List.mem_cons_self
  have hshv : ∀ j : ℕ, F v * BitVec.ofInt L.w (2 ^ j) = BitVec.ofInt L.w (vi * 2 ^ j) := by
    intro j
    rw [hv, ofInt_mul']
  rw [val_ofInt _ _ (vi * 2 ^ m) vi (by rw [readBV_shA, hshv]) (by rw [ofBits_rB, hv])] at h0
  have hstep : ∀ j : Fin m, ∀ a : ℤ, F (acc j.castSucc) = BitVec.ofInt L.w a →
      F (acc j.succ) = BitVec.ofInt L.w (a + (if (dg j).val (cfgOf x F) then 1 else -1) *
        (vi * 2 ^ (j : ℕ))) := by
    intro j a ha
    have hj := h ⟨acc j.succ, rA (acc j.castSucc), shB v j.val, negS (dg j.val)⟩
      (List.mem_cons_of_mem _ (List.mem_map.2 ⟨j, List.mem_finRange j, rfl⟩))
    rw [hj, val_ofInt _ _ a (vi * 2 ^ (j : ℕ)) (by rw [readBV_rA, ha])
      (by rw [ofBits_shB, hshv]), negS_val]
    congr 1
    cases (dg j.val).val (cfgOf x F) <;> simp
  have key : ∀ j (hj : j ≤ m), F (acc ⟨j, by omega⟩) = BitVec.ofInt L.w (vi * ((2 : ℤ) ^ m - 1 +
      ∑ i ∈ Finset.range j, (if (dg i).val (cfgOf x F) then 1 else -1) * 2 ^ i)) := by
    intro j hj
    induction j with
    | zero =>
        rw [show (⟨0, by omega⟩ : Fin (m + 1)) = 0 from rfl, h0]
        congr 1
        simp only [BSrc.val, if_true, Finset.range_zero, Finset.sum_empty]
        ring
    | succ j ih =>
        have hs := hstep ⟨j, by omega⟩ _ (ih (by omega))
        rw [show (Fin.succ (⟨j, by omega⟩ : Fin m)) = ⟨j + 1, by omega⟩ from rfl] at hs
        rw [hs, Finset.sum_range_succ]
        congr 1
        ring
  rw [show Fin.last m = ⟨m, by omega⟩ from rfl, key m le_rfl]
  congr 1
  have hsum : ∑ i ∈ Finset.range m, (if (dg i).val (cfgOf x F) then (1 : ℤ) else -1) * 2 ^ i =
      2 * (∑ j ∈ Finset.range m, if (dg j).val (cfgOf x F) then (2 ^ j : ℤ) else 0) -
        ∑ i ∈ Finset.range m, (2 : ℤ) ^ i := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> ring
  have hgeom : ∑ i ∈ Finset.range m, (2 : ℤ) ^ i = 2 ^ m - 1 := by
    have h2 := geom_sum_mul (2 : ℤ) m
    norm_num at h2
    exact h2
  rw [hsum, hgeom]
  ring

end Chain

end SparseHamiltonian.GateBinaryODE
