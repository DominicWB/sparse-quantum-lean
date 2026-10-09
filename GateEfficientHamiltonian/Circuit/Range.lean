import GateEfficientHamiltonian.Circuit.Tree

/-!
# Uniform pointer states

The uniform state `|u_n⟩ = n^{-1/2} Σ_{j<n} |j⟩` on the little-endian pointer
register is prepared by the binary tree whose rotation at bit `s` is a
Hadamard below a strictly smaller prefix ("loose") and a fixed rotation
`tightRot n s` below the prefix of `n` itself ("tight").  This file computes
the conditional masses of the uniform target by counting, and checks that
these rotations have the required live columns.
-/

namespace SparseHamiltonian.GateCircuit

noncomputable section
open ContinuousLinearMap OracleCircuit
open scoped InnerProduct BigOperators
open GatePointerEncoding (wordValue wordFin wordEquivFin bitValue)

/-! ### Bits and values of little-endian words -/

theorem testBit_wordValue {r : ℕ} (w : Fin r → Bool) (i : Fin r) :
    (wordValue w).testBit i = w i := by
  induction r with
  | zero => exact Fin.elim0 i
  | succ r ih =>
      rw [GatePointerEncoding.wordValue_succ]
      induction i using Fin.cases with
      | zero =>
          simp only [Fin.val_zero, Nat.testBit_zero]
          cases h : w 0
          · simp [bitValue]
          · simp [bitValue, Nat.add_mod]
      | succ i =>
          simp only [Fin.val_succ, Nat.testBit_succ]
          have : (bitValue (w 0) + 2 * wordValue (GatePointerEncoding.tail w)) / 2 =
              wordValue (GatePointerEncoding.tail w) := by
            cases w 0
            · simp [bitValue]
            · simp [bitValue]; omega
          rw [this, ih]
          rfl

theorem testBit_wordValue_ge {r : ℕ} (w : Fin r → Bool) (i : ℕ) (hi : r ≤ i) :
    (wordValue w).testBit i = false := by
  apply Nat.testBit_lt_two_pow
  exact lt_of_lt_of_le (GatePointerEncoding.wordValue_lt_pow w) (Nat.pow_le_pow_right (by norm_num) hi)

/-- Agreement of the bits `≥ k` is equality of the high values. -/
theorem cone_iff_div {r : ℕ} (k : ℕ) (w v : Fin r → Bool) :
    cone k w v ↔ wordValue v / 2 ^ k = wordValue w / 2 ^ k := by
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_div_two_pow, Nat.testBit_div_two_pow]
    by_cases hi : i + k < r
    · rw [testBit_wordValue v ⟨i + k, hi⟩, testBit_wordValue w ⟨i + k, hi⟩]
      exact h ⟨i + k, hi⟩ (by simp)
    · rw [testBit_wordValue_ge v _ (by omega), testBit_wordValue_ge w _ (by omega)]
  · intro h i hi
    have := congrArg (fun x => x.testBit (i - k)) h
    simp only [Nat.testBit_div_two_pow, Nat.sub_add_cancel hi] at this
    rwa [testBit_wordValue, testBit_wordValue] at this

/-- Counting the words of a cone below `n`. -/
theorem card_cone_lt {r : ℕ} (k n : ℕ) (hn : n ≤ 2 ^ r) (w : Fin r → Bool) :
    (Finset.univ.filter (fun v : Fin r → Bool => cone k w v ∧ wordValue v < n)).card =
      min ((wordValue w / 2 ^ k + 1) * 2 ^ k) n - min (wordValue w / 2 ^ k * 2 ^ k) n := by
  set C := wordValue w / 2 ^ k
  have hpos : 0 < 2 ^ k := by positivity
  have himg : (Finset.univ.filter (fun v : Fin r → Bool => cone k w v ∧ wordValue v < n)).card =
      ((Finset.range n).filter (fun u => u / 2 ^ k = C)).card := by
    apply Finset.card_bij (fun v _ => wordValue v)
    · intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range] at hv ⊢
      exact ⟨hv.2, (cone_iff_div k w v).mp hv.1⟩
    · intro v _ v' _ h
      exact GatePointerEncoding.wordValue_injective h
    · intro u hu
      simp only [Finset.mem_filter, Finset.mem_range] at hu
      have hu2 : u < 2 ^ r := lt_of_lt_of_le hu.1 hn
      refine ⟨(wordEquivFin r).symm ⟨u, hu2⟩, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have hval : wordValue ((wordEquivFin r).symm ⟨u, hu2⟩) = u :=
          congrArg Fin.val ((wordEquivFin r).apply_symm_apply ⟨u, hu2⟩)
        rw [cone_iff_div, hval]
        exact ⟨hu.2, hu.1⟩
      · exact congrArg Fin.val ((wordEquivFin r).apply_symm_apply ⟨u, hu2⟩)
  rw [himg]
  have hset : (Finset.range n).filter (fun u => u / 2 ^ k = C) =
      Finset.Ico (min (C * 2 ^ k) n) (min ((C + 1) * 2 ^ k) n) := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    rw [Nat.div_eq_iff hpos, add_mul, one_mul]
    set A := C * 2 ^ k
    set B := 2 ^ k
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨by omega, ?_⟩
      rw [lt_min_iff]
      exact ⟨by omega, h1⟩
    · rintro ⟨h1, h2⟩
      rw [lt_min_iff] at h2
      rw [min_le_iff] at h1
      omega
  rw [hset, Nat.card_Ico]

/-- The value of the bits `≥ s` after setting bit `s`. -/
theorem wordValue_update_div {r : ℕ} (w : Fin r → Bool) (s : Fin r) (b : Bool) :
    wordValue (Function.update w s b) / 2 ^ (s : ℕ) =
      2 * (wordValue w / 2 ^ ((s : ℕ) + 1)) + b.toNat := by
  rw [← Nat.bit_val]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_div_two_pow]
  cases i with
  | zero =>
      rw [Nat.testBit_bit_zero, zero_add, testBit_wordValue (Function.update w s b) s,
        Function.update_self]
  | succ i =>
      rw [Nat.testBit_bit_succ, Nat.testBit_div_two_pow]
      by_cases hi : i + 1 + s < r
      · have hne : (⟨i + 1 + s, hi⟩ : Fin r) ≠ s := by
          intro e; have := congrArg Fin.val e; simp at this
        rw [testBit_wordValue (Function.update w s b) ⟨i + 1 + s, hi⟩,
          Function.update_of_ne hne,
          show i + ((s : ℕ) + 1) = i + 1 + s by omega, testBit_wordValue w ⟨i + 1 + s, hi⟩]
      · rw [testBit_wordValue_ge _ _ (by omega), testBit_wordValue_ge _ _ (by omega)]

/-- Updating bits at or below `s` keeps the value of the bits above `s`. -/
theorem wordValue_update_div_high {r : ℕ} (w : Fin r → Bool) (t : Fin r) (s : ℕ)
    (ht : (t : ℕ) ≤ s) (b : Bool) :
    wordValue (Function.update w t b) / 2 ^ (s + 1) = wordValue w / 2 ^ (s + 1) := by
  rw [← cone_iff_div]
  intro i hi
  rw [Function.update_of_ne]
  intro e; subst e; omega

/-! ### The uniform target and its masses -/

/-- The uniform amplitude on pointer words of value below `n`. -/
def uf (n : ℕ) {r : ℕ} (v : Fin r → Bool) : ℝ :=
  if wordValue v < n then (Real.sqrt n)⁻¹ else 0

/-- The number of words of a cone below `n`. -/
def cnt (n k C : ℕ) : ℕ := min ((C + 1) * 2 ^ k) n - min (C * 2 ^ k) n

theorem mass_uf {r : ℕ} (n : ℕ) (_hn : 0 < n) (hnr : n ≤ 2 ^ r) (k : ℕ) (w : Fin r → Bool) :
    mass (uf n) k w = (cnt n k (wordValue w / 2 ^ k) : ℝ) / n := by
  unfold mass
  have h : ∀ v : Fin r → Bool, (if cone k w v then uf n v ^ 2 else 0) =
      if cone k w v ∧ wordValue v < n then (n : ℝ)⁻¹ else 0 := by
    intro v
    by_cases hc : cone k w v <;> by_cases hv : wordValue v < n <;>
      simp [hc, hv, uf, Real.sq_sqrt (Nat.cast_nonneg n)]
  simp only [h]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
    card_cone_lt k n hnr w]
  rw [div_eq_mul_inv]
  rfl

theorem uf_mass_one {r : ℕ} (n : ℕ) (hn : 0 < n) (hnr : n ≤ 2 ^ r) :
    ∑ v : Fin r → Bool, uf n v ^ 2 = 1 := by
  have h := mass_uf n hn hnr r (fun _ => false)
  rw [mass_top (uf n) r le_rfl] at h
  rw [h]
  have h0 : wordValue (fun _ : Fin r => false) / 2 ^ r = 0 :=
    Nat.div_eq_of_lt (GatePointerEncoding.wordValue_lt_pow _)
  rw [h0, cnt]
  simp only [zero_add, one_mul, zero_mul, Nat.zero_min, Nat.sub_zero, min_eq_right hnr]
  field_simp

/-! ### The rotations of the uniform tree -/

/-- The real rotation with first column `(c, s)`. -/
def rotC (c s : ℝ) : Matrix Bool Bool ℂ := fun row col =>
  match row, col with
  | false, false => (c : ℂ)
  | false, true => -(s : ℂ)
  | true, false => (s : ℂ)
  | true, true => (c : ℂ)

theorem rotC_unitary (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) : UnitaryMat (rotC c s) := by
  have hc : (c : ℂ) ^ 2 + (s : ℂ) ^ 2 = 1 := by exact_mod_cast h
  constructor <;>
  · funext i j
    simp only [Matrix.mul_apply, Fintype.sum_bool, Matrix.conjTranspose_apply, rotC,
      Matrix.one_apply, RCLike.star_def]
    cases i <;> cases j <;> simp <;>
      first | ring1 | linear_combination hc

/-- The Hadamard-type rotation of a loose prefix. -/
def hadC : Matrix Bool Bool ℂ := rotC (Real.sqrt 2)⁻¹ (Real.sqrt 2)⁻¹

theorem hadC_unitary : UnitaryMat hadC := by
  apply rotC_unitary
  rw [inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-- The rotation of the tight prefix at bit `s`. -/
def tightRot (n s : ℕ) : Matrix Bool Bool ℂ :=
  if n % 2 ^ (s + 1) = 0 then 1 else
    rotC (Real.sqrt ((min (2 ^ s) (n % 2 ^ (s + 1)) : ℕ) / (n % 2 ^ (s + 1) : ℕ)))
      (Real.sqrt ((n % 2 ^ (s + 1) - min (2 ^ s) (n % 2 ^ (s + 1)) : ℕ) / (n % 2 ^ (s + 1) : ℕ)))

theorem tightRot_unitary (n s : ℕ) : UnitaryMat (tightRot n s) := by
  unfold tightRot
  split_ifs with h
  · exact one_unitaryMat
  · apply rotC_unitary
    have hρ : (0 : ℝ) < (n % 2 ^ (s + 1) : ℕ) := by exact_mod_cast Nat.pos_of_ne_zero h
    rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity), ← add_div]
    rw [div_eq_one_iff_eq hρ.ne']
    have hle : min (2 ^ s) (n % 2 ^ (s + 1)) ≤ n % 2 ^ (s + 1) := min_le_right _ _
    push_cast [Nat.cast_sub hle]
    ring

/-- The rotation at bit `s` below the pointer prefix of `w`. -/
def rangeLevel {r : ℕ} (n s : ℕ) (w : Fin r → Bool) : Matrix Bool Bool ℂ :=
  if wordValue w / 2 ^ (s + 1) = n / 2 ^ (s + 1) then tightRot n s else hadC

/-! ### Counting in the tight, loose and dead cases -/

theorem cnt_tight (n s : ℕ) :
    cnt n (s + 1) (n / 2 ^ (s + 1)) = n % 2 ^ (s + 1) ∧
    cnt n s (2 * (n / 2 ^ (s + 1))) = min (2 ^ s) (n % 2 ^ (s + 1)) ∧
    cnt n s (2 * (n / 2 ^ (s + 1)) + 1) = n % 2 ^ (s + 1) - min (2 ^ s) (n % 2 ^ (s + 1)) := by
  have hdm := Nat.div_add_mod n (2 ^ (s + 1))
  have hlt := Nat.mod_lt n (show 0 < 2 ^ (s + 1) by positivity)
  set C := n / 2 ^ (s + 1)
  set ρ := n % 2 ^ (s + 1)
  set B := 2 ^ s
  have hB : 2 ^ (s + 1) = 2 * B := by rw [pow_succ]; ring
  set X := C * B
  have e1 : (C + 1) * 2 ^ (s + 1) = 2 * X + 2 * B := by rw [hB]; ring
  have e2 : C * 2 ^ (s + 1) = 2 * X := by rw [hB]; ring
  have e3 : (2 * C + 1) * B = 2 * X + B := by ring
  have e4 : 2 * C * B = 2 * X := by ring
  have e5 : (2 * C + 1 + 1) * B = 2 * X + 2 * B := by ring
  have hn : n = 2 * X + ρ := by rw [← hdm, hB]; ring
  rw [hB] at hlt
  refine ⟨?_, ?_, ?_⟩
  · unfold cnt; rw [e1, e2]; omega
  · unfold cnt; rw [e3, e4]; omega
  · unfold cnt; rw [e5, e3]; omega

theorem cnt_loose (n s C' : ℕ) (h : C' < n / 2 ^ (s + 1)) :
    cnt n (s + 1) C' = 2 ^ (s + 1) ∧ ∀ b : ℕ, b ≤ 1 → cnt n s (2 * C' + b) = 2 ^ s := by
  have hdm := Nat.div_add_mod n (2 ^ (s + 1))
  set C := n / 2 ^ (s + 1)
  set B := 2 ^ s
  have hB : 2 ^ (s + 1) = 2 * B := by rw [pow_succ]; ring
  have hle : (C' + 1) * 2 ^ (s + 1) ≤ C * 2 ^ (s + 1) := Nat.mul_le_mul_right _ h
  have hCn : C * 2 ^ (s + 1) ≤ n := by
    have := Nat.div_mul_le_self n (2 ^ (s + 1)); exact this
  set Y := C' * B
  have e1 : (C' + 1) * 2 ^ (s + 1) = 2 * Y + 2 * B := by rw [hB]; ring
  have e2 : C' * 2 ^ (s + 1) = 2 * Y := by rw [hB]; ring
  rw [e1] at hle
  refine ⟨?_, ?_⟩
  · unfold cnt; rw [e1, e2, hB]; omega
  · intro b hb
    unfold cnt
    have e3 : (2 * C' + b + 1) * B = 2 * Y + b * B + B := by ring
    have e4 : (2 * C' + b) * B = 2 * Y + b * B := by ring
    rw [e3, e4]
    interval_cases b <;> simp <;> omega

theorem cnt_dead (n s C' : ℕ) (h : n / 2 ^ (s + 1) < C') : cnt n (s + 1) C' = 0 := by
  have hn : n < C' * 2 ^ (s + 1) := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)] at h; exact h
  unfold cnt
  have h1 : C' * 2 ^ (s + 1) ≤ (C' + 1) * 2 ^ (s + 1) := Nat.mul_le_mul_right _ (by omega)
  rw [min_eq_right (by omega), min_eq_right (by omega)]
  simp

/-! ### The live columns of the uniform tree -/

theorem sqrt_ratio (a b n : ℝ) (hn : 0 < n) (hb : 0 < b) (ha : 0 ≤ a) :
    Real.sqrt (a / n) / Real.sqrt (b / n) = Real.sqrt (a / b) := by
  rw [Real.sqrt_div ha, Real.sqrt_div hb.le, Real.sqrt_div ha]
  have h1 : Real.sqrt n ≠ 0 := (Real.sqrt_pos.mpr hn).ne'
  have h2 : Real.sqrt b ≠ 0 := (Real.sqrt_pos.mpr hb).ne'
  field_simp

theorem inv_sqrt_div_sqrt (a n : ℝ) (hn : 0 < n) (ha : 0 < a) :
    (Real.sqrt n)⁻¹ / Real.sqrt (a / n) = (Real.sqrt a)⁻¹ := by
  rw [Real.sqrt_div ha.le]
  have h1 : Real.sqrt n ≠ 0 := (Real.sqrt_pos.mpr hn).ne'
  have h2 : Real.sqrt a ≠ 0 := (Real.sqrt_pos.mpr ha).ne'
  field_simp

theorem rangeLevel_col {r : ℕ} (n : ℕ) (hn : 0 < n) (hnr : n ≤ 2 ^ r) (s : Fin r)
    (w : Fin r → Bool) (hlive : 0 < mass (uf n) ((s : ℕ) + 1) w) (b : Bool) :
    rangeLevel n s w b false = (treeCol (uf n) s w b : ℂ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hupd := wordValue_update_div w s b
  have hm1 := mass_uf n hn hnr ((s : ℕ) + 1) w
  have hms := mass_uf n hn hnr (s : ℕ) (Function.update w s b)
  rw [hupd] at hms
  rw [hm1] at hlive
  have hlive' : 0 < cnt n ((s : ℕ) + 1) (wordValue w / 2 ^ ((s : ℕ) + 1)) := by
    by_contra h0
    have : cnt n ((s : ℕ) + 1) (wordValue w / 2 ^ ((s : ℕ) + 1)) = 0 := by omega
    rw [this] at hlive; simp at hlive
  generalize hC' : wordValue w / 2 ^ ((s : ℕ) + 1) = C' at hupd hm1 hms hlive'
  have hrl : rangeLevel n s w = if C' = n / 2 ^ ((s : ℕ) + 1) then tightRot n s else hadC := by
    unfold rangeLevel; rw [hC']
  rw [hrl, treeCol, hm1]
  rcases lt_trichotomy C' (n / 2 ^ ((s : ℕ) + 1)) with hlt | heq | hgt
  · -- loose prefix
    rw [if_neg (by omega)]
    obtain ⟨h1, h2⟩ := cnt_loose n s C' hlt
    rw [h1]
    by_cases hs0 : (s : ℕ) = 0
    · rw [if_pos hs0]
      have hv : wordValue (Function.update w s b) = 2 * C' + b.toNat := by
        have := hupd; rw [hs0, pow_zero, Nat.div_one] at this; exact this
      have hn2 : C' < n / 2 := by have := hlt; rw [hs0] at this; simpa using this
      have hval : wordValue (Function.update w s b) < n := by
        rw [hv]; cases b <;> simp <;> omega
      simp only [uf, if_pos hval, hs0, zero_add, pow_one]
      have e := inv_sqrt_div_sqrt 2 n hnR (by norm_num)
      cases b <;> simp only [hadC, rotC] <;> exact_mod_cast e.symm
    · rw [if_neg hs0, hms, h2 b.toNat (by cases b <;> simp)]
      have : Real.sqrt (((2 ^ (s : ℕ) : ℕ) : ℝ) / n) /
          Real.sqrt (((2 ^ ((s : ℕ) + 1) : ℕ) : ℝ) / n) = (Real.sqrt 2)⁻¹ := by
        rw [sqrt_ratio _ _ _ hnR (by positivity) (by positivity)]
        push_cast
        rw [pow_succ, div_mul_cancel_left₀ (by positivity), Real.sqrt_inv]
      cases b <;> simp only [hadC, rotC] <;> rw [this]
  · -- tight prefix
    rw [if_pos heq]
    obtain ⟨h1, h2, h3⟩ := cnt_tight n s
    rw [← heq] at h1 h2 h3
    rw [h1]
    have hρ : n % 2 ^ ((s : ℕ) + 1) ≠ 0 := by
      intro h0; rw [h1, h0] at hlive'; exact lt_irrefl _ hlive'
    unfold tightRot
    rw [if_neg hρ]
    have hρR : (0 : ℝ) < (n % 2 ^ ((s : ℕ) + 1) : ℕ) := by exact_mod_cast Nat.pos_of_ne_zero hρ
    by_cases hs0 : (s : ℕ) = 0
    · rw [if_pos hs0]
      have hv : wordValue (Function.update w s b) = 2 * C' + b.toNat := by
        have := hupd; rw [hs0, pow_zero, Nat.div_one] at this; exact this
      have hρ1 : n % 2 = 1 := by
        have h := hρ; rw [hs0] at h; norm_num at h; omega
      have hC2 : C' = n / 2 := by rw [heq, hs0]; norm_num
      have hρ1' : n % 2 ^ ((s : ℕ) + 1) = 1 := by rw [hs0]; norm_num; exact hρ1
      have hmin : min (2 ^ (s : ℕ)) 1 = 1 := by rw [hs0]; norm_num
      rw [hρ1', hmin]
      cases b
      · have hval : wordValue (Function.update w s false) < n := by
          rw [hv]; simp; omega
        simp only [uf, if_pos hval, rotC]
        have e := inv_sqrt_div_sqrt 1 n hnR (by norm_num)
        simp only [Real.sqrt_one, inv_one] at e
        simp only [Nat.cast_one, div_one, Real.sqrt_one]
        rw [e]
      · have hval : ¬ wordValue (Function.update w s true) < n := by
          rw [hv]; simp; omega
        simp only [uf, if_neg hval, rotC]
        norm_num
    · rw [if_neg hs0, hms]
      cases b
      · simp only [Bool.toNat_false, add_zero, h2, rotC]
        rw [sqrt_ratio _ _ _ hnR hρR (by positivity)]
      · simp only [Bool.toNat_true, h3, rotC]
        rw [sqrt_ratio _ _ _ hnR hρR (by positivity)]
  · -- dead prefix
    exfalso
    rw [cnt_dead n s C' hgt] at hlive'
    exact lt_irrefl _ hlive'

/-! ### Generic live tree rotations -/

section TreeMat

variable {q : ℕ} (f : (Fin q → Bool) → ℝ)

theorem cone_update_low (k : ℕ) (w v : Fin q → Bool) (t : Fin q) (ht : (t : ℕ) < k) (b : Bool) :
    cone k (Function.update w t b) v ↔ cone k w v := by
  unfold cone
  constructor
  · intro h i hi
    have := h i hi
    rwa [Function.update_of_ne (fun e => by subst e; omega)] at this
  · intro h i hi
    rw [Function.update_of_ne (fun e => by subst e; omega)]
    exact h i hi

theorem mass_update_low (k : ℕ) (w : Fin q → Bool) (t : Fin q) (ht : (t : ℕ) < k) (b : Bool) :
    mass f k (Function.update w t b) = mass f k w := by
  unfold mass
  simp only [cone_update_low k w _ t ht b]

theorem treeCol_update_low (s : Fin q) (w : Fin q → Bool) (t : Fin q) (ht : (t : ℕ) ≤ s)
    (b b' : Bool) : treeCol f s (Function.update w t b') b = treeCol f s w b := by
  unfold treeCol
  rw [mass_update_low f _ w t (by omega) b']
  by_cases hts : t = s
  · subst hts
    simp only [Function.update_idem]
  · rw [Function.update_comm hts]
    by_cases hs0 : (s : ℕ) = 0
    · exfalso; apply hts; apply Fin.ext; omega
    · simp only [if_neg hs0]
      rw [mass_update_low f _ _ t (by
        have : (t : ℕ) ≠ s := fun e => hts (Fin.ext e)
        omega) b']

/-- The live tree rotation at bit `s`; prefixes of zero mass get the identity. -/
def treeMat (s : Fin q) (w : Fin q → Bool) : Matrix Bool Bool ℂ :=
  if 0 < mass f ((s : ℕ) + 1) w then rotC (treeCol f s w false) (treeCol f s w true) else 1

theorem treeMat_update_low (s : Fin q) (w : Fin q → Bool) (t : Fin q) (ht : (t : ℕ) ≤ s)
    (b : Bool) : treeMat f s (Function.update w t b) = treeMat f s w := by
  unfold treeMat
  rw [mass_update_low f _ w t (by omega) b, treeCol_update_low f s w t ht false b,
    treeCol_update_low f s w t ht true b]

theorem treeMat_col (s : Fin q) (w : Fin q → Bool) (hlive : 0 < mass f ((s : ℕ) + 1) w)
    (b : Bool) : treeMat f s w b false = (treeCol f s w b : ℂ) := by
  unfold treeMat
  rw [if_pos hlive]
  cases b <;> rfl

theorem treeMat_unitary (s : Fin q) (w : Fin q → Bool) : UnitaryMat (treeMat f s w) := by
  unfold treeMat
  split_ifs with hlive
  · apply rotC_unitary
    have hsplit := mass_split f s w
    have hm := hlive
    unfold treeCol
    rw [div_pow, div_pow, ← add_div, div_eq_one_iff_eq (by positivity)]
    rw [Real.sq_sqrt (mass_nonneg f _ w)]
    by_cases hs0 : (s : ℕ) = 0
    · simp only [if_pos hs0]
      rw [← hsplit, hs0, mass_zero, mass_zero]
    · simp only [if_neg hs0]
      rw [Real.sq_sqrt (mass_nonneg f _ _), Real.sq_sqrt (mass_nonneg f _ _), hsplit]
  · exact one_unitaryMat

end TreeMat

end

end SparseHamiltonian.GateCircuit
