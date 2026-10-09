import LinearSystemLowerBound.Weight.OneCoordinate

/-!
# The unitary gadget with one-bit entries

On positions `a : Fin m` (`m` even, at least two) the gadget for the marked position `j` is

`(U_j)_{a,b} = 2/m - [j = a - b - 1]`,

i.e. `U_j = S^{j+1} G` with the cyclic shift `S` and `G = 2|u⟩⟨u| - I` (paper,
equation `qlsl:eq:entries`: `(U_x)_{a,b} = 2/m - x_{a-b-1}`).  Each entry depends on the
single bit `[j = a - b - 1]`.

* `gadget_unitary`, `gadget_unitary'`: `U_jᴴ U_j = 1` and `U_j U_jᴴ = 1`.
* `gadget_logical`: on the logical states `|s_L⟩ = √(2/m) ∑_{(-1)^a = s} |a⟩`
  (`s = ±1`), `U_j |s_L⟩ = |(s (-1)^j)_L⟩`; there is no accumulated phase.
* `sum_logical_sq`, `sum_sgn_logical_sq`: `|s_L⟩` is a unit vector whose position parity is
  `s`.
-/

namespace LinearSystemLowerBound.Hard

noncomputable section
open scoped BigOperators Matrix
open LinearSystemLowerBound

/-! ### Signs of positions -/

theorem neg_one_pow_mod {m : ℕ} (hm : Even m) (x : ℕ) : (-1 : ℝ) ^ (x % m) = (-1) ^ x := by
  conv_rhs => rw [← Nat.div_add_mod x m, pow_add, pow_mul, hm.neg_one_pow, one_pow, one_mul]

variable {m : ℕ} [NeZero m]

omit [NeZero m] in
theorem sgn_add (hm : Even m) (a b : Fin m) : sgn m (a + b) = sgn m a * sgn m b := by
  simp only [sgn, Fin.val_add, neg_one_pow_mod hm, pow_add]

theorem sgn_one (hm2 : 2 ≤ m) : sgn m 1 = -1 := by
  have h : (1 : Fin m).val = 1 := by
    rw [Fin.val_one', Nat.mod_eq_of_lt (by omega)]
  rw [sgn, h, pow_one]

/-- `(-1)^{a - (j+1)} = -(-1)^a (-1)^j`. -/
theorem sgn_sub (hm : Even m) (hm2 : 2 ≤ m) (a j : Fin m) :
    sgn m (a - (j + 1)) = -(sgn m a * sgn m j) := by
  have h := sgn_add hm (a - (j + 1)) (j + 1)
  rw [sub_add_cancel, sgn_add hm, sgn_one hm2] at h
  have hj := sgn_sq (m := m) j
  rw [h]
  linear_combination (-(sgn m (a - (j + 1)))) * hj

omit [NeZero m] in
/-- Half of the positions have each sign. -/
theorem sum_sgn_indicator (hm : Even m) (s : ℝ) (hs : s = 1 ∨ s = -1) :
    ∑ a : Fin m, (if sgn m a = s then (1 : ℝ) else 0) = m / 2 := by
  have hsum := sum_sgn (m := m) hm
  have hind : ∀ a : Fin m, (if sgn m a = s then (1 : ℝ) else 0) = (1 + s * sgn m a) / 2 := by
    intro a
    rcases sgn_eq (m := m) a with h | h <;> rcases hs with hs | hs <;> simp [h, hs] <;> norm_num
  simp only [hind, ← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum, hsum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, mul_zero,
    add_zero]

/-! ### The gadget -/

theorem shift_iff (a b j : Fin m) : j = a - b - 1 ↔ a = b + j + 1 := by
  constructor
  · intro h; rw [h]; abel
  · intro h; rw [h]; abel

theorem shift_iff' (a b j : Fin m) : j = a - b - 1 ↔ b = a - (j + 1) := by
  constructor
  · intro h; rw [h]; abel
  · intro h; rw [h]; abel

/-- The gadget `U_j`: entries `2/m - [j = a - b - 1]`. -/
def gadget (j : Fin m) : Matrix (Fin m) (Fin m) ℂ :=
  Matrix.of fun a b => (2 / m : ℂ) - if j = a - b - 1 then 1 else 0

theorem gadget_col (j a b : Fin m) :
    gadget j a b = (2 / m : ℂ) - if a = b + j + 1 then 1 else 0 := by
  simp only [gadget, Matrix.of_apply, shift_iff]

theorem gadget_row (j a b : Fin m) :
    gadget j a b = (2 / m : ℂ) - if b = a - (j + 1) then 1 else 0 := by
  simp only [gadget, Matrix.of_apply, shift_iff']

theorem gadget_conj (j a b : Fin m) : (starRingEnd ℂ) (gadget j a b) = gadget j a b := by
  simp only [gadget, Matrix.of_apply, map_sub, map_div₀, map_ofNat, map_natCast]
  split_ifs <;> simp

omit [NeZero m] in
/-- `∑_a (c - δ_{a,p}) (c - δ_{a,q}) = m c² - 2c + [p = q]`. -/
theorem sum_two_deltas (c : ℂ) (p q : Fin m) :
    ∑ a : Fin m, (c - if a = p then 1 else 0) * (c - if a = q then 1 else 0) =
      m * c ^ 2 - 2 * c + if p = q then 1 else 0 := by
  have e : ∀ a : Fin m, (c - if a = p then (1 : ℂ) else 0) * (c - if a = q then 1 else 0) =
      c ^ 2 - c * (if a = q then 1 else 0) - c * (if a = p then 1 else 0) +
        (if a = p then (if p = q then 1 else 0) else 0) := by
    intro a
    by_cases hp : a = p
    · subst hp
      by_cases hq : a = q <;> simp [hq] <;> ring
    · simp only [hp, if_false, sub_zero, mul_zero, add_zero]
      ring
  simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, mul_one]
  ring

/-- Columns of the gadget are orthonormal. -/
theorem gadget_unitary (j : Fin m) : (gadget j)ᴴ * gadget j = 1 := by
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne m
  ext b b'
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, RCLike.star_def, gadget_conj]
  simp only [gadget_col, sum_two_deltas, Matrix.one_apply]
  have hcancel : (b + j + 1 = b' + j + 1) ↔ b = b' := by
    constructor
    · intro h; simpa using h
    · intro h; rw [h]
  simp only [hcancel]
  field_simp
  ring

/-- Rows of the gadget are orthonormal. -/
theorem gadget_unitary' (j : Fin m) : gadget j * (gadget j)ᴴ = 1 := by
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne m
  ext a a'
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, RCLike.star_def, gadget_conj]
  simp only [gadget_row, sum_two_deltas, Matrix.one_apply]
  have hcancel : (a - (j + 1) = a' - (j + 1)) ↔ a = a' := by
    constructor
    · intro h; simpa using h
    · intro h; rw [h]
  simp only [hcancel]
  field_simp
  ring

/-! ### Logical states -/

/-- The logical state `|s_L⟩ = √(2/m) ∑_{(-1)^a = s} |a⟩`. -/
def logical (s : ℝ) (a : Fin m) : ℂ :=
  if sgn m a = s then (Real.sqrt (2 / (m : ℝ)) : ℂ) else 0

omit [NeZero m] in
theorem norm_sq_logical (s : ℝ) (a : Fin m) :
    ‖logical s a‖ ^ 2 = 2 / (m : ℝ) * (if sgn m a = s then 1 else 0) := by
  unfold logical
  split_ifs
  · rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (by positivity), mul_one]
  · simp

theorem sum_logical_sq (hm : Even m) (s : ℝ) (hs : s = 1 ∨ s = -1) :
    ∑ a : Fin m, ‖logical s a‖ ^ 2 = 1 := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne m
  simp only [norm_sq_logical, ← Finset.mul_sum, sum_sgn_indicator hm s hs]
  field_simp

theorem sum_sgn_logical_sq (hm : Even m) (s : ℝ) (hs : s = 1 ∨ s = -1) :
    ∑ a : Fin m, sgn m a * ‖logical s a‖ ^ 2 = s := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne m
  have e : ∀ a : Fin m, sgn m a * ‖logical s a‖ ^ 2 =
      s * (2 / m) * (if sgn m a = s then 1 else 0) := by
    intro a
    rw [norm_sq_logical]
    split_ifs with h
    · rw [h]; ring
    · ring
  simp only [e, ← Finset.mul_sum, sum_sgn_indicator hm s hs]
  field_simp

omit [NeZero m] in
theorem sum_logical (hm : Even m) (s : ℝ) (hs : s = 1 ∨ s = -1) :
    ∑ b : Fin m, logical s b = (Real.sqrt (2 / (m : ℝ)) : ℂ) * ((m / 2 : ℝ) : ℂ) := by
  have h := sum_sgn_indicator hm s hs
  have e : ∀ b : Fin m, logical s b =
      (Real.sqrt (2 / (m : ℝ)) : ℂ) * ((if sgn m b = s then (1 : ℝ) else 0 : ℝ) : ℂ) := by
    intro b; unfold logical; split_ifs <;> simp
  rw [Finset.sum_congr rfl (fun b _ => e b), ← Finset.mul_sum, ← Complex.ofReal_sum, h]

/-- **Logical action**: `U_j |s_L⟩ = |(s (-1)^j)_L⟩`. -/
theorem gadget_logical (hm : Even m) (hm2 : 2 ≤ m) (j : Fin m) (s : ℝ) (hs : s = 1 ∨ s = -1)
    (a : Fin m) :
    ∑ b, gadget j a b * logical s b = logical (s * sgn m j) a := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne m
  have e : ∀ b, gadget j a b * logical s b =
      (2 / m : ℂ) * logical s b - (if b = a - (j + 1) then logical s b else 0) := by
    intro b
    rw [gadget_row]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun b _ => e b), Finset.sum_sub_distrib, ← Finset.mul_sum,
    sum_logical hm s hs, Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
  have hsq : (2 / m : ℂ) * ((Real.sqrt (2 / (m : ℝ)) : ℂ) * (((m : ℝ) / 2 : ℝ) : ℂ)) =
      (Real.sqrt (2 / (m : ℝ)) : ℂ) := by
    push_cast
    field_simp
  rw [hsq]
  unfold logical
  rw [sgn_sub hm hm2]
  rcases hs with hs | hs <;> rcases sgn_eq (m := m) j with hj | hj <;>
    rcases sgn_eq (m := m) a with ha | ha <;> simp [hs, hj, ha] <;> norm_num

end

end LinearSystemLowerBound.Hard
