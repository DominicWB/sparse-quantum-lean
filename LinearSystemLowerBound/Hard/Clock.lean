import LinearSystemLowerBound.Hard.Gadget
import SparseHamiltonian.SparseStateOverlap

/-!
# The open clock and the hard linear systems

Indices are `(σ, t, a) : Bool × Fin (T + 1) × Fin m`: dilation sector, clock value and
gadget position.  For marked positions `x : Fin n → Fin m` the transition after clock value
`i` is the gadget `U_{x_i}` for `i < n` and the identity afterwards (`step`); the open clock
`T_X = ∑_i L_i ⊗ |i+1⟩⟨i|` is `clock x`.  The hard matrix is the Hermitian dilation

`A_X = [[0, C_X], [C_Xᵀ, 0]]`, `C_X = (I - r T_X)/2`,

written as `A_X = (Π - r Q_X)/2` with the sector swap `Π` (`swapM`) and
`Q_X = [[0, T_X], [T_Xᵀ, 0]]` (`dil x`).  The right-hand side is `b = |false, 0, 0_L⟩`
(`rhs`), with `|0_L⟩` the logical state of sign `+1`.

* `hard_mul_sol`: `A_X y = b` for the explicit history solution
  `y = (0, 2 ∑_t r^t |ψ_t⟩|t⟩)`, `ψ_t` the logical state of the prefix parity (`sol`); this is
  the finite Neumann series of the paper, verified directly.
* `sum_clock_succ`, `sum_clock_castSucc`: the clock moves block `i` to block `i + 1`.
-/

namespace LinearSystemLowerBound.Hard

noncomputable section
open scoped BigOperators Matrix
open LinearSystemLowerBound

variable {n m T : ℕ} [NeZero m]

/-- Indices: dilation sector, clock value, gadget position. -/
abbrev Idx (T m : ℕ) := Bool × Fin (T + 1) × Fin m

/-- The transition after clock value `i`: the gadget for `i < n`, the identity afterwards. -/
def step (x : Fin n → Fin m) (i : Fin T) : Matrix (Fin m) (Fin m) ℂ :=
  if h : i.val < n then gadget (x ⟨i.val, h⟩) else 1

theorem step_unitary (x : Fin n → Fin m) (i : Fin T) : (step x i)ᴴ * step x i = 1 := by
  unfold step
  split_ifs
  · exact gadget_unitary _
  · simp

theorem step_unitary' (x : Fin n → Fin m) (i : Fin T) : step x i * (step x i)ᴴ = 1 := by
  unfold step
  split_ifs
  · exact gadget_unitary' _
  · simp

/-- The open clock `T_X`. -/
def clock (x : Fin n → Fin m) :
    Matrix (Fin (T + 1) × Fin m) (Fin (T + 1) × Fin m) ℂ :=
  Matrix.of fun (p q : Fin (T + 1) × Fin m) =>
    if h : p.1.val = q.1.val + 1 then
      step (T := T) x ⟨q.1.val, by have h1 := p.1.isLt; omega⟩ p.2 q.2
    else 0

/-- The sector swap `Π`. -/
def swapM : Matrix (Idx T m) (Idx T m) ℂ :=
  Matrix.of fun p q => if p.1 = !q.1 ∧ p.2 = q.2 then 1 else 0

/-- `Q_X = [[0, T_X], [T_Xᵀ, 0]]`. -/
def dil (x : Fin n → Fin m) : Matrix (Idx T m) (Idx T m) ℂ :=
  Matrix.of fun p q =>
    if p.1 = false ∧ q.1 = true then clock x p.2 q.2
    else if p.1 = true ∧ q.1 = false then clock x q.2 p.2 else 0

/-- **The hard matrix** `A_X = (Π - r Q_X)/2`, the Hermitian dilation of `(I - r T_X)/2`. -/
def hardMatrix (r : ℝ) (x : Fin n → Fin m) : Matrix (Idx T m) (Idx T m) ℂ :=
  (1 / 2 : ℂ) • (swapM - (r : ℂ) • dil x)

/-- The right-hand side `b = |false, 0, 0_L⟩`. -/
def rhs : EuclideanSpace ℂ (Idx T m) :=
  WithLp.toLp 2 fun p => if p.1 = false ∧ p.2.1 = 0 then logical 1 p.2.2 else 0

/-- The sign of the first `k` marked positions. -/
def prefixSign (x : Fin n → Fin m) (k : ℕ) : ℝ :=
  ∏ c : Fin n, if c.val < k then sgn m (x c) else 1

/-- The history solution `y = (0, 2 ∑_t r^t |ψ_t⟩ |t⟩)`. -/
def sol (r : ℝ) (x : Fin n → Fin m) : EuclideanSpace ℂ (Idx T m) :=
  WithLp.toLp 2 fun p =>
    if p.1 = true then ((2 * r ^ p.2.1.val : ℝ) : ℂ) * logical (prefixSign x p.2.1.val) p.2.2
    else 0

/-! ### Prefix signs -/

omit [NeZero m] in
theorem prefixSign_zero (x : Fin n → Fin m) : prefixSign x 0 = 1 := by
  simp [prefixSign]

omit [NeZero m] in
theorem prefixSign_pm (x : Fin n → Fin m) (k : ℕ) : prefixSign x k = 1 ∨ prefixSign x k = -1 := by
  unfold prefixSign
  induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
  | empty => simp
  | insert c s hc ih =>
      rw [Finset.prod_insert hc]
      rcases ih with h | h <;> split_ifs <;> rcases sgn_eq (m := m) (x c) with hs | hs <;>
        simp [h, hs]

omit [NeZero m] in
theorem prefixSign_succ (x : Fin n → Fin m) (k : ℕ) (hk : k < n) :
    prefixSign x (k + 1) = prefixSign x k * sgn m (x ⟨k, hk⟩) := by
  unfold prefixSign
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (⟨k, hk⟩ : Fin n)),
    ← Finset.mul_prod_erase Finset.univ (fun c : Fin n => if c.val < k then sgn m (x c) else 1)
      (Finset.mem_univ (⟨k, hk⟩ : Fin n))]
  simp only [lt_add_one, if_true, lt_irrefl, if_false, one_mul]
  rw [mul_comm]
  congr 1
  apply Finset.prod_congr rfl
  intro c hc
  have hne : c.val ≠ k := fun h => (Finset.ne_of_mem_erase hc) (Fin.ext h)
  have : c.val < k + 1 ↔ c.val < k := by omega
  simp only [this]

omit [NeZero m] in
theorem prefixSign_succ_of_le (x : Fin n → Fin m) (k : ℕ) (hk : n ≤ k) :
    prefixSign x (k + 1) = prefixSign x k := by
  unfold prefixSign
  apply Finset.prod_congr rfl
  intro c _
  have h1 : c.val < k + 1 := by have := c.isLt; omega
  have h2 : c.val < k := by have := c.isLt; omega
  simp [h1, h2]

omit [NeZero m] in
/-- After all marked positions the prefix sign is the parity sign. -/
theorem prefixSign_of_le (x : Fin n → Fin m) (k : ℕ) (hk : n ≤ k) :
    prefixSign x k = parSign x := by
  unfold prefixSign parSign
  apply Finset.prod_congr rfl
  intro c _
  have h : c.val < k := by have := c.isLt; omega
  simp [h]

/-! ### The transitions -/

/-- One transition advances the prefix sign. -/
theorem step_logical (hm : Even m) (hm2 : 2 ≤ m) (x : Fin n → Fin m) (i : Fin T) (a : Fin m) :
    ∑ b, step x i a b * logical (prefixSign x i.val) b = logical (prefixSign x (i.val + 1)) a := by
  unfold step
  split_ifs with h
  · rw [gadget_logical hm hm2 _ _ (prefixSign_pm x i.val), prefixSign_succ x i.val h]
  · simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    rw [prefixSign_succ_of_le x i.val (by omega)]

/-- The clock moves block `i` to block `i + 1`. -/
theorem sum_clock_succ (x : Fin n → Fin m) (i : Fin T) (a : Fin m)
    (f : Fin (T + 1) × Fin m → ℂ) :
    ∑ q, clock x (i.succ, a) q * f q = ∑ b, step x i a b * f (i.castSucc, b) := by
  rw [Fintype.sum_prod_type, Finset.sum_eq_single i.castSucc]
  · apply Finset.sum_congr rfl
    intro b _
    simp only [clock, Matrix.of_apply, Fin.val_succ, Fin.val_castSucc]
    rfl
  · intro t _ ht
    apply Finset.sum_eq_zero
    intro b _
    have hne : ¬ ((i.succ : Fin (T + 1)).val = t.val + 1) := by
      intro h
      apply ht
      ext
      simp only [Fin.val_succ, Fin.val_castSucc] at h ⊢
      omega
    simp only [clock, Matrix.of_apply]
    rw [dif_neg hne, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem sum_clock_zero (x : Fin n → Fin m) (a : Fin m) (f : Fin (T + 1) × Fin m → ℂ) :
    ∑ q, clock x ((0 : Fin (T + 1)), a) q * f q = 0 := by
  apply Finset.sum_eq_zero
  intro q _
  have hne : ¬ ((0 : Fin (T + 1)).val = q.1.val + 1) := by simp
  simp only [clock, Matrix.of_apply]
  rw [dif_neg hne, zero_mul]

/-- The transposed clock moves block `i + 1` back to block `i`. -/
theorem sum_clock_castSucc (x : Fin n → Fin m) (i : Fin T) (b : Fin m)
    (f : Fin (T + 1) × Fin m → ℂ) :
    ∑ p, clock x p (i.castSucc, b) * f p = ∑ a, step x i a b * f (i.succ, a) := by
  rw [Fintype.sum_prod_type, Finset.sum_eq_single i.succ]
  · apply Finset.sum_congr rfl
    intro a _
    simp only [clock, Matrix.of_apply, Fin.val_succ, Fin.val_castSucc]
    rfl
  · intro t _ ht
    apply Finset.sum_eq_zero
    intro a _
    have hne : ¬ (t.val = (i.castSucc : Fin (T + 1)).val + 1) := by
      intro h
      apply ht
      ext
      simp only [Fin.val_succ, Fin.val_castSucc] at h ⊢
      omega
    simp only [clock, Matrix.of_apply]
    rw [dif_neg hne, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem sum_clock_last (x : Fin n → Fin m) (b : Fin m) (f : Fin (T + 1) × Fin m → ℂ) :
    ∑ p, clock x p (Fin.last T, b) * f p = 0 := by
  apply Finset.sum_eq_zero
  intro p _
  have hne : ¬ (p.1.val = (Fin.last T).val + 1) := by
    have := p.1.isLt
    simp only [Fin.val_last]
    omega
  simp only [clock, Matrix.of_apply]
  rw [dif_neg hne, zero_mul]

/-! ### Actions on vectors -/

omit [NeZero m] in
theorem act_swapM_apply (v : EuclideanSpace ℂ (Idx T m)) (p : Idx T m) :
    act swapM v p = v (!p.1, p.2) := by
  simp only [act_apply, swapM, Matrix.of_apply, ite_smul, one_smul, zero_smul]
  rw [Finset.sum_eq_single (!p.1, p.2)]
  · simp
  · intro q _ hq
    rw [if_neg]
    rintro ⟨h1, h2⟩
    apply hq
    rcases q with ⟨σ, t⟩
    simp only at h1 h2
    rw [h1, h2]
    simp
  · intro h; exact absurd (Finset.mem_univ _) h

theorem act_dil_false (x : Fin n → Fin m) (v : EuclideanSpace ℂ (Idx T m))
    (t : Fin (T + 1)) (a : Fin m) :
    act (dil x) v (false, t, a) = ∑ q, clock x (t, a) q * v (true, q) := by
  simp only [act_apply, smul_eq_mul, Fintype.sum_prod_type, Fintype.sum_bool]
  simp [dil]

theorem act_dil_true (x : Fin n → Fin m) (v : EuclideanSpace ℂ (Idx T m))
    (t : Fin (T + 1)) (b : Fin m) :
    act (dil x) v (true, t, b) = ∑ p, clock x p (t, b) * v (false, p) := by
  simp only [act_apply, smul_eq_mul, Fintype.sum_prod_type, Fintype.sum_bool]
  simp [dil]

theorem act_hard (r : ℝ) (x : Fin n → Fin m) (v : EuclideanSpace ℂ (Idx T m)) :
    act (hardMatrix r x) v = (1 / 2 : ℂ) • (act swapM v - (r : ℂ) • act (dil x) v) := by
  rw [hardMatrix, act_smul_matrix, act_sub_matrix, act_smul_matrix]

/-! ### The solution -/

/-- **The history state solves the system**: `A_X y = b`. -/
theorem hard_mul_sol (hm : Even m) (hm2 : 2 ≤ m) (r : ℝ) (x : Fin n → Fin m) :
    act (hardMatrix (T := T) r x) (sol r x) = rhs := by
  ext p
  rcases p with ⟨σ, t, a⟩
  rw [act_hard, PiLp.smul_apply, PiLp.sub_apply, PiLp.smul_apply, act_swapM_apply]
  cases σ with
  | true =>
      rw [act_dil_true]
      simp [sol, rhs]
  | false =>
      rw [act_dil_false]
      induction t using Fin.cases with
      | zero =>
          rw [show (∑ q, clock x ((0 : Fin (T + 1)), a) q *
              (sol (T := T) r x) (true, q)) = 0 from sum_clock_zero x a _]
          simp only [sol, rhs, Bool.not_false, PiLp.toLp_apply, if_true, Fin.val_zero,
            pow_zero, mul_one, prefixSign_zero, and_self, smul_eq_mul]
          push_cast
          ring
      | succ i =>
          rw [sum_clock_succ]
          have hsum : ∑ b, step x i a b * (sol (T := T) r x) (true, i.castSucc, b) =
              ((2 * r ^ i.val : ℝ) : ℂ) * logical (prefixSign x (i.val + 1)) a := by
            simp only [sol, PiLp.toLp_apply, if_true, Fin.val_castSucc]
            rw [← step_logical hm hm2 x i a, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro b _
            ring
          rw [hsum]
          simp only [sol, rhs, Bool.not_false, PiLp.toLp_apply, if_true, Fin.val_succ,
            Fin.succ_ne_zero, and_false, if_false, smul_eq_mul]
          push_cast
          ring

end

end LinearSystemLowerBound.Hard
