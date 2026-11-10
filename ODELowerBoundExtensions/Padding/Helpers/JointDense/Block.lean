import SparseLowerBounds.ODE.JointInstance

/-!
# A constant block on the padding indices (helper of `Padding/JointDense`)

Manuscript: the end of the proof of Theorem `odel:thm:joint` (the appended unoccupied block
`2^{-⌈log₂ s⌉} 1 1ᵀ`: "Its norm is at most one", "It requires no membership queries and leaves the
solution unchanged"). Facts about a matrix `D` on `α ⊕ Fin s` that vanishes off
the `Fin s` block and is the constant `c` on it (`hl`, `hr`, `hb`), used by `Padding/JointDense`
and `Padding/JointDenseFacts` for the dense block `denseHam`:

* `denseBlock_norm_le`: `‖D‖ ≤ 1` when `s ‖c‖ ≤ 1` (Schur test with the unit vector,
  as `Hamiltonian.norm_padBlock_le`, proof of Theorem `hsl:thm:main`);
* `denseBlock_sum_norm_sq_row`, `denseBlock_sum_norm_sq_col`: the block rows and columns have
  squared Euclidean norm `s ‖c‖²`;
* `denseBlock_matrixOperator_eq_zero`: `D v = 0` for `v` vanishing on the block, and
  `denseBlock_add_I_smul_apply`: then `(A + i D) v = A v`;
* `denseBlock_card_row`, `denseBlock_card_col`: a block row (column) whose block entries are
  nonzero and whose core entries vanish has exactly `s` nonzero entries;
* `denseBlock_card_mul_norm_le`, `denseBlock_card_mul_norm_sq_le`: `s 2^{-B} ≤ 1` for
  `s ≤ 2^B` and `s 4^{-B} ≤ 1` for `s ≤ 4^B`.
-/

set_option autoImplicit false

namespace ODELowerBoundExtensions.Padding

noncomputable section
open SparseHamiltonian SparseLowerBounds

section Block

variable {α : Type*} [Fintype α] {s : ℕ}
  {D : Matrix (α ⊕ Fin s) (α ⊕ Fin s) ℂ} {c : ℂ}

/-- A block row has squared Euclidean norm `s ‖c‖²`. -/
theorem denseBlock_sum_norm_sq_row (hr : ∀ i a, D i (Sum.inl a) = 0)
    (hb : ∀ t t', D (Sum.inr t) (Sum.inr t') = c) (t : Fin s) :
    ∑ j, ‖D (Sum.inr t) j‖ ^ 2 = s * ‖c‖ ^ 2 := by
  simp [Fintype.sum_sum_type, hr, hb]

/-- A block column has squared Euclidean norm `s ‖c‖²`. -/
theorem denseBlock_sum_norm_sq_col (hl : ∀ a j, D (Sum.inl a) j = 0)
    (hb : ∀ t t', D (Sum.inr t) (Sum.inr t') = c) (t : Fin s) :
    ∑ i, ‖D i (Sum.inr t)‖ ^ 2 = s * ‖c‖ ^ 2 := by
  simp [Fintype.sum_sum_type, hl, hb]

/-- **Schur test for the block**: `‖D‖ ≤ 1` when `s ‖c‖ ≤ 1`. -/
theorem denseBlock_norm_le [DecidableEq α] (hl : ∀ a j, D (Sum.inl a) j = 0)
    (hr : ∀ i a, D i (Sum.inl a) = 0) (hb : ∀ t t', D (Sum.inr t) (Sum.inr t') = c)
    (hsc : (s : ℝ) * ‖c‖ ≤ 1) :
    ‖SparseStateOverlap.matrixOperator D‖ ≤ 1 := by
  rw [Hamiltonian.norm_matrixOperator]
  refine Hamiltonian.norm_le_of_schur _ (fun i j => ‖D i j‖) ?_ (fun _ _ => le_rfl)
    (fun _ => 1) (fun _ => one_pos) zero_le_one fun i => ?_
  · intro i j
    rcases i with i | i <;> rcases j with j | j <;> simp [hl, hr, hb]
  · rcases i with i | i
    · simp [hl]
    · simpa [Fintype.sum_sum_type, hr, hb] using hsc

/-- **The block does not see vectors vanishing on it**: `D v = 0`. -/
theorem denseBlock_matrixOperator_eq_zero (hr : ∀ i a, D i (Sum.inl a) = 0)
    (v : EuclideanSpace ℂ (α ⊕ Fin s)) (hv : ∀ t, v (Sum.inr t) = 0) :
    SparseStateOverlap.matrixOperator D v = 0 := by
  ext i
  rw [SparseStateOverlap.matrixOperator_apply, PiLp.zero_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  rcases j with j | j
  · rw [hr, zero_mul]
  · rw [hv, mul_zero]

/-- A block row whose block entries are nonzero and whose core entries vanish has exactly `s`
nonzero entries. -/
theorem denseBlock_card_row (G : Matrix (α ⊕ Fin s) (α ⊕ Fin s) ℂ) (t : Fin s)
    (h1 : ∀ a, G (Sum.inr t) (Sum.inl a) = 0) (h2 : ∀ t', G (Sum.inr t) (Sum.inr t') ≠ 0) :
    (Finset.univ.filter fun j => G (Sum.inr t) j ≠ 0).card = s := by
  have h : (Finset.univ.filter fun j => G (Sum.inr t) j ≠ 0) =
      Finset.univ.map Function.Embedding.inr := by
    ext j
    rcases j with j | j <;> simp [h1, h2]
  rw [h, Finset.card_map, Finset.card_univ, Fintype.card_fin]

/-- A block column whose block entries are nonzero and whose core entries vanish has exactly
`s` nonzero entries. -/
theorem denseBlock_card_col (G : Matrix (α ⊕ Fin s) (α ⊕ Fin s) ℂ) (t : Fin s)
    (h1 : ∀ a, G (Sum.inl a) (Sum.inr t) = 0) (h2 : ∀ t', G (Sum.inr t') (Sum.inr t) ≠ 0) :
    (Finset.univ.filter fun i => G i (Sum.inr t) ≠ 0).card = s := by
  have h : (Finset.univ.filter fun i => G i (Sum.inr t) ≠ 0) =
      Finset.univ.map Function.Embedding.inr := by
    ext i
    rcases i with i | i <;> simp [h1, h2]
  rw [h, Finset.card_map, Finset.card_univ, Fintype.card_fin]

end Block

/-- **A generator perturbation that vanishes along `v`**: `(A + i D) v = A v` if `D v = 0`. -/
theorem denseBlock_add_I_smul_apply {N : Type*} [Fintype N] [DecidableEq N]
    (A D : Matrix N N ℂ) (v : EuclideanSpace ℂ N)
    (h : SparseStateOverlap.matrixOperator D v = 0) :
    SparseStateOverlap.matrixOperator (A + Complex.I • D) v =
      SparseStateOverlap.matrixOperator A v := by
  have hadd : SparseStateOverlap.matrixOperator (A + Complex.I • D) =
      SparseStateOverlap.matrixOperator A + Complex.I • SparseStateOverlap.matrixOperator D := by
    rw [Hamiltonian.matrixOperator_eq_toEuclideanCLM, Hamiltonian.matrixOperator_eq_toEuclideanCLM,
      Hamiltonian.matrixOperator_eq_toEuclideanCLM, map_add, map_smul]
  rw [hadd]
  simp only [FunLike.coe_add, Pi.add_apply, FunLike.coe_smul, Pi.smul_apply, h, smul_zero,
    add_zero]

section Entry

variable {s B : ℕ} {dense : Bool}

/-- `s · 2^{-B} ≤ 1` for `s ≤ 2^B` (needed only when `dense = true`). -/
theorem denseBlock_card_mul_norm_le (hsB : dense = true → s ≤ 2 ^ B) :
    (s : ℝ) * ‖(if dense then ((2 : ℂ) ^ B)⁻¹ else 0)‖ ≤ 1 := by
  cases dense with
  | false => simp
  | true =>
    have h : (s : ℝ) ≤ 2 ^ B := by exact_mod_cast hsB rfl
    rw [if_pos rfl, norm_inv, norm_pow, RCLike.norm_ofNat, mul_inv_le_iff₀ (by positivity)]
    linarith

/-- `s · (2^{-B})² ≤ 1` for `s ≤ 4^B` (needed only when `dense = true`). -/
theorem denseBlock_card_mul_norm_sq_le (hsB : dense = true → s ≤ 4 ^ B) :
    (s : ℝ) * ‖(if dense then ((2 : ℂ) ^ B)⁻¹ else 0)‖ ^ 2 ≤ 1 := by
  cases dense with
  | false => simp
  | true =>
    have h : (s : ℝ) ≤ 4 ^ B := by exact_mod_cast hsB rfl
    have h4 : ((2 : ℝ) ^ B) ^ 2 = 4 ^ B := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    rw [if_pos rfl, norm_inv, norm_pow, RCLike.norm_ofNat, inv_pow, h4,
      mul_inv_le_iff₀ (by positivity)]
    linarith

end Entry

end

end ODELowerBoundExtensions.Padding
