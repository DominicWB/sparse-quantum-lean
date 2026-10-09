import SparseLowerBounds.Helpers.SearchWeight.Proj

set_option synthInstance.maxHeartbeats 400000

section
/-!
# Vector facts for `SparseLowerBounds.Query.SearchWeight`

Helper module of group search-weight. Euclidean norms of vectors in `ℂ^m`
written as `WithLp.toLp 2 v`: conjugation invariance, the basis vector, the
rank-one operator-norm bound `‖x yᵀ‖ ≤ ‖x‖ ‖y‖`, and the norm of the vector
`x P_u|b⟩ + y P_v|b⟩` (entries `x/m + y (-1)^{i+b}/m`) for even `m`.
-/

namespace SparseLowerBounds.Helpers.SearchWeight

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace ComplexConjugate

/-- Entrywise conjugation preserves the Euclidean norm. -/
theorem norm_toLp_star {m : ℕ} (v : Fin m → ℂ) :
    ‖(WithLp.toLp 2 (star v) : EuclideanSpace ℂ (Fin m))‖ =
      ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Fin m))‖ := by
  simp only [EuclideanSpace.norm_eq, Pi.star_apply, norm_star]

/-- The basis vector `|b⟩` is a unit vector. -/
theorem norm_toLp_single {m : ℕ} (b : Fin m) :
    ‖(WithLp.toLp 2 (Pi.single b (1 : ℂ)) : EuclideanSpace ℂ (Fin m))‖ = 1 := by
  rw [PiLp.toLp_single, PiLp.norm_single, norm_one]

/-- The squared Euclidean norm as a sum of squared entries. -/
theorem norm_toLp_sq {m : ℕ} (v : Fin m → ℂ) :
    ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Fin m))‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]

/-- The rank-one matrix `x yᵀ` has L2 operator norm at most `‖x‖ ‖y‖`. -/
theorem norm_vecMulVec_le {m : ℕ} (x y : Fin m → ℂ) :
    ‖Matrix.vecMulVec x y‖ ≤ ‖(WithLp.toLp 2 x : EuclideanSpace ℂ (Fin m))‖ *
      ‖(WithLp.toLp 2 y : EuclideanSpace ℂ (Fin m))‖ := by
  refine Helpers.XorWeight.norm_le_of_sum_sq _ (by positivity) fun z => ?_
  have hentry : ∀ i, (Matrix.vecMulVec x y *ᵥ z) i = x i * (y ⬝ᵥ z) := by
    intro i
    simp only [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Finset.mul_sum, mul_assoc]
  have hCS : ‖y ⬝ᵥ z‖ ^ 2 ≤ (∑ j, ‖y j‖ ^ 2) * ∑ j, ‖z j‖ ^ 2 := by
    calc ‖y ⬝ᵥ z‖ ^ 2 ≤ (∑ j, ‖y j‖ * ‖z j‖) ^ 2 := by
          gcongr
          refine (norm_sum_le _ _).trans (le_of_eq ?_)
          simp only [norm_mul]
      _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  rw [mul_pow, norm_toLp_sq, norm_toLp_sq]
  simp only [hentry, norm_mul, mul_pow]
  rw [← Finset.sum_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left hCS (Finset.sum_nonneg fun i _ => by positivity)

/-- `Σ_k (-1)^k = 0` over `Fin m` for even `m` (real form). -/
theorem sum_neg_one_pow_real {m : ℕ} (hm : Even m) : ∑ k : Fin m, (-1 : ℝ) ^ (k : ℕ) = 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun k => (-1 : ℝ) ^ k) m]
  obtain ⟨r, rfl⟩ := hm
  induction r with
  | zero => simp
  | succ r ih =>
    rw [show r + 1 + (r + 1) = r + r + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, pow_succ]
    ring

/-- For even `m`, the vector with entries `x/m + y (-1)^{i+b}/m` (that is
`x P_u|b⟩ + y P_v|b⟩`) has squared norm `(|x|² + |y|²)/m`. -/
theorem norm_alt_combo_sq {m : ℕ} (hm : Even m) (b : Fin m) (x y : ℂ) :
    ‖(WithLp.toLp 2 (fun i : Fin m => x * (m : ℂ)⁻¹ + y * ((-1 : ℂ) ^ ((i : ℕ) + b) / m)) :
      EuclideanSpace ℂ (Fin m))‖ ^ 2 = (‖x‖ ^ 2 + ‖y‖ ^ 2) / m := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast Fin.pos b
  set u : EuclideanSpace ℂ (Fin m) := WithLp.toLp 2 (fun _ => (1 : ℂ)) with hu
  set z : EuclideanSpace ℂ (Fin m) := WithLp.toLp 2 (fun i : Fin m => (-1 : ℂ) ^ (i : ℕ))
    with hz
  have hv : (WithLp.toLp 2 (fun i : Fin m => x * (m : ℂ)⁻¹ + y * ((-1 : ℂ) ^ ((i : ℕ) + b) / m)) :
      EuclideanSpace ℂ (Fin m)) = (x * (m : ℂ)⁻¹) • u + (y * (-1) ^ (b : ℕ) * (m : ℂ)⁻¹) • z := by
    ext i
    simp only [hu, hz, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pow_add]
    ring
  have huz : ⟪u, z⟫_ℂ = 0 := by
    rw [PiLp.inner_apply]
    simp only [hu, hz, PiLp.toLp_apply, RCLike.inner_apply', map_one, one_mul]
    exact Helpers.XorWeight.sum_neg_one_pow hm
  have hu2 : ‖u‖ ^ 2 = m := by
    rw [hu, norm_toLp_sq]
    simp
  have hz2 : ‖z‖ ^ 2 = m := by
    rw [hz, norm_toLp_sq]
    simp
  rw [hv, norm_add_sq (𝕜 := ℂ), inner_smul_left, inner_smul_right, huz, mul_zero, mul_zero,
    RCLike.zero_re, mul_zero, add_zero, norm_smul, norm_smul, mul_pow, mul_pow, hu2, hz2]
  simp only [norm_mul, norm_inv, norm_pow, norm_neg, norm_one, one_pow, mul_one,
    Complex.norm_natCast]
  field_simp
end
end SparseLowerBounds.Helpers.SearchWeight
end
