import ChebyshevFilter.Laurent
import SparseLinearSystems.Spectral.UnitaryFilter
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

set_option autoImplicit false

/-!
# The filter of a unitary and its error (equation `qls:eq:cheberror`)

For a unitary `W` on a finite-dimensional Hilbert space, `filterOp W b d` is
`F_{b,d}(W) = ∑_{j=-d}^{d} p_j W^j`, with `W^j = (W†)^{-j}` for `j < 0` (`wpow`).

The spectral argument runs through the defect operator `(W - 1)†(W - 1) = 2 - W - W†`
(released `UnitaryFilter.defect`), which is self-adjoint and commutes with `W`:

* `sum_pow_apply_eigen`: on an eigenvector of the defect with eigenvalue `t`,
  `W^m + W†^m = 2 T_m(1 - t/2)`, the operator form of `2 cos(mθ) = 2 T_m(cos θ)`;
* `filterOp_apply_defect_eigen`: hence `F_{b,d}(W) v = F_{b,d}(1 - t/2) v`;
* the defect eigenvalues lie in `{0} ∪ [4b², 4]` under the gap hypothesis (released
  `Unitary.defect_eigen_lower`); eigenvalue `0` is the fixed space, where `F = 1`, and every
  other eigenvector is orthogonal to it, where `|F| ≤ 1 / T_d(1 + 2λ)`.

Results:

* `norm_filterOp_sub_le`: `‖F_{b,d}(W) - P‖ ≤ 1 / T_d(1 + 2λ) = sech(2 d artanh b)`;
* `norm_filterOp_sub_fixedProj_le`: `‖F_{b,d}(W) - P‖ ≤ δ` at `d = chebDegree b δ`;
* `norm_filterOp_apply_sq`: `‖F(W)ψ‖² = ‖Pψ‖² + ‖(F(W) - P)ψ‖²` (equation
  `qls:eq:filterprobability`);
* `filterOp_apply_eigen`: on an eigenvector `W v = e^{iθ} v`, `F_{b,d}(W) v = F_{b,d}(e^{iθ}) v`;
* `gap_of_phase`: the manuscript's hypothesis `|sin(θ/2)| ≥ b` for every eigenphase
  `θ` with `e^{iθ} ≠ 1` gives the chord form `|z - 1| ≥ 2b` of the released gap hypothesis
  (`norm_exp_mul_I_sub_one`: `|e^{iθ} - 1| = 2 |sin(θ/2)|`).
-/

namespace ChebyshevFilter

noncomputable section
open Polynomial ContinuousLinearMap SparseLinearSystems SparseLinearSystems.UnitaryFilter
  SparseLinearSystems.Diagonal
open Polynomial.Chebyshev (T)
open scoped InnerProduct ComplexConjugate

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [CompleteSpace V]

/-! ### Signed powers and the filter operator -/

/-- Signed powers: `W^j` for `j ≥ 0` and `(W†)^{-j}` for `j < 0`. -/
def wpow (W : V →L[ℂ] V) (j : ℤ) : V →L[ℂ] V :=
  if 0 ≤ j then W ^ j.toNat else (W†) ^ (-j).toNat

omit [FiniteDimensional ℂ V] in
theorem wpow_natCast (W : V →L[ℂ] V) (n : ℕ) : wpow W n = W ^ n := by
  simp [wpow]

omit [FiniteDimensional ℂ V] in
theorem wpow_neg_natCast (W : V →L[ℂ] V) (n : ℕ) : wpow W (-(n : ℤ)) = (W†) ^ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [wpow]
  · rw [wpow, if_neg (by omega)]
    simp

/-- **The filter `F_{b,d}(W) = ∑_{j=-d}^{d} p_j W^j`.** -/
def filterOp (W : V →L[ℂ] V) (b : ℝ) (d : ℕ) : V →L[ℂ] V :=
  ∑ j ∈ Finset.Icc (-(d : ℤ)) d, ((filterCoeff b d j : ℝ) : ℂ) • wpow W j

omit [FiniteDimensional ℂ V] in
/-- The filter in symmetric pairs: `p_0 + ∑_{m=1}^{d} p_m (W^m + W†^m)`. -/
theorem filterOp_eq_pairs (W : V →L[ℂ] V) (b : ℝ) (d : ℕ) :
    filterOp W b d = ((filterCoeff b d 0 : ℝ) : ℂ) • (1 : V →L[ℂ] V) +
      ∑ k ∈ Finset.range d, ((filterCoeff b d ((k : ℤ) + 1) : ℝ) : ℂ) •
        (W ^ (k + 1) + (W†) ^ (k + 1)) := by
  have h0 : wpow W 0 = 1 := by
    rw [show ((0 : ℤ)) = ((0 : ℕ) : ℤ) by simp, wpow_natCast, pow_zero]
  rw [filterOp, sum_Icc_symm, h0]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [filterCoeff_neg, show (k : ℤ) + 1 = ((k + 1 : ℕ) : ℤ) by push_cast; ring, wpow_natCast,
    wpow_neg_natCast, smul_add]

/-! ### Signed powers on eigenvectors of the defect -/

variable {W : V →L[ℂ] V}

omit [FiniteDimensional ℂ V] in
theorem adjoint_mul_self_of_unitary (hW : Unitary W) : W† * W = 1 := by
  rw [← star_eq_adjoint]; exact hW.left

omit [FiniteDimensional ℂ V] in
theorem mul_adjoint_self_of_unitary (hW : Unitary W) : W * W† = 1 := by
  rw [← star_eq_adjoint]; exact hW.right

omit [FiniteDimensional ℂ V] in
/-- `(W + W†)(W^{m+1} + W†^{m+1}) = (W^{m+2} + W†^{m+2}) + (W^m + W†^m)`. -/
theorem sum_pow_recurrence (hW : Unitary W) (m : ℕ) :
    (W + W†) * (W ^ (m + 1) + (W†) ^ (m + 1)) =
      (W ^ (m + 2) + (W†) ^ (m + 2)) + (W ^ m + (W†) ^ m) := by
  have h1 : W * (W†) ^ (m + 1) = (W†) ^ m := by
    rw [pow_succ', ← mul_assoc, mul_adjoint_self_of_unitary hW, one_mul]
  have h2 : W† * W ^ (m + 1) = W ^ m := by
    rw [pow_succ', ← mul_assoc, adjoint_mul_self_of_unitary hW, one_mul]
  have h3 : W * W ^ (m + 1) = W ^ (m + 2) := by rw [← pow_succ']
  have h4 : W† * (W†) ^ (m + 1) = (W†) ^ (m + 2) := by rw [← pow_succ']
  rw [add_mul, mul_add, mul_add, h1, h2, h3, h4]
  abel

omit [FiniteDimensional ℂ V] in
/-- **`W^m + W†^m = 2 T_m(1 - t/2)`** on an eigenvector of the defect `(W - 1)†(W - 1)` with
eigenvalue `t`. -/
theorem sum_pow_apply_eigen (hW : Unitary W) {v : V} {t : ℝ}
    (hv : defect W v = (t : ℂ) • v) (m : ℕ) :
    (W ^ m + (W†) ^ m) v = ((2 * (T ℝ m).eval (1 - t / 2) : ℝ) : ℂ) • v := by
  have h1 : (W + W†) v = ((2 * (1 - t / 2) : ℝ) : ℂ) • v := by
    have h : (W + W†) v = (2 : ℂ) • v - defect W v := by
      rw [hW.defect_eq]
      simp only [add_apply, sub_apply, smul_apply, one_apply_eq_self]
      abel
    rw [h, hv, ← sub_smul]
    congr 1
    push_cast
    ring
  induction m using Nat.twoStepInduction with
  | zero =>
    simp only [pow_zero, add_apply, one_apply_eq_self, Nat.cast_zero, Chebyshev.T_zero, eval_one]
    rw [show v + v = (2 : ℂ) • v by rw [two_smul]]
    norm_num
  | one =>
    simpa only [pow_one, Nat.cast_one, Chebyshev.T_one, eval_X] using h1
  | more m ih0 ih1 =>
    have hT : (T ℝ ((m + 2 : ℕ) : ℤ)).eval (1 - t / 2) =
        2 * (1 - t / 2) * (T ℝ ((m + 1 : ℕ) : ℤ)).eval (1 - t / 2) -
          (T ℝ (m : ℤ)).eval (1 - t / 2) := by
      rw [show ((m + 2 : ℕ) : ℤ) = (m : ℤ) + 2 by push_cast; ring, Chebyshev.T_add_two,
        show ((m + 1 : ℕ) : ℤ) = (m : ℤ) + 1 by push_cast; ring]
      simp only [eval_sub, eval_mul, eval_X, eval_ofNat]
    have e : (W ^ (m + 2) + (W†) ^ (m + 2)) v =
        (W + W†) ((W ^ (m + 1) + (W†) ^ (m + 1)) v) - (W ^ m + (W†) ^ m) v := by
      have hrec : ((W + W†) * (W ^ (m + 1) + (W†) ^ (m + 1))) v =
          ((W ^ (m + 2) + (W†) ^ (m + 2)) + (W ^ m + (W†) ^ m)) v := by
        rw [sum_pow_recurrence hW m]
      rw [eq_sub_iff_add_eq, ← add_apply (W ^ (m + 2) + (W†) ^ (m + 2)) (W ^ m + (W†) ^ m) v,
        ← hrec]
      rfl
    rw [e, ih1, ih0, map_smul, h1, smul_smul, ← sub_smul, hT]
    congr 1
    push_cast
    ring

omit [FiniteDimensional ℂ V] in
/-- **The filter on an eigenvector of the defect**: `F_{b,d}(W) v = F_{b,d}(1 - t/2) v`. -/
theorem filterOp_apply_defect_eigen (hW : Unitary W) {b : ℝ} (hb2 : b ^ 2 < 1) (d : ℕ)
    {v : V} {t : ℝ} (hv : defect W v = (t : ℂ) • v) :
    filterOp W b d v = ((filterVal b d (1 - t / 2) : ℝ) : ℂ) • v := by
  rw [← filterCoeff_series hb2 d, filterOp_eq_pairs, Complex.ofReal_add, add_smul,
    Complex.ofReal_sum, Finset.sum_smul, add_apply, smul_apply, one_apply_eq_self, sum_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [smul_apply, sum_pow_apply_eigen hW hv (k + 1), smul_smul]
  congr 1
  push_cast
  ring

/-! ### The defect spectrum -/

omit [FiniteDimensional ℂ V] in
/-- The defect vanishes on the fixed space. -/
theorem defect_apply_of_fixed {u : V} (hu : W u = u) : defect W u = 0 := by
  rw [defect, comp_apply, sub_apply, one_apply_eq_self, hu, sub_self, map_zero]

/-- A defect eigenvalue is `‖W e - e‖²` for its unit eigenvector `e`. -/
theorem eigenValues_eq (W : V →L[ℂ] V) (i : Fin (Module.finrank ℂ V)) :
    eigenValues (defect W) (defect_adjoint W) i =
      ‖W (eigenBasis (defect W) (defect_adjoint W) i) -
        eigenBasis (defect W) (defect_adjoint W) i‖ ^ 2 := by
  have h := re_inner_defect W (eigenBasis (defect W) (defect_adjoint W) i)
  rw [apply_eigenBasis, inner_smul_right, inner_self_eq_norm_sq_to_K,
    (eigenBasis (defect W) (defect_adjoint W)).orthonormal.1 i] at h
  simpa using h

theorem eigenValues_nonneg (W : V →L[ℂ] V) (i : Fin (Module.finrank ℂ V)) :
    0 ≤ eigenValues (defect W) (defect_adjoint W) i := by
  rw [eigenValues_eq]; positivity

theorem eigenValues_le_four (hW : Unitary W) (i : Fin (Module.finrank ℂ V)) :
    eigenValues (defect W) (defect_adjoint W) i ≤ 4 := by
  set e := eigenBasis (defect W) (defect_adjoint W)
  rw [eigenValues_eq]
  have h1 : ‖W (e i) - e i‖ ≤ 2 := by
    calc ‖W (e i) - e i‖ ≤ ‖W (e i)‖ + ‖e i‖ := norm_sub_le _ _
      _ = 2 := by rw [hW.norm_apply, e.orthonormal.1 i]; norm_num
  nlinarith [norm_nonneg (W (e i) - e i)]

/-- Eigenvalue zero: the eigenvector is fixed. -/
theorem eigenBasis_fixed (W : V →L[ℂ] V) (i : Fin (Module.finrank ℂ V))
    (hi : eigenValues (defect W) (defect_adjoint W) i = 0) :
    eigenBasis (defect W) (defect_adjoint W) i ∈ fixedSpace W := by
  rw [mem_fixedSpace]
  have h := eigenValues_eq W i
  rw [hi] at h
  have h0 : ‖W (eigenBasis (defect W) (defect_adjoint W) i) -
      eigenBasis (defect W) (defect_adjoint W) i‖ = 0 := by
    nlinarith [norm_nonneg (W (eigenBasis (defect W) (defect_adjoint W) i) -
      eigenBasis (defect W) (defect_adjoint W) i)]
  exact sub_eq_zero.mp (norm_eq_zero.mp h0)

/-- Nonzero eigenvalue: the eigenvector is orthogonal to the fixed space. -/
theorem eigenBasis_orth (W : V →L[ℂ] V) (i : Fin (Module.finrank ℂ V))
    (hi : eigenValues (defect W) (defect_adjoint W) i ≠ 0) :
    eigenBasis (defect W) (defect_adjoint W) i ∈ (fixedSpace W)ᗮ := by
  set e := eigenBasis (defect W) (defect_adjoint W)
  set t := eigenValues (defect W) (defect_adjoint W)
  rw [Submodule.mem_orthogonal']
  intro u hu
  have h0 : inner ℂ (e i) (defect W u) = 0 := by
    rw [defect_apply_of_fixed (mem_fixedSpace.mp hu), inner_zero_right]
  rw [← adjoint_inner_left, defect_adjoint, apply_eigenBasis, inner_smul_left,
    Complex.conj_ofReal] at h0
  exact (mul_eq_zero.mp h0).resolve_left (by exact_mod_cast hi)

/-! ### The error bound -/

/-- The diagonal entries of `F_{b,d}(W) - P` in the defect eigenbasis. -/
def errEntry (W : V →L[ℂ] V) (b : ℝ) (d : ℕ) (i : Fin (Module.finrank ℂ V)) : ℝ :=
  if eigenValues (defect W) (defect_adjoint W) i = 0 then 0
  else filterVal b d (1 - eigenValues (defect W) (defect_adjoint W) i / 2)

/-- `F_{b,d}(W) - P` is diagonal in the defect eigenbasis. -/
theorem filterOp_sub_apply_eigenBasis (hW : Unitary W) {b : ℝ}
    (hb : b ∈ Set.Ioo (-1 : ℝ) 1) (d : ℕ) (i : Fin (Module.finrank ℂ V)) :
    (filterOp W b d - fixedProj W) (eigenBasis (defect W) (defect_adjoint W) i) =
      ((errEntry W b d i : ℝ) : ℂ) • eigenBasis (defect W) (defect_adjoint W) i := by
  have hF := filterOp_apply_defect_eigen hW (sq_lt_one_of_mem hb) d
    (apply_eigenBasis (defect W) (defect_adjoint W) i)
  rw [sub_apply, hF, errEntry]
  by_cases hi : eigenValues (defect W) (defect_adjoint W) i = 0
  · rw [if_pos hi, (Submodule.starProjection_eq_self_iff).mpr (eigenBasis_fixed W i hi), hi,
      zero_div, sub_zero, filterVal_one hb]
    simp
  · rw [if_neg hi, (Submodule.starProjection_apply_eq_zero_iff _).mpr (eigenBasis_orth W i hi),
      sub_zero]

/-- Every diagonal entry is at most `1 / T_d(1 + 2λ)` in modulus. -/
theorem abs_errEntry_le (hW : Unitary W) {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hgap : ∀ (z : ℂ) (v : V), v ≠ 0 → W v = z • v → z ≠ 1 → 2 * b ≤ ‖z - 1‖) (d : ℕ)
    (i : Fin (Module.finrank ℂ V)) : |errEntry W b d i| ≤ (filterNorm b d)⁻¹ := by
  have hb : b ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith, hb1⟩
  rw [errEntry]
  split_ifs with hi
  · rw [abs_zero]
    exact inv_nonneg.mpr (filterNorm_pos hb d).le
  · have hlo := hW.defect_eigen_lower b hgap hb0 i hi
    have hhi := eigenValues_le_four hW i
    exact abs_filterVal_le hb (by linarith) (by linarith) d

/-- **Pointwise error**: `‖(F_{b,d}(W) - P) x‖ ≤ ‖x‖ / T_d(1 + 2λ)`. -/
theorem norm_filterOp_sub_apply_le (hW : Unitary W) {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hgap : ∀ (z : ℂ) (v : V), v ≠ 0 → W v = z • v → z ≠ 1 → 2 * b ≤ ‖z - 1‖) (d : ℕ)
    (x : V) : ‖(filterOp W b d - fixedProj W) x‖ ≤ (filterNorm b d)⁻¹ * ‖x‖ := by
  have hb : b ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith, hb1⟩
  set e := eigenBasis (defect W) (defect_adjoint W)
  set M := filterOp W b d - fixedProj W
  have hM : ∀ i, M (e i) = ((errEntry W b d i : ℝ) : ℂ) • e i :=
    filterOp_sub_apply_eigenBasis hW hb d
  have hN : 0 ≤ (filterNorm b d)⁻¹ := inv_nonneg.mpr (filterNorm_pos hb d).le
  have hsq : ‖M x‖ ^ 2 ≤ ((filterNorm b d)⁻¹ * ‖x‖) ^ 2 := by
    rw [norm_sq_eq_sum e (M x), mul_pow, norm_sq_eq_sum e x, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [inner_basis_apply e M _ hM i x, norm_mul, mul_pow, Complex.norm_real,
      Real.norm_eq_abs]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact pow_le_pow_left₀ (abs_nonneg _) (abs_errEntry_le hW hb0 hb1 hgap d i) 2
  exact le_of_pow_le_pow_left₀ two_ne_zero (by positivity) hsq

/-- **The error bound** `‖F_{b,d}(W) - P‖ ≤ 1 / T_d(1 + 2λ) = sech(2 d artanh b)`, for every
degree `d`. -/
theorem norm_filterOp_sub_le (hW : Unitary W) {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hgap : ∀ (z : ℂ) (v : V), v ≠ 0 → W v = z • v → z ≠ 1 → 2 * b ≤ ‖z - 1‖) (d : ℕ) :
    ‖filterOp W b d - fixedProj W‖ ≤ (filterNorm b d)⁻¹ :=
  ContinuousLinearMap.opNorm_le_bound _
    (inv_nonneg.mpr (filterNorm_pos ⟨by linarith, hb1⟩ d).le)
    (norm_filterOp_sub_apply_le hW hb0 hb1 hgap d)

/-- **Equation `qls:eq:cheberror`**: at the degree `d = ⌈arcosh(1/δ) / (2 artanh b)⌉`,
`‖F_{b,d}(W) - P‖ ≤ δ`. -/
theorem norm_filterOp_sub_fixedProj_le (hW : Unitary W) {b δ : ℝ} (hb0 : 0 < b) (hb1 : b < 1)
    (hgap : ∀ (z : ℂ) (v : V), v ≠ 0 → W v = z • v → z ≠ 1 → 2 * b ≤ ‖z - 1‖)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    ‖filterOp W b (chebDegree b δ) - fixedProj W‖ ≤ δ :=
  (norm_filterOp_sub_le hW hb0.le hb1 hgap _).trans
    (inv_filterNorm_chebDegree_le hb0 hb1 hδ0 hδ1)

/-- **Spectral orthogonality** (equation `qls:eq:filterprobability`):
`‖F_{b,d}(W) ψ‖² = ‖P ψ‖² + ‖(F_{b,d}(W) - P) ψ‖²`. -/
theorem norm_filterOp_apply_sq (hW : Unitary W) {b : ℝ} (hb : b ∈ Set.Ioo (-1 : ℝ) 1)
    (d : ℕ) (x : V) :
    ‖filterOp W b d x‖ ^ 2 =
      ‖fixedProj W x‖ ^ 2 + ‖(filterOp W b d - fixedProj W) x‖ ^ 2 := by
  set e := eigenBasis (defect W) (defect_adjoint W)
  set M := filterOp W b d - fixedProj W
  have hM : ∀ i, M (e i) = ((errEntry W b d i : ℝ) : ℂ) • e i :=
    filterOp_sub_apply_eigenBasis hW hb d
  have hPmem : fixedProj W x ∈ fixedSpace W := Submodule.starProjection_apply_mem _ x
  have hinner : inner ℂ (fixedProj W x) (M x) = 0 := by
    rw [inner_apply_diag e M _ hM]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : eigenValues (defect W) (defect_adjoint W) i = 0
    · simp [errEntry, hi]
    · have h0 : inner ℂ (e i) (fixedProj W x) = 0 :=
        (Submodule.mem_orthogonal' _ _).mp (eigenBasis_orth W i hi) _ hPmem
      rw [h0]
      simp
  have hsplit : filterOp W b d x = fixedProj W x + M x := by
    simp only [M, sub_apply]
    abel
  rw [hsplit]
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (fixedProj W x) (M x) hinner
  nlinarith [h]

/-- The filter probability lies in `[‖Pψ‖², ‖Pψ‖² + δ²‖ψ‖²]` at `d = chebDegree b δ`. -/
theorem filterOp_probability_bounds (hW : Unitary W) {b δ : ℝ} (hb0 : 0 < b) (hb1 : b < 1)
    (hgap : ∀ (z : ℂ) (v : V), v ≠ 0 → W v = z • v → z ≠ 1 → 2 * b ≤ ‖z - 1‖)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (x : V) :
    ‖fixedProj W x‖ ^ 2 ≤ ‖filterOp W b (chebDegree b δ) x‖ ^ 2 ∧
      ‖filterOp W b (chebDegree b δ) x‖ ^ 2 ≤ ‖fixedProj W x‖ ^ 2 + (δ * ‖x‖) ^ 2 := by
  have h1 := norm_filterOp_apply_sq hW ⟨by linarith, hb1⟩ (chebDegree b δ) x
  have h2 := (norm_filterOp_sub_apply_le hW hb0.le hb1 hgap (chebDegree b δ) x).trans
    (mul_le_mul_of_nonneg_right (inv_filterNorm_chebDegree_le hb0 hb1 hδ0 hδ1) (norm_nonneg x))
  have h3 := pow_le_pow_left₀ (norm_nonneg _) h2 2
  constructor <;> nlinarith [sq_nonneg ‖(filterOp W b (chebDegree b δ) - fixedProj W) x‖]

/-! ### Eigenvectors of `W` and the eigenphase hypothesis -/

omit [FiniteDimensional ℂ V] [CompleteSpace V] in
theorem pow_apply_of_eigen {A : V →L[ℂ] V} {z : ℂ} {v : V} (h : A v = z • v) (n : ℕ) :
    (A ^ n) v = z ^ n • v := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, mul_apply_eq_comp, h, map_smul, ih, smul_smul, ← pow_succ']

omit [FiniteDimensional ℂ V] in
/-- `W^j v = e^{ijθ} v` on an eigenvector `W v = e^{iθ} v`. -/
theorem wpow_apply_eigen (hW : Unitary W) {θ : ℝ} {v : V} (hv : v ≠ 0)
    (hWv : W v = Complex.exp (θ * Complex.I) • v) (j : ℤ) :
    wpow W j v = Complex.exp ((j : ℂ) * θ * Complex.I) • v := by
  rcases le_or_gt 0 j with hj | hj
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hj
    rw [wpow_natCast, pow_apply_of_eigen hWv, ← Complex.exp_nat_mul]
    congr 2
    push_cast
    ring
  · obtain ⟨n, hn⟩ := Int.exists_eq_neg_ofNat hj.le
    subst hn
    have hadj := hW.adjoint_eigen hv hWv
    rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I] at hadj
    rw [wpow_neg_natCast, pow_apply_of_eigen hadj, ← Complex.exp_nat_mul]
    congr 2
    push_cast
    ring

omit [FiniteDimensional ℂ V] in
/-- **The operator filter is the scalar filter on eigenvectors**: if `W v = e^{iθ} v` then
`F_{b,d}(W) v = F_{b,d}(e^{iθ}) v`. -/
theorem filterOp_apply_eigen (hW : Unitary W) {b : ℝ} (hb2 : b ^ 2 < 1) (d : ℕ) {θ : ℝ}
    {v : V} (hv : v ≠ 0) (hWv : W v = Complex.exp (θ * Complex.I) • v) :
    filterOp W b d v = ((filterFun b d θ : ℝ) : ℂ) • v := by
  rw [← laurent_eq hb2 d θ, Finset.sum_smul, filterOp, sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [smul_apply, wpow_apply_eigen hW hv hWv j, smul_smul]

/-- `|e^{iθ} - 1| = 2 |sin(θ/2)|`. -/
theorem norm_exp_mul_I_sub_one (θ : ℝ) :
    ‖Complex.exp (θ * Complex.I) - 1‖ = 2 * |Real.sin (θ / 2)| := by
  have hre : (Complex.exp (θ * Complex.I) - 1).re = Real.cos θ - 1 := by
    rw [Complex.sub_re, Complex.exp_ofReal_mul_I_re, Complex.one_re]
  have him : (Complex.exp (θ * Complex.I) - 1).im = Real.sin θ := by
    rw [Complex.sub_im, Complex.exp_ofReal_mul_I_im, Complex.one_im, sub_zero]
  have hsq : ‖Complex.exp (θ * Complex.I) - 1‖ ^ 2 = (2 * |Real.sin (θ / 2)|) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him, mul_pow, sq_abs]
    have hθ : θ = 2 * (θ / 2) := by ring
    rw [hθ, Real.cos_two_mul, Real.sin_two_mul, show 2 * (θ / 2) / 2 = θ / 2 by ring]
    have h := Real.sin_sq_add_cos_sq (θ / 2)
    linear_combination (4 * (Real.cos (θ / 2) ^ 2 - 1)) * h
  exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq

omit [FiniteDimensional ℂ V] in
/-- **The eigenphase hypothesis** of Proposition `qls:prop:chebyshev` (`|sin(θ/2)| ≥ b` for
every eigenphase `θ` with `e^{iθ} ≠ 1`) gives the chord form `|z - 1| ≥ 2b`. -/
theorem gap_of_phase (hW : Unitary W) {b : ℝ}
    (hphase : ∀ (θ : ℝ) (v : V), v ≠ 0 → W v = Complex.exp (θ * Complex.I) • v →
      Complex.exp (θ * Complex.I) ≠ 1 → b ≤ |Real.sin (θ / 2)|) :
    ∀ (z : ℂ) (v : V), v ≠ 0 → W v = z • v → z ≠ 1 → 2 * b ≤ ‖z - 1‖ := by
  intro z v hv hWv hz
  have hz1 := hW.norm_eigenvalue hv hWv
  have hzexp : Complex.exp (Complex.arg z * Complex.I) = z := by
    have h := Complex.norm_mul_exp_arg_mul_I z
    rw [hz1, Complex.ofReal_one, one_mul] at h
    exact h
  rw [← hzexp] at hWv hz ⊢
  rw [norm_exp_mul_I_sub_one]
  linarith [hphase (Complex.arg z) v hv hWv hz]

end

end ChebyshevFilter
