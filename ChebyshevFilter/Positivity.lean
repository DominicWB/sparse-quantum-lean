import ChebyshevFilter.Cone
import Mathlib.Algebra.Polynomial.HasseDeriv

set_option autoImplicit false

/-!
# Positivity of the shifted Chebyshev polynomial (equation `qls:eq:chebpositive`)

For `λ = b² / (1 - b²)` the filter of Proposition `qls:prop:chebyshev` is built from

`T_d(x + λ (x + 1)) = ∑_{k=0}^{d} (λ^k / k!) (x + 1)^k T_d^{(k)}(x)`

(`shifted_taylor`, an exact polynomial identity; `comp_X_add` is the Taylor expansion at a
polynomial increment). Every summand has nonnegative Chebyshev coefficients
(`Cone.lean`), so for `b² < 1` (`λ ≥ 0`) the shifted polynomial is a nonnegative combination of
`T_0, …, T_d` (`shifted_mem_cone`). Its Chebyshev coefficients `c_m = shiftCoeff b d m` are
therefore nonnegative and vanish for `m > d`, and `T_d(x + λ(x + 1)) = ∑_{m ≤ d} c_m T_m(x)`
(`eval_shifted_eq_sum`).
-/

namespace ChebyshevFilter

noncomputable section
open Polynomial NNReal
open Polynomial.Chebyshev (T)

/-! ### Taylor expansion at a polynomial increment -/

theorem monomial_comp_X_add (h : ℝ[X]) (i M : ℕ) (hi : i < M) (a : ℝ) :
    (monomial i a).comp (X + h) =
      ∑ k ∈ Finset.range M, h ^ k * hasseDeriv k (monomial i a) := by
  rw [monomial_comp, add_comm X h, add_pow]
  simp only [hasseDeriv_monomial]
  rw [← Finset.sum_range_add_sum_Ico _ (show i + 1 ≤ M by omega)]
  rw [Finset.sum_eq_zero (s := Finset.Ico (i + 1) M) (fun k hk => by
    rw [Nat.choose_eq_zero_of_lt (by simp only [Finset.mem_Ico] at hk; omega)]; simp)]
  rw [add_zero, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [← C_mul_X_pow_eq_monomial, map_mul, map_natCast]
  ring

/-- **Taylor expansion** `p(x + h) = ∑_k h^k (D^k p / k!)(x)` with a polynomial increment
`h`, written with Hasse derivatives. -/
theorem comp_X_add (p h : ℝ[X]) (M : ℕ) (hM : p.natDegree < M) :
    p.comp (X + h) = ∑ k ∈ Finset.range M, h ^ k * hasseDeriv k p := by
  have hp := as_sum_range' p M hM
  have hR : ∀ k, hasseDeriv k p =
      ∑ i ∈ Finset.range M, hasseDeriv k (monomial i (p.coeff i)) := by
    intro k
    conv_lhs => rw [hp]
    rw [map_sum]
  rw [Finset.sum_congr rfl (fun k _ => by rw [hR k, Finset.mul_sum]), Finset.sum_comm]
  conv_lhs => rw [hp]
  rw [sum_comp]
  exact Finset.sum_congr rfl (fun i hi => monomial_comp_X_add h i M (Finset.mem_range.mp hi) _)

/-! ### The shifted Chebyshev polynomial -/

/-- `λ = b² / (1 - b²)` (equation `qls:eq:chebdegree`). -/
def lam (b : ℝ) : ℝ := b ^ 2 / (1 - b ^ 2)

theorem lam_nonneg {b : ℝ} (hb : b ^ 2 < 1) : 0 ≤ lam b :=
  div_nonneg (sq_nonneg b) (by linarith)

/-- `T_d(x + λ (x + 1))`. -/
def shifted (b : ℝ) (d : ℕ) : ℝ[X] := (T ℝ d).comp (X + C (lam b) * (X + 1))

theorem eval_shifted (b : ℝ) (d : ℕ) (x : ℝ) :
    (shifted b d).eval x = (T ℝ d).eval ((1 + lam b) * x + lam b) := by
  rw [shifted, eval_comp]
  congr 1
  simp only [eval_add, eval_X, eval_mul, eval_C, eval_one]
  ring

theorem hasseDeriv_eq (k : ℕ) (p : ℝ[X]) :
    hasseDeriv k p = C ((k.factorial : ℝ)⁻¹) * derivative^[k] p := by
  rw [← factorial_smul_hasseDeriv, LinearMap.smul_apply, ← Nat.cast_smul_eq_nsmul ℝ,
    smul_eq_C_mul, ← mul_assoc, ← C_mul, inv_mul_cancel₀ (by positivity), C_1, one_mul]

/-- **Equation `qls:eq:chebpositive`**:
`T_d(x + λ(x + 1)) = ∑_{k=0}^{d} (λ^k / k!) (x + 1)^k T_d^{(k)}(x)`. -/
theorem shifted_taylor (b : ℝ) (d : ℕ) :
    shifted b d = ∑ k ∈ Finset.range (d + 1),
      C (lam b ^ k / k.factorial) * ((X + 1) ^ k * derivative^[k] (T ℝ d)) := by
  rw [shifted, comp_X_add _ _ (d + 1) (by rw [Chebyshev.natDegree_T]; simp)]
  apply Finset.sum_congr rfl
  intro k _
  rw [hasseDeriv_eq, mul_pow, ← C_pow, div_eq_mul_inv, C_mul]
  ring

/-- **Positivity**: for `λ ≥ 0`, `T_d(x + λ(x + 1))` is a nonnegative combination of
`T_0, …, T_d`. -/
theorem shifted_mem_cone {b : ℝ} (hb : b ^ 2 < 1) (d : ℕ) : shifted b d ∈ cone d := by
  rw [shifted_taylor]
  apply Submodule.sum_mem
  intro k hk
  have hk' : k ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  apply C_mul_mem (div_nonneg (pow_nonneg (lam_nonneg hb) k) (Nat.cast_nonneg _))
  have h := mul_mem (X_add_one_pow_mem k) (iterate_derivative_T_mem d k)
  rwa [show k + (d - k) = d by omega] at h

/-! ### Its Chebyshev coefficients -/

/-- The Chebyshev coefficients `c_m` of `T_d(x + λ(x + 1))`. -/
def shiftCoeff (b : ℝ) (d m : ℕ) : ℝ := chebCoeff (shifted b d) m

theorem shiftCoeff_nonneg {b : ℝ} (hb : b ^ 2 < 1) (d m : ℕ) : 0 ≤ shiftCoeff b d m :=
  chebCoeff_nonneg (shifted_mem_cone hb d) m

theorem shiftCoeff_eq_zero {b : ℝ} (hb : b ^ 2 < 1) {d m : ℕ} (hm : d < m) :
    shiftCoeff b d m = 0 :=
  chebCoeff_eq_zero (shifted_mem_cone hb d) hm

theorem shifted_eq_sum {b : ℝ} (hb : b ^ 2 < 1) (d : ℕ) :
    shifted b d = ∑ m ∈ Finset.range (d + 1), shiftCoeff b d m • T ℝ m :=
  eq_sum_chebCoeff (shifted_mem_cone hb d)

/-- `T_d((1 + λ) x + λ) = ∑_{m ≤ d} c_m T_m(x)` with `c_m ≥ 0`. -/
theorem eval_shifted_eq_sum {b : ℝ} (hb : b ^ 2 < 1) (d : ℕ) (x : ℝ) :
    (T ℝ d).eval ((1 + lam b) * x + lam b) =
      ∑ m ∈ Finset.range (d + 1), shiftCoeff b d m * (T ℝ m).eval x := by
  rw [← eval_shifted]
  conv_lhs => rw [shifted_eq_sum hb d]
  rw [eval_finsetSum]
  simp only [smul_eq_C_mul, eval_mul, eval_C]

end

end ChebyshevFilter
