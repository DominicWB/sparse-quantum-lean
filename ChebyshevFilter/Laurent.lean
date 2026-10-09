import ChebyshevFilter.Degree
import Mathlib.Algebra.BigOperators.Field

set_option autoImplicit false

/-!
# The Laurent coefficients of the filter

The filter of Proposition `qls:prop:chebyshev` is

`F_{b,d}(e^{iθ}) = T_d((1 + λ) cos θ + λ) / T_d(1 + 2λ)`  (equation `qls:eq:chebfilter`),

`filterFun b d θ`, the value `filterVal b d x` at `x = cos θ`. With the Chebyshev
coefficients `c_m ≥ 0` of `T_d(x + λ(x + 1))` (`Positivity.lean`) and `N = T_d(1 + 2λ)`, its
Laurent coefficients on the powers `-d, …, d` are

`p_0 = c_0 / N`, `p_{±m} = c_m / (2N)` (`filterCoeff`).

* `filterCoeff_nonneg`, `filterCoeff_eq_zero` (support in `[-d, d]`), `filterCoeff_neg`;
* `sum_filterCoeff`: `∑_j p_j = 1`;
* `laurent_eq`: `∑_{j=-d}^{d} p_j e^{ijθ} = F_{b,d}(e^{iθ})` for every real `θ`, from
  `T_m(cos θ) = cos(mθ)`;
* `filterFun_zero`: `F_{b,d}(1) = 1`;
* `abs_filterVal_le`: on `[-1, 1 - 2b²]`, `|F_{b,d}| ≤ 1 / T_d(1 + 2λ)`.
-/

namespace ChebyshevFilter

noncomputable section
open Polynomial
open Polynomial.Chebyshev (T)

/-- The filter as a function of `x = cos θ`: `T_d((1 + λ) x + λ) / T_d(1 + 2λ)`. -/
def filterVal (b : ℝ) (d : ℕ) (x : ℝ) : ℝ :=
  (T ℝ d).eval ((1 + lam b) * x + lam b) / filterNorm b d

/-- **The filter** `F_{b,d}(e^{iθ}) = T_d((1 + λ) cos θ + λ) / T_d(1 + 2λ)`
(equation `qls:eq:chebfilter`). -/
def filterFun (b : ℝ) (d : ℕ) (θ : ℝ) : ℝ := filterVal b d (Real.cos θ)

/-- **The Laurent coefficient** `p_j`: `p_0 = c_0 / N` and `p_j = c_{|j|} / (2N)` for
`j ≠ 0`, where `c_m` are the Chebyshev coefficients of `T_d(x + λ(x + 1))` and
`N = T_d(1 + 2λ)`. -/
def filterCoeff (b : ℝ) (d : ℕ) (j : ℤ) : ℝ :=
  (if j = 0 then shiftCoeff b d 0 else shiftCoeff b d j.natAbs / 2) / filterNorm b d

/-- A sum over `[-d, d]` in symmetric pairs. -/
theorem sum_Icc_symm {M : Type*} [AddCommMonoid M] (f : ℤ → M) (d : ℕ) :
    ∑ j ∈ Finset.Icc (-(d : ℤ)) d, f j =
      f 0 + ∑ k ∈ Finset.range d, (f ((k : ℤ) + 1) + f (-((k : ℤ) + 1))) := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hI : Finset.Icc (-((d + 1 : ℕ) : ℤ)) ((d + 1 : ℕ) : ℤ) =
        insert (-((d : ℤ) + 1)) (insert ((d : ℤ) + 1) (Finset.Icc (-(d : ℤ)) d)) := by
      ext j
      simp only [Finset.mem_Icc, Finset.mem_insert]
      push_cast
      omega
    rw [hI, Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_Icc]; omega),
      Finset.sum_insert (by simp only [Finset.mem_Icc]; omega), ih, Finset.sum_range_succ]
    abel

theorem filterCoeff_neg (b : ℝ) (d : ℕ) (j : ℤ) : filterCoeff b d (-j) = filterCoeff b d j := by
  simp only [filterCoeff, neg_eq_zero, Int.natAbs_neg]

theorem filterCoeff_zero (b : ℝ) (d : ℕ) :
    filterCoeff b d 0 = shiftCoeff b d 0 / filterNorm b d := by
  simp only [filterCoeff, if_true]

theorem filterCoeff_succ (b : ℝ) (d k : ℕ) :
    filterCoeff b d ((k : ℤ) + 1) = shiftCoeff b d (k + 1) / 2 / filterNorm b d := by
  have e : ((k : ℤ) + 1) = ((k + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [e, filterCoeff, if_neg (by omega), Int.natAbs_natCast]

/-- **Nonnegative coefficients.** -/
theorem filterCoeff_nonneg {b : ℝ} (hb : b ∈ Set.Ioo (-1 : ℝ) 1) (d : ℕ) (j : ℤ) :
    0 ≤ filterCoeff b d j := by
  have hb2 := sq_lt_one_of_mem hb
  unfold filterCoeff
  apply div_nonneg _ (filterNorm_pos hb d).le
  split_ifs
  · exact shiftCoeff_nonneg hb2 d 0
  · exact div_nonneg (shiftCoeff_nonneg hb2 d _) (by norm_num)

/-- **Powers `-d, …, d` only.** -/
theorem filterCoeff_eq_zero {b : ℝ} (hb : b ∈ Set.Ioo (-1 : ℝ) 1) {d : ℕ} {j : ℤ}
    (hj : j ∉ Finset.Icc (-(d : ℤ)) d) : filterCoeff b d j = 0 := by
  have hb2 := sq_lt_one_of_mem hb
  rw [Finset.mem_Icc] at hj
  have hj0 : j ≠ 0 := by rintro rfl; omega
  have hlt : d < j.natAbs := by omega
  rw [filterCoeff, if_neg hj0, shiftCoeff_eq_zero hb2 hlt, zero_div, zero_div]

/-- The Chebyshev form of the filter: `p_0 + ∑_{m=1}^{d} 2 p_m T_m(x) = F_{b,d}(x)`. -/
theorem filterCoeff_series {b : ℝ} (hb2 : b ^ 2 < 1) (d : ℕ) (x : ℝ) :
    filterCoeff b d 0 + ∑ k ∈ Finset.range d,
        2 * filterCoeff b d ((k : ℤ) + 1) * (T ℝ ((k + 1 : ℕ) : ℤ)).eval x =
      filterVal b d x := by
  rw [filterVal, eval_shifted_eq_sum hb2, Finset.sum_range_succ', add_div, Finset.sum_div,
    filterCoeff_zero, add_comm]
  congr 1
  · apply Finset.sum_congr rfl
    intro k _
    rw [filterCoeff_succ]
    ring
  · simp

theorem filterVal_one {b : ℝ} (hb : b ∈ Set.Ioo (-1 : ℝ) 1) (d : ℕ) : filterVal b d 1 = 1 := by
  rw [filterVal, show (1 + lam b) * 1 + lam b = 1 + 2 * lam b by ring, ← filterNorm,
    div_self (filterNorm_pos hb d).ne']

/-- **`F_{b,d}(1) = 1`.** -/
theorem filterFun_zero {b : ℝ} (hb : b ∈ Set.Ioo (-1 : ℝ) 1) (d : ℕ) : filterFun b d 0 = 1 := by
  rw [filterFun, Real.cos_zero, filterVal_one hb]

/-- **The coefficients sum to one.** -/
theorem sum_filterCoeff {b : ℝ} (hb : b ∈ Set.Ioo (-1 : ℝ) 1) (d : ℕ) :
    ∑ j ∈ Finset.Icc (-(d : ℤ)) d, filterCoeff b d j = 1 := by
  have h := filterCoeff_series (sq_lt_one_of_mem hb) d 1
  simp only [Chebyshev.T_eval_one, mul_one] at h
  rw [filterVal_one hb] at h
  rw [sum_Icc_symm, ← h]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [filterCoeff_neg]
  ring

theorem exp_add_exp_neg (a : ℝ) :
    Complex.exp (a * Complex.I) + Complex.exp (-a * Complex.I) = ((2 * Real.cos a : ℝ) : ℂ) := by
  rw [← Complex.two_cos]
  push_cast
  ring

/-- **The Laurent form** (equation `qls:eq:chebfilter`):
`∑_{j=-d}^{d} p_j e^{ijθ} = T_d((1 + λ) cos θ + λ) / T_d(1 + 2λ)`. -/
theorem laurent_eq {b : ℝ} (hb2 : b ^ 2 < 1) (d : ℕ) (θ : ℝ) :
    ∑ j ∈ Finset.Icc (-(d : ℤ)) d,
        ((filterCoeff b d j : ℝ) : ℂ) * Complex.exp ((j : ℂ) * θ * Complex.I) =
      ((filterFun b d θ : ℝ) : ℂ) := by
  rw [sum_Icc_symm, filterFun, ← filterCoeff_series hb2 d (Real.cos θ), Complex.ofReal_add,
    Complex.ofReal_sum]
  simp only [Int.cast_zero, zero_mul, Complex.exp_zero, mul_one]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  set a : ℝ := ((k + 1 : ℕ) : ℝ) * θ with ha
  have e1 : (((k : ℤ) + 1 : ℤ) : ℂ) * θ * Complex.I = (a : ℂ) * Complex.I := by
    rw [ha]; push_cast; ring
  have e2 : ((-((k : ℤ) + 1) : ℤ) : ℂ) * θ * Complex.I = -(a : ℂ) * Complex.I := by
    rw [ha]; push_cast; ring
  have e3 : ((((k + 1 : ℕ) : ℤ) : ℝ)) * θ = a := by rw [ha]; push_cast; ring
  rw [filterCoeff_neg, Chebyshev.T_real_cos, e1, e2, ← mul_add, exp_add_exp_neg, e3]
  push_cast
  ring

/-- **The residual amplitude**: on `[-1, 1 - 2b²]`, `|F_{b,d}(x)| ≤ 1 / T_d(1 + 2λ)`. -/
theorem abs_filterVal_le {b x : ℝ} (hb : b ∈ Set.Ioo (-1 : ℝ) 1) (hx1 : -1 ≤ x)
    (hx2 : x ≤ 1 - 2 * b ^ 2) (d : ℕ) : |filterVal b d x| ≤ (filterNorm b d)⁻¹ := by
  rw [filterVal, abs_div, abs_of_pos (filterNorm_pos hb d), div_eq_mul_inv]
  exact mul_le_of_le_one_left (inv_nonneg.mpr (filterNorm_pos hb d).le)
    (abs_T_affine_le_one (sq_lt_one_of_mem hb) hx1 hx2 d)

end

end ChebyshevFilter
