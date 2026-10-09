import ChebyshevFilter.Positivity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.SpecialFunctions.Artanh

set_option autoImplicit false

/-!
# The normalisation and the degree (equation `qls:eq:chebdegree`)

For `|b| < 1` and `λ = b² / (1 - b²)`:

* `one_add_two_lam`: `1 + 2λ = (1 + b²)/(1 - b²) = cosh(2 artanh b)`;
* `filterNorm_eq_cosh`: the normalisation `T_d(1 + 2λ) = cosh(2 d artanh b) ≥ 1`;
* `chebDegree b δ = ⌈arcosh(1/δ) / (2 artanh b)⌉` and
  `inv_filterNorm_chebDegree_le`: the residual amplitude `sech(2 d artanh b) ≤ δ`;
* `abs_affine_le_one`: for `x ∈ [-1, 1 - 2b²]` (that is, `x = cos θ` at a phase with
  `|sin(θ/2)| ≥ b`), the affine argument `(1 + λ) x + λ` lies in `[-1, 1]`, so
  `|T_d((1 + λ) x + λ)| ≤ 1` (`abs_T_affine_le_one`).
-/

namespace ChebyshevFilter

noncomputable section
open Polynomial
open Polynomial.Chebyshev (T)

/-- The normalisation `T_d(1 + 2λ)`. -/
def filterNorm (b : ℝ) (d : ℕ) : ℝ := (T ℝ d).eval (1 + 2 * lam b)

theorem sq_lt_one_of_mem {b : ℝ} (hb : b ∈ Set.Ioo (-1 : ℝ) 1) : b ^ 2 < 1 := by
  nlinarith [hb.1, hb.2]

/-- `1 + 2λ = (1 + b²)/(1 - b²) = cosh(2 artanh b)`. -/
theorem one_add_two_lam {b : ℝ} (hb : b ∈ Set.Ioo (-1 : ℝ) 1) :
    1 + 2 * lam b = Real.cosh (2 * Real.artanh b) := by
  have h : 0 < 1 - b ^ 2 := by linarith [sq_lt_one_of_mem hb]
  rw [Real.cosh_two_mul, Real.cosh_artanh hb, Real.sinh_artanh hb, div_pow, div_pow, one_pow,
    Real.sq_sqrt h.le]
  unfold lam
  field_simp
  ring

/-- **The normalisation** `T_d(1 + 2λ) = cosh(2 d artanh b)`. -/
theorem filterNorm_eq_cosh {b : ℝ} (hb : b ∈ Set.Ioo (-1 : ℝ) 1) (d : ℕ) :
    filterNorm b d = Real.cosh (2 * d * Real.artanh b) := by
  rw [filterNorm, one_add_two_lam hb, Chebyshev.T_real_cosh]
  congr 1
  push_cast
  ring

theorem one_le_filterNorm {b : ℝ} (hb : b ∈ Set.Ioo (-1 : ℝ) 1) (d : ℕ) :
    1 ≤ filterNorm b d := by
  rw [filterNorm_eq_cosh hb]
  exact Real.one_le_cosh _

theorem filterNorm_pos {b : ℝ} (hb : b ∈ Set.Ioo (-1 : ℝ) 1) (d : ℕ) : 0 < filterNorm b d :=
  lt_of_lt_of_le one_pos (one_le_filterNorm hb d)

/-- **The degree** `d = ⌈arcosh(1/δ) / (2 artanh b)⌉` of equation `qls:eq:chebdegree`. -/
def chebDegree (b δ : ℝ) : ℕ := ⌈Real.arcosh (1 / δ) / (2 * Real.artanh b)⌉₊

/-- **The residual amplitude** at the degree `chebDegree b δ`:
`sech(2 d artanh b) = 1 / T_d(1 + 2λ) ≤ δ`. -/
theorem inv_filterNorm_chebDegree_le {b δ : ℝ} (hb0 : 0 < b) (hb1 : b < 1) (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1) : (filterNorm b (chebDegree b δ))⁻¹ ≤ δ := by
  have hb : b ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith, hb1⟩
  have ha : 0 < Real.artanh b := Real.artanh_pos ⟨hb0, hb1⟩
  have h1δ : 1 ≤ 1 / δ := by rw [le_div_iff₀ hδ0]; linarith
  have hA : 0 ≤ Real.arcosh (1 / δ) := Real.arcosh_nonneg h1δ
  have hd : Real.arcosh (1 / δ) ≤ 2 * (chebDegree b δ) * Real.artanh b := by
    have h := Nat.le_ceil (Real.arcosh (1 / δ) / (2 * Real.artanh b))
    rw [div_le_iff₀ (by positivity)] at h
    unfold chebDegree
    linarith
  have hcosh : 1 / δ ≤ Real.cosh (2 * (chebDegree b δ) * Real.artanh b) := by
    rw [← Real.cosh_arcosh h1δ, Real.cosh_le_cosh, abs_of_nonneg hA,
      abs_of_nonneg (by positivity)]
    exact hd
  rw [filterNorm_eq_cosh hb, inv_le_comm₀ (by positivity) hδ0, ← one_div]
  exact hcosh

/-- For `x ∈ [-1, 1 - 2b²]` the affine argument `(1 + λ) x + λ` lies in `[-1, 1]`. -/
theorem abs_affine_le_one {b x : ℝ} (hb : b ^ 2 < 1) (hx1 : -1 ≤ x)
    (hx2 : x ≤ 1 - 2 * b ^ 2) : |(1 + lam b) * x + lam b| ≤ 1 := by
  have hl := lam_nonneg hb
  have hl2 : lam b * (2 - 2 * b ^ 2) = 2 * b ^ 2 := by
    have h : 1 - b ^ 2 ≠ 0 := by linarith
    unfold lam
    field_simp
  rw [abs_le]
  constructor
  · nlinarith [mul_nonneg hl (show 0 ≤ x + 1 by linarith)]
  · nlinarith [mul_le_mul_of_nonneg_left (show x + 1 ≤ 2 - 2 * b ^ 2 by linarith) hl]

theorem abs_T_affine_le_one {b x : ℝ} (hb : b ^ 2 < 1) (hx1 : -1 ≤ x)
    (hx2 : x ≤ 1 - 2 * b ^ 2) (d : ℕ) : |(T ℝ d).eval ((1 + lam b) * x + lam b)| ≤ 1 :=
  Chebyshev.abs_eval_T_real_le_one _ (abs_affine_le_one hb hx1 hx2)

end

end ChebyshevFilter
