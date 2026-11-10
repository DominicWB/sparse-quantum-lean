import LargeSparsityCore.Scalars
import LargeSparsityCore.CoreFilter
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import SparseHamiltonian.TimeSchedule

set_option autoImplicit false

/-!
# The parameters of the large-sparsity core

For a real parameter `s ≥ 1` (the sparsity; the moment parameter `σ = sμ²/η²` in Appendix B),
rescaled time `τ = η|t|` (`η²|t|/μ` in Appendix B) and precision `ε`, put `L = log(1/ε)`,
`h = log(e + L/τ)` and `r = L/h` (`hs:eq:optimal-parameters`). In the core regime
`sτ ≥ L h` (`opt:eq:core-regime`) with `h ≥ 10⁴` (`opt:eq:core-explicit`) the construction uses

* `q_* = √(sτ/r)`, the even integer `p = 2⌈π q_* + 1⌉`, the angle `π/p` (`theta`) and
  `2q = cot(π/p)` (`opt:eq:phase-choice`), so that `q_* ≤ q ≤ 2 q_*` and `2πq ≤ p ≤ 7q`;
* `k = ⌈4r⌉`, `m = ⌈32 h k⌉` (`opt:eq:filter-orders`, `C_bulk = 32`, `C_order = 4`);
* the bulk average length `B₀ = ⌈64 q/h⌉` with `ρ₀ = 8/B₀` and `Q₀ = 2q/h`, so that
  `B₀ ρ₀ = 8` and `ρ₀ Q₀ ≤ 1/4` (`opt:eq:bulk-contour`);
* the isolated radius `ζ = hτ/(100 q k)` (`opt:eq:zeta`, `c₀ = 1/100`);
* the total Cayley time `a = sτ/q` and the degree `d = m(B₀ - 1) + k(p - 1)`.

This module defines these quantities and proves the scalar inequalities used by the core:
the regime facts (`Regime`), the geometry of the isolated phases, the small-step mesh, the
degree bounds and the final filter estimate `‖f(D_g)‖ ≤ ε/3`.

The choice `B₀ = ⌈64q/h⌉`, `ρ₀ = 8/B₀`, `Q₀ = 2q/h` replaces the manuscript's
`Q₀ = ⌈max{1, 2q/h}⌉`, `B₀ = 32 Q₀`, `ρ₀ = 1/(4Q₀)`; both give `B₀ ρ₀ = 8` and the same order.
The phase count is `p = 2⌈π q_* + 1⌉` rather than the least eligible even `p`.
-/

namespace LargeSparsityCore.Parameters

noncomputable section

open Real

/-- `L = log(1/ε)`. -/
def Lval (ε : ℝ) : ℝ := Real.log (1 / ε)

/-- `h = log(e + L/τ)`. -/
def hval (τ ε : ℝ) : ℝ := Real.log (Real.exp 1 + Lval ε / τ)

/-- `r = L/h`. -/
def rval (τ ε : ℝ) : ℝ := Lval ε / hval τ ε

/-- `q_* = √(sτ/r)`. -/
def qstar (s : ℝ) (τ ε : ℝ) : ℝ := Real.sqrt (s * τ / rval τ ε)

/-- The even integer `p = 2⌈π q_* + 1⌉`. -/
def pval (s : ℝ) (τ ε : ℝ) : ℕ := 2 * ⌈π * qstar s τ ε + 1⌉₊

/-- `θ = π/p`. -/
def theta (s : ℝ) (τ ε : ℝ) : ℝ := π / pval s τ ε

/-- `q = cot(π/p)/2`. -/
def qval (s : ℝ) (τ ε : ℝ) : ℝ := Real.cot (theta s τ ε) / 2

/-- `k = ⌈4r⌉`. -/
def kval (τ ε : ℝ) : ℕ := ⌈4 * rval τ ε⌉₊

/-- `m = ⌈32 h k⌉`. -/
def mval (τ ε : ℝ) : ℕ := ⌈32 * hval τ ε * kval τ ε⌉₊

/-- `B₀ = ⌈64 q/h⌉`. -/
def B0 (s : ℝ) (τ ε : ℝ) : ℕ := ⌈64 * qval s τ ε / hval τ ε⌉₊

/-- `ρ₀ = 8/B₀`. -/
def rho0 (s : ℝ) (τ ε : ℝ) : ℝ := 8 / (B0 s τ ε : ℝ)

/-- `Q₀ = 2q/h`. -/
def Q0 (s : ℝ) (τ ε : ℝ) : ℝ := 2 * qval s τ ε / hval τ ε

/-- `ζ = hτ/(100 q k)`. -/
def zeta (s : ℝ) (τ ε : ℝ) : ℝ := hval τ ε * τ / (100 * qval s τ ε * kval τ ε)

/-- `a = sτ/q`. -/
def aval (s : ℝ) (τ ε : ℝ) : ℝ := s * τ / qval s τ ε

/-- The filter degree `d = m(B₀ - 1) + k(p - 1)`. -/
def degree (s : ℝ) (τ ε : ℝ) : ℕ :=
  ProductFilter.degree (B0 s τ ε) (mval τ ε) (pval s τ ε) (kval τ ε)

/-- The square root of the isolated weight, `√(h/(2s))`. -/
def sw (s : ℝ) (τ ε : ℝ) : ℝ := Real.sqrt (hval τ ε / (2 * s))

/-- The square root of the bulk second moment, `√(2q²/s)`. -/
def sm (s : ℝ) (τ ε : ℝ) : ℝ := Real.sqrt (2 * qval s τ ε ^ 2 / s)

/-- The small-step requirement on the number of slots, `a (2 + 8/ζ + 6Q₀)`. -/
def meshMin (s : ℝ) (τ ε : ℝ) : ℝ := aval s τ ε * (2 + 8 / zeta s τ ε + 6 * Q0 s τ ε)

/-- The number of chronological slots `N_s` (`opt:eq:core-mesh`). -/
def steps (s : ℝ) (τ ε : ℝ) : ℕ :=
  1 + ⌈max (SparseHamiltonian.TimeSchedule.threshold (aval s τ ε) (ε / 3)) (meshMin s τ ε)⌉₊

/-- The slot weight `v = a/N_s`. -/
def wval (s : ℝ) (τ ε : ℝ) : ℝ := aval s τ ε / steps s τ ε

/-- The regime hypotheses of the large-sparsity core. -/
structure Regime (s : ℝ) (τ ε : ℝ) : Prop where
  one_le_s : 1 ≤ s
  one_le_τ : 1 ≤ τ
  ε_pos : 0 < ε
  ε_le : ε ≤ 1 / 64
  h_large : 10 ^ 4 ≤ hval τ ε
  core : Lval ε * hval τ ε ≤ s * τ

theorem pval_ge (s : ℝ) (τ ε : ℝ) : 2 * π * qstar s τ ε + 2 ≤ (pval s τ ε : ℝ) := by
  have h := Nat.le_ceil (π * qstar s τ ε + 1)
  unfold pval
  push_cast
  linarith

theorem steps_pos (s : ℝ) (τ ε : ℝ) : 0 < steps s τ ε := by
  unfold steps
  omega

theorem le_steps (s : ℝ) (τ ε : ℝ) :
    max (SparseHamiltonian.TimeSchedule.threshold (aval s τ ε) (ε / 3)) (meshMin s τ ε) ≤
      (steps s τ ε : ℝ) := by
  have h := Nat.le_ceil
    (max (SparseHamiltonian.TimeSchedule.threshold (aval s τ ε) (ε / 3)) (meshMin s τ ε))
  unfold steps
  push_cast
  linarith

theorem steps_mul_w (s : ℝ) (τ ε : ℝ) : (steps s τ ε : ℝ) * wval s τ ε = aval s τ ε := by
  have h : (steps s τ ε : ℝ) ≠ 0 := by exact_mod_cast (steps_pos s τ ε).ne'
  unfold wval
  field_simp

theorem w_le_quarter (s : ℝ) (τ ε : ℝ) : wval s τ ε ≤ 1 / 4 := by
  have hT : (0 : ℝ) < steps s τ ε := by exact_mod_cast steps_pos s τ ε
  have h := (le_max_left _ _).trans (le_steps s τ ε)
  have h4 := (le_max_left _ _).trans h
  unfold wval
  rw [div_le_iff₀ hT]
  linarith

theorem kval_ge (τ ε : ℝ) : 4 * rval τ ε ≤ (kval τ ε : ℝ) := Nat.le_ceil _

theorem mval_ge (τ ε : ℝ) : 32 * hval τ ε * kval τ ε ≤ (mval τ ε : ℝ) := Nat.le_ceil _

theorem B0_ge (s : ℝ) (τ ε : ℝ) : 64 * qval s τ ε / hval τ ε ≤ (B0 s τ ε : ℝ) := Nat.le_ceil _

theorem sm_nonneg (s : ℝ) (τ ε : ℝ) : 0 ≤ sm s τ ε := Real.sqrt_nonneg _

theorem sw_nonneg (s : ℝ) (τ ε : ℝ) : 0 ≤ sw s τ ε := Real.sqrt_nonneg _

/-- `3 + y ≤ e^y` for `y ≥ 2`. -/
theorem three_add_le_exp (y : ℝ) (hy : 2 ≤ y) : 3 + y ≤ Real.exp y := by
  have := Real.quadratic_le_exp_of_nonneg (by linarith : 0 ≤ y)
  nlinarith

/-- The point bound of the global resolvent, simplified with `w ≤ a`. -/
theorem pointBound_le {Q₀ sw sm w a ip im ζ2 : ℝ} (hw : 0 ≤ w) (hwa : w ≤ a) (hip : 0 ≤ ip)
    (him : 0 ≤ im) (hζ2 : 0 ≤ ζ2) (hsw : 0 ≤ sw) (hsm : 0 ≤ sm) (hQ : 0 ≤ Q₀) :
    CoreFilter.pointBound Q₀ sw sm w a ip im ζ2 ≤
      (ip + im + 4 / 3 * Q₀ + 5 * a * (sw * (ip + im) + 2 / 3 * (1 + sm)) ^ 2) *
        Real.exp (2 * a * ζ2 * (sw * (ip + im) + 2 / 3 * (1 + sm)) ^ 2) := by
  unfold CoreFilter.pointBound
  simp only
  set X := sw * (ip + im) + 2 / 3 * (1 + sm)
  have ha : 0 ≤ a := hw.trans hwa
  have hX2 : 0 ≤ X ^ 2 := sq_nonneg _
  have hE1 : 1 ≤ Real.exp (16 / 9 * a * (ζ2 * X ^ 2)) :=
    Real.one_le_exp (by positivity)
  have hE2 : Real.exp (16 / 9 * a * (ζ2 * X ^ 2)) ≤ Real.exp (2 * a * ζ2 * X ^ 2) :=
    Real.exp_le_exp.mpr (by nlinarith [mul_nonneg (mul_nonneg ha hζ2) hX2])
  set E := Real.exp (16 / 9 * a * (ζ2 * X ^ 2))
  have hr : 0 ≤ ip + im + 4 / 3 * Q₀ := by positivity
  have h1 : ip + im + 4 / 3 * Q₀ ≤ (ip + im + 4 / 3 * Q₀) * E := le_mul_of_one_le_right hr hE1
  have h2 : 4 / 3 * w * X ^ 2 ≤ 4 / 3 * a * X ^ 2 * E := by
    have h3 : 4 / 3 * w * X ^ 2 ≤ 4 / 3 * a * X ^ 2 := by gcongr
    have h4 : 4 / 3 * a * X ^ 2 ≤ 4 / 3 * a * X ^ 2 * E :=
      le_mul_of_one_le_right (by positivity) hE1
    linarith
  calc ip + im + 4 / 3 * Q₀ + 4 / 3 * w * X ^ 2 + 32 / 9 * a * X ^ 2 * E ≤
        (ip + im + 4 / 3 * Q₀) * E + 4 / 3 * a * X ^ 2 * E + 32 / 9 * a * X ^ 2 * E := by
        linarith
    _ ≤ (ip + im + 4 / 3 * Q₀ + 5 * a * X ^ 2) * E := by nlinarith [mul_nonneg ha hX2]
    _ ≤ (ip + im + 4 / 3 * Q₀ + 5 * a * X ^ 2) * Real.exp (2 * a * ζ2 * X ^ 2) := by
        gcongr

/-- The point bound is nonnegative for nonnegative data. -/
theorem pointBound_nonneg {Q₀ sw sm w a ip im ζ2 : ℝ} (hw : 0 ≤ w) (ha : 0 ≤ a) (hip : 0 ≤ ip)
    (him : 0 ≤ im) (hQ : 0 ≤ Q₀) : 0 ≤ CoreFilter.pointBound Q₀ sw sm w a ip im ζ2 := by
  unfold CoreFilter.pointBound
  simp only
  positivity

/-- The value bound on the isolated circles, `F = (1 + ζ)^{B₀ m} (ζ p (1 + ζ)^p/2)^k`. -/
def Fval (s : ℝ) (τ ε : ℝ) : ℝ :=
  (1 + zeta s τ ε) ^ (B0 s τ ε * mval τ ε) *
    (zeta s τ ε * pval s τ ε * (1 + zeta s τ ε) ^ pval s τ ε / 2) ^ kval τ ε

/-- The catalyst moment `ν = (1 + 2q²(1 + h)/s)/2` (`opt:eq:nu-W`). -/
def nu (s : ℝ) (τ ε : ℝ) : ℝ := (1 + 2 * qval s τ ε ^ 2 * (1 + hval τ ε) / s) / 2

namespace Regime

variable {s : ℝ} {τ ε : ℝ} (R : Regime s τ ε)
include R

theorem τ_pos : 0 < τ := lt_of_lt_of_le one_pos R.one_le_τ

theorem L_pos : 0 < Lval ε := by
  unfold Lval
  apply Real.log_pos
  rw [one_div, one_lt_inv₀ R.ε_pos]
  linarith [R.ε_le]

theorem h_pos : 0 < hval τ ε := lt_of_lt_of_le (by norm_num) R.h_large

/-- `e^h = e + L/τ`. -/
theorem exp_h : Real.exp (hval τ ε) = Real.exp 1 + Lval ε / τ := by
  unfold hval
  rw [Real.exp_log (by have := R.L_pos; have := R.τ_pos; positivity)]

/-- `L/τ = e^h - e`. -/
theorem x_eq : Lval ε / τ = Real.exp (hval τ ε) - Real.exp 1 := by
  rw [R.exp_h]
  ring

/-- `L/τ ≥ e^h/2`. -/
theorem x_ge : Real.exp (hval τ ε) / 2 ≤ Lval ε / τ := by
  rw [R.x_eq]
  have h1 : Real.exp 1 ≤ Real.exp (hval τ ε) / 2 := by
    have : Real.exp 1 * 2 ≤ Real.exp 1 * Real.exp 1 := by
      gcongr
      linarith [Real.add_one_le_exp (1 : ℝ)]
    rw [← Real.exp_add] at this
    have h2 : Real.exp (1 + 1) ≤ Real.exp (hval τ ε) :=
      Real.exp_le_exp.mpr (by linarith [R.h_large])
    linarith
  linarith

/-- A polynomial lower bound for `e^{h/4}`. -/
theorem exp_quarter_ge : (hval τ ε) ^ 3 / 384 ≤ Real.exp (hval τ ε / 4) := by
  have h := Real.pow_div_factorial_le_exp (x := hval τ ε / 4) (by linarith [R.h_pos]) 3
  have : (hval τ ε / 4) ^ 3 / (Nat.factorial 3 : ℝ) = (hval τ ε) ^ 3 / 384 := by
    norm_num [Nat.factorial]
    ring
  linarith

theorem exp_quarter_le : Real.exp (hval τ ε / 4) ≤ Real.exp (hval τ ε) / 2 := by
  have hh := R.h_large
  have : Real.exp (hval τ ε / 4) * 2 ≤ Real.exp (hval τ ε / 4) * Real.exp (3 * hval τ ε / 4) := by
    gcongr
    have := Real.add_one_le_exp (3 * hval τ ε / 4)
    linarith
  rw [← Real.exp_add] at this
  rw [show hval τ ε / 4 + 3 * hval τ ε / 4 = hval τ ε by ring] at this
  linarith

/-- `L/τ ≥ h³/384`. -/
theorem x_ge_cube : hval τ ε ^ 3 / 384 ≤ Lval ε / τ := by
  linarith [R.exp_quarter_ge, R.exp_quarter_le, R.x_ge]

/-- `L/τ ≥ h²` (with room to spare). -/
theorem x_ge_sq : 2 * (hval τ ε) ^ 2 ≤ Lval ε / τ := by
  have hh := R.h_large
  have h1 := R.exp_quarter_ge
  have h2 := R.exp_quarter_le
  have h3 : 2 * (hval τ ε) ^ 2 ≤ (hval τ ε) ^ 3 / 384 := by
    have : (hval τ ε) ^ 3 = hval τ ε * (hval τ ε) ^ 2 := by ring
    rw [this]
    nlinarith [sq_nonneg (hval τ ε)]
  linarith [R.x_ge]

/-- `r = L/h > 0`. -/
theorem r_pos : 0 < rval τ ε := div_pos R.L_pos R.h_pos

/-- `r ≥ hτ`, in the form `h² τ ≤ L` (used as `hτ ≤ r`). -/
theorem h_tau_le_r : hval τ ε * τ ≤ rval τ ε := by
  have h1 := R.x_ge_sq
  have hτ := R.τ_pos
  have hh := R.h_pos
  unfold rval
  rw [le_div_iff₀ hh]
  rw [le_div_iff₀ hτ] at h1
  nlinarith

/-- `q_*² = sτ/r ≥ h²`. -/
theorem qstar_sq : qstar s τ ε ^ 2 = s * τ / rval τ ε := by
  unfold qstar
  rw [Real.sq_sqrt (div_nonneg (mul_nonneg (by linarith [R.one_le_s]) R.τ_pos.le) R.r_pos.le)]

theorem h_le_qstar : hval τ ε ≤ qstar s τ ε := by
  apply Real.le_sqrt_of_sq_le
  rw [le_div_iff₀ R.r_pos]
  unfold rval
  rw [show hval τ ε ^ 2 * (Lval ε / hval τ ε) = Lval ε * hval τ ε by
    field_simp [R.h_pos.ne']]
  exact R.core

theorem qstar_pos : 0 < qstar s τ ε := lt_of_lt_of_le R.h_pos R.h_le_qstar

theorem p_le : (pval s τ ε : ℝ) ≤ 2 * π * qstar s τ ε + 4 := by
  have hq := R.qstar_pos
  have h := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ π * qstar s τ ε + 1 by positivity)
  unfold pval
  push_cast
  linarith

theorem p_pos : (0 : ℝ) < pval s τ ε := by
  have := pval_ge s τ ε
  have := R.qstar_pos
  have := Real.pi_pos
  nlinarith

theorem p_large : 2 * π * 10 ^ 4 ≤ (pval s τ ε : ℝ) := by
  have h1 := pval_ge s τ ε
  have h2 := R.h_le_qstar
  have h3 := R.h_large
  have := Real.pi_pos
  nlinarith

theorem theta_pos : 0 < theta s τ ε := div_pos Real.pi_pos R.p_pos

theorem p_mul_theta : (pval s τ ε : ℝ) * theta s τ ε = π := by
  unfold theta
  field_simp [R.p_pos.ne']

theorem theta_le : theta s τ ε ≤ 1 / 10 ^ 4 := by
  unfold theta
  rw [div_le_div_iff₀ R.p_pos (by norm_num)]
  have := R.p_large
  have := Real.pi_pos
  nlinarith

theorem theta_lt_half_pi : theta s τ ε < π / 2 := by
  have h := R.theta_le
  have := Real.pi_gt_three
  linarith

theorem sin_theta_pos : 0 < Real.sin (theta s τ ε) :=
  Real.sin_pos_of_pos_of_lt_pi R.theta_pos (by linarith [R.theta_lt_half_pi, Real.pi_pos])

theorem cos_theta_pos : 0 < Real.cos (theta s τ ε) :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [R.theta_pos, Real.pi_pos], R.theta_lt_half_pi⟩

/-- `cot θ ≤ 1/θ`. -/
theorem cot_le : Real.cot (theta s τ ε) ≤ 1 / theta s τ ε := by
  have hθ := R.theta_pos
  have hs := R.sin_theta_pos
  have hc := R.cos_theta_pos
  have ht := Real.le_tan hθ.le R.theta_lt_half_pi
  rw [Real.tan_eq_sin_div_cos, le_div_iff₀ hc] at ht
  rw [Real.cot_eq_cos_div_sin, div_le_div_iff₀ hs hθ]
  linarith

/-- `cot θ ≥ 1/θ - θ/2`. -/
theorem cot_ge : 1 / theta s τ ε - theta s τ ε / 2 ≤ Real.cot (theta s τ ε) := by
  have hθ := R.theta_pos
  have hs := R.sin_theta_pos
  have hc := R.cos_theta_pos
  have h1 := Real.sin_le hθ.le
  have h2 := Real.one_sub_sq_div_two_le_cos (x := theta s τ ε)
  rw [Real.cot_eq_cos_div_sin, le_div_iff₀ hs]
  have e : (1 / theta s τ ε - theta s τ ε / 2) = (1 - theta s τ ε ^ 2 / 2) / theta s τ ε := by
    field_simp
  rw [e, div_mul_eq_mul_div, div_le_iff₀ hθ]
  have hpos : 0 ≤ 1 - theta s τ ε ^ 2 / 2 := by
    have := R.theta_le
    nlinarith
  calc (1 - theta s τ ε ^ 2 / 2) * Real.sin (theta s τ ε) ≤
        Real.cos (theta s τ ε) * Real.sin (theta s τ ε) := by gcongr
    _ ≤ Real.cos (theta s τ ε) * theta s τ ε := by gcongr

/-- `q ≤ p/(2π)`. -/
theorem q_le_p : qval s τ ε ≤ (pval s τ ε : ℝ) / (2 * π) := by
  have h := R.cot_le
  have e : 1 / theta s τ ε = (pval s τ ε : ℝ) / π := by
    unfold theta
    field_simp
  rw [e] at h
  unfold qval
  calc Real.cot (theta s τ ε) / 2 ≤ (pval s τ ε : ℝ) / π / 2 := by linarith
    _ = (pval s τ ε : ℝ) / (2 * π) := by ring

/-- `q ≥ p/(2π) - π/(4p)`. -/
theorem q_ge_p : (pval s τ ε : ℝ) / (2 * π) - π / (4 * pval s τ ε) ≤ qval s τ ε := by
  have h := R.cot_ge
  have hp := R.p_pos
  have e1 : 1 / theta s τ ε = (pval s τ ε : ℝ) / π := by
    unfold theta
    field_simp
  have e2 : theta s τ ε / 2 = π / (2 * pval s τ ε) := by
    unfold theta
    field_simp
  rw [e1, e2] at h
  unfold qval
  have : (pval s τ ε : ℝ) / (2 * π) - π / (4 * pval s τ ε) =
      ((pval s τ ε : ℝ) / π - π / (2 * pval s τ ε)) / 2 := by
    field_simp
    ring
  rw [this]
  linarith

theorem q_ge_qstar : qstar s τ ε ≤ qval s τ ε := by
  have h1 := R.q_ge_p
  have h2 := pval_ge s τ ε
  have hp := R.p_large
  have hpi := Real.pi_gt_three
  have hpi4 := Real.pi_lt_four
  have hq := R.qstar_pos
  have hp0 := R.p_pos
  have h3 : π / (4 * pval s τ ε) ≤ 1 / π := by
    rw [div_le_div_iff₀ (by positivity) Real.pi_pos]
    nlinarith
  have h4 : qstar s τ ε + 1 / π ≤ (pval s τ ε : ℝ) / (2 * π) := by
    rw [le_div_iff₀ (by positivity)]
    have : (qstar s τ ε + 1 / π) * (2 * π) = 2 * π * qstar s τ ε + 2 := by
      field_simp
    linarith
  linarith

theorem h_le_q : hval τ ε ≤ qval s τ ε := R.h_le_qstar.trans R.q_ge_qstar

theorem q_pos : 0 < qval s τ ε := lt_of_lt_of_le R.h_pos R.h_le_q

theorem q_large : 10 ^ 4 ≤ qval s τ ε := R.h_large.trans R.h_le_q

theorem q_le_two_qstar : qval s τ ε ≤ 2 * qstar s τ ε := by
  have h1 := R.q_le_p
  have h2 := R.p_le
  have hq := R.qstar_pos
  have hqh := R.h_le_qstar
  have hh := R.h_large
  have hpi := Real.pi_gt_three
  have h3 : (pval s τ ε : ℝ) / (2 * π) ≤ qstar s τ ε + 2 / π := by
    rw [div_le_iff₀ (by positivity)]
    have : (qstar s τ ε + 2 / π) * (2 * π) = 2 * π * qstar s τ ε + 4 := by
      field_simp
      ring
    linarith
  have h4 : 2 / π ≤ qstar s τ ε := by
    rw [div_le_iff₀ Real.pi_pos]
    nlinarith
  linarith

theorem two_pi_q_le_p : 2 * π * qval s τ ε ≤ (pval s τ ε : ℝ) := by
  have h := R.q_le_p
  rw [le_div_iff₀ (by positivity)] at h
  linarith

theorem p_le_seven_q : (pval s τ ε : ℝ) ≤ 7 * qval s τ ε := by
  have h1 := R.q_ge_p
  have hp := R.p_large
  have hp0 := R.p_pos
  have hq := R.q_large
  have hpi := Real.pi_gt_three
  have hpi4 := Real.pi_lt_four
  have h2 : π / (4 * pval s τ ε) ≤ 1 / 10 ^ 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have h3 : (pval s τ ε : ℝ) / (2 * π) ≤ qval s τ ε + 1 / 10 ^ 4 := by linarith
  rw [div_le_iff₀ (by positivity)] at h3
  have hpi' := Real.pi_lt_d2
  nlinarith

theorem five_q_le_p_sub_one : 5 * qval s τ ε ≤ (pval s τ ε : ℝ) - 1 := by
  have h := R.two_pi_q_le_p
  have hq := R.q_large
  have hpi := Real.pi_gt_three
  nlinarith


theorem k_le : (kval τ ε : ℝ) ≤ 4 * rval τ ε + 1 :=
  (Nat.ceil_lt_add_one (by linarith [R.r_pos])).le

theorem k_pos : (0 : ℝ) < kval τ ε := lt_of_lt_of_le (by linarith [R.r_pos]) (kval_ge τ ε)

theorem one_le_k : 1 ≤ kval τ ε := by
  have := R.k_pos
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by intro h; rw [h] at this; simp at this)

theorem one_le_k_real : (1 : ℝ) ≤ kval τ ε := by exact_mod_cast R.one_le_k

/-- `4hτ ≤ k`. -/
theorem h_tau_le_k : 4 * (hval τ ε * τ) ≤ kval τ ε := by
  have := R.h_tau_le_r
  linarith [kval_ge τ ε]

/-- `4L ≤ hk`. -/
theorem L_le_hk : 4 * Lval ε ≤ hval τ ε * kval τ ε := by
  have h1 := kval_ge τ ε
  have hh := R.h_pos
  have e : hval τ ε * (4 * rval τ ε) = 4 * Lval ε := by
    unfold rval
    field_simp
  nlinarith


theorem m_le : (mval τ ε : ℝ) ≤ 33 * hval τ ε * kval τ ε := by
  have h := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 32 * hval τ ε * kval τ ε by
    have := R.h_pos; have := R.k_pos; positivity)
  have : (1 : ℝ) ≤ hval τ ε * kval τ ε := by nlinarith [R.h_large, R.one_le_k_real]
  unfold mval
  linarith

theorem one_le_m : 1 ≤ mval τ ε := by
  have h := mval_ge τ ε
  have : (1 : ℝ) ≤ mval τ ε := by nlinarith [R.h_large, R.one_le_k_real]
  exact_mod_cast this


theorem B0_le : (B0 s τ ε : ℝ) ≤ 65 * qval s τ ε / hval τ ε := by
  have hq := R.q_pos
  have hh := R.h_pos
  have h := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 64 * qval s τ ε / hval τ ε by positivity)
  have h1 : (1 : ℝ) ≤ qval s τ ε / hval τ ε := by
    rw [le_div_iff₀ hh]
    linarith [R.h_le_q]
  have : 64 * qval s τ ε / hval τ ε + 1 ≤ 65 * qval s τ ε / hval τ ε := by
    have e1 : 64 * qval s τ ε / hval τ ε = 64 * (qval s τ ε / hval τ ε) := by ring
    have e2 : 65 * qval s τ ε / hval τ ε = 65 * (qval s τ ε / hval τ ε) := by ring
    rw [e1, e2]
    linarith
  unfold B0
  linarith

theorem B0_pos : (0 : ℝ) < B0 s τ ε := by
  have := B0_ge s τ ε
  have := R.q_pos
  have := R.h_pos
  have : (0 : ℝ) < 64 * qval s τ ε / hval τ ε := by positivity
  linarith

theorem one_le_B0 : 1 ≤ B0 s τ ε := by
  have h := R.B0_pos
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by intro h0; rw [h0] at h; simp at h)

theorem rho0_pos : 0 < rho0 s τ ε := div_pos (by norm_num) R.B0_pos

theorem B0_mul_rho0 : (B0 s τ ε : ℝ) * rho0 s τ ε = 8 := by
  unfold rho0
  field_simp [R.B0_pos.ne']

theorem rho0_le : rho0 s τ ε ≤ hval τ ε / (8 * qval s τ ε) := by
  have hq := R.q_pos
  have hh := R.h_pos
  unfold rho0
  rw [div_le_div_iff₀ R.B0_pos (by positivity)]
  have := B0_ge s τ ε
  rw [div_le_iff₀ hh] at this
  linarith

theorem rho0_ge : 8 * hval τ ε / (65 * qval s τ ε) ≤ rho0 s τ ε := by
  have hq := R.q_pos
  have hh := R.h_pos
  unfold rho0
  rw [div_le_div_iff₀ (by positivity) R.B0_pos]
  have := R.B0_le
  rw [le_div_iff₀ hh] at this
  linarith

theorem Q0_ge : 2 ≤ Q0 s τ ε := by
  unfold Q0
  rw [le_div_iff₀ R.h_pos]
  linarith [R.h_le_q]

theorem rho0_mul_Q0 : rho0 s τ ε * Q0 s τ ε ≤ 1 / 4 := by
  have hq := R.q_pos
  have hh := R.h_pos
  have h1 := R.rho0_le
  have hQ : 0 ≤ Q0 s τ ε := by linarith [R.Q0_ge]
  calc rho0 s τ ε * Q0 s τ ε ≤ hval τ ε / (8 * qval s τ ε) * Q0 s τ ε :=
        mul_le_mul_of_nonneg_right h1 hQ
    _ = 1 / 4 := by
        unfold Q0
        field_simp
        ring

theorem zeta_pos : 0 < zeta s τ ε := by
  unfold zeta
  have := R.h_pos; have := R.τ_pos; have := R.q_pos; have := R.k_pos
  positivity

/-- `qζ = hτ/(100k)`. -/
theorem q_mul_zeta : qval s τ ε * zeta s τ ε = hval τ ε * τ / (100 * kval τ ε) := by
  unfold zeta
  field_simp [R.q_pos.ne']

theorem q_mul_zeta_le : qval s τ ε * zeta s τ ε ≤ 1 / 400 := by
  rw [R.q_mul_zeta, div_le_div_iff₀ (by linarith [R.k_pos]) (by norm_num)]
  linarith [R.h_tau_le_k]

theorem zeta_mul_Q0 : zeta s τ ε * Q0 s τ ε ≤ 1 / 50 := by
  have e : zeta s τ ε * Q0 s τ ε = τ / (50 * kval τ ε) := by
    unfold zeta Q0
    field_simp [R.q_pos.ne', R.h_pos.ne']
    ring
  rw [e, div_le_div_iff₀ (by linarith [R.k_pos]) (by norm_num)]
  have := R.h_tau_le_k
  have := R.h_large
  have := R.τ_pos
  nlinarith

theorem a_pos : 0 < aval s τ ε := by
  unfold aval
  have : (0 : ℝ) < s := by linarith [R.one_le_s]
  have := R.τ_pos; have := R.q_pos
  positivity

/-- `sτ = q_*² r`. -/
theorem s_tau_eq : (s : ℝ) * τ = qstar s τ ε ^ 2 * rval τ ε := by
  rw [R.qstar_sq]
  field_simp [R.r_pos.ne']

/-- `a ≤ q r`. -/
theorem a_le_qr : aval s τ ε ≤ qval s τ ε * rval τ ε := by
  unfold aval
  rw [div_le_iff₀ R.q_pos, R.s_tau_eq]
  have h1 := R.q_ge_qstar
  have h2 := R.qstar_pos
  have h3 := R.r_pos
  have : qstar s τ ε ^ 2 ≤ qval s τ ε ^ 2 := pow_le_pow_left₀ h2.le h1 2
  nlinarith

/-- `a ρ₀ ≤ L/8`. -/
theorem a_rho0_le : aval s τ ε * rho0 s τ ε ≤ Lval ε / 8 := by
  have h1 := R.a_le_qr
  have h2 := R.rho0_le
  have hq := R.q_pos
  have hh := R.h_pos
  have ha := R.a_pos
  calc aval s τ ε * rho0 s τ ε ≤ qval s τ ε * rval τ ε * (hval τ ε / (8 * qval s τ ε)) :=
        mul_le_mul h1 h2 R.rho0_pos.le (by have := R.r_pos; positivity)
    _ = Lval ε / 8 := by
        unfold rval
        field_simp

/-- `a ζ ≤ k/1600`. -/
theorem a_zeta_le : aval s τ ε * zeta s τ ε ≤ kval τ ε / 1600 := by
  have h1 := R.a_le_qr
  have h2 := R.q_mul_zeta
  have hk := R.k_pos
  have hr := R.r_pos
  have hrk : rval τ ε ≤ kval τ ε / 4 := by linarith [kval_ge τ ε]
  have hhk : hval τ ε * τ / (100 * kval τ ε) ≤ 1 / 400 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith [R.h_tau_le_k]
  calc aval s τ ε * zeta s τ ε ≤ qval s τ ε * rval τ ε * zeta s τ ε :=
        mul_le_mul_of_nonneg_right h1 R.zeta_pos.le
    _ = rval τ ε * (qval s τ ε * zeta s τ ε) := by ring
    _ = rval τ ε * (hval τ ε * τ / (100 * kval τ ε)) := by rw [h2]
    _ ≤ (kval τ ε / 4) * (1 / 400) :=
        mul_le_mul hrk hhk (by have := R.h_pos; have := R.τ_pos; positivity) (by positivity)
    _ = kval τ ε / 1600 := by ring

/-- `a sw²/ζ = 50k`. -/
theorem a_sw_sq_div_zeta : aval s τ ε * sw s τ ε ^ 2 / zeta s τ ε = 50 * kval τ ε := by
  have hs : (0 : ℝ) < s := by linarith [R.one_le_s]
  unfold aval sw zeta
  rw [Real.sq_sqrt (by have := R.h_pos; positivity)]
  field_simp [R.q_pos.ne', R.h_pos.ne', R.τ_pos.ne', R.k_pos.ne']
  ring

/-- `q²/s ≤ 4hτ/L`. -/
theorem q_sq_div_s : qval s τ ε ^ 2 / s ≤ 4 * hval τ ε * τ / Lval ε := by
  have hs : (0 : ℝ) < s := by linarith [R.one_le_s]
  have h1 := R.q_le_two_qstar
  have hq := R.q_pos
  have h2 : qval s τ ε ^ 2 ≤ 4 * qstar s τ ε ^ 2 := by nlinarith
  rw [R.qstar_sq] at h2
  rw [div_le_div_iff₀ hs R.L_pos]
  have e : 4 * ((s : ℝ) * τ / rval τ ε) = 4 * hval τ ε * τ * s / Lval ε := by
    unfold rval
    field_simp [R.L_pos.ne', R.h_pos.ne']
  rw [e, le_div_iff₀ R.L_pos] at h2
  linarith

/-- `4hτ/L ≤ 2/h` (from `L/τ ≥ 2h²`). -/
theorem four_h_tau_div_L : 4 * hval τ ε * τ / Lval ε ≤ 2 / hval τ ε := by
  have h1 := R.x_ge_sq
  have hτ := R.τ_pos
  have hh := R.h_pos
  have hL := R.L_pos
  rw [div_le_div_iff₀ hL hh]
  rw [le_div_iff₀ hτ] at h1
  nlinarith

/-- `2q²(1 + h)/s ≤ 1`; in particular `ν ≤ 1`. -/
theorem second_le_one : 2 * qval s τ ε ^ 2 * (1 + hval τ ε) / s ≤ 1 := by
  have hs : (0 : ℝ) < s := by linarith [R.one_le_s]
  have h1 := R.q_sq_div_s
  have h2 := R.x_ge_cube
  have hh := R.h_large
  have hh0 := R.h_pos
  have hτ := R.τ_pos
  have hL := R.L_pos
  have h3 : 4 * hval τ ε * τ / Lval ε ≤ 1536 / hval τ ε ^ 2 := by
    rw [div_le_div_iff₀ hL (by positivity)]
    rw [le_div_iff₀ hτ] at h2
    have : hval τ ε ^ 3 / 384 * τ * 4 * 384 / hval τ ε = 4 * hval τ ε ^ 2 * τ := by
      field_simp
    nlinarith [mul_pos hτ hh0]
  have h4 : qval s τ ε ^ 2 / s ≤ 1536 / hval τ ε ^ 2 := h1.trans h3
  have e : 2 * qval s τ ε ^ 2 * (1 + hval τ ε) / s = 2 * (1 + hval τ ε) * (qval s τ ε ^ 2 / s) := by
    ring
  have h5 : 2 * (1 + hval τ ε) * (1536 / hval τ ε ^ 2) ≤ 1 := by
    rw [mul_div_assoc', div_le_one (by positivity)]
    nlinarith
  rw [e]
  calc 2 * (1 + hval τ ε) * (qval s τ ε ^ 2 / s) ≤ 2 * (1 + hval τ ε) * (1536 / hval τ ε ^ 2) :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
    _ ≤ 1 := h5

theorem sm_le : sm s τ ε ≤ 1 / 8 := by
  have hs : (0 : ℝ) < s := by linarith [R.one_le_s]
  have h1 := R.q_sq_div_s
  have h2 := R.four_h_tau_div_L
  have hh := R.h_large
  unfold sm
  rw [Real.sqrt_le_left (by norm_num)]
  have h3 : 2 * qval s τ ε ^ 2 / s = 2 * (qval s τ ε ^ 2 / s) := by ring
  rw [h3]
  have h4 : 2 / hval τ ε ≤ 2 / 10 ^ 4 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hh
  nlinarith



theorem sw_sq : sw s τ ε ^ 2 = hval τ ε / (2 * s) := by
  have hs : (0 : ℝ) < s := by linarith [R.one_le_s]
  unfold sw
  rw [Real.sq_sqrt (by have := R.h_pos; positivity)]

/-- `sw q ≤ 1`. -/
theorem sw_mul_q : sw s τ ε * qval s τ ε ≤ 1 := by
  have hs : (0 : ℝ) < s := by linarith [R.one_le_s]
  have hq := R.q_pos
  have hh := R.h_pos
  have h2 := R.q_sq_div_s
  have h3 := R.four_h_tau_div_L
  have hsq : (sw s τ ε * qval s τ ε) ^ 2 ≤ 1 := by
    rw [mul_pow, R.sw_sq]
    have e : hval τ ε / (2 * s) * qval s τ ε ^ 2 = hval τ ε / 2 * (qval s τ ε ^ 2 / s) := by
      field_simp
    rw [e]
    calc hval τ ε / 2 * (qval s τ ε ^ 2 / s) ≤ hval τ ε / 2 * (2 / hval τ ε) :=
          mul_le_mul_of_nonneg_left (h2.trans h3) (by positivity)
      _ = 1 := by field_simp
  have h0 : 0 ≤ sw s τ ε * qval s τ ε := mul_nonneg (sw_nonneg s τ ε) hq.le
  nlinarith

/-- `sw/ρ₀ ≤ 1/24`. -/
theorem sw_div_rho0 : sw s τ ε / rho0 s τ ε ≤ 1 / 24 := by
  have hq := R.q_pos
  have hh := R.h_pos
  have hρ := R.rho0_pos
  have h1 := R.rho0_ge
  have hinv : 1 / rho0 s τ ε ≤ 65 * qval s τ ε / (8 * hval τ ε) := by
    rw [div_le_div_iff₀ hρ (by positivity)]
    rw [div_le_iff₀ (by positivity)] at h1
    linarith
  calc sw s τ ε / rho0 s τ ε = sw s τ ε * (1 / rho0 s τ ε) := by ring
    _ ≤ sw s τ ε * (65 * qval s τ ε / (8 * hval τ ε)) :=
        mul_le_mul_of_nonneg_left hinv (sw_nonneg s τ ε)
    _ = 65 / (8 * hval τ ε) * (sw s τ ε * qval s τ ε) := by ring
    _ ≤ 65 / (8 * hval τ ε) * 1 := by gcongr; exact R.sw_mul_q
    _ ≤ 1 / 24 := by
        rw [mul_one, div_le_div_iff₀ (by positivity) (by norm_num)]
        linarith [R.h_large]

/-! ### The isolated phases -/

theorem lamp_eq : CayleyBlocks.lamp (qval s τ ε) = Complex.exp (2 * theta s τ ε * Complex.I) :=
  Scalars.lamp_eq_exp _ R.sin_theta_pos.ne'

theorem lamm_eq :
    CayleyBlocks.lamm (qval s τ ε) = Complex.exp (2 * (-theta s τ ε : ℝ) * Complex.I) :=
  Scalars.lamm_eq_exp _ R.sin_theta_pos.ne'

theorem lamp_pow : CayleyBlocks.lamp (qval s τ ε) ^ pval s τ ε = 1 := by
  rw [R.lamp_eq]
  exact Scalars.exp_pow_eq_one _ _ (Or.inl R.p_mul_theta)

theorem lamm_pow : CayleyBlocks.lamm (qval s τ ε) ^ pval s τ ε = 1 := by
  rw [R.lamm_eq]
  exact Scalars.exp_pow_eq_one _ _ (Or.inr (by rw [mul_neg, R.p_mul_theta]))

/-- `2ζ ≤ |λ₊ - λ₋|`. -/
theorem sep :
    2 * zeta s τ ε ≤ ‖CayleyBlocks.lamp (qval s τ ε) - CayleyBlocks.lamm (qval s τ ε)‖ := by
  have hq := R.q_pos
  have h1 := Scalars.norm_lamp_sub_lamm (qval s τ ε) (by linarith [R.q_large])
  have h2 := R.q_mul_zeta_le
  have h3 : 2 * zeta s τ ε ≤ 1 / qval s τ ε := by
    rw [le_div_iff₀ hq]
    linarith
  linarith

/-- The isolated circles lie well inside the bulk circle: `|λ_± - 1| + ζ ≤ ρ₀/2`. -/
theorem inside_aux : 1 / qval s τ ε + zeta s τ ε ≤ rho0 s τ ε / 2 := by
  have hq := R.q_pos
  have hh := R.h_pos
  have h1 := R.q_mul_zeta_le
  have h2 := R.rho0_ge
  have hz : zeta s τ ε ≤ 1 / (400 * qval s τ ε) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  have h3 : 1 / qval s τ ε + 1 / (400 * qval s τ ε) ≤ 8 * hval τ ε / (65 * qval s τ ε) / 2 := by
    rw [show 1 / qval s τ ε + 1 / (400 * qval s τ ε) = (401 / 400) / qval s τ ε by
      field_simp; norm_num]
    rw [show 8 * hval τ ε / (65 * qval s τ ε) / 2 = (4 * hval τ ε / 65) / qval s τ ε by
      field_simp; ring]
    apply div_le_div_of_nonneg_right _ hq.le
    have := R.h_large
    linarith
  linarith

theorem lamp_inside : ‖CayleyBlocks.lamp (qval s τ ε) - 1‖ + zeta s τ ε ≤ rho0 s τ ε / 2 := by
  have := Scalars.norm_lamp_sub_one_le (qval s τ ε) R.q_pos
  linarith [R.inside_aux]

theorem lamm_inside : ‖CayleyBlocks.lamm (qval s τ ε) - 1‖ + zeta s τ ε ≤ rho0 s τ ε / 2 := by
  have := Scalars.norm_lamm_sub_one_le (qval s τ ε) R.q_pos
  linarith [R.inside_aux]

/-! ### The mesh -/

theorem w_nonneg : 0 ≤ wval s τ ε := div_nonneg R.a_pos.le (Nat.cast_nonneg _)

theorem w_le_a : wval s τ ε ≤ aval s τ ε := by
  unfold wval
  have h1 : (1 : ℝ) ≤ steps s τ ε := by exact_mod_cast steps_pos s τ ε
  exact div_le_self R.a_pos.le h1

theorem cubic_le : (steps s τ ε : ℝ) * wval s τ ε ^ 3 ≤ ε / 3 := by
  have hT : (0 : ℝ) < steps s τ ε := by exact_mod_cast steps_pos s τ ε
  have hε : 0 < ε / 3 := by have := R.ε_pos; positivity
  have ha := R.a_pos
  have h := (le_max_left _ _).trans (le_steps s τ ε)
  have hsq := (le_max_right _ _).trans h
  have hratio : 0 ≤ aval s τ ε ^ 3 / (ε / 3) := by positivity
  have hsq2 : aval s τ ε ^ 3 / (ε / 3) ≤ (steps s τ ε : ℝ) ^ 2 := by
    calc aval s τ ε ^ 3 / (ε / 3) = (Real.sqrt (aval s τ ε ^ 3 / (ε / 3))) ^ 2 :=
          (Real.sq_sqrt hratio).symm
      _ ≤ (steps s τ ε : ℝ) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hsq 2
  have e : (steps s τ ε : ℝ) * wval s τ ε ^ 3 = aval s τ ε ^ 3 / (steps s τ ε : ℝ) ^ 2 := by
    unfold wval
    field_simp
  rw [e, div_le_iff₀ (by positivity)]
  rw [div_le_iff₀ hε] at hsq2
  linarith

theorem small_step :
    wval s τ ε * (1 + 2 * (2 / zeta s τ ε + 4 / 3 * Q0 s τ ε)) ≤ 1 / 2 := by
  have hT : (0 : ℝ) < steps s τ ε := by exact_mod_cast steps_pos s τ ε
  have hζ := R.zeta_pos
  have hQ := R.Q0_ge
  have ha := R.a_pos
  have hm := (le_max_right _ _).trans (le_steps s τ ε)
  have hden : 0 < 2 + 8 / zeta s τ ε + 6 * Q0 s τ ε := by positivity
  have hw : wval s τ ε ≤ 1 / (2 + 8 / zeta s τ ε + 6 * Q0 s τ ε) := by
    unfold wval
    rw [div_le_div_iff₀ hT hden]
    unfold meshMin at hm
    linarith
  calc wval s τ ε * (1 + 2 * (2 / zeta s τ ε + 4 / 3 * Q0 s τ ε)) ≤
        1 / (2 + 8 / zeta s τ ε + 6 * Q0 s τ ε) * (1 + 2 * (2 / zeta s τ ε + 4 / 3 * Q0 s τ ε)) :=
        mul_le_mul_of_nonneg_right hw (by positivity)
    _ ≤ 1 / 2 := by
        rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ hden (by norm_num)]
        have : 0 ≤ Q0 s τ ε := by linarith
        have e : (8 : ℝ) / zeta s τ ε = 4 * (2 / zeta s τ ε) := by ring
        rw [e]
        nlinarith

/-! ### Exponential bounds -/

theorem L_large : 2 * (10 ^ 4) ^ 2 ≤ Lval ε := by
  have h1 := R.x_ge_sq
  have hτ := R.one_le_τ
  have hh := R.h_large
  rw [le_div_iff₀ R.τ_pos] at h1
  have : 2 * (10 ^ 4) ^ 2 ≤ 2 * hval τ ε ^ 2 := by gcongr
  nlinarith

theorem eps_eq : ε = Real.exp (-Lval ε) := by
  unfold Lval
  rw [one_div, Real.log_inv, neg_neg, Real.exp_log R.ε_pos]

/-- `e^{3616} h² ≤ 2 e^{h/2}`. -/
theorem exp_h_bound : Real.exp 3616 * hval τ ε ^ 2 ≤ 2 * Real.exp (hval τ ε / 2) := by
  have hh := R.h_large
  have h1 := Real.pow_div_factorial_le_exp (x := hval τ ε / 8) (by linarith) 3
  have h1' : hval τ ε ^ 2 ≤ Real.exp (hval τ ε / 8) := by
    have : (hval τ ε / 8) ^ 3 / (Nat.factorial 3 : ℝ) = hval τ ε ^ 3 / 3072 := by
      norm_num [Nat.factorial]
      ring
    rw [this] at h1
    have : hval τ ε ^ 2 ≤ hval τ ε ^ 3 / 3072 := by
      rw [le_div_iff₀ (by norm_num)]
      have : hval τ ε ^ 3 = hval τ ε * hval τ ε ^ 2 := by ring
      rw [this]
      nlinarith [sq_nonneg (hval τ ε)]
    linarith
  have h2 : Real.exp 3616 ≤ Real.exp (3 * hval τ ε / 8) := Real.exp_le_exp.mpr (by linarith)
  have h3 : Real.exp (hval τ ε / 2) = Real.exp (hval τ ε / 8) * Real.exp (3 * hval τ ε / 8) := by
    rw [← Real.exp_add]
    ring_nf
  rw [h3]
  calc Real.exp 3616 * hval τ ε ^ 2 ≤ Real.exp (3 * hval τ ε / 8) * Real.exp (hval τ ε / 8) := by
        gcongr
    _ ≤ 2 * (Real.exp (hval τ ε / 8) * Real.exp (3 * hval τ ε / 8)) := by
        have := Real.exp_pos (hval τ ε / 8)
        have := Real.exp_pos (3 * hval τ ε / 8)
        nlinarith

/-- `hτ/k ≤ h² e^{-h}/2`. -/
theorem h_tau_div_k : hval τ ε * τ / kval τ ε ≤ hval τ ε ^ 2 * Real.exp (-hval τ ε) / 2 := by
  have hk := R.k_pos
  have hh := R.h_pos
  have hτ := R.τ_pos
  have hL := R.L_pos
  have h1 := kval_ge τ ε
  have h2 := R.x_ge
  have hx : Real.exp (hval τ ε) / 2 * τ ≤ Lval ε := by
    rw [le_div_iff₀ hτ] at h2
    linarith
  have hk' : 4 * Lval ε / hval τ ε ≤ kval τ ε := by
    have : 4 * rval τ ε = 4 * Lval ε / hval τ ε := by unfold rval; ring
    linarith
  rw [div_le_iff₀ hk, Real.exp_neg]
  have hexp := Real.exp_pos (hval τ ε)
  rw [div_le_iff₀ hh] at hk'
  have : hval τ ε * τ * (2 * Real.exp (hval τ ε)) ≤ hval τ ε ^ 2 * kval τ ε := by
    nlinarith
  field_simp
  nlinarith

/-! ### The final filter estimate -/

/-- The isolated resolvent factor: `ζ M₁ ≤ e^{3609 k}`. -/
theorem iso_le :
    zeta s τ ε * CoreFilter.isoBound (Q0 s τ ε) (sw s τ ε) (sm s τ ε) (wval s τ ε) (aval s τ ε)
      (zeta s τ ε) (‖CayleyBlocks.lamp (qval s τ ε) - CayleyBlocks.lamm (qval s τ ε)‖ -
        zeta s τ ε) ≤ Real.exp (3609 * kval τ ε) := by
  set ζ := zeta s τ ε with hζdef
  set g := ‖CayleyBlocks.lamp (qval s τ ε) - CayleyBlocks.lamm (qval s τ ε)‖ - ζ with hgdef
  have hζ : 0 < ζ := R.zeta_pos
  have hg : ζ ≤ g := by have := R.sep; rw [hgdef]; linarith
  have hgpos : 0 < g := hζ.trans_le hg
  have hk := R.k_pos
  have hk1 := R.one_le_k_real
  have hsw := sw_nonneg s τ ε
  have hsm := sm_nonneg s τ ε
  have hsm8 := R.sm_le
  have hQ := R.Q0_ge
  have ha := R.a_pos
  have hw := R.w_nonneg
  have hwa := R.w_le_a
  have hPB := pointBound_le (Q₀ := Q0 s τ ε) (sm := sm s τ ε) hw hwa (inv_nonneg.mpr hζ.le)
    (inv_nonneg.mpr hgpos.le) (by positivity : 0 ≤ 2 * ζ) hsw hsm (by linarith)
  unfold CoreFilter.isoBound
  set X := sw s τ ε * (ζ⁻¹ + g⁻¹) + 2 / 3 * (1 + sm s τ ε) with hXdef
  have hginv : g⁻¹ ≤ ζ⁻¹ := inv_anti₀ hζ hg
  have hX : X ≤ 2 * (sw s τ ε / ζ) + 3 / 4 := by
    rw [hXdef]
    have : sw s τ ε * (ζ⁻¹ + g⁻¹) ≤ sw s τ ε * (2 * ζ⁻¹) := by
      gcongr
      linarith
    have e : sw s τ ε * (2 * ζ⁻¹) = 2 * (sw s τ ε / ζ) := by ring
    nlinarith
  have hX0 : 0 ≤ X := by positivity
  have hX2 : X ^ 2 ≤ 8 * (sw s τ ε / ζ) ^ 2 + 9 / 8 := by
    have h := pow_le_pow_left₀ hX0 hX 2
    nlinarith [sq_nonneg (2 * (sw s τ ε / ζ) - 3 / 4)]
  have haζ := R.a_zeta_le
  have hasw := R.a_sw_sq_div_zeta
  have hY : aval s τ ε * ζ * X ^ 2 ≤ 401 * kval τ ε := by
    have e : aval s τ ε * ζ * (8 * (sw s τ ε / ζ) ^ 2 + 9 / 8) =
        8 * (aval s τ ε * sw s τ ε ^ 2 / ζ) + 9 / 8 * (aval s τ ε * ζ) := by
      field_simp
    calc aval s τ ε * ζ * X ^ 2 ≤ aval s τ ε * ζ * (8 * (sw s τ ε / ζ) ^ 2 + 9 / 8) := by
          gcongr
      _ = 8 * (aval s τ ε * sw s τ ε ^ 2 / ζ) + 9 / 8 * (aval s τ ε * ζ) := e
      _ ≤ 8 * (50 * kval τ ε) + 9 / 8 * (kval τ ε / 1600) := by
          rw [hasw]
          gcongr
      _ ≤ 401 * kval τ ε := by linarith
  have hr : ζ * (ζ⁻¹ + g⁻¹ + 4 / 3 * Q0 s τ ε) ≤ 3 := by
    have h1 : ζ * ζ⁻¹ = 1 := mul_inv_cancel₀ hζ.ne'
    have h2 : ζ * g⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one hgpos]
      exact hg
    have h3 := R.zeta_mul_Q0
    nlinarith
  calc ζ * CoreFilter.pointBound (Q0 s τ ε) (sw s τ ε) (sm s τ ε) (wval s τ ε) (aval s τ ε) ζ⁻¹ g⁻¹
        (2 * ζ) ≤ ζ * ((ζ⁻¹ + g⁻¹ + 4 / 3 * Q0 s τ ε + 5 * aval s τ ε * X ^ 2) *
          Real.exp (2 * aval s τ ε * (2 * ζ) * X ^ 2)) := by
        gcongr
    _ = (ζ * (ζ⁻¹ + g⁻¹ + 4 / 3 * Q0 s τ ε) + 5 * (aval s τ ε * ζ * X ^ 2)) *
          Real.exp (4 * (aval s τ ε * ζ * X ^ 2)) := by ring_nf
    _ ≤ (3 + 5 * (401 * kval τ ε)) * Real.exp (4 * (401 * kval τ ε)) := by
        gcongr
    _ ≤ Real.exp (2005 * kval τ ε) * Real.exp (1604 * kval τ ε) := by
        have h1 : 3 + 5 * (401 * (kval τ ε : ℝ)) ≤ Real.exp (2005 * kval τ ε) := by
          have := three_add_le_exp (2005 * kval τ ε) (by linarith)
          linarith
        have h2 : Real.exp (4 * (401 * (kval τ ε : ℝ))) ≤ Real.exp (1604 * kval τ ε) :=
          le_of_eq (by ring_nf)
        exact mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = Real.exp (3609 * kval τ ε) := by rw [← Real.exp_add]; ring_nf

/-! ### The final filter estimate -/

/-- The filter is at most `F` on the circle `|z - λ₊| = ζ`. -/
theorem F_lamp (z : ℂ) (hz : ‖z - CayleyBlocks.lamp (qval s τ ε)‖ = zeta s τ ε) :
    ‖SparseHamiltonian.FilterCoefficients.geometricAverage (B0 s τ ε) z ^ mval τ ε *
      SparseHamiltonian.FilterCoefficients.geometricAverage (pval s τ ε) z ^ kval τ ε‖ ≤
        Fval s τ ε :=
  Scalars.norm_filter_root_le _ z _ _ _ _ R.zeta_pos.le (CayleyBlocks.norm_lamp _) R.lamp_pow
    (Scalars.lamp_ne_one _) hz.le

/-- The filter is at most `F` on the circle `|z - λ₋| = ζ`. -/
theorem F_lamm (z : ℂ) (hz : ‖z - CayleyBlocks.lamm (qval s τ ε)‖ = zeta s τ ε) :
    ‖SparseHamiltonian.FilterCoefficients.geometricAverage (B0 s τ ε) z ^ mval τ ε *
      SparseHamiltonian.FilterCoefficients.geometricAverage (pval s τ ε) z ^ kval τ ε‖ ≤
        Fval s τ ε :=
  Scalars.norm_filter_root_le _ z _ _ _ _ R.zeta_pos.le (CayleyBlocks.norm_lamm _) R.lamm_pow
    (Scalars.lamm_ne_one _) hz.le

/-- `F ≤ e^{7k} (hτ/k)^k`. -/
theorem F_le : Fval s τ ε ≤ Real.exp (7 * kval τ ε) * (hval τ ε * τ / kval τ ε) ^ kval τ ε := by
  have hζ := R.zeta_pos
  have hk := R.k_pos
  have hq := R.q_pos
  have hh := R.h_pos
  have hτ := R.τ_pos
  have hqζ := R.q_mul_zeta_le
  have hexp : 1 + zeta s τ ε ≤ Real.exp (zeta s τ ε) := by
    have := Real.add_one_le_exp (zeta s τ ε)
    linarith
  have h1 : (1 + zeta s τ ε) ^ (B0 s τ ε * mval τ ε) ≤ Real.exp (6 * kval τ ε) := by
    have hBm : ((B0 s τ ε * mval τ ε : ℕ) : ℝ) * zeta s τ ε ≤ 6 * kval τ ε := by
      have hB := R.B0_le
      have hm := R.m_le
      have hm0 : (0 : ℝ) ≤ mval τ ε := Nat.cast_nonneg _
      push_cast
      calc (B0 s τ ε : ℝ) * mval τ ε * zeta s τ ε ≤
            (65 * qval s τ ε / hval τ ε) * (33 * hval τ ε * kval τ ε) * zeta s τ ε := by
            apply mul_le_mul_of_nonneg_right _ hζ.le
            exact mul_le_mul hB hm hm0 (by positivity)
        _ = 2145 * (qval s τ ε * zeta s τ ε) * kval τ ε := by
            field_simp
            ring
        _ ≤ 2145 * (1 / 400) * kval τ ε := by
            apply mul_le_mul_of_nonneg_right _ hk.le
            linarith
        _ ≤ 6 * kval τ ε := by linarith
    calc (1 + zeta s τ ε) ^ (B0 s τ ε * mval τ ε) ≤
          Real.exp (zeta s τ ε) ^ (B0 s τ ε * mval τ ε) :=
          pow_le_pow_left₀ (by linarith) hexp _
      _ = Real.exp (((B0 s τ ε * mval τ ε : ℕ) : ℝ) * zeta s τ ε) :=
          (Real.exp_nat_mul _ _).symm
      _ ≤ Real.exp (6 * kval τ ε) := Real.exp_le_exp.mpr hBm
  have h2 : zeta s τ ε * pval s τ ε * (1 + zeta s τ ε) ^ pval s τ ε / 2 ≤
      Real.exp 1 * (hval τ ε * τ / kval τ ε) := by
    have hp7 := R.p_le_seven_q
    have hpz : (pval s τ ε : ℝ) * zeta s τ ε ≤ 7 * (qval s τ ε * zeta s τ ε) := by
      calc (pval s τ ε : ℝ) * zeta s τ ε ≤ 7 * qval s τ ε * zeta s τ ε :=
            mul_le_mul_of_nonneg_right hp7 hζ.le
        _ = 7 * (qval s τ ε * zeta s τ ε) := by ring
    have hA : (1 + zeta s τ ε) ^ pval s τ ε ≤ Real.exp 1 := by
      calc (1 + zeta s τ ε) ^ pval s τ ε ≤ Real.exp (zeta s τ ε) ^ pval s τ ε :=
            pow_le_pow_left₀ (by linarith) hexp _
        _ = Real.exp ((pval s τ ε : ℝ) * zeta s τ ε) := (Real.exp_nat_mul _ _).symm
        _ ≤ Real.exp 1 := Real.exp_le_exp.mpr (by linarith)
    have hB : zeta s τ ε * pval s τ ε / 2 ≤ hval τ ε * τ / kval τ ε := by
      have e := R.q_mul_zeta
      have h3 : zeta s τ ε * pval s τ ε / 2 ≤ 7 / 2 * (hval τ ε * τ / (100 * kval τ ε)) := by
        rw [← e]
        linarith
      have e2 : 7 / 2 * (hval τ ε * τ / (100 * kval τ ε)) =
          7 / 200 * (hval τ ε * τ / kval τ ε) := by
        field_simp
        ring
      have hx : 0 ≤ hval τ ε * τ / kval τ ε := by positivity
      linarith
    calc zeta s τ ε * pval s τ ε * (1 + zeta s τ ε) ^ pval s τ ε / 2 =
          (zeta s τ ε * pval s τ ε / 2) * (1 + zeta s τ ε) ^ pval s τ ε := by ring
      _ ≤ (hval τ ε * τ / kval τ ε) * Real.exp 1 :=
          mul_le_mul hB hA (by positivity) (by positivity)
      _ = Real.exp 1 * (hval τ ε * τ / kval τ ε) := by ring
  have h2' : 0 ≤ zeta s τ ε * pval s τ ε * (1 + zeta s τ ε) ^ pval s τ ε / 2 := by positivity
  calc Fval s τ ε ≤
        Real.exp (6 * kval τ ε) * (Real.exp 1 * (hval τ ε * τ / kval τ ε)) ^ kval τ ε := by
        unfold Fval
        exact mul_le_mul h1 (pow_le_pow_left₀ h2' h2 _) (by positivity) (by positivity)
    _ = Real.exp (7 * kval τ ε) * (hval τ ε * τ / kval τ ε) ^ kval τ ε := by
        rw [mul_pow, ← Real.exp_nat_mul, ← mul_assoc, ← Real.exp_add]
        congr 2
        ring

/-- The isolated contribution of `CoreFilter.filter_bound` is at most `2 e^{-hk/2}`. -/
theorem iso_term_le :
    2 * (zeta s τ ε * (Fval s τ ε * CoreFilter.isoBound (Q0 s τ ε) (sw s τ ε) (sm s τ ε)
      (wval s τ ε) (aval s τ ε) (zeta s τ ε)
      (‖CayleyBlocks.lamp (qval s τ ε) - CayleyBlocks.lamm (qval s τ ε)‖ - zeta s τ ε))) ≤
      2 * Real.exp (-(hval τ ε * kval τ ε / 2)) := by
  set I := CoreFilter.isoBound (Q0 s τ ε) (sw s τ ε) (sm s τ ε) (wval s τ ε) (aval s τ ε)
    (zeta s τ ε) (‖CayleyBlocks.lamp (qval s τ ε) - CayleyBlocks.lamm (qval s τ ε)‖ -
      zeta s τ ε) with hIdef
  have hiso : zeta s τ ε * I ≤ Real.exp (3609 * kval τ ε) := R.iso_le
  have hF := R.F_le
  have hF0 : 0 ≤ Fval s τ ε := by
    unfold Fval
    have := R.zeta_pos
    positivity
  have hk := R.k_pos
  have hh := R.h_pos
  have hτ := R.τ_pos
  set x := hval τ ε * τ / kval τ ε with hxdef
  have hx0 : 0 ≤ x := by positivity
  have hy : Real.exp 3616 * x ≤ Real.exp (-(hval τ ε / 2)) := by
    have h1 := R.h_tau_div_k
    have h2 := R.exp_h_bound
    calc Real.exp 3616 * x ≤ Real.exp 3616 * (hval τ ε ^ 2 * Real.exp (-hval τ ε) / 2) :=
          mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
      _ = (Real.exp 3616 * hval τ ε ^ 2) * Real.exp (-hval τ ε) / 2 := by ring
      _ ≤ (2 * Real.exp (hval τ ε / 2)) * Real.exp (-hval τ ε) / 2 := by gcongr
      _ = Real.exp (hval τ ε / 2) * Real.exp (-hval τ ε) := by ring
      _ = Real.exp (-(hval τ ε / 2)) := by
          rw [← Real.exp_add]
          congr 1
          ring
  have he : Real.exp (7 * kval τ ε) * x ^ kval τ ε * Real.exp (3609 * kval τ ε) =
      (Real.exp 3616 * x) ^ kval τ ε := by
    rw [mul_pow, ← Real.exp_nat_mul, mul_right_comm, ← Real.exp_add]
    congr 2
    ring
  calc 2 * (zeta s τ ε * (Fval s τ ε * I)) = 2 * (Fval s τ ε * (zeta s τ ε * I)) := by ring
    _ ≤ 2 * (Fval s τ ε * Real.exp (3609 * kval τ ε)) := by
        have := mul_le_mul_of_nonneg_left hiso hF0
        linarith
    _ ≤ 2 * (Real.exp (7 * kval τ ε) * x ^ kval τ ε * Real.exp (3609 * kval τ ε)) := by
        have := mul_le_mul_of_nonneg_right hF (Real.exp_pos (3609 * kval τ ε)).le
        linarith
    _ = 2 * (Real.exp 3616 * x) ^ kval τ ε := by rw [he]
    _ ≤ 2 * Real.exp (-(hval τ ε / 2)) ^ kval τ ε := by
        have := pow_le_pow_left₀ (by positivity) hy (kval τ ε)
        linarith
    _ = 2 * Real.exp (-(hval τ ε * kval τ ε / 2)) := by
        rw [← Real.exp_nat_mul]
        congr 2
        ring

/-- The bulk contribution of `CoreFilter.filter_bound` is at most `e^{-hk/2}`. -/
theorem bulk_term_le :
    (2 / ((B0 s τ ε : ℝ) * rho0 s τ ε)) ^ mval τ ε * rho0 s τ ε *
      (CoreFilter.bulkBound (Q0 s τ ε) (sw s τ ε) (sm s τ ε) (wval s τ ε) (aval s τ ε)
        (rho0 s τ ε) *
      (1 + 2 * (zeta s τ ε * CoreFilter.isoBound (Q0 s τ ε) (sw s τ ε) (sm s τ ε) (wval s τ ε)
        (aval s τ ε) (zeta s τ ε)
        (‖CayleyBlocks.lamp (qval s τ ε) - CayleyBlocks.lamm (qval s τ ε)‖ - zeta s τ ε)))) ≤
      Real.exp (-(hval τ ε * kval τ ε / 2)) := by
  set I := CoreFilter.isoBound (Q0 s τ ε) (sw s τ ε) (sm s τ ε) (wval s τ ε) (aval s τ ε)
    (zeta s τ ε) (‖CayleyBlocks.lamp (qval s τ ε) - CayleyBlocks.lamm (qval s τ ε)‖ -
      zeta s τ ε) with hIdef
  have hiso : zeta s τ ε * I ≤ Real.exp (3609 * kval τ ε) := R.iso_le
  have hρ := R.rho0_pos
  have hw := R.w_nonneg
  have hwa := R.w_le_a
  have ha := R.a_pos
  have hQ := R.Q0_ge
  have hsw := sw_nonneg s τ ε
  have hsm := sm_nonneg s τ ε
  have hsm8 := R.sm_le
  have hswρ := R.sw_div_rho0
  have haρ := R.a_rho0_le
  have hρQ := R.rho0_mul_Q0
  have hL := R.L_large
  have hk := R.k_pos
  have hh := R.h_large
  have hζ := R.zeta_pos
  have hg : 0 < ‖CayleyBlocks.lamp (qval s τ ε) - CayleyBlocks.lamm (qval s τ ε)‖ -
      zeta s τ ε := by
    have := R.sep
    linarith
  have hI0 : 0 ≤ I := pointBound_nonneg hw ha.le (inv_nonneg.mpr hζ.le)
    (inv_nonneg.mpr hg.le) (by linarith)
  rw [R.B0_mul_rho0]
  -- `(1/4)^m ≤ e^{-m}`
  have h14 : (2 / 8 : ℝ) ^ mval τ ε ≤ Real.exp (-(mval τ ε : ℝ)) := by
    have he : (2 / 8 : ℝ) ≤ Real.exp (-1) := by
      rw [Real.exp_neg, le_inv_comm₀ (by norm_num) (Real.exp_pos 1)]
      have := Real.exp_one_lt_d9
      norm_num
      linarith
    calc (2 / 8 : ℝ) ^ mval τ ε ≤ Real.exp (-1) ^ mval τ ε :=
          pow_le_pow_left₀ (by norm_num) he _
      _ = Real.exp (-(mval τ ε : ℝ)) := by
          rw [← Real.exp_nat_mul]
          congr 1
          ring
  -- `ρ₀ · bulkBound ≤ (5 + L) e^{L/2}`
  have hPB := pointBound_le (Q₀ := Q0 s τ ε) (sw := sw s τ ε) (sm := sm s τ ε)
    (ip := 2 / rho0 s τ ε) (im := 2 / rho0 s τ ε) (ζ2 := 2 * rho0 s τ ε) hw hwa
    (by positivity) (by positivity) (by positivity) hsw hsm (by linarith)
  set X := sw s τ ε * (2 / rho0 s τ ε + 2 / rho0 s τ ε) + 2 / 3 * (1 + sm s τ ε) with hXdef
  have hX0 : 0 ≤ X := by positivity
  have hX1 : X ≤ 1 := by
    have e : sw s τ ε * (2 / rho0 s τ ε + 2 / rho0 s τ ε) = 4 * (sw s τ ε / rho0 s τ ε) := by
      ring
    rw [hXdef, e]
    linarith
  have hX2 : X ^ 2 ≤ 1 := pow_le_one₀ hX0 hX1
  have hbulk0 : 0 ≤ CoreFilter.bulkBound (Q0 s τ ε) (sw s τ ε) (sm s τ ε) (wval s τ ε)
      (aval s τ ε) (rho0 s τ ε) :=
    pointBound_nonneg hw ha.le (by positivity) (by positivity) (by linarith)
  have hρB : rho0 s τ ε * CoreFilter.bulkBound (Q0 s τ ε) (sw s τ ε) (sm s τ ε) (wval s τ ε)
      (aval s τ ε) (rho0 s τ ε) ≤ (5 + Lval ε) * Real.exp (Lval ε / 2) := by
    have hfirst : rho0 s τ ε * (2 / rho0 s τ ε + 2 / rho0 s τ ε + 4 / 3 * Q0 s τ ε +
        5 * aval s τ ε * X ^ 2) ≤ 5 + Lval ε := by
      have e : rho0 s τ ε * (2 / rho0 s τ ε + 2 / rho0 s τ ε + 4 / 3 * Q0 s τ ε +
          5 * aval s τ ε * X ^ 2) =
          4 + 4 / 3 * (rho0 s τ ε * Q0 s τ ε) + 5 * (aval s τ ε * rho0 s τ ε) * X ^ 2 := by
        field_simp
        ring
      rw [e]
      have : (aval s τ ε * rho0 s τ ε) * X ^ 2 ≤ Lval ε / 8 := by
        calc (aval s τ ε * rho0 s τ ε) * X ^ 2 ≤ (aval s τ ε * rho0 s τ ε) * 1 :=
              mul_le_mul_of_nonneg_left hX2 (by positivity)
          _ ≤ Lval ε / 8 := by linarith
      nlinarith
    have hsecond : Real.exp (2 * aval s τ ε * (2 * rho0 s τ ε) * X ^ 2) ≤
        Real.exp (Lval ε / 2) := by
      apply Real.exp_le_exp.mpr
      have : (aval s τ ε * rho0 s τ ε) * X ^ 2 ≤ Lval ε / 8 := by
        calc (aval s τ ε * rho0 s τ ε) * X ^ 2 ≤ (aval s τ ε * rho0 s τ ε) * 1 :=
              mul_le_mul_of_nonneg_left hX2 (by positivity)
          _ ≤ Lval ε / 8 := by linarith
      nlinarith
    have hpos : 0 ≤ 2 / rho0 s τ ε + 2 / rho0 s τ ε + 4 / 3 * Q0 s τ ε +
        5 * aval s τ ε * X ^ 2 := by positivity
    calc rho0 s τ ε * CoreFilter.bulkBound (Q0 s τ ε) (sw s τ ε) (sm s τ ε) (wval s τ ε)
          (aval s τ ε) (rho0 s τ ε) ≤
          rho0 s τ ε * ((2 / rho0 s τ ε + 2 / rho0 s τ ε + 4 / 3 * Q0 s τ ε +
            5 * aval s τ ε * X ^ 2) *
            Real.exp (2 * aval s τ ε * (2 * rho0 s τ ε) * X ^ 2)) :=
          mul_le_mul_of_nonneg_left hPB hρ.le
      _ = (rho0 s τ ε * (2 / rho0 s τ ε + 2 / rho0 s τ ε + 4 / 3 * Q0 s τ ε +
            5 * aval s τ ε * X ^ 2)) *
            Real.exp (2 * aval s τ ε * (2 * rho0 s τ ε) * X ^ 2) := by ring
      _ ≤ (5 + Lval ε) * Real.exp (Lval ε / 2) :=
          mul_le_mul hfirst hsecond (Real.exp_pos _).le (by linarith)
  -- `1 + 2ζI ≤ 3 e^{3609k}`
  have hI3 : 1 + 2 * (zeta s τ ε * I) ≤ 3 * Real.exp (3609 * kval τ ε) := by
    have : 1 ≤ Real.exp (3609 * kval τ ε) := Real.one_le_exp (by positivity)
    linarith
  have hm := mval_ge τ ε
  have hLhk := R.L_le_hk
  have h3 : 3 * (5 + Lval ε) ≤ Real.exp (4 * Lval ε) := by
    have := three_add_le_exp (4 * Lval ε) (by linarith)
    linarith
  have hexpo : -(mval τ ε : ℝ) + 4 * Lval ε + (Lval ε / 2 + 3609 * kval τ ε) ≤
      -(hval τ ε * kval τ ε / 2) := by
    have := mul_le_mul_of_nonneg_right hh hk.le
    linarith
  calc (2 / 8 : ℝ) ^ mval τ ε * rho0 s τ ε *
        (CoreFilter.bulkBound (Q0 s τ ε) (sw s τ ε) (sm s τ ε) (wval s τ ε) (aval s τ ε)
          (rho0 s τ ε) * (1 + 2 * (zeta s τ ε * I))) =
        (2 / 8 : ℝ) ^ mval τ ε * (rho0 s τ ε * CoreFilter.bulkBound (Q0 s τ ε) (sw s τ ε)
          (sm s τ ε) (wval s τ ε) (aval s τ ε) (rho0 s τ ε)) * (1 + 2 * (zeta s τ ε * I)) := by
        ring
    _ ≤ Real.exp (-(mval τ ε : ℝ)) * ((5 + Lval ε) * Real.exp (Lval ε / 2)) *
          (3 * Real.exp (3609 * kval τ ε)) := by
        apply mul_le_mul (mul_le_mul h14 hρB (by positivity) (Real.exp_pos _).le) hI3
          (by positivity) (by positivity)
    _ = (3 * (5 + Lval ε)) * Real.exp (-(mval τ ε : ℝ) + (Lval ε / 2 + 3609 * kval τ ε)) := by
        rw [Real.exp_add, Real.exp_add]
        ring
    _ ≤ Real.exp (4 * Lval ε) * Real.exp (-(mval τ ε : ℝ) + (Lval ε / 2 + 3609 * kval τ ε)) :=
        mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
    _ = Real.exp (-(mval τ ε : ℝ) + 4 * Lval ε + (Lval ε / 2 + 3609 * kval τ ε)) := by
        rw [← Real.exp_add]
        congr 1
        ring
    _ ≤ Real.exp (-(hval τ ε * kval τ ε / 2)) := Real.exp_le_exp.mpr hexpo

/-- **The core filter estimate** `‖f(D_g)‖ ≤ ε/3` (`opt:eq:filter-small`), as a bound on the
right-hand side of `CoreFilter.filter_bound`. -/
theorem filter_estimate :
    2 * (zeta s τ ε * (Fval s τ ε * CoreFilter.isoBound (Q0 s τ ε) (sw s τ ε) (sm s τ ε)
      (wval s τ ε) (aval s τ ε) (zeta s τ ε)
      (‖CayleyBlocks.lamp (qval s τ ε) - CayleyBlocks.lamm (qval s τ ε)‖ - zeta s τ ε))) +
    (2 / ((B0 s τ ε : ℝ) * rho0 s τ ε)) ^ mval τ ε * rho0 s τ ε *
      (CoreFilter.bulkBound (Q0 s τ ε) (sw s τ ε) (sm s τ ε) (wval s τ ε) (aval s τ ε)
        (rho0 s τ ε) *
      (1 + 2 * (zeta s τ ε * CoreFilter.isoBound (Q0 s τ ε) (sw s τ ε) (sm s τ ε) (wval s τ ε)
        (aval s τ ε) (zeta s τ ε)
        (‖CayleyBlocks.lamp (qval s τ ε) - CayleyBlocks.lamm (qval s τ ε)‖ - zeta s τ ε)))) ≤
      ε / 3 := by
  have h1 := R.iso_term_le
  have h2 := R.bulk_term_le
  have hε := R.eps_eq
  have hLhk := R.L_le_hk
  have hh := R.h_large
  have hk := R.one_le_k_real
  have h9 : 9 * Real.exp (-(hval τ ε * kval τ ε / 2)) ≤ Real.exp (-Lval ε) := by
    have h6 : (9 : ℝ) ≤ Real.exp 6 := by
      have := three_add_le_exp 6 (by norm_num)
      linarith
    have hhk : (10 : ℝ) ^ 4 * 1 ≤ hval τ ε * kval τ ε :=
      mul_le_mul hh hk (by norm_num) (by linarith)
    calc 9 * Real.exp (-(hval τ ε * kval τ ε / 2)) ≤
          Real.exp 6 * Real.exp (-(hval τ ε * kval τ ε / 2)) :=
          mul_le_mul_of_nonneg_right h6 (Real.exp_pos _).le
      _ = Real.exp (6 - hval τ ε * kval τ ε / 2) := by
          rw [← Real.exp_add, ← sub_eq_add_neg]
      _ ≤ Real.exp (-Lval ε) := Real.exp_le_exp.mpr (by linarith)
  calc _ ≤ 2 * Real.exp (-(hval τ ε * kval τ ε / 2)) +
        Real.exp (-(hval τ ε * kval τ ε / 2)) := add_le_add h1 h2
    _ ≤ Real.exp (-Lval ε) / 3 := by linarith
    _ = ε / 3 := by rw [← hε]

/-! ### Degree and catalyst -/

theorem two_le_p : 2 ≤ pval s τ ε := by
  have h := R.p_large
  have hpi := Real.pi_gt_three
  have : (2 : ℝ) ≤ pval s τ ε := by nlinarith
  exact_mod_cast this

theorem one_le_p : 1 ≤ pval s τ ε := le_trans (by norm_num) R.two_le_p

/-- The filter degree as a real number: `d = m(B₀ - 1) + k(p - 1)`. -/
theorem degree_eq : (degree s τ ε : ℝ) =
    mval τ ε * ((B0 s τ ε : ℝ) - 1) + kval τ ε * ((pval s τ ε : ℝ) - 1) := by
  have hB1 := R.one_le_B0
  have hp1 := R.one_le_p
  unfold degree ProductFilter.degree
  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hB1, Nat.cast_sub hp1, Nat.cast_one]

theorem degree_pos : 0 < degree s τ ε := by
  have h := R.degree_eq
  have hB1 : (1 : ℝ) ≤ B0 s τ ε := by exact_mod_cast R.one_le_B0
  have hp := R.five_q_le_p_sub_one
  have hq := R.q_pos
  have hk := R.k_pos
  have hm : (0 : ℝ) ≤ mval τ ε := Nat.cast_nonneg _
  have : (0 : ℝ) < degree s τ ε := by
    rw [h]
    have h1 : 0 ≤ (mval τ ε : ℝ) * ((B0 s τ ε : ℝ) - 1) := mul_nonneg hm (by linarith)
    have h2 : 0 < (kval τ ε : ℝ) * ((pval s τ ε : ℝ) - 1) := mul_pos hk (by linarith)
    linarith
  exact_mod_cast this

theorem nu_pos : 0 < nu s τ ε := by
  unfold nu
  have : (0 : ℝ) < s := by linarith [R.one_le_s]
  have := R.h_pos
  positivity

/-- `ν ≤ 3`. -/
theorem nu_le : nu s τ ε ≤ 3 := by
  have hs : (0 : ℝ) < s := by linarith [R.one_le_s]
  have h1 := R.q_sq_div_s
  have h2 := R.four_h_tau_div_L
  have hh := R.h_large
  have hh0 := R.h_pos
  have h3 : qval s τ ε ^ 2 / s ≤ 2 / hval τ ε := h1.trans h2
  have h4 : 2 * (1 + hval τ ε) * (2 / hval τ ε) ≤ 5 := by
    have e : 2 * (1 + hval τ ε) * (2 / hval τ ε) = 4 + 4 / hval τ ε := by
      field_simp
      ring
    have : 4 / hval τ ε ≤ 1 := by
      rw [div_le_one hh0]
      linarith
    linarith
  have h5 : 2 * (1 + hval τ ε) * (qval s τ ε ^ 2 / s) ≤ 2 * (1 + hval τ ε) * (2 / hval τ ε) :=
    mul_le_mul_of_nonneg_left h3 (by positivity)
  have e : 2 * qval s τ ε ^ 2 * (1 + hval τ ε) / s =
      2 * (1 + hval τ ε) * (qval s τ ε ^ 2 / s) := by ring
  unfold nu
  rw [e]
  linarith

/-- The catalyst budget: `6 a ν ≤ d` (`opt:eq:degree-catalyst`). -/
theorem catalyst_le : 6 * (aval s τ ε * nu s τ ε) ≤ degree s τ ε := by
  have hnu := R.nu_le
  have hnu0 := R.nu_pos
  have ha := R.a_le_qr
  have ha0 := R.a_pos
  have hk := kval_ge τ ε
  have hq := R.q_pos
  have hr := R.r_pos
  have hp := R.five_q_le_p_sub_one
  have hk0 := R.k_pos
  have hB1 : (1 : ℝ) ≤ B0 s τ ε := by exact_mod_cast R.one_le_B0
  have hm : (0 : ℝ) ≤ mval τ ε := Nat.cast_nonneg _
  have h1 : 6 * (aval s τ ε * nu s τ ε) ≤ 18 * aval s τ ε := by nlinarith
  have h3 : qval s τ ε * rval τ ε ≤ qval s τ ε * kval τ ε / 4 := by nlinarith
  have h4 : 5 * qval s τ ε * kval τ ε ≤ kval τ ε * ((pval s τ ε : ℝ) - 1) := by nlinarith
  have h5 : 0 ≤ (mval τ ε : ℝ) * ((B0 s τ ε : ℝ) - 1) := mul_nonneg hm (by linarith)
  rw [R.degree_eq]
  nlinarith

/-- `d ≤ 2152 q k`. -/
theorem degree_le : (degree s τ ε : ℝ) ≤ 2152 * (qval s τ ε * kval τ ε) := by
  have hB := R.B0_le
  have hm := R.m_le
  have hp := R.p_le_seven_q
  have hq := R.q_pos
  have hh := R.h_pos
  have hk := R.k_pos
  have hm0 : (0 : ℝ) ≤ mval τ ε := Nat.cast_nonneg _
  have h1 : (mval τ ε : ℝ) * ((B0 s τ ε : ℝ) - 1) ≤ 2145 * (qval s τ ε * kval τ ε) := by
    calc (mval τ ε : ℝ) * ((B0 s τ ε : ℝ) - 1) ≤ (mval τ ε : ℝ) * B0 s τ ε := by nlinarith
      _ ≤ (33 * hval τ ε * kval τ ε) * (65 * qval s τ ε / hval τ ε) :=
          mul_le_mul hm hB (Nat.cast_nonneg _) (by positivity)
      _ = 2145 * (qval s τ ε * kval τ ε) := by
          field_simp
          ring
  have h2 : (kval τ ε : ℝ) * ((pval s τ ε : ℝ) - 1) ≤ 7 * (qval s τ ε * kval τ ε) := by nlinarith
  rw [R.degree_eq]
  linarith

/-- `k ≤ 5r`. -/
theorem k_le_five_r : (kval τ ε : ℝ) ≤ 5 * rval τ ε := by
  have h1 := R.k_le
  have h2 := R.h_tau_le_r
  have hh := R.h_large
  have hτ := R.one_le_τ
  have : (1 : ℝ) ≤ hval τ ε * τ := by nlinarith
  linarith

/-- `q_* r = √(sτr)`. -/
theorem qstar_mul_r : qstar s τ ε * rval τ ε = Real.sqrt (s * τ * rval τ ε) := by
  have hq := R.qstar_pos
  have hr := R.r_pos
  rw [← Real.sqrt_sq (mul_nonneg hq.le hr.le)]
  congr 1
  rw [mul_pow, R.qstar_sq]
  field_simp

/-- `q k ≤ 10 √(sτr)`. -/
theorem qk_le : qval s τ ε * kval τ ε ≤ 10 * Real.sqrt (s * τ * rval τ ε) := by
  have h1 := R.q_le_two_qstar
  have h2 := R.k_le_five_r
  have hq := R.q_pos
  have hk := R.k_pos
  have hqs := R.qstar_pos
  have hr := R.r_pos
  calc qval s τ ε * kval τ ε ≤ (2 * qstar s τ ε) * (5 * rval τ ε) :=
        mul_le_mul h1 h2 hk.le (by positivity)
    _ = 10 * (qstar s τ ε * rval τ ε) := by ring
    _ = 10 * Real.sqrt (s * τ * rval τ ε) := by rw [R.qstar_mul_r]

/-- **The core degree** `d = O(√(sτr))` (`opt:eq:core-degree`): `d ≤ 21520 √(sτr)`. -/
theorem degree_le_sqrt : (degree s τ ε : ℝ) ≤ 21520 * Real.sqrt (s * τ * rval τ ε) := by
  have h1 := R.degree_le
  have h2 := R.qk_le
  linarith

end Regime

end

end LargeSparsityCore.Parameters
