import OptimalPrecision.Taylor.Basic
import OptimalPrecision.Weights.Cesaro
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# The scalar transfer `e^{-t ξ(w)}` and its Laguerre coefficients

With `ξ(w) = (1 - w)/(1 + w)` (`opt:eq:xi-R`), the Taylor coefficients of
`w ↦ e^{-t ξ(w)} / (1 + w)` at the origin are `(-1)^l ℓ_l(t)`, where
`ℓ_l(t) = e^{-t} L_l(2t)` (`opt:eq:laguerre-gf` with `z = -w`). The proof
extracts coefficients from the first-order equation

  `(1 + w)^2 f'(w) = (2t - 1 - w) f(w)`

and compares with the three-term Laguerre recurrence. Consequently
`[w^l] e^{-t ξ(w)} = e^{-t} E_l(t)` with `E_l = (-1)^l (lag_l - lag_{l-1})`.
-/

namespace OptimalPrecision

noncomputable section

open Nat Finset Filter Complex Polynomial
open scoped Topology Polynomial
open ExpPoly

/-- `ξ(w) = (1 - w)/(1 + w)`. -/
def xi (w : ℂ) : ℂ := (1 - w) / (1 + w)

/-- The scalar transfer `w ↦ e^{-t ξ(w)}`. -/
def vt (t : ℂ) (w : ℂ) : ℂ := Complex.exp (-(t * xi w))

/-- The Laguerre generating function `w ↦ e^{-t ξ(w)} / (1 + w)`. -/
def lagGen (t : ℂ) (w : ℂ) : ℂ := vt t w / (1 + w)

theorem one_add_ne_zero_of_norm_lt {w : ℂ} (hw : ‖w‖ < 1) : 1 + w ≠ 0 := by
  intro h
  have : w = -1 := by linear_combination h
  rw [this, norm_neg, norm_one] at hw
  exact lt_irrefl _ hw

theorem analyticAt_xi_of_norm_lt {w : ℂ} (hw : ‖w‖ < 1) : AnalyticAt ℂ xi w := by
  unfold xi
  exact (analyticAt_const.sub analyticAt_id).div (analyticAt_const.add analyticAt_id)
    (one_add_ne_zero_of_norm_lt hw)

theorem analyticAt_vt_of_norm_lt (t : ℂ) {w : ℂ} (hw : ‖w‖ < 1) : AnalyticAt ℂ (vt t) w := by
  unfold vt
  exact (analyticAt_const.mul (analyticAt_xi_of_norm_lt hw)).neg.cexp'

theorem analyticAt_lagGen_of_norm_lt (t : ℂ) {w : ℂ} (hw : ‖w‖ < 1) :
    AnalyticAt ℂ (lagGen t) w := by
  unfold lagGen
  exact (analyticAt_vt_of_norm_lt t hw).div (analyticAt_const.add analyticAt_id)
    (one_add_ne_zero_of_norm_lt hw)

theorem analyticAt_xi : AnalyticAt ℂ xi 0 := analyticAt_xi_of_norm_lt (by simp)
theorem analyticAt_vt (t : ℂ) : AnalyticAt ℂ (vt t) 0 := analyticAt_vt_of_norm_lt t (by simp)
theorem analyticAt_lagGen (t : ℂ) : AnalyticAt ℂ (lagGen t) 0 :=
  analyticAt_lagGen_of_norm_lt t (by simp)

theorem differentiableOn_vt (t : ℂ) : DifferentiableOn ℂ (vt t) (Metric.ball 0 1) :=
  fun w hw =>
    (analyticAt_vt_of_norm_lt t (by simpa using hw)).differentiableAt.differentiableWithinAt

/-- The derivative of the generating function. -/
theorem hasDerivAt_lagGen (t : ℂ) {w : ℂ} (hw : ‖w‖ < 1) :
    HasDerivAt (lagGen t) (lagGen t w * (2 * t / (1 + w) ^ 2 - 1 / (1 + w))) w := by
  have h1 : (1 + w) ≠ 0 := one_add_ne_zero_of_norm_lt hw
  have hd : HasDerivAt (fun w : ℂ => 1 + w) 1 w := by
    simpa using (hasDerivAt_id w).const_add 1
  have hxi : HasDerivAt xi (-2 / (1 + w) ^ 2) w := by
    have hn : HasDerivAt (fun w : ℂ => 1 - w) (-1) w := by
      simpa using (hasDerivAt_id w).const_sub 1
    exact (hn.div hd h1).congr_deriv (by ring)
  have hv : HasDerivAt (vt t) (vt t w * (2 * t / (1 + w) ^ 2)) w :=
    ((hxi.const_mul t).neg).cexp.congr_deriv (by simp only [vt, Pi.neg_apply]; ring)
  exact (hv.div hd h1).congr_deriv (by simp only [lagGen]; field_simp)

/-- The first-order equation `(1 + w)^2 f' = (2t - 1 - w) f` near the origin. -/
theorem lagGen_ode (t : ℂ) :
    (fun w => (1 + w) ^ 2 * deriv (lagGen t) w) =ᶠ[𝓝 0]
      (fun w => (2 * t - 1 - w) * lagGen t w) := by
  have hball : Metric.ball (0 : ℂ) 1 ∈ 𝓝 (0 : ℂ) := Metric.ball_mem_nhds 0 one_pos
  filter_upwards [hball] with w hw
  have hw' : ‖w‖ < 1 := by simpa using hw
  have h1 : (1 + w) ≠ 0 := one_add_ne_zero_of_norm_lt hw'
  rw [(hasDerivAt_lagGen t hw').deriv]
  field_simp
  ring

/-- The coefficients `c_l = [w^l] e^{-t ξ(w)}/(1 + w)`. -/
def lagGenCoeff (t : ℂ) (l : ℕ) : ℂ := coeff (lagGen t) l

theorem analyticAt_deriv_lagGen (t : ℂ) : AnalyticAt ℂ (deriv (lagGen t)) 0 :=
  (analyticAt_lagGen t).deriv

/-- Coefficient form of the first-order equation. -/
theorem lagGenCoeff_rec (t : ℂ) (l : ℕ) :
    ((l + 3 : ℕ) : ℂ) * lagGenCoeff t (l + 3) =
      (2 * t - 1 - 2 * ((l + 2 : ℕ) : ℂ)) * lagGenCoeff t (l + 2) -
        ((l + 2 : ℕ) : ℂ) * lagGenCoeff t (l + 1) := by
  have hode := coeff_congr (lagGen_ode t) (l + 2)
  set g := deriv (lagGen t)
  have hg := analyticAt_deriv_lagGen t
  have hf := analyticAt_lagGen t
  -- left side: `(1 + w)^2 g = g + 2 (w g) + w (w g)`
  have hL : (fun w => (1 + w) ^ 2 * g w) =
      (fun w => g w + ((2 : ℂ) • (w * g w) + w * (w * g w))) := by
    funext w; simp only [smul_eq_mul]; ring
  have hR : (fun w => (2 * t - 1 - w) * lagGen t w) =
      (fun w => (2 * t - 1) • lagGen t w - w * lagGen t w) := by
    funext w; simp only [smul_eq_mul]; ring
  have hwg : AnalyticAt ℂ (fun w => w * g w) 0 := analyticAt_id.fun_mul hg
  have hwwg : AnalyticAt ℂ (fun w => w * (w * g w)) 0 := analyticAt_id.fun_mul hwg
  have hwf : AnalyticAt ℂ (fun w => w * lagGen t w) 0 := analyticAt_id.fun_mul hf
  have h2wg : AnalyticAt ℂ (fun w => (2 : ℂ) • (w * g w)) 0 := hwg.fun_const_smul
  have hcf : AnalyticAt ℂ (fun w => (2 * t - 1) • lagGen t w) 0 := hf.fun_const_smul
  rw [hL, hR] at hode
  rw [coeff_add hg (h2wg.fun_add hwwg), coeff_add h2wg hwwg,
    coeff_const_smul_field, coeff_X_mul hg, coeff_X_mul hwg, coeff_X_mul hg,
    coeff_sub hcf hwf, coeff_const_smul_field, coeff_X_mul hf] at hode
  simp only [coeff_deriv, smul_eq_mul] at hode
  simp only [lagGenCoeff]
  push_cast at hode ⊢
  linear_combination hode

theorem lagGenCoeff_zero (t : ℂ) : lagGenCoeff t 0 = Complex.exp (-t) := by
  simp [lagGenCoeff, coeff_zero_eq, lagGen, vt, xi]

theorem lagGenCoeff_one (t : ℂ) : lagGenCoeff t 1 = (2 * t - 1) * Complex.exp (-t) := by
  have hode := coeff_congr (lagGen_ode t) 0
  set g := deriv (lagGen t)
  have hg := analyticAt_deriv_lagGen t
  have hf := analyticAt_lagGen t
  simp only [coeff_zero_eq] at hode
  have h0 : g 0 = 1 * coeff g 0 := by rw [coeff_zero_eq, one_mul]
  rw [coeff_deriv] at h0
  simp only [zero_add, Nat.cast_one, one_smul, one_mul] at h0
  simp only [add_zero, one_pow, one_mul, sub_zero] at hode
  rw [h0, ← lagGenCoeff, show lagGen t 0 = lagGenCoeff t 0 by
    rw [lagGenCoeff, coeff_zero_eq], lagGenCoeff_zero] at hode
  exact hode

theorem lagGenCoeff_two (t : ℂ) :
    2 * lagGenCoeff t 2 = (2 * t - 3) * lagGenCoeff t 1 - lagGenCoeff t 0 := by
  have hode := coeff_congr (lagGen_ode t) 1
  set g := deriv (lagGen t)
  have hg := analyticAt_deriv_lagGen t
  have hf := analyticAt_lagGen t
  have hL : (fun w => (1 + w) ^ 2 * g w) =
      (fun w => g w + ((2 : ℂ) • (w * g w) + w * (w * g w))) := by
    funext w; simp only [smul_eq_mul]; ring
  have hR : (fun w => (2 * t - 1 - w) * lagGen t w) =
      (fun w => (2 * t - 1) • lagGen t w - w * lagGen t w) := by
    funext w; simp only [smul_eq_mul]; ring
  have hwg : AnalyticAt ℂ (fun w => w * g w) 0 := analyticAt_id.fun_mul hg
  have hwwg : AnalyticAt ℂ (fun w => w * (w * g w)) 0 := analyticAt_id.fun_mul hwg
  have hwf : AnalyticAt ℂ (fun w => w * lagGen t w) 0 := analyticAt_id.fun_mul hf
  have h2wg : AnalyticAt ℂ (fun w => (2 : ℂ) • (w * g w)) 0 := hwg.fun_const_smul
  have hcf : AnalyticAt ℂ (fun w => (2 * t - 1) • lagGen t w) 0 := hf.fun_const_smul
  rw [hL, hR] at hode
  rw [coeff_add hg (h2wg.fun_add hwwg), coeff_add h2wg hwwg,
    coeff_const_smul_field, coeff_X_mul hg, coeff_sub hcf hwf,
    coeff_const_smul_field, coeff_X_mul hf] at hode
  have hww : coeff (fun w => w * (w * g w)) 1 = 0 := by
    rw [show (1 : ℕ) = 0 + 1 from rfl, coeff_X_mul hwg, coeff_X_mul_zero]
  rw [hww] at hode
  simp only [coeff_deriv, smul_eq_mul] at hode
  simp only [lagGenCoeff]
  push_cast at hode ⊢
  linear_combination hode

/-- **Laguerre coefficients** (`opt:eq:laguerre-gf`): `[w^l] e^{-tξ}/(1+w) = (-1)^l ℓ_l(t)`. -/
theorem lagGenCoeff_eq (t : ℂ) (l : ℕ) :
    lagGenCoeff t l = (-1) ^ l * ev t (lag l) := by
  induction l using Nat.strong_induction_on with
  | _ l ih =>
    match l, ih with
    | 0, _ => simp [lagGenCoeff_zero, ev, lag_zero]
    | 1, _ =>
      rw [lagGenCoeff_one]
      simp [ev, lag, lagCoeff, Finset.sum_range_succ]
      ring
    | 2, ih =>
      have h2 := lagGenCoeff_two t
      rw [ih 1 (by norm_num), ih 0 (by norm_num)] at h2
      have hr := lag_recurrence (K := ℂ) 0
      have hr' := congrArg (Polynomial.eval t) hr
      simp only [eval_smul, eval_sub, eval_mul, eval_X, smul_eq_mul] at hr'
      simp only [ev] at h2 ⊢
      push_cast at hr' h2 ⊢
      rw [lag_zero, eval_one] at hr' h2
      linear_combination (1 / 2 : ℂ) * h2 - (Complex.exp (-t) / 2) * hr'
    | k + 3, ih =>
      have hrec := lagGenCoeff_rec t k
      rw [ih (k + 2) (by omega), ih (k + 1) (by omega)] at hrec
      have hr := lag_recurrence (K := ℂ) (k + 1)
      have hr' := congrArg (Polynomial.eval t) hr
      simp only [eval_smul, eval_sub, eval_mul, eval_X, smul_eq_mul] at hr'
      have hk3 : ((k + 3 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (show k + 3 ≠ 0 by omega)
      simp only [ev] at hrec ⊢
      apply mul_left_cancel₀ hk3
      push_cast at hr' hrec ⊢
      rw [show (k + 1 + 2 : ℕ) = k + 3 by ring] at hr'
      linear_combination hrec - (-1) ^ (k + 3) * Complex.exp (-t) * hr'

/-- **Coefficients of the transfer** `e^{-t ξ(w)}`. -/
theorem coeff_vt (t : ℂ) (l : ℕ) : coeff (vt t) l = ev t (lagE l : ℂ[X]) := by
  have hv : vt t =ᶠ[𝓝 0] fun w => lagGen t w + w * lagGen t w := by
    have hball : Metric.ball (0 : ℂ) 1 ∈ 𝓝 (0 : ℂ) := Metric.ball_mem_nhds 0 one_pos
    filter_upwards [hball] with w hw
    have h1 := one_add_ne_zero_of_norm_lt (by simpa using hw)
    simp only [lagGen]
    field_simp
  have hwf : AnalyticAt ℂ (fun w => w * lagGen t w) 0 := analyticAt_id.fun_mul (analyticAt_lagGen t)
  rw [coeff_congr hv, coeff_add (analyticAt_lagGen t) hwf]
  rcases l with _ | l
  · rw [coeff_X_mul_zero, add_zero, ← lagGenCoeff, lagGenCoeff_eq]
    simp [lagE, ev, lag_zero]
  · rw [coeff_X_mul (analyticAt_lagGen t), ← lagGenCoeff, ← lagGenCoeff, lagGenCoeff_eq,
      lagGenCoeff_eq]
    simp only [lagE, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
    rw [ev_smul, ev, ev, ev]
    simp only [eval_sub]
    ring

end

end OptimalPrecision
