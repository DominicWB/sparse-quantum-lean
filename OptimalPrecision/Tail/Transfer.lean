import OptimalPrecision.Tail.ExpTail
import OptimalPrecision.Weights.Exact
import SparseHamiltonian.ODEDissipative
import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# The three-phase transfer and its contractivity

For operators `C, D` and `q > 0`, the generator of the transfer is

  `Ω(w) = ξ(w) I + R(w)(i q C + q² ξ(w) D)`   (`opt:eq:omega`),

and the analytic transfer is `F(w) = e^{-aΩ(w)}` (`opt:eq:continuum`). With
`μ_± = (q ∓ iξ)/(qξ ∓ i)` (the phases `(1 + ζ_± w)/(1 - ζ_± w)` of
`opt:eq:omega`), the generator is the positive combination

  `Ω = ξ (I - D) + (μ_+ / 2)(D + C) + (μ_- / 2)(D - C)`,

and `Re ξ, Re μ_± ≥ 0` on the unit disk. Hence `Ω` is accretive whenever
`I - D`, `D + C`, `D - C` are positive, and `‖F(w)‖ ≤ 1` for `|w| < 1`.
-/

namespace OptimalPrecision.Tail

noncomputable section

open Complex Metric ContinuousLinearMap
open scoped Topology InnerProductSpace

/-! ### Scalars on the unit disk -/

theorem re_xi_pos {w : ℂ} (hw : ‖w‖ < 1) : 0 < (xi w).re := by
  have hd : (1 + w) ≠ 0 := one_add_ne_zero_of_norm_lt hw
  have hn : 0 < normSq (1 + w) := normSq_pos.mpr hd
  have hw2 : w.re ^ 2 + w.im ^ 2 < 1 := by
    have h := Complex.sq_norm w
    rw [Complex.normSq_apply] at h
    nlinarith [norm_nonneg w]
  rw [xi, Complex.div_re, ← add_div]
  apply div_pos _ hn
  simp only [sub_re, one_re, add_re, sub_im, one_im, add_im]
  nlinarith

variable {q : ℝ}

/-- `μ_+ = (q - iξ)/(qξ - i)`. -/
def muP (q : ℝ) (w : ℂ) : ℂ := ((q : ℂ) - I * xi w) / ((q : ℂ) * xi w - I)

/-- `μ_- = (q + iξ)/(qξ + i)`. -/
def muM (q : ℝ) (w : ℂ) : ℂ := ((q : ℂ) + I * xi w) / ((q : ℂ) * xi w + I)

theorem qxi_sub_I_ne_zero (hq : 0 < q) {w : ℂ} (hw : ‖w‖ < 1) : (q : ℂ) * xi w - I ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp only [sub_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, I_re, zero_re] at this
  have := mul_pos hq (re_xi_pos hw)
  linarith

theorem qxi_add_I_ne_zero (hq : 0 < q) {w : ℂ} (hw : ‖w‖ < 1) : (q : ℂ) * xi w + I ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp only [add_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, I_re, add_zero,
    zero_re] at this
  have := mul_pos hq (re_xi_pos hw)
  linarith

theorem one_add_sq_xi_ne_zero (hq : 0 < q) {w : ℂ} (hw : ‖w‖ < 1) :
    1 + (q : ℂ) ^ 2 * xi w ^ 2 ≠ 0 := by
  have h : 1 + (q : ℂ) ^ 2 * xi w ^ 2 = ((q : ℂ) * xi w - I) * ((q : ℂ) * xi w + I) := by
    ring_nf; rw [I_sq]; ring
  rw [h]
  exact mul_ne_zero (qxi_sub_I_ne_zero hq hw) (qxi_add_I_ne_zero hq hw)

theorem re_muP_nonneg {w : ℂ} (hw : ‖w‖ < 1) : 0 ≤ (muP q w).re := by
  have hx := (re_xi_pos hw).le
  rw [muP, Complex.div_re, ← add_div]
  apply div_nonneg _ (normSq_nonneg _)
  simp only [sub_re, mul_re, ofReal_re, ofReal_im, I_re, I_im, sub_im, mul_im, zero_mul,
    one_mul, zero_sub, sub_zero, zero_add]
  nlinarith [sq_nonneg q]

theorem re_muM_nonneg {w : ℂ} (hw : ‖w‖ < 1) : 0 ≤ (muM q w).re := by
  have hx := (re_xi_pos hw).le
  rw [muM, Complex.div_re, ← add_div]
  apply div_nonneg _ (normSq_nonneg _)
  simp only [add_re, mul_re, ofReal_re, ofReal_im, I_re, I_im, add_im, mul_im, zero_mul,
    one_mul, zero_sub, sub_zero, zero_add]
  nlinarith [sq_nonneg q]

theorem qxi_mul_qxi (w : ℂ) :
    ((q : ℂ) * xi w - I) * ((q : ℂ) * xi w + I) = 1 + (q : ℂ) ^ 2 * xi w ^ 2 := by
  ring_nf; rw [I_sq]; ring

theorem muP_sub_muM (hq : 0 < q) {w : ℂ} (hw : ‖w‖ < 1) :
    I * q * Rfun q w = (muP q w - muM q w) / 2 := by
  have h1 := qxi_sub_I_ne_zero hq hw
  have h2 := qxi_add_I_ne_zero hq hw
  rw [muP, muM, div_sub_div _ _ h1 h2, qxi_mul_qxi, Rfun]
  ring

theorem muP_add_muM (hq : 0 < q) {w : ℂ} (hw : ‖w‖ < 1) :
    (q : ℂ) ^ 2 * xi w * Rfun q w = -xi w + (muP q w + muM q w) / 2 := by
  have h1 := qxi_sub_I_ne_zero hq hw
  have h2 := qxi_add_I_ne_zero hq hw
  have h3 := one_add_sq_xi_ne_zero hq hw
  have hN : ((q : ℂ) - I * xi w) * ((q : ℂ) * xi w + I) +
      ((q : ℂ) * xi w - I) * ((q : ℂ) + I * xi w) = 2 * ((q : ℂ) ^ 2 + 1) * xi w := by
    ring_nf; rw [I_sq]; ring
  rw [muP, muM, div_add_div _ _ h1 h2, qxi_mul_qxi, hN, Rfun]
  field_simp
  ring

/-! ### The operator transfer -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The noncommuting part `X(w) = i q C + q² ξ(w) D`. -/
def Xop (q : ℝ) (C D : H →L[ℂ] H) (w : ℂ) : H →L[ℂ] H :=
  (I * q) • C + ((q : ℂ) ^ 2 * xi w) • D

/-- The generator `Ω(w) = ξ(w) I + R(w) X(w)` (`opt:eq:omega`). -/
def Omega (q : ℝ) (C D : H →L[ℂ] H) (w : ℂ) : H →L[ℂ] H :=
  xi w • (1 : H →L[ℂ] H) + Rfun q w • Xop q C D w

/-- The analytic transfer `F(w) = e^{-aΩ(w)}` (`opt:eq:continuum`). -/
def Fop (a q : ℝ) (C D : H →L[ℂ] H) (w : ℂ) : H →L[ℂ] H :=
  NormedSpace.exp ((-(a : ℂ)) • Omega q C D w)

omit [CompleteSpace H] in
/-- The generator as a positive combination of `I - D`, `D + C`, `D - C`. -/
theorem Omega_eq (hq : 0 < q) {w : ℂ} (hw : ‖w‖ < 1) (C D : H →L[ℂ] H) :
    Omega q C D w = xi w • (1 - D) + (muP q w / 2) • (D + C) + (muM q w / 2) • (D - C) := by
  have h1 := muP_sub_muM hq hw
  have h2 := muP_add_muM hq hw
  have e1 : Rfun q w * (I * q) = (muP q w - muM q w) / 2 := by rw [← h1]; ring
  have e2 : Rfun q w * ((q : ℂ) ^ 2 * xi w) = -xi w + (muP q w + muM q w) / 2 := by
    rw [← h2]; ring
  simp only [Omega, Xop, smul_add, smul_smul, e1, e2]
  module

omit [CompleteSpace H] in
/-- **Accretivity** of the generator on the disk. -/
theorem re_inner_Omega_nonneg (hq : 0 < q) {C D : H →L[ℂ] H} (h1 : (1 - D).IsPositive)
    (h2 : (D + C).IsPositive) (h3 : (D - C).IsPositive) {w : ℂ} (hw : ‖w‖ < 1) (v : H) :
    0 ≤ (⟪v, Omega q C D w v⟫_ℂ).re := by
  have hexp : ⟪v, (xi w • (1 - D) + (muP q w / 2) • (D + C) + (muM q w / 2) • (D - C)) v⟫_ℂ =
      xi w * ⟪v, (1 - D) v⟫_ℂ + (muP q w / 2) * ⟪v, (D + C) v⟫_ℂ +
        (muM q w / 2) * ⟪v, (D - C) v⟫_ℂ := by
    simp only [add_apply, smul_apply, inner_add_right, inner_smul_right]
  rw [Omega_eq hq hw, hexp, add_re, add_re]
  have key : ∀ (c : ℂ) (P : H →L[ℂ] H), P.IsPositive → 0 ≤ c.re → 0 ≤ (c * ⟪v, P v⟫_ℂ).re := by
    intro c P hP hc
    have hz := hP.inner_nonneg_right v
    rw [Complex.le_def] at hz
    rw [mul_re, ← hz.2]
    simp only [zero_im, mul_zero, sub_zero]
    exact mul_nonneg hc hz.1
  have hx := (re_xi_pos hw).le
  have hp : 0 ≤ (muP q w / 2).re := by
    rw [div_ofNat_re]; exact div_nonneg (re_muP_nonneg hw) (by norm_num)
  have hm : 0 ≤ (muM q w / 2).re := by
    rw [div_ofNat_re]; exact div_nonneg (re_muM_nonneg hw) (by norm_num)
  have k1 := key _ _ h1 hx
  have k2 := key _ _ h2 hp
  have k3 := key _ _ h3 hm
  linarith

/-- **Contractivity** of the transfer on the open unit disk. -/
theorem norm_Fop_le_one {a : ℝ} (ha : 0 ≤ a) (hq : 0 < q) {C D : H →L[ℂ] H}
    (h1 : (1 - D).IsPositive) (h2 : (D + C).IsPositive) (h3 : (D - C).IsPositive) {w : ℂ}
    (hw : ‖w‖ < 1) : ‖Fop a q C D w‖ ≤ 1 := by
  have hdiss : SparseHamiltonian.ODEDissipative.Dissipative (-Omega q C D w) := by
    intro v
    rw [neg_apply, inner_neg_right, neg_re]
    linarith [re_inner_Omega_nonneg hq h1 h2 h3 hw v]
  have h := SparseHamiltonian.ODEDissipative.exp_norm_le_one _ hdiss a ha
  have e : (-(a : ℂ)) • Omega q C D w = a • (-Omega q C D w) := by
    rw [neg_smul, smul_neg, ← Complex.coe_smul]
  rw [Fop, e]
  exact h

/-! ### Analyticity and the factorization `F = V e^{-aRX}` -/

theorem analyticAt_Rfun_of_norm_lt (hq : 0 < q) {w : ℂ} (hw : ‖w‖ < 1) :
    AnalyticAt ℂ (Rfun q) w := by
  have hξ := analyticAt_xi_of_norm_lt hw
  exact (analyticAt_const.sub (hξ.pow 2)).div
    (analyticAt_const.add (analyticAt_const.mul (hξ.pow 2))) (one_add_sq_xi_ne_zero hq hw)

omit [CompleteSpace H] in
theorem analyticAt_Xop {C D : H →L[ℂ] H} {w : ℂ} (hw : ‖w‖ < 1) :
    AnalyticAt ℂ (Xop q C D) w := by
  have hξ := analyticAt_xi_of_norm_lt hw
  unfold Xop
  exact analyticAt_const.fun_add ((analyticAt_const.fun_mul hξ).fun_smul analyticAt_const)

omit [CompleteSpace H] in
theorem analyticAt_Omega (hq : 0 < q) {C D : H →L[ℂ] H} {w : ℂ} (hw : ‖w‖ < 1) :
    AnalyticAt ℂ (Omega q C D) w := by
  unfold Omega
  exact ((analyticAt_xi_of_norm_lt hw).fun_smul analyticAt_const).fun_add
    ((analyticAt_Rfun_of_norm_lt hq hw).fun_smul (analyticAt_Xop hw))

theorem analyticAt_Fop {a : ℝ} (hq : 0 < q) {C D : H →L[ℂ] H} {w : ℂ} (hw : ‖w‖ < 1) :
    AnalyticAt ℂ (Fop a q C D) w := by
  unfold Fop
  exact (NormedSpace.exp_analytic (𝕂 := ℂ) _).comp
    (analyticAt_const.fun_smul (analyticAt_Omega hq hw))

theorem differentiableOn_Fop {a : ℝ} (hq : 0 < q) (C D : H →L[ℂ] H) :
    DifferentiableOn ℂ (Fop a q C D) (ball 0 1) :=
  fun w hw => (analyticAt_Fop hq (by simpa using hw)).differentiableAt.differentiableWithinAt

theorem Rfun_zero (q : ℝ) : Rfun q 0 = 0 := by simp [Rfun, xi_zero]

/-- `F = V e^{Y}` with `V = e^{-aξ}` and `Y = -aR X`. -/
theorem Fop_eq (a q : ℝ) (C D : H →L[ℂ] H) (w : ℂ) :
    Fop a q C D w = vt (a : ℂ) w • NormedSpace.exp ((-(a : ℂ) * Rfun q w) • Xop q C D w) := by
  have hsplit : (-(a : ℂ)) • Omega q C D w =
      (-(a : ℂ) * xi w) • (1 : H →L[ℂ] H) + (-(a : ℂ) * Rfun q w) • Xop q C D w := by
    simp only [Omega, smul_add, smul_smul]
  letI : NormedAlgebra ℚ (H →L[ℂ] H) := .restrictScalars ℚ ℂ _
  have hcomm : Commute ((-(a : ℂ) * xi w) • (1 : H →L[ℂ] H))
      ((-(a : ℂ) * Rfun q w) • Xop q C D w) :=
    (Commute.one_left _).smul_left _
  rw [Fop, hsplit, NormedSpace.exp_add_of_commute hcomm]
  have hexp1 : NormedSpace.exp ((-(a : ℂ) * xi w) • (1 : H →L[ℂ] H)) = vt (a : ℂ) w • 1 := by
    rw [← Algebra.algebraMap_eq_smul_one, ← NormedSpace.algebraMap_exp_comm,
      Algebra.algebraMap_eq_smul_one, vt, ← Complex.exp_eq_exp_ℂ]
    ring_nf
  rw [hexp1, smul_mul_assoc, one_mul]

end

end OptimalPrecision.Tail
