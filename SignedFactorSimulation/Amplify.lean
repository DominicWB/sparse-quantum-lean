import SparseHamiltonian.AmplificationQuery
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Oblivious amplification by repeated tripling

Theorem `opt:thm:signed` amplifies an attenuated signed average with `k_o = 2j + 1` rounds of
oblivious amplitude amplification (`sin(k_o arcsin y)`). We use `k_o = 3^R`: `R` repetitions of
the released single round (`reflectedAmplification`, block map `X ↦ 3X - 4XX†X`), whose block
amplitudes follow `s_{r+1} = 3 s_r - 4 s_r³` (`ampS_succ`, the triple-angle formula), so that
`s_r = sin(3^r θ₀)` with `θ₀ = π/(2·3^R)` and `s_R = 1` (`ampS_top`).

* `amp_step_error`: if `‖X - sW‖ ≤ e` with `W W† = 1`, `0 ≤ s ≤ 1/2` and `e ≤ 1/16`, then
  `‖3X - 4XX†X - (3s - 4s³)W‖ ≤ 7e`;
* `ampIter`, `ampIter_isometry`, `ampIter_block_error`: after `R` rounds the block is within
  `7^R e₀` of `W` when the initial block is within `e₀` of `s₀ W` and `7^{R-1} e₀ ≤ 1/16`;
* `full_output_error`: a block error `δ` of an isometry gives full-output error `√(2δ)`
  (`opt:eq:amplified-full`).
-/

set_option autoImplicit false

namespace SignedFactorSimulation

noncomputable section

open Real ContinuousLinearMap SparseHamiltonian
open scoped InnerProduct InnerProductSpace

/-! ### The sine schedule -/

/-- The block amplitude after `r` of `R` rounds, `sin(3^r π/(2·3^R))`. -/
def ampS (R r : ℕ) : ℝ := Real.sin (3 ^ r * (π / (2 * 3 ^ R)))

theorem ampS_succ (R r : ℕ) : ampS R (r + 1) = 3 * ampS R r - 4 * ampS R r ^ 3 := by
  rw [ampS, ampS, ← Real.sin_three_mul, pow_succ]
  ring_nf

theorem ampS_top (R : ℕ) : ampS R R = 1 := by
  rw [ampS, show (3 : ℝ) ^ R * (π / (2 * 3 ^ R)) = π / 2 by field_simp, Real.sin_pi_div_two]

theorem ampS_arg_le {R r : ℕ} (hr : r < R) : (3 : ℝ) ^ r * (π / (2 * 3 ^ R)) ≤ π / 6 := by
  have h3 : (3 : ℝ) ^ r * 3 ≤ 3 ^ R := by
    rw [← pow_succ]; exact pow_le_pow_right₀ (by norm_num) hr
  have hp := Real.pi_pos
  rw [show (3 : ℝ) ^ r * (π / (2 * 3 ^ R)) = (3 ^ r * 3) * π / (6 * 3 ^ R) by ring,
    div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

theorem ampS_nonneg (R r : ℕ) (hr : r ≤ R) : 0 ≤ ampS R r := by
  apply Real.sin_nonneg_of_nonneg_of_le_pi (by positivity)
  have h3 : (3 : ℝ) ^ r ≤ 3 ^ R := pow_le_pow_right₀ (by norm_num) hr
  have hp := Real.pi_pos
  rw [show (3 : ℝ) ^ r * (π / (2 * 3 ^ R)) = 3 ^ r * π / (2 * 3 ^ R) by ring,
    div_le_iff₀ (by positivity)]
  have h1 := mul_le_mul_of_nonneg_right h3 hp.le
  have h2 : (0 : ℝ) ≤ 3 ^ R * π := by positivity
  nlinarith

theorem ampS_le_half {R r : ℕ} (hr : r < R) : ampS R r ≤ 1 / 2 := by
  rw [ampS, ← Real.sin_pi_div_six]
  apply Real.sin_le_sin_of_le_of_le_pi_div_two
  · have := Real.pi_pos
    have : 0 ≤ (3 : ℝ) ^ r * (π / (2 * 3 ^ R)) := by positivity
    linarith
  · have := Real.pi_pos; linarith
  · exact ampS_arg_le hr

theorem ampS_zero_le (R : ℕ) : ampS R 0 ≤ π / (2 * 3 ^ R) := by
  rw [ampS, pow_zero, one_mul]
  exact Real.sin_le (by positivity)

/-! ### One round -/

variable {P K : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The defect identity `X X† X - s³ W = Δ X† X + s W Δ† X + s² Δ` for `Δ = X - sW`,
`W W† = 1`. -/
theorem cubic_defect (X W : P →L[ℂ] P) (hW : W ∘L W† = 1) (s : ℝ) :
    X ∘L X† ∘L X - ((s ^ 3 : ℝ) : ℂ) • W =
      (X - (s : ℂ) • W) ∘L X† ∘L X + (s : ℂ) • (W ∘L (X - (s : ℂ) • W)† ∘L X) +
        ((s ^ 2 : ℝ) : ℂ) • (X - (s : ℂ) • W) := by
  have hs : (starRingEnd ℂ) (s : ℂ) = s := Complex.conj_ofReal s
  simp only [map_sub, map_smulₛₗ, hs, sub_comp, smul_comp, comp_sub, comp_smul, smul_sub,
    smul_smul]
  have h1 : W ∘L W† ∘L X = X := by rw [← comp_assoc, hW, one_def, id_comp]
  rw [h1]
  push_cast
  module

/-- **One round of amplification**: if `‖X - sW‖ ≤ e`, `W W† = 1`, `‖W‖ ≤ 1`,
`0 ≤ s ≤ 1/2` and `e ≤ 1/16`, then `‖(3X - 4XX†X) - (3s - 4s³)W‖ ≤ 7e`. -/
theorem amp_step_error {X W : P →L[ℂ] P} (hW : W ∘L W† = 1) (hWn : ‖W‖ ≤ 1) {s e : ℝ}
    (hs0 : 0 ≤ s) (hs : s ≤ 1 / 2) (he : ‖X - (s : ℂ) • W‖ ≤ e) (he1 : e ≤ 1 / 16) :
    ‖((3 : ℂ) • X - (4 : ℂ) • (X ∘L X† ∘L X)) - ((3 * s - 4 * s ^ 3 : ℝ) : ℂ) • W‖ ≤ 7 * e := by
  set Δ := X - (s : ℂ) • W with hΔ
  have he0 : 0 ≤ e := (norm_nonneg _).trans he
  have hX : ‖X‖ ≤ s + e := by
    have : X = (s : ℂ) • W + Δ := by rw [hΔ]; abel
    rw [this]
    calc ‖(s : ℂ) • W + Δ‖ ≤ ‖(s : ℂ) • W‖ + ‖Δ‖ := norm_add_le _ _
      _ ≤ s * 1 + e := by
          rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs0]
          exact add_le_add (mul_le_mul_of_nonneg_left hWn hs0) he
      _ = s + e := by ring
  have hXa : ‖X†‖ ≤ s + e := by rw [LinearIsometryEquiv.norm_map]; exact hX
  have hΔa : ‖Δ†‖ ≤ e := by rw [LinearIsometryEquiv.norm_map]; exact he
  have hid : ((3 : ℂ) • X - (4 : ℂ) • (X ∘L X† ∘L X)) - ((3 * s - 4 * s ^ 3 : ℝ) : ℂ) • W =
      (3 : ℂ) • Δ - (4 : ℂ) • (X ∘L X† ∘L X - ((s ^ 3 : ℝ) : ℂ) • W) := by
    rw [hΔ]; push_cast; module
  rw [hid, cubic_defect X W hW s, ← hΔ]
  have b1 : ‖Δ ∘L X† ∘L X‖ ≤ e * ((s + e) * (s + e)) :=
    (opNorm_comp_le _ _).trans (mul_le_mul he ((opNorm_comp_le _ _).trans
      (mul_le_mul hXa hX (norm_nonneg _) (by positivity))) (norm_nonneg _) he0)
  have b2 : ‖(s : ℂ) • (W ∘L Δ† ∘L X)‖ ≤ s * (1 * (e * (s + e))) := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs0]
    exact mul_le_mul_of_nonneg_left ((opNorm_comp_le _ _).trans (mul_le_mul hWn
      ((opNorm_comp_le _ _).trans (mul_le_mul hΔa hX (norm_nonneg _) he0)) (norm_nonneg _)
      zero_le_one)) hs0
  have b3 : ‖((s ^ 2 : ℝ) : ℂ) • Δ‖ ≤ s ^ 2 * e := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left he (by positivity)
  have hsum : ‖Δ ∘L X† ∘L X + (s : ℂ) • (W ∘L Δ† ∘L X) + ((s ^ 2 : ℝ) : ℂ) • Δ‖ ≤
      e * ((s + e) * (s + e)) + s * (1 * (e * (s + e))) + s ^ 2 * e :=
    (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add b1 b2)) b3)
  calc ‖(3 : ℂ) • Δ - (4 : ℂ) • (Δ ∘L X† ∘L X + (s : ℂ) • (W ∘L Δ† ∘L X) +
        ((s ^ 2 : ℝ) : ℂ) • Δ)‖ ≤ ‖(3 : ℂ) • Δ‖ + ‖(4 : ℂ) • (Δ ∘L X† ∘L X +
          (s : ℂ) • (W ∘L Δ† ∘L X) + ((s ^ 2 : ℝ) : ℂ) • Δ)‖ := norm_sub_le _ _
    _ ≤ 3 * e + 4 * (e * ((s + e) * (s + e)) + s * (1 * (e * (s + e))) + s ^ 2 * e) := by
        rw [norm_smul, norm_smul, Complex.norm_ofNat, Complex.norm_ofNat]
        exact add_le_add (mul_le_mul_of_nonneg_left he (by norm_num))
          (mul_le_mul_of_nonneg_left hsum (by norm_num))
    _ ≤ 7 * e := by
        have hse : s + e ≤ 9 / 16 := by linarith
        have h1 : (s + e) * (s + e) ≤ 81 / 256 := by nlinarith
        have h2 : s * (s + e) ≤ 9 / 32 := by nlinarith
        have h3 : s ^ 2 ≤ 1 / 4 := by nlinarith
        nlinarith [mul_nonneg he0 (by positivity : (0 : ℝ) ≤ (s + e) * (s + e)),
          mul_nonneg he0 hs0]

/-! ### Iterated rounds -/

/-- `r` rounds of amplification of the isometry `T` against the output isometry `J`. -/
def ampIter (J T : P →L[ℂ] K) : ℕ → P →L[ℂ] K
  | 0 => T
  | r + 1 => reflectedAmplification J (ampIter J T r)

theorem ampIter_isometry (J T : P →L[ℂ] K) (hJ : J† ∘L J = 1) (hT : T† ∘L T = 1) (r : ℕ) :
    (ampIter J T r)† ∘L ampIter J T r = 1 := by
  induction r with
  | zero => exact hT
  | succ r ih => exact reflectedAmplification_isometry J _ hJ ih

theorem ampIter_block (J T : P →L[ℂ] K) (hJ : J† ∘L J = 1) (hT : T† ∘L T = 1) (r : ℕ) :
    J† ∘L ampIter J T (r + 1) =
      (3 : ℂ) • (J† ∘L ampIter J T r) -
        (4 : ℂ) • ((J† ∘L ampIter J T r) ∘L (J† ∘L ampIter J T r)† ∘L
          (J† ∘L ampIter J T r)) :=
  reflectedAmplification_compression J _ hJ (ampIter_isometry J T hJ hT r)

/-- **The block error after `R` rounds**: if the initial block is within `e₀` of `s₀ W` with
`s₀ = sin(π/(2·3^R))`, `W W† = 1`, `‖W‖ ≤ 1` and `7^(R-1) e₀ ≤ 1/16`, then the block after
`r ≤ R` rounds is within `7^r e₀` of `s_r W`. -/
theorem ampIter_block_error (J T : P →L[ℂ] K) (hJ : J† ∘L J = 1) (hT : T† ∘L T = 1)
    {W : P →L[ℂ] P} (hW : W ∘L W† = 1) (hWn : ‖W‖ ≤ 1) (R : ℕ) {e₀ : ℝ}
    (h0 : ‖J† ∘L T - (ampS R 0 : ℂ) • W‖ ≤ e₀) (he : 7 ^ R * e₀ ≤ 7 / 16) :
    ∀ r, r ≤ R → ‖J† ∘L ampIter J T r - (ampS R r : ℂ) • W‖ ≤ 7 ^ r * e₀ := by
  have he0 : 0 ≤ e₀ := (norm_nonneg _).trans h0
  intro r
  induction r with
  | zero =>
    intro _
    simp only [pow_zero, one_mul]
    exact h0
  | succ r ih =>
    intro hr
    have hrR : r < R := by omega
    have hprev := ih (by omega)
    have hsmall : 7 ^ r * e₀ ≤ 1 / 16 := by
      have h7 : (7 : ℝ) ^ (r + 1) ≤ 7 ^ R := pow_le_pow_right₀ (by norm_num) hrR
      have : (7 : ℝ) ^ (r + 1) * e₀ ≤ 7 / 16 := (mul_le_mul_of_nonneg_right h7 he0).trans he
      rw [pow_succ] at this
      linarith
    have hstep := amp_step_error hW hWn (ampS_nonneg R r hrR.le) (ampS_le_half hrR) hprev hsmall
    rw [ampIter_block J T hJ hT r, ampS_succ]
    calc _ ≤ 7 * (7 ^ r * e₀) := hstep
      _ = 7 ^ (r + 1) * e₀ := by ring

/-! ### Full output -/

/-- **Full-output error** (`opt:eq:amplified-full`): for isometries `T`, `J` and a unitary `W`
with `‖J†T - W‖ ≤ δ`, `‖T - J W‖ ≤ √(2δ)`. -/
theorem full_output_error (J T : P →L[ℂ] K) (hJ : J† ∘L J = 1) (hT : T† ∘L T = 1)
    {W : P →L[ℂ] P} (hW : W† ∘L W = 1) {δ : ℝ} (hδ : ‖J† ∘L T - W‖ ≤ δ) :
    ‖T - J ∘L W‖ ≤ Real.sqrt (2 * δ) := by
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans hδ
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
  have hTx : ‖T x‖ = ‖x‖ := T.norm_map_iff_adjoint_comp_self.mpr hT x
  have hWx : ‖W x‖ = ‖x‖ := W.norm_map_iff_adjoint_comp_self.mpr hW x
  have hJW : ‖J (W x)‖ = ‖x‖ := by rw [J.norm_map_iff_adjoint_comp_self.mpr hJ, hWx]
  have hinner : ⟪J (W x), T x⟫_ℂ = ⟪W x, (J† ∘L T) x⟫_ℂ := by
    rw [comp_apply, adjoint_inner_right]
  have hsq : ‖(T - J ∘L W) x‖ ^ 2 ≤ (Real.sqrt (2 * δ) * ‖x‖) ^ 2 := by
    have hre : RCLike.re ⟪T x, J (W x)⟫_ℂ = (⟪W x, (J† ∘L T) x⟫_ℂ).re := by
      rw [← inner_conj_symm, RCLike.conj_re, hinner]; rfl
    rw [sub_apply, comp_apply, @norm_sub_sq ℂ, hTx, hJW, mul_pow, Real.sq_sqrt (by positivity),
      hre]
    have key : (⟪W x, (J† ∘L T) x⟫_ℂ).re = ‖x‖ ^ 2 - (⟪W x, (W - J† ∘L T) x⟫_ℂ).re := by
      have h := @inner_self_eq_norm_sq ℂ _ _ _ _ (W x)
      rw [RCLike.re_to_complex, hWx] at h
      rw [sub_apply, inner_sub_right, Complex.sub_re, h]
      ring
    rw [key]
    have hb : (⟪W x, (W - J† ∘L T) x⟫_ℂ).re ≤ ‖x‖ * (δ * ‖x‖) := by
      calc (⟪W x, (W - J† ∘L T) x⟫_ℂ).re ≤ ‖⟪W x, (W - J† ∘L T) x⟫_ℂ‖ := Complex.re_le_norm _
        _ ≤ ‖W x‖ * ‖(W - J† ∘L T) x‖ := norm_inner_le_norm _ _
        _ ≤ ‖x‖ * (δ * ‖x‖) := by
            rw [hWx]
            apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
            calc ‖(W - J† ∘L T) x‖ ≤ ‖W - J† ∘L T‖ * ‖x‖ := le_opNorm _ _
              _ ≤ δ * ‖x‖ := by
                  rw [norm_sub_rev]
                  exact mul_le_mul_of_nonneg_right hδ (norm_nonneg _)
    nlinarith [hb]
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hsq

end

end SignedFactorSimulation
