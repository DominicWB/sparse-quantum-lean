import SparseHamiltonian.CayleyApproximation
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.MeanValue

/-!
# The sharp Cayley step error (the manuscript's slot count, equation `hs:eq:gate-clocks`)

The manuscript chooses the number of time slots `M` as the least power of two at least
`max{2, 4αT, (αT)^{3/2}/√(3ε)}` and states that this makes the Cayley discretisation error at
most `ε/4`. That uses the sharp local error `‖C(w) - exp(-iwH)‖ ≤ w³/12` of one Cayley step
`C(w) = (1 - iwH/2)(1 + iwH/2)⁻¹` for a self-adjoint contraction `H`: then `M` steps of size
`w = αT/M` err by at most `M w³/12 = (αT)³/(12 M²) ≤ ε/4`. The released estimate
(`CayleyApproximation.hamiltonian_cayley_error`) has the constant `1` in place of `1/12`.

This file proves the sharp constant, in every complex Hilbert space, without the spectral
theorem:

* `skew_half_inverse_norm_le_one`: for skew-adjoint `X`, every right inverse `R` of
  `1 - X/2` is a contraction (`‖(1 - X/2) u‖ ≥ ‖u‖`);
* `cayley_exp_error_sharp`: `‖(1 + X/2) R - exp X‖ ≤ ‖X‖³/12`. With `E(s) = exp(sX)` and
  `f(s) = (1 + sX/2) - E(s)(1 - sX/2)` one has `f(0) = f'(0) = 0` and `f''(s) = (s/2) E(s) X³`,
  so two applications of the mean value inequality with a moving bound give
  `‖f(1)‖ ≤ ‖X‖³/12`, and `(1 + X/2) R - exp X = f(1) R`;
* `cayley_power_exp_error_sharp`, `hamiltonian_cayley_error_sharp`: `T` steps err by at most
  `T ‖X‖³/12`, respectively `T w³/12` for `X = -iwH`.
-/

set_option autoImplicit false

namespace SparseHamiltonian.GateSchedule

noncomputable section

open ContinuousLinearMap Set
open scoped InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- A skew-adjoint operator has purely imaginary expectation values. -/
theorem re_inner_skew (X : V →L[ℂ] V) (hX : star X = -X) (u : V) :
    RCLike.re (⟪u, X u⟫_ℂ) = 0 := by
  have h1 : ⟪u, X u⟫_ℂ = ⟪(star X) u, u⟫_ℂ := by
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
  rw [hX, neg_apply, inner_neg_left] at h1
  have h2 := congrArg RCLike.re h1
  rw [map_neg, inner_re_symm (𝕜 := ℂ) (X u) u] at h2
  linarith

/-- **The half-step inverse is a contraction**: for skew-adjoint `X`, a right inverse `R` of
`1 - X/2` satisfies `‖R‖ ≤ 1`, since `‖(1 - X/2) u‖² = ‖u‖² + ‖X u‖²/4`. -/
theorem skew_half_inverse_norm_le_one (X R : V →L[ℂ] V) (hX : star X = -X)
    (hR : (1 - (1 / 2 : ℂ) • X) * R = 1) : ‖R‖ ≤ 1 := by
  refine opNorm_le_bound _ zero_le_one (fun v => ?_)
  rw [one_mul]
  have hv : R v - (1 / 2 : ℂ) • X (R v) = v := by
    have h := congrArg (fun T : V →L[ℂ] V => T v) hR
    simpa only [mul_apply_eq_comp, sub_apply, one_apply_eq_self, smul_apply] using h
  have hsq := norm_sub_sq (𝕜 := ℂ) (R v) ((1 / 2 : ℂ) • X (R v))
  have hre : RCLike.re (⟪R v, (1 / 2 : ℂ) • X (R v)⟫_ℂ) = 0 := by
    rw [inner_smul_right]
    have h0 := re_inner_skew X hX (R v)
    have e : ((1 / 2 : ℂ) * ⟪R v, X (R v)⟫_ℂ).re = (1 / 2 : ℝ) * (⟪R v, X (R v)⟫_ℂ).re := by
      simp [Complex.mul_re]
    change ((1 / 2 : ℂ) * ⟪R v, X (R v)⟫_ℂ).re = 0
    rw [e]
    change (1 / 2 : ℝ) * RCLike.re (⟪R v, X (R v)⟫_ℂ) = 0
    rw [h0, mul_zero]
  rw [hv, hre] at hsq
  have hle : ‖R v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    nlinarith [sq_nonneg ‖(1 / 2 : ℂ) • X (R v)‖]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) (by norm_num)).mp hle

/-- `exp (s X)` is a contraction for skew-adjoint `X` and real `s`. -/
theorem exp_real_smul_norm_le (X : V →L[ℂ] V) (hX : star X = -X) (s : ℝ) :
    ‖NormedSpace.exp (s • X)‖ ≤ 1 := by
  apply CayleyApproximation.skew_exp_norm_le
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ), star_smul, hX, smul_neg, RCLike.star_def,
    RCLike.conj_ofReal]

/-- The derivative of `s ↦ s² c`. -/
theorem hasDerivAt_sq_mul (c s : ℝ) :
    HasDerivAt (fun x : ℝ => x ^ 2 / 4 * c) (s / 2 * c) s := by
  have h := ((hasDerivAt_pow 2 s).div_const 4).mul_const c
  refine h.congr_deriv ?_
  rw [show (2 - 1 : ℕ) = 1 from rfl, pow_one]
  push_cast
  ring

/-- The derivative of `s ↦ s³ c`. -/
theorem hasDerivAt_cube_mul (c s : ℝ) :
    HasDerivAt (fun x : ℝ => x ^ 3 / 12 * c) (s ^ 2 / 4 * c) s := by
  have h := ((hasDerivAt_pow 3 s).div_const 12).mul_const c
  refine h.congr_deriv ?_
  rw [show (3 - 1 : ℕ) = 2 from rfl]
  push_cast
  ring

/-- The first derivative of `f(s) = (1 + sX/2) - exp(sX)(1 - sX/2)`. -/
theorem cayley_aux_deriv1 (X : V →L[ℂ] V) (s : ℝ) :
    HasDerivAt (fun x : ℝ => (1 + (x / 2) • X) - NormedSpace.exp (x • X) * (1 - (x / 2) • X))
      ((1 / 2 : ℝ) • X - (1 / 2 : ℝ) • (NormedSpace.exp (s • X) * X) +
        (s / 2) • (NormedSpace.exp (s • X) * X ^ 2)) s := by
  have hlin : HasDerivAt (fun x : ℝ => (x / 2) • X) ((1 / 2 : ℝ) • X) s :=
    ((hasDerivAt_id' s).div_const 2).smul_const X
  have h3 := (hasDerivAt_exp_smul_const (𝕂 := ℝ) X s).fun_mul (hlin.const_sub 1)
  have h4 := (hlin.const_add 1).sub h3
  refine h4.congr_deriv ?_
  simp only [mul_sub, mul_one, mul_neg, mul_smul_comm, sq, ← mul_assoc]
  module

/-- The second derivative: `f''(s) = (s/2) exp(sX) X³`. -/
theorem cayley_aux_deriv2 (X : V →L[ℂ] V) (s : ℝ) :
    HasDerivAt (fun x : ℝ => (1 / 2 : ℝ) • X - (1 / 2 : ℝ) • (NormedSpace.exp (x • X) * X) +
        (x / 2) • (NormedSpace.exp (x • X) * X ^ 2))
      ((s / 2) • (NormedSpace.exp (s • X) * X ^ 3)) s := by
  have hE := hasDerivAt_exp_smul_const (𝕂 := ℝ) X s
  have h1 := (hE.mul_const X).const_smul (1 / 2 : ℝ)
  have h2 := ((hasDerivAt_id' s).div_const 2).fun_smul (hE.mul_const (X ^ 2))
  have h3 := ((hasDerivAt_const s ((1 / 2 : ℝ) • X)).sub h1).add h2
  refine h3.congr_deriv ?_
  simp only [pow_succ, pow_zero, one_mul, ← mul_assoc]
  module

/-- **The sharp local Cayley error**: for skew-adjoint `X` and a right inverse `R` of
`1 - X/2`, `‖(1 + X/2) R - exp X‖ ≤ ‖X‖³/12`. -/
theorem cayley_exp_error_sharp (X R : V →L[ℂ] V) (hX : star X = -X)
    (hR : (1 - (1 / 2 : ℂ) • X) * R = 1) :
    ‖(1 + (1 / 2 : ℂ) • X) * R - NormedSpace.exp X‖ ≤ ‖X‖ ^ 3 / 12 := by
  have hEn : ∀ s : ℝ, ‖NormedSpace.exp (s • X)‖ ≤ 1 := fun s => exp_real_smul_norm_le X hX s
  -- the bound on the second derivative
  have hf''n : ∀ s : ℝ, 0 ≤ s →
      ‖(s / 2) • (NormedSpace.exp (s • X) * X ^ 3)‖ ≤ s / 2 * ‖X‖ ^ 3 := by
    intro s hs
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ s / 2)]
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    calc ‖NormedSpace.exp (s • X) * X ^ 3‖ ≤ ‖NormedSpace.exp (s • X)‖ * ‖X ^ 3‖ :=
          norm_mul_le _ _
      _ ≤ 1 * ‖X‖ ^ 3 := mul_le_mul (hEn s) (norm_pow_le' X (by norm_num)) (norm_nonneg _)
          zero_le_one
      _ = ‖X‖ ^ 3 := one_mul _
  -- the first derivative on `[0, 1]`
  have hstep1 : ∀ x ∈ Icc (0 : ℝ) 1,
      ‖(1 / 2 : ℝ) • X - (1 / 2 : ℝ) • (NormedSpace.exp (x • X) * X) +
        (x / 2) • (NormedSpace.exp (x • X) * X ^ 2)‖ ≤ x ^ 2 / 4 * ‖X‖ ^ 3 := by
    intro x hx
    refine image_norm_le_of_norm_deriv_right_le_deriv_boundary
      (f := fun x : ℝ => (1 / 2 : ℝ) • X - (1 / 2 : ℝ) • (NormedSpace.exp (x • X) * X) +
        (x / 2) • (NormedSpace.exp (x • X) * X ^ 2))
      (f' := fun x : ℝ => (x / 2) • (NormedSpace.exp (x • X) * X ^ 3))
      (B := fun x : ℝ => x ^ 2 / 4 * ‖X‖ ^ 3) (B' := fun x : ℝ => x / 2 * ‖X‖ ^ 3)
      (fun y _ => (cayley_aux_deriv2 X y).continuousAt.continuousWithinAt)
      (fun y _ => (cayley_aux_deriv2 X y).hasDerivWithinAt) ?_ (fun y => hasDerivAt_sq_mul _ y)
      ?_ hx
    · simp
    · intro y hy
      exact hf''n y hy.1
  -- the function on `[0, 1]`
  have hstep2 : ‖(1 + ((1 : ℝ) / 2) • X) - NormedSpace.exp ((1 : ℝ) • X) *
      (1 - ((1 : ℝ) / 2) • X)‖ ≤ (1 : ℝ) ^ 3 / 12 * ‖X‖ ^ 3 := by
    refine image_norm_le_of_norm_deriv_right_le_deriv_boundary
      (f := fun x : ℝ => (1 + (x / 2) • X) - NormedSpace.exp (x • X) * (1 - (x / 2) • X))
      (f' := fun x : ℝ => (1 / 2 : ℝ) • X - (1 / 2 : ℝ) • (NormedSpace.exp (x • X) * X) +
        (x / 2) • (NormedSpace.exp (x • X) * X ^ 2))
      (B := fun x : ℝ => x ^ 3 / 12 * ‖X‖ ^ 3) (B' := fun x : ℝ => x ^ 2 / 4 * ‖X‖ ^ 3)
      (fun y _ => (cayley_aux_deriv1 X y).continuousAt.continuousWithinAt)
      (fun y _ => (cayley_aux_deriv1 X y).hasDerivWithinAt) ?_ (fun y => hasDerivAt_cube_mul _ y)
      ?_ (⟨zero_le_one, le_rfl⟩ : (1 : ℝ) ∈ Icc (0 : ℝ) 1)
    · simp
    · intro y hy
      exact hstep1 y (Ico_subset_Icc_self hy)
  -- the Cayley step
  have hc : ((1 : ℝ) / 2) • X = (1 / 2 : ℂ) • X := by
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
    norm_num
  rw [hc, one_smul] at hstep2
  have hdiff : (1 + (1 / 2 : ℂ) • X) * R - NormedSpace.exp X =
      ((1 + (1 / 2 : ℂ) • X) - NormedSpace.exp X * (1 - (1 / 2 : ℂ) • X)) * R := by
    rw [sub_mul, mul_assoc, hR, mul_one]
  rw [hdiff]
  calc _ ≤ ‖(1 + (1 / 2 : ℂ) • X) - NormedSpace.exp X * (1 - (1 / 2 : ℂ) • X)‖ * ‖R‖ :=
        norm_mul_le _ _
    _ ≤ ((1 : ℝ) ^ 3 / 12 * ‖X‖ ^ 3) * 1 :=
        mul_le_mul hstep2 (skew_half_inverse_norm_le_one X R hX hR) (norm_nonneg _)
          (by positivity)
    _ = ‖X‖ ^ 3 / 12 := by ring

/-- **The sharp global Cayley error**: `T` Cayley steps of a skew-adjoint `X` differ from
`exp (T X)` by at most `T ‖X‖³/12`. -/
theorem cayley_power_exp_error_sharp (X R : V →L[ℂ] V) (hSkew : star X = -X)
    (hR : (1 - (1 / 2 : ℂ) • X) * R = 1) (T : ℕ) :
    ‖((1 + (1 / 2 : ℂ) • X) * R) ^ T - NormedSpace.exp (T • X)‖ ≤
      (T : ℝ) * (‖X‖ ^ 3 / 12) := by
  rcases subsingleton_or_nontrivial V with h | h
  · letI := h
    have hz : ((1 + (1 / 2 : ℂ) • X) * R) ^ T - NormedSpace.exp (T • X) = 0 :=
      Subsingleton.elim _ _
    rw [hz, norm_zero]
    positivity
  · letI := h
    letI : NormedAlgebra ℚ (V →L[ℂ] V) := .restrictScalars ℚ ℂ _
    rw [NormedSpace.exp_nsmul]
    exact (CayleyApproximation.contraction_power_difference _ _
      (CayleyTransfer.skew_cayley_norm_le_one X R hSkew hR)
      (CayleyApproximation.skew_exp_norm_le X hSkew) T).trans
      (mul_le_mul_of_nonneg_left (cayley_exp_error_sharp X R hSkew hR) (Nat.cast_nonneg _))

/-- **The sharp Hamiltonian Cayley error**: for a self-adjoint contraction `H` and `w ≥ 0`,
`T` Cayley steps of size `w` approximate `exp(-iTwH)` within `T w³/12` (the released
`CayleyApproximation.hamiltonian_cayley_error` has `T w³`). -/
theorem hamiltonian_cayley_error_sharp (H R : V →L[ℂ] V) (w : ℝ)
    (hw : 0 ≤ w) (hHerm : star H = H) (hH : ‖H‖ ≤ 1)
    (hR : CayleyTransfer.cayleyDenominator w H * R = 1) (T : ℕ) :
    ‖(CayleyTransfer.cayleyNumerator w H * R) ^ T -
      NormedSpace.exp ((-Complex.I * (T : ℂ) * (w : ℂ)) • H)‖ ≤ (T : ℝ) * w ^ 3 / 12 := by
  let X : V →L[ℂ] V := (-Complex.I * (w : ℂ)) • H
  have hXw : ‖X‖ ≤ w := by
    simp only [X, norm_smul, norm_mul, norm_neg, Complex.norm_I, one_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw]
    simpa using mul_le_mul_of_nonneg_left hH hw
  have hSkew : star X = -X := by
    simp only [X, star_smul, hHerm, star_mul, star_neg, Complex.star_def,
      Complex.conj_I, Complex.conj_ofReal]
    module
  have hDen : 1 - (1 / 2 : ℂ) • X = CayleyTransfer.cayleyDenominator w H := by
    simp only [X, CayleyTransfer.cayleyDenominator, smul_smul]
    module
  have hNum : 1 + (1 / 2 : ℂ) • X = CayleyTransfer.cayleyNumerator w H := by
    simp only [X, CayleyTransfer.cayleyNumerator, smul_smul]
    module
  have hExp : T • X = (-Complex.I * (T : ℂ) * (w : ℂ)) • H := by
    rw [← Nat.cast_smul_eq_nsmul ℂ]
    simp only [X, smul_smul]
    congr 1
    ring
  have h := cayley_power_exp_error_sharp X R hSkew (hDen ▸ hR) T
  rw [hNum, hExp] at h
  refine h.trans ?_
  have h3 : ‖X‖ ^ 3 ≤ w ^ 3 := pow_le_pow_left₀ (norm_nonneg X) hXw 3
  have hT : (0 : ℝ) ≤ T := Nat.cast_nonneg _
  nlinarith

end

end SparseHamiltonian.GateSchedule
