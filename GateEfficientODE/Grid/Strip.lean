import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Horizontal contour shifts and Fourier decay on a strip

* `integral_shift`: a function holomorphic between two horizontal lines, with
  an envelope that vanishes at both ends of the strip, has the same integral
  along both lines (Cauchy–Goursat on rectangles, vertical edges tending to
  zero).
* `fourier_norm_le`: if `ψ` is holomorphic on the closed strip `|Im z| ≤ b`
  with integrable envelope `G (Re z)`, then its Fourier transform on the real
  line decays exponentially: `‖𝓕 ψ ξ‖ ≤ exp (-2π b |ξ|) ∫ G`.  The transform
  is Mathlib's `𝓕 f ξ = ∫ exp (-2π i x ξ) f x dx`; the line of integration is
  moved to `Im z = ∓ b` according to the sign of `ξ`.
-/

namespace SparseHamiltonian.StripQuadrature

noncomputable section
open Complex MeasureTheory Filter Set
open scoped Interval Topology Real FourierTransform

theorem abs_le_of_mem_uIcc_zero {y y₀ : ℝ} (h : y ∈ [[0, y₀]]) : |y| ≤ |y₀| := by
  rcases Set.mem_uIcc.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [abs_of_nonneg h1, abs_of_nonneg (h1.trans h2)]
    exact h2
  · rw [abs_of_nonpos h2, abs_of_nonpos (h1.trans h2)]
    linarith

section Shift

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- The rectangle identity between the real line and the line `Im z = y₀`. -/
theorem rect_identity (χ : ℂ → E) (y₀ : ℝ)
    (hd : ∀ z : ℂ, z.im ∈ [[0, y₀]] → DifferentiableAt ℂ χ z) (R : ℝ) :
    (∫ x : ℝ in (-R)..R, χ x) - (∫ x : ℝ in (-R)..R, χ (x + y₀ * I)) +
      I • (∫ y : ℝ in (0 : ℝ)..y₀, χ (R + y * I)) -
      I • (∫ y : ℝ in (0 : ℝ)..y₀, χ (-R + y * I)) = 0 := by
  have h := integral_boundary_rect_eq_zero_of_differentiableOn χ ((-R : ℝ) : ℂ)
    ((R : ℂ) + y₀ * I) (fun z hz => by
      refine (hd z ?_).differentiableWithinAt
      have h2 := (mem_reProdIm.mp hz).2
      simpa using h2)
  simpa using h

omit [CompleteSpace E] in
/-- **Horizontal contour shift.** -/
theorem integral_shift (χ : ℂ → E) (y₀ : ℝ)
    (hd : ∀ z : ℂ, z.im ∈ [[0, y₀]] → DifferentiableAt ℂ χ z)
    (G : ℝ → ℝ) (hG : ∀ z : ℂ, z.im ∈ [[0, y₀]] → ‖χ z‖ ≤ G z.re)
    (hGtop : Tendsto G atTop (𝓝 0)) (hGbot : Tendsto G atBot (𝓝 0))
    (hi₀ : Integrable (fun x : ℝ => χ x))
    (hi₁ : Integrable (fun x : ℝ => χ (x + y₀ * I))) :
    ∫ x : ℝ, χ x = ∫ x : ℝ, χ (x + y₀ * I) := by
  have hA : Tendsto (fun R : ℝ => ∫ x : ℝ in (-R)..R, χ x) atTop (𝓝 (∫ x : ℝ, χ x)) :=
    intervalIntegral_tendsto_integral hi₀ tendsto_neg_atTop_atBot tendsto_id
  have hB : Tendsto (fun R : ℝ => ∫ x : ℝ in (-R)..R, χ (x + y₀ * I)) atTop
      (𝓝 (∫ x : ℝ, χ (x + y₀ * I))) :=
    intervalIntegral_tendsto_integral hi₁ tendsto_neg_atTop_atBot tendsto_id
  have hV : ∀ s : ℝ, ‖∫ y : ℝ in (0 : ℝ)..y₀, χ (s + y * I)‖ ≤ G s * |y₀ - 0| := by
    intro s
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro y hy
    have hy' : y ∈ [[0, y₀]] := Set.uIoc_subset_uIcc hy
    have h := hG ((s : ℂ) + y * I) (by simpa using hy')
    simpa using h
  have hVp : Tendsto (fun R : ℝ => ∫ y : ℝ in (0 : ℝ)..y₀, χ (R + y * I)) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun R => hV R)
    simpa using hGtop.mul_const |y₀ - 0|
  have hVm : Tendsto (fun R : ℝ => ∫ y : ℝ in (0 : ℝ)..y₀, χ (-R + y * I)) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun R => by simpa using hV (-R))
    simpa using (hGbot.comp tendsto_neg_atTop_atBot).mul_const |y₀ - 0|
  have hlim := ((hA.sub hB).add (hVp.const_smul I)).sub (hVm.const_smul I)
  have hzero : (fun R : ℝ => (∫ x : ℝ in (-R)..R, χ x) - (∫ x : ℝ in (-R)..R, χ (x + y₀ * I)) +
      I • (∫ y : ℝ in (0 : ℝ)..y₀, χ (R + y * I)) -
      I • (∫ y : ℝ in (0 : ℝ)..y₀, χ (-R + y * I))) = fun _ => 0 :=
    funext (rect_identity χ y₀ hd)
  rw [hzero] at hlim
  have huniq := tendsto_nhds_unique hlim tendsto_const_nhds
  simp only [smul_zero, add_zero, sub_zero] at huniq
  exact sub_eq_zero.mp huniq

end Shift

section Fourier

/-- The Fourier phase continued to the complex plane. -/
def phase (ξ : ℝ) (z : ℂ) : ℂ := Complex.exp (-(2 * π * ξ : ℝ) * I * z)

theorem norm_phase (ξ : ℝ) (z : ℂ) : ‖phase ξ z‖ = Real.exp (2 * π * ξ * z.im) := by
  rw [phase, Complex.norm_exp]
  congr 1
  simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

theorem phase_ofReal (ξ x : ℝ) :
    phase ξ x = Complex.exp (↑(-2 * π * x * ξ) * I) := by
  rw [phase]
  congr 1
  push_cast
  ring

theorem phase_differentiable (ξ : ℝ) : Differentiable ℂ (phase ξ) := by
  intro z
  unfold phase
  fun_prop

/-- **Exponential decay of the Fourier transform** of a function holomorphic on
the closed strip `|Im z| ≤ b`. -/
theorem fourier_norm_le (ψ : ℂ → ℂ) (b : ℝ) (hb : 0 ≤ b)
    (hd : ∀ z : ℂ, |z.im| ≤ b → DifferentiableAt ℂ ψ z)
    (G : ℝ → ℝ) (hG : ∀ z : ℂ, |z.im| ≤ b → ‖ψ z‖ ≤ G z.re)
    (hGi : Integrable G) (hGtop : Tendsto G atTop (𝓝 0)) (hGbot : Tendsto G atBot (𝓝 0))
    (ξ : ℝ) :
    ‖𝓕 (fun x : ℝ => ψ x) ξ‖ ≤ Real.exp (-(2 * π * b * |ξ|)) * ∫ x, G x := by
  set y₀ : ℝ := if 0 ≤ ξ then -b else b with hy₀def
  have hy₀abs : |y₀| = b := by
    rw [hy₀def]
    split_ifs <;> simp [abs_of_nonneg hb]
  have hy₀ξ : 2 * π * ξ * y₀ = -(2 * π * b * |ξ|) := by
    rw [hy₀def]
    split_ifs with h
    · rw [abs_of_nonneg h]; ring
    · rw [abs_of_neg (not_le.mp h)]; ring
  let χ : ℂ → ℂ := fun z => phase ξ z * ψ z
  have hχd : ∀ z : ℂ, z.im ∈ [[0, y₀]] → DifferentiableAt ℂ χ z := by
    intro z hz
    have hz' : |z.im| ≤ b := by
      rw [← hy₀abs]
      exact abs_le_of_mem_uIcc_zero hz
    exact (phase_differentiable ξ z).mul (hd z hz')
  have hcont : ∀ y : ℝ, |y| ≤ b → Continuous (fun x : ℝ => ψ (x + y * I)) := by
    intro y hy
    refine continuous_iff_continuousAt.mpr (fun x => ?_)
    have h1 : DifferentiableAt ℂ ψ (x + y * I) := hd _ (by simpa using hy)
    have h2 : ContinuousAt (fun t : ℝ => (t : ℂ) + y * I) x :=
      (continuous_ofReal.add continuous_const).continuousAt
    exact ContinuousAt.comp (g := ψ) (f := fun t : ℝ => (t : ℂ) + y * I) h1.continuousAt h2
  have hbound : ∀ z : ℂ, z.im ∈ [[0, y₀]] →
      ‖χ z‖ ≤ Real.exp (2 * π * b * |ξ|) * G z.re := by
    intro z hz
    have hz' : |z.im| ≤ b := by
      rw [← hy₀abs]
      exact abs_le_of_mem_uIcc_zero hz
    have hψ := hG z hz'
    rw [norm_mul, norm_phase]
    have he : Real.exp (2 * π * ξ * z.im) ≤ Real.exp (2 * π * b * |ξ|) := by
      apply Real.exp_le_exp.mpr
      have h1 : ξ * z.im ≤ |ξ| * |z.im| := by
        rw [← abs_mul]; exact le_abs_self _
      have h2 : |ξ| * |z.im| ≤ |ξ| * b := mul_le_mul_of_nonneg_left hz' (abs_nonneg _)
      nlinarith [Real.pi_pos]
    exact mul_le_mul he hψ (norm_nonneg _) (Real.exp_pos _).le
  have hGtop' : Tendsto (fun x => Real.exp (2 * π * b * |ξ|) * G x) atTop (𝓝 0) := by
    simpa using hGtop.const_mul (Real.exp (2 * π * b * |ξ|))
  have hGbot' : Tendsto (fun x => Real.exp (2 * π * b * |ξ|) * G x) atBot (𝓝 0) := by
    simpa using hGbot.const_mul (Real.exp (2 * π * b * |ξ|))
  -- integrability on the real line
  have hi₀ : Integrable (fun x : ℝ => χ x) := by
    refine hGi.mono' ?_ (Eventually.of_forall (fun x => ?_))
    · have hc : Continuous (fun x : ℝ => χ x) := by
        have h1 := hcont 0 (by simpa using hb)
        have h2 : Continuous (fun x : ℝ => phase ξ x) :=
          (phase_differentiable ξ).continuous.comp continuous_ofReal
        have h1' : Continuous (fun x : ℝ => ψ x) := by simpa using h1
        exact h2.mul h1'
      exact hc.aestronglyMeasurable
    · have h := hG (x : ℂ) (by simpa using hb)
      simp only [χ, norm_mul, norm_phase, Complex.ofReal_im, mul_zero, Real.exp_zero, one_mul]
      simpa using h
  -- integrability on the shifted line
  have hi₁ : Integrable (fun x : ℝ => χ (x + y₀ * I)) := by
    refine (hGi.const_mul (Real.exp (-(2 * π * b * |ξ|)))).mono' ?_
      (Eventually.of_forall (fun x => ?_))
    · have hc : Continuous (fun x : ℝ => χ (x + y₀ * I)) := by
        have h1 := hcont y₀ hy₀abs.le
        have h2 : Continuous (fun x : ℝ => phase ξ (x + y₀ * I)) :=
          (phase_differentiable ξ).continuous.comp (continuous_ofReal.add continuous_const)
        exact h2.mul h1
      exact hc.aestronglyMeasurable
    · have h := hG ((x : ℂ) + y₀ * I) (by simpa using hy₀abs.le)
      simp only [χ, norm_mul, norm_phase]
      have him : ((x : ℂ) + y₀ * I).im = y₀ := by simp
      have hre : ((x : ℂ) + y₀ * I).re = x := by simp
      rw [him, hy₀ξ]
      rw [hre] at h
      exact mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
  have hshift := integral_shift χ y₀ hχd _ hbound hGtop' hGbot' hi₀ hi₁
  have hF : 𝓕 (fun x : ℝ => ψ x) ξ = ∫ x : ℝ, χ x := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    congr 1
    ext x
    simp only [χ, smul_eq_mul, phase_ofReal]
  rw [hF, hshift, ← integral_const_mul]
  refine norm_integral_le_of_norm_le (hGi.const_mul _) (Eventually.of_forall (fun x => ?_))
  have h := hG ((x : ℂ) + y₀ * I) (by simpa using hy₀abs.le)
  simp only [χ, norm_mul, norm_phase]
  have him : ((x : ℂ) + y₀ * I).im = y₀ := by simp
  have hre : ((x : ℂ) + y₀ * I).re = x := by simp
  rw [him, hy₀ξ]
  rw [hre] at h
  exact mul_le_mul_of_nonneg_left h (Real.exp_pos _).le

end Fourier

end

end SparseHamiltonian.StripQuadrature
