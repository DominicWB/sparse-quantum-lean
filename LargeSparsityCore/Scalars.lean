import LargeSparsityCore.CayleyBlocks
import SparseHamiltonian.FilterCoefficients
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent

set_option autoImplicit false

/-!
# Scalar facts for the isolated phases and the filter

For an integer `p ≥ 3` put `θ = π/p` and `2q = cot θ` (`opt:eq:phase-choice`). The isolated Cayley
phases `λ_± = 1 - 2/(1 ± 2qi)` of `LargeSparsityCore.CayleyBlocks` are then `e^{±2iθ}`
(`lamp_eq_exp`, `lamm_eq_exp`), so they are nontrivial `p`th roots of unity
(`exp_pow_eq_one`, `lamp_ne_one`, `lamm_ne_one`) and the average `g_p` vanishes at both
(`geometricSum_eq_zero`). Their distances are
`|λ_± - 1| = 2/√(1 + 4q²) ≤ 1/q` and `|λ₊ - λ₋| = 8q/(1 + 4q²) ≥ 1/q` for `q ≥ 1/2`
(`norm_lamp_sub_one_le`, `norm_lamp_sub_lamm`).

On a circle `|z - λ| = ζ` about a `p`th root of unity `λ ≠ 1`, the geometric-sum identity gives
`|g_p(z)| ≤ ζ p (1 + ζ)^p / 2`, and every average satisfies `|g_B(z)| ≤ (1 + ζ)^B`
(`norm_geometricAverage_root_le`, `norm_geometricAverage_le`).
-/

namespace LargeSparsityCore.Scalars

noncomputable section

open Complex CayleyBlocks SparseHamiltonian
open scoped Real

theorem lamp_eq_div (q : ℝ) : lamp q = (2 * q * I - 1) / (1 + 2 * q * I) := by
  have hne := Spectral.one_add_ne_zero q
  rw [lamp]
  field_simp
  ring

theorem lamm_eq_div (q : ℝ) : lamm q = (-(2 * q * I) - 1) / (1 - 2 * q * I) := by
  have hne := Spectral.one_sub_ne_zero q
  rw [lamm]
  field_simp
  ring

/-- With `2q = cot θ`, the Cayley phase `λ₊` is `e^{2iθ}`. -/
theorem lamp_eq_exp (θ : ℝ) (hs : Real.sin θ ≠ 0) :
    lamp (Real.cot θ / 2) = Complex.exp (2 * θ * I) := by
  have hne := Spectral.one_add_ne_zero (Real.cot θ / 2)
  rw [lamp_eq_div, div_eq_iff hne]
  have hcot : Real.cot θ = Real.cos θ / Real.sin θ := Real.cot_eq_cos_div_sin θ
  have hexp : Complex.exp (2 * θ * I) = (Real.cos (2 * θ) : ℂ) + (Real.sin (2 * θ) : ℂ) * I := by
    rw [show (2 * (θ : ℂ) * I) = ((2 * θ : ℝ) : ℂ) * I by push_cast; ring, Complex.exp_mul_I,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  rw [hexp]
  apply Complex.ext
  · simp only [Complex.sub_re, Complex.mul_re, Complex.add_re, Complex.mul_im, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_re,
      Complex.one_im, Complex.re_ofNat, Complex.im_ofNat]
    rw [hcot, Real.cos_two_mul, Real.sin_two_mul]
    field_simp
    ring
  · simp only [Complex.sub_im, Complex.mul_re, Complex.add_re, Complex.mul_im, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_re,
      Complex.one_im, Complex.re_ofNat, Complex.im_ofNat]
    rw [hcot, Real.cos_two_mul, Real.sin_two_mul]
    field_simp
    linear_combination (-4 * Real.cos θ) * Real.sin_sq_add_cos_sq θ

theorem lamm_eq_lamp_neg (q : ℝ) : lamm q = lamp (-q) := by
  simp only [lamm, lamp, Complex.ofReal_neg]
  ring_nf

/-- With `2q = cot θ`, the Cayley phase `λ₋` is `e^{-2iθ}`. -/
theorem lamm_eq_exp (θ : ℝ) (hs : Real.sin θ ≠ 0) :
    lamm (Real.cot θ / 2) = Complex.exp (2 * (-θ : ℝ) * I) := by
  have hneg : Real.cot (-θ) = -Real.cot θ := by
    rw [Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin, Real.cos_neg, Real.sin_neg, div_neg]
  rw [lamm_eq_lamp_neg, show -(Real.cot θ / 2) = Real.cot (-θ) / 2 by rw [hneg]; ring]
  exact lamp_eq_exp (-θ) (by rwa [Real.sin_neg, neg_ne_zero])

/-- `e^{2iθ}` is a `p`th root of unity when `pθ = π`. -/
theorem exp_pow_eq_one (θ : ℝ) (p : ℕ) (hθ : (p : ℝ) * θ = π ∨ (p : ℝ) * θ = -π) :
    Complex.exp (2 * θ * I) ^ p = 1 := by
  rw [← Complex.exp_nat_mul]
  rcases hθ with h | h
  · rw [show (p : ℂ) * (2 * θ * I) = 2 * ((p * θ : ℝ) : ℂ) * I by push_cast; ring, h]
    exact Complex.exp_two_pi_mul_I
  · rw [show (p : ℂ) * (2 * θ * I) = -(2 * π * I) by
      rw [show (p : ℂ) * (2 * θ * I) = 2 * ((p * θ : ℝ) : ℂ) * I by push_cast; ring, h]
      push_cast; ring, Complex.exp_neg, Complex.exp_two_pi_mul_I, inv_one]

theorem lamp_sub_one (q : ℝ) : lamp q - 1 = -(2 / (1 + 2 * q * I)) := by
  rw [lamp]
  ring

theorem lamp_ne_one (q : ℝ) : lamp q ≠ 1 := by
  intro h
  have h1 : lamp q - 1 = 0 := by rw [h, sub_self]
  rw [lamp_sub_one, neg_eq_zero, div_eq_zero_iff] at h1
  rcases h1 with h1 | h1
  · norm_num at h1
  · exact Spectral.one_add_ne_zero q h1

theorem lamm_ne_one (q : ℝ) : lamm q ≠ 1 := by
  rw [lamm_eq_lamp_neg]
  exact lamp_ne_one (-q)

theorem norm_one_add (q : ℝ) : ‖1 + 2 * q * I‖ = Real.sqrt (1 + 4 * q ^ 2) := by
  rw [← Real.sqrt_sq (norm_nonneg _), Complex.sq_norm, Complex.normSq_apply]
  congr 1
  simp
  ring

/-- `|λ₊ - 1| ≤ 1/q`. -/
theorem norm_lamp_sub_one_le (q : ℝ) (hq : 0 < q) : ‖lamp q - 1‖ ≤ 1 / q := by
  rw [lamp_sub_one, norm_neg, norm_div, Complex.norm_ofNat, norm_one_add]
  have h2q : 2 * q ≤ Real.sqrt (1 + 4 * q ^ 2) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith
  rw [div_le_div_iff₀ (Real.sqrt_pos.mpr (by positivity)) hq]
  linarith

theorem norm_lamm_sub_one_le (q : ℝ) (hq : 0 < q) : ‖lamm q - 1‖ ≤ 1 / q := by
  rw [lamm_eq_lamp_neg, lamp_sub_one, norm_neg, norm_div, Complex.norm_ofNat]
  have e : ‖(1 : ℂ) + 2 * ((-q : ℝ) : ℂ) * I‖ = Real.sqrt (1 + 4 * q ^ 2) := by
    rw [norm_one_add]
    ring_nf
  rw [e]
  have h2q : 2 * q ≤ Real.sqrt (1 + 4 * q ^ 2) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith
  rw [div_le_div_iff₀ (Real.sqrt_pos.mpr (by positivity)) hq]
  linarith

/-- `|λ₊ - λ₋| ≥ 1/q` for `q ≥ 1/2`. -/
theorem norm_lamp_sub_lamm (q : ℝ) (hq : 1 / 2 ≤ q) : 1 / q ≤ ‖lamp q - lamm q‖ := by
  have hq0 : 0 < q := by linarith
  have h1 := Spectral.one_add_ne_zero q
  have h2 := Spectral.one_sub_ne_zero q
  have e : lamp q - lamm q = (8 * q * I) / (1 + 4 * q ^ 2) := by
    have h3 : (1 + 4 * (q : ℂ) ^ 2) = (1 + 2 * q * I) * (1 - 2 * q * I) := by
      ring_nf
      rw [Complex.I_sq]
      ring
    rw [lamp, lamm, h3]
    field_simp
    ring
  rw [e, norm_div, show (1 + 4 * (q : ℂ) ^ 2) = ((1 + 4 * q ^ 2 : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity),
    show (8 * (q : ℂ) * I) = ((8 * q : ℝ) : ℂ) * I by push_cast; ring, norm_mul,
    Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity),
    div_le_div_iff₀ hq0 (by positivity)]
  nlinarith

/-- The geometric sum vanishes at a nontrivial root of unity. -/
theorem geometricSum_eq_zero (μ : ℂ) (p : ℕ) (hμ : μ ^ p = 1) (hμ1 : μ ≠ 1) :
    FilterCoefficients.geometricSum p μ = 0 := by
  rw [FilterCoefficients.geometricSum, geom_sum_eq hμ1, hμ, sub_self, zero_div]

/-- `|zʲ - μʲ| ≤ j Mʲ⁻¹ |z - μ|` when `|z|, |μ| ≤ M`. -/
theorem norm_pow_sub_pow_le (z μ : ℂ) {M : ℝ} (hz : ‖z‖ ≤ M) (hμ : ‖μ‖ ≤ M) (j : ℕ) :
    ‖z ^ j - μ ^ j‖ ≤ j * M ^ (j - 1) * ‖z - μ‖ := by
  induction j with
  | zero => simp
  | succ j ih =>
      have hM : 0 ≤ M := (norm_nonneg _).trans hz
      have e : z ^ (j + 1) - μ ^ (j + 1) = z * (z ^ j - μ ^ j) + (z - μ) * μ ^ j := by ring
      rw [e]
      calc ‖z * (z ^ j - μ ^ j) + (z - μ) * μ ^ j‖ ≤
            ‖z‖ * ‖z ^ j - μ ^ j‖ + ‖z - μ‖ * ‖μ‖ ^ j := by
            refine (norm_add_le _ _).trans ?_
            rw [norm_mul, norm_mul, norm_pow]
        _ ≤ M * (j * M ^ (j - 1) * ‖z - μ‖) + ‖z - μ‖ * M ^ j := by
            gcongr
        _ = (j + 1 : ℕ) * M ^ (j + 1 - 1) * ‖z - μ‖ := by
            rcases j with _ | j
            · simp
            · simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
              rw [pow_succ M j]
              ring

/-- **The average vanishing at a root of unity is small nearby**:
`|g_p(z)| ≤ ζ p (1 + ζ)^p / 2` for `|z - μ| ≤ ζ`, `|μ| = 1`, `μ^p = 1 ≠ μ`. -/
theorem norm_geometricAverage_root_le (μ z : ℂ) (p : ℕ) {ζ : ℝ} (hζ : 0 ≤ ζ) (hμn : ‖μ‖ = 1)
    (hμ : μ ^ p = 1) (hμ1 : μ ≠ 1) (hz : ‖z - μ‖ ≤ ζ) :
    ‖FilterCoefficients.geometricAverage p z‖ ≤ ζ * p * (1 + ζ) ^ p / 2 := by
  rcases Nat.eq_zero_or_pos p with hp | hp
  · subst hp
    simp [FilterCoefficients.geometricAverage, FilterCoefficients.geometricSum]
  have hM : ‖z‖ ≤ 1 + ζ := by
    have := norm_le_norm_add_norm_sub' z μ
    linarith [norm_sub_rev z μ]
  have hμM : ‖μ‖ ≤ 1 + ζ := by linarith
  have hsum : FilterCoefficients.geometricSum p z = ∑ j ∈ Finset.range p, (z ^ j - μ ^ j) := by
    rw [Finset.sum_sub_distrib, ← FilterCoefficients.geometricSum,
      ← FilterCoefficients.geometricSum, geometricSum_eq_zero μ p hμ hμ1, sub_zero]
  have hbound : ‖FilterCoefficients.geometricSum p z‖ ≤ ζ * (1 + ζ) ^ p * (p * p / 2) := by
    rw [hsum]
    calc ‖∑ j ∈ Finset.range p, (z ^ j - μ ^ j)‖ ≤ ∑ j ∈ Finset.range p, ‖z ^ j - μ ^ j‖ :=
          norm_sum_le _ _
      _ ≤ ∑ j ∈ Finset.range p, ζ * (1 + ζ) ^ p * j := by
          apply Finset.sum_le_sum
          intro j hj
          have hj' : j - 1 ≤ p := by have := Finset.mem_range.mp hj; omega
          calc ‖z ^ j - μ ^ j‖ ≤ j * (1 + ζ) ^ (j - 1) * ‖z - μ‖ :=
                norm_pow_sub_pow_le z μ hM hμM j
            _ ≤ j * (1 + ζ) ^ p * ζ := by
                gcongr
                · linarith
            _ = ζ * (1 + ζ) ^ p * j := by ring
      _ = ζ * (1 + ζ) ^ p * ∑ j ∈ Finset.range p, (j : ℝ) := by rw [Finset.mul_sum]
      _ ≤ ζ * (1 + ζ) ^ p * (p * p / 2) := by
          gcongr
          have hnat : (∑ j ∈ Finset.range p, j) * 2 ≤ p * p := by
            rw [Finset.sum_range_id_mul_two]
            exact Nat.mul_le_mul_left p (Nat.sub_le p 1)
          have hreal := (Nat.cast_le (α := ℝ)).mpr hnat
          push_cast at hreal
          linarith
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  rw [FilterCoefficients.geometricAverage, norm_div, Complex.norm_natCast, div_le_iff₀ hp']
  calc ‖FilterCoefficients.geometricSum p z‖ ≤ ζ * (1 + ζ) ^ p * (p * p / 2) := hbound
    _ = ζ * p * (1 + ζ) ^ p / 2 * p := by ring

/-- Every average is bounded by `(1 + ζ)^B` on `|z| ≤ 1 + ζ`. -/
theorem norm_geometricAverage_le (B : ℕ) (z : ℂ) {ζ : ℝ} (hζ : 0 ≤ ζ) (hz : ‖z‖ ≤ 1 + ζ) :
    ‖FilterCoefficients.geometricAverage B z‖ ≤ (1 + ζ) ^ B := by
  rcases Nat.eq_zero_or_pos B with hB | hB
  · subst hB
    simp [FilterCoefficients.geometricAverage, FilterCoefficients.geometricSum]
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  rw [FilterCoefficients.geometricAverage, norm_div, Complex.norm_natCast, div_le_iff₀ hB',
    FilterCoefficients.geometricSum]
  calc ‖∑ j ∈ Finset.range B, z ^ j‖ ≤ ∑ j ∈ Finset.range B, ‖z ^ j‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ Finset.range B, (1 + ζ) ^ B := by
        apply Finset.sum_le_sum
        intro j hj
        rw [norm_pow]
        calc ‖z‖ ^ j ≤ (1 + ζ) ^ j := pow_le_pow_left₀ (norm_nonneg _) hz j
          _ ≤ (1 + ζ) ^ B := pow_le_pow_right₀ (by linarith)
              (Finset.mem_range.mp hj).le
    _ = (1 + ζ) ^ B * B := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm]

/-- **The product filter on an isolated circle.** -/
theorem norm_filter_root_le (μ z : ℂ) (B m p k : ℕ) {ζ : ℝ} (hζ : 0 ≤ ζ) (hμn : ‖μ‖ = 1)
    (hμ : μ ^ p = 1) (hμ1 : μ ≠ 1) (hz : ‖z - μ‖ ≤ ζ) :
    ‖FilterCoefficients.geometricAverage B z ^ m * FilterCoefficients.geometricAverage p z ^ k‖ ≤
      (1 + ζ) ^ (B * m) * (ζ * p * (1 + ζ) ^ p / 2) ^ k := by
  have hM : ‖z‖ ≤ 1 + ζ := by
    have := norm_le_norm_add_norm_sub' z μ
    linarith [norm_sub_rev z μ]
  rw [norm_mul, norm_pow, norm_pow, pow_mul]
  gcongr
  · exact norm_geometricAverage_le B z hζ hM
  · exact norm_geometricAverage_root_le μ z p hζ hμn hμ hμ1 hz

end

end LargeSparsityCore.Scalars
