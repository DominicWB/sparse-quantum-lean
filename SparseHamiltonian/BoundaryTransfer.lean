import SparseHamiltonian.ChronologicalBound

/-!
# Boundary transfer stability and chronological growth

The exact Woodbury transfer identity gives a dimension-independent norm bound
for the change in the public transfer. Combined with the weighted resolvent
endpoint estimate, the coefficient is `108/49`, and hence at most `3`.

The transfer at the base point is explicitly *assumed contractive*. Its
identification with a unitary Cayley transform is not proved in this module.
The final power estimate uses the genuine operator norm on continuous linear
maps and does not require a nontrivial public space.
-/

namespace SparseHamiltonian
namespace BoundaryTransfer

noncomputable section

section Algebra

variable {𝓐 : Type*} [Ring 𝓐] [Algebra ℂ 𝓐]

/-- Public transfer after eliminating the local private state. -/
def transfer (c : ℂ) (σ2 : ℝ) (F K : 𝓐) : 𝓐 :=
  c • (1 : 𝓐) - (σ2 : ℂ) • (F * K)

/-- Exact transfer difference; the common direct public action cancels. -/
theorem transfer_difference (c κ : ℂ) (σ2 : ℝ) (F F₀ K K₀ : 𝓐)
    (hLK : (1 + κ • F) * K = 1) (hKL : K * (1 + κ • F) = 1)
    (hL₀K₀ : (1 + κ • F₀) * K₀ = 1)
    (hK₀L₀ : K₀ * (1 + κ • F₀) = 1) :
    transfer c σ2 F K - transfer c σ2 F₀ K₀ =
      -(σ2 : ℂ) • (K * (F - F₀) * K₀) := by
  have h := woodbury_transfer_difference F F₀ K K₀ κ hLK hKL hL₀K₀ hK₀L₀
  calc
    transfer c σ2 F K - transfer c σ2 F₀ K₀ =
        -(σ2 : ℂ) • (F * K - F₀ * K₀) := by
      simp only [transfer, smul_sub, neg_smul]
      abel
    _ = -(σ2 : ℂ) • (K * (F - F₀) * K₀) := by rw [h]

end Algebra

section NormEstimates

variable {𝓐 : Type*} [NormedRing 𝓐] [NormedAlgebra ℂ 𝓐]

/-- The sharp coefficient obtained from two inverse bounds `9/7`, coupling
`σ² ≤ 2w`, and the weighted boundary difference bound `(2/3)qr`. -/
theorem transfer_difference_norm_le (c κ : ℂ) (σ2 w q r : ℝ) (F F₀ K K₀ : 𝓐)
    (hw : 0 ≤ w) (hq : 0 ≤ q) (hr : 0 ≤ r)
    (hσ : 0 ≤ σ2) (hσw : σ2 ≤ 2 * w)
    (hLK : (1 + κ • F) * K = 1) (hKL : K * (1 + κ • F) = 1)
    (hL₀K₀ : (1 + κ • F₀) * K₀ = 1)
    (hK₀L₀ : K₀ * (1 + κ • F₀) = 1)
    (hK : ‖K‖ ≤ 9 / 7) (hK₀ : ‖K₀‖ ≤ 9 / 7)
    (hF : ‖F - F₀‖ ≤ (2 / 3 : ℝ) * q * r) :
    ‖transfer c σ2 F K - transfer c σ2 F₀ K₀‖ ≤ (108 / 49 : ℝ) * w * q * r := by
  have hProduct : ‖K * (F - F₀) * K₀‖ ≤
      ((9 / 7 : ℝ) * ((2 / 3 : ℝ) * q * r)) * (9 / 7 : ℝ) := by
    calc
      ‖K * (F - F₀) * K₀‖ ≤ ‖K * (F - F₀)‖ * ‖K₀‖ := norm_mul_le _ _
      _ ≤ (‖K‖ * ‖F - F₀‖) * ‖K₀‖ :=
        mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ ((9 / 7 : ℝ) * ((2 / 3 : ℝ) * q * r)) * (9 / 7 : ℝ) :=
        mul_le_mul (mul_le_mul hK hF (norm_nonneg _) (by norm_num)) hK₀
          (norm_nonneg _) (by positivity)
  rw [transfer_difference c κ σ2 F F₀ K K₀ hLK hKL hL₀K₀ hK₀L₀,
    norm_smul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hσ]
  calc
    σ2 * ‖K * (F - F₀) * K₀‖ ≤
        (2 * w) * (((9 / 7 : ℝ) * ((2 / 3 : ℝ) * q * r)) * (9 / 7 : ℝ)) :=
      mul_le_mul hσw hProduct (norm_nonneg _) (by positivity)
    _ = (108 / 49 : ℝ) * w * q * r := by ring

/-- A convenient slightly weaker transfer bound with integer coefficient. -/
theorem transfer_difference_norm_le_three (c κ : ℂ) (σ2 w q r : ℝ) (F F₀ K K₀ : 𝓐)
    (hw : 0 ≤ w) (hq : 0 ≤ q) (hr : 0 ≤ r)
    (hσ : 0 ≤ σ2) (hσw : σ2 ≤ 2 * w)
    (hLK : (1 + κ • F) * K = 1) (hKL : K * (1 + κ • F) = 1)
    (hL₀K₀ : (1 + κ • F₀) * K₀ = 1)
    (hK₀L₀ : K₀ * (1 + κ • F₀) = 1)
    (hK : ‖K‖ ≤ 9 / 7) (hK₀ : ‖K₀‖ ≤ 9 / 7)
    (hF : ‖F - F₀‖ ≤ (2 / 3 : ℝ) * q * r) :
    ‖transfer c σ2 F K - transfer c σ2 F₀ K₀‖ ≤ 3 * w * q * r := by
  have h := transfer_difference_norm_le c κ σ2 w q r F F₀ K K₀ hw hq hr
    hσ hσw hLK hKL hL₀K₀ hK₀L₀ hK hK₀ hF
  calc
    ‖transfer c σ2 F K - transfer c σ2 F₀ K₀‖ ≤ (108 / 49 : ℝ) * (w * q * r) := by
      simpa only [mul_assoc] using h
    _ ≤ 3 * (w * q * r) := mul_le_mul_of_nonneg_right (by norm_num)
      (mul_nonneg (mul_nonneg hw hq) hr)
    _ = 3 * w * q * r := by ring

/-- Contractivity at the base point and the transfer difference control the
transfer norm in the disk. The base-point premise is not a unitarity proof. -/
theorem transfer_norm_le (c κ : ℂ) (σ2 w q r : ℝ) (F F₀ K K₀ : 𝓐)
    (hw : 0 ≤ w) (hq : 0 ≤ q) (hr : 0 ≤ r)
    (hσ : 0 ≤ σ2) (hσw : σ2 ≤ 2 * w)
    (hLK : (1 + κ • F) * K = 1) (hKL : K * (1 + κ • F) = 1)
    (hL₀K₀ : (1 + κ • F₀) * K₀ = 1)
    (hK₀L₀ : K₀ * (1 + κ • F₀) = 1)
    (hK : ‖K‖ ≤ 9 / 7) (hK₀ : ‖K₀‖ ≤ 9 / 7)
    (hF : ‖F - F₀‖ ≤ (2 / 3 : ℝ) * q * r)
    (hBase : ‖transfer c σ2 F₀ K₀‖ ≤ 1) :
    ‖transfer c σ2 F K‖ ≤ 1 + 3 * w * q * r := by
  have hDiff := transfer_difference_norm_le_three c κ σ2 w q r F F₀ K K₀
    hw hq hr hσ hσw hLK hKL hL₀K₀ hK₀L₀ hK hK₀ hF
  calc
    ‖transfer c σ2 F K‖ =
        ‖transfer c σ2 F₀ K₀ + (transfer c σ2 F K - transfer c σ2 F₀ K₀)‖ := by
      congr 1
      abel
    _ ≤ ‖transfer c σ2 F₀ K₀‖ +
        ‖transfer c σ2 F K - transfer c σ2 F₀ K₀‖ := norm_add_le _ _
    _ ≤ 1 + 3 * w * q * r := add_le_add hBase hDiff

end NormEstimates

/-- The actual operator transfer has exponential power growth, including for a
zero-dimensional public space. -/
theorem transfer_pow_norm_le_exp
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
    (c κ : ℂ) (σ2 w q r : ℝ) (F F₀ K K₀ : P →L[ℂ] P)
    (hw : 0 ≤ w) (hq : 0 ≤ q) (hr : 0 ≤ r)
    (hσ : 0 ≤ σ2) (hσw : σ2 ≤ 2 * w)
    (hLK : (1 + κ • F) * K = 1) (hKL : K * (1 + κ • F) = 1)
    (hL₀K₀ : (1 + κ • F₀) * K₀ = 1)
    (hK₀L₀ : K₀ * (1 + κ • F₀) = 1)
    (hK : ‖K‖ ≤ 9 / 7) (hK₀ : ‖K₀‖ ≤ 9 / 7)
    (hF : ‖F - F₀‖ ≤ (2 / 3 : ℝ) * q * r)
    (hBase : ‖transfer c σ2 F₀ K₀‖ ≤ 1) (n : ℕ) :
    ‖transfer c σ2 F K ^ n‖ ≤ Real.exp (3 * (n : ℝ) * w * q * r) := by
  have hNorm := transfer_norm_le c κ σ2 w q r F F₀ K K₀
    hw hq hr hσ hσw hLK hKL hL₀K₀ hK₀L₀ hK hK₀ hF hBase
  have h := ChronologicalResolvent.transfer_pow_norm_le_exp (transfer c σ2 F K) hNorm n
  convert h using 1
  congr 1
  ring

section ScalarCouplings

/-- The local rank-update coupling is nonnegative. -/
theorem cayley_kappa_nonneg (w : ℝ) (hw : 0 ≤ w) :
    0 ≤ w / (1 + w / 2) := by positivity

/-- A step of size at most one quarter has rank-update coupling at most `2/9`. -/
theorem cayley_kappa_le (w : ℝ) (hw : 0 ≤ w) (hwQuarter : w ≤ 1 / 4) :
    w / (1 + w / 2) ≤ 2 / 9 := by
  have hDen : 0 < 1 + w / 2 := by positivity
  rw [div_le_iff₀ hDen]
  linarith

/-- The squared boundary coupling is nonnegative. -/
theorem cayley_sigma_sq_nonneg (w : ℝ) (hw : 0 ≤ w) :
    0 ≤ 2 * w / (1 + w / 2) ^ 2 := by positivity

/-- The squared boundary coupling is bounded by `2w`. -/
theorem cayley_sigma_sq_le (w : ℝ) (hw : 0 ≤ w) :
    2 * w / (1 + w / 2) ^ 2 ≤ 2 * w := by
  have hDen : 0 < (1 + w / 2) ^ 2 := by positivity
  have hOne : 1 ≤ (1 + w / 2) ^ 2 := by nlinarith [sq_nonneg w]
  rw [div_le_iff₀ hDen]
  exact le_mul_of_one_le_right (by positivity) hOne

end ScalarCouplings

end

end BoundaryTransfer
end SparseHamiltonian
