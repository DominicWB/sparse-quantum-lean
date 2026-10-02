import SparseHamiltonian.CatalystConstruction

/-!
# Explicit Cayley couplings and public action

The scalar rotation parameters satisfy the promises used by the global
resolvent theorem.  Rescaling the existing feedback inverse gives a genuine
two-sided inverse of the Cayley denominator; the transfer is exactly the
usual Cayley rational function of the public Hamiltonian.
-/

namespace SparseHamiltonian.CayleyTransfer

noncomputable section

def c (w : ℝ) : ℝ := (1 - w / 2) / (1 + w / 2)

def kappa (w : ℝ) : ℝ := w / (1 + w / 2)

def sigma (w : ℝ) : ℝ := Real.sqrt (2 * w) / (1 + w / 2)

theorem sigma_sq (w : ℝ) (hw : 0 ≤ w) :
    sigma w ^ 2 = 2 * w / (1 + w / 2) ^ 2 := by
  rw [sigma, div_pow, Real.sq_sqrt (by positivity)]

theorem sigma_nonneg (w : ℝ) (hw : 0 ≤ w) : 0 ≤ sigma w := by
  unfold sigma
  positivity

/-- All scalar promises of the local and global resolvent constructions follow
from the allowed Cayley step size. -/
theorem scalar_promises (w : ℝ) (hw : 0 ≤ w) (hwQuarter : w ≤ 1 / 4) :
    0 ≤ kappa w ∧ kappa w ≤ 2 / 9 ∧ kappa w = 1 - c w ∧
    sigma w ^ 2 = 1 - c w ^ 2 ∧ sigma w ^ 2 ≤ 2 * w := by
  exact ⟨BoundaryTransfer.cayley_kappa_nonneg w hw,
    BoundaryTransfer.cayley_kappa_le w hw hwQuarter,
    BaseTransfer.cayley_kappa_relation w hw,
    (sigma_sq w hw).trans (BaseTransfer.cayley_sigma_relation w hw),
    (sigma_sq w hw).le.trans (BoundaryTransfer.cayley_sigma_sq_le w hw)⟩

section Algebra

variable {𝓐 : Type*} [Ring 𝓐] [Algebra ℂ 𝓐]

def cayleyDenominator (w : ℝ) (H : 𝓐) : 𝓐 :=
  1 + (Complex.I * (w : ℂ) / 2) • H

def cayleyNumerator (w : ℝ) (H : 𝓐) : 𝓐 :=
  1 - (Complex.I * (w : ℂ) / 2) • H

def cayleyInverse (w : ℝ) (K : 𝓐) : 𝓐 :=
  (1 + (w : ℂ) / 2)⁻¹ • K

theorem complex_denominator_ne_zero (w : ℝ) (hw : 0 ≤ w) :
    (1 + (w : ℂ) / 2) ≠ 0 := by
  have h : (1 + w / 2 : ℝ) ≠ 0 := ne_of_gt (by positivity)
  exact_mod_cast h

theorem denominator_scaling (w : ℝ) (hw : 0 ≤ w) (H : 𝓐) :
    (1 + (w : ℂ) / 2) •
      BaseTransfer.denominator (kappa w) (BaseTransfer.halfGenerator H) =
    cayleyDenominator w H := by
  have hden := complex_denominator_ne_zero w hw
  have hden2 : (2 + (w : ℂ)) ≠ 0 := by
    exact_mod_cast (ne_of_gt (by linarith : (0 : ℝ) < 2 + w))
  simp only [BaseTransfer.denominator, BaseTransfer.halfGenerator,
    cayleyDenominator, kappa, smul_add, smul_neg, smul_smul]
  push_cast
  match_scalars <;> field_simp [hden, hden2]
  all_goals ring

theorem numerator_scaling (w : ℝ) (hw : 0 ≤ w) (H : 𝓐) :
    (1 + (w : ℂ) / 2) •
      BaseTransfer.numerator (c w) (kappa w) (BaseTransfer.halfGenerator H) =
    cayleyNumerator w H := by
  have hden := complex_denominator_ne_zero w hw
  have hden2 : (2 + (w : ℂ)) ≠ 0 := by
    exact_mod_cast (ne_of_gt (by linarith : (0 : ℝ) < 2 + w))
  simp only [BaseTransfer.numerator, BaseTransfer.halfGenerator,
    cayleyNumerator, c, kappa, smul_sub, smul_add, smul_neg, smul_smul]
  push_cast
  match_scalars <;> field_simp [hden, hden2]
  all_goals ring

/-- A feedback right inverse supplies an actual Cayley right inverse. -/
theorem cayley_right_inverse (w : ℝ) (hw : 0 ≤ w) (H K : 𝓐)
    (hLK : BaseTransfer.denominator (kappa w) (BaseTransfer.halfGenerator H) * K = 1) :
    cayleyDenominator w H * cayleyInverse w K = 1 := by
  rw [← denominator_scaling w hw H, cayleyInverse,
    smul_mul_assoc, mul_smul_comm, smul_smul,
    mul_inv_cancel₀ (complex_denominator_ne_zero w hw), one_smul, hLK]

/-- A feedback left inverse supplies an actual Cayley left inverse. -/
theorem cayley_left_inverse (w : ℝ) (hw : 0 ≤ w) (H K : 𝓐)
    (hKL : K * BaseTransfer.denominator (kappa w) (BaseTransfer.halfGenerator H) = 1) :
    cayleyInverse w K * cayleyDenominator w H = 1 := by
  rw [← denominator_scaling w hw H, cayleyInverse,
    smul_mul_assoc, mul_smul_comm, smul_smul,
    inv_mul_cancel₀ (complex_denominator_ne_zero w hw), one_smul, hKL]

/-- The public transfer is exactly the Cayley transform of the compressed
Hamiltonian, with an inverse explicitly obtained from the feedback inverse. -/
theorem transfer_eq_cayley (w : ℝ) (hw : 0 ≤ w) (H K : 𝓐)
    (hLK : BaseTransfer.denominator (kappa w) (BaseTransfer.halfGenerator H) * K = 1) :
    BoundaryTransfer.transfer (c w : ℂ) (sigma w ^ 2) (BaseTransfer.halfGenerator H) K =
      cayleyNumerator w H * cayleyInverse w K := by
  rw [BaseTransfer.transfer_eq_numerator_mul (c w) (kappa w) (sigma w ^ 2)
    (BaseTransfer.halfGenerator H) K (BaseTransfer.cayley_kappa_relation w hw)
    ((sigma_sq w hw).trans (BaseTransfer.cayley_sigma_relation w hw)) hLK]
  rw [← numerator_scaling w hw H, cayleyInverse,
    smul_mul_assoc, mul_smul_comm, smul_smul,
    mul_inv_cancel₀ (complex_denominator_ne_zero w hw), one_smul]

end Algebra

section StarAlgebra

variable {𝓐 : Type*} [Ring 𝓐] [StarRing 𝓐] [Algebra ℂ 𝓐] [StarModule ℂ 𝓐]

/-- The Cayley numerator and denominator have equal Gram operators for a
skew-adjoint argument. -/
theorem skew_cayley_gram (X : 𝓐) (hX : star X = -X) :
    star (1 + (1 / 2 : ℂ) • X) * (1 + (1 / 2 : ℂ) • X) =
      star (1 - (1 / 2 : ℂ) • X) * (1 - (1 / 2 : ℂ) • X) := by
  have hh : star (1 / 2 : ℂ) = (1 / 2 : ℂ) := by norm_num
  simp only [star_add, star_sub, star_one, star_smul, hh, hX, smul_neg,
    ← sub_eq_add_neg, sub_neg_eq_add]
  noncomm_ring
  module

/-- A right inverse alone suffices to prove the Cayley action is an isometry. -/
theorem skew_cayley_star_mul_self (X R : 𝓐) (hX : star X = -X)
    (hR : (1 - (1 / 2 : ℂ) • X) * R = 1) :
    star ((1 + (1 / 2 : ℂ) • X) * R) *
      ((1 + (1 / 2 : ℂ) • X) * R) = 1 := by
  calc
    star ((1 + (1 / 2 : ℂ) • X) * R) * ((1 + (1 / 2 : ℂ) • X) * R) =
        star R * (star (1 + (1 / 2 : ℂ) • X) * (1 + (1 / 2 : ℂ) • X)) * R := by
      simp only [star_mul, mul_assoc]
    _ = star R * (star (1 - (1 / 2 : ℂ) • X) * (1 - (1 / 2 : ℂ) • X)) * R := by
      rw [skew_cayley_gram X hX]
    _ = star ((1 - (1 / 2 : ℂ) • X) * R) * ((1 - (1 / 2 : ℂ) • X) * R) := by
      simp only [star_mul, mul_assoc]
    _ = 1 := by rw [hR, star_one, one_mul]

end StarAlgebra

/-- Contractivity of the skew-adjoint Cayley action in the genuine Hilbert
operator norm, including zero-dimensional spaces. -/
theorem skew_cayley_norm_le_one
    {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
    (X R : P →L[ℂ] P) (hX : star X = -X)
    (hR : (1 - (1 / 2 : ℂ) • X) * R = 1) :
    ‖(1 + (1 / 2 : ℂ) • X) * R‖ ≤ 1 := by
  have hIso := skew_cayley_star_mul_self X R hX hR
  have hNorm := CStarRing.norm_mul_self_le ((1 + (1 / 2 : ℂ) • X) * R)
  rw [hIso] at hNorm
  have hOne : ‖(1 : P →L[ℂ] P)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  nlinarith [norm_nonneg ((1 + (1 / 2 : ℂ) • X) * R)]

end
end SparseHamiltonian.CayleyTransfer
