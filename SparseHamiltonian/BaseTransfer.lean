import SparseHamiltonian.BoundaryTransfer

/-!
# Contractivity of the base-point boundary transfer

The condition `F + star F = -1`, together with the scalar coupling identities,
implies that the base transfer is an isometry. This discharges the explicit
base-contractivity premise in `BoundaryTransfer.lean` without separately
identifying the transfer with a Cayley transform. The proof uses only a right
inverse of `1 + κ F`; a two-sided inverse certainly suffices.
-/

namespace SparseHamiltonian
namespace BaseTransfer

noncomputable section

section Algebra

variable {𝓐 : Type*} [Ring 𝓐] [Algebra ℂ 𝓐]

/-- Numerator in the fraction form of the base transfer. -/
def numerator (c κ : ℝ) (F : 𝓐) : 𝓐 :=
  (c : ℂ) • (1 : 𝓐) - (κ : ℂ) • F

/-- Denominator in the fraction form of the base transfer. -/
def denominator (κ : ℝ) (F : 𝓐) : 𝓐 :=
  1 + (κ : ℂ) • F

/-- The eliminated transfer equals numerator times denominator inverse. -/
theorem transfer_eq_numerator_mul (c κ σ2 : ℝ) (F K : 𝓐)
    (hκ : κ = 1 - c) (hσ : σ2 = 1 - c ^ 2)
    (hLK : denominator κ F * K = 1) :
    BoundaryTransfer.transfer (c : ℂ) σ2 F K = numerator c κ F * K := by
  calc
    BoundaryTransfer.transfer (c : ℂ) σ2 F K =
        (c : ℂ) • (denominator κ F * K) - (σ2 : ℂ) • (F * K) := by
      rw [hLK]
      rfl
    _ = numerator c κ F * K := by
      simp only [denominator, numerator, add_mul, sub_mul, one_mul, smul_mul_assoc,
        smul_add, smul_smul]
      rw [hκ, hσ]
      push_cast
      module

end Algebra

section StarAlgebra

variable {𝓐 : Type*} [Ring 𝓐] [StarRing 𝓐] [Algebra ℂ 𝓐] [StarModule ℂ 𝓐]

/-- The numerator and denominator have identical squared moduli at the base
point. No norm or inverse is required for this identity. -/
theorem numerator_gram_eq_denominator_gram (c κ : ℝ) (F : 𝓐)
    (hκ : κ = 1 - c) (hF : F + star F = -1) :
    star (numerator c κ F) * numerator c κ F =
      star (denominator κ F) * denominator κ F := by
  have hStarF : star F = -1 - F := eq_sub_of_add_eq' hF
  simp only [numerator, denominator, star_sub, star_add, star_smul, star_one,
    Complex.star_def, Complex.conj_ofReal, hStarF,
    mul_sub, sub_mul, mul_add, add_mul, smul_mul_assoc, mul_smul_comm,
    mul_one, one_mul, neg_mul, smul_sub, smul_add, smul_neg, smul_smul]
  rw [hκ]
  push_cast
  module

/-- The base transfer is an isometry under the exact boundary relation. -/
theorem transfer_star_mul_self (c κ σ2 : ℝ) (F K : 𝓐)
    (hκ : κ = 1 - c) (hσ : σ2 = 1 - c ^ 2)
    (hF : F + star F = -1) (hLK : denominator κ F * K = 1) :
    star (BoundaryTransfer.transfer (c : ℂ) σ2 F K) *
      BoundaryTransfer.transfer (c : ℂ) σ2 F K = 1 := by
  have hTransfer := transfer_eq_numerator_mul c κ σ2 F K hκ hσ hLK
  calc
    star (BoundaryTransfer.transfer (c : ℂ) σ2 F K) *
        BoundaryTransfer.transfer (c : ℂ) σ2 F K =
        star K * (star (numerator c κ F) * numerator c κ F) * K := by
      rw [hTransfer, star_mul]
      simp only [mul_assoc]
    _ = star K * (star (denominator κ F) * denominator κ F) * K := by
      rw [numerator_gram_eq_denominator_gram c κ F hκ hF]
    _ = star (denominator κ F * K) * (denominator κ F * K) := by
      simp only [star_mul, mul_assoc]
    _ = 1 := by rw [hLK, star_one, one_mul]

/-- The base boundary value associated with a self-adjoint compressed generator. -/
def halfGenerator (H : 𝓐) : 𝓐 :=
  (2 : ℂ)⁻¹ • (-(1 : 𝓐) + Complex.I • H)

/-- A self-adjoint generator has the exact negative-identity star sum. -/
theorem halfGenerator_star_sum (H : 𝓐) (hH : star H = H) :
    halfGenerator H + star (halfGenerator H) = -1 := by
  have hHalf : star ((2 : ℂ)⁻¹) = (2 : ℂ)⁻¹ := by norm_num
  have hI : star Complex.I = -Complex.I := by simp
  simp only [halfGenerator, star_smul, star_add, star_neg, star_one, star_mul, hHalf, hI, hH,
    smul_add, smul_neg, smul_smul]
  module

end StarAlgebra

/-- Base-point contractivity in the genuine Hilbert-space operator norm,
including the zero-dimensional space. -/
theorem transfer_norm_le_one
    {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
    (c κ σ2 : ℝ) (F K : P →L[ℂ] P)
    (hκ : κ = 1 - c) (hσ : σ2 = 1 - c ^ 2)
    (hF : F + star F = -1) (hLK : denominator κ F * K = 1) :
    ‖BoundaryTransfer.transfer (c : ℂ) σ2 F K‖ ≤ 1 := by
  have hIso := transfer_star_mul_self c κ σ2 F K hκ hσ hF hLK
  have hNorm := CStarRing.norm_mul_self_le (BoundaryTransfer.transfer (c : ℂ) σ2 F K)
  rw [hIso] at hNorm
  have hOne : ‖(1 : P →L[ℂ] P)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  nlinarith [norm_nonneg (BoundaryTransfer.transfer (c : ℂ) σ2 F K)]

section ScalarCouplings

/-- The explicit Cayley rotation satisfies `κ = 1-c`. -/
theorem cayley_kappa_relation (w : ℝ) (hw : 0 ≤ w) :
    w / (1 + w / 2) = 1 - (1 - w / 2) / (1 + w / 2) := by
  have hDen : 1 + w / 2 ≠ 0 := ne_of_gt (by positivity : 0 < 1 + w / 2)
  field_simp
  ring

/-- The explicit squared coupling satisfies `σ² = 1-c²`. -/
theorem cayley_sigma_relation (w : ℝ) (hw : 0 ≤ w) :
    2 * w / (1 + w / 2) ^ 2 = 1 - ((1 - w / 2) / (1 + w / 2)) ^ 2 := by
  have hDen : 1 + w / 2 ≠ 0 := ne_of_gt (by positivity : 0 < 1 + w / 2)
  field_simp
  ring

end ScalarCouplings

end

end BaseTransfer
end SparseHamiltonian
