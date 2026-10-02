import SparseHamiltonian.TransducerAlgebra

/-!
# Algebraic error cancellation in one round of oblivious amplification

This module proves the exact noncommutative residual identity used in the
Hamiltonian-simulation note, together with its norm estimate. It does not
construct the amplification circuit: identifying the residual with the squared
full-output isometry error is a separate circuit-level obligation.

The doubled polynomial avoids imposing an unnecessary division operation on
the abstract star ring.
-/

namespace SparseHamiltonian

section Algebra

variable {R : Type*} [Ring R] [StarRing R]

/-- Twice the amplified successful block, after factoring out the target unitary. -/
def amplificationPolynomialTwice (E : R) : R :=
  (1 + E) + (1 + E) + (1 + E) -
    (1 + E) * star (1 + E) * (1 + E)

/-- Twice the Hermitian residual controlling the full-output squared error. -/
def amplificationResidualTwice (E : R) : R :=
  (1 + 1 + 1 + 1) - amplificationPolynomialTwice E -
    star (amplificationPolynomialTwice E)

/-- All terms of degree zero and one cancel exactly, without commutativity. -/
theorem amplification_residual_identity (E : R) :
    amplificationResidualTwice E =
      E * E + star E * star E +
      E * star E + E * star E +
      star E * E + star E * E +
      E * star E * E + star E * E * star E := by
  simp only [amplificationResidualTwice, amplificationPolynomialTwice,
    star_add, star_sub, star_mul, star_one, star_star]
  noncomm_ring

end Algebra

section Norm

variable {R : Type*} [NormedRing R]

/-- A product of two errors of norm at most δ has norm at most δ². -/
theorem norm_error_product_le {X Y : R} {δ : ℝ}
    (hδ : 0 ≤ δ) (hX : ‖X‖ ≤ δ) (hY : ‖Y‖ ≤ δ) :
    ‖X * Y‖ ≤ δ ^ 2 := by
  calc
    ‖X * Y‖ ≤ ‖X‖ * ‖Y‖ := norm_mul_le X Y
    _ ≤ δ * δ := mul_le_mul hX hY (norm_nonneg Y) hδ
    _ = δ ^ 2 := by ring

/-- The analogous cubic estimate, including the displayed multiplication order. -/
theorem norm_error_triple_le {X Y Z : R} {δ : ℝ}
    (hδ : 0 ≤ δ) (hX : ‖X‖ ≤ δ) (hY : ‖Y‖ ≤ δ) (hZ : ‖Z‖ ≤ δ) :
    ‖X * Y * Z‖ ≤ δ ^ 3 := by
  calc
    ‖X * Y * Z‖ ≤ ‖X * Y‖ * ‖Z‖ := norm_mul_le _ _
    _ ≤ δ ^ 2 * δ :=
      mul_le_mul (norm_error_product_le hδ hX hY) hZ (norm_nonneg Z) (sq_nonneg δ)
    _ = δ ^ 3 := by ring

variable [StarRing R] [NormedStarGroup R]

/-- Quantitative form of the quadratic error cancellation. -/
theorem amplification_residual_norm_le {E : R} {δ : ℝ}
    (hδ : 0 ≤ δ) (hE : ‖E‖ ≤ δ) :
    ‖amplificationResidualTwice E‖ ≤ 6 * δ ^ 2 + 2 * δ ^ 3 := by
  have hS : ‖star E‖ ≤ δ := by simpa only [norm_star] using hE
  have hEE := norm_error_product_le hδ hE hE
  have hSS := norm_error_product_le hδ hS hS
  have hES := norm_error_product_le hδ hE hS
  have hSE := norm_error_product_le hδ hS hE
  have hESE := norm_error_triple_le hδ hE hS hE
  have hSES := norm_error_triple_le hδ hS hE hS
  have h12 := (norm_add_le (E * E) (star E * star E)).trans (add_le_add hEE hSS)
  have h123 := (norm_add_le _ (E * star E)).trans (add_le_add h12 hES)
  have h1234 := (norm_add_le _ (E * star E)).trans (add_le_add h123 hES)
  have h12345 := (norm_add_le _ (star E * E)).trans (add_le_add h1234 hSE)
  have h123456 := (norm_add_le _ (star E * E)).trans (add_le_add h12345 hSE)
  have h1234567 := (norm_add_le _ (E * star E * E)).trans (add_le_add h123456 hESE)
  have hall := (norm_add_le _ (star E * E * star E)).trans (add_le_add h1234567 hSES)
  rw [amplification_residual_identity]
  calc
    _ ≤ δ ^ 2 + δ ^ 2 + δ ^ 2 + δ ^ 2 + δ ^ 2 + δ ^ 2 + δ ^ 3 + δ ^ 3 := hall
    _ = 6 * δ ^ 2 + 2 * δ ^ 3 := by ring

end Norm

/-- The real final-error estimate after the squared norm identity is supplied. -/
theorem amplification_error_le {δ error : ℝ}
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hbound : error ^ 2 ≤ 3 * δ ^ 2 + δ ^ 3) :
    error ≤ 2 * δ := by
  have hcubic : δ ^ 3 ≤ δ ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg δ) (sub_nonneg.mpr hδ1)]
  nlinarith [sq_nonneg (error - 2 * δ)]

end SparseHamiltonian
