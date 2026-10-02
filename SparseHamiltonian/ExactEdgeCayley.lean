import SparseHamiltonian.ImprovedCayleyMoments

/-!
# Explicit edge Cayley gates

The entrywise generator has the two-dimensional block
`K(z) = [[0,z],[conj z,0]]`.  Its denominator inverse is an explicit
rational polynomial, so none of the Cayley identities below assumes
inverse existence.  The zero-entry action is exactly `-1`, including on
padded locator positions.  This module proves the actual gate's unitary
semantics; native oracle query accounting is supplied separately.
-/

namespace SparseHamiltonian.ExactEdgeCayley

noncomputable section

open ContinuousLinearMap OracleCircuit
open scoped ComplexConjugate InnerProduct

section Algebra

variable {A : Type*} [Ring A] [Algebra ℂ A]

/-- The explicit inverse associated with a scalar-square generator. -/
def denominatorInverse (K : A) (ρ : ℝ) : A :=
  ((ρ + 1 : ℝ) : ℂ)⁻¹ • (K + Complex.I • (1 : A))

theorem denominator_scalar_ne_zero (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ((ρ + 1 : ℝ) : ℂ) ≠ 0 := by
  exact_mod_cast (show ρ + 1 ≠ 0 by linarith)

/-- Multiplying the two denominator factors gives a positive real scalar. -/
theorem minus_mul_plus (K : A) (ρ : ℝ)
    (hSquare : K * K = (ρ : ℂ) • (1 : A)) :
    (K - Complex.I • (1 : A)) * (K + Complex.I • (1 : A)) =
      ((ρ + 1 : ℝ) : ℂ) • (1 : A) := by
  simp only [sub_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    one_mul, mul_one, hSquare, Complex.ofReal_add,
    Complex.ofReal_one]
  match_scalars
  all_goals ring_nf
  simp only [Complex.I_sq]
  ring

/-- The same scalar product holds with the order of factors reversed. -/
theorem plus_mul_minus (K : A) (ρ : ℝ)
    (hSquare : K * K = (ρ : ℂ) • (1 : A)) :
    (K + Complex.I • (1 : A)) * (K - Complex.I • (1 : A)) =
      ((ρ + 1 : ℝ) : ℂ) • (1 : A) := by
  simp only [add_mul, mul_sub, smul_mul_assoc, mul_smul_comm,
    one_mul, mul_one, hSquare, Complex.ofReal_add,
    Complex.ofReal_one]
  match_scalars
  all_goals ring_nf
  simp only [Complex.I_sq]
  ring

/-- The rational expression is a right inverse, with no existence assumption. -/
theorem denominatorInverse_right (K : A) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hSquare : K * K = (ρ : ℂ) • (1 : A)) :
    (K - Complex.I • (1 : A)) * denominatorInverse K ρ = 1 := by
  rw [denominatorInverse, mul_smul_comm, minus_mul_plus K ρ hSquare,
    smul_smul, inv_mul_cancel₀ (denominator_scalar_ne_zero ρ hρ), one_smul]

/-- It is also a left inverse. -/
theorem denominatorInverse_left (K : A) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hSquare : K * K = (ρ : ℂ) • (1 : A)) :
    denominatorInverse K ρ * (K - Complex.I • (1 : A)) = 1 := by
  rw [denominatorInverse, smul_mul_assoc, plus_mul_minus K ρ hSquare,
    smul_smul, inv_mul_cancel₀ (denominator_scalar_ne_zero ρ hρ), one_smul]

/-- The explicit denominator inverse commutes with the numerator. -/
theorem denominatorInverse_commutes (K : A) (ρ : ℝ) :
    denominatorInverse K ρ * (K + Complex.I • (1 : A)) =
      (K + Complex.I • (1 : A)) * denominatorInverse K ρ := by
  simp only [denominatorInverse, smul_mul_assoc, mul_smul_comm]

/-- The exact Cayley action has a quadratic rational numerator. -/
theorem action_formula (K : A) (ρ : ℝ)
    (hSquare : K * K = (ρ : ℂ) • (1 : A)) :
    ImprovedCayleyMoments.cayleyAction K (denominatorInverse K ρ) =
      ((ρ + 1 : ℝ) : ℂ)⁻¹ •
        (((ρ - 1 : ℝ) : ℂ) • (1 : A) + (2 * Complex.I : ℂ) • K) := by
  rw [ImprovedCayleyMoments.cayleyAction, denominatorInverse, mul_smul_comm]
  congr 1
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    one_mul, mul_one, hSquare, Complex.ofReal_sub,
    Complex.ofReal_one]
  match_scalars
  all_goals ring_nf
  simp only [Complex.I_sq]
  ring

end Algebra

section StarAlgebra

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]

/-- The explicit action satisfies both unitary equations in any star algebra. -/
theorem explicit_action_unitary (K : A) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hSelf : star K = K) (hSquare : K * K = (ρ : ℂ) • (1 : A)) :
    star (ImprovedCayleyMoments.cayleyAction K (denominatorInverse K ρ)) *
      ImprovedCayleyMoments.cayleyAction K (denominatorInverse K ρ) = 1 ∧
    ImprovedCayleyMoments.cayleyAction K (denominatorInverse K ρ) *
      star (ImprovedCayleyMoments.cayleyAction K (denominatorInverse K ρ)) = 1 := by
  have hRight := denominatorInverse_right K ρ hρ hSquare
  have hLeft := denominatorInverse_left K ρ hρ hSquare
  refine ⟨ImprovedCayleyMoments.cayleyAction_star_mul_self K
    (denominatorInverse K ρ) hSelf hRight, ?_⟩
  have hNum : star (K + Complex.I • (1 : A)) = K - Complex.I • (1 : A) := by
    simp [hSelf, sub_eq_add_neg]
  have hDen : star (K - Complex.I • (1 : A)) = K + Complex.I • (1 : A) := by
    simp [hSelf]
  have hAdj : (K + Complex.I • (1 : A)) * star (denominatorInverse K ρ) = 1 := by
    simpa only [star_mul, hDen, star_one] using congrArg star hLeft
  calc
    ImprovedCayleyMoments.cayleyAction K (denominatorInverse K ρ) *
        star (ImprovedCayleyMoments.cayleyAction K (denominatorInverse K ρ)) =
        (denominatorInverse K ρ * (K + Complex.I • (1 : A))) *
          (star (denominatorInverse K ρ) * (K - Complex.I • (1 : A))) := by
      simp only [ImprovedCayleyMoments.cayleyAction, star_mul, hNum,
        denominatorInverse_commutes]
    _ = denominatorInverse K ρ *
        ((K + Complex.I • (1 : A)) * star (denominatorInverse K ρ)) *
          (K - Complex.I • (1 : A)) := by simp only [mul_assoc]
    _ = 1 := by rw [hAdj, mul_one, hLeft]

end StarAlgebra

/-- The edge orientation is a genuine two-dimensional Hilbert register. -/
abbrev Qubit := ComplexAmplitudeRotation.Qubit

/-- The self-adjoint oriented edge generator. -/
def generator (z : ℂ) : Qubit →L[ℂ] Qubit :=
  ComplexAmplitudeRotation.matrix 0 z (conj z) 0

@[simp] theorem generator_false (z : ℂ) (x : Qubit) :
    generator z x false = z * x true := by simp [generator]

@[simp] theorem generator_true (z : ℂ) (x : Qubit) :
    generator z x true = conj z * x false := by simp [generator]

/-- The generator really is self-adjoint, including its complex edge phase. -/
theorem generator_self_adjoint (z : ℂ) : star (generator z) = generator z := by
  change (generator z)† = generator z
  simp [generator, ComplexAmplitudeRotation.matrix_adjoint]

/-- Every edge square is exactly its entry's squared magnitude times identity. -/
theorem generator_square (z : ℂ) :
    generator z * generator z = ((‖z‖ ^ 2 : ℝ) : ℂ) •
      (1 : Qubit →L[ℂ] Qubit) := by
  have hz : z * conj z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hz' : conj z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by rw [mul_comm, hz]
  ext x b
  cases b
  · simp only [mul_apply_eq_comp, generator_false, generator_true,
      smul_apply, PiLp.smul_apply, one_def, id_apply, smul_eq_mul]
    rw [← mul_assoc, hz]
  · simp only [mul_apply_eq_comp, generator_false, generator_true,
      smul_apply, PiLp.smul_apply, one_def, id_apply, smul_eq_mul]
    rw [← mul_assoc, hz']

/-- The complex-scalar version interfaces with the generic Cayley identities. -/
theorem generator_square_complex (z : ℂ) :
    generator z * generator z = ((‖z‖ ^ 2 : ℝ) : ℂ) •
      (1 : Qubit →L[ℂ] Qubit) := generator_square z

/-- The full edge-generator norm is exactly the magnitude of its entry. -/
theorem generator_norm (z : ℂ) : ‖generator z‖ = ‖z‖ := by
  have hGram : (generator z)† ∘L generator z =
      ((‖z‖ ^ 2 : ℝ) : ℂ) • (1 : Qubit →L[ℂ] Qubit) := by
    change star (generator z) * generator z = _
    rw [generator_self_adjoint, generator_square]
  have hNorm := congrArg norm hGram
  rw [norm_adjoint_comp_self, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg _), norm_one, mul_one] at hNorm
  nlinarith [norm_nonneg (generator z), norm_nonneg z]

@[simp] theorem generator_zero : generator 0 = 0 := by
  ext x b
  cases b <;> simp [generator]

/-- An explicit inverse for every complex edge value, with no norm restriction. -/
def inverse (z : ℂ) : Qubit →L[ℂ] Qubit :=
  denominatorInverse (generator z) (‖z‖ ^ 2)

theorem inverse_right (z : ℂ) :
    (generator z - Complex.I • (1 : Qubit →L[ℂ] Qubit)) * inverse z = 1 :=
  denominatorInverse_right _ _ (sq_nonneg _) (generator_square_complex z)

theorem inverse_left (z : ℂ) :
    inverse z * (generator z - Complex.I • (1 : Qubit →L[ℂ] Qubit)) = 1 :=
  denominatorInverse_left _ _ (sq_nonneg _) (generator_square_complex z)

/-- The actual exact edge gate used by the improved simulation. -/
def action (z : ℂ) : Qubit →L[ℂ] Qubit :=
  ImprovedCayleyMoments.cayleyAction (generator z) (inverse z)

/-- Unitarity is unconditional in the decoded complex entry. -/
theorem action_unitary (z : ℂ) : IsUnitary (action z) :=
  explicit_action_unitary _ _ (sq_nonneg _) (generator_self_adjoint z)
    (generator_square_complex z)

/-- Rational gate coefficients: no numerical approximation or square root is used. -/
theorem action_eq_rational (z : ℂ) :
    action z = ((‖z‖ ^ 2 + 1 : ℝ) : ℂ)⁻¹ •
      (((‖z‖ ^ 2 - 1 : ℝ) : ℂ) • (1 : Qubit →L[ℂ] Qubit) +
        (2 * Complex.I : ℂ) • generator z) :=
  action_formula _ _ (generator_square_complex z)

/-- Padded zero entries receive exactly the phase `-1`. -/
@[simp] theorem action_zero : action 0 = -(1 : Qubit →L[ℂ] Qubit) := by
  rw [action_eq_rational, generator_zero]
  simp only [norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_add, zero_sub,
    Complex.ofReal_neg, Complex.ofReal_one, inv_one, one_smul]
  ext x b
  change (-1 : ℂ) * x b + (2 * Complex.I : ℂ) * 0 = -(x b)
  ring

/-- The resolvent at one is exact for this explicitly constructed edge action. -/
theorem one_sub_action_mul_resolvent (z : ℂ) :
    (1 - action z) * ImprovedCayleyMoments.resolventAtOne (generator z) = 1 :=
  ImprovedCayleyMoments.one_sub_cayleyAction_mul_resolventAtOne
    (generator z) (inverse z) (inverse_right z) (inverse_left z)

/-- The reverse resolvent identity is retained, so no finite-dimensional
one-sided inverse inference is hidden in the gate construction. -/
theorem resolvent_mul_one_sub_action (z : ℂ) :
    ImprovedCayleyMoments.resolventAtOne (generator z) * (1 - action z) = 1 :=
  ImprovedCayleyMoments.resolventAtOne_mul_one_sub_cayleyAction
    (generator z) (inverse z) (inverse_right z)

/-- The edge resolvent has only linear growth in the rescaled entry. -/
theorem resolvent_norm_le (z : ℂ) :
    ‖ImprovedCayleyMoments.resolventAtOne (generator z)‖ ≤ (1 + ‖z‖) / 2 := by
  simpa only [generator_norm] using
    ImprovedCayleyMoments.resolventAtOne_norm_le (generator z)

end
end SparseHamiltonian.ExactEdgeCayley
