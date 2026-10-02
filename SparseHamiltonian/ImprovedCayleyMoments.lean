import SparseHamiltonian.ImprovedPrecisionBudget

/-!
# Exact Cayley resolvents and boundary second moments

This module is intended to be appended to `SparseHamiltonian.lean`.

For a self-adjoint operator `K`, the Cayley action
`D = (K + i) (K - i)⁻¹` has resolvent at one
`R = (1 + i K) / 2`.  Its compression depends on `J† K J`, whereas
the squared norm of its boundary response depends on `(K J)† (K J)`.
Keeping these quantities separate is the analytic ingredient needed by the
rescaled Cayley construction in the improved simulation algorithm.

The inverse of `K - i` is an explicit hypothesis in the conditional Cayley
identities below.  This module does not construct that inverse, implement a
sparse-oracle circuit, or prove the final improved simulation complexity.
-/

namespace SparseHamiltonian.ImprovedCayleyMoments

noncomputable section

section Algebra

variable {A : Type*} [Ring A] [Algebra ℂ A]

/-- The exact resolvent-at-one expression for the Cayley convention used here. -/
def resolventAtOne (K : A) : A :=
  (2 : ℂ)⁻¹ • (1 + Complex.I • K)

/-- The Cayley action, with the denominator inverse supplied separately. -/
def cayleyAction (K S : A) : A :=
  (K + Complex.I • (1 : A)) * S

/-- The affine resolvent is also a scalar multiple of the Cayley denominator. -/
theorem resolventAtOne_factor (K : A) :
    resolventAtOne K =
      ((2 : ℂ)⁻¹ * Complex.I) • (K - Complex.I • (1 : A)) := by
  have hCore : 1 + Complex.I • K =
      Complex.I • (K - Complex.I • (1 : A)) := by
    simp [smul_sub, smul_smul, add_comm]
  rw [resolventAtOne, hCore, smul_smul]

/-- A right denominator inverse gives a simple formula for `1-D`. -/
theorem one_sub_cayleyAction (K S : A)
    (hRight : (K - Complex.I • (1 : A)) * S = 1) :
    1 - cayleyAction K S = (-2 * Complex.I : ℂ) • S := by
  calc
    1 - cayleyAction K S =
        (K - Complex.I • (1 : A)) * S -
          (K + Complex.I • (1 : A)) * S := by
      rw [hRight, cayleyAction]
    _ = _ := by
      simp only [sub_mul, add_mul, smul_mul_assoc, one_mul]
      module

/-- Conditional right inverse identity at one.  Inverse existence is not assumed
implicitly: both denominator equations are displayed as hypotheses. -/
theorem one_sub_cayleyAction_mul_resolventAtOne (K S : A)
    (hRight : (K - Complex.I • (1 : A)) * S = 1)
    (hLeft : S * (K - Complex.I • (1 : A)) = 1) :
    (1 - cayleyAction K S) * resolventAtOne K = 1 := by
  have hScalar : (-2 * Complex.I : ℂ) * ((2 : ℂ)⁻¹ * Complex.I) = 1 := by
    calc
      _ = -(Complex.I * Complex.I) := by ring
      _ = 1 := by simp
  have hScalarRev : ((2 : ℂ)⁻¹ * Complex.I) * (-2 * Complex.I : ℂ) = 1 :=
    (mul_comm _ _).trans hScalar
  rw [one_sub_cayleyAction K S hRight, resolventAtOne_factor]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, hLeft, hScalarRev,
    one_smul]

/-- Conditional left inverse identity at one. -/
theorem resolventAtOne_mul_one_sub_cayleyAction (K S : A)
    (hRight : (K - Complex.I • (1 : A)) * S = 1) :
    resolventAtOne K * (1 - cayleyAction K S) = 1 := by
  have hScalar : ((2 : ℂ)⁻¹ * Complex.I) * (-2 * Complex.I : ℂ) = 1 := by
    calc
      _ = -(Complex.I * Complex.I) := by ring
      _ = 1 := by simp
  have hScalarRev : (-2 * Complex.I : ℂ) * ((2 : ℂ)⁻¹ * Complex.I) = 1 :=
    (mul_comm _ _).trans hScalar
  rw [one_sub_cayleyAction K S hRight, resolventAtOne_factor]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, hRight, hScalarRev,
    one_smul]

end Algebra

section StarAlgebra

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]

/-- The squared affine resolvent has no term linear in `K`. -/
theorem resolventAtOne_gram (K : A) (hSelf : star K = K) :
    star (resolventAtOne K) * resolventAtOne K =
      (4 : ℂ)⁻¹ • (1 + K * K) := by
  have hGram : star (1 + Complex.I • K) * (1 + Complex.I • K) =
      1 + K * K := by
    simp [hSelf, add_mul, mul_add, smul_add, smul_smul]
  calc
    star (resolventAtOne K) * resolventAtOne K =
        (4 : ℂ)⁻¹ • (star (1 + Complex.I • K) * (1 + Complex.I • K)) := by
      simp only [resolventAtOne, star_smul, smul_mul_assoc,
        mul_smul_comm, smul_smul]
      norm_num
    _ = _ := by rw [hGram]

/-- A Cayley action built from a right denominator inverse is an isometry.
The norm/finite-dimensional arguments that provide the inverse are separate. -/
theorem cayleyAction_star_mul_self (K S : A) (hSelf : star K = K)
    (hRight : (K - Complex.I • (1 : A)) * S = 1) :
    star (cayleyAction K S) * cayleyAction K S = 1 := by
  have hGram :
      star (K + Complex.I • (1 : A)) * (K + Complex.I • (1 : A)) =
        star (K - Complex.I • (1 : A)) * (K - Complex.I • (1 : A)) := by
    simp [hSelf, add_mul, mul_add, mul_sub, smul_add, smul_smul]; abel
  calc
    star (cayleyAction K S) * cayleyAction K S =
        star S * (star (K + Complex.I • (1 : A)) *
          (K + Complex.I • (1 : A))) * S := by
      simp only [cayleyAction, star_mul, mul_assoc]
    _ = star S * (star (K - Complex.I • (1 : A)) *
          (K - Complex.I • (1 : A))) * S := by rw [hGram]
    _ = star ((K - Complex.I • (1 : A)) * S) *
          ((K - Complex.I • (1 : A)) * S) := by
      simp only [star_mul, mul_assoc]
    _ = 1 := by rw [hRight, star_one, one_mul]

end StarAlgebra

open ContinuousLinearMap
open scoped InnerProduct

variable {P V : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- The compressed affine resolvent records exactly the compressed generator. -/
theorem resolventAtOne_compression (K : V →L[ℂ] V) (J : P →L[ℂ] V)
    (hJ : J† ∘L J = 1) :
    J† ∘L resolventAtOne K ∘L J =
      (2 : ℂ)⁻¹ • (1 + Complex.I • (J† ∘L K ∘L J)) := by
  simp only [resolventAtOne, smul_comp, comp_smul, add_comp, comp_add,
    one_def, id_comp]
  simp only [hJ, one_def]

/-- Exact boundary second moment.  Unlike the compressed generator, this
identity retains excursions outside the public subspace. -/
theorem resolventAtOne_boundary_gram (K : V →L[ℂ] V) (J : P →L[ℂ] V)
    (hSelf : star K = K) (hJ : J† ∘L J = 1) :
    (resolventAtOne K ∘L J)† ∘L (resolventAtOne K ∘L J) =
      (4 : ℂ)⁻¹ • (1 + (K ∘L J)† ∘L (K ∘L J)) := by
  have hK : K† = K := hSelf
  have hGram : (resolventAtOne K)† ∘L resolventAtOne K =
      (4 : ℂ)⁻¹ • (1 + K ∘L K) :=
    resolventAtOne_gram K hSelf
  calc
    (resolventAtOne K ∘L J)† ∘L (resolventAtOne K ∘L J) =
        J† ∘L ((resolventAtOne K)† ∘L resolventAtOne K) ∘L J := by
      simp only [adjoint_comp, comp_assoc]
    _ = J† ∘L ((4 : ℂ)⁻¹ • (1 + K ∘L K)) ∘L J := by rw [hGram]
    _ = (4 : ℂ)⁻¹ • (1 + J† ∘L (K ∘L K) ∘L J) := by
      simp only [smul_comp, comp_smul, add_comp, comp_add, one_def, id_comp]
      simp only [hJ, one_def]
    _ = _ := by simp only [adjoint_comp, hK, comp_assoc]

/-- The response norm is controlled by the second moment of `K` at the
boundary.  No bound on the full operator norm of `K` is used. -/
theorem resolventAtOne_boundary_norm_sq_le (K : V →L[ℂ] V)
    (J : P →L[ℂ] V) (γ : ℝ) (hSelf : star K = K) (hJ : J† ∘L J = 1)
    (hγ : 0 ≤ γ) (hBoundary : ‖K ∘L J‖ ≤ γ) :
    ‖resolventAtOne K ∘L J‖ ^ 2 ≤ (1 + γ ^ 2) / 4 := by
  have hSquare : ‖K ∘L J‖ ^ 2 ≤ γ ^ 2 := by
    nlinarith [norm_nonneg (K ∘L J)]
  have hNorm :
      ‖(resolventAtOne K ∘L J)† ∘L (resolventAtOne K ∘L J)‖ ≤
        (1 + γ ^ 2) / 4 := by
    rw [resolventAtOne_boundary_gram K J hSelf hJ, norm_smul]
    have hScalar : ‖(4 : ℂ)⁻¹‖ = (1 / 4 : ℝ) := by norm_num
    rw [hScalar]
    have hAdd := norm_add_le (1 : P →L[ℂ] P) ((K ∘L J)† ∘L (K ∘L J))
    rw [norm_adjoint_comp_self] at hAdd
    have hId : ‖(1 : P →L[ℂ] P)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    nlinarith
  simpa only [norm_adjoint_comp_self, pow_two] using hNorm

omit [CompleteSpace V] in
/-- A coarse full resolvent bound, valid without self-adjointness. -/
theorem resolventAtOne_norm_le (K : V →L[ℂ] V) :
    ‖resolventAtOne K‖ ≤ (1 + ‖K‖) / 2 := by
  rw [resolventAtOne, norm_smul]
  have hScalar : ‖(2 : ℂ)⁻¹‖ = (1 / 2 : ℝ) := by norm_num
  rw [hScalar]
  have hAdd := norm_add_le (1 : V →L[ℂ] V) (Complex.I • K)
  rw [norm_smul, Complex.norm_I, one_mul] at hAdd
  have hId : ‖(1 : V →L[ℂ] V)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  linarith

/-- The two endpoint responses have equal norm for an actual Cayley action. -/
theorem cayley_boundary_endpoint_norm (K S : V →L[ℂ] V)
    (J : P →L[ℂ] V) (hSelf : star K = K)
    (hRight : (K - Complex.I • (1 : V →L[ℂ] V)) * S = 1)
    (hLeft : S * (K - Complex.I • (1 : V →L[ℂ] V)) = 1) :
    ‖J† ∘L (cayleyAction K S ∘L resolventAtOne K)‖ =
      ‖resolventAtOne K ∘L J‖ := by
  exact UnitaryResolvent.boundary_endpoint_norm (cayleyAction K S)
    (resolventAtOne K) J (cayleyAction_star_mul_self K S hSelf hRight)
    (one_sub_cayleyAction_mul_resolventAtOne K S hRight hLeft)

/-- A normalized boundary moment gives the quadratic response budget after
rescaling by a nonnegative real parameter. -/
theorem rescaled_boundary_norm_sq_le (K : V →L[ℂ] V) (J : P →L[ℂ] V)
    (γ : ℝ) (hSelf : star K = K) (hJ : J† ∘L J = 1)
    (hγ : 0 ≤ γ) (hBoundary : ‖K ∘L J‖ ≤ 1) :
    ‖resolventAtOne ((γ : ℂ) • K) ∘L J‖ ^ 2 ≤ (1 + γ ^ 2) / 4 := by
  have hSelfScaled : star ((γ : ℂ) • K) = (γ : ℂ) • K := by
    simp [star_smul, hSelf]
  have hScaled : ‖((γ : ℂ) • K) ∘L J‖ ≤ γ := by
    rw [smul_comp, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hγ]
    simpa using mul_le_mul_of_nonneg_left hBoundary hγ
  exact resolventAtOne_boundary_norm_sq_le ((γ : ℂ) • K) J γ
    hSelfScaled hJ hγ hScaled

end
end SparseHamiltonian.ImprovedCayleyMoments
