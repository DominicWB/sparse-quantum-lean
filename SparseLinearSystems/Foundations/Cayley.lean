import Mathlib.Algebra.Algebra.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Prod
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Tactic.FieldSimp

/-!
# Cayley resolvent algebra

In a complex algebra let `S` be a right inverse of the Cayley denominator
`K - i`, let `D = (K + i) S` be the Cayley action and `R₀ = (1 + iK)/2` the
resolvent at one.  Then `1 - D = -2i S` (`one_sub_cayleyAction`), `R₀` is a
two-sided inverse of `1 - D` when `S` is a two-sided inverse
(`one_sub_cayleyAction_mul_resolventAtOne`,
`resolventAtOne_mul_one_sub_cayleyAction`), `R₀* R₀ = (1 + K²)/4` for
self-adjoint `K`, and then `D` is an isometry (`cayleyAction_star_mul_self`).
`Foundations.HilbertCayley` constructs the inverse for self-adjoint operators
on finite-dimensional Hilbert spaces.
-/

namespace SparseLinearSystems.Cayley

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
  rw [one_sub_cayleyAction K S hRight, resolventAtOne_factor]
  rw [smul_mul_assoc, mul_smul_comm, smul_smul, hLeft, hScalar, one_smul]

/-- Conditional left inverse identity at one. -/
theorem resolventAtOne_mul_one_sub_cayleyAction (K S : A)
    (hRight : (K - Complex.I • (1 : A)) * S = 1) :
    resolventAtOne K * (1 - cayleyAction K S) = 1 := by
  have hScalar : ((2 : ℂ)⁻¹ * Complex.I) * (-2 * Complex.I : ℂ) = 1 := by
    calc
      _ = -(Complex.I * Complex.I) := by ring
      _ = 1 := by simp
  rw [one_sub_cayleyAction K S hRight, resolventAtOne_factor]
  rw [smul_mul_assoc, mul_smul_comm, smul_smul, hRight, hScalar, one_smul]

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

end
end SparseLinearSystems.Cayley
