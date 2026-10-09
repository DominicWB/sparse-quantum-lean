import SparseLinearSystems.Foundations.HilbertAugmentation

/-!
# The Cayley transform of a self-adjoint operator

A self-adjoint operator `K` on a finite-dimensional Hilbert space has no
eigenvector with eigenvalue `i`, so the denominator `K - i` is invertible
(`denominatorInverse`).  The Cayley transform `(K + i)(K - i)⁻¹` is unitary
(`cayley_unitary`), and `(1 + iK)/2` inverts `1 - cayley K`
(`one_sub_cayley_mul_resolvent`, `resolvent_mul_one_sub_cayley`).
-/

namespace SparseLinearSystems.HilbertCayley

noncomputable section
open ContinuousLinearMap
open scoped ComplexConjugate

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
variable [CompleteSpace V]

/-- The denominator in the convention D = (K+iI)(K-iI)⁻¹. -/
def denominator (K : V →L[ℂ] V) : V →L[ℂ] V :=
  K - Complex.I • (1 : V →L[ℂ] V)

omit [CompleteSpace V] in
@[simp] theorem denominator_apply (K : V →L[ℂ] V) (x : V) :
    denominator K x = K x - Complex.I • x := rfl

/-- A self-adjoint operator cannot have the nonreal eigenvalue i. -/
theorem denominator_eq_zero (K : V →L[ℂ] V) (hSelf : (ContinuousLinearMap.adjoint K) = K)
    (x : V) (hx : denominator K x = 0) : x = 0 := by
  have hKx : K x = Complex.I • x :=
    sub_eq_zero.mp (show K x - Complex.I • x = 0 from hx)
  have hHerm : inner ℂ (K x) x = inner ℂ x (K x) := by
    calc
      _ = inner ℂ ((ContinuousLinearMap.adjoint K) x) x := by rw [hSelf]
      _ = _ := adjoint_inner_left K x x
  have hi : (-Complex.I) * inner ℂ x x = Complex.I * inner ℂ x x := by
    simpa only [hKx, inner_smul_left, inner_smul_right, Complex.conj_I] using hHerm
  have hz : (2 * Complex.I) * inner ℂ x x = 0 := by
    calc
      _ = Complex.I * inner ℂ x x - (-Complex.I) * inner ℂ x x := by ring
      _ = 0 := sub_eq_zero.mpr hi.symm
  have hinner : inner ℂ x x = 0 :=
    (mul_eq_zero.mp hz).resolve_left (mul_ne_zero (by norm_num) Complex.I_ne_zero)
  exact (inner_self_eq_zero (𝕜 := ℂ)).mp hinner

/-- Injectivity uses only self-adjointness, not finite dimensionality. -/
theorem denominator_injective (K : V →L[ℂ] V) (hSelf : (ContinuousLinearMap.adjoint K) = K) :
    Function.Injective (denominator K) := by
  intro x y hxy
  have hzero : denominator K (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  exact sub_eq_zero.mp (denominator_eq_zero K hSelf (x - y) hzero)

/-- The affine resolvent Gram law gives an exact inner-product identity. -/
theorem resolvent_inner (K : V →L[ℂ] V) (hSelf : (ContinuousLinearMap.adjoint K) = K) (x y : V) :
    inner ℂ (Cayley.resolventAtOne K x) (Cayley.resolventAtOne K y) =
      (4 : ℂ)⁻¹ * (inner ℂ x y + inner ℂ (K x) (K y)) := by
  have h := congrArg (fun T : V →L[ℂ] V => inner ℂ x (T y))
    (Cayley.resolventAtOne_gram K hSelf)
  change inner ℂ x ((ContinuousLinearMap.adjoint (Cayley.resolventAtOne K)) (Cayley.resolventAtOne K y)) =
    inner ℂ x ((4 : ℂ)⁻¹ • (y + K (K y))) at h
  rw [adjoint_inner_right, inner_smul_right, inner_add_right] at h
  have hKK : inner ℂ x (K (K y)) = inner ℂ (K x) (K y) := by
    calc
      _ = inner ℂ ((ContinuousLinearMap.adjoint K) x) (K y) := (adjoint_inner_left K (K y) x).symm
      _ = _ := by rw [hSelf]
  rw [hKK] at h
  exact h

/-- Exact squared norm of the affine resolvent on any vector. -/
theorem resolvent_norm_sq (K : V →L[ℂ] V) (hSelf : (ContinuousLinearMap.adjoint K) = K) (x : V) :
    ‖Cayley.resolventAtOne K x‖ ^ 2 = (‖x‖ ^ 2 + ‖K x‖ ^ 2) / 4 := by
  have h := resolvent_inner K hSelf x x
  simp only [inner_self_eq_norm_sq_to_K] at h
  have hc : (4 : ℂ)⁻¹ * ((↑‖x‖ : ℂ) ^ 2 + (↑‖K x‖ : ℂ) ^ 2) =
      (( (‖x‖ ^ 2 + ‖K x‖ ^ 2) / 4 : ℝ) : ℂ) := by
    push_cast
    ring
  have hreal := congrArg (RCLike.re : ℂ → ℝ) (h.trans hc)
  simp only [RCLike.re_ofReal_pow] at hreal
  exact hreal

/-- The compressed second-moment hypothesis produces the walk-lift norm bounds. -/
theorem resolvent_norm_sq_bounds (K : V →L[ℂ] V) (hSelf : (ContinuousLinearMap.adjoint K) = K) (x : V)
    (hMoment : ‖K x‖ ^ 2 ≤ ‖x‖ ^ 2) :
    ‖x‖ ^ 2 / 4 ≤ ‖Cayley.resolventAtOne K x‖ ^ 2 ∧
      ‖Cayley.resolventAtOne K x‖ ^ 2 ≤ ‖x‖ ^ 2 / 2 := by
  rw [resolvent_norm_sq K hSelf x]
  constructor
  · nlinarith [sq_nonneg ‖K x‖]
  · nlinarith

section FiniteDimensional

variable [FiniteDimensional ℂ V]

/-- Finite dimensionality supplies the missing surjectivity. -/
theorem denominator_surjective (K : V →L[ℂ] V) (hSelf : (ContinuousLinearMap.adjoint K) = K) :
    Function.Surjective (denominator K) :=
  (LinearMap.injective_iff_surjective (f := (denominator K).toLinearMap)).mp
    (denominator_injective K hSelf)

/-- The denominator as a genuine algebraic equivalence. -/
def denominatorEquiv (K : V →L[ℂ] V) (hSelf : (ContinuousLinearMap.adjoint K) = K) : V ≃ₗ[ℂ] V :=
  LinearEquiv.ofBijective (denominator K).toLinearMap
    ⟨denominator_injective K hSelf, denominator_surjective K hSelf⟩

/-- The actual continuous inverse, constructed from self-adjointness. -/
def denominatorInverse (K : V →L[ℂ] V) (hSelf : (ContinuousLinearMap.adjoint K) = K) : V →L[ℂ] V :=
  (denominatorEquiv K hSelf).symm.toLinearMap.toContinuousLinearMap

/-- Right inverse law for the constructed denominator inverse. -/
theorem denominator_mul_inverse (K : V →L[ℂ] V) (hSelf : (ContinuousLinearMap.adjoint K) = K) :
    denominator K * denominatorInverse K hSelf = 1 := by
  ext x
  change denominatorEquiv K hSelf ((denominatorEquiv K hSelf).symm x) = x
  exact (denominatorEquiv K hSelf).apply_symm_apply x

/-- Left inverse law for the constructed denominator inverse. -/
theorem inverse_mul_denominator (K : V →L[ℂ] V) (hSelf : (ContinuousLinearMap.adjoint K) = K) :
    denominatorInverse K hSelf * denominator K = 1 := by
  ext x
  change (denominatorEquiv K hSelf).symm (denominatorEquiv K hSelf x) = x
  exact (denominatorEquiv K hSelf).symm_apply_apply x

/-- The Cayley operator, now with no separate inverse-existence hypothesis. -/
def cayley (K : V →L[ℂ] V) (hSelf : (ContinuousLinearMap.adjoint K) = K) : V →L[ℂ] V :=
  Cayley.cayleyAction K (denominatorInverse K hSelf)

/-- The Cayley operator is an isometry in operator algebra. -/
theorem cayley_star_mul_self (K : V →L[ℂ] V) (hSelf : (ContinuousLinearMap.adjoint K) = K) :
    star (cayley K hSelf) * cayley K hSelf = 1 :=
  Cayley.cayleyAction_star_mul_self K (denominatorInverse K hSelf) hSelf
    (denominator_mul_inverse K hSelf)

/-- Norm preservation is a consequence of the proved inverse and Gram laws. -/
theorem cayley_norm_apply (K : V →L[ℂ] V) (hSelf : (ContinuousLinearMap.adjoint K) = K) (x : V) :
    ‖cayley K hSelf x‖ = ‖x‖ := by
  have h := cayley_star_mul_self K hSelf
  change (ContinuousLinearMap.adjoint (cayley K hSelf)) ∘L cayley K hSelf = 1 at h
  exact ((cayley K hSelf).norm_map_iff_adjoint_comp_self.mpr h) x

/-- The reverse unitary law follows from finite-dimensional surjectivity. -/
theorem cayley_mul_star_self (K : V →L[ℂ] V) (hSelf : (ContinuousLinearMap.adjoint K) = K) :
    cayley K hSelf * star (cayley K hSelf) = 1 := by
  let D := cayley K hSelf
  have hLeft : (ContinuousLinearMap.adjoint D) ∘L D = 1 := cayley_star_mul_self K hSelf
  have hInj : Function.Injective D := by
    intro x y hxy
    have hx := congrArg (fun T : V →L[ℂ] V => T x) hLeft
    have hy := congrArg (fun T : V →L[ℂ] V => T y) hLeft
    simp only [comp_apply, one_def, id_apply, hxy] at hx hy
    exact hx.symm.trans hy
  have hSurj : Function.Surjective D :=
    (LinearMap.injective_iff_surjective (f := D.toLinearMap)).mp hInj
  ext x
  obtain ⟨y, rfl⟩ := hSurj x
  have h := congrArg (fun T : V →L[ℂ] V => D (T y)) hLeft
  change D ((ContinuousLinearMap.adjoint D) (D y)) = D y
  simpa only [comp_apply, one_def, id_apply] using h

/-- The affine expression (I+iK)/2 really is a right inverse of I-D. -/
theorem one_sub_cayley_mul_resolvent (K : V →L[ℂ] V) (hSelf : (ContinuousLinearMap.adjoint K) = K) :
    (1 - cayley K hSelf) * Cayley.resolventAtOne K = 1 :=
  Cayley.one_sub_cayleyAction_mul_resolventAtOne K (denominatorInverse K hSelf)
    (denominator_mul_inverse K hSelf) (inverse_mul_denominator K hSelf)

/-- The same affine expression is a left inverse. -/
theorem resolvent_mul_one_sub_cayley (K : V →L[ℂ] V) (hSelf : (ContinuousLinearMap.adjoint K) = K) :
    Cayley.resolventAtOne K * (1 - cayley K hSelf) = 1 :=
  Cayley.resolventAtOne_mul_one_sub_cayleyAction K (denominatorInverse K hSelf)
    (denominator_mul_inverse K hSelf)

/-- Both unitary laws, with no inverse or norm-preservation promise. -/
theorem cayley_unitary (K : V →L[ℂ] V) (hSelf : (ContinuousLinearMap.adjoint K) = K) :
    star (cayley K hSelf) * cayley K hSelf = 1 ∧
      cayley K hSelf * star (cayley K hSelf) = 1 :=
  ⟨cayley_star_mul_self K hSelf, cayley_mul_star_self K hSelf⟩

end FiniteDimensional
end
end SparseLinearSystems.HilbertCayley
