import SparseHamiltonian.FixedLocatorConjugation

/-!
# Transporting Cayley moments to a fixed public preparation

Conjugating the physical edge generator and its explicit denominator inverse
by a full locator unitary moves the input dependence out of the boundary.
These identities apply on the full Hilbert space, including padded entries.
-/

namespace SparseHamiltonian.UnitaryCayleyTransport

noncomputable section
open ContinuousLinearMap OracleCircuit
open scoped InnerProduct

variable {P V : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- Pull an operator back through a full unitary change of coordinates. -/
def conjugate (U A : V →L[ℂ] V) : V →L[ℂ] V := star U * A * U

theorem conjugate_one (U : V →L[ℂ] V) (hU : IsUnitary U) :
    conjugate U 1 = 1 := by
  simp only [conjugate, mul_one, hU.1]

theorem conjugate_add (U A B : V →L[ℂ] V) :
    conjugate U (A + B) = conjugate U A + conjugate U B := by
  simp only [conjugate, mul_add, add_mul]

theorem conjugate_sub (U A B : V →L[ℂ] V) :
    conjugate U (A - B) = conjugate U A - conjugate U B := by
  simp only [conjugate, mul_sub, sub_mul]

theorem conjugate_smul (U : V →L[ℂ] V) (c : ℂ) (A : V →L[ℂ] V) :
    conjugate U (c • A) = c • conjugate U A := by
  simp only [conjugate, mul_smul_comm, smul_mul_assoc]

theorem conjugate_mul (U : V →L[ℂ] V) (hU : IsUnitary U)
    (A B : V →L[ℂ] V) :
    conjugate U (A * B) = conjugate U A * conjugate U B := by
  unfold conjugate
  calc
    star U * (A * B) * U = (star U * A) * ((U * star U) * B) * U := by
      rw [hU.2, one_mul]
      simp only [mul_assoc]
    _ = (star U * A * U) * (star U * B * U) := by
      simp only [mul_assoc]

theorem conjugate_star (U A : V →L[ℂ] V) :
    star (conjugate U A) = conjugate U (star A) := by
  simp only [conjugate, star_mul, star_star, mul_assoc]

theorem conjugate_self_adjoint (U K : V →L[ℂ] V) (hK : star K = K) :
    star (conjugate U K) = conjugate U K := by
  rw [conjugate_star, hK]

theorem conjugate_unitary (U D : V →L[ℂ] V)
    (hU : IsUnitary U) (hD : IsUnitary D) : IsUnitary (conjugate U D) :=
  (hU.adjoint.mul hD).mul hU

/-- No nonzero-dimensionality assumption is needed for this norm bound. -/
theorem conjugate_norm_le (U : V →L[ℂ] V) (hU : IsUnitary U)
    (K : V →L[ℂ] V) : ‖conjugate U K‖ ≤ ‖K‖ := by
  have hLeft : ‖star U * K‖ ≤ ‖K‖ :=
    (norm_mul_le _ _).trans
      (mul_le_of_le_one_left (norm_nonneg K) hU.adjoint.norm_le_one)
  exact (norm_mul_le _ _).trans
    ((mul_le_of_le_one_right (norm_nonneg (star U * K)) hU.norm_le_one).trans hLeft)

omit [CompleteSpace P] in
theorem conjugate_comp (U K : V →L[ℂ] V) (J : P →L[ℂ] V) :
    conjugate U K ∘L J = U† ∘L (K ∘L (U ∘L J)) := by
  simp only [conjugate, star_eq_adjoint, mul_def, comp_assoc]

omit [CompleteSpace P] in
/-- The boundary moment is unchanged in norm under a unitary pullback. -/
theorem boundary_norm_eq (U : V →L[ℂ] V) (hU : IsUnitary U)
    (K : V →L[ℂ] V) (J : P →L[ℂ] V) :
    ‖conjugate U K ∘L J‖ = ‖K ∘L (U ∘L J)‖ := by
  rw [conjugate_comp]
  exact EncodedOracle.norm_comp_eq (U†)
    (by simpa only [← star_eq_adjoint, ← mul_def, star_star] using hU.2) _

omit [CompleteSpace P] in
theorem boundary_norm_le (U : V →L[ℂ] V) (hU : IsUnitary U)
    (K : V →L[ℂ] V) (J : P →L[ℂ] V) :
    ‖conjugate U K ∘L J‖ ≤ ‖K ∘L (U ∘L J)‖ :=
  (boundary_norm_eq U hU K J).le

/-- The compressed Hamiltonian is preserved exactly, not just in norm. -/
theorem compression (U K : V →L[ℂ] V) (J : P →L[ℂ] V) :
    J† ∘L conjugate U K ∘L J =
      (U ∘L J)† ∘L K ∘L (U ∘L J) := by
  simp only [conjugate, star_eq_adjoint, mul_def, adjoint_comp, comp_assoc]

/-- Isometry of the physical preparation certifies the fixed preparation. -/
theorem boundary_isometry (U : V →L[ℂ] V) (hU : IsUnitary U)
    (J : P →L[ℂ] V) (hJ : (U ∘L J)† ∘L (U ∘L J) = 1) :
    J† ∘L J = 1 := by
  have hComp : U† ∘L U = 1 := hU.1
  calc
    J† ∘L J = J† ∘L (U† ∘L U) ∘L J := by
      simp only [hComp, one_def, id_comp]
    _ = (U ∘L J)† ∘L (U ∘L J) := by
      simp only [adjoint_comp, comp_assoc]
    _ = 1 := hJ

theorem conjugate_scaled (U K : V →L[ℂ] V) (γ : ℝ) :
    conjugate U (CayleyClockInterface.scaled K γ) =
      CayleyClockInterface.scaled (conjugate U K) γ :=
  conjugate_smul U (γ : ℂ) K

/-- Conjugation preserves the right denominator inverse on the whole space. -/
theorem inverse_right (U : V →L[ℂ] V) (hU : IsUnitary U)
    (K S : V →L[ℂ] V) (γ : ℝ)
    (hRight : (CayleyClockInterface.scaled K γ -
      Complex.I • (1 : V →L[ℂ] V)) * S = 1) :
    (CayleyClockInterface.scaled (conjugate U K) γ -
      Complex.I • (1 : V →L[ℂ] V)) * conjugate U S = 1 := by
  calc
    (CayleyClockInterface.scaled (conjugate U K) γ -
        Complex.I • (1 : V →L[ℂ] V)) * conjugate U S =
        conjugate U (CayleyClockInterface.scaled K γ -
          Complex.I • (1 : V →L[ℂ] V)) * conjugate U S := by
      rw [conjugate_sub, conjugate_scaled, conjugate_smul, conjugate_one U hU]
    _ = conjugate U ((CayleyClockInterface.scaled K γ -
        Complex.I • (1 : V →L[ℂ] V)) * S) := (conjugate_mul U hU _ _).symm
    _ = 1 := by rw [hRight, conjugate_one U hU]

/-- The separately required left inverse is transported as well. -/
theorem inverse_left (U : V →L[ℂ] V) (hU : IsUnitary U)
    (K S : V →L[ℂ] V) (γ : ℝ)
    (hLeft : S * (CayleyClockInterface.scaled K γ -
      Complex.I • (1 : V →L[ℂ] V)) = 1) :
    conjugate U S * (CayleyClockInterface.scaled (conjugate U K) γ -
      Complex.I • (1 : V →L[ℂ] V)) = 1 := by
  calc
    conjugate U S * (CayleyClockInterface.scaled (conjugate U K) γ -
        Complex.I • (1 : V →L[ℂ] V)) =
        conjugate U S * conjugate U (CayleyClockInterface.scaled K γ -
          Complex.I • (1 : V →L[ℂ] V)) := by
      rw [conjugate_sub, conjugate_scaled, conjugate_smul, conjugate_one U hU]
    _ = conjugate U (S * (CayleyClockInterface.scaled K γ -
        Complex.I • (1 : V →L[ℂ] V))) := (conjugate_mul U hU _ _).symm
    _ = 1 := by rw [hLeft, conjugate_one U hU]

/-- The conjugated local gate is exactly the Cayley action of the transported
generator with the transported explicit inverse. -/
theorem cayleyAction_conjugate (U : V →L[ℂ] V) (hU : IsUnitary U)
    (K S : V →L[ℂ] V) (γ : ℝ) :
    conjugate U (ImprovedCayleyMoments.cayleyAction
      (CayleyClockInterface.scaled K γ) S) =
      ImprovedCayleyMoments.cayleyAction
        (CayleyClockInterface.scaled (conjugate U K) γ) (conjugate U S) := by
  rw [ImprovedCayleyMoments.cayleyAction, conjugate_mul U hU,
    conjugate_add, conjugate_scaled, conjugate_smul, conjugate_one U hU]
  rfl

/-- Package the moment transport with an explicit factorization of the
physical boundary.  Its preparation can depend on the input through `U`,
while the simulator uses the given fixed map `Jfree`. -/
theorem moment_certificate (U : V →L[ℂ] V) (hU : IsUnitary U)
    (K : V →L[ℂ] V) (Jfree Jphysical : P →L[ℂ] V) (a b : ℝ)
    (hBoundary : U ∘L Jfree = Jphysical)
    (hJ : Jphysical† ∘L Jphysical = 1) (hSelf : star K = K)
    (hNorm : ‖K‖ ≤ a) (hMoment : ‖K ∘L Jphysical‖ ≤ b) :
    Jfree† ∘L Jfree = 1 ∧
    star (conjugate U K) = conjugate U K ∧
    ‖conjugate U K‖ ≤ a ∧
    ‖conjugate U K ∘L Jfree‖ ≤ b ∧
    Jfree† ∘L conjugate U K ∘L Jfree = Jphysical† ∘L K ∘L Jphysical := by
  refine ⟨boundary_isometry U hU Jfree (by rw [hBoundary]; exact hJ),
    conjugate_self_adjoint U K hSelf, (conjugate_norm_le U hU K).trans hNorm,
    ?_, ?_⟩
  · rw [boundary_norm_eq U hU K Jfree, hBoundary]
    exact hMoment
  · rw [compression, hBoundary]

end
end SparseHamiltonian.UnitaryCayleyTransport
