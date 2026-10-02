import SparseHamiltonian.PolynomialGainError

/-!
# Free output phases preserve gain error and the full overlap

Converse phase synthesis produces one global phase and one phase on the good
coordinate. A common output unitary cancels from a row/column overlap. At the
scalar level either phase can be transferred to the target gain, preserving
its norm and the relative-error budget. These identities allow the native
phase-pair circuit to use a synthesized multiplier without increasing queries.
-/

namespace SparseHamiltonian.ScalarPhaseError

noncomputable section
open Polynomial ContinuousLinearMap AmplitudePolynomialSequence
open scoped ComplexConjugate InnerProduct

/-- The product of the two fixed synthesis phases is still a unit phase. -/
def productPhase (v u : UnitPhase) : UnitPhase :=
  ⟨(v : ℂ) * (u : ℂ), by rw [norm_mul, v.property, u.property, one_mul]⟩

/-- Multiplying a target by a conjugate unit phase does not change the gain. -/
theorem norm_phased_target (u : UnitPhase) (target : ℂ) :
    ‖conj (u : ℂ) * target‖ = ‖target‖ := by
  rw [norm_mul, Complex.norm_conj, u.property, one_mul]

/-- A fixed output phase can be transferred exactly from the output to the target. -/
theorem norm_phase_sub (u : UnitPhase) (z target : ℂ) :
    ‖(u : ℂ) * z - target‖ = ‖z - conj (u : ℂ) * target‖ := by
  have hu : (u : ℂ) * conj (u : ℂ) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, u.property]
    norm_num
  calc
    _ = ‖(u : ℂ) * (z - conj (u : ℂ) * target)‖ := by
      congr 1
      rw [mul_sub, ← mul_assoc, hu, one_mul]
    _ = _ := by rw [norm_mul, u.property, one_mul]

/-- Relative approximation is invariant under moving a fixed output phase
into the common target gain. This statement includes zero signals. -/
theorem relative_approx_iff (u : UnitPhase) (z target : ℂ) (x δ : ℝ) :
    ‖(u : ℂ) * z - target * (x : ℂ)‖ ≤ (δ * ‖target‖) * |x| ↔
      ‖z - (conj (u : ℂ) * target) * (x : ℂ)‖ ≤
        (δ * ‖conj (u : ℂ) * target‖) * |x| := by
  simp only [norm_phase_sub, norm_phased_target, mul_assoc]

/-- A polynomial realized up to an output phase has exactly the same relative
approximation bound, after the corresponding target-phase adjustment. -/
theorem polynomial_relative_error (u : UnitPhase) (P B : ℂ[X])
    (hP : P = C (u : ℂ) * B) (target : ℂ) (x δ : ℝ)
    (herr : ‖P.eval (x : ℂ) - target * (x : ℂ)‖ ≤ (δ * ‖target‖) * |x|) :
    ‖B.eval (x : ℂ) - (conj (u : ℂ) * target) * (x : ℂ)‖ ≤
      (δ * ‖conj (u : ℂ) * target‖) * |x| := by
  rw [hP, eval_mul, eval_C] at herr
  exact (relative_approx_iff u (B.eval (x : ℂ)) target x δ).mp herr

/-- The two output phases in paired synthesis preserve the exact scalar
relative-error premise consumed by the native overlap theorem. -/
theorem paired_relative_error (v u : UnitPhase) (ss : List Phases) (P : ℂ[X])
    (hP : P = C ((v : ℂ) * (u : ℂ)) * (polynomials ss).1)
    (target : ℂ) (x δ : ℝ)
    (herr : ‖P.eval (x : ℂ) - target * (x : ℂ)‖ ≤ (δ * ‖target‖) * |x|) :
    ‖(polynomials ss).1.eval (x : ℂ) -
        (conj ((v : ℂ) * (u : ℂ)) * target) * (x : ℂ)‖ ≤
      (δ * ‖target‖) * |x| := by
  have h := polynomial_relative_error (productPhase v u) P (polynomials ss).1
    hP target x δ herr
  rwa [norm_phased_target] at h

/-- The adjusted target remains nonzero when the requested target is nonzero. -/
theorem phased_target_ne_zero (u : UnitPhase) (target : ℂ) (ht : target ≠ 0) :
    conj (u : ℂ) * target ≠ 0 := by
  apply norm_ne_zero_iff.mp
  rw [norm_phased_target]
  exact norm_ne_zero_iff.mpr ht

section Overlap
variable {E K L : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]

/-- A shared output isometry, including a shared global/good phase gate,
cancels exactly from the full row/column overlap. -/
theorem common_output_cancels (V : K →L[ℂ] L) (hV : V† ∘L V = 1)
    (R C : E →L[ℂ] K) : (V ∘L R)† ∘L (V ∘L C) = R† ∘L C := by
  rw [adjoint_comp, ContinuousLinearMap.comp_assoc,
    ← ContinuousLinearMap.comp_assoc (V†), hV, one_def, id_comp]

end Overlap
end
end SparseHamiltonian.ScalarPhaseError
