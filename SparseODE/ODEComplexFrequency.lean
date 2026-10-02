import SparseODE.ODEGaussianIntegral

/-!
# Contractivity below the real frequency axis

The complex continuation of the LCHS Hamiltonian exponential is a contraction
throughout the closed lower half-plane. This is the operator estimate needed
when shifting the Gaussian contour. At the pole `-I` the continued evolution
is exactly the dissipative ODE propagator, with no commutativity assumption.
No contour identity or integral approximation is assumed in this file.
-/

namespace SparseHamiltonian.ODEComplexFrequency

noncomputable section
open ContinuousLinearMap NormedSpace
open scoped ComplexConjugate InnerProduct

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [CompleteSpace V]

/-- Continue the frequency to a complex value before exponentiating. -/
def generator (D H : V →L[ℂ] V) (z : ℂ) : V →L[ℂ] V :=
  -Complex.I • (H + z • D)

/-- The complex-frequency propagator at a real duration. -/
def evolution (D H : V →L[ℂ] V) (u : ℝ) (z : ℂ) : V →L[ℂ] V :=
  exp (u • generator D H z)

/-- The quadratic form of a self-adjoint operator is real. -/
theorem inner_im_eq_zero (A : V →L[ℂ] V) (hA : star A = A) (v : V) :
    (inner ℂ v (A v)).im = 0 := by
  have hAdj : A† = A := hA
  have hSwap : inner ℂ v ((A†) v) = inner ℂ (A v) v := by
    rw [adjoint_inner_right]
  rw [hAdj] at hSwap
  have hConj : conj (inner ℂ v (A v)) = inner ℂ v (A v) := by
    rw [inner_conj_symm]
    exact hSwap.symm
  have hIm := congrArg Complex.im hConj
  simp only [Complex.conj_im] at hIm
  linarith

/-- The imaginary frequency alone controls the real quadratic form. -/
theorem generator_real_inner (D H : V →L[ℂ] V)
    (hD : star D = D) (hH : star H = H) (z : ℂ) (v : V) :
    (inner ℂ v (generator D H z v)).re =
      z.im * (inner ℂ v (D v)).re := by
  have hDi := inner_im_eq_zero D hD v
  have hHi := inner_im_eq_zero H hH v
  simp only [generator, smul_apply, add_apply, inner_smul_right,
    inner_add_right, Complex.mul_re, Complex.mul_im, Complex.add_re,
    Complex.add_im, Complex.neg_re, Complex.neg_im, Complex.I_re,
    Complex.I_im, hDi, hHi]
  ring

/-- A positive dissipative part makes every lower-half-plane generator
dissipative. No relation between `D` and `H` is required. -/
theorem generator_dissipative (D H : V →L[ℂ] V)
    (hD : star D = D) (hH : star H = H)
    (hPSD : ∀ v : V, 0 ≤ (inner ℂ v (D v)).re)
    (z : ℂ) (hz : z.im ≤ 0) : ODEDissipative.Dissipative (generator D H z) := by
  intro v
  rw [generator_real_inner D H hD hH z v]
  exact mul_nonpos_of_nonpos_of_nonneg hz (hPSD v)

/-- Complex-frequency evolution is contractive below the real axis. -/
theorem evolution_norm_le_one (D H : V →L[ℂ] V)
    (hD : star D = D) (hH : star H = H)
    (hPSD : ∀ v : V, 0 ≤ (inner ℂ v (D v)).re)
    (u : ℝ) (hu : 0 ≤ u) (z : ℂ) (hz : z.im ≤ 0) :
    ‖evolution D H u z‖ ≤ 1 := by
  exact ODEDissipative.exp_norm_le_one (generator D H z)
    (generator_dissipative D H hD hH hPSD z hz) u hu

omit [CompleteSpace V] in
/-- On the real axis this continuation is exactly the existing LCHS branch. -/
theorem evolution_ofReal (D H : V →L[ℂ] V) (u k : ℝ) :
    evolution D H u (k : ℂ) = ODEWeightedLCHS.evolution D H u k := by
  unfold evolution generator ODEWeightedLCHS.evolution
  congr 1
  rw [← Complex.coe_smul u, smul_smul, mul_comm (u : ℂ)]

/-- Every downward horizontal translate obeys the same bound. -/
theorem shifted_evolution_norm_le_one (D H : V →L[ℂ] V)
    (hD : star D = D) (hH : star H = H)
    (hPSD : ∀ v : V, 0 ≤ (inner ℂ v (D v)).re)
    (u : ℝ) (hu : 0 ≤ u) (k r : ℝ) (hr : 0 ≤ r) :
    ‖evolution D H u ((k : ℂ) - (r : ℂ) * Complex.I)‖ ≤ 1 := by
  apply evolution_norm_le_one D H hD hH hPSD u hu
  simpa using neg_nonpos.mpr hr

omit [CompleteSpace V] in
/-- At the lower pole the generator recovers the original dissipative sign. -/
theorem generator_neg_I (D H : V →L[ℂ] V) :
    generator D H (-Complex.I) = -(D + Complex.I • H) := by
  have hII : (-Complex.I) * (-Complex.I) = (-1 : ℂ) := by simp
  rw [generator, smul_add, smul_smul, hII]
  module

omit [CompleteSpace V] in
theorem evolution_neg_I (D H : V →L[ℂ] V) (u : ℝ) :
    evolution D H u (-Complex.I) = exp (u • (-(D + Complex.I • H))) := by
  rw [evolution, generator_neg_I]

/-- The residue evaluation therefore yields precisely `exp (-u M)`. -/
theorem parts_evolution_neg_I (M : V →L[ℂ] V) (u : ℝ) :
    evolution (ODEHermitianReduction.dissipativePart M)
      (ODEHermitianReduction.hamiltonianPart M) u (-Complex.I) =
      exp (u • (-M)) := by
  rw [evolution_neg_I, ODEHermitianReduction.decomposition]

/-- The complex continuation is continuous on the entire frequency plane. -/
theorem evolution_continuous (D H : V →L[ℂ] V) (u : ℝ) :
    Continuous (evolution D H u) := by
  letI : NormedAlgebra ℚ (V →L[ℂ] V) := .restrictScalars ℚ ℂ _
  have hFrequency : Continuous (fun z : ℂ => H + z • D) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hGenerator : Continuous (generator D H) :=
    (continuous_const : Continuous (fun _ : ℂ => -Complex.I)).smul hFrequency
  have hScaled : Continuous (fun z : ℂ => u • generator D H z) :=
    (continuous_const : Continuous (fun _ : ℂ => u)).smul hGenerator
  exact NormedSpace.exp_continuous.comp hScaled

end
end SparseHamiltonian.ODEComplexFrequency
