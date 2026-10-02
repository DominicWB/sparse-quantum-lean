import SparseODE.ODEGaussianAnalytic

/-!
# Integrated residual on the shifted Gaussian contour

On the horizontal line with imaginary coordinate `-2*w`, the Gaussian
numerator contributes `exp (1-w)`. The complex-frequency propagator is
contractive because the dissipative part is positive. Domination by the
normalized Cauchy density proves both integrability and the uniform residual
bound. No contour deformation or integral identity is assumed here.

-/

namespace SparseHamiltonian.ODEGaussianShiftedIntegral

noncomputable section
open MeasureTheory
open scoped InnerProduct

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [CompleteSpace V]

/-- Exact Gaussian-weighted evolution on the downward horizontal contour. -/
def weighted (D H : V →L[ℂ] V) (u w k : ℝ) : V →L[ℂ] V :=
  ODEGaussianComplex.kernel w ((k : ℂ) - ((2 * w : ℝ) : ℂ) * Complex.I) •
    ODEComplexFrequency.evolution D H u
      ((k : ℂ) - ((2 * w : ℝ) : ℂ) * Complex.I)

/-- The shifted weighted operator family has no singularities on its line. -/
theorem weighted_continuous (D H : V →L[ℂ] V) (u w : ℝ) (hw : 1 ≤ w) :
    Continuous (weighted D H u w) := by
  have hLine : Continuous
      (fun k : ℝ => (k : ℂ) - ((2 * w : ℝ) : ℂ) * Complex.I) :=
    Complex.continuous_ofReal.sub continuous_const
  exact (ODEGaussianComplex.shifted_kernel_continuous w hw).smul
    ((ODEComplexFrequency.evolution_continuous D H u).comp hLine)

/-- The scalar shifted-line Cauchy envelope also bounds the operator integrand. -/
theorem weighted_norm_le (D H : V →L[ℂ] V)
    (hD : star D = D) (hH : star H = H)
    (hPSD : ∀ v : V, 0 ≤ (inner ℂ v (D v)).re)
    (u w : ℝ) (hu : 0 ≤ u) (hw : 1 ≤ w) (k : ℝ) :
    ‖weighted D H u w k‖ ≤ Real.exp (1 - w) / (Real.pi * (1 + k ^ 2)) := by
  have hShift : 0 ≤ 2 * w := by linarith
  have hEvolution := ODEComplexFrequency.shifted_evolution_norm_le_one
    D H hD hH hPSD u hu k (2 * w) hShift
  calc
    _ = ‖ODEGaussianComplex.kernel w
          ((k : ℂ) - ((2 * w : ℝ) : ℂ) * Complex.I)‖ *
        ‖ODEComplexFrequency.evolution D H u
          ((k : ℂ) - ((2 * w : ℝ) : ℂ) * Complex.I)‖ := norm_smul _ _
    _ ≤ ‖ODEGaussianComplex.kernel w
        ((k : ℂ) - ((2 * w : ℝ) : ℂ) * Complex.I)‖ * 1 :=
      mul_le_mul_of_nonneg_left hEvolution (norm_nonneg _)
    _ ≤ Real.exp (1 - w) / (Real.pi * (1 + k ^ 2)) := by
      rw [mul_one]
      exact ODEGaussianComplex.shifted_kernel_norm_le w k hw

/-- The contour residual is a genuine Bochner integral. Its existence is
proved from positivity and scalar domination, rather than assumed. -/
theorem weighted_integrable (D H : V →L[ℂ] V)
    (hD : star D = D) (hH : star H = H)
    (hPSD : ∀ v : V, 0 ≤ (inner ℂ v (D v)).re)
    (u w : ℝ) (hu : 0 ≤ u) (hw : 1 ≤ w) :
    Integrable (weighted D H u w) := by
  apply (ODEGaussianTail.integrable_cauchy (Real.exp (1 - w))).mono'
    (weighted_continuous D H u w hw).aestronglyMeasurable
  exact Filter.Eventually.of_forall (weighted_norm_le D H hD hH hPSD u w hu hw)

/-- The entire shifted contour has operator norm at most `exp (1-w)`.
The bound is uniform in duration, operator norms and dimension. -/
theorem integral_norm_le (D H : V →L[ℂ] V)
    (hD : star D = D) (hH : star H = H)
    (hPSD : ∀ v : V, 0 ≤ (inner ℂ v (D v)).re)
    (u w : ℝ) (hu : 0 ≤ u) (hw : 1 ≤ w) :
    ‖∫ k : ℝ, weighted D H u w k‖ ≤ Real.exp (1 - w) := by
  calc
    _ ≤ ∫ k : ℝ, Real.exp (1 - w) / (Real.pi * (1 + k ^ 2)) := by
      apply MeasureTheory.norm_integral_le_of_norm_le
        (ODEGaussianTail.integrable_cauchy (Real.exp (1 - w)))
      exact Filter.Eventually.of_forall (weighted_norm_le D H hD hH hPSD u w hu hw)
    _ = Real.exp (1 - w) := ODEGaussianTail.cauchy_integral_univ _

section Native

variable {X n Z : Type*} [Fintype n] [DecidableEq n] {s : ℕ}

/-- The same shifted residual expressed using the original sparse matrix. -/
def nativeWeighted (D : NativeSparseBlockEncoding.Data X n Z s)
    (x : X) (u w k : ℝ) : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n :=
  weighted
    (ODEHermitianReduction.dissipativePart (SparseStateOverlap.matrixOperator (D.matrix x)))
    (ODEHermitianReduction.hamiltonianPart (SparseStateOverlap.matrixOperator (D.matrix x)))
    u w k

/-- Native positive dissipative matrices have integrable shifted residuals. -/
theorem native_weighted_integrable
    (D : NativeSparseBlockEncoding.Data X n Z s) (x : X)
    (hPSD : ∀ v : EuclideanSpace ℂ n, 0 ≤ (inner ℂ v
      (SparseStateOverlap.matrixOperator (ODEMatrixEnergy.dissipativePart (D.matrix x)) v)).re)
    (u w : ℝ) (hu : 0 ≤ u) (hw : 1 ≤ w) :
    Integrable (nativeWeighted D x u w) := by
  apply weighted_integrable
    (ODEHermitianReduction.dissipativePart (SparseStateOverlap.matrixOperator (D.matrix x)))
    (ODEHermitianReduction.hamiltonianPart (SparseStateOverlap.matrixOperator (D.matrix x)))
    (ODEHermitianReduction.dissipativePart_selfAdjoint _)
    (ODEHermitianReduction.hamiltonianPart_selfAdjoint _) _ u w hu hw
  intro v
  simpa only [ODEMatrixEnergy.matrixOperator_dissipativePart] using hPSD v

/-- Uniform shifted residual estimate for the native sparse-data family. -/
theorem native_integral_norm_le
    (D : NativeSparseBlockEncoding.Data X n Z s) (x : X)
    (hPSD : ∀ v : EuclideanSpace ℂ n, 0 ≤ (inner ℂ v
      (SparseStateOverlap.matrixOperator (ODEMatrixEnergy.dissipativePart (D.matrix x)) v)).re)
    (u w : ℝ) (hu : 0 ≤ u) (hw : 1 ≤ w) :
    ‖∫ k : ℝ, nativeWeighted D x u w k‖ ≤ Real.exp (1 - w) := by
  apply integral_norm_le
    (ODEHermitianReduction.dissipativePart (SparseStateOverlap.matrixOperator (D.matrix x)))
    (ODEHermitianReduction.hamiltonianPart (SparseStateOverlap.matrixOperator (D.matrix x)))
    (ODEHermitianReduction.dissipativePart_selfAdjoint _)
    (ODEHermitianReduction.hamiltonianPart_selfAdjoint _) _ u w hu hw
  intro v
  simpa only [ODEMatrixEnergy.matrixOperator_dissipativePart] using hPSD v

end Native
end
end SparseHamiltonian.ODEGaussianShiftedIntegral
