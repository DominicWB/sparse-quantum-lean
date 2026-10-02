import SparseODE.ODEGaussianFiniteContour

/-!
# Full-line Gaussian LCHS identity and its actual residual

Finite rectangles, the reciprocal-line limits and Gaussian integrability
identify the full-line operator integral. The shifted residual is already
bounded by exp (1-w). No contour identity or approximation is assumed.

-/

namespace SparseHamiltonian.ODEGaussianFull

noncomputable section
open Filter MeasureTheory
open scoped Interval Topology InnerProduct

/-- Clockwise lower-half-plane orientation cancels the residue coefficient. -/
theorem residue_scalar_normalization :
    ((-2 : ℂ) * (Real.pi : ℂ) * Complex.I) *
      (Complex.I / (2 * (Real.pi : ℂ))) = 1 := by
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hden : 2 * (Real.pi : ℂ) ≠ 0 := mul_ne_zero (by norm_num) hπ
  calc
    _ = (((-2 : ℂ) * (Real.pi : ℂ)) * (Complex.I * Complex.I)) /
        (2 * (Real.pi : ℂ)) := by ring
    _ = (2 * (Real.pi : ℂ)) / (2 * (Real.pi : ℂ)) := by
      rw [Complex.I_mul_I]
      ring
    _ = 1 := div_self hden

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [CompleteSpace V]

omit [CompleteSpace V] in
/-- The limiting principal contribution is exactly the ODE propagator. -/
theorem residue_normalization (D H : V →L[ℂ] V) (u w : ℝ) :
    ((-2 : ℂ) * (Real.pi : ℂ) * Complex.I) •
      ODEGaussianAnalytic.weightedRegular D H u w (-Complex.I) =
        NormedSpace.exp (u • (-(D + Complex.I • H))) := by
  rw [ODEGaussianResidue.weightedRegular_neg_I, smul_smul,
    residue_scalar_normalization, one_smul]

/-- The finite Gaussian contour differences converge to the actual ODE
propagator. All estimates and principal-part integrals are derived. -/
theorem finite_difference_tendsto (D H : V →L[ℂ] V)
    (hD : star D = D) (hH : star H = H)
    (hPSD : ∀ v : V, 0 ≤ (inner ℂ v (D v)).re)
    (u w : ℝ) (hu : 0 ≤ u) (hw : 1 ≤ w) :
    Tendsto (fun R : ℝ =>
      (∫ k in (-R)..R, ODEGaussianLimits.topWeighted D H u w k) -
        (∫ k in (-R)..R, ODEGaussianShiftedIntegral.weighted D H u w k))
      atTop (nhds (NormedSpace.exp (u • (-(D + Complex.I • H))))) := by
  have hwPos : 0 < w := by linarith
  have hEdges := ODEGaussianEdges.horizontal_difference_tendsto_zero
    D H hD hH hPSD u hu w hwPos
  have hPrincipal := ODEReciprocalLine.horizontal_difference_tendsto w hw
  have hConstant : Tendsto
      (fun _ : ℝ => ODEGaussianAnalytic.weightedRegular D H u w (-Complex.I))
      atTop (nhds (ODEGaussianAnalytic.weightedRegular D H u w (-Complex.I))) :=
    tendsto_const_nhds
  have hLimit := hEdges.add (hPrincipal.smul hConstant)
  have hEq : (fun R : ℝ =>
      (∫ k in (-R)..R, ODEGaussianLimits.topWeighted D H u w k) -
        (∫ k in (-R)..R, ODEGaussianShiftedIntegral.weighted D H u w k)) =
      (fun R : ℝ =>
        (ODEContourRectangle.horizontal
            (dslope (ODEGaussianAnalytic.weightedRegular D H u w) (-Complex.I))
            (-R) R 0 -
          ODEContourRectangle.horizontal
            (dslope (ODEGaussianAnalytic.weightedRegular D H u w) (-Complex.I))
            (-R) R (-2 * w)) +
        ((∫ k in (-R)..R, ODEReciprocalLine.reciprocal 1 k) -
          (∫ k in (-R)..R, ODEReciprocalLine.reciprocal (1 - 2 * w) k)) •
          ODEGaussianAnalytic.weightedRegular D H u w (-Complex.I)) := by
    funext R
    exact ODEGaussianFiniteContour.horizontal_difference D H u w R hw
  rw [hEq]
  simpa only [zero_add, residue_normalization] using hLimit

/-- Uniqueness of the operator-valued limit gives the full-line Gaussian
identity, including its explicit shifted residual. -/
theorem integral_difference_eq (D H : V →L[ℂ] V)
    (hD : star D = D) (hH : star H = H)
    (hPSD : ∀ v : V, 0 ≤ (inner ℂ v (D v)).re)
    (u w : ℝ) (hu : 0 ≤ u) (hw : 1 ≤ w) :
    (∫ k : ℝ, ODEGaussianLimits.topWeighted D H u w k) -
        (∫ k : ℝ, ODEGaussianShiftedIntegral.weighted D H u w k) =
      NormedSpace.exp (u • (-(D + Complex.I • H))) := by
  exact tendsto_nhds_unique
    (ODEGaussianLimits.horizontal_difference_tendsto D H hD hH hPSD u w hu hw)
    (finite_difference_tendsto D H hD hH hPSD u w hu hw)

/-- The error of the full real-frequency integral is the actual shifted
Gaussian integral, rather than an assumed approximation certificate. -/
theorem full_line_error_eq_residual (D H : V →L[ℂ] V)
    (hD : star D = D) (hH : star H = H)
    (hPSD : ∀ v : V, 0 ≤ (inner ℂ v (D v)).re)
    (u w : ℝ) (hu : 0 ≤ u) (hw : 1 ≤ w) :
    (∫ k : ℝ, ODEGaussianLimits.topWeighted D H u w k) -
        NormedSpace.exp (u • (-(D + Complex.I • H))) =
      (∫ k : ℝ, ODEGaussianShiftedIntegral.weighted D H u w k) := by
  apply sub_eq_iff_eq_add.mpr
  rw [add_comm]
  exact sub_eq_iff_eq_add.mp (integral_difference_eq D H hD hH hPSD u w hu hw)

/-- The full-line LCHS error bound follows only from self-adjointness,
positive dissipative part, nonnegative duration and the public width. -/
theorem full_line_error (D H : V →L[ℂ] V)
    (hD : star D = D) (hH : star H = H)
    (hPSD : ∀ v : V, 0 ≤ (inner ℂ v (D v)).re)
    (u w : ℝ) (hu : 0 ≤ u) (hw : 1 ≤ w) :
    ‖(∫ k : ℝ, ODEGaussianLimits.topWeighted D H u w k) -
        NormedSpace.exp (u • (-(D + Complex.I • H)))‖ ≤ Real.exp (1 - w) := by
  rw [full_line_error_eq_residual D H hD hH hPSD u w hu hw]
  exact ODEGaussianShiftedIntegral.integral_norm_le D H hD hH hPSD u w hu hw

section Native

variable {X n Z : Type*} [Fintype n] [DecidableEq n] {s : ℕ}

/-- Native real-frequency branches agree pointwise with the contour's
upper integrand for the actual Hermitian parts of the matrix oracle. -/
theorem nativeWeighted_eq_topWeighted
    (D : NativeSparseBlockEncoding.Data X n Z s) (x : X) (u w k : ℝ) :
    ODEWeightedLCHS.nativeWeighted D x u (ODEGaussianKernel.kernel w) k =
      ODEGaussianLimits.topWeighted
        (ODEHermitianReduction.dissipativePart (SparseStateOverlap.matrixOperator (D.matrix x)))
        (ODEHermitianReduction.hamiltonianPart (SparseStateOverlap.matrixOperator (D.matrix x)))
        u w k := by
  unfold ODEWeightedLCHS.nativeWeighted ODEGaussianLimits.topWeighted
  rw [ODEWeightedLCHS.nativeEvolution_eq_evolution]

/-- The full-line approximation needed by the public finite table is
derived directly from the original matrix's positive dissipative part. -/
theorem native_full_line_error
    (D : NativeSparseBlockEncoding.Data X n Z s) (x : X)
    (hPSD : ∀ v : EuclideanSpace ℂ n, 0 ≤ (inner ℂ v
      (SparseStateOverlap.matrixOperator (ODEMatrixEnergy.dissipativePart (D.matrix x)) v)).re)
    (u w : ℝ) (hu : 0 ≤ u) (hw : 1 ≤ w) :
    ‖(∫ k : ℝ, ODEWeightedLCHS.nativeWeighted D x u (ODEGaussianKernel.kernel w) k) -
        NormedSpace.exp (u • ODEPublicSourceMesh.generator D x)‖ ≤ Real.exp (1 - w) := by
  have hPositive : ∀ v : EuclideanSpace ℂ n, 0 ≤ (inner ℂ v
      (ODEHermitianReduction.dissipativePart
        (SparseStateOverlap.matrixOperator (D.matrix x)) v)).re := by
    intro v
    simpa only [ODEMatrixEnergy.matrixOperator_dissipativePart] using hPSD v
  have h := full_line_error
    (ODEHermitianReduction.dissipativePart (SparseStateOverlap.matrixOperator (D.matrix x)))
    (ODEHermitianReduction.hamiltonianPart (SparseStateOverlap.matrixOperator (D.matrix x)))
    (ODEHermitianReduction.dissipativePart_selfAdjoint _)
    (ODEHermitianReduction.hamiltonianPart_selfAdjoint _) hPositive u w hu hw
  simpa only [nativeWeighted_eq_topWeighted, ODEHermitianReduction.decomposition,
    ODEPublicSourceMesh.generator] using h

end Native
end
end SparseHamiltonian.ODEGaussianFull
