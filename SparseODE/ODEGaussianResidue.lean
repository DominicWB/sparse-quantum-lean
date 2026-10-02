import SparseODE.ODEContourRectangle

/-!
# Gaussian pole factor and the actual ODE residue

The analytic numerator used in the rectangle argument is derived from the
actual Gaussian-weighted operator family. Its value at the lower pole is
exactly I/(2*pi) times the dissipative propagator. This section does not
assert the infinite-contour limit or the final full-line LCHS identity.

-/

namespace SparseHamiltonian.ODEGaussianResidue

noncomputable section
open scoped Topology

/-- Factorization of the two simple poles of the scalar Cauchy denominator. -/
theorem denominator_factorization (z : ℂ) :
    1 + z ^ 2 = (z - Complex.I) * (z + Complex.I) := by
  calc
    _ = z ^ 2 - Complex.I * Complex.I := by rw [Complex.I_mul_I]; ring
    _ = _ := by ring

/-- The meromorphic Gaussian kernel is a single-pole quotient of the
regular factor used by the removable-singularity theorem. -/
theorem kernel_factorization (w : ℝ) (z : ℂ) :
    ODEGaussianComplex.kernel w z =
      (z - (-Complex.I))⁻¹ * ODEGaussianAnalytic.regularizedFactor w z := by
  unfold ODEGaussianComplex.kernel ODEGaussianAnalytic.regularizedFactor
  rw [denominator_factorization]
  simp only [sub_neg_eq_add, div_eq_mul_inv, mul_inv_rev]
  ring

/-- Exact scalar coefficient at the enclosed pole; its sign corresponds to
the clockwise downward rectangle. -/
theorem regularizedFactor_neg_I (w : ℝ) :
    ODEGaussianAnalytic.regularizedFactor w (-Complex.I) =
      Complex.I / (2 * (Real.pi : ℂ)) := by
  rw [ODEGaussianAnalytic.regularizedFactor, ODEGaussianComplex.numerator_neg_I]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hminus : (-Complex.I - Complex.I : ℂ) ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    norm_num at hi
  apply (div_eq_div_iff (mul_ne_zero hpi hminus)
    (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) hpi)).mpr
  calc
    _ = 2 * (Real.pi : ℂ) := by ring
    _ = -2 * (Real.pi : ℂ) * (Complex.I * Complex.I) := by
      rw [Complex.I_mul_I]
      ring
    _ = _ := by ring

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [CompleteSpace V]

omit [CompleteSpace V] in
/-- The actual weighted operator family has the required single-pole form. -/
theorem weighted_eq_poleQuotient (D H : V →L[ℂ] V) (u w : ℝ) (z : ℂ) :
    ODEGaussianComplex.kernel w z • ODEComplexFrequency.evolution D H u z =
      ODEContourRectangle.poleQuotient
        (ODEGaussianAnalytic.weightedRegular D H u w) (-Complex.I) z := by
  rw [kernel_factorization]
  exact (smul_smul _ _ _).symm

omit [CompleteSpace V] in
/-- The removed principal part has the actual ODE propagator as its residue
coefficient, with the explicit scalar normalization. -/
theorem weightedRegular_neg_I (D H : V →L[ℂ] V) (u w : ℝ) :
    ODEGaussianAnalytic.weightedRegular D H u w (-Complex.I) =
      (Complex.I / (2 * (Real.pi : ℂ))) •
        NormedSpace.exp (u • (-(D + Complex.I • H))) := by
  rw [ODEGaussianAnalytic.weightedRegular, regularizedFactor_neg_I,
    ODEComplexFrequency.evolution_neg_I]

/-- For the Hermitian parts of an arbitrary matrix operator the residue is
exactly the desired constant-coefficient dissipative evolution. -/
theorem parts_weightedRegular_neg_I (M : V →L[ℂ] V) (u w : ℝ) :
    ODEGaussianAnalytic.weightedRegular
      (ODEHermitianReduction.dissipativePart M)
      (ODEHermitianReduction.hamiltonianPart M) u w (-Complex.I) =
      (Complex.I / (2 * (Real.pi : ℂ))) • NormedSpace.exp (u • (-M)) := by
  rw [weightedRegular_neg_I, ODEHermitianReduction.decomposition]

omit [CompleteSpace V] in
/-- Away from the lower pole, the actual Gaussian integrand decomposes into
the removable divided difference and its explicitly identified residue. -/
theorem weighted_pole_decomposition (D H : V →L[ℂ] V) (u w : ℝ) (z : ℂ)
    (hz : z ≠ -Complex.I) :
    ODEGaussianComplex.kernel w z • ODEComplexFrequency.evolution D H u z =
      dslope (ODEGaussianAnalytic.weightedRegular D H u w) (-Complex.I) z +
        ODEContourRectangle.principalPart
          ((Complex.I / (2 * (Real.pi : ℂ))) •
            NormedSpace.exp (u • (-(D + Complex.I • H)))) (-Complex.I) z := by
  rw [weighted_eq_poleQuotient,
    ODEContourRectangle.pole_decomposition _ _ _ hz,
    weightedRegular_neg_I]

/-- The actual Gaussian integrand after pole subtraction is holomorphic on
the full half-plane needed by every downward rectangle. -/
theorem regularized_differentiableOn (D H : V →L[ℂ] V) (u w : ℝ) :
    DifferentiableOn ℂ
      (dslope (ODEGaussianAnalytic.weightedRegular D H u w) (-Complex.I))
      {z : ℂ | z.im < 1} := by
  have hOpen : IsOpen {z : ℂ | z.im < 1} :=
    isOpen_lt Complex.continuous_im continuous_const
  have hc : {z : ℂ | z.im < 1} ∈ nhds (-Complex.I) :=
    hOpen.mem_nhds (by norm_num)
  exact ODEContourRectangle.regularized_differentiableOn _ _ _ hc
    (ODEGaussianAnalytic.weightedRegular_differentiableOn D H u w)

/-- Every rectangle below the upper pole has the exact zero-boundary
identity for the actual regularized Gaussian operator family. All
holomorphy and removable-pole obligations are derived here. -/
theorem regularized_boundary_eq_zero (D H : V →L[ℂ] V) (u w : ℝ)
    (z ζ : ℂ) (hz : z.im < 1) (hζ : ζ.im < 1) :
    ODEContourRectangle.boundary
      (dslope (ODEGaussianAnalytic.weightedRegular D H u w) (-Complex.I)) z ζ = 0 := by
  apply ODEContourRectangle.boundary_eq_zero
  apply (regularized_differentiableOn D H u w).mono
  intro ξ hξ
  have him : ξ.im ∈ Set.uIcc z.im ζ.im := hξ.2
  have hUpper : ξ.im ≤ max z.im ζ.im := him.2
  exact lt_of_le_of_lt hUpper (max_lt_iff.mpr ⟨hz, hζ⟩)

end
end SparseHamiltonian.ODEGaussianResidue
