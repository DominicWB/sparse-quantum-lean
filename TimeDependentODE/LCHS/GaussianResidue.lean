import TimeDependentODE.LCHS.GaussianIntegrands

/-!
# Pole removal, residue and vanishing vertical edges for a generic family

For an entire operator-valued `F`, the Gaussian contour integrand
`ODEGaussianComplex.kernel w z • F z` has a simple pole at `-I` (inside the
lower contour rectangle) and another at `I`. Writing it as a pole quotient of
`weightedRegular F w z = regularizedFactor w z • F z`, this file proves:

* `weightedRegular F w` is analytic on `Im z < 1`, and its divided difference
  at `-I` (the removed-pole integrand) is complex differentiable there
  (`regularized_differentiableOn`), via the removable-singularity theorem;
* the residue coefficient is exactly `I / (2π) • F (-I)`
  (`weightedRegular_neg_I`); no special form of `F (-I)` is used;
* lower-half-plane contractivity bounds the removed-pole integrand on the
  vertical edges, so by Cauchy-Goursat the difference of its two horizontal
  integrals over `[-R, R]` tends to zero as `R → ∞`
  (`horizontal_difference_tendsto_zero`).

These are generic copies of the operator-valued parts of
`SparseODE.ODEGaussianAnalytic`, `SparseODE.ODEGaussianResidue` and
`SparseODE.ODEGaussianEdges`, with the specific propagator replaced by `F`.
-/

namespace SparseHamiltonian.TimeDependentODE.GaussianLCHS

noncomputable section
open Filter
open scoped Topology Interval

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

section Regular

/-- Operator-valued analytic factor of the pole quotient: the Gaussian
numerator over the upper pole factor, times the generic family. -/
def weightedRegular (F : ℂ → V →L[ℂ] V) (w : ℝ) (z : ℂ) : V →L[ℂ] V :=
  ODEGaussianAnalytic.regularizedFactor w z • F z

/-- Multiplication by the entire family preserves analyticity away from the
upper pole. -/
theorem weightedRegular_analyticAt (F : ℂ → V →L[ℂ] V)
    (hF : ∀ z, AnalyticAt ℂ F z) (w : ℝ) (z : ℂ) (hz : z ≠ Complex.I) :
    AnalyticAt ℂ (weightedRegular F w) z :=
  (ODEGaussianAnalytic.regularizedFactor_analyticAt w z hz).smul (hF z)

/-- Every point strictly below the upper pole has a neighbourhood on which
the regularized operator factor is analytic. -/
theorem weightedRegular_analyticOnNhd (F : ℂ → V →L[ℂ] V)
    (hF : ∀ z, AnalyticAt ℂ F z) (w : ℝ) :
    AnalyticOnNhd ℂ (weightedRegular F w) {z : ℂ | z.im < 1} := by
  intro z hz
  apply weightedRegular_analyticAt F hF w z
  intro h
  have hIm : z.im = 1 := by
    simpa only [Complex.I_im] using congrArg Complex.im h
  change z.im < 1 at hz
  linarith

theorem weightedRegular_differentiableOn (F : ℂ → V →L[ℂ] V)
    (hF : ∀ z, AnalyticAt ℂ F z) (w : ℝ) :
    DifferentiableOn ℂ (weightedRegular F w) {z : ℂ | z.im < 1} :=
  (weightedRegular_analyticOnNhd F hF w).differentiableOn

/-- The Gaussian-weighted family has the single-pole form at `-I`. -/
theorem weighted_eq_poleQuotient (F : ℂ → V →L[ℂ] V) (w : ℝ) (z : ℂ) :
    ODEGaussianComplex.kernel w z • F z =
      ODEContourRectangle.poleQuotient (weightedRegular F w) (-Complex.I) z := by
  rw [ODEGaussianResidue.kernel_factorization]
  exact (smul_smul _ _ _).symm

/-- The residue coefficient at the lower pole is `I/(2π)` times `F (-I)`. -/
theorem weightedRegular_neg_I (F : ℂ → V →L[ℂ] V) (w : ℝ) :
    weightedRegular F w (-Complex.I) =
      (Complex.I / (2 * (Real.pi : ℂ))) • F (-Complex.I) := by
  rw [weightedRegular, ODEGaussianResidue.regularizedFactor_neg_I]

/-- Away from the lower pole, the Gaussian integrand decomposes into the
removable divided difference and its explicit principal part. -/
theorem weighted_pole_decomposition (F : ℂ → V →L[ℂ] V) (w : ℝ) (z : ℂ)
    (hz : z ≠ -Complex.I) :
    ODEGaussianComplex.kernel w z • F z =
      dslope (weightedRegular F w) (-Complex.I) z +
        ODEContourRectangle.principalPart
          ((Complex.I / (2 * (Real.pi : ℂ))) • F (-Complex.I)) (-Complex.I) z := by
  rw [weighted_eq_poleQuotient, ODEContourRectangle.pole_decomposition _ _ _ hz,
    weightedRegular_neg_I]

/-- After pole subtraction the integrand is holomorphic on the half-plane
below the upper pole, including the filled-in point `-I`. -/
theorem regularized_differentiableOn [CompleteSpace V] (F : ℂ → V →L[ℂ] V)
    (hF : ∀ z, AnalyticAt ℂ F z) (w : ℝ) :
    DifferentiableOn ℂ (dslope (weightedRegular F w) (-Complex.I))
      {z : ℂ | z.im < 1} := by
  have hOpen : IsOpen {z : ℂ | z.im < 1} :=
    isOpen_lt Complex.continuous_im continuous_const
  have hc : {z : ℂ | z.im < 1} ∈ nhds (-Complex.I) :=
    hOpen.mem_nhds (by norm_num)
  exact ODEContourRectangle.regularized_differentiableOn _ _ _ hc
    (weightedRegular_differentiableOn F hF w)

end Regular

section Edges

/-- Subtracting the residue leaves an explicit bound throughout the lower
strip `-2 w ≤ Im z ≤ 0`, away from the imaginary axis. -/
theorem regularized_norm_le (F : ℂ → V →L[ℂ] V)
    (hBound : ∀ z : ℂ, z.im ≤ 0 → ‖F z‖ ≤ 1) (w x y : ℝ) (hw : 0 < w)
    (hx : x ≠ 0) (hLower : -2 * w ≤ y) (hUpper : y ≤ 0) :
    ‖dslope (weightedRegular F w) (-Complex.I)
        ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤
      Real.exp 1 / (Real.pi * x ^ 2) +
        ‖weightedRegular F w (-Complex.I)‖ / |x| := by
  rw [ODEContourRectangle.regularized_eq_sub _ _ _
      (ODEGaussianEdges.point_ne_lower_pole x y hx),
    ← weighted_eq_poleQuotient]
  exact (norm_sub_le _ _).trans
    (add_le_add (vertical_weighted_norm_le F hBound w x y hw hx hLower hUpper)
      (ODEGaussianEdges.principalPart_norm_le
        (weightedRegular F w (-Complex.I)) x y hx))

/-- Quantitative disappearance of the two vertical edges on a finite
symmetric rectangle. -/
theorem horizontal_difference_norm_le [CompleteSpace V] (F : ℂ → V →L[ℂ] V)
    (hF : ∀ z, AnalyticAt ℂ F z) (hBound : ∀ z : ℂ, z.im ≤ 0 → ‖F z‖ ≤ 1)
    (w R : ℝ) (hw : 0 < w) (hR : 0 < R) :
    ‖ODEContourRectangle.horizontal
        (dslope (weightedRegular F w) (-Complex.I)) (-R) R 0 -
      ODEContourRectangle.horizontal
        (dslope (weightedRegular F w) (-Complex.I)) (-R) R (-2 * w)‖ ≤
      4 * w * (Real.exp 1 / (Real.pi * R ^ 2) +
        ‖weightedRegular F w (-Complex.I)‖ / R) := by
  let f := dslope (weightedRegular F w) (-Complex.I)
  let C : ℝ := Real.exp 1 / (Real.pi * R ^ 2) +
    ‖weightedRegular F w (-Complex.I)‖ / R
  have hOrder : -2 * w ≤ 0 := by linarith
  have hf : DifferentiableOn ℂ f
      (Complex.reProdIm (Set.uIcc (-R) R) (Set.uIcc (-2 * w) 0)) := by
    apply (regularized_differentiableOn F hF w).mono
    intro z hz
    have hzIm : z.im ∈ Set.Icc (-2 * w) 0 := by
      simpa only [Set.mem_preimage, Set.uIcc_of_le hOrder] using hz.2
    exact lt_of_le_of_lt hzIm.2 (by norm_num)
  have hSide (x : ℝ) (hx : x ≠ 0) (hAbs : |x| = R) (hSq : x ^ 2 = R ^ 2) :
      ∀ y ∈ Set.uIoc (-2 * w) 0,
        ‖f ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤ C := by
    intro y hy
    have hy' : y ∈ Set.Ioc (-2 * w) 0 := by
      simpa only [Set.uIoc_of_le hOrder] using hy
    simpa only [f, C, hAbs, hSq] using
      regularized_norm_le F hBound w x y hw hx hy'.1.le hy'.2
  have h := ODEContourRectangle.horizontal_difference_norm_le f
    (⟨-R, -2 * w⟩ : ℂ) (⟨R, 0⟩ : ℂ) C C hf
    (hSide (-R) (neg_ne_zero.mpr hR.ne')
      (by rw [abs_neg, abs_of_pos hR]) (by rw [neg_sq]))
    (hSide R hR.ne' (abs_of_pos hR) rfl)
  calc
    _ = ‖ODEContourRectangle.horizontal f (-R) R (-2 * w) -
        ODEContourRectangle.horizontal f (-R) R 0‖ := norm_sub_rev _ _
    _ ≤ (C + C) * |0 - (-2 * w)| := h
    _ = _ := by
      rw [abs_of_nonneg (by linarith : 0 ≤ 0 - (-2 * w))]
      dsimp only [C]
      ring

/-- The horizontal integrals of the removed-pole family have vanishing
difference on expanding symmetric rectangles. -/
theorem horizontal_difference_tendsto_zero [CompleteSpace V]
    (F : ℂ → V →L[ℂ] V) (hF : ∀ z, AnalyticAt ℂ F z)
    (hBound : ∀ z : ℂ, z.im ≤ 0 → ‖F z‖ ≤ 1) (w : ℝ) (hw : 0 < w) :
    Tendsto (fun R : ℝ =>
      ODEContourRectangle.horizontal
        (dslope (weightedRegular F w) (-Complex.I)) (-R) R 0 -
      ODEContourRectangle.horizontal
        (dslope (weightedRegular F w) (-Complex.I)) (-R) R (-2 * w))
      atTop (𝓝 0) := by
  refine squeeze_zero_norm' ?_
    (ODEGaussianEdges.edge_bound_tendsto_zero w
      ‖weightedRegular F w (-Complex.I)‖)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  exact horizontal_difference_norm_le F hF hBound w R hw hR

end Edges

end
end SparseHamiltonian.TimeDependentODE.GaussianLCHS
