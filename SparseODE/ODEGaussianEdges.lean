import SparseODE.ODEGaussianLimits

/-!
# Vanishing vertical edges after pole subtraction

The actual regularized Gaussian operator family is bounded on a vertical
edge by the Gaussian bound plus the explicitly removed principal part.
Cauchy-Goursat then bounds the difference of its two horizontal integrals.
That difference tends to zero as the real cutoff tends to positive infinity.

-/

namespace SparseHamiltonian.ODEGaussianEdges

noncomputable section
open Filter
open scoped Topology Interval InnerProduct

section PrincipalPart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- A nonzero real coordinate separates a vertical edge from the lower pole. -/
theorem point_ne_lower_pole (x y : ℝ) (hx : x ≠ 0) :
    (x : ℂ) + (y : ℂ) * Complex.I ≠ -Complex.I := by
  intro h
  apply hx
  simpa using congrArg Complex.re h

omit [CompleteSpace E] in
/-- The principal part decays reciprocally in the real coordinate,
uniformly in the height of the vertical edge. -/
theorem principalPart_norm_le (a : E) (x y : ℝ) (hx : x ≠ 0) :
    ‖ODEContourRectangle.principalPart a (-Complex.I)
        ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤ ‖a‖ / |x| := by
  have hLower : |x| ≤
      ‖((x : ℂ) + (y : ℂ) * Complex.I) - (-Complex.I)‖ := by
    simpa using Complex.abs_re_le_norm
      (((x : ℂ) + (y : ℂ) * Complex.I) - (-Complex.I))
  rw [ODEContourRectangle.principalPart, norm_smul, norm_inv]
  calc
    _ = ‖a‖ / ‖((x : ℂ) + (y : ℂ) * Complex.I) - (-Complex.I)‖ := by
      rw [div_eq_mul_inv, mul_comm]
    _ ≤ ‖a‖ / |x| :=
      div_le_div_of_nonneg_left (norm_nonneg a) (abs_pos.mpr hx) hLower

end PrincipalPart

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [CompleteSpace V]

/-- Subtracting the actual pole residue leaves an explicit bound throughout
the lower strip. No bound on an unspecified analytic family is assumed. -/
theorem regularized_norm_le (D H : V →L[ℂ] V)
    (hD : star D = D) (hH : star H = H)
    (hPSD : ∀ v : V, 0 ≤ (inner ℂ v (D v)).re)
    (u : ℝ) (hu : 0 ≤ u) (w x y : ℝ) (hw : 0 < w) (hx : x ≠ 0)
    (hLower : -2 * w ≤ y) (hUpper : y ≤ 0) :
    ‖dslope (ODEGaussianAnalytic.weightedRegular D H u w) (-Complex.I)
        ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤
      Real.exp 1 / (Real.pi * x ^ 2) +
        ‖ODEGaussianAnalytic.weightedRegular D H u w (-Complex.I)‖ / |x| := by
  rw [ODEContourRectangle.regularized_eq_sub _ _ _ (point_ne_lower_pole x y hx),
    ← ODEGaussianResidue.weighted_eq_poleQuotient]
  exact (norm_sub_le _ _).trans
    (add_le_add (ODEGaussianVertical.weighted_norm_le D H hD hH hPSD
        u hu w x y hw hx hLower hUpper)
      (principalPart_norm_le
        (ODEGaussianAnalytic.weightedRegular D H u w (-Complex.I)) x y hx))

/-- Quantitative disappearance of the two vertical edges for the actual
regularized Gaussian integrand on a finite symmetric rectangle. -/
theorem horizontal_difference_norm_le (D H : V →L[ℂ] V)
    (hD : star D = D) (hH : star H = H)
    (hPSD : ∀ v : V, 0 ≤ (inner ℂ v (D v)).re)
    (u : ℝ) (hu : 0 ≤ u) (w R : ℝ) (hw : 0 < w) (hR : 0 < R) :
    ‖ODEContourRectangle.horizontal
        (dslope (ODEGaussianAnalytic.weightedRegular D H u w) (-Complex.I))
        (-R) R 0 -
      ODEContourRectangle.horizontal
        (dslope (ODEGaussianAnalytic.weightedRegular D H u w) (-Complex.I))
        (-R) R (-2 * w)‖ ≤
      4 * w * (Real.exp 1 / (Real.pi * R ^ 2) +
        ‖ODEGaussianAnalytic.weightedRegular D H u w (-Complex.I)‖ / R) := by
  let f := dslope (ODEGaussianAnalytic.weightedRegular D H u w) (-Complex.I)
  let C : ℝ := Real.exp 1 / (Real.pi * R ^ 2) +
    ‖ODEGaussianAnalytic.weightedRegular D H u w (-Complex.I)‖ / R
  have hOrder : -2 * w ≤ 0 := by linarith
  have hf : DifferentiableOn ℂ f
      (Complex.reProdIm (Set.uIcc (-R) R) (Set.uIcc (-2 * w) 0)) := by
    apply (ODEGaussianResidue.regularized_differentiableOn D H u w).mono
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
    simpa only [f, C, hAbs, hSq] using regularized_norm_le D H hD hH hPSD
      u hu w x y hw hx hy'.1.le hy'.2
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

/-- The explicit edge bound tends to zero at a real cutoff tending to infinity. -/
theorem edge_bound_tendsto_zero (w C : ℝ) :
    Tendsto (fun R : ℝ =>
      4 * w * (Real.exp 1 / (Real.pi * R ^ 2) + C / R)) atTop (𝓝 0) := by
  have hInv : Tendsto (fun R : ℝ => R⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hSquare : Tendsto (fun R : ℝ => (R⁻¹) ^ 2) atTop (𝓝 0) := by
    simpa using hInv.pow 2
  have hGaussian : Tendsto (fun R : ℝ =>
      (Real.exp 1 / Real.pi) * (R⁻¹) ^ 2) atTop (𝓝 0) := by
    simpa using hSquare.const_mul (Real.exp 1 / Real.pi)
  have hPrincipal : Tendsto (fun R : ℝ => C * R⁻¹) atTop (𝓝 0) := by
    simpa using hInv.const_mul C
  have hSum := (hGaussian.add hPrincipal).const_mul (4 * w)
  have hEq : (fun R : ℝ =>
      4 * w * (Real.exp 1 / (Real.pi * R ^ 2) + C / R)) =
      (fun R : ℝ =>
        4 * w * ((Real.exp 1 / Real.pi) * (R⁻¹) ^ 2 + C * R⁻¹)) := by
    funext R
    simp only [div_eq_mul_inv, mul_inv_rev, inv_pow] ; ring
  rw [hEq]
  simpa using hSum

/-- The horizontal integrals of the actual regularized Gaussian family
have vanishing difference on expanding symmetric rectangles. -/
theorem horizontal_difference_tendsto_zero (D H : V →L[ℂ] V)
    (hD : star D = D) (hH : star H = H)
    (hPSD : ∀ v : V, 0 ≤ (inner ℂ v (D v)).re)
    (u : ℝ) (hu : 0 ≤ u) (w : ℝ) (hw : 0 < w) :
    Tendsto (fun R : ℝ =>
      ODEContourRectangle.horizontal
        (dslope (ODEGaussianAnalytic.weightedRegular D H u w) (-Complex.I))
        (-R) R 0 -
      ODEContourRectangle.horizontal
        (dslope (ODEGaussianAnalytic.weightedRegular D H u w) (-Complex.I))
        (-R) R (-2 * w)) atTop (𝓝 0) := by
  refine squeeze_zero_norm' ?_
    (edge_bound_tendsto_zero w
      ‖ODEGaussianAnalytic.weightedRegular D H u w (-Complex.I)‖)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  exact horizontal_difference_norm_le D H hD hH hPSD u hu w R hw hR

end
end SparseHamiltonian.ODEGaussianEdges
