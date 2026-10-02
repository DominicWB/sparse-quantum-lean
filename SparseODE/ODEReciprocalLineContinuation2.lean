import SparseODE.ODEReciprocalLine

/-!
# Symmetric limits of the scalar principal part

The reciprocal line is not absolutely integrable on the real axis.  All
limits here are limits of symmetric finite-interval integrals.  Their
values follow from the exact arctangent formula and the sign of the pole
height.  The top-minus-bottom limit has the clockwise orientation -2*pi*I.

-/

namespace SparseHamiltonian.ODEReciprocalLine

noncomputable section
open Filter
open scoped Topology Interval

/-- A positive vertical displacement gives the upper arctangent endpoint. -/
theorem arctan_div_tendsto_pos (b : ℝ) (hb : 0 < b) :
    Tendsto (fun R : ℝ => Real.arctan (R / b)) atTop
      (𝓝 (Real.pi / 2)) := by
  have hdiv : Tendsto (fun R : ℝ => R / b) atTop atTop := by
    apply tendsto_atTop.2
    intro c
    filter_upwards [eventually_ge_atTop (c * b)] with R hR
    exact (le_div_iff₀ hb).mpr hR
  have hArctan : Tendsto Real.arctan atTop (𝓝 (Real.pi / 2)) :=
    Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds
  exact hArctan.comp hdiv

/-- A negative displacement gives the lower endpoint, by oddness. -/
theorem arctan_div_tendsto_neg (b : ℝ) (hb : b < 0) :
    Tendsto (fun R : ℝ => Real.arctan (R / b)) atTop
      (𝓝 (-(Real.pi / 2))) := by
  have h := (arctan_div_tendsto_pos (-b) (neg_pos.mpr hb)).neg
  simpa only [div_neg, Real.arctan_neg, neg_neg] using h

/-- Symmetric principal-part integral above the pole.  This statement does
not assert whole-line Bochner integrability of the reciprocal. -/
theorem integral_symm_tendsto_pos (b : ℝ) (hb : 0 < b) :
    Tendsto (fun R : ℝ => ∫ x in (-R)..R, reciprocal b x) atTop
      (𝓝 (-(Real.pi : ℂ) * Complex.I)) := by
  have hArctan :
      Tendsto (fun R : ℝ => (Real.arctan (R / b) : ℂ)) atTop
        (𝓝 ((Real.pi / 2 : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp
      (arctan_div_tendsto_pos b hb)
  have hFormula :
      (fun R : ℝ => ∫ x in (-R)..R, reciprocal b x) =
        (fun R : ℝ => (-2 : ℂ) * Complex.I * (Real.arctan (R / b) : ℂ)) := by
    funext R
    exact integral_symm b R hb.ne'
  have hLimit :
      (-2 : ℂ) * Complex.I * ((Real.pi / 2 : ℝ) : ℂ) =
        -(Real.pi : ℂ) * Complex.I := by
    simp only [Complex.ofReal_div, Complex.ofReal_ofNat]
    ring
  rw [hFormula]
  simpa only [hLimit] using hArctan.const_mul ((-2 : ℂ) * Complex.I)

/-- Symmetric principal-part integral below the pole. -/
theorem integral_symm_tendsto_neg (b : ℝ) (hb : b < 0) :
    Tendsto (fun R : ℝ => ∫ x in (-R)..R, reciprocal b x) atTop
      (𝓝 ((Real.pi : ℂ) * Complex.I)) := by
  have hArctan :
      Tendsto (fun R : ℝ => (Real.arctan (R / b) : ℂ)) atTop
        (𝓝 ((-(Real.pi / 2) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp
      (arctan_div_tendsto_neg b hb)
  have hFormula :
      (fun R : ℝ => ∫ x in (-R)..R, reciprocal b x) =
        (fun R : ℝ => (-2 : ℂ) * Complex.I * (Real.arctan (R / b) : ℂ)) := by
    funext R
    exact integral_symm b R hb.ne
  have hLimit :
      (-2 : ℂ) * Complex.I * ((-(Real.pi / 2) : ℝ) : ℂ) =
        (Real.pi : ℂ) * Complex.I := by
    simp only [Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_ofNat]
    ring
  rw [hFormula]
  simpa only [hLimit] using hArctan.const_mul ((-2 : ℂ) * Complex.I)

/-- Crossing the pole at -I gives the scalar factor with clockwise sign.
Both terms remain finite symmetric integrals at every cutoff. -/
theorem horizontal_difference_tendsto (w : ℝ) (hw : 1 ≤ w) :
    Tendsto (fun R : ℝ =>
      (∫ x in (-R)..R, reciprocal 1 x) -
        (∫ x in (-R)..R, reciprocal (1 - 2 * w) x)) atTop
      (𝓝 ((-2 : ℂ) * (Real.pi : ℂ) * Complex.I)) := by
  have hBottom : 1 - 2 * w < 0 := by linarith
  have h := (integral_symm_tendsto_pos 1 (by norm_num)).sub
    (integral_symm_tendsto_neg (1 - 2 * w) hBottom)
  have hLimit : -(Real.pi : ℂ) * Complex.I - (Real.pi : ℂ) * Complex.I =
      (-2 : ℂ) * (Real.pi : ℂ) * Complex.I := by ring
  simpa only [hLimit] using h

end
end SparseHamiltonian.ODEReciprocalLine
