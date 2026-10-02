import SparseODE.ODEGaussianResidue

/-!
# Finite symmetric integrals of the simple-pole factor

On a horizontal line avoiding the pole, the reciprocal is continuous and
interval integrable.  A logarithm/arctangent antiderivative computes every
finite symmetric integral.  No whole-line Bochner integrability is claimed:
the norm of this reciprocal has a nonintegrable inverse-linear tail.

Requires Mathlib.Analysis.SpecialFunctions.Log.Deriv,
Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv, and
Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus.
-/

namespace SparseHamiltonian.ODEReciprocalLine

noncomputable section
open MeasureTheory
open scoped Interval

/-- The simple-pole factor restricted to a horizontal line. -/
def reciprocal (b x : ℝ) : ℂ :=
  ((x : ℂ) + (b : ℂ) * Complex.I)⁻¹

/-- A nonzero vertical offset keeps the entire horizontal line off the pole. -/
theorem denominator_ne_zero (b x : ℝ) (hb : b ≠ 0) :
    (x : ℂ) + (b : ℂ) * Complex.I ≠ 0 := by
  intro h
  apply hb
  have hIm := congrArg Complex.im h
  simpa using hIm

/-- Continuity is derived from the explicit nonvanishing denominator. -/
theorem reciprocal_continuous (b : ℝ) (hb : b ≠ 0) :
    Continuous (reciprocal b) := by
  convert! (continuous_const.div
      (Complex.continuous_ofReal.add continuous_const)
      (fun x : ℝ => denominator_ne_zero b x hb) :
        Continuous (fun x : ℝ => (1 : ℂ) / ((x : ℂ) + (b : ℂ) * Complex.I))) using 1 ;
    first
    | rfl
    | funext x
      simp only [reciprocal, Pi.div_apply, one_div]

/-- The reciprocal is integrable on every finite oriented interval. -/
theorem reciprocal_intervalIntegrable (b : ℝ) (hb : b ≠ 0) (a c : ℝ) :
    IntervalIntegrable (reciprocal b) volume a c :=
  (reciprocal_continuous b hb).intervalIntegrable a c

/-- Positivity of the real squared denominator, with no sign restriction on b. -/
theorem squared_denominator_pos (b x : ℝ) (hb : b ≠ 0) :
    0 < x ^ 2 + b ^ 2 := by
  exact add_pos_of_nonneg_of_pos (sq_nonneg x) (sq_pos_of_ne_zero hb)

/-- Real and imaginary coordinates of the complex reciprocal. -/
theorem reciprocal_eq_coordinates (b x : ℝ) (hb : b ≠ 0) :
    reciprocal b x = ((x / (x ^ 2 + b ^ 2) : ℝ) : ℂ) -
      Complex.I * ((b / (x ^ 2 + b ^ 2) : ℝ) : ℂ) := by
  have hd : ((x ^ 2 + b ^ 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (squared_denominator_pos b x hb).ne'
  have hProduct :
      ((x : ℂ) - (b : ℂ) * Complex.I) *
        ((x : ℂ) + (b : ℂ) * Complex.I) = ((x ^ 2 + b ^ 2 : ℝ) : ℂ) := by
    push_cast
    calc
      _ = (x : ℂ) ^ 2 - (b : ℂ) ^ 2 * (Complex.I * Complex.I) := by ring
      _ = _ := by rw [Complex.I_mul_I]; ring
  symm
  calc
    _ = ((x : ℂ) - (b : ℂ) * Complex.I) / ((x ^ 2 + b ^ 2 : ℝ) : ℂ) := by
      push_cast
      ring
    _ = (1 : ℂ) / ((x : ℂ) + (b : ℂ) * Complex.I) := by
      apply (div_eq_div_iff hd (denominator_ne_zero b x hb)).mpr
      simpa only [one_mul] using hProduct
    _ = reciprocal b x := by simp only [reciprocal, one_div]

/-- Derivative of the real part of the explicit primitive. -/
theorem logRadius_hasDerivAt (b x : ℝ) (hb : b ≠ 0) :
    HasDerivAt (fun y : ℝ => Real.log (y ^ 2 + b ^ 2) / 2)
      (x / (x ^ 2 + b ^ 2)) x := by
  have hd : x ^ 2 + b ^ 2 ≠ 0 := (squared_denominator_pos b x hb).ne'
  have hSquare : HasDerivAt (fun y : ℝ => y ^ 2 + b ^ 2) (2 * x) x := by
    have hScalar : 2 * x = (2 : ℝ) * x ^ (2 - 1) * 1 := by ring
    convert! ((hasDerivAt_id x).pow 2).add_const (b ^ 2) using 1
  have hScalar : x / (x ^ 2 + b ^ 2) =
      ((2 * x) / (x ^ 2 + b ^ 2)) / 2 := by ring
  convert! (hSquare.log hd).div_const 2 using 1

/-- Derivative of the angle, valid for positive and negative offsets alike. -/
theorem angle_hasDerivAt (b x : ℝ) (hb : b ≠ 0) :
    HasDerivAt (fun y : ℝ => Real.arctan (y / b))
      (b / (x ^ 2 + b ^ 2)) x := by
  have hd : x ^ 2 + b ^ 2 ≠ 0 := (squared_denominator_pos b x hb).ne'
  have hq : 1 + (x / b) ^ 2 ≠ 0 := by positivity
  have hScalar : b / (x ^ 2 + b ^ 2) =
      (1 / (1 + (x / b) ^ 2)) * (1 / b) := by
    field_simp [hb, hd, hq] ; ring
  convert! ((hasDerivAt_id x).div_const b).arctan using 1

/-- A single-valued primitive on a fixed horizontal line. -/
def primitive (b x : ℝ) : ℂ :=
  ((Real.log (x ^ 2 + b ^ 2) / 2 : ℝ) : ℂ) -
    Complex.I * (Real.arctan (x / b) : ℂ)

/-- The logarithm and arctangent derivatives give the actual reciprocal,
with the complex scalar coordinates identified algebraically. -/
theorem primitive_hasDerivAt (b x : ℝ) (hb : b ≠ 0) :
    HasDerivAt (primitive b) (reciprocal b x) x := by
  convert! (logRadius_hasDerivAt b x hb).ofReal_comp.sub
    ((angle_hasDerivAt b x hb).ofReal_comp.const_mul Complex.I) using 1 ;
    first | rfl | exact reciprocal_eq_coordinates b x hb

/-- The even logarithmic part cancels at opposite endpoints. -/
theorem primitive_sub_neg (b R : ℝ) :
    primitive b R - primitive b (-R) =
      -2 * Complex.I * (Real.arctan (R / b) : ℂ) := by
  unfold primitive
  rw [neg_sq, neg_div, Real.arctan_neg, Complex.ofReal_neg]
  ring

/-- Exact finite symmetric reciprocal integral.  The radius is arbitrary:
orientation is handled by the interval integral, including R = 0 and R < 0. -/
theorem integral_symm (b R : ℝ) (hb : b ≠ 0) :
    (∫ x in -R..R, reciprocal b x) =
      -2 * Complex.I * (Real.arctan (R / b) : ℂ) := by
  have hFTC : (∫ x in -R..R, reciprocal b x) =
      primitive b R - primitive b (-R) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => primitive_hasDerivAt b x hb)
      (reciprocal_intervalIntegrable b hb (-R) R)
  exact hFTC.trans (primitive_sub_neg b R)

end
end SparseHamiltonian.ODEReciprocalLine
