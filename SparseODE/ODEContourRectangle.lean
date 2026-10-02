import SparseODE.ODEGaussianVertical

/-!
# Removing a simple pole before shifting a rectangular contour

The divided difference `dslope F c` removes the pole of
`(z-c)^(-1) • F z`. Mathlib's removable-singularity theorem establishes its
holomorphy, and Cauchy-Goursat then gives the four-side rectangle identity.
This generic analytic result assumes differentiability of the numerator; it
does not assume an LCHS integral formula or an approximation guarantee.

Requires Mathlib.Analysis.Complex.RemovableSingularity.
-/

namespace SparseHamiltonian.ODEContourRectangle

noncomputable section
open Complex
open scoped Interval Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- One horizontal side, always integrated from its first real endpoint to
its second real endpoint. -/
def horizontal (f : ℂ → E) (a b y : ℝ) : E :=
  ∫ x in a..b, f ((x : ℂ) + (y : ℂ) * Complex.I)

/-- One vertical side, without the complex tangent factor `I`. -/
def vertical (f : ℂ → E) (x a b : ℝ) : E :=
  ∫ y in a..b, f ((x : ℂ) + (y : ℂ) * Complex.I)

/-- The oriented rectangle boundary expression used by Cauchy-Goursat. -/
def boundary (f : ℂ → E) (z w : ℂ) : E :=
  (horizontal f z.re w.re z.im - horizontal f z.re w.re w.im) +
    Complex.I • vertical f w.re z.im w.im -
    Complex.I • vertical f z.re z.im w.im

/-- A numerator divided by a single linear factor. -/
def poleQuotient (F : ℂ → E) (c z : ℂ) : E := (z - c)⁻¹ • F z

/-- The constant-residue principal part. -/
def principalPart (a : E) (c z : ℂ) : E := (z - c)⁻¹ • a

omit [CompleteSpace E] in
/-- Away from its center, the divided difference subtracts exactly the
principal part and nothing else. -/
theorem regularized_eq_sub (F : ℂ → E) (c z : ℂ) (hz : z ≠ c) :
    dslope F c z = poleQuotient F c z - principalPart (F c) c z := by
  rw [dslope_of_ne F hz]
  change (z - c)⁻¹ • (F z - F c) = (z - c)⁻¹ • F z - (z - c)⁻¹ • F c
  exact smul_sub _ _ _

omit [CompleteSpace E] in
theorem pole_decomposition (F : ℂ → E) (c z : ℂ) (hz : z ≠ c) :
    poleQuotient F c z = dslope F c z + principalPart (F c) c z := by
  rw [regularized_eq_sub F c z hz]
  abel

/-- Holomorphy at the filled-in pole follows from the removable-singularity
theorem; it is not an extra promise on the regularized function. -/
theorem regularized_differentiableOn (F : ℂ → E) (c : ℂ) (S : Set ℂ)
    (hc : S ∈ nhds c) (hF : DifferentiableOn ℂ F S) :
    DifferentiableOn ℂ (dslope F c) S :=
  (Complex.differentiableOn_dslope hc).2 hF

omit [CompleteSpace E] in
/-- Exact Cauchy-Goursat identity on a closed rectangle. -/
theorem boundary_eq_zero (f : ℂ → E) (z w : ℂ)
    (hf : DifferentiableOn ℂ f
      (Complex.reProdIm (Set.uIcc z.re w.re) (Set.uIcc z.im w.im))) :
    boundary f z w = 0 := by
  exact Complex.integral_boundary_rect_eq_zero_of_differentiableOn f z w hf

/-- Apply Cauchy-Goursat after deriving the removable value at the pole. -/
theorem regularized_boundary_eq_zero (F : ℂ → E) (c z w : ℂ) (S : Set ℂ)
    (hc : S ∈ nhds c) (hF : DifferentiableOn ℂ F S)
    (hRect : Complex.reProdIm (Set.uIcc z.re w.re) (Set.uIcc z.im w.im) ⊆ S) :
    boundary (dslope F c) z w = 0 := by
  exact boundary_eq_zero _ z w ((regularized_differentiableOn F c S hc hF).mono hRect)

omit [CompleteSpace E] in
/-- The difference between horizontal integrals is exactly the contribution
of the vertical sides. This identity applies at finite truncation widths. -/
theorem horizontal_difference_eq (f : ℂ → E) (z w : ℂ)
    (hf : DifferentiableOn ℂ f
      (Complex.reProdIm (Set.uIcc z.re w.re) (Set.uIcc z.im w.im))) :
    horizontal f z.re w.re z.im - horizontal f z.re w.re w.im =
      Complex.I • (vertical f z.re z.im w.im - vertical f w.re z.im w.im) := by
  have h := boundary_eq_zero f z w hf
  unfold boundary at h
  rw [smul_sub]
  exact (eq_sub_iff_add_eq).2 (sub_eq_zero.mp h)

theorem regularized_horizontal_difference_eq (F : ℂ → E) (c z w : ℂ) (S : Set ℂ)
    (hc : S ∈ nhds c) (hF : DifferentiableOn ℂ F S)
    (hRect : Complex.reProdIm (Set.uIcc z.re w.re) (Set.uIcc z.im w.im) ⊆ S) :
    horizontal (dslope F c) z.re w.re z.im -
        horizontal (dslope F c) z.re w.re w.im =
      Complex.I • (vertical (dslope F c) z.re z.im w.im -
        vertical (dslope F c) w.re z.im w.im) := by
  exact horizontal_difference_eq _ z w
    ((regularized_differentiableOn F c S hc hF).mono hRect)

omit [CompleteSpace E] in
/-- A uniform bound on a vertical side gives its length times that bound. -/
theorem vertical_norm_le (f : ℂ → E) (x a b C : ℝ)
    (hBound : ∀ y ∈ Set.uIoc a b, ‖f ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤ C) :
    ‖vertical f x a b‖ ≤ C * |b - a| := by
  exact intervalIntegral.norm_integral_le_of_norm_le_const hBound

omit [CompleteSpace E] in
/-- Cauchy-Goursat turns two uniform vertical-side bounds into a quantitative
bound on the difference of horizontal integrals. -/
theorem horizontal_difference_norm_le (f : ℂ → E) (z w : ℂ) (CL CR : ℝ)
    (hf : DifferentiableOn ℂ f
      (Complex.reProdIm (Set.uIcc z.re w.re) (Set.uIcc z.im w.im)))
    (hLeft : ∀ y ∈ Set.uIoc z.im w.im,
      ‖f ((z.re : ℂ) + (y : ℂ) * Complex.I)‖ ≤ CL)
    (hRight : ∀ y ∈ Set.uIoc z.im w.im,
      ‖f ((w.re : ℂ) + (y : ℂ) * Complex.I)‖ ≤ CR) :
    ‖horizontal f z.re w.re z.im - horizontal f z.re w.re w.im‖ ≤
      (CL + CR) * |w.im - z.im| := by
  rw [horizontal_difference_eq f z w hf, norm_smul, Complex.norm_I, one_mul, add_mul]
  exact (norm_sub_le _ _).trans
    (add_le_add (vertical_norm_le f z.re z.im w.im CL hLeft)
      (vertical_norm_le f w.re z.im w.im CR hRight))

end
end SparseHamiltonian.ODEContourRectangle
