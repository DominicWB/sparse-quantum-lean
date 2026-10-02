import SparseHamiltonian.ODEDissipative

/-!
# The inhomogeneous equation with constant forcing

The Duhamel integral is defined explicitly and proved to solve `u' = A u + b`.
Dissipativity then bounds the solution norm by `‖v‖ + t * ‖b‖`; this is the
natural input normalisation budget for a solver using a linear combination of
the homogeneous initial state and propagated forcing states.
-/

namespace SparseHamiltonian.ODEConstantForcing

noncomputable section
open ContinuousLinearMap NormedSpace ODEDissipative
open scoped Interval

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- The accumulated response to a constant forcing vector. -/
def response (A : V →L[ℂ] V) (b : V) (t : ℝ) : V :=
  ∫ s in (0 : ℝ)..t, trajectory A b s

/-- The explicit solution with initial vector `v` and constant forcing `b`. -/
def solution (A : V →L[ℂ] V) (v b : V) (t : ℝ) : V :=
  trajectory A v t + response A b t

omit [CompleteSpace V] in
@[simp]
theorem response_zero (A : V →L[ℂ] V) (b : V) : response A b 0 = 0 := by
  simp [response]

omit [CompleteSpace V] in
@[simp]
theorem solution_zero (A : V →L[ℂ] V) (v b : V) : solution A v b 0 = v := by
  simp [solution]

/-- The fundamental theorem of calculus differentiates the actual response
integral. -/
theorem response_hasDerivAt (A : V →L[ℂ] V) (b : V) (t : ℝ) :
    HasDerivAt (response A b) (trajectory A b t) t := by
  have hc := trajectory_continuous A b
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

/-- Applying the generator to the integrated response recovers the propagated
forcing minus its initial value. -/
theorem generator_response (A : V →L[ℂ] V) (b : V) (t : ℝ) :
    A (response A b t) = trajectory A b t - b := by
  have hc := trajectory_continuous A b
  have hi := hc.intervalIntegrable (μ := MeasureTheory.volume) (0 : ℝ) t
  have hAi := (A.continuous.comp hc).intervalIntegrable
    (μ := MeasureTheory.volume) (0 : ℝ) t
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s (_ : s ∈ Set.uIcc (0 : ℝ) t) => trajectory_hasDerivAt A b s) hAi
  rw [A.intervalIntegral_comp_comm hi] at hFTC
  simpa only [response, trajectory_zero] using hFTC

/-- The explicit inhomogeneous solution has the required derivative. -/
theorem solution_hasDerivAt (A : V →L[ℂ] V) (v b : V) (t : ℝ) :
    HasDerivAt (solution A v b) (A (solution A v b t) + b) t := by
  have h := (trajectory_hasDerivAt A v t).add (response_hasDerivAt A b t)
  have hderiv : A (trajectory A v t) + trajectory A b t = A (solution A v b t) + b := by
    simp only [solution, map_add, generator_response]
    abel
  change HasDerivAt (fun u => trajectory A v u + response A b u)
    (A (solution A v b t) + b) t
  rw [← hderiv]
  convert! h using 1

/-- The explicit solution is the unique differentiable solution with its
initial value on nonnegative times. -/
theorem eq_solution_of_hasDerivAt (A : V →L[ℂ] V) (hA : Dissipative A)
    (f : ℝ → V) (v b : V) (hzero : f 0 = v)
    (hf : ∀ t, HasDerivAt f (A (f t) + b) t) (t : ℝ) (ht : 0 ≤ t) :
    f t = solution A v b t := by
  let w : ℝ → V := fun u => f u - solution A v b u
  have hw (u : ℝ) : HasDerivAt w (A (w u)) u := by
    convert! (hf u).sub (solution_hasDerivAt A v b u) using 1
    simp only [w, map_sub]
    abel
  have hwzero : w 0 = 0 := by simp [w, hzero]
  have heq := eq_trajectory_of_hasDerivAt A hA w hw t ht
  rw [hwzero] at heq
  have hn : w t = 0 := by simpa only [trajectory, map_zero] using heq
  exact sub_eq_zero.mp hn

/-- The response to constant forcing costs at most time times the forcing norm
under dissipative dynamics. -/
theorem response_norm_le (A : V →L[ℂ] V) (hA : Dissipative A)
    (b : V) (t : ℝ) (ht : 0 ≤ t) : ‖response A b t‖ ≤ t * ‖b‖ := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := t) (f := trajectory A b) (C := ‖b‖) (fun s hs => by
      have hs' : s ∈ Set.Ioc (0 : ℝ) t := by
        simpa only [Set.uIoc_of_le ht] using hs
      exact trajectory_norm_le A hA b s hs'.1.le)
  simpa only [response, sub_zero, abs_of_nonneg ht, mul_comm] using h

/-- The source budget `‖v‖ + t * ‖b‖` bounds the norm of the actual
inhomogeneous solution. -/
theorem solution_norm_le (A : V →L[ℂ] V) (hA : Dissipative A)
    (v b : V) (t : ℝ) (ht : 0 ≤ t) :
    ‖solution A v b t‖ ≤ ‖v‖ + t * ‖b‖ := by
  exact (norm_add_le _ _).trans
    (add_le_add (trajectory_norm_le A hA v t ht) (response_norm_le A hA b t ht))

/-- For a nonzero solution the source budget divided by the output norm is at
least one, as required of an amplification overhead parameter. -/
theorem normalization_ratio_ge_one (A : V →L[ℂ] V) (hA : Dissipative A)
    (v b : V) (t : ℝ) (ht : 0 ≤ t) (hsol : solution A v b t ≠ 0) :
    1 ≤ (‖v‖ + t * ‖b‖) / ‖solution A v b t‖ := by
  apply (le_div_iff₀ (norm_pos_iff.mpr hsol)).mpr
  simpa only [one_mul] using solution_norm_le A hA v b t ht

/-- A certified left-endpoint quadrature error for one forcing interval. The
bound is quadratic in the interval width and has no exponential time factor. -/
theorem interval_left_endpoint_error (A : V →L[ℂ] V) (hA : Dissipative A)
    (v : V) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    ‖(∫ s in a..b, trajectory A v s) - (b - a) • trajectory A v a‖ ≤
      (b - a) ^ 2 * ‖A‖ * ‖v‖ := by
  have hi := (trajectory_continuous A v).intervalIntegrable (μ := MeasureTheory.volume) a b
  have heq : (∫ s in a..b, trajectory A v s) - (b - a) • trajectory A v a =
      ∫ s in a..b, trajectory A v s - trajectory A v a := by
    rw [intervalIntegral.integral_sub hi intervalIntegrable_const,
      intervalIntegral.integral_const]
  rw [heq]
  have hbound (s : ℝ) (hs : s ∈ Set.uIoc a b) :
      ‖trajectory A v s - trajectory A v a‖ ≤ (b - a) * ‖A‖ * ‖v‖ := by
    have hs' : s ∈ Set.Ioc a b := by simpa only [Set.uIoc_of_le hab] using hs
    have hsa : 0 ≤ s - a := sub_nonneg.mpr hs'.1.le
    calc
      _ ≤ |s - a| * ‖A‖ * ‖v‖ :=
        trajectory_sub_norm_le A hA v s a (ha.trans hs'.1.le) ha
      _ ≤ (b - a) * ‖A‖ * ‖v‖ := by
        rw [abs_of_nonneg hsa]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (sub_le_sub_right hs'.2 a) (norm_nonneg _))
          (norm_nonneg _)
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  calc
    _ ≤ ((b - a) * ‖A‖ * ‖v‖) * |b - a| := h
    _ = (b - a) ^ 2 * ‖A‖ * ‖v‖ := by rw [abs_of_nonneg (sub_nonneg.mpr hab)]; ring

end
end SparseHamiltonian.ODEConstantForcing
