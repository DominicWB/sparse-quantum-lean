import SparseHamiltonian.CoherentQuerySchedule

/-!
# Contractive dynamics for a bounded dissipative generator

These results establish the analytic evolution used by the ODE solver. The
sign convention is `u' = A u`: dissipativity means that the real part of
`⟪v, A v⟫` is nonpositive. In the convention `u' = -B u`, apply the results
to `A = -B`.

The exponential trajectory solves the differential equation, has nonincreasing
norm, and is Lipschitz in nonnegative time without an exponential loss.
-/

namespace SparseHamiltonian.ODEDissipative

noncomputable section
open ContinuousLinearMap NormedSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- A bounded generator is dissipative when it cannot increase squared norm
instantaneously. -/
def Dissipative (A : V →L[ℂ] V) : Prop :=
  ∀ v : V, (inner ℂ v (A v)).re ≤ 0

/-- The homogeneous trajectory of a bounded, time-independent generator. -/
def trajectory (A : V →L[ℂ] V) (v : V) (t : ℝ) : V :=
  exp (t • A) v

omit [CompleteSpace V] in
@[simp]
theorem trajectory_zero (A : V →L[ℂ] V) (v : V) : trajectory A v 0 = v := by
  simp [trajectory]

/-- The exponential trajectory solves the stated differential equation. -/
theorem trajectory_hasDerivAt (A : V →L[ℂ] V) (v : V) (t : ℝ) :
    HasDerivAt (trajectory A v) (A (trajectory A v t)) t := by
  change HasDerivAt (fun u : ℝ => exp (u • A) v) (A (exp (t • A) v)) t
  simpa [Function.comp_def] using
    ((ContinuousLinearMap.apply ℂ V v).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
      t (hasDerivAt_exp_smul_const' A t)

/-- The exact trajectory is continuous on the entire real line. -/
theorem trajectory_continuous (A : V →L[ℂ] V) (v : V) :
    Continuous (trajectory A v) :=
  continuous_iff_continuousAt.mpr fun t => (trajectory_hasDerivAt A v t).continuousAt

/-- The derivative of squared norm exposes precisely the dissipativity form. -/
theorem trajectory_norm_sq_hasDerivAt (A : V →L[ℂ] V) (v : V) (t : ℝ) :
    HasDerivAt (fun u : ℝ => ‖trajectory A v u‖ ^ 2)
      (2 * (inner ℂ (trajectory A v t) (A (trajectory A v t))).re) t := by
  letI : InnerProductSpace ℝ V := InnerProductSpace.rclikeToReal ℂ V
  simpa only [real_inner_eq_re_inner ℂ, RCLike.re_to_complex] using
    (trajectory_hasDerivAt A v t).norm_sq

omit [CompleteSpace V] in
/-- Any differentiable solution of a dissipative homogeneous equation has
nonincreasing squared norm. -/
theorem norm_sq_antitone_of_hasDerivAt (A : V →L[ℂ] V) (hA : Dissipative A)
    (f : ℝ → V) (hf : ∀ t, HasDerivAt f (A (f t)) t) :
    Antitone (fun t : ℝ => ‖f t‖ ^ 2) := by
  letI : InnerProductSpace ℝ V := InnerProductSpace.rclikeToReal ℂ V
  have hderiv (t : ℝ) : HasDerivAt (fun u : ℝ => ‖f u‖ ^ 2)
      (2 * (inner ℂ (f t) (A (f t))).re) t := by
    simpa only [real_inner_eq_re_inner ℂ, RCLike.re_to_complex] using (hf t).norm_sq
  apply antitone_of_hasDerivAt_nonpos hderiv
  intro t
  exact mul_nonpos_of_nonneg_of_nonpos (by norm_num) (hA _)

/-- A dissipative homogeneous trajectory has nonincreasing squared norm. -/
theorem trajectory_norm_sq_antitone (A : V →L[ℂ] V) (hA : Dissipative A) (v : V) :
    Antitone (fun t : ℝ => ‖trajectory A v t‖ ^ 2) := by
  exact norm_sq_antitone_of_hasDerivAt A hA _ (trajectory_hasDerivAt A v)

/-- A differentiable homogeneous solution agrees with the exponential
trajectory on all nonnegative times. -/
theorem eq_trajectory_of_hasDerivAt (A : V →L[ℂ] V) (hA : Dissipative A)
    (f : ℝ → V) (hf : ∀ t, HasDerivAt f (A (f t)) t)
    (t : ℝ) (ht : 0 ≤ t) : f t = trajectory A (f 0) t := by
  let w : ℝ → V := fun u => f u - trajectory A (f 0) u
  have hw (u : ℝ) : HasDerivAt w (A (w u)) u := by
    convert! (hf u).sub (trajectory_hasDerivAt A (f 0) u) using 1
    simp only [w, map_sub]
  have hzero : w 0 = 0 := by simp [w]
  have hsq := norm_sq_antitone_of_hasDerivAt A hA w hw ht
  change ‖w t‖ ^ 2 ≤ ‖w 0‖ ^ 2 at hsq
  rw [hzero, norm_zero, zero_pow (by norm_num : 2 ≠ 0)] at hsq
  have hn : ‖w t‖ = 0 := by nlinarith [norm_nonneg (w t)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

/-- Dissipativity gives a contraction at every nonnegative time. -/
theorem trajectory_norm_le (A : V →L[ℂ] V) (hA : Dissipative A) (v : V)
    (t : ℝ) (ht : 0 ≤ t) : ‖trajectory A v t‖ ≤ ‖v‖ := by
  have h := trajectory_norm_sq_antitone A hA v ht
  simp only [trajectory_zero] at h
  nlinarith [norm_nonneg (trajectory A v t), norm_nonneg v]

/-- The propagator itself is a contraction, including on the trivial space. -/
theorem exp_norm_le_one (A : V →L[ℂ] V) (hA : Dissipative A)
    (t : ℝ) (ht : 0 ≤ t) : ‖exp (t • A)‖ ≤ 1 := by
  apply opNorm_le_bound _ (by norm_num)
  intro v
  simpa only [one_mul, trajectory] using trajectory_norm_le A hA v t ht

/-- The derivative along a straight interpolation of two time parameters. -/
theorem time_interpolation_hasDerivAt (A : V →L[ℂ] V) (t u r : ℝ) :
    HasDerivAt (fun q : ℝ => exp (((1 - q) * u + q * t) • A))
      ((t - u) • (A * exp (((1 - r) * u + r * t) • A))) r := by
  have htime : HasDerivAt (fun q : ℝ => (1 - q) * u + q * t) (t - u) r := by
    convert! (((hasDerivAt_id r).const_sub 1).mul_const u).add
      ((hasDerivAt_id r).mul_const t) using 1
    ring
  simpa only [Function.comp_def] using
    (hasDerivAt_exp_smul_const' A ((1 - r) * u + r * t)).scomp r htime

/-- On nonnegative times the propagator is Lipschitz with constant `‖A‖`.
There is no `exp (t * ‖A‖)` factor. -/
theorem exp_sub_norm_le (A : V →L[ℂ] V) (hA : Dissipative A)
    (t u : ℝ) (ht : 0 ≤ t) (hu : 0 ≤ u) :
    ‖exp (t • A) - exp (u • A)‖ ≤ |t - u| * ‖A‖ := by
  have hbound (r : ℝ) (hr : r ∈ Set.Ico (0 : ℝ) 1) :
      ‖(t - u) • (A * exp (((1 - r) * u + r * t) • A))‖ ≤
        |t - u| * ‖A‖ := by
    have htime : 0 ≤ (1 - r) * u + r * t :=
      add_nonneg (mul_nonneg (sub_nonneg.mpr hr.2.le) hu) (mul_nonneg hr.1 ht)
    rw [norm_smul, Real.norm_eq_abs]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    calc
      _ ≤ ‖A‖ * ‖exp (((1 - r) * u + r * t) • A)‖ := norm_mul_le _ _
      _ ≤ ‖A‖ * 1 := mul_le_mul_of_nonneg_left (exp_norm_le_one A hA _ htime)
        (norm_nonneg _)
      _ = ‖A‖ := mul_one _
  have h := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun r _ => (time_interpolation_hasDerivAt A t u r).hasDerivWithinAt) hbound
  simpa only [sub_self, zero_mul, one_mul, zero_add, sub_zero, add_zero] using h

/-- The same sharp time bound applies to each input vector. -/
theorem trajectory_sub_norm_le (A : V →L[ℂ] V) (hA : Dissipative A)
    (v : V) (t u : ℝ) (ht : 0 ≤ t) (hu : 0 ≤ u) :
    ‖trajectory A v t - trajectory A v u‖ ≤ |t - u| * ‖A‖ * ‖v‖ := by
  calc
    _ = ‖(exp (t • A) - exp (u • A)) v‖ := rfl
    _ ≤ ‖exp (t • A) - exp (u • A)‖ * ‖v‖ := le_opNorm _ _
    _ ≤ |t - u| * ‖A‖ * ‖v‖ :=
      mul_le_mul_of_nonneg_right (exp_sub_norm_le A hA t u ht hu) (norm_nonneg _)

end
end SparseHamiltonian.ODEDissipative
