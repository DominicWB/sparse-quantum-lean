import SparseODE.ODETaggedLCHS

/-!
# Certified uniform forcing quadrature for the improved ODE reduction

This fragment proves a finite source discretization from dissipativity and
continuity of the actual exponential trajectory.  The quadrature error is a
conclusion, not an additional approximation premise.  Refinement changes the
number of free source-selection labels, not a sequential matrix-query count.

-/

namespace SparseHamiltonian.ODESourceQuadrature

noncomputable section
open ContinuousLinearMap NormedSpace ODEDissipative ODEConstantForcing
open scoped Interval

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- A partial left-endpoint sum with a fixed mesh width. -/
def partialSum (A : V →L[ℂ] V) (b : V) (h : ℝ) (N : ℕ) : V :=
  ∑ i ∈ Finset.range N, h • trajectory A b ((i : ℝ) * h)

/-- Telescoping the integral adds the local errors.  This bound remains
valid for width zero and for a zero forcing vector. -/
theorem partialSum_error (A : V →L[ℂ] V) (hA : Dissipative A)
    (b : V) (h : ℝ) (hh : 0 ≤ h) (N : ℕ) :
    ‖response A b ((N : ℝ) * h) - partialSum A b h N‖ ≤
      (N : ℝ) * h ^ 2 * ‖A‖ * ‖b‖ := by
  induction N with
  | zero => simp [partialSum]
  | succ N ih =>
      have hleft : 0 ≤ (N : ℝ) * h := mul_nonneg (Nat.cast_nonneg _) hh
      have hwidth : ((N + 1 : ℕ) : ℝ) * h - (N : ℝ) * h = h := by
        push_cast
        ring
      have horder : (N : ℝ) * h ≤ ((N + 1 : ℕ) : ℝ) * h := by
        linarith
      have hc := trajectory_continuous A b
      have hsplit : response A b (((N + 1 : ℕ) : ℝ) * h) =
          response A b ((N : ℝ) * h) +
            ∫ t in ((N : ℝ) * h)..(((N + 1 : ℕ) : ℝ) * h), trajectory A b t := by
        unfold response
        exact (intervalIntegral.integral_add_adjacent_intervals
          (hc.intervalIntegrable (μ := MeasureTheory.volume) 0 ((N : ℝ) * h))
          (hc.intervalIntegrable (μ := MeasureTheory.volume)
            ((N : ℝ) * h) (((N + 1 : ℕ) : ℝ) * h))).symm
      have hlocal :
          ‖(∫ t in ((N : ℝ) * h)..(((N + 1 : ℕ) : ℝ) * h), trajectory A b t) -
              h • trajectory A b ((N : ℝ) * h)‖ ≤ h ^ 2 * ‖A‖ * ‖b‖ := by
        simpa only [hwidth] using interval_left_endpoint_error A hA b
          ((N : ℝ) * h) (((N + 1 : ℕ) : ℝ) * h) hleft horder
      have hsum : partialSum A b h (N + 1) = partialSum A b h N +
          h • trajectory A b ((N : ℝ) * h) := by
        simp only [partialSum, Finset.sum_range_succ]
      have herror : response A b (((N + 1 : ℕ) : ℝ) * h) -
          partialSum A b h (N + 1) =
          (response A b ((N : ℝ) * h) - partialSum A b h N) +
            ((∫ t in ((N : ℝ) * h)..(((N + 1 : ℕ) : ℝ) * h), trajectory A b t) -
              h • trajectory A b ((N : ℝ) * h)) := by
        rw [hsplit, hsum]
        abel
      rw [herror]
      calc
        _ ≤ ‖response A b ((N : ℝ) * h) - partialSum A b h N‖ +
            ‖(∫ t in ((N : ℝ) * h)..(((N + 1 : ℕ) : ℝ) * h), trajectory A b t) -
              h • trajectory A b ((N : ℝ) * h)‖ := norm_add_le _ _
        _ ≤ (N : ℝ) * h ^ 2 * ‖A‖ * ‖b‖ + h ^ 2 * ‖A‖ * ‖b‖ :=
          add_le_add ih hlocal
        _ = ((N + 1 : ℕ) : ℝ) * h ^ 2 * ‖A‖ * ‖b‖ := by
          push_cast
          ring

/-- The nonnegative coefficient of each forcing branch. -/
def weight (T : ℝ) (N : ℕ) (_ : Fin N) : ℝ := T / (N : ℝ)

/-- Its propagation duration, with a common maximum duration `T`. -/
def time (T : ℝ) (N : ℕ) (i : Fin N) : ℝ := (i.val : ℝ) * (T / (N : ℝ))

/-- The actual finite forcing sum used by the state preparation. -/
def forcingSum (A : V →L[ℂ] V) (b : V) (T : ℝ) (N : ℕ) : V :=
  ∑ i : Fin N, weight T N i • trajectory A b (time T N i)

/-- Add the exactly propagated initial state. -/
def approximation (A : V →L[ℂ] V) (v b : V) (T : ℝ) (N : ℕ) : V :=
  trajectory A v T + forcingSum A b T N

theorem weight_nonneg (T : ℝ) (hT : 0 ≤ T) (N : ℕ) (i : Fin N) :
    0 ≤ weight T N i := div_nonneg hT (Nat.cast_nonneg _)

theorem time_nonneg (T : ℝ) (hT : 0 ≤ T) (N : ℕ) (i : Fin N) :
    0 ≤ time T N i :=
  mul_nonneg (Nat.cast_nonneg _) (weight_nonneg T hT N i)

theorem time_le (T : ℝ) (hT : 0 ≤ T) (N : ℕ) (hN : 0 < N) (i : Fin N) :
    time T N i ≤ T := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  calc
    _ ≤ (N : ℝ) * (T / (N : ℝ)) := by
      apply mul_le_mul_of_nonneg_right _ (div_nonneg hT (Nat.cast_nonneg _))
      exact_mod_cast i.isLt.le
    _ = T := by field_simp [hNr]

/-- Refinement preserves the total source weight exactly. -/
theorem sum_weights (T : ℝ) (N : ℕ) (hN : 0 < N) :
    ∑ i : Fin N, weight T N i = T := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  calc
    _ = (N : ℝ) * (T / (N : ℝ)) := by
      simp [weight, nsmul_eq_mul]
    _ = T := by field_simp [hNr]

omit [CompleteSpace V] in
theorem forcingSum_eq_partialSum (A : V →L[ℂ] V) (b : V) (T : ℝ) (N : ℕ) :
    forcingSum A b T N = partialSum A b (T / (N : ℝ)) N := by
  unfold forcingSum weight time partialSum
  exact Fin.sum_univ_eq_sum_range
    (fun i : ℕ => (T / (N : ℝ)) • trajectory A b ((i : ℝ) * (T / (N : ℝ)))) N

/-- The explicit `1/N` error estimate has no exponential stability factor. -/
theorem forcingSum_error (A : V →L[ℂ] V) (hA : Dissipative A)
    (b : V) (T : ℝ) (hT : 0 ≤ T) (N : ℕ) (hN : 0 < N) :
    ‖forcingSum A b T N - response A b T‖ ≤ T ^ 2 * ‖A‖ * ‖b‖ / (N : ℝ) := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have htime : (N : ℝ) * (T / (N : ℝ)) = T := by
    field_simp [hNr]
  have hfactor : (N : ℝ) * (T / (N : ℝ)) ^ 2 * ‖A‖ * ‖b‖ =
      T ^ 2 * ‖A‖ * ‖b‖ / (N : ℝ) := by
    field_simp [hNr]
  rw [forcingSum_eq_partialSum, norm_sub_rev]
  simpa only [htime, hfactor] using
    partialSum_error A hA b (T / (N : ℝ)) (div_nonneg hT (Nat.cast_nonneg _)) N

/-- Certified global source quadrature for the actual inhomogeneous solution. -/
theorem approximation_error (A : V →L[ℂ] V) (hA : Dissipative A)
    (v b : V) (T : ℝ) (hT : 0 ≤ T) (N : ℕ) (hN : 0 < N) :
    ‖approximation A v b T N - solution A v b T‖ ≤
      T ^ 2 * ‖A‖ * ‖b‖ / (N : ℝ) := by
  have heq : approximation A v b T N - solution A v b T =
      forcingSum A b T N - response A b T := by
    unfold approximation solution
    abel
  rw [heq]
  exact forcingSum_error A hA b T hT N hN

omit [InnerProductSpace ℂ V] [CompleteSpace V] in
/-- The existing finite-Duhamel interface has the exact physical source
budget, independent of the number of quadrature branches. -/
theorem sourceBudget_eq (v b : V) (T : ℝ) (N : ℕ) (hN : 0 < N) :
    ODEErrorBudget.sourceBudget v (weight T N) (fun _ : Fin N => b) =
      ‖v‖ + T * ‖b‖ := by
  unfold ODEErrorBudget.sourceBudget
  rw [← Finset.sum_mul, sum_weights T N hN]

omit [CompleteSpace V] in
/-- The finite-Duhamel vectors use complex scalar coefficients; positive
real source weights define exactly the same vectors. -/
theorem finiteDuhamel_eq_approximation (A : V →L[ℂ] V) (v b : V)
    (T : ℝ) (N : ℕ) :
    ODEErrorBudget.finiteDuhamel (exp (T • A))
      (fun i : Fin N => exp (time T N i • A)) v (weight T N) (fun _ => b) =
      approximation A v b T N := by
  unfold ODEErrorBudget.finiteDuhamel approximation forcingSum trajectory
  congr 1

/-- This discharges the source-quadrature premise in the existing LCHS error
interface, rather than leaving it as an analytic assumption. -/
theorem finiteDuhamel_error (A : V →L[ℂ] V) (hA : Dissipative A)
    (v b : V) (T : ℝ) (hT : 0 ≤ T) (N : ℕ) (hN : 0 < N) :
    ‖ODEErrorBudget.finiteDuhamel (exp (T • A))
        (fun i : Fin N => exp (time T N i • A)) v (weight T N) (fun _ => b) -
      solution A v b T‖ ≤ T ^ 2 * ‖A‖ * ‖b‖ / (N : ℝ) := by
  rw [finiteDuhamel_eq_approximation]
  exact approximation_error A hA v b T hT N hN

/-- Any positive absolute source tolerance is attained with finitely many
explicit uniform branches.  Degenerate time and forcing need no exception. -/
theorem exists_approximation (A : V →L[ℂ] V) (hA : Dissipative A)
    (v b : V) (T : ℝ) (hT : 0 ≤ T) (δ : ℝ) (hδ : 0 < δ) :
    ∃ N : ℕ, 0 < N ∧ ‖approximation A v b T N - solution A v b T‖ ≤ δ := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max (1 : ℝ) (T ^ 2 * ‖A‖ * ‖b‖ / δ))
  have hN1 : (1 : ℝ) < (N : ℝ) := lt_of_le_of_lt (le_max_left _ _) hN
  have hNr : 0 < (N : ℝ) := by linarith
  have hNnat : 0 < N := by exact_mod_cast hNr
  have hfrac : T ^ 2 * ‖A‖ * ‖b‖ / δ < (N : ℝ) :=
    lt_of_le_of_lt (le_max_right _ _) hN
  have hprod : T ^ 2 * ‖A‖ * ‖b‖ < (N : ℝ) * δ := (div_lt_iff₀ hδ).mp hfrac
  refine ⟨N, hNnat, (approximation_error A hA v b T hT N hNnat).trans ?_⟩
  apply (div_le_iff₀ hNr).mpr
  nlinarith

/-- There always exists a finite source quadrature with error at most `ν B`.
The case `B = 0` is proved directly, not divided away. -/
theorem exists_relative_approximation (A : V →L[ℂ] V) (hA : Dissipative A)
    (v b : V) (T : ℝ) (hT : 0 ≤ T) (ν : ℝ) (hν : 0 < ν) :
    ∃ N : ℕ, 0 < N ∧
      ‖approximation A v b T N - solution A v b T‖ ≤ ν * (‖v‖ + T * ‖b‖) := by
  have hB : 0 ≤ ‖v‖ + T * ‖b‖ :=
    add_nonneg (norm_nonneg _) (mul_nonneg hT (norm_nonneg _))
  by_cases hzero : ‖v‖ + T * ‖b‖ = 0
  · have hTb : T * ‖b‖ = 0 := by
      nlinarith [norm_nonneg v, mul_nonneg hT (norm_nonneg b)]
    have hC : T ^ 2 * ‖A‖ * ‖b‖ = 0 := by
      calc
        _ = (T * ‖A‖) * (T * ‖b‖) := by ring
        _ = 0 := by rw [hTb, mul_zero]
    refine ⟨1, by norm_num, ?_⟩
    have herr := approximation_error A hA v b T hT 1 (by norm_num)
    simpa only [hC, hzero, Nat.cast_one, zero_div, mul_zero] using herr
  · exact exists_approximation A hA v b T hT _
      (mul_pos hν (lt_of_le_of_ne hB (Ne.symm hzero)))

/-- A packaged finite-Duhamel source certificate, including positive weights,
common duration bounds, exact source normalization, and actual solution error.
This supplies all source-discretization obligations of the constant-forcing
reduction; Hamiltonian simulation and LCHS coefficients are separate tasks. -/
theorem exists_finiteDuhamel_certificate (A : V →L[ℂ] V) (hA : Dissipative A)
    (v b : V) (T : ℝ) (hT : 0 ≤ T) (ν : ℝ) (hν : 0 < ν) :
    ∃ N : ℕ, 0 < N ∧
      (∀ i : Fin N, 0 ≤ weight T N i) ∧
      (∀ i : Fin N, 0 ≤ time T N i ∧ time T N i ≤ T) ∧
      ODEErrorBudget.sourceBudget v (weight T N) (fun _ : Fin N => b) =
        ‖v‖ + T * ‖b‖ ∧
      ‖ODEErrorBudget.finiteDuhamel (exp (T • A))
          (fun i : Fin N => exp (time T N i • A)) v (weight T N) (fun _ => b) -
        solution A v b T‖ ≤
        ν * ODEErrorBudget.sourceBudget v (weight T N) (fun _ : Fin N => b) := by
  obtain ⟨N, hN, herr⟩ := exists_relative_approximation A hA v b T hT ν hν
  refine ⟨N, hN, weight_nonneg T hT N,
    (fun i => ⟨time_nonneg T hT N i, time_le T hT N hN i⟩),
    sourceBudget_eq v b T N hN, ?_⟩
  rw [finiteDuhamel_eq_approximation, sourceBudget_eq v b T N hN]
  exact herr

end
end SparseHamiltonian.ODESourceQuadrature
