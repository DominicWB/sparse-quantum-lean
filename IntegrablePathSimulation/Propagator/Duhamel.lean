import IntegrablePathSimulation.Propagator.Unitary
import TimeDependentExtensions.Coherent.Theorem

set_option autoImplicit false

/-!
# The unitary Duhamel estimate and the integrated sample-error certificate

The proof of Theorem `hs:thm:time` of the manuscript bounds, on each mesh interval, the
difference between the exact propagator and `exp(-i Δ_r H̃_r)` by the unitary Duhamel formula
(lines 1587-1590) and telescopes over the mesh (equation `hs:eq:timedisc`, lines 1595-1601).
The paragraph after the proof (lines 1618-1632) replaces the regularity of the path by a
certified bound on the sum of integrated sample errors `∑_r ∫_{t_r}^{t_{r+1}} ‖H(u) - H̃_r‖ du`.
This module proves these estimates for propagators of merely integrable paths.

* `SolvesIntegralOn.duhamel`: on one interval, against a fixed self-adjoint sample `H̃`,
  `‖U(b) - exp(-i (b - a) H̃) U(a)‖ ≤ ∫_a^b ‖H(u) - H̃‖ du` for every integral-sense solution
  with `‖U‖ ≤ 1` (the released `TimeDependentExtensions.duhamel_integral` for classical
  solutions). The proof applies the product rule for integral equations to
  `exp((u - a) i H̃) U(u)`.
* `SolvesIntegralOn.window_error`: on a window `[t_a, t_{a+m}]` of a monotone mesh, a solution
  from the identity at `t_a` is within the integrated sample errors of the window of the
  ordered product of the step exponentials over the window (the released
  `TimeDependentExtensions.Coherent.window_error` for piecewise classical propagators). It
  serves the coherent windows of `IntegrablePathSimulation.Coherent`.
* `IsPropagator.mesh_error_integral`: `‖U(T) - ∏_r exp(-i (t_{r+1} - t_r) H̃_r)‖` is at most
  the certificate, for an almost-everywhere self-adjoint, interval-integrable path on any mesh
  (the released `TimeDependentExtensions.mesh_error_integral` for piecewise classical
  propagators).
* `IsPropagator.refined_error`: the same against the refined slot product
  `TimeDependentExtensions.refinedEvolution`, with the additional refinement error
  `M (T / N) Λ` (the released `TimeDependentExtensions.refined_error`).
-/

namespace IntegrablePathSimulation.Propagator

noncomputable section

open MeasureTheory Set Filter ContinuousLinearMap
open TimeDependentExtensions (IsMesh meshEvolution refinedEvolution)
open TimeDependentExtensions (exp_add_commute)
open SparseHamiltonian (CayleyApproximation.skew_exp_norm_le)
open SparseHamiltonian.TimeDependent (real_smul_skew)
open scoped BigOperators Topology

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

variable {H U : ℝ → P →L[ℂ] P}

/-- **Unitary Duhamel estimate for integral-sense solutions** on one interval, against a
fixed self-adjoint sample: `‖U(b) - exp(-i (b - a) H̃) U(a)‖ ≤ ∫_a^b ‖H(u) - H̃‖ du`. -/
theorem SolvesIntegralOn.duhamel (Hs : P →L[ℂ] P) {a b : ℝ} (hab : a ≤ b)
    (hU : SolvesIntegralOn H U a b) (hUnorm : ∀ u ∈ Icc a b, ‖U u‖ ≤ 1)
    (hHs : star Hs = Hs) (hint : IntervalIntegrable H volume a b) :
    ‖U b - NormedSpace.exp ((-Complex.I * ((b - a : ℝ) : ℂ)) • Hs) * U a‖ ≤
      ∫ u in a..b, ‖H u - Hs‖ := by
  let X : P →L[ℂ] P := Complex.I • Hs
  have hXskew : star X = -X := by
    simp only [X, star_smul, hHs, Complex.star_def, Complex.conj_I, neg_smul]
  let E : ℝ → P →L[ℂ] P := fun u => NormedSpace.exp ((u - a) • X)
  have hEnorm : ∀ u, ‖E u‖ ≤ 1 := fun u =>
    CayleyApproximation.skew_exp_norm_le _ (real_smul_skew X hXskew (u - a))
  have hE : ∀ u, HasDerivAt E (E u * X) u := by
    intro u
    have hlin : HasDerivAt (fun v : ℝ => v - a) 1 u := (hasDerivAt_id' u).sub_const a
    have h := (hasDerivAt_exp_smul_const (𝕂 := ℝ) X (u - a)).scomp u hlin
    simpa only [one_smul, Function.comp_def] using h
  have hEcont : Continuous E := continuous_iff_continuousAt.2 fun u => (hE u).continuousAt
  have hEX : Continuous fun u => E u * X := hEcont.mul continuous_const
  have hEint : ∀ s ∈ Icc a b, E s = E a + ∫ u in a..s, E u * X := by
    intro s _
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hE u)
      (hEX.intervalIntegrable a s)]
    abel
  let f' : ℝ → P →L[ℂ] P := fun u => E u * (Complex.I • ((Hs - H u) * U u))
  have hrw : ∀ u, E u * X * U u + E u * ((-Complex.I) • (H u * U u)) = f' u := by
    intro u
    simp only [f', X, mul_smul_comm, smul_mul_assoc, sub_mul, smul_sub, mul_sub, mul_assoc]
    rw [sub_eq_add_neg]
    simp only [neg_smul]
  have hprod := Calculus.mul_eq_add_integral hab (hEX.intervalIntegrable a b)
    hU.intervalIntegrable_rhs hEint hU.2 b ⟨hab, le_rfl⟩
  have hFTC : ∫ u in a..b, f' u = E b * U b - E a * U a := by
    rw [hprod, add_sub_cancel_left]
    exact intervalIntegral.integral_congr fun u _ => (hrw u).symm
  have hbound : ‖E b * U b - E a * U a‖ ≤ ∫ u in a..b, ‖H u - Hs‖ := by
    rw [← hFTC]
    apply intervalIntegral.norm_integral_le_of_norm_le hab
    · refine ae_of_all _ (fun u hu => ?_)
      have huIcc : u ∈ Icc a b := Ioc_subset_Icc_self hu
      calc ‖f' u‖ ≤ ‖E u‖ * (‖Hs - H u‖ * ‖U u‖) := by
            refine (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
            rw [norm_smul, Complex.norm_I, one_mul]
            exact norm_mul_le _ _
        _ ≤ 1 * (‖H u - Hs‖ * 1) := by
            rw [norm_sub_rev]
            exact mul_le_mul (hEnorm u) (mul_le_mul le_rfl (hUnorm u huIcc) (norm_nonneg _)
              (norm_nonneg _)) (by positivity) zero_le_one
        _ = ‖H u - Hs‖ := by ring
    · exact (hint.sub intervalIntegrable_const).norm
  have hEa : E a = 1 := by simp [E]
  rw [hEa, one_mul] at hbound
  let Y : P →L[ℂ] P := (b - a) • X
  have hinv : NormedSpace.exp (-Y) * NormedSpace.exp Y = 1 := by
    rw [← exp_add_commute _ _ (Commute.neg_left (Commute.refl Y)), neg_add_cancel,
      NormedSpace.exp_zero]
  have hY : -Y = (-Complex.I * ((b - a : ℝ) : ℂ)) • Hs := by
    simp only [Y, X, ← Complex.coe_smul, smul_smul, ← neg_smul]
    congr 1
    ring
  have hfactor : U b - NormedSpace.exp ((-Complex.I * ((b - a : ℝ) : ℂ)) • Hs) * U a =
      NormedSpace.exp (-Y) * (E b * U b - U a) := by
    rw [mul_sub, ← mul_assoc, show E b = NormedSpace.exp Y from rfl, hinv, one_mul, hY]
  rw [hfactor]
  calc ‖NormedSpace.exp (-Y) * (E b * U b - U a)‖ ≤
        ‖NormedSpace.exp (-Y)‖ * ‖E b * U b - U a‖ := norm_mul_le _ _
    _ ≤ 1 * ∫ u in a..b, ‖H u - Hs‖ := by
      apply mul_le_mul _ hbound (norm_nonneg _) zero_le_one
      have hskew : star (-Y) = -(-Y) := by
        rw [star_neg, real_smul_skew X hXskew (b - a)]
      exact CayleyApproximation.skew_exp_norm_le _ hskew
    _ = ∫ u in a..b, ‖H u - Hs‖ := one_mul _

variable {t : ℕ → ℝ} {M N : ℕ} {T : ℝ}

/-- **Duhamel on a window of the mesh** for integral-sense solutions: a solution from the
identity at `t_a` of a path that is self-adjoint at almost every time of `[t_a, t_{a+m}]` and
interval integrable there is within the integrated sample errors of the intervals
`a, …, a + m - 1` of the ordered product of the step exponentials over those intervals. -/
theorem SolvesIntegralOn.window_error (Hs : ℕ → P →L[ℂ] P) (hmono : Monotone t) (a m : ℕ)
    (hU : SolvesIntegralOn H U (t a) (t (a + m))) (hU0 : U (t a) = 1)
    (hH : ∀ᵐ u, u ∈ Icc (t a) (t (a + m)) → star (H u) = H u)
    (hHs : ∀ r, star (Hs r) = Hs r) (hint : IntervalIntegrable H volume (t a) (t (a + m))) :
    ‖U (t (a + m)) - SparseHamiltonian.TimeDependent.orderedProduct (fun r => NormedSpace.exp
        ((-Complex.I * ((t (r + 1) - t r : ℝ) : ℂ)) • Hs r)) a m‖ ≤
      ∑ j ∈ Finset.range m, ∫ u in t (a + j)..t (a + j + 1), ‖H u - Hs (a + j)‖ := by
  have hnorm := hU.norm_le_one hU0 hH
  rw [TimeDependentExtensions.Coherent.orderedProduct_eq_evolution]
  have htel := SparseHamiltonian.TimeDependent.propagator_telescope U (fun j =>
    NormedSpace.exp ((-Complex.I * ((t (a + j + 1) - t (a + j) : ℝ) : ℂ)) • Hs (a + j)))
    (fun j => TimeDependentExtensions.exp_skew_norm_le (Hs (a + j)) (hHs _) _)
    (fun j => t (a + j)) hU0 m
  refine htel.trans (Finset.sum_le_sum fun j hj => ?_)
  have hjm := Finset.mem_range.mp hj
  have h0 : t a ≤ t (a + j) := hmono (by omega)
  have h1 : t (a + j) ≤ t (a + j + 1) := hmono (Nat.le_succ _)
  have h2 : t (a + j + 1) ≤ t (a + m) := hmono (by omega)
  have hw : uIcc (t (a + j)) (t (a + j + 1)) ⊆ uIcc (t a) (t (a + m)) := by
    rw [uIcc_of_le h1, uIcc_of_le (h0.trans (h1.trans h2))]
    exact Icc_subset_Icc h0 h2
  have h := (hU.mono h0 h1 h2).duhamel (Hs (a + j)) h1
    (fun u hu => hnorm u ⟨h0.trans hu.1, hu.2.trans h2⟩) (hHs _) (hint.mono_set hw)
  simpa only [← add_assoc] using h

/-- **The integrated sample-error certificate for integrable paths**:
`‖U(T) - ∏_r exp(-i (t_{r+1} - t_r) H̃_r)‖ ≤ ∑_r ∫_{t_r}^{t_{r+1}} ‖H(u) - H̃_r‖ du`. -/
theorem IsPropagator.mesh_error_integral (Hs : ℕ → P →L[ℂ] P) (h : IsMesh t M T)
    (hU : IsPropagator H U T) (hH : ∀ᵐ u, u ∈ Icc 0 T → star (H u) = H u)
    (hHs : ∀ r, star (Hs r) = Hs r) (hint : IntervalIntegrable H volume 0 T) :
    ‖U T - meshEvolution Hs t M‖ ≤
      ∑ r ∈ Finset.range M, ∫ u in t r..t (r + 1), ‖H u - Hs r‖ := by
  have hE : ∀ r, ‖NormedSpace.exp ((-Complex.I * ((t (r + 1) - t r : ℝ) : ℂ)) • Hs r)‖ ≤ 1 :=
    fun r => TimeDependentExtensions.exp_skew_norm_le (Hs r) (hHs r) _
  have htel := SparseHamiltonian.TimeDependent.propagator_telescope U _ hE t
    (by rw [h.zero]; exact hU.1) M
  rw [h.last] at htel
  refine htel.trans (Finset.sum_le_sum fun r hr => ?_)
  have hrM := Finset.mem_range.mp hr
  have h0 : 0 ≤ t r := h.nonneg r
  have h1 : t r ≤ t (r + 1) := h.mono (Nat.le_succ r)
  have h2 : t (r + 1) ≤ T := h.le_last (by omega)
  have hw : uIcc (t r) (t (r + 1)) ⊆ uIcc 0 T := by
    rw [uIcc_of_le h1, uIcc_of_le (h0.trans (h1.trans h2))]
    exact Icc_subset_Icc h0 h2
  exact (hU.solvesIntegralOn h0 h1 h2).duhamel (Hs r) h1
    (fun u hu => hU.norm_le_one hH u ⟨h0.trans hu.1, hu.2.trans h2⟩) (hHs r)
    (hint.mono_set hw)

/-- **Integrated certificate and refinement together** for integrable paths: the refined slot
product of the samples is within `∑_r ∫ ‖H - H̃_r‖ + M (T / N) Λ` of the propagator. -/
theorem IsPropagator.refined_error (Hs : ℕ → P →L[ℂ] P) (h : IsMesh t M T) (hT : 0 < T)
    (hN : 0 < N) (hU : IsPropagator H U T) (hH : ∀ᵐ u, u ∈ Icc 0 T → star (H u) = H u)
    (hHs : ∀ r, star (Hs r) = Hs r) {Λ : ℝ} (hΛ : ∀ r, ‖Hs r‖ ≤ Λ)
    (hint : IntervalIntegrable H volume 0 T) :
    ‖U T - refinedEvolution Hs t T N M‖ ≤
      (∑ r ∈ Finset.range M, ∫ u in t r..t (r + 1), ‖H u - Hs r‖) + M * (T / N) * Λ := by
  calc ‖U T - refinedEvolution Hs t T N M‖ ≤ ‖U T - meshEvolution Hs t M‖ +
        ‖meshEvolution Hs t M - refinedEvolution Hs t T N M‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := by
      apply add_le_add (hU.mesh_error_integral Hs h hH hHs hint)
      rw [norm_sub_rev]
      exact TimeDependentExtensions.refined_evolution_sub_le Hs hHs hΛ h hT hN

end

end IntegrablePathSimulation.Propagator
