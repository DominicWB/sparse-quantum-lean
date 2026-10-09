import IntegrablePathSimulation.Propagator.Classical
import IntegrablePathSimulation.Propagator.Duhamel

set_option autoImplicit false

/-!
# The released mesh estimates as corollaries

The released time-dependent theorems prove the unitary Duhamel estimate and the integrated
sample-error certificate for classical solutions and piecewise propagators
(`TimeDependentExtensions.duhamel_integral`, `TimeDependentExtensions.mesh_error_integral`,
`TimeDependentExtensions.refined_error`). This module derives each of them, with its statement
unchanged, from the integral-sense estimates of `Propagator.Duhamel`, through the containment
results of `Propagator.Classical`. This is the paragraph after Theorem `hs:thm:time` of the
manuscript (lines 1618-1632): for an integrable Hermitian path the integrated sample errors
suffice, and the piecewise case is a special case.

* `duhamel_integral_of_solvesOn`: the statement of `TimeDependentExtensions.duhamel_integral`,
  from `SolvesIntegralOn.duhamel` and `solvesIntegralOn_of_solvesOn`.
* `ae_star_glue`: the glued path of self-adjoint pieces is self-adjoint at almost every time
  of `[0, T]`.
* `mesh_error_integral_piecewise`, `refined_error_piecewise`: the statements of
  `TimeDependentExtensions.mesh_error_integral` and `TimeDependentExtensions.refined_error`,
  from `IsPropagator.mesh_error_integral` and `IsPropagator.refined_error` for the glued path
  (`isPropagator_glue`); the certificates agree because the glued path equals each piece
  almost everywhere on its interval (`glue_ae_eq`).
-/

namespace IntegrablePathSimulation.Propagator

noncomputable section

open MeasureTheory Set Filter
open SparseHamiltonian.TimeDependent (SolvesOn)
open TimeDependentExtensions (IsMesh IsPiecewisePropagator meshEvolution refinedEvolution)
open scoped BigOperators

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-- **The released one-interval Duhamel estimate as a corollary.** The statement of
`TimeDependentExtensions.duhamel_integral` (classical solutions), derived from
`SolvesIntegralOn.duhamel`. -/
theorem duhamel_integral_of_solvesOn {H U : ℝ → P →L[ℂ] P} (Hs : P →L[ℂ] P) {a b : ℝ}
    (hab : a ≤ b) (hU : SolvesOn H U a b) (hUnorm : ∀ u ∈ Icc a b, ‖U u‖ ≤ 1)
    (hHs : star Hs = Hs) (hint : IntervalIntegrable H volume a b) :
    ‖U b - NormedSpace.exp ((-Complex.I * ((b - a : ℝ) : ℂ)) • Hs) * U a‖ ≤
      ∫ u in a..b, ‖H u - Hs‖ :=
  (solvesIntegralOn_of_solvesOn hab hU hint).duhamel Hs hab hUnorm hHs hint

variable {t : ℕ → ℝ} {M N : ℕ} {T : ℝ}

/-- The path glued from pieces that are self-adjoint on their closed mesh intervals is
self-adjoint at almost every time of `[0, T]`. -/
theorem ae_star_glue {Hp : ℕ → ℝ → P →L[ℂ] P} (h : IsMesh t M T)
    (hH : ∀ r < M, ∀ u ∈ Icc (t r) (t (r + 1)), star (Hp r u) = Hp r u) :
    ∀ᵐ u, u ∈ Icc 0 T → star (glue Hp t M u) = glue Hp t M u := by
  rcases Nat.eq_zero_or_pos M with hM | hM
  · subst hM
    have hT : T = 0 := h.last.symm.trans h.zero
    have hnull : ∀ᵐ u : ℝ, u ≠ 0 := by
      simp [ae_iff, measure_singleton]
    filter_upwards [hnull] with u hu hmem
    exact absurd (le_antisymm (by simpa [hT] using hmem.2) hmem.1) hu
  · exact ae_of_all _ fun u hu => hH _ (pieceIndex_lt hM u) u (mem_Icc_pieceIndex h hM hu)

omit [CompleteSpace P] in
/-- The certificate of the glued path equals the certificate of the pieces. -/
theorem sum_integral_glue {Hp : ℕ → ℝ → P →L[ℂ] P} (Hs : ℕ → P →L[ℂ] P) (h : IsMesh t M T) :
    ∑ r ∈ Finset.range M, ∫ u in t r..t (r + 1), ‖glue Hp t M u - Hs r‖ =
      ∑ r ∈ Finset.range M, ∫ u in t r..t (r + 1), ‖Hp r u - Hs r‖ := by
  refine Finset.sum_congr rfl fun r hr => ?_
  refine intervalIntegral.integral_congr_ae ?_
  rw [uIoc_of_le (h.mono (Nat.le_succ r))]
  filter_upwards [glue_ae_eq Hp h (Finset.mem_range.mp hr)] with u hu hmem
  rw [hu hmem]

/-- **The released certificate as a corollary.** The statement of
`TimeDependentExtensions.mesh_error_integral` (piecewise propagators), derived from
`IsPropagator.mesh_error_integral` for the glued path. -/
theorem mesh_error_integral_piecewise {Hp : ℕ → ℝ → P →L[ℂ] P} (Hs : ℕ → P →L[ℂ] P)
    {U : ℝ → P →L[ℂ] P} (h : IsMesh t M T) (hU : IsPiecewisePropagator Hp t M U)
    (hH : ∀ r < M, ∀ u ∈ Icc (t r) (t (r + 1)), star (Hp r u) = Hp r u)
    (hHs : ∀ r, star (Hs r) = Hs r)
    (hint : ∀ r < M, IntervalIntegrable (Hp r) volume (t r) (t (r + 1))) :
    ‖U T - meshEvolution Hs t M‖ ≤
      ∑ r ∈ Finset.range M, ∫ u in t r..t (r + 1), ‖Hp r u - Hs r‖ := by
  rw [← sum_integral_glue Hs h]
  exact (isPropagator_glue h hU hint).mesh_error_integral Hs h (ae_star_glue h hH) hHs
    (intervalIntegrable_glue h hint)

/-- **The released refined certificate as a corollary.** The statement of
`TimeDependentExtensions.refined_error` (piecewise propagators), derived from
`IsPropagator.refined_error` for the glued path. -/
theorem refined_error_piecewise {Hp : ℕ → ℝ → P →L[ℂ] P} (Hs : ℕ → P →L[ℂ] P)
    {U : ℝ → P →L[ℂ] P} (h : IsMesh t M T) (hT : 0 < T) (hN : 0 < N)
    (hU : IsPiecewisePropagator Hp t M U)
    (hH : ∀ r < M, ∀ u ∈ Icc (t r) (t (r + 1)), star (Hp r u) = Hp r u)
    (hHs : ∀ r, star (Hs r) = Hs r) {Λ : ℝ} (hΛ : ∀ r, ‖Hs r‖ ≤ Λ)
    (hint : ∀ r < M, IntervalIntegrable (Hp r) volume (t r) (t (r + 1))) :
    ‖U T - refinedEvolution Hs t T N M‖ ≤
      (∑ r ∈ Finset.range M, ∫ u in t r..t (r + 1), ‖Hp r u - Hs r‖) + M * (T / N) * Λ := by
  rw [← sum_integral_glue Hs h]
  exact (isPropagator_glue h hU hint).refined_error Hs h hT hN (ae_star_glue h hH) hHs hΛ
    (intervalIntegrable_glue h hint)

end

end IntegrablePathSimulation.Propagator
