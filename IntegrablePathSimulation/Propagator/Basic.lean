import IntegrablePathSimulation.Calculus.Absolute
import TimeDependentHamiltonian.Continuous.Propagator

set_option autoImplicit false

/-!
# Propagators of integrable paths

Theorem `hs:thm:time` of the manuscript compares the circuit with the time-ordered exponential
`U_H(T, 0) = 𝒯 exp (-i ∫_0^T H(u) du)` (equation `hs:eq:timeerror`). The paragraphs after its proof
extend the theorem to integrable Hermitian paths. For such a path we read `U_H(·, 0)` as the
solution of the Schrödinger equation in the sense of Carathéodory, that is of the integral equation

  `U(s) = 1 + ∫_0^s (-i) H(u) U(u) du`,  `0 ≤ s ≤ T`,

with a Bochner integral of operator-valued functions.

* `SolvesIntegralOn H U a b`: `u ↦ H u * U u` is interval integrable on `[a, b]` and
  `U s = U a + ∫_a^s (-i) H(u) U(u) du` for `s ∈ [a, b]`. It is the integral counterpart of
  the released classical `SolvesOn` (a derivative at every point).
* `IsPropagator H U T`: `U 0 = 1` and `SolvesIntegralOn H U 0 T`, the propagator `U_H(·, 0)`
  on `[0, T]`.

Basic facts: continuity, absolute continuity, the almost-everywhere derivative
`U' = -i H U`, restriction to subintervals, gluing of adjacent intervals and invariance under
changing `H` on a null set. Existence, uniqueness and unitarity are proved in
`Propagator.Existence`, `Propagator.Uniqueness` and `Propagator.Unitary`.
-/

namespace IntegrablePathSimulation.Propagator

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-- `U` solves `U' = -i H U` on `[a, b]` in the integral (Carathéodory) sense:
`u ↦ H u * U u` is interval integrable on `[a, b]` and
`U s = U a + ∫_a^s (-i) H(u) U(u) du` for every `s ∈ [a, b]`. -/
def SolvesIntegralOn (H U : ℝ → P →L[ℂ] P) (a b : ℝ) : Prop :=
  IntervalIntegrable (fun u => H u * U u) volume a b ∧
    ∀ s ∈ Icc a b, U s = U a + ∫ u in a..s, (-Complex.I) • (H u * U u)

/-- `U` is the propagator `U_H(·, 0)` of the path `H` on `[0, T]`: it starts at the identity
and solves `U' = -i H U` on `[0, T]` in the integral sense. -/
def IsPropagator (H U : ℝ → P →L[ℂ] P) (T : ℝ) : Prop :=
  U 0 = 1 ∧ SolvesIntegralOn H U 0 T

variable {H H' U : ℝ → P →L[ℂ] P} {a b c T : ℝ}

omit [CompleteSpace P] in
/-- The integrand `-i H U` of an integral-sense solution is interval integrable. -/
theorem SolvesIntegralOn.intervalIntegrable_rhs (hU : SolvesIntegralOn H U a b) :
    IntervalIntegrable (fun u => (-Complex.I) • (H u * U u)) volume a b :=
  hU.1.smul (-Complex.I)

omit [CompleteSpace P] in
/-- An integral-sense solution is absolutely continuous on its interval. -/
theorem SolvesIntegralOn.absolutelyContinuousOnInterval (hab : a ≤ b)
    (hU : SolvesIntegralOn H U a b) : AbsolutelyContinuousOnInterval U a b :=
  Calculus.absolutelyContinuousOnInterval_of_eq_add_integral hab hU.intervalIntegrable_rhs hU.2

omit [CompleteSpace P] in
/-- An integral-sense solution is continuous on its interval. -/
theorem SolvesIntegralOn.continuousOn (hab : a ≤ b) (hU : SolvesIntegralOn H U a b) :
    ContinuousOn U (Icc a b) :=
  Calculus.continuousOn_of_eq_add_integral hab hU.intervalIntegrable_rhs hU.2

/-- An integral-sense solution has derivative `-i H(u) U(u)` at almost every point of its
interval. -/
theorem SolvesIntegralOn.ae_hasDerivAt (hab : a ≤ b) (hU : SolvesIntegralOn H U a b) :
    ∀ᵐ u, u ∈ Icc a b → HasDerivAt U ((-Complex.I) • (H u * U u)) u :=
  Calculus.ae_hasDerivAt_of_eq_add_integral hab hU.intervalIntegrable_rhs hU.2

omit [CompleteSpace P] in
/-- Restriction of an integral-sense solution to a subinterval. -/
theorem SolvesIntegralOn.mono {a' b' : ℝ} (hU : SolvesIntegralOn H U a b) (ha : a ≤ a')
    (hab' : a' ≤ b') (hb : b' ≤ b) : SolvesIntegralOn H U a' b' := by
  have ha' : a' ∈ Icc a b := ⟨ha, hab'.trans hb⟩
  refine ⟨hU.1.mono_set (uIcc_subset_uIcc (mem_uIcc_of_le ha (hab'.trans hb))
    (mem_uIcc_of_le (ha.trans hab') hb)), fun s hs => ?_⟩
  have hs' : s ∈ Icc a b := ⟨ha.trans hs.1, hs.2.trans hb⟩
  have hf := hU.intervalIntegrable_rhs
  rw [hU.2 s hs', hU.2 a' ha', ← intervalIntegral.integral_interval_sub_left
    (hf.mono_set (uIcc_subset_uIcc left_mem_uIcc (mem_uIcc_of_le hs'.1 hs'.2)))
    (hf.mono_set (uIcc_subset_uIcc left_mem_uIcc (mem_uIcc_of_le ha'.1 ha'.2)))]
  abel

omit [CompleteSpace P] in
/-- Integral-sense solutions on adjacent intervals glue. -/
theorem SolvesIntegralOn.trans (hab : a ≤ b) (hbc : b ≤ c) (h₁ : SolvesIntegralOn H U a b)
    (h₂ : SolvesIntegralOn H U b c) : SolvesIntegralOn H U a c := by
  have _hac : a ≤ c := hab.trans hbc
  refine ⟨h₁.1.trans h₂.1, fun s hs => ?_⟩
  rcases le_total s b with hsb | hbs
  · exact h₁.2 s ⟨hs.1, hsb⟩
  · rw [h₂.2 s ⟨hbs, hs.2⟩, h₁.2 b ⟨hab, le_rfl⟩, add_assoc,
      intervalIntegral.integral_add_adjacent_intervals h₁.intervalIntegrable_rhs
        (h₂.intervalIntegrable_rhs.mono_set
          (uIcc_subset_uIcc left_mem_uIcc (mem_uIcc_of_le hbs hs.2)))]

omit [CompleteSpace P] in
/-- Changing the path on a null set does not change its integral-sense solutions. -/
theorem SolvesIntegralOn.congr_ae (hab : a ≤ b) (hU : SolvesIntegralOn H U a b)
    (hHH' : ∀ᵐ u, u ∈ Ioc a b → H u = H' u) : SolvesIntegralOn H' U a b := by
  have hfi := (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).1 hU.1
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2 (hfi.congr_fun_ae ?_),
    fun s hs => ?_⟩
  · filter_upwards [(ae_restrict_iff' measurableSet_Ioc).2 hHH'] with u hu
    rw [hu]
  · rw [hU.2 s hs]
    congr 1
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hHH'] with u hu hmem
    rw [uIoc_of_le hs.1] at hmem
    rw [hu ⟨hmem.1, hmem.2.trans hs.2⟩]

omit [CompleteSpace P] in
/-- A propagator on `[0, T]` solves the integral equation on every subinterval. -/
theorem IsPropagator.solvesIntegralOn (hU : IsPropagator H U T) (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : b ≤ T) : SolvesIntegralOn H U a b :=
  hU.2.mono ha hab hb

omit [CompleteSpace P] in
/-- A propagator is continuous on `[0, T]`. -/
theorem IsPropagator.continuousOn (hT : 0 ≤ T) (hU : IsPropagator H U T) :
    ContinuousOn U (Icc 0 T) :=
  hU.2.continuousOn hT

end

end IntegrablePathSimulation.Propagator
