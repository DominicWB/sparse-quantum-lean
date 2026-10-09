import IntegrablePathSimulation.Propagator.Existence
import IntegrablePathSimulation.Calculus.Gronwall

set_option autoImplicit false

/-!
# Uniqueness of propagators of integrable paths

Two integral-sense solutions of `U' = -i H U` with the same initial value agree on the whole
interval: their difference `D` is continuous and obeys `‖D s‖ ≤ ∫_a^s ‖H‖ ‖D‖`, so it
vanishes by the integral form of Grönwall's inequality with the integrable coefficient `‖H‖`
(`Calculus.eq_zero_of_norm_le_integral`). Together with `Propagator.Existence`, every
interval-integrable path has exactly one propagator on `[0, T]` (`existsUnique_isPropagator`),
the operator `U_H(T, 0)` of Theorem `hs:thm:time` of the manuscript (lines 1414-1445) for the
integrable paths of the paragraph after its proof (lines 1618-1632).
-/

namespace IntegrablePathSimulation.Propagator

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

variable {H U V : ℝ → P →L[ℂ] P} {a b T : ℝ}

omit [CompleteSpace P] in
/-- **Uniqueness on an interval**: two integral-sense solutions with the same initial value
agree on `[a, b]`, for an interval-integrable path. -/
theorem SolvesIntegralOn.eqOn (hab : a ≤ b) (hint : IntervalIntegrable H volume a b)
    (hU : SolvesIntegralOn H U a b) (hV : SolvesIntegralOn H V a b) (h0 : U a = V a) :
    ∀ s ∈ Icc a b, U s = V s := by
  have hsub : ∀ s ∈ Icc a b, uIcc a s ⊆ uIcc a b := fun s hs => by
    rw [uIcc_of_le hs.1, uIcc_of_le hab]
    exact Icc_subset_Icc le_rfl hs.2
  have hDc : ContinuousOn (fun u => U u - V u) (Icc a b) :=
    (hU.continuousOn hab).sub (hV.continuousOn hab)
  have hD : ∀ s ∈ Icc a b,
      U s - V s = ∫ u in a..s, (-Complex.I) • (H u * (U u - V u)) := by
    intro s hs
    rw [hU.2 s hs, hV.2 s hs, h0, add_sub_add_left_eq_sub,
      ← intervalIntegral.integral_sub (hU.intervalIntegrable_rhs.mono_set (hsub s hs))
        (hV.intervalIntegrable_rhs.mono_set (hsub s hs))]
    simp_rw [mul_sub, smul_sub]
  have hle : ∀ s ∈ Icc a b, ‖U s - V s‖ ≤ ∫ u in a..s, ‖H u‖ * ‖U u - V u‖ := by
    intro s hs
    rw [hD s hs]
    refine intervalIntegral.norm_integral_le_of_norm_le hs.1 (ae_of_all _ fun u _ => ?_)
      ((hint.norm.mul_continuousOn (by rw [uIcc_of_le hab]; exact hDc.norm)).mono_set
        (hsub s hs))
    rw [norm_smul, norm_neg, Complex.norm_I, one_mul]
    exact norm_mul_le _ _
  intro s hs
  exact sub_eq_zero.mp (Calculus.eq_zero_of_norm_le_integral hab hDc hint.norm
    (ae_of_all _ fun _ _ => norm_nonneg _) hle s hs)

omit [CompleteSpace P] in
/-- **Uniqueness**: two propagators of an interval-integrable path agree on `[0, T]`. -/
theorem IsPropagator.eqOn (hT : 0 ≤ T) (hint : IntervalIntegrable H volume 0 T)
    (hU : IsPropagator H U T) (hV : IsPropagator H V T) : ∀ s ∈ Icc 0 T, U s = V s :=
  hU.2.eqOn hT hint hV.2 (hU.1.trans hV.1.symm)

/-- **Existence and uniqueness**: an interval-integrable path has a propagator on `[0, T]`, and
any two of its propagators agree on `[0, T]`. -/
theorem existsUnique_isPropagator (hT : 0 ≤ T) (hint : IntervalIntegrable H volume 0 T) :
    (∃ U : ℝ → P →L[ℂ] P, IsPropagator H U T) ∧
      ∀ U V : ℝ → P →L[ℂ] P, IsPropagator H U T → IsPropagator H V T →
        ∀ s ∈ Icc 0 T, U s = V s :=
  ⟨exists_isPropagator hT hint, fun _ _ hU hV => hU.eqOn hT hint hV⟩

end

end IntegrablePathSimulation.Propagator
