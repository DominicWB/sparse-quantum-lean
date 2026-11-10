import GeneralSourceODE.Theorem

/-!
# Existence of the propagator

The general-source solver quantifies over a family `U t w` of homogeneous
solutions on `[t, T]` (`IsPropagator`). For a continuous generator path such
a family exists (`exists_isPropagator`): the released existence theorem
`TimeDependentODE.exists_solvesODE` applies to the shifted path
`u ↦ G(u + t)` on `[0, T - t]` (`solvesODE_shift`). For an accretive path it
is unique on `[t, T]` (`homogeneous_unique`), so it is the propagator
`U(T, t)` of the manuscript. The public mesh conditions are those of the
released `TimeDependentODE.mesh_conditions`.
-/

namespace SparseHamiltonian.GeneralSourceODE

noncomputable section
open ContinuousLinearMap Set TimeDependentODE

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- A homogeneous solution of the shifted equation on `[0, c - t]`, shifted
back, solves the equation on `[t, c]`. -/
theorem solvesODE_shift {G : ℝ → V →L[ℂ] V} {y : ℝ → V} {t c : ℝ}
    (hy : SolvesODE (fun u => G (u + t)) 0 y 0 (c - t)) :
    SolvesODE G 0 (fun u => y (u - t)) t c := by
  intro u hu
  have hmem : u - t ∈ Icc 0 (c - t) := ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hg := hy (u - t) hmem
  have hh : HasDerivWithinAt (fun u : ℝ => u - t) 1 (Icc t c) u :=
    (hasDerivWithinAt_id u (Icc t c)).sub_const t
  have hmaps : MapsTo (fun u : ℝ => u - t) (Icc t c) (Icc 0 (c - t)) :=
    fun w hw => ⟨by linarith [hw.1], by linarith [hw.2]⟩
  have h := hg.scomp u hh hmaps
  refine h.congr_deriv ?_
  simp only [one_smul, Pi.zero_apply, add_zero, sub_add_cancel]

/-- **Existence of the propagator.** For a continuous generator path on
`[0, T]` there is a family `U` of homogeneous solutions from every start time
`t ∈ [0, T]` and value `w`. -/
theorem exists_isPropagator [CompleteSpace V] {G : ℝ → V →L[ℂ] V} {T : ℝ}
    (hGc : ContinuousOn G (Icc 0 T)) : ∃ U : ℝ → V → ℝ → V, IsPropagator G U T := by
  have hex : ∀ t ∈ Icc 0 T, ∀ w : V, ∃ y : ℝ → V,
      y 0 = w ∧ SolvesODE (fun u => G (u + t)) 0 y 0 (T - t) := by
    intro t ht w
    have hT' : 0 ≤ T - t := by linarith [ht.2]
    have hc : ContinuousOn (fun u => G (u + t)) (Icc 0 (T - t)) :=
      hGc.comp (continuous_id.add continuous_const).continuousOn
        (fun u hu => ⟨by linarith [hu.1, ht.1], by linarith [hu.2]⟩)
    exact exists_solvesODE (fun u => G (u + t)) 0 hT' hc continuousOn_const w
  classical
  refine ⟨fun t w u => if ht : t ∈ Icc 0 T then (hex t ht w).choose (u - t) else 0, ?_⟩
  intro t ht w
  have hspec := (hex t ht w).choose_spec
  refine ⟨?_, ?_⟩
  · have h := solvesODE_shift hspec.2
    simpa only [dif_pos ht] using h
  · simp only [dif_pos ht, sub_self, hspec.1]

end

end SparseHamiltonian.GeneralSourceODE
