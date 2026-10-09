import SparseLowerBounds.ODE.Model

set_option synthInstance.maxHeartbeats 400000

section
/-!
# Uniqueness of solutions in the piecewise-constant ODE class

Manuscript lines 3675-3678 (the output is the normalised solution `x(T)/‖x(T)‖`).
`ODE.Solver.accurate` (ODE/Model) demands accuracy for the endpoint of **every**
solution of an instance (the release's `TimeDependentODE.Outcome` form), while
the class promise `Family.InClass` provides one solution. This module shows the
two requirements coincide: a piecewise-constant instance has at most one
solution on `[0, T]` (`Family.solves_eqOn`), hence one endpoint
(`Family.solves_endpoint_unique`), so a property of the endpoint holds for every
solution iff it holds for one (`Family.forall_solves_iff`). In particular the
hypothesis `Solver.accurate` is satisfiable by honest solvers that are accurate
for the promised solution.

On each stage the vector field `z ↦ -(G_k z) + b_k` is Lipschitz with constant
`‖G_k‖` on the whole space, so the stage solution is unique by Mathlib's
Grönwall uniqueness theorem `ODE_solution_unique_of_mem_Icc_right`
(`solvesODE_const_eqOn`, for a general Hilbert space `V`); induction over the
public breakpoints `start k` glues the stages.

No proof of a lower bound uses this module; the statement guide imports it.
-/

namespace SparseLowerBounds.ODE

noncomputable section
open SparseHamiltonian Set

/-- **Uniqueness on one stage.** Two solutions of `x' = -L x + c` (constant
generator and source, the release's `SolvesODE`) on `[a, b]` that agree at `a`
agree on `[a, b]`. -/
theorem solvesODE_const_eqOn {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (L : V →L[ℂ] V) (c : V) {x y : ℝ → V} {a b : ℝ}
    (hx : TimeDependentODE.SolvesODE (fun _ => L) (fun _ => c) x a b)
    (hy : TimeDependentODE.SolvesODE (fun _ => L) (fun _ => c) y a b) (ha : x a = y a) :
    EqOn x y (Icc a b) := by
  have hlip : LipschitzWith ‖L‖₊ (fun z => -(L z) + c) :=
    LipschitzWith.of_dist_le_mul fun z w => by
      rw [dist_add_right, dist_neg_neg]
      exact L.lipschitz.dist_le_mul z w
  have hd : ∀ {z : ℝ → V}, TimeDependentODE.SolvesODE (fun _ => L) (fun _ => c) z a b →
      ∀ t ∈ Ico a b, HasDerivWithinAt z (-(L (z t)) + c) (Ici t) t :=
    fun hz t ht => (hz t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ht)
  exact ODE_solution_unique_of_mem_Icc_right (v := fun _ z => -(L z) + c)
    (s := fun _ => univ) (fun _ _ => hlip.lipschitzOnWith) hx.continuousOn (hd hx)
    (fun _ _ => trivial) hy.continuousOn (hd hy) (fun _ _ => trivial) ha

namespace Family

variable {X N Z : Type*} [Fintype N] [DecidableEq N] {K s : ℕ}

/-- **Uniqueness of solutions** (lines 3675-3678): two solutions of the same
instance `x` of a piecewise-constant family agree on `[0, T]`. -/
theorem solves_eqOn (F : Family X N Z K s) {x : X} {sol sol' : ℝ → EuclideanSpace ℂ N}
    (h : F.Solves x sol) (h' : F.Solves x sol') : EqOn sol sol' (Icc 0 F.T) := by
  have key : ∀ k, k ≤ K → EqOn sol sol' (Icc 0 (F.start k)) := by
    intro k
    induction k with
    | zero =>
      intro _ t ht
      rw [F.start_zero] at ht
      rw [le_antisymm ht.2 ht.1, h.1, h'.1]
    | succ k ih =>
      intro hk t ht
      have hk' : k < K := hk
      have ih' := ih hk'.le
      by_cases htk : t ≤ F.start k
      · exact ih' ⟨ht.1, htk⟩
      · exact solvesODE_const_eqOn _ _ (h.2 ⟨k, hk'⟩) (h'.2 ⟨k, hk'⟩)
          (ih' ⟨F.start_nonneg k, le_rfl⟩) ⟨(not_le.mp htk).le, ht.2⟩
  exact key K le_rfl

/-- **The endpoint is unique**: all solutions of an instance have the same
`x(T)`. -/
theorem solves_endpoint_unique (F : Family X N Z K s) {x : X}
    {sol sol' : ℝ → EuclideanSpace ℂ N} (h : F.Solves x sol) (h' : F.Solves x sol') :
    sol F.T = sol' F.T :=
  F.solves_eqOn h h' ⟨F.T_nonneg, le_rfl⟩

/-- **Every solution vs. one solution.** Given one solution `sol₀` of instance
`x`, a property of the endpoint holds for every solution iff it holds for
`sol₀ F.T`. Hence `Solver.accurate` (accuracy for every solution) is the
paper's accuracy requirement for the solution promised by `InClass`. -/
theorem forall_solves_iff (F : Family X N Z K s) {x : X}
    {sol₀ : ℝ → EuclideanSpace ℂ N} (h₀ : F.Solves x sol₀) (P : EuclideanSpace ℂ N → Prop) :
    (∀ sol, F.Solves x sol → P (sol F.T)) ↔ P (sol₀ F.T) :=
  ⟨fun hall => hall sol₀ h₀, fun hP sol hs => by rwa [F.solves_endpoint_unique hs h₀]⟩

end Family

end

end SparseLowerBounds.ODE
end
