import GeneralSourceExtensions.Mesh.Theorem
import TimeDependentExtensions.ODE.Corollaries
import TimeDependentExtensions.Mesh.Duhamel

/-!
# Non-vacuity of the mesh hypotheses

* `exists_isMeshPropagator`: pieces continuous on their closed intervals have a propagator on the
  mesh (`IsMeshPropagator`), from every start time and every initial value;
* `sampleError_le_of_lipschitz`: `β_r`-Lipschitz pieces with left-endpoint sample errors `δ_r`
  have the integrated certificate `ΔG ≤ ∑_r (β_r Δ_r² / 2 + δ_r Δ_r)`.
-/

set_option autoImplicit false

namespace SparseHamiltonian.GeneralSourceExtensions.Mesh

noncomputable section
open ContinuousLinearMap NativeSparseBlockEncoding Set MeasureTheory
open TimeDependentExtensions
open SparseHamiltonian.TimeDependentODE (Accretive SolvesODE)
open scoped BigOperators InnerProduct

section Existence

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

omit [CompleteSpace V] in
/-- A solution of the time-shifted homogeneous equation, shifted back. -/
theorem solvesODE_shift {G : ℝ → V →L[ℂ] V} {x : ℝ → V} {a c t₀ : ℝ}
    (hx : SolvesODE (fun u => G (u + t₀)) 0 x a c) :
    SolvesODE G 0 (fun u => x (u - t₀)) (a + t₀) (c + t₀) := by
  intro u hu
  have hmaps : MapsTo (fun v : ℝ => v - t₀) (Icc (a + t₀) (c + t₀)) (Icc a c) := by
    intro v hv
    exact ⟨by linarith [hv.1], by linarith [hv.2]⟩
  have hg : HasDerivWithinAt (fun v : ℝ => v - t₀) 1 (Icc (a + t₀) (c + t₀)) u :=
    ((hasDerivAt_id' u).sub_const t₀).hasDerivWithinAt
  have h := (hx (u - t₀) (hmaps hu)).scomp u hg hmaps
  simpa only [one_smul, sub_add_cancel, Function.comp_def, Pi.zero_apply, add_zero] using h

variable {M : ℕ}

/-- **Existence of propagators on a mesh.** Pieces continuous on their closed intervals have a
propagator: from every start time `t₀ ∈ [0, T]` and every value, a homogeneous solution solving
every piece on the part of its interval after `t₀`. -/
theorem exists_isMeshPropagator {G : Fin M → ℝ → V →L[ℂ] V} {t : ℕ → ℝ} {T : ℝ}
    (hmesh : IsMesh t M T)
    (hGc : ∀ r : Fin M, ContinuousOn (G r) (Icc (t r) (t ((r : ℕ) + 1)))) :
    ∃ U : ℝ → V → ℝ → V, IsMeshPropagator G t T U := by
  classical
  let Gq : ℕ → ℝ → V →L[ℂ] V := fun r => if h : r < M then G ⟨r, h⟩ else 0
  have hGq : ∀ (r : ℕ) (h : r < M), Gq r = G ⟨r, h⟩ := fun r h => dif_pos h
  have hex : ∀ t₀ ∈ Icc 0 T, ∀ w : V, ∃ y : ℝ → V, y t₀ = w ∧
      ∀ r : Fin M, t₀ ≤ t ((r : ℕ) + 1) →
        SolvesODE (G r) 0 y (max t₀ (t r)) (t ((r : ℕ) + 1)) := by
    intro t₀ ht₀ w
    let s : ℕ → ℝ := fun r => max t₀ (t r) - t₀
    have hs0 : s 0 = 0 := by
      simp only [s, hmesh.zero, max_eq_left ht₀.1, sub_self]
    have hsmono : Monotone s := fun r q hrq =>
      sub_le_sub_right (max_le_max le_rfl (hmesh.mono hrq)) t₀
    have hcont : ∀ r < M, ContinuousOn (fun u => Gq r (u + t₀)) (Icc (s r) (s (r + 1))) := by
      intro r hr
      by_cases hst : t₀ ≤ t (r + 1)
      · have hmaps : MapsTo (fun u : ℝ => u + t₀) (Icc (s r) (s (r + 1)))
            (Icc (t r) (t (r + 1))) := by
          intro u hu
          simp only [s, max_eq_right hst] at hu
          constructor
          · linarith [hu.1, le_max_right t₀ (t r)]
          · linarith [hu.2]
        rw [hGq r hr]
        exact (hGc ⟨r, hr⟩).comp (continuous_add_const t₀).continuousOn hmaps
      · push Not at hst
        have h1 : s r = 0 := by
          simp only [s, max_eq_left ((hmesh.mono (Nat.le_succ r)).trans hst.le), sub_self]
        have h2 : s (r + 1) = 0 := by
          simp only [s, max_eq_left hst.le, sub_self]
        rw [h1, h2, Icc_self]
        exact continuousOn_singleton _ _
    obtain ⟨x, hx0, hx⟩ := TimeDependentExtensions.ODE.exists_piecewise_solution
      (fun r u => Gq r (u + t₀)) (fun _ _ => 0) hs0 hsmono M hcont
      (fun _ _ => continuousOn_const) w
    refine ⟨fun u => x (u - t₀), by simp [hx0], fun r hst => ?_⟩
    have h := solvesODE_shift (hx r r.isLt)
    have ha : s r + t₀ = max t₀ (t r) := by simp only [s, sub_add_cancel]
    have hc : s ((r : ℕ) + 1) + t₀ = t ((r : ℕ) + 1) := by
      simp only [s, max_eq_right hst, sub_add_cancel]
    rw [ha, hc] at h
    have hfun : (fun u => Gq r u) = G r := by
      funext u
      rw [hGq r r.isLt]
    have hz : (fun _ : ℝ => (0 : V)) = 0 := rfl
    simpa only [hfun, hz] using h
  refine ⟨fun t₀ w => if ht : t₀ ∈ Icc 0 T then (hex t₀ ht w).choose else fun _ => w, ?_⟩
  intro t₀ ht₀ w
  simp only [dif_pos ht₀]
  exact (hex t₀ ht₀ w).choose_spec

end Existence

section Lipschitz

variable {X n Z : Type*} [Fintype n] [DecidableEq n] {s M : ℕ}

/-- **Lipschitz pieces.** If piece `r` is `β_r`-Lipschitz on its closed interval and its sample
error at the left endpoint is at most `δ_r`, the integrated sample certificate is at most
`∑_r (β_r Δ_r² / 2 + δ_r Δ_r)`. -/
theorem sampleError_le_of_lipschitz (D : Data (X × Fin M) n Z s) (x : X) {t : ℕ → ℝ} {T : ℝ}
    (hmesh : IsMesh t M T) (G : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (β δ : Fin M → ℝ)
    (hLip : ∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), ∀ w ∈ Icc (t r) (t ((r : ℕ) + 1)),
      ‖G r u - G r w‖ ≤ β r * |u - w|)
    (hδ : ∀ r : Fin M,
      ‖G r (t r) - SparseStateOverlap.matrixOperator (D.matrix (x, r))‖ ≤ δ r) :
    sampleError D x t G ≤
      ∑ r : Fin M, (β r * (t ((r : ℕ) + 1) - t r) ^ 2 / 2 + δ r * (t ((r : ℕ) + 1) - t r)) := by
  unfold sampleError
  exact Finset.sum_le_sum fun r _ =>
    integral_le_of_lipschitz' (G r) _ (hmesh.mono (Nat.le_succ r)) (hLip r) (hδ r)

end Lipschitz

end

end SparseHamiltonian.GeneralSourceExtensions.Mesh
