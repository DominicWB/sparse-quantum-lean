import AdaptiveODELowerBound.Model.Solver
import ODELowerBoundExtensions.Padding.ZeroPad

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

/-!
# Readout transfer of padded adaptive solvers

Manuscript line 4340 ("Known zero padding permits any sufficiently large qubit register")
and 4437-4445 ("Pad dimensions to a common known size if desired").

* `densityAccurate_padReadout`: if a density operator, read through `e` on the padded system
  `N ⊕ P`, is `ε`-accurate for the padded target `ψ ⊕ 0`, then read through the released
  `LowerBoundRemarks.HamiltonianPadding.padReadout P G i₀ ∘ e` on the original system `N` it is
  `ε`-accurate for `ψ` (the density form of `Padding.heraldedAccurate_padReadout`, by
  `outObs_padReadout` and the block observable `blockObs`).
* `treeAccurate_of_zeroPad`: for a zero padding `F'` of `F` (`Padding.ZeroPad`) and every adaptive
  solver of `F'`, the conditional output read through `padReadout P G i₀ ∘ readout` is
  `ε`-accurate for the normalised solution of every instance of `F`.
-/

namespace AdaptiveODELowerBound.Padding

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.ODE SparseLowerBounds.Readout
open SparseLowerBounds.Hamiltonian (HsInstance.inlOp)
open LowerBoundRemarks.HamiltonianPadding
open AdaptiveHamiltonianLowerBound (DensityAccurate)
open AdaptiveODELowerBound.Model
open scoped InnerProduct InnerProductSpace

variable {N : Type*} [Fintype N] [DecidableEq N] {P : Type*} [Fintype P] [DecidableEq P]

/-- **Density readout transfer without loss**: accuracy for the padded target `ψ ⊕ 0` through
`e` is accuracy for `ψ` through `padReadout P G i₀ ∘ e`, at the same `ε`. -/
theorem densityAccurate_padReadout {G E : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [CompleteSpace G] [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [FiniteDimensional ℂ E] (i₀ : N) (e : E →L[ℂ] SysGarb (N ⊕ P) G) (ρ : E →L[ℂ] E)
    (ψ : EuclideanSpace ℂ N) (ε : ℝ) (h : DensityAccurate e ρ (HsInstance.inlOp N P ψ) ε) :
    DensityAccurate (padReadout P G i₀ ∘L e) ρ ψ ε := by
  intro M hM hM1
  have hA : (obsMat M).IsHermitian := hM.map _
  have hc : star (obsMat M i₀ i₀) = obsMat M i₀ i₀ := hA.apply i₀ i₀
  have hn : ‖blockObs P M (obsMat M i₀ i₀)‖ ≤ 1 :=
    (norm_blockObs_le M _).trans (max_le hM1 ((norm_obsMat_apply_le M i₀ i₀).trans hM1))
  have h' := h _ (isSelfAdjoint_blockObs hM hc) hn
  rw [blockObs_inlOp, inner_inlOp] at h'
  rw [outObs_padReadout]
  exact h'

/-- **Readout of a padded adaptive solver**: for every adaptive solver of the zero padding `F'`
of `F`, every `i₀ : N` and every solution of instance `x` of `F`, the conditional output read
through `padReadout P G i₀ ∘ readout` is `ε`-accurate for `x(T)/‖x(T)‖`. -/
theorem treeAccurate_of_zeroPad {X Z Z' : Type*} [Fintype Z'] [AddCommGroup Z'] {K s : ℕ}
    {F' : Family X (N ⊕ P) Z' K s} {F : Family X N Z K s}
    (hF : ODELowerBoundExtensions.Padding.ZeroPad F' F) {L W : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W] {O : L → X → W →L[ℂ] W}
    {Fl E G : Type*} [NormedAddCommGroup Fl] [InnerProductSpace ℂ Fl] [CompleteSpace Fl]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G] {ε : ℝ}
    (A : TreeSolver F' O Fl E G ε) (i₀ : N) (x : X) {sol : ℝ → EuclideanSpace ℂ N}
    (h : F.Solves x sol) :
    DensityAccurate (padReadout P G i₀ ∘L A.readout) (A.tree.conditionalDensity x)
      (ODEStateNormalization.unitDirection (sol F.T)) ε := by
  have h' := A.accurate x _ (hF.solves h)
  beta_reduce at h'
  rw [hF.T_eq, ODELowerBoundExtensions.Padding.unitDirection_inlOp] at h'
  exact densityAccurate_padReadout i₀ A.readout _ _ ε h'

end

end AdaptiveODELowerBound.Padding
