import AdaptiveODELowerBound.Model.Solver
import AdaptiveODELowerBound.Access.Admissible
import AdaptiveHamiltonianLowerBound.Families
import ODELowerBoundExtensions.Psd.Theorem

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

/-!
# The positive semidefinite families against adaptive protocols: access and transfer

Manuscript: Theorem `odel:thm:psd`, the access conditions of the two hard
families for the weight method of the adaptive Hamiltonian lower bound.

* `hardAccess_psdSearchData`, `hardAccess_psdScalarData`: the gadget data have
  input-independent locators and one-bit entries along the identity, the scalar data along
  `Access.toBits` (`AdaptiveHamiltonianLowerBound.Access.HardAccess`, from
  `bitTable_value_bit`: the tables are the one-bit tables `psdSearchTable`, `psdScalarTable`,
  the diagonal and the dense padding are known words).
* `Model.TreeSolver.accurate_heat`: an adaptive solver of
  `ODELowerBoundExtensions.Psd.heatFamily D T x₀` is `ε`-accurate for the normalised solution
  `e^{-TD_x} x₀ / ‖e^{-TD_x} x₀‖`.
* `treeForces_of_heat`: the transfer to `Model.TreeForces` from a bound on every adaptive
  protocol over labels admissible for `D` (the sampled-time access of `heatFamily D` is
  `specOracles (ι × Fin 1) D`, `Psd.access_heatFamily`; its call forms are admissible by
  `Access.admissible_callFamily_spec`).
-/

universe uN uZ

namespace AdaptiveODELowerBound.Model

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.ODE NativeSparseBlockEncoding
open OracleCircuit SparseLinearSystems.Protocol
open AdaptiveHamiltonianLowerBound (DensityAccurate)
open ODELowerBoundExtensions.Psd
open scoped InnerProduct InnerProductSpace

/-- **Accuracy of an adaptive solver on a heat family**: the conditional output is `ε`-accurate
for the normalised solution `e^{-TD_x} x₀ / ‖·‖`. -/
theorem TreeSolver.accurate_heat {X N Z : Type*} [Fintype N] [DecidableEq N] {s : ℕ}
    (D : Data X N Z s) (T : ℝ) (hT : 0 ≤ T) (x₀ : EuclideanSpace ℂ N) {L W : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
    {O : L → X → W →L[ℂ] W} {Fl E G : Type*}
    [NormedAddCommGroup Fl] [InnerProductSpace ℂ Fl] [CompleteSpace Fl]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G] {ε : ℝ}
    (A : TreeSolver (heatFamily D T hT x₀) O Fl E G ε) (x : X) :
    DensityAccurate A.readout (A.tree.conditionalDensity x)
      (ODEStateNormalization.unitDirection (heat (D.matrix x) T x₀)) ε := by
  have h := A.accurate x _ (heatFamily_solves D T hT x₀ x)
  rw [heatFamily_T] at h
  exact h

end

end AdaptiveODELowerBound.Model

namespace AdaptiveODELowerBound.Psd

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.ODE SparseLowerBounds.Hamiltonian
open NativeSparseBlockEncoding OracleCircuit SparseLinearSystems.Protocol
open AdaptiveHamiltonianLowerBound (DensityAccurate)
open AdaptiveHamiltonianLowerBound.Access (Admissible HardAccess valueWeight toBits)
open ODELowerBoundExtensions.Psd
open AdaptiveODELowerBound.Model
open scoped InnerProduct InnerProductSpace

/-- **The gadget data satisfy the access conditions** along the identity: input-independent
locators and one-bit entries. -/
theorem hardAccess_psdSearchData (n μ s : ℕ) (u : ℝ) (hn : 1 ≤ n) (hs : 2 * 2 ^ μ + 1 ≤ s) :
    HardAccess (psdSearchData n μ s u hn hs) (fun j => j) where
  row_const _ _ := rfl
  column_const _ _ := rfl
  table_bit α := AdaptiveHamiltonianLowerBound.Access.bitTable_value_bit (psdSearchTable n μ s u)
    oneHotBits (fun ka => ⟨ka.1, ka.2, fun _ => rfl⟩) α
    (fun z => (z : Word (psdSearchBits n μ s u)))

/-- **The scalar data satisfy the access conditions** along `toBits`. -/
theorem hardAccess_psdScalarData (n s : ℕ) (u : ℝ) (hn : 1 ≤ n) (hs : 3 ≤ s) :
    HardAccess (psdScalarData n s u hn hs) (toBits (n := n)) where
  row_const _ _ := rfl
  column_const _ _ := rfl
  table_bit α := AdaptiveHamiltonianLowerBound.Access.bitTable_value_bit (psdScalarTable n s u)
    (fun j => toBits j) (fun k => ⟨k, 1, fun _ => rfl⟩) α
    (fun z => (z : Word (psdScalarBits n s u)))

section Transfer

variable {X : Type*} {N : Type uN} {Z : Type uZ} [Fintype N] [DecidableEq N] [Fintype Z]
  [AddCommGroup Z] {s' : ℕ} (D : Data X N Z s') (T : ℝ) (hT : 0 ≤ T) (x₀ : EuclideanSpace ℂ N)

/-- **Adaptive-protocol transfer for heat families**: if every adaptive protocol over an oracle
family whose labels are admissible for `D` with weights `w`, heralding success with probability
`≥ 2/3` and `ε`-accurate for the normalised `e^{-TD_x} x₀`, has worst-case cost at least `b`,
then `heatFamily D T x₀` tree-forces `b` (sampled-time access and call forms). The workspaces
range over the universe of the sampled-time workspace and of its call-form space. -/
theorem treeForces_of_heat {ε b : ℝ} (hrow : ∀ x x', D.rowOracle x = D.rowOracle x')
    (hcol : ∀ x x', D.columnOracle x = D.columnOracle x')
    (hb : ∀ (L : Type) (W : Type (max uN uZ)) (Fl E G : Type) [NormedAddCommGroup W]
      [InnerProductSpace ℂ W] [CompleteSpace W]
      [NormedAddCommGroup Fl] [InnerProductSpace ℂ Fl] [CompleteSpace Fl]
      [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E]
      [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
      (O : L → X → W →L[ℂ] W) (w : L → ℕ), (∀ l, Admissible D (O l) (w l)) →
      ∀ (P : Tree O Fl E) (e : E →L[ℂ] SysGarb N G), e† ∘L e = 1 →
      (∀ x, 2 / 3 ≤ P.successMass x) →
      (∀ x, DensityAccurate e (P.conditionalDensity x)
        (ODEStateNormalization.unitDirection (heat (D.matrix x) T x₀)) ε) →
      b ≤ P.worstCost w) :
    TreeForces (heatFamily D T hT x₀) ε b := by
  have hacc : ∀ (ι : Type) [Fintype ι],
      (heatFamily D T hT x₀).access ι = specOracles (ι × Fin 1) D :=
    fun ι _ => funext fun l => funext fun x => access_heatFamily D T hT x₀ ι l x
  have hval : ∀ q : Query, valueWeight q ≤ 1 := fun q => by cases q <;> decide
  refine ⟨fun ι _ Fl E G _ _ _ _ _ _ _ _ _ _ A => ?_, fun ι _ Fl E G _ _ _ _ _ _ _ _ _ _ A => ?_⟩
  · have hv : b ≤ A.tree.worstCost valueWeight :=
      hb Query (Workspace ι N Z 1) Fl E G ((heatFamily D T hT x₀).access ι) valueWeight
        (fun l => by
          rw [hacc ι]
          exact AdaptiveHamiltonianLowerBound.Access.admissible_specOracles _ D hrow hcol l)
        A.tree A.readout A.readout_isometry A.success (TreeSolver.accurate_heat D T hT x₀ A)
    exact ⟨hv, hv.trans (by exact_mod_cast worstCost_mono_tree A.tree hval)⟩
  · have hv : b ≤ A.tree.worstCost (fun c => valueWeight c.1) :=
      hb (Query × Access.CallForm) (Joint Bool (Workspace ι N Z 1)) Fl E G
        (Access.callFamily ((heatFamily D T hT x₀).access ι)) (fun c => valueWeight c.1)
        (fun c => by
          rw [hacc ι]
          exact Access.admissible_callFamily_spec (ι × Fin 1) D hrow hcol c)
        A.tree A.readout A.readout_isometry A.success (TreeSolver.accurate_heat D T hT x₀ A)
    exact ⟨hv, hv.trans (by exact_mod_cast worstCost_mono_tree A.tree fun c => hval c.1)⟩

end Transfer

end

end AdaptiveODELowerBound.Psd
