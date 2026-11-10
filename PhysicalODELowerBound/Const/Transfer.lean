import PhysicalODELowerBound.Const.Model
import PhysicalODELowerBound.Access.Growth
import ConstantODELowerBound.Access

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

/-!
# From oracle-generic bounds to forcing over the constant-coefficient physical oracle

Section `odel:sec:main` (value, inverse and controlled calls; public location lists, exact
finite-word entries, public source preparation).

`constForces_of_growth`: if every adaptive solver of the one-stage family `F` over a unitary
oracle family with search-weight growth `w` along `g` costs at least `b`, and the stage data
`constData F` satisfy the access conditions along `g`, then `F` forces `b` on the physical oracle
of the released constant-coefficient solver and on its call forms. The oracle has growth
`matrixWeight valueWeight` (`ConstantODELowerBound.Access.searchGrowth_const`), its call forms the
growth of their labels (`Access.searchGrowth_callFamily`); unitarity is
`ConstantODELowerBound.Oracle.constOracle_unitary` and
`AdaptiveODELowerBound.Access.callFamily_unitary`.

`searchGrowth_const_calls` states the call-form growth on its own: every call form of every label
of the constant-coefficient physical oracle has the growth of its label (one value query for a
value call in any form, none for a location or source call).
-/

namespace PhysicalODELowerBound.Const

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.ODE NativeSparseBlockEncoding
open OracleCircuit SparseLinearSystems.Protocol
open AdaptiveHamiltonianLowerBound (SearchGrowth)
open AdaptiveHamiltonianLowerBound.Access (HardAccess valueWeight)
open ConstantODELowerBound.Oracle (constData constOracle PublicConstSources)
open AdaptiveODELowerBound.Model (TreeSolver)
open AdaptiveODELowerBound.Access (callFamily)
open ODELowerBoundExtensions.Release (SysOp)

-- The released solver's physical workspace is a nested register product.
set_option synthInstance.maxSize 8192
set_option maxRecDepth 4096

variable {X N Z : Type} [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z] [DecidableEq Z]
  {s : ℕ}

/-- **Call forms of the constant-coefficient physical oracle**: on data `constData F` with the
access conditions along `g`, every call form of every label of `constOracle F ι N_m T_sl d J₀ J_b`
(public source interfaces) has the search-weight growth of its label, with the value-query weight
`matrixWeight valueWeight` of the label. -/
theorem searchGrowth_const_calls {n m : ℕ} (hm : Even m) (F : Family X N Z 1 s)
    (g : (Fin n → Fin m) → X) (hD : HardAccess (constData F) g) (ι : Type) [Fintype ι]
    [DecidableEq ι] (Nm Tsl d : ℕ) {J₀ Jb : X → SysOp N} (hJ : PublicConstSources J₀ Jb) :
    SearchGrowth m (fun c j => callFamily (constOracle F ι Nm Tsl d J₀ Jb) c (g j))
      (fun c => ODESourceQueryBudget.matrixWeight valueWeight c.1) := by
  have h := PhysicalODELowerBound.Access.searchGrowth_callFamily
    (ConstantODELowerBound.Access.searchGrowth_const hm (constData F) g hD ι Nm Tsl d hJ)
  unfold callFamily at h ⊢
  exact h

/-- **Transfer for one-stage families by the weight method, constant-coefficient oracle**: if
every adaptive solver of `F` at accuracy `ε` over a unitary oracle family whose labels have
search-weight growth `w` along `g` has worst-case cost at least `b`, and `constData F` satisfies
the access conditions along `g`, then `F` forces `b` on the physical oracle of the released
constant-coefficient solver and on its call forms. -/
theorem constForces_of_growth {n m : ℕ} (hm : Even m) (F : Family X N Z 1 s)
    (g : (Fin n → Fin m) → X) (hD : HardAccess (constData F) g) {ε b : ℝ}
    (hb : ∀ (L W Fl E G : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
      [NormedAddCommGroup Fl] [InnerProductSpace ℂ Fl] [CompleteSpace Fl]
      [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E]
      [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
      (O : L → X → W →L[ℂ] W) (w : L → ℕ), (∀ l x, IsUnitary (O l x)) →
      SearchGrowth m (fun l j => O l (g j)) w →
      ∀ A : TreeSolver F O Fl E G ε, b ≤ A.tree.worstCost w) :
    ConstForces F ε b := by
  have hw := ODELowerBoundExtensions.Release.matrixWeight_value_le
  refine ⟨?_, ?_⟩
  · intro ι _ _ Nm Tsl d J₀ Jb hJ Fl E G _ _ _ _ _ _ _ _ _ _ A
    have hv : b ≤ A.tree.worstCost (ODESourceQueryBudget.matrixWeight valueWeight) :=
      hb (Query ⊕ Bool) (ODEFinalNativeSource.Physical ι N Z Nm Tsl d) Fl E G
        (constOracle F ι Nm Tsl d J₀ Jb) (ODESourceQueryBudget.matrixWeight valueWeight)
        (ConstantODELowerBound.Oracle.constOracle_unitary F ι Nm Tsl d hJ)
        (ConstantODELowerBound.Access.searchGrowth_const hm (constData F) g hD ι Nm Tsl d hJ) A
    refine ⟨hv, hv.trans ?_⟩
    exact_mod_cast AdaptiveODELowerBound.Model.worstCost_mono_tree A.tree hw
  · intro ι _ _ Nm Tsl d J₀ Jb hJ Fl E G _ _ _ _ _ _ _ _ _ _ A
    have hv : b ≤ A.tree.worstCost (fun c => ODESourceQueryBudget.matrixWeight valueWeight c.1) :=
      hb ((Query ⊕ Bool) × AdaptiveODELowerBound.Access.CallForm)
        (Joint Bool (ODEFinalNativeSource.Physical ι N Z Nm Tsl d)) Fl E G
        (callFamily (constOracle F ι Nm Tsl d J₀ Jb))
        (fun c => ODESourceQueryBudget.matrixWeight valueWeight c.1)
        (AdaptiveODELowerBound.Access.callFamily_unitary
          (ConstantODELowerBound.Oracle.constOracle_unitary F ι Nm Tsl d hJ))
        (searchGrowth_const_calls hm F g hD ι Nm Tsl d hJ) A
    refine ⟨hv, hv.trans ?_⟩
    exact_mod_cast AdaptiveODELowerBound.Model.worstCost_mono_tree A.tree (fun c => hw c.1)

end

end PhysicalODELowerBound.Const
