import PhysicalODELowerBound.Mesh.Model
import PhysicalODELowerBound.Access.Growth
import PhysicalODELowerBound.Access.MeshGrowth
import PhysicalODELowerBound.Access.MeshBoolean
import AdaptiveODELowerBound.Access.Control

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

/-!
# From oracle-generic bounds to forcing over the general-mesh physical oracle

Section `odel:sec:main` (manuscript lines 4105-4109: value, inverse and controlled calls) and the
encoding for the proof of Theorem `odel:thm:joint` (lines 4290-4294: at most two Boolean
membership queries per value call, also for inverse and controlled calls; source calls are known
operations).

Two transfers turn a lower bound for adaptive solvers over **any** oracle family with a hardness
certificate into `MeshForces`, for both access shapes (the physical oracle and its call forms):

* `meshForces_of_growth` (one-stage families, the weight method): if every adaptive solver of
  `F` over a unitary oracle family with search-weight growth `w` along `g` costs at least `b`,
  then `F` mesh-forces `b`. The physical oracle has growth `matrixWeight valueWeight`
  (`Access.searchGrowth_mesh`), its call forms the growth of their labels
  (`Access.searchGrowth_callFamily`).
* `meshForces_of_boolean` (families with any number of stages, Boolean membership programs): if
  the sampled-time access of `F` is implemented with costs `hardCost` (two per value call, none per
  location call) for every branch register, and every adaptive solver of `F` over a unitary
  oracle family implemented with costs `w` costs at least `2b`, then `F` mesh-forces `b`. The
  physical oracle is implemented with costs `matrixWeight hardCost = 2 · matrixWeight valueWeight`
  (`Access.implementsOn_mesh`, `ODELowerBoundExtensions.Release.matrixWeight_hardCost`), its call
  forms with the costs of their labels (`AdaptiveODELowerBound.Access.implementsOn_callFamily`).
-/

namespace PhysicalODELowerBound.Mesh

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.ODE NativeSparseBlockEncoding
open OracleCircuit SparseLinearSystems.Protocol
open AdaptiveHamiltonianLowerBound (SearchGrowth)
open AdaptiveHamiltonianLowerBound.Access (HardAccess valueWeight)
open ODELowerBoundExtensions.Release (meshOracle PublicSources SysOp)
open ConstantODELowerBound.Oracle (constData)
open AdaptiveODELowerBound.Model (TreeSolver)
open scoped InnerProduct InnerProductSpace

-- The release's physical workspace is a nested register product (as in `MeshSource`).
set_option synthInstance.maxSize 8192

variable {X N Z : Type} [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z]

/-- **Transfer for one-stage families by the weight method**: if every adaptive solver of the
one-stage family `F` at accuracy `ε`, over a unitary oracle family whose labels have
search-weight growth `w` along `g`, has worst-case cost at least `b`, and the stage data satisfy
the access conditions along `g`, then `F` forces `b` on the general-mesh physical oracle and on
its call forms. -/
theorem meshForces_of_growth [DecidableEq Z] {n m : ℕ} (hm : Even m) {s : ℕ}
    (F : Family X N Z 1 s) (g : (Fin n → Fin m) → X) (hD : HardAccess (constData F) g)
    {ε b : ℝ}
    (hb : ∀ (L W Fl E G : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
      [NormedAddCommGroup Fl] [InnerProductSpace ℂ Fl] [CompleteSpace Fl]
      [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E]
      [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
      (O : L → X → W →L[ℂ] W) (w : L → ℕ), (∀ l x, IsUnitary (O l x)) →
      SearchGrowth m (fun l j => O l (g j)) w →
      ∀ A : TreeSolver F O Fl E G ε, b ≤ A.tree.worstCost w) :
    MeshForces F ε b := by
  refine ⟨?_, ?_⟩
  · intro M σ ι _ _ Nsl d J₀ Jb hJ Fl E G _ _ _ _ _ _ _ _ _ _ A
    have hU := TimeDependentExtensions.MeshSource.physicalOracle_unitary (ι := ι)
      (ODELowerBoundExtensions.Release.stageData F.data σ) Nsl d J₀ Jb hJ.initial_unitary
      hJ.forcing_unitary
    have hv : b ≤ A.tree.worstCost (ODESourceQueryBudget.matrixWeight valueWeight) :=
      hb (Query ⊕ Bool) (TimeDependentExtensions.MeshSource.PhysicalSpace ι N Z M Nsl d) Fl E G
        (meshOracle F σ ι Nsl d J₀ Jb) (ODESourceQueryBudget.matrixWeight valueWeight) hU
        (Access.searchGrowth_mesh hm F g hD σ ι Nsl d hJ) A
    refine ⟨hv, hv.trans ?_⟩
    exact_mod_cast AdaptiveODELowerBound.Model.worstCost_mono_tree A.tree
      ODELowerBoundExtensions.Release.matrixWeight_value_le
  · intro M σ ι _ _ Nsl d J₀ Jb hJ Fl E G _ _ _ _ _ _ _ _ _ _ A
    have hU := TimeDependentExtensions.MeshSource.physicalOracle_unitary (ι := ι)
      (ODELowerBoundExtensions.Release.stageData F.data σ) Nsl d J₀ Jb hJ.initial_unitary
      hJ.forcing_unitary
    have hv : b ≤ A.tree.worstCost (fun c => ODESourceQueryBudget.matrixWeight valueWeight c.1) :=
      hb ((Query ⊕ Bool) × AdaptiveODELowerBound.Access.CallForm)
        (Joint Bool (TimeDependentExtensions.MeshSource.PhysicalSpace ι N Z M Nsl d)) Fl E G
        (AdaptiveODELowerBound.Access.callFamily (meshOracle F σ ι Nsl d J₀ Jb))
        (fun c => ODESourceQueryBudget.matrixWeight valueWeight c.1)
        (AdaptiveODELowerBound.Access.callFamily_unitary hU)
        (Access.searchGrowth_mesh_calls hm F g hD σ ι Nsl d hJ) A
    refine ⟨hv, hv.trans ?_⟩
    exact_mod_cast AdaptiveODELowerBound.Model.worstCost_mono_tree A.tree
      (fun c => ODELowerBoundExtensions.Release.matrixWeight_value_le c.1)

/-- **Transfer for Boolean-implemented families**: if, for every branch register `ι`, every
label of the sampled-time access of `F` is implemented on an isometric encoding by at most
`hardCost` queries of a Boolean phase oracle `x ↦ P.phase (y x)`, and every adaptive solver of
`F` at accuracy `ε` over a unitary oracle family on a finite-dimensional workspace implemented
with costs `w` by queries of a Boolean phase oracle with the same query function `y` has
worst-case cost at least `2b`, then
`F` forces `b` on the general-mesh physical oracle and on its call forms. -/
theorem meshForces_of_boolean {K s : ℕ} (F : Family X N Z K s) {I : Type} [Fintype I]
    (y : X → I → Bool)
    (hcert : ∀ (ι : Type) [Fintype ι], ∃ (B : Type) (_ : NormedAddCommGroup B)
      (_ : InnerProductSpace ℂ B) (_ : CompleteSpace B) (P : ProjFamily B I)
      (Enc : Workspace ι N Z K →L[ℂ] B), Enc† ∘L Enc = 1 ∧
        ∀ q, EncodedOracle.ImplementsOn (fun x => P.phase (y x)) (F.access ι q) Enc (hardCost q))
    {ε b : ℝ}
    (hb : ∀ (L W Fl E G B : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W]
      [CompleteSpace W] [FiniteDimensional ℂ W] [NormedAddCommGroup Fl] [InnerProductSpace ℂ Fl]
      [CompleteSpace Fl]
      [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E]
      [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
      [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B]
      (P : ProjFamily B I) (Enc : W →L[ℂ] B), Enc† ∘L Enc = 1 →
      ∀ (O : L → X → W →L[ℂ] W), (∀ l x, IsUnitary (O l x)) → ∀ (w : L → ℕ),
      (∀ l, EncodedOracle.ImplementsOn (fun x => P.phase (y x)) (O l) Enc (w l)) →
      ∀ A : TreeSolver F O Fl E G ε, 2 * b ≤ A.tree.worstCost w) :
    MeshForces F ε b := by
  refine ⟨?_, ?_⟩
  · intro M σ ι _ _ Nsl d J₀ Jb hJ Fl E G _ _ _ _ _ _ _ _ _ _ A
    obtain ⟨B, _, _, _, P, Enc, hEnc, hw⟩ :=
      hcert (TimeDependentODE.NativeSource.Label ι M × Fin M)
    obtain ⟨B', _, _, _, P', Enc', hEnc', hw'⟩ :=
      Access.implementsOn_mesh F σ ι Nsl d hJ P y Enc hEnc hardCost hw
    have hU := TimeDependentExtensions.MeshSource.physicalOracle_unitary (ι := ι)
      (ODELowerBoundExtensions.Release.stageData F.data σ) Nsl d J₀ Jb hJ.initial_unitary
      hJ.forcing_unitary
    have h2 := hb (Query ⊕ Bool) (TimeDependentExtensions.MeshSource.PhysicalSpace ι N Z M Nsl d)
      Fl E G B' P' Enc' hEnc' (meshOracle F σ ι Nsl d J₀ Jb) hU
      (ODESourceQueryBudget.matrixWeight hardCost) hw' A
    rw [ODELowerBoundExtensions.Release.matrixWeight_hardCost,
      AdaptiveODELowerBound.Model.worstCost_mul_tree] at h2
    push_cast at h2
    have hv : b ≤ A.tree.worstCost (ODESourceQueryBudget.matrixWeight valueWeight) := by
      linarith
    refine ⟨hv, hv.trans ?_⟩
    exact_mod_cast AdaptiveODELowerBound.Model.worstCost_mono_tree A.tree
      ODELowerBoundExtensions.Release.matrixWeight_value_le
  · intro M σ ι _ _ Nsl d J₀ Jb hJ Fl E G _ _ _ _ _ _ _ _ _ _ A
    obtain ⟨B, _, _, _, P, Enc, hEnc, hw⟩ :=
      hcert (TimeDependentODE.NativeSource.Label ι M × Fin M)
    obtain ⟨B', _, _, _, P', Enc', hEnc', hw'⟩ :=
      Access.implementsOn_mesh_calls F σ ι Nsl d hJ P y Enc hEnc hardCost hw
    have hU := TimeDependentExtensions.MeshSource.physicalOracle_unitary (ι := ι)
      (ODELowerBoundExtensions.Release.stageData F.data σ) Nsl d J₀ Jb hJ.initial_unitary
      hJ.forcing_unitary
    have h2 := hb ((Query ⊕ Bool) × AdaptiveODELowerBound.Access.CallForm)
      (Joint Bool (TimeDependentExtensions.MeshSource.PhysicalSpace ι N Z M Nsl d))
      Fl E G B' P' Enc' hEnc'
      (AdaptiveODELowerBound.Access.callFamily (meshOracle F σ ι Nsl d J₀ Jb))
      (AdaptiveODELowerBound.Access.callFamily_unitary hU)
      (fun c => ODESourceQueryBudget.matrixWeight hardCost c.1) hw' A
    have hfun : (fun c : (Query ⊕ Bool) × AdaptiveODELowerBound.Access.CallForm =>
        ODESourceQueryBudget.matrixWeight hardCost c.1) =
        fun c => 2 * ODESourceQueryBudget.matrixWeight valueWeight c.1 := by
      funext c
      exact congrFun ODELowerBoundExtensions.Release.matrixWeight_hardCost c.1
    rw [hfun, AdaptiveODELowerBound.Model.worstCost_mul_tree] at h2
    push_cast at h2
    have hv :
        b ≤ A.tree.worstCost (fun c => ODESourceQueryBudget.matrixWeight valueWeight c.1) := by
      linarith
    refine ⟨hv, hv.trans ?_⟩
    exact_mod_cast AdaptiveODELowerBound.Model.worstCost_mono_tree A.tree
      (fun c => ODELowerBoundExtensions.Release.matrixWeight_value_le c.1)

end

end PhysicalODELowerBound.Mesh
