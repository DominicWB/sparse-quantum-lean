import ODELowerBoundExtensions.Release.Access
import ConstantODELowerBound.Oracle
import PhysicalODELowerBound.Access.Growth

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

/-!
# The general-mesh physical oracle on one-stage families: search-weight growth

Manuscript lines 4105-4109 (access model), 4114-4115 ("The lower bounds thus apply to Theorems
`ode:thm:main` and `ode:thm:time`") and 4119-4122 (public location lists, all unknown information
in exact finite-word entries, public source preparation).

The released general-mesh solver `TimeDependentExtensions.ODE.solver` queries the physical oracle
`ODELowerBoundExtensions.Release.meshOracle F σ ι N d J₀ J_b` of the data of a family `F` along a
public placement `σ : Fin M → Fin K` of mesh pieces into stages. For a **one-stage** family
(`K = 1`: the constant-coefficient families, `hamFamily` and `Psd.heatFamily` and their zero
paddings) every piece reads the stage-`0` data `ConstantODELowerBound.Oracle.constData F`, so

* the access along any placement is the spectated native access of `constData F`
  (`stageAccess_oneStage`), for every one-stage family (the generic form of
  `ODELowerBoundExtensions.Release.stageAccess_hamFamily`);
* for data `constData F` with input-independent locators and one-bit entries along `g`
  (`AdaptiveHamiltonianLowerBound.Access.HardAccess`), the physical oracle has search-weight
  growth with the value-query weight `ODESourceQueryBudget.matrixWeight valueWeight`
  (`searchGrowth_mesh`, the generic form of
  `ODELowerBoundExtensions.Release.searchGrowth_release_ham`):
  matrix labels through the normal form `ODELowerBoundExtensions.Release.physicalOracle_normal_form`
  and `ODELowerBoundExtensions.Release.searchGrowth_conj_fiber`, public source labels as
  input-independent unitaries (`ODELowerBoundExtensions.Release.physicalOracle_inr_const`);
* every call form of every physical label (`AdaptiveODELowerBound.Access.callFamily`: plain,
  inverse, controlled, controlled inverse) has the growth of its label
  (`searchGrowth_mesh_calls`, from `searchGrowth_callFamily`): a controlled or controlled-inverse
  value call costs one value query, a controlled location or source call none.
-/

namespace PhysicalODELowerBound.Access

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.ODE NativeSparseBlockEncoding
open OracleCircuit TimeDependentExtensions
open AdaptiveHamiltonianLowerBound (SearchGrowth)
open AdaptiveHamiltonianLowerBound.Access (HardAccess valueWeight)
open ODELowerBoundExtensions.Release (meshOracle stageAccess PublicSources SysOp)
open ConstantODELowerBound.Oracle (constData)
open AdaptiveODELowerBound.Access (callFamily)

-- The release's physical workspace is a nested register product (as in `MeshSource`).
set_option synthInstance.maxSize 8192

/-- **The access of a one-stage family along a placement is the spectated native access** of its
stage-`0` data: every piece reads the same generator. -/
theorem stageAccess_oneStage {X N Z : Type} [Fintype N] [DecidableEq N] [Fintype Z]
    [AddCommGroup Z] {s : ℕ} (F : Family X N Z 1 s) {M : ℕ} (σ : Fin M → Fin 1) (ι : Type)
    [Fintype ι] (l : Query) (x : X) :
    stageAccess F σ ι l x = specOracles (ι × Fin M) (constData F) l x := by
  ext Ψ b : 2
  have h : oracles (ODELowerBoundExtensions.Release.stageData F.data σ) l (x, b.2) =
      oracles (constData F) l x := by
    rw [ODELowerBoundExtensions.Release.stageData,
      ODELowerBoundExtensions.Release.oracles_reindexData,
      ConstantODELowerBound.Oracle.oracles_constData]
    exact congrArg (fun r => oracles F.data l (x, r)) (Subsingleton.elim _ _)
  exact congrArg (fun O => O (Ψ b)) h

/-- **The general-mesh physical oracle on a one-stage family has search-weight growth** along
any placement `σ`, for any spectator index, slot count, degree and public source interfaces, with
the value-query weight `matrixWeight valueWeight` (`valueWeight` on matrix labels, `0` on source
labels), whenever the stage data satisfy the access conditions along `g`. -/
theorem searchGrowth_mesh {n m : ℕ} (hm : Even m) {X N Z : Type} [Fintype N] [DecidableEq N]
    [Fintype Z] [AddCommGroup Z] [DecidableEq Z] {s : ℕ} (F : Family X N Z 1 s)
    (g : (Fin n → Fin m) → X) (hD : HardAccess (constData F) g) {M : ℕ} (σ : Fin M → Fin 1)
    (ι : Type) [Fintype ι] [DecidableEq ι] (Nsl d : ℕ) {J₀ : X → SysOp N}
    {Jb : X → Fin M → SysOp N} (hJ : PublicSources J₀ Jb) :
    SearchGrowth m (fun l j => meshOracle F σ ι Nsl d J₀ Jb l (g j))
      (ODESourceQueryBudget.matrixWeight valueWeight) := by
  intro a ha l
  rcases l with q | b
  · obtain ⟨Ω, hΩ, U, hU⟩ :=
      ODELowerBoundExtensions.Release.physicalOracle_normal_form
        (ODELowerBoundExtensions.Release.stageData F.data σ) ι Nsl d J₀ Jb
    have hspec : SearchGrowth m (fun (q : Query) j =>
        specOracles (TimeDependentODE.NativeSource.Label ι M × Fin M) (constData F) q (g j))
        valueWeight :=
      AdaptiveHamiltonianLowerBound.searchGrowth_admissible hm (constData F) g hD _ _
        (fun q => AdaptiveHamiltonianLowerBound.Access.admissible_specOracles _ (constData F)
          hD.row_const hD.column_const q)
    have hc := ODELowerBoundExtensions.Release.searchGrowth_conj_fiber Ω U _ _ hspec a ha q
    have heq : ∀ j, meshOracle F σ ι Nsl d J₀ Jb (Sum.inl q) (g j) =
        U.symm.conjStarAlgEquiv (Joint.fiber fun _ : Ω =>
          specOracles (TimeDependentODE.NativeSource.Label ι M × Fin M) (constData F) q
            (g j)) := by
      intro j
      have hs := stageAccess_oneStage F σ (TimeDependentODE.NativeSource.Label ι M) q (g j)
      dsimp only [stageAccess] at hs
      rw [meshOracle, hU, hs]
    exact ⟨AdaptiveHamiltonianLowerBound.wgrowth_congr hc.1 (fun j => (heq j).symm),
      AdaptiveHamiltonianLowerBound.wgrowth_congr hc.2 (fun j => by beta_reduce; rw [heq j])⟩
  · have hu := MeshSource.physicalOracle_unitary (ι := ι)
      (ODELowerBoundExtensions.Release.stageData F.data σ) Nsl d J₀ Jb hJ.initial_unitary
      hJ.forcing_unitary (Sum.inr b)
    have hc := ODELowerBoundExtensions.Release.physicalOracle_inr_const
      (ODELowerBoundExtensions.Release.stageData F.data σ) ι Nsl d hJ b
    show AdaptiveHamiltonianLowerBound.WGrowth _ _
        ((AdaptiveHamiltonianLowerBound.searchLam m a ^ 2) ^ 0) ∧
      AdaptiveHamiltonianLowerBound.WGrowth _ _
        ((AdaptiveHamiltonianLowerBound.searchLam m a ^ 2) ^ 0)
    rw [pow_zero]
    refine ⟨AdaptiveHamiltonianLowerBound.Access.wgrowth_const_of_eq _ _
        (fun j j' => hc (g j) (g j'))
        (fun j v => LinearSystemLowerBound.isUnitary_norm (hu (g j)) v),
      AdaptiveHamiltonianLowerBound.Access.wgrowth_const_of_eq _ _
        (fun j j' => by simp only [meshOracle]; rw [hc (g j) (g j')])
        (fun j v => LinearSystemLowerBound.isUnitary_norm (hu (g j)).adjoint v)⟩

/-- **Call forms of the general-mesh physical oracle on a one-stage family**: under the
hypotheses of `searchGrowth_mesh`, every call form of every physical label has the search-weight
growth of its label, with the value-query weight `matrixWeight valueWeight` of the label. -/
theorem searchGrowth_mesh_calls {n m : ℕ} (hm : Even m) {X N Z : Type} [Fintype N]
    [DecidableEq N] [Fintype Z] [AddCommGroup Z] [DecidableEq Z] {s : ℕ} (F : Family X N Z 1 s)
    (g : (Fin n → Fin m) → X) (hD : HardAccess (constData F) g) {M : ℕ} (σ : Fin M → Fin 1)
    (ι : Type) [Fintype ι] [DecidableEq ι] (Nsl d : ℕ) {J₀ : X → SysOp N}
    {Jb : X → Fin M → SysOp N} (hJ : PublicSources J₀ Jb) :
    SearchGrowth m (fun c j => callFamily (meshOracle F σ ι Nsl d J₀ Jb) c (g j))
      (fun c => ODESourceQueryBudget.matrixWeight valueWeight c.1) := by
  have h := searchGrowth_callFamily (searchGrowth_mesh hm F g hD σ ι Nsl d hJ)
  unfold callFamily at h ⊢
  exact h

end

end PhysicalODELowerBound.Access
