import DeferredMeasurementLowerBounds.Access.TimeAccess
import ODELowerBoundExtensions.Release.Normal
import ReleasedODESolverLowerBounds.Access.Absorb
import ReleasedODESolverLowerBounds.Access.Dimension
import ReleasedODESolverLowerBounds.Access.ValueConj

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

/-!
# The general-mesh physical oracle in spectator form

Manuscript Section `odel:sec:main`, lines 3669-3673 (value oracle and locators, "their inverses
and controls, with a coherent time address"), and lines 3678-3679 ("The lower bounds thus apply
to Theorems `ode:thm:main` and `ode:thm:time`"); Theorem `ode:thm:time` (line 2879).

The matrix labels of the released general-mesh solver's physical oracle
`ODELowerBoundExtensions.Release.meshOracle F σ ι N d J₀ J_b` are, by the released normal form
`ODELowerBoundExtensions.Release.physicalOracle_normal_form`, `U⁻¹ (1_Ω ⊗ A_l(x)) U` with the
sampled-time access `A` of the staged data on the branch register `Label ι M`; that access is
itself the spectator lift over the branch register of its one-branch form `meshPrim F σ`
(`TimeDependentODE.labelOracle` with `TimeDependentODE.sample` on the branch `Unit`), which does
not depend on `ι`, the slot count, the degree or the source interfaces.

* `meshOracle_spectatorForm`: the matrix labels are in spectator form over `meshPrim F σ`.
* `meshOracle_absorb`: for every finite `J` there is an isometry `ℂ^J ⊗ Phys(ι) → Phys(J × ι)`
  intertwining `1_J ⊗ meshOracle F σ ι` with `meshOracle F σ (J × ι)` on every matrix label
  (`Access.exists_absorb` with `Access.card_mul_finrank_meshPhysical_le`).
* `meshOracle_valueConj`: the inverse value call is a conjugated value call
  (`Access.labelValueConj` through the spectator form).
-/

namespace ReleasedODESolverLowerBounds.Access

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.ODE NativeSparseBlockEncoding
open ContinuousLinearMap OracleCircuit TimeDependentExtensions
open DeferredMeasurementLowerBounds.Access (InverseConj)
open ODELowerBoundExtensions.Release (meshOracle stageData SysOp)
open scoped InnerProduct

-- The release's physical workspace is a nested register product (as in `MeshSource`).
set_option synthInstance.maxSize 8192
set_option maxRecDepth 4096

variable {X N Z : Type} [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z]
  {K s : ℕ}

/-- **The one-branch primitive of the general-mesh physical oracle**: the sampled-time access of
the staged data `stageData F.data σ` on the branch `Unit`. -/
abbrev meshPrim (F : Family X N Z K s) {M : ℕ} (σ : Fin M → Fin K) :
    Query → X → Workspace Unit N Z M →L[ℂ] Workspace Unit N Z M :=
  TimeDependentODE.labelOracle (oracles (stageData F.data σ))
    (TimeDependentODE.sample (ι := Unit) (M := M))

/-- The identification `ℂ^Ω ⊗ Workspace κ ≃ ℂ^{Ω × κ} ⊗ Workspace Unit` that splits the branch
register `κ` of the sampled-time workspace off as a spectator register
(`DeferredMeasurementLowerBounds.Access.accessEquiv` in every block, then the flattening). -/
def branchSplit (Ω κ : Type) [Fintype Ω] [Fintype κ] (M : ℕ) :
    Joint Ω (Workspace κ N Z M) ≃ₗᵢ[ℂ] Joint (Ω × κ) (Workspace Unit N Z M) :=
  (LinearIsometryEquiv.piLpCongrRight 2
      (fun _ : Ω => DeferredMeasurementLowerBounds.Access.accessEquiv (N := N) (Z := Z)
        (Kt := M) κ)).trans
    (ODELowerBoundExtensions.Release.jointFlatten Ω κ (Workspace Unit N Z M)).symm

/-- **The sampled-time access is a spectator lift of its one-branch form**: for data `D` with
`M` pieces, `1_Ω ⊗ A_κ = W⁻¹ (1_{Ω × κ} ⊗ A_Unit) W` with the fixed identification
`W = branchSplit Ω κ M`. -/
theorem fiber_labelOracle_eq {Y : Type} {M : ℕ} (D : Data (Y × Fin M) N Z s) (Ω κ : Type)
    [Fintype Ω] [Fintype κ] (q : Query) (y : Y) :
    Joint.fiber (fun _ : Ω => TimeDependentODE.labelOracle (oracles D)
        (TimeDependentODE.sample (ι := κ) (M := M)) q y) =
      (branchSplit (N := N) (Z := Z) Ω κ M).symm.conjStarAlgEquiv
        (Joint.fiber (fun _ : Ω × κ => TimeDependentODE.labelOracle (oracles D)
          (TimeDependentODE.sample (ι := Unit) (M := M)) q y)) := by
  ext Φ ω b
  rfl

/-- **The matrix labels of the general-mesh physical oracle are in spectator form** over the
one-branch primitive `meshPrim F σ`. -/
theorem meshOracle_spectatorForm (F : Family X N Z K s) {M : ℕ} (σ : Fin M → Fin K) (ι : Type)
    [Fintype ι] [DecidableEq ι] (Nsl d : ℕ) (J₀ : X → SysOp N) (Jb : X → Fin M → SysOp N) :
    SpectatorForm (fun q x => meshOracle F σ ι Nsl d J₀ Jb (Sum.inl q) x) (meshPrim F σ) := by
  obtain ⟨Ω, _, U, hU⟩ := ODELowerBoundExtensions.Release.physicalOracle_normal_form
    (stageData F.data σ) ι Nsl d J₀ Jb
  refine ⟨Ω × TimeDependentODE.NativeSource.Label ι M, inferInstance,
    U.trans (branchSplit Ω _ M), fun q x => ?_⟩
  refine (hU q x).trans ?_
  rw [fiber_labelOracle_eq]
  ext Ψ
  rfl

/-- **Spectator absorption for the general-mesh physical oracle**: an isometry
`ℂ^J ⊗ Phys(ι) → Phys(J × ι)` intertwining `1_J ⊗ meshOracle F σ ι` with
`meshOracle F σ (J × ι)` on every matrix label and input. -/
theorem meshOracle_absorb (F : Family X N Z K s) {M : ℕ} (σ : Fin M → Fin K) (ι J : Type)
    [Fintype ι] [DecidableEq ι] [Fintype J] [DecidableEq J] (Nsl d : ℕ) (J₀ : X → SysOp N)
    (Jb : X → Fin M → SysOp N) :
    ∃ Vm : Joint J (MeshSource.PhysicalSpace ι N Z M Nsl d) →L[ℂ]
        MeshSource.PhysicalSpace (J × ι) N Z M Nsl d,
      Vm† ∘L Vm = 1 ∧ ∀ q x, meshOracle F σ (J × ι) Nsl d J₀ Jb (Sum.inl q) x ∘L Vm =
        Vm ∘L Joint.fiber (fun _ : J => meshOracle F σ ι Nsl d J₀ Jb (Sum.inl q) x) :=
  exists_absorb (meshOracle_spectatorForm F σ ι Nsl d J₀ Jb)
    (meshOracle_spectatorForm F σ (J × ι) Nsl d J₀ Jb)
    (card_mul_finrank_meshPhysical_le ι J N Z M Nsl d)

/-- **The inverse value call of the general-mesh physical oracle is a conjugated value call.** -/
theorem meshOracle_valueConj (F : Family X N Z K s) {M : ℕ} (σ : Fin M → Fin K) (ι : Type)
    [Fintype ι] [DecidableEq ι] (Nsl d : ℕ) (J₀ : X → SysOp N) (Jb : X → Fin M → SysOp N) :
    Nonempty (InverseConj (meshOracle F σ ι Nsl d J₀ Jb) (Sum.inl Query.value)) := by
  obtain ⟨C⟩ := (meshOracle_spectatorForm F σ ι Nsl d J₀ Jb).nonempty_inverseConj
    (labelValueConj (stageData F.data σ))
  exact ⟨⟨C.conj, C.unitary, C.star_eq⟩⟩

end

end ReleasedODESolverLowerBounds.Access
