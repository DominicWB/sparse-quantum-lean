import ConstantODELowerBound.Normal
import ConstantODELowerBound.Oracle
import ReleasedODESolverLowerBounds.Access.Absorb
import ReleasedODESolverLowerBounds.Access.Dimension
import ReleasedODESolverLowerBounds.Access.ValueConj

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

/-!
# The constant-coefficient physical oracle in spectator form

Manuscript Section `odel:sec:main` ("the lower bounds apply to the upper bounds of the preceding
section"); Theorem `ode:thm:main`.

The matrix labels of the released constant-coefficient solver's physical oracle
`ConstantODELowerBound.Oracle.constOracle F ι Nm Tsl d J₀ J_b` are, by the released normal form
`ConstantODELowerBound.Normal.physicalOracle_normal_form`, `U⁻¹ (1_Ω ⊗ O_l(x)) U` with the native
primitive `O = oracles (constData F)`, which does not depend on the branch register, the mesh
size, the slot count, the degree or the source interfaces.

* `constOracle_spectatorForm`: the matrix labels are in spectator form over the native primitive.
* `constOracle_absorb`: for every finite `J` there is an isometry `ℂ^J ⊗ Phys(ι) → Phys(J × ι)`
  intertwining `1_J ⊗ constOracle F ι` with `constOracle F (J × ι)` on every matrix label
  (`Access.exists_absorb` with `Access.card_mul_finrank_constPhysical_le`).
* `constOracle_valueConj`: the inverse value call is a conjugated value call
  (`Access.primValueConj` through the spectator form).
-/

namespace ReleasedODESolverLowerBounds.Access

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.ODE NativeSparseBlockEncoding
open ContinuousLinearMap OracleCircuit
open DeferredMeasurementLowerBounds.Access (InverseConj)
open ODELowerBoundExtensions.Release (SysOp)
open ConstantODELowerBound.Oracle (constOracle constData)
open scoped InnerProduct

-- The released solver's physical workspace is a nested register product.
set_option synthInstance.maxSize 8192
set_option maxRecDepth 4096

variable {X N Z : Type} [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z] [DecidableEq Z]
  {s : ℕ}

/-- **The matrix labels of the constant-coefficient physical oracle are in spectator form** over
the native primitive `oracles (constData F)`. -/
theorem constOracle_spectatorForm (F : Family X N Z 1 s) (ι : Type) [Fintype ι] [DecidableEq ι]
    (Nm Tsl d : ℕ) (J₀ Jb : X → SysOp N) :
    SpectatorForm (fun q x => constOracle F ι Nm Tsl d J₀ Jb (Sum.inl q) x)
      (oracles (constData F)) := by
  obtain ⟨Ω, _, U, hU⟩ :=
    ConstantODELowerBound.Normal.physicalOracle_normal_form (constData F) ι Nm Tsl d J₀ Jb
  exact ⟨Ω, inferInstance, U, fun q x => hU q x⟩

/-- **Spectator absorption for the constant-coefficient physical oracle**: an isometry
`ℂ^J ⊗ Phys(ι) → Phys(J × ι)` intertwining `1_J ⊗ constOracle F ι` with `constOracle F (J × ι)`
on every matrix label and input. -/
theorem constOracle_absorb (F : Family X N Z 1 s) (ι J : Type) [Fintype ι] [DecidableEq ι]
    [Fintype J] [DecidableEq J] (Nm Tsl d : ℕ) (J₀ Jb : X → SysOp N) :
    ∃ Vm : Joint J (ODEFinalNativeSource.Physical ι N Z Nm Tsl d) →L[ℂ]
        ODEFinalNativeSource.Physical (J × ι) N Z Nm Tsl d,
      Vm† ∘L Vm = 1 ∧ ∀ q x, constOracle F (J × ι) Nm Tsl d J₀ Jb (Sum.inl q) x ∘L Vm =
        Vm ∘L Joint.fiber (fun _ : J => constOracle F ι Nm Tsl d J₀ Jb (Sum.inl q) x) :=
  exists_absorb (constOracle_spectatorForm F ι Nm Tsl d J₀ Jb)
    (constOracle_spectatorForm F (J × ι) Nm Tsl d J₀ Jb)
    (card_mul_finrank_constPhysical_le ι J N Z Nm Tsl d)

/-- **The inverse value call of the constant-coefficient physical oracle is a conjugated value
call.** -/
theorem constOracle_valueConj (F : Family X N Z 1 s) (ι : Type) [Fintype ι] [DecidableEq ι]
    (Nm Tsl d : ℕ) (J₀ Jb : X → SysOp N) :
    Nonempty (InverseConj (constOracle F ι Nm Tsl d J₀ Jb) (Sum.inl Query.value)) := by
  obtain ⟨C⟩ := (constOracle_spectatorForm F ι Nm Tsl d J₀ Jb).nonempty_inverseConj
    (primValueConj (constData F))
  exact ⟨⟨C.conj, C.unitary, C.star_eq⟩⟩

end

end ReleasedODESolverLowerBounds.Access
