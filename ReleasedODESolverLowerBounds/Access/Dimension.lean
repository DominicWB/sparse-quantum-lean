import TimeDependentExtensions.ODE.Source
import SparseODE.ODEFinalNativeSource

set_option autoImplicit false

/-!
# Dimensions of the released solvers' physical workspaces

The physical workspaces of the released ODE solvers grow at least linearly in the branch
register: `|J| · dim Phys(ι) ≤ dim Phys(J × ι)`. This is the counting fact behind the
spectator absorption of `Access/Absorb`.

Manuscript: the end of the proof of Lemma `hsl:lem:precision` (purification and deferred
measurement). Enlarging the branch register of
the same released oracle by the absorbed record register is a formalisation device:
`PhysicalODELowerBound.Mesh.MeshForces` and `PhysicalODELowerBound.Const.ConstForces` quantify
over every spectator index, so they cover the enlarged oracle.
-/

namespace ReleasedODESolverLowerBounds.Access

noncomputable section
open SparseHamiltonian TimeDependentExtensions

set_option synthInstance.maxSize 8192
set_option maxRecDepth 4096

/-- The matrix basis of the general-mesh workspace grows with the branch register. -/
theorem card_meshMatrixBasis_le (ι J n Z : Type) [Fintype ι] [Fintype J] [Nonempty J]
    [Fintype n] [Fintype Z] (M N d : ℕ) :
    Fintype.card (MeshSource.MatrixBasis ι n Z M N d) ≤
      Fintype.card (MeshSource.MatrixBasis (J × ι) n Z M N d) := by
  simp only [MeshSource.MatrixBasis, ODEFinalNativeBasis.AlignedBasis,
    FlatBranchNativeAccess.Basis, NativeControlledOracle.Workspace, TimeDependentODE.Basis,
    ODEJointNative.Basis, TimeDependentODE.NativeSource.Label, Fintype.card_prod]
  have h : Fintype.card ι ≤ Fintype.card J * Fintype.card ι :=
    Nat.le_mul_of_pos_left _ Fintype.card_pos
  gcongr

/-- The matrix basis of the constant-coefficient workspace grows with the branch register. -/
theorem card_constMatrixBasis_le (ι J n Z : Type) [Fintype ι] [Fintype J] [Nonempty J]
    [Fintype n] [Fintype Z] (N T d : ℕ) :
    Fintype.card (ODEFinalNativeSource.MatrixBasis ι n Z N T d) ≤
      Fintype.card (ODEFinalNativeSource.MatrixBasis (J × ι) n Z N T d) := by
  simp only [ODEFinalNativeSource.MatrixBasis, ODEFinalNativeBasis.Basis,
    ODEFinalNativeBasis.AlignedBasis, FlatBranchNativeAccess.Basis,
    NativeControlledOracle.Workspace, ODEJointNative.Basis, Fintype.card_prod]
  have h : Fintype.card ι ≤ Fintype.card J * Fintype.card ι :=
    Nat.le_mul_of_pos_left _ Fintype.card_pos
  gcongr

/-- The dimension of a sector-tensor physical space. -/
theorem finrank_sectorPhysical (A B : Type) [Fintype A] [Fintype B] :
    Module.finrank ℂ (ODESectorTensor.Physical A B) =
      Fintype.card A * Fintype.card (NativeControlledOracle.Workspace B) := by
  show Module.finrank ℂ (PiLp 2 fun _ : A =>
    EuclideanSpace ℂ (NativeControlledOracle.Workspace B)) = _
  rw [(WithLp.linearEquiv 2 ℂ _).finrank_eq, Module.finrank_pi_fintype]
  simp [finrank_euclideanSpace]

/-- The sector-tensor dimension grows at least linearly when the source basis is multiplied by
`J` and the matrix basis does not shrink. -/
theorem card_mul_finrank_sectorPhysical_le (J A A' B B' : Type) [Fintype J] [Fintype A]
    [Fintype A'] [Fintype B] [Fintype B'] (hA : Fintype.card A' = Fintype.card J * Fintype.card A)
    (hB : Fintype.card B ≤ Fintype.card B') :
    Fintype.card J * Module.finrank ℂ (ODESectorTensor.Physical A B) ≤
      Module.finrank ℂ (ODESectorTensor.Physical A' B') := by
  rw [finrank_sectorPhysical, finrank_sectorPhysical, hA, ← mul_assoc]
  refine Nat.mul_le_mul_left _ ?_
  simp only [NativeControlledOracle.Workspace, Fintype.card_prod, Fintype.card_bool]
  gcongr

/-- **The general-mesh physical workspace grows at least linearly in the branch register**:
`|J| · dim Phys(ι) ≤ dim Phys(J × ι)`. -/
theorem card_mul_finrank_meshPhysical_le (ι J n Z : Type) [Fintype ι] [Fintype J] [Fintype n]
    [Fintype Z] (M N d : ℕ) :
    Fintype.card J * Module.finrank ℂ (MeshSource.PhysicalSpace ι n Z M N d) ≤
      Module.finrank ℂ (MeshSource.PhysicalSpace (J × ι) n Z M N d) := by
  rcases isEmpty_or_nonempty J with hJ | hJ
  · simp [Fintype.card_eq_zero]
  · refine card_mul_finrank_sectorPhysical_le J _ _ _ _ ?_ (card_meshMatrixBasis_le ι J n Z M N d)
    simp only [TimeDependentODE.NativeSource.SourceBasis, ODEFinalNativeSource.SourceBasis,
      Fintype.card_prod]
    ring

/-- **The constant-coefficient physical workspace grows at least linearly in the branch
register**: `|J| · dim Phys(ι) ≤ dim Phys(J × ι)`. -/
theorem card_mul_finrank_constPhysical_le (ι J n Z : Type) [Fintype ι] [Fintype J] [Fintype n]
    [Fintype Z] (N T d : ℕ) :
    Fintype.card J * Module.finrank ℂ (ODEFinalNativeSource.Physical ι n Z N T d) ≤
      Module.finrank ℂ (ODEFinalNativeSource.Physical (J × ι) n Z N T d) := by
  rcases isEmpty_or_nonempty J with hJ | hJ
  · simp [Fintype.card_eq_zero]
  · refine card_mul_finrank_sectorPhysical_le J _ _ _ _ ?_
      (card_constMatrixBasis_le ι J n Z N T d)
    simp only [ODEFinalNativeSource.SourceBasis, Fintype.card_prod]
    ring

end

end ReleasedODESolverLowerBounds.Access
