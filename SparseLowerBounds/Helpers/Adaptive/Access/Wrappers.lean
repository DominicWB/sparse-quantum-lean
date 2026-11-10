import SparseLowerBounds.Adaptive.Access

set_option synthInstance.maxHeartbeats 400000

section
/-!
# Helper: the release's spectator wrappers are `1_Ω ⊗ ·`

The release wraps the native sparse primitives in three kinds of untouched
registers before the linear-system algorithm queries them
(`SparseLinearSystems.Step.physOracle`); the Hamiltonian simulator uses the
same wrappers (`Helpers/HsRelease/Layers`):

* `WeightedClock.diagonal (fun _ => U)`, the constant block diagonal;
* `MaskedProgram.masked (fun _ => true) U`, the all-active branch mask
  (`NativeMaskedOracle.oracle`, `Source.sourceOracle`);
* `LookupFromBasisOracle.spectator U`, a flattened spectator register
  (`NativeControlledOracle.oracle`).

Each is the homogeneous spectator `Joint.fiber (fun _ => U)`, the last one up
to the fixed relabelling `RegisterEquivalences.productFlatten`. So the
Boolean-access transports of `Adaptive/Access` (`BooleanAccess.spectate`,
`BooleanAccess.conj`) apply to them at no query cost (proof of Lemma
`qlsl:lem:xor`: spectator and controlled registers are covered by purification).
-/

namespace SparseLowerBounds.Helpers.Adaptive.Access

noncomputable section
set_option autoImplicit false
open SparseHamiltonian

section General

variable {ι K : Type*} [Fintype ι] [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [CompleteSpace K]

omit [Fintype ι] [CompleteSpace K] in
/-- The constant block diagonal is the homogeneous spectator. -/
theorem diagonal_const_eq_fiber (U : K →L[ℂ] K) :
    WeightedClock.diagonal (fun _ : ι => U) = Joint.fiber (fun _ : ι => U) := by
  ext Ψ i
  rfl

omit [Fintype ι] [CompleteSpace K] in
/-- The all-active branch mask is the homogeneous spectator. -/
theorem masked_true_eq_fiber (U : K →L[ℂ] K) :
    MaskedProgram.masked (fun _ : ι => true) U = Joint.fiber (fun _ : ι => U) := by
  ext Ψ i
  simp [MaskedProgram.masked_apply]

end General

section Spectator

variable {S B : Type*} [Fintype S] [Fintype B]

/-- A flattened spectator register is the homogeneous spectator, relabelled by
the fixed flattening `ℂ^S ⊗ ℂ^B ≃ ℂ^{S × B}`. -/
theorem spectator_eq_conj_fiber (F : EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B) :
    LookupFromBasisOracle.spectator (S := S) F =
      (RegisterEquivalences.productFlatten S B).conjStarAlgEquiv
        (Joint.fiber (fun _ : S => F)) := by
  unfold LookupFromBasisOracle.spectator
  rw [diagonal_const_eq_fiber]

end Spectator

end

end SparseLowerBounds.Helpers.Adaptive.Access
end
