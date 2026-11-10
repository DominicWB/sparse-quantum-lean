import OptimalSparseSimulation.Spectator
import SparseHamiltonian.ImprovedSparseHamiltonian

set_option autoImplicit false

/-!
# The released physical oracles in the common form

The large-sparsity core (`LargeSparsityCore.Native.core_simulation`) and the baseline simulation
(`SparseHamiltonian.ImprovedSparseHamiltonian.simulation_log_one`) call the oracle family
`NativeCayleyActive.oracle D T d` of the active Cayley layers, the latter with one more Boolean
alignment spectator. Unfolded, a call is the physical native call
`NativeSignedFactor.physOracle D l x` of the native signed factor, flattened by the fixed
`NativeDilationLayout.layout` and extended by the spectator registers of the native-control
construction and of the active chronological labels. No step depends on `l` or `x`.

* `cayleyActive_form`: `SpectatorForm (physOracle D) (NativeCayleyActive.oracle D T d)`.
* `improved_form`: `SpectatorForm (physOracle D) (ImprovedSparseHamiltonian.oracle D γ η t ε)`.

The spectator types are finite types of the first universe; the row and value index types `n`
and `Z` are therefore taken in `Type`.
-/

namespace OptimalSparseSimulation

noncomputable section

open ContinuousLinearMap SparseHamiltonian NativeSparseBlockEncoding
set_option maxRecDepth 4096
set_option synthInstance.maxSize 4096

variable {X : Type*} {n Z : Type} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s : ℕ}

omit [DecidableEq Z] in
/-- The oracle of the active Cayley layers, unfolded: the physical native call, flattened and
extended by the native-control spectators, on every active chronological label. -/
theorem cayleyActive_eq (D : Data X n Z s) (T d : ℕ) :
    NativeCayleyActive.oracle D T d = CoherentQuerySchedule.oracle
      (ι := ActiveRegisterLayout.Label PUnit.{1} T d)
      (fun l x => LookupFromBasisOracle.spectator
        (S := (Bool × NativeCayleyProgram.Basis n Z) × NativeCayleyProgram.Basis n Z)
        ((NativeDilationLayout.layout (B := NativeSparseMaskedAccess.Basis n Z)).conjStarAlgEquiv
          (NativeSignedFactor.physOracle D l x))) := rfl

omit [DecidableEq Z] in
/-- **The oracle of the large-sparsity core is a native call with spectators.** -/
theorem cayleyActive_form (D : Data X n Z s) (T d : ℕ) :
    SpectatorForm (K := NativeCayleyActive.Physical n Z T d) (NativeSignedFactor.physOracle D)
      (NativeCayleyActive.oracle D T d) := by
  rw [cayleyActive_eq]
  exact (SpectatorForm.spectator_conj
    (S := (Bool × NativeCayleyProgram.Basis n Z) × NativeCayleyProgram.Basis n Z)
    (NativeSignedFactor.physOracle D)
    (NativeDilationLayout.layout (B := NativeSparseMaskedAccess.Basis n Z))).diagonal
      (ActiveRegisterLayout.Label PUnit.{1} T d)

omit [DecidableEq Z] in
/-- **The oracle of the baseline simulation is a native call with spectators.** -/
theorem improved_form (D : Data X n Z s) (γ η t ε : ℝ) :
    SpectatorForm (K := ImprovedSparseHamiltonian.Physical n Z s γ η t ε)
      (NativeSignedFactor.physOracle D) (ImprovedSparseHamiltonian.oracle D γ η t ε) :=
  (cayleyActive_form D _ _).diagonal Bool

end

end OptimalSparseSimulation
