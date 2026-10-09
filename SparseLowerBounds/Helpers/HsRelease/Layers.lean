import SparseLowerBounds.Helpers.Adaptive.Access.Wrappers
import SparseLowerBounds.Helpers.HsRelease.PhaseAccess

set_option synthInstance.maxHeartbeats 400000

section
/-!
# Helper: phase-oracle access through the release simulator's oracle layers

For `Hamiltonian/ReleaseAccess`. The release's
Hamiltonian-simulation algorithm (`ImprovedSparseHamiltonian.simulation`,
`simulation_log_one`) is a `MultiOracleCircuit.Program` over
`ImprovedSparseHamiltonian.oracle D γ η t δ`, labelled by
`NativeSparseBlockEncoding.Query`. Unfolded, for every label `l` and input `x`:

* `ImprovedSparseHamiltonian.oracle D γ η t δ l x`
  `= AlignedMultiOracleProgram.oracle (ScaledNativeSimulation.oracle D γ η t δ) l x`
  `= CoherentQuerySchedule.oracle (ι := Bool) … l x`
  `= WeightedClock.diagonal (fun _ : Bool => ScaledNativeSimulation.oracle D γ η t δ l x)`
  (the clean-output alignment spectator `Bool`);
* `ScaledNativeSimulation.oracle D γ η t δ = ImprovedNativeSimulation.oracle D γ (η * |t|) δ`
  `= NativeCayleyActive.oracle D T d` with `T = ImprovedNativeSimulation.slots s γ (η * |t|) δ`,
  `d = ImprovedNativeSimulation.degree s γ (η * |t|) δ`;
* `NativeCayleyActive.oracle D T d = NativeWholeProgramActive.oracle (C := PUnit) (NativeCayleyProgram.oracle D) T d`
  `= NativeMaskedProgram.oracle (ι := ActiveRegisterLayout.Label PUnit T d) (NativeCayleyProgram.oracle D)`,
  i.e. `MaskedProgram.masked (fun _ => true) (NativeControlledOracle.oracle (NativeCayleyProgram.oracle D l) x)`
  (all chronological cells; control, dummy and reference registers via
  `LookupFromBasisOracle.spectator`);
* `NativeCayleyProgram.oracle D = FlatMaskedAccess.flatOracle (NativeSparseMaskedAccess.flatOracle D)`
  `= NativeDilationLayout.oracle (NativeSparseMaskedAccess.flatOracle D)`: the fixed
  `NativeDilationLayout.layout` of `NativeMaskedProgram.oracle (ι := Bool)` (the
  Hermitian-dilation branch);
* `NativeSparseMaskedAccess.flatOracle D l x = layout.conjStarAlgEquiv (oracles D l x)`.

So every label of the release oracle is **exactly one call** of the native
primitive `NativeSparseBlockEncoding.oracles D l` of the same label, with
untouched spectator registers and fixed register relabellings; no label wraps
several native calls, a controlled call, or a selection among labels. A
`PhaseAccess` certificate for `oracles D` therefore passes to every layer with
the **same per-label costs** (`PhaseAccess.spectate`, `PhaseAccess.conj`):

* `maskedAllAccess`, `spectatorAccess`, `controlledAccess`, `nativeMaskedAccess`,
  `dilationAccess`, `flatSparseAccess`, `cayleyAccess`: the layer-by-layer
  transport, for an arbitrary hidden-input type and Boolean pattern;
* `cayleyActiveAccess`: `NativeCayleyActive.oracle D T d` (also
  `ImprovedNativeSimulation.oracle` and `ScaledNativeSimulation.oracle`, which
  are abbreviations of it);
* `releaseAccess`: `ImprovedSparseHamiltonian.oracle D γ η t δ`, for every
  `γ η t δ`.

The equalities between layers are those of `Helpers/Adaptive/Access/Wrappers`
(`masked_true_eq_fiber`,
`spectator_eq_conj_fiber`, `diagonal_const_eq_fiber`).
-/

namespace SparseLowerBounds.Hamiltonian.HsRelease

noncomputable section
set_option autoImplicit false
open SparseHamiltonian Helpers.Adaptive.Access
set_option maxRecDepth 4096
set_option synthInstance.maxSize 4096

variable {I : Type*} [Fintype I] {X : Type*} {y : X → I → Bool} {L : Type*}

section Masked

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The all-active branch mask `MaskedProgram.masked (fun _ => true)` over a
branch register `ι` is a spectator: same Boolean costs. -/
def maskedAllAccess {O : L → X → K →L[ℂ] K} {w : L → ℕ} (A : PhaseAccess I y O w)
    (ι : Type) [Fintype ι] :
    PhaseAccess I y (fun l x => MaskedProgram.masked (fun _ : ι => true) (O l x)) w :=
  (A.spectate ι).congr fun l x => (masked_true_eq_fiber (O l x)).symm

end Masked

section Native

variable {B : Type} [Fintype B]

/-- A flattened spectator register `S` (`LookupFromBasisOracle.spectator`):
same Boolean costs. -/
def spectatorAccess {F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B} {w : L → ℕ}
    (A : PhaseAccess I y F w) (S : Type) [Fintype S] :
    PhaseAccess I y (fun l x => LookupFromBasisOracle.spectator (S := S) (F l x)) w :=
  ((A.spectate S).conj (RegisterEquivalences.productFlatten S B)).congr fun l x =>
    (spectator_eq_conj_fiber (F l x)).symm

/-- `NativeControlledOracle.oracle`: the native call with the control, dummy
and reference registers as spectators. Same Boolean costs. -/
def controlledAccess {F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B} {w : L → ℕ}
    (A : PhaseAccess I y F w) :
    PhaseAccess I y (fun l x => NativeControlledOracle.oracle (F l) x) w :=
  spectatorAccess A ((Bool × B) × B)

/-- `NativeMaskedProgram.oracle (ι := ι) F`: every label is the controlled
native call in every branch of `ι`. Same Boolean costs. -/
def nativeMaskedAccess (ι : Type) [Fintype ι]
    {F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B} {w : L → ℕ}
    (A : PhaseAccess I y F w) : PhaseAccess I y (NativeMaskedProgram.oracle (ι := ι) F) w :=
  maskedAllAccess (controlledAccess A) ι

/-- `NativeDilationLayout.oracle F`: the native-masked family on the dilation
branch `Bool`, flattened by the fixed `NativeDilationLayout.layout`. Same
Boolean costs. -/
def dilationAccess {F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B} {w : L → ℕ}
    (A : PhaseAccess I y F w) : PhaseAccess I y (NativeDilationLayout.oracle F) w :=
  (nativeMaskedAccess Bool A).conj NativeDilationLayout.layout

end Native

section Sparse

variable {N Z : Type} [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z] {s : ℕ}

/-- `NativeSparseMaskedAccess.flatOracle D`: the native primitives in the fixed
computational-basis layout. Same Boolean costs. -/
def flatSparseAccess (D : NativeSparseBlockEncoding.Data X N Z s)
    {w : NativeSparseBlockEncoding.Query → ℕ}
    (A : PhaseAccess I y (NativeSparseBlockEncoding.oracles D) w) :
    PhaseAccess I y (NativeSparseMaskedAccess.flatOracle D) w :=
  A.conj NativeSparseMaskedAccess.layout

/-- `NativeCayleyProgram.oracle D`, the oracle family of the release's native
Cayley circuit. Same Boolean costs as `oracles D`. -/
def cayleyAccess (D : NativeSparseBlockEncoding.Data X N Z s)
    {w : NativeSparseBlockEncoding.Query → ℕ}
    (A : PhaseAccess I y (NativeSparseBlockEncoding.oracles D) w) :
    PhaseAccess I y (NativeCayleyProgram.oracle D) w :=
  dilationAccess (flatSparseAccess D A)

/-- `NativeCayleyActive.oracle D T d` (the oracle family of every active
chronological layer, `ImprovedNativeSimulation.oracle` and
`ScaledNativeSimulation.oracle`): the Cayley family in every cell of
`ActiveRegisterLayout.Label PUnit T d`. Same Boolean costs as `oracles D`. -/
def cayleyActiveAccess (D : NativeSparseBlockEncoding.Data X N Z s)
    {w : NativeSparseBlockEncoding.Query → ℕ}
    (A : PhaseAccess I y (NativeSparseBlockEncoding.oracles D) w) (T d : ℕ) :
    PhaseAccess I y (NativeCayleyActive.oracle D T d) w :=
  nativeMaskedAccess (ActiveRegisterLayout.Label PUnit.{1} T d) (cayleyAccess D A)

/-- **The release simulator's oracle family**
`ImprovedSparseHamiltonian.oracle D γ η t δ` (any `γ η t δ`): the active-layer
family on both sectors of the clean-output alignment spectator `Bool`
(`CoherentQuerySchedule.oracle`). Same Boolean costs as `oracles D`. -/
def releaseAccess (D : NativeSparseBlockEncoding.Data X N Z s)
    {w : NativeSparseBlockEncoding.Query → ℕ}
    (A : PhaseAccess I y (NativeSparseBlockEncoding.oracles D) w) (γ η t δ : ℝ) :
    PhaseAccess I y (ImprovedSparseHamiltonian.oracle D γ η t δ) w :=
  ((cayleyActiveAccess D A (ImprovedNativeSimulation.slots (s : ℝ) γ (η * |t|) δ)
      (ImprovedNativeSimulation.degree (s : ℝ) γ (η * |t|) δ)).spectate Bool).congr
    fun _ _ => (diagonal_const_eq_fiber _).symm

end Sparse

end

end SparseLowerBounds.Hamiltonian.HsRelease
end
