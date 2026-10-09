import GateEfficientBinaryTime.Slot
import GateEfficientBinary.Sparse.Native

/-!
# Time-indexed binary sparse oracles and the slot-selected private operation

Time-indexed binary sparse data are released native sparse data
`D : NativeSparseBlockEncoding.Data (X × Fin (2^m)) n (Cfg (VW b)) s` whose input carries the
time slot: the sample of slot `r` on input `x` is `D.matrix (x, r)`. The slot word
`w : Cfg (Fin m)` names the slot `wordEquivFin m w`.

* `primsT D en x`: the coherent sampled-time primitive oracles `Σ_w |w⟩⟨w| ⊗ O_j(x, w)` on `m`
  slot qubits, the edge register and the value qubits, where `O_j(x, w)` are the binary primitive
  oracles `prims D en (x, wordEquivFin m w)` of the sample (`primsT_isUnitary`).
* `computeVT`: the compute circuit `computeV` with every call also reading the slot qubits; it
  has the same counts (`computeVT_nGates`, `computeVT_nCalls`).
* `sparseOpT`: the native private operation with `m` selection wires and the decoder of the value
  wires (`sparseOpT_public`).
* `sparse_nativeOK_time`: `V† R_val V` acts on clean scratch as the slot-selected lifted private
  Cayley operation, the operation of the sample `wordEquivFin m w` at slot word `w`.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateBinary

noncomputable section
open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
open SparseHamiltonian.OracleCircuit
open SparseHamiltonian.GatePointerEncoding (wordEquivFin)
open NativeSparseBlockEncoding (Data Query)
open scoped InnerProduct

variable {X n : Type*} [Fintype n] [DecidableEq n] {s k b m : ℕ}
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- **The time-indexed binary primitive oracles** `Σ_w |w⟩⟨w| ⊗ O_j(x, w)`: on slot word `w`
they are the binary primitive oracles of the sample `wordEquivFin m w`. -/
def primsT (D : Data (X × Fin (2 ^ m)) n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (x : X) :
    Query → Reg (Fin m ⊕ PY k b) R →L[ℂ] Reg (Fin m ⊕ PY k b) R :=
  slotPrim (fun w => prims (R := R) D en (x, wordEquivFin m w))

theorem primsT_isUnitary (D : Data (X × Fin (2 ^ m)) n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n)
    (x : X) (j : Query) : IsUnitary (primsT (R := R) D en x j) :=
  slotPrim_isUnitary _ (fun w j => prims_isUnitary D en (x, wordEquivFin m w) j) j

/-- **The time-indexed compute circuit**: the compute circuit of `computeV`, every call also
reading the slot wires. -/
def computeVT (k b m : ℕ) :
    List (NInstr (NB (Fin m) (PR k) (SZ k b)) (Fin m ⊕ PY k b) Query) :=
  (computeV k b).map slotInstr

/-- The real components of the stored entry, as wires of the slot-selected operation. -/
def valXT (k b m : ℕ) : Fin b → NB (Fin m) (PR k) (SZ k b) :=
  fun i => Sum.inr (Sum.inr (Sum.inl i))

/-- The imaginary components of the stored entry, as wires of the slot-selected operation. -/
def valYT (k b m : ℕ) : Fin b → NB (Fin m) (PR k) (SZ k b) :=
  fun i => Sum.inr (Sum.inr (Sum.inr i))

/-- **The slot-selected native private operation**: the time-indexed compute circuit, the
orientation wire and the decoder `κ (X + i Y)` of the value wires. -/
def sparseOpT (k b m : ℕ) (κ : ℝ) :
    NativeOp (Fin m) (PR k) (SZ k b) (Fin m ⊕ PY k b) Query where
  V := computeVT k b m
  o := oPR k
  dec := binDec (valXT k b m) (valYT k b m) κ

theorem sparseOpT_dec (k b m : ℕ) (κ : ℝ) (x : Cfg (NB (Fin m) (PR k) (SZ k b))) :
    (sparseOpT k b m κ).dec x = (sparseOp k b κ).dec (baseOf x) := rfl

/-- The time-indexed compute circuit is valid and the decoder does not read the orientation
wire. -/
theorem sparseOpT_public (k b m : ℕ) (κ : ℝ) : (sparseOpT k b m κ).Public :=
  slot_public (sparseOp k b κ) (sparseOp_public k b κ) _ rfl rfl (sparseOpT_dec k b m κ)

theorem computeVT_nGates (k b m : ℕ) : nGatesN (computeVT k b m) = 28 * k := by
  rw [computeVT, nGatesN_slot, computeV_nGates]

theorem computeVT_nCalls (k b m : ℕ) (p : Query → Bool) :
    nCallsN p (computeVT k b m) = 2 * (if p Query.rowLocation then 1 else 0) +
      2 * (if p Query.columnLocation then 1 else 0) + (if p Query.value then 1 else 0) := by
  rw [computeVT, nCallsN_slot, computeV_nCalls]

/-- **The native identity of the slot-selected private operation**: on clean scratch,
`V† R_val V` acts at slot word `w` as the qubit lift of the private Cayley operation of the
sample `wordEquivFin m w` (the locator conjugation of the exact edge action at rescaling `γ`). -/
theorem sparse_nativeOK_time (D : Data (X × Fin (2 ^ m)) n (Cfg (VW b)) s)
    (en : Cfg (Fin k) ≃ n) (k0 : Fin s) (hk0 : D.slot k0 = zIdx en) (c0 : ℝ)
    (hdec : ∀ e z, D.decode e z = (c0 : ℂ) * gauss z) (x : X) (γ : ℝ) :
    NativeOK (primsT (R := R) D en x) (sparseOpT k b m (γ * Real.sqrt s * c0))
      (selOp (fun w : Cfg (Fin m) => unconj (qlift (R := R) (phiPR en)
        (FixedNativeCayleySimulation.action D (x, wordEquivFin m w) γ)))) :=
  nativeOK_slot _ (sparseOp k b (γ * Real.sqrt s * c0)) _ rfl rfl
    (sparseOpT_dec k b m _) _
    (fun w => sparse_nativeOK D en k0 hk0 c0 hdec (x, wordEquivFin m w) γ)

end

end SparseHamiltonian.GateBinary
