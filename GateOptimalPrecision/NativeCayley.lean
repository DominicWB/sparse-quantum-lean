import GateOptimalPrecision.Main
import GateEfficientNative.Hamiltonian.Theorem

/-!
# Native macros for sector-controlled private calls

The private calls of the bounded-regime circuit and of the clipped-transducer circuit are
sector-controlled (`SparseHamiltonian.GateNative.SecOK`). Each is replaced by the native
compute–rotate–uncompute macro of the baseline gate theorem
(`SparseHamiltonian.GateNative.privMacro`): a public compute circuit `V` of elementary gates and
primitive oracle calls, reversible angle arithmetic, the bit-controlled edge rotation under the
sector wire, the inverse arithmetic and `V†`; each call of `U_J` by its elementary gates `UJg` with
the sector wire as an extra control (`hcirc`). As in the baseline theorem, the hypotheses are the
native identity `V† R_val V = D` on clean scratch (`NativeOK`; the paper builds these identities in
Section `gate:sec:native`, here they enter as hypotheses) and the angle accuracy `ζ` of the
arithmetic (`ArithOK`). The system is `S` qubits with an untouched reference payload `R`; `sysEmb`
keeps every other wire clean.

* `native_transfer`: for every valid released circuit `l` with sector-controlled oracle calls whose
  full output is within `ε₀` of a target `U` (run with `U_J = UJop UJg` and the private operation
  `D`), the native circuit is valid and unitary, makes exactly `2 nPriv l` copies of the primitive
  calls of `V`, has at most `nGates l + 7 C_J nUJ l + G_C nPriv l` elementary gates
  (`C_J = |UJg|`, `G_C = 2|V| + 2|circ| + 2 b_P + b_T + 1` for the arithmetic `circ`) on
  `|wires of l| + |S| + |Z| + b_T + b_P + A + 3` wires, and is within `ε₀ + 4ζ nPriv l` of `U` on
  the system embedding.

It applies to the bounded-regime circuits (`bdSigned`) and to the clipped-transducer circuits
(`clipSigned`), which are released amplified circuits (`secOK_bdSigned`, `secOK_clipSigned`). That
the private operation of each regime has this native form is the hypothesis `NativeOK`, not a
theorem of this library; for binary sparse oracles it is proved in `GateOptimalBinary` (the bounded
regime by this macro, the clipped regime by a factor-conjugated native call,
`GateOptimalBinary.gate_optimal_native_clip`). The paragraph "Sparse preparation and the joint
private operation" of Section `gate:sec:native` supplies the local pieces: the bulk Cayley rotation
`D(y)` is the edge rotation of the baseline (`edgeMat_cayley`), and the correction and failure
phases are edge rotations conjugated by Hadamard gates (`hMat_edgeMat_hMat`, `edgeMat_zero`).
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace GateOptimalPrecision

noncomputable section

open ContinuousLinearMap SparseHamiltonian SparseHamiltonian.OracleCircuit
  SparseHamiltonian.GateCircuit SparseHamiltonian.GateCircuit.Sim SparseHamiltonian.GateNative
open scoped InnerProduct InnerProductSpace BigOperators

variable {S Z Y J : Type*} [Fintype S] [DecidableEq S] [Fintype Z] [DecidableEq Z] [Fintype Y]
  [DecidableEq Y]
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- The native circuit of a released circuit with sector-controlled oracle calls and a constant
private operation. -/
def nativeOf {a m r K : ℕ} (UJg : List (Gate (Fin a ⊕ S)))
    (nd : NativeOp Empty (Fin a ⊕ S) Z Y J) (ar : Arith (NB Empty (Fin a ⊕ S) Z))
    (l : List (Instr (Wire a m r K))) :
    List (NInstr (HW (Wire a m r K) S Empty Z ar.bT ar.bP ar.A) Y J) :=
  hcirc (wireRel a m r K) (noSel _) UJg nd ar l

/-- **Native transfer.** See the module docstring. -/
theorem native_transfer {a m r K : ℕ} (prim : J → Reg Y R →L[ℂ] Reg Y R)
    (hprim : ∀ j, IsUnitary (prim j))
    (UJg : List (Gate (Fin a ⊕ S))) (hUJg : ∀ g ∈ UJg, GateOK 3 g)
    (nd : NativeOp Empty (Fin a ⊕ S) Z Y J) (hnd : nd.Public)
    (ar : Arith (NB Empty (Fin a ⊕ S) Z)) {ζ : ℝ} (hζ : 0 ≤ ζ)
    (har : ArithOK ar (Sum.inl (Sum.inr nd.o)) nd.dec ζ)
    (D : Anc a (Reg S R) →L[ℂ] Anc a (Reg S R)) (hD : IsUnitary D)
    (hN : NativeOK prim nd (selOp (fun _ : Cfg Empty => D)))
    (l : List (Instr (Wire a m r K))) (hv : ∀ i ∈ l, i.Valid Wire.anc)
    (hsec : ∀ i ∈ l, SecOK (wireRel a m r K) i)
    (U : Reg S R →L[ℂ] Reg S R) {ε₀ : ℝ}
    (hrel : ‖run (simSem (P := Reg S R) (UJop (R := R) UJg) D) l ∘L io - io ∘L U‖ ≤ ε₀) :
    (∀ i ∈ nativeOf UJg nd ar l, i.Valid) ∧
    (∀ p : J → Bool, nCallsN p (nativeOf UJg nd ar l) = nPriv l * (2 * nCallsN p nd.V)) ∧
    nGatesN (nativeOf UJg nd ar l) ≤ nGates l + nUJ l * (7 * UJg.length) +
      nPriv l * (2 * nGatesN nd.V + 2 * ar.circ.length + (2 * ar.bP + ar.bT + 1)) ∧
    Fintype.card (HW (Wire a m r K) S Empty Z ar.bT ar.bP ar.A) =
      Fintype.card (Wire a m r K) + Fintype.card S +
        (Fintype.card Z + ar.bT + ar.bP + ar.A + 3) ∧
    IsUnitary (nrun prim (nativeOf UJg nd ar l)) ∧
    ‖nrun prim (nativeOf UJg nd ar l) ∘L sysEmb (io (P := Reg S R)) -
        sysEmb (io (P := Reg S R)) ∘L U‖ ≤ ε₀ + (nPriv l : ℝ) * (4 * ζ) := by
  unfold nativeOf
  have hvN := hcirc_valid (X' := Empty) (wireRel a m r K) (noSel _) UJg hUJg nd hnd ar har.elem
    har.classical l hv
  refine ⟨hvN, fun p => hcirc_nCalls p _ _ UJg nd ar l, ?_, ?_, nrun_isUnitary prim hprim _ hvN,
    ?_⟩
  · have h := hcirc_nGates (X' := Empty) (wireRel a m r K) (noSel _) UJg hUJg nd ar l
    rw [mul_one] at h
    exact h
  · rw [card_HW]
    simp only [Fintype.card_empty, add_zero]
  · have hDu : ∀ w, IsUnitary (constFam D false w) := fun _ => hD
    have hDadj : ∀ w, constFam D true w = (constFam D false w)† := fun _ => rfl
    have hN' : NativeOK prim nd (selOp (constFam D false)) := hN
    have hio : ∀ ψ : Reg S R, ‖(io (P := Reg S R) (a := a) (m := m) (r := r) (K := K)) ψ‖ = ‖ψ‖ :=
      fun ψ => by rw [io_apply, norm_bas]
    exact hcirc_error (X' := Empty) prim hprim (wireRel _ _ _ _) (noSel _) UJg hUJg nd hnd ar hζ
      har (constFam D) hDu hDadj hN' l hv io hio U _ (prodOps_evalSel_const UJg D l hsec) hrel

/-! ### The circuits of the bounded and clipped regimes are sector-controlled -/

theorem secOK_simCircuit (a : ℕ) (τ Q qbar ε : ℝ) :
    ∀ i ∈ simCircuit a τ Q qbar ε, SecOK (wireRel _ _ _ _) i := by
  unfold simCircuit
  exact secOK_ampI _ _ _ _ _ _

theorem secOK_bdSigned (a : ℕ) (σ θ ε t : ℝ) :
    ∀ i ∈ bdSigned a σ θ ε t, SecOK (wireRel _ _ _ _) i := by
  unfold bdSigned bdCircuit
  split_ifs
  · exact secOK_simCircuit a _ _ _ _
  · exact secOK_invList _ _ (secOK_simCircuit a _ _ _ _)

theorem secOK_clipSigned (a : ℕ) (σ θ ε t : ℝ) :
    ∀ i ∈ clipSigned a σ θ ε t, SecOK (wireRel _ _ _ _) i := by
  unfold clipSigned clipCircuit
  split_ifs
  · exact secOK_ampI _ _ _ _ _ _
  · exact secOK_invList _ _ (secOK_ampI _ _ _ _ _ _)

end

end GateOptimalPrecision
