import GateEfficientSelective.Prep
import GateEfficientNative.ODE.Time

/-!
# Synthesised gates of the native ODE preparations with supplied source circuits

The native preparations of the dissipative solvers (`GateNative.nprepC` for constant
coefficients, `GateNative.tnprepC` for time-dependent coefficients, also used by the binary-data
solvers on branch-dependent meshes and with computed nodes) are the released preparation with
every instruction replaced by its native macro (`GateNative.omacro`); a source interface is
replaced by a supplied source circuit (or its literal inverse), placed on the native register.

If the supplied source circuits are circuits over the gate set `𝒢` and `𝒢` is adjoint-closed,
none of their gates (nor of their literal inverses) is synthesised by the selective compiler:
the synthesised gate occurrences of the preparation are at most the gates of the same
preparation with empty source circuits (`nSynN_omacro_le`, `nSynN_nprepC_le`,
`nSynN_tnprepC_le`). So the number `K` of synthesised gates, and hence the synthesis logarithm,
does not depend on the length of the source circuits.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateSelective

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit GateNative GateSynth GateSynthTrials
open GateCircuit.Sim (Wire)
open GateODE (OInstr OWire Params)
open GateODE.Time (TParams)

section Omacro

variable {a m r K k l f : ℕ} {S Zs Z Sel Y J : Type*} {nP : ℕ}
variable (𝒢 : Set Kind)

/-- **Source circuits over `𝒢` add no synthesised gate**: the synthesised gate occurrences of a
macro-expanded released list with source macros `srcN` without synthesised gates are at most the
gates of the same list with any other source macros `srcN₀`, for example empty ones. -/
theorem nSynN_omacro_le (sw : SelWires (odeRel a m r K k l f) Sel)
    (UJg : List (Gate (Fin a ⊕ S))) (nd : NativeOp Sel (Fin a ⊕ S) Z Y J)
    (ar : Arith (NB Sel (Fin a ⊕ S) Z))
    (srcN srcN₀ : Bool → Bool → List (NInstr (HWO a m r K k l f S Zs nP Z ar.bT ar.bP ar.A) Y J))
    (hsrc : ∀ b adj, nSynN 𝒢 (srcN b adj) = 0)
    (gs : List (OInstr (Wire a m r K) (OWire k l f))) :
    nSynN 𝒢 (gs.flatMap (omacro sw UJg nd ar srcN)) ≤
      nGatesN (gs.flatMap (omacro sw UJg nd ar srcN₀)) := by
  rw [nSynN_flatMap, nGatesN_flatMap]
  apply List.sum_le_sum
  intro i _
  cases i with
  | gate g => exact nSynN_le 𝒢 _
  | uj cs adj => exact nSynN_le 𝒢 _
  | priv cs adj => exact nSynN_le 𝒢 _
  | src b adj =>
      show nSynN 𝒢 (srcN b adj) ≤ nGatesN (srcN₀ b adj)
      rw [hsrc]
      exact Nat.zero_le _
  | seed c => exact nSynN_le 𝒢 _

end Omacro

section Prep

variable {S Zs Z Y J : Type*} [Fintype S] [DecidableEq S] [Fintype Zs] [DecidableEq Zs]
  [Fintype Z] [DecidableEq Z] [Fintype Y] [DecidableEq Y]
variable (𝒢 : Set Kind)

omit [Fintype S] [DecidableEq S] [Fintype Zs] [DecidableEq Zs] [Fintype Z] [DecidableEq Z]
  [Fintype Y] [DecidableEq Y] in
/-- A circuit over an adjoint-closed `𝒢`, or its literal inverse, placed anywhere, has no
synthesised gate. -/
theorem nSynN_placed {W W' : Type*} (hadj : AdjClosed 𝒢) (e : W ↪ W')
    (C : List (NInstr W Y J)) (hC : ∀ g, NInstr.gate g ∈ C → GateOf 𝒢 g) (adj : Bool) :
    nSynN 𝒢 ((if adj then ninv C else C).map (NInstr.map e)) = 0 := by
  rw [nSynN_map]
  split_ifs
  · rw [nSynN_ninv 𝒢 hadj]
    exact nSynN_eq_zero 𝒢 C hC
  · exact nSynN_eq_zero 𝒢 C hC

omit [DecidableEq S] [DecidableEq Zs] [DecidableEq Z] [Fintype Y] [DecidableEq Y] in
/-- **Constant coefficients: the synthesised gates do not depend on the source circuits.** If
the supplied source circuits are circuits over the adjoint-closed gate set `𝒢`, the synthesised
gate occurrences of the native preparation are at most the gates of the native preparation with
empty source circuits. -/
theorem nSynN_nprepC_le (hadj : AdjClosed 𝒢) (p : Params) (UJg : List (Gate (Fin p.a ⊕ S)))
    (nd : NativeOp (LabW p.k p.l) (Fin p.a ⊕ S) Z Y J)
    (ar : Arith (NB (LabW p.k p.l) (Fin p.a ⊕ S) Z))
    (srcC : Bool → List (NInstr ((Unit ⊕ S) ⊕ Zs) Y J))
    (hsrcG : ∀ c, ∀ g, NInstr.gate g ∈ srcC c → GateOf 𝒢 g) :
    nSynN 𝒢 (nprepC p UJg nd ar srcC) ≤ nGatesN (nprepC (Zs := Zs) p UJg nd ar (fun _ => [])) := by
  unfold nprepC
  exact nSynN_omacro_le 𝒢 labSel UJg nd ar _ _
    (fun c adj => nSynN_placed 𝒢 hadj srcPl (srcC c) (hsrcG c) adj) p.prepC

omit [DecidableEq S] [DecidableEq Zs] [DecidableEq Z] [Fintype Y] [DecidableEq Y] in
/-- **Time-dependent coefficients: the synthesised gates do not depend on the source
circuits.** If the supplied loading and weight-preparation circuits are circuits over the
adjoint-closed gate set `𝒢`, the synthesised gate occurrences of the native preparation are at
most the gates of the native preparation with empty source circuits. -/
theorem nSynN_tnprepC_le (hadj : AdjClosed 𝒢) (p : TParams) (UJg : List (Gate (Fin p.a ⊕ S)))
    (nd : NativeOp (TSel p.m p.l p.m) (Fin p.a ⊕ S) Z Y J)
    (ar : Arith (NB (TSel p.m p.l p.m) (Fin p.a ⊕ S) Z))
    (loadC : List (NInstr ((Fin (p.m + 1) ⊕ S) ⊕ Zs) Y J))
    (hloadG : ∀ g, NInstr.gate g ∈ loadC → GateOf 𝒢 g)
    (wpC : List (NInstr (Fin (p.m + 1) ⊕ Zs) Y J))
    (hwpG : ∀ g, NInstr.gate g ∈ wpC → GateOf 𝒢 g) :
    nSynN 𝒢 (tnprepC p UJg nd ar loadC wpC) ≤ nGatesN (tnprepC (Zs := Zs) p UJg nd ar [] []) := by
  unfold tnprepC
  refine nSynN_omacro_le 𝒢 tlabSel UJg nd ar _ _ (fun c adj => ?_) p.prepC
  cases c <;> cases adj
  · exact nSynN_placed 𝒢 hadj loadPl loadC hloadG false
  · exact nSynN_placed 𝒢 hadj loadPl loadC hloadG true
  · exact nSynN_placed 𝒢 hadj wpPl wpC hwpG false
  · exact nSynN_placed 𝒢 hadj wpPl wpC hwpG true

end Prep

end

end SparseHamiltonian.GateSelective
