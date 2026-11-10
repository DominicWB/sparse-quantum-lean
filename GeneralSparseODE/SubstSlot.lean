import GeneralSparseODE.Subst
import GateEfficientBinaryODETime.Slot

/-!
# Substituted slot-selected native operations

The private operations of the time-dependent solver (`GateBinaryODETime.slotOp2`) extend a compute
circuit `V₀` with label selection wires by slot selection wires: every primitive call also reads the
slot wires, and at every slot word `w` the operation acts as `atSlot2 V₀ o₀ dec w` with the
primitives `primAt w` (`GateBinaryODETime.nativeOK_slot2`). If at every slot word the primitives
`primAt' w` called by `V₀` are implemented by the circuits `impl` from the primitives `primAt w` on
clean ancillas (`GeneralSparseAccess.ImplOK`), the **substituted slot-selected operation**
`substSlot V₀ o₀ dec impl` (the substituted circuit `subst impl V₀` on the base wires with the
ancillas added to the scratch, extended to the slot wires, and the decoder on the base wires) has
the native identity of `slotOp2 V₀ o₀ dec` for the selection-controlled primitives
`slotPrim primAt`:

* `atSlot2_substSlot`: at every slot word it is the substituted operation (`substOp`) of the
  operation at that word;
* `nativeOK_substSlot`: the native identity, with the same selected family;
* `substSlot_public`, `nGatesN_substSlot_le`, `nCallsN_substSlot_le`: the public conditions, at most
  `G` more gates per call and at most `c` calls per call of the same kind.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GeneralSparseODE

noncomputable section
open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
open SparseHamiltonian.GeneralSparseAccess
open SparseHamiltonian.OracleCircuit
open SparseHamiltonian.GateBinary (slotPrim)
open SparseHamiltonian.GateBinaryODETime (slotOp2 atSlot2 slotInstr2 glue2 nativeOK_slot2
  slotOp2_public atSlot2_public nGatesN_slot2 nCallsN_slot2)
open SparseHamiltonian.GateODE (update_comp_injective)
open scoped InnerProduct

section Def

variable {Sel0 Sel1 PR Z Y Y' J J' Xa : Type*}

/-- **The substituted slot-selected operation**: the compute circuit `V₀` with every primitive call
replaced by its implementation on the ancillas `Xa` of the scratch, every call of the result also
reading the slot wires, the orientation wire `o₀` and the decoder `dec` read on the base wires. -/
def substSlot (V0 : List (NInstr (NB Sel0 PR Z) Y' J')) (o0 : PR)
    (dec : Cfg (NB (Sel0 ⊕ Sel1) PR Z) → ℂ) (impl : J' → List (NInstr (Y' ⊕ Xa) Y J)) :
    NativeOp (Sel0 ⊕ Sel1) PR (Z ⊕ Xa) (Sel1 ⊕ Y) J :=
  slotOp2 ((subst impl V0).map (NInstr.map ascE)) o0 (fun y => dec (fun v => y (inclZ v)))

/-- **At every slot word** the substituted slot-selected operation is the substituted operation of
the operation at that word. -/
theorem atSlot2_substSlot (V0 : List (NInstr (NB Sel0 PR Z) Y' J')) (o0 : PR)
    (dec : Cfg (NB (Sel0 ⊕ Sel1) PR Z) → ℂ) (impl : J' → List (NInstr (Y' ⊕ Xa) Y J))
    (w : Cfg Sel1) :
    atSlot2 ((subst impl V0).map (NInstr.map ascE)) o0 (fun y => dec (fun v => y (inclZ v))) w =
      substOp (atSlot2 V0 o0 dec w) impl := by
  have e : ∀ y : Cfg (NB Sel0 PR (Z ⊕ Xa)),
      (fun v : NB (Sel0 ⊕ Sel1) PR Z => glue2 w y (inclZ v)) =
        glue2 w (fun v => y (inclZ v)) := by
    intro y
    funext v
    rcases v with ((s | s) | p) | z <;> rfl
  show NativeOp.mk ((subst impl V0).map (NInstr.map ascE)) o0
      (fun y => dec (fun v => glue2 w y (inclZ v))) =
    NativeOp.mk ((subst impl V0).map (NInstr.map ascE)) o0
      (fun y => dec (glue2 w (fun v => y (inclZ v))))
  congr 1
  funext y
  rw [e y]

end Def

section OK

variable {Sel0 Sel1 Z Y Y' J J' Xa : Type*} [Fintype Sel0] [DecidableEq Sel0] [Fintype Sel1]
  [DecidableEq Sel1] [Fintype Z] [DecidableEq Z] [Fintype Y] [DecidableEq Y] [Fintype Y']
  [DecidableEq Y'] [Fintype Xa] [DecidableEq Xa] {S : Type*} [Fintype S] [DecidableEq S] {a : ℕ}
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- **The native identity of the substituted slot-selected operation**: if at every slot word `w`
the circuits `impl` implement the primitives `primAt' w` from `primAt w` and the operation at `w`
has the native identity for `primAt' w` and the label-selected family `Dat w`, the substituted
slot-selected operation has the native identity for the selection-controlled primitives
`slotPrim primAt` and the label- and slot-selected family. -/
theorem nativeOK_substSlot (primAt : Cfg Sel1 → J → Reg Y R →L[ℂ] Reg Y R)
    (primAt' : Cfg Sel1 → J' → Reg Y' R →L[ℂ] Reg Y' R)
    (hprim : ∀ w j, IsUnitary (primAt w j)) (hprim' : ∀ w j, IsUnitary (primAt' w j))
    {impl : J' → List (NInstr (Y' ⊕ Xa) Y J)} (himpl : ∀ w, ImplOK (primAt w) (primAt' w) impl)
    (V0 : List (NInstr (NB Sel0 (Fin a ⊕ S) Z) Y' J')) (hV0 : ∀ i ∈ V0, i.Valid)
    (o0 : Fin a ⊕ S) (dec : Cfg (NB (Sel0 ⊕ Sel1) (Fin a ⊕ S) Z) → ℂ)
    (hdec : ∀ x b, dec (Function.update x (Sum.inl (Sum.inr o0)) b) = dec x)
    (Dat : Cfg Sel1 → Cfg Sel0 → (Reg (Fin a) (Reg S R) →L[ℂ] Reg (Fin a) (Reg S R)))
    (hOK : ∀ w, NativeOK (primAt' w) (atSlot2 V0 o0 dec w) (selOp (Dat w))) :
    NativeOK (slotPrim primAt) (substSlot V0 o0 dec impl)
      (selOp (fun y => Dat (fun s => y (Sum.inr s)) (fun s => y (Sum.inl s)))) := by
  unfold substSlot
  refine nativeOK_slot2 primAt _ o0 _ Dat (fun w => ?_)
  rw [atSlot2_substSlot]
  exact nativeOK_substOp (primAt w) (primAt' w) (hprim w) (hprim' w) (himpl w)
    (atSlot2 V0 o0 dec w) (atSlot2_public V0 hV0 o0 dec hdec w) (selOp (Dat w)) (hOK w)

end OK

section Counts

variable {Sel0 Sel1 PR Z Y Y' J J' Xa : Type*}

/-- **The substituted slot-selected operation is public** for a valid circuit, valid
implementations and a decoder that does not read the orientation wire. -/
theorem substSlot_public [DecidableEq Sel0] [DecidableEq Sel1] [DecidableEq PR] [DecidableEq Z]
    [DecidableEq Xa] (V0 : List (NInstr (NB Sel0 PR Z) Y' J')) (hV0 : ∀ i ∈ V0, i.Valid)
    (o0 : PR) (dec : Cfg (NB (Sel0 ⊕ Sel1) PR Z) → ℂ)
    (hdec : ∀ x b, dec (Function.update x (Sum.inl (Sum.inr o0)) b) = dec x)
    {impl : J' → List (NInstr (Y' ⊕ Xa) Y J)} (hv : ∀ j, ∀ i ∈ impl j, i.Valid) :
    (substSlot V0 o0 dec impl).Public :=
  slotOp2_public _ (valid_map_list ascE _ (valid_subst hv V0 hV0)) o0 _ (fun x b => by
    have e : (fun v => Function.update x (Sum.inl (Sum.inr o0)) b
        (inclZ (Xa := Xa) (Sel := Sel0 ⊕ Sel1) (PR := PR) (Z := Z) v)) =
        Function.update (fun v => x (inclZ v)) (Sum.inl (Sum.inr o0)) b :=
      update_comp_injective (inclZ (Xa := Xa) (Sel := Sel0 ⊕ Sel1) (PR := PR) (Z := Z)).injective
        x (Sum.inl (Sum.inr o0)) b
    show dec (fun v => Function.update x (Sum.inl (Sum.inr o0)) b (inclZ v)) =
      dec (fun v => x (inclZ v))
    rw [e]
    exact hdec _ b)

/-- **The gates of the substituted slot-selected compute circuit**: at most `G` more per call. -/
theorem nGatesN_substSlot_le (V0 : List (NInstr (NB Sel0 PR Z) Y' J')) (o0 : PR)
    (dec : Cfg (NB (Sel0 ⊕ Sel1) PR Z) → ℂ) (impl : J' → List (NInstr (Y' ⊕ Xa) Y J)) (G : ℕ)
    (hG : ∀ j, nGatesN (impl j) ≤ G) :
    nGatesN (substSlot V0 o0 dec impl).V ≤ nGatesN V0 + G * nCallsN (fun _ => true) V0 := by
  show nGatesN (((subst impl V0).map (NInstr.map ascE)).map (slotInstr2 (Sel1 := Sel1))) ≤ _
  rw [nGatesN_slot2, nGatesN_map]
  exact nGatesN_subst_le impl G hG V0

/-- **The calls of the substituted slot-selected compute circuit**: at most `c` of the kind `p`
per call of the kind `p`. -/
theorem nCallsN_substSlot_le (V0 : List (NInstr (NB Sel0 PR Z) Y' J')) (o0 : PR)
    (dec : Cfg (NB (Sel0 ⊕ Sel1) PR Z) → ℂ) {impl : J' → List (NInstr (Y' ⊕ Xa) Y J)}
    {kind : J → J'} {c : ℕ} (h : KindOK impl kind c) (p : J' → Bool) :
    nCallsN (fun j => p (kind j)) (substSlot V0 o0 dec impl).V ≤ c * nCallsN p V0 := by
  show nCallsN _ (((subst impl V0).map (NInstr.map ascE)).map (slotInstr2 (Sel1 := Sel1))) ≤ _
  rw [nCallsN_slot2, nCallsN_map]
  exact nCallsN_subst_le h p V0

end Counts

end

end SparseHamiltonian.GeneralSparseODE
