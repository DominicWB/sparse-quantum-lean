import GateEfficientBinaryTime.Slot

/-!
# Slot-selected native operations with label selection wires

The coherent selection of Lemma `ode:lem:gate-select` by branch label and time slot, for native
private operations.

`GateBinary.nativeOK_slot` (library `GateEfficientBinaryTime`) extends a native private operation
*without* selection wires to time-slot selection wires. The private operations of the
time-dependent dissipative solver are selected by the label wires *and* the slot wires
(`GateNative.TSel`). This module generalises the transfer to a native operation with label
selection wires `Sel0`, extended by slot selection wires `Sel1`, and with a decoder that may read
the slot wires:

* `slotInstr2`: every elementary gate is placed on the same wires of the larger register
  (`baseW2`), every primitive call additionally reads the slot wires (`posExt2`);
* `slotOp2 V₀ o₀ dec`: the extended compute circuit, the orientation wire `o₀` and a decoder
  `dec` of the larger register; `atSlot2 V₀ o₀ dec w`: the operation without slot wires whose
  decoder is `dec` at the slot word `w` (`glue2`);
* `nrun_slot2`: the extended circuit acts, at slot word `w`, as the original circuit with the
  primitives `primAt w`; `Rdec_slot2`: the decoded rotation is, at slot word `w`, that of
  `atSlot2 … w`;
* `nativeOK_slot2`: if the native identity holds at every slot word `w` for `atSlot2 … w` and the
  label-selected family `Dat w`, it holds for `slotOp2 …`, the selection-controlled primitives
  `GateBinary.slotPrim primAt` and the label- and slot-selected family;
* counts, validity and the public conditions are those of the original circuit
  (`nGatesN_slot2`, `nCallsN_slot2`, `valid_slot2`, `slotOp2_public`, `atSlot2_public`).
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateBinaryODETime

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit SparseHamiltonian.GateNative
open SparseHamiltonian.GateBinary (slotPrim adjIf_localOp)
open SparseHamiltonian.GateODE (adjIf localOp_localOp' overwrite_apply_ι overwrite_apply_out
  update_comp_injective)
open scoped InnerProduct

/-! ### Wires of the doubly selected register -/

section Wires

variable {Sel0 Sel1 PR Z : Type*}

theorem baseW2_injective :
    Function.Injective (Sum.map (Sum.map Sum.inl id) id :
      NB Sel0 PR Z → NB (Sel0 ⊕ Sel1) PR Z) :=
  Sum.map_injective.2 ⟨Sum.map_injective.2 ⟨Sum.inl_injective, Function.injective_id⟩,
    Function.injective_id⟩

/-- The wires of the label-selected register inside the label- and slot-selected register. -/
def baseW2 : NB Sel0 PR Z ↪ NB (Sel0 ⊕ Sel1) PR Z :=
  ⟨Sum.map (Sum.map Sum.inl id) id, baseW2_injective⟩

/-- The slot wires of the label- and slot-selected register. -/
def selW2 : Sel1 ↪ NB (Sel0 ⊕ Sel1) PR Z :=
  ⟨fun s => Sum.inl (Sum.inl (Sum.inr s)), fun _ _ h => by simpa using h⟩

theorem selW2_ne_baseW2 (s : Sel1) (w : NB Sel0 PR Z) :
    (selW2 s : NB (Sel0 ⊕ Sel1) PR Z) ≠ baseW2 w := by
  rcases w with (e | p) | z <;> simp [selW2, baseW2]

/-- The slot word of a configuration. -/
def slotOf2 (c : Cfg (NB (Sel0 ⊕ Sel1) PR Z)) : Cfg Sel1 := fun s => c (selW2 s)

/-- The label-selected part of a configuration. -/
def baseOf2 (c : Cfg (NB (Sel0 ⊕ Sel1) PR Z)) : Cfg (NB Sel0 PR Z) := fun w => c (baseW2 w)

/-- The configuration with slot word `w` and label-selected part `y`. -/
def glue2 (w : Cfg Sel1) (y : Cfg (NB Sel0 PR Z)) : Cfg (NB (Sel0 ⊕ Sel1) PR Z)
  | Sum.inl (Sum.inl (Sum.inl s)) => y (Sum.inl (Sum.inl s))
  | Sum.inl (Sum.inl (Sum.inr s)) => w s
  | Sum.inl (Sum.inr p) => y (Sum.inl (Sum.inr p))
  | Sum.inr z => y (Sum.inr z)

theorem slotOf2_glue2 (w : Cfg Sel1) (y : Cfg (NB Sel0 PR Z)) : slotOf2 (glue2 w y) = w := rfl

theorem baseOf2_glue2 (w : Cfg Sel1) (y : Cfg (NB Sel0 PR Z)) : baseOf2 (glue2 w y) = y := by
  funext v
  rcases v with (s | p) | z <;> rfl

theorem glue2_slotOf2 (c : Cfg (NB (Sel0 ⊕ Sel1) PR Z)) : glue2 (slotOf2 c) (baseOf2 c) = c := by
  funext v
  rcases v with ((s | s) | p) | z <;> rfl

theorem glue2_apply_baseW2 (w : Cfg Sel1) (y : Cfg (NB Sel0 PR Z)) (v : NB Sel0 PR Z) :
    glue2 w y (baseW2 v) = y v := by
  rcases v with (s | p) | z <;> rfl

theorem cases_W2 (u : NB (Sel0 ⊕ Sel1) PR Z) :
    (∃ v, (baseW2 v : NB (Sel0 ⊕ Sel1) PR Z) = u) ∨ ∃ s, (selW2 s : NB (Sel0 ⊕ Sel1) PR Z) = u := by
  rcases u with ((s | s) | p) | z
  · exact Or.inl ⟨Sum.inl (Sum.inl s), rfl⟩
  · exact Or.inr ⟨s, rfl⟩
  · exact Or.inl ⟨Sum.inl (Sum.inr p), rfl⟩
  · exact Or.inl ⟨Sum.inr z, rfl⟩

theorem glue2_update [DecidableEq Sel0] [DecidableEq Sel1] [DecidableEq PR] [DecidableEq Z]
    (w : Cfg Sel1) (y : Cfg (NB Sel0 PR Z)) (v : NB Sel0 PR Z) (b : Bool) :
    glue2 w (Function.update y v b) = Function.update (glue2 w y) (baseW2 v) b := by
  funext u
  rcases cases_W2 u with ⟨v', rfl⟩ | ⟨s, rfl⟩
  · rw [glue2_apply_baseW2]
    by_cases h : v' = v
    · subst h
      rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne h, Function.update_of_ne (fun h' => h (baseW2.injective h')),
        glue2_apply_baseW2]
  · rw [Function.update_of_ne (selW2_ne_baseW2 s v)]
    rfl

/-- The positions of an extended call: the slot wires and the original positions. -/
def posExt2 {Y : Type*} (pos : Y ↪ NB Sel0 PR Z) : Sel1 ⊕ Y ↪ NB (Sel0 ⊕ Sel1) PR Z :=
  ⟨Sum.elim selW2 (fun y => baseW2 (pos y)),
    selW2.injective.sumElim (baseW2.injective.comp pos.injective)
      (fun s y => selW2_ne_baseW2 s (pos y))⟩

/-- **The extended instruction**: gates on the same wires, calls that also read the slot
wires. -/
def slotInstr2 {Y J : Type*} :
    NInstr (NB Sel0 PR Z) Y J → NInstr (NB (Sel0 ⊕ Sel1) PR Z) (Sel1 ⊕ Y) J
  | .gate g => .gate (GateODE.Gate.map baseW2 g)
  | .call j adj pos => .call j adj (posExt2 pos)

/-- **The label- and slot-selected native operation** with the extended compute circuit, the
orientation wire `o₀` and the decoder `dec`. -/
def slotOp2 {Y J : Type*} (V0 : List (NInstr (NB Sel0 PR Z) Y J)) (o0 : PR)
    (dec : Cfg (NB (Sel0 ⊕ Sel1) PR Z) → ℂ) : NativeOp (Sel0 ⊕ Sel1) PR Z (Sel1 ⊕ Y) J where
  V := V0.map slotInstr2
  o := o0
  dec := dec

/-- **The operation at the slot word `w`**: the original compute circuit and the decoder `dec`
read at the slot word `w`. -/
def atSlot2 {Y J : Type*} (V0 : List (NInstr (NB Sel0 PR Z) Y J)) (o0 : PR)
    (dec : Cfg (NB (Sel0 ⊕ Sel1) PR Z) → ℂ) (w : Cfg Sel1) : NativeOp Sel0 PR Z Y J where
  V := V0
  o := o0
  dec := fun y => dec (glue2 w y)

end Wires

/-! ### The extended run -/

section Run

variable {Sel0 Sel1 PR Z Y J : Type*} [Fintype Sel0] [DecidableEq Sel0] [Fintype Sel1]
  [DecidableEq Sel1] [Fintype PR] [DecidableEq PR] [Fintype Z] [DecidableEq Z] [Fintype Y]
  [DecidableEq Y]
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

omit [Fintype Sel1] in
theorem slotOf2_overwrite (z : Cfg (NB (Sel0 ⊕ Sel1) PR Z)) (c : Cfg (NB Sel0 PR Z)) :
    slotOf2 (overwrite (baseW2 : NB Sel0 PR Z ↪ NB (Sel0 ⊕ Sel1) PR Z) z c) = slotOf2 z := by
  funext s
  exact overwrite_apply_out _ z c _ (fun w h => selW2_ne_baseW2 s w h.symm)

omit [Fintype Sel1] in
theorem slotOf2_clearCfg (z : Cfg (NB (Sel0 ⊕ Sel1) PR Z)) :
    slotOf2 (clearCfg (baseW2 : NB Sel0 PR Z ↪ NB (Sel0 ⊕ Sel1) PR Z) z) = slotOf2 z :=
  slotOf2_overwrite z _

/-- One extended instruction acts, at slot word `w`, as the original instruction with the
primitives `primAt w`. -/
theorem eval_slotInstr2 (primAt : Cfg Sel1 → J → Reg Y R →L[ℂ] Reg Y R)
    (i : NInstr (NB Sel0 PR Z) Y J) :
    (slotInstr2 (Sel1 := Sel1) i).eval (slotPrim primAt) =
      localOp baseW2 baseW2.injective (fun c => i.eval (primAt (slotOf2 c))) := by
  cases i with
  | gate g => exact (GateODE.Gate.map_op baseW2.injective g).symm
  | call j adj pos =>
      change localOp (posExt2 pos) (posExt2 pos).injective
          (fun _ => adjIf adj (slotPrim primAt j)) =
        localOp baseW2 baseW2.injective
          (fun c => localOp pos pos.injective (fun _ => adjIf adj (primAt (slotOf2 c) j)))
      rw [slotPrim, adjIf_localOp,
        localOp_localOp' (posExt2 pos).injective Sum.inr_injective (fun y => baseW2 (pos y))
          (baseW2.injective.comp pos.injective) (fun _ => rfl)
          (fun _ c => adjIf adj (primAt (fun s => c (Sum.inl s)) j)),
        localOp_localOp' baseW2.injective pos.injective (fun y => baseW2 (pos y))
          (baseW2.injective.comp pos.injective) (fun _ => rfl)
          (fun c _ => adjIf adj (primAt (slotOf2 c) j))]
      congr 1
      funext z
      rw [slotOf2_clearCfg]
      have hz : (fun s => clearCfg (Sum.inr : Y → Sel1 ⊕ Y) (fun a => z (posExt2 pos a))
          (Sum.inl s)) = slotOf2 z := by
        funext s
        change overwrite (Sum.inr : Y → Sel1 ⊕ Y) (fun a => z (posExt2 pos a)) (fun _ => false)
          (Sum.inl s) = z (selW2 s)
        rw [overwrite_apply_out _ _ _ _ (fun y h => by cases h)]
        rfl
      rw [hz]

/-- **The extended compute circuit** acts, at slot word `w`, as the original circuit with the
primitives `primAt w`. -/
theorem nrun_slot2 (primAt : Cfg Sel1 → J → Reg Y R →L[ℂ] Reg Y R)
    (V : List (NInstr (NB Sel0 PR Z) Y J)) :
    nrun (slotPrim primAt) (V.map (slotInstr2 (Sel1 := Sel1))) =
      localOp baseW2 baseW2.injective (fun c => nrun (primAt (slotOf2 c)) V) := by
  induction V with
  | nil => exact (localOp_one _).symm
  | cons i V ih =>
      rw [List.map_cons, nrun_cons, ih, eval_slotInstr2, localOp_comp]
      rfl

/-- A one-qubit operation on the label-selected wires, selected by the slot word, is the
one-qubit operation on the renamed wire selected by the slot word. -/
theorem localOp_condOp_slot (t : NB Sel0 PR Z)
    (u : Cfg Sel1 → Cfg (NB Sel0 PR Z) → Matrix Bool Bool ℂ) :
    localOp (baseW2 : NB Sel0 PR Z ↪ NB (Sel0 ⊕ Sel1) PR Z) baseW2.injective
        (fun c => condOp (Q := R) t (u (slotOf2 c))) =
      condOp (baseW2 t) (fun z => u (slotOf2 z) (baseOf2 z)) := by
  unfold condOp
  rw [localOp_localOp' baseW2.injective (single_injective t) (fun _ => baseW2 t)
    (single_injective _) (fun _ => rfl) (fun c c' => matOp (qubitMat (u (slotOf2 c) c')))]
  apply localOp_congr
  intro z
  have h1 : slotOf2 (clearCfg (baseW2 : NB Sel0 PR Z ↪ NB (Sel0 ⊕ Sel1) PR Z)
      (clearCfg (fun _ : Unit => (baseW2 t : NB (Sel0 ⊕ Sel1) PR Z)) z)) = slotOf2 z := by
    rw [slotOf2_clearCfg, clearCfg_single]
    funext s
    exact Function.update_of_ne (selW2_ne_baseW2 s t) _ _
  have h2 : slotOf2 (clearCfg (fun _ : Unit => (baseW2 t : NB (Sel0 ⊕ Sel1) PR Z)) z) =
      slotOf2 z := by
    rw [clearCfg_single]
    funext s
    exact Function.update_of_ne (selW2_ne_baseW2 s t) _ _
  rw [h1]
  show _ = matOp (qubitMat (u (slotOf2 (clearCfg (fun _ : Unit =>
    (baseW2 t : NB (Sel0 ⊕ Sel1) PR Z)) z)) (baseOf2 (clearCfg (fun _ : Unit =>
      (baseW2 t : NB (Sel0 ⊕ Sel1) PR Z)) z))))
  rw [h2]
  congr 3
  funext a
  simp only [baseOf2, clearCfg_single, update_comp_injective baseW2.injective,
    Function.update_idem]
  exact (congrFun (update_comp_injective baseW2.injective z t false) a).symm

omit [Fintype Y] [DecidableEq Y] in
/-- **The decoded rotation** of the extended operation is, at slot word `w`, that of the
operation at the slot word `w`. -/
theorem Rdec_slot2 (V0 : List (NInstr (NB Sel0 PR Z) Y J)) (o0 : PR)
    (dec : Cfg (NB (Sel0 ⊕ Sel1) PR Z) → ℂ) :
    Rdec (R := R) (slotOp2 V0 o0 dec) =
      localOp baseW2 baseW2.injective (fun c => Rdec (R := R) (atSlot2 V0 o0 dec (slotOf2 c))) := by
  rw [Rdec]
  simp only [Rdec, atSlot2]
  rw [localOp_condOp_slot (Sum.inl (Sum.inr o0))
    (fun w y => edgeMat (dec (glue2 w y)))]
  congr 1
  funext z
  rw [glue2_slotOf2]
  rfl

end Run

/-! ### The native identity -/

section OK

variable {Sel0 Sel1 Z Y J : Type*} [Fintype Sel0] [DecidableEq Sel0] [Fintype Sel1]
  [DecidableEq Sel1] [Fintype Z] [DecidableEq Z] [Fintype Y] [DecidableEq Y]
  {S : Type*} [Fintype S] [DecidableEq S] {a : ℕ}
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- The column of a register vector of the label- and slot-selected private register at the slot
word `w`, as a vector of the label-selected private register. -/
def selSlice2 (ψ : Reg ((Sel0 ⊕ Sel1) ⊕ (Fin a ⊕ S)) R) (w : Cfg Sel1) :
    Reg (Sel0 ⊕ (Fin a ⊕ S)) R :=
  WithLp.toLp 2 (fun c0 => ψ (Sum.elim (Sum.elim (fun s => c0 (Sum.inl s)) w)
    (fun p => c0 (Sum.inr p))))

omit [Fintype Sel0] [DecidableEq Sel0] [Fintype Sel1] [DecidableEq Sel1] [Fintype S]
  [DecidableEq S] [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R] in
theorem selSlice2_apply (ψ : Reg ((Sel0 ⊕ Sel1) ⊕ (Fin a ⊕ S)) R) (w : Cfg Sel1)
    (c0 : Cfg (Sel0 ⊕ (Fin a ⊕ S))) :
    selSlice2 ψ w c0 = ψ (Sum.elim (Sum.elim (fun s => c0 (Sum.inl s)) w)
      (fun p => c0 (Sum.inr p))) := rfl

omit [Fintype Sel1] [CompleteSpace R] in
theorem slice_cleanEmb2 (ψ : Reg ((Sel0 ⊕ Sel1) ⊕ (Fin a ⊕ S)) R)
    (y : Cfg (NB (Sel0 ⊕ Sel1) (Fin a ⊕ S) Z)) :
    slice (baseW2 : NB Sel0 (Fin a ⊕ S) Z ↪ NB (Sel0 ⊕ Sel1) (Fin a ⊕ S) Z)
        (cleanEmb (X := Z) ψ) y =
      cleanEmb (X := Z) (selSlice2 ψ (slotOf2 y)) := by
  apply PiLp.ext
  intro b
  rw [slice_apply, cleanEmb_apply, cleanEmb_apply]
  have hz : (fun z => overwrite
      (baseW2 : NB Sel0 (Fin a ⊕ S) Z ↪ NB (Sel0 ⊕ Sel1) (Fin a ⊕ S) Z) y b (Sum.inr z)) =
      fun z => b (Sum.inr z) := by
    funext z
    exact overwrite_apply_ι baseW2.injective y b (Sum.inr z)
  rw [hz]
  split_ifs with h
  · have hc : (fun v => overwrite
        (baseW2 : NB Sel0 (Fin a ⊕ S) Z ↪ NB (Sel0 ⊕ Sel1) (Fin a ⊕ S) Z) y b (Sum.inl v)) =
        Sum.elim (Sum.elim (fun s => b (Sum.inl (Sum.inl s))) (slotOf2 y))
          (fun p => b (Sum.inl (Sum.inr p))) := by
      funext v
      rcases v with (s | s) | p
      · exact overwrite_apply_ι baseW2.injective y b (Sum.inl (Sum.inl s))
      · exact overwrite_apply_out _ y b _ (fun w hw => selW2_ne_baseW2 s w hw.symm)
      · exact overwrite_apply_ι baseW2.injective y b (Sum.inl (Sum.inr p))
    rw [hc]
    rfl
  · rfl

/-- **The native identity at every slot word gives the native identity of the label- and
slot-selected operation.** -/
theorem nativeOK_slot2 (primAt : Cfg Sel1 → J → Reg Y R →L[ℂ] Reg Y R)
    (V0 : List (NInstr (NB Sel0 (Fin a ⊕ S) Z) Y J)) (o0 : Fin a ⊕ S)
    (dec : Cfg (NB (Sel0 ⊕ Sel1) (Fin a ⊕ S) Z) → ℂ)
    (Dat : Cfg Sel1 → Cfg Sel0 → (Reg (Fin a) (Reg S R) →L[ℂ] Reg (Fin a) (Reg S R)))
    (hOK : ∀ w, NativeOK (primAt w) (atSlot2 V0 o0 dec w) (selOp (Dat w))) :
    NativeOK (slotPrim primAt) (slotOp2 V0 o0 dec)
      (selOp (fun y => Dat (fun s => y (Sum.inr s)) (fun s => y (Sum.inl s)))) := by
  unfold NativeOK at hOK ⊢
  have hV : (slotOp2 (Sel1 := Sel1) V0 o0 dec).V = V0.map slotInstr2 := rfl
  rw [hV, nrun_slot2, Rdec_slot2, localOp_adjoint, ← comp_assoc, ← comp_assoc,
    localOp_comp, localOp_comp]
  ext ψ y
  rw [comp_apply, localOp_apply, slotOf2_clearCfg, slice_cleanEmb2]
  have h := congrArg (fun T => T (selSlice2 ψ (slotOf2 y)) (baseOf2 y)) (hOK (slotOf2 y))
  simp only [comp_apply] at h
  refine h.trans ?_
  rw [comp_apply, cleanEmb_apply, cleanEmb_apply]
  have hzz : (fun x => baseOf2 y (Sum.inr x)) = (fun x => y (Sum.inr x)) := rfl
  rw [hzz]
  split_ifs with hz
  · rw [selOp, selOp, localOp_apply, localOp_apply]
    have hw : (fun s => clearCfg (Sum.inr : Fin a ⊕ S → (Sel0 ⊕ Sel1) ⊕ (Fin a ⊕ S))
        (fun b => y (Sum.inl b)) (Sum.inl s)) = fun s => y (Sum.inl (Sum.inl s)) := by
      funext s
      exact overwrite_apply_out _ _ _ _ (fun p h => by cases h)
    have hw0 : (fun s => clearCfg (Sum.inr : Fin a ⊕ S → Sel0 ⊕ (Fin a ⊕ S))
        (fun b => baseOf2 y (Sum.inl b)) (Sum.inl s)) =
        fun s => y (Sum.inl (Sum.inl (Sum.inl s))) := by
      funext s
      exact overwrite_apply_out _ _ _ _ (fun p h => by cases h)
    rw [hw, hw0]
    have hs : slice (Sum.inr : Fin a ⊕ S → Sel0 ⊕ (Fin a ⊕ S)) (selSlice2 ψ (slotOf2 y))
        (fun b => baseOf2 y (Sum.inl b)) =
        slice (Sum.inr : Fin a ⊕ S → (Sel0 ⊕ Sel1) ⊕ (Fin a ⊕ S)) ψ (fun b => y (Sum.inl b)) := by
      apply PiLp.ext
      intro p
      rw [slice_apply, slice_apply, selSlice2_apply]
      have e1 : (fun q => overwrite (Sum.inr : Fin a ⊕ S → Sel0 ⊕ (Fin a ⊕ S))
          (fun b => baseOf2 y (Sum.inl b)) p (Sum.inr q)) = p :=
        funext (fun q => overwrite_apply_ι Sum.inr_injective _ p q)
      have e0 : (fun s => overwrite (Sum.inr : Fin a ⊕ S → Sel0 ⊕ (Fin a ⊕ S))
          (fun b => baseOf2 y (Sum.inl b)) p (Sum.inl s)) =
          fun s => y (Sum.inl (Sum.inl (Sum.inl s))) := by
        funext s
        exact overwrite_apply_out _ _ _ _ (fun r h => by cases h)
      have e2 : overwrite (Sum.inr : Fin a ⊕ S → (Sel0 ⊕ Sel1) ⊕ (Fin a ⊕ S))
          (fun b => y (Sum.inl b)) p =
          Sum.elim (Sum.elim (fun s => y (Sum.inl (Sum.inl (Sum.inl s)))) (slotOf2 y)) p := by
        funext v
        rcases v with (s | s) | q
        · exact overwrite_apply_out _ _ _ _ (fun r h => by cases h)
        · exact overwrite_apply_out _ _ _ _ (fun r h => by cases h)
        · exact overwrite_apply_ι Sum.inr_injective _ p q
      rw [e1, e0, e2]
    rw [hs]
    rfl
  · rfl

end OK

/-! ### Counts, validity and public data -/

section Counts

variable {Sel0 Sel1 PR Z Y J : Type*}

theorem nGatesN_slot2 (V : List (NInstr (NB Sel0 PR Z) Y J)) :
    nGatesN (V.map (slotInstr2 (Sel1 := Sel1))) = nGatesN V := by
  unfold nGatesN
  rw [List.countP_map]
  congr 1
  funext i
  cases i <;> rfl

theorem nCallsN_slot2 (p : J → Bool) (V : List (NInstr (NB Sel0 PR Z) Y J)) :
    nCallsN p (V.map (slotInstr2 (Sel1 := Sel1))) = nCallsN p V := by
  unfold nCallsN
  rw [List.countP_map]
  congr 1
  funext i
  cases i <;> rfl

theorem valid_slot2 (V : List (NInstr (NB Sel0 PR Z) Y J)) (h : ∀ i ∈ V, i.Valid) :
    ∀ i ∈ V.map (slotInstr2 (Sel1 := Sel1)), i.Valid := by
  intro i hi
  rw [List.mem_map] at hi
  obtain ⟨i', hi', rfl⟩ := hi
  have hv := h i' hi'
  cases i' with
  | gate g =>
      obtain ⟨h1, h2, h3⟩ := hv
      refine ⟨by simpa [GateODE.Gate.map] using h1, ?_, h3⟩
      intro c hc
      simp only [GateODE.Gate.map, List.mem_map] at hc
      obtain ⟨c', hc', rfl⟩ := hc
      intro e
      exact h2 c' hc' (baseW2.injective e)
  | call j adj pos => trivial

variable [DecidableEq Sel0] [DecidableEq Sel1] [DecidableEq PR] [DecidableEq Z]

/-- The extended operation is public when the original circuit is valid and the decoder does not
read the orientation wire. -/
theorem slotOp2_public (V0 : List (NInstr (NB Sel0 PR Z) Y J)) (hV0 : ∀ i ∈ V0, i.Valid)
    (o0 : PR) (dec : Cfg (NB (Sel0 ⊕ Sel1) PR Z) → ℂ)
    (hdec : ∀ x b, dec (Function.update x (Sum.inl (Sum.inr o0)) b) = dec x) :
    (slotOp2 V0 o0 dec).Public where
  valid := valid_slot2 V0 hV0
  dec_indep := hdec

/-- The operation at every slot word is public under the same conditions. -/
theorem atSlot2_public (V0 : List (NInstr (NB Sel0 PR Z) Y J)) (hV0 : ∀ i ∈ V0, i.Valid)
    (o0 : PR) (dec : Cfg (NB (Sel0 ⊕ Sel1) PR Z) → ℂ)
    (hdec : ∀ x b, dec (Function.update x (Sum.inl (Sum.inr o0)) b) = dec x) (w : Cfg Sel1) :
    (atSlot2 V0 o0 dec w).Public where
  valid := hV0
  dec_indep x b := by
    change dec (glue2 w (Function.update x (Sum.inl (Sum.inr o0)) b)) = dec (glue2 w x)
    rw [glue2_update]
    exact hdec _ b

end Counts

end

end SparseHamiltonian.GateBinaryODETime
