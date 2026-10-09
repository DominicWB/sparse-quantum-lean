import GateEfficientBinaryODETime.Slot
import GateEfficientBinary.Sparse.Oracles

/-!
# Native operations reading a computed address

Two generic transfers of the native identity `GateNative.NativeOK`, used for the private
operation of Lemma `ode:lem:gate-select` on branch-dependent meshes, whose primitive calls read a
sample address computed from the label and the slot.

**Calls reading part of the context** (`slotInstrR`, `slotOpR`, `nativeOK_slotR`). The transfer
`GateBinaryODETime.nativeOK_slot2` extends a label-selected native operation by context wires
`Sel1`, every primitive call reading all of `Sel1`. Here a call reads only the wires `ι : Sel2 ↪
Sel1` of the context (the address bits): the primitives are the selection-controlled
`GateBinary.slotPrim primAt` on `Sel2`, and if the native identity holds at every context word
`c` for the primitives `primAt (c ∘ ι)`, it holds for the extended operation (`nativeOK_slotR`).

**Computed selection** (`reE`, `xorF`, `nativeOK_computed`). A native operation `ndA` selected by
label wires `Sel0`, slot wires `Sel1` and further wires `Za` is turned into an operation `nd`
selected by `Sel0 ⊕ Sel1` alone, the wires `Za` becoming scratch: the compute circuit of `nd` is
a circuit `APN` that, on clean scratch, writes `f σ` into `Za` for the selection `σ` (the XOR
permutation `xorF f`), followed by the compute circuit of `ndA` on the reassociated wires
(`reE`). Then `nd` has the native identity for the family `σ ↦ DatA (σ, f σ)`
(`nativeOK_computed`). `classical_hAP` gives the hypothesis on `APN` for a classical gate list.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateBinarySelect

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit SparseHamiltonian.GateNative
open SparseHamiltonian.GateBinary (slotPrim adjIf_localOp localOp_condOp ext_bas_clm'
  cleanEmb_bas permOp_bas)
open SparseHamiltonian.GateBinaryODETime (baseW2 selW2 slotOf2 baseOf2 glue2 atSlot2 slotOp2
  selW2_ne_baseW2 slotOf2_clearCfg Rdec_slot2 selSlice2 slice_cleanEmb2 baseW2_injective)
open SparseHamiltonian.GateODE (adjIf localOp_localOp' overwrite_apply_ι overwrite_apply_out
  update_comp_injective)
open scoped InnerProduct

/-! ### Calls reading part of the context -/

section Wires

variable {Sel0 Sel1 Sel2 PR Z : Type*}

/-- The positions of a restricted call: the wires `ι` of the context and the original
positions. -/
def posExtR {Y : Type*} (ι : Sel2 ↪ Sel1) (pos : Y ↪ NB Sel0 PR Z) :
    Sel2 ⊕ Y ↪ NB (Sel0 ⊕ Sel1) PR Z :=
  ⟨Sum.elim (fun s => selW2 (ι s)) (fun y => baseW2 (pos y)),
    (selW2.injective.comp ι.injective).sumElim (baseW2.injective.comp pos.injective)
      (fun s y => selW2_ne_baseW2 (ι s) (pos y))⟩

/-- **The restricted instruction**: gates on the same wires, calls that also read the wires
`ι` of the context. -/
def slotInstrR {Y J : Type*} (ι : Sel2 ↪ Sel1) :
    NInstr (NB Sel0 PR Z) Y J → NInstr (NB (Sel0 ⊕ Sel1) PR Z) (Sel2 ⊕ Y) J
  | .gate g => .gate (GateODE.Gate.map baseW2 g)
  | .call j adj pos => .call j adj (posExtR ι pos)

/-- **The extended operation with restricted calls**, the orientation wire `o₀` and the decoder
`dec`. -/
def slotOpR {Y J : Type*} (ι : Sel2 ↪ Sel1) (V0 : List (NInstr (NB Sel0 PR Z) Y J)) (o0 : PR)
    (dec : Cfg (NB (Sel0 ⊕ Sel1) PR Z) → ℂ) : NativeOp (Sel0 ⊕ Sel1) PR Z (Sel2 ⊕ Y) J where
  V := V0.map (slotInstrR ι)
  o := o0
  dec := dec

end Wires

section Run

variable {Sel0 Sel1 Sel2 PR Z Y J : Type*} [Fintype Sel0] [DecidableEq Sel0] [Fintype Sel1]
  [DecidableEq Sel1] [Fintype Sel2] [DecidableEq Sel2] [Fintype PR] [DecidableEq PR] [Fintype Z]
  [DecidableEq Z] [Fintype Y] [DecidableEq Y]
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- One restricted instruction acts, at context word `c`, as the original instruction with the
primitives `primAt (c ∘ ι)`. -/
theorem eval_slotInstrR (ι : Sel2 ↪ Sel1) (primAt : Cfg Sel2 → J → Reg Y R →L[ℂ] Reg Y R)
    (i : NInstr (NB Sel0 PR Z) Y J) :
    (slotInstrR (Sel1 := Sel1) ι i).eval (slotPrim primAt) =
      localOp baseW2 baseW2.injective
        (fun c => i.eval (primAt (fun s => slotOf2 c (ι s)))) := by
  cases i with
  | gate g => exact (GateODE.Gate.map_op baseW2.injective g).symm
  | call j adj pos =>
      change localOp (posExtR ι pos) (posExtR ι pos).injective
          (fun _ => adjIf adj (slotPrim primAt j)) =
        localOp baseW2 baseW2.injective
          (fun c => localOp pos pos.injective
            (fun _ => adjIf adj (primAt (fun s => slotOf2 c (ι s)) j)))
      rw [slotPrim, adjIf_localOp,
        localOp_localOp' (posExtR ι pos).injective Sum.inr_injective (fun y => baseW2 (pos y))
          (baseW2.injective.comp pos.injective) (fun _ => rfl)
          (fun _ c => adjIf adj (primAt (fun s => c (Sum.inl s)) j)),
        localOp_localOp' baseW2.injective pos.injective (fun y => baseW2 (pos y))
          (baseW2.injective.comp pos.injective) (fun _ => rfl)
          (fun c _ => adjIf adj (primAt (fun s => slotOf2 c (ι s)) j))]
      congr 1
      funext z
      rw [slotOf2_clearCfg]
      have hz : (fun s => clearCfg (Sum.inr : Y → Sel2 ⊕ Y) (fun a => z (posExtR ι pos a))
          (Sum.inl s)) = fun s => slotOf2 z (ι s) := by
        funext s
        change overwrite (Sum.inr : Y → Sel2 ⊕ Y) (fun a => z (posExtR ι pos a)) (fun _ => false)
          (Sum.inl s) = z (selW2 (ι s))
        rw [overwrite_apply_out _ _ _ _ (fun y h => by cases h)]
        rfl
      rw [hz]

/-- **The extended compute circuit with restricted calls** acts, at context word `c`, as the
original circuit with the primitives `primAt (c ∘ ι)`. -/
theorem nrun_slotR (ι : Sel2 ↪ Sel1) (primAt : Cfg Sel2 → J → Reg Y R →L[ℂ] Reg Y R)
    (V : List (NInstr (NB Sel0 PR Z) Y J)) :
    nrun (slotPrim primAt) (V.map (slotInstrR (Sel1 := Sel1) ι)) =
      localOp baseW2 baseW2.injective
        (fun c => nrun (primAt (fun s => slotOf2 c (ι s))) V) := by
  induction V with
  | nil => exact (localOp_one _).symm
  | cons i V ih =>
      rw [List.map_cons, nrun_cons, ih, eval_slotInstrR, localOp_comp]
      rfl

omit [Fintype Y] [DecidableEq Y] [Fintype Sel2] [DecidableEq Sel2] in
/-- The decoded rotation of the restricted operation is that of the operation at the context
word. -/
theorem Rdec_slotR (ι : Sel2 ↪ Sel1) (V0 : List (NInstr (NB Sel0 PR Z) Y J)) (o0 : PR)
    (dec : Cfg (NB (Sel0 ⊕ Sel1) PR Z) → ℂ) :
    Rdec (R := R) (slotOpR ι V0 o0 dec) =
      localOp baseW2 baseW2.injective
        (fun c => Rdec (R := R) (atSlot2 V0 o0 dec (slotOf2 c))) :=
  Rdec_slot2 V0 o0 dec

end Run

section OK

variable {Sel0 Sel1 Sel2 Z Y J : Type*} [Fintype Sel0] [DecidableEq Sel0] [Fintype Sel1]
  [DecidableEq Sel1] [Fintype Sel2] [DecidableEq Sel2] [Fintype Z] [DecidableEq Z] [Fintype Y]
  [DecidableEq Y] {S : Type*} [Fintype S] [DecidableEq S] {a : ℕ}
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- **The native identity at every context word gives the native identity of the extended
operation with restricted calls.** -/
theorem nativeOK_slotR (ι : Sel2 ↪ Sel1) (primAt : Cfg Sel2 → J → Reg Y R →L[ℂ] Reg Y R)
    (V0 : List (NInstr (NB Sel0 (Fin a ⊕ S) Z) Y J)) (o0 : Fin a ⊕ S)
    (dec : Cfg (NB (Sel0 ⊕ Sel1) (Fin a ⊕ S) Z) → ℂ)
    (Dat : Cfg Sel1 → Cfg Sel0 → (Reg (Fin a) (Reg S R) →L[ℂ] Reg (Fin a) (Reg S R)))
    (hOK : ∀ c, NativeOK (primAt (fun s => c (ι s))) (atSlot2 V0 o0 dec c) (selOp (Dat c))) :
    NativeOK (slotPrim primAt) (slotOpR ι V0 o0 dec)
      (selOp (fun y => Dat (fun s => y (Sum.inr s)) (fun s => y (Sum.inl s)))) := by
  unfold NativeOK at hOK ⊢
  have hV : (slotOpR (Sel1 := Sel1) ι V0 o0 dec).V = V0.map (slotInstrR ι) := rfl
  rw [hV, nrun_slotR, Rdec_slotR, localOp_adjoint, ← comp_assoc, ← comp_assoc,
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
      rw [slice_apply, slice_apply, GateBinaryODETime.selSlice2_apply]
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

/-! ### Counts, validity and public data of restricted operations -/

section Counts

variable {Sel0 Sel1 Sel2 PR Z Y J : Type*}

theorem nGatesN_slotR (ι : Sel2 ↪ Sel1) (V : List (NInstr (NB Sel0 PR Z) Y J)) :
    nGatesN (V.map (slotInstrR (Sel1 := Sel1) ι)) = nGatesN V := by
  unfold nGatesN
  rw [List.countP_map]
  congr 1
  funext i
  cases i <;> rfl

theorem nCallsN_slotR (ι : Sel2 ↪ Sel1) (p : J → Bool) (V : List (NInstr (NB Sel0 PR Z) Y J)) :
    nCallsN p (V.map (slotInstrR (Sel1 := Sel1) ι)) = nCallsN p V := by
  unfold nCallsN
  rw [List.countP_map]
  congr 1
  funext i
  cases i <;> rfl

theorem valid_slotR (ι : Sel2 ↪ Sel1) (V : List (NInstr (NB Sel0 PR Z) Y J))
    (h : ∀ i ∈ V, i.Valid) : ∀ i ∈ V.map (slotInstrR (Sel1 := Sel1) ι), i.Valid := by
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

end Counts

/-! ### Computed selection -/

section Reassoc

variable {Sel0 Sel1 Za PR Z : Type*}

/-- The reassociation of the wires: the wires `Za` move from the selection to the scratch. -/
def reE : NB (Sel0 ⊕ (Sel1 ⊕ Za)) PR Z ≃ NB (Sel0 ⊕ Sel1) PR (Za ⊕ Z) where
  toFun
    | .inl (.inl (.inl s)) => .inl (.inl (.inl s))
    | .inl (.inl (.inr (.inl s))) => .inl (.inl (.inr s))
    | .inl (.inl (.inr (.inr t))) => .inr (.inl t)
    | .inl (.inr p) => .inl (.inr p)
    | .inr z => .inr (.inr z)
  invFun
    | .inl (.inl (.inl s)) => .inl (.inl (.inl s))
    | .inl (.inl (.inr s)) => .inl (.inl (.inr (.inl s)))
    | .inl (.inr p) => .inl (.inr p)
    | .inr (.inl t) => .inl (.inl (.inr (.inr t)))
    | .inr (.inr z) => .inr z
  left_inv w := by rcases w with ((s | s | t) | p) | z <;> rfl
  right_inv w := by rcases w with ((s | s) | p) | t | z <;> rfl

/-- The reassociation as an embedding. -/
def reW : NB (Sel0 ⊕ (Sel1 ⊕ Za)) PR Z ↪ NB (Sel0 ⊕ Sel1) PR (Za ⊕ Z) :=
  (reE (Sel0 := Sel0) (Sel1 := Sel1) (Za := Za) (PR := PR) (Z := Z)).toEmbedding

/-- The selection part of a configuration. -/
def selP (y : Cfg (NB (Sel0 ⊕ Sel1) PR (Za ⊕ Z))) : Cfg (Sel0 ⊕ Sel1) :=
  fun s => y (Sum.inl (Sum.inl s))

/-- XOR the computed word `f σ` of the selection into the wires `Za`. -/
def xorFun (f : Cfg (Sel0 ⊕ Sel1) → Cfg Za) (y : Cfg (NB (Sel0 ⊕ Sel1) PR (Za ⊕ Z))) :
    Cfg (NB (Sel0 ⊕ Sel1) PR (Za ⊕ Z)) := fun w => match w with
  | .inr (.inl t) => y (.inr (.inl t)) ^^ f (selP y) t
  | w => y w

theorem selP_xorFun (f : Cfg (Sel0 ⊕ Sel1) → Cfg Za) (y : Cfg (NB (Sel0 ⊕ Sel1) PR (Za ⊕ Z))) :
    selP (xorFun f y) = selP y := rfl

theorem xor_false_iff (a b : Bool) : (a ^^ b) = false ↔ a = b := by
  cases a <;> cases b <;> decide

theorem xorFun_xorFun (f : Cfg (Sel0 ⊕ Sel1) → Cfg Za) (y : Cfg (NB (Sel0 ⊕ Sel1) PR (Za ⊕ Z))) :
    xorFun f (xorFun f y) = y := by
  funext w
  rcases w with ((s | s) | p) | t | z
  · rfl
  · rfl
  · rfl
  · change (xorFun f y (Sum.inr (Sum.inl t)) ^^ f (selP (xorFun f y)) t) = y (Sum.inr (Sum.inl t))
    rw [selP_xorFun]
    change ((y (Sum.inr (Sum.inl t)) ^^ f (selP y) t) ^^ f (selP y) t) = y (Sum.inr (Sum.inl t))
    rw [Bool.xor_assoc, Bool.xor_self, Bool.xor_false]
  · rfl

/-- **XOR the computed word `f σ` of the selection into the wires `Za`** (an involution). -/
def xorF (f : Cfg (Sel0 ⊕ Sel1) → Cfg Za) :
    Cfg (NB (Sel0 ⊕ Sel1) PR (Za ⊕ Z)) ≃ Cfg (NB (Sel0 ⊕ Sel1) PR (Za ⊕ Z)) where
  toFun := xorFun f
  invFun := xorFun f
  left_inv y := xorFun_xorFun f y
  right_inv y := xorFun_xorFun f y

theorem xorF_symm (f : Cfg (Sel0 ⊕ Sel1) → Cfg Za) :
    (xorF (PR := PR) (Z := Z) f).symm = xorF f := rfl

end Reassoc

section Computed

variable {Sel0 Sel1 Za Z Y J : Type*} [Fintype Sel0] [DecidableEq Sel0] [Fintype Sel1]
  [DecidableEq Sel1] [Fintype Za] [DecidableEq Za] [Fintype Z] [DecidableEq Z] [Fintype Y]
  [DecidableEq Y] {S : Type*} [Fintype S] [DecidableEq S] {a : ℕ}
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

omit [CompleteSpace R] in
/-- The clean embedding followed by the XOR permutation, evaluated: the selection and the
private register are kept, the wires `Za` carry `f σ`, the scratch `Z` is clean. -/
theorem xor_cleanEmb_apply (f : Cfg (Sel0 ⊕ Sel1) → Cfg Za)
    (ψ : Reg ((Sel0 ⊕ Sel1) ⊕ (Fin a ⊕ S)) R)
    (y : Cfg (NB (Sel0 ⊕ Sel1) (Fin a ⊕ S) (Za ⊕ Z))) :
    (permOp (xorF f) (cleanEmb (X := Za ⊕ Z) ψ)) y =
      if (fun t => y (Sum.inr (Sum.inl t))) = f (selP y) ∧
          (fun z => y (Sum.inr (Sum.inr z))) = (fun _ => false) then
        ψ (fun b => y (Sum.inl b)) else 0 := by
  rw [permOp_apply, xorF_symm, cleanEmb_apply]
  have hsel : (fun b => xorF (PR := Fin a ⊕ S) (Z := Z) f y (Sum.inl b)) =
      fun b => y (Sum.inl b) := by
    funext b
    rcases b with s | p <;> rfl
  have hcond : ((fun x => xorF (PR := Fin a ⊕ S) (Z := Z) f y (Sum.inr x)) = fun _ => false) ↔
      ((fun t => y (Sum.inr (Sum.inl t))) = f (selP y) ∧
        (fun z => y (Sum.inr (Sum.inr z))) = (fun _ => false)) := by
    constructor
    · intro h
      refine ⟨?_, ?_⟩
      · funext t
        have := congrFun h (Sum.inl t)
        change (y (Sum.inr (Sum.inl t)) ^^ f (selP y) t) = false at this
        rw [xor_false_iff] at this
        exact this
      · funext z
        exact congrFun h (Sum.inr z)
    · rintro ⟨h1, h2⟩
      funext x
      rcases x with t | z
      · change (y (Sum.inr (Sum.inl t)) ^^ f (selP y) t) = false
        rw [xor_false_iff]
        exact congrFun h1 t
      · exact congrFun h2 z
  rw [hsel]
  by_cases h : (fun t => y (Sum.inr (Sum.inl t))) = f (selP y) ∧
      (fun z => y (Sum.inr (Sum.inr z))) = (fun _ => false)
  · rw [if_pos (hcond.2 h), if_pos h]
  · rw [if_neg (fun h' => h (hcond.1 h')), if_neg h]

/-- The vector of the selected private register of `ndA` that carries the word `f σ` on the
wires `Za`. -/
def JV (f : Cfg (Sel0 ⊕ Sel1) → Cfg Za) (ψ : Reg ((Sel0 ⊕ Sel1) ⊕ (Fin a ⊕ S)) R) :
    Reg ((Sel0 ⊕ (Sel1 ⊕ Za)) ⊕ (Fin a ⊕ S)) R :=
  WithLp.toLp 2 (fun c =>
    if (fun t => c (Sum.inl (Sum.inr (Sum.inr t)))) =
        f (Sum.elim (fun s => c (Sum.inl (Sum.inl s))) (fun s => c (Sum.inl (Sum.inr (Sum.inl s)))))
    then ψ (Sum.elim (Sum.elim (fun s => c (Sum.inl (Sum.inl s)))
      (fun s => c (Sum.inl (Sum.inr (Sum.inl s))))) (fun p => c (Sum.inr p)))
    else 0)

omit [CompleteSpace R] in
/-- The slice of the computed clean vector along the reassociation is the clean embedding of
`JV f ψ`. -/
theorem slice_reW (f : Cfg (Sel0 ⊕ Sel1) → Cfg Za) (ψ : Reg ((Sel0 ⊕ Sel1) ⊕ (Fin a ⊕ S)) R)
    (y : Cfg (NB (Sel0 ⊕ Sel1) (Fin a ⊕ S) (Za ⊕ Z))) :
    slice (reW : NB (Sel0 ⊕ (Sel1 ⊕ Za)) (Fin a ⊕ S) Z ↪ _)
        (permOp (xorF f) (cleanEmb (X := Za ⊕ Z) ψ)) y = cleanEmb (X := Z) (JV f ψ) := by
  apply PiLp.ext
  intro b
  rw [slice_apply, xor_cleanEmb_apply, cleanEmb_apply]
  set E := (reE (Sel0 := Sel0) (Sel1 := Sel1) (Za := Za) (PR := Fin a ⊕ S) (Z := Z)) with hE
  have hov : overwrite (reW : NB (Sel0 ⊕ (Sel1 ⊕ Za)) (Fin a ⊕ S) Z ↪ _) y b =
      fun w => b (E.symm w) := by
    funext w
    obtain ⟨v, rfl⟩ := E.surjective w
    change overwrite (reW : NB (Sel0 ⊕ (Sel1 ⊕ Za)) (Fin a ⊕ S) Z ↪ _) y b (reW v) = _
    rw [overwrite_apply_ι reW.injective, Equiv.symm_apply_apply]
  rw [hov]
  have hZ : ((fun z => b (E.symm (Sum.inr (Sum.inr z)))) = fun _ => false) ↔
      ((fun x => b (Sum.inr x)) = fun _ => false) := Iff.rfl
  have hza : (fun t => b (E.symm (Sum.inr (Sum.inl t)))) =
      fun t => b (Sum.inl (Sum.inl (Sum.inr (Sum.inr t)))) := rfl
  have hsel : selP (PR := Fin a ⊕ S) (Za := Za) (Z := Z) (fun w => b (E.symm w)) =
      Sum.elim (fun s => b (Sum.inl (Sum.inl (Sum.inl s))))
        (fun s => b (Sum.inl (Sum.inl (Sum.inr (Sum.inl s))))) := by
    funext s
    rcases s with s | s <;> rfl
  have hspr : (fun c => b (E.symm (Sum.inl c))) =
      Sum.elim (Sum.elim (fun s => b (Sum.inl (Sum.inl (Sum.inl s))))
        (fun s => b (Sum.inl (Sum.inl (Sum.inr (Sum.inl s))))))
        (fun p => b (Sum.inl (Sum.inr p))) := by
    funext c
    rcases c with (s | s) | p <;> rfl
  rw [hza, hsel, hspr]
  simp only [JV]
  by_cases hz : (fun x => b (Sum.inr x)) = fun _ => false
  · rw [if_pos hz]
    have hz' : (fun z => b (E.symm (Sum.inr (Sum.inr z)))) = fun _ => false := hz
    by_cases hf : (fun t => b (Sum.inl (Sum.inl (Sum.inr (Sum.inr t))))) =
        f (Sum.elim (fun s => b (Sum.inl (Sum.inl (Sum.inl s))))
          (fun s => b (Sum.inl (Sum.inl (Sum.inr (Sum.inl s))))))
    · rw [if_pos ⟨hf, hz'⟩]
      change _ = (if _ then _ else _)
      rw [if_pos hf]
    · rw [if_neg (fun h => hf h.1)]
      change _ = (if _ then _ else _)
      rw [if_neg hf]
  · rw [if_neg hz]
    have hz' : ¬ (fun z => b (E.symm (Sum.inr (Sum.inr z)))) = fun _ => false := hz
    rw [if_neg (fun h => hz' h.2)]

/-- **Computed selection.** If `ndA` (selected by `Sel0 ⊕ (Sel1 ⊕ Za)`) has the native identity
for the family `DatA`, and the operation `nd` (selected by `Sel0 ⊕ Sel1`, with the wires `Za` as
scratch) first runs a circuit `APN` that writes `f σ` into `Za` on clean scratch and then the
compute circuit of `ndA` on the reassociated wires, with the same orientation wire and decoder,
then `nd` has the native identity for the family `σ ↦ DatA (σ, f σ)`. -/
theorem nativeOK_computed (prim : J → Reg Y R →L[ℂ] Reg Y R)
    (ndA : NativeOp (Sel0 ⊕ (Sel1 ⊕ Za)) (Fin a ⊕ S) Z Y J)
    (nd : NativeOp (Sel0 ⊕ Sel1) (Fin a ⊕ S) (Za ⊕ Z) Y J)
    (APN : List (NInstr (NB (Sel0 ⊕ Sel1) (Fin a ⊕ S) (Za ⊕ Z)) Y J))
    (hV : nd.V = APN ++ ndA.V.map (NInstr.map reW)) (ho : nd.o = ndA.o)
    (hdec : ∀ y, nd.dec y = ndA.dec (fun w => y (reW w)))
    (f : Cfg (Sel0 ⊕ Sel1) → Cfg Za)
    (hAPu : IsUnitary (nrun prim APN))
    (hAP : nrun prim APN ∘L cleanEmb (X := Za ⊕ Z) =
      permOp (xorF (PR := Fin a ⊕ S) (Z := Z) f) ∘L cleanEmb)
    (DatA : Cfg (Sel0 ⊕ (Sel1 ⊕ Za)) → (Reg (Fin a) (Reg S R) →L[ℂ] Reg (Fin a) (Reg S R)))
    (hOK : NativeOK prim ndA (selOp DatA)) :
    NativeOK prim nd (selOp (fun σ => DatA (Sum.elim (fun s => σ (Sum.inl s))
      (Sum.elim (fun s => σ (Sum.inr s)) (f σ))))) := by
  set Dat' : Cfg (Sel0 ⊕ Sel1) → (Reg (Fin a) (Reg S R) →L[ℂ] Reg (Fin a) (Reg S R)) :=
    fun σ => DatA (Sum.elim (fun s => σ (Sum.inl s)) (Sum.elim (fun s => σ (Sum.inr s)) (f σ)))
    with hDat'
  -- the decoded rotation and the compute circuit along the reassociation
  have hR : Rdec (R := R) nd = localOp reW reW.injective (fun _ => Rdec (R := R) ndA) := by
    rw [Rdec, Rdec, localOp_condOp, ho]
    congr 1
    funext z
    rw [hdec]
  have hM : nrun prim (ndA.V.map (NInstr.map reW)) =
      localOp reW reW.injective (fun _ => nrun prim ndA.V) := nrun_map prim reW ndA.V
  set K := (nrun prim ndA.V)† ∘L Rdec (R := R) ndA ∘L nrun prim ndA.V with hKdef
  have hK : (nrun prim (ndA.V.map (NInstr.map reW)))† ∘L Rdec (R := R) nd ∘L
      nrun prim (ndA.V.map (NInstr.map reW)) = localOp reW reW.injective (fun _ => K) := by
    rw [hM, hR, localOp_adjoint, localOp_comp, localOp_comp]
  -- the core identity
  have hcore : localOp reW reW.injective (fun _ => K) ∘L
      (permOp (xorF (PR := Fin a ⊕ S) (Z := Z) f) ∘L cleanEmb (X := Za ⊕ Z)) =
      (permOp (xorF (PR := Fin a ⊕ S) (Z := Z) f) ∘L cleanEmb (X := Za ⊕ Z)) ∘L selOp Dat' := by
    ext ψ y
    have hs : slice (reW : NB (Sel0 ⊕ (Sel1 ⊕ Za)) (Fin a ⊕ S) Z ↪ _)
        ((permOp (xorF (PR := Fin a ⊕ S) (Z := Z) f) ∘L cleanEmb (X := Za ⊕ Z)) ψ) y =
        cleanEmb (X := Z) (JV f ψ) := slice_reW f ψ y
    have hOKψ : K (cleanEmb (X := Z) (JV f ψ)) = cleanEmb (selOp DatA (JV f ψ)) := by
      have h := congrArg (fun T => T (JV f ψ)) hOK
      simp only [comp_apply] at h
      rw [hKdef]
      simp only [comp_apply]
      exact h
    change (localOp reW reW.injective (fun _ => K))
        ((permOp (xorF (PR := Fin a ⊕ S) (Z := Z) f) ∘L cleanEmb (X := Za ⊕ Z)) ψ) y =
      (permOp (xorF (PR := Fin a ⊕ S) (Z := Z) f) (cleanEmb (X := Za ⊕ Z) (selOp Dat' ψ))) y
    rw [localOp_apply, hs, hOKψ, xor_cleanEmb_apply, cleanEmb_apply]
    have hz : (fun x => y (reW (Sum.inr x))) = fun z => y (Sum.inr (Sum.inr z)) := rfl
    rw [hz]
    by_cases hZ : (fun z => y (Sum.inr (Sum.inr z))) = fun _ => false
    · rw [if_pos hZ]
      rw [selOp, selOp, localOp_apply, localOp_apply]
      have hc1 : (fun s => clearCfg (Sum.inr : Fin a ⊕ S → (Sel0 ⊕ (Sel1 ⊕ Za)) ⊕ (Fin a ⊕ S))
          (fun b => y (reW (Sum.inl b))) (Sum.inl s)) =
          Sum.elim (fun s => y (Sum.inl (Sum.inl (Sum.inl s))))
            (Sum.elim (fun s => y (Sum.inl (Sum.inl (Sum.inr s))))
              (fun t => y (Sum.inr (Sum.inl t)))) := by
        funext s
        refine (overwrite_apply_out _ _ _ _ (fun p h => by cases h)).trans ?_
        rcases s with s | s | t <;> rfl
      have hslA : slice (Sum.inr : Fin a ⊕ S → (Sel0 ⊕ (Sel1 ⊕ Za)) ⊕ (Fin a ⊕ S)) (JV f ψ)
          (fun b => y (reW (Sum.inl b))) =
          if (fun t => y (Sum.inr (Sum.inl t))) = f (selP y) then
            slice (Sum.inr : Fin a ⊕ S → (Sel0 ⊕ Sel1) ⊕ (Fin a ⊕ S)) ψ (fun b => y (Sum.inl b))
          else 0 := by
        apply PiLp.ext
        intro p
        rw [slice_apply]
        simp only [JV]
        have hsel : Sum.elim (fun s => overwrite (Sum.inr : Fin a ⊕ S → _)
            (fun b => y (reW (Sum.inl b))) p (Sum.inl (Sum.inl s)))
            (fun s => overwrite (Sum.inr : Fin a ⊕ S → _)
              (fun b => y (reW (Sum.inl b))) p (Sum.inl (Sum.inr (Sum.inl s)))) = selP y := by
          funext s
          rcases s with s | s
          · exact overwrite_apply_out _ _ _ _ (fun r h => by cases h)
          · exact overwrite_apply_out _ _ _ _ (fun r h => by cases h)
        have hza : (fun t => overwrite (Sum.inr : Fin a ⊕ S → _)
            (fun b => y (reW (Sum.inl b))) p (Sum.inl (Sum.inr (Sum.inr t)))) =
            fun t => y (Sum.inr (Sum.inl t)) := by
          funext t
          exact overwrite_apply_out _ _ _ _ (fun r h => by cases h)
        have hpr : (fun q => overwrite (Sum.inr : Fin a ⊕ S → _)
            (fun b => y (reW (Sum.inl b))) p (Sum.inr q)) = p :=
          funext (fun q => overwrite_apply_ι Sum.inr_injective _ p q)
        change (if (fun t => overwrite (Sum.inr : Fin a ⊕ S → _)
            (fun b => y (reW (Sum.inl b))) p (Sum.inl (Sum.inr (Sum.inr t)))) =
            f (Sum.elim (fun s => overwrite (Sum.inr : Fin a ⊕ S → _)
              (fun b => y (reW (Sum.inl b))) p (Sum.inl (Sum.inl s)))
              (fun s => overwrite (Sum.inr : Fin a ⊕ S → _)
                (fun b => y (reW (Sum.inl b))) p (Sum.inl (Sum.inr (Sum.inl s)))))
          then ψ (Sum.elim (Sum.elim (fun s => overwrite (Sum.inr : Fin a ⊕ S → _)
              (fun b => y (reW (Sum.inl b))) p (Sum.inl (Sum.inl s)))
            (fun s => overwrite (Sum.inr : Fin a ⊕ S → _)
              (fun b => y (reW (Sum.inl b))) p (Sum.inl (Sum.inr (Sum.inl s)))))
            (fun q => overwrite (Sum.inr : Fin a ⊕ S → _)
              (fun b => y (reW (Sum.inl b))) p (Sum.inr q)))
          else 0) = _
        rw [hsel, hza, hpr]
        split_ifs with hf
        · rw [slice_apply]
          have hov : overwrite (Sum.inr : Fin a ⊕ S → (Sel0 ⊕ Sel1) ⊕ (Fin a ⊕ S))
              (fun b => y (Sum.inl b)) p = Sum.elim (selP y) p := by
            funext v
            rcases v with s | q
            · exact overwrite_apply_out _ _ _ _ (fun r h => by cases h)
            · exact overwrite_apply_ι Sum.inr_injective _ p q
          rw [hov]
        · rfl
      rw [hc1, hslA]
      by_cases hF : (fun t => y (Sum.inr (Sum.inl t))) = f (selP y)
      · rw [if_pos hF, if_pos ⟨hF, hZ⟩]
        have hc2 : (fun s => clearCfg (Sum.inr : Fin a ⊕ S → (Sel0 ⊕ Sel1) ⊕ (Fin a ⊕ S))
            (fun b => y (Sum.inl b)) (Sum.inl s)) = selP y := by
          funext s
          exact overwrite_apply_out _ _ _ _ (fun p h => by cases h)
        have hsel3 : (Sum.elim (fun s => y (Sum.inl (Sum.inl (Sum.inl s))))
            (Sum.elim (fun s => y (Sum.inl (Sum.inl (Sum.inr s))))
              (fun t => y (Sum.inr (Sum.inl t)))) : Cfg (Sel0 ⊕ (Sel1 ⊕ Za))) =
            Sum.elim (fun s => selP y (Sum.inl s)) (Sum.elim (fun s => selP y (Sum.inr s))
              (f (selP y))) := by
          funext s
          rcases s with s | s | t
          · rfl
          · rfl
          · exact congrFun hF t
        rw [hc2, hDat']
        beta_reduce
        rw [hsel3]
        rfl
      · rw [if_neg hF, if_neg (fun h => hF h.1), map_zero]
        rfl
    · rw [if_neg hZ, if_neg (fun h => hZ h.2)]
  -- assembling
  unfold NativeOK at hOK ⊢
  have hAA : (nrun prim APN)† ∘L nrun prim APN = 1 := by
    have h := hAPu.1
    rwa [star_eq_adjoint, mul_def] at h
  rw [hV, nrun_append, adjoint_comp]
  calc (nrun prim APN)† ∘L (nrun prim (ndA.V.map (NInstr.map reW)))† ∘L Rdec nd ∘L
        (nrun prim (ndA.V.map (NInstr.map reW)) ∘L nrun prim APN) ∘L cleanEmb
      = (nrun prim APN)† ∘L ((nrun prim (ndA.V.map (NInstr.map reW)))† ∘L Rdec nd ∘L
          nrun prim (ndA.V.map (NInstr.map reW))) ∘L (nrun prim APN ∘L cleanEmb) := by
        simp only [comp_assoc]
    _ = (nrun prim APN)† ∘L localOp reW reW.injective (fun _ => K) ∘L
          (permOp (xorF (PR := Fin a ⊕ S) (Z := Z) f) ∘L cleanEmb (X := Za ⊕ Z)) := by
        rw [hK, hAP]
    _ = (nrun prim APN)† ∘L ((permOp (xorF (PR := Fin a ⊕ S) (Z := Z) f) ∘L
          cleanEmb (X := Za ⊕ Z)) ∘L selOp Dat') := by
        rw [hcore]
    _ = (nrun prim APN)† ∘L ((nrun prim APN ∘L cleanEmb (X := Za ⊕ Z)) ∘L selOp Dat') := by
        rw [hAP]
    _ = cleanEmb ∘L selOp Dat' := by
        rw [← comp_assoc, ← comp_assoc, hAA]
        rfl

/-- **A classical circuit writing `f σ` into `Za`**: if a classical gate list maps every clean
configuration to the configuration with `f σ` on the wires `Za`, its run satisfies the
hypotheses of `nativeOK_computed`. -/
theorem classical_hAP (prim : J → Reg Y R →L[ℂ] Reg Y R)
    (gs : List (Gate (NB (Sel0 ⊕ Sel1) (Fin a ⊕ S) (Za ⊕ Z)))) (hcl : Classical gs)
    (f : Cfg (Sel0 ⊕ Sel1) → Cfg Za)
    (hrun : ∀ c : Cfg ((Sel0 ⊕ Sel1) ⊕ (Fin a ⊕ S)),
      cfgRun gs (Sum.elim c (fun _ => false)) =
        xorF (PR := Fin a ⊕ S) (Z := Z) f (Sum.elim c (fun _ => false))) :
    IsUnitary (nrun prim (nGatesOf gs)) ∧
      nrun prim (nGatesOf gs) ∘L cleanEmb (X := Za ⊕ Z) =
        permOp (xorF (PR := Fin a ⊕ S) (Z := Z) f) ∘L cleanEmb := by
  refine ⟨?_, ?_⟩
  · rw [nrun_nGatesOf]
    exact gRun_isUnitary gs (classical_allUnitary hcl)
  · apply ext_bas_clm'
    intro c q
    rw [comp_apply, comp_apply, cleanEmb_bas, nrun_nGatesOf, gRun_classical_bas _ hcl,
      permOp_bas, hrun]

end Computed

end

end SparseHamiltonian.GateBinarySelect
