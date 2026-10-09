import GateEfficientNative.Native.Lift

/-!
# Slot-selected native operations from per-slot ones

A native private operation without selection wires (`NativeOp Empty PR Z Y J`) is extended to
selection wires `Sel` (time slots): every elementary gate of the compute circuit is placed on the
same wires of the larger register (`baseW`), and every primitive call additionally reads the
selection wires (`posExt`). A family of primitive oracles indexed by the selection word,
`primAt w`, becomes one selection-controlled family `slotPrim primAt = Σ_w |w⟩⟨w| ⊗ primAt w`.

* `nrun_slot`: the extended compute circuit acts, at selection word `w`, as the original circuit
  with the primitives `primAt w`.
* `Rdec_slot`: the decoded rotation is the original one on the base wires.
* `nativeOK_slot`: if the native identity holds for every word `w` (with the private operation
  `Dat w`), then it holds for the selected family `selOp Dat`.
* `nGatesN_slot`, `nCallsN_slot`, `valid_slot`, `slot_public`, `slotPrim_isUnitary`: counts,
  validity and the public conditions are unchanged.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateBinary

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit SparseHamiltonian.GateNative
open SparseHamiltonian.GateODE (adjIf localOp_localOp' overwrite_apply_ι overwrite_apply_out
  update_comp_injective)
open scoped InnerProduct

/-! ### Wires of the selected register -/

section Wires

variable {Sel PR Z : Type*}

theorem baseW_injective :
    Function.Injective (Sum.map (Sum.map (Empty.elim : Empty → Sel) id) id :
      NB Empty PR Z → NB Sel PR Z) := by
  refine Sum.map_injective.2 ⟨Sum.map_injective.2 ⟨fun a => a.elim, Function.injective_id⟩,
    Function.injective_id⟩

/-- The wires of the native register without selection wires inside the selected register. -/
def baseW : NB Empty PR Z ↪ NB Sel PR Z :=
  ⟨Sum.map (Sum.map Empty.elim id) id, baseW_injective⟩

/-- The selection wires of the selected register. -/
def selW : Sel ↪ NB Sel PR Z :=
  ⟨fun s => Sum.inl (Sum.inl s), fun _ _ h => by simpa using h⟩

theorem selW_ne_baseW (s : Sel) (w : NB Empty PR Z) :
    (selW s : NB Sel PR Z) ≠ baseW w := by
  rcases w with (e | p) | z
  · exact e.elim
  · simp [selW, baseW]
  · simp [selW, baseW]

/-- The selection word of a configuration. -/
def slotOf (c : Cfg (NB Sel PR Z)) : Cfg Sel := fun s => c (selW s)

/-- The base part of a configuration. -/
def baseOf (c : Cfg (NB Sel PR Z)) : Cfg (NB Empty PR Z) := fun w => c (baseW w)

/-- The positions of an extended call: the selection wires and the original positions. -/
def posExt {Y : Type*} (pos : Y ↪ NB Empty PR Z) : Sel ⊕ Y ↪ NB Sel PR Z :=
  ⟨Sum.elim selW (fun y => baseW (pos y)),
    selW.injective.sumElim (baseW.injective.comp pos.injective)
      (fun s y => selW_ne_baseW s (pos y))⟩

/-- **The extended instruction**: gates on the same wires, calls that also read the selection
wires. -/
def slotInstr {Y J : Type*} : NInstr (NB Empty PR Z) Y J → NInstr (NB Sel PR Z) (Sel ⊕ Y) J
  | .gate g => .gate (GateODE.Gate.map baseW g)
  | .call j adj pos => .call j adj (posExt pos)

end Wires

/-! ### Generic register identities -/

section Generic

variable {A W : Type*} [Fintype A] [DecidableEq A] [Fintype W] [DecidableEq W]
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

theorem adjIf_localOp {ι : A → W} (hι : Function.Injective ι)
    (F : Cfg W → (Reg A R →L[ℂ] Reg A R)) (adj : Bool) :
    adjIf adj (localOp ι hι F) = localOp ι hι (fun c => adjIf adj (F c)) := by
  cases adj
  · rfl
  · simp only [adjIf, if_true]
    exact localOp_adjoint hι F

/-- A one-qubit operation on exposed wires is the one-qubit operation on the renamed wire. -/
theorem localOp_condOp (e : A ↪ W) (t : A) (u : Cfg A → Matrix Bool Bool ℂ) :
    localOp e e.injective (fun _ => condOp (Q := R) t u) =
      condOp (e t) (fun z => u (fun a => z (e a))) := by
  unfold condOp
  rw [localOp_localOp' e.injective (single_injective t) (fun _ => e t) (single_injective _)
    (fun _ => rfl) (fun _ c => matOp (qubitMat (u c)))]
  apply localOp_congr
  intro z
  simp only [clearCfg_single, update_comp_injective e.injective, Function.update_idem]

end Generic

/-! ### Selection-controlled primitives and the extended run -/

section Run

variable {Sel PR Z Y J : Type*} [Fintype Sel] [DecidableEq Sel] [Fintype PR] [DecidableEq PR]
  [Fintype Z] [DecidableEq Z] [Fintype Y] [DecidableEq Y]
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- **The selection-controlled primitives** `Σ_w |w⟩⟨w| ⊗ primAt w j`. -/
def slotPrim (primAt : Cfg Sel → J → Reg Y R →L[ℂ] Reg Y R) (j : J) :
    Reg (Sel ⊕ Y) R →L[ℂ] Reg (Sel ⊕ Y) R :=
  localOp Sum.inr Sum.inr_injective (fun c => primAt (fun s => c (Sum.inl s)) j)

theorem slotPrim_isUnitary (primAt : Cfg Sel → J → Reg Y R →L[ℂ] Reg Y R)
    (h : ∀ w j, IsUnitary (primAt w j)) (j : J) : IsUnitary (slotPrim primAt j) :=
  localOp_isUnitary _ _ (fun _ => h _ j)

omit [Fintype Sel] in
theorem slotOf_clearCfg_baseW (z : Cfg (NB Sel PR Z)) :
    slotOf (clearCfg (baseW : NB Empty PR Z ↪ NB Sel PR Z) z) = slotOf z := by
  funext s
  change overwrite (baseW : NB Empty PR Z ↪ NB Sel PR Z) z (fun _ => false) (selW s) = z (selW s)
  exact overwrite_apply_out _ z _ _ (fun w h => selW_ne_baseW s w h.symm)

/-- One extended instruction acts, at selection word `w`, as the original instruction with the
primitives `primAt w`. -/
theorem eval_slotInstr (primAt : Cfg Sel → J → Reg Y R →L[ℂ] Reg Y R)
    (i : NInstr (NB Empty PR Z) Y J) :
    (slotInstr (Sel := Sel) i).eval (slotPrim primAt) =
      localOp baseW baseW.injective (fun c => i.eval (primAt (slotOf c))) := by
  cases i with
  | gate g => exact (GateODE.Gate.map_op baseW.injective g).symm
  | call j adj pos =>
      change localOp (posExt pos) (posExt pos).injective
          (fun _ => adjIf adj (slotPrim primAt j)) =
        localOp baseW baseW.injective
          (fun c => localOp pos pos.injective (fun _ => adjIf adj (primAt (slotOf c) j)))
      rw [slotPrim, adjIf_localOp,
        localOp_localOp' (posExt pos).injective Sum.inr_injective (fun y => baseW (pos y))
          (baseW.injective.comp pos.injective) (fun _ => rfl)
          (fun _ c => adjIf adj (primAt (fun s => c (Sum.inl s)) j)),
        localOp_localOp' baseW.injective pos.injective (fun y => baseW (pos y))
          (baseW.injective.comp pos.injective) (fun _ => rfl)
          (fun c _ => adjIf adj (primAt (slotOf c) j))]
      congr 1
      funext z
      rw [slotOf_clearCfg_baseW]
      have hz : (fun s => clearCfg (Sum.inr : Y → Sel ⊕ Y) (fun a => z (posExt pos a))
          (Sum.inl s)) = slotOf z := by
        funext s
        change overwrite (Sum.inr : Y → Sel ⊕ Y) (fun a => z (posExt pos a)) (fun _ => false)
          (Sum.inl s) = z (selW s)
        rw [overwrite_apply_out _ _ _ _ (fun y h => by cases h)]
        rfl
      rw [hz]

/-- **The extended compute circuit** acts, at selection word `w`, as the original circuit with
the primitives `primAt w`. -/
theorem nrun_slot (primAt : Cfg Sel → J → Reg Y R →L[ℂ] Reg Y R)
    (V : List (NInstr (NB Empty PR Z) Y J)) :
    nrun (slotPrim primAt) (V.map (slotInstr (Sel := Sel))) =
      localOp baseW baseW.injective (fun c => nrun (primAt (slotOf c)) V) := by
  induction V with
  | nil => exact (localOp_one _).symm
  | cons i V ih =>
      rw [List.map_cons, nrun_cons, ih, eval_slotInstr, localOp_comp]
      rfl

omit [Fintype Y] [DecidableEq Y] in
/-- **The decoded rotation** of the extended operation is the original one on the base wires. -/
theorem Rdec_slot {Y' : Type*} (nd : NativeOp Empty PR Z Y J) (nd' : NativeOp Sel PR Z Y' J)
    (ho : nd'.o = nd.o) (hdec : ∀ x, nd'.dec x = nd.dec (baseOf x)) :
    Rdec (R := R) nd' = localOp baseW baseW.injective (fun _ => Rdec (R := R) nd) := by
  rw [Rdec, Rdec, localOp_condOp, ho]
  congr 1
  funext x
  rw [hdec]
  rfl

end Run

/-! ### The native identity -/

section OK

variable {Sel Z Y J : Type*} [Fintype Sel] [DecidableEq Sel] [Fintype Z] [DecidableEq Z]
  [Fintype Y] [DecidableEq Y] {S : Type*} [Fintype S] [DecidableEq S] {a : ℕ}
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- The column of a register vector of the selected private register at the selection word
`w`, as a vector of the private register without selection wires. -/
def selSlice (ψ : Reg (Sel ⊕ (Fin a ⊕ S)) R) (w : Cfg Sel) : Reg (Empty ⊕ (Fin a ⊕ S)) R :=
  WithLp.toLp 2 (fun c0 => ψ (Sum.elim w (fun p => c0 (Sum.inr p))))

omit [Fintype Sel] [DecidableEq Sel] [Fintype S] [DecidableEq S] [NormedAddCommGroup R]
  [InnerProductSpace ℂ R] [CompleteSpace R] in
theorem selSlice_apply (ψ : Reg (Sel ⊕ (Fin a ⊕ S)) R) (w : Cfg Sel)
    (c0 : Cfg (Empty ⊕ (Fin a ⊕ S))) :
    selSlice ψ w c0 = ψ (Sum.elim w (fun p => c0 (Sum.inr p))) := rfl

omit [Fintype Sel] [CompleteSpace R] in
theorem slice_cleanEmb (ψ : Reg (Sel ⊕ (Fin a ⊕ S)) R) (y : Cfg (NB Sel (Fin a ⊕ S) Z)) :
    slice (baseW : NB Empty (Fin a ⊕ S) Z ↪ NB Sel (Fin a ⊕ S) Z) (cleanEmb (X := Z) ψ) y =
      cleanEmb (X := Z) (selSlice ψ (slotOf y)) := by
  apply PiLp.ext
  intro b
  rw [slice_apply, cleanEmb_apply, cleanEmb_apply]
  have hz : (fun z => overwrite (baseW : NB Empty (Fin a ⊕ S) Z ↪ NB Sel (Fin a ⊕ S) Z) y b
      (Sum.inr z)) = fun z => b (Sum.inr z) := by
    funext z
    exact overwrite_apply_ι baseW.injective y b (Sum.inr z)
  rw [hz]
  split_ifs with h
  · have hc : (fun v => overwrite (baseW : NB Empty (Fin a ⊕ S) Z ↪ NB Sel (Fin a ⊕ S) Z) y b
        (Sum.inl v)) = Sum.elim (slotOf y) (fun p => b (Sum.inl (Sum.inr p))) := by
      funext v
      rcases v with s | p
      · exact overwrite_apply_out _ y b _ (fun w hw => selW_ne_baseW s w hw.symm)
      · exact overwrite_apply_ι baseW.injective y b (Sum.inl (Sum.inr p))
    rw [hc]
    rfl
  · rfl

/-- **The native identity at every selection word gives the native identity of the selected
family.** -/
theorem nativeOK_slot (primAt : Cfg Sel → J → Reg Y R →L[ℂ] Reg Y R)
    (nd : NativeOp Empty (Fin a ⊕ S) Z Y J) (nd' : NativeOp Sel (Fin a ⊕ S) Z (Sel ⊕ Y) J)
    (hV : nd'.V = nd.V.map slotInstr) (ho : nd'.o = nd.o)
    (hdec : ∀ x, nd'.dec x = nd.dec (baseOf x))
    (Dat : Cfg Sel → (Reg (Fin a) (Reg S R) →L[ℂ] Reg (Fin a) (Reg S R)))
    (hOK : ∀ w, NativeOK (primAt w) nd (selOp (fun _ : Cfg Empty => Dat w))) :
    NativeOK (slotPrim primAt) nd' (selOp Dat) := by
  unfold NativeOK at hOK ⊢
  rw [hV, nrun_slot, Rdec_slot nd nd' ho hdec, localOp_adjoint, ← comp_assoc, ← comp_assoc,
    localOp_comp, localOp_comp]
  ext ψ y
  rw [comp_apply, localOp_apply, slotOf_clearCfg_baseW, slice_cleanEmb]
  have h := congrArg (fun T => T (selSlice ψ (slotOf y)) (baseOf y)) (hOK (slotOf y))
  simp only [comp_apply] at h
  refine h.trans ?_
  rw [comp_apply, cleanEmb_apply, cleanEmb_apply]
  have hzz : (fun x => baseOf y (Sum.inr x)) = (fun x => y (Sum.inr x)) := rfl
  rw [hzz]
  split_ifs with hz
  · rw [selOp, selOp, localOp_apply, localOp_apply]
    have hw : (fun s => clearCfg (Sum.inr : Fin a ⊕ S → Sel ⊕ (Fin a ⊕ S))
        (fun b => y (Sum.inl b)) (Sum.inl s)) = slotOf y := by
      funext s
      exact overwrite_apply_out _ _ _ _ (fun p h => by cases h)
    rw [hw]
    have hs : slice (Sum.inr : Fin a ⊕ S → Empty ⊕ (Fin a ⊕ S)) (selSlice ψ (slotOf y))
        (fun b => baseOf y (Sum.inl b)) =
        slice (Sum.inr : Fin a ⊕ S → Sel ⊕ (Fin a ⊕ S)) ψ (fun b => y (Sum.inl b)) := by
      apply PiLp.ext
      intro p
      rw [slice_apply, slice_apply, selSlice_apply]
      have e1 : (fun q => overwrite (Sum.inr : Fin a ⊕ S → Empty ⊕ (Fin a ⊕ S))
          (fun b => baseOf y (Sum.inl b)) p (Sum.inr q)) = p :=
        funext (fun q => overwrite_apply_ι Sum.inr_injective _ p q)
      have e2 : overwrite (Sum.inr : Fin a ⊕ S → Sel ⊕ (Fin a ⊕ S)) (fun b => y (Sum.inl b)) p =
          Sum.elim (slotOf y) p := by
        funext v
        rcases v with s | q
        · exact overwrite_apply_out _ _ _ _ (fun r h => by cases h)
        · exact overwrite_apply_ι Sum.inr_injective _ p q
      rw [e1, e2]
    rw [hs]
    rfl
  · rfl

end OK

/-! ### Counts, validity and public data -/

section Counts

variable {Sel PR Z Y J : Type*}

theorem nGatesN_slot (V : List (NInstr (NB Empty PR Z) Y J)) :
    nGatesN (V.map (slotInstr (Sel := Sel))) = nGatesN V := by
  unfold nGatesN
  rw [List.countP_map]
  congr 1
  funext i
  cases i <;> rfl

theorem nCallsN_slot (p : J → Bool) (V : List (NInstr (NB Empty PR Z) Y J)) :
    nCallsN p (V.map (slotInstr (Sel := Sel))) = nCallsN p V := by
  unfold nCallsN
  rw [List.countP_map]
  congr 1
  funext i
  cases i <;> rfl

theorem valid_slot (V : List (NInstr (NB Empty PR Z) Y J)) (h : ∀ i ∈ V, i.Valid) :
    ∀ i ∈ V.map (slotInstr (Sel := Sel)), i.Valid := by
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
      exact h2 c' hc' (baseW.injective e)
  | call j adj pos => trivial

variable [DecidableEq Sel] [DecidableEq PR] [DecidableEq Z]

/-- The extended operation is public when the original one is. -/
theorem slot_public (nd : NativeOp Empty PR Z Y J) (hnd : nd.Public)
    (nd' : NativeOp Sel PR Z (Sel ⊕ Y) J) (hV : nd'.V = nd.V.map slotInstr)
    (ho : nd'.o = nd.o) (hdec : ∀ x, nd'.dec x = nd.dec (baseOf x)) : nd'.Public where
  valid := by
    rw [hV]
    exact valid_slot nd.V hnd.valid
  dec_indep x v := by
    rw [hdec, hdec, ho]
    have hb : baseOf (Function.update x (Sum.inl (Sum.inr nd.o)) v) =
        Function.update (baseOf x) (Sum.inl (Sum.inr nd.o)) v :=
      update_comp_injective (baseW : NB Empty PR Z ↪ NB Sel PR Z).injective x
        (Sum.inl (Sum.inr nd.o)) v
    rw [hb, hnd.dec_indep]

end Counts

end

end SparseHamiltonian.GateBinary
