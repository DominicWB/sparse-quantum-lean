import GateEfficientNative.Hamiltonian.Macro

/-!
# Errors of the native macros

`hmacro_approx`: every native macro implements its released instruction
(with `U_J` from its gates and the selected private operation) exactly on
clean work wires, except a private call, which is within `4ζ`.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateNative

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit GateCircuit.Sim
open GateODE (localOp_localOp localOp_localOp' localOp_gateOp overwrite_apply_ι overwrite_apply_out)
open scoped InnerProduct BigOperators

variable {V S X' Z Sel Y J : Type*} [Fintype V] [DecidableEq V] [Fintype S] [DecidableEq S]
  [Fintype X'] [DecidableEq X'] [Fintype Z] [DecidableEq Z] [Fintype Sel] [DecidableEq Sel]
  [Fintype Y] [DecidableEq Y] {a : ℕ}
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
variable {bT bP A : ℕ}

/-! ### Clean work wires on the native register -/

omit [Fintype V] [Fintype S] [Fintype X'] [Fintype Z] in
theorem cleanX_update_inl (x : Cfg (HW V S X' Z bT bP A)) (w : V ⊕ S) (b : Bool)
    (h : CleanX x) : CleanX (Function.update x (Sum.inl w) b) := by
  intro v
  rw [Function.update_of_ne (by simp)]
  exact h v

/-! ### The controlled gates of `U_J` -/

omit [Fintype V] [Fintype S] [Fintype X'] [Fintype Z] [DecidableEq Z] [DecidableEq X']
  [DecidableEq V] [DecidableEq S] in
theorem ujGates_ok (ρ : RelW V a) (gs : List (Gate (Fin a ⊕ S)))
    (hgs : ∀ g ∈ gs, GateOK 3 g) :
    ∀ g ∈ ujGates (X' := X') (Z := Z) (bT := bT) (bP := bP) (A := A) ρ gs, GateOK 3 g := by
  intro g hg
  simp only [ujGates, List.mem_flatMap] at hg
  obtain ⟨g', hg', hg⟩ := hg
  have hok := valid_map_list (Y := Empty) (J := Empty)
    (pEmb (S := S) (X' := X') (Z := Z) (bT := bT) (bP := bP) (A := A) ρ)
    [NInstr.gate g'] (fun i hi => by simp at hi; subst hi; exact hgs g' hg')
    (NInstr.gate (GateODE.Gate.map (pEmb ρ) g')) (by simp [NInstr.map])
  refine ctrlGate_ok (secW ρ) flagList _ hok flagList_nodup ?_ ?_ ?_ ?_ g hg
  · simp only [secW, GateODE.Gate.map, pEmb, Function.Embedding.coeFn_mk, mapId, ne_eq]
    rcases g'.t with i | s
    · simp only [Sum.map_inl, Sum.inl.injEq]
      exact (ρ.anc_ne_sec i).symm
    · simp
  · intro f hf
    simp only [flagList, flagW, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl <;> simp [GateODE.Gate.map, pEmb]
  · intro f hf
    simp only [flagList, flagW, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl <;> simp [secW]
  · intro c hc f hf
    simp only [GateODE.Gate.map, List.mem_map] at hc
    obtain ⟨c', _, rfl⟩ := hc
    simp only [flagList, flagW, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl <;> simp [pEmb]

omit [Fintype V] [DecidableEq V] [Fintype S] [Fintype X'] [DecidableEq X'] [Fintype Z]
  [DecidableEq Z] [DecidableEq S] in
theorem ujGates_length (ρ : RelW V a) (gs : List (Gate (Fin a ⊕ S)))
    (hgs : ∀ g ∈ gs, GateOK 3 g) :
    (ujGates (X' := X') (Z := Z) (bT := bT) (bP := bP) (A := A) ρ gs).length ≤
      7 * gs.length := by
  induction gs with
  | nil => simp [ujGates]
  | cons g gs ih =>
      simp only [ujGates, List.flatMap_cons, List.length_append, List.length_cons] at ih ⊢
      have h1 := ctrlGate_length (V := HW V S X' Z bT bP A) (secW ρ) flagList
        (GateODE.Gate.map (pEmb ρ) g)
        (by simpa [GateODE.Gate.map] using (hgs g List.mem_cons_self).1) (by simp [flagList])
      have h2 := ih (fun g' hg' => hgs g' (List.mem_cons_of_mem g hg'))
      omega

omit [Fintype Sel] [DecidableEq Sel] [Fintype Y] [DecidableEq Y] [Fintype V] [DecidableEq V]
  [Fintype S] [DecidableEq S] [Fintype X'] [DecidableEq X'] [Fintype Z] [DecidableEq Z] in
theorem pEmb_ne_secW (ρ : RelW V a) (p : Fin a ⊕ S) :
    (Sum.inl (mapId (S := S) ρ.anc p) : HW V S X' Z bT bP A) ≠ secW ρ := by
  rcases p with i | s
  · simp only [mapId, Sum.map_inl, secW, ne_eq, Sum.inl.injEq]
    exact ρ.anc_ne_sec i
  · simp [mapId, secW]

/-- The controlled gates of `U_J` agree with the enabled gate list on clean
work wires. -/
theorem ujGates_agrees (ρ : RelW V a) (gs : List (Gate (Fin a ⊕ S)))
    (hgs : ∀ g ∈ gs, GateOK 3 g) :
    Agrees (CleanX (B := V ⊕ S) (X := XW Z bT bP A ⊕ X'))
      (gRun (Q := R) (ujGates ρ gs))
      (gRun (gs.map (ctrlMap (secW ρ) (fun p => (Sum.inl (mapId (S := S) ρ.anc p) :
        HW V S X' Z bT bP A))))) := by
  induction gs with
  | nil => exact Agrees.refl _ _
  | cons g gs ih =>
      have hg := hgs g List.mem_cons_self
      simp only [ujGates, List.flatMap_cons, List.map_cons, gRun_append, gRun_cons] at ih ⊢
      have hct : ∀ c ∈ (GateODE.Gate.map (pEmb (S := S) (X' := X') (Z := Z) (bT := bT) (bP := bP)
          (A := A) ρ) g).cs,
          c.1 ≠ (GateODE.Gate.map (pEmb (S := S) (X' := X') (Z := Z) (bT := bT) (bP := bP)
            (A := A) ρ) g).t := by
        intro c hc
        simp only [GateODE.Gate.map, List.mem_map] at hc
        obtain ⟨c', hc', rfl⟩ := hc
        intro h
        exact hg.2.1 c' hc' ((pEmb ρ).injective h)
      have h1 := ctrlGate_agrees (Q := R) (secW ρ) flagList
        (GateODE.Gate.map (pEmb (S := S) (X' := X') (Z := Z) (bT := bT) (bP := bP) (A := A) ρ) g)
        (by simpa [GateODE.Gate.map] using hg.1) (by simp [flagList]) flagList_nodup
        (pEmb_ne_secW ρ g.t).symm hct
        (by intro f hf
            simp only [flagList, flagW, List.mem_cons, List.not_mem_nil, or_false] at hf
            rcases hf with rfl | rfl | rfl <;> simp [GateODE.Gate.map, pEmb])
        (by intro f hf
            simp only [flagList, flagW, List.mem_cons, List.not_mem_nil, or_false] at hf
            rcases hf with rfl | rfl | rfl <;> simp [secW])
        (by intro c hc f hf
            simp only [GateODE.Gate.map, List.mem_map] at hc
            obtain ⟨c', _, rfl⟩ := hc
            simp only [flagList, flagW, List.mem_cons, List.not_mem_nil, or_false] at hf
            rcases hf with rfl | rfl | rfl <;> simp [pEmb])
        CleanX
        (by intro x hx f hf
            simp only [flagList, flagW, List.mem_cons, List.not_mem_nil, or_false] at hf
            rcases hf with rfl | rfl | rfl <;> exact hx _)
        (fun x b hx => cleanX_update_inl x _ b hx)
      have hpres : Preserves (CleanX (B := V ⊕ S) (X := XW Z bT bP A ⊕ X'))
          ((ctrlMap (secW ρ) (fun p => (Sum.inl (mapId (S := S) ρ.anc p) :
            HW V S X' Z bT bP A)) g).op (Q := R)) := by
        unfold Gate.op gateOp
        exact preserves_condOp _ _ _ (fun x b hx => cleanX_update_inl x _ b hx)
      have ih' := ih (fun g' hg' => hgs g' (List.mem_cons_of_mem g hg'))
      exact h1.comp hpres ih'

/-! ### One instruction -/

/-- **Every native macro implements its released instruction.** -/
theorem hmacro_approx (prim : J → Reg Y R →L[ℂ] Reg Y R) (hprim : ∀ j, IsUnitary (prim j))
    (ρ : RelW V a) (sw : SelWires ρ Sel) (UJg : List (Gate (Fin a ⊕ S)))
    (hUJ : ∀ g ∈ UJg, GateOK 3 g)
    (nd : NativeOp Sel (Fin a ⊕ S) Z Y J) (hnd : nd.Public) (ar : Arith (NB Sel (Fin a ⊕ S) Z))
    {ζ : ℝ} (hζ : 0 ≤ ζ) (har : ArithOK ar (Sum.inl (Sum.inr nd.o)) nd.dec ζ)
    (Dfam : Bool → Cfg Sel → (Reg (Fin a) (Reg S R) →L[ℂ] Reg (Fin a) (Reg S R)))
    (hDu : ∀ w, IsUnitary (Dfam false w)) (hDadj : ∀ w, Dfam true w = (Dfam false w)†)
    (hN : NativeOK prim nd (selOp (Dfam false))) (i : Instr V) :
    ApproxOn CleanX (nrun prim (hmacro (X' := X') ρ sw UJg nd ar i))
      (liftB (conj (evalSel ρ UJg sw Dfam i))) (if i.isPriv then 4 * ζ else 0) := by
  cases i with
  | gate g =>
      apply ApproxOn.of_agrees
      have e1 : nrun prim (hmacro (X' := X') ρ sw UJg nd ar (Instr.gate g)) =
          gateOp ((g.cs.map (fun c => (Sum.inl c.1, c.2))).map (fun c => (Sum.inl c.1, c.2)))
            (Sum.inl (Sum.inl g.t)) g.u := by
        simp only [hmacro, nrun_singleton, NInstr.eval_gate, GateODE.Gate.map, List.map_map]
        rfl
      have e2 : liftB (X := XW Z ar.bT ar.bP ar.A ⊕ X') (conj (evalSel (R := R) ρ UJg sw Dfam
          (Instr.gate g))) = gateOp ((g.cs.map (fun c => (Sum.inl c.1, c.2))).map
            (fun c => (Sum.inl c.1, c.2))) (Sum.inl (Sum.inl g.t)) g.u := by
        simp only [evalSel]
        rw [conj_gateOp]
        exact localOp_gateOp Sum.inl_injective _ _ _
      rw [e1, e2]
      exact Agrees.refl _ _
  | uj cs adj =>
      apply ApproxOn.of_agrees
      set gs := if adj then gInv UJg else UJg with hgs
      have hgsok : ∀ g ∈ gs, GateOK 3 g := by
        rw [hgs]; split_ifs
        · exact gInv_ok _ hUJ
        · exact hUJ
      have hconj : conj (if adj then (UJop (R := R) UJg)† else UJop UJg) = gRun gs := by
        rw [hgs]
        split_ifs
        · rw [UJop_adjoint, conj_unfl_fl]
        · exact conj_unfl_fl _
      have e2 : liftB (X := XW Z ar.bT ar.bP ar.A ⊕ X') (conj (evalSel (R := R) ρ UJg sw Dfam
          (Instr.uj cs adj))) =
          gRun (gs.map (ctrlMap (secW ρ) (fun p => (Sum.inl (mapId (S := S) ρ.anc p) :
            HW V S X' Z ar.bT ar.bP ar.A)))) := by
        simp only [evalSel]
        rw [liftB_conj_selOracle_canon]
        simp only [hconj]
        exact localOp_ctrl_gRun _ (secW ρ) (fun p => pEmb_ne_secW ρ p) gs
          (fun g hg => (hgsok g hg).2.1)
      have e1 : nrun prim (hmacro (X' := X') ρ sw UJg nd ar (Instr.uj cs adj)) =
          gRun (ujGates ρ gs) := by
        simp only [hmacro]
        rw [nrun_nGatesOf]
      rw [e1, e2]
      exact ujGates_agrees ρ gs hgsok
  | priv cs adj =>
      simp only [Instr.isPriv, if_true]
      have hlift := liftB_conj_selOracle (R := R) (X' := X') (Z := Z) (bT := ar.bT)
        (bP := ar.bP) (A := ar.A) ρ sw (Dfam adj)
      have e1 : nrun prim (hmacro (X' := X') ρ sw UJg nd ar (Instr.priv cs adj)) =
          localOp (ePW ρ sw) (ePW ρ sw).injective
            (fun _ => nrun prim (if adj then ninv (privMacro nd ar) else privMacro nd ar)) := by
        simp only [hmacro]
        exact nrun_map prim (ePW ρ sw) _
      simp only [evalSel]
      rw [e1, hlift]
      apply approxOn_localOp _ _ _ (by linarith) (SA := CleanP)
        (fun y hy => ⟨fun z => hy (Sum.inl (Sum.inl z)),
          fun w => hy (Sum.inl (Sum.inr (Sum.inl w)))⟩)
      intro _
      cases adj
      · exact privMacro_approx prim hprim nd hnd ar hζ har _ hN
      · have hDsel : IsUnitary (selOp (Dfam false)) := selOp_isUnitary _ hDu
        have h := privMacro_inv_approx prim hprim nd hnd ar hζ har _ hDsel hN
        have hadj : (selOp (Dfam false))† = selOp (Dfam true) := by
          rw [selOp_adjoint]
          exact congrArg selOp (funext fun w => (hDadj w).symm)
        rw [hadj] at h
        exact h

end

end SparseHamiltonian.GateNative
