import GateOptimalPrecision.NativeCayley
import GateOptimalPrecision.NativeFactor

/-!
# The native signed-factor circuit

The expanded signed-factor circuit of Proposition `gate:prop:signed` (`sgCircuit`) calls the
boundary `U_J` under the sector wire and the factor `U_B` unconditionally ("On an inactive branch
the unconditional factor and inverse cancel"; `UncOK`). Its native circuit (`fcirc`) keeps the
elementary gates, replaces every boundary call by the gates of `U_J` with the sector wire as an
extra control (as in the baseline theorem), and every factor call by the native factor
(`factorMacro`) or its literal inverse, placed on the ancilla and system wires; no factor call is
controlled.

* `fcirc_error`: for every valid released circuit `l` of this form whose full output is within
  `ε₀` of a target `U` (run with `U_J = UJop UJg` and the factor `U_B`), the native circuit is
  within `ε₀ + 3ξ nPriv l` of `U` on the system embedding, when the factor arithmetic has accuracy
  `ξ` (`FactorArithOK`) and `W† U(c) W = U_B` on clean scratch (`FactorNativeOK`);
* `fcirc_nCalls`: exactly `2 nPriv l` copies of the primitive calls of the compute circuit `W`;
  `fcirc_nGates`: at most `nGates l + 7 C_J nUJ l + (2|W| + 2|circ| + 2 b_P + b_T + 4) nPriv l`
  elementary gates, where `circ` is the factor arithmetic;
* `uncOK_sgCircuit`: the signed-factor circuits are of this form;
* `UJop_shiftG`: the gates of `U_J` on the last `a` of `a + 1` ancilla wires implement
  `U_J ⊗ I_flag` (`liftA`);
* `signed_transfer`: the transfer for released circuits on `a + 1` ancillas with the boundary
  `U_J ⊗ I_flag` and the factor `U_B ⊗ I_flag` (`factorNativeOf`);
* `signed_native_simulation`: **Proposition `gate:prop:signed` with native factors** (`sgNative`).
-/
set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace GateOptimalPrecision

noncomputable section

open ContinuousLinearMap SparseHamiltonian SparseHamiltonian.OracleCircuit
  SparseHamiltonian.GateCircuit SparseHamiltonian.GateCircuit.Sim SparseHamiltonian.GateNative
open GateODE (localOp_localOp localOp_localOp' localOp_gateOp overwrite_apply_ι overwrite_apply_out)
open Complex (I)
open SignedFactorSimulation (rb)
open scoped InnerProduct InnerProductSpace BigOperators ComplexOrder

/-- The oracle calls of the expanded signed circuit: sector-controlled boundary calls and
unconditional factor calls. -/
def UncOK {V : Type*} {a : ℕ} (ρ : RelW V a) : Instr V → Prop
  | .gate _ => True
  | .uj cs _ => cs = [(ρ.sec, true)]
  | .priv cs _ => cs = []

/-! ### The macros -/

section Macro

variable {V S X' Z Y J : Type*} {a bT bP A : ℕ}

/-- The native macro of an instruction of the expanded circuit. -/
def fmacro (ρ : RelW V a) (UJg : List (Gate (Fin a ⊕ S)))
    (fo : FactorOp (Fin a ⊕ S) Z Y J bT bP A) :
    Instr V → List (NInstr (HW V S X' Z bT bP A) Y J)
  | .gate g => [NInstr.gate (GateODE.Gate.map wEmb g)]
  | .uj _ adj => nGatesOf (ujGates ρ (if adj then gInv UJg else UJg))
  | .priv _ adj => (if adj then ninv (factorMacro fo) else factorMacro fo).map
      (NInstr.map (ePW ρ (noSel ρ)))

/-- **The native signed-factor circuit**: every instruction replaced by its macro. -/
def fcirc (ρ : RelW V a) (UJg : List (Gate (Fin a ⊕ S)))
    (fo : FactorOp (Fin a ⊕ S) Z Y J bT bP A) (l : List (Instr V)) :
    List (NInstr (HW V S X' Z bT bP A) Y J) :=
  l.flatMap (fmacro ρ UJg fo)

theorem fmacro_nCalls (p : J → Bool) (ρ : RelW V a) (UJg : List (Gate (Fin a ⊕ S)))
    (fo : FactorOp (Fin a ⊕ S) Z Y J bT bP A) (i : Instr V) :
    nCallsN p (fmacro (X' := X') ρ UJg fo i) = if i.isPriv then 2 * nCallsN p fo.W else 0 := by
  cases i with
  | gate g => rfl
  | uj cs adj =>
      simp only [fmacro, nCallsN_nGatesOf, Instr.isPriv]
      rfl
  | priv cs adj =>
      simp only [fmacro, nCallsN_map, Instr.isPriv, if_true]
      split_ifs
      · rw [nCallsN_ninv, factorMacro_nCalls]
      · rw [factorMacro_nCalls]

theorem fcirc_nCalls (p : J → Bool) (ρ : RelW V a) (UJg : List (Gate (Fin a ⊕ S)))
    (fo : FactorOp (Fin a ⊕ S) Z Y J bT bP A) (l : List (Instr V)) :
    nCallsN p (fcirc (X' := X') ρ UJg fo l) = nPriv l * (2 * nCallsN p fo.W) := by
  rw [fcirc, nCallsN_flatMap]
  exact sum_priv_nat l _ _ (fun i _ => fmacro_nCalls p ρ UJg fo i)

theorem fmacro_nGates (ρ : RelW V a) (UJg : List (Gate (Fin a ⊕ S)))
    (hUJ : ∀ g ∈ UJg, GateOK 3 g) (fo : FactorOp (Fin a ⊕ S) Z Y J bT bP A) (i : Instr V) :
    nGatesN (fmacro (X' := X') ρ UJg fo i) ≤ (if i.isGate then 1 else 0) +
      (if i.isUJ then 7 * UJg.length else 0) +
      (if i.isPriv then 2 * nGatesN fo.W + 2 * fo.circ.length + (2 * bP + bT + 4) else 0) := by
  cases i with
  | gate g =>
      simp only [fmacro, Instr.isGate, Instr.isUJ, Instr.isPriv, if_true, Bool.false_eq_true,
        if_false, add_zero]
      rfl
  | uj cs adj =>
      simp only [fmacro, nGatesN_nGatesOf, Instr.isGate, Instr.isUJ, Instr.isPriv, if_true,
        Bool.false_eq_true, if_false, add_zero, zero_add]
      have hok : ∀ g ∈ (if adj then gInv UJg else UJg), GateOK 3 g := by
        split_ifs
        · exact gInv_ok _ hUJ
        · exact hUJ
      have hlen : (if adj then gInv UJg else UJg).length = UJg.length := by
        split_ifs
        · exact gInv_length UJg
        · rfl
      have h := ujGates_length (X' := X') (Z := Z) (bT := bT) (bP := bP) (A := A) ρ _ hok
      rw [hlen] at h
      exact h
  | priv cs adj =>
      simp only [fmacro, nGatesN_map, Instr.isGate, Instr.isUJ, Instr.isPriv, if_true,
        Bool.false_eq_true, if_false, zero_add]
      split_ifs
      · rw [nGatesN_ninv, factorMacro_nGates]
      · rw [factorMacro_nGates]

theorem fcirc_nGates (ρ : RelW V a) (UJg : List (Gate (Fin a ⊕ S)))
    (hUJ : ∀ g ∈ UJg, GateOK 3 g) (fo : FactorOp (Fin a ⊕ S) Z Y J bT bP A)
    (l : List (Instr V)) :
    nGatesN (fcirc (X' := X') ρ UJg fo l) ≤ nGates l * 1 + nUJ l * (7 * UJg.length) +
      nPriv l * (2 * nGatesN fo.W + 2 * fo.circ.length + (2 * bP + bT + 4)) := by
  rw [fcirc, nGatesN_flatMap]
  exact sum_le_counts l _ _ _ _ (fun i _ => fmacro_nGates ρ UJg hUJ fo i)

variable [Fintype V] [DecidableEq V] [Fintype S] [DecidableEq S] [Fintype X'] [DecidableEq X']
  [Fintype Z] [DecidableEq Z]

omit [Fintype V] [Fintype S] [Fintype X'] [DecidableEq X'] [Fintype Z] [DecidableEq V]
  [DecidableEq S] [DecidableEq Z] in
theorem fmacro_valid (ρ : RelW V a) (UJg : List (Gate (Fin a ⊕ S)))
    (hUJ : ∀ g ∈ UJg, GateOK 3 g) (fo : FactorOp (Fin a ⊕ S) Z Y J bT bP A)
    (hW : ∀ i ∈ fo.W, i.Valid) (helem : ∀ g ∈ fo.circ, g.cs.length ≤ 3) (hcl : Classical fo.circ)
    (i : Instr V) (hv : i.Valid ρ.anc) : ∀ j ∈ fmacro (X' := X') ρ UJg fo i, j.Valid := by
  cases i with
  | gate g =>
      intro j hj
      simp only [fmacro, List.mem_singleton] at hj
      subst hj
      exact NInstr.valid_map wEmb (NInstr.gate g) hv
  | uj cs adj =>
      simp only [fmacro]
      apply valid_nGatesOf
      apply ujGates_ok
      split_ifs
      · exact gInv_ok _ hUJ
      · exact hUJ
  | priv cs adj =>
      simp only [fmacro]
      apply valid_map_list
      split_ifs
      · exact valid_ninv _ (factorMacro_valid fo hW helem hcl)
      · exact factorMacro_valid fo hW helem hcl

omit [Fintype V] [Fintype S] [Fintype X'] [DecidableEq X'] [Fintype Z] [DecidableEq V]
  [DecidableEq S] [DecidableEq Z] in
theorem fcirc_valid (ρ : RelW V a) (UJg : List (Gate (Fin a ⊕ S)))
    (hUJ : ∀ g ∈ UJg, GateOK 3 g) (fo : FactorOp (Fin a ⊕ S) Z Y J bT bP A)
    (hW : ∀ i ∈ fo.W, i.Valid) (helem : ∀ g ∈ fo.circ, g.cs.length ≤ 3) (hcl : Classical fo.circ)
    (l : List (Instr V)) (hv : ∀ i ∈ l, i.Valid ρ.anc) :
    ∀ j ∈ fcirc (X' := X') ρ UJg fo l, j.Valid := by
  intro j hj
  simp only [fcirc, List.mem_flatMap] at hj
  obtain ⟨i, hi, hj⟩ := hj
  exact fmacro_valid ρ UJg hUJ fo hW helem hcl i (hv i hi) j hj

end Macro

/-! ### The released semantics -/

section Sem

variable {V S X' Z : Type*} [Fintype V] [DecidableEq V] [Fintype S] [DecidableEq S]
  [Fintype X'] [DecidableEq X'] [Fintype Z] [DecidableEq Z] {a bT bP A : ℕ}
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- The released semantics with `U_J` from its gates and an unconditional factor `U`. -/
def evalF (ρ : RelW V a) (UJg : List (Gate (Fin a ⊕ S)))
    (U : Reg (Fin a) (Reg S R) →L[ℂ] Reg (Fin a) (Reg S R)) :
    Instr V → Reg V (Reg S R) →L[ℂ] Reg V (Reg S R)
  | .gate g => gateOp g.cs g.t g.u
  | .uj _ adj => selOracle ρ (noSel ρ) (fun _ => if adj then (UJop UJg)† else UJop UJg)
  | .priv _ adj => localOp ρ.anc ρ.anc_inj (fun _ => if adj then U† else U)

omit [Fintype X'] [DecidableEq X'] [Fintype Z] [DecidableEq Z] in
theorem evalF_isUnitary (ρ : RelW V a) (UJg : List (Gate (Fin a ⊕ S)))
    (hUJ : ∀ g ∈ UJg, GateOK 3 g) (U : Reg (Fin a) (Reg S R) →L[ℂ] Reg (Fin a) (Reg S R))
    (hU : IsUnitary U) (i : Instr V) (hv : i.Valid ρ.anc) : IsUnitary (evalF ρ UJg U i) := by
  cases i with
  | gate g =>
      simp only [evalF]
      exact gateOp_isUnitary g.cs g.t g.u hv.2.2
  | uj cs adj =>
      simp only [evalF]
      refine selOracle_isUnitary ρ (noSel ρ) _ (fun _ => ?_)
      split_ifs
      · simpa [star_eq_adjoint] using (UJop_isUnitary (R := R) UJg hUJ).adjoint
      · exact UJop_isUnitary UJg hUJ
  | priv cs adj =>
      simp only [evalF]
      refine localOp_isUnitary _ _ (fun _ => ?_)
      split_ifs
      · simpa [star_eq_adjoint] using hU.adjoint
      · exact hU

variable {m r K : ℕ}

omit [Fintype X'] [DecidableEq X'] [Fintype Z] [DecidableEq Z] [Fintype V] [DecidableEq V] in
theorem evalF_wire (UJg : List (Gate (Fin a ⊕ S))) (U : Anc a (Reg S R) →L[ℂ] Anc a (Reg S R))
    (i : Instr (Wire a m r K)) (hi : UncOK (wireRel a m r K) i) :
    evalF (wireRel a m r K) UJg U i = i.eval (simSem (P := Reg S R) (UJop (R := R) UJg) U) := by
  cases i with
  | gate g => rfl
  | uj cs adj =>
      simp only [UncOK] at hi
      subst hi
      simp only [evalF, selOracle, Instr.eval, oracleOp, simSem]
      apply localOp_congr
      intro x
      simp only [wireRel_sec, ctrlOK_sec]
      rfl
  | priv cs adj =>
      simp only [UncOK] at hi
      subst hi
      simp only [evalF, Instr.eval, oracleOp, simSem, ctrlOK_nil, if_true]
      rfl

omit [Fintype X'] [DecidableEq X'] [Fintype Z] [DecidableEq Z] [Fintype V] [DecidableEq V] in
theorem prodOps_evalF (UJg : List (Gate (Fin a ⊕ S)))
    (U : Anc a (Reg S R) →L[ℂ] Anc a (Reg S R)) (l : List (Instr (Wire a m r K)))
    (hl : ∀ i ∈ l, UncOK (wireRel a m r K) i) :
    prodOps (V := Wire a m r K) (R := Reg S R) (evalF (wireRel a m r K) UJg U) l =
      run (simSem (P := Reg S R) (UJop (R := R) UJg) U) l := by
  induction l with
  | nil => rfl
  | cons i l ih =>
      rw [prodOps, run_cons, ih (fun j hj => hl j (List.mem_cons_of_mem i hj)),
        evalF_wire UJg U i (hl i List.mem_cons_self)]

end Sem

/-! ### The lifted unconditional factor call -/

section Approx

variable {V S X' Z Y J : Type*} [Fintype V] [DecidableEq V] [Fintype S] [DecidableEq S]
  [Fintype X'] [DecidableEq X'] [Fintype Z] [DecidableEq Z] [Fintype Y] [DecidableEq Y]
  {a bT bP A : ℕ}
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

omit [Fintype Y] [DecidableEq Y] in
/-- **The lifted unconditional factor call is the placed unconditional ideal.** -/
theorem liftB_conj_unc (ρ : RelW V a) (O : Reg (Fin a) (Reg S R) →L[ℂ] Reg (Fin a) (Reg S R)) :
    liftB (X := XW Z bT bP A ⊕ X') (conj (localOp ρ.anc ρ.anc_inj (fun _ => O) :
      Reg V (Reg S R) →L[ℂ] Reg V (Reg S R))) =
      localOp (ePW (S := S) (X' := X') (Z := Z) (bT := bT) (bP := bP) (A := A) ρ (noSel ρ))
        (ePW ρ (noSel ρ)).injective (fun _ => uncIdeal (selOp (fun _ : Cfg Empty => O))) := by
  have hL : liftB (X := XW Z bT bP A ⊕ X') (conj (localOp ρ.anc ρ.anc_inj (fun _ => O) :
      Reg V (Reg S R) →L[ℂ] Reg V (Reg S R))) =
      localOp (fun p => (Sum.inl (mapId (S := S) ρ.anc p) : HW V S X' Z bT bP A))
        (pEmb (S := S) (X' := X') (Z := Z) (bT := bT) (bP := bP) (A := A) ρ).injective
        (fun _ => conj O) := by
    unfold liftB
    rw [conj_localOp ρ.anc_inj]
    rw [localOp_localOp' Sum.inl_injective (mapId_injective (S := S) ρ.anc_inj)
      (fun p => (Sum.inl (mapId (S := S) ρ.anc p) : HW V S X' Z bT bP A))
      (pEmb (S := S) (X' := X') (Z := Z) (bT := bT) (bP := bP) (A := A) ρ).injective
      (fun _ => rfl)]
  have hR : localOp (ePW (S := S) (X' := X') (Z := Z) (bT := bT) (bP := bP) (A := A) ρ (noSel ρ))
      (ePW ρ (noSel ρ)).injective (fun _ => uncIdeal (selOp (fun _ : Cfg Empty => O))) =
      localOp (fun p => ePW (S := S) (X' := X') (Z := Z) (bT := bT) (bP := bP) (A := A) ρ (noSel ρ)
          (selPR (Sum.inr p)))
        (fun _ _ h => Sum.inr_injective (selPR.injective ((ePW ρ (noSel ρ)).injective h)))
        (fun _ => conj O) := by
    unfold uncIdeal selOp
    rw [localOp_localOp selPR.injective Sum.inr_injective (fun _ _ => conj O)]
    rw [localOp_localOp' (ePW ρ (noSel ρ)).injective (selPR.injective.comp Sum.inr_injective)
      (fun p => ePW (S := S) (X' := X') (Z := Z) (bT := bT) (bP := bP) (A := A) ρ (noSel ρ)
        (selPR (Sum.inr p)))
      (fun _ _ h => Sum.inr_injective (selPR.injective ((ePW ρ (noSel ρ)).injective h)))
      (fun _ => rfl)]
  rw [hL, hR]
  rfl

/-- **Every native macro implements its released instruction**: exactly, except a factor call,
which is within `3ξ`. -/
theorem fmacro_approx (prim : J → Reg Y R →L[ℂ] Reg Y R) (hprim : ∀ j, IsUnitary (prim j))
    (ρ : RelW V a) (UJg : List (Gate (Fin a ⊕ S))) (hUJ : ∀ g ∈ UJg, GateOK 3 g)
    (fo : FactorOp (Fin a ⊕ S) Z Y J bT bP A) (hpub : fo.Public)
    (U : Reg (Fin a) (Reg S R) →L[ℂ] Reg (Fin a) (Reg S R)) (hU : IsUnitary U) {ξ : ℝ}
    (hξ : 0 ≤ ξ) (har : FactorArithOK fo ξ)
    (hN : FactorNativeOK prim fo (selOp (fun _ : Cfg Empty => U))) (i : Instr V) :
    ApproxOn CleanX (nrun prim (fmacro (X' := X') ρ UJg fo i))
      (liftB (conj (evalF ρ UJg U i))) (if i.isPriv then 3 * ξ else 0) := by
  cases i with
  | gate g =>
      apply ApproxOn.of_agrees
      have e1 : nrun prim (fmacro (X' := X') ρ UJg fo (Instr.gate g)) =
          gateOp ((g.cs.map (fun c => (Sum.inl c.1, c.2))).map (fun c => (Sum.inl c.1, c.2)))
            (Sum.inl (Sum.inl g.t)) g.u := by
        simp only [fmacro, nrun_singleton, NInstr.eval_gate, GateODE.Gate.map, List.map_map]
        rfl
      have e2 : liftB (X := XW Z bT bP A ⊕ X') (conj (evalF (R := R) ρ UJg U (Instr.gate g))) =
          gateOp ((g.cs.map (fun c => (Sum.inl c.1, c.2))).map (fun c => (Sum.inl c.1, c.2)))
            (Sum.inl (Sum.inl g.t)) g.u := by
        simp only [evalF]
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
      have e2 : liftB (X := XW Z bT bP A ⊕ X') (conj (evalF (R := R) ρ UJg U (Instr.uj cs adj))) =
          gRun (gs.map (ctrlMap (secW ρ) (fun p => (Sum.inl (mapId (S := S) ρ.anc p) :
            HW V S X' Z bT bP A)))) := by
        simp only [evalF]
        rw [liftB_conj_selOracle_canon]
        simp only [hconj]
        exact localOp_ctrl_gRun _ (secW ρ) (fun p => pEmb_ne_secW ρ p) gs
          (fun g hg => (hgsok g hg).2.1)
      have e1 : nrun prim (fmacro (X' := X') ρ UJg fo (Instr.uj cs adj)) =
          gRun (ujGates ρ gs) := by
        simp only [fmacro]
        rw [nrun_nGatesOf]
      rw [e1, e2]
      exact ujGates_agrees ρ gs hgsok
  | priv cs adj =>
      simp only [Instr.isPriv, if_true]
      have e1 : nrun prim (fmacro (X' := X') ρ UJg fo (Instr.priv cs adj)) =
          localOp (ePW ρ (noSel ρ)) (ePW ρ (noSel ρ)).injective
            (fun _ => nrun prim (if adj then ninv (factorMacro fo) else factorMacro fo)) := by
        simp only [fmacro]
        exact nrun_map prim (ePW ρ (noSel ρ)) _
      simp only [evalF]
      rw [e1, liftB_conj_unc]
      apply approxOn_localOp _ _ _ (by linarith : (0 : ℝ) ≤ 3 * ξ) (SA := CleanP)
        (fun y hy => ⟨fun z => hy (Sum.inl (Sum.inl z)),
          fun w => hy (Sum.inl (Sum.inr (Sum.inl w)))⟩)
      intro _
      cases adj
      · exact factorMacro_approx prim hprim fo hpub hξ har _ hN
      · have h := factorMacro_inv_approx prim hprim fo hpub hξ har _
          (selOp_isUnitary _ (fun _ => hU)) hN
        have hadj : (selOp (fun _ : Cfg Empty => U))† = selOp (fun _ : Cfg Empty => U†) := by
          rw [selOp_adjoint]
        rw [hadj] at h
        exact h

/-- **The native signed-factor circuit approximates the lifted released circuit.** -/
theorem fcirc_approx (prim : J → Reg Y R →L[ℂ] Reg Y R) (hprim : ∀ j, IsUnitary (prim j))
    (ρ : RelW V a) (UJg : List (Gate (Fin a ⊕ S))) (hUJ : ∀ g ∈ UJg, GateOK 3 g)
    (fo : FactorOp (Fin a ⊕ S) Z Y J bT bP A) (hpub : fo.Public)
    (U : Reg (Fin a) (Reg S R) →L[ℂ] Reg (Fin a) (Reg S R)) (hU : IsUnitary U) {ξ : ℝ}
    (hξ : 0 ≤ ξ) (har : FactorArithOK fo ξ)
    (hN : FactorNativeOK prim fo (selOp (fun _ : Cfg Empty => U)))
    (l : List (Instr V)) (hv : ∀ i ∈ l, i.Valid ρ.anc) :
    ApproxOn CleanX (nrun prim (fcirc (X' := X') ρ UJg fo l))
      (liftB (conj (prodOps (evalF ρ UJg U) l))) ((nPriv l : ℝ) * (3 * ξ)) := by
  have h := approxOn_flatMap prim CleanX (fmacro (X' := X') ρ UJg fo)
    (fun i => liftB (X := XW Z bT bP A ⊕ X') (conj (evalF ρ UJg U i)))
    (fun i => if i.isPriv then 3 * ξ else 0) l
    (fun i _ => fmacro_approx prim hprim ρ UJg hUJ fo hpub U hU hξ har hN i)
    (fun i _ => preserves_liftB _)
    (fun i hi ψ => IsUnitary.norm_apply_le
      (liftB_isUnitary (conj_isUnitary (evalF_isUnitary ρ UJg hUJ U hU i (hv i hi)))) ψ)
    (fun i hi ψ => IsUnitary.norm_apply_le (nrun_isUnitary prim hprim _
      (fmacro_valid ρ UJg hUJ fo hpub.valid har.elem har.classical i (hv i hi))) ψ)
    (fun i _ => by split_ifs <;> linarith)
  rw [sum_priv_real, prodOps_liftB_conj] at h
  exact h

/-- **The full-output error of the native signed-factor circuit.** -/
theorem fcirc_error (prim : J → Reg Y R →L[ℂ] Reg Y R) (hprim : ∀ j, IsUnitary (prim j))
    (ρ : RelW V a) (UJg : List (Gate (Fin a ⊕ S))) (hUJ : ∀ g ∈ UJg, GateOK 3 g)
    (fo : FactorOp (Fin a ⊕ S) Z Y J bT bP A) (hpub : fo.Public)
    (U : Reg (Fin a) (Reg S R) →L[ℂ] Reg (Fin a) (Reg S R)) (hU : IsUnitary U) {ξ : ℝ}
    (hξ : 0 ≤ ξ) (har : FactorArithOK fo ξ)
    (hN : FactorNativeOK prim fo (selOp (fun _ : Cfg Empty => U)))
    (l : List (Instr V)) (hv : ∀ i ∈ l, i.Valid ρ.anc)
    (ι : Reg S R →L[ℂ] Reg V (Reg S R)) (hι : ∀ ψ, ‖ι ψ‖ = ‖ψ‖)
    (T : Reg S R →L[ℂ] Reg S R) (Orel : Reg V (Reg S R) →L[ℂ] Reg V (Reg S R))
    (hO : prodOps (V := V) (R := Reg S R) (evalF ρ UJg U) l = Orel) {ε₀ : ℝ}
    (hrel : ‖Orel ∘L ι - ι ∘L T‖ ≤ ε₀) :
    ‖nrun prim (fcirc (X' := X') ρ UJg fo l) ∘L sysEmb ι - sysEmb ι ∘L T‖ ≤
      ε₀ + (nPriv l : ℝ) * (3 * ξ) := by
  have hA := fcirc_approx (X' := X') prim hprim ρ UJg hUJ fo hpub U hU hξ har hN l hv
  rw [hO] at hA
  have hε₀ : 0 ≤ ε₀ := le_trans (norm_nonneg (Orel ∘L ι - ι ∘L T)) hrel
  have hδ : 0 ≤ (nPriv l : ℝ) * (3 * ξ) := by positivity
  apply ContinuousLinearMap.opNorm_le_bound _ (by linarith)
  intro ψ
  set C := nrun prim (fcirc (X' := X') ρ UJg fo l) with hC
  set φ : Reg (V ⊕ S) R := fl (ι ψ) with hφ
  have e1 : (C ∘L sysEmb ι - sysEmb ι ∘L T :
      Reg S R →L[ℂ] Reg (HW V S X' Z bT bP A) R) ψ =
      (C (cleanEmb φ) - liftB (X := XW Z bT bP A ⊕ X') (conj Orel) (cleanEmb φ)) +
        cleanEmb (fl ((Orel ∘L ι - ι ∘L T) ψ)) := by
    have h1 : liftB (X := XW Z bT bP A ⊕ X') (conj Orel) (cleanEmb φ) =
        cleanEmb (conj Orel φ) := by
      rw [← comp_apply, liftB_cleanEmb, comp_apply]
    rw [h1, hφ, conj_fl]
    simp only [sysEmb, sub_apply, comp_apply, map_sub]
    abel
  have hφn : ‖φ‖ = ‖ψ‖ := by rw [hφ, norm_fl, hι]
  rw [e1]
  calc ‖C (cleanEmb φ) - liftB (X := XW Z bT bP A ⊕ X') (conj Orel) (cleanEmb φ) +
        cleanEmb (fl ((Orel ∘L ι - ι ∘L T) ψ))‖
      ≤ ‖C (cleanEmb φ) - liftB (X := XW Z bT bP A ⊕ X') (conj Orel) (cleanEmb φ)‖ +
        ‖cleanEmb (X := XW Z bT bP A ⊕ X') (fl ((Orel ∘L ι - ι ∘L T) ψ))‖ :=
        norm_add_le _ _
    _ ≤ (nPriv l : ℝ) * (3 * ξ) * ‖ψ‖ + ε₀ * ‖ψ‖ := by
        gcongr
        · have := hA _ (supp_cleanEmb φ)
          rwa [norm_cleanEmb, hφn] at this
        · rw [norm_cleanEmb, norm_fl]
          exact ((Orel ∘L ι - ι ∘L T).le_opNorm ψ).trans
            (mul_le_mul_of_nonneg_right hrel (norm_nonneg _))
    _ = (ε₀ + (nPriv l : ℝ) * (3 * ξ)) * ‖ψ‖ := by ring

end Approx

/-! ### The signed-factor circuits are of this form -/

section Signed

theorem uncOK_inv {V : Type*} {a : ℕ} (ρ : RelW V a) (i : Instr V) (h : UncOK ρ i) :
    UncOK ρ i.inv := by
  cases i <;> exact h

theorem uncOK_invList {V : Type*} {a : ℕ} (ρ : RelW V a) (l : List (Instr V))
    (h : ∀ i ∈ l, UncOK ρ i) : ∀ i ∈ invList l, UncOK ρ i := by
  intro i hi
  simp only [invList, List.mem_reverse, List.mem_map] at hi
  obtain ⟨j, hj, rfl⟩ := hi
  exact uncOK_inv ρ j (h j hj)

theorem uncOK_expandI {a m r K : ℕ} (f z : Fin a) (q κ : ℝ) (j : Instr (Wire (a + 1) m r K)) :
    ∀ i ∈ expandI f z q κ j, UncOK (wireRel (a + 1) m r K) i := by
  intro i hi
  cases j with
  | gate g =>
      simp only [expandI, List.mem_singleton] at hi
      subst hi
      trivial
  | uj cs adj =>
      simp only [expandI, ujExpand] at hi
      cases adj <;>
        simp only [Bool.false_eq_true, if_false, if_true, List.mem_cons, List.not_mem_nil,
          or_false] at hi <;>
        rcases hi with rfl | rfl <;> trivial
  | priv cs adj =>
      simp only [expandI, privExpand, List.mem_cons, List.mem_append, ofGates, List.mem_map,
        List.not_mem_nil, or_false] at hi
      rcases hi with rfl | ⟨g, -, rfl⟩ | rfl <;> trivial

theorem uncOK_sigCircuit (a : ℕ) (f z : Fin a) (q : ℝ) (M : ℕ) (ε κ : ℝ) :
    ∀ i ∈ sigCircuit a f z q M ε κ, UncOK (wireRel _ _ _ _) i := by
  intro i hi
  simp only [sigCircuit, List.mem_flatMap] at hi
  obtain ⟨j, -, hi⟩ := hi
  exact uncOK_expandI f z q κ j i hi

/-- **The expanded signed-factor circuits call `U_J` under the sector wire and `U_B`
unconditionally.** -/
theorem uncOK_sgCircuit (a : ℕ) (f z : Fin a) (lam δ t ε : ℝ) :
    ∀ i ∈ sgCircuit a f z lam δ t ε, UncOK (wireRel _ _ _ _) i := by
  unfold sgCircuit
  split_ifs
  · intro i hi
    simp at hi
  · exact uncOK_sigCircuit a f z _ _ _ _
  · exact uncOK_invList _ _ (uncOK_sigCircuit a f z _ _ _ _)

end Signed

/-! ### The boundary gates on the last `a` ancilla wires -/

section Shift

variable {S : Type*} [Fintype S] [DecidableEq S]
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- The last `a` of `a + 1` ancilla wires, with the system wires. -/
def sucE (a : ℕ) (S : Type*) : (Fin a ⊕ S) ↪ (Fin (a + 1) ⊕ S) :=
  ⟨Sum.map Fin.succ id, Sum.map_injective.mpr ⟨Fin.succ_injective a, Function.injective_id⟩⟩

/-- The gates of `U_J` placed on the last `a` of `a + 1` ancilla wires (the attenuation flag is
the first). -/
def shiftG {a : ℕ} (UJg : List (Gate (Fin a ⊕ S))) : List (Gate (Fin (a + 1) ⊕ S)) :=
  UJg.map (GateODE.Gate.map (sucE a S))

omit [Fintype S] [DecidableEq S] in
theorem shiftG_length {a : ℕ} (UJg : List (Gate (Fin a ⊕ S))) :
    (shiftG UJg).length = UJg.length :=
  List.length_map _

omit [Fintype S] [DecidableEq S] in
theorem shiftG_ok {a : ℕ} {UJg : List (Gate (Fin a ⊕ S))} (hUJg : ∀ g ∈ UJg, GateOK 3 g) :
    ∀ g ∈ shiftG UJg, GateOK 3 g := by
  intro g hg
  simp only [shiftG, List.mem_map] at hg
  obtain ⟨g', hg', rfl⟩ := hg
  exact NInstr.valid_map (Y := Empty) (J := Empty) (sucE a S) (NInstr.gate g') (hUJg g' hg')

/-- **The shifted gates implement `U_J` on the last `a` ancilla wires.** -/
theorem UJop_shiftG {a : ℕ} (UJg : List (Gate (Fin a ⊕ S))) :
    UJop (R := R) (shiftG UJg) = liftA (P := Reg S R) (UJop (R := R) UJg) := by
  have h1 : conj (liftA (P := Reg S R) (UJop (R := R) UJg)) = gRun (Q := R) (shiftG UJg) := by
    unfold liftA
    rw [conj_localOp (Fin.succ_injective a)]
    unfold shiftG
    rw [gRun_map_gates]
    unfold UJop
    simp only [conj_unfl_fl]
    rfl
  calc UJop (R := R) (shiftG UJg) = unfl ∘L gRun (Q := R) (shiftG UJg) ∘L fl := rfl
    _ = unfl ∘L conj (liftA (P := Reg S R) (UJop (R := R) UJg)) ∘L fl := by rw [h1]
    _ = liftA (P := Reg S R) (UJop (R := R) UJg) := by
        unfold conj
        ext ψ
        simp

end Shift

/-! ### Proposition `gate:prop:signed` with native factors -/

section SignedNative

variable {S Z Y J : Type*} [Fintype S] [DecidableEq S] [Fintype Z] [DecidableEq Z] [Fintype Y]
  [DecidableEq Y] {bT bP A : ℕ}
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- The native circuit of a released circuit on `a + 1` ancilla wires with sector-controlled
boundary calls and unconditional factor calls: `U_J` from its gates `UJg` on the last `a`
ancilla wires, the factor from the native factor `fo`. -/
def factorNativeOf {a m r K : ℕ} (UJg : List (Gate (Fin a ⊕ S)))
    (fo : FactorOp (Fin (a + 1) ⊕ S) Z Y J bT bP A) (l : List (Instr (Wire (a + 1) m r K))) :
    List (NInstr (HW (Wire (a + 1) m r K) S Empty Z bT bP A) Y J) :=
  fcirc (wireRel _ _ _ _) (shiftG UJg) fo l

/-- **Native transfer for unconditional factor calls.** For every valid released circuit `l`
of the signed form (`UncOK`) whose full output, run with the boundary `U_J ⊗ I_flag` and the
factor `U_B ⊗ I_flag`, is within `ε₀` of a target `T`: if `UJg` implements `U_J`, and `fo`
implements `U_B ⊗ I_flag` natively (`FactorOp.Public`; `W† U(c) W = U_B ⊗ I_flag` on clean scratch,
`FactorNativeOK`) with factor arithmetic of accuracy `ξ` (`FactorArithOK`), then the native circuit
is valid and unitary, makes exactly `2 nPriv l` copies of the primitive calls of `W`, has at most
`nGates l + 7 |UJg| nUJ l + (2|W| + 2|circ| + 2 b_P + b_T + 4) nPriv l` elementary gates on
`|wires of l| + |S| + |Z| + b_T + b_P + A + 3` wires, and is within `ε₀ + 3ξ nPriv l` of `T` on
the system embedding. -/
theorem signed_transfer {a m r K : ℕ} (prim : J → Reg Y R →L[ℂ] Reg Y R)
    (hprim : ∀ j, IsUnitary (prim j))
    (UJg : List (Gate (Fin a ⊕ S))) (hUJg : ∀ g ∈ UJg, GateOK 3 g)
    (UJ U : Anc a (Reg S R) →L[ℂ] Anc a (Reg S R)) (hJ : UJop (R := R) UJg = UJ)
    (hU : IsUnitary U) (fo : FactorOp (Fin (a + 1) ⊕ S) Z Y J bT bP A) (hpub : fo.Public)
    {ξ : ℝ} (hξ : 0 ≤ ξ) (har : FactorArithOK fo ξ)
    (hN : FactorNativeOK prim fo (selOp (fun _ : Cfg Empty => liftA U)))
    (l : List (Instr (Wire (a + 1) m r K))) (hv : ∀ i ∈ l, i.Valid Wire.anc)
    (hunc : ∀ i ∈ l, UncOK (wireRel _ _ _ _) i) (T : Reg S R →L[ℂ] Reg S R) {ε₀ : ℝ}
    (hrel : ‖run (simSem (P := Reg S R) (liftA UJ) (liftA U)) l ∘L io - io ∘L T‖ ≤ ε₀) :
    (∀ i ∈ factorNativeOf UJg fo l, i.Valid) ∧
    (∀ p : J → Bool, nCallsN p (factorNativeOf UJg fo l) = nPriv l * (2 * nCallsN p fo.W)) ∧
    nGatesN (factorNativeOf UJg fo l) ≤ nGates l + nUJ l * (7 * UJg.length) +
      nPriv l * (2 * nGatesN fo.W + 2 * fo.circ.length + (2 * bP + bT + 4)) ∧
    Fintype.card (HW (Wire (a + 1) m r K) S Empty Z bT bP A) =
      Fintype.card (Wire (a + 1) m r K) + Fintype.card S + (Fintype.card Z + bT + bP + A + 3) ∧
    IsUnitary (nrun prim (factorNativeOf UJg fo l)) ∧
    ‖nrun prim (factorNativeOf UJg fo l) ∘L sysEmb (io (P := Reg S R)) -
        sysEmb (io (P := Reg S R)) ∘L T‖ ≤ ε₀ + (nPriv l : ℝ) * (3 * ξ) := by
  have hO : prodOps (V := Wire (a + 1) m r K) (R := Reg S R)
      (evalF (wireRel _ _ _ _) (shiftG UJg) (liftA U)) l =
      run (simSem (P := Reg S R) (liftA UJ) (liftA U)) l := by
    rw [prodOps_evalF _ _ _ hunc, UJop_shiftG, hJ]
  have hio : ∀ ψ : Reg S R,
      ‖(io (P := Reg S R) (a := a + 1) (m := m) (r := r) (K := K)) ψ‖ = ‖ψ‖ :=
    fun ψ => by rw [io_apply, norm_bas]
  have hvN := fcirc_valid (X' := Empty) (wireRel _ _ _ _) (shiftG UJg) (shiftG_ok hUJg) fo
    hpub.valid har.elem har.classical _ hv
  refine ⟨hvN, fun p => fcirc_nCalls p _ _ fo _, ?_, ?_, nrun_isUnitary prim hprim _ hvN, ?_⟩
  · have h := fcirc_nGates (X' := Empty) (wireRel _ _ _ _) (shiftG UJg) (shiftG_ok hUJg) fo l
    rw [mul_one, shiftG_length] at h
    exact h
  · rw [card_HW]
    simp only [Fintype.card_empty, add_zero]
  · exact fcirc_error (X' := Empty) prim hprim (wireRel _ _ _ _) (shiftG UJg) (shiftG_ok hUJg) fo
      hpub (liftA U) (liftA_isUnitary hU) hξ har hN _ hv io hio _ _ hO hrel

/-- **The native signed-factor circuit** of Proposition `gate:prop:signed`: the expanded circuit
with every boundary call replaced by the gates of `U_J` under the sector wire and every factor call
by the native factor. -/
def sgNative {a : ℕ} (UJg : List (Gate (Fin a ⊕ S)))
    (fo : FactorOp (Fin (a + 1) ⊕ S) Z Y J bT bP A) (f z : Fin a) (lam δ t ε : ℝ) :
    List (NInstr (HW (SgWire a lam δ t ε) S Empty Z bT bP A) Y J) :=
  factorNativeOf UJg fo (sgCircuit a f z lam δ t ε)

/-- **Proposition `gate:prop:signed` with native factors.** Let `U_J` be given by elementary gates
`UJg` and let the factor `U_B ⊗ I_flag` be implemented natively by `fo`: compute `W`, the
arithmetic, the local factor gates of `U(c)`, the inverse arithmetic, uncompute `W†`
(`factorMacro`), with the native identity `W† U(c) W = U_B ⊗ I_flag` on clean scratch
(`FactorNativeOK`) and the factor arithmetic of accuracy `ξ` (`FactorArithOK`) as hypotheses. Then
the native signed-factor circuit is valid and unitary, makes exactly `2 nPriv` copies of the
primitive calls of `W` with `nPriv` bounded as in `signed_gate_simulation`, has at most
`64·3⁸ (N + 1)(a + m + r + 1) + nPriv (7 |UJg| + 2 |W| + 2 |circ| + 2 b_P + b_T + 4)` elementary
gates on `2a + 3m + 6r + 5 + |S| + |Z| + b_T + b_P + A + 3` wires, and its full output on the system
embedding is within `ε + 3ξ nPriv` of `exp(-itH)`. -/
theorem signed_native_simulation [FiniteDimensional ℂ R] {a : ℕ}
    (prim : J → Reg Y R →L[ℂ] Reg Y R) (hprim : ∀ j, IsUnitary (prim j))
    (UJg : List (Gate (Fin a ⊕ S))) (hUJg : ∀ g ∈ UJg, GateOK 3 g)
    (UJ U : Anc a (Reg S R) →L[ℂ] Anc a (Reg S R)) (hJ : UJop (R := R) UJg = UJ)
    (hUJ : IsUnitary UJ) (hU : IsUnitary U) (fo : FactorOp (Fin (a + 1) ⊕ S) Z Y J bT bP A)
    (hpub : fo.Public) {ξ : ℝ} (hξ : 0 ≤ ξ) (har : FactorArithOK fo ξ)
    (hN : FactorNativeOK prim fo (selOp (fun _ : Cfg Empty => liftA U)))
    {f z : Fin a} (hfz : f ≠ z) {lam δ : ℝ} (hlam : 0 < lam) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hD : (wKnown UJ (unitary_adj_comp hUJ) f z).Dop U ≤ (δ : ℂ) • (1 : Reg S R →L[ℂ] Reg S R))
    (t : ℝ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 64) :
    (∀ i ∈ sgNative UJg fo f z lam δ t ε, i.Valid) ∧
    (∀ p : J → Bool, nCallsN p (sgNative UJg fo f z lam δ t ε) =
      nPriv (sgCircuit a f z lam δ t ε) * (2 * nCallsN p fo.W)) ∧
    ((nPriv (sgCircuit a f z lam δ t ε) : ℝ) ≤ (if sgB lam δ t ≤ ε then 0 else
      4 * 10 ^ 10 * (Real.sqrt (sgT lam t * sgB lam δ t) +
        Real.sqrt (sgT lam t * rb (sgB lam δ t) ε) + rb (sgB lam δ t) ε))) ∧
    nGatesN (sgNative UJg fo f z lam δ t ε) ≤
      64 * 3 ^ 8 * ((sigN (sgQ lam δ t ε) (sgOrd lam δ t ε) + 1) *
        (a + sigM (sgQ lam δ t ε) (sgOrd lam δ t ε) ε + sigR (sgQ lam δ t ε) (sgOrd lam δ t ε) +
          1)) +
      nPriv (sgCircuit a f z lam δ t ε) * (7 * UJg.length +
        (2 * nGatesN fo.W + 2 * fo.circ.length + (2 * bP + bT + 4))) ∧
    Fintype.card (HW (SgWire a lam δ t ε) S Empty Z bT bP A) =
      2 * a + 3 * sigM (sgQ lam δ t ε) (sgOrd lam δ t ε) ε +
        6 * sigR (sgQ lam δ t ε) (sgOrd lam δ t ε) + 5 + Fintype.card S +
          (Fintype.card Z + bT + bP + A + 3) ∧
    IsUnitary (nrun prim (sgNative UJg fo f z lam δ t ε)) ∧
    ‖nrun prim (sgNative UJg fo f z lam δ t ε) ∘L sysEmb (io (P := Reg S R)) -
        sysEmb (io (P := Reg S R)) ∘L
          NormedSpace.exp ((-I * (t : ℂ)) • sgHam (P := Reg S R) UJ hUJ f z lam U)‖ ≤
      ε + (nPriv (sgCircuit a f z lam δ t ε) : ℝ) * (3 * ξ) := by
  obtain ⟨hv, hpriv, hJn, hgates, hcard, herr, -, -⟩ :=
    signed_gate_simulation (P := Reg S R) UJ U hUJ hU hfz hlam hδ hδ1 hD t hε hε1
  obtain ⟨hvN, hcalls, hgN, hcN, huN, herrN⟩ := signed_transfer prim hprim UJg hUJg UJ U hJ hU fo
    hpub hξ har hN _ hv (uncOK_sgCircuit a f z lam δ t ε) _ herr
  refine ⟨hvN, hcalls, hpriv, ?_, ?_, huN, herrN⟩
  · unfold sgNative
    rw [hJn] at hgN
    have e : nPriv (sgCircuit a f z lam δ t ε) * (7 * UJg.length + (2 * nGatesN fo.W +
        2 * fo.circ.length + (2 * bP + bT + 4))) = nPriv (sgCircuit a f z lam δ t ε) *
          (7 * UJg.length) + nPriv (sgCircuit a f z lam δ t ε) * (2 * nGatesN fo.W +
            2 * fo.circ.length + (2 * bP + bT + 4)) := by ring
    rw [e]
    omega
  · rw [hcN, hcard]

end SignedNative

end

end GateOptimalPrecision
