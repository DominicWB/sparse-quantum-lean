import GateEfficientSelective.Compiler

/-!
# Native Hamiltonian macros with a supplied controlled private circuit

The native circuits of Theorem `hs:thm:gates` (`GateNative.hcirc`) replace every released
instruction by a macro: an elementary gate by the same gate, a sector-controlled call of `U_J` by
the controlled gates of `U_J`, and a sector-controlled private Cayley call by the native
implementation `privMacro nd ar` of the enable-controlled private operation (or its literal
inverse), placed on the private wires by `ePW`.

Here the enable-controlled private operation is a **supplied circuit** `pc` on the same private
wires `PWr Sel (Fin a ⊕ S) Z bT bP A` (the enable wire, the selection wires, the private register
and the work wires `Z ⊕ AWr bT bP A`), for example a circuit over a finite gate set, with the
full-output guarantee of the manuscript: on every input whose work wires are clean, it is within
`ξ` of the ideal enable-controlled operation, which returns the work wires clean
(`ApproxOn CleanP (nrun prim pc) (ctrlIdeal Dsel) ξ`). The inverse calls use the literal
reverse-adjoint `ninv pc` of the same circuit (`ctrl_inv_approx`).

* `hmacroP`, `hcircP`: the macros and the circuit; `hcircP` with `pc = privMacro nd ar` is the
  released native circuit (`hcircP_privMacro`).
* `hcircP_valid`, `hcircP_nCalls`, `hcircP_nGates`: validity, the primitive calls
  (`nPriv · |pc|_calls`) and the elementary gates
  (`nGatesN (hcircP pc) = nGatesN (hcircP ∅) + nPriv · nGatesN pc`).
* `nSynN_hcircP_le`: if the gates of `pc` are gates of the adjoint-closed set `𝒢`, the
  synthesised gate occurrences of `hcircP pc` are at most the gates of `hcircP ∅`, which does not
  depend on `pc`.
* `hcircP_approx`, `hcircP_error`: the errors of the private calls add (`nPriv · ξ`), with the
  full-output clean-input convention of the released endpoints.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateSelective

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit GateCircuit.Sim GateNative GateSynth
open GateSynthTrials (AdjClosed)
open GateODE (localOp_gateOp overwrite_apply_out)
open scoped InnerProduct BigOperators

/-! ### The inverse of a supplied controlled circuit -/

section Inverse

variable {Sel PR Z Y J : Type*} [Fintype Sel] [DecidableEq Sel] [Fintype PR] [DecidableEq PR]
  [Fintype Z] [DecidableEq Z] [Fintype Y] [DecidableEq Y] {bT bP A : ℕ}
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

omit [Fintype Y] [DecidableEq Y] in
/-- The enable-controlled operation of a unitary is unitary. -/
theorem ctrlIdeal_isUnitary (Dsel : Reg (Sel ⊕ PR) R →L[ℂ] Reg (Sel ⊕ PR) R)
    (hD : IsUnitary Dsel) :
    IsUnitary (ctrlIdeal (Z := Z) (bT := bT) (bP := bP) (A := A) Dsel) := by
  apply localOp_isUnitary
  intro y
  split_ifs
  · exact hD
  · exact isUnitary_one

omit [Fintype Y] [DecidableEq Y] in
/-- The enable-controlled operation keeps the work wires clean. -/
theorem ctrlIdeal_preserves (Dsel : Reg (Sel ⊕ PR) R →L[ℂ] Reg (Sel ⊕ PR) R) :
    Preserves CleanP (ctrlIdeal (Z := Z) (bT := bT) (bP := bP) (A := A) Dsel) := by
  unfold ctrlIdeal
  apply preserves_localOp
  intro y b hy
  constructor
  · intro z
    rw [overwrite_apply_out _ y b _ (fun p hp => by simp [selPR] at hp)]
    exact hy.1 z
  · intro w
    rw [overwrite_apply_out _ y b _ (fun p hp => by simp [selPR] at hp)]
    exact hy.2 w

/-- **The literal inverse of a supplied controlled circuit implements the inverse**: if a valid
circuit is within `ξ` of the enable-controlled operation of a unitary `Dsel` on clean work wires,
its reverse-adjoint `ninv C` is within `ξ` of the enable-controlled operation of `Dsel†`. -/
theorem ctrl_inv_approx (prim : J → Reg Y R →L[ℂ] Reg Y R) (hprim : ∀ j, IsUnitary (prim j))
    (C : List (NInstr (PWr Sel PR Z bT bP A) Y J)) (hC : ∀ i ∈ C, i.Valid)
    (Dsel : Reg (Sel ⊕ PR) R →L[ℂ] Reg (Sel ⊕ PR) R) (hD : IsUnitary Dsel) {ξ : ℝ}
    (h : ApproxOn CleanP (nrun prim C) (ctrlIdeal Dsel) ξ) :
    ApproxOn CleanP (nrun prim (ninv C))
      (ctrlIdeal (Z := Z) (bT := bT) (bP := bP) (A := A) (Dsel†)) ξ := by
  rw [nrun_ninv, ← ctrlIdeal_adjoint]
  have hCu : IsUnitary (nrun prim C) := nrun_isUnitary prim hprim _ hC
  have hOs : Preserves CleanP ((ctrlIdeal (Z := Z) (bT := bT) (bP := bP) (A := A) Dsel)†) := by
    rw [ctrlIdeal_adjoint]
    exact ctrlIdeal_preserves _
  exact h.adjoint hCu (ctrlIdeal_isUnitary Dsel hD) hOs

end Inverse

/-! ### The macros with a supplied private circuit -/

section Macro

variable {V S X' Z Sel Y J : Type*} {a : ℕ} {bT bP A : ℕ}

/-- The native macro of a released instruction with the supplied enable-controlled private
circuit `pc` (and its literal inverse) in place of the native private implementation. -/
def hmacroP (ρ : RelW V a) (sw : SelWires ρ Sel) (UJg : List (Gate (Fin a ⊕ S)))
    (pc : List (NInstr (PWr Sel (Fin a ⊕ S) Z bT bP A) Y J)) :
    Instr V → List (NInstr (HW V S X' Z bT bP A) Y J)
  | .gate g => [NInstr.gate (GateODE.Gate.map wEmb g)]
  | .uj _ adj => nGatesOf (ujGates ρ (if adj then gInv UJg else UJg))
  | .priv _ adj => (if adj then ninv pc else pc).map (NInstr.map (ePW ρ sw))

/-- **The native circuit with a supplied private circuit**: every released instruction replaced
by its macro. -/
def hcircP (ρ : RelW V a) (sw : SelWires ρ Sel) (UJg : List (Gate (Fin a ⊕ S)))
    (pc : List (NInstr (PWr Sel (Fin a ⊕ S) Z bT bP A) Y J)) (l : List (Instr V)) :
    List (NInstr (HW V S X' Z bT bP A) Y J) :=
  l.flatMap (hmacroP ρ sw UJg pc)

/-- The released native macro is the macro with the native private implementation. -/
theorem hmacroP_privMacro (ρ : RelW V a) (sw : SelWires ρ Sel) (UJg : List (Gate (Fin a ⊕ S)))
    (nd : NativeOp Sel (Fin a ⊕ S) Z Y J) (ar : Arith (NB Sel (Fin a ⊕ S) Z)) :
    hmacroP (X' := X') ρ sw UJg (privMacro nd ar) = hmacro ρ sw UJg nd ar := by
  funext i
  cases i <;> rfl

/-- **The released native circuit is the circuit with the native private implementation.** -/
theorem hcircP_privMacro (ρ : RelW V a) (sw : SelWires ρ Sel) (UJg : List (Gate (Fin a ⊕ S)))
    (nd : NativeOp Sel (Fin a ⊕ S) Z Y J) (ar : Arith (NB Sel (Fin a ⊕ S) Z))
    (l : List (Instr V)) :
    hcircP (X' := X') ρ sw UJg (privMacro nd ar) l = hcirc ρ sw UJg nd ar l := by
  unfold hcircP hcirc
  rw [hmacroP_privMacro]

variable [Fintype V] [DecidableEq V] [Fintype S] [DecidableEq S] [Fintype X'] [DecidableEq X']
  [Fintype Z] [DecidableEq Z] [Fintype Sel] [DecidableEq Sel] [Fintype Y] [DecidableEq Y]
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-! #### Validity -/

omit [Fintype V] [Fintype S] [Fintype X'] [DecidableEq X'] [Fintype Z] [Fintype Sel] [Fintype Y]
  [DecidableEq Y] [DecidableEq V] [DecidableEq S] [DecidableEq Z] [DecidableEq Sel] in
theorem hmacroP_valid (ρ : RelW V a) (sw : SelWires ρ Sel) (UJg : List (Gate (Fin a ⊕ S)))
    (hUJ : ∀ g ∈ UJg, GateOK 3 g) (pc : List (NInstr (PWr Sel (Fin a ⊕ S) Z bT bP A) Y J))
    (hpc : ∀ i ∈ pc, i.Valid) (i : Instr V) (hv : i.Valid ρ.anc) :
    ∀ j ∈ hmacroP (X' := X') ρ sw UJg pc i, j.Valid := by
  cases i with
  | gate g =>
      intro j hj
      simp only [hmacroP, List.mem_singleton] at hj
      subst hj
      exact NInstr.valid_map wEmb (NInstr.gate g) hv
  | uj cs adj =>
      simp only [hmacroP]
      apply valid_nGatesOf
      apply ujGates_ok
      split_ifs
      · exact gInv_ok _ hUJ
      · exact hUJ
  | priv cs adj =>
      simp only [hmacroP]
      apply valid_map_list
      split_ifs
      · exact valid_ninv _ hpc
      · exact hpc

omit [Fintype V] [Fintype S] [Fintype X'] [DecidableEq X'] [Fintype Z] [Fintype Sel] [Fintype Y]
  [DecidableEq Y] [DecidableEq V] [DecidableEq S] [DecidableEq Z] [DecidableEq Sel] in
/-- Every instruction of the circuit with a supplied valid private circuit is valid. -/
theorem hcircP_valid (ρ : RelW V a) (sw : SelWires ρ Sel) (UJg : List (Gate (Fin a ⊕ S)))
    (hUJ : ∀ g ∈ UJg, GateOK 3 g) (pc : List (NInstr (PWr Sel (Fin a ⊕ S) Z bT bP A) Y J))
    (hpc : ∀ i ∈ pc, i.Valid) (l : List (Instr V)) (hv : ∀ i ∈ l, i.Valid ρ.anc) :
    ∀ j ∈ hcircP (X' := X') ρ sw UJg pc l, j.Valid := by
  intro j hj
  simp only [hcircP, List.mem_flatMap] at hj
  obtain ⟨i, hi, hj⟩ := hj
  exact hmacroP_valid ρ sw UJg hUJ pc hpc i (hv i hi) j hj

/-! #### Counts -/

omit [Fintype V] [DecidableEq V] [Fintype S] [DecidableEq S] [Fintype X'] [DecidableEq X']
  [Fintype Z] [DecidableEq Z] [Fintype Sel] [DecidableEq Sel] [Fintype Y] [DecidableEq Y] in
theorem hmacroP_nCalls (p : J → Bool) (ρ : RelW V a) (sw : SelWires ρ Sel)
    (UJg : List (Gate (Fin a ⊕ S))) (pc : List (NInstr (PWr Sel (Fin a ⊕ S) Z bT bP A) Y J))
    (i : Instr V) :
    nCallsN p (hmacroP (X' := X') ρ sw UJg pc i) = if i.isPriv then nCallsN p pc else 0 := by
  cases i with
  | gate g => rfl
  | uj cs adj =>
      simp only [hmacroP, nCallsN_nGatesOf, Instr.isPriv]
      rfl
  | priv cs adj =>
      simp only [hmacroP, nCallsN_map, Instr.isPriv, if_true]
      split_ifs
      · rw [nCallsN_ninv]
      · rfl

omit [Fintype V] [DecidableEq V] [Fintype S] [DecidableEq S] [Fintype X'] [DecidableEq X']
  [Fintype Z] [DecidableEq Z] [Fintype Sel] [DecidableEq Sel] [Fintype Y] [DecidableEq Y] in
/-- **The primitive calls**: those of the supplied private circuit, once per private call. -/
theorem hcircP_nCalls (p : J → Bool) (ρ : RelW V a) (sw : SelWires ρ Sel)
    (UJg : List (Gate (Fin a ⊕ S))) (pc : List (NInstr (PWr Sel (Fin a ⊕ S) Z bT bP A) Y J))
    (l : List (Instr V)) :
    nCallsN p (hcircP (X' := X') ρ sw UJg pc l) = nPriv l * nCallsN p pc := by
  rw [hcircP, nCallsN_flatMap]
  exact sum_priv_nat l _ _ (fun i _ => hmacroP_nCalls p ρ sw UJg pc i)

omit [Fintype V] [DecidableEq V] [Fintype S] [DecidableEq S] [Fintype X'] [DecidableEq X']
  [Fintype Z] [DecidableEq Z] [Fintype Sel] [DecidableEq Sel] [Fintype Y] [DecidableEq Y] in
theorem hmacroP_nGates (ρ : RelW V a) (sw : SelWires ρ Sel) (UJg : List (Gate (Fin a ⊕ S)))
    (pc : List (NInstr (PWr Sel (Fin a ⊕ S) Z bT bP A) Y J)) (i : Instr V) :
    nGatesN (hmacroP (X' := X') ρ sw UJg pc i) =
      nGatesN (hmacroP (X' := X') ρ sw UJg ([] : List (NInstr (PWr Sel (Fin a ⊕ S) Z bT bP A)
        Y J)) i) + (if i.isPriv then nGatesN pc else 0) := by
  cases i with
  | gate g => rfl
  | uj cs adj => rfl
  | priv cs adj =>
      simp only [hmacroP, nGatesN_map, Instr.isPriv, if_true]
      split_ifs
      · rw [nGatesN_ninv, nGatesN_ninv]
        exact (zero_add (nGatesN pc)).symm
      · exact (zero_add (nGatesN pc)).symm

omit [Fintype V] [DecidableEq V] [Fintype S] [DecidableEq S] [Fintype X'] [DecidableEq X']
  [Fintype Z] [DecidableEq Z] [Fintype Sel] [DecidableEq Sel] [Fintype Y] [DecidableEq Y] in
/-- **The elementary gates split exactly** into the gates of the circuit with an empty private
circuit and those of the supplied circuit, once per private call. -/
theorem hcircP_nGates (ρ : RelW V a) (sw : SelWires ρ Sel) (UJg : List (Gate (Fin a ⊕ S)))
    (pc : List (NInstr (PWr Sel (Fin a ⊕ S) Z bT bP A) Y J)) (l : List (Instr V)) :
    nGatesN (hcircP (X' := X') ρ sw UJg pc l) =
      nGatesN (hcircP (X' := X') ρ sw UJg ([] : List (NInstr (PWr Sel (Fin a ⊕ S) Z bT bP A)
        Y J)) l) + nPriv l * nGatesN pc := by
  induction l with
  | nil => simp [hcircP, nPriv]
  | cons i l ih =>
      simp only [hcircP, List.flatMap_cons, nGatesN_append] at ih ⊢
      rw [ih, hmacroP_nGates ρ sw UJg pc i]
      simp only [nPriv, List.countP_cons]
      split_ifs <;> ring

omit [Fintype V] [DecidableEq V] [Fintype X'] [DecidableEq X'] [Fintype Z] [DecidableEq Z]
  [Fintype Sel] [DecidableEq Sel] [Fintype Y] [DecidableEq Y] [Fintype S] [DecidableEq S] in
theorem hmacroP_nil_nGates (ρ : RelW V a) (sw : SelWires ρ Sel) (UJg : List (Gate (Fin a ⊕ S)))
    (hUJ : ∀ g ∈ UJg, GateOK 3 g) (i : Instr V) :
    nGatesN (hmacroP (X' := X') ρ sw UJg ([] : List (NInstr (PWr Sel (Fin a ⊕ S) Z bT bP A)
        Y J)) i) ≤ (if i.isGate then 1 else 0) + (if i.isUJ then 7 * UJg.length else 0) +
      (if i.isPriv then 0 else 0) := by
  cases i with
  | gate g =>
      simp only [hmacroP, Instr.isGate, Instr.isUJ, Instr.isPriv, if_true, Bool.false_eq_true,
        if_false, add_zero]
      rfl
  | uj cs adj =>
      simp only [hmacroP, nGatesN_nGatesOf, Instr.isGate, Instr.isUJ, Instr.isPriv, if_true,
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
      cases adj <;> simp [hmacroP, Instr.isGate, Instr.isUJ, Instr.isPriv, ninv, nGatesN]

omit [Fintype V] [DecidableEq V] [Fintype S] [DecidableEq S] [Fintype X'] [DecidableEq X']
  [Fintype Z] [DecidableEq Z] [Fintype Sel] [DecidableEq Sel] [Fintype Y] [DecidableEq Y] in
/-- The gates of the circuit with an empty private circuit: the released gates and the
controlled gates of `U_J`. -/
theorem hcircP_nil_nGates (ρ : RelW V a) (sw : SelWires ρ Sel) (UJg : List (Gate (Fin a ⊕ S)))
    (hUJ : ∀ g ∈ UJg, GateOK 3 g) (l : List (Instr V)) :
    nGatesN (hcircP (X' := X') ρ sw UJg ([] : List (NInstr (PWr Sel (Fin a ⊕ S) Z bT bP A)
        Y J)) l) ≤ nGates l * 1 + nUJ l * (7 * UJg.length) := by
  have h := sum_le_counts l _ 1 (7 * UJg.length) 0
    (fun i _ => hmacroP_nil_nGates (X' := X') (Z := Z) (bT := bT) (bP := bP) (A := A) (Y := Y)
      (J := J) ρ sw UJg hUJ i)
  rw [mul_zero, add_zero] at h
  rw [hcircP, nGatesN_flatMap]
  exact h

omit [Fintype V] [DecidableEq V] [Fintype S] [DecidableEq S] [Fintype X'] [DecidableEq X']
  [Fintype Z] [DecidableEq Z] [Fintype Sel] [DecidableEq Sel] [Fintype Y] [DecidableEq Y] in
/-- **Synthesised gates do not depend on the supplied private circuit**: if its gates are gates
of the adjoint-closed set `𝒢`, neither they nor their inverses are synthesised, and the
synthesised gate occurrences of the circuit are at most the gates of the circuit with an empty
private circuit. -/
theorem nSynN_hcircP_le (𝒢 : Set Kind) (hadj : AdjClosed 𝒢) (ρ : RelW V a)
    (sw : SelWires ρ Sel) (UJg : List (Gate (Fin a ⊕ S)))
    (pc : List (NInstr (PWr Sel (Fin a ⊕ S) Z bT bP A) Y J))
    (hpcG : ∀ g, NInstr.gate g ∈ pc → GateOf 𝒢 g) (l : List (Instr V)) :
    nSynN 𝒢 (hcircP (X' := X') ρ sw UJg pc l) ≤
      nGatesN (hcircP (X' := X') ρ sw UJg ([] : List (NInstr (PWr Sel (Fin a ⊕ S) Z bT bP A)
        Y J)) l) := by
  rw [hcircP, hcircP, nSynN_flatMap, nGatesN_flatMap]
  apply List.sum_le_sum
  intro i _
  cases i with
  | gate g => exact nSynN_le 𝒢 _
  | uj cs adj => exact nSynN_le 𝒢 _
  | priv cs adj =>
      show nSynN 𝒢 ((if adj then ninv pc else pc).map (NInstr.map (ePW ρ sw))) ≤ _
      rw [nSynN_map]
      have h0 : nSynN 𝒢 (if adj then ninv pc else pc) = 0 := by
        split_ifs
        · rw [nSynN_ninv 𝒢 hadj]
          exact nSynN_eq_zero 𝒢 pc hpcG
        · exact nSynN_eq_zero 𝒢 pc hpcG
      rw [h0]
      exact Nat.zero_le _

/-! #### The error -/

/-- **Every macro implements its released instruction**, the private calls within the accuracy
`ξ` of the supplied circuit. -/
theorem hmacroP_approx (prim : J → Reg Y R →L[ℂ] Reg Y R) (hprim : ∀ j, IsUnitary (prim j))
    (ρ : RelW V a) (sw : SelWires ρ Sel) (UJg : List (Gate (Fin a ⊕ S)))
    (hUJ : ∀ g ∈ UJg, GateOK 3 g)
    (pc : List (NInstr (PWr Sel (Fin a ⊕ S) Z bT bP A) Y J)) (hpcV : ∀ i ∈ pc, i.Valid)
    {ξ : ℝ} (hξ : 0 ≤ ξ)
    (Dfam : Bool → Cfg Sel → (Reg (Fin a) (Reg S R) →L[ℂ] Reg (Fin a) (Reg S R)))
    (hDu : ∀ w, IsUnitary (Dfam false w)) (hDadj : ∀ w, Dfam true w = (Dfam false w)†)
    (hpc : ApproxOn CleanP (nrun prim pc) (ctrlIdeal (selOp (Dfam false))) ξ) (i : Instr V) :
    ApproxOn CleanX (nrun prim (hmacroP (X' := X') ρ sw UJg pc i))
      (liftB (conj (evalSel ρ UJg sw Dfam i))) (if i.isPriv then ξ else 0) := by
  cases i with
  | gate g =>
      apply ApproxOn.of_agrees
      have e1 : nrun prim (hmacroP (X' := X') ρ sw UJg pc (Instr.gate g)) =
          gateOp ((g.cs.map (fun c => (Sum.inl c.1, c.2))).map (fun c => (Sum.inl c.1, c.2)))
            (Sum.inl (Sum.inl g.t)) g.u := by
        simp only [hmacroP, nrun_singleton, NInstr.eval_gate, GateODE.Gate.map, List.map_map]
        rfl
      have e2 : liftB (X := XW Z bT bP A ⊕ X') (conj (evalSel (R := R) ρ UJg sw Dfam
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
      have e2 : liftB (X := XW Z bT bP A ⊕ X') (conj (evalSel (R := R) ρ UJg sw Dfam
          (Instr.uj cs adj))) =
          gRun (gs.map (ctrlMap (secW ρ) (fun p => (Sum.inl (mapId (S := S) ρ.anc p) :
            HW V S X' Z bT bP A)))) := by
        simp only [evalSel]
        rw [liftB_conj_selOracle_canon]
        simp only [hconj]
        exact localOp_ctrl_gRun _ (secW ρ) (fun p => pEmb_ne_secW ρ p) gs
          (fun g hg => (hgsok g hg).2.1)
      have e1 : nrun prim (hmacroP (X' := X') ρ sw UJg pc (Instr.uj cs adj)) =
          gRun (ujGates ρ gs) := by
        simp only [hmacroP]
        rw [nrun_nGatesOf]
      rw [e1, e2]
      exact ujGates_agrees ρ gs hgsok
  | priv cs adj =>
      simp only [Instr.isPriv, if_true]
      have hlift := liftB_conj_selOracle (R := R) (X' := X') (Z := Z) (bT := bT)
        (bP := bP) (A := A) ρ sw (Dfam adj)
      have e1 : nrun prim (hmacroP (X' := X') ρ sw UJg pc (Instr.priv cs adj)) =
          localOp (ePW ρ sw) (ePW ρ sw).injective
            (fun _ => nrun prim (if adj then ninv pc else pc)) := by
        simp only [hmacroP]
        exact nrun_map prim (ePW ρ sw) _
      simp only [evalSel]
      rw [e1, hlift]
      apply approxOn_localOp _ _ _ hξ (SA := CleanP)
        (fun y hy => ⟨fun z => hy (Sum.inl (Sum.inl z)),
          fun w => hy (Sum.inl (Sum.inr (Sum.inl w)))⟩)
      intro _
      cases adj
      · exact hpc
      · have hDsel : IsUnitary (selOp (Dfam false)) := selOp_isUnitary _ hDu
        have h := ctrl_inv_approx prim hprim pc hpcV _ hDsel hpc
        have hadj : (selOp (Dfam false))† = selOp (Dfam true) := by
          rw [selOp_adjoint]
          exact congrArg selOp (funext fun w => (hDadj w).symm)
        rw [hadj] at h
        exact h

/-- **The circuit with a supplied private circuit approximates the lifted released circuit**:
the errors `ξ` of the private calls add. -/
theorem hcircP_approx (prim : J → Reg Y R →L[ℂ] Reg Y R) (hprim : ∀ j, IsUnitary (prim j))
    (ρ : RelW V a) (sw : SelWires ρ Sel) (UJg : List (Gate (Fin a ⊕ S)))
    (hUJ : ∀ g ∈ UJg, GateOK 3 g)
    (pc : List (NInstr (PWr Sel (Fin a ⊕ S) Z bT bP A) Y J)) (hpcV : ∀ i ∈ pc, i.Valid)
    {ξ : ℝ} (hξ : 0 ≤ ξ)
    (Dfam : Bool → Cfg Sel → (Reg (Fin a) (Reg S R) →L[ℂ] Reg (Fin a) (Reg S R)))
    (hDu : ∀ w, IsUnitary (Dfam false w)) (hDadj : ∀ w, Dfam true w = (Dfam false w)†)
    (hpc : ApproxOn CleanP (nrun prim pc) (ctrlIdeal (selOp (Dfam false))) ξ)
    (l : List (Instr V)) (hv : ∀ i ∈ l, i.Valid ρ.anc) :
    ApproxOn CleanX (nrun prim (hcircP (X' := X') ρ sw UJg pc l))
      (liftB (conj (prodOps (evalSel ρ UJg sw Dfam) l))) ((nPriv l : ℝ) * ξ) := by
  have h := approxOn_flatMap prim CleanX (hmacroP (X' := X') ρ sw UJg pc)
    (fun i => liftB (X := XW Z bT bP A ⊕ X') (conj (evalSel ρ UJg sw Dfam i)))
    (fun i => if i.isPriv then ξ else 0) l
    (fun i _ => hmacroP_approx prim hprim ρ sw UJg hUJ pc hpcV hξ Dfam hDu hDadj hpc i)
    (fun i _ => preserves_liftB _)
    (fun i hi ψ => IsUnitary.norm_apply_le
      (liftB_isUnitary (conj_isUnitary (evalSel_isUnitary ρ UJg hUJ sw Dfam hDu hDadj i
        (hv i hi)))) ψ)
    (fun i hi ψ => IsUnitary.norm_apply_le (nrun_isUnitary prim hprim _
      (hmacroP_valid ρ sw UJg hUJ pc hpcV i (hv i hi))) ψ)
    (fun i _ => by split_ifs <;> linarith)
  rw [sum_priv_real, prodOps_liftB_conj] at h
  exact h

/-- **The full-output error of the circuit with a supplied private circuit.** If the released
circuit, with `U_J` from its gates and the selected private operation, is within `ε₀` of `U` on a
clean released embedding `ι`, then the circuit is within `ε₀ + ξ nPriv l` of `U` on the system
embedding, every qubit outside the system starting clean. -/
theorem hcircP_error (prim : J → Reg Y R →L[ℂ] Reg Y R) (hprim : ∀ j, IsUnitary (prim j))
    (ρ : RelW V a) (sw : SelWires ρ Sel) (UJg : List (Gate (Fin a ⊕ S)))
    (hUJ : ∀ g ∈ UJg, GateOK 3 g)
    (pc : List (NInstr (PWr Sel (Fin a ⊕ S) Z bT bP A) Y J)) (hpcV : ∀ i ∈ pc, i.Valid)
    {ξ : ℝ} (hξ : 0 ≤ ξ)
    (Dfam : Bool → Cfg Sel → (Reg (Fin a) (Reg S R) →L[ℂ] Reg (Fin a) (Reg S R)))
    (hDu : ∀ w, IsUnitary (Dfam false w)) (hDadj : ∀ w, Dfam true w = (Dfam false w)†)
    (hpc : ApproxOn CleanP (nrun prim pc) (ctrlIdeal (selOp (Dfam false))) ξ)
    (l : List (Instr V)) (hv : ∀ i ∈ l, i.Valid ρ.anc)
    (ι : Reg S R →L[ℂ] Reg V (Reg S R)) (hι : ∀ ψ, ‖ι ψ‖ = ‖ψ‖)
    (U : Reg S R →L[ℂ] Reg S R) (Orel : Reg V (Reg S R) →L[ℂ] Reg V (Reg S R))
    (hO : prodOps (V := V) (R := Reg S R) (evalSel ρ UJg sw Dfam) l = Orel) {ε₀ : ℝ}
    (hrel : ‖Orel ∘L ι - ι ∘L U‖ ≤ ε₀) :
    ‖nrun prim (hcircP (X' := X') ρ sw UJg pc l) ∘L sysEmb ι - sysEmb ι ∘L U‖ ≤
      ε₀ + (nPriv l : ℝ) * ξ := by
  have hA := hcircP_approx (X' := X') prim hprim ρ sw UJg hUJ pc hpcV hξ Dfam hDu hDadj hpc l hv
  rw [hO] at hA
  have hε₀ : 0 ≤ ε₀ := le_trans (norm_nonneg (Orel ∘L ι - ι ∘L U)) hrel
  have hδ : 0 ≤ (nPriv l : ℝ) * ξ := by positivity
  apply ContinuousLinearMap.opNorm_le_bound _ (by linarith)
  intro ψ
  set C := nrun prim (hcircP (X' := X') ρ sw UJg pc l) with hC
  set φ : Reg (V ⊕ S) R := fl (ι ψ) with hφ
  have e1 : (C ∘L sysEmb ι - sysEmb ι ∘L U :
      Reg S R →L[ℂ] Reg (HW V S X' Z bT bP A) R) ψ =
      (C (cleanEmb φ) - liftB (X := XW Z bT bP A ⊕ X') (conj Orel) (cleanEmb φ)) +
        cleanEmb (fl ((Orel ∘L ι - ι ∘L U) ψ)) := by
    have h1 : liftB (X := XW Z bT bP A ⊕ X') (conj Orel) (cleanEmb φ) =
        cleanEmb (conj Orel φ) := by
      rw [← comp_apply, liftB_cleanEmb, comp_apply]
    rw [h1, hφ, conj_fl]
    simp only [sysEmb, sub_apply, comp_apply, map_sub]
    abel
  have hφn : ‖φ‖ = ‖ψ‖ := by rw [hφ, norm_fl, hι]
  rw [e1]
  calc ‖C (cleanEmb φ) - liftB (X := XW Z bT bP A ⊕ X') (conj Orel) (cleanEmb φ) +
        cleanEmb (fl ((Orel ∘L ι - ι ∘L U) ψ))‖
      ≤ ‖C (cleanEmb φ) - liftB (X := XW Z bT bP A ⊕ X') (conj Orel) (cleanEmb φ)‖ +
        ‖cleanEmb (X := XW Z bT bP A ⊕ X') (fl ((Orel ∘L ι - ι ∘L U) ψ))‖ :=
        norm_add_le _ _
    _ ≤ (nPriv l : ℝ) * ξ * ‖ψ‖ + ε₀ * ‖ψ‖ := by
        gcongr
        · have := hA _ (supp_cleanEmb φ)
          rwa [norm_cleanEmb, hφn] at this
        · rw [norm_cleanEmb, norm_fl]
          exact ((Orel ∘L ι - ι ∘L U).le_opNorm ψ).trans
            (mul_le_mul_of_nonneg_right hrel (norm_nonneg _))
    _ = (ε₀ + (nPriv l : ℝ) * ξ) * ‖ψ‖ := by ring

end Macro

end

end SparseHamiltonian.GateSelective
