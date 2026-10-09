import GateEfficientNative.Hamiltonian.Approx

/-!
# The native circuit of a released instruction list

`hcirc sw UJg nd ar l` replaces every instruction of the released list `l` by
its native macro (`hmacro`).  For lists whose oracle calls are controlled by
the sector wire (`SecOK`, true for every released simulator) and whose
instructions are valid:

* every native instruction is valid (`hcirc_valid`);
* the primitive calls are those of `2 · nPriv l` copies of the compute circuit
  `V` (`hcirc_nCalls`);
* the elementary gates are at most
  `nGates l + 7 C_J nUJ l + G_C nPriv l` (`hcirc_nGates`), where
  `C_J` is the number of gates of `U_J` and
  `G_C = 2 nGatesN V + 2 |circ| + 2 bP + bT + 1` is the number of gates of one
  native private call;
* in the full-output convention with the system embedding `sysEmb` (every
  wire other than the system qubits is zero), the native circuit is within
  `ε₀ + 4ζ · nPriv l` of every target `U` that the released circuit (with
  `U_J` from its gates and the selected private operation) approximates within
  `ε₀` (`hcirc_error`).
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateNative

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit GateCircuit.Sim
open scoped InnerProduct BigOperators

/-! ### Sums along a released instruction list -/

section Sums

variable {W : Type*}

theorem sum_priv_nat (l : List (Instr W)) (f : Instr W → ℕ) (c : ℕ)
    (hf : ∀ i ∈ l, f i = if i.isPriv then c else 0) :
    (l.map f).sum = nPriv l * c := by
  induction l with
  | nil => simp [nPriv]
  | cons i l ih =>
      rw [List.map_cons, List.sum_cons, ih (fun j hj => hf j (List.mem_cons_of_mem i hj)),
        hf i List.mem_cons_self]
      simp only [nPriv, List.countP_cons]
      split_ifs <;> ring

theorem sum_priv_real (l : List (Instr W)) (c : ℝ) :
    (l.map (fun i => if i.isPriv then c else 0)).sum = (nPriv l : ℝ) * c := by
  induction l with
  | nil => simp [nPriv]
  | cons i l ih =>
      rw [List.map_cons, List.sum_cons, ih]
      simp only [nPriv, List.countP_cons]
      split_ifs <;> push_cast <;> ring

theorem sum_le_counts (l : List (Instr W)) (f : Instr W → ℕ) (cg cu cp : ℕ)
    (hf : ∀ i ∈ l, f i ≤ (if i.isGate then cg else 0) + (if i.isUJ then cu else 0) +
      (if i.isPriv then cp else 0)) :
    (l.map f).sum ≤ nGates l * cg + nUJ l * cu + nPriv l * cp := by
  induction l with
  | nil => simp
  | cons i l ih =>
      have h1 := hf i List.mem_cons_self
      have h2 := ih (fun j hj => hf j (List.mem_cons_of_mem i hj))
      rw [List.map_cons, List.sum_cons]
      simp only [nGates, nUJ, nPriv, List.countP_cons] at h2 ⊢
      cases i <;>
        simp only [Instr.isGate, Instr.isUJ, Instr.isPriv, if_true, Bool.false_eq_true, if_false,
          add_zero, zero_add, add_mul, one_mul] at h1 h2 ⊢ <;>
        omega

end Sums

/-! ### Products of lifted operators -/

section Prod

variable {W S X : Type*} [Fintype W] [DecidableEq W] [Fintype S] [DecidableEq S] [Fintype X]
  [DecidableEq X]
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

theorem prodOps_liftB_conj {α : Type*} (O : α → Reg W (Reg S R) →L[ℂ] Reg W (Reg S R))
    (l : List α) :
    prodOps (fun i => liftB (X := X) (conj (O i))) l =
      (liftB (X := X) (conj (prodOps O l)) : Reg ((W ⊕ S) ⊕ X) R →L[ℂ] Reg ((W ⊕ S) ⊕ X) R) := by
  induction l with
  | nil => simp only [prodOps, conj_one, liftB_one]
  | cons i l ih => rw [prodOps, prodOps, ih, conj_comp, liftB_comp]

omit [Fintype X] [DecidableEq X] [CompleteSpace R] in
theorem norm_fl (ψ : Reg W (Reg S R)) : ‖fl ψ‖ = ‖ψ‖ :=
  LinearIsometryEquiv.norm_map (flat W S R) ψ

omit [Fintype X] [DecidableEq X] [CompleteSpace R] in
theorem fl_apply (ψ : Reg W (Reg S R)) (y : Cfg (W ⊕ S)) :
    fl ψ y = ψ (fun w => y (Sum.inl w)) (fun s => y (Sum.inr s)) := rfl

omit [Fintype X] [DecidableEq X] [CompleteSpace R] in
theorem conj_fl (O : Reg W (Reg S R) →L[ℂ] Reg W (Reg S R)) (ψ : Reg W (Reg S R)) :
    conj O (fl ψ) = fl (O ψ) := by
  unfold conj
  simp

end Prod

/-! ### The native circuit -/

section Native

variable {V S X' Z Sel Y J : Type*} [Fintype V] [DecidableEq V] [Fintype S] [DecidableEq S]
  [Fintype X'] [DecidableEq X'] [Fintype Z] [DecidableEq Z] [Fintype Sel] [DecidableEq Sel]
  [Fintype Y] [DecidableEq Y] {a : ℕ}
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- **The native circuit**: every released instruction replaced by its macro. -/
def hcirc (ρ : RelW V a) (sw : SelWires ρ Sel) (UJg : List (Gate (Fin a ⊕ S)))
    (nd : NativeOp Sel (Fin a ⊕ S) Z Y J) (ar : Arith (NB Sel (Fin a ⊕ S) Z))
    (l : List (Instr V)) : List (NInstr (HW V S X' Z ar.bT ar.bP ar.A) Y J) :=
  l.flatMap (hmacro ρ sw UJg nd ar)

/-- The system embedding along a clean released embedding `ι`: every added
work wire is zero. -/
def sysEmb {bT bP A : ℕ} (ι : Reg S R →L[ℂ] Reg V (Reg S R)) :
    Reg S R →L[ℂ] Reg (HW V S X' Z bT bP A) R :=
  cleanEmb ∘L fl ∘L ι

omit [Fintype Sel] [DecidableEq Sel] [Fintype Y] [DecidableEq Y] [CompleteSpace R] in
theorem norm_sysEmb {bT bP A : ℕ} (ι : Reg S R →L[ℂ] Reg V (Reg S R)) (hι : ∀ ψ, ‖ι ψ‖ = ‖ψ‖)
    (ψ : Reg S R) :
    ‖sysEmb (X' := X') (Z := Z) (bT := bT) (bP := bP) (A := A) ι ψ‖ = ‖ψ‖ := by
  rw [sysEmb, comp_apply, comp_apply, norm_cleanEmb, norm_fl, hι]

/-! ### Validity and unitarity -/

omit [Fintype V] [Fintype S] [Fintype X'] [DecidableEq X'] [Fintype Z] [Fintype Sel] [Fintype Y]
  [DecidableEq Y] [DecidableEq V] in
theorem hmacro_valid (ρ : RelW V a) (sw : SelWires ρ Sel) (UJg : List (Gate (Fin a ⊕ S)))
    (hUJ : ∀ g ∈ UJg, GateOK 3 g) (nd : NativeOp Sel (Fin a ⊕ S) Z Y J) (hnd : nd.Public)
    (ar : Arith (NB Sel (Fin a ⊕ S) Z)) (helem : ∀ g ∈ ar.circ, g.cs.length ≤ 3)
    (hcl : Classical ar.circ) (i : Instr V) (hv : i.Valid ρ.anc) :
    ∀ j ∈ hmacro (X' := X') ρ sw UJg nd ar i, j.Valid := by
  cases i with
  | gate g =>
      intro j hj
      simp only [hmacro, List.mem_singleton] at hj
      subst hj
      exact NInstr.valid_map wEmb (NInstr.gate g) hv
  | uj cs adj =>
      simp only [hmacro]
      apply valid_nGatesOf
      apply ujGates_ok
      split_ifs
      · exact gInv_ok _ hUJ
      · exact hUJ
  | priv cs adj =>
      simp only [hmacro]
      apply valid_map_list
      split_ifs
      · exact valid_ninv _ (privMacro_valid nd hnd ar helem hcl)
      · exact privMacro_valid nd hnd ar helem hcl

omit [Fintype V] [Fintype S] [Fintype X'] [DecidableEq X'] [Fintype Z] [Fintype Sel] [Fintype Y]
  [DecidableEq Y] [DecidableEq V] in
theorem hcirc_valid (ρ : RelW V a) (sw : SelWires ρ Sel) (UJg : List (Gate (Fin a ⊕ S)))
    (hUJ : ∀ g ∈ UJg, GateOK 3 g) (nd : NativeOp Sel (Fin a ⊕ S) Z Y J) (hnd : nd.Public)
    (ar : Arith (NB Sel (Fin a ⊕ S) Z)) (helem : ∀ g ∈ ar.circ, g.cs.length ≤ 3)
    (hcl : Classical ar.circ) (l : List (Instr V))
    (hv : ∀ i ∈ l, i.Valid ρ.anc) : ∀ j ∈ hcirc (X' := X') ρ sw UJg nd ar l, j.Valid := by
  intro j hj
  simp only [hcirc, List.mem_flatMap] at hj
  obtain ⟨i, hi, hj⟩ := hj
  exact hmacro_valid ρ sw UJg hUJ nd hnd ar helem hcl i (hv i hi) j hj

omit [Fintype X'] [DecidableEq X'] [Fintype Z] [DecidableEq Z] [Fintype Y] [DecidableEq Y]
  [Fintype Sel] [DecidableEq Sel] in
theorem selOracle_isUnitary (ρ : RelW V a) (sw : SelWires ρ Sel)
    (Dfam : Cfg Sel → (Reg (Fin a) (Reg S R) →L[ℂ] Reg (Fin a) (Reg S R)))
    (hD : ∀ w, IsUnitary (Dfam w)) : IsUnitary (selOracle ρ sw Dfam) := by
  apply localOp_isUnitary
  intro x
  split_ifs
  · exact hD _
  · exact isUnitary_one

omit [Fintype X'] [DecidableEq X'] [Fintype Z] [DecidableEq Z] [Fintype Y] [DecidableEq Y]
  [Fintype Sel] [DecidableEq Sel] in
theorem evalSel_isUnitary (ρ : RelW V a) (UJg : List (Gate (Fin a ⊕ S)))
    (hUJ : ∀ g ∈ UJg, GateOK 3 g) (sw : SelWires ρ Sel)
    (Dfam : Bool → Cfg Sel → (Reg (Fin a) (Reg S R) →L[ℂ] Reg (Fin a) (Reg S R)))
    (hDu : ∀ w, IsUnitary (Dfam false w)) (hDadj : ∀ w, Dfam true w = (Dfam false w)†)
    (i : Instr V) (hv : i.Valid ρ.anc) : IsUnitary (evalSel ρ UJg sw Dfam i) := by
  cases i with
  | gate g =>
      simp only [evalSel]
      exact gateOp_isUnitary g.cs g.t g.u hv.2.2
  | uj cs adj =>
      simp only [evalSel]
      refine selOracle_isUnitary ρ (noSel ρ) _ (fun _ => ?_)
      split_ifs
      · simpa [star_eq_adjoint] using (UJop_isUnitary (R := R) UJg hUJ).adjoint
      · exact UJop_isUnitary UJg hUJ
  | priv cs adj =>
      simp only [evalSel]
      refine selOracle_isUnitary ρ sw _ (fun w => ?_)
      cases adj
      · exact hDu w
      · rw [hDadj]
        simpa [star_eq_adjoint] using (hDu w).adjoint

/-! ### Counts -/

omit [Fintype V] [DecidableEq V] [Fintype S] [DecidableEq S] [Fintype X'] [DecidableEq X']
  [Fintype Z] [DecidableEq Z] [Fintype Sel] [DecidableEq Sel] [Fintype Y] [DecidableEq Y] in
theorem hmacro_nCalls (p : J → Bool) (ρ : RelW V a) (sw : SelWires ρ Sel)
    (UJg : List (Gate (Fin a ⊕ S))) (nd : NativeOp Sel (Fin a ⊕ S) Z Y J)
    (ar : Arith (NB Sel (Fin a ⊕ S) Z)) (i : Instr V) :
    nCallsN p (hmacro (X' := X') ρ sw UJg nd ar i) =
      if i.isPriv then 2 * nCallsN p nd.V else 0 := by
  cases i with
  | gate g => rfl
  | uj cs adj =>
      simp only [hmacro, nCallsN_nGatesOf, Instr.isPriv]
      rfl
  | priv cs adj =>
      simp only [hmacro, nCallsN_map, Instr.isPriv, if_true]
      split_ifs
      · rw [nCallsN_ninv, privMacro_nCalls]
      · rw [privMacro_nCalls]

omit [Fintype V] [DecidableEq V] [Fintype S] [DecidableEq S] [Fintype X'] [DecidableEq X']
  [Fintype Z] [DecidableEq Z] [Fintype Sel] [DecidableEq Sel] [Fintype Y] [DecidableEq Y] in
/-- The primitive calls of the native circuit. -/
theorem hcirc_nCalls (p : J → Bool) (ρ : RelW V a) (sw : SelWires ρ Sel)
    (UJg : List (Gate (Fin a ⊕ S))) (nd : NativeOp Sel (Fin a ⊕ S) Z Y J)
    (ar : Arith (NB Sel (Fin a ⊕ S) Z)) (l : List (Instr V)) :
    nCallsN p (hcirc (X' := X') ρ sw UJg nd ar l) = nPriv l * (2 * nCallsN p nd.V) := by
  rw [hcirc, nCallsN_flatMap]
  exact sum_priv_nat l _ _ (fun i _ => hmacro_nCalls p ρ sw UJg nd ar i)

omit [Fintype V] [DecidableEq V] [Fintype X'] [DecidableEq X'] [Fintype Z] [DecidableEq Z]
  [Fintype Sel] [DecidableEq Sel] [Fintype Y] [DecidableEq Y] [Fintype S] [DecidableEq S] in
theorem hmacro_nGates (ρ : RelW V a) (sw : SelWires ρ Sel) (UJg : List (Gate (Fin a ⊕ S)))
    (hUJ : ∀ g ∈ UJg, GateOK 3 g) (nd : NativeOp Sel (Fin a ⊕ S) Z Y J)
    (ar : Arith (NB Sel (Fin a ⊕ S) Z)) (i : Instr V) :
    nGatesN (hmacro (X' := X') ρ sw UJg nd ar i) ≤ (if i.isGate then 1 else 0) +
      (if i.isUJ then 7 * UJg.length else 0) +
      (if i.isPriv then 2 * nGatesN nd.V + 2 * ar.circ.length + (2 * ar.bP + ar.bT + 1)
        else 0) := by
  cases i with
  | gate g =>
      simp only [hmacro, Instr.isGate, Instr.isUJ, Instr.isPriv, if_true, Bool.false_eq_true,
        if_false, add_zero]
      rfl
  | uj cs adj =>
      simp only [hmacro, nGatesN_nGatesOf, Instr.isGate, Instr.isUJ, Instr.isPriv, if_true,
        Bool.false_eq_true, if_false, add_zero, zero_add]
      have hok : ∀ g ∈ (if adj then gInv UJg else UJg), GateOK 3 g := by
        split_ifs
        · exact gInv_ok _ hUJ
        · exact hUJ
      have hlen : (if adj then gInv UJg else UJg).length = UJg.length := by
        split_ifs
        · exact gInv_length UJg
        · rfl
      have h := ujGates_length (X' := X') (Z := Z) (bT := ar.bT) (bP := ar.bP) (A := ar.A) ρ _ hok
      rw [hlen] at h
      exact h
  | priv cs adj =>
      simp only [hmacro, nGatesN_map, Instr.isGate, Instr.isUJ, Instr.isPriv, if_true,
        Bool.false_eq_true, if_false, zero_add]
      split_ifs
      · rw [nGatesN_ninv, privMacro_nGates]
      · rw [privMacro_nGates]

omit [Fintype V] [DecidableEq V] [Fintype X'] [DecidableEq X'] [Fintype Z] [DecidableEq Z]
  [Fintype Sel] [DecidableEq Sel] [Fintype Y] [DecidableEq Y] [Fintype S] [DecidableEq S] in
/-- The elementary gates of the native circuit. -/
theorem hcirc_nGates (ρ : RelW V a) (sw : SelWires ρ Sel) (UJg : List (Gate (Fin a ⊕ S)))
    (hUJ : ∀ g ∈ UJg, GateOK 3 g) (nd : NativeOp Sel (Fin a ⊕ S) Z Y J)
    (ar : Arith (NB Sel (Fin a ⊕ S) Z)) (l : List (Instr V)) :
    nGatesN (hcirc (X' := X') ρ sw UJg nd ar l) ≤ nGates l * 1 + nUJ l * (7 * UJg.length) +
      nPriv l * (2 * nGatesN nd.V + 2 * ar.circ.length + (2 * ar.bP + ar.bT + 1)) := by
  rw [hcirc, nGatesN_flatMap]
  exact sum_le_counts l _ _ _ _ (fun i _ => hmacro_nGates ρ sw UJg hUJ nd ar i)

/-! ### The error -/

/-- **The native circuit approximates the lifted released circuit**: the
errors of the private calls add. -/
theorem hcirc_approx (prim : J → Reg Y R →L[ℂ] Reg Y R) (hprim : ∀ j, IsUnitary (prim j))
    (ρ : RelW V a) (sw : SelWires ρ Sel) (UJg : List (Gate (Fin a ⊕ S)))
    (hUJ : ∀ g ∈ UJg, GateOK 3 g)
    (nd : NativeOp Sel (Fin a ⊕ S) Z Y J) (hnd : nd.Public) (ar : Arith (NB Sel (Fin a ⊕ S) Z))
    {ζ : ℝ} (hζ : 0 ≤ ζ) (har : ArithOK ar (Sum.inl (Sum.inr nd.o)) nd.dec ζ)
    (Dfam : Bool → Cfg Sel → (Reg (Fin a) (Reg S R) →L[ℂ] Reg (Fin a) (Reg S R)))
    (hDu : ∀ w, IsUnitary (Dfam false w)) (hDadj : ∀ w, Dfam true w = (Dfam false w)†)
    (hN : NativeOK prim nd (selOp (Dfam false)))
    (l : List (Instr V)) (hv : ∀ i ∈ l, i.Valid ρ.anc) :
    ApproxOn CleanX (nrun prim (hcirc (X' := X') ρ sw UJg nd ar l))
      (liftB (conj (prodOps (evalSel ρ UJg sw Dfam) l))) ((nPriv l : ℝ) * (4 * ζ)) := by
  have h := approxOn_flatMap prim CleanX (hmacro (X' := X') ρ sw UJg nd ar)
    (fun i => liftB (X := XW Z ar.bT ar.bP ar.A ⊕ X') (conj (evalSel ρ UJg sw Dfam i)))
    (fun i => if i.isPriv then 4 * ζ else 0) l
    (fun i _ => hmacro_approx prim hprim ρ sw UJg hUJ nd hnd ar hζ har Dfam hDu hDadj hN i)
    (fun i _ => preserves_liftB _)
    (fun i hi ψ => IsUnitary.norm_apply_le
      (liftB_isUnitary (conj_isUnitary (evalSel_isUnitary ρ UJg hUJ sw Dfam hDu hDadj i
        (hv i hi)))) ψ)
    (fun i hi ψ => IsUnitary.norm_apply_le (nrun_isUnitary prim hprim _
      (hmacro_valid ρ sw UJg hUJ nd hnd ar har.elem har.classical i (hv i hi))) ψ)
    (fun i _ => by split_ifs <;> linarith)
  rw [sum_priv_real, prodOps_liftB_conj] at h
  exact h

/-- **The full-output error of the native circuit.**  If the released circuit,
with `U_J` from its gates and the selected private operation, is within `ε₀`
of `U` on a clean released embedding `ι`, then the native circuit is within
`ε₀ + 4ζ nPriv l` of `U` on the system embedding. -/
theorem hcirc_error (prim : J → Reg Y R →L[ℂ] Reg Y R) (hprim : ∀ j, IsUnitary (prim j))
    (ρ : RelW V a) (sw : SelWires ρ Sel) (UJg : List (Gate (Fin a ⊕ S)))
    (hUJ : ∀ g ∈ UJg, GateOK 3 g)
    (nd : NativeOp Sel (Fin a ⊕ S) Z Y J) (hnd : nd.Public) (ar : Arith (NB Sel (Fin a ⊕ S) Z))
    {ζ : ℝ} (hζ : 0 ≤ ζ) (har : ArithOK ar (Sum.inl (Sum.inr nd.o)) nd.dec ζ)
    (Dfam : Bool → Cfg Sel → (Reg (Fin a) (Reg S R) →L[ℂ] Reg (Fin a) (Reg S R)))
    (hDu : ∀ w, IsUnitary (Dfam false w)) (hDadj : ∀ w, Dfam true w = (Dfam false w)†)
    (hN : NativeOK prim nd (selOp (Dfam false)))
    (l : List (Instr V)) (hv : ∀ i ∈ l, i.Valid ρ.anc)
    (ι : Reg S R →L[ℂ] Reg V (Reg S R)) (hι : ∀ ψ, ‖ι ψ‖ = ‖ψ‖)
    (U : Reg S R →L[ℂ] Reg S R) (Orel : Reg V (Reg S R) →L[ℂ] Reg V (Reg S R))
    (hO : prodOps (V := V) (R := Reg S R) (evalSel ρ UJg sw Dfam) l = Orel) {ε₀ : ℝ}
    (hrel : ‖Orel ∘L ι - ι ∘L U‖ ≤ ε₀) :
    ‖nrun prim (hcirc (X' := X') ρ sw UJg nd ar l) ∘L sysEmb ι - sysEmb ι ∘L U‖ ≤
      ε₀ + (nPriv l : ℝ) * (4 * ζ) := by
  have hA := hcirc_approx (X' := X') prim hprim ρ sw UJg hUJ nd hnd ar hζ har Dfam hDu hDadj hN
    l hv
  rw [hO] at hA
  have hε₀ : 0 ≤ ε₀ := le_trans (norm_nonneg (Orel ∘L ι - ι ∘L U)) hrel
  have hδ : 0 ≤ (nPriv l : ℝ) * (4 * ζ) := by positivity
  apply ContinuousLinearMap.opNorm_le_bound _ (by linarith)
  intro ψ
  set C := nrun prim (hcirc (X' := X') ρ sw UJg nd ar l) with hC
  set φ : Reg (V ⊕ S) R := fl (ι ψ) with hφ
  have e1 : (C ∘L sysEmb ι - sysEmb ι ∘L U :
      Reg S R →L[ℂ] Reg (HW V S X' Z ar.bT ar.bP ar.A) R) ψ =
      (C (cleanEmb φ) - liftB (X := XW Z ar.bT ar.bP ar.A ⊕ X') (conj Orel) (cleanEmb φ)) +
        cleanEmb (fl ((Orel ∘L ι - ι ∘L U) ψ)) := by
    have h1 : liftB (X := XW Z ar.bT ar.bP ar.A ⊕ X') (conj Orel) (cleanEmb φ) =
        cleanEmb (conj Orel φ) := by
      rw [← comp_apply, liftB_cleanEmb, comp_apply]
    rw [h1, hφ, conj_fl]
    simp only [sysEmb, sub_apply, comp_apply, map_sub]
    abel
  have hφn : ‖φ‖ = ‖ψ‖ := by rw [hφ, norm_fl, hι]
  rw [e1]
  calc ‖C (cleanEmb φ) - liftB (X := XW Z ar.bT ar.bP ar.A ⊕ X') (conj Orel) (cleanEmb φ) +
        cleanEmb (fl ((Orel ∘L ι - ι ∘L U) ψ))‖
      ≤ ‖C (cleanEmb φ) - liftB (X := XW Z ar.bT ar.bP ar.A ⊕ X') (conj Orel) (cleanEmb φ)‖ +
        ‖cleanEmb (X := XW Z ar.bT ar.bP ar.A ⊕ X') (fl ((Orel ∘L ι - ι ∘L U) ψ))‖ :=
        norm_add_le _ _
    _ ≤ (nPriv l : ℝ) * (4 * ζ) * ‖ψ‖ + ε₀ * ‖ψ‖ := by
        gcongr
        · have := hA _ (supp_cleanEmb φ)
          rwa [norm_cleanEmb, hφn] at this
        · rw [norm_cleanEmb, norm_fl]
          exact ((Orel ∘L ι - ι ∘L U).le_opNorm ψ).trans
            (mul_le_mul_of_nonneg_right hrel (norm_nonneg _))
    _ = (ε₀ + (nPriv l : ℝ) * (4 * ζ)) * ‖ψ‖ := by ring

end Native

end

end SparseHamiltonian.GateNative
