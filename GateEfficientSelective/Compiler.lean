import GateEfficientSynthesis.Hamiltonian
import GateEfficientSynthesisTrials.Kinds

/-!
# Selective synthesis over a finite gate set

The finite-gate-set compiler of `GateEfficientSynthesis` (`GateSynth.synthC`) synthesises every
elementary gate of a native circuit, including the gates of circuits that are already
implemented over the gate set (a supplied private operation or source circuit). Equations
`hs:eq:gate-total`, `ode:eq:gate-main` and `ode:eq:gate-space` of the accompanying paper charge
such circuits by their own gate count over the finite gate set. This file adds the compiler
that does so: in a native circuit (elementary gates and primitive calls, `GateNative.NInstr`)

* every gate that is already a gate of the finite gate set `𝒢` (`GateOf 𝒢`) is kept verbatim
  on the circuit wires (`keepB`; a supplied circuit over `𝒢` is retained unchanged,
  `selC_retained`);
* every other elementary gate is synthesised at accuracy `ζ` under the released synthesis
  hypothesis `GateSynth.Synthesis 𝒢 X L` (`synB`), on one reused register `X` of clean
  synthesis ancillas;
* every primitive call is kept, so the calls of every oracle are exactly preserved.

`nSynN 𝒢 C` counts the synthesised gate occurrences, `nKeepN 𝒢 C` the kept ones
(`nKeepN_add_nSynN`: together the gates of `C`).

* `selC_spec`: valid instructions, every gate a gate of `𝒢`, at most `nKeepN C + nSynN C · L ζ`
  gates, exactly the calls of `C`.
* `selC_approxOn`: for unitary primitive oracles and every payload, the compiled circuit is
  within `nSynN C · ζ` of `C` in the full-output convention on clean synthesis ancillas
  (`ApproxOn CleanX`, residues and phases included). Only the synthesised gates contribute; the
  error of a supplied circuit against its ideal operation is a separate hypothesis of the
  algorithm that uses it.
* `selBudget hS δ C = selC hS (δ/(K+1)) C` with `K = nSynN C`: error at most `δ`
  (`selBudget_approxOn`), at most `nKeepN C + K L(δ/(K+1))` gates (`selBudget_spec`), and, with
  `L ζ ≤ c₁ log(1/ζ) + c₀`, at most `nKeepN C + K' (c₁ log((K'+1)/δ) + c₀)` gates for every
  `K' ≥ K` (`selBudget_gates_log`): the kept gates stay outside the synthesis logarithm.
* `selC_append`, `selC_retained`: the compiler acts instruction by instruction, and leaves a
  circuit all of whose gates are in `𝒢` unchanged (renamed to the circuit wires).
* Adjoints: for an adjoint-closed gate set (`GateSynthTrials.AdjClosed`) the literal inverse of
  the compiled circuit is a circuit over `𝒢` (`selC_inv_gateOf`), and the literal inverse of a
  circuit has the same synthesised and kept counts (`nSynN_ninv`, `nKeepN_ninv`).
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateSelective

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit GateNative GateSynth GateSynthTrials
open scoped InnerProduct

/-! ### Kept and synthesised gates -/

section Count

variable {V V' Y J : Type*} (𝒢 : Set Kind)

open Classical in
/-- An elementary gate that is not a gate of `𝒢`: the compiler synthesises it. -/
def synB : NInstr V Y J → Bool
  | .gate g => !decide (GateOf 𝒢 g)
  | .call _ _ _ => false

open Classical in
/-- An elementary gate of `𝒢`: the compiler keeps it. -/
def keepB : NInstr V Y J → Bool
  | .gate g => decide (GateOf 𝒢 g)
  | .call _ _ _ => false

/-- The synthesised gate occurrences of a circuit: its gates that are not gates of `𝒢`. -/
def nSynN (C : List (NInstr V Y J)) : ℕ := C.countP (synB 𝒢)

/-- The kept gate occurrences of a circuit: its gates of `𝒢`. -/
def nKeepN (C : List (NInstr V Y J)) : ℕ := C.countP (keepB 𝒢)

theorem synB_gate (g : Gate V) :
    (synB 𝒢 (NInstr.gate g : NInstr V Y J) = true) ↔ ¬ GateOf 𝒢 g := by
  classical
  simp [synB]

theorem keepB_gate (g : Gate V) :
    (keepB 𝒢 (NInstr.gate g : NInstr V Y J) = true) ↔ GateOf 𝒢 g := by
  classical
  simp [keepB]

theorem nSynN_nil : nSynN 𝒢 ([] : List (NInstr V Y J)) = 0 := rfl

theorem nKeepN_nil : nKeepN 𝒢 ([] : List (NInstr V Y J)) = 0 := rfl

theorem nSynN_append (C D : List (NInstr V Y J)) :
    nSynN 𝒢 (C ++ D) = nSynN 𝒢 C + nSynN 𝒢 D := List.countP_append ..

theorem nKeepN_append (C D : List (NInstr V Y J)) :
    nKeepN 𝒢 (C ++ D) = nKeepN 𝒢 C + nKeepN 𝒢 D := List.countP_append ..

open Classical in
theorem nSynN_cons_gate (g : Gate V) (C : List (NInstr V Y J)) :
    nSynN 𝒢 (NInstr.gate g :: C) = nSynN 𝒢 C + (if GateOf 𝒢 g then 0 else 1) := by
  classical
  unfold nSynN
  rw [List.countP_cons]
  by_cases h : GateOf 𝒢 g <;> simp [synB, h]

open Classical in
theorem nKeepN_cons_gate (g : Gate V) (C : List (NInstr V Y J)) :
    nKeepN 𝒢 (NInstr.gate g :: C) = nKeepN 𝒢 C + (if GateOf 𝒢 g then 1 else 0) := by
  classical
  unfold nKeepN
  rw [List.countP_cons]
  by_cases h : GateOf 𝒢 g <;> simp [keepB, h]

theorem nSynN_cons_call (j : J) (adj : Bool) (pos : Y ↪ V) (C : List (NInstr V Y J)) :
    nSynN 𝒢 (NInstr.call j adj pos :: C) = nSynN 𝒢 C := by
  unfold nSynN
  rw [List.countP_cons]
  simp [synB]

theorem nKeepN_cons_call (j : J) (adj : Bool) (pos : Y ↪ V) (C : List (NInstr V Y J)) :
    nKeepN 𝒢 (NInstr.call j adj pos :: C) = nKeepN 𝒢 C := by
  unfold nKeepN
  rw [List.countP_cons]
  simp [keepB]

/-- **Kept and synthesised gates are all the gates.** -/
theorem nKeepN_add_nSynN (C : List (NInstr V Y J)) :
    nKeepN 𝒢 C + nSynN 𝒢 C = nGatesN C := by
  induction C with
  | nil => rfl
  | cons i C ih =>
      cases i with
      | gate g =>
          rw [nKeepN_cons_gate, nSynN_cons_gate]
          have e : nGatesN (NInstr.gate g :: C : List (NInstr V Y J)) = nGatesN C + 1 := by
            simp [nGatesN, NInstr.isGate]
          rw [e, ← ih]
          split_ifs <;> omega
      | call j adj pos =>
          rw [nKeepN_cons_call, nSynN_cons_call]
          have e : nGatesN (NInstr.call j adj pos :: C : List (NInstr V Y J)) = nGatesN C := by
            simp [nGatesN, NInstr.isGate]
          rw [e, ih]

theorem nSynN_le (C : List (NInstr V Y J)) : nSynN 𝒢 C ≤ nGatesN C := by
  rw [← nKeepN_add_nSynN 𝒢 C]
  omega

theorem nKeepN_le (C : List (NInstr V Y J)) : nKeepN 𝒢 C ≤ nGatesN C := by
  rw [← nKeepN_add_nSynN 𝒢 C]
  omega

/-- **A circuit over `𝒢` has no synthesised gate.** -/
theorem nSynN_eq_zero (C : List (NInstr V Y J)) (h : ∀ g, NInstr.gate g ∈ C → GateOf 𝒢 g) :
    nSynN 𝒢 C = 0 := by
  induction C with
  | nil => rfl
  | cons i C ih =>
      have h' : ∀ g, NInstr.gate g ∈ C → GateOf 𝒢 g :=
        fun g hg => h g (List.mem_cons_of_mem _ hg)
      cases i with
      | gate g =>
          rw [nSynN_cons_gate, ih h', if_pos (h g List.mem_cons_self)]
      | call j adj pos => rw [nSynN_cons_call, ih h']

/-- A circuit over `𝒢` keeps all its gates. -/
theorem nKeepN_eq (C : List (NInstr V Y J)) (h : ∀ g, NInstr.gate g ∈ C → GateOf 𝒢 g) :
    nKeepN 𝒢 C = nGatesN C := by
  have := nKeepN_add_nSynN 𝒢 C
  rw [nSynN_eq_zero 𝒢 C h] at this
  omega

theorem nSynN_flatMap {α : Type*} (f : α → List (NInstr V Y J)) (l : List α) :
    nSynN 𝒢 (l.flatMap f) = (l.map (fun a => nSynN 𝒢 (f a))).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.flatMap_cons, nSynN_append, ih, List.map_cons, List.sum_cons]

theorem nKeepN_flatMap {α : Type*} (f : α → List (NInstr V Y J)) (l : List α) :
    nKeepN 𝒢 (l.flatMap f) = (l.map (fun a => nKeepN 𝒢 (f a))).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.flatMap_cons, nKeepN_append, ih, List.map_cons, List.sum_cons]

/-- Renaming the wires along an embedding: a gate of `𝒢` exactly when the gate is. -/
theorem gateOf_map_iff (f : V ↪ V') (g : Gate V) :
    GateOf 𝒢 (GateODE.Gate.map f g) ↔ GateOf 𝒢 g := by
  refine ⟨fun h => ⟨?_, by rw [← kind_map f]; exact h.2⟩, GateOf.map f⟩
  have e : ((GateODE.Gate.map f g).cs.map Prod.fst) = (g.cs.map Prod.fst).map f := by
    simp [GateODE.Gate.map, List.map_map, Function.comp_def]
  have h1 := h.1
  rw [e] at h1
  exact h1.of_map f

theorem nSynN_map (f : V ↪ V') (C : List (NInstr V Y J)) :
    nSynN 𝒢 (C.map (NInstr.map f)) = nSynN 𝒢 C := by
  induction C with
  | nil => rfl
  | cons i C ih =>
      cases i with
      | gate g =>
          rw [List.map_cons]
          show nSynN 𝒢 (NInstr.gate (GateODE.Gate.map f g) :: C.map (NInstr.map f)) = _
          rw [nSynN_cons_gate, nSynN_cons_gate, ih, gateOf_map_iff]
      | call j adj pos =>
          rw [List.map_cons]
          show nSynN 𝒢 (NInstr.call j adj (pos.trans f) :: C.map (NInstr.map f)) = _
          rw [nSynN_cons_call, nSynN_cons_call, ih]

theorem nKeepN_map (f : V ↪ V') (C : List (NInstr V Y J)) :
    nKeepN 𝒢 (C.map (NInstr.map f)) = nKeepN 𝒢 C := by
  have h1 := nKeepN_add_nSynN 𝒢 (C.map (NInstr.map f))
  have h2 := nKeepN_add_nSynN 𝒢 C
  rw [nSynN_map, nGatesN_map] at h1
  omega

/-- For an adjoint-closed gate set, the literal inverse of a gate is a gate of `𝒢` exactly when
the gate is. -/
theorem gateOf_inv_iff (hadj : AdjClosed 𝒢) (g : Gate V) :
    GateOf 𝒢 (⟨g.cs, g.t, g.u.conjTranspose⟩ : Gate V) ↔ GateOf 𝒢 g := by
  refine ⟨fun h => ?_, GateOf.inv hadj⟩
  have h2 := GateOf.inv hadj h
  simpa [Matrix.conjTranspose_conjTranspose] using h2

theorem nSynN_cons_inv (hadj : AdjClosed 𝒢) (i : NInstr V Y J) (C : List (NInstr V Y J)) :
    nSynN 𝒢 (i.inv :: C) = nSynN 𝒢 (i :: C) := by
  cases i with
  | gate g =>
      show nSynN 𝒢 (NInstr.gate ⟨g.cs, g.t, g.u.conjTranspose⟩ :: C) = _
      rw [nSynN_cons_gate, nSynN_cons_gate, gateOf_inv_iff 𝒢 hadj]
  | call j adj pos =>
      show nSynN 𝒢 (NInstr.call j (!adj) pos :: C) = _
      rw [nSynN_cons_call, nSynN_cons_call]

/-- **The literal inverse has the same synthesised gates**, for an adjoint-closed gate set. -/
theorem nSynN_ninv (hadj : AdjClosed 𝒢) (C : List (NInstr V Y J)) :
    nSynN 𝒢 (ninv C) = nSynN 𝒢 C := by
  induction C with
  | nil => rfl
  | cons i C ih =>
      have e : ninv (i :: C) = ninv C ++ [i.inv] := by
        simp [ninv]
      rw [e, nSynN_append, ih]
      have h1 := nSynN_cons_inv 𝒢 hadj i []
      have h2 : nSynN 𝒢 (i :: C) = nSynN 𝒢 [i] + nSynN 𝒢 C := by
        rw [show (i :: C) = [i] ++ C from rfl, nSynN_append]
      rw [h2, ← h1]
      omega

theorem nKeepN_ninv (hadj : AdjClosed 𝒢) (C : List (NInstr V Y J)) :
    nKeepN 𝒢 (ninv C) = nKeepN 𝒢 C := by
  have h1 := nKeepN_add_nSynN 𝒢 (ninv C)
  have h2 := nKeepN_add_nSynN 𝒢 C
  rw [nSynN_ninv 𝒢 hadj, nGatesN_ninv] at h1
  omega

theorem nSynN_nGatesOf (gs : List (Gate V)) :
    nSynN 𝒢 (nGatesOf gs : List (NInstr V Y J)) ≤ gs.length := by
  have h := nSynN_le 𝒢 (nGatesOf gs : List (NInstr V Y J))
  rwa [nGatesN_nGatesOf] at h

end Count

/-! ### The compiler -/

section Compiler

variable {V Y J X : Type*} [Fintype V] [DecidableEq V] [Fintype Y] [DecidableEq Y]
  [Fintype X] [DecidableEq X]
variable {𝒢 : Set Kind} {L : ℝ → ℕ}

open Classical in
/-- **The selective replacement of one gate**: a gate of `𝒢` is kept on the circuit wires;
every other gate is synthesised at accuracy `ζ` (`GateSynth.synthRep`). -/
def selRep (hS : Synthesis 𝒢 X L) (ζ : ℝ) (g : Gate V) : List (Gate (V ⊕ X)) :=
  if GateOf 𝒢 g then [GateODE.Gate.map Sum.inl g] else synthRep hS ζ g

/-- **The selectively compiled circuit**: the gates of `𝒢` kept, the other gates synthesised at
accuracy `ζ`, every primitive call kept. It depends only on the circuit. -/
def selC (hS : Synthesis 𝒢 X L) (ζ : ℝ) (C : List (NInstr V Y J)) :
    List (NInstr (V ⊕ X) Y J) :=
  replace (selRep hS ζ) C

omit [Fintype Y] [DecidableEq Y] in
theorem selRep_kept (hS : Synthesis 𝒢 X L) (ζ : ℝ) (g : Gate V) (h : GateOf 𝒢 g) :
    selRep hS ζ g = [GateODE.Gate.map Sum.inl g] := by
  classical
  simp [selRep, h]

omit [Fintype Y] [DecidableEq Y] in
theorem selRep_synth (hS : Synthesis 𝒢 X L) (ζ : ℝ) (g : Gate V) (h : ¬ GateOf 𝒢 g) :
    selRep hS ζ g = synthRep hS ζ g := by
  classical
  simp [selRep, h]

omit [Fintype Y] [DecidableEq Y] in
open Classical in
/-- The replacement of one gate: valid gates of `𝒢`, at most one gate for a kept gate and at
most `L ζ` otherwise. -/
theorem selRep_spec (hS : Synthesis 𝒢 X L) {ζ : ℝ} (hζ : 0 < ζ) (g : Gate V)
    (hg : GateOK 3 g) :
    (∀ h ∈ selRep hS ζ g, GateOK 3 h ∧ GateOf 𝒢 h) ∧
      (selRep hS ζ g).length ≤ (if GateOf 𝒢 g then 1 else L ζ) := by
  by_cases hG : GateOf 𝒢 g
  · rw [selRep_kept hS ζ g hG, if_pos hG]
    refine ⟨fun h hh => ?_, by simp⟩
    simp only [List.mem_singleton] at hh
    subst hh
    exact ⟨NInstr.valid_map inlE (NInstr.gate g : NInstr V Empty Empty) hg, GateOf.map inlE hG⟩
  · rw [selRep_synth hS ζ g hG, if_neg hG]
    obtain ⟨h1, h2, -⟩ := synthRep_spec hS hζ g hg
    exact ⟨h1, h2⟩

variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

omit [Fintype Y] [DecidableEq Y] in
open Classical in
/-- The replacement of one gate is within `0` (a kept gate) or `ζ` (a synthesised gate) of the
lifted gate on clean ancillas, for every payload. -/
theorem selRep_approxOn (hS : Synthesis 𝒢 X L) {ζ : ℝ} (hζ : 0 < ζ) (g : Gate V)
    (hg : GateOK 3 g) :
    ApproxOn (Q := R) CleanX (gRun (selRep hS ζ g)) (liftB (X := X) (Gate.op g))
      (if GateOf 𝒢 g then 0 else ζ) := by
  by_cases hG : GateOf 𝒢 g
  · rw [selRep_kept hS ζ g hG, if_pos hG, ← liftB_op_eq]
    exact ApproxOn.of_agrees (fun _ _ => rfl)
  · rw [selRep_synth hS ζ g hG, if_neg hG]
    have hsp := synthRep_spec hS hζ g hg
    exact approxOn_rep g hg _ (fun h hh => (hsp.1 h hh).1) hζ.le hsp.2.2

omit [Fintype V] [DecidableEq V] [Fintype Y] [DecidableEq Y] [Fintype X] [DecidableEq X] in
theorem replace_append (rep : Gate V → List (Gate (V ⊕ X))) (C D : List (NInstr V Y J)) :
    replace rep (C ++ D) = replace rep C ++ replace rep D := by
  induction C with
  | nil => rfl
  | cons i C ih =>
      cases i with
      | gate g => simp only [List.cons_append, replace, ih, List.append_assoc]
      | call j adj pos => simp only [List.cons_append, replace, ih]

omit [Fintype Y] [DecidableEq Y] in
/-- **The compiler acts instruction by instruction.** -/
theorem selC_append (hS : Synthesis 𝒢 X L) (ζ : ℝ) (C D : List (NInstr V Y J)) :
    selC hS ζ (C ++ D) = selC hS ζ C ++ selC hS ζ D :=
  replace_append _ C D

omit [Fintype Y] [DecidableEq Y] in
/-- **A supplied circuit over `𝒢` is retained verbatim**, renamed to the circuit wires. -/
theorem selC_retained (hS : Synthesis 𝒢 X L) (ζ : ℝ) (D : List (NInstr V Y J))
    (hD : ∀ g, NInstr.gate g ∈ D → GateOf 𝒢 g) :
    selC hS ζ D = D.map (NInstr.map inlE) := by
  induction D with
  | nil => rfl
  | cons i D ih =>
      have hD' : ∀ g, NInstr.gate g ∈ D → GateOf 𝒢 g :=
        fun g hg => hD g (List.mem_cons_of_mem _ hg)
      cases i with
      | gate g =>
          have h := selRep_kept hS ζ g (hD g List.mem_cons_self)
          show replace (selRep hS ζ) (NInstr.gate g :: D) = _
          rw [replace, h, ← selC, ih hD']
          rfl
      | call j adj pos =>
          show replace (selRep hS ζ) (NInstr.call j adj pos :: D) = _
          rw [replace, ← selC, ih hD']
          rfl

omit [Fintype Y] [DecidableEq Y] in
/-- Every gate of the compiled circuit comes from the replacement of a gate of the circuit. -/
theorem mem_selC_gate (hS : Synthesis 𝒢 X L) (ζ : ℝ) (C : List (NInstr V Y J))
    (h : Gate (V ⊕ X)) (hh : NInstr.gate h ∈ selC hS ζ C) :
    ∃ g, NInstr.gate g ∈ C ∧ h ∈ selRep hS ζ g :=
  mem_replace_gate _ C h hh

omit [Fintype Y] [DecidableEq Y] in
theorem nGatesN_selC_le (hS : Synthesis 𝒢 X L) {ζ : ℝ} (hζ : 0 < ζ) (C : List (NInstr V Y J))
    (hC : ∀ i ∈ C, i.Valid) :
    nGatesN (selC hS ζ C) ≤ nKeepN 𝒢 C + nSynN 𝒢 C * L ζ := by
  induction C with
  | nil => simp [selC, replace, nGatesN, nKeepN, nSynN]
  | cons i C ih =>
      have hC' : ∀ i ∈ C, i.Valid := fun i hi => hC i (List.mem_cons_of_mem _ hi)
      have ih' := ih hC'
      cases i with
      | gate g =>
          have hg : GateOK 3 g := hC _ List.mem_cons_self
          have hl := (selRep_spec hS hζ g hg).2
          have e : nGatesN (selC hS ζ (NInstr.gate g :: C)) =
              (selRep hS ζ g).length + nGatesN (selC hS ζ C) := by
            show nGatesN (replace (selRep hS ζ) (NInstr.gate g :: C)) = _
            rw [replace, nGatesN_append, nGatesN_nGatesOf, ← selC]
          rw [e, nKeepN_cons_gate, nSynN_cons_gate]
          split_ifs at hl ⊢ with hG
          · nlinarith
          · rw [add_mul, one_mul]
            nlinarith
      | call j adj pos =>
          have e : nGatesN (selC hS ζ (NInstr.call j adj pos :: C)) = nGatesN (selC hS ζ C) := by
            show nGatesN (replace (selRep hS ζ) (NInstr.call j adj pos :: C)) = _
            simp [replace, nGatesN, NInstr.isGate, selC]
          rw [e, nKeepN_cons_call, nSynN_cons_call]
          exact ih'

omit [Fintype Y] [DecidableEq Y] in
/-- **Validity and counts of the selectively compiled circuit**: valid instructions, every gate
a gate of `𝒢`, at most `nKeepN C + nSynN C · L ζ` gates, and exactly the calls of `C`. -/
theorem selC_spec (hS : Synthesis 𝒢 X L) {ζ : ℝ} (hζ : 0 < ζ) (C : List (NInstr V Y J))
    (hC : ∀ i ∈ C, i.Valid) :
    (∀ i ∈ selC hS ζ C, i.Valid) ∧ (∀ g, NInstr.gate g ∈ selC hS ζ C → GateOf 𝒢 g) ∧
      nGatesN (selC hS ζ C) ≤ nKeepN 𝒢 C + nSynN 𝒢 C * L ζ ∧
      ∀ p : J → Bool, nCallsN p (selC hS ζ C) = nCallsN p C := by
  have hgv : ∀ g, NInstr.gate g ∈ C → GateOK 3 g := fun g hg => hC _ hg
  refine ⟨replace_valid _ C hC (fun g hg h hh =>
      ((selRep_spec hS hζ g (hgv g hg)).1 h hh).1), ?_,
    nGatesN_selC_le hS hζ C hC, fun p => nCallsN_replace _ p C⟩
  intro h hh
  obtain ⟨g, hg, hh'⟩ := mem_selC_gate hS ζ C h hh
  exact ((selRep_spec hS hζ g (hgv g hg)).1 h hh').2

variable (prim : J → Reg Y R →L[ℂ] Reg Y R)

open Classical in
/-- **The selectively compiled circuit approximates the circuit** within `nSynN C · ζ` on clean
synthesis ancillas, for every payload: only the synthesised gates contribute. -/
theorem selC_approxOn (hS : Synthesis 𝒢 X L) {ζ : ℝ} (hζ : 0 < ζ) (C : List (NInstr V Y J))
    (hC : ∀ i ∈ C, i.Valid) (hprim : ∀ j, IsUnitary (prim j)) :
    ApproxOn CleanX (nrun prim (selC hS ζ C)) (liftB (X := X) (nrun prim C))
      (nSynN 𝒢 C * ζ) := by
  induction C with
  | nil =>
      show ApproxOn CleanX (nrun prim (replace (selRep hS ζ) [])) _ _
      rw [replace, nrun_nil, nrun_nil, liftB_one]
      simp only [nSynN_nil, Nat.cast_zero, zero_mul]
      exact ApproxOn.of_agrees (fun ψ _ => rfl)
  | cons i is ih =>
      have hC' : ∀ i ∈ is, i.Valid := fun i hi => hC i (List.mem_cons_of_mem _ hi)
      have hI := ih hC'
      have hU : IsUnitary (nrun prim (selC hS ζ is)) :=
        nrun_isUnitary prim hprim _ (selC_spec hS hζ is hC').1
      have hi : IsUnitary (liftB (X := X) (i.eval prim)) :=
        liftB_isUnitary (NInstr.eval_isUnitary prim hprim i (hC i List.mem_cons_self))
      have hδ : 0 ≤ (nSynN 𝒢 is : ℝ) * ζ := mul_nonneg (Nat.cast_nonneg _) hζ.le
      rw [nrun_cons, liftB_comp]
      cases i with
      | gate g =>
          have hg : GateOK 3 g := hC _ List.mem_cons_self
          have e : (nSynN 𝒢 (NInstr.gate g :: is) : ℝ) * ζ =
              (if GateOf 𝒢 g then 0 else ζ) + nSynN 𝒢 is * ζ := by
            rw [nSynN_cons_gate]
            split_ifs <;> push_cast <;> ring
          have e2 : selC hS ζ (NInstr.gate g :: is) =
              nGatesOf (selRep hS ζ g) ++ selC hS ζ is := rfl
          rw [e2, nrun_append, nrun_nGatesOf, e]
          exact ApproxOn.comp (selRep_approxOn hS hζ g hg) (preserves_liftB _)
            (fun ψ => IsUnitary.norm_apply_le hi ψ) hI (fun ψ => IsUnitary.norm_apply_le hU ψ) hδ
      | call j adj pos =>
          have e : (nSynN 𝒢 (NInstr.call j adj pos :: is) : ℝ) * ζ = 0 + nSynN 𝒢 is * ζ := by
            rw [nSynN_cons_call, zero_add]
          have e2 : selC hS ζ (NInstr.call j adj pos :: is) =
              NInstr.call j adj (pos.trans inlE) :: selC hS ζ is := rfl
          rw [e2, nrun_cons, eval_call_inlE, e]
          exact ApproxOn.comp (ApproxOn.of_agrees (fun ψ _ => rfl)) (preserves_liftB _)
            (fun ψ => IsUnitary.norm_apply_le hi ψ) hI (fun ψ => IsUnitary.norm_apply_le hU ψ) hδ

/-- **The full-output error of the selectively compiled circuit**: along every contractive
embedding `E`, the compilation adds at most `nSynN C · ζ`. -/
theorem selC_error (hS : Synthesis 𝒢 X L) {ζ : ℝ} (hζ : 0 < ζ) (C : List (NInstr V Y J))
    (hC : ∀ i ∈ C, i.Valid) (hprim : ∀ j, IsUnitary (prim j)) {S : Type*} [Fintype S]
    [DecidableEq S] (E : Reg S R →L[ℂ] Reg V R) (hE : ∀ p, ‖E p‖ ≤ ‖p‖)
    (U : Reg S R →L[ℂ] Reg S R) :
    ‖nrun prim (selC hS ζ C) ∘L (cleanEmb (X := X) ∘L E) - (cleanEmb ∘L E) ∘L U‖ ≤
      ‖nrun prim C ∘L E - E ∘L U‖ + nSynN 𝒢 C * ζ := by
  have hδ : 0 ≤ (nSynN 𝒢 C : ℝ) * ζ := mul_nonneg (Nat.cast_nonneg _) hζ.le
  have h1 := norm_sub_cleanEmb_le (selC_approxOn prim hS hζ C hC hprim) hδ
  have hEn : ‖E‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun p => by rw [one_mul]; exact hE p)
  have hcn : ‖(cleanEmb (X := X) : Reg V R →L[ℂ] Reg (V ⊕ X) R)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      (fun ψ => by rw [one_mul, norm_cleanEmb])
  have e : nrun prim (selC hS ζ C) ∘L (cleanEmb (X := X) ∘L E) - (cleanEmb ∘L E) ∘L U =
      (nrun prim (selC hS ζ C) ∘L cleanEmb - cleanEmb ∘L nrun prim C) ∘L E +
        cleanEmb ∘L (nrun prim C ∘L E - E ∘L U) := by
    ext p
    simp only [sub_apply, comp_apply, add_apply, map_sub]
    exact (sub_add_sub_cancel _ _ _).symm
  rw [e]
  calc ‖(nrun prim (selC hS ζ C) ∘L cleanEmb - cleanEmb ∘L nrun prim C) ∘L E +
        cleanEmb (X := X) ∘L (nrun prim C ∘L E - E ∘L U)‖
      ≤ ‖nrun prim (selC hS ζ C) ∘L cleanEmb - cleanEmb ∘L nrun prim C‖ * ‖E‖ +
          ‖(cleanEmb (X := X) : Reg V R →L[ℂ] Reg (V ⊕ X) R)‖ *
            ‖nrun prim C ∘L E - E ∘L U‖ :=
        (norm_add_le _ _).trans (add_le_add (opNorm_comp_le _ _) (opNorm_comp_le _ _))
    _ ≤ (nSynN 𝒢 C * ζ) * 1 + 1 * ‖nrun prim C ∘L E - E ∘L U‖ := by
        gcongr
    _ = ‖nrun prim C ∘L E - E ∘L U‖ + nSynN 𝒢 C * ζ := by ring

end Compiler

/-! ### The synthesis budget -/

section Budget

variable {V Y J X : Type*} [Fintype V] [DecidableEq V] [Fintype Y] [DecidableEq Y]
  [Fintype X] [DecidableEq X]
variable {𝒢 : Set Kind} {L : ℝ → ℕ}

/-- **The selective compilation with the synthesis budget `δ`**, spent over the `K = nSynN C`
synthesised gate occurrences: accuracy `δ/(K+1)` per synthesised gate. -/
def selBudget (hS : Synthesis 𝒢 X L) (δ : ℝ) (C : List (NInstr V Y J)) :
    List (NInstr (V ⊕ X) Y J) :=
  selC hS (δ / (nSynN 𝒢 C + 1)) C

omit [Fintype Y] [DecidableEq Y] in
theorem selBudget_spec (hS : Synthesis 𝒢 X L) {δ : ℝ} (hδ : 0 < δ) (C : List (NInstr V Y J))
    (hC : ∀ i ∈ C, i.Valid) :
    (∀ i ∈ selBudget hS δ C, i.Valid) ∧ (∀ g, NInstr.gate g ∈ selBudget hS δ C → GateOf 𝒢 g) ∧
      nGatesN (selBudget hS δ C) ≤ nKeepN 𝒢 C + nSynN 𝒢 C * L (δ / (nSynN 𝒢 C + 1)) ∧
      ∀ p : J → Bool, nCallsN p (selBudget hS δ C) = nCallsN p C :=
  selC_spec hS (div_pos hδ (by positivity)) C hC

variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
variable (prim : J → Reg Y R →L[ℂ] Reg Y R)

/-- **The selective compilation adds at most the budget `δ`.** -/
theorem selBudget_approxOn (hS : Synthesis 𝒢 X L) {δ : ℝ} (hδ : 0 < δ)
    (C : List (NInstr V Y J)) (hC : ∀ i ∈ C, i.Valid) (hprim : ∀ j, IsUnitary (prim j)) :
    ApproxOn CleanX (nrun prim (selBudget hS δ C)) (liftB (X := X) (nrun prim C)) δ := by
  have hN : (0 : ℝ) < nSynN 𝒢 C + 1 := by positivity
  refine (selC_approxOn prim hS (div_pos hδ hN) C hC hprim).mono ?_
  rw [mul_div_assoc', div_le_iff₀ hN]
  nlinarith

theorem selBudget_error (hS : Synthesis 𝒢 X L) {δ : ℝ} (hδ : 0 < δ) (C : List (NInstr V Y J))
    (hC : ∀ i ∈ C, i.Valid) (hprim : ∀ j, IsUnitary (prim j)) {S : Type*} [Fintype S]
    [DecidableEq S] (E : Reg S R →L[ℂ] Reg V R) (hE : ∀ p, ‖E p‖ ≤ ‖p‖)
    (U : Reg S R →L[ℂ] Reg S R) :
    ‖nrun prim (selBudget hS δ C) ∘L (cleanEmb (X := X) ∘L E) - (cleanEmb ∘L E) ∘L U‖ ≤
      ‖nrun prim C ∘L E - E ∘L U‖ + δ := by
  have hN : (0 : ℝ) < nSynN 𝒢 C + 1 := by positivity
  refine (selC_error prim hS (div_pos hδ hN) C hC hprim E hE U).trans ?_
  have : (nSynN 𝒢 C : ℝ) * (δ / (nSynN 𝒢 C + 1)) ≤ δ := by
    rw [mul_div_assoc', div_le_iff₀ hN]
    nlinarith
  linarith

omit [Fintype Y] [DecidableEq Y] [CompleteSpace R] in
/-- **The gate count in closed form**: with `L ζ ≤ c₁ log(1/ζ) + c₀` on `(0, 1]` and
`0 < δ ≤ 1`, the compiled circuit has at most `nKeepN C + K (c₁ log((K+1)/δ) + c₀)` gates for
every `K ≥ nSynN C`: the kept gates are outside the synthesis logarithm. -/
theorem selBudget_gates_log (hS : Synthesis 𝒢 X L) {c₀ c₁ : ℝ} (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁)
    (hL : ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 → (L ζ : ℝ) ≤ c₁ * Real.log (1 / ζ) + c₀) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (C : List (NInstr V Y J)) (hC : ∀ i ∈ C, i.Valid) (K : ℝ)
    (hK : (nSynN 𝒢 C : ℝ) ≤ K) :
    (nGatesN (selBudget hS δ C) : ℝ) ≤ nKeepN 𝒢 C + K * (c₁ * Real.log ((K + 1) / δ) + c₀) := by
  have h1 := (selBudget_spec hS hδ C hC).2.2.1
  have h2 := gates_log_le hc₀ hc₁ hL hδ hδ1 (nSynN 𝒢 C) K hK
  have h3 : (nGatesN (selBudget hS δ C) : ℝ) ≤
      (nKeepN 𝒢 C : ℝ) + ((nSynN 𝒢 C * L (δ / (nSynN 𝒢 C + 1)) : ℕ) : ℝ) := by
    exact_mod_cast h1
  linarith

end Budget

/-! ### Adjoints -/

section Adjoint

variable {V Y J X : Type*} [Fintype V] [DecidableEq V] [Fintype Y] [DecidableEq Y]
  [Fintype X] [DecidableEq X]
variable {𝒢 : Set Kind} {L : ℝ → ℕ}

omit [Fintype Y] [DecidableEq Y] in
/-- **The literal inverse of a circuit over an adjoint-closed gate set is a circuit over it.** -/
theorem ninv_gateOf (hadj : AdjClosed 𝒢) {W : Type*} (C : List (NInstr W Y J))
    (hC : ∀ g, NInstr.gate g ∈ C → GateOf 𝒢 g) :
    ∀ g, NInstr.gate g ∈ ninv C → GateOf 𝒢 g := by
  intro g hg
  simp only [ninv, List.mem_reverse, List.mem_map] at hg
  obtain ⟨i, hi, he⟩ := hg
  cases i with
  | gate h =>
      simp only [NInstr.inv, NInstr.gate.injEq] at he
      subst he
      exact GateOf.inv hadj (hC h hi)
  | call j adj pos => simp [NInstr.inv] at he

omit [Fintype Y] [DecidableEq Y] in
/-- **The actual inverse of the compiled circuit is a circuit over `𝒢`**, for an adjoint-closed
gate set. -/
theorem selC_inv_gateOf (hS : Synthesis 𝒢 X L) (hadj : AdjClosed 𝒢) {ζ : ℝ} (hζ : 0 < ζ)
    (C : List (NInstr V Y J)) (hC : ∀ i ∈ C, i.Valid) :
    ∀ g, NInstr.gate g ∈ ninv (selC hS ζ C) → GateOf 𝒢 g :=
  ninv_gateOf hadj _ (selC_spec hS hζ C hC).2.1

end Adjoint

end

end SparseHamiltonian.GateSelective
