import GateEfficientSynthesis.Place

/-!
# Synthesis of native circuits over a finite gate set

A native circuit (`GateNative.NInstr`) consists of elementary gates and calls of the primitive
oracles. Its synthesis replaces every elementary gate by a gate list on the circuit wires and the
clean ancilla wires `X`, and keeps every call on the circuit wires.

* `replace rep C`: the replacement by an arbitrary gate rule `rep`. If every gate of `C` is
  approximated within `η` by its replacement in the full-output convention (`ApproxOn CleanX`),
  then the whole circuit is approximated within `nGatesN C * η` (`approxOn_replace`): errors add
  along the circuit, and the calls and the ideal gates do not touch the ancillas.
* `synthC hS ζ C`: the replacement by the synthesis of every gate at accuracy `ζ` under
  `Synthesis 𝒢 X L` (`synthRep`). It depends only on the circuit, not on the payload or the
  primitive oracles. `synthC_spec`: valid instructions, every gate a gate of `𝒢`, at most
  `nGatesN C * L ζ` gates and exactly the calls of `C`. `synthC_approxOn`, `synthC_error`: for
  unitary primitive oracles and every payload, the full output on clean ancillas is within
  `nGatesN C * ζ` of that of `C`.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateSynth

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit GateNative
open scoped InnerProduct

section Replace

variable {V Y J X : Type*} [Fintype V] [DecidableEq V] [Fintype Y] [DecidableEq Y]
  [Fintype X] [DecidableEq X]

/-- The circuit wires among the wires with ancillas. -/
def inlE : V ↪ V ⊕ X := ⟨Sum.inl, Sum.inl_injective⟩

/-- **Gate replacement**: every elementary gate `g` replaced by the gate list `rep g`, every
call kept on the circuit wires. -/
def replace (rep : Gate V → List (Gate (V ⊕ X))) :
    List (NInstr V Y J) → List (NInstr (V ⊕ X) Y J)
  | [] => []
  | NInstr.gate g :: is => nGatesOf (rep g) ++ replace rep is
  | NInstr.call j adj pos :: is => NInstr.call j adj (pos.trans inlE) :: replace rep is

omit [Fintype V] [DecidableEq V] [Fintype Y] [DecidableEq Y] [Fintype X] [DecidableEq X] in
theorem replace_valid (rep : Gate V → List (Gate (V ⊕ X))) (C : List (NInstr V Y J))
    (hC : ∀ i ∈ C, i.Valid) (hrep : ∀ g, NInstr.gate g ∈ C → ∀ h ∈ rep g, GateOK 3 h) :
    ∀ i ∈ replace rep C, i.Valid := by
  induction C with
  | nil => simp [replace]
  | cons i is ih =>
      have hC' : ∀ i ∈ is, i.Valid := fun i hi => hC i (List.mem_cons_of_mem _ hi)
      have hrep' : ∀ g, NInstr.gate g ∈ is → ∀ h ∈ rep g, GateOK 3 h :=
        fun g hg => hrep g (List.mem_cons_of_mem _ hg)
      cases i with
      | gate g =>
          intro k hk
          simp only [replace, List.mem_append] at hk
          rcases hk with hk | hk
          · exact valid_nGatesOf _ (hrep g List.mem_cons_self) k hk
          · exact ih hC' hrep' k hk
      | call j adj pos =>
          intro k hk
          simp only [replace, List.mem_cons] at hk
          rcases hk with rfl | hk
          · trivial
          · exact ih hC' hrep' k hk

omit [Fintype V] [DecidableEq V] [Fintype Y] [DecidableEq Y] [Fintype X] [DecidableEq X] in
/-- Every gate of the replaced circuit comes from the replacement of a gate of the circuit. -/
theorem mem_replace_gate (rep : Gate V → List (Gate (V ⊕ X))) (C : List (NInstr V Y J))
    (h : Gate (V ⊕ X)) (hh : NInstr.gate h ∈ replace rep C) :
    ∃ g, NInstr.gate g ∈ C ∧ h ∈ rep g := by
  induction C with
  | nil => simp [replace] at hh
  | cons i is ih =>
      cases i with
      | gate g =>
          simp only [replace, List.mem_append, nGatesOf, List.mem_map, NInstr.gate.injEq,
            exists_eq_right] at hh
          rcases hh with hh | hh
          · exact ⟨g, List.mem_cons_self, hh⟩
          · obtain ⟨g', hg', hh'⟩ := ih hh
            exact ⟨g', List.mem_cons_of_mem _ hg', hh'⟩
      | call j adj pos =>
          simp only [replace, List.mem_cons, reduceCtorEq, false_or] at hh
          obtain ⟨g', hg', hh'⟩ := ih hh
          exact ⟨g', List.mem_cons_of_mem _ hg', hh'⟩

omit [Fintype V] [DecidableEq V] [Fintype Y] [DecidableEq Y] [Fintype X] [DecidableEq X] in
theorem nGatesN_replace_le (rep : Gate V → List (Gate (V ⊕ X))) (C : List (NInstr V Y J))
    (ℓ : ℕ) (h : ∀ g, NInstr.gate g ∈ C → (rep g).length ≤ ℓ) :
    nGatesN (replace rep C) ≤ nGatesN C * ℓ := by
  induction C with
  | nil => simp [replace, nGatesN]
  | cons i is ih =>
      have h' : ∀ g, NInstr.gate g ∈ is → (rep g).length ≤ ℓ :=
        fun g hg => h g (List.mem_cons_of_mem _ hg)
      cases i with
      | gate g =>
          have hg := h g List.mem_cons_self
          have e : nGatesN (NInstr.gate g :: is : List (NInstr V Y J)) = nGatesN is + 1 := by
            simp [nGatesN, NInstr.isGate]
          rw [replace, nGatesN_append, nGatesN_nGatesOf, e, add_mul, one_mul, add_comm]
          exact Nat.add_le_add (ih h') hg
      | call j adj pos =>
          have e : nGatesN (NInstr.call j adj pos :: is : List (NInstr V Y J)) = nGatesN is := by
            simp [nGatesN, NInstr.isGate]
          have e' : nGatesN (replace rep (NInstr.call j adj pos :: is)) =
              nGatesN (replace rep is) := by
            simp [replace, nGatesN, NInstr.isGate]
          rw [e', e]
          exact ih h'

omit [Fintype V] [DecidableEq V] [Fintype Y] [DecidableEq Y] [Fintype X] [DecidableEq X] in
theorem nCallsN_replace (rep : Gate V → List (Gate (V ⊕ X))) (p : J → Bool)
    (C : List (NInstr V Y J)) : nCallsN p (replace rep C) = nCallsN p C := by
  induction C with
  | nil => rfl
  | cons i is ih =>
      cases i with
      | gate g =>
          rw [replace, nCallsN_append, nCallsN_nGatesOf, ih, zero_add]
          simp [nCallsN, NInstr.isCall]
      | call j adj pos =>
          have e1 : nCallsN p (replace rep (NInstr.call j adj pos :: is)) =
              nCallsN p (replace rep is) + (if p j then 1 else 0) := by
            simp [replace, nCallsN, List.countP_cons, NInstr.isCall]
          have e2 : nCallsN p (NInstr.call j adj pos :: is : List (NInstr V Y J)) =
              nCallsN p is + (if p j then 1 else 0) := by
            simp [nCallsN, List.countP_cons, NInstr.isCall]
          rw [e1, e2, ih]

variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
variable (prim : J → Reg Y R →L[ℂ] Reg Y R)

/-- A call kept on the circuit wires acts as the original call, the identity on the
ancillas. -/
theorem eval_call_inlE (j : J) (adj : Bool) (pos : Y ↪ V) :
    (NInstr.call j adj (pos.trans inlE) : NInstr (V ⊕ X) Y J).eval prim =
      liftB (X := X) ((NInstr.call j adj pos : NInstr V Y J).eval prim) :=
  NInstr.eval_map prim inlE (NInstr.call j adj pos)

/-- **Errors add along a replaced circuit.** -/
theorem approxOn_replace (hprim : ∀ j, IsUnitary (prim j)) (rep : Gate V → List (Gate (V ⊕ X)))
    {η : ℝ} (hη : 0 ≤ η) (C : List (NInstr V Y J)) (hC : ∀ i ∈ C, i.Valid)
    (hrepV : ∀ g, NInstr.gate g ∈ C → ∀ h ∈ rep g, GateOK 3 h)
    (hrep : ∀ g, NInstr.gate g ∈ C →
      ApproxOn (Q := R) CleanX (gRun (rep g)) (liftB (X := X) (Gate.op g)) η) :
    ApproxOn CleanX (nrun prim (replace rep C)) (liftB (X := X) (nrun prim C))
      (nGatesN C * η) := by
  induction C with
  | nil =>
      rw [replace, nrun_nil, nrun_nil, liftB_one]
      simp only [nGatesN, List.countP_nil, Nat.cast_zero, zero_mul]
      exact ApproxOn.of_agrees (fun ψ _ => rfl)
  | cons i is ih =>
      have hC' : ∀ i ∈ is, i.Valid := fun i hi => hC i (List.mem_cons_of_mem _ hi)
      have hrepV' : ∀ g, NInstr.gate g ∈ is → ∀ h ∈ rep g, GateOK 3 h :=
        fun g hg => hrepV g (List.mem_cons_of_mem _ hg)
      have hrep' : ∀ g, NInstr.gate g ∈ is →
          ApproxOn (Q := R) CleanX (gRun (rep g)) (liftB (X := X) (Gate.op g)) η :=
        fun g hg => hrep g (List.mem_cons_of_mem _ hg)
      have hI := ih hC' hrepV' hrep'
      have hU : IsUnitary (nrun prim (replace rep is)) :=
        nrun_isUnitary prim hprim _ (replace_valid rep is hC' hrepV')
      have hi : IsUnitary (liftB (X := X) (i.eval prim)) :=
        liftB_isUnitary (NInstr.eval_isUnitary prim hprim i (hC i List.mem_cons_self))
      have hδ : 0 ≤ (nGatesN is : ℝ) * η := mul_nonneg (Nat.cast_nonneg _) hη
      rw [nrun_cons, liftB_comp]
      cases i with
      | gate g =>
          have e : (nGatesN (NInstr.gate g :: is : List (NInstr V Y J)) : ℝ) * η =
              η + nGatesN is * η := by
            simp only [nGatesN, List.countP_cons, NInstr.isGate, if_true, Nat.cast_add,
              Nat.cast_one]
            ring
          rw [replace, nrun_append, nrun_nGatesOf, e]
          exact ApproxOn.comp (hrep g List.mem_cons_self) (preserves_liftB _)
            (fun ψ => IsUnitary.norm_apply_le hi ψ) hI (fun ψ => IsUnitary.norm_apply_le hU ψ) hδ
      | call j adj pos =>
          have e : (nGatesN (NInstr.call j adj pos :: is : List (NInstr V Y J)) : ℝ) * η =
              0 + nGatesN is * η := by
            simp [nGatesN, NInstr.isGate]
          rw [replace, nrun_cons, eval_call_inlE, e]
          exact ApproxOn.comp (ApproxOn.of_agrees (fun ψ _ => rfl)) (preserves_liftB _)
            (fun ψ => IsUnitary.norm_apply_le hi ψ) hI (fun ψ => IsUnitary.norm_apply_le hU ψ) hδ

end Replace

/-! ### The synthesised circuit -/

section Synth

variable {V Y J X : Type*} [Fintype V] [DecidableEq V] [Fintype Y] [DecidableEq Y]
  [Fintype X] [DecidableEq X]
variable {𝒢 : Set Kind} {L : ℝ → ℕ}

/-- The synthesis of one gate at accuracy `ζ` (empty for an invalid gate or `ζ ≤ 0`). -/
def synthRep (hS : Synthesis 𝒢 X L) (ζ : ℝ) (g : Gate V) : List (Gate (V ⊕ X)) :=
  open Classical in
  if h : GateOK 3 g ∧ 0 < ζ then Classical.choose (exists_rep hS g h.1 h.2) else []

omit [Fintype Y] [DecidableEq Y] in
theorem synthRep_spec (hS : Synthesis 𝒢 X L) {ζ : ℝ} (hζ : 0 < ζ) (g : Gate V)
    (hg : GateOK 3 g) :
    (∀ h ∈ synthRep hS ζ g, GateOK 3 h ∧ GateOf 𝒢 h) ∧ (synthRep hS ζ g).length ≤ L ζ ∧
      ApproxOn (Q := ℂ) CleanX (gRun (synthRep hS ζ g)) (liftB (X := X) (Gate.op g)) ζ := by
  have h : GateOK 3 g ∧ 0 < ζ := ⟨hg, hζ⟩
  simp only [synthRep, dif_pos h]
  exact Classical.choose_spec (exists_rep hS g hg hζ)

/-- **The synthesised circuit**: every elementary gate synthesised at accuracy `ζ`, every call
kept. -/
def synthC (hS : Synthesis 𝒢 X L) (ζ : ℝ) (C : List (NInstr V Y J)) :
    List (NInstr (V ⊕ X) Y J) :=
  replace (synthRep hS ζ) C

omit [Fintype Y] [DecidableEq Y] in
/-- **Validity and counts of the synthesised circuit.** -/
theorem synthC_spec (hS : Synthesis 𝒢 X L) {ζ : ℝ} (hζ : 0 < ζ) (C : List (NInstr V Y J))
    (hC : ∀ i ∈ C, i.Valid) :
    (∀ i ∈ synthC hS ζ C, i.Valid) ∧ (∀ g, NInstr.gate g ∈ synthC hS ζ C → GateOf 𝒢 g) ∧
      nGatesN (synthC hS ζ C) ≤ nGatesN C * L ζ ∧
      ∀ p : J → Bool, nCallsN p (synthC hS ζ C) = nCallsN p C := by
  have hgv : ∀ g, NInstr.gate g ∈ C → GateOK 3 g := fun g hg => hC _ hg
  refine ⟨replace_valid _ C hC (fun g hg h hh => ((synthRep_spec hS hζ g (hgv g hg)).1 h hh).1),
    ?_, nGatesN_replace_le _ C _ (fun g hg => (synthRep_spec hS hζ g (hgv g hg)).2.1),
    fun p => nCallsN_replace _ p C⟩
  intro h hh
  obtain ⟨g, hg, hh'⟩ := mem_replace_gate _ C h hh
  exact ((synthRep_spec hS hζ g (hgv g hg)).1 h hh').2

variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
variable (prim : J → Reg Y R →L[ℂ] Reg Y R)

/-- **The synthesised circuit approximates the circuit** within `nGatesN C * ζ` on clean
ancillas, for every payload. -/
theorem synthC_approxOn (hS : Synthesis 𝒢 X L) {ζ : ℝ} (hζ : 0 < ζ) (C : List (NInstr V Y J))
    (hC : ∀ i ∈ C, i.Valid) (hprim : ∀ j, IsUnitary (prim j)) :
    ApproxOn CleanX (nrun prim (synthC hS ζ C)) (liftB (X := X) (nrun prim C))
      (nGatesN C * ζ) := by
  have hgv : ∀ g, NInstr.gate g ∈ C → GateOK 3 g := fun g hg => hC _ hg
  refine approxOn_replace prim hprim _ hζ.le C hC
    (fun g hg h hh => ((synthRep_spec hS hζ g (hgv g hg)).1 h hh).1) ?_
  intro g hg
  have hsp := synthRep_spec hS hζ g (hgv g hg)
  exact approxOn_rep g (hgv g hg) _ (fun h hh => (hsp.1 h hh).1) hζ.le hsp.2.2

/-- **The full-output error of the synthesised circuit**: on the clean ancillas the synthesis
adds at most `nGatesN C * ζ` to the full-output error of `C` along every contractive
embedding `E` of the system register `Reg S R`. -/
theorem synthC_error (hS : Synthesis 𝒢 X L) {ζ : ℝ} (hζ : 0 < ζ) (C : List (NInstr V Y J))
    (hC : ∀ i ∈ C, i.Valid) (hprim : ∀ j, IsUnitary (prim j)) {S : Type*} [Fintype S]
    [DecidableEq S] (E : Reg S R →L[ℂ] Reg V R) (hE : ∀ p, ‖E p‖ ≤ ‖p‖)
    (U : Reg S R →L[ℂ] Reg S R) :
    ‖nrun prim (synthC hS ζ C) ∘L (cleanEmb (X := X) ∘L E) - (cleanEmb ∘L E) ∘L U‖ ≤
      ‖nrun prim C ∘L E - E ∘L U‖ + nGatesN C * ζ := by
  have hδ : 0 ≤ (nGatesN C : ℝ) * ζ := mul_nonneg (Nat.cast_nonneg _) hζ.le
  have h1 := norm_sub_cleanEmb_le (synthC_approxOn prim hS hζ C hC hprim) hδ
  have hEn : ‖E‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun p => by rw [one_mul]; exact hE p)
  have hcn : ‖(cleanEmb (X := X) : Reg V R →L[ℂ] Reg (V ⊕ X) R)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      (fun ψ => by rw [one_mul, norm_cleanEmb])
  have e : nrun prim (synthC hS ζ C) ∘L (cleanEmb (X := X) ∘L E) - (cleanEmb ∘L E) ∘L U =
      (nrun prim (synthC hS ζ C) ∘L cleanEmb - cleanEmb ∘L nrun prim C) ∘L E +
        cleanEmb ∘L (nrun prim C ∘L E - E ∘L U) := by
    ext p
    simp only [sub_apply, comp_apply, add_apply, map_sub]
    exact (sub_add_sub_cancel _ _ _).symm
  rw [e]
  calc ‖(nrun prim (synthC hS ζ C) ∘L cleanEmb - cleanEmb ∘L nrun prim C) ∘L E +
        cleanEmb (X := X) ∘L (nrun prim C ∘L E - E ∘L U)‖
      ≤ ‖nrun prim (synthC hS ζ C) ∘L cleanEmb - cleanEmb ∘L nrun prim C‖ * ‖E‖ +
          ‖(cleanEmb (X := X) : Reg V R →L[ℂ] Reg (V ⊕ X) R)‖ *
            ‖nrun prim C ∘L E - E ∘L U‖ :=
        (norm_add_le _ _).trans (add_le_add (opNorm_comp_le _ _) (opNorm_comp_le _ _))
    _ ≤ (nGatesN C * ζ) * 1 + 1 * ‖nrun prim C ∘L E - E ∘L U‖ := by
        gcongr
    _ = ‖nrun prim C ∘L E - E ∘L U‖ + nGatesN C * ζ := by ring

end Synth

end

end SparseHamiltonian.GateSynth
