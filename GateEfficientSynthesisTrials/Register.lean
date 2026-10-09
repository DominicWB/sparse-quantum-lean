import GateEfficientSynthesisTrials.Kinds
import GateEfficientSynthesis.Hamiltonian

/-!
# The register and the preparation of the synthesised trials

A native preparation `prepN` acts on a native ODE register
`V = HWO a m r K k l f S Zs nP Z bT bP A` (the released wires, the system, the work wires of
the private implementation, the source scratch `Zs`, a flag and a pool `Fin nP`). Under the
synthesis hypothesis `Synthesis 𝒢 X len` its synthesis `synthBudget hS η prepN` acts on
`V ⊕ X`, `X` the synthesis ancillas.

The trials run on the native ODE register `SWO … = HWO a m r K k l f S (SX Zs nP X) (sPool …)
Z bT bP A` whose scratch slot `SX Zs nP X = OX Zs nP ⊕ X` holds the native scratch, the native
flag and pool and the synthesis ancillas, with a fresh flag and a fresh pool of `sPool` wires
for the zero tests. `embS : V ⊕ X ↪ SWO …` places the synthesised wires; it avoids the fresh
flag and pool (`embS_not_refl`). The synthesised preparation is
`synthPrep hS η prepN = (synthBudget hS η prepN).map (NInstr.map embS)`; the trials are the
released native trials `trialN (synthPrep hS η prepN) j` on `SWO …`: the synthesised
preparation, its literal inverse (the exact adjoint), and the released exact zero tests
`rgoodNG`, `rseedNG` and sign `negGateN` of the register `SWO …`, which test every wire of
`V ⊕ X` except, for `rgoodNG`, the system.

* `synthPrep_valid`, `synthPrep_counts`: valid instructions, at most `N len(η/(N+1))` gates,
  exactly the calls of `prepN`.
* `synthPrep_pres`: the synthesised preparation never touches the fresh flag and pool.
* `trialS_gateOf`: under `AdjClosed 𝒢` and `zeroTestKinds ⊆ 𝒢`, every gate of every trial is a
  gate of `𝒢`; `trialS_valid`: every instruction is valid.
* `hnP_SWO`: the fresh pool is large enough for the released zero tests.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateSynthTrials

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit GateNative GateSynth

/-! ### The register -/

/-- The scratch slot of the trial register: the native scratch, flag and pool, and the
synthesis ancillas. -/
abbrev SX (Zs : Type*) (nP : ℕ) (X : Type*) := OX Zs nP ⊕ X

/-- The size of the fresh pool of the trial register: the wires tested by the seed zero test. -/
abbrev sPool (a m r K k l f : ℕ) (S Zs : Type*) (nP : ℕ) (Z : Type*) (bT bP A : ℕ) (X : Type*)
    [Fintype S] [Fintype Zs] [Fintype Z] [Fintype X] : ℕ :=
  Fintype.card (GateODE.AW a m r K k l f) + Fintype.card (XW Z bT bP A) +
    Fintype.card (SX Zs nP X) + Fintype.card S

/-- **The register of the synthesised trials.** -/
abbrev SWO (a m r K k l f : ℕ) (S Zs : Type*) (nP : ℕ) (Z : Type*) (bT bP A : ℕ) (X : Type*)
    [Fintype S] [Fintype Zs] [Fintype Z] [Fintype X] :=
  HWO a m r K k l f S (SX Zs nP X) (sPool a m r K k l f S Zs nP Z bT bP A X) Z bT bP A

section Embed

variable {a m r K k l f : ℕ} {S Zs Z X : Type*} {nP bT bP A : ℕ}
variable [Fintype S] [Fintype Zs] [Fintype Z] [Fintype X]

/-- The placement of the native wires and the synthesis ancillas in the trial register. -/
def embFun : HWO a m r K k l f S Zs nP Z bT bP A ⊕ X → SWO a m r K k l f S Zs nP Z bT bP A X
  | Sum.inl (Sum.inl v) => Sum.inl v
  | Sum.inl (Sum.inr (Sum.inl x)) => Sum.inr (Sum.inl x)
  | Sum.inl (Sum.inr (Sum.inr o)) => Sum.inr (Sum.inr (Sum.inl (Sum.inl o)))
  | Sum.inr y => Sum.inr (Sum.inr (Sum.inl (Sum.inr y)))

theorem embFun_injective :
    Function.Injective (embFun (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f)
      (S := S) (Zs := Zs) (nP := nP) (Z := Z) (bT := bT) (bP := bP) (A := A) (X := X)) := by
  intro u w h
  rcases u with (v | (x | o)) | y <;> rcases w with (v' | (x' | o')) | y' <;>
    simp_all [embFun]

/-- **The placement of the synthesised wires** in the trial register. -/
def embS : HWO a m r K k l f S Zs nP Z bT bP A ⊕ X ↪ SWO a m r K k l f S Zs nP Z bT bP A X :=
  ⟨embFun, embFun_injective⟩

/-- The placement avoids the fresh flag and pool of the trial register. -/
theorem embS_not_refl (w : HWO a m r K k l f S Zs nP Z bT bP A ⊕ X) :
    ¬ reflWire (embS (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f) (S := S)
      (Zs := Zs) (nP := nP) (Z := Z) (bT := bT) (bP := bP) (A := A) (X := X) w) := by
  rcases w with (v | (x | o)) | y <;> exact fun h => h

/-- The fresh pool is large enough for the released zero tests of the trial register. -/
theorem hnP_SWO :
    Fintype.card (GateODE.AW a m r K k l f) + Fintype.card (XW Z bT bP A) +
      Fintype.card (SX Zs nP X) + Fintype.card S ≤
      sPool a m r K k l f S Zs nP Z bT bP A X + 1 := Nat.le_succ _

end Embed

/-! ### Gates of renamed circuits -/

section Gates

variable {V V' Y J : Type*}

/-- A gate of a renamed circuit is a renamed gate of the circuit. -/
theorem mem_map_gate (e : V ↪ V') (C : List (NInstr V Y J)) (g : Gate V')
    (hg : NInstr.gate g ∈ C.map (NInstr.map e)) :
    ∃ g', NInstr.gate g' ∈ C ∧ g = GateODE.Gate.map e g' := by
  obtain ⟨i, hi, he⟩ := List.mem_map.mp hg
  cases i with
  | gate g' =>
      refine ⟨g', hi, ?_⟩
      simp only [NInstr.map, NInstr.gate.injEq] at he
      exact he.symm
  | call j adj pos => simp [NInstr.map] at he

/-- A gate of a gate list read as instructions is a gate of the list. -/
theorem mem_nGatesOf_gate (gs : List (Gate V)) (g : Gate V)
    (hg : NInstr.gate g ∈ (nGatesOf gs : List (NInstr V Y J))) : g ∈ gs := by
  simp only [nGatesOf, List.mem_map, NInstr.gate.injEq] at hg
  obtain ⟨g', hg', rfl⟩ := hg
  exact hg'

end Gates

/-! ### The synthesised preparation -/

section Prep

variable {a m r K k l f : ℕ} {S Zs Z Y J X : Type*} {nP bT bP A : ℕ}
variable [Fintype S] [DecidableEq S] [Fintype Zs] [DecidableEq Zs] [Fintype Z] [DecidableEq Z]
  [Fintype Y] [DecidableEq Y] [Fintype X] [DecidableEq X]
variable {𝒢 : Set Kind} {len : ℝ → ℕ}

/-- **The synthesised preparation** on the trial register: every elementary gate of the native
preparation synthesised over `𝒢` with the budget `η` (`synthBudget`), every primitive call
kept, placed by `embS`. -/
def synthPrep (hS : Synthesis 𝒢 X len) (η : ℝ)
    (prepN : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J)) :
    List (NInstr (SWO a m r K k l f S Zs nP Z bT bP A X) Y J) :=
  (synthBudget hS η prepN).map (NInstr.map embS)

omit [Fintype Y] [DecidableEq Y] in
/-- **The synthesised preparation is valid.** -/
theorem synthPrep_valid (hS : Synthesis 𝒢 X len) {η : ℝ} (hη : 0 < η)
    (prepN : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J))
    (hvalid : ∀ i ∈ prepN, i.Valid) : ∀ i ∈ synthPrep hS η prepN, i.Valid :=
  valid_map_list _ _ (synthBudget_spec hS hη prepN hvalid).1

omit [Fintype Y] [DecidableEq Y] in
/-- **The counts of the synthesised preparation**: at most `N len(η/(N+1))` gates for the
`N` gates of the native preparation, and exactly its primitive calls. -/
theorem synthPrep_counts (hS : Synthesis 𝒢 X len) {η : ℝ} (hη : 0 < η)
    (prepN : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J))
    (hvalid : ∀ i ∈ prepN, i.Valid) :
    nGatesN (synthPrep hS η prepN) ≤ nGatesN prepN * len (η / (nGatesN prepN + 1)) ∧
      ∀ q : J → Bool, nCallsN q (synthPrep hS η prepN) = nCallsN q prepN := by
  obtain ⟨-, -, hG, hC⟩ := synthBudget_spec hS hη prepN hvalid
  refine ⟨?_, fun q => ?_⟩
  · rw [synthPrep, nGatesN_map]
    exact hG
  · rw [synthPrep, nCallsN_map]
    exact hC q

omit [Fintype Y] [DecidableEq Y] in
/-- **Every gate of the synthesised preparation is a gate of `𝒢`.** -/
theorem synthPrep_gateOf (hS : Synthesis 𝒢 X len) {η : ℝ} (hη : 0 < η)
    (prepN : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J))
    (hvalid : ∀ i ∈ prepN, i.Valid) :
    ∀ g, NInstr.gate g ∈ synthPrep hS η prepN → GateOf 𝒢 g := by
  intro g hg
  obtain ⟨g', hg', rfl⟩ := mem_map_gate _ _ g hg
  exact ((synthBudget_spec hS hη prepN hvalid).2.1 g' hg').map _

omit [Fintype Y] [DecidableEq Y] in
/-- **Every gate of the inverse synthesised preparation is a gate of `𝒢`**, for an
adjoint-closed gate set. -/
theorem synthPrep_inv_gateOf (hS : Synthesis 𝒢 X len) (hadj : AdjClosed 𝒢) {η : ℝ}
    (hη : 0 < η) (prepN : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J))
    (hvalid : ∀ i ∈ prepN, i.Valid) :
    ∀ g, NInstr.gate g ∈ ninv (synthPrep hS η prepN) → GateOf 𝒢 g := by
  intro g hg
  rw [synthPrep, ninv_map] at hg
  obtain ⟨g', hg', rfl⟩ := mem_map_gate _ _ g hg
  refine GateOf.map _ ?_
  simp only [ninv, List.mem_reverse, List.mem_map] at hg'
  obtain ⟨i, hi, he⟩ := hg'
  cases i with
  | gate h =>
      simp only [NInstr.inv, NInstr.gate.injEq] at he
      subst he
      exact GateOf.inv hadj ((synthBudget_spec hS hη prepN hvalid).2.1 h hi)
  | call j adj pos => simp [NInstr.inv] at he

/-- **The synthesised preparation never touches the fresh flag and pool**, nor does its
inverse. -/
theorem synthPrep_pres (hS : Synthesis 𝒢 X len) (η : ℝ)
    (prepN : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J))
    (prim : J → Reg Y ℂ →L[ℂ] Reg Y ℂ) :
    Pres2 (ZeroOn reflWire) (nrun prim (synthPrep hS η prepN)) := by
  apply pres2_nrun_zeroOn
  intro i hi
  simp only [synthPrep, List.mem_map] at hi
  obtain ⟨i', _, rfl⟩ := hi
  exact NInstr.not_touches_map _ _ embS_not_refl i'

omit [Fintype Y] [DecidableEq Y] in
/-- **Every instruction of every trial is valid.** -/
theorem trialS_valid (hS : Synthesis 𝒢 X len) {η : ℝ} (hη : 0 < η)
    (prepN : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J))
    (hvalid : ∀ i ∈ prepN, i.Valid) (j : ℕ) :
    ∀ i ∈ trialN (synthPrep hS η prepN) j, i.Valid :=
  trialN_valid _ (synthPrep_valid hS hη prepN hvalid) j

omit [Fintype Y] [DecidableEq Y] in
/-- **Every gate of every synthesised trial is a gate of `𝒢`**: the synthesised preparation and
its exact adjoint (`AdjClosed 𝒢`), and the exact zero tests and sign (`zeroTestKinds ⊆ 𝒢`). -/
theorem trialS_gateOf (hS : Synthesis 𝒢 X len) (hadj : AdjClosed 𝒢)
    (hzt : zeroTestKinds ⊆ 𝒢) {η : ℝ} (hη : 0 < η)
    (prepN : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J))
    (hvalid : ∀ i ∈ prepN, i.Valid) (j : ℕ) :
    ∀ g, NInstr.gate g ∈ trialN (synthPrep hS η prepN) j → GateOf 𝒢 g := by
  have hP := synthPrep_gateOf hS hη prepN hvalid
  have hI := synthPrep_inv_gateOf hS hadj hη prepN hvalid
  intro g hg
  simp only [trialN, List.mem_append, List.mem_flatten, List.mem_replicate] at hg
  rcases hg with hg | ⟨l', ⟨_, rfl⟩, hg⟩
  · exact hP g hg
  · simp only [stepN, List.mem_append, List.mem_singleton] at hg
    rcases hg with (((hg | hg) | hg) | hg) | hg
    · exact gateOf_rgoodNG hzt (Nat.le_succ_of_le (Nat.le_add_right _ _)) g
        (mem_nGatesOf_gate _ g hg)
    · exact hI g hg
    · exact gateOf_rseedNG hzt hnP_SWO g (mem_nGatesOf_gate _ g hg)
    · exact hP g hg
    · simp only [NInstr.gate.injEq] at hg
      subst hg
      exact gateOf_negGateN hzt

end Prep

end

end SparseHamiltonian.GateSynthTrials
