import GateEfficientSelective.Compiler
import GateEfficientSynthesisTrials.Protocol

/-!
# The selectively compiled preparation of the ODE trials

Theorem `ode:thm:gates` (here a partial formalisation, under this package's format hypotheses, of
its finite-set statement) amplifies one finite-gate
preparation with its actual inverse and exact zero tests, and charges the supplied source circuits
by their own gate count over the gate set (`G_src(ν)` in equation `ode:eq:gate-main`). The released
finite-gate-set solvers (`GateSynthTrials.synthPrep`) synthesise every gate of the native
preparation, the source circuits included. Here the native preparation `prepN` (on a native ODE
register `HWO …`) is
compiled selectively (`GateSelective.selBudget`): its gates of `𝒢` (in particular every gate of a
supplied source circuit over `𝒢`) are kept verbatim, the other gates are synthesised with the
budget `η`, every primitive call is kept. The selective preparation is placed on the released
trial register `SWO …` (`GateSynthTrials.embS`, fresh flag and pool for the exact zero tests):

`selPrep hS η prepN = (selBudget hS η prepN).map (NInstr.map embS)`,

and the protocol is the released native four-attempt protocol `nprotocol (selPrep hS η prepN) g`:
a uniform trial count, the trial `trialN (selPrep hS η prepN) j` (the preparation, then `j`
Grover steps with the released exact zero tests, the literal inverse of the preparation, which is
its exact adjoint, and the exact sign), and the clean-output herald.

* `selPrep_valid`, `selPrep_counts`: valid instructions; at most
  `nKeepN prepN + K len(η/(K+1))` gates, `K = nSynN prepN` the synthesised gate occurrences;
  exactly the calls of `prepN`.
* `selPrep_gateOf`, `selPrep_inv_gateOf` (`AdjClosed 𝒢`), `trialSel_gateOf`
  (`zeroTestKinds ⊆ 𝒢`): every gate of every trial is a gate of `𝒢`; `trialSel_valid`.
* `selPrep_pres`: the preparation never touches the fresh flag and pool.
* `selPrep_approx`: within `η + δ` of the lifted released preparation on clean work wires, when
  the native preparation is within `δ`; the native error `δ` contains the errors of the supplied
  circuits against their ideal operations (as in the released native solvers).
* `sel_noutcome`: with `η + δ ≤ 4ν/3` and the released vector certificate, the guarantees
  `GateNative.NOutcome` (every successful trial within `ε/500` of the normalised solution up to a
  global phase, success probability at least `2/3`, conditional output within trace distance
  `ε`).
* `sel_protocol_worst`, `sel_protocol_worst_log`: in every history at most `40 g` times the
  native calls, and at most `40 g N_S + 20 g (4 n + 3)` gates, `N_S` the gates of the selective
  preparation; with `len ζ ≤ c₁ log(1/ζ) + c₀` at most
  `40 g (nKeepN prepN + K' (c₁ log((K'+1)/η) + c₀)) + 20 g (4 n + 3)` for every `K' ≥ K`: the
  kept gates (the source circuits) are outside the synthesis logarithm.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateSelective

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit GateNative GateSynth GateSynthTrials
open GateODE (AW goodF)
open scoped InnerProduct BigOperators

section Prep

variable {a m r K k l f : ℕ} {S Zs Z Y J X : Type*} {nP bT bP A : ℕ}
variable [Fintype S] [DecidableEq S] [Fintype Zs] [DecidableEq Zs] [Fintype Z] [DecidableEq Z]
  [Fintype Y] [DecidableEq Y] [Fintype X] [DecidableEq X]
variable {𝒢 : Set Kind} {len : ℝ → ℕ}

/-- **The selective preparation** on the trial register: the native preparation compiled with
the gates of `𝒢` kept and the others synthesised with the budget `η`, every call kept, placed
by `embS`. -/
def selPrep (hS : Synthesis 𝒢 X len) (η : ℝ)
    (prepN : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J)) :
    List (NInstr (SWO a m r K k l f S Zs nP Z bT bP A X) Y J) :=
  (selBudget hS η prepN).map (NInstr.map embS)

omit [Fintype Y] [DecidableEq Y] in
theorem selPrep_valid (hS : Synthesis 𝒢 X len) {η : ℝ} (hη : 0 < η)
    (prepN : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J))
    (hvalid : ∀ i ∈ prepN, i.Valid) : ∀ i ∈ selPrep hS η prepN, i.Valid :=
  valid_map_list _ _ (selBudget_spec hS hη prepN hvalid).1

omit [Fintype Y] [DecidableEq Y] in
/-- **The counts of the selective preparation**: at most `nKeepN prepN + K len(η/(K+1))` gates
for the `K = nSynN prepN` synthesised gate occurrences, and exactly the calls of `prepN`. -/
theorem selPrep_counts (hS : Synthesis 𝒢 X len) {η : ℝ} (hη : 0 < η)
    (prepN : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J))
    (hvalid : ∀ i ∈ prepN, i.Valid) :
    nGatesN (selPrep hS η prepN) ≤
        nKeepN 𝒢 prepN + nSynN 𝒢 prepN * len (η / (nSynN 𝒢 prepN + 1)) ∧
      ∀ q : J → Bool, nCallsN q (selPrep hS η prepN) = nCallsN q prepN := by
  obtain ⟨-, -, hG, hC⟩ := selBudget_spec hS hη prepN hvalid
  refine ⟨?_, fun q => ?_⟩
  · rw [selPrep, nGatesN_map]
    exact hG
  · rw [selPrep, nCallsN_map]
    exact hC q

omit [Fintype Y] [DecidableEq Y] in
/-- **Every gate of the selective preparation is a gate of `𝒢`.** -/
theorem selPrep_gateOf (hS : Synthesis 𝒢 X len) {η : ℝ} (hη : 0 < η)
    (prepN : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J))
    (hvalid : ∀ i ∈ prepN, i.Valid) :
    ∀ g, NInstr.gate g ∈ selPrep hS η prepN → GateOf 𝒢 g := by
  intro g hg
  obtain ⟨g', hg', rfl⟩ := mem_map_gate _ _ g hg
  exact ((selBudget_spec hS hη prepN hvalid).2.1 g' hg').map _

omit [Fintype Y] [DecidableEq Y] in
/-- **Every gate of the inverse selective preparation is a gate of `𝒢`**, for an adjoint-closed
gate set. -/
theorem selPrep_inv_gateOf (hS : Synthesis 𝒢 X len) (hadj : AdjClosed 𝒢) {η : ℝ}
    (hη : 0 < η) (prepN : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J))
    (hvalid : ∀ i ∈ prepN, i.Valid) :
    ∀ g, NInstr.gate g ∈ ninv (selPrep hS η prepN) → GateOf 𝒢 g :=
  ninv_gateOf hadj _ (selPrep_gateOf hS hη prepN hvalid)

/-- **The selective preparation never touches the fresh flag and pool**, nor does its inverse. -/
theorem selPrep_pres (hS : Synthesis 𝒢 X len) (η : ℝ)
    (prepN : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J))
    (prim : J → Reg Y ℂ →L[ℂ] Reg Y ℂ) :
    Pres2 (ZeroOn reflWire) (nrun prim (selPrep hS η prepN)) := by
  apply pres2_nrun_zeroOn
  intro i hi
  simp only [selPrep, List.mem_map] at hi
  obtain ⟨i', _, rfl⟩ := hi
  exact NInstr.not_touches_map _ _ embS_not_refl i'

omit [Fintype Y] [DecidableEq Y] in
/-- **Every instruction of every trial is valid.** -/
theorem trialSel_valid (hS : Synthesis 𝒢 X len) {η : ℝ} (hη : 0 < η)
    (prepN : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J))
    (hvalid : ∀ i ∈ prepN, i.Valid) (j : ℕ) :
    ∀ i ∈ trialN (selPrep hS η prepN) j, i.Valid :=
  trialN_valid _ (selPrep_valid hS hη prepN hvalid) j

omit [Fintype Y] [DecidableEq Y] in
/-- **Every gate of every trial is a gate of `𝒢`**: the selective preparation and its exact
adjoint (`AdjClosed 𝒢`), and the exact zero tests and sign (`zeroTestKinds ⊆ 𝒢`). -/
theorem trialSel_gateOf (hS : Synthesis 𝒢 X len) (hadj : AdjClosed 𝒢)
    (hzt : zeroTestKinds ⊆ 𝒢) {η : ℝ} (hη : 0 < η)
    (prepN : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J))
    (hvalid : ∀ i ∈ prepN, i.Valid) (j : ℕ) :
    ∀ g, NInstr.gate g ∈ trialN (selPrep hS η prepN) j → GateOf 𝒢 g := by
  have hP := selPrep_gateOf hS hη prepN hvalid
  have hI := selPrep_inv_gateOf hS hadj hη prepN hvalid
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

/-- **The selective preparation is within `η + δ` of the lifted released preparation** on clean
work wires of the trial register, if the native preparation is within `δ` on clean work wires
of the native register. -/
theorem selPrep_approx (hS : Synthesis 𝒢 X len) {η : ℝ} (hη : 0 < η)
    (prepN : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J))
    (hvalid : ∀ i ∈ prepN, i.Valid) (prim : J → Reg Y ℂ →L[ℂ] Reg Y ℂ)
    (hprim : ∀ j, IsUnitary (prim j))
    (Urel : Reg (GateODE.AW a m r K k l f) (Reg S ℂ) →L[ℂ] Reg (GateODE.AW a m r K k l f) (Reg S ℂ))
    {δ : ℝ} (hδ : 0 ≤ δ) (hA : ApproxOn CleanX (nrun prim prepN) (liftB (conj Urel)) δ) :
    ApproxOn CleanX (nrun prim (selPrep hS η prepN)) (liftB (conj Urel)) (η + δ) := by
  -- the selective compilation, on clean synthesis ancillas
  have h1 : ApproxOn CleanX (nrun prim (selBudget hS η prepN))
      (liftB (X := X) (nrun prim prepN)) η :=
    selBudget_approxOn prim hS hη prepN hvalid hprim
  -- the native error, lifted to the synthesis ancillas
  have h2 : ApproxOn (fun y : Cfg (HWO a m r K k l f S Zs nP Z bT bP A ⊕ X) =>
        CleanX y ∧ CleanX (fun v => y (Sum.inl v)))
      (liftB (X := X) (nrun prim prepN)) (liftB (X := X) (liftB (conj Urel))) δ :=
    approxOn_localOp Sum.inl_injective (fun _ => nrun prim prepN)
      (fun _ => liftB (conj Urel)) hδ (fun _ hy => hy.2) (fun _ => hA)
  have h3 := approxOn_trans (approxOn_restrict h1 (fun _ hy => hy.1)) h2
  -- transport along the placement
  have h4 := approxOn_localOp (embS (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f)
      (S := S) (Zs := Zs) (nP := nP) (Z := Z) (bT := bT) (bP := bP) (A := A) (X := X)).injective
    (fun _ => nrun prim (selBudget hS η prepN))
    (fun _ => liftB (X := X) (liftB (conj Urel))) (by positivity)
    (SW := CleanX)
    (fun y hy => ⟨fun x => hy _, fun o => by rcases o with x | o <;> exact hy _⟩)
    (fun _ => h3)
  rw [selPrep, nrun_map, ← liftB_embS]
  exact h4

/-- **The selective protocol is correct, trial by trial.** Let the native preparation be within
`δ` of the lifted released preparation, whose decoded vector meets the released vector error
`6νB`, and let `η + δ ≤ 4ν/3`. Then the released native protocol `nprotocol (selPrep hS η prepN) g`
on the trial register (the selective preparation, its exact adjoint and the exact zero tests)
has the guarantees `NOutcome`. -/
theorem sel_noutcome (prim : J → Reg Y ℂ →L[ℂ] Reg Y ℂ) (hS : Synthesis 𝒢 X len) {η : ℝ}
    (hη : 0 < η) (prepN : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J))
    (hvalid : ∀ i ∈ prepN, i.Valid) (hprim : ∀ j, IsUnitary (prim j))
    (Urel : Reg (AW a m r K k l f) (Reg S ℂ) →L[ℂ] Reg (AW a m r K k l f) (Reg S ℂ))
    {δ : ℝ} (hδ : 0 ≤ δ) (hA : ApproxOn CleanX (nrun prim prepN) (liftB (conj Urel)) δ)
    (x : Reg S ℂ) (B g ε : ℝ) (hx : x ≠ 0) (hg : 1 ≤ g) (hε : 0 < ε) (hεHalf : ε ≤ 1 / 2)
    (hNorm : ‖x‖ ≤ B) (hBudget : B ≤ g * ‖x‖)
    (hrel : ‖(3 * B) • (goodF†) (Urel (GateODE.seedState seedV)) - x‖ ≤
      6 * ImprovedODEQueryBudget.precision g ε * B)
    (hηδ : η + δ ≤ 4 / 3 * ImprovedODEQueryBudget.precision g ε) :
    NOutcome (selPrep hS η prepN) g ε hg prim x :=
  noutcome10 prim hnP_SWO (selPrep hS η prepN) hprim (selPrep_valid hS hη prepN hvalid)
    (selPrep_pres hS η prepN prim) Urel
    (selPrep_approx hS hη prepN hvalid prim hprim Urel hδ hA) x B g ε hx hg hε hεHalf hNorm
    hBudget hrel hηδ

/-- **Worst-case counts of the selective protocol**, over every history: at most `40 g` times the
primitive calls of the native preparation, and at most `40 g N_S + 20 g (4 n + 3)` elementary
gates, `N_S` the gates of the selective preparation and `n` the wires tested by the seed zero
test. -/
theorem sel_protocol_worst (hS : Synthesis 𝒢 X len) {η : ℝ} (hη : 0 < η)
    (prepN : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J))
    (hvalid : ∀ i ∈ prepN, i.Valid) (g : ℝ) (hg : 1 ≤ g) :
    (∀ q : J → Bool, ((nprotocol (selPrep hS η prepN) g hg).worstCost (wCallN q) : ℝ) ≤
      40 * g * nCallsN q prepN) ∧
    ((nprotocol (selPrep hS η prepN) g hg).worstCost wGateN : ℝ) ≤
      40 * g * nGatesN (selPrep hS η prepN) +
        20 * g * (4 * (Fintype.card (AW a m r K k l f) + Fintype.card (XW Z bT bP A) +
          Fintype.card (SX Zs nP X) + Fintype.card S) + 3) := by
  refine ⟨fun q => ?_, ?_⟩
  · have h := (nprotocol_worst (selPrep hS η prepN) g hg q).2
    rwa [(selPrep_counts hS hη prepN hvalid).2 q] at h
  · exact (nprotocol_worst (selPrep hS η prepN) g hg (fun _ => true)).1

/-- **Worst-case gate count with a logarithmic synthesis length**: if `len ζ ≤ c₁ log(1/ζ) + c₀`
on `(0, 1]` and `0 < η ≤ 1`, the selective protocol uses at most
`40 g (nKeepN prepN + K' (c₁ log((K'+1)/η) + c₀)) + 20 g (4 n + 3)` elementary gates in every
history, for every `K'` at least the number of synthesised gate occurrences of the native
preparation. -/
theorem sel_protocol_worst_log (hS : Synthesis 𝒢 X len) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (prepN : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J))
    (hvalid : ∀ i ∈ prepN, i.Valid) (g : ℝ) (hg : 1 ≤ g) {c₀ c₁ : ℝ} (hc₀ : 0 ≤ c₀)
    (hc₁ : 0 ≤ c₁) (hlen : ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 → (len ζ : ℝ) ≤ c₁ * Real.log (1 / ζ) + c₀)
    (K' : ℝ) (hK : (nSynN 𝒢 prepN : ℝ) ≤ K') :
    ((nprotocol (selPrep hS η prepN) g hg).worstCost wGateN : ℝ) ≤
      40 * g * ((nKeepN 𝒢 prepN : ℝ) + K' * (c₁ * Real.log ((K' + 1) / η) + c₀)) +
        20 * g * (4 * (Fintype.card (AW a m r K k l f) + Fintype.card (XW Z bT bP A) +
          Fintype.card (SX Zs nP X) + Fintype.card S) + 3) := by
  have h := (sel_protocol_worst hS hη prepN hvalid g hg).2
  have hN : ((nGatesN (selPrep hS η prepN) : ℕ) : ℝ) ≤
      (nKeepN 𝒢 prepN : ℝ) + K' * (c₁ * Real.log ((K' + 1) / η) + c₀) := by
    rw [selPrep, nGatesN_map]
    exact selBudget_gates_log hS hc₀ hc₁ hlen hη hη1 prepN hvalid K' hK
  have hg0 : 0 ≤ 40 * g := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hN hg0]

end Prep

end

end SparseHamiltonian.GateSelective
