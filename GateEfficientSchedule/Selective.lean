import GateEfficientSelective.HamSim
import GateEfficientSchedule.Endpoint

/-!
# Theorem `hs:thm:gates` over a finite gate set with the manuscript's schedule
(equations `hs:eq:gate-schedule`, `hs:eq:gate-clocks`, `hs:eq:gate-Gzero`, `hs:eq:gate-total`)

The selective finite-set compilation of `GateEfficientSelective.HamSim` applied to the circuit with
the manuscript's schedule (`simCircuitMs`: `k = ⌈4τq̄/Q + log₂(4096/ε)⌉`, `d = k (⌈32Q⌉ - 1)`,
`2^m` the least power of two at least `max{2, 4τ, τ^{3/2}/√(3ε)}`, `r = ⌈log₂(2d+2)⌉`). The error
allocation is the manuscript's:

* the exact-gate circuit: filter `δ = ε/8` and Cayley discretisation `ε/4`, total `ε/2`
  (`gate_efficient_simulation_ms`);
* the `6d` private calls, each implemented by the supplied finite-set circuit `pc` (and its literal
  reverse-adjoint) with accuracy `ξ`, `ξ = ε/(24d)` (`24 d ξ ≤ ε`): at most `ε/4`;
* the synthesis of the remaining exact gates (`selBudget` with budget `ε/4`): at most `ε/4`.

Endpoints, with `G₀ = 200 (d+1)(a+m+r+1) + 84 d C_J` the synthesised gate occurrences:

* `sim_supplied_ms`: the native circuit with the supplied private calls (before synthesis);
* `sel_simulation_ms`: calls exactly `6 d` times those of `pc`; at most
  `6 d |pc| + G₀ (c₁ log((G₀+1)/(ε/4)) + c₀ + 1)` gates of `𝒢`;
  `|S| + (2a + 3m + 6r + 3) + (|Z| + bT + bP + A + 3) + |X|` qubits; full-output error at most `ε`;
  `d ≤ 128 τ q̄ + 32 Q (log₂(4096/ε) + 1)`; `2^m` the manuscript's slot count;
* `sel_simulation_ms_signed`: every real time, by the literal inverse of the compiled circuit.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateSchedule

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit GateCircuit.Sim GateNative GateSynth
  GateSelective
open GateSynthTrials (AdjClosed)
open scoped InnerProduct

variable {S Z Y J X : Type*} [Fintype S] [DecidableEq S] [Fintype Z] [DecidableEq Z]
  [Fintype Y] [DecidableEq Y] [Fintype X] [DecidableEq X] {bT bP A : ℕ}
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
variable {𝒢 : Set Kind} {L : ℝ → ℕ}

/-- The native circuit with the manuscript's schedule and the supplied private circuit `pc`. -/
def simPMs (a : ℕ) (τ Q qbar ε : ℝ) (UJg : List (Gate (Fin a ⊕ S)))
    (pc : List (NInstr (PWr Empty (Fin a ⊕ S) Z bT bP A) Y J)) :
    List (NInstr (HW (SimWireMs a Q τ qbar ε) S Empty Z bT bP A) Y J) :=
  hcircP (wireRel _ _ _ _) (noSel _) UJg pc (simCircuitMs a τ Q qbar ε)

/-- **The selective finite-set circuit with the manuscript's schedule**: the supplied private
circuit retained, the remaining exact gates synthesised with the budget `ε/4`. -/
def selSimMs (hS : Synthesis 𝒢 X L) (a : ℕ) (τ Q qbar ε : ℝ) (UJg : List (Gate (Fin a ⊕ S)))
    (pc : List (NInstr (PWr Empty (Fin a ⊕ S) Z bT bP A) Y J)) :
    List (NInstr (HW (SimWireMs a Q τ qbar ε) S Empty Z bT bP A ⊕ X) Y J) :=
  selBudget hS (ε / 4) (simPMs a τ Q qbar ε UJg pc)

set_option maxRecDepth 8192 in
/-- **The native circuit with the manuscript's schedule and a supplied private circuit**
(before synthesis). Under the clock promises for `D` and `J = U_J ι₀` and a valid supplied
circuit `pc` within `ξ` of the enable-controlled private operation on clean work wires: valid
instructions, exactly `6 d` times the primitive calls of `pc`, exactly
`nGatesN (simPMs ∅) + 6 d |pc|` elementary gates with
`nGatesN (simPMs ∅) ≤ 200 (d+1)(a+m+r+1) + 84 d C_J`, and full output on the system embedding
within `ε/2 + 6 d ξ` of `exp(-iτH)`. -/
theorem sim_supplied_ms (a : ℕ) (prim : J → Reg Y R →L[ℂ] Reg Y R)
    (hprim : ∀ j, IsUnitary (prim j))
    (UJg : List (Gate (Fin a ⊕ S))) (hUJg : ∀ g ∈ UJg, GateOK 3 g)
    (pc : List (NInstr (PWr Empty (Fin a ⊕ S) Z bT bP A) Y J)) (hpcV : ∀ i ∈ pc, i.Valid)
    (ξ : ℝ) (hξ : 0 ≤ ξ)
    (D R1 : Anc a (Reg S R) →L[ℂ] Anc a (Reg S R)) (H : Reg S R →L[ℂ] Reg S R)
    (hD : IsUnitary D)
    (hpc : ApproxOn CleanP (nrun prim pc) (ctrlIdeal (selOp (fun _ : Cfg Empty => D))) ξ)
    (τ Q b qbar ε : ℝ) (hτ : 0 ≤ τ) (hQ : 1 ≤ Q)
    (hRight : (1 - D) ∘L R1 = 1) (hLeft : R1 ∘L (1 - D) = 1) (hR1 : ‖R1‖ ≤ Q)
    (hBoundary : (UJop (R := R) UJg ∘L iota0 (P := Reg S R))† ∘L R1 ∘L
      (UJop (R := R) UJg ∘L iota0 (P := Reg S R)) = (2 : ℂ)⁻¹ • (1 + Complex.I • H))
    (hSelf : star H = H) (hH : ‖H‖ ≤ 1)
    (hEndpoint : ‖R1 ∘L (UJop (R := R) UJg ∘L iota0 (P := Reg S R))‖ ≤ b)
    (hbq : b ^ 2 ≤ qbar / 2) (hqQ : qbar ≤ Q) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (∀ i ∈ simPMs a τ Q qbar ε UJg pc, i.Valid) ∧
    (∀ p : J → Bool, nCallsN p (simPMs a τ Q qbar ε UJg pc) =
      6 * degreeMs Q (τ * qbar) ε * nCallsN p pc) ∧
    nGatesN (simPMs a τ Q qbar ε UJg pc) =
      nGatesN (simPMs a τ Q qbar ε UJg
        ([] : List (NInstr (PWr Empty (Fin a ⊕ S) Z bT bP A) Y J))) +
        6 * degreeMs Q (τ * qbar) ε * nGatesN pc ∧
    nGatesN (simPMs a τ Q qbar ε UJg
        ([] : List (NInstr (PWr Empty (Fin a ⊕ S) Z bT bP A) Y J))) ≤
      200 * (degreeMs Q (τ * qbar) ε + 1) * (a + slotMs τ ε + rMs Q τ qbar ε + 1) +
        84 * degreeMs Q (τ * qbar) ε * UJg.length ∧
    Fintype.card (HW (SimWireMs a Q τ qbar ε) S Empty Z bT bP A) =
      Fintype.card S + (2 * a + 3 * slotMs τ ε + 6 * rMs Q τ qbar ε + 3) +
        (Fintype.card Z + bT + bP + A + 3) ∧
    ‖nrun prim (simPMs a τ Q qbar ε UJg pc) ∘L sysEmb (io (P := Reg S R)) -
        sysEmb (io (P := Reg S R)) ∘L NormedSpace.exp ((-Complex.I * (τ : ℂ)) • H)‖ ≤
      ε / 2 + 6 * degreeMs Q (τ * qbar) ε * ξ := by
  have hUJu : IsUnitary (UJop (R := R) UJg) := UJop_isUnitary UJg hUJg
  obtain ⟨hvalid, hP, hJ, hG, hW, herr, -, -, -, -, -⟩ :=
    gate_efficient_simulation_ms (P := Reg S R) a (UJop (R := R) UJg) D R1 H hUJu hD τ Q b qbar
      ε hτ hQ hRight hLeft hR1 hBoundary hSelf hH hEndpoint hbq hqQ hε hε1
  have hsec : ∀ i ∈ simCircuitMs a τ Q qbar ε, SecOK (wireRel _ _ _ _) i := by
    unfold simCircuitMs simCircuitK
    exact secOK_ampI _ _ _ _ _ _
  have hDu : ∀ w, IsUnitary (constFam D false w) := fun _ => hD
  have hDadj : ∀ w, constFam D true w = (constFam D false w)† := fun _ => rfl
  have hpc' : ApproxOn CleanP (nrun prim pc) (ctrlIdeal (selOp (constFam D false))) ξ := hpc
  refine ⟨hcircP_valid (wireRel _ _ _ _) (noSel _) UJg hUJg pc hpcV _ hvalid, fun p => ?_, ?_,
    ?_, ?_, ?_⟩
  · rw [simPMs, hcircP_nCalls, hP]
  · rw [simPMs, simPMs, hcircP_nGates, hP]
  · refine (hcircP_nil_nGates (wireRel _ _ _ _) (noSel _) UJg hUJg _).trans ?_
    rw [hJ, mul_one]
    have h84 : 12 * degreeMs Q (τ * qbar) ε * (7 * UJg.length) =
        84 * degreeMs Q (τ * qbar) ε * UJg.length := by ring
    rw [h84]
    exact Nat.add_le_add_right hG _
  · rw [card_HW, hW]
    simp only [Fintype.card_empty, add_zero]
    ring
  · have hio : ∀ ψ : Reg S R, ‖(io (P := Reg S R) (a := a) (m := slotMs τ ε)
        (r := rMs Q τ qbar ε) (K := simKK a (slotMs τ ε) Q (kMs Q τ qbar ε))) ψ‖ = ‖ψ‖ :=
      fun ψ => by rw [io_apply, norm_bas]
    rw [simPMs]
    generalize NormedSpace.exp ((-Complex.I * (τ : ℂ)) • H) = U at herr ⊢
    generalize simCircuitMs a τ Q qbar ε = l at herr hvalid hsec hP ⊢
    have h := hcircP_error (X' := Empty) prim hprim (wireRel _ _ _ _) (noSel _) UJg hUJg pc hpcV
      hξ (constFam D) hDu hDadj hpc' l hvalid io hio U _ (prodOps_evalSel_const UJg D l hsec) herr
    refine h.trans (le_of_eq ?_)
    rw [hP]
    push_cast
    ring

set_option maxRecDepth 8192 in
/-- **Gate-efficient sparse Hamiltonian simulation over a finite gate set with the manuscript's
schedule** (Theorem `hs:thm:gates`, with `k`, `d`, `M` and `r = r_reuse` of equations
`hs:eq:gate-schedule`, `hs:eq:gate-clocks` and `ξ = ε/(24d)` of `hs:eq:gate-Gzero`). Under the
synthesis hypothesis `Synthesis 𝒢 X L` with `L ζ ≤ c₁ log(1/ζ) + c₀` on `(0, 1]`, an
adjoint-closed `𝒢`, the clock promises of the released analysis, and a valid supplied circuit
`pc` over `𝒢` within `ξ` of the enable-controlled private operation on clean work wires, with
`24 d ξ ≤ ε`: the selective circuit `selSimMs` (1) consists of valid gates of `𝒢` and primitive
calls; (2) makes exactly `6 d` times the primitive calls of `pc`; (3) synthesises at most
`G₀ = 200 (d+1)(a+m+r+1) + 84 d C_J` gate occurrences, whatever `pc`; (4) has at most
`6 d |pc| + G₀ (c₁ log((G₀+1)/(ε/4)) + c₀ + 1)` gates; (5) has
`|S| + (2a + 3m + 6r + 3) + (|Z| + bT + bP + A + 3) + |X|` qubits; (6) has full output, with every
qubit outside the system clean, within `ε` of `exp(-iτH)`; (7) `d = k (⌈32Q⌉ - 1)` with
`d ≤ 128 τ q̄ + 32 Q (log₂(4096/ε) + 1)`; and (8) `2^m` is the least power of two at least
`max{2, 4τ, √(τ³/(3ε))}`. -/
theorem sel_simulation_ms (hS : Synthesis 𝒢 X L) (hadj : AdjClosed 𝒢) {c₀ c₁ : ℝ}
    (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁)
    (hL : ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 → (L ζ : ℝ) ≤ c₁ * Real.log (1 / ζ) + c₀)
    (a : ℕ) (prim : J → Reg Y R →L[ℂ] Reg Y R) (hprim : ∀ j, IsUnitary (prim j))
    (UJg : List (Gate (Fin a ⊕ S))) (hUJg : ∀ g ∈ UJg, GateOK 3 g)
    (pc : List (NInstr (PWr Empty (Fin a ⊕ S) Z bT bP A) Y J)) (hpcV : ∀ i ∈ pc, i.Valid)
    (hpcG : ∀ g, NInstr.gate g ∈ pc → GateOf 𝒢 g) (ξ : ℝ) (hξ : 0 ≤ ξ)
    (D R1 : Anc a (Reg S R) →L[ℂ] Anc a (Reg S R)) (H : Reg S R →L[ℂ] Reg S R)
    (hD : IsUnitary D)
    (hpc : ApproxOn CleanP (nrun prim pc) (ctrlIdeal (selOp (fun _ : Cfg Empty => D))) ξ)
    (τ Q b qbar ε : ℝ) (hτ : 0 ≤ τ) (hQ : 1 ≤ Q)
    (hRight : (1 - D) ∘L R1 = 1) (hLeft : R1 ∘L (1 - D) = 1) (hR1 : ‖R1‖ ≤ Q)
    (hBoundary : (UJop (R := R) UJg ∘L iota0 (P := Reg S R))† ∘L R1 ∘L
      (UJop (R := R) UJg ∘L iota0 (P := Reg S R)) = (2 : ℂ)⁻¹ • (1 + Complex.I • H))
    (hSelf : star H = H) (hH : ‖H‖ ≤ 1)
    (hEndpoint : ‖R1 ∘L (UJop (R := R) UJg ∘L iota0 (P := Reg S R))‖ ≤ b)
    (hbq : b ^ 2 ≤ qbar / 2) (hqQ : qbar ≤ Q) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hξε : 24 * (degreeMs Q (τ * qbar) ε : ℝ) * ξ ≤ ε) :
    (∀ i ∈ selSimMs hS a τ Q qbar ε UJg pc, i.Valid) ∧
    (∀ g, NInstr.gate g ∈ selSimMs hS a τ Q qbar ε UJg pc → GateOf 𝒢 g) ∧
    (∀ p : J → Bool, nCallsN p (selSimMs hS a τ Q qbar ε UJg pc) =
      6 * degreeMs Q (τ * qbar) ε * nCallsN p pc) ∧
    nSynN 𝒢 (simPMs a τ Q qbar ε UJg pc) ≤
      200 * (degreeMs Q (τ * qbar) ε + 1) * (a + slotMs τ ε + rMs Q τ qbar ε + 1) +
        84 * degreeMs Q (τ * qbar) ε * UJg.length ∧
    (nGatesN (selSimMs hS a τ Q qbar ε UJg pc) : ℝ) ≤
      6 * (degreeMs Q (τ * qbar) ε : ℝ) * nGatesN pc +
        ((200 * (degreeMs Q (τ * qbar) ε + 1) * (a + slotMs τ ε + rMs Q τ qbar ε + 1) +
          84 * degreeMs Q (τ * qbar) ε * UJg.length : ℕ) : ℝ) *
        (c₁ * Real.log ((((200 * (degreeMs Q (τ * qbar) ε + 1) *
          (a + slotMs τ ε + rMs Q τ qbar ε + 1) +
          84 * degreeMs Q (τ * qbar) ε * UJg.length : ℕ) : ℝ) + 1) / (ε / 4)) + c₀ + 1) ∧
    Fintype.card (HW (SimWireMs a Q τ qbar ε) S Empty Z bT bP A ⊕ X) =
      Fintype.card S + (2 * a + 3 * slotMs τ ε + 6 * rMs Q τ qbar ε + 3) +
        (Fintype.card Z + bT + bP + A + 3) + Fintype.card X ∧
    ‖nrun prim (selSimMs hS a τ Q qbar ε UJg pc) ∘L
        (cleanEmb (X := X) ∘L sysEmb (io (P := Reg S R))) -
        (cleanEmb ∘L sysEmb (io (P := Reg S R))) ∘L
          NormedSpace.exp ((-Complex.I * (τ : ℂ)) • H)‖ ≤ ε ∧
    degreeMs Q (τ * qbar) ε = depthMs Q (τ * qbar) ε * (SharpFilterSchedule.length Q - 1) ∧
    (degreeMs Q (τ * qbar) ε : ℝ) ≤ 128 * (τ * qbar) + 32 * Q * (Real.logb 2 (4096 / ε) + 1) ∧
    meshMs τ ε ≤ 2 ^ slotMs τ ε ∧ (∀ j : ℕ, meshMs τ ε ≤ 2 ^ j → slotMs τ ε ≤ j) := by
  have hq : 0 ≤ qbar := by nlinarith [sq_nonneg b]
  have hW : 0 ≤ τ * qbar := mul_nonneg hτ hq
  have hdeg := degreeMs_le Q (τ * qbar) ε hQ hW hε hε1
  obtain ⟨hmesh, hleast, -⟩ := slotMs_spec τ ε
  have hδ : 0 < ε / 4 := by linarith
  have hδ1 : ε / 4 ≤ 1 := by linarith
  have h6 : 6 * (degreeMs Q (τ * qbar) ε : ℝ) * ξ ≤ ε / 4 := by linarith
  obtain ⟨hvalid, hcalls, hgates, hgates0, hcard, herr⟩ := sim_supplied_ms a prim hprim UJg
    hUJg pc hpcV ξ hξ D R1 H hD hpc τ Q b qbar ε hτ hQ hRight hLeft hR1 hBoundary hSelf hH
    hEndpoint hbq hqQ hε hε1
  obtain ⟨hv, hk, -, hc⟩ := selBudget_spec hS hδ _ hvalid
  have hsyn : nSynN 𝒢 (simPMs a τ Q qbar ε UJg pc) ≤
      200 * (degreeMs Q (τ * qbar) ε + 1) * (a + slotMs τ ε + rMs Q τ qbar ε + 1) +
        84 * degreeMs Q (τ * qbar) ε * UJg.length :=
    (nSynN_hcircP_le 𝒢 hadj _ _ UJg pc hpcG _).trans hgates0
  refine ⟨hv, hk, fun p => (hc p).trans (hcalls p), hsyn, ?_, ?_, ?_, rfl, hdeg, hmesh, hleast⟩
  · -- the separated gate count
    set G₀ : ℕ := 200 * (degreeMs Q (τ * qbar) ε + 1) *
      (a + slotMs τ ε + rMs Q τ qbar ε + 1) + 84 * degreeMs Q (τ * qbar) ε * UJg.length
      with hG₀
    have h1 := selBudget_gates_log hS hc₀ hc₁ hL hδ hδ1 _ hvalid (G₀ : ℝ)
      (by exact_mod_cast hsyn)
    have hNk : (nKeepN 𝒢 (simPMs a τ Q qbar ε UJg pc) : ℝ) ≤
        6 * (degreeMs Q (τ * qbar) ε : ℝ) * nGatesN pc + G₀ := by
      have h2 : nKeepN 𝒢 (simPMs a τ Q qbar ε UJg pc) ≤
          6 * degreeMs Q (τ * qbar) ε * nGatesN pc + G₀ := by
        have := nKeepN_le 𝒢 (simPMs a τ Q qbar ε UJg pc)
        rw [hgates] at this
        omega
      exact_mod_cast h2
    exact sel_count_arith hNk h1
  · rw [Fintype.card_sum, hcard]
  · generalize NormedSpace.exp ((-Complex.I * (τ : ℂ)) • H) = U at herr ⊢
    unfold selSimMs
    generalize simPMs a τ Q qbar ε UJg pc = C at hvalid herr ⊢
    refine (selBudget_error_of hS hδ C hvalid prim hprim _ ?_ U herr).trans ?_
    · intro ψ
      exact (norm_sysEmb _ (fun φ => by rw [io_apply, norm_bas]) ψ).le
    · clear herr hvalid hcard hgates hgates0 hcalls hv hk hc hsyn
      linarith

/-- The selective circuit with the manuscript's schedule for a signed time `t`: the circuit for
`|t|`, or its literal inverse (the reverse-adjoint of the compiled circuit) for `t < 0`. -/
def selSimMsSigned (hS : Synthesis 𝒢 X L) (a : ℕ) (t Q qbar ε : ℝ)
    (UJg : List (Gate (Fin a ⊕ S))) (pc : List (NInstr (PWr Empty (Fin a ⊕ S) Z bT bP A) Y J)) :
    List (NInstr (HW (SimWireMs a Q |t| qbar ε) S Empty Z bT bP A ⊕ X) Y J) :=
  if 0 ≤ t then selSimMs hS a |t| Q qbar ε UJg pc else ninv (selSimMs hS a |t| Q qbar ε UJg pc)

set_option maxRecDepth 8192 in
/-- **Every real time with the manuscript's schedule** (`sel_simulation_ms`): for `t < 0` the
literal reverse-adjoint of the compiled circuit for `|t|` simulates `exp(-itH)` with the same
counts and the same full-output error. -/
theorem sel_simulation_ms_signed (hS : Synthesis 𝒢 X L) (hadj : AdjClosed 𝒢) {c₀ c₁ : ℝ}
    (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁)
    (hL : ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 → (L ζ : ℝ) ≤ c₁ * Real.log (1 / ζ) + c₀)
    (a : ℕ) (prim : J → Reg Y R →L[ℂ] Reg Y R) (hprim : ∀ j, IsUnitary (prim j))
    (UJg : List (Gate (Fin a ⊕ S))) (hUJg : ∀ g ∈ UJg, GateOK 3 g)
    (pc : List (NInstr (PWr Empty (Fin a ⊕ S) Z bT bP A) Y J)) (hpcV : ∀ i ∈ pc, i.Valid)
    (hpcG : ∀ g, NInstr.gate g ∈ pc → GateOf 𝒢 g) (ξ : ℝ) (hξ : 0 ≤ ξ)
    (D R1 : Anc a (Reg S R) →L[ℂ] Anc a (Reg S R)) (H : Reg S R →L[ℂ] Reg S R)
    (hD : IsUnitary D)
    (hpc : ApproxOn CleanP (nrun prim pc) (ctrlIdeal (selOp (fun _ : Cfg Empty => D))) ξ)
    (t Q b qbar ε : ℝ) (hQ : 1 ≤ Q)
    (hRight : (1 - D) ∘L R1 = 1) (hLeft : R1 ∘L (1 - D) = 1) (hR1 : ‖R1‖ ≤ Q)
    (hBoundary : (UJop (R := R) UJg ∘L iota0 (P := Reg S R))† ∘L R1 ∘L
      (UJop (R := R) UJg ∘L iota0 (P := Reg S R)) = (2 : ℂ)⁻¹ • (1 + Complex.I • H))
    (hSelf : star H = H) (hH : ‖H‖ ≤ 1)
    (hEndpoint : ‖R1 ∘L (UJop (R := R) UJg ∘L iota0 (P := Reg S R))‖ ≤ b)
    (hbq : b ^ 2 ≤ qbar / 2) (hqQ : qbar ≤ Q) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hξε : 24 * (degreeMs Q (|t| * qbar) ε : ℝ) * ξ ≤ ε) :
    (∀ i ∈ selSimMsSigned hS a t Q qbar ε UJg pc, i.Valid) ∧
    (∀ g, NInstr.gate g ∈ selSimMsSigned hS a t Q qbar ε UJg pc → GateOf 𝒢 g) ∧
    (∀ p : J → Bool, nCallsN p (selSimMsSigned hS a t Q qbar ε UJg pc) =
      6 * degreeMs Q (|t| * qbar) ε * nCallsN p pc) ∧
    (nGatesN (selSimMsSigned hS a t Q qbar ε UJg pc) : ℝ) ≤
      6 * (degreeMs Q (|t| * qbar) ε : ℝ) * nGatesN pc +
        ((200 * (degreeMs Q (|t| * qbar) ε + 1) * (a + slotMs |t| ε + rMs Q |t| qbar ε + 1) +
          84 * degreeMs Q (|t| * qbar) ε * UJg.length : ℕ) : ℝ) *
        (c₁ * Real.log ((((200 * (degreeMs Q (|t| * qbar) ε + 1) *
          (a + slotMs |t| ε + rMs Q |t| qbar ε + 1) +
          84 * degreeMs Q (|t| * qbar) ε * UJg.length : ℕ) : ℝ) + 1) / (ε / 4)) + c₀ + 1) ∧
    ‖nrun prim (selSimMsSigned hS a t Q qbar ε UJg pc) ∘L
        (cleanEmb (X := X) ∘L sysEmb (io (P := Reg S R))) -
        (cleanEmb ∘L sysEmb (io (P := Reg S R))) ∘L
          NormedSpace.exp ((-Complex.I * (t : ℂ)) • H)‖ ≤ ε := by
  obtain ⟨hv, hk, hcalls, -, hgates, -, herr, -⟩ := sel_simulation_ms hS hadj hc₀ hc₁ hL a prim
    hprim UJg hUJg pc hpcV hpcG ξ hξ D R1 H hD hpc |t| Q b qbar ε (abs_nonneg t) hQ hRight hLeft
    hR1 hBoundary hSelf hH hEndpoint hbq hqQ hε hε1 hξε
  unfold selSimMsSigned
  split_ifs with ht
  · have ht' : ((|t| : ℝ) : ℂ) = (t : ℂ) := by rw [abs_of_nonneg ht]
    rw [ht'] at herr
    exact ⟨hv, hk, hcalls, hgates, herr⟩
  · refine ⟨valid_ninv _ hv, ninv_gateOf hadj _ hk, fun p => ?_, ?_, ?_⟩
    · rw [nCallsN_ninv, hcalls p]
    · rw [nGatesN_ninv]
      exact hgates
    have hC : IsUnitary (nrun prim (selSimMs hS a |t| Q qbar ε UJg pc)) :=
      nrun_isUnitary prim hprim _ hv
    rw [nrun_ninv]
    generalize nrun prim (selSimMs hS a |t| Q qbar ε UJg pc) = C at hC herr ⊢
    exact err_neg C hC _ H hSelf t ε (lt_of_not_ge ht) herr

end

end SparseHamiltonian.GateSchedule
