import GateEfficientSelective.HamMacro

/-!
# Theorem `hs:thm:gates` with a supplied controlled private circuit (equation `hs:eq:gate-total`)

The manuscript's gate count for Hamiltonian simulation over a finite gate set `𝒢` is
`O(d G_C(ξ) + G_syn log((G_syn+1)/ε))`, `ξ = ε/(24d)`,
`G_syn = C₀[d(C_J+a+m_slot+r_reuse) + A_C(ξ)]` (equation `hs:eq:gate-Gzero`), where `G_C(ξ)` and
`A_C(ξ)` are the gates and work qubits of a
supplied finite-set circuit for the controlled private Cayley operation at accuracy `ξ`, whose
inverse is its circuit adjoint. Here:

* the private calls of the released circuit are implemented by the supplied circuit `pc` (and
  its literal reverse-adjoint), retained verbatim (`hcircP`);
* only the remaining exact elementary gates (the released gates and the controlled gates of
  `U_J`) are synthesised, with the synthesis budget `ε/4` spread over their occurrences
  (`selBudget`); the primitive calls are kept;
* the released circuit is taken at accuracy `ε/2`, the private calls contribute `6 d ξ ≤ ε/4`
  (`24 d ξ ≤ ε`), and the synthesis `ε/4`, so the full output on the clean system embedding is
  within `ε` of the evolution.

Endpoints, with `d` the formal degree of the released circuit and
`G₀ = 200 (d+1)(a+m+r+1) + 84 d C_J`:

* `sel_simulation` (time-independent): calls exactly `6 d` times those of `pc`; at most
  `6 d |pc| + G₀ (c₁ log((G₀+1)/(ε/4)) + c₀ + 1)` gates of `𝒢`; `|S| + (2a + 3m + 6r + 3) +
  (|Z| + bT + bP + A + 3) + |X|` qubits (the work wires `Z ⊕ AWr bT bP A` of `pc` are the
  `A_C(ξ)` term, `X` the synthesis ancillas); full-output error at most `ε`.
* `sel_simulation_signed`: every real time, by the literal inverse of the compiled circuit.
* `sel_time_simulation`: time-dependent Hamiltonians on a uniform mesh, slot-selected private
  operations.

The synthesised count is bounded by `G₀` whatever the length of `pc` (`nSynN_hcircP_le`), so
`d G_C(ξ)` enters linearly and outside every logarithm; no assumption on the size of the supplied
circuit is made.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateSelective

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit GateCircuit.Sim GateNative GateSynth
open GateSynthTrials (AdjClosed)
open GatePointerEncoding (wordEquivFin)
open scoped InnerProduct

/-- The separated closed form of a selective synthesis count: `N_keep ≤ G + K` retained gates
and at most `K` synthesised occurrences give `G + K (c₁ log((K+1)/δ) + c₀ + 1)`. -/
theorem sel_count_arith {Nt Nk G K lam c₀ c₁ : ℝ} (hNk : Nk ≤ G + K)
    (hW : Nt ≤ Nk + K * (c₁ * lam + c₀)) : Nt ≤ G + K * (c₁ * lam + c₀ + 1) := by
  nlinarith

/-- The selective compilation adds its budget to a full-output error bound. -/
theorem selBudget_error_of {V Y J X : Type*} [Fintype V] [DecidableEq V] [Fintype Y]
    [DecidableEq Y] [Fintype X] [DecidableEq X] {𝒢 : Set Kind} {L : ℝ → ℕ}
    {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
    (hS : Synthesis 𝒢 X L) {δ : ℝ} (hδ : 0 < δ) (C : List (NInstr V Y J))
    (hC : ∀ i ∈ C, i.Valid) (prim : J → Reg Y R →L[ℂ] Reg Y R) (hprim : ∀ j, IsUnitary (prim j))
    {S : Type*} [Fintype S] [DecidableEq S] (E : Reg S R →L[ℂ] Reg V R)
    (hE : ∀ p, ‖E p‖ ≤ ‖p‖) (U : Reg S R →L[ℂ] Reg S R) {ε : ℝ}
    (herr : ‖nrun prim C ∘L E - E ∘L U‖ ≤ ε) :
    ‖nrun prim (selBudget hS δ C) ∘L (cleanEmb (X := X) ∘L E) - (cleanEmb ∘L E) ∘L U‖ ≤
      ε + δ := by
  have h := selBudget_error prim hS hδ C hC hprim E hE U
  linarith

/-! ### Time-independent Hamiltonians -/

section Constant

variable {S Z Y J X : Type*} [Fintype S] [DecidableEq S] [Fintype Z] [DecidableEq Z]
  [Fintype Y] [DecidableEq Y] [Fintype X] [DecidableEq X] {bT bP A : ℕ}
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
variable {𝒢 : Set Kind} {L : ℝ → ℕ}

/-- The native circuit for target accuracy `ε` with the supplied private circuit `pc`: the
released circuit at accuracy `ε/2` with the supplied private calls. -/
def simP (a : ℕ) (τ Q qbar ε : ℝ) (UJg : List (Gate (Fin a ⊕ S)))
    (pc : List (NInstr (PWr Empty (Fin a ⊕ S) Z bT bP A) Y J)) :
    List (NInstr (HW (SimWire a Q τ qbar (ε / 2)) S Empty Z bT bP A) Y J) :=
  hcircP (wireRel _ _ _ _) (noSel _) UJg pc (simCircuit a τ Q qbar (ε / 2))

/-- **The selective finite-set circuit**: the supplied private circuit retained, the remaining
exact gates synthesised with the budget `ε/4`. It is fixed by the public data and `pc`. -/
def selSim (hS : Synthesis 𝒢 X L) (a : ℕ) (τ Q qbar ε : ℝ) (UJg : List (Gate (Fin a ⊕ S)))
    (pc : List (NInstr (PWr Empty (Fin a ⊕ S) Z bT bP A) Y J)) :
    List (NInstr (HW (SimWire a Q τ qbar (ε / 2)) S Empty Z bT bP A ⊕ X) Y J) :=
  selBudget hS (ε / 4) (simP a τ Q qbar ε UJg pc)

/-- **The native circuit with a supplied private circuit** (time-independent Hamiltonian, before
synthesis). Under the clock promises of the released analysis for `D` and `J = U_J ι₀` and a
valid supplied circuit `pc` within `ξ` of the enable-controlled private operation on clean work
wires, the circuit consists of valid instructions, makes exactly `6 d` times the primitive calls
of `pc`, has exactly `nGatesN (simP ∅) + 6 d |pc|` elementary gates with
`nGatesN (simP ∅) ≤ 200 (d+1)(a+m+r+1) + 84 d C_J`, and its full output on the system embedding
is within `ε/2 + 6 d ξ` of `exp(-iτH)`. -/
theorem sim_supplied (a : ℕ) (prim : J → Reg Y R →L[ℂ] Reg Y R)
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
    (∀ i ∈ simP a τ Q qbar ε UJg pc, i.Valid) ∧
    (∀ p : J → Bool, nCallsN p (simP a τ Q qbar ε UJg pc) =
      6 * fDeg Q τ qbar (ε / 2) * nCallsN p pc) ∧
    nGatesN (simP a τ Q qbar ε UJg pc) =
      nGatesN (simP a τ Q qbar ε UJg ([] : List (NInstr (PWr Empty (Fin a ⊕ S) Z bT bP A) Y J))) +
        6 * fDeg Q τ qbar (ε / 2) * nGatesN pc ∧
    nGatesN (simP a τ Q qbar ε UJg ([] : List (NInstr (PWr Empty (Fin a ⊕ S) Z bT bP A) Y J))) ≤
      200 * (fDeg Q τ qbar (ε / 2) + 1) * (a + simM τ (ε / 2) + simR Q τ qbar (ε / 2) + 1) +
        84 * fDeg Q τ qbar (ε / 2) * UJg.length ∧
    Fintype.card (HW (SimWire a Q τ qbar (ε / 2)) S Empty Z bT bP A) =
      Fintype.card S + (2 * a + 3 * simM τ (ε / 2) + 6 * simR Q τ qbar (ε / 2) + 3) +
        (Fintype.card Z + bT + bP + A + 3) ∧
    ‖nrun prim (simP a τ Q qbar ε UJg pc) ∘L sysEmb (io (P := Reg S R)) -
        sysEmb (io (P := Reg S R)) ∘L NormedSpace.exp ((-Complex.I * (τ : ℂ)) • H)‖ ≤
      ε / 2 + 6 * fDeg Q τ qbar (ε / 2) * ξ ∧
    (fDeg Q τ qbar (ε / 2) : ℝ) ≤ 128 * (τ * qbar + Q * (1 + Real.log (6 / ε))) := by
  have hε2 : 0 < ε / 2 := by linarith
  have hε21 : ε / 2 ≤ 1 := by linarith
  have hUJu : IsUnitary (UJop (R := R) UJg) := UJop_isUnitary UJg hUJg
  obtain ⟨hvalid, hP, hJ, hG, hW, herr, hdeg, -, -, -, -⟩ :=
    gate_efficient_simulation (P := Reg S R) a (UJop (R := R) UJg) D R1 H hUJu hD τ Q b qbar
      (ε / 2) hτ hQ hRight hLeft hR1 hBoundary hSelf hH hEndpoint hbq hqQ hε2 hε21
  have hsec : ∀ i ∈ simCircuit a τ Q qbar (ε / 2), SecOK (wireRel _ _ _ _) i := by
    unfold simCircuit
    exact secOK_ampI _ _ _ _ _ _
  have hDu : ∀ w, IsUnitary (constFam D false w) := fun _ => hD
  have hDadj : ∀ w, constFam D true w = (constFam D false w)† := fun _ => rfl
  have hpc' : ApproxOn CleanP (nrun prim pc) (ctrlIdeal (selOp (constFam D false))) ξ := hpc
  have hlog : (1 : ℝ) / (ε / 2 / 3) = 6 / ε := by
    field_simp
    ring
  rw [hlog] at hdeg
  refine ⟨hcircP_valid (wireRel _ _ _ _) (noSel _) UJg hUJg pc hpcV _ hvalid, fun p => ?_, ?_,
    ?_, ?_, ?_, hdeg⟩
  · rw [simP, hcircP_nCalls, hP]
  · rw [simP, simP, hcircP_nGates, hP]
  · refine (hcircP_nil_nGates (wireRel _ _ _ _) (noSel _) UJg hUJg _).trans ?_
    rw [hJ, mul_one]
    have h84 : 12 * fDeg Q τ qbar (ε / 2) * (7 * UJg.length) =
        84 * fDeg Q τ qbar (ε / 2) * UJg.length := by ring
    rw [h84]
    exact Nat.add_le_add_right hG _
  · rw [card_HW, card_simWire]
    simp only [Fintype.card_empty, add_zero]
    ring
  · have hio : ∀ ψ : Reg S R, ‖(io (P := Reg S R) (a := a) (m := simM τ (ε / 2))
        (r := simR Q τ qbar (ε / 2)) (K := simK a Q τ qbar (ε / 2))) ψ‖ = ‖ψ‖ :=
      fun ψ => by rw [io_apply, norm_bas]
    rw [simP]
    generalize NormedSpace.exp ((-Complex.I * (τ : ℂ)) • H) = U at herr ⊢
    generalize simCircuit a τ Q qbar (ε / 2) = l at herr hvalid hsec hP ⊢
    have h := hcircP_error (X' := Empty) prim hprim (wireRel _ _ _ _) (noSel _) UJg hUJg pc hpcV
      hξ (constFam D) hDu hDadj hpc' l hvalid io hio U _ (prodOps_evalSel_const UJg D l hsec) herr
    refine h.trans (le_of_eq ?_)
    rw [hP]
    push_cast
    ring

/-- **Gate-efficient sparse Hamiltonian simulation over a finite gate set with a supplied
controlled private circuit** (Theorem `hs:thm:gates`; equation
`hs:eq:gate-total`). Under the synthesis hypothesis `Synthesis 𝒢 X L` with
`L ζ ≤ c₁ log(1/ζ) + c₀` on `(0, 1]`, an adjoint-closed `𝒢`, the clock promises of the released
analysis, and a valid supplied circuit `pc` over `𝒢` within `ξ` of the enable-controlled private
operation on clean work wires (its full output, not only a block), with `24 d ξ ≤ ε`: the
selective circuit `selSim` (1) consists of valid gates of `𝒢` and primitive calls; (2) makes
exactly `6 d` times the primitive calls of `pc`; (3) synthesises at most
`G₀ = 200 (d+1)(a+m+r+1) + 84 d C_J` gate occurrences, whatever `pc`; (4) has at most
`6 d |pc| + G₀ (c₁ log((G₀+1)/(ε/4)) + c₀ + 1)` gates; (5) has
`|S| + (2a + 3m + 6r + 3) + (|Z| + bT + bP + A + 3) + |X|` qubits; (6) has full output, with every
qubit outside the system clean, within `ε` of `exp(-iτH)`; and (7) `d ≤ 128 (τ q̄ + Q (1 + log(6/ε)))`.
-/
theorem sel_simulation (hS : Synthesis 𝒢 X L) (hadj : AdjClosed 𝒢) {c₀ c₁ : ℝ} (hc₀ : 0 ≤ c₀)
    (hc₁ : 0 ≤ c₁) (hL : ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 → (L ζ : ℝ) ≤ c₁ * Real.log (1 / ζ) + c₀)
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
    (hξε : 24 * (fDeg Q τ qbar (ε / 2) : ℝ) * ξ ≤ ε) :
    (∀ i ∈ selSim hS a τ Q qbar ε UJg pc, i.Valid) ∧
    (∀ g, NInstr.gate g ∈ selSim hS a τ Q qbar ε UJg pc → GateOf 𝒢 g) ∧
    (∀ p : J → Bool, nCallsN p (selSim hS a τ Q qbar ε UJg pc) =
      6 * fDeg Q τ qbar (ε / 2) * nCallsN p pc) ∧
    nSynN 𝒢 (simP a τ Q qbar ε UJg pc) ≤
      200 * (fDeg Q τ qbar (ε / 2) + 1) * (a + simM τ (ε / 2) + simR Q τ qbar (ε / 2) + 1) +
        84 * fDeg Q τ qbar (ε / 2) * UJg.length ∧
    (nGatesN (selSim hS a τ Q qbar ε UJg pc) : ℝ) ≤
      6 * (fDeg Q τ qbar (ε / 2) : ℝ) * nGatesN pc +
        ((200 * (fDeg Q τ qbar (ε / 2) + 1) * (a + simM τ (ε / 2) + simR Q τ qbar (ε / 2) + 1) +
          84 * fDeg Q τ qbar (ε / 2) * UJg.length : ℕ) : ℝ) *
        (c₁ * Real.log ((((200 * (fDeg Q τ qbar (ε / 2) + 1) *
          (a + simM τ (ε / 2) + simR Q τ qbar (ε / 2) + 1) +
          84 * fDeg Q τ qbar (ε / 2) * UJg.length : ℕ) : ℝ) + 1) / (ε / 4)) + c₀ + 1) ∧
    Fintype.card (HW (SimWire a Q τ qbar (ε / 2)) S Empty Z bT bP A ⊕ X) =
      Fintype.card S + (2 * a + 3 * simM τ (ε / 2) + 6 * simR Q τ qbar (ε / 2) + 3) +
        (Fintype.card Z + bT + bP + A + 3) + Fintype.card X ∧
    ‖nrun prim (selSim hS a τ Q qbar ε UJg pc) ∘L
        (cleanEmb (X := X) ∘L sysEmb (io (P := Reg S R))) -
        (cleanEmb ∘L sysEmb (io (P := Reg S R))) ∘L
          NormedSpace.exp ((-Complex.I * (τ : ℂ)) • H)‖ ≤ ε ∧
    (fDeg Q τ qbar (ε / 2) : ℝ) ≤ 128 * (τ * qbar + Q * (1 + Real.log (6 / ε))) := by
  obtain ⟨hvalid, hcalls, hgates, hgates0, hcard, herr, hdeg⟩ := sim_supplied a prim hprim UJg
    hUJg pc hpcV ξ hξ D R1 H hD hpc τ Q b qbar ε hτ hQ hRight hLeft hR1 hBoundary hSelf hH
    hEndpoint hbq hqQ hε hε1
  have hδ : 0 < ε / 4 := by linarith
  have hδ1 : ε / 4 ≤ 1 := by linarith
  obtain ⟨hv, hk, -, hc⟩ := selBudget_spec hS hδ _ hvalid
  have hsyn : nSynN 𝒢 (simP a τ Q qbar ε UJg pc) ≤
      200 * (fDeg Q τ qbar (ε / 2) + 1) * (a + simM τ (ε / 2) + simR Q τ qbar (ε / 2) + 1) +
        84 * fDeg Q τ qbar (ε / 2) * UJg.length :=
    (nSynN_hcircP_le 𝒢 hadj _ _ UJg pc hpcG _).trans hgates0
  refine ⟨hv, hk, fun p => (hc p).trans (hcalls p), hsyn, ?_, ?_, ?_, hdeg⟩
  · -- the separated gate count
    set G₀ : ℕ := 200 * (fDeg Q τ qbar (ε / 2) + 1) *
      (a + simM τ (ε / 2) + simR Q τ qbar (ε / 2) + 1) + 84 * fDeg Q τ qbar (ε / 2) * UJg.length
      with hG₀
    have h1 := selBudget_gates_log hS hc₀ hc₁ hL hδ hδ1 _ hvalid (G₀ : ℝ) (by exact_mod_cast hsyn)
    have hNk : (nKeepN 𝒢 (simP a τ Q qbar ε UJg pc) : ℝ) ≤
        6 * (fDeg Q τ qbar (ε / 2) : ℝ) * nGatesN pc + G₀ := by
      have h2 : nKeepN 𝒢 (simP a τ Q qbar ε UJg pc) ≤
          6 * fDeg Q τ qbar (ε / 2) * nGatesN pc + G₀ := by
        have := nKeepN_le 𝒢 (simP a τ Q qbar ε UJg pc)
        rw [hgates] at this
        omega
      exact_mod_cast h2
    exact sel_count_arith hNk h1
  · rw [Fintype.card_sum, hcard]
  · generalize NormedSpace.exp ((-Complex.I * (τ : ℂ)) • H) = U at herr ⊢
    unfold selSim
    generalize simP a τ Q qbar ε UJg pc = C at hvalid herr ⊢
    refine (selBudget_error_of hS hδ C hvalid prim hprim _ ?_ U herr).trans ?_
    · intro ψ
      exact (norm_sysEmb _ (fun φ => by rw [io_apply, norm_bas]) ψ).le
    · linarith

/-- The selective circuit for a signed time `t`: the circuit for `|t|`, or its literal inverse
(the reverse-adjoint of the compiled circuit, gate by gate) for `t < 0`. -/
def selSimSigned (hS : Synthesis 𝒢 X L) (a : ℕ) (t Q qbar ε : ℝ)
    (UJg : List (Gate (Fin a ⊕ S))) (pc : List (NInstr (PWr Empty (Fin a ⊕ S) Z bT bP A) Y J)) :
    List (NInstr (HW (SimWire a Q |t| qbar (ε / 2)) S Empty Z bT bP A ⊕ X) Y J) :=
  if 0 ≤ t then selSim hS a |t| Q qbar ε UJg pc else ninv (selSim hS a |t| Q qbar ε UJg pc)

/-- **Every real time** (`sel_simulation`): for `t < 0` the literal reverse-adjoint of the
compiled circuit for `|t|` simulates `exp(-itH)` with the same counts and the same full-output
error; its gates are gates of `𝒢` since `𝒢` is adjoint-closed. -/
theorem sel_simulation_signed (hS : Synthesis 𝒢 X L) (hadj : AdjClosed 𝒢) {c₀ c₁ : ℝ}
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
    (hξε : 24 * (fDeg Q |t| qbar (ε / 2) : ℝ) * ξ ≤ ε) :
    (∀ i ∈ selSimSigned hS a t Q qbar ε UJg pc, i.Valid) ∧
    (∀ g, NInstr.gate g ∈ selSimSigned hS a t Q qbar ε UJg pc → GateOf 𝒢 g) ∧
    (∀ p : J → Bool, nCallsN p (selSimSigned hS a t Q qbar ε UJg pc) =
      6 * fDeg Q |t| qbar (ε / 2) * nCallsN p pc) ∧
    (nGatesN (selSimSigned hS a t Q qbar ε UJg pc) : ℝ) ≤
      6 * (fDeg Q |t| qbar (ε / 2) : ℝ) * nGatesN pc +
        ((200 * (fDeg Q |t| qbar (ε / 2) + 1) * (a + simM |t| (ε / 2) + simR Q |t| qbar (ε / 2) + 1) +
          84 * fDeg Q |t| qbar (ε / 2) * UJg.length : ℕ) : ℝ) *
        (c₁ * Real.log ((((200 * (fDeg Q |t| qbar (ε / 2) + 1) *
          (a + simM |t| (ε / 2) + simR Q |t| qbar (ε / 2) + 1) +
          84 * fDeg Q |t| qbar (ε / 2) * UJg.length : ℕ) : ℝ) + 1) / (ε / 4)) + c₀ + 1) ∧
    ‖nrun prim (selSimSigned hS a t Q qbar ε UJg pc) ∘L
        (cleanEmb (X := X) ∘L sysEmb (io (P := Reg S R))) -
        (cleanEmb ∘L sysEmb (io (P := Reg S R))) ∘L
          NormedSpace.exp ((-Complex.I * (t : ℂ)) • H)‖ ≤ ε := by
  obtain ⟨hv, hk, hcalls, -, hgates, -, herr, -⟩ := sel_simulation hS hadj hc₀ hc₁ hL a prim hprim
    UJg hUJg pc hpcV hpcG ξ hξ D R1 H hD hpc |t| Q b qbar ε (abs_nonneg t) hQ hRight hLeft hR1
    hBoundary hSelf hH hEndpoint hbq hqQ hε hε1 hξε
  unfold selSimSigned
  split_ifs with ht
  · have ht' : ((|t| : ℝ) : ℂ) = (t : ℂ) := by rw [abs_of_nonneg ht]
    rw [ht'] at herr
    exact ⟨hv, hk, hcalls, hgates, herr⟩
  · refine ⟨valid_ninv _ hv, ninv_gateOf hadj _ hk, fun p => ?_, ?_, ?_⟩
    · rw [nCallsN_ninv, hcalls p]
    · rw [nGatesN_ninv]
      exact hgates
    have hC : IsUnitary (nrun prim (selSim hS a |t| Q qbar ε UJg pc)) :=
      nrun_isUnitary prim hprim _ hv
    rw [nrun_ninv]
    generalize nrun prim (selSim hS a |t| Q qbar ε UJg pc) = C at hC herr ⊢
    exact err_neg C hC _ H hSelf t ε (lt_of_not_ge ht) herr

end Constant

/-! ### Time-dependent Hamiltonians -/

section Time

variable {S Z Y J X : Type*} [Fintype S] [DecidableEq S] [Fintype Z] [DecidableEq Z]
  [Fintype Y] [DecidableEq Y] [Fintype X] [DecidableEq X] {bT bP A : ℕ}
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
variable {𝒢 : Set Kind} {L : ℝ → ℕ}

/-- The native time-dependent circuit with `2^m` slots and the supplied slot-selected private
circuit: the released slot circuit for accuracy `ε/2` (filter parameter `ε/4`). -/
def simPT (a m : ℕ) (τ Q qbar ε : ℝ) (UJg : List (Gate (Fin a ⊕ S)))
    (pc : List (NInstr (PWr (Fin m) (Fin a ⊕ S) Z bT bP A) Y J)) :
    List (NInstr (HW (Wire a m (simR Q τ qbar (ε / 4)) (a + m + 2 * simR Q τ qbar (ε / 4))) S Empty
      Z bT bP A) Y J) :=
  hcircP (wireRel _ _ _ _) (slotSel _ _ _ _) UJg pc (SlotSim.simCircuitT a τ Q qbar (ε / 4) m)

/-- **The selective finite-set time-dependent circuit** (synthesis budget `ε/4`). -/
def selSimT (hS : Synthesis 𝒢 X L) (a m : ℕ) (τ Q qbar ε : ℝ) (UJg : List (Gate (Fin a ⊕ S)))
    (pc : List (NInstr (PWr (Fin m) (Fin a ⊕ S) Z bT bP A) Y J)) :
    List (NInstr (HW (Wire a m (simR Q τ qbar (ε / 4)) (a + m + 2 * simR Q τ qbar (ε / 4))) S Empty
      Z bT bP A ⊕ X) Y J) :=
  selBudget hS (ε / 4) (simPT a m τ Q qbar ε UJg pc)

/-- **Gate-efficient time-dependent simulation over a finite gate set with a supplied slot-selected
controlled private circuit** (Theorem `hs:thm:time` with the circuit of `hs:thm:gates`; equation
`hs:eq:gate-total`). The private Cayley operations `D k` at the slot words are implemented by one
supplied valid circuit `pc` over `𝒢` on the slot wires, the private register and its work wires,
within `ξ` of the enable-controlled slot-selected operation on clean work wires. Under the
hypotheses of `GateNative.native_time_simulation` (with `24 d ξ ≤ ε` in place of the arithmetic
budget), the synthesis hypothesis and an adjoint-closed `𝒢`: the selective circuit consists of valid
gates of `𝒢` and primitive calls, makes exactly `6 d` times the primitive calls of `pc`, synthesises
at most `G₀ = 200 (d+1)(a+m+r+1) + 84 d C_J` gate occurrences, has at most
`6 d |pc| + G₀ (c₁ log((G₀+1)/(ε/4)) + c₀ + 1)` gates and
`|S| + (2a + 3m + 6r + 3) + (|Z| + bT + bP + A + 3) + |X|` qubits, and for every propagator `U` of
the path its full output on the clean system embedding is within `ε` of `U(t)`. -/
theorem sel_time_simulation (hS : Synthesis 𝒢 X L) (hadj : AdjClosed 𝒢) {c₀ c₁ : ℝ}
    (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁)
    (hL : ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 → (L ζ : ℝ) ≤ c₁ * Real.log (1 / ζ) + c₀)
    (a m : ℕ) (prim : J → Reg Y R →L[ℂ] Reg Y R) (hprim : ∀ j, IsUnitary (prim j))
    (UJg : List (Gate (Fin a ⊕ S))) (hUJg : ∀ g ∈ UJg, GateOK 3 g)
    (pc : List (NInstr (PWr (Fin m) (Fin a ⊕ S) Z bT bP A) Y J)) (hpcV : ∀ i ∈ pc, i.Valid)
    (hpcG : ∀ g, NInstr.gate g ∈ pc → GateOf 𝒢 g) (ξ : ℝ) (hξ : 0 ≤ ξ)
    (D R1 : ℕ → Anc a (Reg S R) →L[ℂ] Anc a (Reg S R))
    (hpc : ApproxOn CleanP (nrun prim pc)
      (ctrlIdeal (selOp (fun w : Cfg (Fin m) => D (wordEquivFin m w)))) ξ)
    (Hpath : ℝ → Reg S R →L[ℂ] Reg S R) (Hs : ℕ → Reg S R →L[ℂ] Reg S R)
    (t α β δ Q b qbar ε : ℝ) (ht : 0 ≤ t) (hα : 0 < α) (hβ : 0 ≤ β) (hQ : 1 ≤ Q)
    (hqQ : qbar ≤ Q) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hCayley : TimeSchedule.steps (α * t) (ε / 12) ≤ 2 ^ m)
    (hFreeze : 8 * β * t ^ 2 ≤ ε * 2 ^ m)
    (hD : ∀ k < 2 ^ m, IsUnitary (D k))
    (hRight : ∀ k < 2 ^ m, (1 - D k) ∘L R1 k = 1)
    (hLeft : ∀ k < 2 ^ m, R1 k ∘L (1 - D k) = 1) (hR1 : ∀ k < 2 ^ m, ‖R1 k‖ ≤ Q)
    (hBoundary : ∀ k < 2 ^ m, (UJop (R := R) UJg ∘L iota0 (P := Reg S R))† ∘L R1 k ∘L
      (UJop (R := R) UJg ∘L iota0 (P := Reg S R)) =
        (2 : ℂ)⁻¹ • (1 + Complex.I • ((α : ℂ)⁻¹ • Hs k)))
    (hEndpoint : ∀ k < 2 ^ m, ‖R1 k ∘L (UJop (R := R) UJg ∘L iota0 (P := Reg S R))‖ ≤ b)
    (hbq : b ^ 2 ≤ qbar / 2)
    (hSelf : ∀ k < 2 ^ m, star (Hs k) = Hs k) (hHs : ∀ k < 2 ^ m, ‖Hs k‖ ≤ α)
    (hPath : ∀ u ∈ Set.Icc 0 t, star (Hpath u) = Hpath u)
    (hLip : ∀ u ∈ Set.Icc 0 t, ∀ v ∈ Set.Icc 0 t, ‖Hpath u - Hpath v‖ ≤ β * |u - v|)
    (hVal : ∀ k : ℕ, k < 2 ^ m → ‖Hpath (k * t / 2 ^ m) - Hs k‖ ≤ δ)
    (hValBudget : 8 * t * δ ≤ ε)
    (hξε : 24 * (fDeg Q (α * t) qbar (ε / 4) : ℝ) * ξ ≤ ε) :
    (∀ i ∈ selSimT hS a m (α * t) Q qbar ε UJg pc, i.Valid) ∧
    (∀ g, NInstr.gate g ∈ selSimT hS a m (α * t) Q qbar ε UJg pc → GateOf 𝒢 g) ∧
    (∀ p : J → Bool, nCallsN p (selSimT hS a m (α * t) Q qbar ε UJg pc) =
      6 * fDeg Q (α * t) qbar (ε / 4) * nCallsN p pc) ∧
    nSynN 𝒢 (simPT a m (α * t) Q qbar ε UJg pc) ≤
      200 * (fDeg Q (α * t) qbar (ε / 4) + 1) * (a + m + simR Q (α * t) qbar (ε / 4) + 1) +
        84 * fDeg Q (α * t) qbar (ε / 4) * UJg.length ∧
    (nGatesN (selSimT hS a m (α * t) Q qbar ε UJg pc) : ℝ) ≤
      6 * (fDeg Q (α * t) qbar (ε / 4) : ℝ) * nGatesN pc +
        ((200 * (fDeg Q (α * t) qbar (ε / 4) + 1) * (a + m + simR Q (α * t) qbar (ε / 4) + 1) +
          84 * fDeg Q (α * t) qbar (ε / 4) * UJg.length : ℕ) : ℝ) *
        (c₁ * Real.log ((((200 * (fDeg Q (α * t) qbar (ε / 4) + 1) *
          (a + m + simR Q (α * t) qbar (ε / 4) + 1) +
          84 * fDeg Q (α * t) qbar (ε / 4) * UJg.length : ℕ) : ℝ) + 1) / (ε / 4)) + c₀ + 1) ∧
    Fintype.card (HW (Wire a m (simR Q (α * t) qbar (ε / 4))
        (a + m + 2 * simR Q (α * t) qbar (ε / 4))) S Empty Z bT bP A ⊕ X) =
      Fintype.card S + (2 * a + 3 * m + 6 * simR Q (α * t) qbar (ε / 4) + 3) +
        (Fintype.card Z + bT + bP + A + 3) + Fintype.card X ∧
    (fDeg Q (α * t) qbar (ε / 4) : ℝ) ≤ 128 * (α * t * qbar + Q * (1 + Real.log (12 / ε))) ∧
    (∃ U : ℝ → Reg S R →L[ℂ] Reg S R, U 0 = 1 ∧ TimeDependent.SolvesOn Hpath U 0 t) ∧
    ∀ U : ℝ → Reg S R →L[ℂ] Reg S R, U 0 = 1 → TimeDependent.SolvesOn Hpath U 0 t →
      ‖nrun prim (selSimT hS a m (α * t) Q qbar ε UJg pc) ∘L
          (cleanEmb (X := X) ∘L sysEmb (io (P := Reg S R))) -
          (cleanEmb ∘L sysEmb (io (P := Reg S R))) ∘L U t‖ ≤ ε := by
  have hε2 : 0 < ε / 2 := by linarith
  have hε21 : ε / 2 ≤ 1 := by linarith
  have hUJu : IsUnitary (UJop (R := R) UJg) := UJop_isUnitary UJg hUJg
  have hC' : TimeSchedule.steps (α * t) (ε / 2 / 6) ≤ 2 ^ m := by
    rw [show ε / 2 / 6 = ε / 12 by ring]
    exact hCayley
  have hF' : 4 * β * t ^ 2 ≤ ε / 2 * 2 ^ m := by linarith
  have hV' : 4 * t * δ ≤ ε / 2 := by linarith
  obtain ⟨hvalid, hP, hJ, hG, hW, hdeg, -, -, hex, herr⟩ :=
    SlotSim.gate_efficient_time_simulation (P := Reg S R) a m (UJop (R := R) UJg) D R1 Hpath Hs t α
      β δ Q b qbar (ε / 2)
      ht hα hβ hQ hqQ hε2 hε21 hC' hF' hUJu hD hRight hLeft hR1 hBoundary hEndpoint hbq hSelf hHs
      hPath hLip hVal hV'
  have e4 : ε / 2 / 2 = ε / 4 := by ring
  have hlog : (6 : ℝ) / (ε / 2) = 12 / ε := by
    field_simp
    ring
  rw [e4] at hvalid hP hJ hG hW hdeg herr
  rw [hlog] at hdeg
  have hsec : ∀ i ∈ SlotSim.simCircuitT a (α * t) Q qbar (ε / 4) m,
      SecOK (wireRel _ _ _ _) i := by
    unfold SlotSim.simCircuitT
    exact secOK_ampI _ _ _ _ _ _
  have hfam : slotFam (m := m) (S := S) (R := R) D false = fun w => D (wordEquivFin m w) := rfl
  have hDu : ∀ w, IsUnitary (slotFam (m := m) (S := S) (R := R) D false w) := by
    intro w
    rw [hfam]
    exact hD _ (wordEquivFin m w).isLt
  have hDadj : ∀ w, slotFam (m := m) (S := S) (R := R) D true w = (slotFam D false w)† :=
    fun _ => rfl
  have hpc' : ApproxOn CleanP (nrun prim pc) (ctrlIdeal (selOp (slotFam D false))) ξ := by
    rw [hfam]
    exact hpc
  have hvalidP : ∀ i ∈ simPT a m (α * t) Q qbar ε UJg pc, i.Valid :=
    hcircP_valid (X' := Empty) (wireRel _ _ _ _) (slotSel _ _ _ _) UJg hUJg pc hpcV _ hvalid
  have hgates : nGatesN (simPT a m (α * t) Q qbar ε UJg pc) =
      nGatesN (simPT a m (α * t) Q qbar ε UJg
        ([] : List (NInstr (PWr (Fin m) (Fin a ⊕ S) Z bT bP A) Y J))) +
        6 * fDeg Q (α * t) qbar (ε / 4) * nGatesN pc := by
    rw [simPT, simPT, hcircP_nGates, hP]
  have hgates0 : nGatesN (simPT a m (α * t) Q qbar ε UJg
      ([] : List (NInstr (PWr (Fin m) (Fin a ⊕ S) Z bT bP A) Y J))) ≤
      200 * (fDeg Q (α * t) qbar (ε / 4) + 1) * (a + m + simR Q (α * t) qbar (ε / 4) + 1) +
        84 * fDeg Q (α * t) qbar (ε / 4) * UJg.length := by
    refine (hcircP_nil_nGates (wireRel _ _ _ _) (slotSel _ _ _ _) UJg hUJg _).trans ?_
    rw [hJ, mul_one]
    have h84 : 12 * fDeg Q (α * t) qbar (ε / 4) * (7 * UJg.length) =
        84 * fDeg Q (α * t) qbar (ε / 4) * UJg.length := by ring
    rw [h84]
    exact Nat.add_le_add_right hG _
  have hsyn : nSynN 𝒢 (simPT a m (α * t) Q qbar ε UJg pc) ≤
      200 * (fDeg Q (α * t) qbar (ε / 4) + 1) * (a + m + simR Q (α * t) qbar (ε / 4) + 1) +
        84 * fDeg Q (α * t) qbar (ε / 4) * UJg.length :=
    (nSynN_hcircP_le 𝒢 hadj _ _ UJg pc hpcG _).trans hgates0
  have hδ : 0 < ε / 4 := by linarith
  have hδ1 : ε / 4 ≤ 1 := by linarith
  obtain ⟨hv, hk, -, hc⟩ := selBudget_spec hS hδ _ hvalidP
  refine ⟨hv, hk, fun p => ?_, hsyn, ?_, ?_, hdeg, hex, fun U hU0 hU => ?_⟩
  · rw [selSimT, hc p, simPT, hcircP_nCalls, hP]
  · -- the separated gate count
    set G₀ : ℕ := 200 * (fDeg Q (α * t) qbar (ε / 4) + 1) *
      (a + m + simR Q (α * t) qbar (ε / 4) + 1) + 84 * fDeg Q (α * t) qbar (ε / 4) * UJg.length
      with hG₀
    have h1 := selBudget_gates_log hS hc₀ hc₁ hL hδ hδ1 _ hvalidP (G₀ : ℝ)
      (by exact_mod_cast hsyn)
    have hNk : (nKeepN 𝒢 (simPT a m (α * t) Q qbar ε UJg pc) : ℝ) ≤
        6 * (fDeg Q (α * t) qbar (ε / 4) : ℝ) * nGatesN pc + G₀ := by
      have h2 : nKeepN 𝒢 (simPT a m (α * t) Q qbar ε UJg pc) ≤
          6 * fDeg Q (α * t) qbar (ε / 4) * nGatesN pc + G₀ := by
        have := nKeepN_le 𝒢 (simPT a m (α * t) Q qbar ε UJg pc)
        rw [hgates] at this
        omega
      exact_mod_cast h2
    exact sel_count_arith hNk h1
  · rw [Fintype.card_sum, card_HW, card_wire]
    simp only [Fintype.card_empty, add_zero]
    ring
  · have hio : ∀ ψ : Reg S R, ‖(io (P := Reg S R) (a := a) (m := m)
        (r := simR Q (α * t) qbar (ε / 4)) (K := a + m + 2 * simR Q (α * t) qbar (ε / 4))) ψ‖ =
        ‖ψ‖ :=
      fun ψ => by rw [io_apply, norm_bas]
    have herr' := herr U hU0 hU
    have hP' := hP
    have hnat : ‖nrun prim (simPT a m (α * t) Q qbar ε UJg pc) ∘L sysEmb (io (P := Reg S R)) -
        sysEmb (io (P := Reg S R)) ∘L U t‖ ≤
        ε / 2 + 6 * (fDeg Q (α * t) qbar (ε / 4) : ℝ) * ξ := by
      rw [simPT]
      generalize U t = Ut at herr' ⊢
      generalize SlotSim.simCircuitT a (α * t) Q qbar (ε / 4) m = l at herr' hvalid hsec hP' ⊢
      have h := hcircP_error (X' := Empty) prim hprim (wireRel _ _ _ _) (slotSel _ _ _ _) UJg hUJg
        pc hpcV hξ (slotFam D) hDu hDadj hpc' l hvalid io hio Ut _
        (prodOps_evalSel_slot UJg D l hsec) herr'
      refine h.trans (le_of_eq ?_)
      rw [hP']
      push_cast
      ring
    generalize U t = Ut at hnat ⊢
    unfold selSimT
    generalize simPT a m (α * t) Q qbar ε UJg pc = C at hvalidP hnat ⊢
    refine (selBudget_error_of hS hδ C hvalidP prim hprim _ ?_ Ut hnat).trans ?_
    · intro ψ
      exact (norm_sysEmb _ (fun φ => by rw [io_apply, norm_bas]) ψ).le
    · linarith

end Time

end

end SparseHamiltonian.GateSelective
