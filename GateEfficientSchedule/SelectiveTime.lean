import GateEfficientSchedule.Selective
import GateEfficientSchedule.TimeCircuit

/-!
# The time-dependent part of Theorem `hs:thm:gates` over a finite gate set with the manuscript's
schedule

The selective finite-set compilation (`GateEfficientSelective`) of the slot-selected circuit with
the manuscript's schedule (`simCircuitTMs`): the supplied slot-selected private circuit `pc` (and
its literal reverse-adjoint) is retained verbatim, and only the remaining exact gates are
synthesised. The error allocation is the manuscript's: `ε/2` for the exact-gate circuit (filter
`ε/4`, Cayley `ε/12`, freezing `ε/12`, samples `ε/12`, `gate_efficient_time_simulation_ms`),
`6 d ξ ≤ ε/4` for the private calls (`ξ = ε/(24d)`) and `ε/4` for the synthesis.

* `sel_time_simulation_ms`: valid gates of `𝒢` and primitive calls; exactly `6 d` times the
  primitive calls of `pc`; at most `G₀ = 200 (d+1)(a+m+r+1) + 84 d C_J` synthesised occurrences
  and `6 d |pc| + G₀ (c₁ log((G₀+1)/(ε/4)) + c₀ + 1)` gates; `|S| + (2a + 3m + 6r + 3) +
  (|Z| + bT + bP + A + 3) + |X|` qubits; a propagator exists, and for every propagator `U` the full
  output on the clean system embedding is within `ε` of `U(t)`.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateSchedule

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit GateCircuit.Sim GateNative GateSynth
  GateSelective
open GateSynthTrials (AdjClosed)
open GatePointerEncoding (wordEquivFin)
open scoped InnerProduct

variable {S Z Y J X : Type*} [Fintype S] [DecidableEq S] [Fintype Z] [DecidableEq Z]
  [Fintype Y] [DecidableEq Y] [Fintype X] [DecidableEq X] {bT bP A : ℕ}
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
variable {𝒢 : Set Kind} {L : ℝ → ℕ}

/-- The native slot-selected circuit with the manuscript's schedule and the supplied
slot-selected private circuit `pc`. -/
def simPTMs (a m : ℕ) (α t Q qbar ε : ℝ) (UJg : List (Gate (Fin a ⊕ S)))
    (pc : List (NInstr (PWr (Fin m) (Fin a ⊕ S) Z bT bP A) Y J)) :
    List (NInstr (HW (SimWireK a m Q (depthMs Q (α * t * qbar) ε)) S Empty Z bT bP A) Y J) :=
  hcircP (wireRel _ _ _ _) (slotSel _ _ _ _) UJg pc (simCircuitTMs a m α t Q qbar ε)

/-- **The selective finite-set slot-selected circuit with the manuscript's schedule**
(synthesis budget `ε/4`). -/
def selSimTMs (hS : Synthesis 𝒢 X L) (a m : ℕ) (α t Q qbar ε : ℝ)
    (UJg : List (Gate (Fin a ⊕ S))) (pc : List (NInstr (PWr (Fin m) (Fin a ⊕ S) Z bT bP A) Y J)) :
    List (NInstr (HW (SimWireK a m Q (depthMs Q (α * t * qbar) ε)) S Empty Z bT bP A ⊕ X) Y J) :=
  selBudget hS (ε / 4) (simPTMs a m α t Q qbar ε UJg pc)

set_option maxRecDepth 8192 in
/-- **Gate-efficient time-dependent simulation over a finite gate set with the manuscript's
schedule** (Theorem `hs:thm:gates`, time-dependent part, equations `hs:eq:gate-schedule`,
`hs:eq:timegrid`, `hs:eq:gate-Gzero`, `hs:eq:gate-total`). The private Cayley operations `D j` at
the slot words are implemented by one supplied valid circuit `pc` over `𝒢` within `ξ` of the
enable-controlled slot-selected operation on clean work wires, with `24 d ξ ≤ ε`. Under the
hypotheses of `gate_efficient_time_simulation_ms`, the synthesis hypothesis and an adjoint-closed
`𝒢`: the selective circuit consists of valid gates of `𝒢` and primitive calls, makes exactly
`6 d` times the primitive calls of `pc`, synthesises at most `G₀ = 200 (d+1)(a+m+r+1) + 84 d C_J`
gate occurrences, has at most `6 d |pc| + G₀ (c₁ log((G₀+1)/(ε/4)) + c₀ + 1)` gates and
`|S| + (2a + 3m + 6r + 3) + (|Z| + bT + bP + A + 3) + |X|` qubits, and for every propagator `U` of
the path its full output on the clean system embedding is within `ε` of `U(t)`. -/
theorem sel_time_simulation_ms (hS : Synthesis 𝒢 X L) (hadj : AdjClosed 𝒢) {c₀ c₁ : ℝ}
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
    (t α Λ β δ Q b qbar ε : ℝ) (ht : 0 ≤ t) (hα : 0 < α) (hΛ : 0 ≤ Λ) (hΛα : Λ ≤ α)
    (hQ : 1 ≤ Q) (hqQ : qbar ≤ Q) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hgrid : timegridMs α Λ β t ε ≤ 2 ^ m)
    (hD : ∀ k < 2 ^ m, IsUnitary (D k))
    (hRight : ∀ k < 2 ^ m, (1 - D k) ∘L R1 k = 1)
    (hLeft : ∀ k < 2 ^ m, R1 k ∘L (1 - D k) = 1) (hR1 : ∀ k < 2 ^ m, ‖R1 k‖ ≤ Q)
    (hBoundary : ∀ k < 2 ^ m, (UJop (R := R) UJg ∘L iota0 (P := Reg S R))† ∘L R1 k ∘L
      (UJop (R := R) UJg ∘L iota0 (P := Reg S R)) =
        (2 : ℂ)⁻¹ • (1 + Complex.I • ((α : ℂ)⁻¹ • Hs k)))
    (hEndpoint : ∀ k < 2 ^ m, ‖R1 k ∘L (UJop (R := R) UJg ∘L iota0 (P := Reg S R))‖ ≤ b)
    (hbq : b ^ 2 ≤ qbar / 2)
    (hSelf : ∀ k < 2 ^ m, star (Hs k) = Hs k) (hHs : ∀ k < 2 ^ m, ‖Hs k‖ ≤ Λ)
    (hPath : ∀ u ∈ Set.Icc 0 t, star (Hpath u) = Hpath u)
    (hLip : ∀ u ∈ Set.Icc 0 t, ∀ v ∈ Set.Icc 0 t, ‖Hpath u - Hpath v‖ ≤ β * |u - v|)
    (hVal : ∀ k : ℕ, k < 2 ^ m → ‖Hpath (k * t / 2 ^ m) - Hs k‖ ≤ δ)
    (hValBudget : 12 * t * δ ≤ ε)
    (hξε : 24 * (degreeMs Q (α * t * qbar) ε : ℝ) * ξ ≤ ε) :
    (∀ i ∈ selSimTMs hS a m α t Q qbar ε UJg pc, i.Valid) ∧
    (∀ g, NInstr.gate g ∈ selSimTMs hS a m α t Q qbar ε UJg pc → GateOf 𝒢 g) ∧
    (∀ p : J → Bool, nCallsN p (selSimTMs hS a m α t Q qbar ε UJg pc) =
      6 * degreeMs Q (α * t * qbar) ε * nCallsN p pc) ∧
    nSynN 𝒢 (simPTMs a m α t Q qbar ε UJg pc) ≤
      200 * (degreeMs Q (α * t * qbar) ε + 1) *
        (a + m + simRK Q (depthMs Q (α * t * qbar) ε) + 1) +
        84 * degreeMs Q (α * t * qbar) ε * UJg.length ∧
    (nGatesN (selSimTMs hS a m α t Q qbar ε UJg pc) : ℝ) ≤
      6 * (degreeMs Q (α * t * qbar) ε : ℝ) * nGatesN pc +
        ((200 * (degreeMs Q (α * t * qbar) ε + 1) *
          (a + m + simRK Q (depthMs Q (α * t * qbar) ε) + 1) +
          84 * degreeMs Q (α * t * qbar) ε * UJg.length : ℕ) : ℝ) *
        (c₁ * Real.log ((((200 * (degreeMs Q (α * t * qbar) ε + 1) *
          (a + m + simRK Q (depthMs Q (α * t * qbar) ε) + 1) +
          84 * degreeMs Q (α * t * qbar) ε * UJg.length : ℕ) : ℝ) + 1) / (ε / 4)) + c₀ + 1) ∧
    Fintype.card (HW (SimWireK a m Q (depthMs Q (α * t * qbar) ε)) S Empty Z bT bP A ⊕ X) =
      Fintype.card S + (2 * a + 3 * m + 6 * simRK Q (depthMs Q (α * t * qbar) ε) + 3) +
        (Fintype.card Z + bT + bP + A + 3) + Fintype.card X ∧
    (degreeMs Q (α * t * qbar) ε : ℝ) ≤
      128 * (α * t * qbar) + 32 * Q * (Real.logb 2 (4096 / ε) + 1) ∧
    (∃ U : ℝ → Reg S R →L[ℂ] Reg S R, U 0 = 1 ∧ TimeDependent.SolvesOn Hpath U 0 t) ∧
    ∀ U : ℝ → Reg S R →L[ℂ] Reg S R, U 0 = 1 → TimeDependent.SolvesOn Hpath U 0 t →
      ‖nrun prim (selSimTMs hS a m α t Q qbar ε UJg pc) ∘L
          (cleanEmb (X := X) ∘L sysEmb (io (P := Reg S R))) -
          (cleanEmb ∘L sysEmb (io (P := Reg S R))) ∘L U t‖ ≤ ε := by
  have hδ : 0 < ε / 4 := by linarith
  have hδ1 : ε / 4 ≤ 1 := by linarith
  have h6 : 6 * (degreeMs Q (α * t * qbar) ε : ℝ) * ξ ≤ ε / 4 := by linarith
  have hUJu : IsUnitary (UJop (R := R) UJg) := UJop_isUnitary UJg hUJg
  obtain ⟨hvalid, hP, hJ, hG, hW, hdeg, -, -, hex, herr⟩ :=
    gate_efficient_time_simulation_ms (P := Reg S R) a m (UJop (R := R) UJg) D R1 Hpath Hs t α
      Λ β δ Q b qbar ε ht hα hΛ hΛα hQ hqQ hε hε1 hgrid hUJu hD hRight hLeft hR1 hBoundary
      hEndpoint hbq hSelf hHs hPath hLip hVal hValBudget
  have hsec : ∀ i ∈ simCircuitTMs a m α t Q qbar ε, SecOK (wireRel _ _ _ _) i := by
    unfold simCircuitTMs simCircuitTK
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
  have hvalidP : ∀ i ∈ simPTMs a m α t Q qbar ε UJg pc, i.Valid :=
    hcircP_valid (X' := Empty) (wireRel _ _ _ _) (slotSel _ _ _ _) UJg hUJg pc hpcV _ hvalid
  have hgates : nGatesN (simPTMs a m α t Q qbar ε UJg pc) =
      nGatesN (simPTMs a m α t Q qbar ε UJg
        ([] : List (NInstr (PWr (Fin m) (Fin a ⊕ S) Z bT bP A) Y J))) +
        6 * degreeMs Q (α * t * qbar) ε * nGatesN pc := by
    rw [simPTMs, simPTMs, hcircP_nGates, hP]
  have hgates0 : nGatesN (simPTMs a m α t Q qbar ε UJg
      ([] : List (NInstr (PWr (Fin m) (Fin a ⊕ S) Z bT bP A) Y J))) ≤
      200 * (degreeMs Q (α * t * qbar) ε + 1) *
        (a + m + simRK Q (depthMs Q (α * t * qbar) ε) + 1) +
        84 * degreeMs Q (α * t * qbar) ε * UJg.length := by
    refine (hcircP_nil_nGates (wireRel _ _ _ _) (slotSel _ _ _ _) UJg hUJg _).trans ?_
    rw [hJ, mul_one]
    have h84 : 12 * degreeMs Q (α * t * qbar) ε * (7 * UJg.length) =
        84 * degreeMs Q (α * t * qbar) ε * UJg.length := by ring
    rw [h84]
    exact Nat.add_le_add_right hG _
  have hsyn : nSynN 𝒢 (simPTMs a m α t Q qbar ε UJg pc) ≤
      200 * (degreeMs Q (α * t * qbar) ε + 1) *
        (a + m + simRK Q (depthMs Q (α * t * qbar) ε) + 1) +
        84 * degreeMs Q (α * t * qbar) ε * UJg.length :=
    (nSynN_hcircP_le 𝒢 hadj _ _ UJg pc hpcG _).trans hgates0
  obtain ⟨hv, hk, -, hc⟩ := selBudget_spec hS hδ _ hvalidP
  refine ⟨hv, hk, fun p => ?_, hsyn, ?_, ?_, hdeg, hex, fun U hU0 hU => ?_⟩
  · rw [selSimTMs, hc p, simPTMs, hcircP_nCalls, hP]
  · -- the separated gate count
    set G₀ : ℕ := 200 * (degreeMs Q (α * t * qbar) ε + 1) *
      (a + m + simRK Q (depthMs Q (α * t * qbar) ε) + 1) +
      84 * degreeMs Q (α * t * qbar) ε * UJg.length with hG₀
    have h1 := selBudget_gates_log hS hc₀ hc₁ hL hδ hδ1 _ hvalidP (G₀ : ℝ)
      (by exact_mod_cast hsyn)
    have hNk : (nKeepN 𝒢 (simPTMs a m α t Q qbar ε UJg pc) : ℝ) ≤
        6 * (degreeMs Q (α * t * qbar) ε : ℝ) * nGatesN pc + G₀ := by
      have h2 : nKeepN 𝒢 (simPTMs a m α t Q qbar ε UJg pc) ≤
          6 * degreeMs Q (α * t * qbar) ε * nGatesN pc + G₀ := by
        have := nKeepN_le 𝒢 (simPTMs a m α t Q qbar ε UJg pc)
        rw [hgates] at this
        omega
      exact_mod_cast h2
    exact sel_count_arith hNk h1
  · rw [Fintype.card_sum, card_HW, hW]
    simp only [Fintype.card_empty, add_zero]
    ring
  · have hio : ∀ ψ : Reg S R, ‖(io (P := Reg S R) (a := a) (m := m)
        (r := simRK Q (depthMs Q (α * t * qbar) ε))
        (K := simKK a m Q (depthMs Q (α * t * qbar) ε))) ψ‖ = ‖ψ‖ :=
      fun ψ => by rw [io_apply, norm_bas]
    have herr' := herr U hU0 hU
    have hP' := hP
    have hnat : ‖nrun prim (simPTMs a m α t Q qbar ε UJg pc) ∘L sysEmb (io (P := Reg S R)) -
        sysEmb (io (P := Reg S R)) ∘L U t‖ ≤
        ε / 2 + 6 * (degreeMs Q (α * t * qbar) ε : ℝ) * ξ := by
      rw [simPTMs]
      generalize U t = Ut at herr' ⊢
      generalize simCircuitTMs a m α t Q qbar ε = l at herr' hvalid hsec hP' ⊢
      have h := hcircP_error (X' := Empty) prim hprim (wireRel _ _ _ _) (slotSel _ _ _ _) UJg hUJg
        pc hpcV hξ (slotFam D) hDu hDadj hpc' l hvalid io hio Ut _
        (prodOps_evalSel_slot UJg D l hsec) herr'
      refine h.trans (le_of_eq ?_)
      rw [hP']
      push_cast
      ring
    generalize U t = Ut at hnat ⊢
    unfold selSimTMs
    generalize simPTMs a m α t Q qbar ε UJg pc = C at hvalidP hnat ⊢
    refine (selBudget_error_of hS hδ C hvalidP prim hprim _ ?_ Ut hnat).trans ?_
    · intro ψ
      exact (norm_sysEmb _ (fun φ => by rw [io_apply, norm_bas]) ψ).le
    · clear herr hvalid hv hk hc hsyn hgates hgates0 hex hvalidP hP hJ hG hW hsec hDu hDadj hpc'
      linarith

end

end SparseHamiltonian.GateSchedule
