import GateEfficientSchedule.SelectiveTime
import GateEfficientSelective.HamBridge

/-!
# The manuscript-schedule endpoints over a finite gate set from the native data

The supplied finite-set controlled private circuit of `sel_simulation_ms` and
`sel_time_simulation_ms` can be constructed from the native data of `GateEfficientNative`: the
native implementation `privMacro nd ar` compiled selectively once (`GateSelective.privSel`, its
gates of `𝒢` and oracle calls retained, the remaining exact gates synthesised with the budget
`η`), which is within `ξ = η + 4ζ` of the enable-controlled private operation on clean work wires
(`GateSelective.privSel_spec`).

* `sel_simulation_ms_native`, `sel_time_simulation_ms_native`: the manuscript-schedule
  endpoints for this circuit under `24 d (η + 4ζ) ≤ ε`, with exactly `12 d` times the primitive
  calls of the compute circuit `V`, `|privSel| ≤ nKeepN + K L(η/(K+1))` and
  `K ≤ 2 nSynN V + 2 |arith| + 2 bP + bT + 1`.
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
  [Fintype Y] [DecidableEq Y] [Fintype X] [DecidableEq X]
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
variable {𝒢 : Set Kind} {L : ℝ → ℕ}

set_option maxRecDepth 8192 in
/-- **Theorem `hs:thm:gates` over a finite gate set with the manuscript's schedule, from the
native data**: `sel_simulation_ms` for the selectively compiled native
private circuit `privSel hS η nd ar`, under the hypotheses of `GateNative.native_simulation` and
`24 d (η + 4ζ) ≤ ε`. -/
theorem sel_simulation_ms_native (hS : Synthesis 𝒢 X L) (hadj : AdjClosed 𝒢) {c₀ c₁ : ℝ}
    (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁)
    (hL : ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 → (L ζ : ℝ) ≤ c₁ * Real.log (1 / ζ) + c₀)
    (a : ℕ) (prim : J → Reg Y R →L[ℂ] Reg Y R) (hprim : ∀ j, IsUnitary (prim j))
    (UJg : List (Gate (Fin a ⊕ S))) (hUJg : ∀ g ∈ UJg, GateOK 3 g)
    (nd : NativeOp Empty (Fin a ⊕ S) Z Y J) (hnd : nd.Public)
    (ar : Arith (NB Empty (Fin a ⊕ S) Z)) (ζ η : ℝ) (hζ : 0 ≤ ζ) (hη : 0 < η)
    (har : ArithOK ar (Sum.inl (Sum.inr nd.o)) nd.dec ζ)
    (D R1 : Anc a (Reg S R) →L[ℂ] Anc a (Reg S R)) (H : Reg S R →L[ℂ] Reg S R)
    (hD : IsUnitary D) (hN : NativeOK prim nd (selOp (fun _ : Cfg Empty => D)))
    (τ Q b qbar ε : ℝ) (hτ : 0 ≤ τ) (hQ : 1 ≤ Q)
    (hRight : (1 - D) ∘L R1 = 1) (hLeft : R1 ∘L (1 - D) = 1) (hR1 : ‖R1‖ ≤ Q)
    (hBoundary : (UJop (R := R) UJg ∘L iota0 (P := Reg S R))† ∘L R1 ∘L
      (UJop (R := R) UJg ∘L iota0 (P := Reg S R)) = (2 : ℂ)⁻¹ • (1 + Complex.I • H))
    (hSelf : star H = H) (hH : ‖H‖ ≤ 1)
    (hEndpoint : ‖R1 ∘L (UJop (R := R) UJg ∘L iota0 (P := Reg S R))‖ ≤ b)
    (hbq : b ^ 2 ≤ qbar / 2) (hqQ : qbar ≤ Q) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hξε : 24 * (degreeMs Q (τ * qbar) ε : ℝ) * (η + 4 * ζ) ≤ ε) :
    (∀ i ∈ selSimMs hS a τ Q qbar ε UJg (privSel hS η nd ar), i.Valid) ∧
    (∀ g, NInstr.gate g ∈ selSimMs hS a τ Q qbar ε UJg (privSel hS η nd ar) → GateOf 𝒢 g) ∧
    (∀ p : J → Bool, nCallsN p (selSimMs hS a τ Q qbar ε UJg (privSel hS η nd ar)) =
      12 * degreeMs Q (τ * qbar) ε * nCallsN p nd.V) ∧
    (nGatesN (selSimMs hS a τ Q qbar ε UJg (privSel hS η nd ar)) : ℝ) ≤
      6 * (degreeMs Q (τ * qbar) ε : ℝ) * nGatesN (privSel hS η nd ar) +
        ((200 * (degreeMs Q (τ * qbar) ε + 1) * (a + slotMs τ ε + rMs Q τ qbar ε + 1) +
          84 * degreeMs Q (τ * qbar) ε * UJg.length : ℕ) : ℝ) *
        (c₁ * Real.log ((((200 * (degreeMs Q (τ * qbar) ε + 1) *
          (a + slotMs τ ε + rMs Q τ qbar ε + 1) +
          84 * degreeMs Q (τ * qbar) ε * UJg.length : ℕ) : ℝ) + 1) / (ε / 4)) + c₀ + 1) ∧
    nGatesN (privSel hS η nd ar) ≤ nKeepN 𝒢 (privMacro nd ar) +
      nSynN 𝒢 (privMacro nd ar) * L (η / (nSynN 𝒢 (privMacro nd ar) + 1)) ∧
    nSynN 𝒢 (privMacro nd ar) ≤
      2 * nSynN 𝒢 nd.V + 2 * ar.circ.length + (2 * ar.bP + ar.bT + 1) ∧
    Fintype.card (HW (SimWireMs a Q τ qbar ε) S Empty (Z ⊕ X) ar.bT ar.bP ar.A ⊕ X) =
      Fintype.card S + (2 * a + 3 * slotMs τ ε + 6 * rMs Q τ qbar ε + 3) +
        (Fintype.card Z + Fintype.card X + ar.bT + ar.bP + ar.A + 3) + Fintype.card X ∧
    ‖nrun prim (selSimMs hS a τ Q qbar ε UJg (privSel hS η nd ar)) ∘L
        (cleanEmb (X := X) ∘L sysEmb (io (P := Reg S R))) -
        (cleanEmb ∘L sysEmb (io (P := Reg S R))) ∘L
          NormedSpace.exp ((-Complex.I * (τ : ℂ)) • H)‖ ≤ ε := by
  obtain ⟨hpV, hpG, hpN, hpC, hpA⟩ := privSel_spec (R := R) hS hη nd hnd ar hζ har
  have hξ : 0 ≤ η + 4 * ζ := by linarith
  obtain ⟨hv, hk, hcalls, -, hgates, hcard, herr, -⟩ := sel_simulation_ms hS hadj hc₀ hc₁ hL a
    prim hprim UJg hUJg (privSel hS η nd ar) hpV hpG (η + 4 * ζ) hξ D R1 H hD
    (hpA prim hprim _ hN) τ Q b qbar ε hτ hQ hRight hLeft hR1 hBoundary hSelf hH hEndpoint hbq hqQ
    hε hε1 hξε
  refine ⟨hv, hk, fun p => ?_, hgates, hpN, nSynN_privMacro_le hadj nd ar, ?_, ?_⟩
  · rw [hcalls p, hpC p]
    ring
  · rw [hcard, Fintype.card_sum]
  · -- the same bound, up to the instance paths of the joined scratch `Z ⊕ X`
    convert herr using 4

set_option maxRecDepth 8192 in
/-- **Package extension: Theorem `hs:thm:time` with the circuit of `hs:thm:gates` (single-label
case of Lemma `ode:lem:gate-select`), over a finite gate set with the manuscript's schedule, from
the native data**: `sel_time_simulation_ms` for the selectively compiled
slot-selected native private circuit, under `24 d (η + 4ζ) ≤ ε`. -/
theorem sel_time_simulation_ms_native (hS : Synthesis 𝒢 X L) (hadj : AdjClosed 𝒢) {c₀ c₁ : ℝ}
    (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁)
    (hL : ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 → (L ζ : ℝ) ≤ c₁ * Real.log (1 / ζ) + c₀)
    (a m : ℕ) (prim : J → Reg Y R →L[ℂ] Reg Y R) (hprim : ∀ j, IsUnitary (prim j))
    (UJg : List (Gate (Fin a ⊕ S))) (hUJg : ∀ g ∈ UJg, GateOK 3 g)
    (nd : NativeOp (Fin m) (Fin a ⊕ S) Z Y J) (hnd : nd.Public)
    (ar : Arith (NB (Fin m) (Fin a ⊕ S) Z)) (ζ η : ℝ) (hζ : 0 ≤ ζ) (hη : 0 < η)
    (har : ArithOK ar (Sum.inl (Sum.inr nd.o)) nd.dec ζ)
    (D R1 : ℕ → Anc a (Reg S R) →L[ℂ] Anc a (Reg S R))
    (hN : NativeOK prim nd (selOp (fun w : Cfg (Fin m) => D (wordEquivFin m w))))
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
    (hξε : 24 * (degreeMs Q (α * t * qbar) ε : ℝ) * (η + 4 * ζ) ≤ ε) :
    (∀ i ∈ selSimTMs hS a m α t Q qbar ε UJg (privSel hS η nd ar), i.Valid) ∧
    (∀ g, NInstr.gate g ∈ selSimTMs hS a m α t Q qbar ε UJg (privSel hS η nd ar) →
      GateOf 𝒢 g) ∧
    (∀ p : J → Bool, nCallsN p (selSimTMs hS a m α t Q qbar ε UJg (privSel hS η nd ar)) =
      12 * degreeMs Q (α * t * qbar) ε * nCallsN p nd.V) ∧
    (nGatesN (selSimTMs hS a m α t Q qbar ε UJg (privSel hS η nd ar)) : ℝ) ≤
      6 * (degreeMs Q (α * t * qbar) ε : ℝ) * nGatesN (privSel hS η nd ar) +
        ((200 * (degreeMs Q (α * t * qbar) ε + 1) *
          (a + m + simRK Q (depthMs Q (α * t * qbar) ε) + 1) +
          84 * degreeMs Q (α * t * qbar) ε * UJg.length : ℕ) : ℝ) *
        (c₁ * Real.log ((((200 * (degreeMs Q (α * t * qbar) ε + 1) *
          (a + m + simRK Q (depthMs Q (α * t * qbar) ε) + 1) +
          84 * degreeMs Q (α * t * qbar) ε * UJg.length : ℕ) : ℝ) + 1) / (ε / 4)) + c₀ + 1) ∧
    nGatesN (privSel hS η nd ar) ≤ nKeepN 𝒢 (privMacro nd ar) +
      nSynN 𝒢 (privMacro nd ar) * L (η / (nSynN 𝒢 (privMacro nd ar) + 1)) ∧
    nSynN 𝒢 (privMacro nd ar) ≤
      2 * nSynN 𝒢 nd.V + 2 * ar.circ.length + (2 * ar.bP + ar.bT + 1) ∧
    ∀ U : ℝ → Reg S R →L[ℂ] Reg S R, U 0 = 1 → TimeDependent.SolvesOn Hpath U 0 t →
      ‖nrun prim (selSimTMs hS a m α t Q qbar ε UJg (privSel hS η nd ar)) ∘L
          (cleanEmb (X := X) ∘L sysEmb (io (P := Reg S R))) -
          (cleanEmb ∘L sysEmb (io (P := Reg S R))) ∘L U t‖ ≤ ε := by
  obtain ⟨hpV, hpG, hpN, hpC, hpA⟩ := privSel_spec (R := R) hS hη nd hnd ar hζ har
  have hξ : 0 ≤ η + 4 * ζ := by linarith
  obtain ⟨hv, hk, hcalls, -, hgates, -, -, -, herr⟩ := sel_time_simulation_ms hS hadj hc₀ hc₁ hL
    a m prim hprim UJg hUJg (privSel hS η nd ar) hpV hpG (η + 4 * ζ) hξ D R1
    (hpA prim hprim _ hN) Hpath Hs t α Λ β δ Q b qbar ε ht hα hΛ hΛα hQ hqQ hε hε1 hgrid hD
    hRight hLeft hR1 hBoundary hEndpoint hbq hSelf hHs hPath hLip hVal hValBudget hξε
  refine ⟨hv, hk, fun p => ?_, hgates, hpN, nSynN_privMacro_le hadj nd ar,
    fun U hU0 hU => ?_⟩
  · rw [hcalls p, hpC p]
    ring
  · -- the same bound, up to the instance paths of the joined scratch `Z ⊕ X`
    convert herr U hU0 hU using 4

end

end SparseHamiltonian.GateSchedule
