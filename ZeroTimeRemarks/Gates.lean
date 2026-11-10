import GateEfficientNative.Hamiltonian.Theorem

/-!
# Theorem `hs:thm:gates` at zero time

Theorem `hs:thm:gates` of the accompanying paper states "This is a time-independent result; at
`t = 0` the identity suffices." The released gate-level endpoints build one circuit from the public
data for every `τ ≥ 0` (`GateCircuit.Sim.gate_efficient_simulation`, the slot-selected
`GateCircuit.SlotSim.gate_efficient_time_simulation`) and their native forms
(`GateNative.native_simulation`, `GateNative.native_simulation_signed` for every real time,
`GateNative.native_time_simulation`); at zero time these circuits still contain `6 d` private calls
and `12 d` calls of `U_J`, with a positive filter degree `d`. This file states the remark in the
same gate models: the empty circuit, over the same wires and with the same clean system embedding,
has no elementary gate, no private or primitive call and no `U_J` call, and its full output error is
exactly `0` at zero time.

* `circuit`, `simulation_nonneg`: exact gates, constant Hamiltonian, every `τ ≥ 0`.
* `circuitT`, `time_simulation_nonneg`: exact gates, slot-selected time-dependent circuit,
  every `t ≥ 0`.
* `nativeCircuit`, `native_simulation_nonneg`: native gates, constant Hamiltonian, every
  `τ ≥ 0`.
* `nativeCircuitSigned`, `native_simulation_signed_zero`: native gates, constant Hamiltonian,
  every real `t`.
* `nativeCircuitT`, `native_time_simulation_nonneg`: native gates, time-dependent circuit,
  every `t ≥ 0`.

In each combined form the circuit is the empty circuit at zero time and the released circuit
otherwise, every count is `0` at zero time and the released count otherwise, the error is at
most `ε` and, at zero time, exactly `0`. The other conclusions of the released theorems (wire
counts, degree and schedule bounds, existence of a propagator) do not depend on the circuit and
are kept unchanged.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.ZeroTimeRemarks.Gates

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit GateCircuit.Sim GateNative
open scoped InnerProduct BigOperators SparseHamiltonian.GateNative

/-- The evolution `exp(-i t H)` is the identity at `t = 0`, on every complex Banach space
(`hs:thm:gates`). -/
theorem exp_zero_time {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (t : ℝ) (ht : t = 0) (H : E →L[ℂ] E) :
    NormedSpace.exp ((-Complex.I * (t : ℂ)) • H) = 1 := by
  rw [ht, Complex.ofReal_zero, mul_zero, zero_smul]
  exact NormedSpace.exp_zero

/-- An encoding commutes with the identity: `‖1 ∘ ι - ι ∘ 1‖ = 0` (`hs:thm:gates`). -/
theorem identity_comp_error_eq_zero {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (ι : E →L[ℂ] F) :
    ‖(1 : F →L[ℂ] F) ∘L ι - ι ∘L (1 : E →L[ℂ] E)‖ = 0 := by
  have h0 : (1 : F →L[ℂ] F) ∘L ι - ι ∘L (1 : E →L[ℂ] E) = 0 := by
    rw [sub_eq_zero]
    rfl
  rw [h0]
  exact ContinuousLinearMap.opNorm_zero

/-- An encoding commutes with the identity: `‖1 ∘ ι - ι ∘ 1‖ ≤ ε` for every `ε ≥ 0`
(`hs:thm:gates`). -/
theorem identity_comp_error_le {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (ι : E →L[ℂ] F) (ε : ℝ) (hε : 0 ≤ ε) :
    ‖(1 : F →L[ℂ] F) ∘L ι - ι ∘L (1 : E →L[ℂ] E)‖ ≤ ε :=
  (identity_comp_error_eq_zero ι).le.trans hε

/-! ### Exact gates, constant Hamiltonian -/

section Exact

/-- The circuit of Theorem `hs:thm:gates` for every `τ ≥ 0`: the empty (identity) circuit at
`τ = 0` and the released `simCircuit` otherwise, on the same wires. -/
def circuit (a : ℕ) (τ Q qbar ε : ℝ) : List (Instr (SimWire a Q τ qbar ε)) :=
  if τ = 0 then [] else simCircuit a τ Q qbar ε

/-- **Theorem `hs:thm:gates` (exact gates) for every `τ ≥ 0`.** Under the hypotheses of the
released `gate_efficient_simulation`, the circuit `circuit a τ Q qbar ε` consists of valid
elementary instructions, makes `0` private Cayley calls and `0` calls of `U_J` if `τ = 0`, and
exactly `6 d` and `12 d` otherwise, has `0` elementary gates if `τ = 0` and at most
`200 (d+1)(a+m+r+1)` otherwise, and its full output on clean inputs is within `ε` of
`exp(-iτH)`; at `τ = 0` the error is exactly `0`. The wire count and the degree and schedule
bounds of the released theorem are unchanged. -/
theorem simulation_nonneg (a : ℕ) {P : Type*} [NormedAddCommGroup P]
    [InnerProductSpace ℂ P] [CompleteSpace P]
    (UJ D R1 : Anc a P →L[ℂ] Anc a P) (H : P →L[ℂ] P)
    (hUJ : IsUnitary UJ) (hD : IsUnitary D)
    (τ Q b qbar ε : ℝ) (hτ : 0 ≤ τ) (hQ : 1 ≤ Q)
    (hRight : (1 - D) ∘L R1 = 1) (hLeft : R1 ∘L (1 - D) = 1) (hR1 : ‖R1‖ ≤ Q)
    (hBoundary : (UJ ∘L iota0)† ∘L R1 ∘L (UJ ∘L iota0) = (2 : ℂ)⁻¹ • (1 + Complex.I • H))
    (hSelf : star H = H) (hH : ‖H‖ ≤ 1)
    (hEndpoint : ‖R1 ∘L (UJ ∘L iota0)‖ ≤ b) (hbq : b ^ 2 ≤ qbar / 2) (hqQ : qbar ≤ Q)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (∀ g ∈ circuit a τ Q qbar ε, g.Valid Wire.anc) ∧
    nPriv (circuit a τ Q qbar ε) = (if τ = 0 then 0 else 6 * fDeg Q τ qbar ε) ∧
    nUJ (circuit a τ Q qbar ε) = (if τ = 0 then 0 else 12 * fDeg Q τ qbar ε) ∧
    nGates (circuit a τ Q qbar ε) ≤
      (if τ = 0 then 0 else
        200 * (fDeg Q τ qbar ε + 1) * (a + simM τ ε + simR Q τ qbar ε + 1)) ∧
    Fintype.card (SimWire a Q τ qbar ε) = 2 * a + 3 * simM τ ε + 6 * simR Q τ qbar ε + 3 ∧
    ‖run (simSem UJ D) (circuit a τ Q qbar ε) ∘L io -
        io ∘L NormedSpace.exp ((-Complex.I * (τ : ℂ)) • H)‖ ≤ ε ∧
    (τ = 0 → ‖run (simSem UJ D) (circuit a τ Q qbar ε) ∘L io -
        io ∘L NormedSpace.exp ((-Complex.I * (τ : ℂ)) • H)‖ = 0) ∧
    (fDeg Q τ qbar ε : ℝ) ≤ 128 * (τ * qbar + Q * (1 + Real.log (1 / (ε / 3)))) ∧
    TimeSchedule.steps τ (ε / 3) ≤ 2 ^ simM τ ε ∧
    2 ^ simM τ ε < 2 * TimeSchedule.steps τ (ε / 3) ∧
    2 * fDeg Q τ qbar ε + 2 ≤ 2 ^ simR Q τ qbar ε ∧
    2 ^ simR Q τ qbar ε ≤ 4 * (fDeg Q τ qbar ε + 1) := by
  obtain ⟨hvalid, hP, hJ, hG, hW, herr, hdeg, hm1, hm2, hr1, hr2⟩ := gate_efficient_simulation
    a UJ D R1 H hUJ hD τ Q b qbar ε hτ hQ hRight hLeft hR1 hBoundary hSelf hH hEndpoint hbq hqQ
    hε hε1
  by_cases hτ0 : τ = 0
  · have hc : circuit a τ Q qbar ε = [] := if_pos hτ0
    rw [hc, if_pos hτ0, if_pos hτ0, if_pos hτ0, run_nil, exp_zero_time τ hτ0]
    exact ⟨fun g hg => absurd hg List.not_mem_nil, rfl, rfl, le_rfl, hW,
      identity_comp_error_le _ ε hε.le, fun _ => identity_comp_error_eq_zero _, hdeg, hm1, hm2,
      hr1, hr2⟩
  · have hc : circuit a τ Q qbar ε = simCircuit a τ Q qbar ε := if_neg hτ0
    rw [hc, if_neg hτ0, if_neg hτ0, if_neg hτ0]
    exact ⟨hvalid, hP, hJ, hG, hW, herr, fun h => absurd h hτ0, hdeg, hm1, hm2, hr1, hr2⟩

end Exact

/-! ### Exact gates, time-dependent Hamiltonian -/

section ExactTime

/-- The slot-selected time-dependent circuit for every `t ≥ 0`: the empty (identity) circuit at
`t = 0` and the released `simCircuitT` otherwise, on the same wires (`hs:thm:gates`). -/
def circuitT (a m : ℕ) (α t Q qbar ε : ℝ) :
    List (Instr (Wire a m (simR Q (α * t) qbar (ε / 2))
      (a + m + 2 * simR Q (α * t) qbar (ε / 2)))) :=
  if t = 0 then [] else SlotSim.simCircuitT a (α * t) Q qbar (ε / 2) m

/-- **The time-dependent gate-level simulation (Theorem `hs:thm:time` with the circuit of
`hs:thm:gates`) (exact gates) for every `t ≥ 0`.** Under the hypotheses of the released
`SlotSim.gate_efficient_time_simulation`, the circuit `circuitT a m α t Q qbar ε` consists of valid
instructions, makes `0` slot-selected private calls and `0` calls of `U_J` if `t = 0`, and exactly
`6 d` and `12 d` otherwise, has `0` elementary gates if `t = 0` and at most `200 (d+1)(a+m+r+1)`
otherwise, and for every propagator `U` of the path its full output on clean inputs is within `ε` of
`U(t)`; at `t = 0` the error is exactly `0`. The wire count, the degree bounds and the existence of
a propagator are those of the released theorem. -/
theorem time_simulation_nonneg (a m : ℕ) {P : Type*} [NormedAddCommGroup P]
    [InnerProductSpace ℂ P] [CompleteSpace P] (UJ : Vsp a P →L[ℂ] Vsp a P)
    (D R1 : ℕ → Vsp a P →L[ℂ] Vsp a P) (Hpath : ℝ → P →L[ℂ] P) (Hs : ℕ → P →L[ℂ] P)
    (t α β δ Q b qbar ε : ℝ) (ht : 0 ≤ t) (hα : 0 < α) (hβ : 0 ≤ β) (hQ : 1 ≤ Q)
    (hqQ : qbar ≤ Q) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hCayley : TimeSchedule.steps (α * t) (ε / 6) ≤ 2 ^ m)
    (hFreeze : 4 * β * t ^ 2 ≤ ε * 2 ^ m)
    (hUJ : IsUnitary UJ) (hD : ∀ k < 2 ^ m, IsUnitary (D k))
    (hRight : ∀ k < 2 ^ m, (1 - D k) ∘L R1 k = 1)
    (hLeft : ∀ k < 2 ^ m, R1 k ∘L (1 - D k) = 1) (hR1 : ∀ k < 2 ^ m, ‖R1 k‖ ≤ Q)
    (hBoundary : ∀ k < 2 ^ m, (UJ ∘L iota0)† ∘L R1 k ∘L (UJ ∘L iota0) =
      (2 : ℂ)⁻¹ • (1 + Complex.I • ((α : ℂ)⁻¹ • Hs k)))
    (hEndpoint : ∀ k < 2 ^ m, ‖R1 k ∘L (UJ ∘L iota0)‖ ≤ b) (hbq : b ^ 2 ≤ qbar / 2)
    (hSelf : ∀ k < 2 ^ m, star (Hs k) = Hs k) (hHs : ∀ k < 2 ^ m, ‖Hs k‖ ≤ α)
    (hPath : ∀ u ∈ Set.Icc 0 t, star (Hpath u) = Hpath u)
    (hLip : ∀ u ∈ Set.Icc 0 t, ∀ v ∈ Set.Icc 0 t, ‖Hpath u - Hpath v‖ ≤ β * |u - v|)
    (hVal : ∀ k : ℕ, k < 2 ^ m → ‖Hpath (k * t / 2 ^ m) - Hs k‖ ≤ δ)
    (hValBudget : 4 * t * δ ≤ ε) :
    (∀ g ∈ circuitT a m α t Q qbar ε, g.Valid Wire.anc) ∧
    nPriv (circuitT a m α t Q qbar ε) =
      (if t = 0 then 0 else 6 * fDeg Q (α * t) qbar (ε / 2)) ∧
    nUJ (circuitT a m α t Q qbar ε) =
      (if t = 0 then 0 else 12 * fDeg Q (α * t) qbar (ε / 2)) ∧
    nGates (circuitT a m α t Q qbar ε) ≤
      (if t = 0 then 0 else
        200 * (fDeg Q (α * t) qbar (ε / 2) + 1) * (a + m + simR Q (α * t) qbar (ε / 2) + 1)) ∧
    Fintype.card (Wire a m (simR Q (α * t) qbar (ε / 2))
        (a + m + 2 * simR Q (α * t) qbar (ε / 2))) =
      2 * a + 3 * m + 6 * simR Q (α * t) qbar (ε / 2) + 3 ∧
    (fDeg Q (α * t) qbar (ε / 2) : ℝ) ≤ 128 * (α * t * qbar + Q * (1 + Real.log (6 / ε))) ∧
    2 * fDeg Q (α * t) qbar (ε / 2) + 2 ≤ 2 ^ simR Q (α * t) qbar (ε / 2) ∧
    2 ^ simR Q (α * t) qbar (ε / 2) ≤ 4 * (fDeg Q (α * t) qbar (ε / 2) + 1) ∧
    (∃ U : ℝ → P →L[ℂ] P, U 0 = 1 ∧ TimeDependent.SolvesOn Hpath U 0 t) ∧
    (∀ U : ℝ → P →L[ℂ] P, U 0 = 1 → TimeDependent.SolvesOn Hpath U 0 t →
      ‖SlotSim.runT UJ D (circuitT a m α t Q qbar ε) ∘L io - io ∘L U t‖ ≤ ε) ∧
    (t = 0 → ∀ U : ℝ → P →L[ℂ] P, U 0 = 1 → TimeDependent.SolvesOn Hpath U 0 t →
      ‖SlotSim.runT UJ D (circuitT a m α t Q qbar ε) ∘L io - io ∘L U t‖ = 0) := by
  obtain ⟨hvalid, hP, hJ, hG, hW, hdeg, hr1, hr2, hex, herr⟩ :=
    SlotSim.gate_efficient_time_simulation a m UJ D R1 Hpath Hs t α β δ Q b qbar ε ht hα hβ
      hQ hqQ hε hε1 hCayley hFreeze hUJ hD hRight hLeft hR1 hBoundary hEndpoint hbq hSelf hHs
      hPath hLip hVal hValBudget
  by_cases ht0 : t = 0
  · have hc : circuitT a m α t Q qbar ε = [] := if_pos ht0
    rw [hc, if_pos ht0, if_pos ht0, if_pos ht0, SlotSim.runT_nil]
    refine ⟨fun g hg => absurd hg List.not_mem_nil, rfl, rfl, le_rfl, hW, hdeg, hr1, hr2, hex,
      fun U hU0 _ => ?_, fun _ U hU0 _ => ?_⟩
    · have hUt : U t = 1 := by rw [ht0, hU0]
      rw [hUt]
      exact identity_comp_error_le _ ε hε.le
    · have hUt : U t = 1 := by rw [ht0, hU0]
      rw [hUt]
      exact identity_comp_error_eq_zero _
  · have hc : circuitT a m α t Q qbar ε = SlotSim.simCircuitT a (α * t) Q qbar (ε / 2) m :=
      if_neg ht0
    rw [hc, if_neg ht0, if_neg ht0, if_neg ht0]
    exact ⟨hvalid, hP, hJ, hG, hW, hdeg, hr1, hr2, hex, herr, fun h => absurd h ht0⟩

end ExactTime

/-! ### Native gates -/

section Native

variable {S Z Y J : Type*} [Fintype S] [DecidableEq S] [Fintype Z] [DecidableEq Z] [Fintype Y]
  [DecidableEq Y]
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- The native circuit of Theorem `hs:thm:gates` for every `τ ≥ 0`: the empty (identity)
circuit at `τ = 0` and the released `nativeSim` otherwise, on the same wires. -/
def nativeCircuit (a : ℕ) (τ Q qbar ε : ℝ) (UJg : List (Gate (Fin a ⊕ S)))
    (nd : NativeOp Empty (Fin a ⊕ S) Z Y J) (ar : Arith (NB Empty (Fin a ⊕ S) Z)) :
    List (NInstr (HW (SimWire a Q τ qbar (ε / 2)) S Empty Z ar.bT ar.bP ar.A) Y J) :=
  if τ = 0 then [] else nativeSim a τ Q qbar ε UJg nd ar

/-- **Native Theorem `hs:thm:gates` for every `τ ≥ 0`, with the identity circuit at `τ = 0`.**
Under the hypotheses of the released `native_simulation`, the circuit
`nativeCircuit a τ Q qbar ε UJg nd ar` consists of valid instructions, makes `0` primitive calls
if `τ = 0` and exactly `12 d` times the calls of the compute circuit `V` otherwise, has `0`
elementary gates if `τ = 0` and at most `200 (d+1)(a+m+r+1) + 84 d C_J + 6 d G_C` otherwise,
and its full output on the system embedding is within `ε` of `exp(-iτH)`; at `τ = 0` the error
is exactly `0`. The wire count and the degree and schedule bounds of the released theorem are
unchanged. -/
theorem native_simulation_nonneg (a : ℕ) (prim : J → Reg Y R →L[ℂ] Reg Y R)
    (hprim : ∀ j, IsUnitary (prim j))
    (UJg : List (Gate (Fin a ⊕ S))) (hUJg : ∀ g ∈ UJg, GateOK 3 g)
    (nd : NativeOp Empty (Fin a ⊕ S) Z Y J) (hnd : nd.Public)
    (ar : Arith (NB Empty (Fin a ⊕ S) Z)) (ζ : ℝ) (hζ : 0 ≤ ζ)
    (har : ArithOK ar (Sum.inl (Sum.inr nd.o)) nd.dec ζ)
    (D R1 : Anc a (Reg S R) →L[ℂ] Anc a (Reg S R)) (H : Reg S R →L[ℂ] Reg S R)
    (hD : IsUnitary D) (hN : NativeOK prim nd (selOp (fun _ : Cfg Empty => D)))
    (τ Q b qbar ε : ℝ) (hτ : 0 ≤ τ) (hQ : 1 ≤ Q)
    (hRight : (1 - D) ∘L R1 = 1) (hLeft : R1 ∘L (1 - D) = 1) (hR1 : ‖R1‖ ≤ Q)
    (hBoundary : (UJop (R := R) UJg ∘L iota0 (P := Reg S R))† ∘L R1 ∘L
      (UJop (R := R) UJg ∘L iota0 (P := Reg S R)) = (2 : ℂ)⁻¹ • (1 + Complex.I • H))
    (hSelf : star H = H) (hH : ‖H‖ ≤ 1)
    (hEndpoint : ‖R1 ∘L (UJop (R := R) UJg ∘L iota0 (P := Reg S R))‖ ≤ b)
    (hbq : b ^ 2 ≤ qbar / 2) (hqQ : qbar ≤ Q)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hζε : 48 * (fDeg Q τ qbar (ε / 2) : ℝ) * ζ ≤ ε) :
    (∀ i ∈ nativeCircuit a τ Q qbar ε UJg nd ar, i.Valid) ∧
    (∀ p : J → Bool, nCallsN p (nativeCircuit a τ Q qbar ε UJg nd ar) =
      (if τ = 0 then 0 else 12 * fDeg Q τ qbar (ε / 2) * nCallsN p nd.V)) ∧
    nGatesN (nativeCircuit a τ Q qbar ε UJg nd ar) ≤
      (if τ = 0 then 0 else
        200 * (fDeg Q τ qbar (ε / 2) + 1) * (a + simM τ (ε / 2) + simR Q τ qbar (ε / 2) + 1) +
          84 * fDeg Q τ qbar (ε / 2) * UJg.length +
          6 * fDeg Q τ qbar (ε / 2) *
            (2 * nGatesN nd.V + 2 * ar.circ.length + (2 * ar.bP + ar.bT + 1))) ∧
    Fintype.card (HW (SimWire a Q τ qbar (ε / 2)) S Empty Z ar.bT ar.bP ar.A) =
      Fintype.card S + (2 * a + 3 * simM τ (ε / 2) + 6 * simR Q τ qbar (ε / 2) + 3) +
        (Fintype.card Z + ar.bT + ar.bP + ar.A + 3) ∧
    ‖nrun prim (nativeCircuit a τ Q qbar ε UJg nd ar) ∘L sysEmb (io (P := Reg S R)) -
        sysEmb (io (P := Reg S R)) ∘L NormedSpace.exp ((-Complex.I * (τ : ℂ)) • H)‖ ≤ ε ∧
    (τ = 0 → ‖nrun prim (nativeCircuit a τ Q qbar ε UJg nd ar) ∘L sysEmb (io (P := Reg S R)) -
        sysEmb (io (P := Reg S R)) ∘L NormedSpace.exp ((-Complex.I * (τ : ℂ)) • H)‖ = 0) ∧
    (fDeg Q τ qbar (ε / 2) : ℝ) ≤ 128 * (τ * qbar + Q * (1 + Real.log (6 / ε))) ∧
    TimeSchedule.steps τ (ε / 6) ≤ 2 ^ simM τ (ε / 2) ∧
    2 ^ simM τ (ε / 2) < 2 * TimeSchedule.steps τ (ε / 6) ∧
    2 * fDeg Q τ qbar (ε / 2) + 2 ≤ 2 ^ simR Q τ qbar (ε / 2) ∧
    2 ^ simR Q τ qbar (ε / 2) ≤ 4 * (fDeg Q τ qbar (ε / 2) + 1) := by
  obtain ⟨hvalid, hcalls, hgates, hW, herr, hdeg, hm1, hm2, hr1, hr2⟩ := native_simulation a
    prim hprim UJg hUJg nd hnd ar ζ hζ har D R1 H hD hN τ Q b qbar ε hτ hQ hRight hLeft hR1
    hBoundary hSelf hH hEndpoint hbq hqQ hε hε1 hζε
  by_cases hτ0 : τ = 0
  · have hc : nativeCircuit a τ Q qbar ε UJg nd ar = [] := if_pos hτ0
    rw [hc, if_pos hτ0, nrun_nil, exp_zero_time τ hτ0]
    refine ⟨fun i hi => absurd hi List.not_mem_nil, fun p => ?_, le_rfl, hW,
      identity_comp_error_le _ ε hε.le, fun _ => identity_comp_error_eq_zero _, hdeg, hm1, hm2,
      hr1, hr2⟩
    rw [if_pos hτ0]
    rfl
  · have hc : nativeCircuit a τ Q qbar ε UJg nd ar = nativeSim a τ Q qbar ε UJg nd ar :=
      if_neg hτ0
    rw [hc, if_neg hτ0]
    refine ⟨hvalid, fun p => ?_, hgates, hW, herr, fun h => absurd h hτ0, hdeg, hm1, hm2, hr1,
      hr2⟩
    rw [if_neg hτ0]
    exact hcalls p

/-- The native circuit of Theorem `hs:thm:gates` for every real time: the empty (identity)
circuit at `t = 0` and the released `nativeSimSigned` otherwise, on the same wires. -/
def nativeCircuitSigned (a : ℕ) (t Q qbar ε : ℝ) (UJg : List (Gate (Fin a ⊕ S)))
    (nd : NativeOp Empty (Fin a ⊕ S) Z Y J) (ar : Arith (NB Empty (Fin a ⊕ S) Z)) :
    List (NInstr (HW (SimWire a Q |t| qbar (ε / 2)) S Empty Z ar.bT ar.bP ar.A) Y J) :=
  if t = 0 then [] else nativeSimSigned a t Q qbar ε UJg nd ar

/-- **Native Theorem `hs:thm:gates` for every real time, with the identity circuit at `t = 0`.**
Under the hypotheses of the released `native_simulation_signed`, the circuit
`nativeCircuitSigned a t Q qbar ε UJg nd ar` consists of valid instructions, makes `0` primitive
calls if `t = 0` and exactly `12 d` times the calls of the compute circuit `V` otherwise, has `0`
elementary gates if `t = 0` and at most `200 (d+1)(a+m+r+1) + 84 d C_J + 6 d G_C` otherwise,
and its full output on the system embedding is within `ε` of `exp(-itH)`; at `t = 0` the error
is exactly `0`. -/
theorem native_simulation_signed_zero (a : ℕ) (prim : J → Reg Y R →L[ℂ] Reg Y R)
    (hprim : ∀ j, IsUnitary (prim j))
    (UJg : List (Gate (Fin a ⊕ S))) (hUJg : ∀ g ∈ UJg, GateOK 3 g)
    (nd : NativeOp Empty (Fin a ⊕ S) Z Y J) (hnd : nd.Public)
    (ar : Arith (NB Empty (Fin a ⊕ S) Z)) (ζ : ℝ) (hζ : 0 ≤ ζ)
    (har : ArithOK ar (Sum.inl (Sum.inr nd.o)) nd.dec ζ)
    (D R1 : Anc a (Reg S R) →L[ℂ] Anc a (Reg S R)) (H : Reg S R →L[ℂ] Reg S R)
    (hD : IsUnitary D) (hN : NativeOK prim nd (selOp (fun _ : Cfg Empty => D)))
    (t Q b qbar ε : ℝ) (hQ : 1 ≤ Q)
    (hRight : (1 - D) ∘L R1 = 1) (hLeft : R1 ∘L (1 - D) = 1) (hR1 : ‖R1‖ ≤ Q)
    (hBoundary : (UJop (R := R) UJg ∘L iota0 (P := Reg S R))† ∘L R1 ∘L
      (UJop (R := R) UJg ∘L iota0 (P := Reg S R)) = (2 : ℂ)⁻¹ • (1 + Complex.I • H))
    (hSelf : star H = H) (hH : ‖H‖ ≤ 1)
    (hEndpoint : ‖R1 ∘L (UJop (R := R) UJg ∘L iota0 (P := Reg S R))‖ ≤ b)
    (hbq : b ^ 2 ≤ qbar / 2) (hqQ : qbar ≤ Q)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hζε : 48 * (fDeg Q |t| qbar (ε / 2) : ℝ) * ζ ≤ ε) :
    (∀ i ∈ nativeCircuitSigned a t Q qbar ε UJg nd ar, i.Valid) ∧
    (∀ p : J → Bool, nCallsN p (nativeCircuitSigned a t Q qbar ε UJg nd ar) =
      (if t = 0 then 0 else 12 * fDeg Q |t| qbar (ε / 2) * nCallsN p nd.V)) ∧
    nGatesN (nativeCircuitSigned a t Q qbar ε UJg nd ar) ≤
      (if t = 0 then 0 else
        200 * (fDeg Q |t| qbar (ε / 2) + 1) * (a + simM |t| (ε / 2) + simR Q |t| qbar (ε / 2) + 1) +
          84 * fDeg Q |t| qbar (ε / 2) * UJg.length +
          6 * fDeg Q |t| qbar (ε / 2) *
            (2 * nGatesN nd.V + 2 * ar.circ.length + (2 * ar.bP + ar.bT + 1))) ∧
    ‖nrun prim (nativeCircuitSigned a t Q qbar ε UJg nd ar) ∘L sysEmb (io (P := Reg S R)) -
        sysEmb (io (P := Reg S R)) ∘L NormedSpace.exp ((-Complex.I * (t : ℂ)) • H)‖ ≤ ε ∧
    (t = 0 → ‖nrun prim (nativeCircuitSigned a t Q qbar ε UJg nd ar) ∘L sysEmb (io (P := Reg S R)) -
        sysEmb (io (P := Reg S R)) ∘L NormedSpace.exp ((-Complex.I * (t : ℂ)) • H)‖ = 0) := by
  by_cases ht0 : t = 0
  · have hc : nativeCircuitSigned a t Q qbar ε UJg nd ar = [] := if_pos ht0
    rw [hc, if_pos ht0, nrun_nil, exp_zero_time t ht0]
    refine ⟨fun i hi => absurd hi List.not_mem_nil, fun p => ?_, le_rfl,
      identity_comp_error_le _ ε hε.le, fun _ => identity_comp_error_eq_zero _⟩
    rw [if_pos ht0]
    rfl
  · obtain ⟨hvalid, hcalls, hgates, herr⟩ := native_simulation_signed a prim hprim UJg hUJg nd
      hnd ar ζ hζ har D R1 H hD hN t Q b qbar ε hQ hRight hLeft hR1 hBoundary hSelf hH
      hEndpoint hbq hqQ hε hε1 hζε
    have hc : nativeCircuitSigned a t Q qbar ε UJg nd ar = nativeSimSigned a t Q qbar ε UJg nd ar :=
      if_neg ht0
    rw [hc, if_neg ht0]
    refine ⟨hvalid, fun p => ?_, hgates, herr, fun h => absurd h ht0⟩
    rw [if_neg ht0]
    exact hcalls p

/-- The native time-dependent circuit for every `t ≥ 0`: the empty (identity) circuit at
`t = 0` and the released `nativeSimT` otherwise, on the same wires (`hs:thm:gates`). -/
def nativeCircuitT (a m : ℕ) (α t Q qbar ε : ℝ) (UJg : List (Gate (Fin a ⊕ S)))
    (nd : NativeOp (Fin m) (Fin a ⊕ S) Z Y J) (ar : Arith (NB (Fin m) (Fin a ⊕ S) Z)) :
    List (NInstr (HW (Wire a m (simR Q (α * t) qbar (ε / 4))
      (a + m + 2 * simR Q (α * t) qbar (ε / 4))) S Empty Z ar.bT ar.bP ar.A) Y J) :=
  if t = 0 then [] else nativeSimT a m (α * t) Q qbar ε UJg nd ar

/-- **Native time-dependent gate-level simulation (Theorem `hs:thm:time` with the circuit of
`hs:thm:gates`) for every `t ≥ 0`.** Under the hypotheses of the released `native_time_simulation`,
the circuit `nativeCircuitT a m α t Q qbar ε UJg nd ar` consists of valid instructions, makes `0`
primitive calls and has `0` elementary gates if `t = 0`, has the released counts otherwise, and for
every propagator `U` of the path its full output on the system embedding is within `ε` of `U(t)`; at
`t = 0` the error is exactly `0`. The wire count, the degree bounds and the existence of a
propagator are those of the released theorem. -/
theorem native_time_simulation_nonneg (a m : ℕ) (prim : J → Reg Y R →L[ℂ] Reg Y R)
    (hprim : ∀ j, IsUnitary (prim j))
    (UJg : List (Gate (Fin a ⊕ S))) (hUJg : ∀ g ∈ UJg, GateOK 3 g)
    (nd : NativeOp (Fin m) (Fin a ⊕ S) Z Y J) (hnd : nd.Public)
    (ar : Arith (NB (Fin m) (Fin a ⊕ S) Z)) (ζ : ℝ) (hζ : 0 ≤ ζ)
    (har : ArithOK ar (Sum.inl (Sum.inr nd.o)) nd.dec ζ)
    (D R1 : ℕ → Anc a (Reg S R) →L[ℂ] Anc a (Reg S R))
    (hN : NativeOK prim nd (selOp (fun w : Cfg (Fin m) =>
      D (GatePointerEncoding.wordEquivFin m w))))
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
    (hζε : 48 * (fDeg Q (α * t) qbar (ε / 4) : ℝ) * ζ ≤ ε) :
    (∀ i ∈ nativeCircuitT a m α t Q qbar ε UJg nd ar, i.Valid) ∧
    (∀ p : J → Bool, nCallsN p (nativeCircuitT a m α t Q qbar ε UJg nd ar) =
      (if t = 0 then 0 else 12 * fDeg Q (α * t) qbar (ε / 4) * nCallsN p nd.V)) ∧
    nGatesN (nativeCircuitT a m α t Q qbar ε UJg nd ar) ≤
      (if t = 0 then 0 else
        200 * (fDeg Q (α * t) qbar (ε / 4) + 1) * (a + m + simR Q (α * t) qbar (ε / 4) + 1) +
          84 * fDeg Q (α * t) qbar (ε / 4) * UJg.length +
          6 * fDeg Q (α * t) qbar (ε / 4) *
            (2 * nGatesN nd.V + 2 * ar.circ.length + (2 * ar.bP + ar.bT + 1))) ∧
    Fintype.card (HW (Wire a m (simR Q (α * t) qbar (ε / 4))
        (a + m + 2 * simR Q (α * t) qbar (ε / 4))) S Empty Z ar.bT ar.bP ar.A) =
      Fintype.card S + (2 * a + 3 * m + 6 * simR Q (α * t) qbar (ε / 4) + 3) +
        (Fintype.card Z + ar.bT + ar.bP + ar.A + 3) ∧
    (fDeg Q (α * t) qbar (ε / 4) : ℝ) ≤ 128 * (α * t * qbar + Q * (1 + Real.log (12 / ε))) ∧
    2 * fDeg Q (α * t) qbar (ε / 4) + 2 ≤ 2 ^ simR Q (α * t) qbar (ε / 4) ∧
    2 ^ simR Q (α * t) qbar (ε / 4) ≤ 4 * (fDeg Q (α * t) qbar (ε / 4) + 1) ∧
    (∃ U : ℝ → Reg S R →L[ℂ] Reg S R, U 0 = 1 ∧ TimeDependent.SolvesOn Hpath U 0 t) ∧
    (∀ U : ℝ → Reg S R →L[ℂ] Reg S R, U 0 = 1 → TimeDependent.SolvesOn Hpath U 0 t →
      ‖nrun prim (nativeCircuitT a m α t Q qbar ε UJg nd ar) ∘L sysEmb (io (P := Reg S R)) -
          sysEmb (io (P := Reg S R)) ∘L U t‖ ≤ ε) ∧
    (t = 0 → ∀ U : ℝ → Reg S R →L[ℂ] Reg S R, U 0 = 1 → TimeDependent.SolvesOn Hpath U 0 t →
      ‖nrun prim (nativeCircuitT a m α t Q qbar ε UJg nd ar) ∘L sysEmb (io (P := Reg S R)) -
          sysEmb (io (P := Reg S R)) ∘L U t‖ = 0) := by
  obtain ⟨hvalid, hcalls, hgates, hW, hdeg, hr1, hr2, hex, herr⟩ := native_time_simulation a m
    prim hprim UJg hUJg nd hnd ar ζ hζ har D R1 hN Hpath Hs t α β δ Q b qbar ε ht hα hβ hQ hqQ
    hε hε1 hCayley hFreeze hD hRight hLeft hR1 hBoundary hEndpoint hbq hSelf hHs hPath hLip
    hVal hValBudget hζε
  by_cases ht0 : t = 0
  · have hc : nativeCircuitT a m α t Q qbar ε UJg nd ar = [] := if_pos ht0
    rw [hc, if_pos ht0, nrun_nil]
    refine ⟨fun i hi => absurd hi List.not_mem_nil, fun p => ?_, le_rfl, hW, hdeg, hr1, hr2,
      hex, fun U hU0 _ => ?_, fun _ U hU0 _ => ?_⟩
    · rw [if_pos ht0]
      rfl
    · have hUt : U t = 1 := by rw [ht0, hU0]
      rw [hUt]
      exact identity_comp_error_le _ ε hε.le
    · have hUt : U t = 1 := by rw [ht0, hU0]
      rw [hUt]
      exact identity_comp_error_eq_zero _
  · have hc : nativeCircuitT a m α t Q qbar ε UJg nd ar =
        nativeSimT a m (α * t) Q qbar ε UJg nd ar := if_neg ht0
    rw [hc, if_neg ht0]
    refine ⟨hvalid, fun p => ?_, hgates, hW, hdeg, hr1, hr2, hex, herr, fun h => absurd h ht0⟩
    rw [if_neg ht0]
    exact hcalls p

end Native

end
end SparseHamiltonian.ZeroTimeRemarks.Gates
