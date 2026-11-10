import GateEfficientSynthesis.Hamiltonian
import ZeroTimeRemarks.Gates

/-!
# Theorem `hs:thm:gates` at zero time over a finite gate set: native implementations

Theorem `hs:thm:gates` of the accompanying paper states "This is a time-independent result; at
`t = 0` the identity suffices." The released library `ZeroTimeRemarks` states this remark for the
exact-gate and native circuits; its guide lists the finite-gate-set variants (`GateSynth.*`) as not
formalised. The released finite-gate-set endpoints (library `GateEfficientSynthesis`) synthesise
every elementary gate of a native circuit with the budget `ε'` (`GateSynth.synthBudget`). The
synthesis of the empty circuit is the empty circuit (`synthBudget_nil`), so the synthesis of the
combined native circuits of `ZeroTimeRemarks.Gates` (the empty circuit at zero time, the released
circuit otherwise) has no gate and no call at zero time:

* `native_simulation_synth_nonneg` (`GateSynth.native_simulation_synth`, every `τ ≥ 0`, with
  `ZeroTimeRemarks.Gates.nativeCircuit`);
* `native_simulation_signed_synth_zero` (`GateSynth.native_simulation_signed_synth`, every real
  `t`, with `ZeroTimeRemarks.Gates.nativeCircuitSigned`);
* `native_time_simulation_synth_nonneg` (`GateSynth.native_time_simulation_synth`, every
  `t ≥ 0`, with `ZeroTimeRemarks.Gates.nativeCircuitT`).

Each keeps every conclusion of the released theorem: the synthesised counts are `0` at zero time
and the released counts otherwise, the conclusions that do not depend on the circuit (the bound on
the native gate count of the released native circuit, the qubit count, the existence of a
propagator) are unchanged, and the full-output error is at most `ε + ε'` and exactly `0` at zero
time.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateRemarks

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit GateCircuit.Sim GateNative GateSynth
open GatePointerEncoding (wordEquivFin)
open ZeroTimeRemarks.Gates (nativeCircuit nativeCircuitSigned nativeCircuitT exp_zero_time
  identity_comp_error_eq_zero identity_comp_error_le)
open scoped InnerProduct

/-- **The synthesis of the empty circuit is empty** (`hs:thm:gates`, zero time): it has no gate
and no call. -/
theorem synthBudget_nil {V Y J X : Type*} [Fintype V] [DecidableEq V] [Fintype X]
    [DecidableEq X] {𝒢 : Set Kind} {L : ℝ → ℕ} (hS : Synthesis 𝒢 X L) (ε' : ℝ) :
    synthBudget hS ε' ([] : List (NInstr V Y J)) = [] := rfl

section Native

variable {S Z Y J X : Type*} [Fintype S] [DecidableEq S] [Fintype Z] [DecidableEq Z]
  [Fintype Y] [DecidableEq Y] [Fintype X] [DecidableEq X]
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
variable {𝒢 : Set Kind} {L : ℝ → ℕ}

/-- **Native Theorem `hs:thm:gates` over a finite gate set for every `τ ≥ 0`, with the identity
circuit at `τ = 0`.** Under the hypotheses of the released `GateSynth.native_simulation_synth`,
the synthesis `synthBudget hS ε' (nativeCircuit a τ Q qbar ε UJg nd ar)` of the combined native
circuit of `ZeroTimeRemarks.Gates` consists of valid gates of `𝒢` and primitive calls, makes `0`
primitive calls if `τ = 0` and exactly `12 d` times the calls of `V` otherwise, uses `0` gates if
`τ = 0` and at most `N L(ε'/(N+1))` gates otherwise (`N` the gate count of the released native
circuit `nativeSim`, bounded as in the released theorem), has the released qubit count, and its
full output on the clean embedding is within `ε + ε'` of `exp(-iτH)`; at `τ = 0` the error is
exactly `0`. -/
theorem native_simulation_synth_nonneg (hS : Synthesis 𝒢 X L) (ε' : ℝ) (hε' : 0 < ε') (a : ℕ)
    (prim : J → Reg Y R →L[ℂ] Reg Y R) (hprim : ∀ j, IsUnitary (prim j))
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
    (∀ i ∈ synthBudget hS ε' (nativeCircuit a τ Q qbar ε UJg nd ar), i.Valid) ∧
    (∀ g, NInstr.gate g ∈ synthBudget hS ε' (nativeCircuit a τ Q qbar ε UJg nd ar) →
      GateOf 𝒢 g) ∧
    (∀ p : J → Bool, nCallsN p (synthBudget hS ε' (nativeCircuit a τ Q qbar ε UJg nd ar)) =
      (if τ = 0 then 0 else 12 * fDeg Q τ qbar (ε / 2) * nCallsN p nd.V)) ∧
    nGatesN (synthBudget hS ε' (nativeCircuit a τ Q qbar ε UJg nd ar)) ≤
      (if τ = 0 then 0 else
        nGatesN (nativeSim a τ Q qbar ε UJg nd ar) *
          L (ε' / (nGatesN (nativeSim a τ Q qbar ε UJg nd ar) + 1))) ∧
    nGatesN (nativeSim a τ Q qbar ε UJg nd ar) ≤
      200 * (fDeg Q τ qbar (ε / 2) + 1) * (a + simM τ (ε / 2) + simR Q τ qbar (ε / 2) + 1) +
        84 * fDeg Q τ qbar (ε / 2) * UJg.length +
        6 * fDeg Q τ qbar (ε / 2) *
          (2 * nGatesN nd.V + 2 * ar.circ.length + (2 * ar.bP + ar.bT + 1)) ∧
    Fintype.card (HW (SimWire a Q τ qbar (ε / 2)) S Empty Z ar.bT ar.bP ar.A ⊕ X) =
      Fintype.card S + (2 * a + 3 * simM τ (ε / 2) + 6 * simR Q τ qbar (ε / 2) + 3) +
        (Fintype.card Z + ar.bT + ar.bP + ar.A + 3) + Fintype.card X ∧
    ‖nrun prim (synthBudget hS ε' (nativeCircuit a τ Q qbar ε UJg nd ar)) ∘L
        (cleanEmb (X := X) ∘L sysEmb (io (P := Reg S R))) -
        (cleanEmb ∘L sysEmb (io (P := Reg S R))) ∘L
          NormedSpace.exp ((-Complex.I * (τ : ℂ)) • H)‖ ≤ ε + ε' ∧
    (τ = 0 → ‖nrun prim (synthBudget hS ε' (nativeCircuit a τ Q qbar ε UJg nd ar)) ∘L
        (cleanEmb (X := X) ∘L sysEmb (io (P := Reg S R))) -
        (cleanEmb ∘L sysEmb (io (P := Reg S R))) ∘L
          NormedSpace.exp ((-Complex.I * (τ : ℂ)) • H)‖ = 0) := by
  obtain ⟨hv, hk, hcalls, hg, hgates, hcard, herr⟩ := native_simulation_synth hS ε' hε' a prim
    hprim UJg hUJg nd hnd ar ζ hζ har D R1 H hD hN τ Q b qbar ε hτ hQ hRight hLeft hR1 hBoundary
    hSelf hH hEndpoint hbq hqQ hε hε1 hζε
  by_cases hτ0 : τ = 0
  · have hc : nativeCircuit a τ Q qbar ε UJg nd ar = [] := if_pos hτ0
    rw [hc, synthBudget_nil, if_pos hτ0, nrun_nil, exp_zero_time τ hτ0]
    have hε0 : 0 ≤ ε + ε' := by linarith
    refine ⟨fun i hi => absurd hi List.not_mem_nil, fun g hg => absurd hg List.not_mem_nil,
      fun p => ?_, le_rfl, hgates, hcard, identity_comp_error_le _ _ hε0,
      fun _ => identity_comp_error_eq_zero _⟩
    rw [if_pos hτ0]
    rfl
  · have hc : nativeCircuit a τ Q qbar ε UJg nd ar = nativeSim a τ Q qbar ε UJg nd ar :=
      if_neg hτ0
    rw [hc, if_neg hτ0]
    refine ⟨hv, hk, fun p => ?_, hg, hgates, hcard, ?_, fun h => absurd h hτ0⟩
    · rw [if_neg hτ0]
      exact hcalls p
    · convert herr using 1

/-- **Native Theorem `hs:thm:gates` over a finite gate set for every real time, with the
identity circuit at `t = 0`.** Under the hypotheses of the released
`GateSynth.native_simulation_signed_synth`, the synthesis of the combined native circuit
`nativeCircuitSigned a t Q qbar ε UJg nd ar` consists of valid gates of `𝒢` and primitive calls,
makes `0` primitive calls if `t = 0` and exactly `12 d` times the calls of `V` otherwise, uses
`0` gates if `t = 0` and at most `N L(ε'/(N+1))` gates otherwise (`N` the gate count of the
released `nativeSimSigned`, bounded as in the released theorem), and its full output on the clean
embedding is within `ε + ε'` of `exp(-itH)`; at `t = 0` the error is exactly `0`. -/
theorem native_simulation_signed_synth_zero (hS : Synthesis 𝒢 X L) (ε' : ℝ) (hε' : 0 < ε')
    (a : ℕ) (prim : J → Reg Y R →L[ℂ] Reg Y R) (hprim : ∀ j, IsUnitary (prim j))
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
    (∀ i ∈ synthBudget hS ε' (nativeCircuitSigned a t Q qbar ε UJg nd ar), i.Valid) ∧
    (∀ g, NInstr.gate g ∈ synthBudget hS ε' (nativeCircuitSigned a t Q qbar ε UJg nd ar) →
      GateOf 𝒢 g) ∧
    (∀ p : J → Bool,
      nCallsN p (synthBudget hS ε' (nativeCircuitSigned a t Q qbar ε UJg nd ar)) =
        (if t = 0 then 0 else 12 * fDeg Q |t| qbar (ε / 2) * nCallsN p nd.V)) ∧
    nGatesN (synthBudget hS ε' (nativeCircuitSigned a t Q qbar ε UJg nd ar)) ≤
      (if t = 0 then 0 else
        nGatesN (nativeSimSigned a t Q qbar ε UJg nd ar) *
          L (ε' / (nGatesN (nativeSimSigned a t Q qbar ε UJg nd ar) + 1))) ∧
    nGatesN (nativeSimSigned a t Q qbar ε UJg nd ar) ≤
      200 * (fDeg Q |t| qbar (ε / 2) + 1) * (a + simM |t| (ε / 2) + simR Q |t| qbar (ε / 2) + 1) +
        84 * fDeg Q |t| qbar (ε / 2) * UJg.length +
        6 * fDeg Q |t| qbar (ε / 2) *
          (2 * nGatesN nd.V + 2 * ar.circ.length + (2 * ar.bP + ar.bT + 1)) ∧
    ‖nrun prim (synthBudget hS ε' (nativeCircuitSigned a t Q qbar ε UJg nd ar)) ∘L
        (cleanEmb (X := X) ∘L sysEmb (io (P := Reg S R))) -
        (cleanEmb ∘L sysEmb (io (P := Reg S R))) ∘L
          NormedSpace.exp ((-Complex.I * (t : ℂ)) • H)‖ ≤ ε + ε' ∧
    (t = 0 → ‖nrun prim (synthBudget hS ε' (nativeCircuitSigned a t Q qbar ε UJg nd ar)) ∘L
        (cleanEmb (X := X) ∘L sysEmb (io (P := Reg S R))) -
        (cleanEmb ∘L sysEmb (io (P := Reg S R))) ∘L
          NormedSpace.exp ((-Complex.I * (t : ℂ)) • H)‖ = 0) := by
  obtain ⟨hv, hk, hcalls, hg, hgates, herr⟩ := native_simulation_signed_synth hS ε' hε' a prim
    hprim UJg hUJg nd hnd ar ζ hζ har D R1 H hD hN t Q b qbar ε hQ hRight hLeft hR1 hBoundary
    hSelf hH hEndpoint hbq hqQ hε hε1 hζε
  by_cases ht0 : t = 0
  · have hc : nativeCircuitSigned a t Q qbar ε UJg nd ar = [] := if_pos ht0
    rw [hc, synthBudget_nil, if_pos ht0, nrun_nil, exp_zero_time t ht0]
    have hε0 : 0 ≤ ε + ε' := by linarith
    refine ⟨fun i hi => absurd hi List.not_mem_nil, fun g hg => absurd hg List.not_mem_nil,
      fun p => ?_, le_rfl, hgates, identity_comp_error_le _ _ hε0,
      fun _ => identity_comp_error_eq_zero _⟩
    rw [if_pos ht0]
    rfl
  · have hc : nativeCircuitSigned a t Q qbar ε UJg nd ar =
        nativeSimSigned a t Q qbar ε UJg nd ar := if_neg ht0
    rw [hc, if_neg ht0]
    refine ⟨hv, hk, fun p => ?_, hg, hgates, ?_, fun h => absurd h ht0⟩
    · rw [if_neg ht0]
      exact hcalls p
    · convert herr using 1

/-- **Native time-dependent gate-level simulation (Theorem `hs:thm:time` with the circuit of
`hs:thm:gates`) over a finite gate set for every `t ≥ 0`, with the identity circuit at `t = 0`.**
Under the hypotheses of the released `GateSynth.native_time_simulation_synth`, the synthesis of the
combined native circuit `nativeCircuitT a m α t Q qbar ε UJg nd ar` consists of valid gates of `𝒢`
and primitive calls, makes `0` primitive calls and uses `0` gates if `t = 0`, has the released
counts otherwise (`N` the gate count of the released `nativeSimT`, bounded as in the released
theorem), has the released qubit count, the propagator of the path exists, and for every propagator
`U` its full output on the clean embedding is within `ε + ε'` of `U(t)`; at `t = 0` the error is
exactly `0`. -/
theorem native_time_simulation_synth_nonneg (hS : Synthesis 𝒢 X L) (ε' : ℝ) (hε' : 0 < ε')
    (a m : ℕ) (prim : J → Reg Y R →L[ℂ] Reg Y R) (hprim : ∀ j, IsUnitary (prim j))
    (UJg : List (Gate (Fin a ⊕ S))) (hUJg : ∀ g ∈ UJg, GateOK 3 g)
    (nd : NativeOp (Fin m) (Fin a ⊕ S) Z Y J) (hnd : nd.Public)
    (ar : Arith (NB (Fin m) (Fin a ⊕ S) Z)) (ζ : ℝ) (hζ : 0 ≤ ζ)
    (har : ArithOK ar (Sum.inl (Sum.inr nd.o)) nd.dec ζ)
    (D R1 : ℕ → Anc a (Reg S R) →L[ℂ] Anc a (Reg S R))
    (hN : NativeOK prim nd (selOp (fun w : Cfg (Fin m) => D (wordEquivFin m w))))
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
    (∀ i ∈ synthBudget hS ε' (nativeCircuitT a m α t Q qbar ε UJg nd ar), i.Valid) ∧
    (∀ g, NInstr.gate g ∈ synthBudget hS ε' (nativeCircuitT a m α t Q qbar ε UJg nd ar) →
      GateOf 𝒢 g) ∧
    (∀ p : J → Bool,
      nCallsN p (synthBudget hS ε' (nativeCircuitT a m α t Q qbar ε UJg nd ar)) =
        (if t = 0 then 0 else 12 * fDeg Q (α * t) qbar (ε / 4) * nCallsN p nd.V)) ∧
    nGatesN (synthBudget hS ε' (nativeCircuitT a m α t Q qbar ε UJg nd ar)) ≤
      (if t = 0 then 0 else
        nGatesN (nativeSimT a m (α * t) Q qbar ε UJg nd ar) *
          L (ε' / (nGatesN (nativeSimT a m (α * t) Q qbar ε UJg nd ar) + 1))) ∧
    nGatesN (nativeSimT a m (α * t) Q qbar ε UJg nd ar) ≤
      200 * (fDeg Q (α * t) qbar (ε / 4) + 1) * (a + m + simR Q (α * t) qbar (ε / 4) + 1) +
        84 * fDeg Q (α * t) qbar (ε / 4) * UJg.length +
        6 * fDeg Q (α * t) qbar (ε / 4) *
          (2 * nGatesN nd.V + 2 * ar.circ.length + (2 * ar.bP + ar.bT + 1)) ∧
    Fintype.card (HW (Wire a m (simR Q (α * t) qbar (ε / 4))
        (a + m + 2 * simR Q (α * t) qbar (ε / 4))) S Empty Z ar.bT ar.bP ar.A ⊕ X) =
      Fintype.card S + (2 * a + 3 * m + 6 * simR Q (α * t) qbar (ε / 4) + 3) +
        (Fintype.card Z + ar.bT + ar.bP + ar.A + 3) + Fintype.card X ∧
    (∃ U : ℝ → Reg S R →L[ℂ] Reg S R, U 0 = 1 ∧ TimeDependent.SolvesOn Hpath U 0 t) ∧
    (∀ U : ℝ → Reg S R →L[ℂ] Reg S R, U 0 = 1 → TimeDependent.SolvesOn Hpath U 0 t →
      ‖nrun prim (synthBudget hS ε' (nativeCircuitT a m α t Q qbar ε UJg nd ar)) ∘L
          (cleanEmb (X := X) ∘L sysEmb (io (P := Reg S R))) -
          (cleanEmb ∘L sysEmb (io (P := Reg S R))) ∘L U t‖ ≤ ε + ε') ∧
    (t = 0 → ∀ U : ℝ → Reg S R →L[ℂ] Reg S R, U 0 = 1 → TimeDependent.SolvesOn Hpath U 0 t →
      ‖nrun prim (synthBudget hS ε' (nativeCircuitT a m α t Q qbar ε UJg nd ar)) ∘L
          (cleanEmb (X := X) ∘L sysEmb (io (P := Reg S R))) -
          (cleanEmb ∘L sysEmb (io (P := Reg S R))) ∘L U t‖ = 0) := by
  obtain ⟨hv, hk, hcalls, hg, hgates, hcard, hex, herr⟩ := native_time_simulation_synth hS ε' hε'
    a m prim hprim UJg hUJg nd hnd ar ζ hζ har D R1 hN Hpath Hs t α β δ Q b qbar ε ht hα hβ hQ
    hqQ hε hε1 hCayley hFreeze hD hRight hLeft hR1 hBoundary hEndpoint hbq hSelf hHs hPath hLip
    hVal hValBudget hζε
  by_cases ht0 : t = 0
  · have hc : nativeCircuitT a m α t Q qbar ε UJg nd ar = [] := if_pos ht0
    rw [hc, synthBudget_nil, if_pos ht0, nrun_nil]
    have hε0 : 0 ≤ ε + ε' := by linarith
    refine ⟨fun i hi => absurd hi List.not_mem_nil, fun g hg => absurd hg List.not_mem_nil,
      fun p => ?_, le_rfl, hgates, hcard, hex, fun U hU0 _ => ?_, fun _ U hU0 _ => ?_⟩
    · rw [if_pos ht0]
      rfl
    · have hUt : U t = 1 := by rw [ht0, hU0]
      rw [hUt]
      exact identity_comp_error_le _ _ hε0
    · have hUt : U t = 1 := by rw [ht0, hU0]
      rw [hUt]
      exact identity_comp_error_eq_zero _
  · have hc : nativeCircuitT a m α t Q qbar ε UJg nd ar =
        nativeSimT a m (α * t) Q qbar ε UJg nd ar := if_neg ht0
    rw [hc, if_neg ht0]
    refine ⟨hv, hk, fun p => ?_, hg, hgates, hcard, hex, fun U hU0 hU => ?_,
      fun h => absurd h ht0⟩
    · rw [if_neg ht0]
      exact hcalls p
    · convert herr U hU0 hU using 1

end Native

end

end SparseHamiltonian.GateRemarks
