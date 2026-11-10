import GateEfficientSynthesis.Circuit
import GateEfficientNative.Hamiltonian.Theorem

/-!
# Theorem `hs:thm:gates` and a package extension over a finite gate set: native implementations

The native gate-level circuits of `GateEfficientNative` consist of elementary gates and primitive
oracle calls. Under the synthesis hypothesis `Synthesis 𝒢 X L`, a synthesis budget `ε' > 0` is spent
uniformly: every elementary gate is synthesised at accuracy `ε'/(N+1)`, where `N` is the number of
elementary gates of the native circuit (`synthBudget`). The synthesised circuit then consists of
valid gates of `𝒢` and the same primitive calls, has at most `N L(ε'/(N+1))` gates and `|X|` more
qubits (the reused synthesis ancillas), and its full output, with every ancilla clean, is within
`ε + ε'` of the ideal evolution whenever the native circuit is within `ε` (`synthBudget_spec`,
`synthBudget_error`).

* `native_simulation_synth`: time-independent Hamiltonians (`native_simulation`).
* `native_simulation_signed_synth`: every real time (`native_simulation_signed`).
* `native_time_simulation_synth`: time-dependent Hamiltonians on a uniform mesh
  (`native_time_simulation`), for every propagator of the path (package extension: Theorem
  `hs:thm:time` with the circuit of `hs:thm:gates` (single-label case of Lemma
  `ode:lem:gate-select`)).
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateSynth

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit GateCircuit.Sim GateNative
open GatePointerEncoding (wordEquivFin)
open scoped InnerProduct

/-! ### Spending a synthesis budget -/

section Budget

variable {V Y J X : Type*} [Fintype V] [DecidableEq V] [Fintype Y] [DecidableEq Y]
  [Fintype X] [DecidableEq X]
variable {𝒢 : Set Kind} {L : ℝ → ℕ}

/-- The synthesis of a circuit with the synthesis budget `ε'`: every elementary gate at accuracy
`ε'/(N+1)`, `N` the number of elementary gates. -/
def synthBudget (hS : Synthesis 𝒢 X L) (ε' : ℝ) (C : List (NInstr V Y J)) :
    List (NInstr (V ⊕ X) Y J) :=
  synthC hS (ε' / (nGatesN C + 1)) C

omit [Fintype Y] [DecidableEq Y] in
/-- **Validity and counts with a synthesis budget.** -/
theorem synthBudget_spec (hS : Synthesis 𝒢 X L) {ε' : ℝ} (hε' : 0 < ε')
    (C : List (NInstr V Y J)) (hC : ∀ i ∈ C, i.Valid) :
    (∀ i ∈ synthBudget hS ε' C, i.Valid) ∧
      (∀ g, NInstr.gate g ∈ synthBudget hS ε' C → GateOf 𝒢 g) ∧
      nGatesN (synthBudget hS ε' C) ≤ nGatesN C * L (ε' / (nGatesN C + 1)) ∧
      ∀ p : J → Bool, nCallsN p (synthBudget hS ε' C) = nCallsN p C :=
  synthC_spec hS (div_pos hε' (by positivity)) C hC

variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- **The synthesis budget adds at most `ε'` to the full-output error.** -/
theorem synthBudget_error (hS : Synthesis 𝒢 X L) {ε' : ℝ} (hε' : 0 < ε')
    (C : List (NInstr V Y J)) (hC : ∀ i ∈ C, i.Valid) (prim : J → Reg Y R →L[ℂ] Reg Y R)
    (hprim : ∀ j, IsUnitary (prim j)) {S : Type*} [Fintype S] [DecidableEq S]
    (E : Reg S R →L[ℂ] Reg V R) (hE : ∀ p, ‖E p‖ ≤ ‖p‖) (U : Reg S R →L[ℂ] Reg S R) {ε : ℝ}
    (herr : ‖nrun prim C ∘L E - E ∘L U‖ ≤ ε) :
    ‖nrun prim (synthBudget hS ε' C) ∘L (cleanEmb (X := X) ∘L E) - (cleanEmb ∘L E) ∘L U‖ ≤
      ε + ε' := by
  have hN : (0 : ℝ) < nGatesN C + 1 := by positivity
  have h := synthC_error prim hS (div_pos hε' hN) C hC hprim E hE U
  have hb : (nGatesN C : ℝ) * (ε' / (nGatesN C + 1)) ≤ ε' := by
    rw [mul_div_assoc', div_le_iff₀ hN]
    nlinarith
  unfold synthBudget
  linarith

/-- The number of gates with a logarithmic synthesis length: if `L ζ ≤ c₁ log(1/ζ) + c₀` on
`(0, 1]`, then `N L(ε'/(N+1)) ≤ G (c₁ log((G+1)/ε') + c₀)` for every `G ≥ N` and `ε' ≤ 1`. -/
theorem gates_log_le {c₀ c₁ : ℝ} (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁)
    (hL : ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 → (L ζ : ℝ) ≤ c₁ * Real.log (1 / ζ) + c₀) {ε' : ℝ}
    (hε' : 0 < ε') (hε'1 : ε' ≤ 1) (N : ℕ) (G : ℝ) (hNG : (N : ℝ) ≤ G) :
    ((N * L (ε' / (N + 1)) : ℕ) : ℝ) ≤ G * (c₁ * Real.log ((G + 1) / ε') + c₀) := by
  have hN1 : (0 : ℝ) < N + 1 := by positivity
  have hζ : 0 < ε' / (N + 1) := div_pos hε' hN1
  have hζ1 : ε' / (N + 1) ≤ 1 := by
    rw [div_le_one hN1]
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    linarith
  have h1 := hL _ hζ hζ1
  have e : 1 / (ε' / (N + 1)) = (N + 1) / ε' := by
    field_simp
  rw [e] at h1
  have hge : 1 ≤ ((N : ℝ) + 1) / ε' := by
    rw [le_div_iff₀ hε']
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    linarith
  have hlog : Real.log (((N : ℝ) + 1) / ε') ≤ Real.log ((G + 1) / ε') := by
    apply Real.log_le_log (by linarith)
    exact div_le_div_of_nonneg_right (by linarith) hε'.le
  have hlog0 : 0 ≤ Real.log (((N : ℝ) + 1) / ε') := Real.log_nonneg hge
  have h2 : (L (ε' / (N + 1)) : ℝ) ≤ c₁ * Real.log ((G + 1) / ε') + c₀ := by
    nlinarith
  have h3 : 0 ≤ c₁ * Real.log ((G + 1) / ε') + c₀ := by
    have : 0 ≤ Real.log ((G + 1) / ε') := hlog0.trans hlog
    positivity
  push_cast
  calc (N : ℝ) * (L (ε' / (N + 1)) : ℝ) ≤ (N : ℝ) * (c₁ * Real.log ((G + 1) / ε') + c₀) :=
        mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg _)
    _ ≤ G * (c₁ * Real.log ((G + 1) / ε') + c₀) := mul_le_mul_of_nonneg_right hNG h3

end Budget

/-! ### Native endpoints -/

section Native

variable {S Z Y J X : Type*} [Fintype S] [DecidableEq S] [Fintype Z] [DecidableEq Z]
  [Fintype Y] [DecidableEq Y] [Fintype X] [DecidableEq X]
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
variable {𝒢 : Set Kind} {L : ℝ → ℕ}

/-- **Native gate-efficient sparse simulation over a finite gate set** (Theorem `hs:thm:gates`).
Under the hypotheses of `native_simulation` and the synthesis hypothesis,
the synthesis of the native circuit with the budget `ε'` consists of valid gates of `𝒢` and
primitive calls, makes exactly `12 d` times the primitive calls of `V`, uses at most `N L(ε'/(N+1))`
gates, where `N` is the native gate count bounded in `native_simulation`, has `|X|` more qubits, and
its full output with every qubit outside the system clean is within `ε + ε'` of `exp(-iτH)`. -/
theorem native_simulation_synth (hS : Synthesis 𝒢 X L) (ε' : ℝ) (hε' : 0 < ε') (a : ℕ)
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
    (∀ i ∈ synthBudget hS ε' (nativeSim a τ Q qbar ε UJg nd ar), i.Valid) ∧
    (∀ g, NInstr.gate g ∈ synthBudget hS ε' (nativeSim a τ Q qbar ε UJg nd ar) →
      GateOf 𝒢 g) ∧
    (∀ p : J → Bool, nCallsN p (synthBudget hS ε' (nativeSim a τ Q qbar ε UJg nd ar)) =
      12 * fDeg Q τ qbar (ε / 2) * nCallsN p nd.V) ∧
    nGatesN (synthBudget hS ε' (nativeSim a τ Q qbar ε UJg nd ar)) ≤
      nGatesN (nativeSim a τ Q qbar ε UJg nd ar) *
        L (ε' / (nGatesN (nativeSim a τ Q qbar ε UJg nd ar) + 1)) ∧
    nGatesN (nativeSim a τ Q qbar ε UJg nd ar) ≤
      200 * (fDeg Q τ qbar (ε / 2) + 1) * (a + simM τ (ε / 2) + simR Q τ qbar (ε / 2) + 1) +
        84 * fDeg Q τ qbar (ε / 2) * UJg.length +
        6 * fDeg Q τ qbar (ε / 2) *
          (2 * nGatesN nd.V + 2 * ar.circ.length + (2 * ar.bP + ar.bT + 1)) ∧
    Fintype.card (HW (SimWire a Q τ qbar (ε / 2)) S Empty Z ar.bT ar.bP ar.A ⊕ X) =
      Fintype.card S + (2 * a + 3 * simM τ (ε / 2) + 6 * simR Q τ qbar (ε / 2) + 3) +
        (Fintype.card Z + ar.bT + ar.bP + ar.A + 3) + Fintype.card X ∧
    ‖nrun prim (synthBudget hS ε' (nativeSim a τ Q qbar ε UJg nd ar)) ∘L
        (cleanEmb (X := X) ∘L sysEmb (io (P := Reg S R))) -
        (cleanEmb ∘L sysEmb (io (P := Reg S R))) ∘L
          NormedSpace.exp ((-Complex.I * (τ : ℂ)) • H)‖ ≤ ε + ε' := by
  obtain ⟨hvalid, hcalls, hgates, hcard, herr, -⟩ := native_simulation a prim hprim UJg hUJg nd
    hnd ar ζ hζ har D R1 H hD hN τ Q b qbar ε hτ hQ hRight hLeft hR1 hBoundary hSelf hH hEndpoint
    hbq hqQ hε hε1 hζε
  obtain ⟨hv, hk, hg, hc⟩ := synthBudget_spec hS hε' _ hvalid
  refine ⟨hv, hk, fun p => (hc p).trans (hcalls p), hg, hgates, ?_, ?_⟩
  · rw [Fintype.card_sum, hcard]
  · generalize NormedSpace.exp ((-Complex.I * (τ : ℂ)) • H) = U at herr ⊢
    generalize nativeSim a τ Q qbar ε UJg nd ar = C at hvalid herr ⊢
    refine synthBudget_error hS hε' C hvalid prim hprim _ ?_ U herr
    intro ψ
    exact (norm_sysEmb _ (fun φ => by rw [io_apply, norm_bas]) ψ).le

/-- **Every real time over a finite gate set** (`native_simulation_signed`). -/
theorem native_simulation_signed_synth (hS : Synthesis 𝒢 X L) (ε' : ℝ) (hε' : 0 < ε') (a : ℕ)
    (prim : J → Reg Y R →L[ℂ] Reg Y R) (hprim : ∀ j, IsUnitary (prim j))
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
    (∀ i ∈ synthBudget hS ε' (nativeSimSigned a t Q qbar ε UJg nd ar), i.Valid) ∧
    (∀ g, NInstr.gate g ∈ synthBudget hS ε' (nativeSimSigned a t Q qbar ε UJg nd ar) →
      GateOf 𝒢 g) ∧
    (∀ p : J → Bool, nCallsN p (synthBudget hS ε' (nativeSimSigned a t Q qbar ε UJg nd ar)) =
      12 * fDeg Q |t| qbar (ε / 2) * nCallsN p nd.V) ∧
    nGatesN (synthBudget hS ε' (nativeSimSigned a t Q qbar ε UJg nd ar)) ≤
      nGatesN (nativeSimSigned a t Q qbar ε UJg nd ar) *
        L (ε' / (nGatesN (nativeSimSigned a t Q qbar ε UJg nd ar) + 1)) ∧
    nGatesN (nativeSimSigned a t Q qbar ε UJg nd ar) ≤
      200 * (fDeg Q |t| qbar (ε / 2) + 1) * (a + simM |t| (ε / 2) + simR Q |t| qbar (ε / 2) + 1) +
        84 * fDeg Q |t| qbar (ε / 2) * UJg.length +
        6 * fDeg Q |t| qbar (ε / 2) *
          (2 * nGatesN nd.V + 2 * ar.circ.length + (2 * ar.bP + ar.bT + 1)) ∧
    ‖nrun prim (synthBudget hS ε' (nativeSimSigned a t Q qbar ε UJg nd ar)) ∘L
        (cleanEmb (X := X) ∘L sysEmb (io (P := Reg S R))) -
        (cleanEmb ∘L sysEmb (io (P := Reg S R))) ∘L
          NormedSpace.exp ((-Complex.I * (t : ℂ)) • H)‖ ≤ ε + ε' := by
  obtain ⟨hvalid, hcalls, hgates, herr⟩ := native_simulation_signed a prim hprim UJg hUJg nd
    hnd ar ζ hζ har D R1 H hD hN t Q b qbar ε hQ hRight hLeft hR1 hBoundary hSelf hH hEndpoint
    hbq hqQ hε hε1 hζε
  obtain ⟨hv, hk, hg, hc⟩ := synthBudget_spec hS hε' _ hvalid
  refine ⟨hv, hk, fun p => (hc p).trans (hcalls p), hg, hgates, ?_⟩
  generalize NormedSpace.exp ((-Complex.I * (t : ℂ)) • H) = U at herr ⊢
  generalize nativeSimSigned a t Q qbar ε UJg nd ar = C at hvalid herr ⊢
  refine synthBudget_error hS hε' C hvalid prim hprim _ ?_ U herr
  intro ψ
  exact (norm_sysEmb _ (fun φ => by rw [io_apply, norm_bas]) ψ).le

/-- **Native gate-efficient time-dependent simulation over a finite gate set** (Theorem
`hs:thm:time` with the circuit of `hs:thm:gates`; `native_time_simulation`): for every propagator
`U` of the path, the synthesised circuit is within `ε + ε'` of `U(t)` on the clean system
embedding. -/
theorem native_time_simulation_synth (hS : Synthesis 𝒢 X L) (ε' : ℝ) (hε' : 0 < ε') (a m : ℕ)
    (prim : J → Reg Y R →L[ℂ] Reg Y R) (hprim : ∀ j, IsUnitary (prim j))
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
    (∀ i ∈ synthBudget hS ε' (nativeSimT a m (α * t) Q qbar ε UJg nd ar), i.Valid) ∧
    (∀ g, NInstr.gate g ∈ synthBudget hS ε' (nativeSimT a m (α * t) Q qbar ε UJg nd ar) →
      GateOf 𝒢 g) ∧
    (∀ p : J → Bool, nCallsN p (synthBudget hS ε' (nativeSimT a m (α * t) Q qbar ε UJg nd ar)) =
      12 * fDeg Q (α * t) qbar (ε / 4) * nCallsN p nd.V) ∧
    nGatesN (synthBudget hS ε' (nativeSimT a m (α * t) Q qbar ε UJg nd ar)) ≤
      nGatesN (nativeSimT a m (α * t) Q qbar ε UJg nd ar) *
        L (ε' / (nGatesN (nativeSimT a m (α * t) Q qbar ε UJg nd ar) + 1)) ∧
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
    ∀ U : ℝ → Reg S R →L[ℂ] Reg S R, U 0 = 1 → TimeDependent.SolvesOn Hpath U 0 t →
      ‖nrun prim (synthBudget hS ε' (nativeSimT a m (α * t) Q qbar ε UJg nd ar)) ∘L
          (cleanEmb (X := X) ∘L sysEmb (io (P := Reg S R))) -
          (cleanEmb ∘L sysEmb (io (P := Reg S R))) ∘L U t‖ ≤ ε + ε' := by
  obtain ⟨hvalid, hcalls, hgates, hcard, -, -, -, hex, herr⟩ := native_time_simulation a m prim
    hprim UJg hUJg nd hnd ar ζ hζ har D R1 hN Hpath Hs t α β δ Q b qbar ε ht hα hβ hQ hqQ hε hε1
    hCayley hFreeze hD hRight hLeft hR1 hBoundary hEndpoint hbq hSelf hHs hPath hLip hVal
    hValBudget hζε
  obtain ⟨hv, hk, hg, hc⟩ := synthBudget_spec hS hε' _ hvalid
  refine ⟨hv, hk, fun p => (hc p).trans (hcalls p), hg, hgates, ?_, hex, ?_⟩
  · rw [Fintype.card_sum, hcard]
  · intro U hU0 hU
    have h1 := herr U hU0 hU
    generalize U t = Ut at h1 ⊢
    generalize nativeSimT a m (α * t) Q qbar ε UJg nd ar = C at hvalid h1 ⊢
    refine synthBudget_error hS hε' C hvalid prim hprim _ ?_ Ut h1
    intro ψ
    exact (norm_sysEmb _ (fun φ => by rw [io_apply, norm_bas]) ψ).le

end Native

end

end SparseHamiltonian.GateSynth
