import GateEfficientMesh.BinaryMesh
import GateEfficientSynthesis.Binary

/-!
# The Hamiltonian endpoints over a finite gate set

The released finite-set forms of Theorem `hs:thm:gates` (`GateSynth.native_time_simulation_synth`,
`GateSynth.binary_time_simulation_synth`, `GateSynth.binary_time_simulation_budget_synth`)
synthesise the native circuit with the synthesis budget `ε'` (`GateSynth.synthBudget`: every
elementary gate at accuracy `ε'/(N+1)`) under the synthesis hypothesis `Synthesis 𝒢 X L`. The
same synthesis applies to the endpoints of this library, with the released `synthBudget_spec`
(validity, gates of `𝒢`, `N L(ε'/(N+1))` gates, unchanged primitive calls) and
`synthBudget_error` (the synthesis adds at most `ε'` to the full-output error):

* `native_time_simulation_certified_synth`, `native_time_simulation_mesh_synth`;
* `binary_time_simulation_certified_synth`, `binary_time_simulation_mesh_synth`;
* `binary_time_simulation_budget_certified_synth`: the budget form, with the released
  `GateSynth.gates_log_le` for a logarithmic synthesis length.

Every guarantee is the full-output error `ε + ε'` on the clean system embedding against every
integral-sense propagator and every classical piecewise propagator under the respective
certificate.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateMesh

noncomputable section

open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
open SparseHamiltonian.GateBinary SparseHamiltonian.GateSynth
open SparseHamiltonian.GateCircuit.Sim (iota0 fDeg simR io Wire io_apply)
open SparseHamiltonian.OracleCircuit CayleyClockInterface
open SparseHamiltonian.GatePointerEncoding (wordEquivFin)
open NativeSparseBlockEncoding (Data Query)
open MeasureTheory Set
open TimeDependentExtensions (IsMesh IsPiecewisePropagator slotPiece)
open IntegrablePathSimulation.Propagator (IsPropagator)
open scoped InnerProduct BigOperators

universe u v w x

section Native

variable {S Z Y J X : Type*} [Fintype S] [DecidableEq S] [Fintype Z] [DecidableEq Z]
  [Fintype Y] [DecidableEq Y] [Fintype X] [DecidableEq X]
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
variable {𝒢 : Set Kind} {L : ℝ → ℕ}

/-- **Native time-dependent simulation under the integrated certificate over a finite gate
set** (Theorem `hs:thm:gates`, time-dependent part, with finite-set synthesis as a hypothesis).
Under the hypotheses of `native_time_simulation_certified` and `Synthesis 𝒢 X L`, the synthesis
of the native circuit with the budget `ε' > 0` consists of valid gates of `𝒢` and primitive
calls, makes exactly `12 d` times the calls of `V`, uses at most `N L(ε'/(N+1))` gates (`N` the
native gate count), has `|X|` more qubits, and its full output with clean ancillas is within
`ε + ε'` of `U(t)` for every integral-sense and every classical piecewise propagator whenever
the certificate on the uniform slots is at most `ε / 4`. -/
theorem native_time_simulation_certified_synth (hS : Synthesis 𝒢 X L) (ε' : ℝ) (hε' : 0 < ε')
    (a m : ℕ) (prim : J → Reg Y R →L[ℂ] Reg Y R) (hprim : ∀ j, IsUnitary (prim j))
    (UJg : List (Gate (Fin a ⊕ S))) (hUJg : ∀ g ∈ UJg, GateOK 3 g)
    (nd : NativeOp (Fin m) (Fin a ⊕ S) Z Y J) (hnd : nd.Public)
    (ar : Arith (NB (Fin m) (Fin a ⊕ S) Z)) (ζ : ℝ) (hζ : 0 ≤ ζ)
    (har : ArithOK ar (Sum.inl (Sum.inr nd.o)) nd.dec ζ)
    (D R1 : ℕ → Anc a (Reg S R) →L[ℂ] Anc a (Reg S R))
    (hN : NativeOK prim nd (selOp (fun w : Cfg (Fin m) => D (wordEquivFin m w))))
    (Hs : ℕ → Reg S R →L[ℂ] Reg S R)
    (t α Q b qbar ε : ℝ) (ht : 0 ≤ t) (hα : 0 < α) (hQ : 1 ≤ Q)
    (hqQ : qbar ≤ Q) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hCayley : TimeSchedule.steps (α * t) (ε / 12) ≤ 2 ^ m)
    (hD : ∀ k < 2 ^ m, IsUnitary (D k))
    (hRight : ∀ k < 2 ^ m, (1 - D k) ∘L R1 k = 1)
    (hLeft : ∀ k < 2 ^ m, R1 k ∘L (1 - D k) = 1) (hR1 : ∀ k < 2 ^ m, ‖R1 k‖ ≤ Q)
    (hBoundary : ∀ k < 2 ^ m, (UJop (R := R) UJg ∘L iota0 (P := Reg S R))† ∘L R1 k ∘L
      (UJop (R := R) UJg ∘L iota0 (P := Reg S R)) =
        (2 : ℂ)⁻¹ • (1 + Complex.I • ((α : ℂ)⁻¹ • Hs k)))
    (hEndpoint : ∀ k < 2 ^ m, ‖R1 k ∘L (UJop (R := R) UJg ∘L iota0 (P := Reg S R))‖ ≤ b)
    (hbq : b ^ 2 ≤ qbar / 2)
    (hSelf : ∀ k < 2 ^ m, star (Hs k) = Hs k) (hHs : ∀ k < 2 ^ m, ‖Hs k‖ ≤ α)
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
    (∀ H U : ℝ → Reg S R →L[ℂ] Reg S R, (∀ᵐ u, u ∈ Icc 0 t → star (H u) = H u) →
      IntervalIntegrable H volume 0 t →
      ∑ k ∈ Finset.range (2 ^ m), ∫ u in slotMesh t m k..slotMesh t m (k + 1), ‖H u - Hs k‖ ≤
        ε / 4 →
      IsPropagator H U t →
      ‖nrun prim (synthBudget hS ε' (nativeSimT a m (α * t) Q qbar ε UJg nd ar)) ∘L
          (cleanEmb (X := X) ∘L sysEmb (io (P := Reg S R))) -
          (cleanEmb ∘L sysEmb (io (P := Reg S R))) ∘L U t‖ ≤ ε + ε') ∧
    (∀ (Hp : ℕ → ℝ → Reg S R →L[ℂ] Reg S R) (U : ℝ → Reg S R →L[ℂ] Reg S R),
      (∀ k < 2 ^ m, ∀ u ∈ Icc (slotMesh t m k) (slotMesh t m (k + 1)),
        star (Hp k u) = Hp k u) →
      (∀ k < 2 ^ m, IntervalIntegrable (Hp k) volume (slotMesh t m k) (slotMesh t m (k + 1))) →
      ∑ k ∈ Finset.range (2 ^ m),
          ∫ u in slotMesh t m k..slotMesh t m (k + 1), ‖Hp k u - Hs k‖ ≤ ε / 4 →
      IsPiecewisePropagator Hp (slotMesh t m) (2 ^ m) U →
      ‖nrun prim (synthBudget hS ε' (nativeSimT a m (α * t) Q qbar ε UJg nd ar)) ∘L
          (cleanEmb (X := X) ∘L sysEmb (io (P := Reg S R))) -
          (cleanEmb ∘L sysEmb (io (P := Reg S R))) ∘L U t‖ ≤ ε + ε') := by
  obtain ⟨hvalid, hcalls, hgates, hcard, -, -, -, herrI, herrP⟩ :=
    native_time_simulation_certified a m prim hprim UJg hUJg nd hnd ar ζ hζ har D R1 hN Hs t α Q
      b qbar ε ht hα hQ hqQ hε hε1 hCayley hD hRight hLeft hR1 hBoundary hEndpoint hbq hSelf hHs
      hζε
  obtain ⟨hv, hk, hg, hc⟩ := synthBudget_spec hS hε' _ hvalid
  refine ⟨hv, hk, fun p => (hc p).trans (hcalls p), hg, hgates, by rw [Fintype.card_sum, hcard],
    fun H U hH hint hcert hU => ?_, fun Hp U hH hint hcert hU => ?_⟩
  · have h1 := herrI H U hH hint hcert hU
    generalize U t = Ut at h1 ⊢
    generalize nativeSimT a m (α * t) Q qbar ε UJg nd ar = C at hvalid h1 ⊢
    refine synthBudget_error hS hε' C hvalid prim hprim _ ?_ Ut h1
    intro ψ
    exact (norm_sysEmb _ (fun φ => by rw [io_apply, norm_bas]) ψ).le
  · have h1 := herrP Hp U hH hint hcert hU
    generalize U t = Ut at h1 ⊢
    generalize nativeSimT a m (α * t) Q qbar ε UJg nd ar = C at hvalid h1 ⊢
    refine synthBudget_error hS hε' C hvalid prim hprim _ ?_ Ut h1
    intro ψ
    exact (norm_sysEmb _ (fun φ => by rw [io_apply, norm_bas]) ψ).le

/-- **Native time-dependent simulation on a nonuniform mesh over a finite gate set** (Theorem
`hs:thm:gates`, time-dependent part, extended by uniform refinement to nonuniform meshes with
breakpoints, with finite-set synthesis as a hypothesis).
Under the hypotheses of `native_time_simulation_mesh` and `Synthesis 𝒢 X L`, the synthesis of
the native circuit with the budget `ε' > 0` has the counts of
`native_time_simulation_certified_synth`, and its full output with clean ancillas is within
`ε + ε'` of `U(T)` for every integral-sense and every classical piecewise propagator (one piece
per mesh interval) whenever the mesh certificate is at most `ε / 8`. -/
theorem native_time_simulation_mesh_synth (hS : Synthesis 𝒢 X L) (ε' : ℝ) (hε' : 0 < ε')
    (a m M : ℕ) (hM : 0 < M) (prim : J → Reg Y R →L[ℂ] Reg Y R)
    (hprim : ∀ j, IsUnitary (prim j))
    (UJg : List (Gate (Fin a ⊕ S))) (hUJg : ∀ g ∈ UJg, GateOK 3 g)
    (nd : NativeOp (Fin m) (Fin a ⊕ S) Z Y J) (hnd : nd.Public)
    (ar : Arith (NB (Fin m) (Fin a ⊕ S) Z)) (ζ : ℝ) (hζ : 0 ≤ ζ)
    (har : ArithOK ar (Sum.inl (Sum.inr nd.o)) nd.dec ζ)
    (D R1 : ℕ → Anc a (Reg S R) →L[ℂ] Anc a (Reg S R)) (Hs : ℕ → Reg S R →L[ℂ] Reg S R)
    (tm : ℕ → ℝ) (T α Q b qbar ε : ℝ) (hmesh : IsMesh tm M T) (hT : 0 < T)
    (hN : NativeOK prim nd
      (selOp (fun w : Cfg (Fin m) => D (slotPiece tm T (2 ^ m) M (wordEquivFin m w)))))
    (hα : 0 < α) (hQ : 1 ≤ Q) (hqQ : qbar ≤ Q) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hCayley : TimeSchedule.steps (α * T) (ε / 12) ≤ 2 ^ m)
    (hRound : 8 * M * α * T ≤ ε * 2 ^ m)
    (hD : ∀ r < M, IsUnitary (D r))
    (hRight : ∀ r < M, (1 - D r) ∘L R1 r = 1)
    (hLeft : ∀ r < M, R1 r ∘L (1 - D r) = 1) (hR1 : ∀ r < M, ‖R1 r‖ ≤ Q)
    (hBoundary : ∀ r < M, (UJop (R := R) UJg ∘L iota0 (P := Reg S R))† ∘L R1 r ∘L
      (UJop (R := R) UJg ∘L iota0 (P := Reg S R)) =
        (2 : ℂ)⁻¹ • (1 + Complex.I • ((α : ℂ)⁻¹ • Hs r)))
    (hEndpoint : ∀ r < M, ‖R1 r ∘L (UJop (R := R) UJg ∘L iota0 (P := Reg S R))‖ ≤ b)
    (hbq : b ^ 2 ≤ qbar / 2)
    (hSelf : ∀ r < M, star (Hs r) = Hs r) (hHs : ∀ r < M, ‖Hs r‖ ≤ α)
    (hζε : 48 * (fDeg Q (α * T) qbar (ε / 4) : ℝ) * ζ ≤ ε) :
    (∀ i ∈ synthBudget hS ε' (nativeSimT a m (α * T) Q qbar ε UJg nd ar), i.Valid) ∧
    (∀ g, NInstr.gate g ∈ synthBudget hS ε' (nativeSimT a m (α * T) Q qbar ε UJg nd ar) →
      GateOf 𝒢 g) ∧
    (∀ p : J → Bool, nCallsN p (synthBudget hS ε' (nativeSimT a m (α * T) Q qbar ε UJg nd ar)) =
      12 * fDeg Q (α * T) qbar (ε / 4) * nCallsN p nd.V) ∧
    nGatesN (synthBudget hS ε' (nativeSimT a m (α * T) Q qbar ε UJg nd ar)) ≤
      nGatesN (nativeSimT a m (α * T) Q qbar ε UJg nd ar) *
        L (ε' / (nGatesN (nativeSimT a m (α * T) Q qbar ε UJg nd ar) + 1)) ∧
    nGatesN (nativeSimT a m (α * T) Q qbar ε UJg nd ar) ≤
      200 * (fDeg Q (α * T) qbar (ε / 4) + 1) * (a + m + simR Q (α * T) qbar (ε / 4) + 1) +
        84 * fDeg Q (α * T) qbar (ε / 4) * UJg.length +
        6 * fDeg Q (α * T) qbar (ε / 4) *
          (2 * nGatesN nd.V + 2 * ar.circ.length + (2 * ar.bP + ar.bT + 1)) ∧
    Fintype.card (HW (Wire a m (simR Q (α * T) qbar (ε / 4))
        (a + m + 2 * simR Q (α * T) qbar (ε / 4))) S Empty Z ar.bT ar.bP ar.A ⊕ X) =
      Fintype.card S + (2 * a + 3 * m + 6 * simR Q (α * T) qbar (ε / 4) + 3) +
        (Fintype.card Z + ar.bT + ar.bP + ar.A + 3) + Fintype.card X ∧
    (∀ H U : ℝ → Reg S R →L[ℂ] Reg S R, (∀ᵐ u, u ∈ Icc 0 T → star (H u) = H u) →
      IntervalIntegrable H volume 0 T →
      ∑ r ∈ Finset.range M, ∫ u in tm r..tm (r + 1), ‖H u - Hs r‖ ≤ ε / 8 →
      IsPropagator H U T →
      ‖nrun prim (synthBudget hS ε' (nativeSimT a m (α * T) Q qbar ε UJg nd ar)) ∘L
          (cleanEmb (X := X) ∘L sysEmb (io (P := Reg S R))) -
          (cleanEmb ∘L sysEmb (io (P := Reg S R))) ∘L U T‖ ≤ ε + ε') ∧
    (∀ (Hp : ℕ → ℝ → Reg S R →L[ℂ] Reg S R) (U : ℝ → Reg S R →L[ℂ] Reg S R),
      (∀ r < M, ∀ u ∈ Icc (tm r) (tm (r + 1)), star (Hp r u) = Hp r u) →
      (∀ r < M, IntervalIntegrable (Hp r) volume (tm r) (tm (r + 1))) →
      ∑ r ∈ Finset.range M, ∫ u in tm r..tm (r + 1), ‖Hp r u - Hs r‖ ≤ ε / 8 →
      IsPiecewisePropagator Hp tm M U →
      ‖nrun prim (synthBudget hS ε' (nativeSimT a m (α * T) Q qbar ε UJg nd ar)) ∘L
          (cleanEmb (X := X) ∘L sysEmb (io (P := Reg S R))) -
          (cleanEmb ∘L sysEmb (io (P := Reg S R))) ∘L U T‖ ≤ ε + ε') := by
  obtain ⟨hvalid, hcalls, hgates, hcard, -, -, -, herrI, herrP⟩ :=
    native_time_simulation_mesh a m M hM prim hprim UJg hUJg nd hnd ar ζ hζ har D R1 Hs tm T α Q
      b qbar ε hmesh hT hN hα hQ hqQ hε hε1 hCayley hRound hD hRight hLeft hR1 hBoundary
      hEndpoint hbq hSelf hHs hζε
  obtain ⟨hv, hk, hg, hc⟩ := synthBudget_spec hS hε' _ hvalid
  refine ⟨hv, hk, fun p => (hc p).trans (hcalls p), hg, hgates, by rw [Fintype.card_sum, hcard],
    fun H U hH hint hcert hU => ?_, fun Hp U hH hint hcert hU => ?_⟩
  · have h1 := herrI H U hH hint hcert hU
    generalize U T = Ut at h1 ⊢
    generalize nativeSimT a m (α * T) Q qbar ε UJg nd ar = C at hvalid h1 ⊢
    refine synthBudget_error hS hε' C hvalid prim hprim _ ?_ Ut h1
    intro ψ
    exact (norm_sysEmb _ (fun φ => by rw [io_apply, norm_bas]) ψ).le
  · have h1 := herrP Hp U hH hint hcert hU
    generalize U T = Ut at h1 ⊢
    generalize nativeSimT a m (α * T) Q qbar ε UJg nd ar = C at hvalid h1 ⊢
    refine synthBudget_error hS hε' C hvalid prim hprim _ ?_ Ut h1
    intro ψ
    exact (norm_sysEmb _ (fun φ => by rw [io_apply, norm_bas]) ψ).le

end Native

section Binary

variable {X n : Type*} [Fintype n] [DecidableEq n] {s k b m M : ℕ}
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
variable {Xa : Type*} [Fintype Xa] [DecidableEq Xa] {𝒢 : Set Kind} {L : ℝ → ℕ}

/-- **Time-dependent simulation from binary data under the integrated certificate over a finite
gate set** (Theorem `hs:thm:gates`, time-dependent part, for time-indexed binary sparse oracles,
with finite-set synthesis as a hypothesis). Under the hypotheses of
`binary_time_simulation_certified` and `Synthesis 𝒢 Xa L`, the synthesis of `binaryTimeSim`
with the budget `ε' > 0` consists of valid gates of `𝒢` and primitive calls, makes `12 d` times
`2` row, `2` column and `1` value calls, uses at most `N L(ε'/(N+1))` gates (`N` the native
gate count), has `|Xa|` more qubits, and its full output with clean ancillas is within
`ε + ε'` of `U(t)` for every integral-sense and every classical piecewise propagator of the
lifted path whenever the certificate on the uniform slots is at most `ε / 4`. -/
theorem binary_time_simulation_certified_synth (hS : Synthesis 𝒢 Xa L) (ε' : ℝ) (hε' : 0 < ε')
    (D : Data (X × Fin (2 ^ m)) n (Cfg (VW b)) s)
    (en : Cfg (Fin k) ≃ n) (σ : ℕ) (hσ : σ ≤ k) (hs : s = 2 ^ σ)
    (hrange : ∀ j : n, (∃ q, D.slot q = j) ↔ ∃ u : Fin σ → Bool, j = en (lowWord σ u))
    (hb : 0 < b) (c0 : ℝ) (hc0 : 0 < c0) (hdec : ∀ e z, D.decode e z = (c0 : ℂ) * gauss z)
    (x : X) (hHerm : ∀ r, (D.matrix (x, r)).IsHermitian)
    (hrow : ∀ r i, ∑ j, ‖D.matrix (x, r) i j‖ ^ 2 ≤ 1)
    (hcol : ∀ r j, ∑ i, ‖D.matrix (x, r) i j‖ ^ 2 ≤ 1)
    (t γ ε ζ : ℝ) (ht : 0 ≤ t) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hCayley : TimeSchedule.steps (time (s : ℝ) t γ) (ε / 12) ≤ 2 ^ m)
    (hζε : 48 * (fDeg (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4) : ℝ) * ζ ≤ ε) :
    (∀ i ∈ synthBudget hS ε' (binaryTimeSim k b m σ hσ s γ c0 t ε ζ), i.Valid) ∧
    (∀ g, NInstr.gate g ∈ synthBudget hS ε' (binaryTimeSim k b m σ hσ s γ c0 t ε ζ) →
      GateOf 𝒢 g) ∧
    (∀ p : Query → Bool,
      nCallsN p (synthBudget hS ε' (binaryTimeSim k b m σ hσ s γ c0 t ε ζ)) =
        12 * fDeg (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4) *
          (2 * (if p Query.rowLocation then 1 else 0) +
            2 * (if p Query.columnLocation then 1 else 0) + (if p Query.value then 1 else 0))) ∧
    nGatesN (synthBudget hS ε' (binaryTimeSim k b m σ hσ s γ c0 t ε ζ)) ≤
      nGatesN (binaryTimeSim k b m σ hσ s γ c0 t ε ζ) *
        L (ε' / (nGatesN (binaryTimeSim k b m σ hσ s γ c0 t ε ζ) + 1)) ∧
    nGatesN (binaryTimeSim k b m σ hσ s γ c0 t ε ζ) ≤
      200 * (fDeg (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4) + 1) *
          (k + 1 + m + simR (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4) + 1) +
        84 * fDeg (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4) * (σ + 1) +
        6 * fDeg (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4) *
          (2 * (28 * k) + 2 * (binArithT k b m (γ * Real.sqrt s * c0) ζ).circ.length +
            (2 * (binArithT k b m (γ * Real.sqrt s * c0) ζ).bP +
              (binArithT k b m (γ * Real.sqrt s * c0) ζ).bT + 1)) ∧
    Fintype.card (HW (Wire (k + 1) m
        (simR (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4))
        (k + 1 + m + 2 * simR (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4)))
        (Fin k) Empty (SZ k b) (binArithT k b m (γ * Real.sqrt s * c0) ζ).bT
        (binArithT k b m (γ * Real.sqrt s * c0) ζ).bP
        (binArithT k b m (γ * Real.sqrt s * c0) ζ).A ⊕ Xa) =
      k + (2 * (k + 1) + 3 * m +
          6 * simR (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4) + 3) +
        (6 * k + 2 * b + (binArithT k b m (γ * Real.sqrt s * c0) ζ).bT +
          (binArithT k b m (γ * Real.sqrt s * c0) ζ).bP +
          (binArithT k b m (γ * Real.sqrt s * c0) ζ).A + 3) + Fintype.card Xa ∧
    (∀ (H : ℝ → Matrix n n ℂ) (U : ℝ → Reg (Fin k) R →L[ℂ] Reg (Fin k) R),
      (∀ᵐ u, u ∈ Icc 0 t → (H u).IsHermitian) →
      IntervalIntegrable (fun u => SparseStateOverlap.matrixOperator (H u)) volume 0 t →
      ∑ r : Fin (2 ^ m), ∫ u in slotMesh t m r..slotMesh t m ((r : ℕ) + 1),
          ‖SparseStateOverlap.matrixOperator (H u) -
            SparseStateOverlap.matrixOperator (D.matrix (x, r))‖ ≤ ε / 4 →
      IsPropagator (fun u => qlift (R := R) en (SparseStateOverlap.matrixOperator (H u))) U t →
      ‖nrun (primsT (R := R) D en x)
            (synthBudget hS ε' (binaryTimeSim k b m σ hσ s γ c0 t ε ζ)) ∘L
          (cleanEmb (X := Xa) ∘L sysEmb (io (P := Reg (Fin k) R))) -
          (cleanEmb ∘L sysEmb (io (P := Reg (Fin k) R))) ∘L U t‖ ≤ ε + ε') ∧
    (∀ (Hp : ℕ → ℝ → Matrix n n ℂ) (U : ℝ → Reg (Fin k) R →L[ℂ] Reg (Fin k) R),
      (∀ r < 2 ^ m, ∀ u ∈ Icc (slotMesh t m r) (slotMesh t m (r + 1)), (Hp r u).IsHermitian) →
      (∀ r < 2 ^ m, IntervalIntegrable (fun u => SparseStateOverlap.matrixOperator (Hp r u))
        volume (slotMesh t m r) (slotMesh t m (r + 1))) →
      ∑ r : Fin (2 ^ m), ∫ u in slotMesh t m r..slotMesh t m ((r : ℕ) + 1),
          ‖SparseStateOverlap.matrixOperator (Hp r u) -
            SparseStateOverlap.matrixOperator (D.matrix (x, r))‖ ≤ ε / 4 →
      IsPiecewisePropagator
        (fun r u => qlift (R := R) en (SparseStateOverlap.matrixOperator (Hp r u)))
        (slotMesh t m) (2 ^ m) U →
      ‖nrun (primsT (R := R) D en x)
            (synthBudget hS ε' (binaryTimeSim k b m σ hσ s γ c0 t ε ζ)) ∘L
          (cleanEmb (X := Xa) ∘L sysEmb (io (P := Reg (Fin k) R))) -
          (cleanEmb ∘L sysEmb (io (P := Reg (Fin k) R))) ∘L U t‖ ≤ ε + ε') := by
  obtain ⟨hvalid, hcalls, hgates, hcard, -, -, -, herrI, herrP⟩ :=
    binary_time_simulation_certified (R := R) D en σ hσ hs hrange hb c0 hc0 hdec x hHerm hrow
      hcol t γ ε ζ ht hγ hγ1 hε hε1 hζ hζ1 hCayley hζε
  obtain ⟨hv, hk, hg, hc⟩ := synthBudget_spec hS hε' _ hvalid
  have hpu := primsT_isUnitary (R := R) D en x
  refine ⟨hv, hk, fun p => (hc p).trans (hcalls p), hg, hgates, by rw [Fintype.card_sum, hcard],
    fun H U hH hint hcert hU => ?_, fun Hp U hH hint hcert hU => ?_⟩
  · have h1 := herrI H U hH hint hcert hU
    generalize U t = Ut at h1 ⊢
    generalize binaryTimeSim k b m σ hσ s γ c0 t ε ζ = C at hvalid h1 ⊢
    generalize primsT (R := R) D en x = prim at hpu h1 ⊢
    refine synthBudget_error hS hε' C hvalid prim hpu _ ?_ Ut h1
    intro ψ
    exact (norm_sysEmb _ (fun φ => by rw [io_apply, norm_bas]) ψ).le
  · have h1 := herrP Hp U hH hint hcert hU
    generalize U t = Ut at h1 ⊢
    generalize binaryTimeSim k b m σ hσ s γ c0 t ε ζ = C at hvalid h1 ⊢
    generalize primsT (R := R) D en x = prim at hpu h1 ⊢
    refine synthBudget_error hS hε' C hvalid prim hpu _ ?_ Ut h1
    intro ψ
    exact (norm_sysEmb _ (fun φ => by rw [io_apply, norm_bas]) ψ).le

/-- **Time-dependent simulation from binary data on a nonuniform mesh over a finite gate set**
(Theorem `hs:thm:gates`, time-dependent part, for binary sparse oracles, extended by uniform
refinement to nonuniform meshes with breakpoints, with finite-set synthesis as a hypothesis).
Under the hypotheses of `binary_time_simulation_mesh` and `Synthesis 𝒢 Xa L`, the synthesis of
`binaryTimeSim` (run on the clock data `clockData D_m`) with the budget `ε' > 0` has the counts
of `binary_time_simulation_certified_synth`, and its full output with clean ancillas is within
`ε + ε'` of `U(T)` for every integral-sense and every classical piecewise propagator (one piece
per mesh interval) of the lifted path whenever the mesh certificate is at most `ε / 8`. -/
theorem binary_time_simulation_mesh_synth (hS : Synthesis 𝒢 Xa L) (ε' : ℝ) (hε' : 0 < ε')
    (D : Data (X × Fin M) n (Cfg (VW b)) s) (hM : 0 < M)
    (en : Cfg (Fin k) ≃ n) (σ : ℕ) (hσ : σ ≤ k) (hs : s = 2 ^ σ)
    (hrange : ∀ j : n, (∃ q, D.slot q = j) ↔ ∃ u : Fin σ → Bool, j = en (lowWord σ u))
    (hb : 0 < b) (c0 : ℝ) (hc0 : 0 < c0) (hdec : ∀ e z, D.decode e z = (c0 : ℂ) * gauss z)
    (x : X) (hHerm : ∀ r, (D.matrix (x, r)).IsHermitian)
    (hrow : ∀ r i, ∑ j, ‖D.matrix (x, r) i j‖ ^ 2 ≤ 1)
    (hcol : ∀ r j, ∑ i, ‖D.matrix (x, r) i j‖ ^ 2 ≤ 1)
    (tm : ℕ → ℝ) (T γ ε ζ : ℝ) (hmesh : IsMesh tm M T) (hT : 0 < T) (hγ : 0 < γ)
    (hγ1 : γ ≤ 1) (hε : 0 < ε) (hε1 : ε ≤ 1) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hCayley : TimeSchedule.steps (time (s : ℝ) T γ) (ε / 12) ≤ 2 ^ m)
    (hRound : 8 * M * time (s : ℝ) T γ ≤ ε * 2 ^ m)
    (hζε : 48 * (fDeg (width (s : ℝ) γ) (time (s : ℝ) T γ) (moment γ) (ε / 4) : ℝ) * ζ ≤ ε) :
    (∀ i ∈ synthBudget hS ε' (binaryTimeSim k b m σ hσ s γ c0 T ε ζ), i.Valid) ∧
    (∀ g, NInstr.gate g ∈ synthBudget hS ε' (binaryTimeSim k b m σ hσ s γ c0 T ε ζ) →
      GateOf 𝒢 g) ∧
    (∀ p : Query → Bool,
      nCallsN p (synthBudget hS ε' (binaryTimeSim k b m σ hσ s γ c0 T ε ζ)) =
        12 * fDeg (width (s : ℝ) γ) (time (s : ℝ) T γ) (moment γ) (ε / 4) *
          (2 * (if p Query.rowLocation then 1 else 0) +
            2 * (if p Query.columnLocation then 1 else 0) + (if p Query.value then 1 else 0))) ∧
    nGatesN (synthBudget hS ε' (binaryTimeSim k b m σ hσ s γ c0 T ε ζ)) ≤
      nGatesN (binaryTimeSim k b m σ hσ s γ c0 T ε ζ) *
        L (ε' / (nGatesN (binaryTimeSim k b m σ hσ s γ c0 T ε ζ) + 1)) ∧
    nGatesN (binaryTimeSim k b m σ hσ s γ c0 T ε ζ) ≤
      200 * (fDeg (width (s : ℝ) γ) (time (s : ℝ) T γ) (moment γ) (ε / 4) + 1) *
          (k + 1 + m + simR (width (s : ℝ) γ) (time (s : ℝ) T γ) (moment γ) (ε / 4) + 1) +
        84 * fDeg (width (s : ℝ) γ) (time (s : ℝ) T γ) (moment γ) (ε / 4) * (σ + 1) +
        6 * fDeg (width (s : ℝ) γ) (time (s : ℝ) T γ) (moment γ) (ε / 4) *
          (2 * (28 * k) + 2 * (binArithT k b m (γ * Real.sqrt s * c0) ζ).circ.length +
            (2 * (binArithT k b m (γ * Real.sqrt s * c0) ζ).bP +
              (binArithT k b m (γ * Real.sqrt s * c0) ζ).bT + 1)) ∧
    Fintype.card (HW (Wire (k + 1) m
        (simR (width (s : ℝ) γ) (time (s : ℝ) T γ) (moment γ) (ε / 4))
        (k + 1 + m + 2 * simR (width (s : ℝ) γ) (time (s : ℝ) T γ) (moment γ) (ε / 4)))
        (Fin k) Empty (SZ k b) (binArithT k b m (γ * Real.sqrt s * c0) ζ).bT
        (binArithT k b m (γ * Real.sqrt s * c0) ζ).bP
        (binArithT k b m (γ * Real.sqrt s * c0) ζ).A ⊕ Xa) =
      k + (2 * (k + 1) + 3 * m +
          6 * simR (width (s : ℝ) γ) (time (s : ℝ) T γ) (moment γ) (ε / 4) + 3) +
        (6 * k + 2 * b + (binArithT k b m (γ * Real.sqrt s * c0) ζ).bT +
          (binArithT k b m (γ * Real.sqrt s * c0) ζ).bP +
          (binArithT k b m (γ * Real.sqrt s * c0) ζ).A + 3) + Fintype.card Xa ∧
    (∀ (H : ℝ → Matrix n n ℂ) (U : ℝ → Reg (Fin k) R →L[ℂ] Reg (Fin k) R),
      (∀ᵐ u, u ∈ Icc 0 T → (H u).IsHermitian) →
      IntervalIntegrable (fun u => SparseStateOverlap.matrixOperator (H u)) volume 0 T →
      ∑ r : Fin M, ∫ u in tm r..tm ((r : ℕ) + 1),
          ‖SparseStateOverlap.matrixOperator (H u) -
            SparseStateOverlap.matrixOperator (D.matrix (x, r))‖ ≤ ε / 8 →
      IsPropagator (fun u => qlift (R := R) en (SparseStateOverlap.matrixOperator (H u))) U T →
      ‖nrun (primsT (R := R) (clockData D hM tm T m) en x)
            (synthBudget hS ε' (binaryTimeSim k b m σ hσ s γ c0 T ε ζ)) ∘L
          (cleanEmb (X := Xa) ∘L sysEmb (io (P := Reg (Fin k) R))) -
          (cleanEmb ∘L sysEmb (io (P := Reg (Fin k) R))) ∘L U T‖ ≤ ε + ε') ∧
    (∀ (Hp : ℕ → ℝ → Matrix n n ℂ) (U : ℝ → Reg (Fin k) R →L[ℂ] Reg (Fin k) R),
      (∀ r < M, ∀ u ∈ Icc (tm r) (tm (r + 1)), (Hp r u).IsHermitian) →
      (∀ r < M, IntervalIntegrable (fun u => SparseStateOverlap.matrixOperator (Hp r u))
        volume (tm r) (tm (r + 1))) →
      ∑ r : Fin M, ∫ u in tm r..tm ((r : ℕ) + 1),
          ‖SparseStateOverlap.matrixOperator (Hp r u) -
            SparseStateOverlap.matrixOperator (D.matrix (x, r))‖ ≤ ε / 8 →
      IsPiecewisePropagator
        (fun r u => qlift (R := R) en (SparseStateOverlap.matrixOperator (Hp r u))) tm M U →
      ‖nrun (primsT (R := R) (clockData D hM tm T m) en x)
            (synthBudget hS ε' (binaryTimeSim k b m σ hσ s γ c0 T ε ζ)) ∘L
          (cleanEmb (X := Xa) ∘L sysEmb (io (P := Reg (Fin k) R))) -
          (cleanEmb ∘L sysEmb (io (P := Reg (Fin k) R))) ∘L U T‖ ≤ ε + ε') := by
  obtain ⟨hvalid, hcalls, hgates, hcard, -, -, -, herrI, herrP⟩ :=
    binary_time_simulation_mesh (R := R) D hM en σ hσ hs hrange hb c0 hc0 hdec x hHerm hrow hcol
      tm T γ ε ζ hmesh hT hγ hγ1 hε hε1 hζ hζ1 hCayley hRound hζε
  obtain ⟨hv, hk, hg, hc⟩ := synthBudget_spec hS hε' _ hvalid
  have hpu := primsT_isUnitary (R := R) (clockData D hM tm T m) en x
  refine ⟨hv, hk, fun p => (hc p).trans (hcalls p), hg, hgates, by rw [Fintype.card_sum, hcard],
    fun H U hH hint hcert hU => ?_, fun Hp U hH hint hcert hU => ?_⟩
  · have h1 := herrI H U hH hint hcert hU
    generalize U T = Ut at h1 ⊢
    generalize binaryTimeSim k b m σ hσ s γ c0 T ε ζ = C at hvalid h1 ⊢
    generalize primsT (R := R) (clockData D hM tm T m) en x = prim at hpu h1 ⊢
    refine synthBudget_error hS hε' C hvalid prim hpu _ ?_ Ut h1
    intro ψ
    exact (norm_sysEmb _ (fun φ => by rw [io_apply, norm_bas]) ψ).le
  · have h1 := herrP Hp U hH hint hcert hU
    generalize U T = Ut at h1 ⊢
    generalize binaryTimeSim k b m σ hσ s γ c0 T ε ζ = C at hvalid h1 ⊢
    generalize primsT (R := R) (clockData D hM tm T m) en x = prim at hpu h1 ⊢
    refine synthBudget_error hS hε' C hvalid prim hpu _ ?_ Ut h1
    intro ψ
    exact (norm_sysEmb _ (fun φ => by rw [io_apply, norm_bas]) ψ).le

end Binary

/-- **The gate budget of the time-dependent binary construction under the integrated
certificate over a finite gate set** (Theorem `hs:thm:gates`, time-dependent part, equation
`hs:eq:gate-total` with the binary-data construction and finite-set synthesis as a hypothesis).
The rescaling `γ` of `binary_time_simulation_budget_certified` is chosen from `s`, `t` and `ε`
before the gate set, the synthesis budget, the data and the path, with `d ≤ 4608 q`. For every
gate set with a logarithmic synthesis length `L ζ ≤ c₁ log(1/ζ) + c₀`, every synthesis budget
`0 < ε' ≤ 1` and all data as in `binary_time_simulation_budget_certified` (the slot exponent
constrained only by the subdivision condition), the synthesised circuit consists of valid gates
of `𝒢` and primitive calls, makes at most `55296 q` times `2` row, `2` column and `1` value calls,
uses at most `G (c₁ log((G+1)/ε') + c₀)` gates with the pre-synthesis budget
`G = 200 (4608 q + 1)(G_C + (σ+1) + (k+1) + m + r + 1)`, `2^r ≤ 4 (4608 q + 1)`, and its full
output is within `ε + ε'` of `U(t)` for every integral-sense propagator of the lift of every
matrix path that is Hermitian almost everywhere and interval integrable with certificate at most
`ε / 4`. -/
theorem binary_time_simulation_budget_certified_synth (s : ℕ) (hs1 : 1 ≤ s) (t ε : ℝ)
    (ht : 0 ≤ t) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 1 ≤ γ * Real.sqrt s ∧
      (fDeg (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4) : ℝ) ≤
        4608 * ImprovedPrecisionBudget.shape s t (Real.log (2 / ε)) ∧
      ∀ {Xa : Type x} [Fintype Xa] [DecidableEq Xa] {𝒢 : Set Kind} {L : ℝ → ℕ}
        (hS : Synthesis 𝒢 Xa L) {c₀ c₁ : ℝ}, 0 ≤ c₀ → 0 ≤ c₁ →
        (∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 → (L ζ : ℝ) ≤ c₁ * Real.log (1 / ζ) + c₀) →
        ∀ ε' : ℝ, 0 < ε' → ε' ≤ 1 →
      ∀ {X : Type u} {n : Type v} [Fintype n] [DecidableEq n] {k b m : ℕ} {R : Type w}
        [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
        (D : Data (X × Fin (2 ^ m)) n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (σ : ℕ)
        (hσ : σ ≤ k), s = 2 ^ σ →
        (∀ j : n, (∃ q, D.slot q = j) ↔ ∃ u : Fin σ → Bool, j = en (lowWord σ u)) →
        0 < b → ∀ c0 : ℝ, 0 < c0 → (∀ e z, D.decode e z = (c0 : ℂ) * gauss z) →
        ∀ x : X, (∀ r, (D.matrix (x, r)).IsHermitian) →
        (∀ r i, ∑ j, ‖D.matrix (x, r) i j‖ ^ 2 ≤ 1) →
        (∀ r j, ∑ i, ‖D.matrix (x, r) i j‖ ^ 2 ≤ 1) →
        TimeSchedule.steps (time (s : ℝ) t γ) (ε / 12) ≤ 2 ^ m →
        ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 →
        221184 * ImprovedPrecisionBudget.shape s t (Real.log (2 / ε)) * ζ ≤ ε →
        (∀ i ∈ synthBudget hS ε' (binaryTimeSim k b m σ hσ s γ c0 t ε ζ), i.Valid) ∧
        (∀ g, NInstr.gate g ∈ synthBudget hS ε' (binaryTimeSim k b m σ hσ s γ c0 t ε ζ) →
          GateOf 𝒢 g) ∧
        (∀ p : Query → Bool,
          (nCallsN p (synthBudget hS ε' (binaryTimeSim k b m σ hσ s γ c0 t ε ζ)) : ℝ) ≤
            55296 * ImprovedPrecisionBudget.shape s t (Real.log (2 / ε)) *
              (2 * (if p Query.rowLocation then 1 else 0) +
                2 * (if p Query.columnLocation then 1 else 0) +
                (if p Query.value then 1 else 0))) ∧
        (nGatesN (synthBudget hS ε' (binaryTimeSim k b m σ hσ s γ c0 t ε ζ)) : ℝ) ≤
          200 * (4608 * ImprovedPrecisionBudget.shape s t (Real.log (2 / ε)) + 1) *
              ((privGates (sparseOpT k b m (γ * Real.sqrt s * c0))
                  (binArithT k b m (γ * Real.sqrt s * c0) ζ) : ℝ) + (σ + 1) + (k + 1) + m +
                simR (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4) + 1) *
            (c₁ * Real.log ((200 * (4608 * ImprovedPrecisionBudget.shape s t
                  (Real.log (2 / ε)) + 1) *
              ((privGates (sparseOpT k b m (γ * Real.sqrt s * c0))
                  (binArithT k b m (γ * Real.sqrt s * c0) ζ) : ℝ) + (σ + 1) + (k + 1) + m +
                simR (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4) + 1) + 1) / ε') +
              c₀) ∧
        ((2 ^ simR (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4) : ℕ) : ℝ) ≤
          4 * (4608 * ImprovedPrecisionBudget.shape s t (Real.log (2 / ε)) + 1) ∧
        ∀ (H : ℝ → Matrix n n ℂ) (U : ℝ → Reg (Fin k) R →L[ℂ] Reg (Fin k) R),
          (∀ᵐ u, u ∈ Icc 0 t → (H u).IsHermitian) →
          IntervalIntegrable (fun u => SparseStateOverlap.matrixOperator (H u)) volume 0 t →
          ∑ r : Fin (2 ^ m), ∫ u in slotMesh t m r..slotMesh t m ((r : ℕ) + 1),
              ‖SparseStateOverlap.matrixOperator (H u) -
                SparseStateOverlap.matrixOperator (D.matrix (x, r))‖ ≤ ε / 4 →
          IsPropagator (fun u => qlift (R := R) en (SparseStateOverlap.matrixOperator (H u)))
            U t →
          ‖nrun (primsT (R := R) D en x)
                (synthBudget hS ε' (binaryTimeSim k b m σ hσ s γ c0 t ε ζ)) ∘L
              (cleanEmb (X := Xa) ∘L sysEmb (io (P := Reg (Fin k) R))) -
              (cleanEmb ∘L sysEmb (io (P := Reg (Fin k) R))) ∘L U t‖ ≤ ε + ε' := by
  obtain ⟨γ, hγ, hγ1, hγs, hdeg, hall⟩ :=
    binary_time_simulation_budget_certified.{u, v, w} s hs1 t ε ht hε hε1
  refine ⟨γ, hγ, hγ1, hγs, hdeg, ?_⟩
  intro Xa _ _ 𝒢 L hS c₀ c₁ hc₀ hc₁ hL ε' hε' hε'1 X n _ _ k b m R _ _ _ D en σ hσ hs hrange hb
    c0 hc0 hdec x hHerm hrow hcol hCayley ζ hζ hζ1 hζε
  have hζε' : 48 * (fDeg (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4) : ℝ) * ζ ≤
      ε := by
    nlinarith [hdeg, hζ]
  obtain ⟨hvalid, -, -, -, -, -, -, -, -⟩ := binary_time_simulation_certified (R := R) D en σ hσ
    hs hrange hb c0 hc0 hdec x hHerm hrow hcol t γ ε ζ ht hγ hγ1 hε hε1 hζ hζ1 hCayley hζε'
  obtain ⟨hcalls, hgates, hr2, herr⟩ := hall (R := R) D en σ hσ hs hrange hb c0 hc0 hdec x
    hHerm hrow hcol hCayley ζ hζ hζ1 hζε
  obtain ⟨hv, hk, hg, hc⟩ := synthBudget_spec hS hε' _ hvalid
  have hpu := primsT_isUnitary (R := R) D en x
  refine ⟨hv, hk, fun p => by rw [hc p]; exact hcalls p, ?_, hr2, fun H U hH hint hcert hU => ?_⟩
  · refine (Nat.cast_le.mpr hg).trans ?_
    exact gates_log_le hc₀ hc₁ hL hε' hε'1 _ _ hgates
  · have h1 := herr H U hH hint hcert hU
    generalize U t = Ut at h1 ⊢
    generalize binaryTimeSim k b m σ hσ s γ c0 t ε ζ = C at hvalid h1 ⊢
    generalize primsT (R := R) D en x = prim at hpu h1 ⊢
    refine synthBudget_error hS hε' C hvalid prim hpu _ ?_ Ut h1
    intro ψ
    exact (norm_sysEmb _ (fun φ => by rw [io_apply, norm_bas]) ψ).le

end

end SparseHamiltonian.GateMesh
