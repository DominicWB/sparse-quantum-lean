import GateEfficientSigned.Synth
import GateEfficientRemarks.ZeroSynthBinary

/-!
# Theorem `hs:thm:gates` from binary sparse data for every real time, with the identity at zero

Theorem `hs:thm:main` ends with "If `t = 0` …, the identity circuit suffices." The library
`GateEfficientRemarks` states this remark for the binary-data endpoints for every `τ ≥ 0`
(`GateRemarks.binary_simulation_nonneg`, `GateRemarks.binary_simulation_budget_nonneg`,
`GateRemarks.binary_simulation_synth_nonneg`, `GateRemarks.binary_simulation_budget_synth_nonneg`,
with the combined circuit `GateRemarks.binaryCircuit`). This file states it for every real `t`:

* `binaryCircuitSigned`: the empty circuit at `t = 0` and `binarySimSigned` otherwise, on the
  same wires;
* `binary_simulation_signed_zero`, `binary_simulation_budget_signed_zero`,
  `binary_simulation_synth_signed_zero`, `binary_simulation_budget_synth_signed_zero`: the
  endpoints of `binary_simulation_signed`, `binary_simulation_budget_signed`,
  `binary_simulation_synth_signed` and `binary_simulation_budget_synth_signed` for the combined
  circuit, with every count `0` at `t = 0` and the signed count otherwise, every other conclusion
  unchanged, and the full-output error exactly `0` at `t = 0`.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000

namespace SparseHamiltonian.GateSigned

noncomputable section
open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
open SparseHamiltonian.GateBinary SparseHamiltonian.OracleCircuit CayleyClockInterface
open SparseHamiltonian.GateSynth SparseHamiltonian.GateRemarks
open SparseHamiltonian.GateCircuit.Sim (fDeg simM simR SimWire io)
open SparseHamiltonian.ZeroTimeRemarks.Gates (exp_zero_time identity_comp_error_eq_zero
  identity_comp_error_le)
open NativeSparseBlockEncoding (Data Query)
open scoped InnerProduct

universe u v w x

/-- **The circuit from binary sparse data for every real time, with the identity at zero**: the
empty (identity) circuit at `t = 0` and `binarySimSigned` otherwise, on the same wires. -/
def binaryCircuitSigned (k b σ : ℕ) (hσ : σ ≤ k) (s : ℕ) (γ c0 t ε ζ : ℝ) :
    List (NInstr (HW (SimWire (k + 1) (width (s : ℝ) γ) (time (s : ℝ) |t| γ) (moment γ) (ε / 2))
      (Fin k) Empty (SZ k b) (binArith k b (γ * Real.sqrt s * c0) ζ).bT
      (binArith k b (γ * Real.sqrt s * c0) ζ).bP (binArith k b (γ * Real.sqrt s * c0) ζ).A)
      (PY k b) Query) :=
  if t = 0 then [] else binarySimSigned k b σ hσ s γ c0 t ε ζ

section Native

variable {X n : Type*} [Fintype n] [DecidableEq n] {s k b : ℕ}
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

set_option maxHeartbeats 1000000 in
/-- **Theorem `hs:thm:gates` from binary sparse data for every real time, with the identity
circuit at `t = 0`.** Under the hypotheses of `binary_simulation_signed`, the circuit
`binaryCircuitSigned k b σ hσ s γ c₀ t ε ζ` consists of valid instructions, makes `0` primitive
calls if `t = 0` and exactly `12 d` times `2` row, `2` column and `1` value calls otherwise, has
`0` elementary gates if `t = 0` and at most
`200 (d+1)(k+1+m+r+1) + 84 d (σ+1) + 6 d (56 k + 2 |circ| + 2 bP + bT + 1)` otherwise, and its
full output on the system embedding is within `ε` of `exp(-itĤ)`; at `t = 0` the error is exactly
`0`. The qubit count and the degree and register bounds are those of `binary_simulation_signed`
(the released ones for `|t|`). -/
theorem binary_simulation_signed_zero (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n)
    (σ : ℕ) (hσ : σ ≤ k) (hs : s = 2 ^ σ)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin σ → Bool, j = en (lowWord σ u))
    (hb : 0 < b) (c0 : ℝ) (hc0 : 0 < c0) (hdec : ∀ e z, D.decode e z = (c0 : ℂ) * gauss z)
    (x : X) (hH : (D.matrix x).IsHermitian) (hrow : ∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ 1)
    (hcol : ∀ j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ 1) (γ t ε ζ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hζε : 48 * (fDeg (width (s : ℝ) γ) (time (s : ℝ) |t| γ) (moment γ) (ε / 2) : ℝ) * ζ ≤ ε) :
    (∀ i ∈ binaryCircuitSigned k b σ hσ s γ c0 t ε ζ, i.Valid) ∧
    (∀ p : Query → Bool, nCallsN p (binaryCircuitSigned k b σ hσ s γ c0 t ε ζ) =
      (if t = 0 then 0 else
        12 * fDeg (width (s : ℝ) γ) (time (s : ℝ) |t| γ) (moment γ) (ε / 2) *
          (2 * (if p Query.rowLocation then 1 else 0) +
            2 * (if p Query.columnLocation then 1 else 0) +
            (if p Query.value then 1 else 0)))) ∧
    nGatesN (binaryCircuitSigned k b σ hσ s γ c0 t ε ζ) ≤
      (if t = 0 then 0 else
        200 * (fDeg (width (s : ℝ) γ) (time (s : ℝ) |t| γ) (moment γ) (ε / 2) + 1) *
            (k + 1 + simM (time (s : ℝ) |t| γ) (ε / 2) +
              simR (width (s : ℝ) γ) (time (s : ℝ) |t| γ) (moment γ) (ε / 2) + 1) +
          84 * fDeg (width (s : ℝ) γ) (time (s : ℝ) |t| γ) (moment γ) (ε / 2) * (σ + 1) +
          6 * fDeg (width (s : ℝ) γ) (time (s : ℝ) |t| γ) (moment γ) (ε / 2) *
            (2 * (28 * k) + 2 * (binArith k b (γ * Real.sqrt s * c0) ζ).circ.length +
              (2 * (binArith k b (γ * Real.sqrt s * c0) ζ).bP +
                (binArith k b (γ * Real.sqrt s * c0) ζ).bT + 1))) ∧
    Fintype.card (HW (SimWire (k + 1) (width (s : ℝ) γ) (time (s : ℝ) |t| γ) (moment γ) (ε / 2))
        (Fin k) Empty (SZ k b) (binArith k b (γ * Real.sqrt s * c0) ζ).bT
        (binArith k b (γ * Real.sqrt s * c0) ζ).bP (binArith k b (γ * Real.sqrt s * c0) ζ).A) =
      k + (2 * (k + 1) + 3 * simM (time (s : ℝ) |t| γ) (ε / 2) +
          6 * simR (width (s : ℝ) γ) (time (s : ℝ) |t| γ) (moment γ) (ε / 2) + 3) +
        (6 * k + 2 * b + (binArith k b (γ * Real.sqrt s * c0) ζ).bT +
          (binArith k b (γ * Real.sqrt s * c0) ζ).bP +
          (binArith k b (γ * Real.sqrt s * c0) ζ).A + 3) ∧
    ‖nrun (prims (R := R) D en x) (binaryCircuitSigned k b σ hσ s γ c0 t ε ζ) ∘L
        sysEmb (io (P := Reg (Fin k) R)) - sysEmb (io (P := Reg (Fin k) R)) ∘L
          NormedSpace.exp ((-Complex.I * (t : ℂ)) •
            qlift (R := R) en (SparseStateOverlap.matrixOperator (D.matrix x)))‖ ≤ ε ∧
    (t = 0 → ‖nrun (prims (R := R) D en x) (binaryCircuitSigned k b σ hσ s γ c0 t ε ζ) ∘L
        sysEmb (io (P := Reg (Fin k) R)) - sysEmb (io (P := Reg (Fin k) R)) ∘L
          NormedSpace.exp ((-Complex.I * (t : ℂ)) •
            qlift (R := R) en (SparseStateOverlap.matrixOperator (D.matrix x)))‖ = 0) ∧
    (fDeg (width (s : ℝ) γ) (time (s : ℝ) |t| γ) (moment γ) (ε / 2) : ℝ) ≤
      128 * (time (s : ℝ) |t| γ * moment γ + width (s : ℝ) γ * (1 + Real.log (6 / ε))) ∧
    TimeSchedule.steps (time (s : ℝ) |t| γ) (ε / 6) ≤ 2 ^ simM (time (s : ℝ) |t| γ) (ε / 2) ∧
    2 ^ simM (time (s : ℝ) |t| γ) (ε / 2) < 2 * TimeSchedule.steps (time (s : ℝ) |t| γ) (ε / 6) ∧
    2 * fDeg (width (s : ℝ) γ) (time (s : ℝ) |t| γ) (moment γ) (ε / 2) + 2 ≤
      2 ^ simR (width (s : ℝ) γ) (time (s : ℝ) |t| γ) (moment γ) (ε / 2) ∧
    2 ^ simR (width (s : ℝ) γ) (time (s : ℝ) |t| γ) (moment γ) (ε / 2) ≤
      4 * (fDeg (width (s : ℝ) γ) (time (s : ℝ) |t| γ) (moment γ) (ε / 2) + 1) := by
  obtain ⟨hvalid, hcalls, hgates, hcard, herr, hdeg, hm1, hm2, hr1, hr2⟩ :=
    binary_simulation_signed (R := R) D en σ hσ hs hrange hb c0 hc0 hdec x hH hrow hcol γ t ε ζ
      hγ hγ1 hε hε1 hζ hζ1 hζε
  by_cases ht0 : t = 0
  · have hc : binaryCircuitSigned k b σ hσ s γ c0 t ε ζ = [] := if_pos ht0
    rw [hc, if_pos ht0, nrun_nil, exp_zero_time t ht0]
    refine ⟨fun i hi => absurd hi List.not_mem_nil, fun p => ?_, le_rfl, hcard,
      identity_comp_error_le _ ε hε.le, fun _ => identity_comp_error_eq_zero _, hdeg, hm1, hm2,
      hr1, hr2⟩
    rw [if_pos ht0]
    rfl
  · have hc : binaryCircuitSigned k b σ hσ s γ c0 t ε ζ = binarySimSigned k b σ hσ s γ c0 t ε ζ :=
      if_neg ht0
    rw [hc, if_neg ht0]
    refine ⟨hvalid, fun p => ?_, hgates, hcard, herr, fun h => absurd h ht0, hdeg, hm1, hm2, hr1,
      hr2⟩
    rw [if_neg ht0]
    exact hcalls p

end Native

set_option maxHeartbeats 1000000 in
/-- **The budget of the binary construction for every real time, with the identity circuit at
`t = 0`** (Theorem `hs:thm:gates`, pre-synthesis form of `hs:eq:gate-binary`). For `s ≥ 1`, every
real `t`, `0 < ε ≤ 1/2` and `q = √s |t| + √(s |t| log(1/ε)) + log(1/ε)`, the rescaling `γ` of
`binary_simulation_budget_signed` (chosen from `s`, `|t|` and `ε` before the data, with its
bounds) satisfies: for all data, inputs and arithmetic accuracies as in the released budget, the
circuit `binaryCircuitSigned` makes `0` calls if `t = 0` and at most `55296 q` times `2` row, `2`
column and `1` value calls otherwise, uses `0` elementary gates if `t = 0` and at most
`200 (4608 q + 1) (G_C + (σ+1) + (k+1) + m + r + 1)` otherwise, and has full-output error at most
`ε` against `exp(-itĤ)`, exactly `0` at `t = 0`. -/
theorem binary_simulation_budget_signed_zero (s : ℕ) (hs1 : 1 ≤ s) (t ε : ℝ) (hε : 0 < ε)
    (hε2 : ε ≤ 1 / 2) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 1 ≤ γ * Real.sqrt s ∧
      (fDeg (width (s : ℝ) γ) (time (s : ℝ) |t| γ) (moment γ) (ε / 2) : ℝ) ≤
        4608 * ImprovedPrecisionBudget.shape s |t| (Real.log (1 / ε)) ∧
      time (s : ℝ) |t| γ ≤ Real.sqrt s * ImprovedPrecisionBudget.shape s |t| (Real.log (1 / ε)) ∧
      ((2 ^ simM (time (s : ℝ) |t| γ) (ε / 2) : ℕ) : ℝ) <
        2 * (2 + 4 * time (s : ℝ) |t| γ + Real.sqrt (6 * time (s : ℝ) |t| γ ^ 3 / ε)) ∧
      ((2 ^ simR (width (s : ℝ) γ) (time (s : ℝ) |t| γ) (moment γ) (ε / 2) : ℕ) : ℝ) ≤
        4 * (4608 * ImprovedPrecisionBudget.shape s |t| (Real.log (1 / ε)) + 1) ∧
      ∀ {X : Type u} {n : Type v} [Fintype n] [DecidableEq n] {k b : ℕ} {R : Type w}
        [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
        (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (σ : ℕ) (hσ : σ ≤ k),
        s = 2 ^ σ →
        (∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin σ → Bool, j = en (lowWord σ u)) →
        0 < b → ∀ c0 : ℝ, 0 < c0 → (∀ e z, D.decode e z = (c0 : ℂ) * gauss z) →
        ∀ x : X, (D.matrix x).IsHermitian → (∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ 1) →
        (∀ j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ 1) →
        ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 →
        221184 * ImprovedPrecisionBudget.shape s |t| (Real.log (1 / ε)) * ζ ≤ ε →
        (∀ p : Query → Bool, (nCallsN p (binaryCircuitSigned k b σ hσ s γ c0 t ε ζ) : ℝ) ≤
          (if t = 0 then 0 else
            55296 * ImprovedPrecisionBudget.shape s |t| (Real.log (1 / ε)) *
              (2 * (if p Query.rowLocation then 1 else 0) +
                2 * (if p Query.columnLocation then 1 else 0) +
                (if p Query.value then 1 else 0)))) ∧
        (nGatesN (binaryCircuitSigned k b σ hσ s γ c0 t ε ζ) : ℝ) ≤
          (if t = 0 then 0 else
            200 * (4608 * ImprovedPrecisionBudget.shape s |t| (Real.log (1 / ε)) + 1) *
              ((privGates (sparseOp k b (γ * Real.sqrt s * c0))
                  (binArith k b (γ * Real.sqrt s * c0) ζ) : ℝ) + (σ + 1) + (k + 1) +
                simM (time (s : ℝ) |t| γ) (ε / 2) +
                simR (width (s : ℝ) γ) (time (s : ℝ) |t| γ) (moment γ) (ε / 2) + 1)) ∧
        ‖nrun (prims (R := R) D en x) (binaryCircuitSigned k b σ hσ s γ c0 t ε ζ) ∘L
            sysEmb (io (P := Reg (Fin k) R)) - sysEmb (io (P := Reg (Fin k) R)) ∘L
              NormedSpace.exp ((-Complex.I * (t : ℂ)) •
                qlift (R := R) en (SparseStateOverlap.matrixOperator (D.matrix x)))‖ ≤ ε ∧
        (t = 0 → ‖nrun (prims (R := R) D en x) (binaryCircuitSigned k b σ hσ s γ c0 t ε ζ) ∘L
            sysEmb (io (P := Reg (Fin k) R)) - sysEmb (io (P := Reg (Fin k) R)) ∘L
              NormedSpace.exp ((-Complex.I * (t : ℂ)) •
                qlift (R := R) en (SparseStateOverlap.matrixOperator (D.matrix x)))‖ = 0) := by
  obtain ⟨γ, hγ, hγ1, hγs, hdeg, hτq, hm, hr, hall⟩ :=
    binary_simulation_budget_signed.{u, v, w} s hs1 t ε hε hε2
  refine ⟨γ, hγ, hγ1, hγs, hdeg, hτq, hm, hr, ?_⟩
  intro X n _ _ k b R _ _ _ D en σ hσ hs hrange hb c0 hc0 hdec x hH hrow hcol ζ hζ hζ1 hζε
  obtain ⟨hcalls, hgates, herr⟩ := hall (R := R) D en σ hσ hs hrange hb c0 hc0 hdec x hH hrow
    hcol ζ hζ hζ1 hζε
  by_cases ht0 : t = 0
  · have hc : binaryCircuitSigned k b σ hσ s γ c0 t ε ζ = [] := if_pos ht0
    rw [hc, nrun_nil, exp_zero_time t ht0]
    refine ⟨fun p => ?_, ?_, identity_comp_error_le _ ε hε.le,
      fun _ => identity_comp_error_eq_zero _⟩
    · rw [if_pos ht0]
      simp
    · rw [if_pos ht0]
      simp
  · have hc : binaryCircuitSigned k b σ hσ s γ c0 t ε ζ = binarySimSigned k b σ hσ s γ c0 t ε ζ :=
      if_neg ht0
    rw [hc]
    refine ⟨fun p => ?_, ?_, herr, fun h => absurd h ht0⟩
    · rw [if_neg ht0]
      exact hcalls p
    · rw [if_neg ht0]
      exact hgates

section Endpoints

variable {X n : Type*} [Fintype n] [DecidableEq n] {s k b : ℕ}
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
variable {Xa : Type*} [Fintype Xa] [DecidableEq Xa] {𝒢 : Set Kind} {L : ℝ → ℕ}

set_option maxHeartbeats 1000000 in
/-- **Theorem `hs:thm:gates` from binary sparse data over a finite gate set for every real time,
with the identity circuit at `t = 0`.** Under the hypotheses of `binary_simulation_synth_signed`,
the synthesis `synthBudget hS ε' (binaryCircuitSigned …)` consists of valid gates of `𝒢` and
primitive calls, makes `0` calls if `t = 0` and exactly `12 d` times `2` row, `2` column and `1`
value calls otherwise, uses `0` gates if `t = 0` and at most `N L(ε'/(N+1))` gates otherwise (`N`
the gate count of `binarySimSigned`, bounded as in the released theorem for `|t|`), has the
released qubit count (`|Xa|` synthesis ancillas included), and its full output is within
`ε + ε'` of `exp(-itĤ)`; at `t = 0` the error is exactly `0`. -/
theorem binary_simulation_synth_signed_zero (hS : Synthesis 𝒢 Xa L) (ε' : ℝ) (hε' : 0 < ε')
    (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (σ : ℕ)
    (hσ : σ ≤ k) (hs : s = 2 ^ σ)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin σ → Bool, j = en (lowWord σ u))
    (hb : 0 < b) (c0 : ℝ) (hc0 : 0 < c0) (hdec : ∀ e z, D.decode e z = (c0 : ℂ) * gauss z)
    (x : X) (hH : (D.matrix x).IsHermitian) (hrow : ∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ 1)
    (hcol : ∀ j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ 1) (γ t ε ζ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hζε : 48 * (fDeg (width (s : ℝ) γ) (time (s : ℝ) |t| γ) (moment γ) (ε / 2) : ℝ) * ζ ≤ ε) :
    (∀ i ∈ synthBudget hS ε' (binaryCircuitSigned k b σ hσ s γ c0 t ε ζ), i.Valid) ∧
    (∀ g, NInstr.gate g ∈ synthBudget hS ε' (binaryCircuitSigned k b σ hσ s γ c0 t ε ζ) →
      GateOf 𝒢 g) ∧
    (∀ p : Query → Bool,
      nCallsN p (synthBudget hS ε' (binaryCircuitSigned k b σ hσ s γ c0 t ε ζ)) =
        (if t = 0 then 0 else
          12 * fDeg (width (s : ℝ) γ) (time (s : ℝ) |t| γ) (moment γ) (ε / 2) *
            (2 * (if p Query.rowLocation then 1 else 0) +
              2 * (if p Query.columnLocation then 1 else 0) +
              (if p Query.value then 1 else 0)))) ∧
    nGatesN (synthBudget hS ε' (binaryCircuitSigned k b σ hσ s γ c0 t ε ζ)) ≤
      (if t = 0 then 0 else
        nGatesN (binarySimSigned k b σ hσ s γ c0 t ε ζ) *
          L (ε' / (nGatesN (binarySimSigned k b σ hσ s γ c0 t ε ζ) + 1))) ∧
    nGatesN (binarySimSigned k b σ hσ s γ c0 t ε ζ) ≤
      200 * (fDeg (width (s : ℝ) γ) (time (s : ℝ) |t| γ) (moment γ) (ε / 2) + 1) *
          (k + 1 + simM (time (s : ℝ) |t| γ) (ε / 2) +
            simR (width (s : ℝ) γ) (time (s : ℝ) |t| γ) (moment γ) (ε / 2) + 1) +
        84 * fDeg (width (s : ℝ) γ) (time (s : ℝ) |t| γ) (moment γ) (ε / 2) * (σ + 1) +
        6 * fDeg (width (s : ℝ) γ) (time (s : ℝ) |t| γ) (moment γ) (ε / 2) *
          (2 * (28 * k) + 2 * (binArith k b (γ * Real.sqrt s * c0) ζ).circ.length +
            (2 * (binArith k b (γ * Real.sqrt s * c0) ζ).bP +
              (binArith k b (γ * Real.sqrt s * c0) ζ).bT + 1)) ∧
    Fintype.card (HW (SimWire (k + 1) (width (s : ℝ) γ) (time (s : ℝ) |t| γ) (moment γ) (ε / 2))
        (Fin k) Empty (SZ k b) (binArith k b (γ * Real.sqrt s * c0) ζ).bT
        (binArith k b (γ * Real.sqrt s * c0) ζ).bP (binArith k b (γ * Real.sqrt s * c0) ζ).A ⊕
        Xa) =
      k + (2 * (k + 1) + 3 * simM (time (s : ℝ) |t| γ) (ε / 2) +
          6 * simR (width (s : ℝ) γ) (time (s : ℝ) |t| γ) (moment γ) (ε / 2) + 3) +
        (6 * k + 2 * b + (binArith k b (γ * Real.sqrt s * c0) ζ).bT +
          (binArith k b (γ * Real.sqrt s * c0) ζ).bP +
          (binArith k b (γ * Real.sqrt s * c0) ζ).A + 3) + Fintype.card Xa ∧
    ‖nrun (prims (R := R) D en x)
          (synthBudget hS ε' (binaryCircuitSigned k b σ hσ s γ c0 t ε ζ)) ∘L
        (cleanEmb (X := Xa) ∘L sysEmb (io (P := Reg (Fin k) R))) -
        (cleanEmb ∘L sysEmb (io (P := Reg (Fin k) R))) ∘L
          NormedSpace.exp ((-Complex.I * (t : ℂ)) •
            qlift (R := R) en (SparseStateOverlap.matrixOperator (D.matrix x)))‖ ≤ ε + ε' ∧
    (t = 0 →
      ‖nrun (prims (R := R) D en x)
          (synthBudget hS ε' (binaryCircuitSigned k b σ hσ s γ c0 t ε ζ)) ∘L
        (cleanEmb (X := Xa) ∘L sysEmb (io (P := Reg (Fin k) R))) -
        (cleanEmb ∘L sysEmb (io (P := Reg (Fin k) R))) ∘L
          NormedSpace.exp ((-Complex.I * (t : ℂ)) •
            qlift (R := R) en (SparseStateOverlap.matrixOperator (D.matrix x)))‖ = 0) := by
  obtain ⟨hv, hk, hcalls, hg, hgates, hcard, herr⟩ := binary_simulation_synth_signed (R := R) hS
    ε' hε' D en σ hσ hs hrange hb c0 hc0 hdec x hH hrow hcol γ t ε ζ hγ hγ1 hε hε1 hζ hζ1 hζε
  by_cases ht0 : t = 0
  · have hc : binaryCircuitSigned k b σ hσ s γ c0 t ε ζ = [] := if_pos ht0
    rw [hc, synthBudget_nil, if_pos ht0, nrun_nil, exp_zero_time t ht0]
    have hε0 : 0 ≤ ε + ε' := by linarith
    refine ⟨fun i hi => absurd hi List.not_mem_nil, fun g hg => absurd hg List.not_mem_nil,
      fun p => ?_, le_rfl, hgates, hcard, identity_comp_error_le _ _ hε0,
      fun _ => identity_comp_error_eq_zero _⟩
    rw [if_pos ht0]
    rfl
  · have hc : binaryCircuitSigned k b σ hσ s γ c0 t ε ζ = binarySimSigned k b σ hσ s γ c0 t ε ζ :=
      if_neg ht0
    rw [hc, if_neg ht0]
    refine ⟨hv, hk, fun p => ?_, hg, hgates, hcard, herr, fun h => absurd h ht0⟩
    rw [if_neg ht0]
    exact hcalls p

end Endpoints

set_option maxHeartbeats 1000000 in
/-- **The gate budget from binary sparse oracles over a finite gate set for every real time, with
the identity circuit at `t = 0`** (equation `hs:eq:gate-total`). The rescaling `γ` of
`binary_simulation_budget_synth_signed` (chosen from `s`, `|t|` and `ε` before the gate set, the
synthesis budget and the data, with its bounds) satisfies: for every gate set with
`L ζ ≤ c₁ log(1/ζ) + c₀`, every `0 < ε' ≤ 1` and all data as in the released budget, the
synthesis of `binaryCircuitSigned` consists of valid gates of `𝒢` and primitive calls, makes `0`
calls if `t = 0` and at most `55296 q` times `2` row, `2` column and `1` value calls otherwise,
uses `0` gates if `t = 0` and at most `G (c₁ log((G+1)/ε') + c₀)` otherwise, with the released
pre-synthesis budget `G` for `|t|`, and has full-output error at most `ε + ε'` against
`exp(-itĤ)`, exactly `0` at `t = 0`. -/
theorem binary_simulation_budget_synth_signed_zero (s : ℕ) (hs1 : 1 ≤ s) (t ε : ℝ) (hε : 0 < ε)
    (hε2 : ε ≤ 1 / 2) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 1 ≤ γ * Real.sqrt s ∧
      (fDeg (width (s : ℝ) γ) (time (s : ℝ) |t| γ) (moment γ) (ε / 2) : ℝ) ≤
        4608 * ImprovedPrecisionBudget.shape s |t| (Real.log (1 / ε)) ∧
      time (s : ℝ) |t| γ ≤ Real.sqrt s * ImprovedPrecisionBudget.shape s |t| (Real.log (1 / ε)) ∧
      ((2 ^ simM (time (s : ℝ) |t| γ) (ε / 2) : ℕ) : ℝ) <
        2 * (2 + 4 * time (s : ℝ) |t| γ + Real.sqrt (6 * time (s : ℝ) |t| γ ^ 3 / ε)) ∧
      ((2 ^ simR (width (s : ℝ) γ) (time (s : ℝ) |t| γ) (moment γ) (ε / 2) : ℕ) : ℝ) ≤
        4 * (4608 * ImprovedPrecisionBudget.shape s |t| (Real.log (1 / ε)) + 1) ∧
      ∀ {Xa : Type x} [Fintype Xa] [DecidableEq Xa] {𝒢 : Set Kind} {L : ℝ → ℕ}
        (hS : Synthesis 𝒢 Xa L) {c₀ c₁ : ℝ}, 0 ≤ c₀ → 0 ≤ c₁ →
        (∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 → (L ζ : ℝ) ≤ c₁ * Real.log (1 / ζ) + c₀) →
        ∀ ε' : ℝ, 0 < ε' → ε' ≤ 1 →
      ∀ {X : Type u} {n : Type v} [Fintype n] [DecidableEq n] {k b : ℕ} {R : Type w}
        [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
        (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (σ : ℕ) (hσ : σ ≤ k),
        s = 2 ^ σ →
        (∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin σ → Bool, j = en (lowWord σ u)) →
        0 < b → ∀ c0 : ℝ, 0 < c0 → (∀ e z, D.decode e z = (c0 : ℂ) * gauss z) →
        ∀ x : X, (D.matrix x).IsHermitian → (∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ 1) →
        (∀ j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ 1) →
        ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 →
        221184 * ImprovedPrecisionBudget.shape s |t| (Real.log (1 / ε)) * ζ ≤ ε →
        (∀ i ∈ synthBudget hS ε' (binaryCircuitSigned k b σ hσ s γ c0 t ε ζ), i.Valid) ∧
        (∀ g, NInstr.gate g ∈ synthBudget hS ε' (binaryCircuitSigned k b σ hσ s γ c0 t ε ζ) →
          GateOf 𝒢 g) ∧
        (∀ p : Query → Bool,
          (nCallsN p (synthBudget hS ε' (binaryCircuitSigned k b σ hσ s γ c0 t ε ζ)) : ℝ) ≤
            (if t = 0 then 0 else
              55296 * ImprovedPrecisionBudget.shape s |t| (Real.log (1 / ε)) *
                (2 * (if p Query.rowLocation then 1 else 0) +
                  2 * (if p Query.columnLocation then 1 else 0) +
                  (if p Query.value then 1 else 0)))) ∧
        (nGatesN (synthBudget hS ε' (binaryCircuitSigned k b σ hσ s γ c0 t ε ζ)) : ℝ) ≤
          (if t = 0 then 0 else
            200 * (4608 * ImprovedPrecisionBudget.shape s |t| (Real.log (1 / ε)) + 1) *
                ((privGates (sparseOp k b (γ * Real.sqrt s * c0))
                    (binArith k b (γ * Real.sqrt s * c0) ζ) : ℝ) + (σ + 1) + (k + 1) +
                  simM (time (s : ℝ) |t| γ) (ε / 2) +
                  simR (width (s : ℝ) γ) (time (s : ℝ) |t| γ) (moment γ) (ε / 2) + 1) *
              (c₁ * Real.log ((200 * (4608 * ImprovedPrecisionBudget.shape s |t|
                    (Real.log (1 / ε)) + 1) *
                ((privGates (sparseOp k b (γ * Real.sqrt s * c0))
                    (binArith k b (γ * Real.sqrt s * c0) ζ) : ℝ) + (σ + 1) + (k + 1) +
                  simM (time (s : ℝ) |t| γ) (ε / 2) +
                  simR (width (s : ℝ) γ) (time (s : ℝ) |t| γ) (moment γ) (ε / 2) + 1) + 1) /
                    ε') + c₀)) ∧
        ‖nrun (prims (R := R) D en x)
              (synthBudget hS ε' (binaryCircuitSigned k b σ hσ s γ c0 t ε ζ)) ∘L
            (cleanEmb (X := Xa) ∘L sysEmb (io (P := Reg (Fin k) R))) -
            (cleanEmb ∘L sysEmb (io (P := Reg (Fin k) R))) ∘L
              NormedSpace.exp ((-Complex.I * (t : ℂ)) •
                qlift (R := R) en (SparseStateOverlap.matrixOperator (D.matrix x)))‖ ≤
          ε + ε' ∧
        (t = 0 → ‖nrun (prims (R := R) D en x)
              (synthBudget hS ε' (binaryCircuitSigned k b σ hσ s γ c0 t ε ζ)) ∘L
            (cleanEmb (X := Xa) ∘L sysEmb (io (P := Reg (Fin k) R))) -
            (cleanEmb ∘L sysEmb (io (P := Reg (Fin k) R))) ∘L
              NormedSpace.exp ((-Complex.I * (t : ℂ)) •
                qlift (R := R) en (SparseStateOverlap.matrixOperator (D.matrix x)))‖ = 0) := by
  obtain ⟨γ, hγ, hγ1, hγs, hdeg, hτq, hm, hr, hall⟩ :=
    binary_simulation_budget_synth_signed.{u, v, w, x} s hs1 t ε hε hε2
  refine ⟨γ, hγ, hγ1, hγs, hdeg, hτq, hm, hr, ?_⟩
  intro Xa _ _ 𝒢 L hS c₀ c₁ hc₀ hc₁ hL ε' hε' hε'1 X n _ _ k b R _ _ _ D en σ hσ hs hrange hb c0
    hc0 hdec x hH hrow hcol ζ hζ hζ1 hζε
  obtain ⟨hv, hk, hcalls, hgates, herr⟩ := hall hS hc₀ hc₁ hL ε' hε' hε'1 (R := R) D en σ hσ hs
    hrange hb c0 hc0 hdec x hH hrow hcol ζ hζ hζ1 hζε
  by_cases ht0 : t = 0
  · have hc : binaryCircuitSigned k b σ hσ s γ c0 t ε ζ = [] := if_pos ht0
    rw [hc, synthBudget_nil, nrun_nil, exp_zero_time t ht0]
    have hε0 : 0 ≤ ε + ε' := by linarith
    refine ⟨fun i hi => absurd hi List.not_mem_nil, fun g hg => absurd hg List.not_mem_nil,
      fun p => ?_, ?_, identity_comp_error_le _ _ hε0, fun _ => identity_comp_error_eq_zero _⟩
    · rw [if_pos ht0]
      simp
    · rw [if_pos ht0]
      simp
  · have hc : binaryCircuitSigned k b σ hσ s γ c0 t ε ζ = binarySimSigned k b σ hσ s γ c0 t ε ζ :=
      if_neg ht0
    rw [hc]
    refine ⟨hv, hk, fun p => ?_, ?_, herr, fun h => absurd h ht0⟩
    · rw [if_neg ht0]
      exact hcalls p
    · rw [if_neg ht0]
      exact hgates

end

end SparseHamiltonian.GateSigned
