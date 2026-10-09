import GateEfficientSigned.Basic
import GateEfficientRemarks.Qubits

/-!
# Theorem `hs:thm:gates` from binary sparse data for every real time

Theorem `hs:thm:gates` assumes the hypotheses of Theorem `hs:thm:main`, for every real `t` with
`τ = η|t|`. The released binary-data endpoints (`GateBinary.binary_simulation`,
`GateBinary.binary_simulation_budget`, `GateBitBudget.binary_simulation_bits` and
`GateRemarks.binary_simulation_bits_qubits`) are stated for `τ ≥ 0`. This file states each of them
for every real `t`, with the circuit `binarySimSigned` (the released circuit for `|t|`, or its
literal inverse if `t < 0`):

* `binary_simulation_signed`: every conclusion of `GateBinary.binary_simulation` for `|t|`, with
  the full-output error against `exp(-itĤ)`;
* `binary_simulation_budget_signed`: the rescaling `γ` of `GateBinary.binary_simulation_budget`
  for `|t|`, chosen before the data, and its counts and error, with
  `q = √s |t| + √(s |t| log(1/ε)) + log(1/ε)`;
* `binary_simulation_bits_signed`: the same for `GateBitBudget.binary_simulation_bits` (gate
  counts in `𝔟_H = b_data + log₂(N+1) + log₂((q+1)/ε)`);
* `binary_simulation_bits_qubits_signed`: the same for
  `GateRemarks.binary_simulation_bits_qubits` (qubit count in `𝔟_H`).

The hypotheses are those of the released theorems for the time `|t|`; the counts, the qubit
counts and the degree and register bounds are the released ones for `|t|`.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000

namespace SparseHamiltonian.GateSigned

noncomputable section
open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
open SparseHamiltonian.GateBinary SparseHamiltonian.OracleCircuit CayleyClockInterface
open SparseHamiltonian.GateBitBudget SparseHamiltonian.GateRemarks
open SparseHamiltonian.GateCircuit.Sim (fDeg simM simR SimWire io)
open NativeSparseBlockEncoding (Data Query)
open scoped InnerProduct

universe u v w

section Native

variable {X n : Type*} [Fintype n] [DecidableEq n] {s k b : ℕ}
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

set_option maxHeartbeats 1000000 in
/-- **Native gate-efficient sparse Hamiltonian simulation from binary data for every real time**
(Theorem `hs:thm:gates` for binary sparse oracles, before finite-set synthesis). Under the
hypotheses of the released `GateBinary.binary_simulation` for the time `|t|` (binary sparse data
with `k`-bit indices, `s = 2^σ` slots on the lowest `σ ≤ k` bits, `b`-bit two's complement
components with decoder `c₀ (X + i Y)`, an input with a Hermitian matrix of row and column norms
at most one, `0 < γ ≤ 1`, `0 < ε ≤ 1`, `0 < ζ ≤ 1` and `48 d ζ ≤ ε`), for every real `t` the
circuit `binarySimSigned` consists of valid instructions, makes `12 d` times `2` row-location,
`2` column-location and `1` value calls, has at most
`200 (d+1)(k+1+m+r+1) + 84 d (σ+1) + 6 d (56 k + 2 |arith| + 2 bP + bT + 1)` elementary gates and
the released qubit count, and its full output on the system embedding is within `ε` of
`exp(-itĤ)`; `d`, `m`, `r` and their bounds are those of the released theorem for `|t|`. -/
theorem binary_simulation_signed (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (σ : ℕ)
    (hσ : σ ≤ k) (hs : s = 2 ^ σ)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin σ → Bool, j = en (lowWord σ u))
    (hb : 0 < b) (c0 : ℝ) (hc0 : 0 < c0) (hdec : ∀ e z, D.decode e z = (c0 : ℂ) * gauss z)
    (x : X) (hH : (D.matrix x).IsHermitian) (hrow : ∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ 1)
    (hcol : ∀ j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ 1) (γ t ε ζ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hζε : 48 * (fDeg (width (s : ℝ) γ) (time (s : ℝ) |t| γ) (moment γ) (ε / 2) : ℝ) * ζ ≤ ε) :
    (∀ i ∈ binarySimSigned k b σ hσ s γ c0 t ε ζ, i.Valid) ∧
    (∀ p : Query → Bool, nCallsN p (binarySimSigned k b σ hσ s γ c0 t ε ζ) =
      12 * fDeg (width (s : ℝ) γ) (time (s : ℝ) |t| γ) (moment γ) (ε / 2) *
        (2 * (if p Query.rowLocation then 1 else 0) +
          2 * (if p Query.columnLocation then 1 else 0) + (if p Query.value then 1 else 0))) ∧
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
        (binArith k b (γ * Real.sqrt s * c0) ζ).bP (binArith k b (γ * Real.sqrt s * c0) ζ).A) =
      k + (2 * (k + 1) + 3 * simM (time (s : ℝ) |t| γ) (ε / 2) +
          6 * simR (width (s : ℝ) γ) (time (s : ℝ) |t| γ) (moment γ) (ε / 2) + 3) +
        (6 * k + 2 * b + (binArith k b (γ * Real.sqrt s * c0) ζ).bT +
          (binArith k b (γ * Real.sqrt s * c0) ζ).bP +
          (binArith k b (γ * Real.sqrt s * c0) ζ).A + 3) ∧
    ‖nrun (prims (R := R) D en x) (binarySimSigned k b σ hσ s γ c0 t ε ζ) ∘L
        sysEmb (io (P := Reg (Fin k) R)) - sysEmb (io (P := Reg (Fin k) R)) ∘L
          NormedSpace.exp ((-Complex.I * (t : ℂ)) •
            qlift (R := R) en (SparseStateOverlap.matrixOperator (D.matrix x)))‖ ≤ ε ∧
    (fDeg (width (s : ℝ) γ) (time (s : ℝ) |t| γ) (moment γ) (ε / 2) : ℝ) ≤
      128 * (time (s : ℝ) |t| γ * moment γ + width (s : ℝ) γ * (1 + Real.log (6 / ε))) ∧
    TimeSchedule.steps (time (s : ℝ) |t| γ) (ε / 6) ≤ 2 ^ simM (time (s : ℝ) |t| γ) (ε / 2) ∧
    2 ^ simM (time (s : ℝ) |t| γ) (ε / 2) < 2 * TimeSchedule.steps (time (s : ℝ) |t| γ) (ε / 6) ∧
    2 * fDeg (width (s : ℝ) γ) (time (s : ℝ) |t| γ) (moment γ) (ε / 2) + 2 ≤
      2 ^ simR (width (s : ℝ) γ) (time (s : ℝ) |t| γ) (moment γ) (ε / 2) ∧
    2 ^ simR (width (s : ℝ) γ) (time (s : ℝ) |t| γ) (moment γ) (ε / 2) ≤
      4 * (fDeg (width (s : ℝ) γ) (time (s : ℝ) |t| γ) (moment γ) (ε / 2) + 1) := by
  obtain ⟨hvalid, hcalls, hgates, hcard, herr, hdeg, hm1, hm2, hr1, hr2⟩ :=
    binary_simulation (R := R) D en σ hσ hs hrange hb c0 hc0 hdec x hH hrow hcol γ |t| ε ζ hγ hγ1
      (abs_nonneg t) hε hε1 hζ hζ1 hζε
  refine ⟨valid_signed t _ hvalid, fun p => ?_, ?_, hcard,
    err_signed (prims (R := R) D en x) (prims_isUnitary D en x) _ hvalid _ _
      (qlift_matrixOperator_self en _ hH) t ε herr, hdeg, hm1, hm2, hr1, hr2⟩
  · rw [nCallsN_binarySimSigned]
    exact hcalls p
  · rw [nGatesN_binarySimSigned]
    exact hgates

end Native

set_option maxHeartbeats 1000000 in
/-- **The budget of the binary construction for every real time** (Theorem `hs:thm:gates`,
pre-synthesis form of equation `hs:eq:gate-binary`). For `s ≥ 1` slots, every real `t` and
`0 < ε ≤ 1/2`, put `q = √s |t| + √(s |t| log(1/ε)) + log(1/ε)`. There is one rescaling
`γ ∈ (0, 1]` with `γ √s ≥ 1`, chosen from `s`, `|t|` and `ε` before the data and the input, with
every bound that the released `GateBinary.binary_simulation_budget` states for `|t|` (filter degree
`d ≤ 4608 q`, rescaled time `τ' = √s |t|/γ ≤ √s q`, `2^m < 2 (2 + 4τ' + √(6τ'³/ε))`,
`2^r ≤ 4 (4608 q + 1)`), such that for all binary sparse data, inputs and arithmetic accuracies as
in the released budget (`221184 q ζ ≤ ε`), the circuit `binarySimSigned` makes at most `55296 q`
times `2` row-location, `2` column-location and `1` value calls, uses at most
`200 (4608 q + 1) (G_C + (σ + 1) + (k + 1) + m + r + 1)` elementary gates and has full-output
error at most `ε` against `exp(-itĤ)`. -/
theorem binary_simulation_budget_signed (s : ℕ) (hs1 : 1 ≤ s) (t ε : ℝ) (hε : 0 < ε)
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
        (∀ p : Query → Bool, (nCallsN p (binarySimSigned k b σ hσ s γ c0 t ε ζ) : ℝ) ≤
          55296 * ImprovedPrecisionBudget.shape s |t| (Real.log (1 / ε)) *
            (2 * (if p Query.rowLocation then 1 else 0) +
              2 * (if p Query.columnLocation then 1 else 0) +
              (if p Query.value then 1 else 0))) ∧
        (nGatesN (binarySimSigned k b σ hσ s γ c0 t ε ζ) : ℝ) ≤
          200 * (4608 * ImprovedPrecisionBudget.shape s |t| (Real.log (1 / ε)) + 1) *
            ((privGates (sparseOp k b (γ * Real.sqrt s * c0))
                (binArith k b (γ * Real.sqrt s * c0) ζ) : ℝ) + (σ + 1) + (k + 1) +
              simM (time (s : ℝ) |t| γ) (ε / 2) +
              simR (width (s : ℝ) γ) (time (s : ℝ) |t| γ) (moment γ) (ε / 2) + 1) ∧
        ‖nrun (prims (R := R) D en x) (binarySimSigned k b σ hσ s γ c0 t ε ζ) ∘L
            sysEmb (io (P := Reg (Fin k) R)) - sysEmb (io (P := Reg (Fin k) R)) ∘L
              NormedSpace.exp ((-Complex.I * (t : ℂ)) •
                qlift (R := R) en (SparseStateOverlap.matrixOperator (D.matrix x)))‖ ≤ ε := by
  obtain ⟨γ, hγ, hγ1, hγs, hdeg, hτq, hm, hr, hall⟩ :=
    binary_simulation_budget.{u, v, w} s hs1 |t| ε (abs_nonneg t) hε hε2
  refine ⟨γ, hγ, hγ1, hγs, hdeg, hτq, hm, hr, ?_⟩
  intro X n _ _ k b R _ _ _ D en σ hσ hs hrange hb c0 hc0 hdec x hH hrow hcol ζ hζ hζ1 hζε
  obtain ⟨hcalls, hgates, herr⟩ := hall (R := R) D en σ hσ hs hrange hb c0 hc0 hdec x hH hrow
    hcol ζ hζ hζ1 hζε
  have hζε' : 48 * (fDeg (width (s : ℝ) γ) (time (s : ℝ) |t| γ) (moment γ) (ε / 2) : ℝ) * ζ ≤
      ε := by
    nlinarith [hdeg, hζ]
  obtain ⟨hvalid, -⟩ := binary_simulation (R := R) D en σ hσ hs hrange hb c0 hc0 hdec x hH hrow
    hcol γ |t| ε ζ hγ hγ1 (abs_nonneg t) hε (by linarith) hζ hζ1 hζε'
  refine ⟨fun p => ?_, ?_, err_signed (prims (R := R) D en x) (prims_isUnitary D en x) _ hvalid
    _ _ (qlift_matrixOperator_self en _ hH) t ε herr⟩
  · rw [nCallsN_binarySimSigned]
    exact hcalls p
  · rw [nGatesN_binarySimSigned]
    exact hgates

set_option maxHeartbeats 1000000 in
/-- **Equation `hs:eq:gate-binary` for binary sparse data for every real time** (Theorem
`hs:thm:gates`, before finite-set synthesis). For `s ≥ 1` slots, every real `t` and
`0 < ε ≤ 1/2`, put `q = √s |t| + √(s |t| log(1/ε)) + log(1/ε)`. The rescaling `γ ∈ (0, 1]` of
`GateBitBudget.binary_simulation_bits` for `|t|` (chosen from `s`, `|t|` and `ε` before the data,
with its bounds) satisfies: for all binary sparse data with `s = 2^σ` slots, `k`-bit indices
(`N = 2^k`) and `b ≤ b_data` stored bits, every decoder scale `c₀ > 0` of bit length `b_data`,
every admissible input and every arithmetic accuracy `ε/(442368 q) ≤ ζ ≤ ε/(221184 q)`,
`0 < ζ ≤ 1`, the circuit `binarySimSigned` uses at most `10¹⁵ q (𝔟_H + 1)³` elementary gates,
`𝔟_H = bitH b_data (2^k) q ε`, the private operation uses at most `2·10⁹ (𝔟_H + 1)³` gates, the
circuit makes at most `55296 q` times `2` row, `2` column and `1` value calls, uses at most
`200 (4608 q + 1) (G_C + (σ+1) + (k+1) + m + r + 1)` gates and has full-output error at most `ε`
against `exp(-itĤ)`. -/
theorem binary_simulation_bits_signed (s : ℕ) (hs1 : 1 ≤ s) (t ε : ℝ) (hε : 0 < ε)
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
        ∀ bd : ℕ, b ≤ bd → HasBits bd c0 →
        ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 →
        221184 * ImprovedPrecisionBudget.shape s |t| (Real.log (1 / ε)) * ζ ≤ ε →
        ε ≤ 442368 * ImprovedPrecisionBudget.shape s |t| (Real.log (1 / ε)) * ζ →
        (nGatesN (binarySimSigned k b σ hσ s γ c0 t ε ζ) : ℝ) ≤
          10 ^ 15 * ImprovedPrecisionBudget.shape s |t| (Real.log (1 / ε)) *
            (bitH bd (2 ^ k) (ImprovedPrecisionBudget.shape s |t| (Real.log (1 / ε))) ε + 1) ^ 3 ∧
        (privGates (sparseOp k b (γ * Real.sqrt s * c0))
            (binArith k b (γ * Real.sqrt s * c0) ζ) : ℝ) ≤
          2 * 10 ^ 9 *
            (bitH bd (2 ^ k) (ImprovedPrecisionBudget.shape s |t| (Real.log (1 / ε))) ε + 1) ^ 3 ∧
        (∀ p : Query → Bool, (nCallsN p (binarySimSigned k b σ hσ s γ c0 t ε ζ) : ℝ) ≤
          55296 * ImprovedPrecisionBudget.shape s |t| (Real.log (1 / ε)) *
            (2 * (if p Query.rowLocation then 1 else 0) +
              2 * (if p Query.columnLocation then 1 else 0) +
              (if p Query.value then 1 else 0))) ∧
        (nGatesN (binarySimSigned k b σ hσ s γ c0 t ε ζ) : ℝ) ≤
          200 * (4608 * ImprovedPrecisionBudget.shape s |t| (Real.log (1 / ε)) + 1) *
            ((privGates (sparseOp k b (γ * Real.sqrt s * c0))
                (binArith k b (γ * Real.sqrt s * c0) ζ) : ℝ) + (σ + 1) + (k + 1) +
              simM (time (s : ℝ) |t| γ) (ε / 2) +
              simR (width (s : ℝ) γ) (time (s : ℝ) |t| γ) (moment γ) (ε / 2) + 1) ∧
        ‖nrun (prims (R := R) D en x) (binarySimSigned k b σ hσ s γ c0 t ε ζ) ∘L
            sysEmb (io (P := Reg (Fin k) R)) - sysEmb (io (P := Reg (Fin k) R)) ∘L
              NormedSpace.exp ((-Complex.I * (t : ℂ)) •
                qlift (R := R) en (SparseStateOverlap.matrixOperator (D.matrix x)))‖ ≤ ε := by
  obtain ⟨γ, hγ, hγ1, hγs, hdeg, hτq, hm, hr, hall⟩ :=
    binary_simulation_bits.{u, v, w} s hs1 |t| ε (abs_nonneg t) hε hε2
  refine ⟨γ, hγ, hγ1, hγs, hdeg, hτq, hm, hr, ?_⟩
  intro X n _ _ k b R _ _ _ D en σ hσ hs hrange hb c0 hc0 hdec x hH hrow hcol bd hbd hbits ζ hζ
    hζ1 hζε hζlo
  obtain ⟨hG, hpriv, hcalls, hgates, herr⟩ := hall (R := R) D en σ hσ hs hrange hb c0 hc0 hdec x
    hH hrow hcol bd hbd hbits ζ hζ hζ1 hζε hζlo
  have hζε' : 48 * (fDeg (width (s : ℝ) γ) (time (s : ℝ) |t| γ) (moment γ) (ε / 2) : ℝ) * ζ ≤
      ε := by
    nlinarith [hdeg, hζ]
  obtain ⟨hvalid, -⟩ := binary_simulation (R := R) D en σ hσ hs hrange hb c0 hc0 hdec x hH hrow
    hcol γ |t| ε ζ hγ hγ1 (abs_nonneg t) hε (by linarith) hζ hζ1 hζε'
  refine ⟨?_, hpriv, fun p => ?_, ?_, err_signed (prims (R := R) D en x) (prims_isUnitary D en x)
    _ hvalid _ _ (qlift_matrixOperator_self en _ hH) t ε herr⟩
  · rw [nGatesN_binarySimSigned]
    exact hG
  · rw [nCallsN_binarySimSigned]
    exact hcalls p
  · rw [nGatesN_binarySimSigned]
    exact hgates

set_option maxHeartbeats 1000000 in
/-- **The qubits and gates of `hs:thm:gates` for binary sparse data in the bit lengths, for every
real time** (equations `hs:eq:gate-total` and `hs:eq:gate-binary`, before finite-set synthesis).
For `s ≥ 1` slots, every real `t`, `0 < ε ≤ 1/2` and `q = √s |t| + √(s |t| log(1/ε)) + log(1/ε)`,
the rescaling `γ` of `GateRemarks.binary_simulation_bits_qubits` for `|t|` (chosen before the
data, with its bounds) satisfies: for all data, inputs and accuracies as in
`binary_simulation_bits_signed`, the circuit `binarySimSigned` uses at most `10¹⁵ q (𝔟_H + 1)³`
elementary gates on at most `4·10⁶ (𝔟_H + 1)³` qubits, `𝔟_H = bitH b_data (2^k) q ε`; its register
has exactly `k + (2(k+1) + 3m + 6r + 3) + (6k + 2b + bT + bP + A + 3)` qubits; and every other
conclusion of `binary_simulation_bits_signed` holds (the private operation has at most
`2·10⁹ (𝔟_H + 1)³` gates, at most `55296 q` times `2` row, `2` column and `1` value calls, the
released gate count `200 (4608 q + 1) (G_C + (σ+1) + (k+1) + m + r + 1)`, full-output error at
most `ε` against `exp(-itĤ)`). -/
theorem binary_simulation_bits_qubits_signed (s : ℕ) (hs1 : 1 ≤ s) (t ε : ℝ) (hε : 0 < ε)
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
        ∀ bd : ℕ, b ≤ bd → HasBits bd c0 →
        ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 →
        221184 * ImprovedPrecisionBudget.shape s |t| (Real.log (1 / ε)) * ζ ≤ ε →
        ε ≤ 442368 * ImprovedPrecisionBudget.shape s |t| (Real.log (1 / ε)) * ζ →
        (nGatesN (binarySimSigned k b σ hσ s γ c0 t ε ζ) : ℝ) ≤
          10 ^ 15 * ImprovedPrecisionBudget.shape s |t| (Real.log (1 / ε)) *
            (bitH bd (2 ^ k) (ImprovedPrecisionBudget.shape s |t| (Real.log (1 / ε))) ε + 1) ^ 3 ∧
        (Fintype.card (HW (SimWire (k + 1) (width (s : ℝ) γ) (time (s : ℝ) |t| γ) (moment γ)
            (ε / 2)) (Fin k) Empty (SZ k b) (binArith k b (γ * Real.sqrt s * c0) ζ).bT
            (binArith k b (γ * Real.sqrt s * c0) ζ).bP
            (binArith k b (γ * Real.sqrt s * c0) ζ).A) : ℝ) ≤
          4 * 10 ^ 6 *
            (bitH bd (2 ^ k) (ImprovedPrecisionBudget.shape s |t| (Real.log (1 / ε))) ε + 1) ^ 3 ∧
        Fintype.card (HW (SimWire (k + 1) (width (s : ℝ) γ) (time (s : ℝ) |t| γ) (moment γ)
            (ε / 2)) (Fin k) Empty (SZ k b) (binArith k b (γ * Real.sqrt s * c0) ζ).bT
            (binArith k b (γ * Real.sqrt s * c0) ζ).bP
            (binArith k b (γ * Real.sqrt s * c0) ζ).A) =
          k + (2 * (k + 1) + 3 * simM (time (s : ℝ) |t| γ) (ε / 2) +
              6 * simR (width (s : ℝ) γ) (time (s : ℝ) |t| γ) (moment γ) (ε / 2) + 3) +
            (6 * k + 2 * b + (binArith k b (γ * Real.sqrt s * c0) ζ).bT +
              (binArith k b (γ * Real.sqrt s * c0) ζ).bP +
              (binArith k b (γ * Real.sqrt s * c0) ζ).A + 3) ∧
        (privGates (sparseOp k b (γ * Real.sqrt s * c0))
            (binArith k b (γ * Real.sqrt s * c0) ζ) : ℝ) ≤
          2 * 10 ^ 9 *
            (bitH bd (2 ^ k) (ImprovedPrecisionBudget.shape s |t| (Real.log (1 / ε))) ε + 1) ^ 3 ∧
        (∀ p : Query → Bool, (nCallsN p (binarySimSigned k b σ hσ s γ c0 t ε ζ) : ℝ) ≤
          55296 * ImprovedPrecisionBudget.shape s |t| (Real.log (1 / ε)) *
            (2 * (if p Query.rowLocation then 1 else 0) +
              2 * (if p Query.columnLocation then 1 else 0) +
              (if p Query.value then 1 else 0))) ∧
        (nGatesN (binarySimSigned k b σ hσ s γ c0 t ε ζ) : ℝ) ≤
          200 * (4608 * ImprovedPrecisionBudget.shape s |t| (Real.log (1 / ε)) + 1) *
            ((privGates (sparseOp k b (γ * Real.sqrt s * c0))
                (binArith k b (γ * Real.sqrt s * c0) ζ) : ℝ) + (σ + 1) + (k + 1) +
              simM (time (s : ℝ) |t| γ) (ε / 2) +
              simR (width (s : ℝ) γ) (time (s : ℝ) |t| γ) (moment γ) (ε / 2) + 1) ∧
        ‖nrun (prims (R := R) D en x) (binarySimSigned k b σ hσ s γ c0 t ε ζ) ∘L
            sysEmb (io (P := Reg (Fin k) R)) - sysEmb (io (P := Reg (Fin k) R)) ∘L
              NormedSpace.exp ((-Complex.I * (t : ℂ)) •
                qlift (R := R) en (SparseStateOverlap.matrixOperator (D.matrix x)))‖ ≤ ε := by
  obtain ⟨γ, hγ, hγ1, hγs, hdeg, hτq, hm, hr, hall⟩ :=
    binary_simulation_bits_qubits.{u, v, w} s hs1 |t| ε (abs_nonneg t) hε hε2
  refine ⟨γ, hγ, hγ1, hγs, hdeg, hτq, hm, hr, ?_⟩
  intro X n _ _ k b R _ _ _ D en σ hσ hs hrange hb c0 hc0 hdec x hH hrow hcol bd hbd hbits ζ hζ
    hζ1 hζε hζlo
  obtain ⟨hG, hq, hcard, hpriv, hcalls, hgates, herr⟩ := hall (R := R) D en σ hσ hs hrange hb c0
    hc0 hdec x hH hrow hcol bd hbd hbits ζ hζ hζ1 hζε hζlo
  have hζε' : 48 * (fDeg (width (s : ℝ) γ) (time (s : ℝ) |t| γ) (moment γ) (ε / 2) : ℝ) * ζ ≤
      ε := by
    nlinarith [hdeg, hζ]
  obtain ⟨hvalid, -⟩ := binary_simulation (R := R) D en σ hσ hs hrange hb c0 hc0 hdec x hH hrow
    hcol γ |t| ε ζ hγ hγ1 (abs_nonneg t) hε (by linarith) hζ hζ1 hζε'
  refine ⟨?_, hq, hcard, hpriv, fun p => ?_, ?_, err_signed (prims (R := R) D en x)
    (prims_isUnitary D en x) _ hvalid _ _ (qlift_matrixOperator_self en _ hH) t ε herr⟩
  · rw [nGatesN_binarySimSigned]
    exact hG
  · rw [nCallsN_binarySimSigned]
    exact hcalls p
  · rw [nGatesN_binarySimSigned]
    exact hgates

end

end SparseHamiltonian.GateSigned
