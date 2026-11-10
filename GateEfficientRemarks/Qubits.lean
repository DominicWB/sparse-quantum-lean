import GateEfficientRemarks.QubitWords
import GateEfficientBitBudget.HamiltonianBudget
import GateEfficientBitBudget.SynthHamiltonian

/-!
# The auxiliary qubits of `hs:eq:gate-total` in the bit-length parameter

Theorem `hs:thm:gates` of the accompanying paper counts, besides the gates of
`hs:eq:gate-total`, `O(A_C(ξ) + a + m_slot + r_reuse)` auxiliary qubits, and for binary or
fixed-point data of bit lengths at most `b_data` states the gate count
`Q_base poly(b_data, log(N+1), log((Q_base+1)/ε))`
(equation `hs:eq:gate-binary`). The released library `GateEfficientBitBudget` proves the gate
count in this form (`GateBitBudget.binary_simulation_bits` and its time-dependent and
finite-gate-set forms) and lists the qubit count in `𝔟` as not formalised. This file adds it,
with a rescaling `γ` that has every property the released endpoint states for its rescaling,
and the same circuits, so that gate and qubit bounds hold together:

* `binary_simulation_bits_qubits`: every conclusion of `GateBitBudget.binary_simulation_bits`,
  the register size of `binarySim` (the released formula of `GateBinary.binary_simulation`) and
  the bound `4·10⁶ (𝔟_H + 1)³` on it, `𝔟_H = bitH b_data (2^k) q ε`;
* `binary_time_simulation_bits_qubits`: the same for `binaryTimeSim` on `M = 2^m` time slots,
  with `4·10⁶ (𝔟_H + log₂(M+1) + 1)³`;
* `binary_simulation_budget_synth_bits_qubits`, `binary_time_simulation_budget_synth_bits_qubits`:
  the same after finite-gate-set synthesis, with `|Xa|` synthesis ancillas added.

The polynomial is cubic, as the gate polynomial of the released library: the work wires of the
released CORDIC arithmetic are `1 + 2w + (6(n+1)+1) w ≥ 12 n³` with `n` steps and width
`w = 2n² + …`, and `n ≥ log₂(1/ε)` in the accuracy window of the endpoints (`cordic_A_ge`,
`binArith_A_ge`), so no quadratic bound holds for these circuits. The register formulas hold for
all parameters (`card_binary_register`, `card_binary_registerT`); the rescaling is existential,
as in the released endpoints, and `binary_register_le`, `binary_registerT_le` assume only
properties that the released endpoints state for their rescaling.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateRemarks

noncomputable section
open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
open SparseHamiltonian.GateBinary SparseHamiltonian.OracleCircuit CayleyClockInterface
open SparseHamiltonian.GateBitBudget SparseHamiltonian.GateSynth
open SparseHamiltonian.GateCircuit.Sim (fDeg simM simR SimWire Wire io)
open NativeSparseBlockEncoding (Data Query)
open scoped InnerProduct

universe u v w x

/-- **The qubits and gates of `hs:thm:gates` for binary sparse data in the bit lengths**
(equations `hs:eq:gate-total` and `hs:eq:gate-binary`, before finite-set synthesis). For `s ≥ 1`
slots, `τ ≥ 0`, `0 < ε ≤ 1/2` and `q = √s τ + √(s τ log(1/ε)) + log(1/ε)`, there is a rescaling
`γ ∈ (0, 1]`, chosen from `s`, `τ`, `ε` before the data, with every property that
`GateBitBudget.binary_simulation_bits` states (`γ √s ≥ 1`, `d ≤ 4608 q`, `τ' ≤ √s q` and the
bounds on the simulator words), such that: for all binary sparse data with `s = 2^σ` slots,
`k`-bit indices (`N = 2^k`) and `b ≤ b_data` stored bits, every decoder scale `c₀ > 0` of bit
length `b_data`, every admissible input and every arithmetic accuracy
`ε/(442368 q) ≤ ζ ≤ ε/(221184 q)`, the circuit
`binarySim` uses at most `10¹⁵ q (𝔟_H + 1)³` elementary gates on at most `4·10⁶ (𝔟_H + 1)³`
qubits, `𝔟_H = bitH b_data (2^k) q ε`; its register has exactly
`k + (2(k+1) + 3m + 6r + 3) + (6k + 2b + bT + bP + A + 3)` qubits; and every other conclusion of
`binary_simulation_bits` holds (the private operation has at most `2·10⁹ (𝔟_H + 1)³` gates, at
most `55296 q` times `2` row, `2` column and `1` value calls, the released gate count
`200 (4608 q + 1) (G_C + (σ+1) + (k+1) + m + r + 1)`, full-output error at most `ε`). -/
theorem binary_simulation_bits_qubits (s : ℕ) (hs1 : 1 ≤ s) (τ ε : ℝ) (hτ : 0 ≤ τ)
    (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 1 ≤ γ * Real.sqrt s ∧
      (fDeg (width (s : ℝ) γ) (time (s : ℝ) τ γ) (moment γ) (ε / 2) : ℝ) ≤
        4608 * ImprovedPrecisionBudget.shape s τ (Real.log (1 / ε)) ∧
      time (s : ℝ) τ γ ≤ Real.sqrt s * ImprovedPrecisionBudget.shape s τ (Real.log (1 / ε)) ∧
      ((2 ^ simM (time (s : ℝ) τ γ) (ε / 2) : ℕ) : ℝ) <
        2 * (2 + 4 * time (s : ℝ) τ γ + Real.sqrt (6 * time (s : ℝ) τ γ ^ 3 / ε)) ∧
      ((2 ^ simR (width (s : ℝ) γ) (time (s : ℝ) τ γ) (moment γ) (ε / 2) : ℕ) : ℝ) ≤
        4 * (4608 * ImprovedPrecisionBudget.shape s τ (Real.log (1 / ε)) + 1) ∧
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
        221184 * ImprovedPrecisionBudget.shape s τ (Real.log (1 / ε)) * ζ ≤ ε →
        ε ≤ 442368 * ImprovedPrecisionBudget.shape s τ (Real.log (1 / ε)) * ζ →
        (nGatesN (binarySim k b σ hσ s γ c0 τ ε ζ) : ℝ) ≤
          10 ^ 15 * ImprovedPrecisionBudget.shape s τ (Real.log (1 / ε)) *
            (bitH bd (2 ^ k) (ImprovedPrecisionBudget.shape s τ (Real.log (1 / ε))) ε + 1) ^ 3 ∧
        (Fintype.card (HW (SimWire (k + 1) (width (s : ℝ) γ) (time (s : ℝ) τ γ) (moment γ)
            (ε / 2)) (Fin k) Empty (SZ k b) (binArith k b (γ * Real.sqrt s * c0) ζ).bT
            (binArith k b (γ * Real.sqrt s * c0) ζ).bP
            (binArith k b (γ * Real.sqrt s * c0) ζ).A) : ℝ) ≤
          4 * 10 ^ 6 *
            (bitH bd (2 ^ k) (ImprovedPrecisionBudget.shape s τ (Real.log (1 / ε))) ε + 1) ^ 3 ∧
        Fintype.card (HW (SimWire (k + 1) (width (s : ℝ) γ) (time (s : ℝ) τ γ) (moment γ)
            (ε / 2)) (Fin k) Empty (SZ k b) (binArith k b (γ * Real.sqrt s * c0) ζ).bT
            (binArith k b (γ * Real.sqrt s * c0) ζ).bP
            (binArith k b (γ * Real.sqrt s * c0) ζ).A) =
          k + (2 * (k + 1) + 3 * simM (time (s : ℝ) τ γ) (ε / 2) +
              6 * simR (width (s : ℝ) γ) (time (s : ℝ) τ γ) (moment γ) (ε / 2) + 3) +
            (6 * k + 2 * b + (binArith k b (γ * Real.sqrt s * c0) ζ).bT +
              (binArith k b (γ * Real.sqrt s * c0) ζ).bP +
              (binArith k b (γ * Real.sqrt s * c0) ζ).A + 3) ∧
        (privGates (sparseOp k b (γ * Real.sqrt s * c0))
            (binArith k b (γ * Real.sqrt s * c0) ζ) : ℝ) ≤
          2 * 10 ^ 9 *
            (bitH bd (2 ^ k) (ImprovedPrecisionBudget.shape s τ (Real.log (1 / ε))) ε + 1) ^ 3 ∧
        (∀ p : Query → Bool, (nCallsN p (binarySim k b σ hσ s γ c0 τ ε ζ) : ℝ) ≤
          55296 * ImprovedPrecisionBudget.shape s τ (Real.log (1 / ε)) *
            (2 * (if p Query.rowLocation then 1 else 0) +
              2 * (if p Query.columnLocation then 1 else 0) +
              (if p Query.value then 1 else 0))) ∧
        (nGatesN (binarySim k b σ hσ s γ c0 τ ε ζ) : ℝ) ≤
          200 * (4608 * ImprovedPrecisionBudget.shape s τ (Real.log (1 / ε)) + 1) *
            ((privGates (sparseOp k b (γ * Real.sqrt s * c0))
                (binArith k b (γ * Real.sqrt s * c0) ζ) : ℝ) + (σ + 1) + (k + 1) +
              simM (time (s : ℝ) τ γ) (ε / 2) +
              simR (width (s : ℝ) γ) (time (s : ℝ) τ γ) (moment γ) (ε / 2) + 1) ∧
        ‖nrun (prims (R := R) D en x) (binarySim k b σ hσ s γ c0 τ ε ζ) ∘L
            sysEmb (io (P := Reg (Fin k) R)) - sysEmb (io (P := Reg (Fin k) R)) ∘L
              NormedSpace.exp ((-Complex.I * (τ : ℂ)) •
                qlift (R := R) en (SparseStateOverlap.matrixOperator (D.matrix x)))‖ ≤ ε := by
  obtain ⟨γ, hγ, hγ1, hγs, hdeg, hτq, hm, hr, hall⟩ :=
    binary_simulation_bits.{u, v, w} s hs1 τ ε hτ hε hε2
  refine ⟨γ, hγ, hγ1, hγs, hdeg, hτq, hm, hr, ?_⟩
  intro X n _ _ k b R _ _ _ D en σ hσ hs hrange hb c0 hc0 hdec x hH hrow hcol bd hbd hbits ζ hζ
    hζ1 hζε hζlo
  obtain ⟨hG, hpriv, hcalls, hgates, herr⟩ := hall (R := R) D en σ hσ hs hrange hb c0 hc0 hdec x
    hH hrow hcol bd hbd hbits ζ hζ hζ1 hζε hζlo
  have hcard := card_binary_register k b (binArith k b (γ * Real.sqrt s * c0) ζ).bT
    (binArith k b (γ * Real.sqrt s * c0) ζ).bP (binArith k b (γ * Real.sqrt s * c0) ζ).A
    (width (s : ℝ) γ) (time (s : ℝ) τ γ) (moment γ) (ε / 2)
  have hq := binary_register_le s k b σ bd (c0 := c0) hs hσ hbd hγ1 hγs hτ hε hε2 hbits hc0 hζ
    hζlo hτq hm hr
  refine ⟨hG, ?_, hcard, hpriv, hcalls, hgates, herr⟩
  rw [hcard]
  exact hq

/-- **The qubits and gates of the time-dependent gate-level simulation (Theorem `hs:thm:time` with
the circuit of `hs:thm:gates`) for time-indexed binary sparse data in the bit lengths** (before
finite-set synthesis). For `s ≥ 1`, `t ≥ 0`, `0 < ε ≤ 1` and
`q = √s t + √(s t log(2/ε)) + log(2/ε)`, there is a rescaling `γ ∈ (0, 1]`, chosen before the data,
the input, the path and the mesh, with every property that
`GateBitBudget.binary_time_simulation_bits` states (`γ √s ≥ 1` and `d ≤ 4608 q`), such that: for all
data, paths, meshes and accuracies as in `binary_time_simulation_bits` (`M = 2^m` time slots,
`b ≤ b_data`, `c₀` of bit length `b_data`, `ε/(442368 q) ≤ ζ ≤ ε/(221184 q)`), the circuit
`binaryTimeSim` uses at most `10¹⁵ q (𝔟_H + log₂(M+1) + 1)³` elementary gates on at most
`4·10⁶ (𝔟_H + log₂(M+1) + 1)³` qubits, `𝔟_H = bitH b_data (2^k) q ε`; its register has exactly
`k + (2(k+1) + 3m + 6r + 3) + (6k + 2b + bT + bP + A + 3)` qubits; and every other conclusion of
`binary_time_simulation_bits` holds. -/
theorem binary_time_simulation_bits_qubits (s : ℕ) (hs1 : 1 ≤ s) (t ε : ℝ) (ht : 0 ≤ t)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 1 ≤ γ * Real.sqrt s ∧
      (fDeg (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4) : ℝ) ≤
        4608 * ImprovedPrecisionBudget.shape s t (Real.log (2 / ε)) ∧
      ∀ {X : Type u} {n : Type v} [Fintype n] [DecidableEq n] {k b m : ℕ} {R : Type w}
        [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
        (D : Data (X × Fin (2 ^ m)) n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (σ : ℕ)
        (hσ : σ ≤ k), s = 2 ^ σ →
        (∀ j : n, (∃ q, D.slot q = j) ↔ ∃ u : Fin σ → Bool, j = en (lowWord σ u)) →
        0 < b → ∀ c0 : ℝ, 0 < c0 → (∀ e z, D.decode e z = (c0 : ℂ) * gauss z) →
        ∀ x : X, (∀ r, (D.matrix (x, r)).IsHermitian) →
        (∀ r i, ∑ j, ‖D.matrix (x, r) i j‖ ^ 2 ≤ 1) →
        (∀ r j, ∑ i, ‖D.matrix (x, r) i j‖ ^ 2 ≤ 1) →
        ∀ (H : ℝ → Matrix n n ℂ) (β δ : ℝ), 0 ≤ β →
        (∀ u ∈ Set.Icc 0 t, (H u).IsHermitian) →
        (∀ u ∈ Set.Icc 0 t, ∀ v ∈ Set.Icc 0 t,
          ‖SparseStateOverlap.matrixOperator (H u) - SparseStateOverlap.matrixOperator (H v)‖ ≤
            β * |u - v|) →
        (∀ r : Fin (2 ^ m),
          ‖SparseStateOverlap.matrixOperator (H (((r : ℕ) : ℝ) * t / 2 ^ m)) -
            SparseStateOverlap.matrixOperator (D.matrix (x, r))‖ ≤ δ) →
        8 * t * δ ≤ ε →
        TimeSchedule.steps (time (s : ℝ) t γ) (ε / 12) ≤ 2 ^ m →
        8 * β * t ^ 2 ≤ ε * 2 ^ m →
        ∀ bd : ℕ, b ≤ bd → HasBits bd c0 →
        ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 →
        221184 * ImprovedPrecisionBudget.shape s t (Real.log (2 / ε)) * ζ ≤ ε →
        ε ≤ 442368 * ImprovedPrecisionBudget.shape s t (Real.log (2 / ε)) * ζ →
        (nGatesN (binaryTimeSim k b m σ hσ s γ c0 t ε ζ) : ℝ) ≤
          10 ^ 15 * ImprovedPrecisionBudget.shape s t (Real.log (2 / ε)) *
            (bitH bd (2 ^ k) (ImprovedPrecisionBudget.shape s t (Real.log (2 / ε))) ε +
              Real.logb 2 (((2 ^ m : ℕ) : ℝ) + 1) + 1) ^ 3 ∧
        (Fintype.card (HW (Wire (k + 1) m
            (simR (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4))
            (k + 1 + m + 2 * simR (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4)))
            (Fin k) Empty (SZ k b) (binArithT k b m (γ * Real.sqrt s * c0) ζ).bT
            (binArithT k b m (γ * Real.sqrt s * c0) ζ).bP
            (binArithT k b m (γ * Real.sqrt s * c0) ζ).A) : ℝ) ≤
          4 * 10 ^ 6 *
            (bitH bd (2 ^ k) (ImprovedPrecisionBudget.shape s t (Real.log (2 / ε))) ε +
              Real.logb 2 (((2 ^ m : ℕ) : ℝ) + 1) + 1) ^ 3 ∧
        Fintype.card (HW (Wire (k + 1) m
            (simR (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4))
            (k + 1 + m + 2 * simR (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4)))
            (Fin k) Empty (SZ k b) (binArithT k b m (γ * Real.sqrt s * c0) ζ).bT
            (binArithT k b m (γ * Real.sqrt s * c0) ζ).bP
            (binArithT k b m (γ * Real.sqrt s * c0) ζ).A) =
          k + (2 * (k + 1) + 3 * m +
              6 * simR (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4) + 3) +
            (6 * k + 2 * b + (binArithT k b m (γ * Real.sqrt s * c0) ζ).bT +
              (binArithT k b m (γ * Real.sqrt s * c0) ζ).bP +
              (binArithT k b m (γ * Real.sqrt s * c0) ζ).A + 3) ∧
        (privGates (sparseOpT k b m (γ * Real.sqrt s * c0))
            (binArithT k b m (γ * Real.sqrt s * c0) ζ) : ℝ) ≤
          2 * 10 ^ 9 *
            (bitH bd (2 ^ k) (ImprovedPrecisionBudget.shape s t (Real.log (2 / ε))) ε + 1) ^ 3 ∧
        (∀ p : Query → Bool, (nCallsN p (binaryTimeSim k b m σ hσ s γ c0 t ε ζ) : ℝ) ≤
          55296 * ImprovedPrecisionBudget.shape s t (Real.log (2 / ε)) *
            (2 * (if p Query.rowLocation then 1 else 0) +
              2 * (if p Query.columnLocation then 1 else 0) +
              (if p Query.value then 1 else 0))) ∧
        (nGatesN (binaryTimeSim k b m σ hσ s γ c0 t ε ζ) : ℝ) ≤
          200 * (4608 * ImprovedPrecisionBudget.shape s t (Real.log (2 / ε)) + 1) *
            ((privGates (sparseOpT k b m (γ * Real.sqrt s * c0))
                (binArithT k b m (γ * Real.sqrt s * c0) ζ) : ℝ) + (σ + 1) + (k + 1) + m +
              simR (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4) + 1) ∧
        ((2 ^ simR (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4) : ℕ) : ℝ) ≤
          4 * (4608 * ImprovedPrecisionBudget.shape s t (Real.log (2 / ε)) + 1) ∧
        (∃ U : ℝ → Reg (Fin k) R →L[ℂ] Reg (Fin k) R, U 0 = 1 ∧
          TimeDependent.SolvesOn
            (fun u => qlift (R := R) en (SparseStateOverlap.matrixOperator (H u))) U 0 t) ∧
        ∀ U : ℝ → Reg (Fin k) R →L[ℂ] Reg (Fin k) R, U 0 = 1 →
          TimeDependent.SolvesOn
            (fun u => qlift (R := R) en (SparseStateOverlap.matrixOperator (H u))) U 0 t →
          ‖nrun (primsT (R := R) D en x) (binaryTimeSim k b m σ hσ s γ c0 t ε ζ) ∘L
              sysEmb (io (P := Reg (Fin k) R)) - sysEmb (io (P := Reg (Fin k) R)) ∘L U t‖ ≤
            ε := by
  obtain ⟨γ, hγ, hγ1, hγs, hdeg, hall⟩ :=
    binary_time_simulation_bits.{u, v, w} s hs1 t ε ht hε hε1
  refine ⟨γ, hγ, hγ1, hγs, hdeg, ?_⟩
  intro X n _ _ k b m R _ _ _ D en σ hσ hs hrange hb c0 hc0 hdec x hHerm hrow hcol H β δ hβ
    hPath hLip hVal hValBudget hCayley hFreeze bd hbd hbits ζ hζ hζ1 hζε hζlo
  obtain ⟨hG, hpriv, hcalls, hgates, hr2, hex, herr⟩ := hall (R := R) D en σ hσ hs hrange hb c0
    hc0 hdec x hHerm hrow hcol H β δ hβ hPath hLip hVal hValBudget hCayley hFreeze bd hbd hbits ζ
    hζ hζ1 hζε hζlo
  have hcard := card_binary_registerT k b m
    (simR (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4))
    (binArithT k b m (γ * Real.sqrt s * c0) ζ).bT (binArithT k b m (γ * Real.sqrt s * c0) ζ).bP
    (binArithT k b m (γ * Real.sqrt s * c0) ζ).A
  have hq := binary_registerT_le s k b m σ bd (c0 := c0) hs hσ hbd hγ1 hγs ht hε hε1 hbits hc0
    hζ hζlo hr2
  refine ⟨hG, ?_, hcard, hpriv, hcalls, hgates, hr2, hex, herr⟩
  rw [hcard]
  exact hq

end

end SparseHamiltonian.GateRemarks
