import GateEfficientRemarks.Qubits

/-!
# The auxiliary qubits of `hs:eq:gate-total` in the bit lengths over a finite gate set

The finite-gate-set forms of the bit-length budgets
(`GateBitBudget.binary_simulation_budget_synth_bits`,
`GateBitBudget.binary_time_simulation_budget_synth_bits`) synthesise every elementary gate of the
binary-data circuits over the finite gate set `𝒢` with the clean synthesis ancillas `Xa`
(`GateSynth.synthBudget`); the synthesised circuits act on the native register and `Xa`. This file
adds the qubit count to these endpoints, with a rescaling `γ` that has every property the
released endpoint states for its rescaling, and the same circuits:

* `binary_simulation_budget_synth_bits_qubits`: at most `4·10⁶ (𝔟_H + 1)³ + |Xa|` qubits, with the
  exact register size and every conclusion of `binary_simulation_budget_synth_bits`;
* `binary_time_simulation_budget_synth_bits_qubits`: at most `4·10⁶ (𝔟_H + log₂(M+1) + 1)³ + |Xa|`
  qubits, with the exact register size and every conclusion of
  `binary_time_simulation_budget_synth_bits`.
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

/-- **The qubits and gates of `hs:thm:gates` over a finite gate set for binary sparse data in the
bit lengths** (equations `hs:eq:gate-total` and `hs:eq:gate-binary` after synthesis). For `s ≥ 1`,
`τ ≥ 0`, `0 < ε ≤ 1/2` and `q = √s τ + √(s τ log(1/ε)) + log(1/ε)`, there is a rescaling `γ`,
chosen before the gate set, the synthesis budget and the data, with every property that
`GateBitBudget.binary_simulation_budget_synth_bits` states, such that: under `Synthesis 𝒢 Xa L` with
`L ζ ≤ c₁ log(1/ζ) + c₀` on `(0, 1]` (`c₀, c₁ ≥ 0` the synthesis constants), for every synthesis
accuracy `ε' ∈ (0, 1]` and all data, inputs and accuracies as in `binary_simulation_bits`, the
synthesised circuit `synthBudget hS ε' (binarySim …)` uses at most
`10¹⁵ q (𝔟_H+1)³ (c₁ (36 (𝔟_H+1) + log(1/ε')) + c₀)` gates of `𝒢` on at most
`4·10⁶ (𝔟_H + 1)³ + |Xa|` qubits, `𝔟_H = bitH b_data (2^k) q ε`; its register (the native one
and `Xa`) has exactly `k + (2(k+1) + 3m + 6r + 3) + (6k + 2b + bT + bP + A + 3) + |Xa|` qubits;
and every other conclusion of `binary_simulation_budget_synth_bits` holds (valid gates of `𝒢` and
primitive calls, at most `55296 q` times `2` row, `2` column and `1` value calls, the released gate
count, full-output error at most `ε + ε'`). -/
theorem binary_simulation_budget_synth_bits_qubits (s : ℕ) (hs1 : 1 ≤ s) (τ ε : ℝ)
    (hτ : 0 ≤ τ) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 1 ≤ γ * Real.sqrt s ∧
      (fDeg (width (s : ℝ) γ) (time (s : ℝ) τ γ) (moment γ) (ε / 2) : ℝ) ≤
        4608 * ImprovedPrecisionBudget.shape s τ (Real.log (1 / ε)) ∧
      time (s : ℝ) τ γ ≤ Real.sqrt s * ImprovedPrecisionBudget.shape s τ (Real.log (1 / ε)) ∧
      ((2 ^ simM (time (s : ℝ) τ γ) (ε / 2) : ℕ) : ℝ) <
        2 * (2 + 4 * time (s : ℝ) τ γ + Real.sqrt (6 * time (s : ℝ) τ γ ^ 3 / ε)) ∧
      ((2 ^ simR (width (s : ℝ) γ) (time (s : ℝ) τ γ) (moment γ) (ε / 2) : ℕ) : ℝ) ≤
        4 * (4608 * ImprovedPrecisionBudget.shape s τ (Real.log (1 / ε)) + 1) ∧
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
        ∀ bd : ℕ, b ≤ bd → HasBits bd c0 →
        ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 →
        221184 * ImprovedPrecisionBudget.shape s τ (Real.log (1 / ε)) * ζ ≤ ε →
        ε ≤ 442368 * ImprovedPrecisionBudget.shape s τ (Real.log (1 / ε)) * ζ →
        (nGatesN (synthBudget hS ε' (binarySim k b σ hσ s γ c0 τ ε ζ)) : ℝ) ≤
          10 ^ 15 * ImprovedPrecisionBudget.shape s τ (Real.log (1 / ε)) *
            (bitH bd (2 ^ k) (ImprovedPrecisionBudget.shape s τ (Real.log (1 / ε))) ε + 1) ^ 3 *
            (c₁ * (36 * (bitH bd (2 ^ k) (ImprovedPrecisionBudget.shape s τ
              (Real.log (1 / ε))) ε + 1) + Real.log (1 / ε')) + c₀) ∧
        (Fintype.card (HW (SimWire (k + 1) (width (s : ℝ) γ) (time (s : ℝ) τ γ) (moment γ)
            (ε / 2)) (Fin k) Empty (SZ k b) (binArith k b (γ * Real.sqrt s * c0) ζ).bT
            (binArith k b (γ * Real.sqrt s * c0) ζ).bP
            (binArith k b (γ * Real.sqrt s * c0) ζ).A ⊕ Xa) : ℝ) ≤
          4 * 10 ^ 6 *
            (bitH bd (2 ^ k) (ImprovedPrecisionBudget.shape s τ (Real.log (1 / ε))) ε + 1) ^ 3 +
            Fintype.card Xa ∧
        Fintype.card (HW (SimWire (k + 1) (width (s : ℝ) γ) (time (s : ℝ) τ γ) (moment γ)
            (ε / 2)) (Fin k) Empty (SZ k b) (binArith k b (γ * Real.sqrt s * c0) ζ).bT
            (binArith k b (γ * Real.sqrt s * c0) ζ).bP
            (binArith k b (γ * Real.sqrt s * c0) ζ).A ⊕ Xa) =
          k + (2 * (k + 1) + 3 * simM (time (s : ℝ) τ γ) (ε / 2) +
              6 * simR (width (s : ℝ) γ) (time (s : ℝ) τ γ) (moment γ) (ε / 2) + 3) +
            (6 * k + 2 * b + (binArith k b (γ * Real.sqrt s * c0) ζ).bT +
              (binArith k b (γ * Real.sqrt s * c0) ζ).bP +
              (binArith k b (γ * Real.sqrt s * c0) ζ).A + 3) + Fintype.card Xa ∧
        (∀ i ∈ synthBudget hS ε' (binarySim k b σ hσ s γ c0 τ ε ζ), i.Valid) ∧
        (∀ g, NInstr.gate g ∈ synthBudget hS ε' (binarySim k b σ hσ s γ c0 τ ε ζ) →
          GateOf 𝒢 g) ∧
        (∀ p : Query → Bool,
          (nCallsN p (synthBudget hS ε' (binarySim k b σ hσ s γ c0 τ ε ζ)) : ℝ) ≤
            55296 * ImprovedPrecisionBudget.shape s τ (Real.log (1 / ε)) *
              (2 * (if p Query.rowLocation then 1 else 0) +
                2 * (if p Query.columnLocation then 1 else 0) +
                (if p Query.value then 1 else 0))) ∧
        (nGatesN (synthBudget hS ε' (binarySim k b σ hσ s γ c0 τ ε ζ)) : ℝ) ≤
          200 * (4608 * ImprovedPrecisionBudget.shape s τ (Real.log (1 / ε)) + 1) *
              ((privGates (sparseOp k b (γ * Real.sqrt s * c0))
                  (binArith k b (γ * Real.sqrt s * c0) ζ) : ℝ) + (σ + 1) + (k + 1) +
                simM (time (s : ℝ) τ γ) (ε / 2) +
                simR (width (s : ℝ) γ) (time (s : ℝ) τ γ) (moment γ) (ε / 2) + 1) *
            (c₁ * Real.log ((200 * (4608 * ImprovedPrecisionBudget.shape s τ
                  (Real.log (1 / ε)) + 1) *
              ((privGates (sparseOp k b (γ * Real.sqrt s * c0))
                  (binArith k b (γ * Real.sqrt s * c0) ζ) : ℝ) + (σ + 1) + (k + 1) +
                simM (time (s : ℝ) τ γ) (ε / 2) +
                simR (width (s : ℝ) γ) (time (s : ℝ) τ γ) (moment γ) (ε / 2) + 1) + 1) / ε') +
              c₀) ∧
        ‖nrun (prims (R := R) D en x) (synthBudget hS ε' (binarySim k b σ hσ s γ c0 τ ε ζ)) ∘L
            (cleanEmb (X := Xa) ∘L sysEmb (io (P := Reg (Fin k) R))) -
            (cleanEmb ∘L sysEmb (io (P := Reg (Fin k) R))) ∘L
              NormedSpace.exp ((-Complex.I * (τ : ℂ)) •
                qlift (R := R) en (SparseStateOverlap.matrixOperator (D.matrix x)))‖ ≤
          ε + ε' := by
  obtain ⟨γ, hγ, hγ1, hγs, hdeg, hτq, hm, hr, hall⟩ :=
    binary_simulation_budget_synth_bits.{u, v, w, x} s hs1 τ ε hτ hε hε2
  refine ⟨γ, hγ, hγ1, hγs, hdeg, hτq, hm, hr, ?_⟩
  intro Xa _ _ 𝒢 L hS c₀ c₁ hc₀ hc₁ hL ε' hε' hε'1 X n _ _ k b R _ _ _ D en σ hσ hs hrange hb
    c0 hc0 hdec x hH hrow hcol bd hbd hbits ζ hζ hζ1 hζε hζlo
  obtain ⟨hG, hv, hk, hcalls, hgates, herr⟩ := hall hS hc₀ hc₁ hL ε' hε' hε'1 (R := R) D en σ hσ
    hs hrange hb c0 hc0 hdec x hH hrow hcol bd hbd hbits ζ hζ hζ1 hζε hζlo
  have hcard := card_binary_register k b (binArith k b (γ * Real.sqrt s * c0) ζ).bT
    (binArith k b (γ * Real.sqrt s * c0) ζ).bP (binArith k b (γ * Real.sqrt s * c0) ζ).A
    (width (s : ℝ) γ) (time (s : ℝ) τ γ) (moment γ) (ε / 2)
  have hq := binary_register_le s k b σ bd (c0 := c0) hs hσ hbd hγ1 hγs hτ hε hε2 hbits hc0 hζ
    hζlo hτq hm hr
  refine ⟨hG, ?_, ?_, hv, hk, hcalls, hgates, herr⟩
  · rw [Fintype.card_sum, Nat.cast_add, hcard]
    linarith
  · rw [Fintype.card_sum, hcard]

/-- **The qubits and gates of the time-dependent part of `hs:thm:gates` over a finite gate set for
time-indexed binary sparse data in the bit lengths.** For `s ≥ 1`, `t ≥ 0`, `0 < ε ≤ 1` and
`q = √s t + √(s t log(2/ε)) + log(2/ε)`, there is a rescaling `γ`, chosen before the gate set,
the synthesis budget, the data, the path and the mesh, with every property that
`GateBitBudget.binary_time_simulation_budget_synth_bits` states, such that: under
`Synthesis 𝒢 Xa L` with
`L ζ ≤ c₁ log(1/ζ) + c₀`, for every `ε' ∈ (0, 1]` and all data, paths, meshes and accuracies as in
`binary_time_simulation_bits` (`M = 2^m` time slots), the synthesised circuit uses at most
`10¹⁵ q (𝔟+1)³ (c₁ (36 (𝔟+1) + log(1/ε')) + c₀)` gates of `𝒢`, `𝔟 = 𝔟_H + log₂(M+1)`, on at
most `4·10⁶ (𝔟 + 1)³ + |Xa|` qubits; its register has exactly
`k + (2(k+1) + 3m + 6r + 3) + (6k + 2b + bT + bP + A + 3) + |Xa|` qubits; and every other
conclusion of `binary_time_simulation_budget_synth_bits` holds. -/
theorem binary_time_simulation_budget_synth_bits_qubits (s : ℕ) (hs1 : 1 ≤ s) (t ε : ℝ)
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
        (nGatesN (synthBudget hS ε' (binaryTimeSim k b m σ hσ s γ c0 t ε ζ)) : ℝ) ≤
          10 ^ 15 * ImprovedPrecisionBudget.shape s t (Real.log (2 / ε)) *
            (bitH bd (2 ^ k) (ImprovedPrecisionBudget.shape s t (Real.log (2 / ε))) ε +
              Real.logb 2 (((2 ^ m : ℕ) : ℝ) + 1) + 1) ^ 3 *
            (c₁ * (36 * (bitH bd (2 ^ k) (ImprovedPrecisionBudget.shape s t (Real.log (2 / ε)))
              ε + Real.logb 2 (((2 ^ m : ℕ) : ℝ) + 1) + 1) + Real.log (1 / ε')) + c₀) ∧
        (Fintype.card (HW (Wire (k + 1) m
            (simR (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4))
            (k + 1 + m + 2 * simR (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4)))
            (Fin k) Empty (SZ k b) (binArithT k b m (γ * Real.sqrt s * c0) ζ).bT
            (binArithT k b m (γ * Real.sqrt s * c0) ζ).bP
            (binArithT k b m (γ * Real.sqrt s * c0) ζ).A ⊕ Xa) : ℝ) ≤
          4 * 10 ^ 6 *
            (bitH bd (2 ^ k) (ImprovedPrecisionBudget.shape s t (Real.log (2 / ε))) ε +
              Real.logb 2 (((2 ^ m : ℕ) : ℝ) + 1) + 1) ^ 3 + Fintype.card Xa ∧
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
        (∃ U : ℝ → Reg (Fin k) R →L[ℂ] Reg (Fin k) R, U 0 = 1 ∧
          TimeDependent.SolvesOn
            (fun u => qlift (R := R) en (SparseStateOverlap.matrixOperator (H u))) U 0 t) ∧
        ∀ U : ℝ → Reg (Fin k) R →L[ℂ] Reg (Fin k) R, U 0 = 1 →
          TimeDependent.SolvesOn
            (fun u => qlift (R := R) en (SparseStateOverlap.matrixOperator (H u))) U 0 t →
          ‖nrun (primsT (R := R) D en x)
                (synthBudget hS ε' (binaryTimeSim k b m σ hσ s γ c0 t ε ζ)) ∘L
              (cleanEmb (X := Xa) ∘L sysEmb (io (P := Reg (Fin k) R))) -
              (cleanEmb ∘L sysEmb (io (P := Reg (Fin k) R))) ∘L U t‖ ≤ ε + ε' := by
  obtain ⟨γ, hγ, hγ1, hγs, hdeg, hall⟩ :=
    binary_time_simulation_budget_synth_bits.{u, v, w, x} s hs1 t ε ht hε hε1
  refine ⟨γ, hγ, hγ1, hγs, hdeg, ?_⟩
  intro Xa _ _ 𝒢 L hS c₀ c₁ hc₀ hc₁ hL ε' hε' hε'1 X n _ _ k b m R _ _ _ D en σ hσ hs hrange hb
    c0 hc0 hdec x hHerm hrow hcol H β δ hβ hPath hLip hVal hValBudget hCayley hFreeze bd hbd
    hbits ζ hζ hζ1 hζε hζlo
  obtain ⟨hG, hv, hk, hcalls, hgates, hr2, hex, herr⟩ := hall hS hc₀ hc₁ hL ε' hε' hε'1 (R := R)
    D en σ hσ hs hrange hb c0 hc0 hdec x hHerm hrow hcol H β δ hβ hPath hLip hVal hValBudget
    hCayley hFreeze bd hbd hbits ζ hζ hζ1 hζε hζlo
  have hcard := card_binary_registerT k b m
    (simR (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4))
    (binArithT k b m (γ * Real.sqrt s * c0) ζ).bT (binArithT k b m (γ * Real.sqrt s * c0) ζ).bP
    (binArithT k b m (γ * Real.sqrt s * c0) ζ).A
  have hq := binary_registerT_le s k b m σ bd (c0 := c0) hs hσ hbd hγ1 hγs ht hε hε1 hbits hc0
    hζ hζlo hr2
  refine ⟨hG, ?_, ?_, hv, hk, hcalls, hgates, hr2, hex, herr⟩
  · rw [Fintype.card_sum, Nat.cast_add, hcard]
    linarith
  · rw [Fintype.card_sum, hcard]

end

end SparseHamiltonian.GateRemarks
