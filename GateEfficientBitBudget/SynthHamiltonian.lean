import GateEfficientBitBudget.HamiltonianGates
import GateEfficientBitBudget.SynthWords
import GateEfficientSynthesis.Binary

/-!
# Equation `hs:eq:gate-binary` in the bit lengths over a finite gate set

The finite-gate-set forms of the binary constructions (`GateSynth.binary_simulation_budget_synth`
and `GateSynth.binary_time_simulation_budget_synth`: every elementary gate of the native circuit
synthesised over `𝒢` with total accuracy `ε'`) use at most `G₀ (c₁ log((G₀+1)/ε') + c₀)` gates of
`𝒢`, `G₀ = 200 (4608 q + 1) (G_C + (σ+1) + (k+1) + m + r + 1)` the native count, when
`len ζ ≤ c₁ log(1/ζ) + c₀` (`c₀, c₁ ≥ 0` the synthesis constants, not the decoder scale `c₀`).
With the bit-length hypotheses of `binary_simulation_bits`
(respectively `binary_time_simulation_bits`):

* `hs_log_le`: `log((G₀+1)/ε') ≤ 36 (𝔟 + 1) + log(1/ε')` for `G₀ ≤ 10¹⁵ q (𝔟+1)³`;
* `binary_simulation_budget_synth_bits`: at most `10¹⁵ q (𝔟_H+1)³ (c₁ (36 (𝔟_H+1) + log(1/ε')) +
  c₀)` gates of `𝒢`, that is `q · poly(b_data, log(N+1), log((q+1)/ε))` up to the synthesis
  accuracy `log(1/ε')` (equation `hs:eq:gate-binary` after synthesis);
* `binary_time_simulation_budget_synth_bits`: the same with `𝔟_H + log₂(M+1)`, `M = 2^m`;

and every conclusion of the released statements is kept.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateBitBudget

noncomputable section
open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
open SparseHamiltonian.GateBinary SparseHamiltonian.OracleCircuit CayleyClockInterface
open SparseHamiltonian.GateSynth
open SparseHamiltonian.GateCircuit.Sim (fDeg simM simR io)
open NativeSparseBlockEncoding (Data Query)
open scoped InnerProduct

universe u v w x

/-! ### The synthesis factor -/

/-- **The synthesis factor of `hs:eq:gate-binary`**: for `0 ≤ G ≤ 10¹⁵ q (B+1)³` with `q ≥ 1/2`,
`B ≥ 0`, `q ≤ Y`, `Y ≥ 1`, `log₂ Y ≤ B` and `ε' > 0`,
`log((G+1)/ε') ≤ 36 (B + 1) + log(1/ε')`. -/
theorem hs_log_le {G Q B ε' Y : ℝ} (hG0 : 0 ≤ G) (hG : G ≤ 10 ^ 15 * Q * (B + 1) ^ 3)
    (hQ : 1 / 2 ≤ Q) (hB : 0 ≤ B) (hQY : Q ≤ Y) (hY : 1 ≤ Y) (hLB : Real.logb 2 Y ≤ B)
    (hε' : 0 < ε') :
    Real.log ((G + 1) / ε') ≤ 36 * (B + 1) + Real.log (1 / ε') := by
  have hQ0 : 0 < Q := by linarith
  have hB3 : 1 ≤ (B + 1) ^ 3 := one_le_pow₀ (by linarith)
  have hP : 1 / 2 ≤ Q * (B + 1) ^ 3 := by nlinarith
  have h1 : G + 1 ≤ (10 ^ 15 + 2) * (Q * (B + 1) ^ 3) := by nlinarith
  have e : (G + 1) / ε' = (G + 1) * (1 / ε') := by ring
  rw [e, Real.log_mul (by positivity) (by positivity)]
  have h2 : Real.log (G + 1) ≤ Real.log ((10 ^ 15 + 2) * (Q * (B + 1) ^ 3)) :=
    Real.log_le_log (by positivity) h1
  rw [Real.log_mul (by norm_num) (by positivity)] at h2
  have h3 : Real.log (10 ^ 15 + 2) ≤ 35 := by
    have h4 : Real.log (10 ^ 15 + 2) ≤ Real.log (2 ^ 50) :=
      Real.log_le_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at h4
    have := Real.log_two_lt_d9
    norm_num at h4 this ⊢
    linarith
  have h4 := log_q_cube_le hQ0 hQY hY hB
  generalize Real.log (10 ^ 15 + 2) = a at h2 h3
  linarith

/-- The arithmetic of the synthesised gate count: `G (c₁ log((G+1)/ε') + c₀) ≤
10¹⁵ q (B+1)³ (c₁ (36 (B+1) + log(1/ε')) + c₀)` under the hypotheses of `hs_log_le`,
`ε' ≤ 1` and the synthesis constants `c₀, c₁ ≥ 0`. -/
theorem hs_synth_arith {G Q B ε' Y c₀ c₁ : ℝ} (hG0 : 0 ≤ G) (hG : G ≤ 10 ^ 15 * Q * (B + 1) ^ 3)
    (hQ : 1 / 2 ≤ Q) (hB : 0 ≤ B) (hQY : Q ≤ Y) (hY : 1 ≤ Y) (hLB : Real.logb 2 Y ≤ B)
    (hε' : 0 < ε') (hε'1 : ε' ≤ 1) (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁) :
    G * (c₁ * Real.log ((G + 1) / ε') + c₀) ≤
      10 ^ 15 * Q * (B + 1) ^ 3 * (c₁ * (36 * (B + 1) + Real.log (1 / ε')) + c₀) := by
  have hlog := hs_log_le hG0 hG hQ hB hQY hY hLB hε'
  have hl0 : 0 ≤ Real.log ((G + 1) / ε') := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hε']
    linarith
  have hf0 : 0 ≤ c₁ * Real.log ((G + 1) / ε') + c₀ := by positivity
  have hf : c₁ * Real.log ((G + 1) / ε') + c₀ ≤ c₁ * (36 * (B + 1) + Real.log (1 / ε')) + c₀ := by
    have := mul_le_mul_of_nonneg_left hlog hc₁
    linarith
  exact mul_le_mul hG hf hf0 (hG0.trans hG)

/-! ### Time-independent Hamiltonians -/

/-- **Equation `hs:eq:gate-binary` after finite-gate-set synthesis** (Theorem `hs:thm:gates`,
binary sparse data). For `s ≥ 1`, `τ ≥ 0`, `0 < ε ≤ 1/2` and
`q = √s τ + √(s τ log(1/ε)) + log(1/ε)`, the rescaling `γ` of
`GateSynth.binary_simulation_budget_synth` satisfies: under `Synthesis 𝒢 Xa L` with
`L ζ ≤ c₁ log(1/ζ) + c₀` on `(0, 1]` (`c₀, c₁ ≥ 0` the synthesis constants, not the decoder
scale `c₀`), for every synthesis accuracy `ε' ∈ (0, 1]`, all binary
sparse data with `s = 2^σ` slots, `k`-bit indices and `b ≤ b_data` stored bits, every decoder
scale `c₀ > 0` of bit length `b_data`, every admissible input and every arithmetic accuracy
`ε/(442368 q) ≤ ζ ≤ ε/(221184 q)`, the synthesised circuit
`synthBudget hS ε' (binarySim …)` uses at most
`10¹⁵ q (𝔟_H+1)³ (c₁ (36 (𝔟_H+1) + log(1/ε')) + c₀)` gates of `𝒢`,
`𝔟_H = bitH b_data (2^k) q ε`, and every conclusion of `binary_simulation_budget_synth` holds:
its instructions are valid gates of `𝒢` and primitive calls, at most `55296 q` times `2` row,
`2` column and `1` value calls, the released gate count, and full-output error at most `ε + ε'`
with the clean synthesis ancillas. -/
theorem binary_simulation_budget_synth_bits (s : ℕ) (hs1 : 1 ≤ s) (τ ε : ℝ) (hτ : 0 ≤ τ)
    (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
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
    binary_simulation_budget_synth.{u, v, w, x} s hs1 τ ε hτ hε hε2
  refine ⟨γ, hγ, hγ1, hγs, hdeg, hτq, hm, hr, ?_⟩
  intro Xa _ _ 𝒢 L hS c₀ c₁ hc₀ hc₁ hL ε' hε' hε'1 X n _ _ k b R _ _ _ D en σ hσ hs hrange hb
    c0 hc0 hdec x hH hrow hcol bd hbd hbits ζ hζ hζ1 hζε hζlo
  obtain ⟨hv, hk, hcalls, hgates, herr⟩ := hall hS hc₀ hc₁ hL ε' hε' hε'1 (R := R) D en σ hσ hs
    hrange hb c0 hc0 hdec x hH hrow hcol ζ hζ hζ1 hζε
  obtain ⟨-, hG0, hG⟩ := hs_gates_le s k b σ bd hs hσ hbd hγ hγ1 hγs hτ hε hε2 hbits hc0 hζ
    hζlo hτq hm hr
  refine ⟨hgates.trans ?_, hv, hk, hcalls, hgates, herr⟩
  have hε1 : ε ≤ 1 := by linarith
  have hQ0 : 0 ≤ ImprovedPrecisionBudget.shape s τ (Real.log (1 / ε)) :=
    (Real.log_nonneg (by rw [le_div_iff₀ hε]; linarith)).trans (le_shape _ _ _ hτ)
  have hℓ : 1 / 2 ≤ Real.log (1 / ε) := by
    have h1 : Real.log 2 ≤ Real.log (1 / ε) :=
      Real.log_le_log (by norm_num) (by rw [le_div_iff₀ hε]; linarith)
    have h2 := Real.log_two_gt_d9
    norm_num at h2
    linarith
  have hQ : 1 / 2 ≤ ImprovedPrecisionBudget.shape s τ (Real.log (1 / ε)) :=
    hℓ.trans (le_shape _ _ _ hτ)
  have hY1 : 1 ≤ (ImprovedPrecisionBudget.shape s τ (Real.log (1 / ε)) + 1) / ε := by
    rw [le_div_iff₀ hε]
    linarith
  have hQY : ImprovedPrecisionBudget.shape s τ (Real.log (1 / ε)) ≤
      (ImprovedPrecisionBudget.shape s τ (Real.log (1 / ε)) + 1) / ε := by
    rw [le_div_iff₀ hε]
    nlinarith
  have hB0 := bitH_nonneg bd (2 ^ k) hQ0 hε hε1
  have hLB : Real.logb 2 ((ImprovedPrecisionBudget.shape s τ (Real.log (1 / ε)) + 1) / ε) ≤
      bitH bd (2 ^ k) (ImprovedPrecisionBudget.shape s τ (Real.log (1 / ε))) ε := by
    have h1 := logb_succ_nonneg (2 ^ k)
    have h2 : (0 : ℝ) ≤ bd := Nat.cast_nonneg _
    unfold bitH
    linarith
  exact hs_synth_arith hG0 hG hQ hB0 hQY hY1 hLB hε' hε'1 hc₀ hc₁

/-! ### Time-dependent Hamiltonians -/

/-- **The time-dependent part of equation `hs:eq:gate-binary` after finite-gate-set synthesis**
(Theorem `hs:thm:gates`, time-indexed binary sparse data). For `s ≥ 1`, `t ≥ 0`, `0 < ε ≤ 1` and
`q = √s t + √(s t log(2/ε)) + log(2/ε)`, the rescaling `γ` of
`GateSynth.binary_time_simulation_budget_synth` satisfies: under `Synthesis 𝒢 Xa L` with
`L ζ ≤ c₁ log(1/ζ) + c₀` (`c₀, c₁ ≥ 0` the synthesis constants, not the decoder scale `c₀`),
for every `ε' ∈ (0, 1]` and all data, paths, meshes and accuracies as in
`binary_time_simulation_bits` (`M = 2^m` time slots, `b ≤ b_data`, `c₀` of bit length `b_data`,
`ε/(442368 q) ≤ ζ ≤ ε/(221184 q)`), the synthesised circuit uses at most
`10¹⁵ q (𝔟+1)³ (c₁ (36 (𝔟+1) + log(1/ε')) + c₀)` gates of `𝒢`,
`𝔟 = bitH b_data (2^k) q ε + log₂(M+1)`, and every conclusion of
`binary_time_simulation_budget_synth` holds (valid gates of `𝒢`, the calls, the released gate
count, `2^r ≤ 4 (4608 q + 1)`, the propagator of the lifted path, and full-output error at most
`ε + ε'` for every propagator). -/
theorem binary_time_simulation_budget_synth_bits (s : ℕ) (hs1 : 1 ≤ s) (t ε : ℝ) (ht : 0 ≤ t)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
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
    binary_time_simulation_budget_synth.{u, v, w, x} s hs1 t ε ht hε hε1
  refine ⟨γ, hγ, hγ1, hγs, hdeg, ?_⟩
  intro Xa _ _ 𝒢 L hS c₀ c₁ hc₀ hc₁ hL ε' hε' hε'1 X n _ _ k b m R _ _ _ D en σ hσ hs hrange hb
    c0 hc0 hdec x hHerm hrow hcol H β δ hβ hPath hLip hVal hValBudget hCayley hFreeze bd hbd
    hbits ζ hζ hζ1 hζε hζlo
  obtain ⟨hv, hk, hcalls, hgates, hr2, hex, herr⟩ := hall hS hc₀ hc₁ hL ε' hε' hε'1 (R := R) D
    en σ hσ hs hrange hb c0 hc0 hdec x hHerm hrow hcol H β δ hβ hPath hLip hVal hValBudget
    hCayley hFreeze ζ hζ hζ1 hζε
  obtain ⟨-, hG0, hG⟩ := hs_gatesT_le s k b m σ bd hs hσ hbd hγ1 hγs ht hε hε1 hbits hc0 hζ
    hζlo hr2
  refine ⟨hgates.trans ?_, hv, hk, hcalls, hgates, hr2, hex, herr⟩
  have hℓ : 1 / 2 ≤ Real.log (2 / ε) := ImprovedPrecisionBudget.targetLog_ge_half ε hε hε1
  have hQ : 1 / 2 ≤ ImprovedPrecisionBudget.shape s t (Real.log (2 / ε)) :=
    hℓ.trans (le_shape _ _ _ ht)
  have hQ0 : 0 ≤ ImprovedPrecisionBudget.shape s t (Real.log (2 / ε)) := by linarith
  have hY1 : 1 ≤ (ImprovedPrecisionBudget.shape s t (Real.log (2 / ε)) + 1) / ε := by
    rw [le_div_iff₀ hε]
    linarith
  have hQY : ImprovedPrecisionBudget.shape s t (Real.log (2 / ε)) ≤
      (ImprovedPrecisionBudget.shape s t (Real.log (2 / ε)) + 1) / ε := by
    rw [le_div_iff₀ hε]
    nlinarith
  have hB0 := bitH_nonneg bd (2 ^ k) hQ0 hε hε1
  have hM0 := logb_succ_nonneg (2 ^ m)
  have hLB : Real.logb 2 ((ImprovedPrecisionBudget.shape s t (Real.log (2 / ε)) + 1) / ε) ≤
      bitH bd (2 ^ k) (ImprovedPrecisionBudget.shape s t (Real.log (2 / ε))) ε +
        Real.logb 2 (((2 ^ m : ℕ) : ℝ) + 1) := by
    have h1 := logb_succ_nonneg (2 ^ k)
    have h2 : (0 : ℝ) ≤ bd := Nat.cast_nonneg _
    unfold bitH
    linarith
  exact hs_synth_arith hG0 hG hQ (by linarith) hQY hY1 hLB hε' hε'1 hc₀ hc₁

end

end SparseHamiltonian.GateBitBudget
