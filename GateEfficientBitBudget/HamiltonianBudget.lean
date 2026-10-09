import GateEfficientBitBudget.HamiltonianGates

/-!
# Equation `hs:eq:gate-binary` for the binary constructions

The endpoints of equation `hs:eq:gate-binary` (Theorem `hs:thm:gates`) in the bit lengths, from
the released budgets `GateBinary.binary_simulation_budget` (time-independent Hamiltonians) and
`GateBinary.binary_time_simulation_budget` (time-dependent Hamiltonians on `2^m` time slots):

* `binary_simulation_bits`: with the rescaling of the released budget, for stored bits
  `b ≤ b_data`, a decoder scale `c₀` of bit length `b_data` and `ε/(442368 q) ≤ ζ ≤ ε/(221184 q)`,
  the circuit has at most `10¹⁵ q (𝔟_H + 1)³` elementary gates and the private operation at most
  `2·10⁹ (𝔟_H + 1)³`, `𝔟_H = b_data + log₂(N+1) + log₂((q+1)/ε)`, besides every conclusion of
  `binary_simulation_budget`;
* `binary_time_simulation_bits`: the same for the time-dependent construction, with
  `𝔟_H + log₂(M+1)`, `M = 2^m`, in the total gate count.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateBitBudget

noncomputable section
open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
open SparseHamiltonian.GateBinary SparseHamiltonian.OracleCircuit CayleyClockInterface
open SparseHamiltonian.GateCircuit.Sim (fDeg simM simR io)
open NativeSparseBlockEncoding (Data Query)
open scoped InnerProduct

universe u v w

/-! ### Equation `hs:eq:gate-binary`, time-independent Hamiltonians -/

/-- **Equation `hs:eq:gate-binary` for binary sparse data** (Theorem `hs:thm:gates`, before
finite-set synthesis). For `s ≥ 1` slots, a time `τ ≥ 0` and `0 < ε ≤ 1/2`, put
`q = √s τ + √(s τ log(1/ε)) + log(1/ε)`. The rescaling `γ ∈ (0, 1]` of
`GateBinary.binary_simulation_budget` (chosen from `s`, `τ` and `ε` before the data, with
`γ √s ≥ 1`, filter degree `d ≤ 4608 q`, rescaled time `τ' ≤ √s q` and the released bounds on the
simulator words) satisfies: for all binary sparse data with `s = 2^σ` slots, `k`-bit indices
(`N = 2^k`) and `b ≤ b_data` stored bits, every decoder scale `c₀ > 0` of bit length `b_data`
(`HasBits`), every input `x` with a Hermitian matrix of row and column norms at most one and
every arithmetic accuracy `ζ ∈ (0, 1]` with `ε ≤ 442368 q ζ` and `221184 q ζ ≤ ε` (that is,
`ε/(442368 q) ≤ ζ ≤ ε/(221184 q)`; `ζ = ε/(442368 q)` is admissible, `hs_zeta_spec`), the circuit
`binarySim` uses at most `10¹⁵ q (𝔟_H + 1)³` elementary gates, with
`𝔟_H = bitH b_data (2^k) q ε = b_data + log₂(N+1) + log₂((q+1)/ε)` (equation
`hs:eq:gate-binary`, `G_additional = q poly(b_data, log(N+1), log((q+1)/ε))` with
`poly(x) = 10¹⁵ (x+1)³`), the private operation uses at most `2·10⁹ (𝔟_H + 1)³` gates, and every
conclusion of `binary_simulation_budget` holds: at most `55296 q` times `2` row, `2` column and
`1` value calls, at most `200 (4608 q + 1) (G_C + (σ+1) + (k+1) + m + r + 1)` gates, and
full-output error at most `ε` against `exp(-iτĤ)`. -/
theorem binary_simulation_bits (s : ℕ) (hs1 : 1 ≤ s) (τ ε : ℝ) (hτ : 0 ≤ τ) (hε : 0 < ε)
    (hε2 : ε ≤ 1 / 2) :
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
    binary_simulation_budget.{u, v, w} s hs1 τ ε hτ hε hε2
  refine ⟨γ, hγ, hγ1, hγs, hdeg, hτq, hm, hr, ?_⟩
  intro X n _ _ k b R _ _ _ D en σ hσ hs hrange hb c0 hc0 hdec x hH hrow hcol bd hbd hbits ζ hζ
    hζ1 hζε hζlo
  obtain ⟨hcalls, hgates, herr⟩ :=
    hall (R := R) D en σ hσ hs hrange hb c0 hc0 hdec x hH hrow hcol ζ hζ hζ1 hζε
  obtain ⟨hpriv, -, hG⟩ := hs_gates_le s k b σ bd hs hσ hbd hγ hγ1 hγs hτ hε hε2 hbits hc0 hζ
    hζlo hτq hm hr
  have hY : 0 ≤ (bitH bd (2 ^ k) (ImprovedPrecisionBudget.shape s τ (Real.log (1 / ε))) ε +
      1) ^ 3 := by
    have hε1 : ε ≤ 1 := by linarith
    have hQ0 : 0 ≤ ImprovedPrecisionBudget.shape s τ (Real.log (1 / ε)) :=
      (Real.log_nonneg (by rw [le_div_iff₀ hε]; linarith)).trans (le_shape _ _ _ hτ)
    have := bitH_nonneg bd (2 ^ k) hQ0 hε hε1
    positivity
  exact ⟨hgates.trans hG, by linarith, hcalls, hgates, herr⟩

/-! ### Equation `hs:eq:gate-binary`, time-dependent Hamiltonians -/

/-- **The time-dependent part of equation `hs:eq:gate-binary` for time-indexed binary sparse
data** (Theorem `hs:thm:gates`, time-dependent part, before finite-set synthesis). For `s ≥ 1`
slots, a time `t ≥ 0` and `0 < ε ≤ 1`, put `q = √s t + √(s t log(2/ε)) + log(2/ε)`. The rescaling
`γ ∈ (0, 1]` of `GateBinary.binary_time_simulation_budget` (chosen from `s`, `t` and `ε` before
the data, the input, the path and the mesh, with `γ √s ≥ 1` and filter degree `d ≤ 4608 q`)
satisfies: for all time-indexed binary sparse data with `s = 2^σ` slots, `k`-bit indices
(`N = 2^k`), `M = 2^m` time slots and `b ≤ b_data` stored bits, every decoder scale `c₀ > 0` of
bit length `b_data`, every input with Hermitian samples of row and column norms at most one,
every Hermitian `β`-Lipschitz path within `δ` of the samples with `8 t δ ≤ ε`, the mesh conditions
`steps τ' (ε/12) ≤ 2^m` and `8 β t² ≤ ε 2^m` (`τ' = √s t/γ`), and every arithmetic accuracy
`ζ ∈ (0, 1]` with `ε/(442368 q) ≤ ζ ≤ ε/(221184 q)`, the circuit `binaryTimeSim` uses at most
`10¹⁵ q (𝔟_H + log₂(M+1) + 1)³` elementary gates, `𝔟_H = bitH b_data (2^k) q ε`, the slot-selected
private operation uses at most `2·10⁹ (𝔟_H + 1)³` gates, and every conclusion of
`binary_time_simulation_budget` holds: at most `55296 q` times `2` row, `2` column and `1` value
calls of the coherent sampled-time oracles, at most
`200 (4608 q + 1) (G_C + (σ+1) + (k+1) + m + r + 1)` gates, `2^r ≤ 4 (4608 q + 1)`, the
propagator of the lifted path exists, and the full output is within `ε` of `U(t)` for every
propagator `U` of the lifted path. -/
theorem binary_time_simulation_bits (s : ℕ) (hs1 : 1 ≤ s) (t ε : ℝ) (ht : 0 ≤ t)
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
    binary_time_simulation_budget.{u, v, w} s hs1 t ε ht hε hε1
  refine ⟨γ, hγ, hγ1, hγs, hdeg, ?_⟩
  intro X n _ _ k b m R _ _ _ D en σ hσ hs hrange hb c0 hc0 hdec x hHerm hrow hcol H β δ hβ
    hPath hLip hVal hValBudget hCayley hFreeze bd hbd hbits ζ hζ hζ1 hζε hζlo
  obtain ⟨hcalls, hgates, hr2, hex, herr⟩ := hall (R := R) D en σ hσ hs hrange hb c0 hc0 hdec
    x hHerm hrow hcol H β δ hβ hPath hLip hVal hValBudget hCayley hFreeze ζ hζ hζ1 hζε
  obtain ⟨hpriv, -, hG⟩ := hs_gatesT_le s k b m σ bd hs hσ hbd hγ1 hγs ht hε hε1 hbits hc0 hζ
    hζlo hr2
  have hY : 0 ≤ (bitH bd (2 ^ k) (ImprovedPrecisionBudget.shape s t (Real.log (2 / ε))) ε +
      1) ^ 3 := by
    have hQ0 : 0 ≤ ImprovedPrecisionBudget.shape s t (Real.log (2 / ε)) :=
      (Real.log_nonneg (by rw [le_div_iff₀ hε]; linarith)).trans (le_shape _ _ _ ht)
    have := bitH_nonneg bd (2 ^ k) hQ0 hε hε1
    positivity
  exact ⟨hgates.trans hG, by linarith, hcalls, hgates, hr2, hex, herr⟩

end

end SparseHamiltonian.GateBitBudget
