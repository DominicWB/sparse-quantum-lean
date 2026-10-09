import GateEfficientBinaryTime.Simulation
import GateEfficientBinary.Sparse.Budget

/-!
# The query and gate budget of the time-dependent binary construction

The released time-dependent precision budget (`GateCircuit.SlotSim.sparse_counts`, used here at
accuracy `ε/2`, so that the filter accuracy is `ε/4`) chooses the rescaling `γ` from the sparsity
`s`, the time `t` and the accuracy `ε` alone. `binary_time_simulation_budget` states this choice
before the data: one `γ` serves all time-indexed binary sparse data with `s` slots, all inputs,
paths and meshes satisfying the hypotheses of `binary_time_simulation`, and every arithmetic
accuracy `ζ` with `221184 q ζ ≤ ε`, where `q = √s t + √(s t log(2/ε)) + log(2/ε)`. With it the
circuit makes `O(q)` primitive calls of the coherent sampled-time oracles and
`O(q (G_C + C_J + k + m + r))` elementary gates, and its output is within `ε` of every propagator
of the path. The regularity `β` of the path and the sample error `δ` do not enter these counts;
`β` only constrains the number `2^m` of time slots (`8 β t² ≤ ε 2^m`), which enters only through
the `m` slot wires.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateBinary

noncomputable section
open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
open SparseHamiltonian.GateCircuit.Sim (fDeg simR io)
open SparseHamiltonian.OracleCircuit CayleyClockInterface
open NativeSparseBlockEncoding (Data Query)
open scoped InnerProduct

universe u v w

/-- **The budget of the time-dependent binary construction** (Theorem `hs:thm:gates`,
time-dependent part, before finite-set synthesis, with the rescaled sparse parameters of
`hs:thm:time`). For `s ≥ 1` slots, a time `t ≥ 0` and `0 < ε ≤ 1`, put
`q = √s t + √(s t log(2/ε)) + log(2/ε)`. There is one rescaling `γ ∈ (0, 1]` with `γ √s ≥ 1`,
chosen from `s`, `t` and `ε` before the data, the input and the path, whose filter degree is
`d ≤ 4608 q`, such that for all time-indexed binary sparse data with `s = 2^σ` slots and `2^m`
time slots, every input with Hermitian samples of row and column norms at most one, every
Hermitian `β`-Lipschitz path within `δ` of the samples with `8 t δ ≤ ε`, the mesh conditions
`steps τ' (ε/12) ≤ 2^m` and `8 β t² ≤ ε 2^m` (`τ' = √s t/γ`), and every arithmetic accuracy
`0 < ζ ≤ 1` with `221184 q ζ ≤ ε`, the circuit `binaryTimeSim` makes at most `55296 q` times `2`
row-location, `2` column-location and `1` value calls, uses at most
`200 (4608 q + 1) (G_C + (σ + 1) + (k + 1) + m + r + 1)` elementary gates with
`G_C = privGates` of the time-indexed compute circuit and the CORDIC arithmetic and
`2^r ≤ 4 (4608 q + 1)`, the propagator of the lifted path exists, and the full output is within
`ε` of `U(t)` for every propagator `U` of the lifted path. -/
theorem binary_time_simulation_budget (s : ℕ) (hs1 : 1 ≤ s) (t ε : ℝ) (ht : 0 ≤ t)
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
        ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 →
        221184 * ImprovedPrecisionBudget.shape s t (Real.log (2 / ε)) * ζ ≤ ε →
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
  have hs1' : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs1
  have hε2 : 0 < ε / 2 := by linarith
  -- The rescaling of the released time-dependent budget; it depends on `s`, `t` and `ε` only.
  obtain ⟨γ, hγ, hγ1, hγs, -, -, hdeg, -⟩ :=
    SlotSim.sparse_counts 0 (s : ℝ) 1 t (ε / 2) hs1' zero_le_one ht hε2 (by linarith)
  have ht' : 1 * Real.sqrt s / γ * t = time (s : ℝ) t γ := by
    unfold time
    ring
  have he4 : ε / 2 / 2 = ε / 4 := by ring
  have hl : (1 : ℝ) / (ε / 2) = 2 / ε := by
    field_simp
  rw [ht', he4, one_mul, hl] at hdeg
  refine ⟨γ, hγ, hγ1, hγs, hdeg, ?_⟩
  intro X n _ _ k b m R _ _ _ D en σ hσ hs hrange hb c0 hc0 hdec x hHerm hrow hcol H β δ hβ hPath
    hLip hVal hValBudget hCayley hFreeze ζ hζ hζ1 hζε
  have hζε' : 48 * (fDeg (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4) : ℝ) * ζ ≤
      ε := by
    nlinarith [hdeg, hζ]
  obtain ⟨-, hcalls, hgates, -, -, -, hr2, hex, herr⟩ :=
    binary_time_simulation (R := R) D en σ hσ hs hrange hb c0 hc0 hdec x hHerm hrow hcol H t β
      δ γ ε ζ ht hβ hγ hγ1 hε hε1 hζ hζ1 hPath hLip hVal hValBudget hCayley hFreeze hζε'
  refine ⟨fun p => ?_, ?_, ?_, hex, herr⟩
  · rw [hcalls p]
    generalize fDeg (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4) = dn at hdeg ⊢
    generalize ImprovedPrecisionBudget.shape (s : ℝ) t (Real.log (2 / ε)) = q at hdeg ⊢
    push_cast
    have hc : (0 : ℝ) ≤ 2 * (if p Query.rowLocation then 1 else 0) +
        2 * (if p Query.columnLocation then 1 else 0) + (if p Query.value then 1 else 0) := by
      split_ifs <;> norm_num
    generalize (2 * (if p Query.rowLocation then 1 else 0) +
        2 * (if p Query.columnLocation then 1 else 0) + (if p Query.value then 1 else 0) : ℝ) =
      c at hc ⊢
    have h := mul_le_mul_of_nonneg_right hdeg hc
    linarith only [h]
  · have hpg : privGates (sparseOpT k b m (γ * Real.sqrt s * c0))
        (binArithT k b m (γ * Real.sqrt s * c0) ζ) =
        2 * (28 * k) + 2 * (binArithT k b m (γ * Real.sqrt s * c0) ζ).circ.length +
          (2 * (binArithT k b m (γ * Real.sqrt s * c0) ζ).bP +
            (binArithT k b m (γ * Real.sqrt s * c0) ζ).bT + 1) := by
      rw [privGates, show (sparseOpT k b m (γ * Real.sqrt s * c0)).V = computeVT k b m from rfl,
        computeVT_nGates]
    rw [hpg]
    generalize 2 * (28 * k) + 2 * (binArithT k b m (γ * Real.sqrt s * c0) ζ).circ.length +
        (2 * (binArithT k b m (γ * Real.sqrt s * c0) ζ).bP +
          (binArithT k b m (γ * Real.sqrt s * c0) ζ).bT + 1) = G at hgates ⊢
    generalize fDeg (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4) = dn
      at hdeg hgates ⊢
    generalize nGatesN (binaryTimeSim k b m σ hσ s γ c0 t ε ζ) = Gt at hgates ⊢
    generalize simR (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4) = N at hgates ⊢
    generalize ImprovedPrecisionBudget.shape (s : ℝ) t (Real.log (2 / ε)) = q at hdeg ⊢
    have hg : (Gt : ℝ) ≤ 200 * ((dn : ℝ) + 1) * ((k : ℝ) + 1 + m + N + 1) +
        84 * (dn : ℝ) * ((σ : ℝ) + 1) + 6 * (dn : ℝ) * G := by
      exact_mod_cast hgates
    have hG0 : (0 : ℝ) ≤ G := Nat.cast_nonneg _
    have hA0 : (0 : ℝ) ≤ (k : ℝ) + 1 + m + N + 1 := by positivity
    have hB0 : (0 : ℝ) ≤ (σ : ℝ) + 1 := by positivity
    have hd0' : (0 : ℝ) ≤ (dn : ℝ) := Nat.cast_nonneg _
    have h1 := mul_le_mul_of_nonneg_right hdeg hA0
    have h2 := mul_le_mul_of_nonneg_right hdeg hB0
    have h3 := mul_le_mul_of_nonneg_right hdeg hG0
    nlinarith only [hg, h1, h2, h3, hG0, hA0, hB0, hd0']
  · generalize fDeg (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4) = dn
      at hdeg hr2 ⊢
    generalize simR (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4) = N at hr2 ⊢
    generalize ImprovedPrecisionBudget.shape (s : ℝ) t (Real.log (2 / ε)) = q at hdeg ⊢
    have h : ((2 ^ N : ℕ) : ℝ) ≤ 4 * ((dn : ℝ) + 1) := by exact_mod_cast hr2
    linarith only [h, hdeg]

end

end SparseHamiltonian.GateBinary
