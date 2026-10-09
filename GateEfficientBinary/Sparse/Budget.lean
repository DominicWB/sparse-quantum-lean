import GateEfficientBinary.Sparse.Simulation
import GateEfficientNative.Corollaries

/-!
# The query and gate budget of the binary construction

The released precision budget (`GateNative.native_sparse_counts`) chooses the rescaling `γ`
from the sparsity `s`, the time `τ` and the accuracy `ε` alone. `binary_simulation_budget`
states this choice before the data: one `γ`, depending on `s`, `τ` and `ε` only, serves all
binary sparse data with `s` slots, all inputs and every arithmetic accuracy `ζ` with
`221184 q ζ ≤ ε`, where `q = √s τ + √(s τ log(1/ε)) + log(1/ε)`. With it the binary
construction of `binary_simulation` makes `O(q)` primitive calls and
`O(q (G_C + C_J + k + m + r))` elementary gates and is within `ε` of `exp(-iτH)`; the per-call
gate cost `G_C` is `2 · 28 k` for the compute circuit plus the CORDIC arithmetic at accuracy
`ζ` (`cordicArith_counts`), and `C_J = σ + 1`. The register sizes are logarithmic:
`2^m < 2 (2 + 4τ' + √(6τ'³/ε))` with `τ' = √s τ/γ ≤ √s q`, and `2^r ≤ 4 (4608 q + 1)`.
This is the pre-synthesis form of equation `hs:eq:gate-binary`.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateBinary

noncomputable section
open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
open SparseHamiltonian.GateCircuit.Sim (fDeg simM simR io)
open SparseHamiltonian.OracleCircuit CayleyClockInterface
open NativeSparseBlockEncoding (Data Query)
open scoped InnerProduct

universe u v w

/-- **The budget of the binary construction** (Theorem `hs:thm:gates`, pre-synthesis form of
equation `hs:eq:gate-binary`, for binary sparse data). For `s ≥ 1` slots, a time `τ ≥ 0` and
`0 < ε ≤ 1/2`, put `q = √s τ + √(s τ log(1/ε)) + log(1/ε)`. There is one rescaling
`γ ∈ (0, 1]` with `γ √s ≥ 1`, chosen from `s`, `τ` and `ε` before the data and the input,
whose filter degree is `d ≤ 4608 q` and whose rescaled time `τ' = √s τ/γ` satisfies
`τ' ≤ √s q`, with `2^m < 2 (2 + 4τ' + √(6τ'³/ε))` and `2^r ≤ 4 (4608 q + 1)`, such that for
all binary sparse data as in `binary_simulation` with `s = 2^σ` slots, every input `x` with a
Hermitian matrix of row and column norms at most one and every arithmetic accuracy
`0 < ζ ≤ 1` with `221184 q ζ ≤ ε`, the circuit `binarySim` makes at most `55296 q` times `2`
row-location, `2` column-location and `1` value calls, uses at most
`200 (4608 q + 1) (G_C + (σ + 1) + (k + 1) + m + r + 1)` elementary gates with
`G_C = privGates` of the compute circuit and the CORDIC arithmetic, and has full-output error at
most `ε` against `exp(-iτĤ)`. -/
theorem binary_simulation_budget (s : ℕ) (hs1 : 1 ≤ s) (τ ε : ℝ) (hτ : 0 ≤ τ) (hε : 0 < ε)
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
        ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 →
        221184 * ImprovedPrecisionBudget.shape s τ (Real.log (1 / ε)) * ζ ≤ ε →
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
  have hs1' : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs1
  -- The rescaling of the released budget; it depends on `s`, `τ` and `ε` only.
  obtain ⟨γ, hγ, hγ1, hγs, -, -, hτq, hdeg, hm, hr, -⟩ :=
    native_sparse_counts (S := Empty) (Z := Empty) (Y := Empty) (J := Empty) 0
      (s : ℝ) 1 τ ε hs1' zero_le_one hτ hε hε2
  have ht : Real.sqrt s / γ * τ = time (s : ℝ) τ γ := by
    unfold time
    ring
  simp only [one_mul] at hτq hdeg hm hr
  rw [ht] at hτq hdeg hm hr
  refine ⟨γ, hγ, hγ1, hγs, hdeg, hτq, hm, hr, ?_⟩
  intro X n _ _ k b R _ _ _ D en σ hσ hs hrange hb c0 hc0 hdec x hH hrow hcol ζ hζ hζ1 hζε
  have hd0 : (0 : ℝ) ≤ (fDeg (width (s : ℝ) γ) (time (s : ℝ) τ γ) (moment γ) (ε / 2) : ℝ) :=
    Nat.cast_nonneg _
  have hζε' : 48 * (fDeg (width (s : ℝ) γ) (time (s : ℝ) τ γ) (moment γ) (ε / 2) : ℝ) * ζ ≤
      ε := by
    nlinarith [hdeg, hζ]
  obtain ⟨-, hcalls, hgates, -, herr, -⟩ := binary_simulation (R := R) D en σ hσ hs hrange hb c0
    hc0 hdec x hH hrow hcol γ τ ε ζ hγ hγ1 hτ hε (by linarith) hζ hζ1 hζε'
  refine ⟨fun p => ?_, ?_, herr⟩
  · rw [hcalls p]
    generalize fDeg (width (s : ℝ) γ) (time (s : ℝ) τ γ) (moment γ) (ε / 2) = dn at hdeg ⊢
    generalize ImprovedPrecisionBudget.shape (s : ℝ) τ (Real.log (1 / ε)) = q at hdeg ⊢
    push_cast
    have hc : (0 : ℝ) ≤ 2 * (if p Query.rowLocation then 1 else 0) +
        2 * (if p Query.columnLocation then 1 else 0) + (if p Query.value then 1 else 0) := by
      split_ifs <;> norm_num
    generalize (2 * (if p Query.rowLocation then 1 else 0) +
        2 * (if p Query.columnLocation then 1 else 0) + (if p Query.value then 1 else 0) : ℝ) =
      c at hc ⊢
    have h := mul_le_mul_of_nonneg_right hdeg hc
    linarith only [h]
  · have hpg : privGates (sparseOp k b (γ * Real.sqrt s * c0))
        (binArith k b (γ * Real.sqrt s * c0) ζ) =
        2 * (28 * k) + 2 * (binArith k b (γ * Real.sqrt s * c0) ζ).circ.length +
          (2 * (binArith k b (γ * Real.sqrt s * c0) ζ).bP +
            (binArith k b (γ * Real.sqrt s * c0) ζ).bT + 1) := by
      rw [privGates, show (sparseOp k b (γ * Real.sqrt s * c0)).V = computeV k b from rfl,
        computeV_nGates]
    rw [hpg]
    generalize 2 * (28 * k) + 2 * (binArith k b (γ * Real.sqrt s * c0) ζ).circ.length +
        (2 * (binArith k b (γ * Real.sqrt s * c0) ζ).bP +
          (binArith k b (γ * Real.sqrt s * c0) ζ).bT + 1) = G at hgates ⊢
    generalize fDeg (width (s : ℝ) γ) (time (s : ℝ) τ γ) (moment γ) (ε / 2) = dn
      at hdeg hgates ⊢
    generalize simM (time (s : ℝ) τ γ) (ε / 2) = M at hgates ⊢
    generalize simR (width (s : ℝ) γ) (time (s : ℝ) τ γ) (moment γ) (ε / 2) = N at hgates ⊢
    generalize nGatesN (binarySim k b σ hσ s γ c0 τ ε ζ) = Gt at hgates ⊢
    generalize ImprovedPrecisionBudget.shape (s : ℝ) τ (Real.log (1 / ε)) = q at hdeg ⊢
    have hg : (Gt : ℝ) ≤ 200 * ((dn : ℝ) + 1) * ((k : ℝ) + 1 + M + N + 1) +
        84 * (dn : ℝ) * ((σ : ℝ) + 1) + 6 * (dn : ℝ) * G := by
      exact_mod_cast hgates
    have hG0 : (0 : ℝ) ≤ G := Nat.cast_nonneg _
    have hA0 : (0 : ℝ) ≤ (k : ℝ) + 1 + M + N + 1 := by positivity
    have hB0 : (0 : ℝ) ≤ (σ : ℝ) + 1 := by positivity
    have hd0' : (0 : ℝ) ≤ (dn : ℝ) := Nat.cast_nonneg _
    have h1 := mul_le_mul_of_nonneg_right hdeg hA0
    have h2 := mul_le_mul_of_nonneg_right hdeg hB0
    have h3 := mul_le_mul_of_nonneg_right hdeg hG0
    nlinarith only [hg, h1, h2, h3, hG0, hA0, hB0, hd0']

end

end SparseHamiltonian.GateBinary
