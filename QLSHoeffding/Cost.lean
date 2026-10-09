import QLSHoeffding.Algorithm
import ChebyshevLinearSystemFinite.Cost

/-!
# Explicit query counts with Hoeffding's repetition schedule

Every transcript of the protocol with Hoeffding's counts makes at most `5 n_j` tests of
`d^fin_j` signed steps at each stage `j = 1, …, m` and at most `1000` final attempts of
`d^fin_fin` signed steps (`impl_worstCostH`, with `walkStepsH`), each signed step making `54`
matrix-oracle calls and `2` source calls. With `L = log(1/ε)`:

* `d^fin_j < 112 √s 2^j` and `d^fin_fin ≤ 168 √s κ L` (`ChebyshevLinearSystemFinite`);
* `n_j ≤ 25509 L + 3537 (m - j)` (`repsH_le`);
* `Σ_q (25509 L + 3537 q) 2^{-q} ≤ 54555 L` and `2^m ≤ 2κ`;

so `walkStepsH ≤ 6.2·10⁷ √s κ L` (`walkStepsH_le`), and every transcript of every
implementation makes at most `3.4·10⁹ √s κ L` matrix-oracle calls and `1.25·10⁸ √s κ L`
source calls (`impl_matrix_queriesH`, `impl_source_queriesH`; with the released counts
`2.7·10¹⁰` and `10⁹`).
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 2048

namespace QLSHoeffding

noncomputable section
open SparseHamiltonian SparseLinearSystems OracleCircuit LogicalWalk Step Augmented
  ChebyshevFilter Protocol Endpoint ChebyshevLinearSystem ChebyshevLinearSystemFinite

/-! ### The step count -/

/-- Signed walk steps along any transcript of the protocol with Hoeffding's counts: `5 n_j` tests
of `d^fin_j` steps at each stage and at most `1000` final attempts of `d^fin_fin` steps. -/
def walkStepsH (s : ℕ) (κ ε : ℝ) : ℕ :=
  (∑ q ∈ Finset.range (stagesM κ),
    5 * (repsH κ ε (stagesM κ - q) * dTestF s (stageOf κ (stagesM κ - q)))) + 1000 * dFinF s κ ε

/-- **Equation `qls:eq:geometriccost` with the final preparation and Hoeffding's counts**:
`walkStepsH ≤ 6.2·10⁷ √s κ log(1/ε)`. -/
theorem walkStepsH_le (s : ℕ) (hs : 0 < s) (κ ε : ℝ) (hκ : 1 ≤ κ) (hε : 0 < ε)
    (hε1 : ε ≤ 1 / 10) :
    (walkStepsH s κ ε : ℝ) ≤ 62 * 10 ^ 6 * Real.sqrt s * κ * Real.log (1 / ε) := by
  have hL2 := two_le_logInv ε hε hε1
  have hsq0 : 0 ≤ Real.sqrt s := Real.sqrt_nonneg _
  have hκ0 : 0 < κ := by linarith
  -- one stage
  have hterm : ∀ q ∈ Finset.range (stagesM κ),
      5 * ((repsH κ ε (stagesM κ - q) : ℝ) * (dTestF s (stageOf κ (stagesM κ - q)) : ℝ)) ≤
        560 * Real.sqrt s * 2 ^ stagesM κ *
          ((25509 * Real.log (1 / ε) + 3537 * q) * (1 / 2) ^ q) := by
    intro q hq
    have hqm : q < stagesM κ := Finset.mem_range.mp hq
    rw [stageOf_of_le κ (stagesM κ - q) (Nat.sub_le _ _)]
    have hr := repsH_le κ ε hε hε1 (stagesM κ - q)
    rw [show stagesM κ - (stagesM κ - q) = q by omega] at hr
    have ht := (dTestF_lt s hs (stagesM κ - q)).le
    have hpow : (2 : ℝ) ^ (stagesM κ - q) = 2 ^ stagesM κ * (1 / 2) ^ q := by
      have e : (2 : ℝ) ^ stagesM κ = 2 ^ (stagesM κ - q) * 2 ^ q := by
        rw [← pow_add, Nat.sub_add_cancel hqm.le]
      rw [e, one_div_pow, mul_assoc, mul_one_div_cancel (by positivity), mul_one]
    rw [hpow] at ht
    have hr0 : (0 : ℝ) ≤ repsH κ ε (stagesM κ - q) := Nat.cast_nonneg _
    have ht0 : (0 : ℝ) ≤ dTestF s (stagesM κ - q) := Nat.cast_nonneg _
    have hprod := mul_le_mul hr ht ht0 (by positivity)
    calc 5 * ((repsH κ ε (stagesM κ - q) : ℝ) * (dTestF s (stagesM κ - q) : ℝ))
        ≤ 5 * ((25509 * Real.log (1 / ε) + 3537 * (q : ℝ)) *
            (112 * Real.sqrt s * (2 ^ stagesM κ * (1 / 2) ^ q))) := by linarith
      _ = 560 * Real.sqrt s * 2 ^ stagesM κ *
            ((25509 * Real.log (1 / ε) + 3537 * q) * (1 / 2) ^ q) := by ring
  have hsum : ∑ q ∈ Finset.range (stagesM κ),
      5 * ((repsH κ ε (stagesM κ - q) : ℝ) * (dTestF s (stageOf κ (stagesM κ - q)) : ℝ)) ≤
      560 * Real.sqrt s * 2 ^ stagesM κ *
        ∑ q ∈ Finset.range (stagesM κ),
          (25509 * Real.log (1 / ε) + 3537 * q) * (1 / 2 : ℝ) ^ q := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hterm
  have hgeo : ∑ q ∈ Finset.range (stagesM κ),
      (25509 * Real.log (1 / ε) + 3537 * q) * (1 / 2 : ℝ) ^ q ≤
      54555 * Real.log (1 / ε) := by
    have h1 : ∑ q ∈ Finset.range (stagesM κ),
        (25509 * Real.log (1 / ε) + 3537 * q) * (1 / 2 : ℝ) ^ q =
        25509 * Real.log (1 / ε) * ∑ q ∈ Finset.range (stagesM κ), (1 / 2 : ℝ) ^ q +
          3537 * ∑ q ∈ Finset.range (stagesM κ), (q : ℝ) * (1 / 2) ^ q := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro q _
      ring
    have h2 := sum_geometric_two_le (stagesM κ)
    have h3 := sum_mul_half_pow (stagesM κ)
    have h4 : 0 ≤ 2 * ((stagesM κ : ℝ) + 1) * (1 / 2) ^ stagesM κ := by positivity
    have h5 := mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ 25509 * Real.log (1 / ε))
    rw [h1]
    linarith
  have h2m := two_pow_stages_le κ hκ
  have hest : 560 * Real.sqrt s * 2 ^ stagesM κ *
      ∑ q ∈ Finset.range (stagesM κ),
        (25509 * Real.log (1 / ε) + 3537 * q) * (1 / 2 : ℝ) ^ q ≤
      61101600 * Real.sqrt s * κ * Real.log (1 / ε) := by
    have hA : (0 : ℝ) ≤ 560 * Real.sqrt s := by positivity
    calc 560 * Real.sqrt s * 2 ^ stagesM κ *
          ∑ q ∈ Finset.range (stagesM κ),
            (25509 * Real.log (1 / ε) + 3537 * q) * (1 / 2 : ℝ) ^ q
        ≤ 560 * Real.sqrt s * (2 * κ) * (54555 * Real.log (1 / ε)) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left h2m hA) hgeo
            (Finset.sum_nonneg (fun q _ => by positivity)) (by positivity)
      _ = 61101600 * Real.sqrt s * κ * Real.log (1 / ε) := by ring
  -- the final leaf
  have hfin : ((1000 * dFinF s κ ε : ℕ) : ℝ) ≤ 168000 * Real.sqrt s * κ * Real.log (1 / ε) := by
    push_cast
    have h := dFinF_le s hs κ ε hκ hε hε1
    linarith
  have hprod0 : 0 ≤ Real.sqrt s * κ * Real.log (1 / ε) := by
    have : 0 ≤ Real.log (1 / ε) := by linarith
    positivity
  unfold walkStepsH
  rw [Nat.cast_add]
  push_cast at hfin ⊢
  linarith

/-! ### The cost of every transcript -/

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s : ℕ}

local notation "V0" => EuclideanSpace ℂ n

/-- **Every transcript of every implementation** with Hoeffding's counts whose runs have the
weighted costs of the ideal finite-degree runs makes at most the calls of `walkStepsH` signed
steps, each of weighted cost `c`. -/
theorem impl_worstCostH (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (sv : V0) (κ ε : ℝ) (test : ℕ → ℝ → TestRun (physOracle D Ub (TcF s κ ε)) (PrivO n))
    (fin : ℝ → TestRun (physOracle D Ub (TcF s κ ε)) V0) (w : Lbl → ℕ)
    (htest : ∀ j r, (test j r).circuit.cost w = (testRunF D Ub sv κ ε j r).circuit.cost w)
    (hfin : ∀ r, (fin r).circuit.cost w = (finalRunF D Ub sv κ ε r).circuit.cost w) (c : ℕ)
    (hc : ∀ σ r d, (runPhys D Ub sv (TcF s κ ε) σ r d).cost w = d * c) :
    (implAlgorithmH κ ε test fin).worstCost w ≤ walkStepsH s κ ε * c := by
  have ht : ∀ j r, (test j r).circuit.cost w ≤ dTestF s (stageOf κ j) * c := fun j r => by
    rw [htest j r, testRunF_cost D Ub sv κ ε j r w c hc]
  have hl : ∀ r, (repeatLeaf (fin r) 1000).worstCost w ≤ 1000 * (dFinF s κ ε * c) := fun r => by
    rw [repeatLeaf_worstCost, hfin r, finalRunF_cost D Ub sv κ ε r w c hc]
  have h := Estimator.stages_cost w test (fun r => repeatLeaf (fin r) 1000) (repsH κ ε)
    (stagesM κ) κ (fun j => dTestF s (stageOf κ j) * c) ht (1000 * (dFinF s κ ε * c)) hl
    (stagesM κ) 1
  refine h.trans (le_of_eq ?_)
  unfold walkStepsH
  rw [add_mul, Finset.sum_mul]
  congr 1
  · apply Finset.sum_congr rfl
    intro q _
    ring
  · ring

/-- **Matrix-oracle calls** of every transcript of every implementation with Hoeffding's counts
whose runs make the matrix-oracle calls of the ideal finite-degree runs: at most
`3.4·10⁹ √s κ log(1/ε)`. -/
theorem impl_matrix_queriesH (D : NativeSparseBlockEncoding.Data X n Z s)
    (Ub : X → V0 →L[ℂ] V0) (sv : V0) (κ ε : ℝ) (hκ : 1 ≤ κ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 10)
    (test : ℕ → ℝ → TestRun (physOracle D Ub (TcF s κ ε)) (PrivO n))
    (fin : ℝ → TestRun (physOracle D Ub (TcF s κ ε)) V0)
    (htest : ∀ j r, (test j r).circuit.cost wMat = (testRunF D Ub sv κ ε j r).circuit.cost wMat)
    (hfin : ∀ r, (fin r).circuit.cost wMat = (finalRunF D Ub sv κ ε r).circuit.cost wMat) :
    ((implAlgorithmH κ ε test fin).worstCost wMat : ℝ) ≤
      34 * 10 ^ 8 * Real.sqrt s * κ * Real.log (1 / ε) := by
  have h := impl_worstCostH D Ub sv κ ε test fin wMat htest hfin 54
    (fun σ r d => runPhys_cost_mat D Ub sv _ σ r d)
  have h2 := walkStepsH_le s D.slots_pos κ ε hκ hε hε1
  have h3 : ((implAlgorithmH κ ε test fin).worstCost wMat : ℝ) ≤
      (walkStepsH s κ ε : ℝ) * 54 := by
    exact_mod_cast h
  have hL := two_le_logInv ε hε hε1
  have hpos : 0 ≤ Real.sqrt s * κ * Real.log (1 / ε) := by
    have : 0 ≤ κ := by linarith
    have : 0 ≤ Real.log (1 / ε) := by linarith
    positivity
  nlinarith

/-- **Calls of the controlled source preparation** (forward and inverse) of every transcript of
every implementation with Hoeffding's counts whose runs make the source calls of the ideal
finite-degree runs: at most `1.25·10⁸ √s κ log(1/ε)`. -/
theorem impl_source_queriesH (D : NativeSparseBlockEncoding.Data X n Z s)
    (Ub : X → V0 →L[ℂ] V0) (sv : V0) (κ ε : ℝ) (hκ : 1 ≤ κ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 10)
    (test : ℕ → ℝ → TestRun (physOracle D Ub (TcF s κ ε)) (PrivO n))
    (fin : ℝ → TestRun (physOracle D Ub (TcF s κ ε)) V0)
    (htest : ∀ j r, (test j r).circuit.cost wSrc = (testRunF D Ub sv κ ε j r).circuit.cost wSrc)
    (hfin : ∀ r, (fin r).circuit.cost wSrc = (finalRunF D Ub sv κ ε r).circuit.cost wSrc) :
    ((implAlgorithmH κ ε test fin).worstCost wSrc : ℝ) ≤
      125 * 10 ^ 6 * Real.sqrt s * κ * Real.log (1 / ε) := by
  have h := impl_worstCostH D Ub sv κ ε test fin wSrc htest hfin 2
    (fun σ r d => runPhys_cost_src D Ub sv _ σ r d)
  have h2 := walkStepsH_le s D.slots_pos κ ε hκ hε hε1
  have h3 : ((implAlgorithmH κ ε test fin).worstCost wSrc : ℝ) ≤
      (walkStepsH s κ ε : ℝ) * 2 := by
    exact_mod_cast h
  have hL := two_le_logInv ε hε hε1
  have hpos : 0 ≤ Real.sqrt s * κ * Real.log (1 / ε) := by
    have : 0 ≤ κ := by linarith
    have : 0 ≤ Real.log (1 / ε) := by linarith
    positivity
  nlinarith

end

end QLSHoeffding
