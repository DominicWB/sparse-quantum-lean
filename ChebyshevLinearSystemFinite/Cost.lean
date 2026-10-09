import ChebyshevLinearSystemFinite.Algorithm
import ChebyshevLinearSystemFinite.Constants

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 2048

/-!
# Explicit query counts (equations `qls:eq:geometriccost`, `qls:eq:main`)

If every implemented run has the weighted cost of the corresponding ideal run (`AmpApprox.cost_eq`,
`RunApprox.cost_eq`), every transcript of the implemented protocol makes at most the oracle calls
of the ideal finite-degree protocol: `5 n_j` tests of `d^fin_j` signed steps at each stage
`j = 1, …, m` and at most `1000` final attempts of `d^fin_fin` signed steps (`impl_worstCost`,
with `walkStepsF`), each signed step making `54` matrix-oracle calls and `2` source calls. With
`L = log(1/ε)`:

* `d^fin_j < 112 √s 2^j` (`dTestF_lt`, equation `qls:eq:testconstant`) and
  `d^fin_fin ≤ 168 √s κ L` (`dFinF_le`, through `d^fin(δ) ≤ k d^fin(1/100)`);
* the sharper repetition bound `n_j ≤ 204062 L + 28290 (m - j)` (`reps_le_sharp`; the released
  `Endpoint.reps_le` has `210000 (L + m - j)`);
* `Σ_q (204062 L + 28290 q) 2^{-q} ≤ 408124 L + 56580` and `2^m ≤ 2κ`;

so `walkStepsF ≤ 4.9·10⁸ √s κ L` (`walkStepsF_le`), and every transcript of every
implementation makes at most `2.7·10¹⁰ √s κ L` matrix-oracle calls and `10⁹ √s κ L` source
calls (`impl_matrix_queries`, `impl_source_queries`). The same bounds hold for the released
exact-gate Chebyshev algorithm (`algorithm_matrix_queries_sharp`,
`algorithm_source_queries_sharp`; released constants `4.4·10¹⁰` and `1.7·10⁹`), whose degrees
are one smaller (`walkStepsC_le_walkStepsF`).

With `2^{stage(j)} ≤ 2κ` (`two_pow_stageOf_le`), the test allowance has the uniform explicit
lower bounds `e_test(s, j) ≥ 1/(3.6·10⁷ s κ²)` (`eTest_ge_uniform`) and
`e_test(s, j) ≥ 1/(1.65·10⁶ √s κ)` (`eTest_ge_uniform_sharp`) at every stage.
-/

namespace ChebyshevLinearSystemFinite

noncomputable section
open SparseHamiltonian SparseLinearSystems OracleCircuit LogicalWalk Step Augmented
  ChebyshevFilter Protocol Endpoint ChebyshevLinearSystem

/-! ### Repetitions -/

/-- **Sharper repetition bound**: `n_j ≤ 204062 log(1/ε) + 28290 (m - j)`. -/
theorem reps_le_sharp (κ ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 10) (j : ℕ) :
    (reps κ ε j : ℝ) ≤ 204062 * Real.log (1 / ε) + 28290 * ((stagesM κ - j : ℕ) : ℝ) := by
  have hL2 := two_le_logInv ε hε hε1
  have hL10 := log_ten_le_logInv ε hε hε1
  have h10 := two_le_log_ten
  have hz : 2 / zeta κ ε j = 10 ^ 4 * (1 / ε) * 2 ^ (stagesM κ - j) := by
    unfold zeta
    rw [one_div_pow]
    field_simp
    ring
  have hlogz : Real.log (2 / zeta κ ε j) =
      4 * Real.log 10 + Real.log (1 / ε) + ((stagesM κ - j : ℕ) : ℝ) * Real.log 2 := by
    rw [hz, Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hlog2 : Real.log 2 < 13863 / 20000 := by
    have := Real.log_two_lt_d9
    norm_num at this
    linarith
  have hlog2' : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hd0 : (0 : ℝ) ≤ ((stagesM κ - j : ℕ) : ℝ) := Nat.cast_nonneg _
  have htacc : Estimator.tAcc ^ 2 = 9801 / 100000000 := by
    unfold Estimator.tAcc
    norm_num
  have hX : 4 * Real.log (2 / zeta κ ε j) / Estimator.tAcc ^ 2 ≤
      204061 * Real.log (1 / ε) + 28290 * ((stagesM κ - j : ℕ) : ℝ) := by
    rw [htacc, div_le_iff₀ (by norm_num), hlogz]
    have := mul_le_mul_of_nonneg_left hlog2.le hd0
    linarith
  have hpos : 0 ≤ 4 * Real.log (2 / zeta κ ε j) / Estimator.tAcc ^ 2 := by
    rw [htacc, hlogz]
    have := mul_nonneg hd0 hlog2'.le
    have : (0 : ℝ) ≤ 4 * Real.log 10 + Real.log (1 / ε) + ((stagesM κ - j : ℕ) : ℝ) * Real.log 2 :=
      by linarith
    positivity
  have hceil := Nat.ceil_lt_add_one hpos
  unfold reps
  linarith

/-! ### Uniform test allowance -/

/-- `2^{stage(j)} ≤ 2κ`. -/
theorem two_pow_stageOf_le (κ : ℝ) (hκ : 1 ≤ κ) (j : ℕ) : (2 : ℝ) ^ stageOf κ j ≤ 2 * κ :=
  (pow_le_pow_right₀ (by norm_num) (stageOf_le κ j)).trans (two_pow_stages_le κ hκ)

/-- **A uniform test allowance**: `e_test(s, j) ≥ 1/(3.6·10⁷ s κ²)` at every stage. -/
theorem eTest_ge_uniform (s : ℕ) (hs : 0 < s) (κ : ℝ) (hκ : 1 ≤ κ) (j : ℕ) :
    1 / (36 * 10 ^ 6 * (s : ℝ) * κ ^ 2) ≤ eTest s (stageOf κ j) := by
  refine le_trans ?_ (eTest_ge s (stageOf κ j) hs)
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have h2 := two_pow_stageOf_le κ hκ j
  have h4 : (4 : ℝ) ^ stageOf κ j ≤ 4 * κ ^ 2 := by
    have e : (4 : ℝ) ^ stageOf κ j = ((2 : ℝ) ^ stageOf κ j) ^ 2 := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    rw [e]
    nlinarith [pow_pos (show (0 : ℝ) < 2 by norm_num) (stageOf κ j)]
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith

/-- **A sharper uniform test allowance**: `e_test(s, j) ≥ 1/(1.65·10⁶ √s κ)` at every stage
(`eTest_ge_sharp` with `2^{stage(j)} ≤ 2κ`). -/
theorem eTest_ge_uniform_sharp (s : ℕ) (hs : 0 < s) (κ : ℝ) (hκ : 1 ≤ κ) (j : ℕ) :
    1 / (165 * 10 ^ 4 * Real.sqrt s * κ) ≤ eTest s (stageOf κ j) := by
  refine le_trans ?_ (eTest_ge_sharp s (stageOf κ j) hs)
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hsq : 0 < Real.sqrt (s : ℝ) := Real.sqrt_pos.mpr hs'
  have h2 := two_pow_stageOf_le κ hκ j
  apply one_div_le_one_div_of_le (by positivity)
  calc 825000 * Real.sqrt s * 2 ^ stageOf κ j ≤ 825000 * Real.sqrt s * (2 * κ) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = 165 * 10 ^ 4 * Real.sqrt s * κ := by ring

/-! ### The step count -/

/-- Signed walk steps along any transcript of the finite-degree protocol: `5 n_j` tests of
`d^fin_j` steps at each stage and at most `1000` final attempts of `d^fin_fin` steps. -/
def walkStepsF (s : ℕ) (κ ε : ℝ) : ℕ :=
  (∑ q ∈ Finset.range (stagesM κ),
    5 * (reps κ ε (stagesM κ - q) * dTestF s (stageOf κ (stagesM κ - q)))) + 1000 * dFinF s κ ε

/-- **Equation `qls:eq:geometriccost` with the final preparation, at the finite degrees**:
`walkStepsF ≤ 4.9·10⁸ √s κ log(1/ε)`. -/
theorem walkStepsF_le (s : ℕ) (hs : 0 < s) (κ ε : ℝ) (hκ : 1 ≤ κ) (hε : 0 < ε)
    (hε1 : ε ≤ 1 / 10) :
    (walkStepsF s κ ε : ℝ) ≤ 49 * 10 ^ 7 * Real.sqrt s * κ * Real.log (1 / ε) := by
  have hL2 := two_le_logInv ε hε hε1
  have hsq0 : 0 ≤ Real.sqrt s := Real.sqrt_nonneg _
  have hκ0 : 0 < κ := by linarith
  -- one stage
  have hterm : ∀ q ∈ Finset.range (stagesM κ),
      5 * ((reps κ ε (stagesM κ - q) : ℝ) * (dTestF s (stageOf κ (stagesM κ - q)) : ℝ)) ≤
        560 * Real.sqrt s * 2 ^ stagesM κ *
          ((204062 * Real.log (1 / ε) + 28290 * q) * (1 / 2) ^ q) := by
    intro q hq
    have hqm : q < stagesM κ := Finset.mem_range.mp hq
    rw [stageOf_of_le κ (stagesM κ - q) (Nat.sub_le _ _)]
    have hr := reps_le_sharp κ ε hε hε1 (stagesM κ - q)
    rw [show stagesM κ - (stagesM κ - q) = q by omega] at hr
    have ht := (dTestF_lt s hs (stagesM κ - q)).le
    have hpow : (2 : ℝ) ^ (stagesM κ - q) = 2 ^ stagesM κ * (1 / 2) ^ q := by
      have e : (2 : ℝ) ^ stagesM κ = 2 ^ (stagesM κ - q) * 2 ^ q := by
        rw [← pow_add, Nat.sub_add_cancel hqm.le]
      rw [e, one_div_pow, mul_assoc, mul_one_div_cancel (by positivity), mul_one]
    rw [hpow] at ht
    have hr0 : (0 : ℝ) ≤ reps κ ε (stagesM κ - q) := Nat.cast_nonneg _
    have ht0 : (0 : ℝ) ≤ dTestF s (stagesM κ - q) := Nat.cast_nonneg _
    have hprod := mul_le_mul hr ht ht0 (by positivity)
    calc 5 * ((reps κ ε (stagesM κ - q) : ℝ) * (dTestF s (stagesM κ - q) : ℝ))
        ≤ 5 * ((204062 * Real.log (1 / ε) + 28290 * (q : ℝ)) *
            (112 * Real.sqrt s * (2 ^ stagesM κ * (1 / 2) ^ q))) := by linarith
      _ = 560 * Real.sqrt s * 2 ^ stagesM κ *
            ((204062 * Real.log (1 / ε) + 28290 * q) * (1 / 2) ^ q) := by ring
  have hsum : ∑ q ∈ Finset.range (stagesM κ),
      5 * ((reps κ ε (stagesM κ - q) : ℝ) * (dTestF s (stageOf κ (stagesM κ - q)) : ℝ)) ≤
      560 * Real.sqrt s * 2 ^ stagesM κ *
        ∑ q ∈ Finset.range (stagesM κ),
          (204062 * Real.log (1 / ε) + 28290 * q) * (1 / 2 : ℝ) ^ q := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hterm
  have hgeo : ∑ q ∈ Finset.range (stagesM κ),
      (204062 * Real.log (1 / ε) + 28290 * q) * (1 / 2 : ℝ) ^ q ≤
      436414 * Real.log (1 / ε) := by
    have h1 : ∑ q ∈ Finset.range (stagesM κ),
        (204062 * Real.log (1 / ε) + 28290 * q) * (1 / 2 : ℝ) ^ q =
        204062 * Real.log (1 / ε) * ∑ q ∈ Finset.range (stagesM κ), (1 / 2 : ℝ) ^ q +
          28290 * ∑ q ∈ Finset.range (stagesM κ), (q : ℝ) * (1 / 2) ^ q := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro q _
      ring
    have h2 := sum_geometric_two_le (stagesM κ)
    have h3 := sum_mul_half_pow (stagesM κ)
    have h4 : 0 ≤ 2 * ((stagesM κ : ℝ) + 1) * (1 / 2) ^ stagesM κ := by positivity
    have h5 := mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ 204062 * Real.log (1 / ε))
    rw [h1]
    linarith
  have h2m := two_pow_stages_le κ hκ
  have hest : 560 * Real.sqrt s * 2 ^ stagesM κ *
      ∑ q ∈ Finset.range (stagesM κ),
        (204062 * Real.log (1 / ε) + 28290 * q) * (1 / 2 : ℝ) ^ q ≤
      488783680 * Real.sqrt s * κ * Real.log (1 / ε) := by
    have hA : (0 : ℝ) ≤ 560 * Real.sqrt s := by positivity
    calc 560 * Real.sqrt s * 2 ^ stagesM κ *
          ∑ q ∈ Finset.range (stagesM κ),
            (204062 * Real.log (1 / ε) + 28290 * q) * (1 / 2 : ℝ) ^ q
        ≤ 560 * Real.sqrt s * (2 * κ) * (436414 * Real.log (1 / ε)) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left h2m hA) hgeo
            (Finset.sum_nonneg (fun q _ => by positivity)) (by positivity)
      _ = 488783680 * Real.sqrt s * κ * Real.log (1 / ε) := by ring
  -- the final leaf
  have hfin : ((1000 * dFinF s κ ε : ℕ) : ℝ) ≤ 168000 * Real.sqrt s * κ * Real.log (1 / ε) := by
    push_cast
    have h := dFinF_le s hs κ ε hκ hε hε1
    linarith
  have hprod0 : 0 ≤ Real.sqrt s * κ * Real.log (1 / ε) := by
    have : 0 ≤ Real.log (1 / ε) := by linarith
    positivity
  unfold walkStepsF
  rw [Nat.cast_add]
  push_cast at hfin ⊢
  linarith

/-- The released degrees are one smaller: `walkStepsC ≤ walkStepsF`. -/
theorem walkStepsC_le_walkStepsF (s : ℕ) (κ ε : ℝ) : walkStepsC s κ ε ≤ walkStepsF s κ ε := by
  unfold walkStepsC walkStepsF
  apply Nat.add_le_add
  · apply Finset.sum_le_sum
    intro q _
    apply Nat.mul_le_mul_left
    apply Nat.mul_le_mul_left
    exact Nat.le_succ _
  · exact Nat.mul_le_mul_left _ (Nat.le_succ _)

/-! ### The cost of every transcript -/

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s : ℕ}

local notation "V0" => EuclideanSpace ℂ n

/-- **Every transcript of every implementation** whose runs have the weighted costs of the
ideal finite-degree runs makes at most the calls of `walkStepsF` signed steps, each of weighted
cost `c`. -/
theorem impl_worstCost (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (sv : V0) (κ ε : ℝ) (test : ℕ → ℝ → TestRun (physOracle D Ub (TcF s κ ε)) (PrivO n))
    (fin : ℝ → TestRun (physOracle D Ub (TcF s κ ε)) V0) (w : Lbl → ℕ)
    (htest : ∀ j r, (test j r).circuit.cost w = (testRunF D Ub sv κ ε j r).circuit.cost w)
    (hfin : ∀ r, (fin r).circuit.cost w = (finalRunF D Ub sv κ ε r).circuit.cost w) (c : ℕ)
    (hc : ∀ σ r d, (runPhys D Ub sv (TcF s κ ε) σ r d).cost w = d * c) :
    (implAlgorithm κ ε test fin).worstCost w ≤ walkStepsF s κ ε * c := by
  have ht : ∀ j r, (test j r).circuit.cost w ≤ dTestF s (stageOf κ j) * c := fun j r => by
    rw [htest j r, testRunF_cost D Ub sv κ ε j r w c hc]
  have hl : ∀ r, (repeatLeaf (fin r) 1000).worstCost w ≤ 1000 * (dFinF s κ ε * c) := fun r => by
    rw [repeatLeaf_worstCost, hfin r, finalRunF_cost D Ub sv κ ε r w c hc]
  have h := Estimator.stages_cost w test (fun r => repeatLeaf (fin r) 1000) (reps κ ε)
    (stagesM κ) κ (fun j => dTestF s (stageOf κ j) * c) ht (1000 * (dFinF s κ ε * c)) hl
    (stagesM κ) 1
  refine h.trans (le_of_eq ?_)
  unfold walkStepsF
  rw [add_mul, Finset.sum_mul]
  congr 1
  · apply Finset.sum_congr rfl
    intro q _
    ring
  · ring

/-- **Matrix-oracle calls** of every transcript of every implementation whose runs make the
matrix-oracle calls of the ideal finite-degree runs: at most `2.7·10¹⁰ √s κ log(1/ε)`. -/
theorem impl_matrix_queries (D : NativeSparseBlockEncoding.Data X n Z s)
    (Ub : X → V0 →L[ℂ] V0) (sv : V0) (κ ε : ℝ) (hκ : 1 ≤ κ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 10)
    (test : ℕ → ℝ → TestRun (physOracle D Ub (TcF s κ ε)) (PrivO n))
    (fin : ℝ → TestRun (physOracle D Ub (TcF s κ ε)) V0)
    (htest : ∀ j r, (test j r).circuit.cost wMat = (testRunF D Ub sv κ ε j r).circuit.cost wMat)
    (hfin : ∀ r, (fin r).circuit.cost wMat = (finalRunF D Ub sv κ ε r).circuit.cost wMat) :
    ((implAlgorithm κ ε test fin).worstCost wMat : ℝ) ≤
      27 * 10 ^ 9 * Real.sqrt s * κ * Real.log (1 / ε) := by
  have h := impl_worstCost D Ub sv κ ε test fin wMat htest hfin 54
    (fun σ r d => runPhys_cost_mat D Ub sv _ σ r d)
  have h2 := walkStepsF_le s D.slots_pos κ ε hκ hε hε1
  have h3 : ((implAlgorithm κ ε test fin).worstCost wMat : ℝ) ≤ (walkStepsF s κ ε : ℝ) * 54 := by
    exact_mod_cast h
  have hL := two_le_logInv ε hε hε1
  have hpos : 0 ≤ Real.sqrt s * κ * Real.log (1 / ε) := by
    have : 0 ≤ κ := by linarith
    have : 0 ≤ Real.log (1 / ε) := by linarith
    positivity
  nlinarith

/-- **Calls of the controlled source preparation** (forward and inverse) of every transcript of
every implementation whose runs make the source calls of the ideal finite-degree runs: at most
`10⁹ √s κ log(1/ε)`. -/
theorem impl_source_queries (D : NativeSparseBlockEncoding.Data X n Z s)
    (Ub : X → V0 →L[ℂ] V0) (sv : V0) (κ ε : ℝ) (hκ : 1 ≤ κ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 10)
    (test : ℕ → ℝ → TestRun (physOracle D Ub (TcF s κ ε)) (PrivO n))
    (fin : ℝ → TestRun (physOracle D Ub (TcF s κ ε)) V0)
    (htest : ∀ j r, (test j r).circuit.cost wSrc = (testRunF D Ub sv κ ε j r).circuit.cost wSrc)
    (hfin : ∀ r, (fin r).circuit.cost wSrc = (finalRunF D Ub sv κ ε r).circuit.cost wSrc) :
    ((implAlgorithm κ ε test fin).worstCost wSrc : ℝ) ≤
      10 ^ 9 * Real.sqrt s * κ * Real.log (1 / ε) := by
  have h := impl_worstCost D Ub sv κ ε test fin wSrc htest hfin 2
    (fun σ r d => runPhys_cost_src D Ub sv _ σ r d)
  have h2 := walkStepsF_le s D.slots_pos κ ε hκ hε hε1
  have h3 : ((implAlgorithm κ ε test fin).worstCost wSrc : ℝ) ≤ (walkStepsF s κ ε : ℝ) * 2 := by
    exact_mod_cast h
  have hL := two_le_logInv ε hε hε1
  have hpos : 0 ≤ Real.sqrt s * κ * Real.log (1 / ε) := by
    have : 0 ≤ κ := by linarith
    have : 0 ≤ Real.log (1 / ε) := by linarith
    positivity
  nlinarith

/-! ### The released exact-gate algorithm -/

/-- **Matrix-oracle calls of the released Chebyshev algorithm** (exact gates): at most
`2.7·10¹⁰ √s κ log(1/ε)` (released bound `4.4·10¹⁰`). -/
theorem algorithm_matrix_queries_sharp (D : NativeSparseBlockEncoding.Data X n Z s)
    (Ub : X → V0 →L[ℂ] V0) (sv : V0) (κ ε : ℝ) (hκ : 1 ≤ κ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 10) :
    ((ChebyshevLinearSystem.algorithm D Ub sv κ ε).worstCost wMat : ℝ) ≤
      27 * 10 ^ 9 * Real.sqrt s * κ * Real.log (1 / ε) := by
  have h := ChebyshevLinearSystem.algorithm_worstCost D Ub sv κ ε wMat 54
    (fun σ r d => runPhys_cost_mat D Ub sv _ σ r d)
  have hW : (walkStepsC s κ ε : ℝ) ≤ walkStepsF s κ ε := by
    exact_mod_cast walkStepsC_le_walkStepsF s κ ε
  have h2 := walkStepsF_le s D.slots_pos κ ε hκ hε hε1
  have h3 : ((ChebyshevLinearSystem.algorithm D Ub sv κ ε).worstCost wMat : ℝ) ≤
      (walkStepsC s κ ε : ℝ) * 54 := by
    exact_mod_cast h
  have hL := two_le_logInv ε hε hε1
  have hpos : 0 ≤ Real.sqrt s * κ * Real.log (1 / ε) := by
    have : 0 ≤ κ := by linarith
    have : 0 ≤ Real.log (1 / ε) := by linarith
    positivity
  nlinarith

/-- **Source calls of the released Chebyshev algorithm** (exact gates): at most
`10⁹ √s κ log(1/ε)` (released bound `1.7·10⁹`). -/
theorem algorithm_source_queries_sharp (D : NativeSparseBlockEncoding.Data X n Z s)
    (Ub : X → V0 →L[ℂ] V0) (sv : V0) (κ ε : ℝ) (hκ : 1 ≤ κ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 10) :
    ((ChebyshevLinearSystem.algorithm D Ub sv κ ε).worstCost wSrc : ℝ) ≤
      10 ^ 9 * Real.sqrt s * κ * Real.log (1 / ε) := by
  have h := ChebyshevLinearSystem.algorithm_worstCost D Ub sv κ ε wSrc 2
    (fun σ r d => runPhys_cost_src D Ub sv _ σ r d)
  have hW : (walkStepsC s κ ε : ℝ) ≤ walkStepsF s κ ε := by
    exact_mod_cast walkStepsC_le_walkStepsF s κ ε
  have h2 := walkStepsF_le s D.slots_pos κ ε hκ hε hε1
  have h3 : ((ChebyshevLinearSystem.algorithm D Ub sv κ ε).worstCost wSrc : ℝ) ≤
      (walkStepsC s κ ε : ℝ) * 2 := by
    exact_mod_cast h
  have hL := two_le_logInv ε hε hε1
  have hpos : 0 ≤ Real.sqrt s * κ * Real.log (1 / ε) := by
    have : 0 ≤ κ := by linarith
    have : 0 ≤ Real.log (1 / ε) := by linarith
    positivity
  nlinarith

end

end ChebyshevLinearSystemFinite
