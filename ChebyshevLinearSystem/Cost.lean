import ChebyshevLinearSystem.Algorithm
import SparseLinearSystems.Endpoint.Cost

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 2048

/-!
# The worst-case query count with the Chebyshev filter (equations `qls:eq:main`,
`qls:eq:geometriccost`)

Every transcript of `algorithm` performs at most `walkStepsC s κ ε` signed walk steps
(`algorithm_worstCost`): `5 n_j` runs of `d_j` signed steps at each stage `j = 1, …, m` and at
most `1000` final attempts of `d_fin` signed steps. Each signed step makes `54` matrix-oracle
calls and `2` calls of the controlled source preparation (`runPhys_cost_mat`,
`runPhys_cost_src`, from Lemma `qls:lem:signedwalk`).

`walkStepsC_le` is the explicit form of equation `qls:eq:geometriccost` together with the
final preparation: with `L = log(1/ε)`,

* `d_j ≤ 128 √s 2^j` (`dTest_le`, from `ChebyshevFilter.augDegree_le` and `log 200 ≤ 8 log 2`);
* `d_fin ≤ 111 √s κ L` (`dFin_le`, from `log(2000/ε) ≤ 11 log 2 + L` and `L ≥ 2`);
* `n_j ≤ 210000 (L + m - j)` and the geometric sums are those of the released proof
  (`Endpoint.reps_le`, `Endpoint.sum_mul_half_pow`, `Endpoint.two_pow_stages_le`);

so `walkStepsC ≤ 8.1·10⁸ √s κ log(1/ε)`, and every transcript makes at most
`4.4·10¹⁰ √s κ log(1/ε)` matrix-oracle calls and `1.7·10⁹ √s κ log(1/ε)` source calls.

Notation: the regularization parameter is `σ` here and `ξ` in the manuscript, so a subscript `σ` (as
in `g_σ`, `r_σ`, `H_{σ,r}`) stands for the manuscript's subscript `ξ`.
-/

namespace ChebyshevLinearSystem

noncomputable section
open SparseHamiltonian SparseLinearSystems OracleCircuit LogicalWalk Step Augmented
  ChebyshevFilter Protocol Endpoint

/-! ### Degree bounds -/

/-- `log 200 ≤ 8 log 2 < 5.546`. -/
theorem log_two_hundred_le : Real.log 200 ≤ 5546 / 1000 := by
  have h1 : Real.log 200 ≤ Real.log 256 := Real.log_le_log (by norm_num) (by norm_num)
  have h2 : Real.log 256 = 8 * Real.log 2 := by
    rw [show (256 : ℝ) = 2 ^ 8 by norm_num, Real.log_pow]
    norm_num
  linarith [Real.log_two_lt_d9]

/-- `log 2000 ≤ 11 log 2 < 7.625`. -/
theorem log_two_thousand_le : Real.log 2000 ≤ 7625 / 1000 := by
  have h1 : Real.log 2000 ≤ Real.log 2048 := Real.log_le_log (by norm_num) (by norm_num)
  have h2 : Real.log 2048 = 11 * Real.log 2 := by
    rw [show (2048 : ℝ) = 2 ^ 11 by norm_num, Real.log_pow]
    norm_num
  linarith [Real.log_two_lt_d9]

/-- **Test degrees**: `d_j = d_{σ_j}(1/100) ≤ 128 √s 2^j`. -/
theorem dTest_le (s : ℕ) (hs : 0 < s) (j : ℕ) :
    (dTest s j : ℝ) ≤ 128 * Real.sqrt s * 2 ^ j := by
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have h := augDegree_le hs1 (sig_pos j) (sig_le_one j) (by norm_num : (0 : ℝ) < 1 / 100)
    (by norm_num : (1 : ℝ) / 100 < 1)
  have h2 : (2 : ℝ) / (1 / 100) = 200 := by norm_num
  have h3 : 23 * Real.sqrt s * Real.log 200 / sig j =
      23 * Real.log 200 * (Real.sqrt s * 2 ^ j) := by
    unfold sig
    rw [one_div_pow, div_div_eq_mul_div, div_one]
    ring
  rw [h2, h3] at h
  have hl : 23 * Real.log 200 ≤ 128 := by linarith [log_two_hundred_le]
  have hp : 0 ≤ Real.sqrt s * 2 ^ j := by positivity
  unfold dTest
  calc ((augDegree (s : ℝ) (sig j) (1 / 100) : ℕ) : ℝ)
      ≤ 23 * Real.log 200 * (Real.sqrt s * 2 ^ j) := h
    _ ≤ 128 * (Real.sqrt s * 2 ^ j) := mul_le_mul_of_nonneg_right hl hp
    _ = 128 * Real.sqrt s * 2 ^ j := by ring

/-- **The final degree**: `d_0(ε/1000)` at `g = 1/κ` is at most `111 √s κ log(1/ε)`. -/
theorem dFin_le (s : ℕ) (hs : 0 < s) (κ ε : ℝ) (hκ : 1 ≤ κ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 10) :
    (dFin s κ ε : ℝ) ≤ 111 * Real.sqrt s * κ * Real.log (1 / ε) := by
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hκ0 : 0 < κ := by linarith
  have hg0 : 0 < 1 / κ := by positivity
  have hg1 : 1 / κ ≤ 1 := by rw [div_le_one hκ0]; exact hκ
  have h := augDegree_le hs1 hg0 hg1 (by positivity : (0 : ℝ) < ε / 1000)
    (by linarith : ε / 1000 < 1)
  have hL2 := two_le_logInv ε hε hε1
  have h2 : Real.log (2 / (ε / 1000)) = Real.log 2000 + Real.log (1 / ε) := by
    rw [show (2 : ℝ) / (ε / 1000) = 2000 * (1 / ε) by field_simp; ring,
      Real.log_mul (by norm_num) (by positivity)]
  have h3 : Real.log (2 / (ε / 1000)) ≤ 4813 / 1000 * Real.log (1 / ε) := by
    rw [h2]
    linarith [log_two_thousand_le]
  have h4 : 23 * Real.sqrt s * Real.log (2 / (ε / 1000)) / (1 / κ) =
      23 * (Real.sqrt s * κ) * Real.log (2 / (ε / 1000)) := by
    field_simp
  rw [h4] at h
  have hp : 0 ≤ Real.sqrt s * κ := by positivity
  unfold dFin
  calc ((augDegree (s : ℝ) (1 / κ) (ε / 1000) : ℕ) : ℝ)
      ≤ 23 * (Real.sqrt s * κ) * Real.log (2 / (ε / 1000)) := h
    _ ≤ 23 * (Real.sqrt s * κ) * (4813 / 1000 * Real.log (1 / ε)) := by
        apply mul_le_mul_of_nonneg_left h3
        positivity
    _ ≤ 111 * Real.sqrt s * κ * Real.log (1 / ε) := by
        have hL0 : 0 ≤ Real.log (1 / ε) := by linarith
        have := mul_nonneg hp hL0
        nlinarith

/-! ### The step count -/

/-- Signed walk steps along any transcript: `5 n_j` tests of `d_j` steps at each stage and at
most `1000` final attempts of `d_fin` steps. -/
def walkStepsC (s : ℕ) (κ ε : ℝ) : ℕ :=
  (∑ q ∈ Finset.range (stagesM κ),
    5 * (reps κ ε (stagesM κ - q) * dTest s (stageOf κ (stagesM κ - q)))) + 1000 * dFin s κ ε

/-- **Equation `qls:eq:geometriccost` with the final preparation, for the Chebyshev filter**:
`walkStepsC ≤ 8.1·10⁸ √s κ log(1/ε)`. -/
theorem walkStepsC_le (s : ℕ) (hs : 0 < s) (κ ε : ℝ) (hκ : 1 ≤ κ) (hε : 0 < ε)
    (hε1 : ε ≤ 1 / 10) :
    (walkStepsC s κ ε : ℝ) ≤ 81 * 10 ^ 7 * Real.sqrt s * κ * Real.log (1 / ε) := by
  have hL2 := two_le_logInv ε hε hε1
  have hsq0 : 0 ≤ Real.sqrt s := Real.sqrt_nonneg _
  have hκ0 : 0 < κ := by linarith
  -- one stage
  have hterm : ∀ q ∈ Finset.range (stagesM κ),
      5 * ((reps κ ε (stagesM κ - q) : ℝ) * (dTest s (stageOf κ (stagesM κ - q)) : ℝ)) ≤
        134400000 * Real.sqrt s * 2 ^ stagesM κ *
          ((Real.log (1 / ε) + q) * (1 / 2) ^ q) := by
    intro q hq
    have hqm : q < stagesM κ := Finset.mem_range.mp hq
    rw [stageOf_of_le κ (stagesM κ - q) (Nat.sub_le _ _)]
    have hr := reps_le κ ε hε hε1 (stagesM κ - q)
    rw [show stagesM κ - (stagesM κ - q) = q by omega] at hr
    have ht := dTest_le s hs (stagesM κ - q)
    have hpow : (2 : ℝ) ^ (stagesM κ - q) = 2 ^ stagesM κ * (1 / 2) ^ q := by
      have e : (2 : ℝ) ^ stagesM κ = 2 ^ (stagesM κ - q) * 2 ^ q := by
        rw [← pow_add, Nat.sub_add_cancel hqm.le]
      rw [e, one_div_pow, mul_assoc, mul_one_div_cancel (by positivity), mul_one]
    rw [hpow] at ht
    have hr0 : (0 : ℝ) ≤ reps κ ε (stagesM κ - q) := Nat.cast_nonneg _
    have ht0 : (0 : ℝ) ≤ dTest s (stagesM κ - q) := Nat.cast_nonneg _
    have hprod := mul_le_mul hr ht ht0 (by positivity)
    calc 5 * ((reps κ ε (stagesM κ - q) : ℝ) * (dTest s (stagesM κ - q) : ℝ))
        ≤ 5 * (210000 * (Real.log (1 / ε) + (q : ℝ)) *
            (128 * Real.sqrt s * (2 ^ stagesM κ * (1 / 2) ^ q))) := by linarith
      _ = 134400000 * Real.sqrt s * 2 ^ stagesM κ *
            ((Real.log (1 / ε) + q) * (1 / 2) ^ q) := by ring
  have hsum : ∑ q ∈ Finset.range (stagesM κ),
      5 * ((reps κ ε (stagesM κ - q) : ℝ) * (dTest s (stageOf κ (stagesM κ - q)) : ℝ)) ≤
      134400000 * Real.sqrt s * 2 ^ stagesM κ *
        ∑ q ∈ Finset.range (stagesM κ), (Real.log (1 / ε) + q) * (1 / 2 : ℝ) ^ q := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hterm
  have hgeo : ∑ q ∈ Finset.range (stagesM κ), (Real.log (1 / ε) + q) * (1 / 2 : ℝ) ^ q ≤
      2 * Real.log (1 / ε) + 2 := by
    have h1 : ∑ q ∈ Finset.range (stagesM κ), (Real.log (1 / ε) + q) * (1 / 2 : ℝ) ^ q =
        Real.log (1 / ε) * ∑ q ∈ Finset.range (stagesM κ), (1 / 2 : ℝ) ^ q +
          ∑ q ∈ Finset.range (stagesM κ), (q : ℝ) * (1 / 2) ^ q := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro q _
      ring
    have h2 := sum_geometric_two_le (stagesM κ)
    have h3 := sum_mul_half_pow (stagesM κ)
    have h4 : 0 ≤ 2 * ((stagesM κ : ℝ) + 1) * (1 / 2) ^ stagesM κ := by positivity
    have h5 := mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ Real.log (1 / ε))
    rw [h1]
    linarith
  have h2m := two_pow_stages_le κ hκ
  have hest : 134400000 * Real.sqrt s * 2 ^ stagesM κ *
      ∑ q ∈ Finset.range (stagesM κ), (Real.log (1 / ε) + q) * (1 / 2 : ℝ) ^ q ≤
      806400000 * Real.sqrt s * κ * Real.log (1 / ε) := by
    have hA : (0 : ℝ) ≤ 134400000 * Real.sqrt s := by positivity
    calc 134400000 * Real.sqrt s * 2 ^ stagesM κ *
          ∑ q ∈ Finset.range (stagesM κ), (Real.log (1 / ε) + q) * (1 / 2 : ℝ) ^ q
        ≤ 134400000 * Real.sqrt s * (2 * κ) * (3 * Real.log (1 / ε)) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left h2m hA) (by linarith)
            (Finset.sum_nonneg (fun q _ => by positivity)) (by positivity)
      _ = 806400000 * Real.sqrt s * κ * Real.log (1 / ε) := by ring
  -- the final leaf
  have hfin : ((1000 * dFin s κ ε : ℕ) : ℝ) ≤ 111000 * Real.sqrt s * κ * Real.log (1 / ε) := by
    push_cast
    have h := dFin_le s hs κ ε hκ hε hε1
    linarith
  have hprod0 : 0 ≤ Real.sqrt s * κ * Real.log (1 / ε) := by
    have : 0 ≤ Real.log (1 / ε) := by linarith
    positivity
  unfold walkStepsC
  rw [Nat.cast_add]
  push_cast at hfin ⊢
  linarith

/-! ### The cost of every transcript -/

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s : ℕ}

local notation "V0" => EuclideanSpace ℂ n

/-- The final leaf: at most `1000` attempts of `d_fin` signed steps. -/
theorem finalLeaf_worstCost (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (sv : V0) (κ ε r : ℝ) (w : Lbl → ℕ) (c : ℕ)
    (hc : ∀ σ r d, (runPhys D Ub sv (Tc s κ ε) σ r d).cost w = d * c) :
    (finalLeaf D Ub sv κ ε r).worstCost w ≤ 1000 * (dFin s κ ε * c) := by
  rw [finalLeaf, ODERepeatProtocol.Protocol.repeat_worstCost]
  apply Nat.mul_le_mul_left
  unfold ODERepeatProtocol.TrialFamily.maxCost
  apply Finset.sup_le
  intro j _
  exact (hc 0 r (dFin s κ ε)).le

/-- **Every transcript** of the algorithm performs at most `walkStepsC` signed walk steps, each
of weighted cost `c`. -/
theorem algorithm_worstCost (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (sv : V0) (κ ε : ℝ) (w : Lbl → ℕ) (c : ℕ)
    (hc : ∀ σ r d, (runPhys D Ub sv (Tc s κ ε) σ r d).cost w = d * c) :
    (algorithm D Ub sv κ ε).worstCost w ≤ walkStepsC s κ ε * c := by
  have h := Estimator.stages_cost w (testRun D Ub sv κ ε) (finalLeaf D Ub sv κ ε) (reps κ ε)
    (stagesM κ) κ (fun j => dTest s (stageOf κ j) * c) (fun j r => (hc _ _ _).le)
    (1000 * (dFin s κ ε * c)) (fun r => finalLeaf_worstCost D Ub sv κ ε r w c hc) (stagesM κ) 1
  refine h.trans (le_of_eq ?_)
  unfold walkStepsC
  rw [add_mul, Finset.sum_mul]
  congr 1
  · apply Finset.sum_congr rfl
    intro q _
    ring
  · ring

/-- **Matrix-oracle calls** of every transcript: at most `4.4·10¹⁰ √s κ log(1/ε)`. -/
theorem algorithm_matrix_queries (D : NativeSparseBlockEncoding.Data X n Z s)
    (Ub : X → V0 →L[ℂ] V0) (sv : V0) (κ ε : ℝ) (hκ : 1 ≤ κ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 10) :
    ((algorithm D Ub sv κ ε).worstCost wMat : ℝ) ≤
      44 * 10 ^ 9 * Real.sqrt s * κ * Real.log (1 / ε) := by
  have h := algorithm_worstCost D Ub sv κ ε wMat 54
    (fun σ r d => runPhys_cost_mat D Ub sv _ σ r d)
  have h2 := walkStepsC_le s D.slots_pos κ ε hκ hε hε1
  have h3 : ((algorithm D Ub sv κ ε).worstCost wMat : ℝ) ≤ (walkStepsC s κ ε : ℝ) * 54 := by
    exact_mod_cast h
  have hL := two_le_logInv ε hε hε1
  have hpos : 0 ≤ Real.sqrt s * κ * Real.log (1 / ε) := by
    have : 0 ≤ κ := by linarith
    have : 0 ≤ Real.log (1 / ε) := by linarith
    positivity
  nlinarith

/-- **Calls of the controlled source preparation** (forward and inverse) of every transcript:
at most `1.7·10⁹ √s κ log(1/ε)`. -/
theorem algorithm_source_queries (D : NativeSparseBlockEncoding.Data X n Z s)
    (Ub : X → V0 →L[ℂ] V0) (sv : V0) (κ ε : ℝ) (hκ : 1 ≤ κ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 10) :
    ((algorithm D Ub sv κ ε).worstCost wSrc : ℝ) ≤
      17 * 10 ^ 8 * Real.sqrt s * κ * Real.log (1 / ε) := by
  have h := algorithm_worstCost D Ub sv κ ε wSrc 2
    (fun σ r d => runPhys_cost_src D Ub sv _ σ r d)
  have h2 := walkStepsC_le s D.slots_pos κ ε hκ hε hε1
  have h3 : ((algorithm D Ub sv κ ε).worstCost wSrc : ℝ) ≤ (walkStepsC s κ ε : ℝ) * 2 := by
    exact_mod_cast h
  have hL := two_le_logInv ε hε hε1
  have hpos : 0 ≤ Real.sqrt s * κ * Real.log (1 / ε) := by
    have : 0 ≤ κ := by linarith
    have : 0 ≤ Real.log (1 / ε) := by linarith
    positivity
  nlinarith

end

end ChebyshevLinearSystem
