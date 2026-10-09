import SparseLinearSystems.Endpoint.Algorithm
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The worst-case query count (equations `qls:eq:main`, `qls:eq:geometriccost`)

Every transcript of `algorithm` performs at most `walkSteps s κ ε` counter-controlled
walk steps (`algorithm_worstCost`): `5 n_j` runs of `T_j` steps at each stage
`j = 1, …, m` and at most `1000` final attempts of `k (N - 1)` steps.  Each walk
step makes `54` matrix-oracle calls and `2` calls of the controlled source
preparation (`runPhys_cost_mat`, `runPhys_cost_src`).

`walkSteps_le` is the explicit form of equation `qls:eq:geometriccost` together
with the final preparation: with `L = log(1/ε)`,

* `T_j ≤ 8250 √s 2^j` (`Ttest_le`) and `N - 1 ≤ 8250 √s κ` (`Nfin_sub_le`);
* `n_j ≤ 210000 (L + m - j)` (`reps_le`) and `k ≤ 2 L` (`kfin_le`);
* `Σ_{j ≤ m} 2^j (L + m - j) ≤ 2^m (2L + 2)` and `2^m ≤ 2κ`;

so `walkSteps ≤ 6·10¹⁰ √s κ log(1/ε)`.  No logarithm of `s` or `κ` appears.
-/

namespace SparseLinearSystems.Endpoint

noncomputable section
open SparseHamiltonian
open ContinuousLinearMap OracleCircuit HilbertAugmentation Augmented SparseBranch LogicalWalk
  Cells Step Run Facts Protocol
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 2048

/-! ### Elementary estimates -/

/-- `log 10 ≥ 2`. -/
theorem two_le_log_ten : (2 : ℝ) ≤ Real.log 10 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have h := Real.exp_one_lt_d9
  have h2 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [Real.exp_one_pow]; norm_num
  have h0 : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
  rw [h2]
  nlinarith

theorem log_ten_le_logInv (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 10) :
    Real.log 10 ≤ Real.log (1 / ε) := by
  apply Real.log_le_log (by norm_num)
  rw [le_div_iff₀ hε]
  linarith

/-- `log(1/ε) ≥ 2` for `ε ≤ 1/10`. -/
theorem two_le_logInv (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 10) : 2 ≤ Real.log (1 / ε) :=
  two_le_log_ten.trans (log_ten_le_logInv ε hε hε1)

/-- `100 / b(g) ≤ 8250 √s / g` for `s ≥ 1`, `0 < g ≤ 1`. -/
theorem hundred_div_bLow_le (s g : ℝ) (hs : 1 ≤ s) (hg0 : 0 < g) (hg1 : g ≤ 1) :
    100 / bLow s g ≤ 8250 * Real.sqrt s / g := by
  have hsq : 1 ≤ Real.sqrt s := Real.one_le_sqrt.mpr hs
  have hchi0 : 0 < chi s g := by unfold chi; positivity
  have hchi1 : chi s g ≤ 1 := by
    unfold chi
    rw [div_le_one (by positivity)]
    nlinarith
  have hroot : Real.sqrt (1 + chi s g ^ 2) ≤ 2 := by
    rw [Real.sqrt_le_left (by norm_num)]
    nlinarith
  have hc : 8250 * Real.sqrt s * chi s g = 200 * g := by
    unfold chi
    field_simp
    ring
  unfold bLow
  rw [div_div_eq_mul_div, div_le_div_iff₀ hchi0 hg0, hc]
  nlinarith

/-- `max 1 ⌈y⌉ - 1 ≤ y`. -/
theorem ceil_pred_le (y : ℝ) (hy : 0 ≤ y) : ((max 1 ⌈y⌉₊ - 1 : ℕ) : ℝ) ≤ y := by
  rcases Nat.eq_zero_or_pos ⌈y⌉₊ with h | h
  · rw [h]
    norm_num
    exact hy
  · rw [max_eq_right h, Nat.cast_sub h, Nat.cast_one]
    linarith [Nat.ceil_lt_add_one hy]

/-- Test walk steps: `T_j ≤ 8250 √s 2^j`. -/
theorem Ttest_le (s : ℕ) (hs : 0 < s) (j : ℕ) :
    (Ttest s j : ℝ) ≤ 8250 * Real.sqrt s * 2 ^ j := by
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hb := bLow_pos (s : ℝ) (sig j) (by linarith) (sig_pos j)
  have h1 := ceil_pred_le (100 / bLow (s : ℝ) (sig j)) (by positivity)
  have h2 := hundred_div_bLow_le (s : ℝ) (sig j) hs1 (sig_pos j) (sig_le_one j)
  have h3 : 8250 * Real.sqrt s / sig j = 8250 * Real.sqrt s * 2 ^ j := by
    unfold sig
    rw [one_div_pow, div_div_eq_mul_div, div_one]
  unfold Ttest Ntest
  linarith

/-- Final filter length: `N - 1 ≤ 8250 √s κ`. -/
theorem Nfin_sub_le (s : ℕ) (hs : 0 < s) (κ : ℝ) (hκ : 1 ≤ κ) :
    ((Nfin s κ - 1 : ℕ) : ℝ) ≤ 8250 * Real.sqrt s * κ := by
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hκ0 : 0 < κ := by linarith
  have hb := bLow_pos (s : ℝ) (1 / κ) (by linarith) (by positivity)
  have h1 := ceil_pred_le (100 / bLow (s : ℝ) (1 / κ)) (by positivity)
  have h2 := hundred_div_bLow_le (s : ℝ) (1 / κ) hs1 (by positivity)
    (by rw [div_le_one hκ0]; exact hκ)
  have h3 : 8250 * Real.sqrt s / (1 / κ) = 8250 * Real.sqrt s * κ := by
    rw [div_div_eq_mul_div, div_one]
  unfold Nfin
  linarith

/-- The final filter power: `k ≤ 2 log(1/ε)`. -/
theorem kfin_le (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 10) :
    (kfin ε : ℝ) ≤ 2 * Real.log (1 / ε) := by
  have hL2 := two_le_logInv ε hε hε1
  have hinv : 10 ≤ 1 / ε := by rw [le_div_iff₀ hε]; linarith
  have hN1 : 1 < ⌈1000 / ε⌉₊ := by
    rw [Nat.lt_ceil, lt_div_iff₀ hε]
    push_cast
    linarith
  have hk := Nat.pow_pred_clog_lt_self (by norm_num : 1 < 100) hN1
  have hkpos := Nat.clog_pos (by norm_num : 1 < 100) hN1
  have hNle : (⌈1000 / ε⌉₊ : ℝ) < 1000 / ε + 1 := Nat.ceil_lt_add_one (by positivity)
  have hpow5 : 1000 / ε + 1 ≤ (1 / ε) ^ 5 := by
    have h4 : (10 : ℝ) ^ 4 ≤ (1 / ε) ^ 4 := pow_le_pow_left₀ (by norm_num) hinv 4
    have h1 : (1 : ℝ) ≤ 1 / ε := by linarith
    have hq : 1000 / ε = 1000 * (1 / ε) := by ring
    calc 1000 / ε + 1 ≤ 1001 * (1 / ε) := by rw [hq]; linarith
      _ ≤ (1 / ε) ^ 4 * (1 / ε) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          linarith
      _ = (1 / ε) ^ 5 := by ring
  have hlt : (100 : ℝ) ^ (Nat.clog 100 ⌈1000 / ε⌉₊).pred < (1 / ε) ^ 5 := by
    have h : ((100 ^ (Nat.clog 100 ⌈1000 / ε⌉₊).pred : ℕ) : ℝ) < ⌈1000 / ε⌉₊ := by
      exact_mod_cast hk
    push_cast at h
    linarith
  have hlog := Real.log_lt_log (by positivity) hlt
  rw [Real.log_pow, Real.log_pow] at hlog
  have h100 : 4 ≤ Real.log 100 := by
    have : Real.log 100 = 2 * Real.log 10 := by
      rw [show (100 : ℝ) = 10 ^ 2 by norm_num, Real.log_pow]
      norm_num
    linarith [two_le_log_ten]
  have hpred0 : (0 : ℝ) ≤ ((Nat.clog 100 ⌈1000 / ε⌉₊).pred : ℕ) := Nat.cast_nonneg _
  have hk' : (((Nat.clog 100 ⌈1000 / ε⌉₊).pred : ℕ) : ℝ) * 4 < 5 * Real.log (1 / ε) := by
    have := mul_le_mul_of_nonneg_left h100 hpred0
    push_cast at hlog
    linarith
  have hsucc : (kfin ε : ℝ) = (((Nat.clog 100 ⌈1000 / ε⌉₊).pred : ℕ) : ℝ) + 1 := by
    have e : kfin ε = (Nat.clog 100 ⌈1000 / ε⌉₊).pred + 1 :=
      (Nat.succ_pred_eq_of_pos hkpos).symm
    rw [e]
    push_cast
    ring
  rw [hsucc]
  linarith

/-- Fresh runs per candidate: `n_j ≤ 210000 (log(1/ε) + m - j)`. -/
theorem reps_le (κ ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 10) (j : ℕ) :
    (reps κ ε j : ℝ) ≤ 210000 * (Real.log (1 / ε) + ((stagesM κ - j : ℕ) : ℝ)) := by
  have hL2 := two_le_logInv ε hε hε1
  have hL10 := log_ten_le_logInv ε hε hε1
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
  have hlog2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hd0 : (0 : ℝ) ≤ ((stagesM κ - j : ℕ) : ℝ) := Nat.cast_nonneg _
  have hle : Real.log (2 / zeta κ ε j) ≤ 5 * Real.log (1 / ε) + ((stagesM κ - j : ℕ) : ℝ) := by
    rw [hlogz]
    have := mul_le_mul_of_nonneg_left hlog2 hd0
    linarith
  have htacc : Estimator.tAcc ^ 2 = 9801 / 100000000 := by
    unfold Estimator.tAcc
    norm_num
  have hX : 4 * Real.log (2 / zeta κ ε j) / Estimator.tAcc ^ 2 ≤
      40813 * (5 * Real.log (1 / ε) + ((stagesM κ - j : ℕ) : ℝ)) := by
    rw [htacc, div_le_iff₀ (by norm_num)]
    nlinarith
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ 4 * Real.log (2 / zeta κ ε j) / Estimator.tAcc ^ 2 by
    rw [htacc]
    have : 0 ≤ Real.log (2 / zeta κ ε j) := by
      rw [hlogz]
      have := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
      have := mul_nonneg hd0 this
      linarith [two_le_log_ten]
    positivity)
  unfold reps
  linarith

/-- `Σ_{q < m} q 2^{-q} + 2 (m + 1) 2^{-m} = 2`. -/
theorem sum_mul_half_pow (m : ℕ) :
    ∑ q ∈ Finset.range m, (q : ℝ) * (1 / 2) ^ q + 2 * ((m : ℝ) + 1) * (1 / 2) ^ m = 2 := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [Finset.sum_range_succ, pow_succ]
    push_cast
    linear_combination ih

/-- `2^m ≤ 2κ` for `m = ⌈log₂ ⌈κ⌉⌉`. -/
theorem two_pow_stages_le (κ : ℝ) (hκ : 1 ≤ κ) : (2 : ℝ) ^ stagesM κ ≤ 2 * κ := by
  unfold stagesM
  rcases Nat.lt_or_ge 1 ⌈κ⌉₊ with h | h
  · have hp := Nat.pow_pred_clog_lt_self (by norm_num : 1 < 2) h
    have hpos := Nat.clog_pos (by norm_num : 1 < 2) h
    have h1 : ((2 ^ (Nat.clog 2 ⌈κ⌉₊).pred : ℕ) : ℝ) + 1 ≤ ⌈κ⌉₊ := by exact_mod_cast hp
    have h2 := Nat.ceil_lt_add_one (show 0 ≤ κ by linarith)
    have h3 : (2 : ℝ) ^ Nat.clog 2 ⌈κ⌉₊ = 2 * 2 ^ (Nat.clog 2 ⌈κ⌉₊).pred := by
      conv_lhs => rw [← Nat.succ_pred_eq_of_pos hpos]
      rw [pow_succ]
      ring
    push_cast at h1
    rw [h3]
    linarith
  · rw [Nat.clog_of_right_le_one h]
    norm_num
    linarith

/-! ### The step count -/

/-- Walk steps along any transcript: `5 n_j` tests of `T_j` steps at each stage
and at most `1000` final attempts of `k (N - 1)` steps. -/
def walkSteps (s : ℕ) (κ ε : ℝ) : ℕ :=
  (∑ q ∈ Finset.range (stagesM κ),
    5 * (reps κ ε (stagesM κ - q) * Ttest s (stageOf κ (stagesM κ - q)))) + 1000 * Tfin s κ ε

/-- **Equation `qls:eq:geometriccost` with the final preparation**:
`walkSteps ≤ 6·10¹⁰ √s κ log(1/ε)`. -/
theorem walkSteps_le (s : ℕ) (hs : 0 < s) (κ ε : ℝ) (hκ : 1 ≤ κ) (hε : 0 < ε)
    (hε1 : ε ≤ 1 / 10) :
    (walkSteps s κ ε : ℝ) ≤ 6 * 10 ^ 10 * Real.sqrt s * κ * Real.log (1 / ε) := by
  have hL2 := two_le_logInv ε hε hε1
  have hsq0 : 0 ≤ Real.sqrt s := Real.sqrt_nonneg _
  have hκ0 : 0 < κ := by linarith
  -- one stage
  have hterm : ∀ q ∈ Finset.range (stagesM κ),
      5 * ((reps κ ε (stagesM κ - q) : ℝ) * (Ttest s (stageOf κ (stagesM κ - q)) : ℝ)) ≤
        8662500000 * Real.sqrt s * 2 ^ stagesM κ *
          ((Real.log (1 / ε) + q) * (1 / 2) ^ q) := by
    intro q hq
    have hqm : q < stagesM κ := Finset.mem_range.mp hq
    rw [stageOf_of_le κ (stagesM κ - q) (Nat.sub_le _ _)]
    have hr := reps_le κ ε hε hε1 (stagesM κ - q)
    rw [show stagesM κ - (stagesM κ - q) = q by omega] at hr
    have ht := Ttest_le s hs (stagesM κ - q)
    have hpow : (2 : ℝ) ^ (stagesM κ - q) = 2 ^ stagesM κ * (1 / 2) ^ q := by
      have e : (2 : ℝ) ^ stagesM κ = 2 ^ (stagesM κ - q) * 2 ^ q := by
        rw [← pow_add, Nat.sub_add_cancel hqm.le]
      rw [e, one_div_pow, mul_assoc, mul_one_div_cancel (by positivity), mul_one]
    rw [hpow] at ht
    have hr0 : (0 : ℝ) ≤ reps κ ε (stagesM κ - q) := Nat.cast_nonneg _
    have ht0 : (0 : ℝ) ≤ Ttest s (stagesM κ - q) := Nat.cast_nonneg _
    have hprod := mul_le_mul hr ht ht0 (by positivity)
    calc 5 * ((reps κ ε (stagesM κ - q) : ℝ) * (Ttest s (stagesM κ - q) : ℝ))
        ≤ 5 * (210000 * (Real.log (1 / ε) + (q : ℝ)) *
            (8250 * Real.sqrt s * (2 ^ stagesM κ * (1 / 2) ^ q))) := by linarith
      _ = 8662500000 * Real.sqrt s * 2 ^ stagesM κ *
            ((Real.log (1 / ε) + q) * (1 / 2) ^ q) := by ring
  have hsum : ∑ q ∈ Finset.range (stagesM κ),
      5 * ((reps κ ε (stagesM κ - q) : ℝ) * (Ttest s (stageOf κ (stagesM κ - q)) : ℝ)) ≤
      8662500000 * Real.sqrt s * 2 ^ stagesM κ *
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
  have hest : 8662500000 * Real.sqrt s * 2 ^ stagesM κ *
      ∑ q ∈ Finset.range (stagesM κ), (Real.log (1 / ε) + q) * (1 / 2 : ℝ) ^ q ≤
      51975000000 * Real.sqrt s * κ * Real.log (1 / ε) := by
    have hA : (0 : ℝ) ≤ 8662500000 * Real.sqrt s := by positivity
    have hB : (0 : ℝ) ≤ 2 ^ stagesM κ := by positivity
    calc 8662500000 * Real.sqrt s * 2 ^ stagesM κ *
          ∑ q ∈ Finset.range (stagesM κ), (Real.log (1 / ε) + q) * (1 / 2 : ℝ) ^ q
        ≤ 8662500000 * Real.sqrt s * (2 * κ) * (3 * Real.log (1 / ε)) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left h2m hA) (by linarith)
            (Finset.sum_nonneg (fun q _ => by positivity)) (by positivity)
      _ = 51975000000 * Real.sqrt s * κ * Real.log (1 / ε) := by ring
  -- the final leaf
  have hfin : ((1000 * Tfin s κ ε : ℕ) : ℝ) ≤ 16500000 * Real.sqrt s * κ * Real.log (1 / ε) := by
    unfold Tfin
    push_cast
    have hk := kfin_le ε hε hε1
    have hN := Nfin_sub_le s hs κ hκ
    have hN0 : (0 : ℝ) ≤ ((Nfin s κ - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hprod := mul_le_mul hk hN hN0 (by positivity)
    calc 1000 * ((kfin ε : ℝ) * ((Nfin s κ - 1 : ℕ) : ℝ))
        ≤ 1000 * (2 * Real.log (1 / ε) * (8250 * Real.sqrt s * κ)) := by linarith
      _ = 16500000 * Real.sqrt s * κ * Real.log (1 / ε) := by ring
  have hprod0 : 0 ≤ Real.sqrt s * κ * Real.log (1 / ε) := by
    have : 0 ≤ Real.log (1 / ε) := by linarith
    positivity
  unfold walkSteps
  rw [Nat.cast_add]
  push_cast at hfin ⊢
  linarith

/-! ### The cost of every transcript -/

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s : ℕ}

local notation "V0" => EuclideanSpace ℂ n

/-- The final leaf: at most `1000` attempts of `k (N - 1)` steps. -/
theorem finalLeaf_worstCost (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (sv : V0) (κ ε r : ℝ) (w : Lbl → ℕ) (c : ℕ)
    (hc : ∀ σ r t, (runPhys D Ub sv (Tw s κ ε) σ r t).cost w = t * c) :
    (finalLeaf D Ub sv κ ε r).worstCost w ≤ 1000 * (Tfin s κ ε * c) := by
  rw [finalLeaf, ODERepeatProtocol.Protocol.repeat_worstCost]
  apply Nat.mul_le_mul_left
  unfold ODERepeatProtocol.TrialFamily.maxCost
  apply Finset.sup_le
  intro j _
  exact (hc 0 r (Tfin s κ ε)).le

/-- **Every transcript** of the algorithm performs at most `walkSteps` walk steps,
each of weighted cost `c`. -/
theorem algorithm_worstCost (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (sv : V0) (κ ε : ℝ) (w : Lbl → ℕ) (c : ℕ)
    (hc : ∀ σ r t, (runPhys D Ub sv (Tw s κ ε) σ r t).cost w = t * c) :
    (algorithm D Ub sv κ ε).worstCost w ≤ walkSteps s κ ε * c := by
  have h := Estimator.stages_cost w (testRun D Ub sv κ ε) (finalLeaf D Ub sv κ ε) (reps κ ε)
    (stagesM κ) κ (fun j => Ttest s (stageOf κ j) * c) (fun j r => (hc _ _ _).le)
    (1000 * (Tfin s κ ε * c)) (fun r => finalLeaf_worstCost D Ub sv κ ε r w c hc) (stagesM κ) 1
  refine h.trans (le_of_eq ?_)
  unfold walkSteps
  rw [add_mul, Finset.sum_mul]
  congr 1
  · apply Finset.sum_congr rfl
    intro q _
    ring
  · ring

/-- **Matrix-oracle calls** of every transcript: at most `4·10¹² √s κ log(1/ε)`. -/
theorem algorithm_matrix_queries (D : NativeSparseBlockEncoding.Data X n Z s)
    (Ub : X → V0 →L[ℂ] V0) (sv : V0) (κ ε : ℝ) (hκ : 1 ≤ κ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 10) :
    ((algorithm D Ub sv κ ε).worstCost wMat : ℝ) ≤
      4 * 10 ^ 12 * Real.sqrt s * κ * Real.log (1 / ε) := by
  have h := algorithm_worstCost D Ub sv κ ε wMat 54
    (fun σ r t => runPhys_cost_mat D Ub sv _ σ r t)
  have h2 := walkSteps_le s D.slots_pos κ ε hκ hε hε1
  have h3 : ((algorithm D Ub sv κ ε).worstCost wMat : ℝ) ≤ (walkSteps s κ ε : ℝ) * 54 := by
    exact_mod_cast h
  have hL := two_le_logInv ε hε hε1
  have hpos : 0 ≤ Real.sqrt s * κ * Real.log (1 / ε) := by
    have : 0 ≤ κ := by linarith
    have : 0 ≤ Real.log (1 / ε) := by linarith
    positivity
  nlinarith

/-- **Calls of the controlled source preparation** (forward and inverse) of every
transcript: at most `2·10¹¹ √s κ log(1/ε)`. -/
theorem algorithm_source_queries (D : NativeSparseBlockEncoding.Data X n Z s)
    (Ub : X → V0 →L[ℂ] V0) (sv : V0) (κ ε : ℝ) (hκ : 1 ≤ κ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 10) :
    ((algorithm D Ub sv κ ε).worstCost wSrc : ℝ) ≤
      2 * 10 ^ 11 * Real.sqrt s * κ * Real.log (1 / ε) := by
  have h := algorithm_worstCost D Ub sv κ ε wSrc 2
    (fun σ r t => runPhys_cost_src D Ub sv _ σ r t)
  have h2 := walkSteps_le s D.slots_pos κ ε hκ hε hε1
  have h3 : ((algorithm D Ub sv κ ε).worstCost wSrc : ℝ) ≤ (walkSteps s κ ε : ℝ) * 2 := by
    exact_mod_cast h
  have hL := two_le_logInv ε hε hε1
  have hpos : 0 ≤ Real.sqrt s * κ * Real.log (1 / ε) := by
    have : 0 ≤ κ := by linarith
    have : 0 ≤ Real.log (1 / ε) := by linarith
    positivity
  nlinarith

end

end SparseLinearSystems.Endpoint
