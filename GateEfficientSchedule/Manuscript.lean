import GateEfficientSchedule.Depth
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# The manuscript's filter schedule (equation `hs:eq:gate-schedule`)

The manuscript fixes the filter repetitions and the filter degree as

`k = ⌈4W/Q + log₂(4096/ε)⌉`,   `d = k (b_av - 1)`,   `b_av = 32 Q`,

and takes the filter accuracy `δ = ε/8` (equation `hs:eq:kchoice` with `δ = ε/8`). The released
formal schedule is `k_Lean = 1 + ⌈4W/Q + 2 log(3/ε)⌉`, `d_Lean = k_Lean (⌈32Q⌉ - 1)`; neither
dominates the other for all `ε`.

* `depthMs`, `degreeMs`: the manuscript's `k` and `d = k (⌈32Q⌉ - 1)`; `degreeMs_of_nat`: when
  `32 Q = b` is a natural number (the manuscript's `b_av`), `d = k (b - 1)`, the printed formula;
  `degreeMs_natCast`: at the manuscript's integer `Q`, `d = k (32 Q - 1)`.
* `depthMs_admissible`: the manuscript's `k` is an admissible depth (`GateSchedule.Admissible`)
  at the filter accuracy `ε/8`, for every `Q ≥ 1`, `W ≥ 0` and `0 < ε ≤ 1`: `k ≥ 1`, the decay
  `prefactor(Q, W) (1/4)^k ≤ ε/8` (through `SharpFilterSchedule.log_prefactor_ratio_le` and
  `FilterDepth.decay_le_of_log_depth`), and the smoothing slack `6W ≤ k (⌈32Q⌉ - 1)`.
* `degreeMs_le`: `d ≤ 128 W + 32 Q (log₂(4096/ε) + 1)`.
-/

set_option autoImplicit false

namespace SparseHamiltonian.GateSchedule

noncomputable section

/-- **The manuscript's filter repetitions** `k = ⌈4W/Q + log₂(4096/ε)⌉`. -/
def depthMs (Q W ε : ℝ) : ℕ := ⌈4 * W / Q + Real.logb 2 (4096 / ε)⌉₊

/-- **The manuscript's filter degree** `d = k (⌈32Q⌉ - 1)`. -/
def degreeMs (Q W ε : ℝ) : ℕ := depthMs Q W ε * (SharpFilterSchedule.length Q - 1)

/-- The filter length at `Q = b/32` is `b`. -/
theorem length_of_nat (b : ℕ) : SharpFilterSchedule.length ((b : ℝ) / 32) = b := by
  change ⌈32 * ((b : ℝ) / 32)⌉₊ = b
  rw [show 32 * ((b : ℝ) / 32) = b by ring, Nat.ceil_natCast]

/-- **The printed degree**: when `32 Q = b` is a natural number (the manuscript's `b_av`),
`d = k (b - 1)`. -/
theorem degreeMs_of_nat (b : ℕ) (W ε : ℝ) :
    degreeMs ((b : ℝ) / 32) W ε = depthMs ((b : ℝ) / 32) W ε * (b - 1) := by
  rw [degreeMs, length_of_nat]

/-- The filter length at a natural `Q` is `b = 32 Q`. -/
theorem length_natCast (n : ℕ) : SharpFilterSchedule.length (n : ℝ) = 32 * n := by
  change ⌈32 * (n : ℝ)⌉₊ = 32 * n
  rw [show 32 * (n : ℝ) = ((32 * n : ℕ) : ℝ) by push_cast; ring, Nat.ceil_natCast]

/-- **The printed degree at the manuscript's integer `Q`** (`Q = ⌈max{1, γ√s}⌉`,
eq. `ov:eq:Q`): `d = k (32 Q - 1)`. -/
theorem degreeMs_natCast (n : ℕ) (W ε : ℝ) :
    degreeMs (n : ℝ) W ε = depthMs (n : ℝ) W ε * (32 * n - 1) := by
  rw [degreeMs, length_natCast]

theorem logb_4096_le (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) : 12 ≤ Real.logb 2 (4096 / ε) := by
  have h1 : (4096 : ℝ) ≤ 4096 / ε := by
    rw [le_div_iff₀ hε]
    nlinarith
  have h2 : Real.logb 2 (4096 : ℝ) = 12 := by
    have h4096 : (4096 : ℝ) = 2 ^ (12 : ℕ) := by norm_num
    rw [h4096, Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one]
    norm_num
  rw [← h2]
  exact Real.logb_le_logb_of_le (by norm_num) (by norm_num) h1

theorem depthMs_ge (Q W ε : ℝ) : 4 * W / Q + Real.logb 2 (4096 / ε) ≤ (depthMs Q W ε : ℝ) :=
  Nat.le_ceil _

theorem depthMs_lt (Q W ε : ℝ) (hQ : 1 ≤ Q) (hW : 0 ≤ W) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (depthMs Q W ε : ℝ) < 4 * W / Q + Real.logb 2 (4096 / ε) + 1 := by
  have h12 := logb_4096_le ε hε hε1
  have hx : 0 ≤ 4 * W / Q := div_nonneg (by linarith) (by linarith)
  exact Nat.ceil_lt_add_one (by linarith)

/-- **The manuscript's filter repetitions are an admissible depth** at the filter accuracy
`ε/8`. -/
theorem depthMs_admissible (Q W ε : ℝ) (hQ : 1 ≤ Q) (hW : 0 ≤ W) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Admissible Q W (ε / 8) (depthMs Q W ε) where
  pos := by
    have h12 := logb_4096_le ε hε hε1
    have hx : 0 ≤ 4 * W / Q := div_nonneg (by linarith) (by linarith)
    exact Nat.one_le_ceil_iff.mpr (by linarith)
  decay := by
    have hδ : 0 < ε / 8 := by positivity
    have hC := FilterSchedule.prefactor_pos Q W hQ hW
    have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
      have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at h ⊢
      exact h
    have hlog2pos : 0 < Real.log (2 : ℝ) := by linarith
    have hbound := SharpFilterSchedule.log_prefactor_ratio_le Q W (ε / 8) hQ hW hδ
    have hk := depthMs_ge Q W ε
    have hQ0 : 0 < Q := by linarith
    have hx : 0 ≤ W / Q := div_nonneg hW hQ0.le
    -- `log(8/ε) ≤ log(4096/ε)`
    have hlogle : Real.log (1 / (ε / 8)) ≤ Real.log (4096 / ε) := by
      apply Real.log_le_log (by positivity)
      rw [one_div_div]
      exact div_le_div_of_nonneg_right (by norm_num) hε.le
    have hhalf : FilterSchedule.prefactor Q W * (1 / 2 : ℝ) ^ depthMs Q W ε ≤ ε / 8 := by
      apply FilterDepth.decay_le_of_log_depth _ _ hC hδ
      rw [div_le_iff₀ hlog2pos]
      have hlogb : Real.logb 2 (4096 / ε) * Real.log 2 = Real.log (4096 / ε) := by
        rw [Real.logb, div_mul_cancel₀ _ hlog2pos.ne']
      have h1 : (4 * W / Q + Real.logb 2 (4096 / ε)) * Real.log 2 ≤
          (depthMs Q W ε : ℝ) * Real.log 2 := mul_le_mul_of_nonneg_right hk hlog2pos.le
      have h2 : 2 * W / Q ≤ 4 * W / Q * Real.log 2 := by
        have e1 : 2 * W / Q = 2 * (W / Q) := by ring
        have e2 : 4 * W / Q * Real.log 2 = 4 * (W / Q) * Real.log 2 := by ring
        rw [e1, e2]
        nlinarith
      unfold SharpFilterSchedule.logBudget at hbound
      nlinarith
    refine le_trans ?_ hhalf
    apply mul_le_mul_of_nonneg_left _ hC.le
    exact pow_le_pow_left₀ (by norm_num) (by norm_num) _
  slack := by
    have hQ0 : 0 < Q := by linarith
    have h12 := logb_4096_le ε hε hε1
    have hk := depthMs_ge Q W ε
    have hklo : 4 * W / Q ≤ (depthMs Q W ε : ℝ) := by linarith
    have hlen : 1 ≤ SharpFilterSchedule.length Q := by
      change 1 ≤ ⌈32 * Q⌉₊
      apply Nat.one_le_ceil_iff.mpr
      linarith
    have hlenlo : 31 * Q ≤ ((SharpFilterSchedule.length Q - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub hlen, Nat.cast_one]
      have h := SharpFilterSchedule.length_ge Q
      linarith
    have hprod := mul_le_mul hklo hlenlo (show 0 ≤ 31 * Q by positivity)
      (show (0 : ℝ) ≤ depthMs Q W ε by positivity)
    have heq : (4 * W / Q) * (31 * Q) = 124 * W := by
      field_simp
      ring
    rw [heq] at hprod
    linarith

/-- **The manuscript's degree bound**: `d ≤ 128 W + 32 Q (log₂(4096/ε) + 1)`. -/
theorem degreeMs_le (Q W ε : ℝ) (hQ : 1 ≤ Q) (hW : 0 ≤ W) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (degreeMs Q W ε : ℝ) ≤ 128 * W + 32 * Q * (Real.logb 2 (4096 / ε) + 1) := by
  have hQ0 : 0 < Q := by linarith
  have hk := (depthMs_lt Q W ε hQ hW hε hε1).le
  have hL := (SharpFilterSchedule.length_sub_one_bounds Q hQ).2.le
  have h12 := logb_4096_le ε hε hε1
  have hx : 0 ≤ 4 * W / Q := div_nonneg (by linarith) (by linarith)
  have hprod := mul_le_mul hk hL (Nat.cast_nonneg _) (by linarith)
  have heq : (4 * W / Q + Real.logb 2 (4096 / ε) + 1) * (32 * Q) =
      128 * W + 32 * Q * (Real.logb 2 (4096 / ε) + 1) := by
    field_simp
    ring
  rw [heq] at hprod
  simpa only [degreeMs, Nat.cast_mul] using hprod

end

end SparseHamiltonian.GateSchedule
