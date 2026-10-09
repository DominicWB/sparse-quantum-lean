import QLSHoeffding.Schedule

/-!
# The repetition count quoted in Remark `qls:rem:constants`

Remark `qls:rem:constants` quotes "the remaining repetition count of about `5102 log(10/ζ_j)`
per stage test". The count of equation `qls:eq:hoeffding` at the per-test budget `ζ_j/5` is
`n_j = ⌈log(10/ζ_j)/(2 · 0.0099²)⌉` (`repsH_eq_ms`), and `1/(2 · 0.0099²) = 5101.52…`. Since
`ζ_j ≤ ε/1000 ≤ 1/1000` (`zetaMs_le`), `log(10/ζ_j) ≥ log 16 = 4 log 2`
(`four_log_two_le_log_ten_div_zetaMs`), so the ceiling adds less than
`1 ≤ 0.47 log(10/ζ_j)`:

* `repsH_bracket`: `5101 log(10/ζ_j) ≤ n_j ≤ 5102 log(10/ζ_j)` for `0 < ε ≤ 1` and every stage
  `j`.
-/

set_option autoImplicit false

namespace QLSHoeffding

noncomputable section
open SparseLinearSystems Protocol Endpoint

/-- The manuscript's stage budget is at most `ε/1000`. -/
theorem zetaMs_le (κ ε : ℝ) (hε : 0 ≤ ε) (j : ℕ) : zetaMs κ ε j ≤ ε / 1000 := by
  unfold zetaMs
  have h1 : (1 / 2 : ℝ) ^ (stagesM κ - j) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have h0 : 0 ≤ ε / 1000 := by positivity
  calc ε / 1000 * (1 / 2) ^ (stagesM κ - j) ≤ ε / 1000 * 1 := mul_le_mul_of_nonneg_left h1 h0
    _ = ε / 1000 := mul_one _

/-- `log(10/ζ_j) ≥ 4 log 2` for `0 < ε ≤ 1`. -/
theorem four_log_two_le_log_ten_div_zetaMs (κ ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (j : ℕ) :
    4 * Real.log 2 ≤ Real.log (10 / zetaMs κ ε j) := by
  have hz : 0 < zetaMs κ ε j := by unfold zetaMs; positivity
  have hzle := zetaMs_le κ ε hε.le j
  have h16 : (16 : ℝ) ≤ 10 / zetaMs κ ε j := by
    rw [le_div_iff₀ hz]
    linarith
  have e : 4 * Real.log 2 = Real.log 16 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    norm_num
  rw [e]
  exact Real.log_le_log (by norm_num) h16

/-- **The repetition count of Remark `qls:rem:constants`**: for `0 < ε ≤ 1` and every stage `j`,
the count `n_j = ⌈log(10/ζ_j)/(2 · 0.0099²)⌉` of equation `qls:eq:hoeffding` satisfies
`5101 log(10/ζ_j) ≤ n_j ≤ 5102 log(10/ζ_j)`, with `ζ_j = (ε/1000) 2^{j-m}`. -/
theorem repsH_bracket (κ ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (j : ℕ) :
    5101 * Real.log (10 / zetaMs κ ε j) ≤ (repsH κ ε j : ℝ) ∧
      (repsH κ ε j : ℝ) ≤ 5102 * Real.log (10 / zetaMs κ ε j) := by
  have hL := four_log_two_le_log_ten_div_zetaMs κ ε hε hε1 j
  have hl2 := Real.log_two_gt_d9
  norm_num at hl2
  rw [repsH_eq_ms κ ε hε j]
  have hc : (2 * (99 / 10000 : ℝ) ^ 2) = 19602 / 100000000 := by norm_num
  rw [hc]
  have hx : Real.log (10 / zetaMs κ ε j) / (19602 / 100000000) =
      100000000 / 19602 * Real.log (10 / zetaMs κ ε j) := by
    field_simp
  rw [hx]
  have hLnn : 0 ≤ Real.log (10 / zetaMs κ ε j) := by linarith
  have hpos : 0 ≤ 100000000 / 19602 * Real.log (10 / zetaMs κ ε j) := by positivity
  constructor
  · calc 5101 * Real.log (10 / zetaMs κ ε j)
        ≤ 100000000 / 19602 * Real.log (10 / zetaMs κ ε j) := by
          apply mul_le_mul_of_nonneg_right _ hLnn
          norm_num
      _ ≤ _ := Nat.le_ceil _
  · have hceil := Nat.ceil_lt_add_one hpos
    have : 100000000 / 19602 * Real.log (10 / zetaMs κ ε j) + 1 ≤
        5102 * Real.log (10 / zetaMs κ ε j) := by
      nlinarith
    linarith

end

end QLSHoeffding
