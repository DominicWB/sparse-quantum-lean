import QLSHoeffding.Estimator
import SparseLinearSystems.Endpoint.Cost

/-!
# The repetition schedule of equation `qls:eq:hoeffding`

The manuscript gives the five tests of stage `j` the combined failure budget
`ζ_j = (ε/1000) 2^{j-m}` (`zetaMs`), so each test has budget `ζ_j/5`, and estimates every test
probability within `t = 0.0099` with Hoeffding's count
`n_rep = ⌈log(2/ζ)/(2t²)⌉` at `ζ = ζ_j/5`, that is `⌈log(10/ζ_j)/(2 · 0.0099²)⌉`.

The released per-test budget is `Endpoint.zeta κ ε j = (ε/5000) 2^{-(m-j)} = ζ_j/5`
(`zeta_eq_zetaMs`), so the allocation agrees; only the count differs (the released
`Endpoint.reps = ⌈4 log(2/ζ)/t²⌉`, eight times larger).

* `repsH`: the manuscript's count `⌈log(2/ζ)/(2t²)⌉` at the released per-test budget;
  `repsH_eq_ms`: `repsH κ ε j = ⌈log(10/ζ_j)/(2 · 0.0099²)⌉` with the manuscript's stage budget;
* `repsH_tailOK`: the counts meet the tail budgets (Hoeffding's inequality);
* `repsH_le`: `n_j ≤ 25509 log(1/ε) + 3537 (m - j)` (the released `Endpoint.reps_le` has
  `210000 (log(1/ε) + m - j)`).
-/

set_option autoImplicit false

namespace QLSHoeffding

noncomputable section
open SparseLinearSystems Protocol Endpoint

/-- **The manuscript's stage budget** `ζ_j = (ε/1000) 2^{j-m}` of the five tests of stage `j`
(written `(ε/1000) (1/2)^{m-j}`). -/
def zetaMs (κ ε : ℝ) (j : ℕ) : ℝ := ε / 1000 * (1 / 2) ^ (stagesM κ - j)

/-- The released per-test budget is the manuscript's stage budget shared by the five tests. -/
theorem zeta_eq_zetaMs (κ ε : ℝ) (j : ℕ) : zeta κ ε j = zetaMs κ ε j / 5 := by
  unfold zeta zetaMs
  ring

/-- **The repetition count of equation `qls:eq:hoeffding`**: `n_j = ⌈log(2/ζ)/(2t²)⌉` fresh runs
per candidate at stage `j`, with `t = 0.0099` and the per-test budget `ζ = ζ_j/5`. -/
def repsH (κ ε : ℝ) (j : ℕ) : ℕ := ⌈Real.log (2 / zeta κ ε j) / (2 * Estimator.tAcc ^ 2)⌉₊

theorem repsH_spec (κ ε : ℝ) (j : ℕ) :
    Real.log (2 / zeta κ ε j) / (2 * Estimator.tAcc ^ 2) ≤ repsH κ ε j :=
  Nat.le_ceil _

/-- **The count in the manuscript's notation**: `n_j = ⌈log(10/ζ_j)/(2 · 0.0099²)⌉`. -/
theorem repsH_eq_ms (κ ε : ℝ) (hε : 0 < ε) (j : ℕ) :
    repsH κ ε j = ⌈Real.log (10 / zetaMs κ ε j) / (2 * (99 / 10000 : ℝ) ^ 2)⌉₊ := by
  have hz : 0 < zetaMs κ ε j := by unfold zetaMs; positivity
  have e : 2 / zeta κ ε j = 10 / zetaMs κ ε j := by
    rw [zeta_eq_zetaMs]
    field_simp
    ring
  unfold repsH Estimator.tAcc
  rw [e]

/-- **Hoeffding's counts meet the tail budgets** `ζ = zeta κ ε j`. -/
theorem repsH_tailOK (κ ε : ℝ) (hε : 0 < ε) (j : ℕ) :
    TailOK (repsH κ ε j) Estimator.tAcc (zeta κ ε j) :=
  tailOK_hoeffding (by unfold Estimator.tAcc; norm_num) (zeta_pos κ ε hε j) (repsH_spec κ ε j)

/-- **Fresh runs per candidate**: `n_j ≤ 25509 log(1/ε) + 3537 (m - j)`. -/
theorem repsH_le (κ ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 10) (j : ℕ) :
    (repsH κ ε j : ℝ) ≤ 25509 * Real.log (1 / ε) + 3537 * ((stagesM κ - j : ℕ) : ℝ) := by
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
  have hlog2 : Real.log 2 < 6932 / 10000 := by
    have := Real.log_two_lt_d9
    norm_num at this
    linarith
  have hlog2' : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hd0 : (0 : ℝ) ≤ ((stagesM κ - j : ℕ) : ℝ) := Nat.cast_nonneg _
  have htacc : 2 * Estimator.tAcc ^ 2 = 19602 / 100000000 := by
    unfold Estimator.tAcc
    norm_num
  have hX : Real.log (2 / zeta κ ε j) / (2 * Estimator.tAcc ^ 2) ≤
      25509 * Real.log (1 / ε) + 3537 * ((stagesM κ - j : ℕ) : ℝ) - 1 := by
    rw [htacc, div_le_iff₀ (by norm_num), hlogz]
    have := mul_le_mul_of_nonneg_left hlog2.le hd0
    nlinarith
  have hpos : 0 ≤ Real.log (2 / zeta κ ε j) / (2 * Estimator.tAcc ^ 2) := by
    rw [htacc, hlogz]
    have := mul_nonneg hd0 hlog2'.le
    have : (0 : ℝ) ≤ 4 * Real.log 10 + Real.log (1 / ε) +
        ((stagesM κ - j : ℕ) : ℝ) * Real.log 2 := by linarith
    positivity
  have hceil := Nat.ceil_lt_add_one hpos
  unfold repsH
  linarith

end

end QLSHoeffding
