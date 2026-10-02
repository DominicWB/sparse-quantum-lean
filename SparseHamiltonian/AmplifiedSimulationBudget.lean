import SparseHamiltonian.ActualDilatedBands

/-!
# Explicit logarithmic simplification of the native simulation budget

The constants include sixfold native involution dilation and both fixed clock
links. The scalar endpoint is designed for the actual family resource bounds;
it does not posit an algorithm or an approximation polynomial.
-/
namespace SparseHamiltonian.AmplifiedSimulationBudget

noncomputable section
open AmplifiedBandPrecision

/-- The common logarithmic envelope absorbs the filter's own logarithm. -/
theorem filter_log_le (s η t ε Q W : ℝ) (hs : 1 ≤ s) (hη : 0 ≤ η)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hQ0 : 0 ≤ Q) (hW0 : 0 ≤ W)
    (hQ : Q ≤ 162 * Real.sqrt s * logBudget s η t ε)
    (hW : W ≤ 319488 * |t| * η * Real.sqrt s * (logBudget s η t ε) ^ 2) :
    Real.log (3 * (Q + W + 2) / (ε / 4)) ≤ 23 * logBudget s η t ε := by
  let B := logBudget s η t ε
  let T := |t| * η
  let R := (T + 1) * (s + 1)
  let G := 120 * R / ε
  have hB : 1 ≤ B := logBudget_ge_one s η t ε hs hη hε hε1
  have hB0 : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hT : 0 ≤ T := mul_nonneg (abs_nonneg t) hη
  have hs0 : 0 ≤ s := le_trans zero_le_one hs
  have hR : 1 ≤ R := one_le_mul_of_one_le_of_one_le (by linarith)
    (by linarith)
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hG0 : 0 < G := by dsimp [G]; positivity
  have hB2 : B ≤ B ^ 2 := by nlinarith
  have hroot : Real.sqrt s ≤ s + 1 :=
    (Real.sqrt_le_self_iff.mpr (Or.inr hs)).trans (by linarith)
  have hrootR : Real.sqrt s ≤ R := by
    apply hroot.trans
    dsimp [R]
    exact le_mul_of_one_le_left (by linarith) (by linarith)
  have hTroot : T * Real.sqrt s ≤ R := by
    dsimp [R]
    exact mul_le_mul (by linarith : T ≤ T + 1) hroot (Real.sqrt_nonneg s) (by linarith)
  have hX : 1 ≤ R * B ^ 2 := one_le_mul_of_one_le_of_one_le hR (one_le_pow₀ hB)
  have hQ' : Q ≤ 162 * (R * B ^ 2) := by
    apply hQ.trans
    change 162 * Real.sqrt s * B ≤ _
    nlinarith [mul_le_mul hrootR hB2 hB0.le hR0.le]
  have hW' : W ≤ 319488 * (R * B ^ 2) := by
    apply hW.trans
    change 319488 * |t| * η * Real.sqrt s * B ^ 2 ≤ _
    have hm := mul_le_mul_of_nonneg_right hTroot (sq_nonneg B)
    dsimp only [T] at hm
    nlinarith
  have hsum : Q + W + 2 ≤ (2 : ℝ) ^ 20 * (R * B ^ 2) := by
    norm_num
    nlinarith
  have harg : 3 * (Q + W + 2) / (ε / 4) ≤ (2 : ℝ) ^ 20 * G * B ^ 2 := by
    calc
      _ = 12 * (Q + W + 2) / ε := by ring
      _ ≤ 12 * ((2 : ℝ) ^ 20 * (R * B ^ 2)) / ε := by
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsum (by norm_num)) hε.le
      _ ≤ 120 * ((2 : ℝ) ^ 20 * (R * B ^ 2)) / ε := by
        apply div_le_div_of_nonneg_right _ hε.le
        gcongr
        norm_num
      _ = _ := by dsimp [G]; ring
  have hl := Real.log_le_log (by positivity : (0 : ℝ) < 3 * (Q + W + 2) / (ε / 4)) harg
  rw [Real.log_mul (mul_ne_zero (by positivity) hG0.ne') (pow_ne_zero _ hB0.ne'),
    Real.log_mul (by positivity : (2 : ℝ) ^ 20 ≠ 0) hG0.ne', Real.log_pow, Real.log_pow] at hl
  have hd : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hd1 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlogG : Real.log G = (B - 1) * Real.log 2 := by
    dsimp [G, R, T, B, logBudget]
    field_simp
    ring
  have hG : Real.log G ≤ B := by
    rw [hlogG]
    nlinarith [mul_le_mul_of_nonneg_left hd1 (show 0 ≤ B - 1 by linarith)]
  have hb : Real.log B ≤ B := (Real.log_le_sub_one_of_pos hB0).trans (by linarith)
  change _ ≤ 23 * B
  norm_num at hl
  nlinarith

/-- The weighted and maximum-clock terms have a single square-logarithmic envelope. -/
theorem filter_budget_le (s η t ε Q W : ℝ) (hs : 1 ≤ s) (hη : 0 ≤ η)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hQ0 : 0 ≤ Q) (hW0 : 0 ≤ W)
    (hQ : Q ≤ 162 * Real.sqrt s * logBudget s η t ε)
    (hW : W ≤ 319488 * |t| * η * Real.sqrt s * (logBudget s η t ε) ^ 2) :
    W + Q * (1 + Real.log (3 * (Q + W + 2) / (ε / 4))) ≤
      323376 * (1 + |t| * η) * Real.sqrt s * (logBudget s η t ε) ^ 2 := by
  let B := logBudget s η t ε
  have hB : 1 ≤ B := logBudget_ge_one s η t ε hs hη hε hε1
  have hT : 0 ≤ |t| * η := mul_nonneg (abs_nonneg t) hη
  have hlog := filter_log_le s η t ε Q W hs hη hε hε1 hQ0 hW0 hQ hW
  have hlog' : 1 + Real.log (3 * (Q + W + 2) / (ε / 4)) ≤ 24 * B := by linarith
  have hQB : Q * (1 + Real.log (3 * (Q + W + 2) / (ε / 4))) ≤
      3888 * Real.sqrt s * B ^ 2 := by
    calc
      _ ≤ Q * (24 * B) := mul_le_mul_of_nonneg_left hlog' hQ0
      _ ≤ (162 * Real.sqrt s * B) * (24 * B) :=
        mul_le_mul_of_nonneg_right hQ (by positivity)
      _ = _ := by ring
  calc
    _ ≤ 319488 * |t| * η * Real.sqrt s * B ^ 2 + 3888 * Real.sqrt s * B ^ 2 :=
      add_le_add hW hQB
    _ = (319488 * (|t| * η) + 3888) * (Real.sqrt s * B ^ 2) := by ring
    _ ≤ (323376 * (1 + |t| * η)) * (Real.sqrt s * B ^ 2) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      linarith
    _ = _ := by dsimp [B]; ring

/-- Including the actual eighteen-query active-clock compiler and filter constant. -/
theorem native_count_le (s η t ε Q W count : ℝ) (hs : 1 ≤ s) (hη : 0 ≤ η)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hQ0 : 0 ≤ Q) (hW0 : 0 ≤ W)
    (hQ : Q ≤ 162 * Real.sqrt s * logBudget s η t ε)
    (hW : W ≤ 319488 * |t| * η * Real.sqrt s * (logBudget s η t ε) ^ 2)
    (hc : count ≤ 384 * 18 *
      (W + Q * (1 + Real.log (3 * (Q + W + 2) / (ε / 4))))) :
    count ≤ 2235174912 * (1 + |t| * η) * Real.sqrt s * (logBudget s η t ε) ^ 2 := by
  have h := mul_le_mul_of_nonneg_left
    (filter_budget_le s η t ε Q W hs hη hε hε1 hQ0 hW0 hQ hW)
    (by norm_num : (0 : ℝ) ≤ 384 * 18)
  exact hc.trans (by nlinarith [h])

end
end SparseHamiltonian.AmplifiedSimulationBudget
