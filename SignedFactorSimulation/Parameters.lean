import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The order and the query count of Theorem `opt:thm:signed`

For `0 < ε ≤ 1/64`, `L = log(1/ε)` and `b > 0`, the parameter of Theorem `opt:thm:signed` is

  `r_b = L / log(e + L/b)`  (`rb`).

The proof of the theorem chooses an integer order `M = O(b + r_b)` large enough that
`M ≥ 2·27² b` and that the factorial tail of Lemma `opt:lem:tail` is small. We take

  `M = ⌈40000 b + 100000 r_b⌉`  (`order`),

and prove the explicit tail bound `2 · 3001 (e² 27² b/M)^M ≤ ε²/(4·7⁸)` (`tail_bound`) in two
cases: `L ≤ e² b`, where `log(M/B₀) ≥ 2`, and `L > e² b`, where `log(M/B₀) ≥ log(e + L/b)/2`
(`B₀ = e² 27² b`). (The paper states that a large multiple of `B₀ + 𝓛/log(e + 𝓛/B₀)` suffices.)

For `b > ε`, `r_b ≥ 1/2` (`rb_ge_half`, `opt:eq:rb-lower`); hence `M ≤ 40000 b + 100002 r_b`
(`order_le`), and the query counts `2·3⁸·27·√(TM)` (for `T ≥ M`) and `2·3⁸·27·M` (for `T < M`,
using `b ≤ T`) are at most `4·10¹⁰ (√(Tb) + √(T r_b) + r_b)` (`count_le_of_large`,
`count_le_of_small`).
-/

set_option autoImplicit false

namespace SignedFactorSimulation

noncomputable section

open Real

/-- `r_b = L / log(e + L/b)` with `L = log(1/ε)`, for `b > 0` (the theorem uses it only for
`b > ε`). -/
def rb (b ε : ℝ) : ℝ := Real.log (1 / ε) / Real.log (Real.exp 1 + Real.log (1 / ε) / b)

/-- The order `M = ⌈40000 b + 100000 r_b⌉`. -/
def order (b ε : ℝ) : ℕ := ⌈40000 * b + 100000 * rb b ε⌉₊

section Scalars

theorem exp_one_lt : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9

theorem exp_one_gt : 2.7182818283 < Real.exp 1 := Real.exp_one_gt_d9

theorem exp_two_eq : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
  rw [← Real.exp_add]; norm_num

theorem exp_two_lt : Real.exp 2 < 7.39 := by
  rw [exp_two_eq]
  have h := exp_one_lt
  have h0 := Real.exp_pos 1
  nlinarith

theorem exp_two_gt : 7.38 < Real.exp 2 := by
  rw [exp_two_eq]
  have h := exp_one_gt
  nlinarith

theorem four_lt_log_64 : 4 < Real.log 64 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have h4 : Real.exp 4 = Real.exp 2 * Real.exp 2 := by rw [← Real.exp_add]; norm_num
  rw [h4]
  have h := exp_two_lt
  have h0 := Real.exp_pos 2
  nlinarith

/-- `log y ≤ 2 √y`. -/
theorem log_le_two_sqrt {y : ℝ} (hy : 0 < y) : Real.log y ≤ 2 * Real.sqrt y := by
  have hs : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy
  have h := Real.log_le_sub_one_of_pos hs
  rw [Real.log_sqrt hy.le] at h
  linarith

/-- `√(x + y) ≤ √x + √y`. -/
theorem sqrt_add_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  rw [Real.sqrt_le_left (by positivity)]
  have h1 := Real.sq_sqrt hx
  have h2 := Real.sq_sqrt hy
  have h3 : 0 ≤ Real.sqrt x * Real.sqrt y := by positivity
  nlinarith

end Scalars

section Order

variable {b ε : ℝ}

theorem log_inv_ge (hε : 0 < ε) (hε1 : ε ≤ 1 / 64) : 4 ≤ Real.log (1 / ε) := by
  have h64 : (64 : ℝ) ≤ 1 / ε := by rw [le_div_iff₀ hε]; linarith
  have := Real.log_le_log (by norm_num) h64
  linarith [four_lt_log_64]

theorem one_lt_exp_one_add {z : ℝ} (hz : 0 ≤ z) : 1 < Real.exp 1 + z := by
  have := exp_one_gt
  linarith

theorem log_exp_one_add_pos {z : ℝ} (hz : 0 ≤ z) : 0 < Real.log (Real.exp 1 + z) :=
  Real.log_pos (one_lt_exp_one_add hz)

theorem rb_pos (hε : 0 < ε) (hε1 : ε ≤ 1 / 64) (hb : 0 < b) : 0 < rb b ε := by
  have hL := log_inv_ge hε hε1
  exact div_pos (by linarith) (log_exp_one_add_pos (by positivity))

/-- **`r_b ≥ 1/2` for `b > ε`** (`opt:eq:rb-lower`): `log(e + L/b) < log(e + L e^L) ≤ 2L`. -/
theorem rb_ge_half (hε : 0 < ε) (hε1 : ε ≤ 1 / 64) (hb : ε < b) : 1 / 2 ≤ rb b ε := by
  set L := Real.log (1 / ε) with hL_def
  have hL := log_inv_ge hε hε1
  have hb0 : 0 < b := hε.trans hb
  have hexpL : Real.exp L = 1 / ε := Real.exp_log (by positivity)
  -- `L / b ≤ L e^L`
  have h1 : L / b ≤ L * Real.exp L := by
    rw [hexpL, ← div_eq_mul_one_div]
    exact div_le_div_of_nonneg_left (by linarith) hε hb.le
  -- `e + L e^L ≤ e^{2L}`
  have hLe : L * Real.exp 1 ≤ Real.exp L := by
    have h := Real.add_one_le_exp (L - 1)
    have h' : Real.exp L = Real.exp (L - 1) * Real.exp 1 := by
      rw [← Real.exp_add]; ring_nf
    rw [h']
    have := Real.exp_pos 1
    nlinarith
  have h2 : Real.exp 1 + L * Real.exp L ≤ Real.exp (2 * L) := by
    have hsq : Real.exp (2 * L) = Real.exp L * Real.exp L := by rw [← Real.exp_add]; ring_nf
    rw [hsq]
    have he := exp_one_gt
    have hpos := Real.exp_pos L
    have hone : 1 ≤ Real.exp L := Real.one_le_exp (by linarith)
    have hLe2 : L + Real.exp 1 ≤ Real.exp L := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hLe2 hpos.le]
  have hLb : 0 ≤ L / b := div_nonneg (by linarith) hb0.le
  have hD : Real.log (Real.exp 1 + L / b) ≤ 2 * L := by
    rw [← Real.log_exp (2 * L)]
    exact Real.log_le_log (lt_trans zero_lt_one (one_lt_exp_one_add hLb)) (by linarith)
  have hDpos := log_exp_one_add_pos hLb
  rw [rb, ← hL_def, le_div_iff₀ hDpos]
  linarith

theorem order_ge (b ε : ℝ) : 40000 * b + 100000 * rb b ε ≤ order b ε := Nat.le_ceil _

theorem order_le (hε : 0 < ε) (hε1 : ε ≤ 1 / 64) (hb : ε < b) :
    (order b ε : ℝ) ≤ 40000 * b + 100002 * rb b ε := by
  have h := Nat.ceil_lt_add_one (by
    have := rb_pos hε hε1 (hε.trans hb)
    have := hε.trans hb
    positivity : (0 : ℝ) ≤ 40000 * b + 100000 * rb b ε)
  have h2 := rb_ge_half hε hε1 hb
  rw [order]
  linarith

theorem one_le_order (hε : 0 < ε) (hε1 : ε ≤ 1 / 64) (hb : 0 < b) : 1 ≤ order b ε := by
  have h := order_ge b ε
  have hr := rb_pos hε hε1 hb
  have : (0 : ℝ) < order b ε := by linarith
  exact_mod_cast this

/-- The two case conditions of the order: `M log(M/B₀) ≥ 9 L`. -/
theorem order_log (hε : 0 < ε) (hε1 : ε ≤ 1 / 64) (hb : 0 < b) {M : ℝ}
    (hM : 40000 * b + 100000 * rb b ε ≤ M) :
    9 * Real.log (1 / ε) ≤ M * Real.log (M / (Real.exp 2 * 27 ^ 2 * b)) := by
  set L := Real.log (1 / ε) with hL_def
  have hL := log_inv_ge hε hε1
  have hr := rb_pos hε hε1 hb
  have he2 := exp_two_lt
  have he2' := exp_two_gt
  have hB : 0 < Real.exp 2 * 27 ^ 2 * b := by positivity
  have hM0 : 0 < M := by linarith
  by_cases hz : L ≤ Real.exp 2 * b
  · -- `L ≤ e² b`: `M ≥ e² B₀`, so `log(M/B₀) ≥ 2`
    have hMe : Real.exp 2 * (Real.exp 2 * 27 ^ 2 * b) ≤ M := by
      have : Real.exp 2 * (Real.exp 2 * 27 ^ 2 * b) ≤ 40000 * b := by
        have h1 : Real.exp 2 * Real.exp 2 ≤ 7.39 * 7.39 := by nlinarith [Real.exp_pos 2]
        nlinarith
      linarith
    have hlog : 2 ≤ Real.log (M / (Real.exp 2 * 27 ^ 2 * b)) := by
      rw [Real.le_log_iff_exp_le (div_pos hM0 hB), le_div_iff₀ hB]
      linarith
    nlinarith
  · -- `L > e² b`: `log(M/B₀) ≥ log(e + L/b)/2`
    push Not at hz
    set z := L / b with hz_def
    have hz2 : Real.exp 2 < z := by rw [hz_def, lt_div_iff₀ hb]; linarith
    have hz0 : 0 < z := by linarith [Real.exp_pos 2]
    set D := Real.log (Real.exp 1 + z) with hD_def
    have hD : 0 < D := log_exp_one_add_pos hz0.le
    have hrb : rb b ε = L / D := rfl
    have hMr : 100000 * (L / D) ≤ M := by rw [← hrb]; nlinarith
    -- `√(e + z) ≤ 18 z / D ≤ M / B₀`
    have hy : 0 < Real.exp 1 + z := by linarith [Real.exp_pos 1]
    have hsD : Real.sqrt (Real.exp 1 + z) * D ≤ 18 * z := by
      have h1 := log_le_two_sqrt hy
      have h2 := Real.sq_sqrt hy.le
      have hs := Real.sqrt_nonneg (Real.exp 1 + z)
      have he1 := exp_one_lt
      nlinarith
    have hsM : Real.sqrt (Real.exp 1 + z) ≤ M / (Real.exp 2 * 27 ^ 2 * b) := by
      rw [le_div_iff₀ hB]
      have h18 : 18 * (Real.exp 2 * 27 ^ 2) ≤ 100000 := by nlinarith
      -- `√(e+z) B₀ ≤ 18 z / D · e² 27² b ≤ 100000 L / D ≤ M`
      have hzb : z * b = L := by rw [hz_def]; field_simp
      have key : Real.sqrt (Real.exp 1 + z) * (Real.exp 2 * 27 ^ 2 * b) ≤
          100000 * (L / D) := by
        rw [mul_div_assoc', le_div_iff₀ hD]
        calc Real.sqrt (Real.exp 1 + z) * (Real.exp 2 * 27 ^ 2 * b) * D =
            (Real.sqrt (Real.exp 1 + z) * D) * (Real.exp 2 * 27 ^ 2 * b) := by ring
          _ ≤ (18 * z) * (Real.exp 2 * 27 ^ 2 * b) := mul_le_mul_of_nonneg_right hsD hB.le
          _ = 18 * (Real.exp 2 * 27 ^ 2) * (z * b) := by ring
          _ = 18 * (Real.exp 2 * 27 ^ 2) * L := by rw [hzb]
          _ ≤ 100000 * L := mul_le_mul_of_nonneg_right h18 (by linarith)
      linarith
    have hlog : D / 2 ≤ Real.log (M / (Real.exp 2 * 27 ^ 2 * b)) := by
      have h := Real.log_le_log (Real.sqrt_pos.mpr hy) hsM
      rw [Real.log_sqrt hy.le] at h
      exact h
    have hD2 : 0 ≤ D / 2 := by positivity
    calc 9 * L ≤ 100000 * (L / D) * (D / 2) := by
          rw [show 100000 * (L / D) * (D / 2) = 50000 * L by field_simp; ring]
          linarith
      _ ≤ M * Real.log (M / (Real.exp 2 * 27 ^ 2 * b)) :=
          mul_le_mul hMr hlog hD2 hM0.le

/-- **The factorial tail is small** (`opt:eq:order-choice`): for `M ≥ 40000 b + 100000 r_b`,
`2 · 3001 (e² 27² b/M)^M ≤ ε²/(4·7⁸)`. -/
theorem tail_bound (hε : 0 < ε) (hε1 : ε ≤ 1 / 64) (hb : 0 < b) {M : ℕ}
    (hM : 40000 * b + 100000 * rb b ε ≤ M) :
    2 * (3000 + 1) * (Real.exp 2 * 27 ^ 2 * b / M) ^ M ≤ ε ^ 2 / (4 * 7 ^ 8) := by
  have hr := rb_pos hε hε1 hb
  have hM0 : (0 : ℝ) < M := by nlinarith
  have hB : 0 < Real.exp 2 * 27 ^ 2 * b := by positivity
  have hx : 0 < Real.exp 2 * 27 ^ 2 * b / M := div_pos hB hM0
  have hkey := order_log hε hε1 hb hM
  have hlogx : Real.log (Real.exp 2 * 27 ^ 2 * b / M) =
      -Real.log (M / (Real.exp 2 * 27 ^ 2 * b)) := by
    rw [← Real.log_inv, inv_div]
  have hxM : (Real.exp 2 * 27 ^ 2 * b / M) ^ M =
      Real.exp (M * Real.log (Real.exp 2 * 27 ^ 2 * b / M)) := by
    rw [← Real.log_pow, Real.exp_log (pow_pos hx M)]
  have hL : Real.log (1 / ε) = -Real.log ε := by rw [one_div, Real.log_inv]
  have hε9 : Real.exp (-(9 * Real.log (1 / ε))) = ε ^ 9 := by
    rw [hL, show -(9 * -Real.log ε) = ((9 : ℕ) : ℝ) * Real.log ε by push_cast; ring,
      Real.exp_nat_mul, Real.exp_log hε]
  have hbound : (Real.exp 2 * 27 ^ 2 * b / M) ^ M ≤ ε ^ 9 := by
    rw [hxM, hlogx, ← hε9]
    apply Real.exp_le_exp.mpr
    linarith
  have hε7 : ε ^ 7 ≤ (1 / 64) ^ 7 := pow_le_pow_left₀ hε.le hε1 7
  have hε2 : 0 ≤ ε ^ 2 := by positivity
  calc 2 * (3000 + 1) * (Real.exp 2 * 27 ^ 2 * b / M) ^ M ≤ 2 * (3000 + 1) * ε ^ 9 := by
        gcongr
    _ = 2 * (3000 + 1) * (ε ^ 2 * ε ^ 7) := by ring
    _ ≤ 2 * (3000 + 1) * (ε ^ 2 * (1 / 64) ^ 7) := by gcongr
    _ ≤ ε ^ 2 / (4 * 7 ^ 8) := by
        rw [le_div_iff₀ (by norm_num)]
        nlinarith

end Order

/-! ### The query count -/

/-- For `T ≥ M`: `2·3⁸·27·√(TM) ≤ 4·10¹⁰ (√(Tb) + √(T r) + r)` when `M ≤ 40000 b + 100002 r`. -/
theorem count_le_of_large {T b r M : ℝ} (hT : 0 ≤ T) (hb : 0 ≤ b) (hr : 0 ≤ r)
    (hM : M ≤ 40000 * b + 100002 * r) :
    2 * 3 ^ 8 * 27 * Real.sqrt (T * M) ≤
      4 * 10 ^ 10 * (Real.sqrt (T * b) + Real.sqrt (T * r) + r) := by
  have h1 : Real.sqrt (T * M) ≤ Real.sqrt (T * (40000 * b)) + Real.sqrt (T * (100002 * r)) := by
    calc Real.sqrt (T * M) ≤ Real.sqrt (T * (40000 * b) + T * (100002 * r)) :=
          Real.sqrt_le_sqrt (by nlinarith)
      _ ≤ _ := sqrt_add_le (by positivity) (by positivity)
  have h2 : Real.sqrt (T * (40000 * b)) = 200 * Real.sqrt (T * b) := by
    rw [show T * (40000 * b) = 200 ^ 2 * (T * b) by ring, Real.sqrt_mul (by norm_num),
      Real.sqrt_sq (by norm_num)]
  have h3 : Real.sqrt (T * (100002 * r)) ≤ 317 * Real.sqrt (T * r) := by
    rw [show T * (100002 * r) = 100002 * (T * r) by ring, Real.sqrt_mul (by norm_num)]
    apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hs1 := Real.sqrt_nonneg (T * b)
  have hs2 := Real.sqrt_nonneg (T * r)
  nlinarith

/-- For `T < M` (and `b ≤ T`): `2·3⁸·27·M ≤ 4·10¹⁰ (√(Tb) + √(T r) + r)`. -/
theorem count_le_of_small {T b r M : ℝ} (hb : 0 ≤ b) (hbT : b ≤ T) (hr : 0 ≤ r)
    (hM : M ≤ 40000 * b + 100002 * r) :
    2 * 3 ^ 8 * 27 * M ≤ 4 * 10 ^ 10 * (Real.sqrt (T * b) + Real.sqrt (T * r) + r) := by
  have hbs : b ≤ Real.sqrt (T * b) := by
    calc b = Real.sqrt (b ^ 2) := (Real.sqrt_sq hb).symm
      _ ≤ Real.sqrt (T * b) := Real.sqrt_le_sqrt (by nlinarith)
  have hs := Real.sqrt_nonneg (T * r)
  nlinarith

end

end SignedFactorSimulation
