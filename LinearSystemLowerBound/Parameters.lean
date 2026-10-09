import LinearSystemLowerBound.Hard.Answer

/-!
# Parameters of the hard family

For `κ ≥ 32`, `s ≥ 5` and `0 < ε ≤ 1/64` (paper, equation `qlsl:eq:parameters`):

* `R = 2^{⌊log₂(κ/2)⌋}` (`Rpar`), with `16 ≤ R`, `κ/4 < R ≤ κ/2`;
* `m = 2^{⌊log₂(s-1)⌋}` (`mpar`), even, with `4 ≤ m ≤ s - 1 < 2m`;
* `L = ln(1/ε)` and `n = ⌊((R - 1)/2) ln(1/(16ε))⌋` (`npar`), with `n ≥ RL/8 > κL/32`,
  `n ≥ 2L` and `n ≤ ((R - 1)/2) ln(1/(16ε))`;
* `r = 1 - 1/R`, `T = 2n - 1` clock transitions.

Consequences: `r^{2n} ≥ 16ε`, the answer probability is at least `64ε/5`, and the decoder
bias `(2/3)(p - 2ε)` is at least `ε`.  Finally `q_bound`: if `n ≥ 2L` and
`ε ≤ 2^{-n} ((1 + 2/√m)²)^Q` then `Q > n √m / 24`; with `n > κL/32` and `√m > √s/2` this
gives `Q > κ √s ln(1/ε) / 1536` (`lower_bound_of_bias`).
-/

namespace LinearSystemLowerBound.Params

noncomputable section
open LinearSystemLowerBound LinearSystemLowerBound.Hard

/-- `R = 2^{⌊log₂(κ/2)⌋}`. -/
def Rpar (κ : ℝ) : ℕ := 2 ^ Nat.log 2 ⌊κ / 2⌋₊

/-- `m = 2^{⌊log₂(s-1)⌋}`. -/
def mpar (s : ℕ) : ℕ := 2 ^ Nat.log 2 (s - 1)

/-- `n = ⌊((R - 1)/2) ln(1/(16ε))⌋`. -/
def npar (κ ε : ℝ) : ℕ := ⌊((Rpar κ - 1 : ℝ) / 2) * Real.log (1 / (16 * ε))⌋₊

/-- `r = 1 - 1/R`. -/
def rpar (κ : ℝ) : ℝ := 1 - 1 / (Rpar κ : ℝ)

/-! ### `R` -/

theorem floor_ge (κ : ℝ) (hκ : 32 ≤ κ) : 16 ≤ ⌊κ / 2⌋₊ := by
  apply Nat.le_floor
  push_cast
  linarith

theorem Rpar_le (κ : ℝ) (hκ : 32 ≤ κ) : (Rpar κ : ℝ) ≤ κ / 2 := by
  have h0 : ⌊κ / 2⌋₊ ≠ 0 := by have := floor_ge κ hκ; omega
  have h1 : Rpar κ ≤ ⌊κ / 2⌋₊ := Nat.pow_log_le_self 2 h0
  have h2 : (⌊κ / 2⌋₊ : ℝ) ≤ κ / 2 := Nat.floor_le (by linarith)
  calc (Rpar κ : ℝ) ≤ ⌊κ / 2⌋₊ := by exact_mod_cast h1
    _ ≤ κ / 2 := h2

theorem lt_Rpar (κ : ℝ) : κ / 4 < (Rpar κ : ℝ) := by
  have h1 : ⌊κ / 2⌋₊ < 2 ^ (Nat.log 2 ⌊κ / 2⌋₊ + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have h2 : κ / 2 < ⌊κ / 2⌋₊ + 1 := Nat.lt_floor_add_one _
  have h3 : ((⌊κ / 2⌋₊ : ℕ) : ℝ) + 1 ≤ 2 * (Rpar κ : ℝ) := by
    have : ⌊κ / 2⌋₊ + 1 ≤ 2 * Rpar κ := by
      rw [Rpar, ← pow_succ']
      omega
    exact_mod_cast this
  linarith

theorem sixteen_le_Rpar (κ : ℝ) (hκ : 32 ≤ κ) : (16 : ℝ) ≤ Rpar κ := by
  have h : 4 ≤ Nat.log 2 ⌊κ / 2⌋₊ := by
    have := Nat.log_mono_right (b := 2) (floor_ge κ hκ)
    have h16 : Nat.log 2 16 = 4 := by decide
    omega
  have : 16 ≤ Rpar κ := by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ Nat.log 2 ⌊κ / 2⌋₊ := Nat.pow_le_pow_right (by norm_num) h
  exact_mod_cast this

theorem rpar_nonneg (κ : ℝ) (hκ : 32 ≤ κ) : 0 ≤ rpar κ := by
  have := sixteen_le_Rpar κ hκ
  unfold rpar
  rw [sub_nonneg, div_le_one (by linarith)]
  linarith

theorem rpar_lt_one (κ : ℝ) (hκ : 32 ≤ κ) : rpar κ < 1 := by
  have := sixteen_le_Rpar κ hκ
  unfold rpar
  have : 0 < 1 / (Rpar κ : ℝ) := by positivity
  linarith

theorem two_div_one_sub_rpar (κ : ℝ) (hκ : 32 ≤ κ) : 2 / (1 - rpar κ) ≤ κ := by
  have h16 := sixteen_le_Rpar κ hκ
  have hR := Rpar_le κ hκ
  have : 1 - rpar κ = 1 / (Rpar κ : ℝ) := by unfold rpar; ring
  rw [this, div_div_eq_mul_div, div_one]
  linarith

/-! ### `m` -/

theorem mpar_le (s : ℕ) (hs : 5 ≤ s) : mpar s ≤ s - 1 :=
  Nat.pow_log_le_self 2 (by omega)

theorem lt_two_mpar (s : ℕ) : s - 1 < 2 * mpar s := by
  have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (s - 1)
  rw [mpar, ← pow_succ']
  exact this

theorem two_le_log (s : ℕ) (hs : 5 ≤ s) : 2 ≤ Nat.log 2 (s - 1) := by
  have := Nat.log_mono_right (b := 2) (show 4 ≤ s - 1 by omega)
  have h4 : Nat.log 2 4 = 2 := by decide
  omega

theorem four_le_mpar (s : ℕ) (hs : 5 ≤ s) : 4 ≤ mpar s := by
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ Nat.log 2 (s - 1) := Nat.pow_le_pow_right (by norm_num) (two_le_log s hs)

theorem mpar_even (s : ℕ) (hs : 5 ≤ s) : Even (mpar s) := by
  have h := two_le_log s hs
  exact Nat.even_pow.mpr ⟨even_two, by omega⟩

theorem sqrt_mpar (s : ℕ) (hs : 5 ≤ s) : Real.sqrt s / 2 < Real.sqrt (mpar s) := by
  have h1 := lt_two_mpar s
  have h2 : (s : ℝ) < 4 * mpar s := by
    have : s < 4 * mpar s := by omega
    exact_mod_cast this
  rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)]
  have hs0 : (0 : ℝ) ≤ s := by positivity
  rw [show Real.sqrt (mpar s) * 2 = Real.sqrt (4 * mpar s) by
    rw [Real.sqrt_mul (by norm_num), show Real.sqrt 4 = 2 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]; ring]
  exact Real.sqrt_lt_sqrt hs0 h2

/-! ### `n` -/

theorem log_64_gt : (2 : ℝ) < Real.log 64 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have := Real.exp_one_lt_d9
  have h2 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
  rw [h2]
  nlinarith [Real.exp_pos 1]

theorem L_ge (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 64) : Real.log 64 ≤ Real.log (1 / ε) := by
  apply Real.log_le_log (by norm_num)
  rw [le_div_iff₀ hε]
  linarith

theorem log16_le (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 64) :
    Real.log (1 / ε) / 3 ≤ Real.log (1 / (16 * ε)) := by
  have hL := L_ge ε hε hε1
  have h16 : Real.log 16 = 2 / 3 * Real.log 64 := by
    rw [show (64 : ℝ) = 16 * 4 by norm_num, Real.log_mul (by norm_num) (by norm_num),
      show (16 : ℝ) = 4 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  have hsplit : Real.log (1 / (16 * ε)) = Real.log (1 / ε) - Real.log 16 := by
    rw [show 1 / (16 * ε) = (1 / ε) / 16 by field_simp, Real.log_div (by positivity) (by norm_num)]
  rw [hsplit, h16]
  linarith

theorem npar_ge (κ ε : ℝ) (hκ : 32 ≤ κ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 64) :
    (Rpar κ : ℝ) * Real.log (1 / ε) / 8 ≤ npar κ ε := by
  have hR := sixteen_le_Rpar κ hκ
  have hL := L_ge ε hε hε1
  have h64 := log_64_gt
  have hl := log16_le ε hε hε1
  have hfl : ((Rpar κ - 1 : ℝ) / 2) * Real.log (1 / (16 * ε)) < npar κ ε + 1 :=
    Nat.lt_floor_add_one _
  have hlow : ((Rpar κ - 1 : ℝ) / 2) * (Real.log (1 / ε) / 3) ≤
      ((Rpar κ - 1 : ℝ) / 2) * Real.log (1 / (16 * ε)) :=
    mul_le_mul_of_nonneg_left hl (by linarith)
  nlinarith

theorem npar_le (κ ε : ℝ) (hκ : 32 ≤ κ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 64) :
    (npar κ ε : ℝ) ≤ ((Rpar κ - 1 : ℝ) / 2) * Real.log (1 / (16 * ε)) := by
  have hR := sixteen_le_Rpar κ hκ
  have hl := log16_le ε hε hε1
  have hL := L_ge ε hε hε1
  have h64 := log_64_gt
  exact Nat.floor_le (mul_nonneg (by linarith) (by linarith))

theorem npar_pos (κ ε : ℝ) (hκ : 32 ≤ κ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 64) : 0 < npar κ ε := by
  have h := npar_ge κ ε hκ hε hε1
  have hR := sixteen_le_Rpar κ hκ
  have hL := L_ge ε hε hε1
  have h64 := log_64_gt
  have : (0 : ℝ) < npar κ ε := by nlinarith
  exact_mod_cast this

theorem npar_ge_twoL (κ ε : ℝ) (hκ : 32 ≤ κ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 64) :
    2 * Real.log (1 / ε) ≤ npar κ ε := by
  have h := npar_ge κ ε hκ hε hε1
  have hR := sixteen_le_Rpar κ hκ
  have hL := L_ge ε hε hε1
  have h64 := log_64_gt
  nlinarith

theorem npar_gt (κ ε : ℝ) (hκ : 32 ≤ κ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 64) :
    κ * Real.log (1 / ε) / 32 < npar κ ε := by
  have h := npar_ge κ ε hκ hε hε1
  have hR := lt_Rpar κ
  have hL := L_ge ε hε hε1
  have h64 := log_64_gt
  nlinarith

/-! ### The answer probability and the bias -/

theorem rpar_pow_ge (κ ε : ℝ) (hκ : 32 ≤ κ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 64) :
    16 * ε ≤ rpar κ ^ (2 * npar κ ε) := by
  have hR := sixteen_le_Rpar κ hκ
  have hr0 : 0 < rpar κ := by
    unfold rpar
    have : 1 / (Rpar κ : ℝ) < 1 := by rw [div_lt_one (by linarith)]; linarith
    linarith
  have hn := npar_le κ ε hκ hε hε1
  -- `ln r ≥ 1 - 1/r = -1/(R-1)`
  have hlogr : -1 / ((Rpar κ : ℝ) - 1) ≤ Real.log (rpar κ) := by
    have h := Real.one_sub_inv_le_log_of_pos hr0
    have hR1 : (Rpar κ : ℝ) - 1 ≠ 0 := by linarith
    have hR0 : (Rpar κ : ℝ) ≠ 0 := by linarith
    have : 1 - (rpar κ)⁻¹ = -1 / ((Rpar κ : ℝ) - 1) := by
      unfold rpar
      field_simp
      ring
    linarith
  have hexp : rpar κ ^ (2 * npar κ ε) = Real.exp (2 * npar κ ε * Real.log (rpar κ)) := by
    rw [← Real.exp_log (pow_pos hr0 _), Real.log_pow]
    push_cast
    ring_nf
  have h16 : 16 * ε = Real.exp (-Real.log (1 / (16 * ε))) := by
    rw [Real.exp_neg, Real.exp_log (by positivity)]
    field_simp
  rw [hexp, h16]
  apply Real.exp_le_exp.mpr
  have hR1 : 0 < (Rpar κ : ℝ) - 1 := by linarith
  have h2n : 2 * (npar κ ε : ℝ) / ((Rpar κ : ℝ) - 1) ≤ Real.log (1 / (16 * ε)) := by
    rw [div_le_iff₀ hR1]
    nlinarith
  have hnn : (0 : ℝ) ≤ npar κ ε := Nat.cast_nonneg _
  calc -Real.log (1 / (16 * ε)) ≤ -(2 * (npar κ ε : ℝ) / ((Rpar κ : ℝ) - 1)) := by linarith
    _ = 2 * npar κ ε * (-1 / ((Rpar κ : ℝ) - 1)) := by ring
    _ ≤ 2 * npar κ ε * Real.log (rpar κ) := mul_le_mul_of_nonneg_left hlogr (by positivity)

theorem answerProb_ge (κ ε : ℝ) (hκ : 32 ≤ κ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 64) :
    64 / 5 * ε ≤ answerProb (rpar κ) (npar κ ε) := by
  have h := rpar_pow_ge κ ε hκ hε hε1
  unfold answerProb
  set t := rpar κ ^ (2 * npar κ ε)
  have ht : 0 < t := by linarith
  rw [le_div_iff₀ (by linarith)]
  nlinarith

theorem bias_ge (κ ε : ℝ) (hκ : 32 ≤ κ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 64) :
    2 * ε ≤ answerProb (rpar κ) (npar κ ε) ∧
      ε ≤ 2 / 3 * (answerProb (rpar κ) (npar κ ε) - 2 * ε) := by
  have h := answerProb_ge κ ε hκ hε hε1
  constructor <;> nlinarith

/-! ### The final count -/

/-- **From the XOR inequality to the query count.**  If
`ε ≤ 2^{-n} ((1 + 2/√m)²)^Q` with `n ≥ 2 ln(1/ε)`, then `Q > n √m / 24`. -/
theorem q_bound (n m Q : ℕ) (ε : ℝ) (hε : 0 < ε) (hm : 0 < m) (hn : 0 < n)
    (hnL : 2 * Real.log (1 / ε) ≤ n)
    (h : ε ≤ (1 / 2) ^ n * ((1 + 2 / Real.sqrt m) ^ 2) ^ Q) :
    (n : ℝ) * Real.sqrt m / 24 < Q := by
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.mpr (by exact_mod_cast hm)
  have hγ : 0 < 1 + 2 / Real.sqrt m := by positivity
  have hlog := Real.log_le_log hε h
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow,
    one_div, Real.log_inv] at hlog
  have hlg : Real.log (1 + 2 / Real.sqrt m) ≤ 2 / Real.sqrt m := by
    have := Real.log_le_sub_one_of_pos hγ
    linarith
  have hL : Real.log ε = -Real.log (1 / ε) := by
    rw [one_div, Real.log_inv, neg_neg]
  have hln2 : (2 : ℝ) / 3 < Real.log 2 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    have := Real.exp_one_lt_d9
    have h23 : Real.exp (2 / 3) ^ 3 = Real.exp 2 := by
      rw [← Real.exp_nat_mul]; norm_num
    have h2 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
    have hpos := Real.exp_pos (2 / 3)
    nlinarith [sq_nonneg (Real.exp (2 / 3) - 2), Real.exp_pos 1]
  have hQ0 : (0 : ℝ) ≤ Q := Nat.cast_nonneg _
  have key : (n : ℝ) * Real.log 2 - Real.log (1 / ε) ≤ 4 * Q / Real.sqrt m := by
    have h4 : (Q : ℝ) * (2 * Real.log (1 + 2 / Real.sqrt m)) ≤ Q * (2 * (2 / Real.sqrt m)) :=
      mul_le_mul_of_nonneg_left (by linarith) hQ0
    have : 4 * (Q : ℝ) / Real.sqrt m = Q * (2 * (2 / Real.sqrt m)) := by ring
    rw [this]
    push_cast at hlog
    linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h6 : (n : ℝ) / 6 < n * Real.log 2 - Real.log (1 / ε) := by nlinarith
  rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 24)]
  have : (n : ℝ) / 6 * Real.sqrt m < 4 * Q := by
    have := mul_lt_mul_of_pos_right (h6.trans_le key) hsm
    rwa [div_mul_cancel₀ _ hsm.ne'] at this
  nlinarith

end

end LinearSystemLowerBound.Params
