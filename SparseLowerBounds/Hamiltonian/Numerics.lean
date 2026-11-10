import SparseLowerBounds.Hamiltonian.Parameters

set_option synthInstance.maxHeartbeats 400000

section
/-!
# Numeric facts for the three hard families

Real analysis only (the proofs of Lemmas `hsl:lem:mixed` and `hsl:lem:time` and of Theorem
`hsl:thm:main`).

* Search lemma at `β₀ = 1/4` (time family, proof of Lemma `hsl:lem:time`):
  `4 β₀^{-1/n} ≤ 16` and `β₀^{1/(2n)} ≥ 1/2`.
* Time family (Lemma `hsl:lem:time`): `n ≥ τ/π`, `0 < c ≤ 1`, amplitude
  `sin(cτ/n)^n ≥ 1/2`, and the final `c_T √s τ ≤ (log 2/96) n √m`.
* Mixed and precision families (proof of Lemma `hsl:lem:mixed`): for `0 < τ ≤ n`,
  `(τ/(2n))^n ≤ sin(τ/n)^n`; with `β₀ = sin(τ/n)^n/2` and `n ≥ 2`,
  `4 β₀^{-1/n} ≤ 16n/τ` and `β₀^{1/(2n)} ≥ ½ √(τ/n)`.
* Main parameters with `L ≥ 64τ` (proof of Theorem `hsl:thm:main`): `log(e + z) ≤ z/8` for
  `z ≥ 64`, eq. `hsl:eq:nrange`, eq. `hsl:eq:precisionchoice` in the form
  `(τ/(2n))^n ≥ 16ε` (also used by Lemma `odel:lem:herald`),
  eqs. `hsl:eq:rbound`, `hsl:eq:mixrbound`, `hsl:eq:failedmix`, and the mixed
  family's condition `m ≥ 16n/τ`.

Intermediate statements (for the proofs of the above): `half_le_floor`,
`sin_ge_half_mul`, `half_lt_sin_one`; the `rpow` algebra
`(1/4)^{-1/n} = 4^{1/n}`, `(1/4)^{1/(2n)} = 2^{-1/n}`,
`(x^n/2)^{-1/n} = 2^{1/n}/x`, `(x^n/2)^{1/(2n)} = 2^{-1/(2n)} √x` and the
bounds on `2^{±1/n}`; the case analysis of `timeN`/`timeC` at `τ = π/2`;
`√s/2 < √m`; and, for the main parameters, `h ≤ z/8`, `r ≥ 8τ`, `r ≤ 8n`,
`2n/τ ≤ e + z`, eq. `hsl:eq:precisionchoice` (`precision_exp_bound`),
`(τ/(2n))^n ≥ e^{-L/4}` and `e^{-L/4} ≥ 16 e^{-L}`, `sτr ≤ 32 mnτ` and
`sτr < 512 n²`. Several of these hold without `L ≥ 64τ` and are stated so.
-/

namespace SparseLowerBounds.Hamiltonian

noncomputable section

variable {τ ε : ℝ} {s n : ℕ}

/-! ### Elementary inequalities -/

/-- `⌊x⌋ ≥ x/2` for `x ≥ 1` (used for `n ≥ τ/π`, proof of Lemma `hsl:lem:time`, and `n ≥ r/8`,
eq. `hsl:eq:nrange`). -/
theorem half_le_floor {x : ℝ} (hx : 1 ≤ x) : x / 2 ≤ ⌊x⌋₊ := by
  have h1 := Nat.lt_floor_add_one x
  have h2 : (1 : ℝ) ≤ ⌊x⌋₊ := by
    have : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
    exact_mod_cast this
  linarith

/-- `sin x ≥ x/2` on `[0, 1]` (weaker than Jordan's `sin x ≥ 2x/π`; proof of Lemma
`hsl:lem:mixed`). -/
theorem sin_ge_half_mul {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : x / 2 ≤ Real.sin x := by
  have hpi := Real.one_le_pi_div_two
  have hpi4 := Real.pi_le_four
  have h := Real.mul_le_sin hx0 (by linarith)
  have : x / 2 ≤ 2 / Real.pi * x := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by norm_num) Real.pi_pos]
    nlinarith
  linarith

/-- `sin 1 > 1/2` (proof of Lemma `hsl:lem:time`). -/
theorem half_lt_sin_one : 1 / 2 < Real.sin 1 := by
  have := Real.sin_gt_sub_cube (x := 1) one_pos
  norm_num at this
  linarith

/-! ### `rpow` algebra -/

/-- `(1/4)^{-1/n} = 4^{1/n}` (Lean's `-1/0 = 0` makes both sides `1` at `n = 0`). -/
theorem quarter_rpow_neg_inv (n : ℕ) :
    (1 / 4 : ℝ) ^ (-(1 : ℝ) / n) = (4 : ℝ) ^ (1 / (n : ℝ)) := by
  rw [one_div (4 : ℝ), Real.inv_rpow (by norm_num), neg_div, Real.rpow_neg (by norm_num),
    inv_inv]

/-- `4^{1/n} ≤ 4` for `n ≥ 1`. -/
theorem four_rpow_inv_le (hn : 1 ≤ n) : (4 : ℝ) ^ (1 / (n : ℝ)) ≤ 4 := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : 1 / (n : ℝ) ≤ 1 := by rw [div_le_one₀ (by linarith)]; exact hn'
  calc (4 : ℝ) ^ (1 / (n : ℝ)) ≤ 4 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
    _ = 4 := Real.rpow_one 4

/-- `(1/4)^{1/(2n)} = 2^{-1/n}` (both sides `1` at `n = 0`). -/
theorem quarter_rpow_root (n : ℕ) :
    (1 / 4 : ℝ) ^ (1 / (2 * (n : ℝ))) = (2 : ℝ) ^ (-(1 : ℝ) / n) := by
  have h4 : (1 / 4 : ℝ) = (2 : ℝ) ^ (-2 : ℝ) := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_two]; norm_num
  rw [h4, ← Real.rpow_mul (by norm_num)]
  congr 1
  ring

/-- `2^{-1/n} ≥ 1/2` (all `n`, with `2^{-1/0} = 1`). -/
theorem half_le_two_rpow_neg_inv (n : ℕ) : 1 / 2 ≤ (2 : ℝ) ^ (-(1 : ℝ) / n) := by
  have h : -(1 : ℝ) ≤ -(1 : ℝ) / n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · norm_num
    · have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
      rw [neg_div, neg_le_neg_iff, div_le_one₀ (by linarith)]; exact hn'
  calc (1 / 2 : ℝ) = 2 ^ (-(1 : ℝ)) := by rw [Real.rpow_neg_one]; norm_num
    _ ≤ 2 ^ (-(1 : ℝ) / n) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h

/-- `2^{1/n} ≤ 2` for `n ≥ 1` (proof of Lemma `hsl:lem:mixed`). -/
theorem two_rpow_inv_le_two (hn : 1 ≤ n) : (2 : ℝ) ^ (1 / (n : ℝ)) ≤ 2 := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : 1 / (n : ℝ) ≤ 1 := by rw [div_le_one₀ (by linarith)]; exact hn'
  calc (2 : ℝ) ^ (1 / (n : ℝ)) ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
    _ = 2 := Real.rpow_one 2

/-- `2^{-1/(2n)} ≥ 1/√2` for `n ≥ 1` (proof of Lemma `hsl:lem:mixed`). -/
theorem inv_sqrt_two_le_two_rpow (hn : 1 ≤ n) :
    1 / Real.sqrt 2 ≤ (2 : ℝ) ^ (-(1 : ℝ) / (2 * n)) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : 1 / Real.sqrt 2 = (2 : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_neg (by norm_num), one_div]
  rw [h1]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  rw [neg_div, neg_le_neg_iff, div_le_div_iff₀ (by linarith) (by norm_num)]
  linarith

/-- `(x^n/2)^{-1/n} = 2^{1/n}/x` for `x > 0` (an equality of the proof of Lemma
`hsl:lem:mixed`, with `x = sin(τ/n)`). -/
theorem pow_div_two_rpow_neg_inv (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x) :
    (x ^ n / 2) ^ (-(1 : ℝ) / n) = (2 : ℝ) ^ (1 / (n : ℝ)) / x := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [Real.div_rpow (by positivity) (by norm_num), ← Real.rpow_natCast x n,
    ← Real.rpow_mul hx.le]
  have e : (n : ℝ) * (-(1 : ℝ) / n) = -1 := by field_simp
  rw [e, Real.rpow_neg_one, neg_div, Real.rpow_neg (by norm_num), div_inv_eq_mul,
    inv_mul_eq_div]

/-- `(x^n/2)^{1/(2n)} = 2^{-1/(2n)} √x` for `x > 0` (an equality of
the proof of Lemma `hsl:lem:mixed`, with `x = sin(τ/n)`). -/
theorem pow_div_two_rpow_root (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x) :
    (x ^ n / 2) ^ (1 / (2 * (n : ℝ))) = (2 : ℝ) ^ (-(1 : ℝ) / (2 * n)) * Real.sqrt x := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [Real.div_rpow (by positivity) (by norm_num), ← Real.rpow_natCast x n,
    ← Real.rpow_mul hx.le]
  have e : (n : ℝ) * (1 / (2 * (n : ℝ))) = 1 / 2 := by field_simp
  rw [e, ← Real.sqrt_eq_rpow, neg_div, Real.rpow_neg (by norm_num)]
  ring

/-! ### The search lemma at `β₀ = 1/4` -/

/-- `4 β₀^{-1/n} ≤ 16` at `β₀ = 1/4` (proof of Lemma `hsl:lem:time`). -/
theorem quarter_hyp (hn : 1 ≤ n) : 4 * (1 / 4 : ℝ) ^ (-(1 : ℝ) / n) ≤ 16 := by
  rw [quarter_rpow_neg_inv]
  linarith [four_rpow_inv_le hn]

/-- `β₀^{1/(2n)} ≥ 1/2` at `β₀ = 1/4` (proof of Lemma `hsl:lem:time`). -/
theorem quarter_root (n : ℕ) : (1 / 2 : ℝ) ≤ (1 / 4 : ℝ) ^ (1 / (2 * (n : ℝ))) := by
  rw [quarter_rpow_root]
  exact half_le_two_rpow_neg_inv n

/-! ### Time family -/

/-- For `τ < π/2`, `n = 1` (Lemma `hsl:lem:time`). -/
theorem timeN_eq_one_of_lt (hτ : τ < Real.pi / 2) : timeN τ = 1 := by
  unfold timeN
  have : ⌊2 * τ / Real.pi⌋₊ = 0 :=
    Nat.floor_eq_zero.mpr (by rw [div_lt_one Real.pi_pos]; linarith)
  rw [this]
  rfl

/-- For `0 < τ < π/2`, `c = 1` (Lemma `hsl:lem:time`). -/
theorem timeC_eq_one_of_lt (hτ0 : 0 < τ) (hτ : τ < Real.pi / 2) : timeC τ = 1 := by
  unfold timeC
  rw [timeN_eq_one_of_lt hτ]
  apply min_eq_left
  rw [Nat.cast_one, mul_one, le_div_iff₀ (by linarith)]
  linarith

/-- For `τ ≥ π/2`, `n = ⌊2τ/π⌋`. -/
theorem timeN_eq_floor (hτ : Real.pi / 2 ≤ τ) : timeN τ = ⌊2 * τ / Real.pi⌋₊ := by
  unfold timeN
  apply max_eq_right
  apply Nat.le_floor
  rw [Nat.cast_one, le_div_iff₀ Real.pi_pos]
  linarith

/-- For `τ ≥ π/2`, `cτ/n = π/2` (Lemma `hsl:lem:time`). -/
theorem timeC_mul_div_timeN (hτ : Real.pi / 2 ≤ τ) :
    timeC τ * τ / timeN τ = Real.pi / 2 := by
  have hpi := Real.pi_pos
  have hτ0 : 0 < τ := by linarith
  have hn1 : (1 : ℝ) ≤ timeN τ := by exact_mod_cast one_le_timeN τ
  have hn0 : (timeN τ : ℝ) ≠ 0 := ne_of_gt (by linarith)
  have hτ0' : τ ≠ 0 := hτ0.ne'
  have hnle : (timeN τ : ℝ) ≤ 2 * τ / Real.pi := by
    rw [timeN_eq_floor hτ]; exact Nat.floor_le (by positivity)
  have hc : timeC τ = Real.pi * timeN τ / (2 * τ) := by
    unfold timeC
    apply min_eq_right
    rw [div_le_one₀ (by positivity)]
    rw [le_div_iff₀ hpi] at hnle
    linarith
  rw [hc]
  field_simp

/-- `n ≥ τ/π` (proof of Lemma `hsl:lem:time`). -/
theorem tau_div_pi_le_timeN (_hτ : 0 < τ) : τ / Real.pi ≤ timeN τ := by
  have hpi := Real.pi_pos
  have hn1 : (1 : ℝ) ≤ timeN τ := by exact_mod_cast one_le_timeN τ
  have hfl : (⌊2 * τ / Real.pi⌋₊ : ℝ) ≤ timeN τ := by
    exact_mod_cast le_max_right 1 ⌊2 * τ / Real.pi⌋₊
  have e : τ / Real.pi = (2 * τ / Real.pi) / 2 := by ring
  by_cases h : 1 ≤ 2 * τ / Real.pi
  · have := half_le_floor h
    linarith
  · have h' := lt_of_not_ge h
    linarith

/-- `c > 0` (proof of Lemma `hsl:lem:time`). -/
theorem timeC_pos (hτ : 0 < τ) : 0 < timeC τ := by
  have hn : (0 : ℝ) < timeN τ := Nat.cast_pos.mpr (one_le_timeN τ)
  exact lt_min one_pos (div_pos (mul_pos Real.pi_pos hn) (by linarith))

/-- `c ≤ 1` (proof of Lemma `hsl:lem:time`). -/
theorem timeC_le_one (τ : ℝ) : timeC τ ≤ 1 := min_le_left _ _

/-- The time family's amplitude is at least `1/2` (Lemma `hsl:lem:time`: exactly
one for `τ ≥ π/2`, `sin τ ≥ sin 1 > 1/2` otherwise). -/
theorem half_le_timeAmp (hτ : 1 ≤ τ) :
    1 / 2 ≤ Real.sin (timeC τ * τ / timeN τ) ^ timeN τ := by
  rcases le_or_gt (Real.pi / 2) τ with hge | hlt
  · rw [timeC_mul_div_timeN hge, Real.sin_pi_div_two, one_pow]
    norm_num
  · rw [timeC_eq_one_of_lt (by linarith) hlt, timeN_eq_one_of_lt hlt, Nat.cast_one, div_one,
      one_mul, pow_one]
    have hpi := Real.two_le_pi
    have := Real.sin_le_sin_of_le_of_le_pi_div_two (x := 1) (y := τ) (by linarith) hlt.le hτ
    linarith [half_lt_sin_one]

/-- `√m > √s/2` from `m > s/4` (eq. `hsl:eq:mrange`; `s ≥ 2` suffices). -/
theorem sqrt_div_two_lt_sqrt_hsM (hs : 2 ≤ s) :
    Real.sqrt s / 2 < Real.sqrt ((2 : ℝ) ^ hsMu s) := by
  have h := lt_two_pow_hsMu_add_two hs
  have h' : (s : ℝ) < (2 : ℝ) ^ (hsMu s + 2) := by exact_mod_cast h
  rw [pow_add] at h'
  norm_num at h'
  have h4 : (Real.sqrt s / 2) ^ 2 = (s : ℝ) / 4 := by
    rw [div_pow, Real.sq_sqrt (by positivity)]; norm_num
  rw [Real.lt_sqrt (by positivity), h4]
  linarith

/-- **Eq. `hsl:eq:timelower`, arithmetic** (Lemma `hsl:lem:time`):
`n ≥ τ/π` and `m > s/4` turn `(log 2/96) n √m` into `c_T √s τ`. -/
theorem time_final (hτ : 1 ≤ τ) (hs : 32 ≤ s) :
    cT * Real.sqrt s * τ ≤ Real.log 2 / 96 * timeN τ * Real.sqrt ((2 : ℝ) ^ hsMu s) := by
  have hτ0 : 0 < τ := by linarith
  have hpi := Real.pi_pos
  have h1 := tau_div_pi_le_timeN hτ0
  have h2 := (sqrt_div_two_lt_sqrt_hsM (by omega : 2 ≤ s)).le
  have hl : 0 < Real.log 2 := Real.log_pos one_lt_two
  have key : τ / Real.pi * (Real.sqrt s / 2) ≤ timeN τ * Real.sqrt ((2 : ℝ) ^ hsMu s) :=
    mul_le_mul h1 h2 (by positivity) (by positivity)
  have e : cT * Real.sqrt s * τ = Real.log 2 / 96 * (τ / Real.pi * (Real.sqrt s / 2)) := by
    unfold cT; field_simp; ring
  rw [e, mul_assoc (Real.log 2 / 96)]
  exact mul_le_mul_of_nonneg_left key (div_nonneg hl.le (by norm_num))

/-! ### Mixed and precision families -/

/-- `sin(τ/n) > 0` for `0 < τ ≤ n`. -/
theorem sin_div_pos (hn : 1 ≤ n) (hτ : 0 < τ) (hτn : τ ≤ n) : 0 < Real.sin (τ / n) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  apply Real.sin_pos_of_pos_of_lt_pi (div_pos hτ hn')
  have : τ / n ≤ 1 := by rw [div_le_one₀ hn']; exact hτn
  linarith [Real.two_le_pi]

/-- `A = sin(τ/n)^n ≥ (τ/(2n))^n` for `0 < τ ≤ n` (proof of Lemma `hsl:lem:mixed`). -/
theorem amp_ge (hn : 1 ≤ n) (hτ : 0 < τ) (hτn : τ ≤ n) :
    (τ / (2 * n)) ^ n ≤ Real.sin (τ / n) ^ n := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have h01 : τ / n ≤ 1 := by rw [div_le_one₀ hn']; exact hτn
  have e : τ / (2 * n) = (τ / n) / 2 := by ring
  apply pow_le_pow_left₀ (div_nonneg hτ.le (by positivity)) _ n
  rw [e]
  exact sin_ge_half_mul (div_pos hτ hn').le h01

/-- The search-lemma hypothesis for `β₀ = A/2` (proof of Lemma `hsl:lem:mixed`). -/
theorem mixed_hyp (hn : 2 ≤ n) (hτ : 0 < τ) (hτn : τ ≤ n) :
    4 * (Real.sin (τ / n) ^ n / 2) ^ (-(1 : ℝ) / n) ≤ 16 * n / τ := by
  have hn1 : 1 ≤ n := by omega
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn1
  have hn0 : (n : ℝ) ≠ 0 := hn'.ne'
  have hsin := sin_div_pos hn1 hτ hτn
  have h01 : τ / n ≤ 1 := by rw [div_le_one₀ hn']; exact hτn
  have hge := sin_ge_half_mul (div_pos hτ hn').le h01
  rw [pow_div_two_rpow_neg_inv hn1 hsin]
  have h2 := two_rpow_inv_le_two hn1
  have hA : 4 * ((2 : ℝ) ^ (1 / (n : ℝ)) / Real.sin (τ / n)) ≤ 8 / Real.sin (τ / n) := by
    rw [mul_div_assoc', div_le_div_iff_of_pos_right hsin]; linarith
  have hB : 8 / Real.sin (τ / n) ≤ 16 * n / τ := by
    rw [div_le_div_iff₀ hsin hτ]
    calc 8 * τ = 16 * n * (τ / n / 2) := by field_simp; ring
      _ ≤ 16 * n * Real.sin (τ / n) := mul_le_mul_of_nonneg_left hge (by positivity)
  linarith

/-- `β₀^{1/(2n)} ≥ ½ √(τ/n)` for `β₀ = A/2` (proof of Lemma `hsl:lem:mixed`). -/
theorem mixed_root (hn : 2 ≤ n) (hτ : 0 < τ) (hτn : τ ≤ n) :
    1 / 2 * Real.sqrt (τ / n) ≤ (Real.sin (τ / n) ^ n / 2) ^ (1 / (2 * (n : ℝ))) := by
  have hn1 : 1 ≤ n := by omega
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn1
  have hsin := sin_div_pos hn1 hτ hτn
  have h01 : τ / n ≤ 1 := by rw [div_le_one₀ hn']; exact hτn
  have hge := sin_ge_half_mul (div_pos hτ hn').le h01
  rw [pow_div_two_rpow_root hn1 hsin]
  have h2 := inv_sqrt_two_le_two_rpow hn1
  have hs2 : Real.sqrt (τ / n / 2) ≤ Real.sqrt (Real.sin (τ / n)) := Real.sqrt_le_sqrt hge
  have h22 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have e : 1 / 2 * Real.sqrt (τ / n) = 1 / Real.sqrt 2 * Real.sqrt (τ / n / 2) := by
    rw [Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 2)]
    calc 1 / 2 * Real.sqrt (τ / n) = Real.sqrt (τ / n) / (Real.sqrt 2 * Real.sqrt 2) := by
          rw [h22]; ring
      _ = 1 / Real.sqrt 2 * (Real.sqrt (τ / n) / Real.sqrt 2) := by ring
  rw [e]
  exact mul_le_mul h2 hs2 (Real.sqrt_nonneg _) (by positivity)

/-! ### Main parameters, `L ≥ 64τ` -/

/-- `log(e + 64) ≤ 8`, the base case of `log_exp_add_le` (proof of Theorem `hsl:thm:main`). -/
theorem log_exp_add_sixtyfour_le : Real.log (Real.exp 1 + 64) ≤ 8 := by
  rw [Real.log_le_iff_le_exp (by positivity)]
  have h1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have h3 : Real.exp 8 = Real.exp 1 ^ 7 * Real.exp 1 := by
    rw [← pow_succ, ← Real.exp_nat_mul]; norm_num
  have h4 : (128 : ℝ) ≤ Real.exp 1 ^ 7 :=
    calc (128 : ℝ) = 2 ^ 7 := by norm_num
      _ ≤ Real.exp 1 ^ 7 := pow_le_pow_left₀ (by norm_num) h1 7
  rw [h3]
  nlinarith [mul_le_mul_of_nonneg_right h4 (by linarith : (0 : ℝ) ≤ Real.exp 1)]

/-- `log(e + z) ≤ z/8` for `z ≥ 64` (proof of Theorem `hsl:thm:main`). -/
theorem log_exp_add_le (z : ℝ) (hz : 64 ≤ z) : Real.log (Real.exp 1 + z) ≤ z / 8 := by
  have he := Real.exp_pos 1
  have hA : 0 < Real.exp 1 + 64 := by positivity
  have hB : 0 < Real.exp 1 + z := by linarith
  have hsplit : Real.log (Real.exp 1 + z) =
      Real.log (Real.exp 1 + 64) + Real.log ((Real.exp 1 + z) / (Real.exp 1 + 64)) := by
    rw [Real.log_div hB.ne' hA.ne']; ring
  have hq := Real.log_le_sub_one_of_pos (div_pos hB hA)
  have hq2 : (Real.exp 1 + z) / (Real.exp 1 + 64) - 1 ≤ (z - 64) / 8 := by
    rw [div_sub_one hA.ne', div_le_div_iff₀ hA (by norm_num)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hz) (by linarith : (0 : ℝ) ≤ Real.exp 1 + 56)]
  linarith [log_exp_add_sixtyfour_le]

/-- `h ≤ z/8 = L/(8τ)` when `z = L/τ ≥ 64` (proof of Theorem `hsl:thm:main`). -/
theorem HSRange.hsH_le (h : HSRange τ s ε) (hL : 64 * τ ≤ hsL ε) :
    hsH τ ε ≤ hsL ε / (8 * τ) := by
  have hτ := h.tau_pos
  have hz : 64 ≤ hsL ε / τ := by rw [le_div_iff₀ hτ]; exact hL
  have := log_exp_add_le _ hz
  unfold hsH
  calc _ ≤ hsL ε / τ / 8 := this
    _ = hsL ε / (8 * τ) := by rw [div_div, mul_comm]

/-- `r ≥ 8τ` (proof of Theorem `hsl:thm:main`). -/
theorem hsR_ge_eight_tau (h : HSRange τ s ε) (hL : 64 * τ ≤ hsL ε) : 8 * τ ≤ hsR τ ε := by
  have hτ := h.tau_pos
  have hle := h.hsH_le hL
  rw [le_div_iff₀ (by positivity)] at hle
  unfold hsR
  rw [le_div_iff₀ h.hsH_pos]
  linarith

/-- **Eq. `hsl:eq:nrange`** (eq. `hsl:eq:nrange`): `n ≥ 2`, `n ≥ r/8 ≥ τ`, `n ≤ r/4`. -/
theorem precN_range (h : HSRange τ s ε) (hL : 64 * τ ≤ hsL ε) :
    2 ≤ precN τ ε ∧ hsR τ ε / 8 ≤ precN τ ε ∧ τ ≤ hsR τ ε / 8 ∧
      (precN τ ε : ℝ) ≤ hsR τ ε / 4 := by
  have hτ1 := h.one_le_tau
  have hr := hsR_ge_eight_tau h hL
  refine ⟨?_, ?_, by linarith, h.precN_le_quarter⟩
  · unfold precN
    apply Nat.le_floor
    push_cast
    linarith
  · have := half_le_floor (x := hsR τ ε / 4) (by linarith)
    unfold precN
    linarith

/-- `r ≤ 8n` (proof of Theorem `hsl:thm:main`). -/
theorem hsR_le_eight_precN (h : HSRange τ s ε) (hL : 64 * τ ≤ hsL ε) :
    hsR τ ε ≤ 8 * precN τ ε := by
  have := (precN_range h hL).2.1
  linarith

/-- `2n/τ ≤ z/(2h) ≤ e + z` (proof of Theorem `hsl:thm:main`); holds for all parameters in range. -/
theorem two_precN_div_le (h : HSRange τ s ε) :
    2 * (precN τ ε : ℝ) / τ ≤ Real.exp 1 + hsL ε / τ := by
  have hτ := h.tau_pos
  have h1 := h.precN_le_quarter
  have h2 := h.hsR_le_hsL
  have hL := h.hsL_pos
  have he := Real.exp_pos 1
  have : 2 * (precN τ ε : ℝ) / τ ≤ hsL ε / τ :=
    (div_le_div_iff_of_pos_right hτ).mpr (by linarith)
  linarith

/-- `log(2n/τ) ≤ h` (proof of Theorem `hsl:thm:main`; at `n = 0` the left side is `log 0 = 0`). -/
theorem log_two_precN_div_le (h : HSRange τ s ε) :
    Real.log (2 * precN τ ε / τ) ≤ hsH τ ε := by
  rcases Nat.eq_zero_or_pos (precN τ ε) with h0 | hpos
  · rw [h0]
    simp only [Nat.cast_zero, mul_zero, zero_div, Real.log_zero]
    exact h.hsH_pos.le
  · unfold hsH
    have hn : (0 : ℝ) < precN τ ε := by exact_mod_cast hpos
    exact Real.log_le_log (div_pos (by linarith) h.tau_pos) (two_precN_div_le h)

/-- **Eq. `hsl:eq:precisionchoice`** (eq. `hsl:eq:precisionchoice`): `n log(2n/τ) ≤ nh ≤ L/4`
(for all parameters in range). -/
theorem precision_exp_bound (h : HSRange τ s ε) :
    (precN τ ε : ℝ) * Real.log (2 * precN τ ε / τ) ≤ precN τ ε * hsH τ ε ∧
      (precN τ ε : ℝ) * hsH τ ε ≤ hsL ε / 4 := by
  refine ⟨mul_le_mul_of_nonneg_left (log_two_precN_div_le h) (Nat.cast_nonneg _), ?_⟩
  have h1 := h.precN_le_quarter
  have h2 := h.hsR_mul_hsH
  have h3 := h.hsH_pos
  calc (precN τ ε : ℝ) * hsH τ ε ≤ hsR τ ε / 4 * hsH τ ε :=
        mul_le_mul_of_nonneg_right h1 h3.le
    _ = hsL ε / 4 := by rw [← h2]; ring

/-- `(τ/(2n))^n ≥ e^{-L/4}` (proof of Theorem `hsl:thm:main`; at `n = 0` the left side is `1`). -/
theorem exp_neg_quarter_le_pow (h : HSRange τ s ε) :
    Real.exp (-(hsL ε / 4)) ≤ (τ / (2 * precN τ ε)) ^ precN τ ε := by
  have hτ := h.tau_pos
  rcases Nat.eq_zero_or_pos (precN τ ε) with h0 | hpos
  · rw [h0, pow_zero, Real.exp_le_one_iff]
    have := h.hsL_pos
    linarith
  · have hn : (0 : ℝ) < precN τ ε := by exact_mod_cast hpos
    have hx : 0 < τ / (2 * precN τ ε) := div_pos hτ (by linarith)
    have hb := precision_exp_bound h
    have e : Real.log (τ / (2 * precN τ ε)) = -Real.log (2 * precN τ ε / τ) := by
      rw [← Real.log_inv, inv_div]
    rw [← Real.exp_log (pow_pos hx _), Real.log_pow, e]
    apply Real.exp_le_exp.mpr
    linarith [hb.1, hb.2]

/-- `e^{-L/4} ≥ 16 e^{-L}` for `L ≥ 4` (`e³ > 16`; the paper uses `L ≥ 64`,
proof of Theorem `hsl:thm:main` and proof of Lemma `odel:lem:herald`). -/
theorem exp_neg_quarter_ge {L : ℝ} (hL : 4 ≤ L) : 16 * Real.exp (-L) ≤ Real.exp (-(L / 4)) := by
  have h1 : Real.exp (-(L / 4)) = Real.exp (3 * L / 4) * Real.exp (-L) := by
    rw [← Real.exp_add]; congr 1; ring
  have he : (11 / 10 : ℝ) ≤ Real.exp (1 / 10) := by
    have := Real.add_one_le_exp (1 / 10 : ℝ); norm_num at this ⊢; linarith
  have h3 : Real.exp 3 = Real.exp (1 / 10) ^ 30 := by
    rw [← Real.exp_nat_mul]; norm_num
  have h16 : (16 : ℝ) ≤ Real.exp 3 := by
    rw [h3]
    have := pow_le_pow_left₀ (by norm_num) he 30
    norm_num at this; linarith
  have h34 : Real.exp 3 ≤ Real.exp (3 * L / 4) := Real.exp_le_exp.mpr (by linarith)
  rw [h1]
  exact mul_le_mul_of_nonneg_right (h16.trans h34) (Real.exp_pos _).le

/-- **Eq. `hsl:eq:precisionchoice`** and the line after it (proof of Theorem `hsl:thm:main`),
in the form `(τ/(2n))^n ≥ e^{-L/4} ≥ 16ε` used by both Lemma `hsl:lem:mixed`
(which needs `8ε`) and Lemma `odel:lem:herald`. -/
theorem sixteen_eps_le (h : HSRange τ s ε) (_hL : 64 * τ ≤ hsL ε) :
    16 * ε ≤ (τ / (2 * precN τ ε)) ^ precN τ ε := by
  have h1 := exp_neg_quarter_ge h.four_le_hsL
  rw [exp_neg_hsL h.eps_pos] at h1
  exact h1.trans (exp_neg_quarter_le_pow h)

/-- **Eq. `hsl:eq:rbound`** (eq. `hsl:eq:rbound`): `n/4 ≥ r/32`. -/
theorem rbound (h : HSRange τ s ε) (hL : 64 * τ ≤ hsL ε) :
    hsR τ ε / 32 ≤ (precN τ ε : ℝ) / 4 := by
  have := hsR_le_eight_precN h hL
  linarith

/-- The mixed family's condition `m ≥ 16n/τ` when `s ≥ 64n/τ` (proof of Theorem `hsl:thm:main`). -/
theorem mixed_m_cond (h : HSRange τ s ε) (hs : 64 * (precN τ ε : ℝ) / τ ≤ s) :
    16 * (precN τ ε : ℝ) / τ ≤ (2 : ℝ) ^ hsMu s := by
  have hm := (hsM_range h.s_ge).2.1
  have e : 16 * (precN τ ε : ℝ) / τ = (64 * (precN τ ε : ℝ) / τ) / 4 := by ring
  rw [e]
  linarith

/-- `sτr ≤ 32 mnτ` from `s < 4m` and `r ≤ 8n` (eq. `hsl:eq:mixrbound`). -/
theorem s_mul_hsR_le (h : HSRange τ s ε) (hL : 64 * τ ≤ hsL ε) :
    (s : ℝ) * τ * hsR τ ε ≤ 32 * ((2 : ℝ) ^ hsMu s * precN τ ε * τ) := by
  have hm := (hsM_range h.s_ge).2.1
  have hr := hsR_le_eight_precN h hL
  have hτ := h.tau_pos
  have hr0 := h.hsR_pos
  have hs4 : (s : ℝ) ≤ 4 * (2 : ℝ) ^ hsMu s := by linarith
  have hmpos : (0 : ℝ) < (2 : ℝ) ^ hsMu s := by positivity
  calc (s : ℝ) * τ * hsR τ ε ≤ (4 * (2 : ℝ) ^ hsMu s) * τ * hsR τ ε :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hs4 hτ.le) hr0.le
    _ ≤ (4 * (2 : ℝ) ^ hsMu s) * τ * (8 * precN τ ε) :=
        mul_le_mul_of_nonneg_left hr (mul_pos (by positivity) hτ).le
    _ = 32 * ((2 : ℝ) ^ hsMu s * precN τ ε * τ) := by ring

/-- **Eq. `hsl:eq:mixrbound`** (eq. `hsl:eq:mixrbound`):
`(log 2/96)√(mnτ) ≥ (log 2/(384√2))√(sτr)`. -/
theorem mixrbound (h : HSRange τ s ε) (hL : 64 * τ ≤ hsL ε) :
    Real.log 2 / (384 * Real.sqrt 2) * Real.sqrt (s * τ * hsR τ ε) ≤
      Real.log 2 / 96 * Real.sqrt ((2 : ℝ) ^ hsMu s * precN τ ε * τ) := by
  have hle := s_mul_hsR_le h hL
  have h1 : Real.sqrt (s * τ * hsR τ ε) ≤
      Real.sqrt 32 * Real.sqrt ((2 : ℝ) ^ hsMu s * precN τ ε * τ) := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 32)]
    exact Real.sqrt_le_sqrt hle
  have h32 : Real.sqrt 32 = 4 * Real.sqrt 2 := by
    rw [show (32 : ℝ) = 4 ^ 2 * 2 by norm_num, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4 ^ 2),
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4)]
  have hl : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hs2 : 0 < Real.sqrt 2 := by positivity
  have hs2' : Real.sqrt 2 ≠ 0 := hs2.ne'
  rw [h32] at h1
  calc Real.log 2 / (384 * Real.sqrt 2) * Real.sqrt (s * τ * hsR τ ε)
      ≤ Real.log 2 / (384 * Real.sqrt 2) *
          (4 * Real.sqrt 2 * Real.sqrt ((2 : ℝ) ^ hsMu s * precN τ ε * τ)) :=
        mul_le_mul_of_nonneg_left h1 (div_nonneg hl.le (by positivity))
    _ = Real.log 2 / 96 * Real.sqrt ((2 : ℝ) ^ hsMu s * precN τ ε * τ) := by
        field_simp; ring

/-- `sτr < 512 n²` when `s < 64n/τ` (proof of Theorem `hsl:thm:main`). -/
theorem s_mul_hsR_lt (h : HSRange τ s ε) (hL : 64 * τ ≤ hsL ε)
    (hs : (s : ℝ) < 64 * precN τ ε / τ) :
    (s : ℝ) * τ * hsR τ ε < 512 * (precN τ ε : ℝ) ^ 2 := by
  have hτ := h.tau_pos
  have hr0 := h.hsR_pos
  have hr := hsR_le_eight_precN h hL
  have hsτ : (s : ℝ) * τ < 64 * precN τ ε := by rwa [lt_div_iff₀ hτ] at hs
  have hn0 : (0 : ℝ) ≤ precN τ ε := Nat.cast_nonneg _
  calc (s : ℝ) * τ * hsR τ ε < 64 * precN τ ε * hsR τ ε := mul_lt_mul_of_pos_right hsτ hr0
    _ ≤ 64 * precN τ ε * (8 * precN τ ε) := mul_le_mul_of_nonneg_left hr (by positivity)
    _ = 512 * (precN τ ε : ℝ) ^ 2 := by ring

/-- **Eq. `hsl:eq:failedmix`** (proof of Theorem `hsl:thm:main`): if `s < 64n/τ` then
`n/4 ≥ √(sτr)/(64√2)`. -/
theorem failedmix (h : HSRange τ s ε) (hL : 64 * τ ≤ hsL ε)
    (hs : (s : ℝ) < 64 * precN τ ε / τ) :
    Real.sqrt (s * τ * hsR τ ε) / (64 * Real.sqrt 2) ≤ (precN τ ε : ℝ) / 4 := by
  have hlt := s_mul_hsR_lt h hL hs
  have hn0 : (0 : ℝ) ≤ precN τ ε := Nat.cast_nonneg _
  have h1 : Real.sqrt (s * τ * hsR τ ε) ≤ 16 * Real.sqrt 2 * precN τ ε := by
    have e : Real.sqrt (512 * (precN τ ε : ℝ) ^ 2) = 16 * Real.sqrt 2 * precN τ ε := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 512), Real.sqrt_sq hn0,
        show (512 : ℝ) = 16 ^ 2 * 2 by norm_num,
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 16 ^ 2), Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 16)]
    rw [← e]
    exact Real.sqrt_le_sqrt hlt.le
  have hs2 : 0 < Real.sqrt 2 := by positivity
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  linarith

end

end SparseLowerBounds.Hamiltonian
end
