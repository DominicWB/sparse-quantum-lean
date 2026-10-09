import ChebyshevLinearSystemFinite.Degree
import ChebyshevLinearSystem.Cost
import Mathlib.Analysis.Real.Pi.Bounds

set_option autoImplicit false

/-!
# The explicit filtering constants (Remark `qls:rem:constants`)

Put `y = g/√s ∈ (0, 1]` and `h₀ = arcosh 100`. With `arsinh u ≥ u/√(1 + u²)` (from the
released `artanh b ≥ b` and `artanh b_σ = arsinh χ_σ`):

* equation `qls:eq:testconstant`: the finite test degree satisfies
  `d^fin_σ(1/100) ≤ ((h₀/2) √((165/4)² + 1) + 2)/y` (`finDegree_hundred_le`, including the
  integer rounding and the extra degree for finite gates) `< 112/y` (`finDegree_hundred_lt`,
  `testconstant_lt`: `h₀ ≤ log 200 < 5.32643`, `arcosh_hundred_lt`);
* `finDegree_le_kStages`: for `δ ≤ 1/100` and `k = ⌈log(1/δ)/log 100⌉` (`kStages`),
  `cosh(k a) ≥ cosh(a)^k` (`cosh_pow_le`) gives `arcosh(1/δ) ≤ k arcosh 100`
  (`arcosh_le_kStages`), hence `d^fin_σ(δ) ≤ k d^fin_σ(1/100)`;
* the averaging comparison: the averaging filter with the angle bound `ω = g/(512√s)` and
  `N = ⌈100π/ω⌉` uses `q_av = ⌈51200π/y⌉ - 1` forward steps (`qAv`), `q_av ≥ (51200π - 1)/y`
  (`qAv_ge`), so `1400 d^fin_σ(1/100) < q_av` (`averaging_ratio`) and, for the final filter,
  `1400 d^fin_σ(δ) < k q_av` (`averaging_ratio_final`).

For the protocol: `dTestF_lt` (`d^fin_j < 112 √s 2^j`, at the public gap `σ_j = 2^{-j}`) and
`dFinF_le` (`d^fin_fin ≤ k · 112 √s κ ≤ 168 √s κ log(1/ε)`, at the public gap `1/κ`).
-/

namespace ChebyshevLinearSystemFinite

noncomputable section
open SparseHamiltonian SparseLinearSystems Augmented ChebyshevFilter Endpoint
  ChebyshevLinearSystem

/-! ### Elementary bounds -/

/-- `log 200 < 5.32643`: `log 200 = 8 log 2 - log(32/25)` and `log(32/25) ≥ 1 - 25/32`. -/
theorem log_two_hundred_lt : Real.log 200 < 532643 / 100000 := by
  have h1 : Real.log 200 = 8 * Real.log 2 - Real.log (32 / 25) := by
    rw [show (200 : ℝ) = 2 ^ 8 / (32 / 25) by norm_num, Real.log_div (by norm_num) (by norm_num),
      Real.log_pow]
    norm_num
  have h2 := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 32 / 25 by norm_num)
  have h3 := Real.log_two_lt_d9
  rw [h1]
  norm_num at h2 h3 ⊢
  linarith

/-- `h₀ = arcosh 100 ≤ log 200 < 5.32643`. -/
theorem arcosh_hundred_lt : Real.arcosh 100 < 532643 / 100000 := by
  have h := arcosh_le_log (show (1 : ℝ) ≤ 100 by norm_num)
  rw [show (2 : ℝ) * 100 = 200 by norm_num] at h
  linarith [log_two_hundred_lt]

/-- `arsinh u ≥ u / √(1 + u²)` for `u = χ`, from `artanh b ≥ b` at `b = χ/√(1 + χ²)`. -/
theorem div_sqrt_le_arsinh_chi (s : ℝ) {g : ℝ} (hg : 0 ≤ g) :
    chi s g / Real.sqrt (1 + chi s g ^ 2) ≤ Real.arsinh (chi s g) := by
  have h := le_artanh (bLow_nonneg s hg) (bLow_lt_one s g)
  rw [artanh_bLow] at h
  exact h

/-! ### The test constant -/

/-- **Equation `qls:eq:testconstant`, exact form**: for `y = g/√s ∈ (0, 1]` and
`h₀ = arcosh 100`, `d^fin_σ(1/100) ≤ ((h₀/2) √((165/4)² + 1) + 2)/y`, rounding and the extra
degree for finite gates included. -/
theorem finDegree_hundred_le {s g : ℝ} (hs : 0 < s) (hg0 : 0 < g) (hg : g ≤ Real.sqrt s) :
    (finDegree s g (1 / 100) : ℝ) ≤
      (Real.arcosh 100 / 2 * Real.sqrt ((165 / 4) ^ 2 + 1) + 2) * (Real.sqrt s / g) := by
  have hsq : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have hχ := chi_pos hs hg0
  have hA := arsinh_chi_pos hs hg0
  have hR : 1 ≤ Real.sqrt s / g := by rw [le_div_iff₀ hg0]; linarith
  have hχR : chi s g * (Real.sqrt s / g) = 4 / 165 := by
    unfold chi
    field_simp
  generalize Real.sqrt s / g = R at hR hχR ⊢
  have hχ1 : chi s g ≤ 4 / 165 := by nlinarith
  have hc0 : 0 < Real.sqrt ((165 / 4) ^ 2 + 1) := Real.sqrt_pos.mpr (by norm_num)
  generalize hc : Real.sqrt ((165 / 4) ^ 2 + 1) = c at hc0 ⊢
  -- `√(1 + χ²) ≤ c R χ`
  have hroot : Real.sqrt (1 + chi s g ^ 2) ≤ c * R * chi s g := by
    have hcR : c * R * chi s g = Real.sqrt (((165 / 4) ^ 2 + 1) * (R * chi s g) ^ 2) := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity), hc]
      ring
    rw [hcR]
    apply Real.sqrt_le_sqrt
    rw [show R * chi s g = 4 / 165 by linarith]
    nlinarith
  -- `arsinh χ ≥ χ / √(1 + χ²) ≥ 1/(c R)`
  have hcR0 : 0 < c * R := by positivity
  have hAc : 1 ≤ Real.arsinh (chi s g) * (c * R) := by
    have h1 := div_sqrt_le_arsinh_chi s hg0.le
    have h2 : chi s g / (c * R * chi s g) ≤ chi s g / Real.sqrt (1 + chi s g ^ 2) :=
      div_le_div_of_nonneg_left hχ.le (Real.sqrt_pos.mpr (by positivity)) hroot
    have h3 : chi s g / (c * R * chi s g) = 1 / (c * R) := by
      field_simp
    rw [h3] at h2
    have h4 := h2.trans h1
    rwa [div_le_iff₀ hcR0] at h4
  have h0 : 0 ≤ Real.arcosh 100 := Real.arcosh_nonneg (by norm_num)
  have hq : Real.arcosh 100 / (2 * Real.arsinh (chi s g)) ≤ Real.arcosh 100 / 2 * c * R := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hAc h0]
  have hceil : (augDegree s g (1 / 100) : ℝ) <
      Real.arcosh 100 / (2 * Real.arsinh (chi s g)) + 1 := by
    unfold augDegree
    rw [show (1 : ℝ) / (1 / 100) = 100 by norm_num]
    exact Nat.ceil_lt_add_one (by positivity)
  unfold finDegree
  push_cast
  nlinarith

/-- **The numerical test constant**: `(h₀/2) √((165/4)² + 1) + 2 < 112`, from
`h₀ < 5.32643` and `√((165/4)² + 1) ≤ 41.2622`. -/
theorem testconstant_lt : Real.arcosh 100 / 2 * Real.sqrt ((165 / 4) ^ 2 + 1) + 2 < 112 := by
  have h1 := arcosh_hundred_lt
  have h2 : Real.sqrt ((165 / 4) ^ 2 + 1) ≤ 412622 / 10000 := by
    calc Real.sqrt ((165 / 4) ^ 2 + 1) ≤ Real.sqrt ((412622 / 10000) ^ 2) :=
          Real.sqrt_le_sqrt (by norm_num)
      _ = 412622 / 10000 := Real.sqrt_sq (by norm_num)
  have h0 : 0 ≤ Real.arcosh 100 := Real.arcosh_nonneg (by norm_num)
  have h3 : 0 ≤ Real.sqrt ((165 / 4) ^ 2 + 1) := Real.sqrt_nonneg _
  nlinarith [mul_le_mul h1.le h2 h3 (by norm_num)]

/-- **Equation `qls:eq:testconstant`**: for `y = g/√s ∈ (0, 1]`,
`d^fin_σ(1/100) = d_σ(1/100) + 1 < 112/y`, rounding and the extra degree included. -/
theorem finDegree_hundred_lt {s g : ℝ} (hs : 0 < s) (hg0 : 0 < g) (hg : g ≤ Real.sqrt s) :
    (finDegree s g (1 / 100) : ℝ) < 112 * Real.sqrt s / g := by
  have hsq : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have h := finDegree_hundred_le hs hg0 hg
  calc (finDegree s g (1 / 100) : ℝ)
      ≤ (Real.arcosh 100 / 2 * Real.sqrt ((165 / 4) ^ 2 + 1) + 2) * (Real.sqrt s / g) := h
    _ < 112 * (Real.sqrt s / g) := mul_lt_mul_of_pos_right testconstant_lt (by positivity)
    _ = 112 * Real.sqrt s / g := by ring

/-! ### The final degree -/

/-- `cosh(a)^k ≤ cosh(k a)` for `a ≥ 0`. -/
theorem cosh_pow_le (a : ℝ) (ha : 0 ≤ a) (k : ℕ) : Real.cosh a ^ k ≤ Real.cosh (k * a) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, show ((k + 1 : ℕ) : ℝ) * a = k * a + a by push_cast; ring, Real.cosh_add]
    have h1 : 0 ≤ Real.sinh (k * a) * Real.sinh a :=
      mul_nonneg (Real.sinh_nonneg_iff.mpr (mul_nonneg (Nat.cast_nonneg k) ha))
        (Real.sinh_nonneg_iff.mpr ha)
    have h2 := Real.cosh_pos a
    nlinarith [mul_le_mul_of_nonneg_right ih h2.le]

/-- The number `k = ⌈log(1/δ)/log 100⌉` of factors `1/100` in a target `δ` (Remark
`qls:rem:constants`). -/
def kStages (δ : ℝ) : ℕ := ⌈Real.log (1 / δ) / Real.log 100⌉₊

/-- `arcosh(1/δ) ≤ k arcosh 100`, from `cosh(k h₀) ≥ cosh(h₀)^k = 100^k ≥ 1/δ`. -/
theorem arcosh_le_kStages {δ : ℝ} (hδ0 : 0 < δ) :
    Real.arcosh (1 / δ) ≤ kStages δ * Real.arcosh 100 := by
  have h100 : (0 : ℝ) < Real.log 100 := Real.log_pos (by norm_num)
  have hk : Real.log (1 / δ) ≤ kStages δ * Real.log 100 := by
    have := Nat.le_ceil (Real.log (1 / δ) / Real.log 100)
    rw [div_le_iff₀ h100] at this
    exact this
  have h1 : 1 / δ ≤ 100 ^ kStages δ := by
    have h := Real.exp_le_exp.mpr hk
    rwa [Real.exp_log (by positivity), ← Real.log_pow, Real.exp_log (by positivity)] at h
  have h2 : (100 : ℝ) ^ kStages δ ≤ Real.cosh (kStages δ * Real.arcosh 100) := by
    have := cosh_pow_le (Real.arcosh 100) (Real.arcosh_nonneg (by norm_num)) (kStages δ)
    rwa [Real.cosh_arcosh (by norm_num)] at this
  have h0 : 0 ≤ (kStages δ : ℝ) * Real.arcosh 100 :=
    mul_nonneg (Nat.cast_nonneg _) (Real.arcosh_nonneg (by norm_num))
  calc Real.arcosh (1 / δ) ≤ Real.arcosh (Real.cosh (kStages δ * Real.arcosh 100)) :=
        (Real.arcosh_le_arcosh (by positivity) (Real.cosh_pos _)).mpr (h1.trans h2)
    _ = kStages δ * Real.arcosh 100 := Real.arcosh_cosh h0

theorem one_le_kStages {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) : 1 ≤ kStages δ := by
  unfold kStages
  apply Nat.ceil_pos.mpr
  apply div_pos (Real.log_pos _) (Real.log_pos (by norm_num))
  rw [lt_div_iff₀ hδ0]
  linarith

/-- **The final degree in units of the test degree** (Remark `qls:rem:constants`): for
`0 < δ ≤ 1/100` and `k = ⌈log(1/δ)/log 100⌉`, `d^fin_σ(δ) ≤ k d^fin_σ(1/100)`. -/
theorem finDegree_le_kStages {s g δ : ℝ} (hs : 0 < s) (hg : 0 < g) (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1 / 100) : finDegree s g δ ≤ kStages δ * finDegree s g (1 / 100) := by
  have hA := arsinh_chi_pos hs hg
  have hk1 := one_le_kStages hδ0 (by linarith)
  have hd : augDegree s g δ ≤ kStages δ * augDegree s g (1 / 100) := by
    unfold augDegree
    rw [Nat.ceil_le]
    push_cast
    have h1 := arcosh_le_kStages hδ0
    rw [show (1 : ℝ) / (1 / 100) = 100 by norm_num]
    have h2 := Nat.le_ceil (Real.arcosh 100 / (2 * Real.arsinh (chi s g)))
    calc Real.arcosh (1 / δ) / (2 * Real.arsinh (chi s g)) ≤
          kStages δ * Real.arcosh 100 / (2 * Real.arsinh (chi s g)) :=
          div_le_div_of_nonneg_right h1 (by positivity)
      _ = kStages δ * (Real.arcosh 100 / (2 * Real.arsinh (chi s g))) := by ring
      _ ≤ kStages δ * ⌈Real.arcosh 100 / (2 * Real.arsinh (chi s g))⌉₊ :=
          mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg _)
  unfold finDegree
  calc augDegree s g δ + 1 ≤ kStages δ * augDegree s g (1 / 100) + kStages δ :=
        Nat.add_le_add hd hk1
    _ = kStages δ * (augDegree s g (1 / 100) + 1) := by ring

/-! ### The averaging comparison -/

/-- **The averaging budget** of Remark `qls:rem:constants`: an averaging filter with the
conservative angle bound `ω = g/(512√s)` and `N = ⌈100π/ω⌉` uses `q_av = ⌈51200π/y⌉ - 1`
forward walk steps, `y = g/√s`. -/
def qAv (s g : ℝ) : ℕ := ⌈51200 * Real.pi * Real.sqrt s / g⌉₊ - 1

/-- `q_av ≥ (51200π - 1)/y`. -/
theorem qAv_ge {s g : ℝ} (hs : 0 < s) (hg0 : 0 < g) (hg : g ≤ Real.sqrt s) :
    (51200 * Real.pi - 1) * Real.sqrt s / g ≤ qAv s g := by
  have hsq : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have hR : 1 ≤ Real.sqrt s / g := by rw [le_div_iff₀ hg0]; linarith
  have hpos : 0 < 51200 * Real.pi * Real.sqrt s / g := by
    have := Real.pi_pos
    positivity
  have h1 : 1 ≤ ⌈51200 * Real.pi * Real.sqrt s / g⌉₊ := Nat.ceil_pos.mpr hpos
  have h2 := Nat.le_ceil (51200 * Real.pi * Real.sqrt s / g)
  unfold qAv
  rw [Nat.cast_sub h1, Nat.cast_one]
  have e : (51200 * Real.pi - 1) * Real.sqrt s / g =
      51200 * Real.pi * Real.sqrt s / g - Real.sqrt s / g := by ring
  rw [e]
  linarith

/-- **The averaging comparison** (Remark `qls:rem:constants`): for `y = g/√s ∈ (0, 1]`,
`1400 d^fin_σ(1/100) < q_av`, since `d^fin_σ(1/100) < 112/y` and `q_av ≥ (51200π - 1)/y`. -/
theorem averaging_ratio {s g : ℝ} (hs : 0 < s) (hg0 : 0 < g) (hg : g ≤ Real.sqrt s) :
    1400 * (finDegree s g (1 / 100) : ℝ) < qAv s g := by
  have hsq : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have h1 := finDegree_hundred_lt hs hg0 hg
  have h2 := qAv_ge hs hg0 hg
  have hpi := Real.pi_gt_d2
  have hR : 1 ≤ Real.sqrt s / g := by rw [le_div_iff₀ hg0]; linarith
  have e1 : 112 * Real.sqrt s / g = 112 * (Real.sqrt s / g) := by ring
  have e2 : (51200 * Real.pi - 1) * Real.sqrt s / g = (51200 * Real.pi - 1) * (Real.sqrt s / g) :=
    by ring
  rw [e1] at h1
  rw [e2] at h2
  nlinarith

/-- **The averaging comparison for the final filter**: for `0 < δ ≤ 1/100`,
`1400 d^fin_σ(δ) < k q_av` (the repeated averaging schedule costs `k q_av`). -/
theorem averaging_ratio_final {s g δ : ℝ} (hs : 0 < s) (hg0 : 0 < g) (hg : g ≤ Real.sqrt s)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 100) :
    1400 * (finDegree s g δ : ℝ) < kStages δ * (qAv s g : ℝ) := by
  have h1 : (finDegree s g δ : ℝ) ≤ kStages δ * (finDegree s g (1 / 100) : ℝ) := by
    exact_mod_cast finDegree_le_kStages hs hg0 hδ0 hδ1
  have h2 := averaging_ratio hs hg0 hg
  have hk : (1 : ℝ) ≤ kStages δ := by exact_mod_cast one_le_kStages hδ0 (by linarith)
  nlinarith

/-! ### The degrees of the protocol -/

/-- **Test degrees of the finite-degree protocol**: `d^fin_j < 112 √s 2^j` (equation
`qls:eq:testconstant` at the public gap `σ_j = 2^{-j}`). -/
theorem dTestF_lt (s : ℕ) (hs : 0 < s) (j : ℕ) :
    (dTestF s j : ℝ) < 112 * Real.sqrt s * 2 ^ j := by
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hsq : 1 ≤ Real.sqrt (s : ℝ) := Real.one_le_sqrt.mpr hs1
  have h := finDegree_hundred_lt (by linarith : (0 : ℝ) < s) (sig_pos j)
    ((sig_le_one j).trans hsq)
  rw [dTestF_eq]
  have e : 112 * Real.sqrt s / sig j = 112 * Real.sqrt s * 2 ^ j := by
    unfold sig
    rw [one_div_pow, div_div_eq_mul_div, div_one]
  rwa [e] at h

/-- `k = ⌈log(1000/ε)/log 100⌉ ≤ 3/2 log(1/ε)` for `0 < ε ≤ 1/10`. -/
theorem kStages_le (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 10) :
    (kStages (ε / 1000) : ℝ) ≤ 3 / 2 * Real.log (1 / ε) := by
  have hL2 := two_le_logInv ε hε hε1
  have h10 := two_le_log_ten
  have h100 : Real.log 100 = 2 * Real.log 10 := by
    rw [show (100 : ℝ) = 10 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have h1000 : Real.log (1 / (ε / 1000)) = 3 * Real.log 10 + Real.log (1 / ε) := by
    rw [show (1 : ℝ) / (ε / 1000) = 10 ^ 3 * (1 / ε) by field_simp; ring,
      Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    norm_num
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ Real.log (1 / (ε / 1000)) / Real.log 100 by
    rw [h1000, h100]
    positivity)
  unfold kStages
  rw [h1000, h100] at hceil ⊢
  have hq : (3 * Real.log 10 + Real.log (1 / ε)) / (2 * Real.log 10) =
      3 / 2 + Real.log (1 / ε) / (2 * Real.log 10) := by
    field_simp
  have hq2 : Real.log (1 / ε) / (2 * Real.log 10) ≤ Real.log (1 / ε) / 4 := by
    apply div_le_div_of_nonneg_left (by linarith) (by norm_num) (by linarith)
  rw [hq] at hceil ⊢
  linarith

/-- **The final degree of the finite-degree protocol**:
`d^fin_fin ≤ k · 112 √s κ ≤ 168 √s κ log(1/ε)`. -/
theorem dFinF_le (s : ℕ) (hs : 0 < s) (κ ε : ℝ) (hκ : 1 ≤ κ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 10) :
    (dFinF s κ ε : ℝ) ≤ 168 * Real.sqrt s * κ * Real.log (1 / ε) := by
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hsq : 1 ≤ Real.sqrt (s : ℝ) := Real.one_le_sqrt.mpr hs1
  have hκ0 : 0 < κ := by linarith
  have hg : 1 / κ ≤ Real.sqrt s := by
    have : 1 / κ ≤ 1 := by rw [div_le_one hκ0]; exact hκ
    linarith
  have h1 : (dFinF s κ ε : ℝ) ≤ kStages (ε / 1000) * (finDegree s (1 / κ) (1 / 100) : ℝ) := by
    rw [dFinF_eq]
    exact_mod_cast finDegree_le_kStages (by linarith : (0 : ℝ) < s) (by positivity)
      (by positivity) (by linarith)
  have h2 := finDegree_hundred_lt (by linarith : (0 : ℝ) < s) (by positivity : (0 : ℝ) < 1 / κ) hg
  rw [show 112 * Real.sqrt s / (1 / κ) = 112 * Real.sqrt s * κ by field_simp] at h2
  have hk := kStages_le ε hε hε1
  have hk0 : (0 : ℝ) ≤ kStages (ε / 1000) := Nat.cast_nonneg _
  have hp : 0 ≤ 112 * Real.sqrt s * κ := by positivity
  calc (dFinF s κ ε : ℝ) ≤ kStages (ε / 1000) * (finDegree s (1 / κ) (1 / 100) : ℝ) := h1
    _ ≤ kStages (ε / 1000) * (112 * Real.sqrt s * κ) := mul_le_mul_of_nonneg_left h2.le hk0
    _ ≤ 3 / 2 * Real.log (1 / ε) * (112 * Real.sqrt s * κ) := mul_le_mul_of_nonneg_right hk hp
    _ = 168 * Real.sqrt s * κ * Real.log (1 / ε) := by ring

end

end ChebyshevLinearSystemFinite
