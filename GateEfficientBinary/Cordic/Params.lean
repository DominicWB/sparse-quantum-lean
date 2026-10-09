import GateEfficientBinary.Cordic.Error

/-!
# The parameters of the CORDIC program

For `b`-bit components, a scale `κ > 0` and an accuracy `0 < ζ ≤ 1` we fix the public
parameters of the CORDIC angle program (`params`) and verify the hypotheses of the error
theorems `phi_error` and `theta_error`.

* Each stage takes `n = ⌈log₂ ⌈8 / ζ⌉⌉ + 2` steps, so that `2^(n-1) ζ ≥ 16` and the CORDIC
  residual is `α_(n-1) ≤ 2^(1-n) ≤ ζ / 16`.
* Both output words have `bP = bT = n + ⌈log₂ (n + 2)⌉ + 4` bits, so that
  `2^bP ζ ≥ 512 (n + 2)` and the accumulated rounding `n π / 2^bP` of the angle constants is
  at most `ζ / 128`.
* The angle constants `c₁ k` and `c₂ k` round `α_k` to the nearest multiples of the units
  `2π / 2^bP` and `π / 2^(bT+1)` (`params_c1`, `params_c2`), and `U` rounds `g_n 2^S₂ / κ`
  (`params_U`). With `T = n²` and `S₂ = T + ⌈log₂ ⌈κ⌉⌉ + n + 5` this gives `U ≥ 2^(n+4)`
  (`params_U_ge`), so that the rounding error `1 / (2U)` of the stage-2 scale is at most
  `ζ / 1024`.
* The register width `w = T + S₂ + ⌈log₂ ⌈1/κ⌉⌉ + b + 2 bP + 8` leaves room for every register
  (`params_OK`), and the error bounds of both output words are at most `ζ` (`params_phi`,
  `params_theta`).
-/

set_option autoImplicit false

namespace SparseHamiltonian.GateBinary.Cordic

noncomputable section

/-- Steps per stage for accuracy `ζ`. -/
def nOf (ζ : ℝ) : ℕ := Nat.clog 2 ⌈8 / ζ⌉₊ + 2

/-- Bits of the words for `n` steps. -/
def wordOf (n : ℕ) : ℕ := n + Nat.clog 2 (n + 2) + 4

/-- The extra stage-2 scale for the factor `κ`. -/
def g2Of (n : ℕ) (κ : ℝ) : ℕ := Nat.clog 2 ⌈κ⌉₊ + n + 5

/-- The bits needed for `1 / κ`. -/
def lkOf (κ : ℝ) : ℕ := Nat.clog 2 ⌈1 / κ⌉₊

/-- **The CORDIC parameters** for `b`-bit components, scale `κ` and accuracy `ζ`. -/
def params (b : ℕ) (κ ζ : ℝ) : CParams where
  n := nOf ζ
  b := b
  w := 2 * (nOf ζ * nOf ζ) + g2Of (nOf ζ) κ + lkOf κ + b + 2 * wordOf (nOf ζ) + 8
  T := nOf ζ * nOf ζ
  bP := wordOf (nOf ζ)
  bT := wordOf (nOf ζ)
  U := ⌊gain (nOf ζ) * 2 ^ (g2Of (nOf ζ) κ + nOf ζ * nOf ζ) / κ + 1 / 2⌋₊
  S2 := g2Of (nOf ζ) κ + nOf ζ * nOf ζ
  c1 k := ⌊alpha k * 2 ^ wordOf (nOf ζ) / (2 * Real.pi) + 1 / 2⌋₊
  c2 k := ⌊alpha k * 2 ^ (wordOf (nOf ζ) + 1) / Real.pi + 1 / 2⌋₊

/-! ### Rounding -/

/-- Rounding a nonnegative number to the nearest integer errs by at most `1 / 2`. -/
theorem abs_floor_add_half_sub_le (x : ℝ) (hx : 0 ≤ x) :
    |(⌊x + 1 / 2⌋₊ : ℝ) - x| ≤ 1 / 2 := by
  have h1 := Nat.floor_le (by linarith : (0 : ℝ) ≤ x + 1 / 2)
  have h2 := Nat.lt_floor_add_one (x + 1 / 2)
  rw [abs_le]
  constructor <;> linarith

/-- Rounding `a ≥ 0` to the nearest multiple of `u > 0` errs by at most `u / 2`. -/
theorem abs_round_mul_sub_le (a u : ℝ) (ha : 0 ≤ a) (hu : 0 < u) :
    |(⌊a / u + 1 / 2⌋₊ : ℝ) * u - a| ≤ u / 2 := by
  have h := abs_floor_add_half_sub_le (a / u) (div_nonneg ha hu.le)
  have e : (⌊a / u + 1 / 2⌋₊ : ℝ) * u - a = ((⌊a / u + 1 / 2⌋₊ : ℝ) - a / u) * u := by
    rw [sub_mul, div_mul_cancel₀ a hu.ne']
  rw [e, abs_mul, abs_of_pos hu]
  have := mul_le_mul_of_nonneg_right h hu.le
  linarith

/-! ### The number of steps and the word length -/

/-- There are at least two steps per stage. -/
theorem two_le_nOf (ζ : ℝ) : 2 ≤ nOf ζ := by
  unfold nOf
  omega

/-- The number of steps satisfies `2^(n-1) ζ ≥ 16`. -/
theorem sixteen_le_mul_two_pow_nOf (ζ : ℝ) (hζ : 0 < ζ) : 16 ≤ ζ * 2 ^ (nOf ζ - 1) := by
  have h1 : (⌈8 / ζ⌉₊ : ℝ) ≤ 2 ^ Nat.clog 2 ⌈8 / ζ⌉₊ := by
    exact_mod_cast Nat.le_pow_clog (by norm_num) _
  have h2 : 8 ≤ (⌈8 / ζ⌉₊ : ℝ) * ζ := by
    have := Nat.le_ceil (8 / ζ)
    rwa [div_le_iff₀ hζ] at this
  have h3 : nOf ζ - 1 = Nat.clog 2 ⌈8 / ζ⌉₊ + 1 := by
    unfold nOf
    omega
  have h4 := mul_le_mul_of_nonneg_right h1 hζ.le
  rw [h3, pow_succ]
  linarith

/-- The number of steps satisfies `2^n ζ ≥ 32`. -/
theorem thirtytwo_le_mul_two_pow_nOf (ζ : ℝ) (hζ : 0 < ζ) : 32 ≤ ζ * 2 ^ nOf ζ := by
  have h := sixteen_le_mul_two_pow_nOf ζ hζ
  have e : nOf ζ = nOf ζ - 1 + 1 := by
    have := two_le_nOf ζ
    omega
  rw [e, pow_succ]
  linarith

/-- The CORDIC residual is at most `ζ / 16`. -/
theorem alpha_nOf_le (ζ : ℝ) (hζ : 0 < ζ) : alpha (nOf ζ - 1) ≤ ζ / 16 := by
  have h := sixteen_le_mul_two_pow_nOf ζ hζ
  have h1 := alpha_le (nOf ζ - 1)
  rw [one_div_pow] at h1
  have h2 : 1 / (2 : ℝ) ^ (nOf ζ - 1) ≤ ζ / 16 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  linarith

/-- The words are long: `2^(wordOf n) ≥ 16 (n + 2) 2^n`. -/
theorem le_two_pow_wordOf (n : ℕ) : 16 * (n + 2) * 2 ^ n ≤ 2 ^ wordOf n := by
  have h := Nat.le_pow_clog (by norm_num : 1 < 2) (n + 2)
  unfold wordOf
  rw [pow_add, pow_add]
  calc 16 * (n + 2) * 2 ^ n = 2 ^ n * (n + 2) * 2 ^ 4 := by ring
    _ ≤ 2 ^ n * 2 ^ Nat.clog 2 (n + 2) * 2 ^ 4 := by gcongr

/-- The words are long compared with the accuracy: `2^(wordOf n) ζ ≥ 512 (n + 2)`. -/
theorem le_mul_two_pow_wordOf (ζ : ℝ) (hζ : 0 < ζ) :
    512 * ((nOf ζ : ℝ) + 2) ≤ ζ * 2 ^ wordOf (nOf ζ) := by
  have h1 : 16 * ((nOf ζ : ℝ) + 2) * 2 ^ nOf ζ ≤ 2 ^ wordOf (nOf ζ) := by
    exact_mod_cast le_two_pow_wordOf (nOf ζ)
  have h2 := thirtytwo_le_mul_two_pow_nOf ζ hζ
  have h3 := mul_le_mul_of_nonneg_left h1 hζ.le
  have h4 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 16 * ((nOf ζ : ℝ) + 2))
  linarith

/-- The accumulated rounding of the angle constants: `n π / 2^(wordOf n) ≤ ζ / 128`. -/
theorem nOf_mul_pi_div_le (ζ : ℝ) (hζ : 0 < ζ) :
    (nOf ζ : ℝ) * Real.pi / 2 ^ wordOf (nOf ζ) ≤ ζ / 128 := by
  have h := le_mul_two_pow_wordOf ζ hζ
  have hπ := mul_le_mul_of_nonneg_left Real.pi_le_four (Nat.cast_nonneg (α := ℝ) (nOf ζ))
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  linarith

/-- One unit of the angle words: `π / 2^(wordOf n) ≤ ζ / 256`. -/
theorem pi_div_two_pow_wordOf_le (ζ : ℝ) (hζ : 0 < ζ) :
    Real.pi / 2 ^ wordOf (nOf ζ) ≤ ζ / 256 := by
  have h := le_mul_two_pow_wordOf ζ hζ
  have hn : (0 : ℝ) ≤ nOf ζ := Nat.cast_nonneg _
  have hπ := Real.pi_le_four
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  linarith

/-! ### The scale `U` -/

/-- `U ≥ 2^(n+4)`, as natural numbers. -/
theorem params_U_ge_nat (b : ℕ) (κ ζ : ℝ) (hκ : 0 < κ) :
    2 ^ (nOf ζ + 4) ≤ (params b κ ζ).U := by
  apply Nat.le_floor
  push_cast
  have hL : κ ≤ 2 ^ Nat.clog 2 ⌈κ⌉₊ := by
    have h1 := Nat.le_ceil κ
    have h2 : (⌈κ⌉₊ : ℝ) ≤ 2 ^ Nat.clog 2 ⌈κ⌉₊ := by
      exact_mod_cast Nat.le_pow_clog (by norm_num) _
    linarith
  have hS : (2 : ℝ) ^ (g2Of (nOf ζ) κ + nOf ζ * nOf ζ) =
      2 ^ Nat.clog 2 ⌈κ⌉₊ * 2 ^ (nOf ζ + 5 + nOf ζ * nOf ζ) := by
    rw [← pow_add]
    congr 1
    unfold g2Of
    omega
  have hg := one_le_gain (nOf ζ)
  have key : (2 : ℝ) ^ (nOf ζ + 4) ≤
      gain (nOf ζ) * 2 ^ (g2Of (nOf ζ) κ + nOf ζ * nOf ζ) / κ := by
    rw [le_div_iff₀ hκ, hS]
    have h3 : (2 : ℝ) ^ (nOf ζ + 4) ≤ 2 ^ (nOf ζ + 5 + nOf ζ * nOf ζ) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have h4 := mul_le_mul h3 hL hκ.le (by positivity)
    have h5 := mul_le_mul_of_nonneg_right hg
      (by positivity : (0 : ℝ) ≤ 2 ^ Nat.clog 2 ⌈κ⌉₊ * 2 ^ (nOf ζ + 5 + nOf ζ * nOf ζ))
    linarith
  linarith

/-- `U ≤ 2^(S₂ + ⌈log₂ ⌈1/κ⌉⌉ + 2)`, as natural numbers. -/
theorem params_U_le (b : ℕ) (κ ζ : ℝ) (hκ : 0 < κ) :
    (params b κ ζ).U ≤ 2 ^ (g2Of (nOf ζ) κ + nOf ζ * nOf ζ + lkOf κ + 2) := by
  apply Nat.floor_le_of_le
  have h1 : 1 / κ ≤ 2 ^ lkOf κ := by
    have h2 := Nat.le_ceil (1 / κ)
    have h3 : (⌈1 / κ⌉₊ : ℝ) ≤ 2 ^ lkOf κ := by
      exact_mod_cast Nat.le_pow_clog (by norm_num) _
    linarith
  have hg := gain_le_two (nOf ζ)
  set S := g2Of (nOf ζ) κ + nOf ζ * nOf ζ
  have e : ((2 ^ (S + lkOf κ + 2) : ℕ) : ℝ) = 2 ^ S * 2 ^ lkOf κ * 4 := by
    push_cast
    rw [pow_add, pow_add]
    norm_num
  rw [e]
  have h4 : gain (nOf ζ) * 2 ^ S / κ = gain (nOf ζ) * 2 ^ S * (1 / κ) := by ring
  rw [h4]
  have h5 : gain (nOf ζ) * 2 ^ S * (1 / κ) ≤ 2 * 2 ^ S * 2 ^ lkOf κ :=
    mul_le_mul (mul_le_mul_of_nonneg_right hg (by positivity)) h1 (by positivity)
      (by positivity)
  have h6 : (1 : ℝ) ≤ 2 ^ S * 2 ^ lkOf κ := by
    rw [← pow_add]
    exact one_le_pow₀ (by norm_num)
  linarith

/-! ### The width conditions -/

/-- The words have at least one bit. -/
theorem wordOf_pos (n : ℕ) : 0 < wordOf n := by
  unfold wordOf
  omega

/-- The stage-2 starting values fit in the registers. -/
theorem params_w2 (b : ℕ) (κ ζ : ℝ) (hκ : 0 < κ) :
    2 * ((params b κ ζ).U * 2 ^ (params b κ ζ).T +
      2 ^ ((params b κ ζ).T + (params b κ ζ).b + 1 + (params b κ ζ).S2)) <
        2 ^ ((params b κ ζ).w - 1) := by
  have hU := params_U_le b κ ζ hκ
  dsimp only [params] at hU ⊢
  generalize ⌊gain (nOf ζ) * 2 ^ (g2Of (nOf ζ) κ + nOf ζ * nOf ζ) / κ + 1 / 2⌋₊ = U at hU ⊢
  generalize nOf ζ * nOf ζ = T at hU ⊢
  generalize g2Of (nOf ζ) κ = g at hU ⊢
  generalize lkOf κ = l at hU ⊢
  generalize wordOf (nOf ζ) = W
  have h1 : U * 2 ^ T ≤ 2 ^ (g + T + l + b + 2 + T) :=
    calc U * 2 ^ T ≤ 2 ^ (g + T + l + 2) * 2 ^ T := Nat.mul_le_mul_right _ hU
      _ = 2 ^ (g + T + l + 2 + T) := by rw [← pow_add]
      _ ≤ 2 ^ (g + T + l + b + 2 + T) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 2 ^ (T + b + 1 + (g + T)) ≤ 2 ^ (g + T + l + b + 2 + T) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : 2 ^ (g + T + l + b + 2 + T + 2) < 2 ^ (2 * T + g + l + b + 2 * W + 8 - 1) :=
    Nat.pow_lt_pow_right (by norm_num) (by omega)
  have h4 : 2 ^ (g + T + l + b + 2 + T + 2) = 4 * 2 ^ (g + T + l + b + 2 + T) := by ring
  omega

/-- The stage-1 angle constants are at most `2^bP`. -/
theorem params_c1_le (b : ℕ) (κ ζ : ℝ) (k : ℕ) :
    (params b κ ζ).c1 k ≤ 2 ^ wordOf (nOf ζ) := by
  apply Nat.floor_le_of_le
  push_cast
  have h1 := alpha_le_pi_div_four k
  have h2 : alpha k * 2 ^ wordOf (nOf ζ) / (2 * Real.pi) ≤ 2 ^ wordOf (nOf ζ) / 8 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have := mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ 2 ^ wordOf (nOf ζ) * 8)
    linarith
  have h3 : (1 : ℝ) ≤ 2 ^ wordOf (nOf ζ) := one_le_pow₀ (by norm_num)
  linarith

/-- The stage-1 angle constants fit in the registers. -/
theorem params_c1_lt (b : ℕ) (κ ζ : ℝ) (k : ℕ) :
    (params b κ ζ).c1 k < 2 ^ ((params b κ ζ).w - 1) := by
  refine (params_c1_le b κ ζ k).trans_lt (Nat.pow_lt_pow_right (by norm_num) ?_)
  dsimp only [params]
  omega

/-- The stage-2 angle constants are at most `2^bT`. -/
theorem params_c2_le (b : ℕ) (κ ζ : ℝ) (k : ℕ) :
    (params b κ ζ).c2 k ≤ 2 ^ (params b κ ζ).bT := by
  apply Nat.floor_le_of_le
  dsimp only [params]
  push_cast
  have h1 := alpha_le_pi_div_four k
  have h2 : alpha k * 2 ^ (wordOf (nOf ζ) + 1) / Real.pi ≤ 2 ^ wordOf (nOf ζ) / 2 := by
    rw [div_le_div_iff₀ Real.pi_pos (by norm_num), pow_succ]
    have := mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ 2 ^ wordOf (nOf ζ) * 4)
    linarith
  have h3 : (1 : ℝ) ≤ 2 ^ wordOf (nOf ζ) := one_le_pow₀ (by norm_num)
  linarith

/-- The stage-2 angle register does not overflow. -/
theorem params_acc2 (b : ℕ) (κ ζ : ℝ) :
    (params b κ ζ).n * 2 ^ (params b κ ζ).bT + 2 ^ (params b κ ζ).bT <
      2 ^ ((params b κ ζ).w - 1) := by
  dsimp only [params]
  unfold g2Of
  generalize nOf ζ = n
  generalize wordOf n = W
  have h1 : n + 1 ≤ 2 ^ n := Nat.lt_two_pow_self
  have h2 : 2 ^ n * 2 ^ W <
      2 ^ (2 * (n * n) + (Nat.clog 2 ⌈κ⌉₊ + n + 5) + lkOf κ + b + 2 * W + 8 - 1) := by
    rw [← pow_add]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  calc n * 2 ^ W + 2 ^ W = (n + 1) * 2 ^ W := by ring
    _ ≤ 2 ^ n * 2 ^ W := Nat.mul_le_mul_right _ h1
    _ < _ := h2

/-! ### The main statements -/

/-- **The width conditions** hold for the chosen parameters. -/
theorem params_OK (b : ℕ) (hb : 0 < b) (κ ζ : ℝ) (hκ : 0 < κ) :
    (params b κ ζ).OK := by
  exact
    { n2 := two_le_nOf ζ
      b1 := hb
      T := le_rfl
      S2 := Nat.le_add_left _ _
      bP1 := wordOf_pos _
      bPw := by
        dsimp only [params]
        omega
      U1 := Nat.one_le_two_pow.trans (params_U_ge_nat b κ ζ hκ)
      w1 := by
        dsimp only [params]
        omega
      w2 := params_w2 b κ ζ hκ
      c1 := params_c1_lt b κ ζ
      c2 := params_c2_le b κ ζ
      acc2 := params_acc2 b κ ζ }

/-- **The stage-1 angle constants** `c₁ k` round `α_k` to the nearest multiple of
`2π / 2^bP`. -/
theorem params_c1 (b : ℕ) (κ ζ : ℝ) (k : ℕ) :
    |(c1Z (params b κ ζ) k : ℝ) * (2 * Real.pi / 2 ^ (params b κ ζ).bP) - alpha k| ≤
      (2 * Real.pi / 2 ^ (params b κ ζ).bP) / 2 := by
  have h := abs_round_mul_sub_le (alpha k) (2 * Real.pi / 2 ^ wordOf (nOf ζ)) (alpha_nonneg k)
    (by positivity)
  rw [div_div_eq_mul_div] at h
  rw [c1Z, Int.cast_natCast]
  exact h

/-- **The stage-2 angle constants** `c₂ k` round `α_k` to the nearest multiple of
`π / 2^(bT+1)`. -/
theorem params_c2 (b : ℕ) (κ ζ : ℝ) (k : ℕ) :
    |(c2Z (params b κ ζ) k : ℝ) * (Real.pi / 2 ^ ((params b κ ζ).bT + 1)) - alpha k| ≤
      (Real.pi / 2 ^ ((params b κ ζ).bT + 1)) / 2 := by
  have h := abs_round_mul_sub_le (alpha k) (Real.pi / 2 ^ (wordOf (nOf ζ) + 1))
    (alpha_nonneg k) (by positivity)
  rw [div_div_eq_mul_div] at h
  rw [c2Z, Int.cast_natCast]
  exact h

/-- **The scale** `U` rounds `g_n 2^S₂ / κ` to the nearest integer. -/
theorem params_U (b : ℕ) (κ ζ : ℝ) (hκ : 0 < κ) :
    |((params b κ ζ).U : ℝ) - gain (params b κ ζ).n * 2 ^ (params b κ ζ).S2 / κ| ≤ 1 / 2 :=
  abs_floor_add_half_sub_le _ (div_nonneg (mul_nonneg (gain_pos _).le (by positivity)) hκ.le)

/-- **The scale is large**: `U ≥ 2^(n+4)`. -/
theorem params_U_ge (b : ℕ) (κ ζ : ℝ) (hκ : 0 < κ) :
    (2 : ℝ) ^ ((params b κ ζ).n + 4) ≤ (params b κ ζ).U := by
  exact_mod_cast params_U_ge_nat b κ ζ hκ

/-- **The `φ` error budget** `α_(n-1) + n u₁ / 2` with `u₁ = 2π / 2^bP` is at most `ζ`. -/
theorem params_phi (b : ℕ) (κ ζ : ℝ) (hζ : 0 < ζ) :
    alpha ((params b κ ζ).n - 1) +
      (params b κ ζ).n * (2 * Real.pi / 2 ^ (params b κ ζ).bP) / 2 ≤ ζ := by
  show alpha (nOf ζ - 1) + (nOf ζ : ℝ) * (2 * Real.pi / 2 ^ wordOf (nOf ζ)) / 2 ≤ ζ
  have h1 := alpha_nOf_le ζ hζ
  have h2 := nOf_mul_pi_div_le ζ hζ
  have e : (nOf ζ : ℝ) * (2 * Real.pi / 2 ^ wordOf (nOf ζ)) / 2 =
      (nOf ζ : ℝ) * Real.pi / 2 ^ wordOf (nOf ζ) := by ring
  rw [e]
  linarith

/-- **The `θ` error budget** `2 (α_(n-1) + n u₂ / 2 + (1 / (2U) + α_(n-1)² / 2) + u₂)` with
`u₂ = π / 2^(bT+1)` is at most `ζ`. -/
theorem params_theta (b : ℕ) (κ ζ : ℝ) (hκ : 0 < κ) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) :
    2 * (alpha ((params b κ ζ).n - 1) +
      (params b κ ζ).n * (Real.pi / 2 ^ ((params b κ ζ).bT + 1)) / 2 +
      (1 / (2 * (params b κ ζ).U) + alpha ((params b κ ζ).n - 1) ^ 2 / 2) +
      Real.pi / 2 ^ ((params b κ ζ).bT + 1)) ≤ ζ := by
  have hU : (2 : ℝ) ^ nOf ζ * 16 ≤ (params b κ ζ).U :=
    calc (2 : ℝ) ^ nOf ζ * 16 = 2 ^ (nOf ζ + 4) := by rw [pow_add]; norm_num
      _ ≤ (params b κ ζ).U := params_U_ge b κ ζ hκ
  show 2 * (alpha (nOf ζ - 1) + (nOf ζ : ℝ) * (Real.pi / 2 ^ (wordOf (nOf ζ) + 1)) / 2 +
      (1 / (2 * ((params b κ ζ).U : ℝ)) + alpha (nOf ζ - 1) ^ 2 / 2) +
      Real.pi / 2 ^ (wordOf (nOf ζ) + 1)) ≤ ζ
  have h1 := alpha_nOf_le ζ hζ
  have h0 := alpha_nonneg (nOf ζ - 1)
  have h2 := nOf_mul_pi_div_le ζ hζ
  have h3 := pi_div_two_pow_wordOf_le ζ hζ
  have h32 := thirtytwo_le_mul_two_pow_nOf ζ hζ
  rw [pow_succ (2 : ℝ) (wordOf (nOf ζ))]
  set X : ℝ := 2 ^ wordOf (nOf ζ)
  set U : ℝ := ((params b κ ζ).U : ℝ)
  set a := alpha (nOf ζ - 1)
  -- the rounding of the stage-2 scale
  have hU' : 1 / (2 * U) ≤ ζ / 1024 := by
    have hU0 : 0 < U := lt_of_lt_of_le (by positivity) hU
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    have := mul_le_mul_of_nonneg_left hU hζ.le
    linarith
  -- the second-order term of the residual
  have ha2 : a ^ 2 / 2 ≤ ζ / 512 := by
    have := mul_le_mul_of_nonneg_left (show a ≤ 1 / 16 by linarith) h0
    linarith
  have e1 : (nOf ζ : ℝ) * (Real.pi / (X * 2)) / 2 = (nOf ζ : ℝ) * Real.pi / X / 4 := by ring
  have e2 : Real.pi / (X * 2) = Real.pi / X / 2 := by ring
  rw [e1, e2]
  linarith


attribute [irreducible] nOf wordOf g2Of lkOf

end

end SparseHamiltonian.GateBinary.Cordic
