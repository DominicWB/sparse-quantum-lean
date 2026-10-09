import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Bit lengths of public parameters and the word budget `𝔟`

Theorem `ode:thm:gates` of the accompanying paper states its gate and qubit budgets (equations
`ode:eq:gate-main` and `ode:eq:gate-space`) in the word budget
`𝔟 = b_data + log(N+1) + log(M+1) + log(m+1) + log((q ḡ + 1)/ε)` (equation
`ode:eq:gate-word-budget`), where `b_data` bounds the bit lengths of the represented entries and
of the public parameters; equation `hs:eq:gate-binary` of Theorem `hs:thm:gates` is a polynomial
in `b_data`, `log(N+1)` and `log((q+1)/ε)`. This file fixes the bit-length model and the base of
the logarithm.

* `HasBits b x`: `x` is a signed fixed-point number with `b` integer and `b` fractional bits,
  `x = n / 2^b` with `|n| < 2^(2b)`; equivalently, `x` is an integer multiple of `2^(-b)` with
  `|x| < 2^b` (`hasBits_iff`). A fixed-point word with `i` integer and `f` fractional bits has
  bit length `i + f` in this sense (`hasBits_fixed`), an integer of `i` bits has `i`
  (`hasBits_int`), every dyadic rational has some bit length (`exists_hasBits`), and the bit
  length is monotone (`HasBits.mono`). The consequences used: `|x| < 2^b` (`HasBits.abs_lt`,
  `HasBits.lt`), and for `x ≠ 0`: `1 ≤ 2^b |x|` (`HasBits.one_le_mul_abs`,
  `HasBits.one_le_mul`), hence `|log₂ |x|| ≤ b` (`HasBits.abs_logb_le`).
* `bitB bd N M m q g ε = bd + log₂(N+1) + log₂(M+1) + log₂(m+1) + log₂((q g + 1)/ε)`: the
  paper's `𝔟` with base-2 logarithms; `bitH bd N q ε = bd + log₂(N+1) + log₂((q+1)/ε)`: the
  argument of equation `hs:eq:gate-binary` (`bitH_eq`: `bitH bd N q ε = bitB bd N 0 0 q 1 ε`).
  Since `log₂ x = log x / log 2`, the cubic bounds in `𝔟` hold in the paper's natural-log `𝔟`
  with the constants multiplied by at most `(1/log 2)³ < 3.01` (`(1/log 2)⁴ < 4.34` for the forms
  over a finite gate set); the proofs use the converse `log x ≤ log₂ x` for `x ≥ 1`
  (`log_le_logb`).
  The budgets are nonnegative (`bitB_nonneg`, `bitH_nonneg`, `logb_succ_nonneg`) and `𝔟` grows
  with the time mesh and the number of source nodes (`bitB_mono`).
* Word estimates: `⌈log₂ ⌈y⌉⌉ ≤ B + 1` for `y ≤ 2^B` (`clog_ceil_le`, `clog_ceil_le_logb`,
  `clog_ceil_le_nat`), and the forms used for the register words of the constructions:
  `clog_le_mul_pow` (`⌈log₂ ⌈y⌉⌉ ≤ n + p log₂ X + 1` for `y ≤ c X^p`, `c ≤ 2^n`),
  `nat_le_mul_pow` (`w ≤ n + p log₂ X` for `2^w ≤ c X^p`), `logb_le_mul_pow`,
  `logb_two_pow_mul_pow` and `nat_le_logb` (`w ≤ log₂(2^w + 1)`).
* Polynomial bounds: `cube_le` (`(w+1)³ ≤ (c+1)³ (B+1)³` for `w ≤ c (B+1)`) and `budget_mono`
  (budgets of the form `c g (Q a + S₁ + S₂)`).
-/

set_option autoImplicit false

namespace SparseHamiltonian.GateBitBudget

noncomputable section

/-! ### Fixed-point bit lengths -/

/-- **The fixed-point bit length** of a public real parameter: `x` is a signed fixed-point number
with `b` integer bits and `b` fractional bits, `x = n / 2^b` for an integer `n` with
`|n| < 2^(2b)`. -/
def HasBits (b : ℕ) (x : ℝ) : Prop :=
  ∃ n : ℤ, |(n : ℝ)| < 2 ^ (2 * b) ∧ x = n / 2 ^ b

/-- `HasBits b x` iff `x` is an integer multiple of `2^(-b)` with `|x| < 2^b`. -/
theorem hasBits_iff (b : ℕ) (x : ℝ) :
    HasBits b x ↔ (∃ n : ℤ, x = n / 2 ^ b) ∧ |x| < 2 ^ b := by
  have h2 : (0 : ℝ) < 2 ^ b := by positivity
  have e : (2 : ℝ) ^ (2 * b) = 2 ^ b * 2 ^ b := by rw [two_mul, pow_add]
  constructor
  · rintro ⟨n, hn, rfl⟩
    refine ⟨⟨n, rfl⟩, ?_⟩
    rw [abs_div, abs_of_pos h2, div_lt_iff₀ h2, ← e]
    exact hn
  · rintro ⟨⟨n, rfl⟩, hx⟩
    refine ⟨n, ?_, rfl⟩
    rw [abs_div, abs_of_pos h2, div_lt_iff₀ h2, ← e] at hx
    exact hx

namespace HasBits

variable {b : ℕ} {x : ℝ}

/-- A parameter of bit length `b` has `|x| < 2^b`. -/
theorem abs_lt (h : HasBits b x) : |x| < 2 ^ b := ((hasBits_iff b x).mp h).2

/-- A parameter of bit length `b` has `x < 2^b`. -/
theorem lt (h : HasBits b x) : x < 2 ^ b := (le_abs_self x).trans_lt h.abs_lt

/-- A nonzero parameter of bit length `b` has `|x| ≥ 2^(-b)`: `1 ≤ 2^b |x|`. -/
theorem one_le_mul_abs (h : HasBits b x) (hx : x ≠ 0) : 1 ≤ 2 ^ b * |x| := by
  obtain ⟨n, -, rfl⟩ := h
  have h2 : (0 : ℝ) < 2 ^ b := by positivity
  have hn : n ≠ 0 := by
    rintro rfl
    simp at hx
  have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hn
  rw [abs_div, abs_of_pos h2, mul_div_cancel₀ _ h2.ne']
  exact h1

/-- A positive parameter of bit length `b` has `x ≥ 2^(-b)`: `1 ≤ 2^b x`. -/
theorem one_le_mul (h : HasBits b x) (hx : 0 < x) : 1 ≤ 2 ^ b * x := by
  have h1 := h.one_le_mul_abs hx.ne'
  rwa [abs_of_pos hx] at h1

/-- **The logarithm of a nonzero parameter of bit length `b`**: `|log₂ |x|| ≤ b`. -/
theorem abs_logb_le (h : HasBits b x) (hx : x ≠ 0) : abs (Real.logb 2 |x|) ≤ b := by
  have hpos : 0 < |x| := abs_pos.mpr hx
  have h2 : (0 : ℝ) < 2 ^ b := by positivity
  rw [abs_le]
  constructor
  · have h1 := h.one_le_mul_abs hx
    have e : Real.logb 2 (2 ^ b * |x|) = b + Real.logb 2 |x| := by
      rw [Real.logb_mul h2.ne' hpos.ne', Real.logb_pow, Real.logb_self_eq_one one_lt_two,
        mul_one]
    have h3 : 0 ≤ Real.logb 2 (2 ^ b * |x|) := Real.logb_nonneg one_lt_two h1
    linarith
  · have h3 : Real.logb 2 |x| ≤ Real.logb 2 (2 ^ b) :=
      Real.logb_le_logb_of_le one_lt_two hpos h.abs_lt.le
    rwa [Real.logb_pow, Real.logb_self_eq_one one_lt_two, mul_one] at h3

/-- The bit length is monotone. -/
theorem mono {b' : ℕ} (h : HasBits b x) (hb : b ≤ b') : HasBits b' x := by
  rw [hasBits_iff] at h ⊢
  obtain ⟨⟨n, rfl⟩, hx⟩ := h
  refine ⟨⟨n * 2 ^ (b' - b), ?_⟩, hx.trans_le (pow_le_pow_right₀ (by norm_num) hb)⟩
  have e : (2 : ℝ) ^ b' = 2 ^ b * 2 ^ (b' - b) := by
    rw [← pow_add, Nat.add_sub_cancel' hb]
  push_cast
  rw [e, mul_div_mul_right _ _ (by positivity : (2 : ℝ) ^ (b' - b) ≠ 0)]

end HasBits

/-- Zero has every bit length. -/
theorem hasBits_zero (b : ℕ) : HasBits b 0 :=
  ⟨0, by rw [Int.cast_zero, abs_zero]; positivity, by rw [Int.cast_zero, zero_div]⟩

/-- **Fixed-point words**: a signed word `x = n / 2^f` with `i` integer bits and `f` fractional
bits, `|n| < 2^(i+f)`, has bit length `i + f`. -/
theorem hasBits_fixed (i f : ℕ) (n : ℤ) (hn : |(n : ℝ)| < 2 ^ (i + f)) :
    HasBits (i + f) ((n : ℝ) / 2 ^ f) := by
  rw [hasBits_iff]
  have h2 : (0 : ℝ) < 2 ^ f := by positivity
  constructor
  · refine ⟨n * 2 ^ i, ?_⟩
    push_cast
    rw [show i + f = f + i by ring, pow_add,
      mul_div_mul_right _ _ (by positivity : (2 : ℝ) ^ i ≠ 0)]
  · rw [abs_div, abs_of_pos h2, div_lt_iff₀ h2]
    calc |(n : ℝ)| < 2 ^ (i + f) := hn
      _ ≤ 2 ^ (i + f) * 2 ^ f :=
        le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by norm_num))

/-- **Integers**: an integer with `|n| < 2^i` has bit length `i`. -/
theorem hasBits_int (i : ℕ) (n : ℤ) (hn : |(n : ℝ)| < 2 ^ i) : HasBits i (n : ℝ) := by
  have h := hasBits_fixed i 0 n (by rwa [Nat.add_zero])
  rwa [Nat.add_zero, pow_zero, div_one] at h

/-- **Every dyadic rational has a bit length.** -/
theorem exists_hasBits (n : ℤ) (f : ℕ) : ∃ b : ℕ, HasBits b ((n : ℝ) / 2 ^ f) := by
  refine ⟨n.natAbs + f, hasBits_fixed _ _ n ?_⟩
  have h1 : ((n.natAbs : ℕ) : ℝ) < 2 ^ n.natAbs := by exact_mod_cast Nat.lt_two_pow_self
  have h2 : (2 : ℝ) ^ n.natAbs ≤ 2 ^ (n.natAbs + f) :=
    pow_le_pow_right₀ (by norm_num) (Nat.le_add_right _ _)
  have e : |(n : ℝ)| = ((n.natAbs : ℕ) : ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  rw [e]
  linarith

/-! ### The word budget -/

/-- **The word budget `𝔟`** of equation `ode:eq:gate-word-budget`, with base-2 logarithms:
`𝔟 = b_data + log₂(N+1) + log₂(M+1) + log₂(m+1) + log₂((q ḡ + 1)/ε)` for the bit lengths
`b_data = bd`, the dimension `N`, the power-of-two time mesh `M`, the number `m` of source nodes,
the query shape `q`, the amplification bound `ḡ = g` and the accuracy `ε`. -/
def bitB (bd N M m : ℕ) (q g ε : ℝ) : ℝ :=
  bd + Real.logb 2 ((N : ℝ) + 1) + Real.logb 2 ((M : ℝ) + 1) + Real.logb 2 ((m : ℝ) + 1) +
    Real.logb 2 ((q * g + 1) / ε)

/-- **The argument of equation `hs:eq:gate-binary`**: `b_data + log₂(N+1) + log₂((q+1)/ε)`. -/
def bitH (bd N : ℕ) (q ε : ℝ) : ℝ :=
  bd + Real.logb 2 ((N : ℝ) + 1) + Real.logb 2 ((q + 1) / ε)

/-- `bitH` is `𝔟` without time mesh and source nodes, at `ḡ = 1`. -/
theorem bitH_eq (bd N : ℕ) (q ε : ℝ) : bitH bd N q ε = bitB bd N 0 0 q 1 ε := by
  simp only [bitH, bitB, Nat.cast_zero, zero_add, Real.logb_one, add_zero, mul_one]

/-- The logarithmic terms `log₂(n+1)` of `𝔟` are nonnegative. -/
theorem logb_succ_nonneg (n : ℕ) : 0 ≤ Real.logb 2 ((n : ℝ) + 1) :=
  Real.logb_nonneg one_lt_two (by have := n.cast_nonneg (α := ℝ); linarith)

/-- `𝔟` grows with the time mesh and the number of source nodes. -/
theorem bitB_mono (bd N M m M' m' : ℕ) (q g ε : ℝ) (hM : M ≤ M') (hm : m ≤ m') :
    bitB bd N M m q g ε ≤ bitB bd N M' m' q g ε := by
  have hM' : (M : ℝ) ≤ M' := by exact_mod_cast hM
  have hm' : (m : ℝ) ≤ m' := by exact_mod_cast hm
  have h1 : Real.logb 2 ((M : ℝ) + 1) ≤ Real.logb 2 ((M' : ℝ) + 1) :=
    Real.logb_le_logb_of_le one_lt_two (by positivity) (by linarith)
  have h2 : Real.logb 2 ((m : ℝ) + 1) ≤ Real.logb 2 ((m' : ℝ) + 1) :=
    Real.logb_le_logb_of_le one_lt_two (by positivity) (by linarith)
  unfold bitB
  linarith

/-- `𝔟 ≥ 0` for `q ḡ ≥ 0` and `0 < ε ≤ 1`. -/
theorem bitB_nonneg (bd N M m : ℕ) {q g ε : ℝ} (hqg : 0 ≤ q * g) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    0 ≤ bitB bd N M m q g ε := by
  have h1 : 1 ≤ (q * g + 1) / ε := by
    rw [le_div_iff₀ hε]
    linarith
  have h2 := Real.logb_nonneg one_lt_two h1
  have h3 := logb_succ_nonneg N
  have h4 := logb_succ_nonneg M
  have h5 := logb_succ_nonneg m
  have h6 : (0 : ℝ) ≤ bd := Nat.cast_nonneg _
  unfold bitB
  linarith

/-- The argument of `hs:eq:gate-binary` is nonnegative for `q ≥ 0` and `0 < ε ≤ 1`. -/
theorem bitH_nonneg (bd N : ℕ) {q ε : ℝ} (hq : 0 ≤ q) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    0 ≤ bitH bd N q ε := by
  rw [bitH_eq]
  exact bitB_nonneg bd N 0 0 (by rw [mul_one]; exact hq) hε hε1

/-- `log x ≤ log₂ x` for `x ≥ 1`: the base-2 budget dominates the natural-logarithm one. -/
theorem log_le_logb (x : ℝ) (hx : 1 ≤ x) : Real.log x ≤ Real.logb 2 x := by
  have h0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have h2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have h21 : Real.log 2 ≤ 1 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have := Real.add_one_le_exp 1
    linarith
  rw [← Real.log_div_log, le_div_iff₀ h2]
  nlinarith

/-! ### Word estimates -/

/-- `⌈log₂ ⌈y⌉⌉ ≤ n` for `y ≤ 2^n`. -/
theorem clog_ceil_le_nat (y : ℝ) (n : ℕ) (h : y ≤ 2 ^ n) : Nat.clog 2 ⌈y⌉₊ ≤ n := by
  apply Nat.clog_le_of_le_pow
  apply Nat.ceil_le.mpr
  exact_mod_cast h

/-- **`⌈log₂ ⌈y⌉⌉ ≤ B + 1` for `y ≤ 2^B`**, `B ≥ 0` real. -/
theorem clog_ceil_le (y B : ℝ) (hB : 0 ≤ B) (h : y ≤ (2 : ℝ) ^ B) :
    (Nat.clog 2 ⌈y⌉₊ : ℝ) ≤ B + 1 := by
  have h1 : (2 : ℝ) ^ B ≤ (2 : ℝ) ^ ((⌈B⌉₊ : ℕ) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil B)
  rw [Real.rpow_natCast] at h1
  have h2 := clog_ceil_le_nat y ⌈B⌉₊ (h.trans h1)
  have h3 : ((Nat.clog 2 ⌈y⌉₊ : ℕ) : ℝ) ≤ (⌈B⌉₊ : ℝ) := by exact_mod_cast h2
  have h4 := Nat.ceil_lt_add_one hB
  linarith

/-- `⌈log₂ ⌈y⌉⌉ ≤ log₂ y + 1` for `y ≥ 1`. -/
theorem clog_ceil_le_logb (y : ℝ) (hy : 1 ≤ y) :
    (Nat.clog 2 ⌈y⌉₊ : ℝ) ≤ Real.logb 2 y + 1 :=
  clog_ceil_le y _ (Real.logb_nonneg one_lt_two hy)
    (le_of_eq (Real.rpow_logb (by norm_num) (by norm_num) (by linarith)).symm)

/-- `log₂ (2^n X^p) = n + p log₂ X`. -/
theorem logb_two_pow_mul_pow (n p : ℕ) (X : ℝ) (hX : 0 < X) :
    Real.logb 2 ((2 : ℝ) ^ n * X ^ p) = n + p * Real.logb 2 X := by
  rw [Real.logb_mul (by positivity) (by positivity), Real.logb_pow, Real.logb_pow,
    Real.logb_self_eq_one one_lt_two, mul_one]

/-- **The logarithm of a product bound**: `log₂ y ≤ n + p log₂ X` for `0 < y ≤ c X^p` with
`c ≤ 2^n` and `X ≥ 1`. -/
theorem logb_le_mul_pow (y c X : ℝ) (n p : ℕ) (hy : 0 < y) (hX : 1 ≤ X) (hc : c ≤ 2 ^ n)
    (h : y ≤ c * X ^ p) : Real.logb 2 y ≤ n + p * Real.logb 2 X := by
  have hX0 : 0 < X := by linarith
  have h1 : y ≤ (2 : ℝ) ^ n * X ^ p :=
    h.trans (mul_le_mul_of_nonneg_right hc (by positivity))
  rw [← logb_two_pow_mul_pow n p X hX0]
  exact Real.logb_le_logb_of_le one_lt_two hy h1

/-- **A word given by a power of two**: `w ≤ n + p log₂ X` for `2^w ≤ c X^p` with `c ≤ 2^n` and
`X ≥ 1`. -/
theorem nat_le_mul_pow (w : ℕ) (c X : ℝ) (n p : ℕ) (hX : 1 ≤ X) (hc : c ≤ 2 ^ n)
    (h : ((2 ^ w : ℕ) : ℝ) ≤ c * X ^ p) : (w : ℝ) ≤ n + p * Real.logb 2 X := by
  have h2 := logb_le_mul_pow _ c X n p (by positivity) hX hc h
  rwa [Nat.cast_pow, Nat.cast_ofNat, Real.logb_pow, Real.logb_self_eq_one one_lt_two,
    mul_one] at h2

/-- **A word given by a ceiling logarithm**: `⌈log₂ ⌈y⌉⌉ ≤ n + p log₂ X + 1` for `y ≤ c X^p` with
`c ≤ 2^n` and `X ≥ 1`. -/
theorem clog_le_mul_pow (y c X : ℝ) (n p : ℕ) (hX : 1 ≤ X) (hc : c ≤ 2 ^ n)
    (h : y ≤ c * X ^ p) : (Nat.clog 2 ⌈y⌉₊ : ℝ) ≤ n + p * Real.logb 2 X + 1 := by
  have hX0 : 0 < X := by linarith
  have hY : 1 ≤ (2 : ℝ) ^ n * X ^ p :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (one_le_pow₀ hX)
  have h1 : y ≤ (2 : ℝ) ^ n * X ^ p := h.trans (mul_le_mul_of_nonneg_right hc (by positivity))
  have h2 : Nat.clog 2 ⌈y⌉₊ ≤ Nat.clog 2 ⌈(2 : ℝ) ^ n * X ^ p⌉₊ :=
    Nat.clog_mono_right 2 (Nat.ceil_mono h1)
  have h3 := clog_ceil_le_logb _ hY
  rw [logb_two_pow_mul_pow n p X hX0] at h3
  have h4 : ((Nat.clog 2 ⌈y⌉₊ : ℕ) : ℝ) ≤ (Nat.clog 2 ⌈(2 : ℝ) ^ n * X ^ p⌉₊ : ℕ) := by
    exact_mod_cast h2
  linarith

/-- **The word of a power-of-two count**: `w ≤ log₂(2^w + 1)`. -/
theorem nat_le_logb (w : ℕ) : (w : ℝ) ≤ Real.logb 2 (((2 ^ w : ℕ) : ℝ) + 1) := by
  have h := Real.logb_le_logb_of_le one_lt_two (by positivity : (0 : ℝ) < 2 ^ w)
    (by push_cast; linarith : (2 : ℝ) ^ w ≤ ((2 ^ w : ℕ) : ℝ) + 1)
  rwa [Real.logb_pow, Real.logb_self_eq_one one_lt_two, mul_one] at h

/-! ### Polynomial bounds -/

/-- **Cubes of linear bounds**: `(w + 1)^3 ≤ (c + 1)^3 (B + 1)^3` for `0 ≤ w ≤ c (B + 1)` and
`B ≥ 0`. -/
theorem cube_le {w B c : ℝ} (hw : 0 ≤ w) (hB : 0 ≤ B) (h : w ≤ c * (B + 1)) :
    (w + 1) ^ 3 ≤ (c + 1) ^ 3 * (B + 1) ^ 3 := by
  have h1 : w + 1 ≤ (c + 1) * (B + 1) := by nlinarith
  rw [← mul_pow]
  exact pow_le_pow_left₀ (by linarith) h1 3

/-- **Budgets of the form `c g (Q a + S₁ + S₂)`**: `c g (Q a + S₁ + S₂) ≤ C g (Q b + S₁ + S₂)`
for `a ≤ k b`, `1 ≤ k`, `c k ≤ C` and nonnegative data. -/
theorem budget_mono {c C k g Q a b S₁ S₂ : ℝ} (hc : 0 ≤ c) (hg : 0 ≤ g) (hQ : 0 ≤ Q)
    (hb : 0 ≤ b) (hS₁ : 0 ≤ S₁) (hS₂ : 0 ≤ S₂) (hk : 1 ≤ k) (hab : a ≤ k * b) (hcC : c * k ≤ C) :
    c * g * (Q * a + S₁ + S₂) ≤ C * g * (Q * b + S₁ + S₂) := by
  have h1 : Q * a ≤ Q * (k * b) := mul_le_mul_of_nonneg_left hab hQ
  have hY : 0 ≤ Q * b + S₁ + S₂ := by positivity
  have h2 : Q * a + S₁ + S₂ ≤ k * (Q * b + S₁ + S₂) := by nlinarith
  have h3 : c * g * (Q * a + S₁ + S₂) ≤ c * g * (k * (Q * b + S₁ + S₂)) :=
    mul_le_mul_of_nonneg_left h2 (mul_nonneg hc hg)
  have h4 : c * g * (k * (Q * b + S₁ + S₂)) = (c * k) * (g * (Q * b + S₁ + S₂)) := by ring
  have h5 : (c * k) * (g * (Q * b + S₁ + S₂)) ≤ C * (g * (Q * b + S₁ + S₂)) :=
    mul_le_mul_of_nonneg_right hcC (mul_nonneg hg hY)
  have h6 : C * (g * (Q * b + S₁ + S₂)) = C * g * (Q * b + S₁ + S₂) := by ring
  linarith

end

end SparseHamiltonian.GateBitBudget
