import GateEfficientBinary.Cordic.Real

/-!
# Integer CORDIC with floor quotients

We compare the integer CORDIC vectoring iteration, in which the multiplications by `2^{-k}` are
replaced by floor quotients by `2^k`, with the exact complex iteration `iter`. An integer point
`(x, y)` is identified with the complex number `x + i y`, and one integer step is
`(x, y) ↦ (x + σ ⌊y / 2^k⌋, y - σ ⌊x / 2^k⌋)`, where `σ = -1` if `y < 0` and `σ = +1` otherwise.
The angle is accumulated with integer constants `c_k`, which approximate `α_k / u` for a unit
angle `u`.

* `toC_re`, `toC_im`, `isgn_eq_sgn`: the real and imaginary parts of `x + i y` are `x` and `y`,
  and the integer direction of `(x, y)` is the complex direction of `x + i y`.
* `toC_citer`: if both coordinates of the starting point are divisible by `2^T` with `n² ≤ T`,
  then every quotient taken in the first `n` steps is exact, so the first `n` integer steps
  reproduce the complex iteration exactly. The proof carries the invariant that after `k ≤ n`
  steps both coordinates are divisible by `2^{T - kn}`.
* `abs_citer_le`: in this regime the coordinates never exceed twice the modulus of the starting
  point, because the CORDIC gain is at most `2`.
* `cacc_error`: if `|c_k u - α_k| ≤ u / 2` for every `k`, then after `m ≤ n` steps the integer
  accumulated angle, scaled by `u`, is within `m u / 2` of the exact accumulated angle.
* `citer_fst`, `citer_fst_nonneg`: after `n` steps the first coordinate equals
  `g_n |z| cos (arg z_n)`, where `z` is the starting point, `g_n` the gain and `z_n` the `n`-th
  complex iterate; it is nonnegative when `z` lies in the closed right half-plane and `n ≥ 2`.
-/

set_option autoImplicit false

namespace SparseHamiltonian.GateBinary.Cordic

noncomputable section

/-! ### The integer iteration -/

/-- The CORDIC direction of an integer point: `-1` strictly below the axis, `+1` otherwise. -/
def isgn (p : ℤ × ℤ) : ℤ := if p.2 < 0 then -1 else 1

/-- One integer CORDIC step with floor quotients by `2^k`. -/
def cstep (k : ℕ) (p : ℤ × ℤ) : ℤ × ℤ :=
  (p.1 + isgn p * (p.2 / 2 ^ k), p.2 - isgn p * (p.1 / 2 ^ k))

/-- The integer CORDIC iterates. -/
def citer (p : ℤ × ℤ) : ℕ → ℤ × ℤ
  | 0 => p
  | k + 1 => cstep k (citer p k)

/-- The complex number of an integer point. -/
def toC (p : ℤ × ℤ) : ℂ := (p.1 : ℂ) + (p.2 : ℂ) * Complex.I

/-- The integer angle accumulator with integer angle constants `c`. -/
def cacc (p : ℤ × ℤ) (c : ℕ → ℤ) (m : ℕ) : ℤ :=
  ∑ k ∈ Finset.range m, isgn (citer p k) * c k

/-- Unfolding one step of the integer iteration. -/
theorem citer_succ (p : ℤ × ℤ) (k : ℕ) : citer p (k + 1) = cstep k (citer p k) := rfl

/-- Unfolding one step of the integer angle accumulator. -/
theorem cacc_succ (p : ℤ × ℤ) (c : ℕ → ℤ) (m : ℕ) :
    cacc p c (m + 1) = cacc p c m + isgn (citer p m) * c m := by
  simp only [cacc, Finset.sum_range_succ]

/-! ### Integer points as complex numbers -/

/-- The real part of an integer point is its first coordinate. -/
theorem toC_re (p : ℤ × ℤ) : (toC p).re = p.1 := by
  simp [toC]

/-- The imaginary part of an integer point is its second coordinate. -/
theorem toC_im (p : ℤ × ℤ) : (toC p).im = p.2 := by
  simp [toC]

/-- The integer direction agrees with the complex direction. -/
theorem isgn_eq_sgn (p : ℤ × ℤ) : ((isgn p : ℤ) : ℝ) = sgn (toC p) := by
  simp only [isgn, sgn, toC_im, Int.cast_lt_zero]
  split_ifs <;> simp

/-- The real part of a complex CORDIC step. -/
theorem step_re (k : ℕ) (z : ℂ) : (step k z).re = z.re + sgn z * (1 / 2 : ℝ) ^ k * z.im := by
  simp only [step, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im]
  ring

/-- The imaginary part of a complex CORDIC step. -/
theorem step_im (k : ℕ) (z : ℂ) : (step k z).im = z.im - sgn z * (1 / 2 : ℝ) ^ k * z.re := by
  simp only [step, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im]
  ring

/-- An exact quotient by `2^k` is multiplication by `2^{-k}`. -/
theorem cast_ediv_two_pow {a : ℤ} {k : ℕ} (h : (2 : ℤ) ^ k ∣ a) :
    ((a / 2 ^ k : ℤ) : ℝ) = (a : ℝ) * (1 / 2 : ℝ) ^ k := by
  rw [Int.cast_div h (by positivity)]
  push_cast
  rw [one_div_pow, mul_one_div]

/-- Dividing a multiple of `2^{a+k}` by `2^k` leaves a multiple of `2^a`. -/
theorem two_pow_dvd_ediv {a k : ℕ} {x : ℤ} (h : (2 : ℤ) ^ (k + a) ∣ x) :
    (2 : ℤ) ^ a ∣ x / 2 ^ k :=
  Int.dvd_ediv_of_mul_dvd (by rwa [← pow_add])

/-- When both coordinates are divisible by `2^k`, the integer step is the exact complex step. -/
theorem toC_cstep (k : ℕ) (q : ℤ × ℤ) (h1 : (2 : ℤ) ^ k ∣ q.1) (h2 : (2 : ℤ) ^ k ∣ q.2) :
    toC (cstep k q) = step k (toC q) := by
  apply Complex.ext
  · rw [step_re, toC_re, toC_re, toC_im, ← isgn_eq_sgn]
    simp only [cstep, Int.cast_add, Int.cast_mul, cast_ediv_two_pow h2]
    ring
  · rw [step_im, toC_im, toC_re, toC_im, ← isgn_eq_sgn]
    simp only [cstep, Int.cast_sub, Int.cast_mul, cast_ediv_two_pow h1]
    ring

/-! ### Exactness -/

/-- The invariant behind `toC_citer`: after `k ≤ n` steps the integer iterate is the complex
iterate, and both of its coordinates are divisible by `2^{T - kn}`. -/
theorem citer_aux (p : ℤ × ℤ) (n T : ℕ) (hT : n * n ≤ T) (h1 : (2 : ℤ) ^ T ∣ p.1)
    (h2 : (2 : ℤ) ^ T ∣ p.2) (k : ℕ) (hk : k ≤ n) :
    toC (citer p k) = iter (toC p) k ∧ (2 : ℤ) ^ (T - k * n) ∣ (citer p k).1 ∧
      (2 : ℤ) ^ (T - k * n) ∣ (citer p k).2 := by
  induction k with
  | zero => simpa [citer, iter] using ⟨h1, h2⟩
  | succ k ih =>
    obtain ⟨he, d1, d2⟩ := ih (by omega)
    have hkn : (k + 1) * n ≤ n * n := Nat.mul_le_mul_right n hk
    have e : (k + 1) * n = k * n + n := Nat.succ_mul k n
    have a1 : k ≤ T - k * n := by omega
    have a2 : k + (T - (k + 1) * n) ≤ T - k * n := by omega
    have a3 : T - (k + 1) * n ≤ T - k * n := by omega
    have q1 : (2 : ℤ) ^ k ∣ (citer p k).1 := (pow_dvd_pow 2 a1).trans d1
    have q2 : (2 : ℤ) ^ k ∣ (citer p k).2 := (pow_dvd_pow 2 a1).trans d2
    refine ⟨?_, ?_, ?_⟩
    · rw [citer_succ, iter_succ, toC_cstep k _ q1 q2, he]
    · rw [citer_succ, cstep]
      exact dvd_add ((pow_dvd_pow 2 a3).trans d1)
        (dvd_mul_of_dvd_right (two_pow_dvd_ediv ((pow_dvd_pow 2 a2).trans d2)) _)
    · rw [citer_succ, cstep]
      exact dvd_sub ((pow_dvd_pow 2 a3).trans d2)
        (dvd_mul_of_dvd_right (two_pow_dvd_ediv ((pow_dvd_pow 2 a2).trans d1)) _)

/-- Exactness: for coordinates divisible by `2^T` with `n * n ≤ T`, the first `n` integer
steps are exact complex CORDIC steps. -/
theorem toC_citer (p : ℤ × ℤ) (n T : ℕ) (hT : n * n ≤ T) (h1 : (2 : ℤ) ^ T ∣ p.1)
    (h2 : (2 : ℤ) ^ T ∣ p.2) (k : ℕ) (hk : k ≤ n) :
    toC (citer p k) = iter (toC p) k :=
  (citer_aux p n T hT h1 h2 k hk).1

/-- Coordinates stay below twice the initial norm. -/
theorem abs_citer_le (p : ℤ × ℤ) (n T : ℕ) (hT : n * n ≤ T) (h1 : (2 : ℤ) ^ T ∣ p.1)
    (h2 : (2 : ℤ) ^ T ∣ p.2) (k : ℕ) (hk : k ≤ n) :
    |((citer p k).1 : ℝ)| ≤ 2 * ‖toC p‖ ∧ |((citer p k).2 : ℝ)| ≤ 2 * ‖toC p‖ := by
  have hn : ‖toC (citer p k)‖ ≤ 2 * ‖toC p‖ := by
    rw [toC_citer p n T hT h1 h2 k hk, norm_iter]
    exact mul_le_mul_of_nonneg_right (gain_le_two k) (norm_nonneg _)
  constructor
  · rw [← toC_re]
    exact (Complex.abs_re_le_norm _).trans hn
  · rw [← toC_im]
    exact (Complex.abs_im_le_norm _).trans hn

/-! ### The accumulated angle -/

/-- In the exact regime the integer directions are the complex directions. -/
theorem isgn_citer (p : ℤ × ℤ) (n T : ℕ) (hT : n * n ≤ T) (h1 : (2 : ℤ) ^ T ∣ p.1)
    (h2 : (2 : ℤ) ^ T ∣ p.2) (k : ℕ) (hk : k ≤ n) :
    ((isgn (citer p k) : ℤ) : ℝ) = sgn (iter (toC p) k) := by
  rw [isgn_eq_sgn, toC_citer p n T hT h1 h2 k hk]

/-- The rounded accumulator is close to the exact one. -/
theorem cacc_error (p : ℤ × ℤ) (n T : ℕ) (hT : n * n ≤ T) (h1 : (2 : ℤ) ^ T ∣ p.1)
    (h2 : (2 : ℤ) ^ T ∣ p.2) (c : ℕ → ℤ) (u : ℝ) (hc : ∀ k, |(c k : ℝ) * u - alpha k| ≤ u / 2)
    (m : ℕ) (hm : m ≤ n) :
    |(cacc p c m : ℝ) * u - acc (toC p) m| ≤ m * u / 2 := by
  induction m with
  | zero => simp [cacc, acc]
  | succ m ih =>
    have hs := isgn_citer p n T hT h1 h2 m (by omega)
    have e : (cacc p c (m + 1) : ℝ) * u - acc (toC p) (m + 1)
        = ((cacc p c m : ℝ) * u - acc (toC p) m)
          + sgn (iter (toC p) m) * ((c m : ℝ) * u - alpha m) := by
      rw [cacc_succ, acc_succ]
      push_cast
      rw [hs]
      ring
    have hb : |sgn (iter (toC p) m) * ((c m : ℝ) * u - alpha m)| ≤ u / 2 := by
      rw [abs_mul, abs_sgn, one_mul]
      exact hc m
    rw [e]
    calc _ ≤ |(cacc p c m : ℝ) * u - acc (toC p) m|
          + |sgn (iter (toC p) m) * ((c m : ℝ) * u - alpha m)| := abs_add_le _ _
      _ ≤ m * u / 2 + u / 2 := add_le_add (ih (by omega)) hb
      _ = ((m + 1 : ℕ) : ℝ) * u / 2 := by push_cast; ring

/-! ### The first coordinate -/

/-- The first coordinate after `n` steps from the closed right half-plane. -/
theorem citer_fst (p : ℤ × ℤ) (n T : ℕ) (hT : n * n ≤ T) (h1 : (2 : ℤ) ^ T ∣ p.1)
    (h2 : (2 : ℤ) ^ T ∣ p.2) :
    ((citer p n).1 : ℝ) = gain n * ‖toC p‖ * Real.cos (Complex.arg (iter (toC p) n)) := by
  rw [← norm_iter, Complex.norm_mul_cos_arg, ← toC_citer p n T hT h1 h2 n le_rfl, toC_re]

/-- It is nonnegative when the start lies in the closed right half-plane. -/
theorem citer_fst_nonneg (p : ℤ × ℤ) (n T : ℕ) (hn : 2 ≤ n) (hT : n * n ≤ T)
    (h1 : (2 : ℤ) ^ T ∣ p.1) (h2 : (2 : ℤ) ^ T ∣ p.2) (hp : 0 ≤ p.1) : 0 ≤ (citer p n).1 := by
  have h := citer_fst p n T hT h1 h2
  by_cases hz : toC p = 0
  · rw [hz, norm_zero, mul_zero, zero_mul] at h
    exact_mod_cast h.ge
  · have hre : 0 ≤ (toC p).re := by
      rw [toC_re]
      exact_mod_cast hp
    obtain ⟨hl, hu⟩ := abs_le.mp (converge (toC p) hz hre n hn).2
    have hα := alpha_le_pi_div_four (n - 1)
    have hpi := Real.pi_pos
    have hcos : 0 ≤ Real.cos (Complex.arg (iter (toC p) n)) :=
      Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith) (by linarith)
    have hx : (0 : ℝ) ≤ (citer p n).1 := by
      rw [h]
      exact mul_nonneg (mul_nonneg (gain_pos n).le (norm_nonneg _)) hcos
    exact_mod_cast hx

end

end SparseHamiltonian.GateBinary.Cordic
