import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Exact CORDIC vectoring over the complex numbers

We study the exact (infinite-precision) CORDIC iteration in vectoring mode. With the angles
`α_k = arctan 2^{-k}` and the direction `σ(z) = -1` strictly below the real axis and `σ(z) = +1`
otherwise, one step is the multiplication `z ↦ (1 - i σ(z) 2^{-k}) z`. It rotates `z` by
`-σ(z) α_k` and multiplies its modulus by `√(1 + 4^{-k})`.

* `norm_iter`, `gain_pos`, `one_le_gain`, `gain_le_two`: after `m` steps the modulus has been
  multiplied by the gain `∏_{k<m} √(1 + 4^{-k})`, which lies in `[1, 2]`.
* `converge`: for a nonzero starting point `z` in the closed right half-plane and `n ≥ 2`, the
  argument of `z` is the accumulated angle `∑_{k<n} σ(z_k) α_k` plus the argument of the `n`-th
  iterate `z_n`, and `|arg z_n| ≤ α_{n-1}`. The proof rests on the inequality `α_k ≤ 2 α_{k+1}`,
  which gives `α_k ≤ ∑_{k<j<n} α_j + α_{n-1}`: the residual angle never exceeds the angles still
  available.
* `arg_ofReal_add_mul_I`, `abs_arctan_sub_le`, `arg_neg_eq`: auxiliary facts, namely
  `arg (u + i y) = arctan (y / u)` for `u > 0`, the bound
  `|arctan ((1 + ρ) b) - arctan b| ≤ |ρ|` for `b ≥ 0` and `|ρ| ≤ 1/2`, and
  `arg (-w) ≡ arg w + π (mod 2π)` for `w ≠ 0`.
-/

set_option autoImplicit false

namespace SparseHamiltonian.GateBinary.Cordic

noncomputable section

/-! ### The iteration -/

/-- The CORDIC angles `α_k = arctan 2^{-k}`. -/
def alpha (k : ℕ) : ℝ := Real.arctan ((1 / 2 : ℝ) ^ k)

/-- The CORDIC direction of a point: `-1` strictly below the real axis, `+1` otherwise. -/
def sgn (z : ℂ) : ℝ := if z.im < 0 then -1 else 1

/-- One exact CORDIC vectoring step `z ↦ (1 - i σ 2^{-k}) z` with `σ = sgn z`. -/
def step (k : ℕ) (z : ℂ) : ℂ :=
  (1 - Complex.I * ((sgn z * (1 / 2 : ℝ) ^ k : ℝ) : ℂ)) * z

/-- The CORDIC iterates `z_0 = z`, `z_{k+1} = step k z_k`. -/
def iter (z : ℂ) : ℕ → ℂ
  | 0 => z
  | k + 1 => step k (iter z k)

/-- The accumulated CORDIC angle after `m` steps. -/
def acc (z : ℂ) (m : ℕ) : ℝ := ∑ k ∈ Finset.range m, sgn (iter z k) * alpha k

/-- The CORDIC gain after `m` steps. -/
def gain (m : ℕ) : ℝ := ∏ k ∈ Finset.range m, Real.sqrt (1 + (1 / 4 : ℝ) ^ k)

/-- Unfolding one step of the iteration. -/
theorem iter_succ (z : ℂ) (k : ℕ) : iter z (k + 1) = step k (iter z k) := rfl

/-- Unfolding one step of the accumulated angle. -/
theorem acc_succ (z : ℂ) (k : ℕ) : acc z (k + 1) = acc z k + sgn (iter z k) * alpha k := by
  simp only [acc, Finset.sum_range_succ]

/-! ### The angles -/

/-- `arctan x ≤ x` for `x ≥ 0`. -/
theorem arctan_le_self {x : ℝ} (hx : 0 ≤ x) : Real.arctan x ≤ x := by
  have h := Real.le_tan (Real.arctan_nonneg.mpr hx) (Real.arctan_lt_pi_div_two x)
  rwa [Real.tan_arctan] at h

/-- `|arctan x| ≤ |x|` for every real `x`. -/
theorem abs_arctan_le (x : ℝ) : |Real.arctan x| ≤ |x| := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg (Real.arctan_nonneg.mpr hx), abs_of_nonneg hx]
    exact arctan_le_self hx
  · have h := arctan_le_self (neg_nonneg.mpr hx)
    rw [Real.arctan_neg] at h
    rw [abs_of_nonpos (Real.arctan_le_zero.mpr hx), abs_of_nonpos hx]
    exact h

/-- The CORDIC angles are nonnegative. -/
theorem alpha_nonneg (k : ℕ) : 0 ≤ alpha k :=
  Real.arctan_nonneg.mpr (by positivity)

/-- The CORDIC angles satisfy `α_k ≤ 2^{-k}`. -/
theorem alpha_le (k : ℕ) : alpha k ≤ (1 / 2 : ℝ) ^ k :=
  arctan_le_self (by positivity)

/-- The first CORDIC angle is `α_0 = π / 4`. -/
theorem alpha_zero : alpha 0 = Real.pi / 4 := by
  simp [alpha]

/-- Every CORDIC angle is at most `π / 4`. -/
theorem alpha_le_pi_div_four (k : ℕ) : alpha k ≤ Real.pi / 4 := by
  rw [← Real.arctan_one]
  exact Real.arctan_le_arctan_iff.mpr (pow_le_one₀ (by norm_num) (by norm_num))

/-- `α_k ≤ 2 α_{k+1}`, from the doubling formula `2 arctan t = arctan (2t / (1 - t²))`. -/
theorem alpha_le_two_mul (k : ℕ) : alpha k ≤ 2 * alpha (k + 1) := by
  have ht0 : 0 < (1 / 2 : ℝ) ^ (k + 1) := by positivity
  have hk1 : (1 / 2 : ℝ) ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hk : (1 / 2 : ℝ) ^ k = 2 * (1 / 2 : ℝ) ^ (k + 1) := by rw [pow_succ]; ring
  have ht1 : (1 / 2 : ℝ) ^ (k + 1) ≤ 1 / 2 := by rw [pow_succ]; nlinarith
  unfold alpha
  rw [hk, Real.two_mul_arctan (by linarith) (by linarith)]
  apply Real.arctan_le_arctan_iff.mpr
  rw [le_div_iff₀ (by nlinarith)]
  nlinarith

/-- `α_k ≤ α_{k+1} + ⋯ + α_{k+m} + α_{k+m}`. -/
theorem alpha_le_tail (k m : ℕ) :
    alpha k ≤ (∑ j ∈ Finset.Ico (k + 1) (k + 1 + m), alpha j) + alpha (k + m) := by
  induction m generalizing k with
  | zero => simp
  | succ m ih =>
    have h1 := alpha_le_two_mul k
    have h2 := ih (k + 1)
    rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : k + 1 < k + 1 + (m + 1))]
    have e1 : k + 1 + 1 + m = k + 1 + (m + 1) := by omega
    have e2 : k + 1 + m = k + (m + 1) := by omega
    rw [e1, e2] at h2
    linarith

/-- For `k < n`, the angle `α_k` is at most `∑_{k<j<n} α_j + α_{n-1}`. -/
theorem alpha_le_tail_sum {k n : ℕ} (hk : k < n) :
    alpha k ≤ (∑ j ∈ Finset.Ico (k + 1) n, alpha j) + alpha (n - 1) := by
  have h := alpha_le_tail k (n - 1 - k)
  have e1 : k + 1 + (n - 1 - k) = n := by omega
  have e2 : k + (n - 1 - k) = n - 1 := by omega
  rwa [e1, e2] at h

/-! ### The directions -/

/-- The CORDIC direction is `±1`. -/
theorem sgn_eq (z : ℂ) : sgn z = 1 ∨ sgn z = -1 := by
  unfold sgn
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- The CORDIC direction has absolute value `1`. -/
theorem abs_sgn (z : ℂ) : |sgn z| = 1 := by
  rcases sgn_eq z with h | h <;> rw [h] <;> norm_num

/-- `arctan` commutes with multiplication by a CORDIC direction. -/
theorem arctan_sgn_mul (w : ℂ) (x : ℝ) : Real.arctan (sgn w * x) = sgn w * Real.arctan x := by
  rcases sgn_eq w with h | h <;> rw [h] <;> simp

/-- The direction of a point times its argument is the absolute value of the argument. -/
theorem sgn_mul_arg (w : ℂ) : sgn w * Complex.arg w = |Complex.arg w| := by
  unfold sgn
  split_ifs with h
  · rw [abs_of_neg (Complex.arg_neg_iff.mpr h)]
    ring
  · rw [abs_of_nonneg (Complex.arg_nonneg_iff.mpr (not_lt.mp h))]
    ring

/-! ### Moduli and the gain -/

/-- One CORDIC step multiplies the modulus by `√(1 + 4^{-k})`. -/
theorem norm_step (k : ℕ) (z : ℂ) :
    ‖step k z‖ = Real.sqrt (1 + (1 / 4 : ℝ) ^ k) * ‖z‖ := by
  unfold step
  rw [norm_mul]
  congr 1
  have h1 : (1 : ℂ) - Complex.I * ((sgn z * (1 / 2 : ℝ) ^ k : ℝ) : ℂ)
      = ((1 : ℝ) : ℂ) + ((-(sgn z * (1 / 2 : ℝ) ^ k) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h1, Complex.norm_add_mul_I]
  congr 1
  have hσ : sgn z ^ 2 = 1 := by rcases sgn_eq z with h | h <;> rw [h] <;> norm_num
  rw [neg_sq, mul_pow, hσ, ← pow_mul, mul_comm k 2, pow_mul]
  norm_num

/-- After `m` steps the modulus has been multiplied by the gain. -/
theorem norm_iter (z : ℂ) (m : ℕ) : ‖iter z m‖ = gain m * ‖z‖ := by
  induction m with
  | zero => simp [iter, gain]
  | succ m ih =>
    rw [iter, norm_step, ih]
    simp only [gain, Finset.prod_range_succ]
    ring

/-- The gain is positive. -/
theorem gain_pos (m : ℕ) : 0 < gain m :=
  Finset.prod_pos (fun k _ => Real.sqrt_pos.mpr (by positivity))

/-- The gain is at least `1`. -/
theorem one_le_gain (m : ℕ) : 1 ≤ gain m := by
  induction m with
  | zero => simp [gain]
  | succ m ih =>
    simp only [gain, Finset.prod_range_succ] at ih ⊢
    have h : 1 ≤ Real.sqrt (1 + (1 / 4 : ℝ) ^ m) := by
      rw [Real.one_le_sqrt]
      have : (0 : ℝ) ≤ (1 / 4) ^ m := by positivity
      linarith
    nlinarith

/-- `∏_{k ≤ m} (1 + 4^{-k}) ≤ 3 - 4^{-m}`. -/
theorem prod_le_three (m : ℕ) :
    ∏ k ∈ Finset.range (m + 1), (1 + (1 / 4 : ℝ) ^ k) ≤ 3 - (1 / 4 : ℝ) ^ m := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [Finset.prod_range_succ, pow_succ]
    have hx : 0 ≤ (1 / 4 : ℝ) ^ m := by positivity
    have h := mul_le_mul_of_nonneg_right ih
      (by positivity : (0 : ℝ) ≤ 1 + (1 / 4) ^ m * (1 / 4))
    nlinarith [sq_nonneg ((1 / 4 : ℝ) ^ m)]

/-- The square of the gain is `∏_{k<m} (1 + 4^{-k})`. -/
theorem gain_sq (m : ℕ) : gain m ^ 2 = ∏ k ∈ Finset.range m, (1 + (1 / 4 : ℝ) ^ k) := by
  rw [gain, ← Finset.prod_pow]
  exact Finset.prod_congr rfl (fun k _ => Real.sq_sqrt (by positivity))

/-- The gain is at most `2` (its square is in fact at most `3`). -/
theorem gain_le_two (m : ℕ) : gain m ≤ 2 := by
  have h3 : gain m ^ 2 ≤ 3 := by
    rw [gain_sq]
    cases m with
    | zero => norm_num
    | succ m =>
      have h := prod_le_three m
      have hx : (0 : ℝ) ≤ (1 / 4) ^ m := by positivity
      linarith
  nlinarith [gain_pos m]

/-- The iterates of a nonzero point are nonzero. -/
theorem iter_ne_zero (z : ℂ) (hz : z ≠ 0) (m : ℕ) : iter z m ≠ 0 := by
  rw [← norm_pos_iff, norm_iter]
  exact mul_pos (gain_pos m) (norm_pos_iff.mpr hz)

/-! ### Arguments -/

/-- The argument of a point of the open right half-plane. -/
theorem arg_ofReal_add_mul_I (u y : ℝ) (hu : 0 < u) :
    Complex.arg ((u : ℂ) + (y : ℂ) * Complex.I) = Real.arctan (y / u) := by
  have hre : ((u : ℂ) + (y : ℂ) * Complex.I).re = u := by simp
  have him : ((u : ℂ) + (y : ℂ) * Complex.I).im = y := by simp
  have htan : Real.tan (Complex.arg ((u : ℂ) + (y : ℂ) * Complex.I)) = y / u := by
    rw [Complex.tan_arg, hre, him]
  have habs : |Complex.arg ((u : ℂ) + (y : ℂ) * Complex.I)| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl (by rw [hre]; exact hu))
  exact (Real.arctan_eq_of_tan_eq htan (abs_lt.mp habs)).symm

/-- Relative perturbations of a nonnegative argument move `arctan` by at most `|ρ|`. -/
theorem abs_arctan_sub_le (b ρ : ℝ) (hb : 0 ≤ b) (hρ : |ρ| ≤ 1 / 2) :
    |Real.arctan ((1 + ρ) * b) - Real.arctan b| ≤ |ρ| := by
  have hρ' := abs_le.mp hρ
  have hbb : 0 ≤ (1 / 2 + ρ) * (b * b) := mul_nonneg (by linarith) (mul_self_nonneg b)
  have hden : 0 < 1 + (1 + ρ) * b * b := by nlinarith
  have hsub : Real.arctan ((1 + ρ) * b) - Real.arctan b
      = Real.arctan (ρ * b / (1 + (1 + ρ) * b * b)) := by
    rw [sub_eq_add_neg, ← Real.arctan_neg, Real.arctan_add (by nlinarith)]
    congr 1
    ring
  rw [hsub]
  refine (abs_arctan_le _).trans ?_
  rw [abs_div, abs_mul, abs_of_nonneg hb, abs_of_pos hden, div_le_iff₀ hden]
  have : b ≤ 1 + (1 + ρ) * b * b := by nlinarith [sq_nonneg (b - 1)]
  exact mul_le_mul_of_nonneg_left this (abs_nonneg ρ)

/-- Negation adds `π` to the argument, modulo `2π`. -/
theorem arg_neg_eq (w : ℂ) (hw : w ≠ 0) :
    ∃ m : ℤ, Complex.arg (-w) = Complex.arg w + Real.pi + 2 * Real.pi * m := by
  have h := Complex.arg_neg_coe_angle hw
  rw [← Real.Angle.coe_add, Real.Angle.angle_eq_iff_two_pi_dvd_sub] at h
  obtain ⟨m, hm⟩ := h
  exact ⟨m, by linarith⟩

/-- A CORDIC step is multiplication by the point `1 - i σ 2^{-k}` in Cartesian form. -/
theorem step_eq (k : ℕ) (w : ℂ) :
    step k w = (((1 : ℝ) : ℂ) + ((-(sgn w * (1 / 2 : ℝ) ^ k) : ℝ) : ℂ) * Complex.I) * w := by
  unfold step
  push_cast
  ring

/-- On the closed right half-plane, one step rotates the argument by `-σ α_k`. -/
theorem arg_step (k : ℕ) (w : ℂ) (hw : w ≠ 0) (habs : |Complex.arg w| ≤ Real.pi / 2) :
    Complex.arg (step k w) = Complex.arg w - sgn w * alpha k := by
  have hf : ((1 : ℝ) : ℂ) + ((-(sgn w * (1 / 2 : ℝ) ^ k) : ℝ) : ℂ) * Complex.I ≠ 0 := by
    rw [← norm_pos_iff, Complex.norm_add_mul_I]
    positivity
  have harg : Complex.arg (((1 : ℝ) : ℂ) + ((-(sgn w * (1 / 2 : ℝ) ^ k) : ℝ) : ℂ) * Complex.I)
      = -(sgn w * alpha k) := by
    rw [arg_ofReal_add_mul_I 1 _ one_pos, div_one, Real.arctan_neg, arctan_sgn_mul]
    rfl
  have h1 : |sgn w * alpha k| ≤ Real.pi / 4 := by
    rw [abs_mul, abs_sgn, one_mul, abs_of_nonneg (alpha_nonneg k)]
    exact alpha_le_pi_div_four k
  have hmem : Complex.arg (((1 : ℝ) : ℂ) + ((-(sgn w * (1 / 2 : ℝ) ^ k) : ℝ) : ℂ) * Complex.I)
      + Complex.arg w ∈ Set.Ioc (-Real.pi) Real.pi := by
    rw [harg]
    have hpi := Real.pi_pos
    have h2 := abs_le.mp h1
    have h3 := abs_le.mp habs
    constructor <;> linarith
  rw [step_eq, Complex.arg_mul hf hw hmem, harg]
  ring

/-- On the closed right half-plane, one step replaces `|arg w|` by `||arg w| - α_k|`. -/
theorem abs_arg_step (k : ℕ) (w : ℂ) (hw : w ≠ 0) (habs : |Complex.arg w| ≤ Real.pi / 2) :
    |Complex.arg (step k w)| = |(|Complex.arg w| - alpha k)| := by
  rw [arg_step k w hw habs, ← sgn_mul_arg]
  have hσ : sgn w * sgn w = 1 := by rcases sgn_eq w with h | h <;> rw [h] <;> norm_num
  have e : Complex.arg w - sgn w * alpha k = sgn w * (sgn w * Complex.arg w - alpha k) := by
    linear_combination (-Complex.arg w) * hσ
  rw [e, abs_mul, abs_sgn, one_mul]

/-! ### Convergence -/

/-- The invariant behind `converge`: after `k ≤ n` steps, `arg z` is the accumulated angle plus
the residual angle `arg z_k`, and `|arg z_k|` is at most `π / 2` and at most the remaining budget
`∑_{k≤j<n} α_j + α_{n-1}`. -/
theorem converge_aux (z : ℂ) (hz : z ≠ 0) (hre : 0 ≤ z.re) (n : ℕ) (hn : 1 ≤ n) (k : ℕ)
    (hk : k ≤ n) :
    Complex.arg z = acc z k + Complex.arg (iter z k) ∧
      |Complex.arg (iter z k)| ≤ Real.pi / 2 ∧
      |Complex.arg (iter z k)| ≤ (∑ j ∈ Finset.Ico k n, alpha j) + alpha (n - 1) := by
  induction k with
  | zero =>
    have h0 : |Complex.arg z| ≤ Real.pi / 2 := Complex.abs_arg_le_pi_div_two_iff.mpr hre
    have h1 := alpha_le_tail_sum (by omega : 0 < n)
    have h2 := Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < n) alpha
    have h3 := alpha_zero
    have e : iter z 0 = z := rfl
    have ea : acc z 0 = 0 := by simp [acc]
    rw [e, ea, zero_add]
    exact ⟨rfl, h0, by linarith⟩
  | succ k ih =>
    obtain ⟨ha, hb, hc⟩ := ih (by omega)
    have hw := iter_ne_zero z hz k
    have harg := arg_step k (iter z k) hw hb
    have habs := abs_arg_step k (iter z k) hw hb
    have htail := alpha_le_tail_sum (by omega : k < n)
    have hsum := Finset.sum_eq_sum_Ico_succ_bot (by omega : k < n) alpha
    have hα := alpha_le_pi_div_four k
    have hα0 := alpha_nonneg k
    have hψ := abs_nonneg (Complex.arg (iter z k))
    rw [iter_succ, acc_succ, harg]
    refine ⟨by linarith, ?_, ?_⟩
    · rw [← harg, habs, abs_le]
      constructor <;> linarith
    · rw [← harg, habs, abs_le]
      constructor <;> linarith

/-- Convergence of exact CORDIC from the closed right half-plane. -/
theorem converge (z : ℂ) (hz : z ≠ 0) (hre : 0 ≤ z.re) (n : ℕ) (hn : 2 ≤ n) :
    Complex.arg z = acc z n + Complex.arg (iter z n) ∧
      |Complex.arg (iter z n)| ≤ alpha (n - 1) := by
  obtain ⟨ha, -, hc⟩ := converge_aux z hz hre n (by omega) n le_rfl
  refine ⟨ha, ?_⟩
  rwa [Finset.Ico_self, Finset.sum_empty, zero_add] at hc

end

end SparseHamiltonian.GateBinary.Cordic
