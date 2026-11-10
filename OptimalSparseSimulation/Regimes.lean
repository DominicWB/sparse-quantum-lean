import LargeSparsityCore.Parameters
import SignedFactorSimulation.Parameters

set_option autoImplicit false

/-!
# The three regimes of Theorem `hs:thm:optimal`

The proof of Theorem `hs:thm:optimal` (Appendix A, eq. `opt:eq:regime-comparison`) splits by the
size of `h = log(e + L/τ)` and by the sign of `sτ - Lh`, with `L = log(1/ε)`, `r = L/h` and
`τ = η|t|`. This module proves the scalar comparisons of the three cases, for the threshold
`h ≥ 10⁴` of the large-sparsity core.

* `bounded_bound`: for `h < 10⁴`, the baseline bound `√s τ + √(sτL) + L` is at most
  `10⁴ (√s τ + √(sτr) + r)`, since `L = hr` and `h` is bounded.
* `signed_bound`: for `h ≥ 10⁴` and `sτ < Lh`, the signed-factor bound
  `√(Tb) + √(T r_b) + r_b` with `T = sτ` and `b = √s τ` is at most `4 (√(sτr) + r)`
  (`opt:eq:regime-comparison`): `b ≤ r` and `log(e + L/b) ≥ h/4`, so `r_b ≤ 4r`.
* `rval_eq_rb`: `r = L/log(e + L/τ)` is `r_b` at `b = τ`.

The lemmas of the signed-factor regime take a real parameter `s ≥ 1`; Theorem `hs:thm:two-norm`
uses them with the moment parameter `σ = sμ²/η²` in place of the sparsity.
-/

namespace OptimalSparseSimulation

noncomputable section

open LargeSparsityCore.Parameters SignedFactorSimulation

/-- `r = L/h` is the quantity `r_b = L/log(e + L/b)` of the signed-factor theorem at `b = τ`. -/
theorem rval_eq_rb (τ ε : ℝ) : rval τ ε = rb τ ε := rfl

section Basic

variable {τ ε : ℝ}

theorem L_pos (hε : 0 < ε) (hε1 : ε ≤ 1 / 64) : 0 < Lval ε := by
  unfold Lval
  apply Real.log_pos
  rw [one_div, one_lt_inv₀ hε]
  linarith

theorem one_le_h (hτ : 1 ≤ τ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 64) : 1 ≤ hval τ ε := by
  unfold hval
  have hx : 0 ≤ Lval ε / τ := div_nonneg (L_pos hε hε1).le (by linarith)
  rw [Real.le_log_iff_exp_le (by positivity)]
  linarith

theorem h_pos (hτ : 1 ≤ τ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 64) : 0 < hval τ ε :=
  lt_of_lt_of_le one_pos (one_le_h hτ hε hε1)

theorem r_pos (hτ : 1 ≤ τ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 64) : 0 < rval τ ε :=
  div_pos (L_pos hε hε1) (h_pos hτ hε hε1)

/-- `L = h r`. -/
theorem L_eq (hτ : 1 ≤ τ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 64) : Lval ε = hval τ ε * rval τ ε := by
  unfold rval
  field_simp [(h_pos hτ hε hε1).ne']

/-- A regime of the core with the same `τ, ε` and a large moment parameter, used only for the
scalar facts about `h` that do not involve the moment parameter. -/
theorem aux_regime (hτ : 1 ≤ τ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 64) (hh : 10 ^ 4 ≤ hval τ ε) :
    Regime (Lval ε * hval τ ε + 1) τ ε where
  one_le_s := by
    have := mul_pos (L_pos hε hε1) (h_pos hτ hε hε1)
    linarith
  one_le_τ := hτ
  ε_pos := hε
  ε_le := hε1
  h_large := hh
  core := by
    have := mul_pos (L_pos hε hε1) (h_pos hτ hε hε1)
    nlinarith

end Basic

/-! ### Bounded `h` -/

/-- **Bounded `h`.** For `h < 10⁴` the three terms of the baseline bound are within the factor
`10⁴` of `√s τ + √(sτr) + r`. -/
theorem bounded_bound {s : ℕ} {τ ε : ℝ} (hτ : 1 ≤ τ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 64)
    (hh : hval τ ε < 10 ^ 4) :
    Real.sqrt s * τ + Real.sqrt (s * τ * Lval ε) + Lval ε ≤
      10 ^ 4 * (Real.sqrt s * τ + Real.sqrt (s * τ * rval τ ε) + rval τ ε) := by
  have hr := r_pos hτ hε hε1
  have hh0 := h_pos hτ hε hε1
  have hL := L_eq hτ hε hε1
  have hsτ : (0 : ℝ) ≤ s * τ := mul_nonneg (Nat.cast_nonneg s) (by linarith)
  have h1 : Real.sqrt (s * τ * Lval ε) ≤ 100 * Real.sqrt (s * τ * rval τ ε) := by
    rw [hL, show (s : ℝ) * τ * (hval τ ε * rval τ ε) = hval τ ε * (s * τ * rval τ ε) by ring,
      Real.sqrt_mul hh0.le]
    have : Real.sqrt (hval τ ε) ≤ 100 := by
      rw [Real.sqrt_le_left (by norm_num)]
      linarith
    exact mul_le_mul_of_nonneg_right this (Real.sqrt_nonneg _)
  have h2 : Lval ε ≤ 10 ^ 4 * rval τ ε := by
    rw [hL]
    exact mul_le_mul_of_nonneg_right hh.le hr.le
  have h3 : 0 ≤ Real.sqrt s * τ := mul_nonneg (Real.sqrt_nonneg _) (by linarith)
  have h4 := Real.sqrt_nonneg (s * τ * rval τ ε)
  nlinarith

/-! ### Large `h` and `sτ < Lh`: the signed factor -/

section Signed

variable {s τ ε : ℝ}

/-- `h⁴/24 ≤ e^h`. -/
theorem pow_four_le_exp (hτ : 1 ≤ τ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 64) :
    hval τ ε ^ 4 / 24 ≤ Real.exp (hval τ ε) := by
  have h := Real.pow_div_factorial_le_exp (x := hval τ ε) (h_pos hτ hε hε1).le 4
  have h24 : (Nat.factorial 4 : ℝ) = 24 := by norm_num [Nat.factorial]
  rw [h24] at h
  exact h

/-- `2h ≤ e^{h/2}`. -/
theorem two_h_le_exp_half (hh : 10 ^ 4 ≤ hval τ ε) :
    2 * hval τ ε ≤ Real.exp (hval τ ε / 2) := by
  have h := Real.pow_div_factorial_le_exp (x := hval τ ε / 2) (by linarith) 2
  have h2 : (Nat.factorial 2 : ℝ) = 2 := by norm_num [Nat.factorial]
  rw [h2] at h
  nlinarith

/-- `h³ ≤ L/τ`. -/
theorem cube_le_x (hτ : 1 ≤ τ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 64) (hh : 10 ^ 4 ≤ hval τ ε) :
    hval τ ε ^ 3 ≤ Lval ε / τ := by
  have R := aux_regime hτ hε hε1 hh
  have h1 := R.x_ge
  have h2 := pow_four_le_exp hτ hε hε1
  have h3 : hval τ ε ^ 3 ≤ hval τ ε ^ 4 / 48 := by
    have : hval τ ε ^ 4 = hval τ ε * hval τ ε ^ 3 := by ring
    rw [this]
    have h0 : 0 ≤ hval τ ε ^ 3 := by positivity
    nlinarith
  linarith

/-- `h e^{h/2} ≤ L/τ`. -/
theorem h_exp_half_le_x (hτ : 1 ≤ τ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 64)
    (hh : 10 ^ 4 ≤ hval τ ε) : hval τ ε * Real.exp (hval τ ε / 2) ≤ Lval ε / τ := by
  have R := aux_regime hτ hε hε1 hh
  have h1 := R.x_ge
  have h2 := two_h_le_exp_half hh
  have he : Real.exp (hval τ ε) = Real.exp (hval τ ε / 2) * Real.exp (hval τ ε / 2) := by
    rw [← Real.exp_add]
    ring_nf
  have hpos := Real.exp_pos (hval τ ε / 2)
  nlinarith

/-- `b = √s τ ≤ r` when `sτ < Lh` (`opt:eq:regime-comparison`, `b/r ≤ h^{3/2}/√x`). -/
theorem b_le_r (hs : 1 ≤ s) (hτ : 1 ≤ τ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 64)
    (hh : 10 ^ 4 ≤ hval τ ε) (hcore : (s : ℝ) * τ < Lval ε * hval τ ε) :
    Real.sqrt s * τ ≤ rval τ ε := by
  have hτ0 : 0 < τ := by linarith
  have hh0 := h_pos hτ hε hε1
  have hL := L_pos hε hε1
  have hr := r_pos hτ hε hε1
  have hcube := cube_le_x hτ hε hε1 hh
  rw [le_div_iff₀ hτ0] at hcube
  have hb0 : 0 ≤ Real.sqrt s * τ := mul_nonneg (Real.sqrt_nonneg _) hτ0.le
  rw [← abs_of_nonneg hb0, ← abs_of_nonneg hr.le, ← sq_le_sq]
  have hsq : (Real.sqrt s * τ) ^ 2 = s * τ * τ := by
    rw [mul_pow, Real.sq_sqrt (by linarith)]
    ring
  have hrsq : rval τ ε ^ 2 * hval τ ε ^ 2 = Lval ε ^ 2 := by
    unfold rval
    field_simp
  rw [hsq]
  have h1 : (s : ℝ) * τ * τ ≤ Lval ε * hval τ ε * τ := by nlinarith
  have h2 : Lval ε * hval τ ε * τ * hval τ ε ^ 2 ≤ Lval ε ^ 2 := by nlinarith
  have hh2 : 0 < hval τ ε ^ 2 := by positivity
  have h3 : Lval ε * hval τ ε * τ ≤ rval τ ε ^ 2 := by
    rw [← mul_le_mul_iff_of_pos_right hh2, hrsq]
    exact h2
  linarith

/-- `e^{h/4} ≤ L/b` when `sτ < Lh` (`opt:eq:regime-comparison`, `L/b ≥ √(x/h)`). -/
theorem exp_quarter_le_L_div_b (hs : 1 ≤ s) (hτ : 1 ≤ τ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 64)
    (hh : 10 ^ 4 ≤ hval τ ε) (hcore : (s : ℝ) * τ < Lval ε * hval τ ε) :
    Real.exp (hval τ ε / 4) ≤ Lval ε / (Real.sqrt s * τ) := by
  have hτ0 : 0 < τ := by linarith
  have hs1 : (1 : ℝ) ≤ s := hs
  have hsq0 : 0 < Real.sqrt s := Real.sqrt_pos.mpr (by linarith)
  have hb0 : 0 < Real.sqrt s * τ := mul_pos hsq0 hτ0
  have hL := L_pos hε hε1
  have hh0 := h_pos hτ hε hε1
  have hx := h_exp_half_le_x hτ hε hε1 hh
  rw [le_div_iff₀ hτ0] at hx
  rw [le_div_iff₀ hb0]
  have he0 := Real.exp_pos (hval τ ε / 4)
  have hlhs : 0 ≤ Real.exp (hval τ ε / 4) * (Real.sqrt s * τ) := by positivity
  rw [← abs_of_nonneg hlhs, ← abs_of_nonneg hL.le, ← sq_le_sq]
  have hsq : (Real.exp (hval τ ε / 4) * (Real.sqrt s * τ)) ^ 2 =
      Real.exp (hval τ ε / 2) * (s * τ * τ) := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by linarith), ← Real.exp_nat_mul]
    ring_nf
  rw [hsq]
  have hE := Real.exp_pos (hval τ ε / 2)
  have h1 : Real.exp (hval τ ε / 2) * ((s : ℝ) * τ * τ) ≤
      Real.exp (hval τ ε / 2) * (Lval ε * hval τ ε * τ) := by
    apply mul_le_mul_of_nonneg_left _ hE.le
    nlinarith
  have h2 : Real.exp (hval τ ε / 2) * (Lval ε * hval τ ε * τ) ≤ Lval ε ^ 2 := by
    have : Real.exp (hval τ ε / 2) * (Lval ε * hval τ ε * τ) =
        Lval ε * (hval τ ε * Real.exp (hval τ ε / 2) * τ) := by ring
    rw [this, sq]
    exact mul_le_mul_of_nonneg_left hx hL.le
  linarith

/-- `log(e + L/b) ≥ h/4` when `sτ < Lh`. -/
theorem quarter_le_log (hs : 1 ≤ s) (hτ : 1 ≤ τ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 64)
    (hh : 10 ^ 4 ≤ hval τ ε) (hcore : (s : ℝ) * τ < Lval ε * hval τ ε) :
    hval τ ε / 4 ≤ Real.log (Real.exp 1 + Lval ε / (Real.sqrt s * τ)) := by
  have h := exp_quarter_le_L_div_b hs hτ hε hε1 hh hcore
  have he := Real.exp_pos 1
  rw [Real.le_log_iff_exp_le (by linarith [Real.exp_pos (hval τ ε / 4)])]
  linarith

/-- `r_b ≤ 4r` when `sτ < Lh`, with `b = √s τ` (`opt:eq:regime-comparison`, `r_b = Θ(r)`). -/
theorem rb_le (hs : 1 ≤ s) (hτ : 1 ≤ τ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 64)
    (hh : 10 ^ 4 ≤ hval τ ε) (hcore : (s : ℝ) * τ < Lval ε * hval τ ε) :
    rb (Real.sqrt s * τ) ε ≤ 4 * rval τ ε := by
  have hq := quarter_le_log hs hτ hε hε1 hh hcore
  have hh0 := h_pos hτ hε hε1
  have hL := L_pos hε hε1
  have hlog : 0 < Real.log (Real.exp 1 + Lval ε / (Real.sqrt s * τ)) := by linarith
  change Lval ε / Real.log (Real.exp 1 + Lval ε / (Real.sqrt s * τ)) ≤ 4 * (Lval ε / hval τ ε)
  rw [div_le_iff₀ hlog]
  have : 4 * (Lval ε / hval τ ε) * Real.log (Real.exp 1 + Lval ε / (Real.sqrt s * τ)) ≥
      4 * (Lval ε / hval τ ε) * (hval τ ε / 4) :=
    mul_le_mul_of_nonneg_left hq (by positivity)
  have h4 : 4 * (Lval ε / hval τ ε) * (hval τ ε / 4) = Lval ε := by
    field_simp
  linarith

/-- **The signed-factor regime.** For `h ≥ 10⁴` and `sτ < Lh`, with `T = sτ` and `b = √s τ`,
`√(Tb) + √(T r_b) + r_b ≤ 4 (√(sτr) + r)`. -/
theorem signed_bound (hs : 1 ≤ s) (hτ : 1 ≤ τ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 64)
    (hh : 10 ^ 4 ≤ hval τ ε) (hcore : (s : ℝ) * τ < Lval ε * hval τ ε) :
    Real.sqrt (s * τ * (Real.sqrt s * τ)) + Real.sqrt (s * τ * rb (Real.sqrt s * τ) ε) +
      rb (Real.sqrt s * τ) ε ≤ 4 * (Real.sqrt (s * τ * rval τ ε) + rval τ ε) := by
  have hsτ : (0 : ℝ) ≤ s * τ := mul_nonneg (by linarith) (by linarith)
  have hb := b_le_r hs hτ hε hε1 hh hcore
  have hrb := rb_le hs hτ hε hε1 hh hcore
  have hr := r_pos hτ hε hε1
  have h1 : Real.sqrt (s * τ * (Real.sqrt s * τ)) ≤ Real.sqrt (s * τ * rval τ ε) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hb hsτ)
  have h2 : Real.sqrt (s * τ * rb (Real.sqrt s * τ) ε) ≤ 2 * Real.sqrt (s * τ * rval τ ε) := by
    have h4 : Real.sqrt (s * τ * (4 * rval τ ε)) = 2 * Real.sqrt (s * τ * rval τ ε) := by
      rw [show (s : ℝ) * τ * (4 * rval τ ε) = 2 ^ 2 * (s * τ * rval τ ε) by ring,
        Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
    rw [← h4]
    exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hrb hsτ)
  have h3 := Real.sqrt_nonneg (s * τ * rval τ ε)
  linarith

end Signed

end

end OptimalSparseSimulation
