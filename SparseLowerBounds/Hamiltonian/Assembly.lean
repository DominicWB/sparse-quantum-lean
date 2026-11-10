import SparseLowerBounds.Hamiltonian.Numerics

set_option synthInstance.maxHeartbeats 400000

section
/-!
# Assembly of the three family bounds

Manuscript: the numerical part of the proof of Theorem `hsl:thm:main`. Real analysis only.

* If `L < 64τ`: `√(sτr) ≤ 8 √s τ` and `r ≤ 64τ ≤ 12 √s τ` (`s ≥ 32`), so the
  sum in eq. `hsl:eq:main` is at most `21 √s τ` (`sum_le_of_small_L`).
* If `L ≥ 64τ`: each of the three terms is bounded by one family with a
  constant at least `c_T` (eqs. `hsl:eq:rbound`, `hsl:eq:mixrbound`,
  `hsl:eq:failedmix`), so the maximum of the three bounds is at least
  `c_T/3` times the sum (`third_cT_mul_sum_le`).
* `c₀ = log 2/(4096π)` is below both `c_T/3` and `c_T/21` (`c0_le`,
  `three_mul_c0_le`); `c0_le` is tight to about 1.6% (`21/4096` against
  `1/192`, i.e. `4032 ≤ 4096`).

`assembly` packages this for three arbitrary real quantities `Q_T, Q_M, Q_P` (the query counts of
algorithms for the time, mixed and precision families): it is the step "For three nonnegative
numbers, that maximum is at least one third of their sum" (Section `hsl:sec:main`), and contains no
claim about how one algorithm relates to the three families.
-/

namespace SparseLowerBounds.Hamiltonian

noncomputable section

variable {τ ε : ℝ} {s : ℕ}

/-! ### Constants (proof of Theorem `hsl:thm:main`) -/

/-- `c₀ ≤ c_T/21` (hence `c₀ ≤ c_T/3`), proof of Theorem `hsl:thm:main`. -/
theorem c0_le : 21 * c0 ≤ cT := by
  unfold c0 cT
  have hl : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hp : 0 < Real.pi := Real.pi_pos
  rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_pos hl hp]

/-- `c₀ ≤ c_T/3` (proof of Theorem `hsl:thm:main`). -/
theorem three_mul_c0_le : 3 * c0 ≤ cT := by
  have h1 := c0_le
  have h2 := c0_pos
  linarith

/-- `log 2 ≤ 1` (from `log x ≤ x - 1`). -/
theorem log_two_le_one : Real.log 2 ≤ 1 := by
  have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
  linarith

/-- `√2 ≤ 2`. -/
theorem sqrt_two_le_two : Real.sqrt 2 ≤ 2 := by
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]

/-- `2√2 < π`: `cos √2 > 1 - (√2)²/2 = 0`, so `√2 < π/2`. -/
theorem two_mul_sqrt_two_lt_pi : 2 * Real.sqrt 2 < Real.pi := by
  have h2pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hcos : 0 < Real.cos (Real.sqrt 2) := by
    have := Real.one_sub_sq_div_two_lt_cos h2pos.ne'
    rw [Real.sq_sqrt (by norm_num)] at this
    linarith
  refine lt_of_not_ge fun hcon => ?_
  have hpi := Real.two_le_pi
  have h1 : Real.pi / 2 ≤ Real.sqrt 2 := by linarith
  have h2 : Real.sqrt 2 ≤ Real.pi + Real.pi / 2 := by
    have := sqrt_two_le_two
    linarith
  have := Real.cos_nonpos_of_pi_div_two_le_of_le h1 h2
  linarith

/-- `1/32` in eq. `hsl:eq:rbound` is at least `c_T`. -/
theorem cT_le_inv_32 : cT ≤ 1 / 32 := by
  unfold cT
  have hl := log_two_le_one
  have hp := Real.two_le_pi
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  linarith

/-- The constant of eq. `hsl:eq:mixrbound` is at least `c_T` (equivalent to `π ≥ 2√2`). -/
theorem cT_le_mixConst : cT ≤ Real.log 2 / (384 * Real.sqrt 2) := by
  unfold cT
  have hl0 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hp := two_mul_sqrt_two_lt_pi
  have h2pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  apply div_le_div_of_nonneg_left hl0.le (by positivity)
  linarith

/-- The constant of eq. `hsl:eq:failedmix` is at least `c_T`. -/
theorem cT_le_failedConst : cT ≤ 1 / (64 * Real.sqrt 2) := by
  unfold cT
  have hl := log_two_le_one
  have hl0 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hp := Real.two_le_pi
  have h2 := sqrt_two_le_two
  have h2pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hprod : Real.log 2 * Real.sqrt 2 ≤ 1 * 2 :=
    mul_le_mul hl h2 h2pos.le zero_le_one
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-! ### The case `L < 64τ` (proof of Theorem `hsl:thm:main`) -/

/-- `64 ≤ 12 √s` for `s ≥ 32` (proof of Theorem `hsl:thm:main`). -/
theorem sixtyfour_le_twelve_sqrt (hs : 32 ≤ s) : 64 ≤ 12 * Real.sqrt s := by
  have hs' : (32 : ℝ) ≤ s := by exact_mod_cast hs
  have hsq := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) s)
  nlinarith [Real.sqrt_nonneg (s : ℝ)]

/-- `r ≤ L < 64τ` (proof of Theorem `hsl:thm:main`). -/
theorem hsR_lt_of_small_L (h : HSRange τ s ε) (hL : hsL ε < 64 * τ) : hsR τ ε < 64 * τ := by
  exact lt_of_le_of_lt h.hsR_le_hsL hL

/-- `√(sτr) ≤ 8 √s τ` (proof of Theorem `hsl:thm:main`). -/
theorem sqrt_mul_hsR_le_of_small_L (h : HSRange τ s ε) (hL : hsL ε < 64 * τ) :
    Real.sqrt (s * τ * hsR τ ε) ≤ 8 * (Real.sqrt s * τ) := by
  have hτ := h.tau_pos
  have hrl := hsR_lt_of_small_L h hL
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  have key : (s : ℝ) * τ * hsR τ ε ≤ (8 * (Real.sqrt s * τ)) ^ 2 := by
    have e : (8 * (Real.sqrt s * τ)) ^ 2 = (s : ℝ) * τ * (64 * τ) := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hs0]; ring
    rw [e]
    exact mul_le_mul_of_nonneg_left hrl.le (mul_nonneg hs0 hτ.le)
  calc Real.sqrt (s * τ * hsR τ ε) ≤ Real.sqrt ((8 * (Real.sqrt s * τ)) ^ 2) :=
        Real.sqrt_le_sqrt key
    _ = 8 * (Real.sqrt s * τ) :=
        Real.sqrt_sq (mul_nonneg (by norm_num) (mul_nonneg (Real.sqrt_nonneg _) hτ.le))

/-- `r ≤ 64τ ≤ 12 √s τ` (proof of Theorem `hsl:thm:main`). -/
theorem hsR_le_of_small_L (h : HSRange τ s ε) (hL : hsL ε < 64 * τ) :
    hsR τ ε ≤ 12 * (Real.sqrt s * τ) := by
  have hτ := h.tau_pos
  have hrl := hsR_lt_of_small_L h hL
  have h64 := sixtyfour_le_twelve_sqrt h.s_ge
  have : 64 * τ ≤ 12 * Real.sqrt s * τ := mul_le_mul_of_nonneg_right h64 hτ.le
  nlinarith

/-- The small-`L` case (proof of Theorem `hsl:thm:main`). -/
theorem sum_le_of_small_L (h : HSRange τ s ε) (hL : hsL ε < 64 * τ) :
    Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε ≤ 21 * (Real.sqrt s * τ) := by
  have h1 := sqrt_mul_hsR_le_of_small_L h hL
  have h2 := hsR_le_of_small_L h hL
  linarith

/-- The small-`L` case with the time bound alone: coefficient `c_T/21 ≥ c₀`
(proof of Theorem `hsl:thm:main`). -/
theorem assembly_small_L (h : HSRange τ s ε) (hL : hsL ε < 64 * τ) {QT : ℝ}
    (hT : cT * Real.sqrt s * τ ≤ QT) :
    c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤ QT := by
  have h1 := sum_le_of_small_L h hL
  have hpos : 0 ≤ Real.sqrt s * τ := mul_nonneg (Real.sqrt_nonneg _) h.tau_pos.le
  calc c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)
      ≤ c0 * (21 * (Real.sqrt s * τ)) := mul_le_mul_of_nonneg_left h1 c0_pos.le
    _ = (21 * c0) * (Real.sqrt s * τ) := by ring
    _ ≤ cT * (Real.sqrt s * τ) := mul_le_mul_of_nonneg_right c0_le hpos
    _ = cT * Real.sqrt s * τ := by ring
    _ ≤ QT := hT

/-! ### The case `L ≥ 64τ` (proof of Theorem `hsl:thm:main`) -/

/-- The three-family step (proof of Theorem `hsl:thm:main`): given the time bound, the precision
bound `r/32` and, according to whether `s < 64n/τ`, either the precision bound
`√(sτr)/(64√2)` or the mixed bound `(log 2/(384√2))√(sτr)`, the maximum of the
three quantities is at least `(c_T/3)(√s τ + √(sτr) + r)`. The hypotheses are
those available when `L ≥ 64τ`; the arithmetic itself does not use `L ≥ 64τ`. -/
theorem third_cT_mul_sum_le (h : HSRange τ s ε) {QT QM QP : ℝ}
    (hT : cT * Real.sqrt s * τ ≤ QT) (hPr : hsR τ ε / 32 ≤ QP)
    (hPm : (s : ℝ) < 64 * precN τ ε / τ → Real.sqrt (s * τ * hsR τ ε) / (64 * Real.sqrt 2) ≤ QP)
    (hM : 64 * (precN τ ε : ℝ) / τ ≤ s →
      Real.log 2 / (384 * Real.sqrt 2) * Real.sqrt (s * τ * hsR τ ε) ≤ QM) :
    cT / 3 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
      max QT (max QM QP) := by
  have hTX : QT ≤ max QT (max QM QP) := le_max_left _ _
  have hMX : QM ≤ max QT (max QM QP) := (le_max_left _ _).trans (le_max_right _ _)
  have hPX : QP ≤ max QT (max QM QP) := (le_max_right _ _).trans (le_max_right _ _)
  have hr := h.hsR_pos
  have hsq := Real.sqrt_nonneg ((s : ℝ) * τ * hsR τ ε)
  have h1 : cT * (Real.sqrt s * τ) ≤ max QT (max QM QP) := by
    rw [← mul_assoc]; exact hT.trans hTX
  have h2 : cT * hsR τ ε ≤ max QT (max QM QP) :=
    calc cT * hsR τ ε ≤ 1 / 32 * hsR τ ε := mul_le_mul_of_nonneg_right cT_le_inv_32 hr.le
      _ = hsR τ ε / 32 := by ring
      _ ≤ QP := hPr
      _ ≤ max QT (max QM QP) := hPX
  have h3 : cT * Real.sqrt (s * τ * hsR τ ε) ≤ max QT (max QM QP) := by
    rcases lt_or_ge (s : ℝ) (64 * precN τ ε / τ) with hc | hc
    · calc cT * Real.sqrt (s * τ * hsR τ ε)
          ≤ 1 / (64 * Real.sqrt 2) * Real.sqrt (s * τ * hsR τ ε) :=
            mul_le_mul_of_nonneg_right cT_le_failedConst hsq
        _ = Real.sqrt (s * τ * hsR τ ε) / (64 * Real.sqrt 2) := by ring
        _ ≤ QP := hPm hc
        _ ≤ max QT (max QM QP) := hPX
    · calc cT * Real.sqrt (s * τ * hsR τ ε)
          ≤ Real.log 2 / (384 * Real.sqrt 2) * Real.sqrt (s * τ * hsR τ ε) :=
            mul_le_mul_of_nonneg_right cT_le_mixConst hsq
        _ ≤ QM := hM hc
        _ ≤ max QT (max QM QP) := hMX
  linarith

/-- **The numerical bound of Theorem `hsl:thm:main`** (proof of Theorem `hsl:thm:main`), as the
maximum of the three family bounds: the time bound always, and for `L ≥ 64τ`
the precision bound `r/32` (and `√(sτr)/(64√2)` when `s < 64n/τ`) and the
mixed bound `(log 2/(384√2))√(sτr)` (when `s ≥ 64n/τ`). -/
theorem assembly (h : HSRange τ s ε) {QT QM QP : ℝ}
    (hT : cT * Real.sqrt s * τ ≤ QT)
    (hP : 64 * τ ≤ hsL ε → hsR τ ε / 32 ≤ QP ∧
      ((s : ℝ) < 64 * precN τ ε / τ → Real.sqrt (s * τ * hsR τ ε) / (64 * Real.sqrt 2) ≤ QP))
    (hM : 64 * τ ≤ hsL ε → 64 * (precN τ ε : ℝ) / τ ≤ s →
      Real.log 2 / (384 * Real.sqrt 2) * Real.sqrt (s * τ * hsR τ ε) ≤ QM) :
    c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤ max QT (max QM QP) := by
  rcases le_or_gt (64 * τ) (hsL ε) with hL | hL
  · obtain ⟨hPr, hPm⟩ := hP hL
    have key := third_cT_mul_sum_le h hT hPr hPm (hM hL)
    have hsum : 0 ≤ Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε :=
      add_nonneg (add_nonneg (mul_nonneg (Real.sqrt_nonneg _) h.tau_pos.le)
        (Real.sqrt_nonneg _)) h.hsR_pos.le
    have hc : c0 ≤ cT / 3 := by have := three_mul_c0_le; linarith
    exact (mul_le_mul_of_nonneg_right hc hsum).trans key
  · exact (assembly_small_L h hL hT).trans (le_max_left _ _)

end

end SparseLowerBounds.Hamiltonian
end
