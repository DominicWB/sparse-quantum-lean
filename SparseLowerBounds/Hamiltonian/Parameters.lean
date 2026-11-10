import SparseLowerBounds.Query.PhaseCircuit

set_option synthInstance.maxHeartbeats 400000

section
/-!
# Parameters of Theorem `hsl:thm:main`

Manuscript: Theorem `hsl:thm:main` (eqs. `hsl:eq:parameters` and `hsl:eq:main`), Lemma
`hsl:lem:time` (time family) and eq. `hsl:eq:nchoice`.
Real analysis only; no quantum objects.

* `HSRange τ s ε`: exactly `τ ≥ 1`, `s ≥ 32`, `0 < ε ≤ 1/64`;
* `hsL ε = log(1/ε)`, `hsH τ ε = log(e + L/τ)`, `hsR τ ε = L/h`;
* `hsMu s = ⌊log₂ s⌋ - 1`, so `hsM s = 2^{hsMu s}` is the largest power of two
  at most `s/2` (eq. `hsl:eq:mrange`);
* time family: `timeN τ = max{1, ⌊2τ/π⌋}`, `timeC τ = min{1, π n/(2τ)}`;
* mixed and precision families: `precN τ ε = ⌊r/4⌋` (eq. `hsl:eq:nchoice`);
* constants `c0 = log 2/(4096π)` (eq. `hsl:eq:main`) and `cT = log 2/(192π)`
  (eq. `hsl:eq:timelower`).

Basic facts: the binary-logarithm bracket `2^{hsMu s + 1} ≤ s < 2^{hsMu s + 2}`
(`two_pow_hsMu_succ_le`, `lt_two_pow_hsMu_add_two`), eq. `hsl:eq:mrange`
(`hsM_range`), `L ≥ log 64 > 4` (`HSRange.four_le_hsL`), `h ≥ 1`, `0 < r ≤ L`,
`L = r h` (`HSRange.hsR_mul_hsH`), `ε = e^{-L}` (`exp_neg_hsL`), and
`n = ⌊r/4⌋ ≤ r/4` (`HSRange.precN_le_quarter`).

The per-family and assembly inequalities are in `Hamiltonian/Numerics` and
`Hamiltonian/Assembly`.
-/

namespace SparseLowerBounds.Hamiltonian

noncomputable section

/-- The parameter range of Theorem `hsl:thm:main`. -/
structure HSRange (τ : ℝ) (s : ℕ) (ε : ℝ) : Prop where
  one_le_tau : 1 ≤ τ
  s_ge : 32 ≤ s
  eps_pos : 0 < ε
  eps_le : ε ≤ 1 / 64

/-- `L = log(1/ε)` (eq. `hsl:eq:parameters`). -/
def hsL (ε : ℝ) : ℝ := Real.log (1 / ε)

/-- `h = log(e + L/τ)` (eq. `hsl:eq:parameters`). -/
def hsH (τ ε : ℝ) : ℝ := Real.log (Real.exp 1 + hsL ε / τ)

/-- `r = L/h` (eq. `hsl:eq:parameters`). -/
def hsR (τ ε : ℝ) : ℝ := hsL ε / hsH τ ε

/-- `log₂ m` for the largest power of two `m ≤ s/2` (eq. `hsl:eq:mrange`). -/
def hsMu (s : ℕ) : ℕ := Nat.log 2 s - 1

/-- `m = 2^{hsMu s}`, the largest power of two at most `s/2`. -/
def hsM (s : ℕ) : ℕ := 2 ^ hsMu s

/-- The time family's clock length `n = max{1, ⌊2τ/π⌋}` (proof of Lemma `hsl:lem:time`). -/
def timeN (τ : ℝ) : ℕ := max 1 ⌊2 * τ / Real.pi⌋₊

/-- The time family's weight scale `c = min{1, π n/(2τ)}` (proof of Lemma `hsl:lem:time`). -/
def timeC (τ : ℝ) : ℝ := min 1 (Real.pi * timeN τ / (2 * τ))

/-- The mixed and precision families' clock length `n = ⌊r/4⌋`
(eq. `hsl:eq:nchoice`). -/
def precN (τ ε : ℝ) : ℕ := ⌊hsR τ ε / 4⌋₊

/-- The constant of eq. `hsl:eq:main`, `c₀ = log 2/(4096π)`. -/
def c0 : ℝ := Real.log 2 / (4096 * Real.pi)

/-- The time constant of eq. `hsl:eq:timelower`, `c_T = log 2/(192π)`. -/
def cT : ℝ := Real.log 2 / (192 * Real.pi)

variable {τ ε : ℝ} {s : ℕ}

/-! ### The power of two `m = 2^{hsMu s}` (eq. `hsl:eq:mrange`) -/

/-- `hsMu s + 1 = ⌊log₂ s⌋` as soon as `s ≥ 2` (the truncated subtraction in
`hsMu` does not bite). -/
theorem hsMu_add_one (hs : 2 ≤ s) : hsMu s + 1 = Nat.log 2 s := by
  have : 0 < Nat.log 2 s := Nat.log_pos (by norm_num) hs
  unfold hsMu
  omega

/-- Lower half of the binary-logarithm bracket: `2^{hsMu s + 1} = 2^{⌊log₂ s⌋} ≤ s`. -/
theorem two_pow_hsMu_succ_le (hs : 2 ≤ s) : 2 ^ (hsMu s + 1) ≤ s := by
  rw [hsMu_add_one hs]
  exact Nat.pow_log_le_self 2 (by omega)

/-- Upper half of the binary-logarithm bracket: `s < 2^{⌊log₂ s⌋ + 1} = 2^{hsMu s + 2}`. -/
theorem lt_two_pow_hsMu_add_two (hs : 2 ≤ s) : s < 2 ^ (hsMu s + 2) := by
  have h1 := hsMu_add_one hs
  rw [show hsMu s + 2 = Nat.log 2 s + 1 by omega]
  exact Nat.lt_pow_succ_log_self (by norm_num) s

/-- `hsMu s ≥ 4` for `s ≥ 32` (so `m ≥ 16`, eq. `hsl:eq:mrange`). -/
theorem four_le_hsMu (hs : 32 ≤ s) : 4 ≤ hsMu s := by
  have h5 : 5 ≤ Nat.log 2 s := Nat.le_log_of_pow_le (by norm_num) (by norm_num; omega)
  unfold hsMu
  omega

/-- `hsMu s ≥ 1` for `s ≥ 32`, the hypothesis `1 ≤ μ` of the search families. -/
theorem one_le_hsMu (hs : 32 ≤ s) : 1 ≤ hsMu s := by
  have := four_le_hsMu hs
  omega

/-- `2m ≤ s` for `m = 2^{hsMu s}`. -/
theorem two_mul_hsM_le (hs : 32 ≤ s) : 2 * 2 ^ hsMu s ≤ s := by
  have h := two_pow_hsMu_succ_le (s := s) (by omega)
  rw [pow_succ] at h
  linarith

/-- **Eq. `hsl:eq:mrange`** (Lemma `hsl:lem:time`): `m ≥ 16` and `s/4 < m ≤ s/2`. -/
theorem hsM_range (hs : 32 ≤ s) :
    16 ≤ 2 ^ hsMu s ∧ (s : ℝ) / 4 < (2 : ℝ) ^ hsMu s ∧ (2 : ℝ) ^ hsMu s ≤ s / 2 := by
  refine ⟨?_, ?_, ?_⟩
  · calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ hsMu s := Nat.pow_le_pow_right (by norm_num) (four_le_hsMu hs)
  · have h1 := lt_two_pow_hsMu_add_two (s := s) (by omega)
    rw [pow_add] at h1
    have h2 : s < 2 ^ hsMu s * 4 := by simpa using h1
    have h3 : (s : ℝ) < (2 : ℝ) ^ hsMu s * 4 := by exact_mod_cast h2
    linarith
  · have h := two_mul_hsM_le hs
    have h' : (2 : ℝ) * 2 ^ hsMu s ≤ s := by exact_mod_cast h
    linarith

/-- The time family's clock length is positive (proof of Lemma `hsl:lem:time`). -/
theorem one_le_timeN (τ : ℝ) : 1 ≤ timeN τ := le_max_left _ _

/-! ### `L`, `h`, `r` (eq. `hsl:eq:parameters`) -/

/-- `L = log(1/ε) = -log ε` (any `ε`; `Real.log` is even and `log 0 = 0`). -/
theorem hsL_eq_neg_log (ε : ℝ) : hsL ε = -Real.log ε := by
  unfold hsL
  rw [one_div, Real.log_inv]

/-- `ε = e^{-L}` (used in the form `8ε = 8e^{-L}`, proof of Theorem `hsl:thm:main`). -/
theorem exp_neg_hsL (hε : 0 < ε) : Real.exp (-hsL ε) = ε := by
  rw [hsL_eq_neg_log, neg_neg, Real.exp_log hε]

/-- `τ > 0` in the parameter range. -/
theorem HSRange.tau_pos (h : HSRange τ s ε) : 0 < τ := by
  exact lt_of_lt_of_le one_pos h.one_le_tau

/-- `L ≥ log 64` from `ε ≤ 1/64`. -/
theorem HSRange.log_64_le_hsL (h : HSRange τ s ε) : Real.log 64 ≤ hsL ε := by
  unfold hsL
  apply Real.log_le_log (by norm_num)
  rw [le_div_iff₀ h.eps_pos]
  linarith [h.eps_le]

/-- `L ≥ 4` (`log 64 ≈ 4.159`); enough for `e^{-L/4} ≥ 16 e^{-L}`. -/
theorem HSRange.four_le_hsL (h : HSRange τ s ε) : 4 ≤ hsL ε := by
  refine le_trans ?_ h.log_64_le_hsL
  rw [Real.le_log_iff_exp_le (by norm_num)]
  -- `exp 4 = exp(1/16)^64 ≤ (16/15)^64 < 63` (`exp x ≤ 1/(1-x)` on `[0,1)`).
  have h1 : Real.exp 4 = Real.exp (1 / 16) ^ 64 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have h2 : Real.exp (1 / 16) ≤ 16 / 15 := by
    have := Real.exp_bound_div_one_sub_of_interval (x := 1 / 16) (by norm_num) (by norm_num)
    norm_num at this ⊢
    exact this
  have h3 : Real.exp (1 / 16) ^ 64 ≤ (16 / 15 : ℝ) ^ 64 :=
    pow_le_pow_left₀ (Real.exp_pos _).le h2 64
  rw [h1]
  refine h3.trans ?_
  norm_num

/-- `L > 0` in the parameter range. -/
theorem HSRange.hsL_pos (h : HSRange τ s ε) : 0 < hsL ε := by
  linarith [h.four_le_hsL]

/-- `h ≥ 1` (proof of Theorem `hsl:thm:main`). -/
theorem HSRange.one_le_hsH (h : HSRange τ s ε) : 1 ≤ hsH τ ε := by
  have hpos : 0 < hsL ε / τ := div_pos h.hsL_pos h.tau_pos
  unfold hsH
  rw [Real.le_log_iff_exp_le (by positivity)]
  linarith

/-- `h > 0` in the parameter range. -/
theorem HSRange.hsH_pos (h : HSRange τ s ε) : 0 < hsH τ ε := by
  exact one_pos.trans_le h.one_le_hsH

/-- `r > 0` in the parameter range. -/
theorem HSRange.hsR_pos (h : HSRange τ s ε) : 0 < hsR τ ε := by
  exact div_pos h.hsL_pos h.hsH_pos

/-- `r ≤ L`. -/
theorem HSRange.hsR_le_hsL (h : HSRange τ s ε) : hsR τ ε ≤ hsL ε := by
  exact div_le_self h.hsL_pos.le h.one_le_hsH

/-- `L = r h` (definition of `r`, using `h ≠ 0`). -/
theorem HSRange.hsR_mul_hsH (h : HSRange τ s ε) : hsR τ ε * hsH τ ε = hsL ε := by
  exact div_mul_cancel₀ _ h.hsH_pos.ne'

/-- `n = ⌊r/4⌋ ≤ r/4` (eq. `hsl:eq:nrange`, third part; no `L ≥ 64τ` needed). -/
theorem HSRange.precN_le_quarter (h : HSRange τ s ε) : (precN τ ε : ℝ) ≤ hsR τ ε / 4 := by
  exact Nat.floor_le (div_nonneg h.hsR_pos.le (by norm_num))

/-! ### The constants -/

/-- `c₀ > 0`. -/
theorem c0_pos : 0 < c0 := by
  exact div_pos (Real.log_pos one_lt_two) (by positivity)

/-- `c_T > 0`. -/
theorem cT_pos : 0 < cT := by
  exact div_pos (Real.log_pos one_lt_two) (by positivity)

end

end SparseLowerBounds.Hamiltonian
end
