import SparseLowerBounds.Query.Ancilla
import SparseLowerBounds.Query.Reduction

set_option synthInstance.maxHeartbeats 400000

section
/-!
# Parameters of the linear-system lower bound

The hard instance of Theorem `qlsl:thm:main` (manuscript lines 5070-5100) is
built from the parameters of eq. `qlsl:eq:parameters` (lines 5342-5348):

* `R = 2^{⌊log₂(κ/2)⌋}` (`hardR`, exponent `hardRho`),
* `m = 2^{⌊log₂(s-1)⌋}` (`hardM`, exponent `hardMu`),
* `L = ln(1/ε)`,
* `n = ⌊(R-1)/2 · ln(1/(16ε))⌋` (`hardN`),

and the clock ratio `r = 1 - 1/R` (`clockRatio`, eq. `qlsl:eq:C`). This module
proves every numeric fact the proof uses, in the parameter range
`κ ≥ 32`, `s ≥ 5`, `0 < ε ≤ 1/64` (`HardRange`): lines 5349-5433. It needs only
real analysis, so it can be proved independently of the operator modules.
-/

namespace SparseLowerBounds.LinearSystems

noncomputable section

/-- The parameter range of Theorem `qlsl:thm:main` (lines 5071-5072):
`κ ≥ 32`, `s ≥ 5`, `0 < ε ≤ 1/64`. -/
structure HardRange (κ : ℝ) (s : ℕ) (ε : ℝ) : Prop where
  kappa_ge : 32 ≤ κ
  s_ge : 5 ≤ s
  eps_pos : 0 < ε
  eps_le : ε ≤ 1 / 64

/-- `⌊log₂(κ/2)⌋`, the exponent of `R`. -/
def hardRho (κ : ℝ) : ℕ := Nat.log 2 ⌊κ / 2⌋₊

/-- `R = 2^{⌊log₂(κ/2)⌋}` (eq. `qlsl:eq:parameters`). -/
abbrev hardR (κ : ℝ) : ℕ := 2 ^ hardRho κ

/-- `⌊log₂(s-1)⌋`, the exponent of `m`. -/
def hardMu (s : ℕ) : ℕ := Nat.log 2 (s - 1)

/-- `m = 2^{⌊log₂(s-1)⌋}` (eq. `qlsl:eq:parameters`). -/
abbrev hardM (s : ℕ) : ℕ := 2 ^ hardMu s

/-- `n = ⌊(R-1)/2 · ln(1/(16ε))⌋` (eq. `qlsl:eq:parameters`). -/
def hardN (κ ε : ℝ) : ℕ := ⌊((hardR κ : ℝ) - 1) / 2 * Real.log (1 / (16 * ε))⌋₊

/-- The clock ratio `r = 1 - 1/R` for `R = 2^ρ` (eq. `qlsl:eq:C`). -/
def clockRatio (ρ : ℕ) : ℝ := 1 - 1 / 2 ^ ρ

/-- The answer-region probability `p = r^{2n}/(1 + r^{2n})` (eq. `qlsl:eq:p`). -/
def answerProb (r : ℝ) (n : ℕ) : ℝ := r ^ (2 * n) / (1 + r ^ (2 * n))

variable {κ ε : ℝ} {s : ℕ}

/-! ### Private numeric helpers -/

/-- `ln 2 > 2/3`, from `ln((15/14)^10) ≥ 10 (1 - 14/15)` and `(15/14)^10 < 2`. -/
lemma two_thirds_lt_log_two : (2 : ℝ) / 3 < Real.log 2 := by
  have h1 : (2 : ℝ) / 3 ≤ Real.log ((15 / 14 : ℝ) ^ 10) := by
    rw [Real.log_pow]
    have := Real.one_sub_inv_le_log_of_pos (x := (15 / 14 : ℝ)) (by norm_num)
    norm_num at this
    push_cast
    linarith
  have h2 : Real.log ((15 / 14 : ℝ) ^ 10) < Real.log 2 :=
    Real.log_lt_log (by positivity) (by norm_num)
  linarith

lemma sixteen_le_floor (h : HardRange κ s ε) : 16 ≤ ⌊κ / 2⌋₊ :=
  Nat.le_floor (by push_cast; linarith [h.kappa_ge])

lemma four_le_hardRho (h : HardRange κ s ε) : 4 ≤ hardRho κ :=
  Nat.le_log_of_pow_le (by norm_num) (le_trans (by norm_num) (sixteen_le_floor h))

/-- `L = ln(1/ε) ≥ ln 64 = 6 ln 2`. -/
lemma six_log_two_le (h : HardRange κ s ε) : 6 * Real.log 2 ≤ Real.log (1 / ε) := by
  have h64 : (64 : ℝ) ≤ 1 / ε := by
    rw [le_div_iff₀ h.eps_pos]; linarith [h.eps_le]
  calc 6 * Real.log 2 = Real.log ((2 : ℝ) ^ 6) := by rw [Real.log_pow]; push_cast; ring
    _ = Real.log 64 := by norm_num
    _ ≤ Real.log (1 / ε) := Real.log_le_log (by norm_num) h64

/-- `ln(1/(16ε)) = L - 4 ln 2`. -/
lemma log_sixteen_eq (h : HardRange κ s ε) :
    Real.log (1 / (16 * ε)) = Real.log (1 / ε) - 4 * Real.log 2 := by
  have he := h.eps_pos
  rw [show 1 / (16 * ε) = (1 / ε) / 2 ^ 4 by ring, Real.log_div (by positivity) (by norm_num),
    Real.log_pow]
  push_cast; ring

lemma four_le_log (h : HardRange κ s ε) : 4 ≤ Real.log (1 / ε) := by
  linarith [six_log_two_le h, two_thirds_lt_log_two]

lemma log_sixteen_nonneg (h : HardRange κ s ε) : 0 ≤ Real.log (1 / (16 * ε)) := by
  rw [log_sixteen_eq h]; linarith [six_log_two_le h, two_thirds_lt_log_two]

lemma log_sixteen_le (h : HardRange κ s ε) :
    Real.log (1 / (16 * ε)) ≤ Real.log (1 / ε) := by
  rw [log_sixteen_eq h]; linarith [two_thirds_lt_log_two]

/-! ### `R` and `m` (lines 5349-5352) -/

theorem sixteen_le_hardR (h : HardRange κ s ε) : 16 ≤ hardR κ := by
  exact calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ hardRho κ := Nat.pow_le_pow_right (by norm_num) (four_le_hardRho h)

lemma sixteen_le_hardR_real (h : HardRange κ s ε) : (16 : ℝ) ≤ (hardR κ : ℝ) := by
  exact_mod_cast sixteen_le_hardR h

theorem kappa_div_four_lt_hardR (_h : HardRange κ s ε) : κ / 4 < (hardR κ : ℝ) := by
  have h1 : ⌊κ / 2⌋₊ < 2 ^ (hardRho κ + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  rw [pow_succ] at h1
  have h2 : ⌊κ / 2⌋₊ + 1 ≤ hardR κ * 2 := h1
  have h3 : ((⌊κ / 2⌋₊ : ℕ) : ℝ) + 1 ≤ (hardR κ : ℝ) * 2 := by exact_mod_cast h2
  have h4 := Nat.lt_floor_add_one (κ / 2)
  linarith

theorem hardR_le_kappa_div_two (h : HardRange κ s ε) : (hardR κ : ℝ) ≤ κ / 2 := by
  have h1 : hardR κ ≤ ⌊κ / 2⌋₊ :=
    Nat.pow_log_le_self 2 (by have := sixteen_le_floor h; omega)
  have h2 : (hardR κ : ℝ) ≤ ((⌊κ / 2⌋₊ : ℕ) : ℝ) := by exact_mod_cast h1
  have h3 : ((⌊κ / 2⌋₊ : ℕ) : ℝ) ≤ κ / 2 := Nat.floor_le (by linarith [h.kappa_ge])
  linarith

/-- `‖A⁻¹‖ ≤ 2R ≤ κ` (line 5351). -/
theorem two_hardR_le_kappa (h : HardRange κ s ε) : 2 * (hardR κ : ℝ) ≤ κ := by
  linarith [hardR_le_kappa_div_two h]

theorem two_le_hardMu (h : HardRange κ s ε) : 2 ≤ hardMu s := by
  exact Nat.le_log_of_pow_le (by norm_num) (by have := h.s_ge; norm_num; omega)

theorem four_le_hardM (h : HardRange κ s ε) : 4 ≤ hardM s := by
  exact calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ hardMu s := Nat.pow_le_pow_right (by norm_num) (two_le_hardMu h)

theorem even_hardM (h : HardRange κ s ε) : Even (hardM s) := by
  exact Nat.even_pow.mpr ⟨even_two, by have := two_le_hardMu h; omega⟩

lemma hardM_le (h : HardRange κ s ε) : hardM s ≤ s - 1 :=
  Nat.pow_log_le_self 2 (by have := h.s_ge; omega)

lemma s_le_two_hardM (h : HardRange κ s ε) : s ≤ 2 * hardM s := by
  have h1 : s - 1 < 2 ^ (hardMu s + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  rw [pow_succ] at h1
  have h2 : s - 1 + 1 ≤ hardM s * 2 := h1
  have := h.s_ge
  omega

/-- `m > s/4` (line 5349; in fact `m ≥ s/2`). -/
theorem s_div_four_lt_hardM (h : HardRange κ s ε) : (s : ℝ) / 4 < hardM s := by
  have h1 : (s : ℝ) ≤ 2 * (hardM s : ℝ) := by exact_mod_cast s_le_two_hardM h
  have h2 : (4 : ℝ) ≤ (hardM s : ℝ) := by exact_mod_cast four_le_hardM h
  linarith

/-- `m + 1 ≤ s` (line 5352): the hard matrices are `s`-sparse. -/
theorem hardM_succ_le (h : HardRange κ s ε) : hardM s + 1 ≤ s := by
  have h1 := hardM_le h
  have := h.s_ge
  omega

/-! ### `n` (eq. `qlsl:eq:nrange`, lines 5354-5366) -/

/-- `ln(1/(16ε)) ≥ L/3`, from `L ≥ ln 64` (lines 5354-5355). -/
theorem log_div_three_le (h : HardRange κ s ε) :
    Real.log (1 / ε) / 3 ≤ Real.log (1 / (16 * ε)) := by
  rw [log_sixteen_eq h]; linarith [six_log_two_le h]

lemma hardN_le_real (h : HardRange κ s ε) :
    (hardN κ ε : ℝ) ≤ ((hardR κ : ℝ) - 1) / 2 * Real.log (1 / (16 * ε)) := by
  have hR := sixteen_le_hardR_real h
  exact Nat.floor_le (mul_nonneg (by linarith) (log_sixteen_nonneg h))

lemma lt_hardN_add_one (_h : HardRange κ s ε) :
    ((hardR κ : ℝ) - 1) / 2 * Real.log (1 / (16 * ε)) < (hardN κ ε : ℝ) + 1 :=
  Nat.lt_floor_add_one _

/-- **Eq. `qlsl:eq:nrange`** (lines 5356-5364):
`(R-1)L/6 - 1 ≤ n`, `RL/8 ≤ n`, `κL/32 < n` and `n ≤ RL/2`. -/
theorem nrange (h : HardRange κ s ε) :
    ((hardR κ : ℝ) - 1) * Real.log (1 / ε) / 6 - 1 ≤ hardN κ ε ∧
      (hardR κ : ℝ) * Real.log (1 / ε) / 8 ≤ hardN κ ε ∧
      κ * Real.log (1 / ε) / 32 < hardN κ ε ∧
      (hardN κ ε : ℝ) ≤ (hardR κ : ℝ) * Real.log (1 / ε) / 2 := by
  have hR := sixteen_le_hardR_real h
  have hL := four_le_log h
  have h3 := log_div_three_le h
  have hℓ0 := log_sixteen_nonneg h
  have hℓL := log_sixteen_le h
  have hlo := lt_hardN_add_one h
  have hhi := hardN_le_real h
  have hκ := kappa_div_four_lt_hardR h
  have e1 : ((hardR κ : ℝ) - 1) / 2 * (Real.log (1 / ε) / 3) ≤
      ((hardR κ : ℝ) - 1) / 2 * Real.log (1 / (16 * ε)) :=
    mul_le_mul_of_nonneg_left h3 (by linarith)
  have first : ((hardR κ : ℝ) - 1) * Real.log (1 / ε) / 6 - 1 ≤ hardN κ ε := by linarith
  have e2 : (12 : ℝ) * 4 ≤ ((hardR κ : ℝ) - 4) * Real.log (1 / ε) :=
    mul_le_mul_of_nonneg (by linarith) hL (by norm_num) (by linarith)
  have second : (hardR κ : ℝ) * Real.log (1 / ε) / 8 ≤ hardN κ ε := by linarith
  have e3 : κ * Real.log (1 / ε) < (4 * (hardR κ : ℝ)) * Real.log (1 / ε) :=
    mul_lt_mul_of_pos_right (by linarith) (by linarith)
  have e4 : ((hardR κ : ℝ) - 1) * Real.log (1 / (16 * ε)) ≤
      (hardR κ : ℝ) * Real.log (1 / ε) :=
    mul_le_mul_of_nonneg (by linarith) hℓL (by linarith) (by linarith)
  exact ⟨first, second, by linarith, by linarith⟩

/-- `n ≥ 2L` (line 5365). -/
theorem two_log_le_hardN (h : HardRange κ s ε) : 2 * Real.log (1 / ε) ≤ hardN κ ε := by
  have hR := sixteen_le_hardR_real h
  have hL := four_le_log h
  have e : (16 : ℝ) * Real.log (1 / ε) ≤ (hardR κ : ℝ) * Real.log (1 / ε) :=
    mul_le_mul_of_nonneg_right hR (by linarith)
  linarith [(nrange h).2.1]

/-- `n ≥ R/2` (line 5365), as used for the actual conditioning. -/
theorem hardR_le_two_hardN (h : HardRange κ s ε) : hardR κ ≤ 2 * hardN κ ε := by
  have hR := sixteen_le_hardR_real h
  have hL := four_le_log h
  have e : (hardR κ : ℝ) * 4 ≤ (hardR κ : ℝ) * Real.log (1 / ε) :=
    mul_le_mul_of_nonneg_left hL (by linarith)
  have h1 : (hardR κ : ℝ) ≤ 2 * (hardN κ ε : ℝ) := by linarith [(nrange h).2.1]
  exact_mod_cast h1

theorem hardN_pos (h : HardRange κ s ε) : 0 < hardN κ ε := by
  have h1 : (0 : ℝ) < hardN κ ε := by linarith [two_log_le_hardN h, four_le_log h]
  exact_mod_cast h1

/-! ### Dimension `N = 4mn` (lines 5088-5089, 5302 and 5365-5366) -/

/-- The slot list fits into the dimension: `s ≤ N = 4mn`. -/
theorem s_le_dim (h : HardRange κ s ε) : s ≤ 4 * hardM s * hardN κ ε := by
  have h1 := s_le_two_hardM h
  have h2 : 1 ≤ hardN κ ε := hardN_pos h
  calc s ≤ 4 * hardM s * 1 := by omega
    _ ≤ 4 * hardM s * hardN κ ε := Nat.mul_le_mul_left _ h2

/-- `N = Θ(s κ L)`: `s κ L / 32 ≤ 4mn ≤ (s-1) κ L`. -/
theorem dim_bounds (h : HardRange κ s ε) :
    (s : ℝ) * κ * Real.log (1 / ε) / 32 ≤ 4 * (hardM s : ℝ) * hardN κ ε ∧
      4 * (hardM s : ℝ) * hardN κ ε ≤ ((s : ℝ) - 1) * κ * Real.log (1 / ε) := by
  obtain ⟨-, -, hn3, hn4⟩ := nrange h
  have hL := four_le_log h
  have hκ := h.kappa_ge
  have hRk := hardR_le_kappa_div_two h
  have hm := s_div_four_lt_hardM h
  have hm1 : (hardM s : ℝ) + 1 ≤ s := by exact_mod_cast hardM_succ_le h
  have hm0 : (0 : ℝ) ≤ hardM s := Nat.cast_nonneg _
  have hn0 : (0 : ℝ) ≤ hardN κ ε := Nat.cast_nonneg _
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg _
  have hκL : (0 : ℝ) ≤ κ * Real.log (1 / ε) := mul_nonneg (by linarith) (by linarith)
  have e1 : (s : ℝ) * (κ * Real.log (1 / ε) / 32) ≤ (4 * (hardM s : ℝ)) * hardN κ ε :=
    mul_le_mul_of_nonneg (by linarith) hn3.le hs0 hn0
  have e2 : (hardR κ : ℝ) * Real.log (1 / ε) ≤ κ / 2 * Real.log (1 / ε) :=
    mul_le_mul_of_nonneg_right hRk (by linarith)
  have e3 : (hardM s : ℝ) * hardN κ ε ≤ ((s : ℝ) - 1) * (κ * Real.log (1 / ε) / 4) :=
    mul_le_mul_of_nonneg (by linarith) (by linarith) hm0 (by linarith)
  constructor
  · linarith
  · linarith

/-! ### Answer probability and bias (lines 5392-5418) -/

lemma one_le_two_pow (ρ : ℕ) : (1 : ℝ) ≤ (2 : ℝ) ^ ρ := one_le_pow₀ (by norm_num)

theorem clockRatio_nonneg (ρ : ℕ) : 0 ≤ clockRatio ρ := by
  have h1 := one_le_two_pow ρ
  have h2 : 1 / (2 : ℝ) ^ ρ ≤ 1 := by rw [div_le_one (by positivity)]; exact h1
  unfold clockRatio; linarith

theorem clockRatio_lt_one (ρ : ℕ) : clockRatio ρ < 1 := by
  have h2 : 0 < 1 / (2 : ℝ) ^ ρ := by positivity
  unfold clockRatio; linarith

/-- `ln r ≥ -1/(R-1)` for `r = 1 - 1/R`, `R = 2^ρ ≥ 2`. -/
lemma neg_inv_le_log_clockRatio {ρ : ℕ} (hR : (2 : ℝ) ≤ (2 : ℝ) ^ ρ) :
    -(1 / ((2 : ℝ) ^ ρ - 1)) ≤ Real.log (clockRatio ρ) := by
  have hR1 : (0 : ℝ) < (2 : ℝ) ^ ρ - 1 := by linarith
  have hpos : 0 < clockRatio ρ := by
    unfold clockRatio
    have : 1 / (2 : ℝ) ^ ρ ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hR
    linarith
  have h1 := Real.one_sub_inv_le_log_of_pos hpos
  have h2 : 1 - (clockRatio ρ)⁻¹ = -(1 / ((2 : ℝ) ^ ρ - 1)) := by
    unfold clockRatio
    have h0 : (2 : ℝ) ^ ρ ≠ 0 := by positivity
    have h0' : (2 : ℝ) ^ ρ - 1 ≠ 0 := hR1.ne'
    rw [show (1 : ℝ) - 1 / 2 ^ ρ = (2 ^ ρ - 1) / 2 ^ ρ by field_simp, inv_div]
    field_simp
    ring
  linarith

/-- `r^{2n} ≥ e^{-2n/(R-1)} ≥ 16ε` (lines 5392-5395). -/
theorem sixteen_eps_le_pow (h : HardRange κ s ε) :
    16 * ε ≤ clockRatio (hardRho κ) ^ (2 * hardN κ ε) := by
  have hRc : (hardR κ : ℝ) = (2 : ℝ) ^ hardRho κ := by push_cast; rfl
  have hR := sixteen_le_hardR_real h
  rw [hRc] at hR
  have he := h.eps_pos
  have hr : 0 < clockRatio (hardRho κ) := by
    have h2 : 1 / (2 : ℝ) ^ hardRho κ ≤ 1 / 16 := one_div_le_one_div_of_le (by norm_num) hR
    unfold clockRatio; linarith
  have hlogr := neg_inv_le_log_clockRatio (ρ := hardRho κ) (by linarith)
  have hn := hardN_le_real h
  rw [hRc] at hn
  set R : ℝ := (2 : ℝ) ^ hardRho κ with hRdef
  set ℓ := Real.log (1 / (16 * ε)) with hℓdef
  set n : ℝ := (hardN κ ε : ℝ) with hndef
  have hR1 : 0 < R - 1 := by linarith
  -- `2n/(R-1) ≤ ℓ`
  have h2n : 2 * n / (R - 1) ≤ ℓ := by
    rw [div_le_iff₀ hR1]; linarith
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  have e1 : 2 * n * (-(1 / (R - 1))) ≤ 2 * n * Real.log (clockRatio (hardRho κ)) :=
    mul_le_mul_of_nonneg_left hlogr (by linarith)
  have e2 : 2 * n * (-(1 / (R - 1))) = -(2 * n / (R - 1)) := by ring
  have hlogpow : Real.log (clockRatio (hardRho κ) ^ (2 * hardN κ ε)) =
      2 * n * Real.log (clockRatio (hardRho κ)) := by
    rw [Real.log_pow]; push_cast; ring
  have hℓ : ℓ = -Real.log (16 * ε) := by
    rw [hℓdef, one_div, Real.log_inv]
  have key : Real.log (16 * ε) ≤ Real.log (clockRatio (hardRho κ) ^ (2 * hardN κ ε)) := by
    rw [hlogpow]; linarith
  exact (Real.log_le_log_iff (by positivity) (by positivity)).mp key

/-- **Eq. `qlsl:eq:answerprob`** (lines 5396-5400): `p ≥ 16ε/(1+16ε) ≥ 64ε/5`. -/
theorem answerProb_ge (h : HardRange κ s ε) :
    64 / 5 * ε ≤ answerProb (clockRatio (hardRho κ)) (hardN κ ε) := by
  have hq := sixteen_eps_le_pow h
  have he := h.eps_pos
  have he' := h.eps_le
  unfold answerProb
  set q := clockRatio (hardRho κ) ^ (2 * hardN κ ε) with hqdef
  have hq0 : 0 ≤ q := by linarith
  rw [le_div_iff₀ (by linarith)]
  have e1 : 16 * ε * (1 - 64 / 5 * ε) ≤ q * (1 - 64 / 5 * ε) :=
    mul_le_mul_of_nonneg_right hq (by linarith)
  have e2 : ε * ε ≤ ε * (1 / 64) := mul_le_mul_of_nonneg_left he' he.le
  nlinarith

theorem two_eps_le_answerProb (h : HardRange κ s ε) :
    2 * ε ≤ answerProb (clockRatio (hardRho κ)) (hardN κ ε) := by
  linarith [answerProb_ge h, h.eps_pos]

/-- **Eq. `qlsl:eq:bias`** (lines 5409-5416): `(2/3)(p - 2ε) ≥ 36ε/5 ≥ ε`. -/
theorem eps_le_bias (h : HardRange κ s ε) :
    ε ≤ 2 / 3 * (answerProb (clockRatio (hardRho κ)) (hardN κ ε) - 2 * ε) := by
  linarith [answerProb_ge h, h.eps_pos]

/-! ### The final inequality (lines 5420-5433) -/

/-- **The final count** (lines 5420-5433). With `β = ε`, the right side is the
XOR lower bound `(√m/4)(n ln 2 + ln β)` of `qlsl:lem:xor`; using `n ≥ 2L`,
`ln 2 > 2/3`, eq. `qlsl:eq:nrange` and `√m > √s/2`, it exceeds
`κ √s ln(1/ε)/1536`. A Boolean count `2Q` at least the XOR bound therefore
gives `Q > κ √s ln(1/ε)/3072`. -/
theorem final_bound (h : HardRange κ s ε) :
    κ * Real.sqrt s * Real.log (1 / ε) / 1536 <
      Real.sqrt (hardM s) / 4 * (hardN κ ε * Real.log 2 + Real.log ε) := by
  have hlogε : Real.log ε = -Real.log (1 / ε) := by rw [one_div, Real.log_inv, neg_neg]
  rw [hlogε]
  have hL := four_le_log h
  have hκ := h.kappa_ge
  have h2L := two_log_le_hardN h
  have hn3 := (nrange h).2.2.1
  have hlog2 := two_thirds_lt_log_two
  have hnpos : (0 : ℝ) < hardN κ ε := by linarith
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg _
  have hsqrt : Real.sqrt s / 2 < Real.sqrt (hardM s) := by
    rw [Real.lt_sqrt (by positivity), div_pow, Real.sq_sqrt hs0]
    linarith [s_div_four_lt_hardM h]
  have hsq0 : 0 ≤ Real.sqrt s / 2 := by positivity
  have hm0 : 0 < Real.sqrt (hardM s) := lt_of_le_of_lt hsq0 hsqrt
  have hκL : 0 < κ * Real.log (1 / ε) / 32 := by
    have : 0 < κ * Real.log (1 / ε) := mul_pos (by linarith) (by linarith)
    linarith
  -- `√s/2 · κL/32 < √m · n`
  have e1 : Real.sqrt s / 2 * (κ * Real.log (1 / ε) / 32) <
      Real.sqrt (hardM s) * hardN κ ε := by
    rcases hsq0.eq_or_lt with h0 | h0
    · rw [← h0, zero_mul]; exact mul_pos hm0 hnpos
    · exact mul_lt_mul_of_pos hsqrt hn3 h0 hnpos
  -- `n ln 2 - L > n/6`
  have e2 : (hardN κ ε : ℝ) * (2 / 3) < hardN κ ε * Real.log 2 :=
    mul_lt_mul_of_pos_left hlog2 hnpos
  have e3 : Real.sqrt (hardM s) / 4 * ((hardN κ ε : ℝ) / 6) <
      Real.sqrt (hardM s) / 4 * (hardN κ ε * Real.log 2 + -Real.log (1 / ε)) :=
    mul_lt_mul_of_pos_left (by linarith) (by positivity)
  have e4 : κ * Real.sqrt s * Real.log (1 / ε) / 1536 =
      Real.sqrt s / 2 * (κ * Real.log (1 / ε) / 32) / 24 := by ring
  have e5 : Real.sqrt (hardM s) / 4 * ((hardN κ ε : ℝ) / 6) =
      Real.sqrt (hardM s) * hardN κ ε / 24 := by ring
  rw [e4]
  linarith

end

end SparseLowerBounds.LinearSystems
end
