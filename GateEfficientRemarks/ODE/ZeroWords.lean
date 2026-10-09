import GateEfficientRemarks.ODE.MinRegister
import GateEfficientBitBudget.Constant
import ZeroTimeGateODE.Binary

/-!
# Zero time or a known zero generator: the words of the released binary registers

The released key lemmas `GateBitBudget.words_le` and `GateBitBudget.wordsT_le` of the word budget
`ode:eq:gate-word-budget` of Theorem `ode:thm:gates` bound the register words of the dissipative
solvers from binary data, `𝔴 = GateODEBudget.words q` (the sum of the words
`k_x, b, m, r, k, l, F, n_c, ⌈log₂ ⌈κ⌉⌉, ⌈log₂ ⌈1/κ⌉⌉`), resp. `GateODEBudget.wordsT q` (without the
quadrature word `k`), by `𝔴 + ℓ ≤ 300 (𝔟 + 1)` under the released public conditions with the public
rescaling `γ = gammaOf T η_H η_D g ε`, which vanishes in the zero case. For zero time or a known
zero generator (`ZeroTimeGateODE.BZeroCase`, `ZeroTimeGateODE.BTZeroCase`: `T = 0 ∨ η_H + η_D = 0`)
the released registers of the combined preparations `ZeroTimeGateODE.bprepC`,
`ZeroTimeGateODE.btprepC` keep these words, with the rescaling `γ ∈ (0, 1]` a public parameter. This
module collects the word bounds that do not depend on the time:

* the envelope lemmas `env_*` (the released `shape_*` lemmas of `GateBitBudget` for any query
  shape `Q ≥ 1`, with `X = (Q g + 1)/ε`), including `env_radius_le`: `1 + R ≤ 2^17 X` for the
  LCHS radius `R`;
* the words of a simulator at zero common time: the clock width `Q_w = width(4s, γ) ≤ 3 · 2^k_x`
  (`width_le_of`), the reuse word `r ≤ 24 + k_x + log₂ X` from a filter degree
  `d ≤ 128 Q_w (1 + log(3/ν))` (`r_word_of`), the LCHS grid `J ≤ 60 Q ℓ` at zero dissipative time
  (`J_le_of`), and the decoder words for `γ` of bit length `b_data` (`kap_words_of`:
  `κ = γ √(4s) c₀ / (2^e ρ)` is zero for zero energy bounds and otherwise satisfies the released
  `kap_le`, `kap_inv_le` with `γ⁻¹ ≤ 2^b_data`); the public choice `γ = 1` has every bit length
  `b_data ≥ 1` (`hasBits_one`);
* for the constant-coefficient data: the common simulation time and the energy scales vanish
  (`zero_TlamD`, `zero_TlamHD`, `zero_tau`), so the time and quadrature words vanish (`zero_m`,
  `zero_k`), the filter degree is `d ≤ 128 Q_w (1 + log(3/ν))` (`zero_degree`), and
  `width_le`, `zero_r_word`, `zero_J_le` are the generic bounds for these data.
-/

set_option autoImplicit false

namespace SparseHamiltonian.GateRemarks.ODE

noncomputable section
open GateCircuit GateNative
open SparseHamiltonian.GateBinary SparseHamiltonian.GateBinaryODE
open SparseHamiltonian.GateBitBudget (bitB HasBits)
open GateODEBudget (qOf words)
open ImprovedODEQueryBudget (precision logBudget radius)
open ZeroTimeGateODE (BPublicOK0 BZeroCase)
open CayleyClockInterface (width moment)

/-! ### The envelope `X = (Q g + 1)/ε` -/

section Envelope

variable {Q g ε : ℝ}

/-- `1 ≤ X = (Q g + 1)/ε` for `Q, g ≥ 1` and `0 < ε ≤ 1`. -/
theorem env_one_le (hQ : 1 ≤ Q) (hg : 1 ≤ g) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    1 ≤ (Q * g + 1) / ε := by
  rw [le_div_iff₀ hε]
  nlinarith

/-- `Q ≤ X = (Q g + 1)/ε` for `Q, g ≥ 1` and `0 < ε ≤ 1`. -/
theorem env_q_le (hQ : 1 ≤ Q) (hg : 1 ≤ g) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Q ≤ (Q * g + 1) / ε := by
  rw [le_div_iff₀ hε]
  nlinarith

/-- `g/ε ≤ X = (Q g + 1)/ε` for `Q, g ≥ 1` and `ε > 0`. -/
theorem env_div_le (hQ : 1 ≤ Q) (hg : 1 ≤ g) (hε : 0 < ε) : g / ε ≤ (Q * g + 1) / ε :=
  div_le_div_of_nonneg_right (by nlinarith) hε.le

/-- `1/ν = 10⁴ g/ε ≤ 10⁴ X`. -/
theorem env_inv_precision_le (hQ : 1 ≤ Q) (hg : 1 ≤ g) (hε : 0 < ε) :
    1 / precision g ε ≤ 10000 * ((Q * g + 1) / ε) := by
  have hg0 : 0 < g := by linarith
  have e : 1 / precision g ε = 10000 * (g / ε) := by
    unfold ImprovedODEQueryBudget.precision
    field_simp
  rw [e]
  have := env_div_le hQ hg hε
  linarith

/-- `ℓ = log(10⁴ g/ε) ≤ 10⁴ X`. -/
theorem env_ell_le (hQ : 1 ≤ Q) (hg : 1 ≤ g) (hε : 0 < ε) :
    logBudget g ε ≤ 10000 * ((Q * g + 1) / ε) := by
  have hg0 : 0 < g := by linarith
  have h1 := Real.log_le_sub_one_of_pos (by positivity : 0 < 10000 * g / ε)
  have e : 10000 * g / ε = 10000 * (g / ε) := by ring
  have := env_div_le hQ hg hε
  unfold ImprovedODEQueryBudget.logBudget
  rw [e] at h1 ⊢
  linarith

/-- `ℓ = log(10⁴ g/ε) ≤ 14 + log₂ X`. -/
theorem env_ell_le_logb (hQ : 1 ≤ Q) (hg : 1 ≤ g) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    logBudget g ε ≤ 14 + Real.logb 2 ((Q * g + 1) / ε) := by
  have hg0 : 0 < g := by linarith
  have harg : 1 ≤ 10000 * g / ε := by
    rw [le_div_iff₀ hε]
    nlinarith
  have h1 := GateBitBudget.log_le_logb _ harg
  have h2 := GateBitBudget.logb_le_mul_pow (10000 * g / ε) 10000 _ 14 1 (by positivity)
    (env_one_le hQ hg hε hε1) (by norm_num) (by
      have := env_div_le hQ hg hε
      rw [pow_one, mul_div_assoc]
      linarith)
  unfold ImprovedODEQueryBudget.logBudget
  push_cast at h2
  linarith

/-- `1 + R ≤ 2^17 X` for the LCHS radius `R = 4 log(2·10⁴ g/ε)` and `X = (Q g + 1)/ε`. -/
theorem env_radius_le (hQ : 1 ≤ Q) (hg : 1 ≤ g) (hε : 0 < ε) :
    1 + radius g ε ≤ 2 ^ 17 * ((Q * g + 1) / ε) := by
  have hg0 : 0 < g := by linarith
  have h3 := Real.log_le_sub_one_of_pos (by positivity : 0 < 20000 * g / ε)
  have h4 := env_div_le hQ hg hε
  have h5 : 0 < g / ε := by positivity
  have e : 20000 * g / ε = 20000 * (g / ε) := by ring
  unfold ImprovedODEQueryBudget.radius
  rw [e] at h3 ⊢
  rw [show (2 : ℝ) ^ 17 = 131072 by norm_num]
  linarith

end Envelope

/-! ### The words of a simulator at zero common time -/

section Generic

/-- **The clock width**: `width(4s, γ) ≤ 3 · 2^k_x` for `γ ≤ 1` and `1 ≤ s ≤ 2^k_x`. -/
theorem width_le_of {s kx : ℕ} {γ : ℝ} (hγ1 : γ ≤ 1) (hs1 : 1 ≤ s) (hskx : s ≤ 2 ^ kx) :
    width (4 * (s : ℝ)) γ ≤ 3 * 2 ^ kx := by
  have hs1' : (1 : ℝ) ≤ s := by exact_mod_cast hs1
  have hsk : (s : ℝ) ≤ 2 ^ kx := by exact_mod_cast hskx
  have hsq : Real.sqrt (4 * (s : ℝ)) ≤ 2 * 2 ^ kx := by
    rw [GateODEBudget.sqrt_four_mul]
    have := GateBitBudget.sqrt_le_self_of_one_le hs1'
    linarith
  have h1 : (1 : ℝ) ≤ 2 ^ kx := one_le_pow₀ (by norm_num)
  have hγs : γ * Real.sqrt (4 * (s : ℝ)) ≤ 2 * 2 ^ kx := by
    have := mul_le_mul hγ1 hsq (Real.sqrt_nonneg _) zero_le_one
    linarith
  have hm : max 1 (γ * Real.sqrt (4 * (s : ℝ))) ≤ 2 * 2 ^ kx := max_le (by linarith) hγs
  have hc := Nat.ceil_lt_add_one (le_trans zero_le_one
    (le_max_left 1 (γ * Real.sqrt (4 * (s : ℝ)))))
  unfold width
  linarith

/-- **The reuse word at zero common time**: for a filter degree `d ≤ 128 Q_w (1 + log(3/ν))`,
`ν = precision g ε`, a clock width `Q_w ≤ 3 · 2^k_x` and `2^r ≤ 4 (d + 1)`:
`r ≤ 24 + k_x + log₂ X`, `X = (Q g + 1)/ε`, for every `Q ≥ 1`. -/
theorem r_word_of {d r kx : ℕ} {Qw g ε Q : ℝ} (hg : 1 ≤ g) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hQ : 1 ≤ Q) (hd : (d : ℝ) ≤ 128 * (Qw * (1 + Real.log (3 / precision g ε))))
    (hw : Qw ≤ 3 * 2 ^ kx) (hr : 2 ^ r ≤ 4 * (d + 1)) :
    (r : ℝ) ≤ 24 + kx + Real.logb 2 ((Q * g + 1) / ε) := by
  have hX := env_one_le hQ hg hε hε1
  have hℓX := env_ell_le hQ hg hε
  have hr' : ((2 ^ r : ℕ) : ℝ) ≤ 4 * ((d : ℝ) + 1) := by exact_mod_cast hr
  have hν : 0 < precision g ε := ImprovedODEQueryBudget.precision_pos g ε hg hε
  have hν1 : precision g ε ≤ 1 / 10000 :=
    ImprovedODEQueryBudget.precision_le_one_ten_thousandth g ε hg hε1
  have hlog3 : Real.log (3 / precision g ε) ≤ 2 + logBudget g ε := by
    have hg0 : 0 < g := by linarith
    have e : 3 / precision g ε = 3 * (10000 * g / ε) := by
      unfold ImprovedODEQueryBudget.precision
      field_simp
    have hpos : 0 < 10000 * g / ε := by positivity
    rw [e, Real.log_mul (by norm_num) hpos.ne']
    have h3 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    unfold ImprovedODEQueryBudget.logBudget
    linarith
  have hk0 : (0 : ℝ) ≤ 1 + Real.log (3 / precision g ε) := by
    have : 1 ≤ 3 / precision g ε := by
      rw [le_div_iff₀ hν]
      linarith
    have := Real.log_nonneg this
    linarith
  have h2k : (1 : ℝ) ≤ 2 ^ kx := one_le_pow₀ (by norm_num)
  have h1 : (d : ℝ) ≤ 128 * (3 * 2 ^ kx * (10003 * ((Q * g + 1) / ε))) := by
    refine hd.trans ?_
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact mul_le_mul hw (by linarith) hk0 (by positivity)
  have h2 : ((2 ^ r : ℕ) : ℝ) ≤ (2 ^ (24 + kx) : ℝ) * ((Q * g + 1) / ε) ^ 1 := by
    rw [pow_one, pow_add]
    have : (4 : ℝ) * (128 * (3 * 2 ^ kx * (10003 * ((Q * g + 1) / ε))) + 1) ≤
        2 ^ 24 * 2 ^ kx * ((Q * g + 1) / ε) := by
      have h3 : (1 : ℝ) ≤ 2 ^ kx * ((Q * g + 1) / ε) := one_le_mul_of_one_le_of_one_le h2k hX
      nlinarith
    linarith
  have h4 := GateBitBudget.nat_le_mul_pow r (2 ^ (24 + kx)) _ (24 + kx) 1 hX le_rfl h2
  push_cast at h4
  linarith

/-- **The LCHS grid at zero dissipative time**: if `J ≤ R (2 log(512/ν))/π + 3`
(`R = radius g ε`, `ν = precision g ε`), then `J ≤ 60 Q ℓ` for every `Q ≥ ℓ = log(10⁴ g/ε)`. -/
theorem J_le_of {J : ℕ} {g ε Q : ℝ} (hg : 1 ≤ g) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hJ : (J : ℝ) ≤ radius g ε * (2 * Real.log (512 / precision g ε)) / Real.pi + 3)
    (hQ : logBudget g ε ≤ Q) : (J : ℝ) ≤ 60 * Q * logBudget g ε := by
  have hg0 : 0 < g := by linarith
  have hℓ := ImprovedODEQueryBudget.logBudget_ge_one g ε hg hε hε1
  have hR : radius g ε ≤ 4 * logBudget g ε + 3 := by
    have e : 20000 * g / ε = 2 * (10000 * g / ε) := by ring
    have hpos : 0 < 10000 * g / ε := by positivity
    unfold ImprovedODEQueryBudget.radius ImprovedODEQueryBudget.logBudget
    rw [e, Real.log_mul (by norm_num) hpos.ne']
    have := Real.log_two_lt_d9
    norm_num at this
    linarith
  have hR0 : 0 ≤ radius g ε := ImprovedODEQueryBudget.radius_nonneg g ε hg hε hε1
  have h512 : Real.log (512 / precision g ε) ≤ 8 + logBudget g ε := by
    have e : 512 / precision g ε = 512 * (10000 * g / ε) := by
      unfold ImprovedODEQueryBudget.precision
      field_simp
    have hpos : 0 < 10000 * g / ε := by positivity
    rw [e, Real.log_mul (by norm_num) hpos.ne']
    have h2 : Real.log 512 = 9 * Real.log 2 := by
      rw [show (512 : ℝ) = 2 ^ 9 by norm_num, Real.log_pow]
      norm_num
    have h3 := Real.log_two_lt_d9
    unfold ImprovedODEQueryBudget.logBudget
    rw [h2]
    norm_num at h3 ⊢
    linarith
  have h512' : 0 ≤ Real.log (512 / precision g ε) := by
    apply Real.log_nonneg
    have hν1 := ImprovedODEQueryBudget.precision_le_one_ten_thousandth g ε hg hε1
    have hν := ImprovedODEQueryBudget.precision_pos g ε hg hε
    rw [le_div_iff₀ hν]
    linarith
  have hpi := Real.pi_gt_three
  have h1 : radius g ε * (2 * Real.log (512 / precision g ε)) ≤
      (4 * logBudget g ε + 3) * (2 * (8 + logBudget g ε)) :=
    mul_le_mul hR (by linarith) (by linarith) (by linarith)
  have h2 : radius g ε * (2 * Real.log (512 / precision g ε)) / Real.pi ≤
      (4 * logBudget g ε + 3) * (2 * (8 + logBudget g ε)) / 3 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    have h0 : 0 ≤ radius g ε * (2 * Real.log (512 / precision g ε)) := by positivity
    nlinarith
  have h3 : 60 * logBudget g ε * logBudget g ε ≤ 60 * Q * logBudget g ε := by
    have := mul_le_mul_of_nonneg_right hQ (by linarith : (0 : ℝ) ≤ logBudget g ε)
    linarith
  nlinarith

/-- **The decoder words for a rescaling of bit length `b_data`**: for
`κ = γ √(4s) c₀ / (2^e (η_H + R η_D))` with `0 < γ ≤ 1` of bit length `b_data`, `1 ≤ s ≤ 2^k_x`,
`c₀ > 0`, `η_H, η_D ≥ 0` of bit length `b_data`, `R ≥ 1`, `1 + R ≤ 2^17 X` and `X ≥ 1`:
`⌈log₂ ⌈κ⌉⌉ ≤ 1 + k_x + 2 b_data` and `⌈log₂ ⌈1/κ⌉⌉ ≤ e + 17 + 3 b_data + log₂ X` (`κ = 0` for
zero energy bounds). -/
theorem kap_words_of (bd kx e s : ℕ) {γ c0 ηH ηD R X κ : ℝ}
    (hκ : κ = γ * Real.sqrt (4 * (s : ℝ)) * c0 / (2 ^ e * (ηH + R * ηD)))
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hγb : HasBits bd γ) (hs1 : 1 ≤ s) (hskx : s ≤ 2 ^ kx)
    (hc0 : HasBits bd c0) (hc0p : 0 < c0) (hH : HasBits bd ηH) (hD : HasBits bd ηD)
    (hH0 : 0 ≤ ηH) (hD0 : 0 ≤ ηD) (hR1 : 1 ≤ R) (hRX : 1 + R ≤ 2 ^ 17 * X) (hX : 1 ≤ X) :
    (Nat.clog 2 ⌈κ⌉₊ : ℝ) ≤ 1 + kx + 2 * bd ∧
    (Nat.clog 2 ⌈1 / κ⌉₊ : ℝ) ≤ e + 17 + 3 * bd + Real.logb 2 X := by
  have hL0 := Real.logb_nonneg one_lt_two hX
  rcases eq_or_lt_of_le (add_nonneg hH0 hD0) with h0 | hpos
  · -- zero energy bounds: `κ = 0`
    have hH0' : ηH = 0 := by linarith
    have hD0' : ηD = 0 := by linarith
    have hk0 : κ = 0 := by
      rw [hκ, hH0', hD0']
      simp
    rw [hk0, div_zero]
    simp only [Nat.ceil_zero, Nat.clog_zero_right, Nat.cast_zero]
    constructor <;> positivity
  · have hρ1 : 1 ≤ 2 ^ bd * (ηH + R * ηD) :=
      GateBitBudget.one_le_mul_rho bd hH hD hH0 hD0 hpos hR1
    have hρ0 : 0 < ηH + R * ηD := by
      by_contra hn
      have hn' : ηH + R * ηD ≤ 0 := le_of_not_gt hn
      have : (2 : ℝ) ^ bd * (ηH + R * ηD) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) hn'
      linarith
    have h1 := GateBitBudget.kap_le bd kx e s hγ1 hs1 hskx hc0 hc0p hρ0 hρ1
    rw [← hκ] at h1
    have w1 := GateBitBudget.clog_ceil_le_nat κ (1 + kx + 2 * bd) h1
    have h2 := GateBitBudget.kap_inv_le bd e s hγ0 hs1 hc0 hc0p hρ0
    rw [← hκ] at h2
    have hρle : ηH + R * ηD ≤ (1 + R) * 2 ^ bd :=
      GateBitBudget.rho_le bd hH hD (le_trans zero_le_one hR1)
    have hγinv : γ⁻¹ ≤ 2 ^ bd := by
      have h := hγb.one_le_mul hγ0
      rw [inv_le_iff_one_le_mul₀ hγ0]
      linarith
    have hpow : (0 : ℝ) < 2 ^ e := by positivity
    have h3 : κ⁻¹ ≤ (2 : ℝ) ^ (e + 3 * bd + 16) * X ^ 1 := by
      refine h2.trans ?_
      have hb0 : (0 : ℝ) < 2 ^ bd := by positivity
      have ee : (2 : ℝ) ^ (e + 3 * bd + 16) =
          2 ^ e * (2 ^ bd * 2 ^ bd * 2 ^ bd) * 2 ^ 17 / 2 := by
        rw [show e + 3 * bd + 16 = e + (bd + bd + bd) + 16 by ring, pow_add, pow_add, pow_add,
          pow_add]
        ring
      rw [ee, pow_one]
      have h5 : (ηH + R * ηD) * γ⁻¹ ≤ (1 + R) * 2 ^ bd * 2 ^ bd :=
        mul_le_mul hρle hγinv (inv_nonneg.mpr hγ0.le) (by positivity)
      have h6 : (1 + R) * 2 ^ bd * 2 ^ bd ≤ 2 ^ 17 * X * 2 ^ bd * 2 ^ bd := by
        have := mul_le_mul_of_nonneg_right hRX (by positivity : (0 : ℝ) ≤ 2 ^ bd * 2 ^ bd)
        linarith
      have h7 : 2 ^ e * (ηH + R * ηD) * γ⁻¹ * 2 ^ bd / 2 =
          2 ^ e * ((ηH + R * ηD) * γ⁻¹) * 2 ^ bd / 2 := by ring
      rw [h7]
      have h8 : 2 ^ e * ((ηH + R * ηD) * γ⁻¹) * 2 ^ bd / 2 ≤
          2 ^ e * (2 ^ 17 * X * 2 ^ bd * 2 ^ bd) * 2 ^ bd / 2 := by
        apply div_le_div_of_nonneg_right _ (by norm_num)
        apply mul_le_mul_of_nonneg_right _ hb0.le
        exact mul_le_mul_of_nonneg_left (h5.trans h6) hpow.le
      refine h8.trans (le_of_eq ?_)
      ring
    have w2 := GateBitBudget.clog_le_mul_pow (1 / κ) _ X (e + 3 * bd + 16) 1 hX le_rfl
      (by rw [one_div]; exact h3)
    constructor
    · have : ((Nat.clog 2 ⌈κ⌉₊ : ℕ) : ℝ) ≤ ((1 + kx + 2 * bd : ℕ) : ℝ) := by
        exact_mod_cast w1
      push_cast at this
      linarith
    · push_cast at w2
      linarith

/-- **The rescaling `γ = 1` has every bit length `b_data ≥ 1`**: with `1 ≤ b ≤ b_data` the
zero-case hypothesis `HasBits b_data γ` is met by the public choice `γ = 1`. -/
theorem hasBits_one {bd : ℕ} (h : 1 ≤ bd) : HasBits bd 1 := by
  have h1 := GateBitBudget.hasBits_int 1 1 (by norm_num)
  simpa using h1.mono h

end Generic

/-! ### The zero case of the constant-coefficient public data -/

section Zero

variable (q : Pub)

/-- In the zero case `T λ_D = 0`. -/
theorem zero_TlamD (hq : BPublicOK0 q) (hz : BZeroCase q) : q.params.T * q.params.lamD = 0 := by
  rcases hz with h | h
  · show q.T * _ = 0
    rw [h, zero_mul]
  · have hD : q.etaD = 0 := by linarith [hq.etaH_nonneg, hq.etaD_nonneg]
    show q.T * (Real.sqrt (4 * (q.s : ℝ)) * q.etaD / q.γ) = 0
    rw [hD, mul_zero, zero_div, mul_zero]

/-- In the zero case `T (λ_H + λ_D) = 0`. -/
theorem zero_TlamHD (hq : BPublicOK0 q) (hz : BZeroCase q) :
    q.params.T * (q.params.lamH + q.params.lamD) = 0 := by
  rcases hz with h | h
  · show q.T * _ = 0
    rw [h, zero_mul]
  · have hH : q.etaH = 0 := by linarith [hq.etaH_nonneg, hq.etaD_nonneg]
    have hD : q.etaD = 0 := by linarith [hq.etaH_nonneg, hq.etaD_nonneg]
    show q.T * (Real.sqrt (4 * (q.s : ℝ)) * q.etaH / q.γ +
      Real.sqrt (4 * (q.s : ℝ)) * q.etaD / q.γ) = 0
    rw [hH, hD]
    simp

/-- In the zero case the common simulation time `τ = T (λ_H + R λ_D)` vanishes. -/
theorem zero_tau (hq : BPublicOK0 q) (hz : BZeroCase q) : q.params.tau = 0 := by
  rcases hz with h | h
  · show q.T * _ = 0
    rw [h, zero_mul]
  · have hH : q.etaH = 0 := by linarith [hq.etaH_nonneg, hq.etaD_nonneg]
    have hD : q.etaD = 0 := by linarith [hq.etaH_nonneg, hq.etaD_nonneg]
    show q.T * (Real.sqrt (4 * (q.s : ℝ)) * q.etaH / q.γ +
      q.params.R * (Real.sqrt (4 * (q.s : ℝ)) * q.etaD / q.γ)) = 0
    rw [hH, hD]
    simp

/-- In the zero case the time word of the released simulator vanishes: `m = 0`. -/
theorem zero_m (hq : BPublicOK0 q) (hz : BZeroCase q) : q.params.m = 0 := by
  obtain ⟨-, h2, -⟩ := q.params.sim_sizes
  have hs : TimeSchedule.steps q.params.tau (q.params.nu / 3) = 1 := by
    simp [TimeSchedule.steps, TimeSchedule.threshold, zero_tau q hq hz]
  rw [hs] at h2
  rcases Nat.eq_zero_or_pos q.params.m with h0 | h0
  · exact h0
  · have : 2 ≤ 2 ^ q.params.m := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ q.params.m := Nat.pow_le_pow_right (by norm_num) h0
    omega

/-- In the zero case the quadrature word vanishes: `k = 0`. -/
theorem zero_k (hq : BPublicOK0 q) (hz : BZeroCase q) : q.params.k = 0 := by
  show Nat.clog 2 ⌈q.params.T * (q.params.lamH + q.params.lamD) / q.params.nu⌉₊ = 0
  rw [zero_TlamHD q hq hz]
  simp

/-- **The filter degree in the zero case**: `d ≤ 128 Q_w (1 + log(3/ν))`, `Q_w = width(4s, γ)`. -/
theorem zero_degree (hq : BPublicOK0 q) (hz : BZeroCase q) :
    (q.params.d : ℝ) ≤ 128 * (q.params.Q * (1 + Real.log (3 / q.params.nu))) := by
  have hν : 0 < q.params.nu :=
    ImprovedODEQueryBudget.precision_pos q.g q.ε hq.g_ge hq.ε_pos
  have hν1 : q.params.nu ≤ 1 / 10000 :=
    ImprovedODEQueryBudget.precision_le_one_ten_thousandth q.g q.ε hq.g_ge
      (hq.ε_half.trans (by norm_num))
  have hτ := zero_tau q hq hz
  have h := SharpFilterSchedule.degree_le q.params.Q (q.params.tau * q.params.qbar)
    (q.params.nu / 3) (CayleyClockInterface.width_ge_one _ _) (by rw [hτ, zero_mul])
    (by positivity) (by linarith)
  have e1 : (q.params.d : ℝ) =
      (SharpFilterSchedule.degree q.params.Q (q.params.tau * q.params.qbar) (q.params.nu / 3) :
        ℝ) := rfl
  have e2 : Real.log (3 / q.params.nu) = SharpFilterSchedule.logBudget (q.params.nu / 3) := by
    unfold SharpFilterSchedule.logBudget
    rw [one_div_div]
  rw [e1, e2]
  refine h.trans (le_of_eq ?_)
  rw [hτ, zero_mul, zero_add]

/-- **The clock width**: `Q_w = width(4s, γ) ≤ 3 · 2^k_x` (`width_le_of`). -/
theorem width_le (hq : BPublicOK0 q) : q.params.Q ≤ 3 * 2 ^ q.kx := by
  show width (4 * (q.s : ℝ)) q.γ ≤ 3 * 2 ^ q.kx
  exact width_le_of hq.γ_le Nat.one_le_two_pow (Nat.pow_le_pow_right (by norm_num) q.hσ)

/-- **The reuse word in the zero case**: `r ≤ 24 + k_x + log₂ X`, `X = (Q g + 1)/ε`, `Q ≥ 1`. -/
theorem zero_r_word (hq : BPublicOK0 q) (hz : BZeroCase q) {Q : ℝ} (hQ : 1 ≤ Q) :
    (q.params.r : ℝ) ≤ 24 + q.kx + Real.logb 2 ((Q * q.g + 1) / q.ε) := by
  obtain ⟨-, -, -, hr⟩ := q.params.sim_sizes
  exact r_word_of (g := q.g) (ε := q.ε) hq.g_ge hq.ε_pos (hq.ε_half.trans (by norm_num)) hQ
    (zero_degree q hq hz) (width_le q hq) hr

/-- **The LCHS grid in the zero case**: `J ≤ 60 Q ℓ` for every `Q ≥ ℓ` (in particular for
`q* = ℓ`). -/
theorem zero_J_le (hq : BPublicOK0 q) (hz : BZeroCase q) {Q : ℝ} (hQ : logBudget q.g q.ε ≤ Q) :
    (q.params.J : ℝ) ≤ 60 * Q * logBudget q.g q.ε := by
  have hε1 : q.ε ≤ 1 := hq.ε_half.trans (by norm_num)
  have hJ := GateODE.AnalyticLCHS.gridSize_le (le_of_eq (zero_TlamD q hq hz).symm) hq.g_ge
    hq.ε_pos hε1
  change (q.params.J : ℝ) ≤ radius q.g q.ε *
    (q.params.T * q.params.lamD + 2 * Real.log (512 / precision q.g q.ε)) / Real.pi + 3 at hJ
  rw [zero_TlamD q hq hz, zero_add] at hJ
  exact J_le_of hq.g_ge hq.ε_pos hε1 hJ hQ

end Zero

end

end SparseHamiltonian.GateRemarks.ODE
