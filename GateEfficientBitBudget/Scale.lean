import GateEfficientBitBudget.Bits
import GateEfficientODEBudget.Shape
import GateEfficientBinaryODE.Clock

/-!
# The public scales from the bit lengths of the public parameters

For equations `ode:eq:gate-main` and `ode:eq:gate-space` in the word budget `𝔟` of equation
`ode:eq:gate-word-budget` (Theorem `ode:thm:gates`): the register words of the dissipative
solvers from binary data that are not bounded by the released size lemmas are the fractional bits
`F` of the LCHS step, the CORDIC steps and the bits of the decoder scale
`κ = γ √(4s) c₀ / (2^e ρ)`, with `ρ = η_H + R η_D` (`R` the LCHS radius) and the public rescaling
`γ = gammaOf T η_H η_D g ε = min(1, √(Θ/ℓ))`, `Θ = T η_H + T η_D ℓ`. This file bounds the public
scales behind them from the bit lengths of `c₀`, `T`, `η_H` and `η_D` (`HasBits`):

* `one_le_mul_eta`: `1 ≤ 2^bd (η_H + η_D)`; `one_le_mul_theta`: `1 ≤ 2^bd 2^bd Θ`;
* `gam_inv_le`: `γ⁻¹ ≤ 1 + ℓ/Θ`; `gammaOf_inv_le`: `γ⁻¹ ≤ 2 ℓ 2^bd 2^bd` for the public
  rescaling (no hypothesis on `γ` besides its public choice); `logb_inv_gammaOf_le`:
  `log₂(1/γ) ≤ 2 bd + 1 + log₂ ℓ`;
* `one_le_radius`: `R ≥ 1` (from the released `R ≥ 4`); `rho_le`: `ρ ≤ (1 + R) 2^bd`;
  `one_le_mul_rho`: `1 ≤ 2^bd ρ`;
* `step_inv_le`: the step `h = R/K` of the analytic LCHS grid has `h⁻¹ ≤ J = 2K + 1`;
  `four_div_step_le`: `4/(ζ h) ≤ 4 J/ζ` (the argument of the fractional bits `F = fOf p ζ`);
* `kap_le`: `κ ≤ 2^(1 + k_x + 2 bd)` for `1 ≤ s ≤ 2^k_x` (with `sqrt_le_self_of_one_le`:
  `√s ≤ s` for `s ≥ 1`); `kap_inv_le`: `κ⁻¹ ≤ 2^e ρ γ⁻¹ 2^bd / 2`.

In the paper the rescaling has the floor `γ ≥ p^(-1/2)`, which bounds `log(1/γ)` by
`log(2s)/2`; the released rescaling has no floor, and `gammaOf_inv_le` replaces it by the bit
lengths of `T`, `η_H` and `η_D`.
-/

set_option autoImplicit false

namespace SparseHamiltonian.GateBitBudget

noncomputable section
open GateODEBudget (gam gammaOf thetaOf qOf ShapeOK gam_cases)
open ImprovedODEQueryBudget (precision logBudget radius)

/-! ### The energy bounds, the time budget and the rescaling -/

/-- **The energy scale**: `1 ≤ 2^bd (η_H + η_D)` for nonnegative `η_H`, `η_D` of bit length `bd`
with a positive sum. -/
theorem one_le_mul_eta (bd : ℕ) {ηH ηD : ℝ} (hH : HasBits bd ηH) (hD : HasBits bd ηD)
    (hH0 : 0 ≤ ηH) (hD0 : 0 ≤ ηD) (hpos : 0 < ηH + ηD) : 1 ≤ 2 ^ bd * (ηH + ηD) := by
  have h2 : (0 : ℝ) ≤ 2 ^ bd := by positivity
  rcases lt_or_eq_of_le hH0 with h | h
  · have h1 := hH.one_le_mul h
    nlinarith
  · have hD' : 0 < ηD := by
      rw [← h] at hpos
      linarith
    have h1 := hD.one_le_mul hD'
    nlinarith

/-- **The time budget is not too small**: `1 ≤ 2^bd 2^bd Θ` for `Θ = T η_H + T η_D ℓ`, from the
bit lengths of `T`, `η_H` and `η_D`. -/
theorem one_le_mul_theta (bd : ℕ) {s T ηH ηD g ε : ℝ} (h : ShapeOK s T ηH ηD g ε)
    (hT : HasBits bd T) (hH : HasBits bd ηH) (hD : HasBits bd ηD) :
    1 ≤ 2 ^ bd * 2 ^ bd * thetaOf T ηH ηD g ε := by
  have h1 := hT.one_le_mul h.T_pos
  have h2 := one_le_mul_eta bd hH hD h.etaH_nonneg h.etaD_nonneg h.eta_pos
  have h3 := h.sum_le_theta
  have h4 : 1 ≤ (2 ^ bd * T) * (2 ^ bd * (ηH + ηD)) := one_le_mul_of_one_le_of_one_le h1 h2
  have h5 : (2 ^ bd * T) * (2 ^ bd * (ηH + ηD)) = 2 ^ bd * 2 ^ bd * (T * ηH + T * ηD) := by
    ring
  have h6 : 2 ^ bd * 2 ^ bd * (T * ηH + T * ηD) ≤ 2 ^ bd * 2 ^ bd * thetaOf T ηH ηD g ε :=
    mul_le_mul_of_nonneg_left h3 (by positivity)
  linarith

/-- `γ⁻¹ ≤ 1 + ℓ/Θ` for the rescaling `γ = min(1, √(Θ/ℓ))`. -/
theorem gam_inv_le {Θ ℓ : ℝ} (hΘ : 0 < Θ) (hℓ : 0 < ℓ) : (gam Θ ℓ)⁻¹ ≤ 1 + ℓ / Θ := by
  rcases gam_cases (Θ := Θ) hℓ with ⟨-, h1⟩ | ⟨hlt, h2⟩
  · rw [h1, inv_one]
    have := div_nonneg hℓ.le hΘ.le
    linarith
  · rw [h2, inv_div]
    have hsq : (Real.sqrt ℓ / Real.sqrt Θ) ^ 2 = ℓ / Θ := by
      rw [div_pow, Real.sq_sqrt hℓ.le, Real.sq_sqrt hΘ.le]
    have hu1 : 1 ≤ Real.sqrt ℓ / Real.sqrt Θ := by
      rw [one_le_div (Real.sqrt_pos.mpr hΘ)]
      exact Real.sqrt_le_sqrt hlt.le
    nlinarith

/-- **The public rescaling is not too small**: `γ⁻¹ ≤ 2 ℓ 2^bd 2^bd` for
`γ = gammaOf T η_H η_D g ε`, from the bit lengths of `T`, `η_H` and `η_D`. -/
theorem gammaOf_inv_le (bd : ℕ) {s T ηH ηD g ε : ℝ} (h : ShapeOK s T ηH ηD g ε)
    (hT : HasBits bd T) (hH : HasBits bd ηH) (hD : HasBits bd ηD) :
    (gammaOf T ηH ηD g ε)⁻¹ ≤ 2 * logBudget g ε * (2 ^ bd * 2 ^ bd) := by
  have hΘ := h.theta_pos
  have hℓ := h.ell_ge
  have h1 := gam_inv_le hΘ (lt_of_lt_of_le one_pos hℓ)
  have h2 := one_le_mul_theta bd h hT hH hD
  have h3 : logBudget g ε / thetaOf T ηH ηD g ε ≤ logBudget g ε * (2 ^ bd * 2 ^ bd) := by
    rw [div_le_iff₀ hΘ]
    have h4 : logBudget g ε * 1 ≤ logBudget g ε * (2 ^ bd * 2 ^ bd * thetaOf T ηH ηD g ε) :=
      mul_le_mul_of_nonneg_left h2 (by linarith)
    have e : logBudget g ε * (2 ^ bd * 2 ^ bd) * thetaOf T ηH ηD g ε =
        logBudget g ε * (2 ^ bd * 2 ^ bd * thetaOf T ηH ηD g ε) := by ring
    rw [e]
    linarith
  have h4 : (1 : ℝ) ≤ 2 ^ bd * 2 ^ bd :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (one_le_pow₀ (by norm_num))
  have h5 : 1 ≤ logBudget g ε * (2 ^ bd * 2 ^ bd) := one_le_mul_of_one_le_of_one_le hℓ h4
  change (gam (thetaOf T ηH ηD g ε) (logBudget g ε))⁻¹ ≤ _
  linarith

/-- **The logarithm of the public rescaling**: `log₂(1/γ) ≤ 2 bd + 1 + log₂ ℓ` for
`γ = gammaOf T η_H η_D g ε`, `ℓ = log(10000 g/ε)`, from the bit lengths of `T`, `η_H` and `η_D`
(in the paper the floor `γ ≥ p^(-1/2)` gives `log(1/γ) ≤ log(2s)/2` instead). -/
theorem logb_inv_gammaOf_le (bd : ℕ) {s T ηH ηD g ε : ℝ} (h : ShapeOK s T ηH ηD g ε)
    (hT : HasBits bd T) (hH : HasBits bd ηH) (hD : HasBits bd ηD) :
    Real.logb 2 (gammaOf T ηH ηD g ε)⁻¹ ≤ 2 * bd + 1 + Real.logb 2 (logBudget g ε) := by
  have hγ := h.gammaOf_pos
  have hℓ := h.ell_ge
  have h1 := gammaOf_inv_le bd h hT hH hD
  have h2 : Real.logb 2 (gammaOf T ηH ηD g ε)⁻¹ ≤
      Real.logb 2 (2 * logBudget g ε * (2 ^ bd * 2 ^ bd)) :=
    Real.logb_le_logb_of_le one_lt_two (inv_pos.mpr hγ) h1
  have e : Real.logb 2 (2 * logBudget g ε * (2 ^ bd * 2 ^ bd)) =
      1 + Real.logb 2 (logBudget g ε) + (bd + bd) := by
    rw [Real.logb_mul (by positivity) (by positivity),
      Real.logb_mul (by norm_num) (by linarith), Real.logb_mul (by positivity) (by positivity),
      Real.logb_pow, Real.logb_self_eq_one one_lt_two]
    ring
  rw [e] at h2
  linarith

/-! ### The LCHS radius, the scale of the sectors and the LCHS step -/

/-- **The LCHS radius is at least one**: `R = 4 log(20000 g/ε) ≥ 1`, from the released bound
`R ≥ 4` (`ODEGaussianParameters.radius_ge_four`). -/
theorem one_le_radius {g ε : ℝ} (hg : 1 ≤ g) (hε : 0 < ε) (hε1 : ε ≤ 1) : 1 ≤ radius g ε :=
  le_trans (by norm_num) (ODEGaussianParameters.radius_ge_four g ε hg hε hε1)

/-- **The scale of the sectors is not too large**: `η_H + R η_D ≤ (1 + R) 2^bd`. -/
theorem rho_le (bd : ℕ) {ηH ηD R : ℝ} (hH : HasBits bd ηH) (hD : HasBits bd ηD) (hR : 0 ≤ R) :
    ηH + R * ηD ≤ (1 + R) * 2 ^ bd := by
  have h1 := hH.lt
  have h3 : R * ηD ≤ R * 2 ^ bd := mul_le_mul_of_nonneg_left hD.lt.le hR
  have e : (1 + R) * (2 : ℝ) ^ bd = 2 ^ bd + R * 2 ^ bd := by ring
  rw [e]
  linarith

/-- **The scale of the sectors is not too small**: `1 ≤ 2^bd (η_H + R η_D)` for `R ≥ 1`. -/
theorem one_le_mul_rho (bd : ℕ) {ηH ηD R : ℝ} (hH : HasBits bd ηH) (hD : HasBits bd ηD)
    (hH0 : 0 ≤ ηH) (hD0 : 0 ≤ ηD) (hpos : 0 < ηH + ηD) (hR : 1 ≤ R) :
    1 ≤ 2 ^ bd * (ηH + R * ηD) := by
  have h1 := one_le_mul_eta bd hH hD hH0 hD0 hpos
  have h2 : ηD ≤ R * ηD := le_mul_of_one_le_left hD0 hR
  have h3 : (2 : ℝ) ^ bd * (ηH + ηD) ≤ 2 ^ bd * (ηH + R * ηD) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  linarith

/-- **The LCHS step is not too small**: `h⁻¹ ≤ J` for the step `h = R/K` and the size
`J = 2K + 1` of the analytic LCHS grid. -/
theorem step_inv_le {D g ε : ℝ} (hD : 0 ≤ D) (hg : 1 ≤ g) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (GateODE.AnalyticLCHS.step D g ε)⁻¹ ≤ GateODE.AnalyticLCHS.gridSize D g ε := by
  have hK := GateODE.AnalyticLCHS.halfCount_pos hD hg hε hε1
  have hR := one_le_radius hg hε hε1
  have hK' : (0 : ℝ) < GateODE.AnalyticLCHS.halfCount D g ε := by exact_mod_cast hK
  unfold GateODE.AnalyticLCHS.step GateODE.AnalyticLCHS.gridSize
  rw [inv_div, div_le_iff₀ (by linarith)]
  push_cast
  nlinarith

/-- **The argument of the fractional bits of the LCHS step**: `4/(ζ h) ≤ 4 J/ζ`, so that
`F = fOf p ζ = ⌈log₂ ⌈4/(ζ h)⌉⌉` is logarithmic in `J/ζ`. -/
theorem four_div_step_le (p : GateODE.Params) (hg : 1 ≤ p.g) (hε : 0 < p.ε) (hε1 : p.ε ≤ 1)
    (hTD : 0 ≤ p.T * p.lamD) {ζ : ℝ} (hζ : 0 < ζ) :
    4 / (ζ * GateBinaryODE.hStep p) ≤ 4 * (p.J : ℝ) / ζ := by
  have hh := GateBinaryODE.hStep_pos p hg hε hε1 hTD
  have hinv : (GateBinaryODE.hStep p)⁻¹ ≤ (p.J : ℝ) := step_inv_le hTD hg hε hε1
  have e : 4 / (ζ * GateBinaryODE.hStep p) = 4 * (GateBinaryODE.hStep p)⁻¹ / ζ := by
    field_simp
  rw [e]
  apply div_le_div_of_nonneg_right _ hζ.le
  linarith

/-! ### The decoder scale -/

/-- `√s ≤ s` for `s ≥ 1`. -/
theorem sqrt_le_self_of_one_le {s : ℝ} (hs : 1 ≤ s) : Real.sqrt s ≤ s := by
  have h1 : Real.sqrt s ≤ Real.sqrt (s ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
  rwa [Real.sqrt_sq (by linarith)] at h1

/-- **The decoder scale is not too large**: `γ √(4s) c₀ / (2^e ρ) ≤ 2^(1 + k_x + 2 bd)` for
`0 < γ ≤ 1`, `1 ≤ s ≤ 2^k_x`, `0 < c₀` of bit length `bd` and `1 ≤ 2^bd ρ`. -/
theorem kap_le (bd kx e s : ℕ) {γ c0 ρ : ℝ} (hγ1 : γ ≤ 1) (hs : 1 ≤ s) (hskx : s ≤ 2 ^ kx)
    (hc0 : HasBits bd c0) (hc0p : 0 < c0) (hρ : 0 < ρ) (hρ1 : 1 ≤ 2 ^ bd * ρ) :
    γ * Real.sqrt (4 * (s : ℝ)) * c0 / (2 ^ e * ρ) ≤ 2 ^ (1 + kx + 2 * bd) := by
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hsk : (s : ℝ) ≤ 2 ^ kx := by exact_mod_cast hskx
  have hsq : Real.sqrt (4 * (s : ℝ)) ≤ 2 * 2 ^ kx := by
    rw [GateODEBudget.sqrt_four_mul]
    have := sqrt_le_self_of_one_le hs1
    linarith
  have hc0' : c0 ≤ 2 ^ bd := hc0.lt.le
  have hρinv : 1 / ρ ≤ 2 ^ bd := by
    rw [div_le_iff₀ hρ]
    linarith
  have he : (1 : ℝ) ≤ 2 ^ e := one_le_pow₀ (by norm_num)
  have h0 : 0 ≤ Real.sqrt (4 * (s : ℝ)) * c0 * ρ := by positivity
  calc γ * Real.sqrt (4 * (s : ℝ)) * c0 / (2 ^ e * ρ)
      ≤ Real.sqrt (4 * (s : ℝ)) * c0 / ρ := by
        rw [div_le_div_iff₀ (by positivity) hρ]
        nlinarith [mul_le_mul_of_nonneg_right (hγ1.trans he) h0]
    _ = Real.sqrt (4 * (s : ℝ)) * c0 * (1 / ρ) := by ring
    _ ≤ (2 * 2 ^ kx) * 2 ^ bd * 2 ^ bd := by gcongr
    _ = 2 ^ (1 + kx + 2 * bd) := by ring

/-- **The decoder scale is not too small**: `(γ √(4s) c₀ / (2^e ρ))⁻¹ ≤ 2^e ρ γ⁻¹ 2^bd / 2` for
`γ > 0`, `s ≥ 1`, `0 < c₀` of bit length `bd` and `ρ > 0`. -/
theorem kap_inv_le (bd e s : ℕ) {γ c0 ρ : ℝ} (hγ : 0 < γ) (hs : 1 ≤ s) (hc0 : HasBits bd c0)
    (hc0p : 0 < c0) (hρ : 0 < ρ) :
    (γ * Real.sqrt (4 * (s : ℝ)) * c0 / (2 ^ e * ρ))⁻¹ ≤ 2 ^ e * ρ * γ⁻¹ * 2 ^ bd / 2 := by
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hsq : 2 ≤ Real.sqrt (4 * (s : ℝ)) := by
    rw [GateODEBudget.sqrt_four_mul]
    have : 1 ≤ Real.sqrt (s : ℝ) := by
      rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
      exact Real.sqrt_le_sqrt hs1
    linarith
  have hc0inv : c0⁻¹ ≤ 2 ^ bd := by
    rw [inv_eq_one_div, div_le_iff₀ hc0p]
    linarith [hc0.one_le_mul hc0p]
  have hsqinv : (Real.sqrt (4 * (s : ℝ)))⁻¹ ≤ 1 / 2 := by
    rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) hsq
  have e1 : (γ * Real.sqrt (4 * (s : ℝ)) * c0 / (2 ^ e * ρ))⁻¹ =
      2 ^ e * ρ * γ⁻¹ * (Real.sqrt (4 * (s : ℝ)))⁻¹ * c0⁻¹ := by
    rw [inv_div, div_eq_mul_inv, mul_inv, mul_inv]
    ring
  rw [e1]
  calc 2 ^ e * ρ * γ⁻¹ * (Real.sqrt (4 * (s : ℝ)))⁻¹ * c0⁻¹
      ≤ 2 ^ e * ρ * γ⁻¹ * (1 / 2) * 2 ^ bd := by gcongr
    _ = 2 ^ e * ρ * γ⁻¹ * 2 ^ bd / 2 := by ring

end

end SparseHamiltonian.GateBitBudget
