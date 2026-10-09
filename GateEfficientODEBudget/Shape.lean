import SparseODE.ImprovedODEQueryBudget
import SparseHamiltonian.CayleyClockInterface
import SparseHamiltonian.TimeSchedule

/-!
# The public rescaling and the size bounds of the dissipative solvers

For the dissipative solvers from binary data the released parameters have the Cayley rescaling
`γ` as public datum: `Q = width(4s, γ)`, `q̄ = moment γ`, `λ_H = √(4s) η_H / γ`,
`λ_D = √(4s) η_D / γ`, the common simulation time `τ = T (λ_H + R λ_D)` and the precision unit
`ν = ε/(10000 g)`. With the logarithmic envelope `ℓ = log(10000 g/ε) = log(1/ν)`
(`ImprovedODEQueryBudget.logBudget`), the time budget `Θ = T η_H + T η_D ℓ` (`thetaOf`) and the
query shape `q = √s Θ + √(s Θ ℓ) + ℓ` of equation `ode:eq:gate-q` (`qOf`), this file chooses
`γ = min(1, √(Θ/ℓ))` (`gam`, `gammaOf`) from the public data `T`, `η_H`, `η_D`, `g`, `ε`
alone, and proves the bounds behind `d = O(q)`:

* `ShapeOK.tau_le`: `τ ≤ 16 q`;
* `ShapeOK.width_mul_le`: `Q (1 + log(3/ν)) ≤ 16 q`, hence the released degree bound
  `128 (τ q̄ + Q (1 + log(3/ν)))` is at most `4096 q` (`ShapeOK.degree_shape_le`);
* `ShapeOK.lamD_le`: `T λ_D ≤ 2 q / ℓ` and `ShapeOK.grid_le`: the released LCHS grid bound
  `R (T λ_D + 2 log(512/ν))/π + 3` is at most `60 q ℓ`;
* `ShapeOK.lam_le`: `T (λ_H + λ_D) ≤ 2 q` (the quadrature register);
* `steps_le`: the released simulator schedule for `τ ≤ 16 q` has at most
  `2 + 64 q + √(12288 q³/ν)` steps.

The algebra uses the two regimes of the rescaling (`gam_cases`): `γ = 1` if `ℓ ≤ Θ`, and
`γ = √Θ/√ℓ` otherwise, where `Θ/γ = √(Θℓ)` and `γ ℓ = √(Θℓ)` (`key_div`, `key_mul`, `key_dis`).
The same lemmas serve the time-dependent solver with `(2g, ε/2)` in place of `(g, ε)`.
-/

set_option autoImplicit false

namespace SparseHamiltonian.GateODEBudget

noncomputable section
open ImprovedODEQueryBudget (precision logBudget radius theta effectiveTime queryShape
  logBudget_ge_one effectiveTime_le precision_pos radius_le radius_nonneg
  precision_le_one_ten_thousandth)
open CayleyClockInterface (width moment)

/-! ### The rescaling -/

/-- **The public rescaling** `γ = min(1, √(Θ/ℓ))`. -/
def gam (Θ ℓ : ℝ) : ℝ := min 1 (Real.sqrt (Θ / ℓ))

section Key

/-- `Θ / γ ≤ Θ + √(Θℓ)` in the variables `Θ = a²`, `ℓ = b²`, scaled by `u ≥ 0`. -/
theorem key_div (u a b : ℝ) (hu : 0 ≤ u) (ha : 0 < a) (hb : 0 < b) :
    u * (a * a) / min 1 (a / b) ≤ u * (a * a) + u * (a * b) := by
  rcases le_or_gt b a with h | h
  · have h1 : 1 ≤ a / b := by rw [le_div_iff₀ hb]; linarith
    rw [min_eq_left h1, div_one]
    have := mul_nonneg hu (mul_nonneg ha.le hb.le)
    linarith
  · have h1 : a / b ≤ 1 := by rw [div_le_iff₀ hb]; linarith
    rw [min_eq_right h1]
    have e : u * (a * a) / (a / b) = u * (a * b) := by
      field_simp
    rw [e]
    have := mul_nonneg hu (mul_nonneg ha.le ha.le)
    linarith

/-- `γ ℓ ≤ Θ + √(Θℓ)` in the variables `Θ = a²`, `ℓ = b²`, scaled by `u ≥ 0`. -/
theorem key_mul (u a b : ℝ) (hu : 0 ≤ u) (ha : 0 < a) (hb : 0 < b) :
    min 1 (a / b) * u * (b * b) ≤ u * (a * a) + u * (a * b) := by
  rcases le_or_gt b a with h | h
  · have h1 : 1 ≤ a / b := by rw [le_div_iff₀ hb]; linarith
    rw [min_eq_left h1, one_mul]
    have h2 : b * b ≤ a * a := mul_self_le_mul_self hb.le h
    have := mul_nonneg hu (mul_nonneg ha.le hb.le)
    nlinarith
  · have h1 : a / b ≤ 1 := by rw [div_le_iff₀ hb]; linarith
    rw [min_eq_right h1]
    have e : a / b * u * (b * b) = u * (a * b) := by
      field_simp
    rw [e]
    have := mul_nonneg hu (mul_nonneg ha.le ha.le)
    linarith

/-- `D / γ ≤ (Θ + √(Θℓ)) / ℓ` for `D ℓ ≤ Θ`, in the variables `Θ = a²`, `ℓ = b²`, scaled by
`u ≥ 0`. -/
theorem key_dis (u a b D : ℝ) (hu : 0 ≤ u) (ha : 0 < a) (hb : 0 < b)
    (hDl : D * (b * b) ≤ a * a) :
    u * D / min 1 (a / b) ≤ (u * (a * a) + u * (a * b)) / (b * b) := by
  have hbb : 0 < b * b := mul_pos hb hb
  rw [le_div_iff₀ hbb]
  rcases le_or_gt b a with h | h
  · have h1 : 1 ≤ a / b := by rw [le_div_iff₀ hb]; linarith
    rw [min_eq_left h1, div_one]
    have h2 : u * D * (b * b) ≤ u * (a * a) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hDl hu
    have := mul_nonneg hu (mul_nonneg ha.le hb.le)
    linarith
  · have h1 : a / b ≤ 1 := by rw [div_le_iff₀ hb]; linarith
    rw [min_eq_right h1]
    have e : u * D / (a / b) * (b * b) = u * (D * (b * b)) * b / a := by
      field_simp
    rw [e, div_le_iff₀ ha]
    have h2 : u * (D * (b * b)) * b ≤ u * (a * a) * b :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hDl hu) hb.le
    have h3 : u * (a * a) * b = u * (a * b) * a := by ring
    have h4 : 0 ≤ u * (a * a) * a := mul_nonneg (mul_nonneg hu (mul_nonneg ha.le ha.le)) ha.le
    nlinarith

end Key

section Gam

variable {Θ ℓ : ℝ}

theorem gam_pos (hΘ : 0 < Θ) (hℓ : 0 < ℓ) : 0 < gam Θ ℓ :=
  lt_min one_pos (Real.sqrt_pos.mpr (div_pos hΘ hℓ))

theorem gam_le_one : gam Θ ℓ ≤ 1 := min_le_left _ _

/-- The rescaling in the variables `√Θ`, `√ℓ`. -/
theorem gam_eq (hℓ : 0 < ℓ) : gam Θ ℓ = min 1 (Real.sqrt Θ / Real.sqrt ℓ) := by
  rw [gam, Real.sqrt_div' _ hℓ.le]

/-- **The two regimes of the rescaling**: `γ = 1` if `ℓ ≤ Θ`, `γ = √Θ/√ℓ` otherwise. -/
theorem gam_cases (hℓ : 0 < ℓ) :
    (ℓ ≤ Θ ∧ gam Θ ℓ = 1) ∨ (Θ < ℓ ∧ gam Θ ℓ = Real.sqrt Θ / Real.sqrt ℓ) := by
  rcases le_or_gt ℓ Θ with h | h
  · refine Or.inl ⟨h, min_eq_left ?_⟩
    rw [Real.one_le_sqrt, le_div_iff₀ hℓ, one_mul]
    exact h
  · refine Or.inr ⟨h, ?_⟩
    rw [gam_eq hℓ, min_eq_right]
    rw [div_le_one (Real.sqrt_pos.mpr hℓ)]
    exact Real.sqrt_le_sqrt h.le

/-- `u Θ / γ ≤ u Θ + u √(Θℓ)`. -/
theorem gam_div_le (hΘ : 0 < Θ) (hℓ : 0 < ℓ) (u : ℝ) (hu : 0 ≤ u) :
    u * Θ / gam Θ ℓ ≤ u * Θ + u * Real.sqrt (Θ * ℓ) := by
  have h := key_div u (Real.sqrt Θ) (Real.sqrt ℓ) hu (Real.sqrt_pos.mpr hΘ) (Real.sqrt_pos.mpr hℓ)
  rwa [Real.mul_self_sqrt hΘ.le, ← Real.sqrt_mul hΘ.le, ← gam_eq hℓ] at h

/-- `γ u ℓ ≤ u Θ + u √(Θℓ)`. -/
theorem gam_mul_le (hΘ : 0 < Θ) (hℓ : 0 < ℓ) (u : ℝ) (hu : 0 ≤ u) :
    gam Θ ℓ * u * ℓ ≤ u * Θ + u * Real.sqrt (Θ * ℓ) := by
  have h := key_mul u (Real.sqrt Θ) (Real.sqrt ℓ) hu (Real.sqrt_pos.mpr hΘ) (Real.sqrt_pos.mpr hℓ)
  rwa [Real.mul_self_sqrt hΘ.le, Real.mul_self_sqrt hℓ.le, ← Real.sqrt_mul hΘ.le,
    ← gam_eq hℓ] at h

/-- `u D / γ ≤ (u Θ + u √(Θℓ)) / ℓ` for `D ℓ ≤ Θ`. -/
theorem gam_dis_le (hΘ : 0 < Θ) (hℓ : 0 < ℓ) (u D : ℝ) (hu : 0 ≤ u) (hDl : D * ℓ ≤ Θ) :
    u * D / gam Θ ℓ ≤ (u * Θ + u * Real.sqrt (Θ * ℓ)) / ℓ := by
  have h := key_dis u (Real.sqrt Θ) (Real.sqrt ℓ) D hu (Real.sqrt_pos.mpr hΘ)
    (Real.sqrt_pos.mpr hℓ) (by rwa [Real.mul_self_sqrt hℓ.le, Real.mul_self_sqrt hΘ.le])
  rwa [Real.mul_self_sqrt hΘ.le, Real.mul_self_sqrt hℓ.le, ← Real.sqrt_mul hΘ.le,
    ← gam_eq hℓ] at h

end Gam

/-! ### The public choices of the dissipative solvers -/

/-- The time budget `Θ = T η_H + T η_D ℓ` of equation `ode:eq:gate-q`. -/
def thetaOf (T ηH ηD g ε : ℝ) : ℝ := theta (T * ηH) (T * ηD) g ε

/-- **The query shape** `q = √s Θ + √(s Θ ℓ) + ℓ` of equation `ode:eq:gate-q`. -/
def qOf (s T ηH ηD g ε : ℝ) : ℝ := queryShape s (thetaOf T ηH ηD g ε) (logBudget g ε)

/-- **The public rescaling** of the dissipative solvers: `γ = min(1, √(Θ/ℓ))`. -/
def gammaOf (T ηH ηD g ε : ℝ) : ℝ := gam (thetaOf T ηH ηD g ε) (logBudget g ε)

theorem gammaOf_le_one (T ηH ηD g ε : ℝ) : gammaOf T ηH ηD g ε ≤ 1 := gam_le_one

/-- `√(4s) = 2 √s`. -/
theorem sqrt_four_mul (s : ℝ) : Real.sqrt (4 * s) = 2 * Real.sqrt s := by
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
  have : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [this]

/-- The public conditions used by the size bounds. -/
structure ShapeOK (s T ηH ηD g ε : ℝ) : Prop where
  s_ge : 1 ≤ s
  T_pos : 0 < T
  etaH_nonneg : 0 ≤ ηH
  etaD_nonneg : 0 ≤ ηD
  eta_pos : 0 < ηH + ηD
  g_ge : 1 ≤ g
  ε_pos : 0 < ε
  ε_le : ε ≤ 1

namespace ShapeOK

variable {s T ηH ηD g ε : ℝ} (h : ShapeOK s T ηH ηD g ε)
include h

theorem ell_ge : 1 ≤ logBudget g ε := logBudget_ge_one g ε h.g_ge h.ε_pos h.ε_le

theorem ell_pos : 0 < logBudget g ε := lt_of_lt_of_le one_pos h.ell_ge

theorem theta_pos : 0 < thetaOf T ηH ηD g ε := by
  have hℓ := h.ell_ge
  have hT := h.T_pos
  have hH := h.etaH_nonneg
  have hD := h.etaD_nonneg
  have hη := h.eta_pos
  unfold thetaOf theta
  have h1 : 0 < T * (ηH + ηD) := mul_pos hT hη
  have h2 : T * ηD ≤ T * ηD * logBudget g ε :=
    le_mul_of_one_le_right (mul_nonneg hT.le hD) hℓ
  nlinarith

/-- `T η_H + T η_D ≤ Θ`. -/
theorem sum_le_theta : T * ηH + T * ηD ≤ thetaOf T ηH ηD g ε := by
  have h2 : T * ηD ≤ T * ηD * logBudget g ε :=
    le_mul_of_one_le_right (mul_nonneg h.T_pos.le h.etaD_nonneg) h.ell_ge
  unfold thetaOf theta
  linarith

/-- `T η_D ℓ ≤ Θ`. -/
theorem dis_le_theta : T * ηD * logBudget g ε ≤ thetaOf T ηH ηD g ε := by
  have := mul_nonneg h.T_pos.le h.etaH_nonneg
  unfold thetaOf theta
  linarith

theorem gammaOf_pos : 0 < gammaOf T ηH ηD g ε := gam_pos h.theta_pos h.ell_pos

/-- `√s (Θ + √(Θℓ)) ≤ q`. -/
theorem sqrt_le_q :
    Real.sqrt s * thetaOf T ηH ηD g ε +
      Real.sqrt s * Real.sqrt (thetaOf T ηH ηD g ε * logBudget g ε) ≤ qOf s T ηH ηD g ε := by
  have hs : 0 ≤ s := by linarith [h.s_ge]
  have e : Real.sqrt (s * thetaOf T ηH ηD g ε * logBudget g ε) =
      Real.sqrt s * Real.sqrt (thetaOf T ηH ηD g ε * logBudget g ε) := by
    rw [mul_assoc, Real.sqrt_mul hs]
  unfold qOf queryShape
  rw [e]
  linarith [h.ell_ge]

/-- `ℓ ≤ q`. -/
theorem ell_le_q : logBudget g ε ≤ qOf s T ηH ηD g ε := by
  have h1 : 0 ≤ Real.sqrt s * thetaOf T ηH ηD g ε :=
    mul_nonneg (Real.sqrt_nonneg _) h.theta_pos.le
  have h2 := Real.sqrt_nonneg (s * thetaOf T ηH ηD g ε * logBudget g ε)
  unfold qOf queryShape
  linarith

theorem one_le_q : 1 ≤ qOf s T ηH ηD g ε := h.ell_ge.trans h.ell_le_q

theorem q_pos : 0 < qOf s T ηH ηD g ε := lt_of_lt_of_le one_pos h.one_le_q

/-- **The common simulation time is at most `16 q`**:
`T (√(4s) η_H/γ + R √(4s) η_D/γ) ≤ 16 q`. -/
theorem tau_le :
    T * (Real.sqrt (4 * s) * ηH / gammaOf T ηH ηD g ε +
      radius g ε * (Real.sqrt (4 * s) * ηD / gammaOf T ηH ηD g ε)) ≤ 16 * qOf s T ηH ηD g ε := by
  have hγ := h.gammaOf_pos
  have heff := effectiveTime_le (T * ηH) (T * ηD) g ε (mul_nonneg h.T_pos.le h.etaH_nonneg)
    (mul_nonneg h.T_pos.le h.etaD_nonneg) h.g_ge h.ε_pos h.ε_le
  have hb := gam_div_le h.theta_pos h.ell_pos (Real.sqrt s) (Real.sqrt_nonneg s)
  have hq := h.sqrt_le_q
  change effectiveTime (T * ηH) (T * ηD) g ε ≤ 8 * thetaOf T ηH ηD g ε at heff
  change Real.sqrt s * thetaOf T ηH ηD g ε / gammaOf T ηH ηD g ε ≤ _ at hb
  have e : T * (Real.sqrt (4 * s) * ηH / gammaOf T ηH ηD g ε +
      radius g ε * (Real.sqrt (4 * s) * ηD / gammaOf T ηH ηD g ε)) =
      2 * Real.sqrt s * effectiveTime (T * ηH) (T * ηD) g ε / gammaOf T ηH ηD g ε := by
    rw [sqrt_four_mul]
    unfold effectiveTime
    field_simp
  rw [e]
  have hs0 := Real.sqrt_nonneg s
  have h1 : 2 * Real.sqrt s * effectiveTime (T * ηH) (T * ηD) g ε ≤
      16 * (Real.sqrt s * thetaOf T ηH ηD g ε) := by nlinarith
  calc 2 * Real.sqrt s * effectiveTime (T * ηH) (T * ηD) g ε / gammaOf T ηH ηD g ε
      ≤ 16 * (Real.sqrt s * thetaOf T ηH ηD g ε) / gammaOf T ηH ηD g ε :=
        div_le_div_of_nonneg_right h1 hγ.le
    _ = 16 * (Real.sqrt s * thetaOf T ηH ηD g ε / gammaOf T ηH ηD g ε) := by ring
    _ ≤ 16 * qOf s T ηH ηD g ε := by linarith

/-- `log(3/ν) ≤ 2 + ℓ`, `ν = ε/(10000 g)`. -/
theorem log_three_le : Real.log (3 / precision g ε) ≤ 2 + logBudget g ε := by
  have hg0 : 0 < g := lt_of_lt_of_le one_pos h.g_ge
  have e : 3 / precision g ε = 3 * (10000 * g / ε) := by
    unfold precision
    field_simp
  have hpos : 0 < 10000 * g / ε := by have := h.ε_pos; positivity
  rw [e, Real.log_mul (by norm_num) hpos.ne']
  have h3 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
  unfold logBudget
  linarith

/-- `log(512/ν) ≤ 8 + ℓ`, `ν = ε/(10000 g)`. -/
theorem log_512_le : Real.log (512 / precision g ε) ≤ 8 + logBudget g ε := by
  have hg0 : 0 < g := lt_of_lt_of_le one_pos h.g_ge
  have e : 512 / precision g ε = 512 * (10000 * g / ε) := by
    unfold precision
    field_simp
  have hpos : 0 < 10000 * g / ε := by have := h.ε_pos; positivity
  rw [e, Real.log_mul (by norm_num) hpos.ne']
  have h2 : Real.log 512 = 9 * Real.log 2 := by
    rw [show (512 : ℝ) = 2 ^ 9 by norm_num, Real.log_pow]
    norm_num
  have h3 := Real.log_two_lt_d9
  unfold logBudget
  rw [h2]
  norm_num at h3 ⊢
  linarith

/-- **The clock width times the filter logarithm is at most `16 q`**:
`width(4s, γ) (1 + log(3/ν)) ≤ 16 q`. -/
theorem width_mul_le :
    width (4 * s) (gammaOf T ηH ηD g ε) * (1 + Real.log (3 / precision g ε)) ≤
      16 * qOf s T ηH ηD g ε := by
  have hγ := h.gammaOf_pos
  have hs := Real.sqrt_nonneg s
  have hℓ := h.ell_ge
  have hW : width (4 * s) (gammaOf T ηH ηD g ε) ≤ 2 + 2 * (gammaOf T ηH ηD g ε * Real.sqrt s) := by
    unfold width
    have h1 := Nat.ceil_lt_add_one (le_trans zero_le_one
      (le_max_left 1 (gammaOf T ηH ηD g ε * Real.sqrt (4 * s))))
    have h2 : max 1 (gammaOf T ηH ηD g ε * Real.sqrt (4 * s)) ≤
        1 + 2 * (gammaOf T ηH ηD g ε * Real.sqrt s) := by
      rw [sqrt_four_mul]
      apply max_le
      · nlinarith
      · nlinarith
    linarith
  have hL : 1 + Real.log (3 / precision g ε) ≤ 4 * logBudget g ε := by
    linarith [h.log_three_le]
  have hc := gam_mul_le h.theta_pos h.ell_pos (Real.sqrt s) hs
  have hq := h.sqrt_le_q
  have hlq := h.ell_le_q
  change gammaOf T ηH ηD g ε * Real.sqrt s * logBudget g ε ≤ _ at hc
  have hW0 : 0 ≤ width (4 * s) (gammaOf T ηH ηD g ε) :=
    le_trans zero_le_one (CayleyClockInterface.width_ge_one _ _)
  have hL0 : 0 ≤ 1 + Real.log (3 / precision g ε) := by
    have := CayleyClockInterface.width_ge_one (4 * s) (gammaOf T ηH ηD g ε)
    have hν := precision_pos g ε h.g_ge h.ε_pos
    have hν1 := precision_le_one_ten_thousandth g ε h.g_ge h.ε_le
    have : 0 ≤ Real.log (3 / precision g ε) :=
      Real.log_nonneg (by rw [le_div_iff₀ hν]; linarith)
    linarith
  calc width (4 * s) (gammaOf T ηH ηD g ε) * (1 + Real.log (3 / precision g ε))
      ≤ (2 + 2 * (gammaOf T ηH ηD g ε * Real.sqrt s)) * (4 * logBudget g ε) :=
        mul_le_mul hW hL hL0 (by nlinarith)
    _ = 8 * logBudget g ε + 8 * (gammaOf T ηH ηD g ε * Real.sqrt s * logBudget g ε) := by ring
    _ ≤ 16 * qOf s T ηH ηD g ε := by linarith

/-- **The released degree bound is at most `4096 q`**:
`128 (τ q̄ + width(4s, γ) (1 + log(3/ν))) ≤ 4096 q` for `0 ≤ τ ≤ 16 q`. -/
theorem degree_shape_le (τ : ℝ) (hτ0 : 0 ≤ τ) (hτ : τ ≤ 16 * qOf s T ηH ηD g ε) :
    128 * (τ * moment (gammaOf T ηH ηD g ε) +
      width (4 * s) (gammaOf T ηH ηD g ε) * (1 + Real.log (3 / precision g ε))) ≤
      4096 * qOf s T ηH ηD g ε := by
  have hm := CayleyClockInterface.moment_le_one _ h.gammaOf_pos.le (gammaOf_le_one T ηH ηD g ε)
  have hm0 : 0 ≤ moment (gammaOf T ηH ηD g ε) := by
    unfold moment
    positivity
  have h1 : τ * moment (gammaOf T ηH ηD g ε) ≤ τ := mul_le_of_le_one_right hτ0 hm
  have h2 := h.width_mul_le
  linarith

/-- **The rescaled dissipative norm**: `T √(4s) η_D/γ ≤ 2 q / ℓ`. -/
theorem lamD_le :
    T * (Real.sqrt (4 * s) * ηD / gammaOf T ηH ηD g ε) ≤
      2 * qOf s T ηH ηD g ε / logBudget g ε := by
  have hd := gam_dis_le h.theta_pos h.ell_pos (Real.sqrt s) (T * ηD) (Real.sqrt_nonneg s)
    h.dis_le_theta
  have hq := h.sqrt_le_q
  change Real.sqrt s * (T * ηD) / gammaOf T ηH ηD g ε ≤ _ at hd
  have e : T * (Real.sqrt (4 * s) * ηD / gammaOf T ηH ηD g ε) =
      2 * (Real.sqrt s * (T * ηD) / gammaOf T ηH ηD g ε) := by
    rw [sqrt_four_mul]
    ring
  rw [e, show 2 * qOf s T ηH ηD g ε / logBudget g ε = 2 * (qOf s T ηH ηD g ε / logBudget g ε)
    by ring]
  exact mul_le_mul_of_nonneg_left (hd.trans (div_le_div_of_nonneg_right hq h.ell_pos.le))
    (by norm_num)

/-- **The quadrature norm**: `T (√(4s) η_H/γ + √(4s) η_D/γ) ≤ 2 q`. -/
theorem lam_le :
    T * (Real.sqrt (4 * s) * ηH / gammaOf T ηH ηD g ε +
      Real.sqrt (4 * s) * ηD / gammaOf T ηH ηD g ε) ≤ 2 * qOf s T ηH ηD g ε := by
  have hγ := h.gammaOf_pos
  have hb := gam_div_le h.theta_pos h.ell_pos (Real.sqrt s) (Real.sqrt_nonneg s)
  have hq := h.sqrt_le_q
  have hsum := h.sum_le_theta
  change Real.sqrt s * thetaOf T ηH ηD g ε / gammaOf T ηH ηD g ε ≤ _ at hb
  have e : T * (Real.sqrt (4 * s) * ηH / gammaOf T ηH ηD g ε +
      Real.sqrt (4 * s) * ηD / gammaOf T ηH ηD g ε) =
      2 * (Real.sqrt s * (T * ηH + T * ηD) / gammaOf T ηH ηD g ε) := by
    rw [sqrt_four_mul]
    field_simp
  rw [e]
  have h1 : Real.sqrt s * (T * ηH + T * ηD) / gammaOf T ηH ηD g ε ≤
      Real.sqrt s * thetaOf T ηH ηD g ε / gammaOf T ηH ηD g ε :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsum (Real.sqrt_nonneg s)) hγ.le
  linarith

/-- **The LCHS grid bound is at most `60 q ℓ`**: `R (T λ_D + 2 log(512/ν))/π + 3 ≤ 60 q ℓ`. -/
theorem grid_le :
    radius g ε * (T * (Real.sqrt (4 * s) * ηD / gammaOf T ηH ηD g ε) +
      2 * Real.log (512 / precision g ε)) / Real.pi + 3 ≤
      60 * qOf s T ηH ηD g ε * logBudget g ε := by
  have hR := radius_le g ε h.g_ge h.ε_pos h.ε_le
  have hR0 := radius_nonneg g ε h.g_ge h.ε_pos h.ε_le
  have hD := h.lamD_le
  have hL := h.log_512_le
  have hℓ := h.ell_ge
  have hℓ0 := h.ell_pos
  have hq := h.ell_le_q
  have hq1 := h.one_le_q
  have hpi := Real.pi_gt_three
  set A := T * (Real.sqrt (4 * s) * ηD / gammaOf T ηH ηD g ε) with hA
  set L := Real.log (512 / precision g ε) with hLdef
  set ℓ := logBudget g ε with hℓdef
  set Q := qOf s T ηH ηD g ε with hQ
  have hA0 : 0 ≤ A := by
    have := h.gammaOf_pos
    have := h.T_pos
    have := h.etaD_nonneg
    positivity
  have hL0 : 0 ≤ L := by
    have hν := precision_pos g ε h.g_ge h.ε_pos
    have hν1 := precision_le_one_ten_thousandth g ε h.g_ge h.ε_le
    exact Real.log_nonneg (by rw [le_div_iff₀ hν]; linarith)
  have hAℓ : A * ℓ ≤ 2 * Q := (le_div_iff₀ hℓ0).mp hD
  have h1 : radius g ε * (A + 2 * L) ≤ 16 * Q + 128 * ℓ + 16 * (ℓ * ℓ) := by
    have h2 : radius g ε * (A + 2 * L) ≤ 8 * ℓ * (A + 2 * L) :=
      mul_le_mul_of_nonneg_right hR (by linarith)
    nlinarith
  have hX0 : 0 ≤ radius g ε * (A + 2 * L) := mul_nonneg hR0 (by linarith)
  have h3 : radius g ε * (A + 2 * L) / Real.pi ≤ radius g ε * (A + 2 * L) / 3 :=
    div_le_div_of_nonneg_left hX0 (by norm_num) hpi.le
  have hqℓ : ℓ * ℓ ≤ Q * ℓ := mul_le_mul_of_nonneg_right hq hℓ0.le
  have hq2 : Q ≤ Q * ℓ := le_mul_of_one_le_right (by linarith) hℓ
  have hq3 : ℓ ≤ Q * ℓ := le_mul_of_one_le_left hℓ0.le hq1
  have hq4 : 1 ≤ Q * ℓ := by nlinarith
  linarith

end ShapeOK

/-- **The released simulator schedule for `0 ≤ τ ≤ 16 q`** has at most
`2 + 64 q + √(12288 q³/ν)` steps. -/
theorem steps_le (τ q ν : ℝ) (hτ0 : 0 ≤ τ) (hτ : τ ≤ 16 * q) (hν : 0 < ν) :
    (TimeSchedule.steps τ (ν / 3) : ℝ) ≤ 2 + 64 * q + Real.sqrt (12288 * q ^ 3 / ν) := by
  have hq0 : 0 ≤ q := by linarith
  have hth0 : 0 ≤ TimeSchedule.threshold τ (ν / 3) :=
    (by positivity : (0 : ℝ) ≤ 4 * τ).trans (le_max_left _ _)
  have hc := Nat.ceil_lt_add_one hth0
  have hsq : Real.sqrt (τ ^ 3 / (ν / 3)) ≤ Real.sqrt (12288 * q ^ 3 / ν) := by
    apply Real.sqrt_le_sqrt
    have e : τ ^ 3 / (ν / 3) = 3 * τ ^ 3 / ν := by field_simp
    rw [e]
    apply div_le_div_of_nonneg_right _ hν.le
    have h3 : τ ^ 3 ≤ (16 * q) ^ 3 := pow_le_pow_left₀ hτ0 hτ 3
    nlinarith
  have hmax : TimeSchedule.threshold τ (ν / 3) ≤ 64 * q + Real.sqrt (12288 * q ^ 3 / ν) := by
    unfold TimeSchedule.threshold
    apply max_le
    · have := Real.sqrt_nonneg (12288 * q ^ 3 / ν)
      linarith
    · have : 0 ≤ q := hq0
      linarith
  unfold TimeSchedule.steps
  push_cast
  linarith

end

end SparseHamiltonian.GateODEBudget
