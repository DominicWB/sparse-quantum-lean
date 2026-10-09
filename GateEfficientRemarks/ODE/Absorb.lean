import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Absorbing source costs polynomial in `𝔟`: the arithmetic

Theorem `ode:thm:gates` of the accompanying paper bounds the complete dissipative solver by
`G_ODE ≤ C ḡ [q P(𝔟) + G_src(ν) + A_src(ν)]` gates and `A_ODE ≤ P(𝔟) + C A_src(ν)` auxiliary
qubits (equations `ode:eq:gate-main`, `ode:eq:gate-space`) and remarks: "If the source gate and
work costs are polynomial in `𝔟`, the total gate bound is `ḡ q poly(𝔟)`." This file contains
the arithmetic of that remark for the explicit forms of the released library
`GateEfficientBitBudget`, with `Y = 𝔟 + 1 ≥ 1`, the query shape `Q = q* ≥ 1`, source costs
`G ≤ c Y^j`, `Z ≤ c Y^j` and `J = max j 3`:

* `gates_absorb`: `K g (Q Y³ + G + Z) ≤ K (1 + 2c) g Q Y^J`;
* `space_absorb`: `P Y³ + a Z ≤ (P + a c) Y^J` for `a ≥ 0`;
* `log_succ_le`: `log(G + 1) ≤ c + j Y`, so the synthesis factor `c₁ (64 Y + log(G + 1)) + c₀`
  of the finite-gate-set budgets is at most `(c₁ (64 + j + c) + c₀) Y`;
* `synth_absorb`: the gate bound of the finite-gate-set budgets,
  `K₁ g (P₁ Q Y³ + G) (c₁ (64 Y + log(G + 1)) + c₀) + K₂ g (4 (P₂ Y³ + 2 Z + X) + 3)`, is at most
  `(K₁ (P₁ + c) (c₁ (64 + j + c) + c₀) + K₂ (4 P₂ + 8 c + 3)) g Q Y^(J+1) + 4 K₂ g X`.

`nonneg_of_le_mul_pow` recovers `c ≥ 0` from `0 ≤ Z ≤ c Y^j`.
-/

set_option autoImplicit false

namespace SparseHamiltonian.GateRemarks.ODE

/-- A nonnegative quantity bounded by `c Y^j` with `Y > 0` forces `c ≥ 0`. -/
theorem nonneg_of_le_mul_pow {Z c Y : ℝ} (j : ℕ) (hZ0 : 0 ≤ Z) (hY : 0 < Y)
    (hZ : Z ≤ c * Y ^ j) : 0 ≤ c := by
  have hP : 0 < Y ^ j := pow_pos hY j
  rcases le_or_gt 0 c with h | h
  · exact h
  · have : c * Y ^ j < 0 := mul_neg_of_neg_of_pos h hP
    linarith

/-- **Absorbing polynomial source costs into the gate bound**: for `Q ≥ 1`, `Y ≥ 1`, `c ≥ 0`,
`G ≤ c Y^j` and `Z ≤ c Y^j`, `K g (Q Y³ + G + Z) ≤ K (1 + 2c) g Q Y^(max j 3)`. -/
theorem gates_absorb {K g Q Y G Z c : ℝ} (j : ℕ) (hK : 0 ≤ K) (hg : 0 ≤ g) (hQ : 1 ≤ Q)
    (hY : 1 ≤ Y) (hc : 0 ≤ c) (hG : G ≤ c * Y ^ j) (hZ : Z ≤ c * Y ^ j) :
    K * g * (Q * Y ^ 3 + G + Z) ≤ K * (1 + 2 * c) * g * Q * Y ^ max j 3 := by
  have h3 : Y ^ 3 ≤ Y ^ max j 3 := pow_le_pow_right₀ hY (le_max_right j 3)
  have hj : Y ^ j ≤ Y ^ max j 3 := pow_le_pow_right₀ hY (le_max_left j 3)
  have hP : 1 ≤ Y ^ max j 3 := one_le_pow₀ hY
  generalize Y ^ max j 3 = P at h3 hj hP ⊢
  have h1 : Q * Y ^ 3 ≤ Q * P := mul_le_mul_of_nonneg_left h3 (by linarith)
  have h2 : c * Y ^ j ≤ c * P := mul_le_mul_of_nonneg_left hj hc
  have h4 : c * P ≤ c * P * Q := le_mul_of_one_le_right (mul_nonneg hc (by linarith)) hQ
  have hsum : Q * Y ^ 3 + G + Z ≤ (1 + 2 * c) * (Q * P) := by nlinarith
  have hKg : 0 ≤ K * g := mul_nonneg hK hg
  calc K * g * (Q * Y ^ 3 + G + Z) ≤ K * g * ((1 + 2 * c) * (Q * P)) :=
        mul_le_mul_of_nonneg_left hsum hKg
    _ = K * (1 + 2 * c) * g * Q * P := by ring

/-- **Absorbing polynomial source work into the qubit bound**: for `P ≥ 0`, `a ≥ 0`, `Y ≥ 1`,
`c ≥ 0` and `Z ≤ c Y^j`, `P Y³ + a Z ≤ (P + a c) Y^(max j 3)`. -/
theorem space_absorb {P Y Z c : ℝ} (a : ℝ) (j : ℕ) (hP : 0 ≤ P) (ha : 0 ≤ a) (hY : 1 ≤ Y)
    (hc : 0 ≤ c) (hZ : Z ≤ c * Y ^ j) :
    P * Y ^ 3 + a * Z ≤ (P + a * c) * Y ^ max j 3 := by
  have h3 : Y ^ 3 ≤ Y ^ max j 3 := pow_le_pow_right₀ hY (le_max_right j 3)
  have hj : Y ^ j ≤ Y ^ max j 3 := pow_le_pow_right₀ hY (le_max_left j 3)
  have h1 : P * Y ^ 3 ≤ P * Y ^ max j 3 := mul_le_mul_of_nonneg_left h3 hP
  have h2 : a * Z ≤ a * (c * Y ^ max j 3) :=
    mul_le_mul_of_nonneg_left (hZ.trans (mul_le_mul_of_nonneg_left hj hc)) ha
  nlinarith

/-- **The logarithm of a polynomial cost**: `log(G + 1) ≤ c + j Y` for `0 ≤ G ≤ c Y^j`,
`Y ≥ 1`, `c ≥ 0`. -/
theorem log_succ_le {G Y c : ℝ} (j : ℕ) (hG0 : 0 ≤ G) (hY : 1 ≤ Y) (hc : 0 ≤ c)
    (hG : G ≤ c * Y ^ j) : Real.log (G + 1) ≤ c + j * Y := by
  have hPj : 1 ≤ Y ^ j := one_le_pow₀ hY
  have hY0 : 0 < Y := by linarith
  have h1 : G + 1 ≤ (c + 1) * Y ^ j := by nlinarith
  have h2 : Real.log (G + 1) ≤ Real.log ((c + 1) * Y ^ j) := Real.log_le_log (by linarith) h1
  rw [Real.log_mul (by linarith) (pow_pos hY0 j).ne', Real.log_pow] at h2
  have h3 : Real.log (c + 1) ≤ c := by
    have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < c + 1)
    linarith
  have h4 : Real.log Y ≤ Y := by
    have := Real.log_le_sub_one_of_pos hY0
    linarith
  have h5 : (j : ℝ) * Real.log Y ≤ j * Y := mul_le_mul_of_nonneg_left h4 (Nat.cast_nonneg j)
  linarith

/-- **The synthesis factor of a polynomial cost**: for `0 ≤ G ≤ c Y^j`, `Y ≥ 1`, `c ≥ 0` and
`c₀, c₁ ≥ 0`, `c₁ (64 Y + log(G + 1)) + c₀ ≤ (c₁ (64 + j + c) + c₀) Y`. -/
theorem synth_factor_le {G Y c c₀ c₁ : ℝ} (j : ℕ) (hG0 : 0 ≤ G) (hY : 1 ≤ Y) (hc : 0 ≤ c)
    (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁) (hG : G ≤ c * Y ^ j) :
    c₁ * (64 * Y + Real.log (G + 1)) + c₀ ≤ (c₁ * (64 + j + c) + c₀) * Y := by
  have hl := log_succ_le j hG0 hY hc hG
  have h1 : 64 * Y + Real.log (G + 1) ≤ (64 + j + c) * Y := by nlinarith
  have h2 : c₁ * (64 * Y + Real.log (G + 1)) ≤ c₁ * ((64 + j + c) * Y) :=
    mul_le_mul_of_nonneg_left h1 hc₁
  have h3 : c₀ ≤ c₀ * Y := le_mul_of_one_le_right hc₀ hY
  nlinarith

/-- **Absorbing polynomial source costs into the finite-gate-set gate bound**: for `Q ≥ 1`,
`Y ≥ 1`, `c ≥ 0`, `0 ≤ G ≤ c Y^j`, `Z ≤ c Y^j` and nonnegative constants,
`K₁ g (P₁ Q Y³ + G) (c₁ (64 Y + log(G + 1)) + c₀) + K₂ g (4 (P₂ Y³ + 2 Z + X) + 3)` is at most
`(K₁ (P₁ + c) (c₁ (64 + j + c) + c₀) + K₂ (4 P₂ + 8 c + 3)) g Q Y^(max j 3 + 1) + 4 K₂ g X`. -/
theorem synth_absorb {K₁ K₂ P₁ P₂ g Q Y G Z X c c₀ c₁ : ℝ} (j : ℕ) (hK₁ : 0 ≤ K₁)
    (hK₂ : 0 ≤ K₂) (hP₁ : 0 ≤ P₁) (hP₂ : 0 ≤ P₂) (hg : 0 ≤ g) (hQ : 1 ≤ Q) (hY : 1 ≤ Y)
    (hc : 0 ≤ c) (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁) (hG0 : 0 ≤ G) (hG : G ≤ c * Y ^ j)
    (hZ : Z ≤ c * Y ^ j) :
    K₁ * g * ((P₁ * Q * Y ^ 3 + G) * (c₁ * (64 * Y + Real.log (G + 1)) + c₀)) +
        K₂ * g * (4 * (P₂ * Y ^ 3 + 2 * Z + X) + 3) ≤
      (K₁ * (P₁ + c) * (c₁ * (64 + j + c) + c₀) + K₂ * (4 * P₂ + 8 * c + 3)) * g * Q *
          Y ^ (max j 3 + 1) + 4 * K₂ * g * X := by
  have h3 : Y ^ 3 ≤ Y ^ max j 3 := pow_le_pow_right₀ hY (le_max_right j 3)
  have hj : Y ^ j ≤ Y ^ max j 3 := pow_le_pow_right₀ hY (le_max_left j 3)
  have hP : 1 ≤ Y ^ max j 3 := one_le_pow₀ hY
  have hpow : Y ^ (max j 3 + 1) = Y ^ max j 3 * Y := pow_succ Y (max j 3)
  rw [hpow]
  have hF := synth_factor_le j hG0 hY hc hc₀ hc₁ hG
  have hF0 : 0 ≤ c₁ * (64 * Y + Real.log (G + 1)) + c₀ := by
    have : 0 ≤ Real.log (G + 1) := Real.log_nonneg (by linarith)
    have : 0 ≤ 64 * Y + Real.log (G + 1) := by linarith
    positivity
  generalize Y ^ max j 3 = P at h3 hj hP ⊢
  generalize c₁ * (64 * Y + Real.log (G + 1)) + c₀ = F at hF hF0 ⊢
  -- the preparation factor
  have hA : P₁ * Q * Y ^ 3 + G ≤ (P₁ + c) * (Q * P) := by
    have h1 : P₁ * Q * Y ^ 3 ≤ P₁ * Q * P := mul_le_mul_of_nonneg_left h3 (by positivity)
    have h2 : G ≤ c * P := hG.trans (mul_le_mul_of_nonneg_left hj hc)
    have h4 : c * P ≤ c * (Q * P) := by
      have := le_mul_of_one_le_left (by linarith : (0 : ℝ) ≤ P) hQ
      exact mul_le_mul_of_nonneg_left this hc
    nlinarith
  have hA0 : 0 ≤ P₁ * Q * Y ^ 3 + G := by
    have : 0 ≤ P₁ * Q * Y ^ 3 := by positivity
    linarith
  have hAF : (P₁ * Q * Y ^ 3 + G) * F ≤ ((P₁ + c) * (Q * P)) * ((c₁ * (64 + j + c) + c₀) * Y) :=
    mul_le_mul hA hF hF0 (by positivity)
  -- the zero tests
  have hZ' : Z ≤ c * P := hZ.trans (mul_le_mul_of_nonneg_left hj hc)
  have hB : 4 * (P₂ * Y ^ 3 + 2 * Z + X) + 3 ≤ (4 * P₂ + 8 * c + 3) * (Q * P * Y) + 4 * X := by
    have h1 : P₂ * Y ^ 3 ≤ P₂ * P := mul_le_mul_of_nonneg_left h3 hP₂
    have h2 : P ≤ Q * P * Y := by
      have h5 : P ≤ Q * P := le_mul_of_one_le_left (by linarith) hQ
      have h6 : Q * P ≤ Q * P * Y := le_mul_of_one_le_right (by nlinarith) hY
      linarith
    have h7 : (4 * P₂ + 8 * c + 3) * P ≤ (4 * P₂ + 8 * c + 3) * (Q * P * Y) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    nlinarith
  have e1 : K₁ * g * ((P₁ * Q * Y ^ 3 + G) * F) ≤
      K₁ * g * (((P₁ + c) * (Q * P)) * ((c₁ * (64 + j + c) + c₀) * Y)) :=
    mul_le_mul_of_nonneg_left hAF (mul_nonneg hK₁ hg)
  have e2 : K₂ * g * (4 * (P₂ * Y ^ 3 + 2 * Z + X) + 3) ≤
      K₂ * g * ((4 * P₂ + 8 * c + 3) * (Q * P * Y) + 4 * X) :=
    mul_le_mul_of_nonneg_left hB (mul_nonneg hK₂ hg)
  have e3 : K₁ * g * (((P₁ + c) * (Q * P)) * ((c₁ * (64 + j + c) + c₀) * Y)) +
      K₂ * g * ((4 * P₂ + 8 * c + 3) * (Q * P * Y) + 4 * X) =
      (K₁ * (P₁ + c) * (c₁ * (64 + j + c) + c₀) + K₂ * (4 * P₂ + 8 * c + 3)) * g * Q * (P * Y) +
        4 * K₂ * g * X := by ring
  linarith

end SparseHamiltonian.GateRemarks.ODE
