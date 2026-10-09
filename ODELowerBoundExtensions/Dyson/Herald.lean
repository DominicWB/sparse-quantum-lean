import SparseHamiltonian.ODEStateNormalization
import SparseODE.ODEHeraldedSuccess

set_option autoImplicit false

/-!
# Herald amplitude and normalised error of the Dyson preparation (`odel:lem:dyson`)

Manuscript lines 4246-4253: "Choose the truncation, discretisation, and quadrature errors so the
unnormalised solution error is at most `ε B/(C₂ ḡ)` … Since `‖x(T)‖ ≥ B/ḡ`, the normalised error
is at most `ε`, and success amplitude is `Ω(1/(ḡ e^z))`."

The decoded vector of the LCU preparation is `w = (2 m)⁻¹ y`, where `y` is the selected LCU sum
and `2 m` the coefficient mass (`m = lcuMass`, `B ≤ m ≤ B e^z`). If `‖y - x‖ ≤ ε B/(1000 g)`,
`B ≤ g ‖x‖` and `‖y‖ ≤ m`, then (`herald_bounds`)

* `1/(4 g') ≤ ‖w‖` with the public amplification parameter `g' = g m / B ≤ g e^z`;
* `‖w‖ ≤ 1/2` (the range of the released amplitude amplification);
* `‖w/‖w‖ - x/‖x‖‖ ≤ ε/500` (the direction accuracy of the released trial certificate).
-/

namespace ODELowerBoundExtensions.Dyson

noncomputable section

open SparseHamiltonian

/-- **Amplitude window and direction error of the decoded Dyson vector.** -/
theorem herald_bounds {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (y x : E) (m B g ε : ℝ) (hB : 0 < B) (hm : B ≤ m) (hg : 1 ≤ g) (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hx : B ≤ g * ‖x‖) (hy : ‖y‖ ≤ m)
    (herr : ‖y - x‖ ≤ ε * B / (1000 * g)) :
    1 / (4 * (g * m / B)) ≤ ‖((2 * m : ℝ) : ℂ)⁻¹ • y‖ ∧
      ‖((2 * m : ℝ) : ℂ)⁻¹ • y‖ ≤ 1 / 2 ∧
      ‖ODEStateNormalization.unitDirection (((2 * m : ℝ) : ℂ)⁻¹ • y) -
          ODEStateNormalization.unitDirection x‖ ≤ ε / 500 := by
  have hg0 : 0 < g := by linarith
  have hm0 : 0 < m := by linarith
  have hBg : B / g ≤ ‖x‖ := by
    rw [div_le_iff₀ hg0]; linarith
  have hx0 : 0 < ‖x‖ := lt_of_lt_of_le (div_pos hB hg0) hBg
  have hxne : x ≠ 0 := norm_pos_iff.mp hx0
  have hErrSmall : ‖y - x‖ ≤ B / (2 * g) := by
    refine herr.trans ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos hB hg0]
  have hyLower : B / (2 * g) ≤ ‖y‖ := by
    have hTri : ‖x‖ ≤ ‖y‖ + ‖y - x‖ := by
      have := norm_sub_le_norm_sub_add_norm_sub x y 0
      simpa only [sub_zero, norm_sub_rev x y, add_comm] using this
    have hHalf : B / (2 * g) = B / g - B / (2 * g) := by
      field_simp; ring
    linarith
  have hy0 : 0 < ‖y‖ := lt_of_lt_of_le (by positivity) hyLower
  have hyne : y ≠ 0 := norm_pos_iff.mp hy0
  have hScal : ((2 * m : ℝ) : ℂ)⁻¹ • y = ((2 * m)⁻¹ : ℝ) • y := by
    rw [← Complex.ofReal_inv, Complex.coe_smul]
  have hNorm : ‖((2 * m : ℝ) : ℂ)⁻¹ • y‖ = ‖y‖ / (2 * m) := by
    rw [hScal, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    ring
  refine ⟨?_, ?_, ?_⟩
  · rw [hNorm]
    have hEq : 1 / (4 * (g * m / B)) = (B / (2 * g)) / (2 * m) := by
      field_simp; ring
    rw [hEq]
    exact div_le_div_of_nonneg_right hyLower (by positivity)
  · rw [hNorm, div_le_iff₀ (by positivity)]
    linarith
  · rw [hScal, ODEHeraldedSuccess.unitDirection_pos_smul _ (by positivity) y]
    refine (ODEStateNormalization.unitDirection_error_le x y hxne hyne).trans ?_
    rw [div_le_iff₀ hx0]
    have h1 : ε * B ≤ ε * (g * ‖x‖) := mul_le_mul_of_nonneg_left hx hε.le
    have h2 : 2 * (ε * B / (1000 * g)) ≤ ε / 500 * ‖x‖ := by
      rw [div_le_iff₀ hg0] at hBg
      have : 2 * (ε * B / (1000 * g)) = ε * B / (500 * g) := by field_simp; ring
      rw [this, div_le_iff₀ (by positivity)]
      nlinarith
    calc 2 * ‖y - x‖ ≤ 2 * (ε * B / (1000 * g)) := by linarith
      _ ≤ _ := h2

end

end ODELowerBoundExtensions.Dyson
