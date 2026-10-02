import SparseHamiltonian.ODEErrorBudget

/-!
# Normalized ODE state error and extraction amplitude

Approximation of an unnormalized solution is converted into approximation of
its direction. The source-to-solution ratio appears explicitly, as it must for
an ODE state preparation theorem. These are vector and scalar estimates; no
amplitude-amplification circuit or its query bound is assumed or claimed.
-/

namespace SparseHamiltonian.ODEStateNormalization

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The unit direction, with the usual total definition at the zero vector. -/
def unitDirection (x : E) : E := ‖x‖⁻¹ • x

/-- Every nonzero vector has a unit-norm direction. -/
theorem unitDirection_norm (x : E) (hx : x ≠ 0) : ‖unitDirection x‖ = 1 := by
  have hxNorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  unfold unitDirection
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hxNorm)]
  exact inv_mul_cancel₀ (ne_of_gt hxNorm)

omit [NormedSpace ℝ E] in
/-- A relative approximation with error below one cannot vanish. -/
theorem approximate_ne_zero (x y : E) (η : ℝ) (hx : x ≠ 0) (hη : η < 1)
    (hError : ‖y - x‖ ≤ η * ‖x‖) : y ≠ 0 := by
  intro hy
  have hxNorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  subst y
  simp only [zero_sub, norm_neg] at hError
  nlinarith

omit [NormedSpace ℝ E] in
/-- Relative vector error gives a lower bound on the unnormalized output norm. -/
theorem approximate_norm_lower (x y : E) (η : ℝ)
    (hError : ‖y - x‖ ≤ η * ‖x‖) : (1 - η) * ‖x‖ ≤ ‖y‖ := by
  have hTriangle := norm_sub_le_norm_sub_add_norm_sub x y 0
  simp only [sub_zero, norm_sub_rev x y] at hTriangle
  nlinarith

/-- Normalizing a nonzero vector costs at most twice the relative error. -/
theorem unitDirection_error_le (x y : E) (hx : x ≠ 0) (hy : y ≠ 0) :
    ‖unitDirection y - unitDirection x‖ ≤ 2 * ‖y - x‖ / ‖x‖ := by
  have hxNorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hyNorm : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hScale :
      ‖unitDirection y - ‖x‖⁻¹ • y‖ = |‖x‖ - ‖y‖| / ‖x‖ := by
    unfold unitDirection
    rw [← sub_smul, norm_smul, Real.norm_eq_abs]
    have hScalar : (‖y‖⁻¹ - ‖x‖⁻¹) = (‖x‖ - ‖y‖) / (‖y‖ * ‖x‖) := by
      field_simp [ne_of_gt hxNorm, ne_of_gt hyNorm]
    rw [hScalar, abs_div, abs_mul, abs_of_pos hyNorm, abs_of_pos hxNorm]
    field_simp [ne_of_gt hxNorm, ne_of_gt hyNorm]
  have hFirst : ‖unitDirection y - ‖x‖⁻¹ • y‖ ≤ ‖y - x‖ / ‖x‖ := by
    rw [hScale]
    exact div_le_div_of_nonneg_right (by simpa [norm_sub_rev] using abs_norm_sub_norm_le x y)
      (le_of_lt hxNorm)
  have hSecond : ‖‖x‖⁻¹ • y - unitDirection x‖ = ‖y - x‖ / ‖x‖ := by
    unfold unitDirection
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hxNorm)]
    ring
  calc
    _ ≤ ‖unitDirection y - ‖x‖⁻¹ • y‖ + ‖‖x‖⁻¹ • y - unitDirection x‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ‖y - x‖ / ‖x‖ + ‖y - x‖ / ‖x‖ := by rw [hSecond]; exact add_le_add hFirst (le_refl _)
    _ = 2 * ‖y - x‖ / ‖x‖ := by ring

/-- A relative tolerance `η < 1` simultaneously certifies nonvanishing and
normalized output error at most `2η`. -/
theorem relative_error (x y : E) (η : ℝ) (hx : x ≠ 0) (hη : η < 1)
    (hError : ‖y - x‖ ≤ η * ‖x‖) :
    y ≠ 0 ∧ ‖unitDirection y - unitDirection x‖ ≤ 2 * η := by
  have hy := approximate_ne_zero x y η hx hη hError
  refine ⟨hy, (unitDirection_error_le x y hx hy).trans ?_⟩
  have hxNorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  apply (div_le_iff₀ hxNorm).mpr
  nlinarith

omit [NormedSpace ℝ E] in
/-- If `B = g ‖x‖`, a relative solution error gives extraction amplitude
at least `(1-η)/(C g)` for an LCU normalization `C B`. -/
theorem extraction_amplitude_lower (x y : E) (B g C η : ℝ)
    (hx : x ≠ 0) (hg : 0 < g) (hC : 0 < C)
    (hBudget : B = g * ‖x‖) (hError : ‖y - x‖ ≤ η * ‖x‖) :
    (1 - η) / (C * g) ≤ ‖y‖ / (C * B) := by
  have hxNorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hDenom : 0 < C * g := mul_pos hC hg
  rw [hBudget]
  have hRewrite : ‖y‖ / (C * (g * ‖x‖)) = (‖y‖ / ‖x‖) / (C * g) := by
    ring
  rw [hRewrite]
  apply div_le_div_of_nonneg_right _ (le_of_lt hDenom)
  exact (le_div_iff₀ hxNorm).mpr (approximate_norm_lower x y η hError)

omit [NormedSpace ℝ E] in
/-- The source-to-solution ratio gives the required budget identity. -/
theorem ratio_budget_identity (x : E) (B : ℝ) (hx : x ≠ 0) :
    B = (B / ‖x‖) * ‖x‖ := by
  have hxNorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  field_simp [hxNorm]

/-- A conservative common tolerance for LCHS, branch simulation, and source
quadrature. Constants leave room for subsequent circuit error allocations. -/
def precision (ε g : ℝ) : ℝ := ε / (1000 * g)

theorem precision_pos (ε g : ℝ) (hε : 0 < ε) (hg : 0 < g) :
    0 < precision ε g := div_pos hε (mul_pos (by norm_num) hg)

omit [NormedSpace ℝ E] in
/-- Ten copies of the common tolerance, weighted by the source budget, consume
only `ε/100` of relative solution error. -/
theorem precision_budget (x : E) (B g ε : ℝ) (hg : 0 < g)
    (hBudget : B = g * ‖x‖) :
    10 * precision ε g * B = (ε / 100) * ‖x‖ := by
  unfold precision
  rw [hBudget]
  field_simp [ne_of_gt hg]
  ring

/-- An error budget of `10 ν B` at `ν = ε/(1000g)` yields a nonzero state,
normalized error at most `ε/50`, and a constant-fraction extraction amplitude. -/
theorem conservative_output_certificate (x y : E) (B g C ε : ℝ)
    (hx : x ≠ 0) (hg : 0 < g) (hC : 0 < C)
    (hεOne : ε ≤ 1) (hBudget : B = g * ‖x‖)
    (hError : ‖y - x‖ ≤ 10 * precision ε g * B) :
    y ≠ 0 ∧ ‖unitDirection y - unitDirection x‖ ≤ ε / 50 ∧
      (99 / 100 : ℝ) / (C * g) ≤ ‖y‖ / (C * B) := by
  have hRelative : ‖y - x‖ ≤ (ε / 100) * ‖x‖ := by
    simpa only [precision_budget x B g ε hg hBudget] using hError
  have hSmall : ε / 100 < 1 := by linarith
  have hNormal := relative_error x y (ε / 100) hx hSmall hRelative
  refine ⟨hNormal.1, ?_, ?_⟩
  · calc
      _ ≤ 2 * (ε / 100) := hNormal.2
      _ = ε / 50 := by ring
  · calc
      _ ≤ (1 - ε / 100) / (C * g) := by
        apply div_le_div_of_nonneg_right _ (le_of_lt (mul_pos hC hg))
        linarith
      _ ≤ ‖y‖ / (C * B) := extraction_amplitude_lower x y B g C (ε / 100)
        hx hg hC hBudget hRelative

omit [NormedSpace ℝ E] in
/-- A supplied upper bound on the source-to-solution ratio suffices for the
same relative-error allocation. The exact ratio need not be known. -/
theorem precision_budget_le (x : E) (B g ε : ℝ) (hg : 0 < g)
    (hε : 0 ≤ ε) (hBudget : B ≤ g * ‖x‖) :
    10 * precision ε g * B ≤ (ε / 100) * ‖x‖ := by
  have hPrec : 0 ≤ precision ε g := div_nonneg hε (le_of_lt (mul_pos (by norm_num) hg))
  calc
    _ ≤ 10 * precision ε g * (g * ‖x‖) :=
      mul_le_mul_of_nonneg_left hBudget (mul_nonneg (by norm_num) hPrec)
    _ = (ε / 100) * ‖x‖ := precision_budget x (g * ‖x‖) g ε hg rfl

omit [NormedSpace ℝ E] in
/-- The certified source ratio, as an inequality, implies a lower extraction
amplitude with the supplied ratio bound in the denominator. -/
theorem extraction_amplitude_lower_of_budget_le (x y : E) (B g C η : ℝ)
    (hB : 0 < B) (hg : 0 < g) (hC : 0 < C) (hη : η ≤ 1)
    (hBudget : B ≤ g * ‖x‖) (hError : ‖y - x‖ ≤ η * ‖x‖) :
    (1 - η) / (C * g) ≤ ‖y‖ / (C * B) := by
  have hNorm := approximate_norm_lower x y η hError
  have hRatio : (1 - η) * B ≤ g * ‖y‖ := by
    calc
      _ ≤ (1 - η) * (g * ‖x‖) :=
        mul_le_mul_of_nonneg_left hBudget (sub_nonneg.mpr hη)
      _ = g * ((1 - η) * ‖x‖) := by ring
      _ ≤ g * ‖y‖ := mul_le_mul_of_nonneg_left hNorm (le_of_lt hg)
  apply (div_le_div_iff₀ (mul_pos hC hg) (mul_pos hC hB)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hRatio (le_of_lt hC)]

/-- An upper ratio bound gives a unit-norm approximate output with controlled
error and extraction amplitude. This is the form needed when only a supplied
bound on the ODE amplification factor is available. -/
theorem bounded_ratio_output_certificate (x y : E) (B g C ε : ℝ)
    (hx : x ≠ 0) (hB : 0 < B) (hg : 0 < g) (hC : 0 < C)
    (hε : 0 < ε) (hεOne : ε ≤ 1) (hBudget : B ≤ g * ‖x‖)
    (hError : ‖y - x‖ ≤ 10 * precision ε g * B) :
    y ≠ 0 ∧ ‖unitDirection y‖ = 1 ∧
      ‖unitDirection y - unitDirection x‖ ≤ ε / 50 ∧
      (99 / 100 : ℝ) / (C * g) ≤ ‖y‖ / (C * B) := by
  have hRelative : ‖y - x‖ ≤ (ε / 100) * ‖x‖ :=
    hError.trans (precision_budget_le x B g ε hg (le_of_lt hε) hBudget)
  have hSmall : ε / 100 < 1 := by linarith [hε]
  have hNormal := relative_error x y (ε / 100) hx hSmall hRelative
  refine ⟨hNormal.1, unitDirection_norm y hNormal.1, ?_, ?_⟩
  · calc
      _ ≤ 2 * (ε / 100) := hNormal.2
      _ = ε / 50 := by ring
  · calc
      _ ≤ (1 - ε / 100) / (C * g) := by
        apply div_le_div_of_nonneg_right _ (le_of_lt (mul_pos hC hg))
        linarith
      _ ≤ ‖y‖ / (C * B) := extraction_amplitude_lower_of_budget_le x y B g C
        (ε / 100) hB hg hC (le_of_lt hSmall) hBudget hRelative

section ComplexSource

open scoped BigOperators
open ODEErrorBudget

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [NormedSpace ℂ E]

/-- A normalized output certificate for the concrete finite LCHS/source sum.
The analytic LCHS and quadrature certificates are explicit premises, and this
result makes no controlled-circuit or amplification-query assertion. -/
theorem finite_lchs_output_certificate
    (c : κ → ℂ) (U₀ V₀ : κ → E →L[ℂ] E)
    (U V : ι → κ → E →L[ℂ] E)
    (S₀ : E →L[ℂ] E) (S : ι → E →L[ℂ] E)
    (x₀ x : E) (w : ι → ℝ) (b : ι → E) (g C ε : ℝ)
    (hx : x ≠ 0) (hg : 0 < g) (hC : 0 < C) (hε : 0 < ε) (hεOne : ε ≤ 1)
    (hw : ∀ i, 0 ≤ w i) (hB : 0 < sourceBudget x₀ w b)
    (hBudget : sourceBudget x₀ w b ≤ g * ‖x‖) (hCoeff : ∑ k, ‖c k‖ ≤ 3)
    (hLCHS₀ : ‖(∑ k, c k • U₀ k) - S₀‖ ≤ precision ε g)
    (hLCHS : ∀ i, ‖(∑ k, c k • U i k) - S i‖ ≤ precision ε g)
    (hSimulation₀ : ∀ k, ‖V₀ k - U₀ k‖ ≤ precision ε g)
    (hSimulation : ∀ i k, ‖V i k - U i k‖ ≤ precision ε g)
    (hQuadrature : ‖finiteDuhamel S₀ S x₀ w b - x‖ ≤
      precision ε g * sourceBudget x₀ w b) :
    let y := finiteDuhamel (∑ k, c k • V₀ k) (fun i => ∑ k, c k • V i k) x₀ w b
    y ≠ 0 ∧ ‖unitDirection y‖ = 1 ∧
      ‖unitDirection y - unitDirection x‖ ≤ ε / 50 ∧
      (99 / 100 : ℝ) / (C * g) ≤ ‖y‖ / (C * sourceBudget x₀ w b) := by
  dsimp only
  apply bounded_ratio_output_certificate x _ (sourceBudget x₀ w b) g C ε
    hx hB hg hC hε hεOne hBudget
  have hν : 0 ≤ precision ε g := le_of_lt (precision_pos ε g hε hg)
  calc
    _ ≤ 5 * precision ε g * sourceBudget x₀ w b :=
      common_tolerance_error_le c U₀ V₀ U V S₀ S x₀ x w b (precision ε g)
        hw hν hCoeff hLCHS₀ hLCHS hSimulation₀ hSimulation hQuadrature
    _ ≤ 10 * precision ε g * sourceBudget x₀ w b := by
      nlinarith [mul_nonneg hν (le_of_lt hB)]

end ComplexSource
end
end SparseHamiltonian.ODEStateNormalization
