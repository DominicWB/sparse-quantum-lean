import SparseODE.ImprovedODEQueryBudget

/-!
# Improved ODE vector-error and extraction budgets

The finite LCHS approximation contributes `2ν`, its simulated branches
contribute `3ν`, and the source quadrature contributes `ν B`.  The resulting
`6ν B` estimate controls the successful direction and gives the amplitude
interval needed for randomized amplification.  This file does not construct
that amplification circuit or the Gaussian LCHS quadrature.
-/

namespace SparseHamiltonian.ImprovedODEOutput

noncomputable section
open ODEErrorBudget ODEStateNormalization
open scoped BigOperators

section FiniteSource

variable {E ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable [Fintype ι] [Fintype κ]

/-- The improved manuscript allocates twice the common tolerance to LCHS.
All three approximation obligations are displayed rather than hidden. -/
theorem six_tolerance_error_le
    (c : κ → ℂ) (U₀ V₀ : κ → E →L[ℂ] E)
    (U V : ι → κ → E →L[ℂ] E)
    (S₀ : E →L[ℂ] E) (S : ι → E →L[ℂ] E)
    (x₀ x : E) (w : ι → ℝ) (b : ι → E) (ν : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hν : 0 ≤ ν) (hCoeff : ∑ k, ‖c k‖ ≤ 3)
    (hLCHS₀ : ‖(∑ k, c k • U₀ k) - S₀‖ ≤ 2 * ν)
    (hLCHS : ∀ i, ‖(∑ k, c k • U i k) - S i‖ ≤ 2 * ν)
    (hSimulation₀ : ∀ k, ‖V₀ k - U₀ k‖ ≤ ν)
    (hSimulation : ∀ i k, ‖V i k - U i k‖ ≤ ν)
    (hQuadrature : ‖finiteDuhamel S₀ S x₀ w b - x‖ ≤ ν * sourceBudget x₀ w b) :
    ‖finiteDuhamel (∑ k, c k • V₀ k) (fun i => ∑ k, c k • V i k) x₀ w b - x‖ ≤
      6 * ν * sourceBudget x₀ w b := by
  calc
    _ ≤ (2 * ν + 3 * ν) * sourceBudget x₀ w b + ν * sourceBudget x₀ w b :=
      lchs_source_error_le c U₀ V₀ U V S₀ S x₀ x w b 3 (2 * ν) ν
        (ν * sourceBudget x₀ w b) hw hν hCoeff hLCHS₀ hLCHS
        hSimulation₀ hSimulation hQuadrature
    _ = _ := by ring

end FiniteSource

section Normalization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
/-- A known upper bound on the source-to-output ratio suffices for precision
selection. The exact ratio is never required as classical input. -/
theorem relative_budget (x : E) (B g ε : ℝ) (hg : 1 ≤ g)
    (hε : 0 < ε) (hBudget : B ≤ g * ‖x‖) :
    6 * ImprovedODEQueryBudget.precision g ε * B ≤ (ε / 1000) * ‖x‖ := by
  have hg0 : 0 < g := by linarith
  have hν := ImprovedODEQueryBudget.precision_pos g ε hg hε
  calc
    _ ≤ 6 * ImprovedODEQueryBudget.precision g ε * (g * ‖x‖) :=
      mul_le_mul_of_nonneg_left hBudget (by positivity)
    _ = (3 * ε / 5000) * ‖x‖ := by
      unfold ImprovedODEQueryBudget.precision
      field_simp [hg0.ne']
      ring
    _ ≤ (ε / 1000) * ‖x‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg x)
      linarith

/-- The implemented successful vector has a well-defined direction, small
normalized error, and amplitude between `1/(4g)` and `1/2`. This certifies
the input promises for a later amplification theorem, not its execution. -/
theorem output_certificate (x y : E) (B g ε : ℝ)
    (hx : x ≠ 0) (hg : 1 ≤ g) (hε : 0 < ε) (hεHalf : ε ≤ 1 / 2)
    (hNorm : ‖x‖ ≤ B) (hBudget : B ≤ g * ‖x‖)
    (hError : ‖y - x‖ ≤ 6 * ImprovedODEQueryBudget.precision g ε * B) :
    y ≠ 0 ∧ ‖unitDirection y‖ = 1 ∧
      ‖unitDirection y - unitDirection x‖ ≤ ε / 500 ∧
      1 / (4 * g) ≤ ‖y‖ / (3 * B) ∧ ‖y‖ / (3 * B) < 1 / 2 := by
  have hg0 : 0 < g := by linarith
  have hB : 0 < B := (norm_pos_iff.mpr hx).trans_le hNorm
  have hRel : ‖y - x‖ ≤ (ε / 1000) * ‖x‖ :=
    hError.trans (relative_budget x B g ε hg hε hBudget)
  have hSmall : ε / 1000 < 1 := by linarith
  have hDirection := relative_error x y (ε / 1000) hx hSmall hRel
  have hLower := extraction_amplitude_lower_of_budget_le x y B g 3 (ε / 1000)
    hB hg0 (by norm_num) hSmall.le hBudget hRel
  have hνBound : ImprovedODEQueryBudget.precision g ε ≤ 1 / 10000 := by
    unfold ImprovedODEQueryBudget.precision
    apply (div_le_iff₀ (by positivity : 0 < 10000 * g)).2
    nlinarith
  have hUpper : ‖y‖ ≤ (1 + 6 * ImprovedODEQueryBudget.precision g ε) * B := by
    calc
      _ ≤ ‖y - x‖ + ‖x‖ := by
        simpa only [sub_zero] using norm_sub_le_norm_sub_add_norm_sub y x 0
      _ ≤ 6 * ImprovedODEQueryBudget.precision g ε * B + B :=
        add_le_add hError hNorm
      _ = _ := by ring
  refine ⟨hDirection.1, unitDirection_norm y hDirection.1, ?_, ?_, ?_⟩
  · convert hDirection.2 using 1; ring
  · calc
      1 / (4 * g) = (3 / 4 : ℝ) / (3 * g) := by
        field_simp [hg0.ne']
      _ ≤ (1 - ε / 1000) / (3 * g) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        linarith
      _ ≤ ‖y‖ / (3 * B) := hLower
  · apply (div_lt_iff₀ (by positivity : 0 < 3 * B)).2
    have hScale := mul_le_mul_of_nonneg_right hνBound hB.le
    nlinarith

end Normalization

section FiniteOutput

variable {E ι κ : Type*} [NormedAddCommGroup E]
variable [NormedSpace ℝ E] [NormedSpace ℂ E] [Fintype ι] [Fintype κ]

/-- Complete error and amplitude accounting for the concrete finite source
and LCHS sums. Gaussian approximation, Hamiltonian branches and quadrature
remain explicit certificates; no full ODE query theorem is asserted here. -/
theorem finite_lchs_output_certificate
    (c : κ → ℂ) (U₀ V₀ : κ → E →L[ℂ] E)
    (U V : ι → κ → E →L[ℂ] E)
    (S₀ : E →L[ℂ] E) (S : ι → E →L[ℂ] E)
    (x₀ x : E) (w : ι → ℝ) (b : ι → E) (g ε : ℝ)
    (hx : x ≠ 0) (hg : 1 ≤ g) (hε : 0 < ε) (hεHalf : ε ≤ 1 / 2)
    (hw : ∀ i, 0 ≤ w i) (hNorm : ‖x‖ ≤ sourceBudget x₀ w b)
    (hBudget : sourceBudget x₀ w b ≤ g * ‖x‖) (hCoeff : ∑ k, ‖c k‖ ≤ 3)
    (hLCHS₀ : ‖(∑ k, c k • U₀ k) - S₀‖ ≤ 2 * ImprovedODEQueryBudget.precision g ε)
    (hLCHS : ∀ i, ‖(∑ k, c k • U i k) - S i‖ ≤ 2 * ImprovedODEQueryBudget.precision g ε)
    (hSimulation₀ : ∀ k, ‖V₀ k - U₀ k‖ ≤ ImprovedODEQueryBudget.precision g ε)
    (hSimulation : ∀ i k, ‖V i k - U i k‖ ≤ ImprovedODEQueryBudget.precision g ε)
    (hQuadrature : ‖finiteDuhamel S₀ S x₀ w b - x‖ ≤
      ImprovedODEQueryBudget.precision g ε * sourceBudget x₀ w b) :
    let y := finiteDuhamel (∑ k, c k • V₀ k) (fun i => ∑ k, c k • V i k) x₀ w b
    y ≠ 0 ∧ ‖unitDirection y‖ = 1 ∧
      ‖unitDirection y - unitDirection x‖ ≤ ε / 500 ∧
      1 / (4 * g) ≤ ‖y‖ / (3 * sourceBudget x₀ w b) ∧
      ‖y‖ / (3 * sourceBudget x₀ w b) < 1 / 2 := by
  dsimp only
  apply output_certificate x _ (sourceBudget x₀ w b) g ε
    hx hg hε hεHalf hNorm hBudget
  exact six_tolerance_error_le c U₀ V₀ U V S₀ S x₀ x w b
    (ImprovedODEQueryBudget.precision g ε) hw
    (ImprovedODEQueryBudget.precision_pos g ε hg hε).le
    hCoeff hLCHS₀ hLCHS hSimulation₀ hSimulation hQuadrature

end FiniteOutput
end
end SparseHamiltonian.ImprovedODEOutput
