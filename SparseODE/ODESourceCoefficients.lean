import SparseODE.ODEJointSourceLCU

/-!
# Product coefficients for the source and Hamiltonian-node registers

Nonnegative source weights of mass one can be folded into the complex LCHS
coefficients without increasing their absolute mass. The same product-index
sum combines all prepared source vectors. These identities require neither
division by a source norm nor a nonzero coefficient, so zero source weights
and zero LCHS coefficients are included.

The uniform-error theorem below transports a stated operator approximation
to the normalized source sum. It does not assert the Gaussian approximation
or provide a source-state oracle; those obligations remain separate.

-/

namespace SparseHamiltonian.ODESourceCoefficients

noncomputable section
open ContinuousLinearMap
open scoped BigOperators

variable {σ ι : Type*} [Fintype σ] [Fintype ι]

/-- One coefficient table indexed by a source label and an LCHS node. -/
def productCoeff (w : σ → ℝ) (c : ι → ℂ) (j : σ × ι) : ℂ :=
  (w j.1 : ℂ) * c j.2

/-- Absolute coefficient mass factors exactly for nonnegative source weights. -/
theorem coefficientMass_product (w : σ → ℝ) (c : ι → ℂ)
    (hw : ∀ a, 0 ≤ w a) :
    ODECoherentLCU.coefficientMass (productCoeff w c) =
      (∑ a, w a) * ODECoherentLCU.coefficientMass c := by
  unfold ODECoherentLCU.coefficientMass
  rw [Fintype.sum_prod_type]
  simp only [productCoeff, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (hw _)]
  calc
    (∑ a, ∑ i, w a * ‖c i‖) = ∑ a, w a * ∑ i, ‖c i‖ := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.mul_sum]
    _ = (∑ a, w a) * ∑ i, ‖c i‖ := by rw [Finset.sum_mul]

/-- A probability distribution over source labels preserves the LCHS mass. -/
theorem coefficientMass_normalized (w : σ → ℝ) (c : ι → ℂ)
    (hw : ∀ a, 0 ≤ w a) (hSum : ∑ a, w a = 1) :
    ODECoherentLCU.coefficientMass (productCoeff w c) =
      ODECoherentLCU.coefficientMass c := by
  rw [coefficientMass_product w c hw, hSum, one_mul]

/-- In particular, the padding normalization three is unchanged. -/
theorem coefficientMass_three (w : σ → ℝ) (c : ι → ℂ)
    (hw : ∀ a, 0 ≤ w a) (hSum : ∑ a, w a = 1)
    (hc : ODECoherentLCU.coefficientMass c = 3) :
    ODECoherentLCU.coefficientMass (productCoeff w c) = 3 := by
  rw [coefficientMass_normalized w c hw hSum, hc]

section Vectors

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Flattening the two public labels preserves the vector combination exactly. -/
theorem weighted_sum (w : σ → ℝ) (c : ι → ℂ) (v : σ → ι → E) :
    (∑ j : σ × ι, productCoeff w c j • v j.1 j.2) =
      ∑ a, (w a : ℂ) • ∑ i, c i • v a i := by
  rw [Fintype.sum_prod_type]
  simp only [productCoeff, mul_smul, Finset.smul_sum]

/-- The product-index target is the source sum of the LCHS operator sums.
The vectors `v a` may be supplied by arbitrary source-state preparations. -/
theorem target_sum (w : σ → ℝ) (c : ι → ℂ)
    (U : σ → ι → E →L[ℂ] E) (v : σ → E) :
    (∑ j : σ × ι, productCoeff w c j • U j.1 j.2 (v j.1)) =
      ∑ a, (w a : ℂ) • ((∑ i, c i • U a i) (v a)) := by
  rw [weighted_sum w c (fun a i => U a i (v a))]
  simp only [_root_.sum_apply, smul_apply]

/-- A uniform operator error passes to the normalized source sum without a
factor depending on the number of sources or Hamiltonian nodes. -/
theorem uniform_error (w : σ → ℝ) (c : ι → ℂ)
    (U : σ → ι → E →L[ℂ] E) (S : σ → E →L[ℂ] E)
    (v : σ → E) (δ : ℝ)
    (hw : ∀ a, 0 ≤ w a) (hSum : ∑ a, w a = 1)
    (hv : ∀ a, ‖v a‖ = 1)
    (hError : ∀ a, ‖(∑ i, c i • U a i) - S a‖ ≤ δ) :
    ‖(∑ j : σ × ι, productCoeff w c j • U j.1 j.2 (v j.1)) -
        ∑ a, (w a : ℂ) • S a (v a)‖ ≤ δ := by
  have hMass : (∑ a, ‖(w a : ℂ)‖) = 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw _)] using hSum
  have hApplied (a : σ) :
      ‖(∑ i, c i • U a i) (v a) - S a (v a)‖ ≤ δ := by
    calc
      _ ≤ δ * ‖v a‖ := ODEErrorBudget.applied_error_le
        (∑ i, c i • U a i) (S a) (v a) δ (hError a)
      _ = δ := by rw [hv a, mul_one]
  rw [target_sum w c U v]
  calc
    _ ≤ (∑ a, ‖(w a : ℂ)‖) * δ :=
      ODEErrorBudget.lcu_uniform_error_le (fun a => (w a : ℂ))
        (fun a => (∑ i, c i • U a i) (v a)) (fun a => S a (v a)) δ hApplied
    _ = δ := by rw [hMass, one_mul]

/-- Restoring the source budget costs exactly that budget in the error bound.
For the LCHS allocation, instantiate `δ` with `2 * ν`. -/
theorem scaled_uniform_error (w : σ → ℝ) (c : ι → ℂ)
    (U : σ → ι → E →L[ℂ] E) (S : σ → E →L[ℂ] E)
    (v : σ → E) (B δ : ℝ)
    (hw : ∀ a, 0 ≤ w a) (hSum : ∑ a, w a = 1)
    (hv : ∀ a, ‖v a‖ = 1) (hB : 0 ≤ B)
    (hError : ∀ a, ‖(∑ i, c i • U a i) - S a‖ ≤ δ) :
    ‖(B : ℂ) • (∑ j : σ × ι, productCoeff w c j • U j.1 j.2 (v j.1)) -
        (B : ℂ) • (∑ a, (w a : ℂ) • S a (v a))‖ ≤ B * δ := by
  rw [← smul_sub, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hB]
  exact mul_le_mul_of_nonneg_left (uniform_error w c U S v δ hw hSum hv hError) hB

end Vectors
end
end SparseHamiltonian.ODESourceCoefficients
