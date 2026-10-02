import SparseHamiltonian.FullCoherentReuse

/-!
# Exact smoothing of typed reuse expressions

The signed average of the reuse public blocks equals the explicit smoothing
residual already bounded in operator norm. The actual reuse implementation is
connected separately; no circuit formula or operator norm is assumed here.
-/

namespace SparseHamiltonian.SmoothedReuse

noncomputable section
open ContinuousLinearMap
open FilterCoefficients
open scoped BigOperators InnerProduct

variable {P V : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- The public expression derived by the reuse recurrence. -/
def reuseExpression (U : P →L[ℂ] P) (B : V →L[ℂ] P) (Γ : P →L[ℂ] V)
    (D : V →L[ℂ] V) (n : ℕ) : P →L[ℂ] P :=
  U - B ∘L averagedGeometricFilter D n ∘L Γ

/-- The uncombined signed weights retain normalization exactly two. -/
def weightedReuse (a : ℕ → ℝ) (d : ℕ) (R : ℕ → P →L[ℂ] P) : P →L[ℂ] P :=
  ∑ j ∈ Finset.range (d + 1),
    (positiveWeight d a j • R (j + d) + negativeWeight d a j • R j)

omit [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P] [CompleteSpace V] in
/-- Real coefficient polynomials commute with the complex private operator. -/
theorem polynomial_commutes (a : ℕ → ℝ) (d : ℕ) (D : V →L[ℂ] V) :
    D * (∑ j ∈ Finset.range (d + 1), a j • D ^ j) =
      (∑ j ∈ Finset.range (d + 1), a j • D ^ j) * D := by
  simp only [Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc]
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun X : V →L[ℂ] V => a j • X) (Commute.self_pow D j).eq

omit [CompleteSpace P] [CompleteSpace V] in
/-- The normalized signed combination has exactly the intended public action
and a single filtered geometric error term. -/
theorem weighted_expression_eq (a : ℕ → ℝ) (d : ℕ) (hd : 0 < d)
    (hmass : ∑ j ∈ Finset.range (d + 1), a j = 1)
    (U : P →L[ℂ] P) (B : V →L[ℂ] P) (Γ : P →L[ℂ] V) (D : V →L[ℂ] V) :
    weightedReuse a d (reuseExpression U B Γ D) =
      U - B ∘L ((∑ j ∈ Finset.range (d + 1), a j • D ^ j) *
        averagedGeometricFilter D d) ∘L Γ := by
  have hs := smoothing_average_operator_identity (K := ℝ) a d D
  simp only [OperatorPolynomial.real_average_eq] at hs
  have hw := smoothing_signed_mass a d hd hmass
  have hterm (j : ℕ) :
      positiveWeight d a j • reuseExpression U B Γ D (j + d) +
        negativeWeight d a j • reuseExpression U B Γ D j =
      (positiveWeight d a j + negativeWeight d a j) • U -
        B ∘L (positiveWeight d a j • averagedGeometricFilter D (j + d) +
          negativeWeight d a j • averagedGeometricFilter D j) ∘L Γ := by
    simp only [reuseExpression, smul_sub, add_smul, comp_add, add_comp, comp_smul, smul_comp]
    abel
  rw [weightedReuse]
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, ← Finset.sum_smul, hw, one_smul, hs]
  congr 1
  ext x
  simp only [_root_.sum_apply, comp_apply, map_sum]

/-- The public error equals the already-defined smoothing residual. -/
theorem weighted_expression_residual (a : ℕ → ℝ) (d : ℕ) (hd : 0 < d)
    (hmass : ∑ j ∈ Finset.range (d + 1), a j = 1)
    (U : P →L[ℂ] P) (B : V →L[ℂ] P) (Γ : P →L[ℂ] V) (D : V →L[ℂ] V)
    (hExit : B = U ∘L (Γ† ∘L (1 - D))) :
    U - weightedReuse a d (reuseExpression U B Γ D) =
      smoothedTransducerResidual U Γ (∑ j ∈ Finset.range (d + 1), a j • D ^ j) D d := by
  rw [weighted_expression_eq a d hd hmass, sub_sub_cancel]
  have h := normalized_smoothing_cancellation U B Γ
    (∑ j ∈ Finset.range (d + 1), a j • D ^ j) D d hExit (polynomial_commutes a d D)
  simpa only [averagedGeometricFilter, mul_def, comp_smul, smul_comp, comp_assoc] using h

/-- Concrete averaging-polynomial coefficients produce the actual filter
power, connecting the signed weights to the established analytic norm bound. -/
theorem concrete_filter_residual (L k : ℕ) (hL : 1 ≤ L) (hd : 0 < k * (L - 1))
    (U : P →L[ℂ] P) (B : V →L[ℂ] P) (Γ : P →L[ℂ] V) (D : V →L[ℂ] V)
    (hExit : B = U ∘L (Γ† ∘L (1 - D))) :
    U - weightedReuse (AveragingPolynomial.filter L k).coeff (k * (L - 1))
      (reuseExpression U B Γ D) =
        smoothedTransducerResidual U Γ (averagedGeometricFilter D L ^ k) D (k * (L - 1)) := by
  rw [weighted_expression_residual _ _ hd (AveragingPolynomial.filter_coeff_sum L k hL)
    U B Γ D hExit, OperatorPolynomial.filter_operator_eq]

end
end SparseHamiltonian.SmoothedReuse
