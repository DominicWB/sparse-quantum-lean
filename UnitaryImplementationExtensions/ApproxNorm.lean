import UnitaryImplementationExtensions.ApproxData

set_option autoImplicit false

/-!
# Norm estimates for dilations of approximate entry tables

The estimates of the proof of corollary `hs:cor:unitary` in the manuscript: if every represented
entry is within `δ` of the unitary target, the two Hermitian dilations differ by at most `N δ` in
operator norm (row and column absolute sums, `SparseValuePrecision.norm_matrixOperator_le_nonneg`),
the dilation of the target has norm at most one, and hence the dilation of the represented matrix
has norm at most `2` once `N δ ≤ 1`.
-/

namespace UnitaryImplementationExtensions.ApproxNorm

noncomputable section
open SparseHamiltonian
open ContinuousLinearMap OracleCircuit ApproxData
open scoped BigOperators InnerProduct

variable {X n Z : Type*} [Fintype n]

/-- An entrywise bound `δ` gives the operator bound `N δ` for the dilation. -/
theorem norm_dilation_le (M : Matrix n n ℂ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hM : ∀ i j, ‖M i j‖ ≤ δ) :
    ‖SparseStateOverlap.matrixOperator (dilation M)‖ ≤ (Fintype.card n : ℝ) * δ := by
  have hsum : ∀ f : n → ℂ, (∀ j, ‖f j‖ ≤ δ) →
      ∑ j, ‖f j‖ ≤ (Fintype.card n : ℝ) * δ := by
    intro f hf
    calc ∑ j, ‖f j‖ ≤ ∑ _j : n, δ := Finset.sum_le_sum fun j _ => hf j
      _ = (Fintype.card n : ℝ) * δ := by simp [Finset.card_univ]
  apply SparseValuePrecision.norm_matrixOperator_le_nonneg _ _
    (mul_nonneg (Nat.cast_nonneg _) hδ)
  · rintro ⟨b, i⟩
    rw [Fintype.sum_prod_type, Fintype.sum_bool]
    cases b <;> simp [dilation] <;> exact hsum _ fun j => hM _ _
  · rintro ⟨c, j⟩
    rw [Fintype.sum_prod_type, Fintype.sum_bool]
    cases c <;> simp [dilation] <;> exact hsum _ fun i => hM _ _

/-- The dilation is self-adjoint as an operator. -/
theorem star_matrixOperator_dilation (M : Matrix n n ℂ) :
    star (SparseStateOverlap.matrixOperator (dilation M)) =
      SparseStateOverlap.matrixOperator (dilation M) :=
  SparseValuePrecision.matrixOperator_star_eq _ (dilation_hermitian M)

/-- The dilation of a unitary target is a contraction. -/
theorem norm_target_dilation_le_one (D : ApproxData.Data X n Z) (x : X) :
    ‖SparseStateOverlap.matrixOperator (dilation (D.target x))‖ ≤ 1 := by
  have hsq := UnitaryEntryData.dilation_sq (targetData D) x
  have hstar := star_matrixOperator_dilation (D.target x)
  rw [target_dilation_eq] at hstar ⊢
  have hU : IsUnitary (SparseStateOverlap.matrixOperator
      (UnitaryEntryData.dilationMatrix (targetData D) x)) := by
    refine ⟨?_, ?_⟩ <;> rw [hstar] <;> exact hsq
  exact hU.norm_le_one

/-- Entrywise error `δ` gives dilation error at most `N δ`. -/
theorem dilation_error_le (D : ApproxData.Data X n Z) (x : X) (δ : ℝ) (hδ : 0 ≤ δ)
    (hEntry : ∀ i j, ‖represented D x i j - D.target x i j‖ ≤ δ) :
    ‖SparseStateOverlap.matrixOperator (dilation (represented D x)) -
      SparseStateOverlap.matrixOperator (dilation (D.target x))‖ ≤
        (Fintype.card n : ℝ) * δ := by
  rw [← SparseValuePrecision.matrixOperator_sub, dilation_sub]
  exact norm_dilation_le _ δ hδ hEntry

/-- With `N δ ≤ 1`, the represented dilation has operator norm at most `2`. -/
theorem norm_represented_dilation_le (D : ApproxData.Data X n Z) (x : X) (δ : ℝ)
    (hδ : 0 ≤ δ) (hEntry : ∀ i j, ‖represented D x i j - D.target x i j‖ ≤ δ)
    (hδN : (Fintype.card n : ℝ) * δ ≤ 1) :
    ‖SparseStateOverlap.matrixOperator (dilation (represented D x))‖ ≤ 2 := by
  have hErr := dilation_error_le D x δ hδ hEntry
  have hTarget := norm_target_dilation_le_one D x
  have hTri := norm_sub_norm_le
    (SparseStateOverlap.matrixOperator (dilation (represented D x)))
    (SparseStateOverlap.matrixOperator (dilation (D.target x)))
  linarith

end
end UnitaryImplementationExtensions.ApproxNorm
