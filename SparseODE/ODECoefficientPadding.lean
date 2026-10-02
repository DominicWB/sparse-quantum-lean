import SparseODE.ODENativeLCU

/-!
# Fixed normalization of finite complex LCHS coefficients

Two opposite coefficients on zero-duration identity branches fill unused
absolute coefficient mass. Both the exact finite operator sum and the
original node/duration bounds are preserved. The coherent simulator's query
bound has no branch-cardinality factor, so these branches need no extra
matrix-query multiplier.

-/

namespace SparseHamiltonian.ODECoefficientPadding

noncomputable section
open ContinuousLinearMap NativeSparseBlockEncoding
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- Opposite real coefficients fill the unused absolute coefficient mass. -/
def paddedCoefficient (c : ι → ℂ) (α : ℝ) : ι ⊕ Bool → ℂ
  | .inl i => c i
  | .inr false => ((α - ODECoherentLCU.coefficientMass c) / 2 : ℝ)
  | .inr true => -(((α - ODECoherentLCU.coefficientMass c) / 2 : ℝ) : ℂ)

/-- The padding branches both select the identity. -/
def paddedOperator {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (U : ι → H →L[ℂ] H) : ι ⊕ Bool → H →L[ℂ] H
  | .inl i => U i
  | .inr _ => 1

theorem coefficientMass_eq (c : ι → ℂ) (α : ℝ)
    (hc : ODECoherentLCU.coefficientMass c ≤ α) :
    ODECoherentLCU.coefficientMass (paddedCoefficient c α) = α := by
  have hδ : 0 ≤ (α - ODECoherentLCU.coefficientMass c) / 2 := by linarith
  change (∑ i : ι ⊕ Bool, ‖paddedCoefficient c α i‖) = α
  simp only [Fintype.sum_sum_type, Fintype.sum_bool, paddedCoefficient,
    norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hδ]
  change ODECoherentLCU.coefficientMass c +
    ((α - ODECoherentLCU.coefficientMass c) / 2 +
      (α - ODECoherentLCU.coefficientMass c) / 2) = α
  ring

theorem coefficientMass_pos (c : ι → ℂ) (α : ℝ)
    (hc : ODECoherentLCU.coefficientMass c ≤ α) (hα : 0 < α) :
    0 < ODECoherentLCU.coefficientMass (paddedCoefficient c α) := by
  rw [coefficientMass_eq c α hc]
  exact hα

/-- The two added branches cancel exactly, including their complex phases. -/
theorem padded_weighted_sum {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (c : ι → ℂ) (α : ℝ) (U : ι → H →L[ℂ] H) :
    ∑ i, paddedCoefficient c α i • paddedOperator U i = ∑ i, c i • U i := by
  simp only [Fintype.sum_sum_type, Fintype.sum_bool, paddedCoefficient,
    paddedOperator, neg_smul, neg_add_cancel, add_zero]

/-- A zero node is valid for either of the zero-duration padding branches. -/
def paddedNodes (k : ι → ℝ) : ι ⊕ Bool → ℝ
  | .inl i => k i
  | .inr _ => 0

/-- Both padding branches have zero evolution duration. -/
def paddedDurations (u : ι → ℝ) : ι ⊕ Bool → ℝ
  | .inl i => u i
  | .inr _ => 0

omit [Fintype ι] in
theorem paddedNodes_bound (k : ι → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hk : ∀ i, |k i| ≤ R) : ∀ i, |paddedNodes k i| ≤ R := by
  intro i
  cases i with
  | inl i => exact hk i
  | inr b => simpa only [paddedNodes, abs_zero] using hR

omit [Fintype ι] in
theorem paddedDurations_nonneg (u : ι → ℝ) (hu : ∀ i, 0 ≤ u i) :
    ∀ i, 0 ≤ paddedDurations u i := by
  intro i
  cases i with
  | inl i => exact hu i
  | inr b => exact le_refl 0

omit [Fintype ι] in
theorem paddedDurations_le (u : ι → ℝ) (T : ℝ) (hT : 0 ≤ T)
    (huT : ∀ i, u i ≤ T) : ∀ i, paddedDurations u i ≤ T := by
  intro i
  cases i with
  | inl i => exact huT i
  | inr b => exact hT

section NativeEvolution

variable {X n Z : Type*} [DecidableEq ι] [Fintype n] [DecidableEq n]
  [Fintype Z] [AddCommGroup Z] [DecidableEq Z] {s : ℕ}

omit [Fintype ι] [DecidableEq ι] [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- The simulator's actual exponential target gives the identity on padding. -/
theorem branchEvolution_eq_paddedOperator (D : Data X n Z s)
    (k u : ι → ℝ) (x : X) :
    ODENativeLCU.branchEvolution D (paddedNodes k) (paddedDurations u) x =
      paddedOperator (ODENativeLCU.branchEvolution D k u x) := by
  funext i
  cases i with
  | inl i => rfl
  | inr b =>
      simp only [ODENativeLCU.branchEvolution, paddedNodes, paddedDurations,
        paddedOperator, Complex.ofReal_zero, mul_zero]
      have hzero : (0 : ℂ) • SparseStateOverlap.matrixOperator
          (ODEMatrixEnergy.lchsHamiltonian (D.matrix x) 0) =
          (0 : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) := by
        apply ContinuousLinearMap.ext
        intro v
        apply PiLp.ext
        intro i
        simp only [_root_.smul_apply, PiLp.smul_apply, smul_eq_mul, zero_mul,
          zero_apply, PiLp.zero_apply]
      rw [hzero]
      exact NormedSpace.exp_zero

omit [DecidableEq ι] [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- Filling the coefficient mass does not change the physical finite sum. -/
theorem finiteSum_eq (D : Data X n Z s) (c : ι → ℂ) (α : ℝ)
    (k u : ι → ℝ) (x : X) :
    ODENativeLCU.finiteSum D (paddedNodes k) (paddedDurations u)
      (paddedCoefficient c α) x = ODENativeLCU.finiteSum D k u c x := by
  unfold ODENativeLCU.finiteSum
  rw [branchEvolution_eq_paddedOperator]
  exact padded_weighted_sum c α (ODENativeLCU.branchEvolution D k u x)

omit [DecidableEq ι] [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- In particular `α = 3` supplies a fixed normalization independent of the
coefficient table, even if its unpadded mass is zero. -/
theorem normalizedTarget_eq (D : Data X n Z s) (c : ι → ℂ) (α : ℝ)
    (hc : ODECoherentLCU.coefficientMass c ≤ α)
    (k u : ι → ℝ) (x : X) :
    ODENativeLCU.normalizedTarget D (paddedNodes k) (paddedDurations u)
      (paddedCoefficient c α) x =
        (α : ℂ)⁻¹ • ODENativeLCU.finiteSum D k u c x := by
  unfold ODENativeLCU.normalizedTarget ODEJointLCU.normalizedSum
  rw [coefficientMass_eq c α hc, branchEvolution_eq_paddedOperator,
    padded_weighted_sum]
  rfl

end NativeEvolution
end
end SparseHamiltonian.ODECoefficientPadding
