import SparseODE.ODEPrimitiveEndpoint

/-!
# Coefficient padding with a common source duration

The previously proved cancelling-pair construction fills the coefficient
mass to three. Here its two extra nodes both select frequency zero while
retaining the source branch's duration. Their evolutions agree and their
opposite coefficients cancel; neither evolution needs to be the identity.
Thus the source endpoint can keep one common duration for all frequency
labels, including the two added labels.

-/

namespace SparseHamiltonian.ODESourcePadding

noncomputable section
open ContinuousLinearMap NativeSparseBlockEncoding
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- Two equal added node values with opposite coefficients contribute zero
for any complex-linear combination, independently of the selected operator. -/
theorem weighted_node_sum_eq {V : Type*} [AddCommGroup V] [Module ℂ V]
    (c : ι → ℂ) (α : ℝ) (k : ι → ℝ) (U : ℝ → V) :
    (∑ i : ι ⊕ Bool,
      ODECoefficientPadding.paddedCoefficient c α i •
        U (ODECoefficientPadding.paddedNodes k i)) = ∑ i, c i • U (k i) := by
  simp only [Fintype.sum_sum_type, Fintype.sum_bool,
    ODECoefficientPadding.paddedCoefficient, ODECoefficientPadding.paddedNodes,
    neg_smul, neg_add_cancel, add_zero]

section NativeEvolution

variable {X n Z : Type*} [DecidableEq ι] [Fintype n] [DecidableEq n]
  [Fintype Z] [AddCommGroup Z] [DecidableEq Z] {s : ℕ}

omit [DecidableEq ι] [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- Retaining the same duration on both padding nodes preserves the finite
Hamiltonian sum exactly. This differs from zero-duration identity padding
only in the chosen, mutually cancelling operator on the added labels. -/
theorem finite_sum_eq (D : Data X n Z s) (c : ι → ℂ) (α : ℝ)
    (k : ι → ℝ) (u : ℝ) (x : X) :
    ODENativeLCU.finiteSum D (ODECoefficientPadding.paddedNodes k)
      (fun _ : ι ⊕ Bool => u) (ODECoefficientPadding.paddedCoefficient c α) x =
      ODENativeLCU.finiteSum D k (fun _ : ι => u) c x := by
  unfold ODENativeLCU.finiteSum ODENativeLCU.branchEvolution
  exact weighted_node_sum_eq c α k (fun r : ℝ =>
    NormedSpace.exp ((-Complex.I * (u : ℂ)) • SparseStateOverlap.matrixOperator
      (ODEMatrixEnergy.lchsHamiltonian (D.matrix x) r)))

omit [DecidableEq ι] [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- The common-duration padding identity on each source slice of the actual
joint source/frequency register. No assumption on the source label or its
duration is needed for cancellation. Bounds on durations are unchanged. -/
theorem branch_sum_eq {σ : Type*} [Fintype σ] [DecidableEq σ]
    (D : Data X n Z s) (c : ι → ℂ) (α : ℝ) (k : ι → ℝ)
    (u : σ → ℝ) (x : X) (a : σ) :
    (∑ i : ι ⊕ Bool, ODECoefficientPadding.paddedCoefficient c α i •
      ODENativeLCU.branchEvolution D
        (fun j : σ × (ι ⊕ Bool) => ODECoefficientPadding.paddedNodes k j.2)
        (fun j : σ × (ι ⊕ Bool) => u j.1) x (a, i)) =
      ODENativeLCU.finiteSum D k (fun _ : ι => u a) c x := by
  change ODENativeLCU.finiteSum D (ODECoefficientPadding.paddedNodes k)
    (fun _ : ι ⊕ Bool => u a) (ODECoefficientPadding.paddedCoefficient c α) x = _
  exact finite_sum_eq D c α k (u a) x

end NativeEvolution
end
end SparseHamiltonian.ODESourcePadding
