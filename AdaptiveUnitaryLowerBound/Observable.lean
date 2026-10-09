import AdaptiveHamiltonianLowerBound.Readout

set_option autoImplicit false

/-!
# The pair observable of two marked elements

The reduction of the lower half of corollary `hs:cor:unitary` of the manuscript
(lines 1711-1718: `U_m |0⟩ = |m⟩`, so a constant-error implementation solves
unstructured search) distinguishes the outputs of two instances `m ≠ m'` with
the system observable `D_{m,m'} = |m⟩⟨m| - |m'⟩⟨m'|` on `ℂ^N`
(`pairObs`). It is self-adjoint (`isSelfAdjoint_pairObs`), a contraction
(`norm_pairObs_le`), and its ideal expectations are `+1` on `|m⟩` and `-1` on
`|m'⟩` (`pairObs_expect_left`, `pairObs_expect_right`).
-/

namespace AdaptiveUnitaryLowerBound.Observable

noncomputable section
open SparseHamiltonian
open scoped InnerProduct InnerProductSpace

/-- The basis vector `|m⟩` of `ℂ^N`. -/
abbrev ket {N : ℕ} (m : Fin N) : EuclideanSpace ℂ (Fin N) := EuclideanSpace.single m 1

/-- **The pair observable** `D_{m,m'} = |m⟩⟨m| - |m'⟩⟨m'|`. -/
def pairObs {N : ℕ} (m m' : Fin N) :
    EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N) :=
  ODEMixedOutput.pureOperator (ket m) - ODEMixedOutput.pureOperator (ket m')

/-- The pair observable is self-adjoint. -/
theorem isSelfAdjoint_pairObs {N : ℕ} (m m' : Fin N) : IsSelfAdjoint (pairObs m m') :=
  (ODEMixedOutput.pureOperator_positive (ket m)).isSelfAdjoint.sub
    (ODEMixedOutput.pureOperator_positive (ket m')).isSelfAdjoint

/-- The pair observable is a contraction. -/
theorem norm_pairObs_le {N : ℕ} (m m' : Fin N) : ‖pairObs m m'‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
  rw [one_mul]
  have hcoord : ∀ i : Fin N, ‖(pairObs m m' v) i‖ ^ 2 ≤ ‖v i‖ ^ 2 := by
    intro i
    simp only [pairObs, ODEMixedOutput.pureOperator, sub_apply,
      InnerProductSpace.rankOne_apply, EuclideanSpace.inner_single_left, map_one, one_mul,
      PiLp.sub_apply, PiLp.smul_apply, PiLp.single_apply, smul_eq_mul, mul_ite, mul_one,
      mul_zero]
    by_cases him : i = m <;> by_cases him' : i = m' <;> subst_vars <;> simp [*]
  have hsq : ‖pairObs m m' v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    exact Finset.sum_le_sum fun i _ => hcoord i
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

/-- The ideal expectation of the pair observable on `|m⟩` is `1`. -/
theorem pairObs_expect_left {N : ℕ} {m m' : Fin N} (h : m ≠ m') :
    (⟪ket m, pairObs m m' (ket m)⟫_ℂ).re = 1 := by
  simp [pairObs, ODEMixedOutput.pureOperator, InnerProductSpace.rankOne_apply,
    EuclideanSpace.inner_single_left, Ne.symm h]

/-- The ideal expectation of the pair observable on `|m'⟩` is `-1`. -/
theorem pairObs_expect_right {N : ℕ} {m m' : Fin N} (h : m ≠ m') :
    (⟪ket m', pairObs m m' (ket m')⟫_ℂ).re = -1 := by
  simp [pairObs, ODEMixedOutput.pureOperator, InnerProductSpace.rankOne_apply,
    EuclideanSpace.inner_single_left, h]

end
end AdaptiveUnitaryLowerBound.Observable
