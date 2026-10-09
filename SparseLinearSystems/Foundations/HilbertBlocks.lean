import SparseLinearSystems.Foundations.GeometricBudget

/-!
## Hilbert direct-sum block operators

These operators use the genuine Hilbert norm on `WithLp 2 (P × Q)`.
The rectangular adjoint identity is needed for the augmented system.
-/

namespace SparseLinearSystems.HilbertBlocks

noncomputable section
open ContinuousLinearMap
open scoped InnerProduct

section Normed

variable {P Q : Type*}
variable [NormedAddCommGroup P] [NormedSpace ℂ P]
variable [NormedAddCommGroup Q] [NormedSpace ℂ Q]

/-- A continuous block operator on the Hilbert direct sum. -/
def blockMap (A : P →L[ℂ] P) (B : Q →L[ℂ] P)
    (C : P →L[ℂ] Q) (D : Q →L[ℂ] Q) :
    WithLp 2 (P × Q) →L[ℂ] WithLp 2 (P × Q) :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ P Q).symm.toContinuousLinearMap ∘L
    ((A ∘L WithLp.fstL 2 ℂ P Q + B ∘L WithLp.sndL 2 ℂ P Q).prod
      (C ∘L WithLp.fstL 2 ℂ P Q + D ∘L WithLp.sndL 2 ℂ P Q))

@[simp] theorem blockMap_apply (A : P →L[ℂ] P) (B : Q →L[ℂ] P)
    (C : P →L[ℂ] Q) (D : Q →L[ℂ] Q) (x : WithLp 2 (P × Q)) :
    blockMap A B C D x =
      WithLp.toLp 2 (A x.fst + B x.snd, C x.fst + D x.snd) := rfl

/-- Composition keeps the usual four-block matrix multiplication rule. -/
theorem block_comp (A E : P →L[ℂ] P) (B F : Q →L[ℂ] P)
    (C G : P →L[ℂ] Q) (D H : Q →L[ℂ] Q) :
    blockMap A B C D ∘L blockMap E F G H =
      blockMap (A ∘L E + B ∘L G) (A ∘L F + B ∘L H)
        (C ∘L E + D ∘L G) (C ∘L F + D ∘L H) := by
  ext x
  simp only [comp_apply, blockMap_apply, WithLp.fst, WithLp.snd,
    map_add, add_apply]
  congr 1
  abel_nf

/-- Endomorphism notation for the equal-summand composition rule. -/
theorem block_mul (A B C D E F G H : P →L[ℂ] P) :
    blockMap A B C D * blockMap E F G H =
      blockMap (A * E + B * G) (A * F + B * H)
        (C * E + D * G) (C * F + D * H) := by
  exact block_comp A E B F C G D H

@[simp] theorem block_identity :
    blockMap (1 : P →L[ℂ] P) (0 : Q →L[ℂ] P)
      (0 : P →L[ℂ] Q) (1 : Q →L[ℂ] Q) = 1 := by
  ext x
  simp only [blockMap_apply, zero_apply, add_zero, zero_add]
  exact WithLp.toLp_ofLp 2 x

end Normed

section Adjoint

variable {P Q : Type*}
variable [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
variable [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] [CompleteSpace Q]

/-- The adjoint transposes the rectangular off-diagonal blocks. -/
theorem block_adjoint (A : P →L[ℂ] P) (B : Q →L[ℂ] P)
    (C : P →L[ℂ] Q) (D : Q →L[ℂ] Q) :
    (ContinuousLinearMap.adjoint (blockMap A B C D)) = blockMap (ContinuousLinearMap.adjoint A) (ContinuousLinearMap.adjoint C) (ContinuousLinearMap.adjoint B) (ContinuousLinearMap.adjoint D) := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℂ
  intro y
  rw [adjoint_inner_left]
  simp only [blockMap_apply, WithLp.prod_inner_apply, WithLp.fst, WithLp.snd,
    inner_add_left, inner_add_right, adjoint_inner_left]
  abel

end Adjoint
end
end SparseLinearSystems.HilbertBlocks
