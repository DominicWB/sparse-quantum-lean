import SparseLinearSystems.Foundations.FourBranchCompression
import SparseLinearSystems.Spectral.Diagonal

/-!
# Functional-calculus facts for the Cayley transform

`HilbertCayley.cayley K = (K + i)(K - i)⁻¹` for a self-adjoint `K` on a
finite-dimensional space.  These identities identify the Cayley transform of
a block or conjugated generator with the corresponding combination of known
Cayley transforms, using only uniqueness of inverses:

* `cayley_eq_of_right_inverse`: any right inverse of `K - i` gives the Cayley map;
* `cayley_blockMap`: block-diagonal generators;
* `cayley_fourDiagonal`: the four-branch generator;
* `cayley_conj`: unitary conjugation;
* `cayley_zero`: `cayley 0 = -1`.
-/

namespace SparseLinearSystems.CayleyAlgebra

noncomputable section
open ContinuousLinearMap HilbertBlocks
open scoped InnerProduct

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V]

/-- Any right inverse of the denominator gives the Cayley transform. -/
theorem cayley_eq_of_right_inverse (K : V →L[ℂ] V) (hK : (K†) = K) (S : V →L[ℂ] V)
    (hS : (K - Complex.I • (1 : V →L[ℂ] V)) * S = 1) :
    HilbertCayley.cayley K hK = (K + Complex.I • (1 : V →L[ℂ] V)) * S := by
  have hinv : HilbertCayley.denominatorInverse K hK = S :=
    Diagonal.inverse_unique (HilbertCayley.denominator K) _ S
      (HilbertCayley.inverse_mul_denominator K hK) hS
  rw [HilbertCayley.cayley, Cayley.cayleyAction, hinv]

theorem cayley_mul_denominator (K : V →L[ℂ] V) (hK : (K†) = K) :
    (K - Complex.I • (1 : V →L[ℂ] V)) * HilbertCayley.denominatorInverse K hK = 1 :=
  HilbertCayley.denominator_mul_inverse K hK

/-- `cayley 0 = -1`. -/
theorem cayley_zero (h0 : ((0 : V →L[ℂ] V)†) = 0) : HilbertCayley.cayley 0 h0 = -1 := by
  rw [cayley_eq_of_right_inverse 0 h0 (Complex.I • (1 : V →L[ℂ] V))]
  · simp only [zero_add, smul_mul_smul_comm, one_mul, Complex.I_mul_I, neg_smul, one_smul]
  · simp only [zero_sub, neg_mul, smul_mul_smul_comm, one_mul, Complex.I_mul_I, neg_smul,
      one_smul, neg_neg]

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W]

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] in
theorem blockMap_selfAdjoint (K₁ : V →L[ℂ] V) (K₂ : W →L[ℂ] W) (h₁ : (K₁†) = K₁) (h₂ : (K₂†) = K₂) :
    ((blockMap K₁ 0 0 K₂)†) = blockMap K₁ 0 0 K₂ := by
  rw [block_adjoint, h₁, h₂]
  simp only [map_zero]

omit [FiniteDimensional ℂ V] [CompleteSpace V] [FiniteDimensional ℂ W] [CompleteSpace W] in
theorem blockMap_mul_diag (A₁ B₁ : V →L[ℂ] V) (A₂ B₂ : W →L[ℂ] W) :
    blockMap A₁ 0 0 A₂ * blockMap B₁ 0 0 B₂ = blockMap (A₁ * B₁) 0 0 (A₂ * B₂) := by
  rw [mul_def, block_comp]
  simp only [comp_zero, zero_comp, add_zero, zero_add]
  rfl

omit [FiniteDimensional ℂ V] [CompleteSpace V] [FiniteDimensional ℂ W] [CompleteSpace W] in
theorem blockMap_one' : blockMap (1 : V →L[ℂ] V) 0 0 (1 : W →L[ℂ] W) = 1 :=
  block_identity

omit [FiniteDimensional ℂ V] [CompleteSpace V] [FiniteDimensional ℂ W] [CompleteSpace W] in
theorem blockMap_sub_I (A : V →L[ℂ] V) (B : W →L[ℂ] W) (c : ℂ) :
    blockMap A 0 0 B - c • (1 : WithLp 2 (V × W) →L[ℂ] WithLp 2 (V × W)) =
      blockMap (A - c • 1) 0 0 (B - c • 1) := by
  ext x : 1
  apply prodExt <;> simp [blockMap_apply]

omit [FiniteDimensional ℂ V] [CompleteSpace V] [FiniteDimensional ℂ W] [CompleteSpace W] in
theorem blockMap_add_I (A : V →L[ℂ] V) (B : W →L[ℂ] W) (c : ℂ) :
    blockMap A 0 0 B + c • (1 : WithLp 2 (V × W) →L[ℂ] WithLp 2 (V × W)) =
      blockMap (A + c • 1) 0 0 (B + c • 1) := by
  ext x : 1
  apply prodExt <;> simp [blockMap_apply]

/-- Cayley transform of a block-diagonal generator. -/
theorem cayley_blockMap (K₁ : V →L[ℂ] V) (K₂ : W →L[ℂ] W) (h₁ : (K₁†) = K₁) (h₂ : (K₂†) = K₂)
    (h : ((blockMap K₁ 0 0 K₂)†) = blockMap K₁ 0 0 K₂) :
    HilbertCayley.cayley (blockMap K₁ 0 0 K₂) h =
      blockMap (HilbertCayley.cayley K₁ h₁) 0 0 (HilbertCayley.cayley K₂ h₂) := by
  rw [cayley_eq_of_right_inverse _ h (blockMap (HilbertCayley.denominatorInverse K₁ h₁) 0 0
    (HilbertCayley.denominatorInverse K₂ h₂))]
  · rw [blockMap_add_I, blockMap_mul_diag]
    rfl
  · rw [blockMap_sub_I, blockMap_mul_diag]
    have e1 := HilbertCayley.denominator_mul_inverse K₁ h₁
    have e2 := HilbertCayley.denominator_mul_inverse K₂ h₂
    simp only [HilbertCayley.denominator] at e1 e2
    rw [e1, e2, blockMap_one']

/-- Cayley transform under unitary conjugation. -/
theorem cayley_conj (K : V →L[ℂ] V) (hK : (K†) = K) (U : V →L[ℂ] V)
    (hU : (U†) * U = 1 ∧ U * (U†) = 1) (h : ((U * K * (U†))†) = U * K * (U†)) :
    HilbertCayley.cayley (U * K * (U†)) h = U * HilbertCayley.cayley K hK * (U†) := by
  rw [cayley_eq_of_right_inverse _ h (U * HilbertCayley.denominatorInverse K hK * (U†))]
  · rw [HilbertCayley.cayley, Cayley.cayleyAction]
    have e : U * K * (U†) + Complex.I • (1 : V →L[ℂ] V) = U * (K + Complex.I • 1) * (U†) := by
      rw [mul_add, add_mul, mul_smul_comm, mul_one, smul_mul_assoc, hU.2]
    rw [e]
    simp only [mul_assoc]
    rw [← mul_assoc (U†) U, hU.1, one_mul]
  · have e : U * K * (U†) - Complex.I • (1 : V →L[ℂ] V) = U * (K - Complex.I • 1) * (U†) := by
      rw [mul_sub, sub_mul, mul_smul_comm, mul_one, smul_mul_assoc, hU.2]
    rw [e]
    have hd := HilbertCayley.denominator_mul_inverse K hK
    simp only [HilbertCayley.denominator] at hd
    calc U * (K - Complex.I • 1) * (U†) * (U * HilbertCayley.denominatorInverse K hK * (U†))
        = U * ((K - Complex.I • 1) * ((U†) * U) * HilbertCayley.denominatorInverse K hK) * (U†) := by
          simp only [mul_assoc]
      _ = 1 := by rw [hU.1, mul_one, hd, mul_one, hU.2]

end

end SparseLinearSystems.CayleyAlgebra
