import SparseLinearSystems.Foundations.Cayley

/-!
# Dilation and regularization: algebraic identities

The algebra of equations `qls:eq:regularization` and
`qls:eq:regularizedsquare` on algebraic product modules: the dilation
`[[0, A], [A', 0]]`, the signed diagonal `Z ⊗ B`, the exchange `X` and the
regularized operator `a (Z ⊗ B) + σ X`, whose square is block diagonal
(`regularized_square`, `regularized_real_square`).  No norm is involved; the
Hilbert-space versions, with the adjoint as second map of the dilation, are in
`Foundations.HilbertRegularization`.
-/

namespace SparseLinearSystems.Regularization

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The off-diagonal dilation of two linear maps. -/
def dilation (A Aadj : V →ₗ[ℂ] V) : V × V →ₗ[ℂ] V × V where
  toFun v := (A v.2, Aadj v.1)
  map_add' v w := by
    apply Prod.ext <;> simp
  map_smul' c v := by
    apply Prod.ext <;> simp

/-- Its square separates the two ordered products; this does not require
the maps to commute. -/
theorem dilation_square (A Aadj : V →ₗ[ℂ] V) (v : V × V) :
    dilation A Aadj (dilation A Aadj v) =
      (A (Aadj v.1), Aadj (A v.2)) := rfl

/-- Invertible off-diagonal blocks give an invertible dilation. -/
def dilationEquiv (A Aadj : V ≃ₗ[ℂ] V) : (V × V) ≃ₗ[ℂ] (V × V) where
  toLinearMap := dilation A.toLinearMap Aadj.toLinearMap
  invFun v := (Aadj.symm v.2, A.symm v.1)
  left_inv v := by
    apply Prod.ext <;> simp [dilation]
  right_inv v := by
    apply Prod.ext <;> simp [dilation]

/-- Applying the inverse dilation to the first-block right-hand side
extracts exactly the inverse of the original map in the second block. -/
theorem dilation_inverse_on_left (A Aadj : V ≃ₗ[ℂ] V) (b : V) :
    (dilationEquiv A Aadj).symm (b, 0) = (0, A.symm b) := by
  change (Aadj.symm 0, A.symm b) = (0, A.symm b)
  rw [map_zero]

/-- The signed diagonal map corresponding to `Z ⊗ B`. -/
def signedDiagonal (B : V →ₗ[ℂ] V) : V × V →ₗ[ℂ] V × V where
  toFun v := (B v.1, -B v.2)
  map_add' v w := by
    apply Prod.ext
    · exact map_add B v.1 w.1
    · change -B (v.2 + w.2) = -B v.2 + -B w.2
      rw [map_add]
      abel
  map_smul' c v := by
    apply Prod.ext <;> simp

/-- The exchange of the two blocks corresponding to `X ⊗ I`. -/
def exchange : V × V →ₗ[ℂ] V × V where
  toFun v := (v.2, v.1)
  map_add' _v _w := rfl
  map_smul' _c _v := rfl

/-- The two Pauli block maps anticommute. -/
theorem signedDiagonal_exchange (B : V →ₗ[ℂ] V) (v : V × V) :
    signedDiagonal B (exchange v) = -exchange (signedDiagonal B v) := by
  apply Prod.ext
  · change B v.2 = -(-B v.2)
    rw [neg_neg]
  · rfl

/-- Exchanging twice is the identity. -/
theorem exchange_square (v : V × V) : exchange (exchange v) = v := by
  cases v
  rfl

/-- Squaring the signed diagonal removes its sign. -/
theorem signedDiagonal_square (B : V →ₗ[ℂ] V) (v : V × V) :
    signedDiagonal B (signedDiagonal B v) = (B (B v.1), B (B v.2)) := by
  apply Prod.ext
  · rfl
  · change -B (-B v.2) = B (B v.2)
    rw [map_neg, neg_neg]

/-- The regularized block map, initially with arbitrary complex weights. -/
def regularized (B : V →ₗ[ℂ] V) (a σ : ℂ) : V × V →ₗ[ℂ] V × V :=
  a • signedDiagonal B + σ • exchange

/-- The cross terms cancel exactly; no spectral assertion is needed. -/
theorem regularized_square (B : V →ₗ[ℂ] V) (a σ : ℂ) (v : V × V) :
    regularized B a σ (regularized B a σ v) =
      (a ^ 2 • B (B v.1) + σ ^ 2 • v.1,
       a ^ 2 • B (B v.2) + σ ^ 2 • v.2) := by
  apply Prod.ext
  · change
      a • B (a • B v.1 + σ • v.2) +
        σ • (a • (-B v.2) + σ • v.1) =
      a ^ 2 • B (B v.1) + σ ^ 2 • v.1
    simp only [map_add, map_smul]
    module
  · change
      a • (-B (a • (-B v.2) + σ • v.1)) +
        σ • (a • B v.1 + σ • v.2) =
      a ^ 2 • B (B v.2) + σ ^ 2 • v.2
    simp only [map_add, map_smul, map_neg]
    module

omit [AddCommGroup V] [Module ℂ V] in
/-- The public real regularization weights lie on the unit circle. -/
theorem regularization_weight_identity (σ : ℝ) (hσ₀ : 0 ≤ σ) (hσ₁ : σ ≤ 1) :
    Real.sqrt (1 - σ ^ 2) ^ 2 + σ ^ 2 = 1 := by
  have hnonneg : 0 ≤ 1 - σ ^ 2 := by
    nlinarith [mul_self_le_mul_self hσ₀ hσ₁]
  rw [Real.sq_sqrt hnonneg]
  ring

/-- The manuscript's regularized-square formula, with the real weights
embedded into the complex scalar field. -/
theorem regularized_real_square (B : V →ₗ[ℂ] V) (σ : ℝ)
    (hσ₀ : 0 ≤ σ) (hσ₁ : σ ≤ 1) (v : V × V) :
    regularized B (Real.sqrt (1 - σ ^ 2) : ℂ) (σ : ℂ)
      (regularized B (Real.sqrt (1 - σ ^ 2) : ℂ) (σ : ℂ) v) =
      (((1 - σ ^ 2 : ℝ) : ℂ) • B (B v.1) + ((σ ^ 2 : ℝ) : ℂ) • v.1,
       ((1 - σ ^ 2 : ℝ) : ℂ) • B (B v.2) + ((σ ^ 2 : ℝ) : ℂ) • v.2) := by
  have hnonneg : 0 ≤ 1 - σ ^ 2 := by
    nlinarith [mul_self_le_mul_self hσ₀ hσ₁]
  have hsquare : (Real.sqrt (1 - σ ^ 2) : ℂ) ^ 2 = ((1 - σ ^ 2 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hnonneg]
  have h := regularized_square B (Real.sqrt (1 - σ ^ 2) : ℂ) (σ : ℂ) v
  rw [hsquare] at h
  simpa only [Complex.ofReal_pow] using h

end
end SparseLinearSystems.Regularization
