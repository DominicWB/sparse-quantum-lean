import SparseLowerBounds.Helpers.Chains.Kron

set_option synthInstance.maxHeartbeats 400000

section
/-!
# Helpers for `Hamiltonian/Chains`: block matrices on `clock × register`

Matrices on `I × J` read as `I × I` block matrices with `J × J` blocks through
Mathlib's `Matrix.comp`. Block-diagonal unitaries, their conjugation action on
a block matrix, and `B ⊗ I` as a block matrix; plus two `Finset` facts behind
the gauge-sign recursions.
-/

namespace SparseLowerBounds.Helpers.Chains

noncomputable section
open scoped Matrix Kronecker

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

omit [DecidableEq I] [DecidableEq J] in
/-- Block matrix product. -/
theorem comp_mul (M N : Matrix I I (Matrix J J ℂ)) :
    Matrix.comp I I J J ℂ (M * N) = Matrix.comp I I J J ℂ M * Matrix.comp I I J J ℂ N :=
  map_mul (Matrix.compRingEquiv I J ℂ) M N

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
/-- Conjugate transpose of a block matrix: transpose the blocks' positions and
conjugate-transpose each block. -/
theorem comp_conjTranspose (M : Matrix I I (Matrix J J ℂ)) :
    (Matrix.comp I I J J ℂ M)ᴴ = Matrix.comp I I J J ℂ (Matrix.of fun i k => (M k i)ᴴ) := by
  ext ⟨i, a⟩ ⟨k, b⟩
  simp [Matrix.comp_apply, Matrix.conjTranspose_apply]

omit [Fintype I] [Fintype J] [DecidableEq J] in
theorem of_conjTranspose_diagonal (V : I → Matrix J J ℂ) :
    (Matrix.of fun i k => (Matrix.diagonal V k i)ᴴ) = Matrix.diagonal fun i => (V i)ᴴ := by
  ext i k : 2
  by_cases h : i = k
  · subst h
    simp [Matrix.diagonal_apply_eq]
  · rw [Matrix.of_apply, Matrix.diagonal_apply_ne _ (Ne.symm h), Matrix.diagonal_apply_ne _ h,
      Matrix.conjTranspose_zero]

omit [DecidableEq J] in
/-- Conjugation of a block matrix by a block-diagonal matrix acts blockwise. -/
theorem conj_comp_diagonal (V : I → Matrix J J ℂ) (M : Matrix I I (Matrix J J ℂ)) :
    (Matrix.comp I I J J ℂ (Matrix.diagonal V))ᴴ * Matrix.comp I I J J ℂ M *
        Matrix.comp I I J J ℂ (Matrix.diagonal V) =
      Matrix.comp I I J J ℂ (Matrix.of fun i k => (V i)ᴴ * M i k * V k) := by
  rw [comp_conjTranspose, of_conjTranspose_diagonal, ← comp_mul, ← comp_mul]
  congr 1
  ext i k : 2
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.of_apply]

omit [DecidableEq J] in
/-- Conjugation the other way round. -/
theorem comp_diagonal_conj (V : I → Matrix J J ℂ) (M : Matrix I I (Matrix J J ℂ)) :
    Matrix.comp I I J J ℂ (Matrix.diagonal V) * Matrix.comp I I J J ℂ M *
        (Matrix.comp I I J J ℂ (Matrix.diagonal V))ᴴ =
      Matrix.comp I I J J ℂ (Matrix.of fun i k => V i * M i k * (V k)ᴴ) := by
  rw [comp_conjTranspose, of_conjTranspose_diagonal, ← comp_mul, ← comp_mul]
  congr 1
  ext i k : 2
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.of_apply]

/-- A block-diagonal matrix with unitary blocks is unitary. -/
theorem comp_diagonal_mem_unitaryGroup (V : I → Matrix J J ℂ)
    (hV : ∀ i, V i ∈ Matrix.unitaryGroup J ℂ) :
    Matrix.comp I I J J ℂ (Matrix.diagonal V) ∈ Matrix.unitaryGroup (I × J) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, comp_conjTranspose,
    of_conjTranspose_diagonal, ← comp_mul, Matrix.diagonal_mul_diagonal]
  have h : (fun i => V i * (V i)ᴴ) = fun _ => (1 : Matrix J J ℂ) := by
    funext i
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff.mp (hV i)
  rw [h, Matrix.diagonal_one, Matrix.comp_one]

omit [Fintype I] [DecidableEq I] [Fintype J] in
/-- `B ⊗ I` as a block matrix with scalar blocks `B_{ik} I`. -/
theorem kronecker_one_eq_comp (B : Matrix I I ℂ) :
    Matrix.kronecker B (1 : Matrix J J ℂ) =
      Matrix.comp I I J J ℂ (Matrix.of fun i k => B i k • (1 : Matrix J J ℂ)) := by
  ext ⟨i, a⟩ ⟨k, b⟩
  show B i k * (1 : Matrix J J ℂ) a b = _
  simp [Matrix.comp_apply]

/-! ### Products over the edges before `k` -/

theorem prod_filter_lt_zero {M : Type*} [CommMonoid M] {n : ℕ} (f : Fin n → M) :
    ∏ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < 0), f i = 1 := by
  simp

theorem prod_filter_lt_of_le {M : Type*} [CommMonoid M] {n k : ℕ} (hk : n ≤ k) (f : Fin n → M) :
    ∏ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k), f i = ∏ i, f i := by
  rw [Finset.filter_true_of_mem fun i _ => lt_of_lt_of_le i.isLt hk]

theorem prod_filter_lt_succ {M : Type*} [CommMonoid M] {n k : ℕ} (hk : k < n) (f : Fin n → M) :
    ∏ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k + 1), f i =
      f ⟨k, hk⟩ * ∏ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k), f i := by
  have hs : Finset.univ.filter (fun i : Fin n => (i : ℕ) < k + 1) =
      insert ⟨k, hk⟩ (Finset.univ.filter (fun i : Fin n => (i : ℕ) < k)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  rw [hs, Finset.prod_insert]
  simp

end

end SparseLowerBounds.Helpers.Chains
end
