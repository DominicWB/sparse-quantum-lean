import SparseLowerBounds.Helpers.HsInstance.Blocks

set_option synthInstance.maxHeartbeats 400000

section
/-!
# Rows, columns and sparsity of block-diagonal matrices

Helpers for `SparseLowerBounds.Hamiltonian.Instance`: a row (column) of
`fromBlocks H 0 0 K` is a row (column) of `H` or of `K` padded with zeros, so
squared Euclidean masses, nonzero counts and reality pass to the blocks.
-/

namespace SparseLowerBounds.Hamiltonian.HsInstance

noncomputable section
open scoped Matrix

variable {α β : Type*} [Fintype α] [Fintype β]

theorem sum_sq_fromBlocks_row_inl (H : Matrix α α ℂ) (K : Matrix β β ℂ) (a : α) :
    ∑ i', ‖Matrix.fromBlocks H 0 0 K (Sum.inl a) i'‖ ^ 2 = ∑ a', ‖H a a'‖ ^ 2 := by
  simp [Fintype.sum_sum_type]

theorem sum_sq_fromBlocks_row_inr (H : Matrix α α ℂ) (K : Matrix β β ℂ) (b : β) :
    ∑ i', ‖Matrix.fromBlocks H 0 0 K (Sum.inr b) i'‖ ^ 2 = ∑ b', ‖K b b'‖ ^ 2 := by
  simp [Fintype.sum_sum_type]

theorem sum_sq_fromBlocks_col_inl (H : Matrix α α ℂ) (K : Matrix β β ℂ) (a' : α) :
    ∑ i, ‖Matrix.fromBlocks H 0 0 K i (Sum.inl a')‖ ^ 2 = ∑ a, ‖H a a'‖ ^ 2 := by
  simp [Fintype.sum_sum_type]

theorem sum_sq_fromBlocks_col_inr (H : Matrix α α ℂ) (K : Matrix β β ℂ) (b' : β) :
    ∑ i, ‖Matrix.fromBlocks H 0 0 K i (Sum.inr b')‖ ^ 2 = ∑ b, ‖K b b'‖ ^ 2 := by
  simp [Fintype.sum_sum_type]

theorem sum_sq_fromBlocks_row_le {H : Matrix α α ℂ} {K : Matrix β β ℂ} {r : ℝ}
    (hH : ∀ a, ∑ a', ‖H a a'‖ ^ 2 ≤ r) (hK : ∀ b, ∑ b', ‖K b b'‖ ^ 2 ≤ r) (i : α ⊕ β) :
    ∑ i', ‖Matrix.fromBlocks H 0 0 K i i'‖ ^ 2 ≤ r := by
  cases i with
  | inl a => rw [sum_sq_fromBlocks_row_inl]; exact hH a
  | inr b => rw [sum_sq_fromBlocks_row_inr]; exact hK b

theorem sum_sq_fromBlocks_col_le {H : Matrix α α ℂ} {K : Matrix β β ℂ} {r : ℝ}
    (hH : ∀ a', ∑ a, ‖H a a'‖ ^ 2 ≤ r) (hK : ∀ b', ∑ b, ‖K b b'‖ ^ 2 ≤ r) (i' : α ⊕ β) :
    ∑ i, ‖Matrix.fromBlocks H 0 0 K i i'‖ ^ 2 ≤ r := by
  cases i' with
  | inl a => rw [sum_sq_fromBlocks_col_inl]; exact hH a
  | inr b => rw [sum_sq_fromBlocks_col_inr]; exact hK b

theorem card_fromBlocks_row_inl (H : Matrix α α ℂ) (K : Matrix β β ℂ) (a : α) :
    (Finset.univ.filter fun i' => Matrix.fromBlocks H 0 0 K (Sum.inl a) i' ≠ 0).card =
      (Finset.univ.filter fun a' => H a a' ≠ 0).card := by
  rw [Finset.card_filter, Finset.card_filter, Fintype.sum_sum_type]
  simp
  congr!

theorem card_fromBlocks_row_inr (H : Matrix α α ℂ) (K : Matrix β β ℂ) (b : β) :
    (Finset.univ.filter fun i' => Matrix.fromBlocks H 0 0 K (Sum.inr b) i' ≠ 0).card =
      (Finset.univ.filter fun b' => K b b' ≠ 0).card := by
  rw [Finset.card_filter, Finset.card_filter, Fintype.sum_sum_type]
  simp
  congr!

theorem card_fromBlocks_col_inl (H : Matrix α α ℂ) (K : Matrix β β ℂ) (a' : α) :
    (Finset.univ.filter fun i => Matrix.fromBlocks H 0 0 K i (Sum.inl a') ≠ 0).card =
      (Finset.univ.filter fun a => H a a' ≠ 0).card := by
  rw [Finset.card_filter, Finset.card_filter, Fintype.sum_sum_type]
  simp
  congr!

theorem card_fromBlocks_col_inr (H : Matrix α α ℂ) (K : Matrix β β ℂ) (b' : β) :
    (Finset.univ.filter fun i => Matrix.fromBlocks H 0 0 K i (Sum.inr b') ≠ 0).card =
      (Finset.univ.filter fun b => K b b' ≠ 0).card := by
  rw [Finset.card_filter, Finset.card_filter, Fintype.sum_sum_type]
  simp
  congr!

theorem card_fromBlocks_row_le {H : Matrix α α ℂ} {K : Matrix β β ℂ} {s : ℕ}
    (hH : ∀ a, (Finset.univ.filter fun a' => H a a' ≠ 0).card ≤ s)
    (hK : ∀ b, (Finset.univ.filter fun b' => K b b' ≠ 0).card ≤ s) (i : α ⊕ β) :
    (Finset.univ.filter fun i' => Matrix.fromBlocks H 0 0 K i i' ≠ 0).card ≤ s := by
  cases i with
  | inl a => rw [card_fromBlocks_row_inl]; exact hH a
  | inr b => rw [card_fromBlocks_row_inr]; exact hK b

theorem card_fromBlocks_col_le {H : Matrix α α ℂ} {K : Matrix β β ℂ} {s : ℕ}
    (hH : ∀ a', (Finset.univ.filter fun a => H a a' ≠ 0).card ≤ s)
    (hK : ∀ b', (Finset.univ.filter fun b => K b b' ≠ 0).card ≤ s) (i' : α ⊕ β) :
    (Finset.univ.filter fun i => Matrix.fromBlocks H 0 0 K i i' ≠ 0).card ≤ s := by
  cases i' with
  | inl a => rw [card_fromBlocks_col_inl]; exact hH a
  | inr b => rw [card_fromBlocks_col_inr]; exact hK b

omit [Fintype α] [Fintype β] in
theorem star_fromBlocks_apply {H : Matrix α α ℂ} {K : Matrix β β ℂ}
    (hH : ∀ a a', star (H a a') = H a a') (hK : ∀ b b', star (K b b') = K b b')
    (i i' : α ⊕ β) : star (Matrix.fromBlocks H 0 0 K i i') = Matrix.fromBlocks H 0 0 K i i' := by
  cases i <;> cases i' <;> simp [hH, hK]

end

end SparseLowerBounds.Hamiltonian.HsInstance
end
