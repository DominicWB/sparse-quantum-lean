import SparseLowerBounds.Helpers.SpinChain.Schur

set_option synthInstance.maxHeartbeats 400000

section
/-!
# Row sums of a tridiagonal (path) pattern on `Fin (n+1)`

Helper module of group spin-chain (`SparseLowerBounds.Hamiltonian.SpinChain`).
A row `i` of the path pattern `(i = j+1) ∨ (j = i+1)` meets the predecessor
`i-1` (when `0 < i`) and the successor `i+1` (when `i < n`).
-/

namespace SparseLowerBounds.Helpers.SpinChain

variable {M : Type*} [AddCommMonoid M] {n : ℕ}

theorem sum_ite_pred (x : Fin (n + 1) → M) (i : Fin (n + 1)) :
    (∑ j : Fin (n + 1), if (i : ℕ) = j + 1 then x j else 0) =
      if h : 0 < (i : ℕ) then x ⟨i - 1, by omega⟩ else 0 := by
  split_ifs with h
  · rw [Fintype.sum_eq_single ⟨i - 1, by omega⟩]
    · rw [if_pos (by simp; omega)]
    · intro j hj
      rw [if_neg]
      intro h'
      apply hj
      ext
      simp
      omega
  · refine Finset.sum_eq_zero fun j _ => ?_
    rw [if_neg]
    omega

theorem sum_ite_succ (y : Fin (n + 1) → M) (i : Fin (n + 1)) :
    (∑ j : Fin (n + 1), if (j : ℕ) = i + 1 then y j else 0) =
      if h : (i : ℕ) < n then y ⟨i + 1, by omega⟩ else 0 := by
  split_ifs with h
  · rw [Fintype.sum_eq_single ⟨i + 1, by omega⟩]
    · rw [if_pos rfl]
    · intro j hj
      rw [if_neg]
      intro h'
      apply hj
      ext
      simp
      omega
  · refine Finset.sum_eq_zero fun j _ => ?_
    rw [if_neg]
    have := j.isLt
    omega

/-- The two-neighbour row sum of a path pattern. -/
theorem sum_path (x y : Fin (n + 1) → M) (i : Fin (n + 1)) :
    (∑ j : Fin (n + 1),
        if (i : ℕ) = j + 1 then x j else if (j : ℕ) = i + 1 then y j else 0) =
      (if h : 0 < (i : ℕ) then x ⟨i - 1, by omega⟩ else 0) +
        (if h : (i : ℕ) < n then y ⟨i + 1, by omega⟩ else 0) := by
  rw [← sum_ite_pred, ← sum_ite_succ, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h1 : (i : ℕ) = j + 1
  · rw [if_pos h1, if_pos h1, if_neg (by omega), add_zero]
  · rw [if_neg h1, if_neg h1, zero_add]

end SparseLowerBounds.Helpers.SpinChain
end
