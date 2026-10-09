import SparseLowerBounds.Helpers.HsInstance.BlockRows

set_option synthInstance.maxHeartbeats 400000

section
/-!
# Row masses and sparsity of the decorated chains

Helpers for `SparseLowerBounds.Hamiltonian.Instance`: every row of the
search-decorated chain and of the signed scalar chain has squared Euclidean
mass `c_{k-1}² + c_k²` (the edges meeting the clock vertex `k`), which is at
most one for weights `0 ≤ c_k ≤ b_k`; a decorated-chain row meets at most two
`m × m` gadget blocks, a scalar-chain row at most two entries.
-/

namespace SparseLowerBounds.Hamiltonian.HsInstance

noncomputable section
open scoped Matrix

/-- Rows of a unitary matrix are unit vectors. -/
theorem sum_norm_sq_row_of_unitary {ι : Type*} [Fintype ι] [DecidableEq ι] {U : Matrix ι ι ℂ}
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) (a : ι) : ∑ b, ‖U a b‖ ^ 2 = 1 := by
  have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff.1 hU) a) a
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at h
  simp only [Matrix.star_apply] at h
  have h' : ((∑ b, ‖U a b‖ ^ 2 : ℝ) : ℂ) = 1 := by
    rw [← h]
    push_cast
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Complex.mul_conj']
    rfl
  exact_mod_cast h'

/-- Columns of a unitary matrix are unit vectors. -/
theorem sum_norm_sq_col_of_unitary {ι : Type*} [Fintype ι] [DecidableEq ι] {U : Matrix ι ι ℂ}
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) (a : ι) : ∑ b, ‖U b a‖ ^ 2 = 1 := by
  have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff'.1 hU) a) a
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at h
  simp only [Matrix.star_apply] at h
  have h' : ((∑ b, ‖U b a‖ ^ 2 : ℝ) : ℂ) = 1 := by
    rw [← h]
    push_cast
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Complex.mul_conj', mul_comm]
    rfl
  exact_mod_cast h'

variable {n m : ℕ}

/-- The two-edge mass at clock vertex `k`: `c_{k-1}² + c_k² ≤ 1` for
`0 ≤ c ≤ b` (`spinWeight_sq_add_sq_le`). -/
theorem edge_mass_le {c : ℕ → ℝ} (hc0 : ∀ k, 0 ≤ c k)
    (hc : ∀ k, k < n → c k ≤ spinWeight n k) (k : ℕ) (hk : k ≤ n) :
    (if 1 ≤ k then c (k - 1) ^ 2 else 0) + (if k < n then c k ^ 2 else 0) ≤ 1 := by
  have hsq : ∀ i, i < n → c i ^ 2 ≤ spinWeight n i ^ 2 := fun i hi =>
    pow_le_pow_left₀ (hc0 i) (hc i hi) 2
  have hb : ∀ i, spinWeight n i ^ 2 ≤ 1 := fun i => by
    have := spinWeight_sq_add_sq_le n i
    nlinarith [sq_nonneg (spinWeight n (i + 1))]
  split_ifs with h1 h2 h2
  · have := spinWeight_sq_add_sq_le n (k - 1)
    rw [show k - 1 + 1 = k by omega] at this
    linarith [hsq (k - 1) (by omega), hsq k h2]
  · linarith [hsq (k - 1) (by omega), hb (k - 1)]
  · linarith [hsq k h2, hb k]
  · norm_num

/-- The sum over the lower neighbour `k' = k - 1`. -/
theorem sum_ite_eq_succ (k : Fin (n + 1)) (g : ℕ → ℝ) :
    ∑ k' : Fin (n + 1), (if (k : ℕ) = k' + 1 then g k' else 0) =
      if 1 ≤ (k : ℕ) then g ((k : ℕ) - 1) else 0 := by
  split_ifs with hk
  · rw [Finset.sum_eq_single ⟨(k : ℕ) - 1, by omega⟩]
    · rw [if_pos (by simp; omega)]
    · intro b _ hb
      rw [if_neg]
      intro h
      exact hb (Fin.ext (by simp; omega))
    · simp
  · exact Finset.sum_eq_zero fun k' _ => if_neg (by omega)

/-- The sum over the upper neighbour `k' = k + 1`. -/
theorem sum_ite_succ_eq (k : Fin (n + 1)) (C : ℝ) :
    ∑ k' : Fin (n + 1), (if (k' : ℕ) = k + 1 then C else 0) = if (k : ℕ) < n then C else 0 := by
  split_ifs with hk
  · rw [Finset.sum_eq_single ⟨(k : ℕ) + 1, by omega⟩]
    · rw [if_pos rfl]
    · intro b _ hb
      rw [if_neg]
      intro h
      exact hb (Fin.ext (by simp; omega))
    · simp
  · exact Finset.sum_eq_zero fun k' _ => if_neg (by have := k'.isLt; omega)

theorem norm_bitSign (b : Bool) : ‖bitSign b‖ = 1 := by
  cases b <;> simp [bitSign]

/-- Row mass of the decorated chain. -/
theorem sum_sq_searchChain_row (c : ℕ → ℝ) (j : Fin n → Fin m) (k : Fin (n + 1)) (a : Fin m)
    (k' : Fin (n + 1)) :
    ∑ b, ‖searchChain n m c j (k, a) (k', b)‖ ^ 2 =
      (if (k : ℕ) = k' + 1 then c k' ^ 2 else 0) + (if (k' : ℕ) = k + 1 then c k ^ 2 else 0) := by
  by_cases h1 : (k : ℕ) = k' + 1
  · have h2 : ¬ ((k' : ℕ) = k + 1) := by omega
    rw [if_pos h1, if_neg h2, add_zero]
    simp only [searchChain, Matrix.of_apply]
    simp only [dif_pos h1, norm_mul, mul_pow, ← Finset.mul_sum, Complex.norm_real,
      Real.norm_eq_abs, sq_abs]
    exact (congrArg (fun x => c k' ^ 2 * x) (sum_norm_sq_row_of_unitary
      (LinearSystems.gadget_mem_unitaryGroup (j ⟨k', by have := k.isLt; omega⟩)) a)).trans
      (mul_one _)
  · by_cases h2 : (k' : ℕ) = k + 1
    · rw [if_neg h1, if_pos h2, zero_add]
      simp only [searchChain, Matrix.of_apply]
      simp only [dif_neg h1, dif_pos h2, norm_mul, mul_pow, ← Finset.mul_sum, Complex.norm_real,
        Real.norm_eq_abs, sq_abs]
      exact (congrArg (fun x => c k ^ 2 * x) (sum_norm_sq_col_of_unitary
        (LinearSystems.gadget_mem_unitaryGroup (j ⟨k, by have := k'.isLt; omega⟩)) a)).trans
        (mul_one _)
    · rw [if_neg h1, if_neg h2, add_zero]
      simp only [searchChain, Matrix.of_apply]
      simp [dif_neg h1, dif_neg h2]

/-- Row Euclidean norms of the decorated chain are at most one. -/
theorem sum_sq_searchChain_le {c : ℕ → ℝ} (hc0 : ∀ k, 0 ≤ c k)
    (hc : ∀ k, k < n → c k ≤ spinWeight n k) (j : Fin n → Fin m) (p : Fin (n + 1) × Fin m) :
    ∑ q, ‖searchChain n m c j p q‖ ^ 2 ≤ 1 := by
  obtain ⟨k, a⟩ := p
  rw [Fintype.sum_prod_type]
  simp only [sum_sq_searchChain_row, Finset.sum_add_distrib]
  rw [sum_ite_eq_succ k (fun i => c i ^ 2), sum_ite_succ_eq k]
  exact edge_mass_le hc0 hc k (by have := k.isLt; omega)

/-- Row mass of the scalar chain. -/
theorem sq_scalarChain (c : ℕ → ℝ) (x : Fin n → Bool) (k k' : Fin (n + 1)) :
    ‖scalarChain n c x k k'‖ ^ 2 =
      (if (k : ℕ) = k' + 1 then c k' ^ 2 else 0) + (if (k' : ℕ) = k + 1 then c k ^ 2 else 0) := by
  by_cases h1 : (k : ℕ) = k' + 1
  · have h2 : ¬ ((k' : ℕ) = k + 1) := by omega
    rw [if_pos h1, if_neg h2, add_zero]
    simp only [scalarChain, Matrix.of_apply]
    simp only [dif_pos h1, norm_mul, norm_bitSign, mul_one, Complex.norm_real,
      Real.norm_eq_abs, sq_abs]
  · by_cases h2 : (k' : ℕ) = k + 1
    · rw [if_neg h1, if_pos h2, zero_add]
      simp only [scalarChain, Matrix.of_apply]
      simp only [dif_neg h1, dif_pos h2, norm_mul, norm_bitSign, mul_one, Complex.norm_real,
        Real.norm_eq_abs, sq_abs]
    · rw [if_neg h1, if_neg h2, add_zero]
      simp only [scalarChain, Matrix.of_apply]
      simp [dif_neg h1, dif_neg h2]

theorem sum_sq_scalarChain_le {c : ℕ → ℝ} (hc0 : ∀ k, 0 ≤ c k)
    (hc : ∀ k, k < n → c k ≤ spinWeight n k) (x : Fin n → Bool) (i : Fin (n + 1)) :
    ∑ i', ‖scalarChain n c x i i'‖ ^ 2 ≤ 1 := by
  simp only [sq_scalarChain, Finset.sum_add_distrib]
  rw [sum_ite_eq_succ i (fun i => c i ^ 2), sum_ite_succ_eq i]
  exact edge_mass_le hc0 hc i (by have := i.isLt; omega)

/-- The clock neighbours of `k`: at most two. -/
theorem card_neighbours_le (k : Fin (n + 1)) :
    ((Finset.univ.filter fun k' : Fin (n + 1) => (k : ℕ) = k' + 1) ∪
      (Finset.univ.filter fun k' : Fin (n + 1) => (k' : ℕ) = k + 1)).card ≤ 2 := by
  refine (Finset.card_union_le _ _).trans ?_
  have h1 : (Finset.univ.filter fun k' : Fin (n + 1) => (k : ℕ) = k' + 1).card ≤ 1 :=
    Finset.card_le_one.2 fun x hx y hy => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
      exact Fin.ext (by omega)
  have h2 : (Finset.univ.filter fun k' : Fin (n + 1) => (k' : ℕ) = k + 1).card ≤ 1 :=
    Finset.card_le_one.2 fun x hx y hy => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
      exact Fin.ext (by omega)
  omega

theorem card_row_searchChain_le (c : ℕ → ℝ) (j : Fin n → Fin m) (p : Fin (n + 1) × Fin m) :
    (Finset.univ.filter fun q => searchChain n m c j p q ≠ 0).card ≤ 2 * m := by
  obtain ⟨k, a⟩ := p
  set S : Finset (Fin (n + 1)) :=
    (Finset.univ.filter fun k' : Fin (n + 1) => (k : ℕ) = k' + 1) ∪
      (Finset.univ.filter fun k' : Fin (n + 1) => (k' : ℕ) = k + 1) with hSdef
  have hsub : (Finset.univ.filter fun q => searchChain n m c j (k, a) q ≠ 0) ⊆
      S ×ˢ (Finset.univ : Finset (Fin m)) := by
    intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
    simp only [Finset.mem_product, Finset.mem_univ, and_true, hSdef, Finset.mem_union,
      Finset.mem_filter, true_and]
    by_contra h
    simp only [not_or] at h
    apply hq
    simp only [searchChain, Matrix.of_apply]
    rw [dif_neg h.1, dif_neg h.2]
  calc _ ≤ (S ×ˢ (Finset.univ : Finset (Fin m))).card := Finset.card_le_card hsub
    _ = S.card * m := by simp [Finset.card_product]
    _ ≤ 2 * m := Nat.mul_le_mul_right _ (card_neighbours_le k)

theorem card_row_scalarChain_le (c : ℕ → ℝ) (x : Fin n → Bool) (i : Fin (n + 1)) :
    (Finset.univ.filter fun i' => scalarChain n c x i i' ≠ 0).card ≤ 2 := by
  refine le_trans (Finset.card_le_card ?_) (card_neighbours_le i)
  intro q hq
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
  by_contra h
  simp only [not_or] at h
  apply hq
  simp only [scalarChain, Matrix.of_apply]
  rw [dif_neg h.1, dif_neg h.2]

end

end SparseLowerBounds.Hamiltonian.HsInstance
end
