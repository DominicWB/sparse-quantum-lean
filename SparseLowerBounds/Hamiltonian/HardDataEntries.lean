import SparseLowerBounds.Hamiltonian.Compile

set_option synthInstance.maxHeartbeats 400000

section
/-!
# Entry formulas of the hard Hamiltonians

Helper statements for `Hamiltonian/HardData` (manuscript lines 2234-2252,
2277-2284, 2342-2343 and 2476-2487):

* the entries of `fullMatrix H s = H ⊕ diag(0, 1) ⊕ 2^{-⌈log₂ s⌉} 𝟙𝟙ᵀ` on each
  block of `FullIndex C s = C ⊕ (Fin 2 ⊕ Fin s)`;
* the entries of the search-decorated and signed scalar chains on adjacent and
  on distant clock pairs (`searchChain_succ/pred/far`, `scalarChain_succ/pred/far`);
* the exact dyadic arithmetic `word / 2^B = entry` of the chain, padding and
  energy-one words (`searchWord_div`, `scalarWord_div`, `padWord_div`,
  `topWord_div`).

Together with the block lemmas for the word tables in `Hamiltonian/HardData`,
these are the steps of `searchTable_decode` and `scalarTable_decode`.
Namespace `SparseLowerBounds.Hamiltonian.HardData`.
-/

namespace SparseLowerBounds.Hamiltonian.HardData

noncomputable section
open scoped Matrix

/-! ### Blocks of `fullMatrix` -/

section Blocks

variable {C : Type} [Fintype C] [DecidableEq C] (H : Matrix C C ℂ) {s : ℕ}

@[simp] theorem fullMatrix_core (c c' : C) :
    fullMatrix H s (Sum.inl c) (Sum.inl c') = H c c' := rfl

@[simp] theorem fullMatrix_core_side (c : C) (r : Fin 2 ⊕ Fin s) :
    fullMatrix H s (Sum.inl c) (Sum.inr r) = 0 := rfl

@[simp] theorem fullMatrix_side_core (r : Fin 2 ⊕ Fin s) (c : C) :
    fullMatrix H s (Sum.inr r) (Sum.inl c) = 0 := rfl

/-- The reference block `diag(0, 1)`. -/
@[simp] theorem fullMatrix_ref (r r' : Fin 2) :
    fullMatrix H s (Sum.inr (Sum.inl r)) (Sum.inr (Sum.inl r')) =
      if r = 1 ∧ r' = 1 then 1 else 0 := by
  fin_cases r <;> fin_cases r' <;> simp [fullMatrix, refBlock]

@[simp] theorem fullMatrix_ref_pad (r : Fin 2) (t : Fin s) :
    fullMatrix H s (Sum.inr (Sum.inl r)) (Sum.inr (Sum.inr t)) = 0 := rfl

@[simp] theorem fullMatrix_pad_ref (t : Fin s) (r : Fin 2) :
    fullMatrix H s (Sum.inr (Sum.inr t)) (Sum.inr (Sum.inl r)) = 0 := rfl

/-- The padding block `2^{-⌈log₂ s⌉} 𝟙𝟙ᵀ` (line 2480). -/
@[simp] theorem fullMatrix_pad (t t' : Fin s) :
    fullMatrix H s (Sum.inr (Sum.inr t)) (Sum.inr (Sum.inr t')) = ((2 : ℂ) ^ padExp s)⁻¹ := rfl

end Blocks

/-! ### Chain entries -/

section Chains

variable {n m : ℕ} (c : ℕ → ℝ)

/-- Forward edge `k`: entry `((k+1, a), (k, b)) = c_k (U_{j k})_{ab}`. -/
theorem searchChain_succ (j : Fin n → Fin m) {p q : Fin (n + 1) × Fin m}
    (h : (p.1 : ℕ) = q.1 + 1) :
    searchChain n m c j p q =
      (c q.1 : ℂ) * LinearSystems.gadget m (j ⟨q.1, by have := p.1.isLt; omega⟩) p.2 q.2 := by
  rw [searchChain, Matrix.of_apply, dif_pos h]

/-- Reverse edge `k`: entry `((k, b), (k+1, a)) = c_k (U_{j k})_{ab}`. -/
theorem searchChain_pred (j : Fin n → Fin m) {p q : Fin (n + 1) × Fin m}
    (h : (q.1 : ℕ) = p.1 + 1) :
    searchChain n m c j p q =
      (c p.1 : ℂ) * LinearSystems.gadget m (j ⟨p.1, by have := q.1.isLt; omega⟩) q.2 p.2 := by
  rw [searchChain, Matrix.of_apply, dif_neg (by omega), dif_pos h]

/-- Clock indices that are not adjacent are not coupled. -/
theorem searchChain_far (j : Fin n → Fin m) {p q : Fin (n + 1) × Fin m}
    (h1 : (p.1 : ℕ) ≠ q.1 + 1) (h2 : (q.1 : ℕ) ≠ p.1 + 1) : searchChain n m c j p q = 0 := by
  rw [searchChain, Matrix.of_apply, dif_neg h1, dif_neg h2]

/-- Forward edge `k` of the signed scalar chain: `c_k (-1)^{x_k}`. -/
theorem scalarChain_succ (x : Fin n → Bool) {i i' : Fin (n + 1)} (h : (i : ℕ) = i' + 1) :
    scalarChain n c x i i' = (c i' : ℂ) * bitSign (x ⟨i', by have := i.isLt; omega⟩) := by
  rw [scalarChain, Matrix.of_apply, dif_pos h]

/-- Reverse edge `k` of the signed scalar chain. -/
theorem scalarChain_pred (x : Fin n → Bool) {i i' : Fin (n + 1)} (h : (i' : ℕ) = i + 1) :
    scalarChain n c x i i' = (c i : ℂ) * bitSign (x ⟨i, by have := i'.isLt; omega⟩) := by
  rw [scalarChain, Matrix.of_apply, dif_neg (by omega), dif_pos h]

theorem scalarChain_far (x : Fin n → Bool) {i i' : Fin (n + 1)} (h1 : (i : ℕ) ≠ i' + 1)
    (h2 : (i' : ℕ) ≠ i + 1) : scalarChain n c x i i' = 0 := by
  rw [scalarChain, Matrix.of_apply, dif_neg h1, dif_neg h2]

end Chains

/-! ### Exact dyadic words -/

section Words

variable {n μ s : ℕ} {a τ : ℝ}

/-- **Search chain words** (lines 2277-2278): at scale `2^{F+μ+σ}` the word
`N_k (2 - 2^μ y) 2^σ` is the gadget-decorated rounded weight `b'_k (2/m - y)`,
`m = 2^μ`, `b'_k = N_k/2^F`. -/
theorem searchWord_div (k : ℕ) (y : Bool) :
    ((((chainNum n a τ k : ℤ) * (2 - 2 ^ μ * (if y then 1 else 0)) * 2 ^ padExp s : ℤ) : ℂ) /
        2 ^ (chainBits n a τ + μ + padExp s)) =
      (chainWeight n a τ k : ℂ) * ((2 / ((2 ^ μ : ℕ) : ℂ)) - if y then 1 else 0) := by
  have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
  unfold chainWeight
  cases y <;> simp only [Bool.false_eq_true, if_false, if_true] <;> push_cast <;>
    rw [pow_add, pow_add] <;> field_simp

/-- **Scalar chain words**: at scale `2^{F+σ}` the word `(-1)^y N_k 2^σ` is the
signed rounded weight `(-1)^y b'_k`. -/
theorem scalarWord_div (k : ℕ) (y : Bool) :
    ((((if y then -1 else 1) * (chainNum n 1 τ k : ℤ) * 2 ^ padExp s : ℤ) : ℂ) /
        2 ^ (chainBits n 1 τ + padExp s)) =
      (chainWeight n 1 τ k : ℂ) * bitSign y := by
  have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
  unfold chainWeight
  cases y <;> simp only [bitSign, Bool.false_eq_true, if_false, if_true] <;> push_cast <;>
    rw [pow_add] <;> field_simp

/-- **Padding words**: `2^E / 2^{E+σ} = 2^{-σ}`, `σ = ⌈log₂ s⌉` (with
`E = F + μ` for the search words and `E = F` for the scalar words). -/
theorem padWord_div (E : ℕ) :
    ((((2 : ℤ) ^ E : ℤ) : ℂ) / 2 ^ (E + padExp s)) = ((2 : ℂ) ^ padExp s)⁻¹ := by
  push_cast
  rw [pow_add, div_mul_eq_div_div, div_self (pow_ne_zero _ two_ne_zero), one_div]

/-- **Energy-one word**: `2^B / 2^B = 1`. -/
theorem topWord_div (B : ℕ) : ((((2 : ℤ) ^ B : ℤ) : ℂ) / 2 ^ B) = 1 := by
  push_cast
  exact div_self (pow_ne_zero _ two_ne_zero)

end Words

end

end SparseLowerBounds.Hamiltonian.HardData
end
