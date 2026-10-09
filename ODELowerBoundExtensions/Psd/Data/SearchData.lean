import ODELowerBoundExtensions.Psd.Data.SearchTable

/-!
# The gadget family as release sparse-access data

Manuscript lines 4048-4077 and 4106-4107 ("each matrix
query takes at most two membership queries"). The PSD gadget-family generator `psdSearchMat` is
packaged as `NativeSparseBlockEncoding.Data` by the one-bit builder `Hamiltonian.bitData`:

* `psdSearchTable_decode`: `word/2^B` is the matrix entry on every block;
* `psdSearchLoc_row`, `psdSearchLoc_col`: the fixed location lists cover the support;
* `psdSearchData`: the data; the native primitives are `hardCost`-query programs over the
  one-hot Boolean oracle of the hidden strings (`implementsOn_psdSearchData_spec`, from
  `Hamiltonian.implementsOn_bitData_spec`: two Boolean queries per value call, location calls
  free);
* `psdSearchData_hardInstance`: every instance property of the Hamiltonian lower bound
  (`Hamiltonian.HardInstance`: real symmetric, norm one, row/column norms at most one with
  maximum exactly one, maximum sparsity exactly `s` by the PSD dense padding, scale one,
  exact dyadic entries, input-independent locators), and `psdSearchData_posSemidef`
  (`D_X ⪰ 0`).
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

namespace ODELowerBoundExtensions.Psd

noncomputable section
open SparseHamiltonian NativeSparseBlockEncoding OracleCircuit SparseLowerBounds
  SparseLowerBounds.Hamiltonian
open scoped ComplexOrder

-- The nested spectator spaces over the search index exceed the default instance size.
set_option synthInstance.maxSize 1024

variable {n μ s : ℕ} {u : ℝ}

/-! ### The PSD words on each block (any hidden bits `y`) -/

section Words

variable (y : Fin n × Fin (2 ^ μ) → Bool)

/-- Diagonal of the path block: the known word `2^{F+μ+σ}` (no query). -/
theorem psdSearchTable_value_diag (p : SearchCore n μ) :
    (psdSearchTable n μ s u).value y (Sum.inl p, Sum.inl p) =
      2 ^ (psdBits n u + μ + padExp s) := by
  have ha : (psdSearchTable n μ s u).addr (Sum.inl p, Sum.inl p) = none := by
    simp only [psdSearchTable, searchAddr, dif_neg (by omega : ¬ (p.1 : ℕ) = p.1 + 1)]
  rw [BitTable.value_of_addr_none _ _ ha]
  simp only [psdSearchTable, psdSearchWord, ↓reduceIte]

/-- Forward edge `k = q.1`: the word of membership bit `(k, gadgetPos p.2 q.2)`. -/
theorem psdSearchTable_value_succ {p q : SearchCore n μ} (h : (p.1 : ℕ) = q.1 + 1) :
    (psdSearchTable n μ s u).value y (Sum.inl p, Sum.inl q) =
      -((psdNum n u q.1 : ℤ) *
        (2 - 2 ^ μ * (if y (⟨q.1, by have := p.1.isLt; omega⟩, LinearSystems.gadgetPos p.2 q.2)
          then 1 else 0)) * 2 ^ padExp s) := by
  have hpq : p ≠ q := fun e => by rw [e] at h; omega
  have ha : (psdSearchTable n μ s u).addr (Sum.inl p, Sum.inl q) =
      some (⟨q.1, by have := p.1.isLt; omega⟩, LinearSystems.gadgetPos p.2 q.2) := by
    simp only [psdSearchTable, searchAddr, dif_pos h]
  rw [BitTable.value_of_addr_some _ _ ha]
  simp only [psdSearchTable, psdSearchWord, if_neg hpq, if_pos h]

/-- Reverse edge `k = p.1`: the word of membership bit `(k, gadgetPos q.2 p.2)`. -/
theorem psdSearchTable_value_pred {p q : SearchCore n μ} (h : (q.1 : ℕ) = p.1 + 1) :
    (psdSearchTable n μ s u).value y (Sum.inl p, Sum.inl q) =
      -((psdNum n u p.1 : ℤ) *
        (2 - 2 ^ μ * (if y (⟨p.1, by have := q.1.isLt; omega⟩, LinearSystems.gadgetPos q.2 p.2)
          then 1 else 0)) * 2 ^ padExp s) := by
  have hpq : p ≠ q := fun e => by rw [e] at h; omega
  have h' : ¬ (p.1 : ℕ) = q.1 + 1 := by omega
  have ha : (psdSearchTable n μ s u).addr (Sum.inl p, Sum.inl q) =
      some (⟨p.1, by have := q.1.isLt; omega⟩, LinearSystems.gadgetPos q.2 p.2) := by
    simp only [psdSearchTable, searchAddr, dif_neg h', dif_pos h]
  rw [BitTable.value_of_addr_some _ _ ha]
  simp only [psdSearchTable, psdSearchWord, if_neg hpq, if_neg h', if_pos h]

/-- Distinct, non-adjacent clock indices: word `0`. -/
theorem psdSearchTable_value_far {p q : SearchCore n μ} (hpq : p ≠ q)
    (h1 : (p.1 : ℕ) ≠ q.1 + 1) (h2 : (q.1 : ℕ) ≠ p.1 + 1) :
    (psdSearchTable n μ s u).value y (Sum.inl p, Sum.inl q) = 0 := by
  simp only [BitTable.value, psdSearchTable, psdSearchWord, if_neg hpq, if_neg h1, if_neg h2]

/-- Core-to-side blocks: word `0`. -/
theorem psdSearchTable_value_core_side (p : SearchCore n μ) (r : Fin 2 ⊕ Fin s) :
    (psdSearchTable n μ s u).value y (Sum.inl p, Sum.inr r) = 0 := by
  cases r <;> rfl

/-- Side-to-core blocks: word `0`. -/
theorem psdSearchTable_value_side_core (r : Fin 2 ⊕ Fin s) (p : SearchCore n μ) :
    (psdSearchTable n μ s u).value y (Sum.inr r, Sum.inl p) = 0 := by
  rcases r with r | r <;> rfl

end Words

/-! ### Exact dyadic words -/

/-- **Gadget words**: at scale `2^B`, `B = F + μ + σ + 1`, the word `-N_k (2 - 2^μ y) 2^σ` is the
entry `-½ b'_k (2/m - y)` of `(I - H'_X)/2`. -/
theorem psdGadgetWord_div (k : ℕ) (y : Bool) :
    ((((-((psdNum n u k : ℤ) * (2 - 2 ^ μ * (if y then 1 else 0)) * 2 ^ padExp s)) : ℤ) : ℂ) /
        2 ^ psdSearchBits n μ s u) =
      (1 / 2 : ℂ) *
        (0 - (psdWeight n u k : ℂ) * ((2 / ((2 ^ μ : ℕ) : ℂ)) - if y then 1 else 0)) := by
  have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
  unfold psdWeight psdSearchBits
  cases y <;> simp only [Bool.false_eq_true, if_false, if_true] <;> push_cast <;>
    rw [pow_succ, pow_add, pow_add] <;> field_simp <;> ring

/-- **Diagonal words**: `2^{F+μ+σ} / 2^B = 1/2`. -/
theorem psdDiagWord_div :
    ((((2 : ℤ) ^ (psdBits n u + μ + padExp s) : ℤ) : ℂ) / 2 ^ psdSearchBits n μ s u) =
      (1 / 2 : ℂ) * (1 - 0) := by
  unfold psdSearchBits
  push_cast
  rw [pow_succ]
  field_simp
  ring

/-- **Padding words**: `2^{F+μ+1} / 2^B = 2^{-σ}`. -/
theorem psdPadWord_div :
    ((((2 : ℤ) ^ (psdBits n u + μ + 1) : ℤ) : ℂ) / 2 ^ psdSearchBits n μ s u) =
      ((2 : ℂ) ^ padExp s)⁻¹ := by
  rw [show psdSearchBits n μ s u = psdBits n u + μ + 1 + padExp s by unfold psdSearchBits; omega]
  exact HardData.padWord_div _

/-! ### Decoding and coverage -/

/-- **Exact decoding**: `word/2^B = D_X` entry on every block, for the one-hot bits of `j`. -/
theorem psdSearchTable_decode (j : Fin n → Fin (2 ^ μ)) (i i' : SearchIndex n μ s) :
    (((psdSearchTable n μ s u).value (oneHotBits j) (i, i') : ℤ) : ℂ) /
        2 ^ psdSearchBits n μ s u = psdSearchMat n μ s u j i i' := by
  unfold psdSearchMat
  rcases i with p | r | t <;> rcases i' with q | r' | t'
  · rw [HardData.fullMatrix_core]
    simp only [psdCore, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
    by_cases hpq : p = q
    · subst hpq
      rw [psdSearchTable_value_diag, Matrix.one_apply_eq,
        HardData.searchChain_far _ j (by omega) (by omega)]
      exact psdDiagWord_div
    rw [Matrix.one_apply_ne hpq]
    by_cases h1 : (p.1 : ℕ) = q.1 + 1
    · rw [psdSearchTable_value_succ _ h1, HardData.searchChain_succ _ j h1, ← gadget_oneHotBits]
      exact psdGadgetWord_div _ _
    · by_cases h2 : (q.1 : ℕ) = p.1 + 1
      · rw [psdSearchTable_value_pred _ h2, HardData.searchChain_pred _ j h2, ← gadget_oneHotBits]
        exact psdGadgetWord_div _ _
      · rw [psdSearchTable_value_far _ hpq h1 h2, HardData.searchChain_far _ j h1 h2]
        simp
  · rw [psdSearchTable_value_core_side, HardData.fullMatrix_core_side]; simp
  · rw [psdSearchTable_value_core_side, HardData.fullMatrix_core_side]; simp
  · rw [psdSearchTable_value_side_core, HardData.fullMatrix_side_core]; simp
  · rw [HardData.fullMatrix_ref]
    simp only [BitTable.value, psdSearchTable]
    simp only [psdSearchWord]
    split_ifs
    · exact HardData.topWord_div _
    · simp
  · rw [HardData.fullMatrix_ref_pad]
    simp only [BitTable.value, psdSearchTable]
    simp [psdSearchWord]
  · rw [psdSearchTable_value_side_core, HardData.fullMatrix_side_core]; simp
  · rw [HardData.fullMatrix_pad_ref]
    simp only [BitTable.value, psdSearchTable]
    simp [psdSearchWord]
  · rw [HardData.fullMatrix_pad]
    exact psdPadWord_div

/-- **Row coverage**: every nonzero of row `i` is in its location list (`2m + 1 ≤ s`). -/
theorem psdSearchLoc_row (hn : 1 ≤ n) (hs : 2 * 2 ^ μ + 1 ≤ s) (j : Fin n → Fin (2 ^ μ))
    (i i' : SearchIndex n μ s) (h : psdSearchMat n μ s u j i i' ≠ 0) :
    i' ∈ Set.range (fullLoc (by omega) (psdSearchLoc n μ s hn) i) := by
  unfold psdSearchMat at h
  rcases i with p | r | t <;> rcases i' with q | r' | t'
  · by_cases hpq : p = q
    · -- the diagonal, slot `2m`
      subst hpq
      refine ⟨⟨2 * 2 ^ μ, by omega⟩, ?_⟩
      show psdSearchLocFun n μ s p ⟨2 * 2 ^ μ, _⟩ = Sum.inl p
      rw [psdSearchLocFun, if_pos rfl]
    have adj : (q.1 : ℕ) = p.1 + 1 ∨ (p.1 : ℕ) = q.1 + 1 := by
      by_contra hc
      rw [not_or] at hc
      apply h
      rw [HardData.fullMatrix_core]
      simp only [psdCore, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul,
        Matrix.one_apply_ne hpq, HardData.searchChain_far _ j hc.2 hc.1]
      simp
    obtain ⟨t, ht⟩ := searchLoc_adj_mem (s := s) (by omega) p q adj
    refine ⟨t, ?_⟩
    have ht' : searchLocFun n μ s p t = Sum.inl q := ht
    have htne : (t : ℕ) ≠ 2 * 2 ^ μ := by
      intro he
      rw [searchLocFun, dif_neg (by omega), dif_neg (by omega)] at ht'
      exact Sum.inr_ne_inl ht'
    show psdSearchLocFun n μ s p t = Sum.inl q
    rw [psdSearchLocFun, if_neg htne]
    exact ht'
  · exact (h (HardData.fullMatrix_core_side _ _ _)).elim
  · exact (h (HardData.fullMatrix_core_side _ _ _)).elim
  · exact (h (HardData.fullMatrix_side_core _ _ _)).elim
  · rw [HardData.fullMatrix_ref] at h
    split_ifs at h with hr
    · obtain ⟨rfl, rfl⟩ := hr
      exact ref_mem_range_fullLoc _ _ _
    · exact (h rfl).elim
  · exact (h (HardData.fullMatrix_ref_pad _ _ _)).elim
  · exact (h (HardData.fullMatrix_side_core _ _ _)).elim
  · exact (h (HardData.fullMatrix_pad_ref _ _ _)).elim
  · exact pad_mem_range_fullLoc _ _ _ _

/-- **Column coverage** (the generator is symmetric, columns use the row lists). -/
theorem psdSearchLoc_col (hn : 1 ≤ n) (hs : 2 * 2 ^ μ + 1 ≤ s) (j : Fin n → Fin (2 ^ μ))
    (i i' : SearchIndex n μ s) (h : psdSearchMat n μ s u j i i' ≠ 0) :
    i ∈ Set.range (fullLoc (by omega) (psdSearchLoc n μ s hn) i') := by
  have e := congrFun (congrFun (psdSearchMat_realSymmetric (n := n) (μ := μ) (s := s) u j).1 i) i'
  rw [Matrix.transpose_apply] at e
  exact psdSearchLoc_row hn hs j i' i (by rwa [e])

/-- **The PSD gadget family as native sparse data** (lines 4048-4077): hidden input `n`
one-hot strings of length `2^μ`, matrix `psdSearchMat n μ s u`, exact dyadic words,
input-independent locators. -/
def psdSearchData (n μ s : ℕ) (u : ℝ) (hn : 1 ≤ n) (hs : 2 * 2 ^ μ + 1 ≤ s) :
    Data (Fin n → Fin (2 ^ μ)) (SearchIndex n μ s) (Word (psdSearchBits n μ s u)) s :=
  bitData s (psdSearchBits n μ s u) (by omega) (padSlot _ s)
    (fullLoc (by omega) (psdSearchLoc n μ s hn)) (psdSearchTable n μ s u) oneHotBits
    (psdSearchMat n μ s u) psdSearchTable_bound psdSearchTable_decode
    (psdSearchLoc_row hn hs) (psdSearchLoc_col hn hs)

/-- The native workspace of the PSD gadget data. -/
abbrev PsdSearchSpace (n μ s : ℕ) (u : ℝ) : Type :=
  SparseFlagEmbedding.Space (SearchIndex n μ s × SearchIndex n μ s) (Word (psdSearchBits n μ s u))

/-- The Boolean family of the PSD gadget data with a spectator register (one-hot address
family with ancilla). -/
abbrev psdSearchSpecBoolean (Ω : Type*) [Fintype Ω] (n μ s : ℕ) (u : ℝ) :=
  bitSpecFamily Ω (psdSearchTable n μ s u) (Word (psdSearchBits n μ s u))

/-- The matrix of the PSD gadget data is `psdSearchMat`. -/
@[simp] theorem psdSearchData_matrix (hn : 1 ≤ n) (hs : 2 * 2 ^ μ + 1 ≤ s) :
    (psdSearchData n μ s u hn hs).matrix = psdSearchMat n μ s u := rfl

/-- **Two Boolean queries per value call** (lines 4106-4107): the native primitives of the PSD
gadget data, with an untouched spectator register, are `hardCost`-query programs over the
one-hot oracle of the hidden strings. -/
theorem implementsOn_psdSearchData_spec (Ω : Type*) [Fintype Ω] (hn : 1 ≤ n)
    (hs : 2 * 2 ^ μ + 1 ≤ s) (l : Query) :
    EncodedOracle.ImplementsOn (oneHotOracle (psdSearchSpecBoolean Ω n μ s u))
      (specOracles Ω (psdSearchData n μ s u hn hs) l)
      (ancillaEmbed (Joint Ω (PsdSearchSpace n μ s u))) (hardCost l) :=
  implementsOn_bitData_spec Ω _ _ _ _ _ _ _ _ _ _ l

/-- **The instance properties** of the PSD gadget data (lines 4074-4077, 4132-4134). -/
theorem psdSearchData_hardInstance (hn : 1 ≤ n) (hs : 2 * 2 ^ μ + 1 ≤ s) :
    HardInstance (psdSearchData n μ s u hn hs) := by
  have hP := fun j => psdSearchMat_props (n := n) hs u j
  have hR := fun j => psdSearchMat_realSymmetric (n := n) (μ := μ) (s := s) u j
  refine
    { transpose_eq := fun j => (hR j).1
      real := fun j => (hR j).2
      isHermitian := fun j => isHermitian_of_realSymmetric (hR j)
      norm_eq_one := fun j => (hP j).1
      row_norm_le := fun j => (hP j).2.1
      col_norm_le := fun j => (hP j).2.2.1
      row_norm_attained := fun j => ⟨refOne, (hP j).2.2.2.1⟩
      col_norm_attained := fun j => ⟨refOne, ?_⟩
      row_sparsity_le := fun j => (hP j).2.2.2.2.1
      col_sparsity_le := fun j => (hP j).2.2.2.2.2.1
      row_sparsity_attained := fun j => (hP j).2.2.2.2.2.2.1
      col_sparsity_attained := fun j => (hP j).2.2.2.2.2.2.2
      scale_eq := rfl
      decode_eq := fun _ => rfl
      dyadic := fun j i i' =>
        ⟨(psdSearchTable n μ s u).value (oneHotBits j) (i, i'),
          (psdSearchTable_bound (i, i') ((psdSearchTable n μ s u).bit (oneHotBits j) (i, i'))).1,
          (psdSearchTable_bound (i, i') ((psdSearchTable n μ s u).bit (oneHotBits j) (i, i'))).2,
          (psdSearchTable_decode j i i').symm⟩
      locators_const := bitData_locators_const }
  calc ∑ i, ‖psdSearchMat n μ s u j i refOne‖ ^ 2 = ∑ i, ‖psdSearchMat n μ s u j refOne i‖ ^ 2 :=
        Finset.sum_congr rfl fun i _ => by rw [entry_symm_of_transpose (hR j).1 i refOne]
    _ = 1 := (hP j).2.2.2.1

/-- **`D_X ⪰ 0`** for every hidden input (lines 4074-4075). -/
theorem psdSearchData_posSemidef (hn : 1 ≤ n) (hs : 2 * 2 ^ μ + 1 ≤ s)
    (j : Fin n → Fin (2 ^ μ)) : ((psdSearchData n μ s u hn hs).matrix j).PosSemidef :=
  psdSearchMat_posSemidef u j

end

end ODELowerBoundExtensions.Psd
