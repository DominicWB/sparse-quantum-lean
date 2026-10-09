import ODELowerBoundExtensions.Psd.Data.ScalarTable

/-!
# The scalar family as release sparse-access data

Manuscript lines 4119-4127. The PSD scalar-family
generator `psdScalarMat` (three-sparse core, dense PSD padding to sparsity exactly `s`) is
packaged as `NativeSparseBlockEncoding.Data` by `Hamiltonian.bitData`:

* `psdScalarTable_decode`, `psdScalarLoc_row`, `psdScalarLoc_col`: exact decoding and coverage;
* `psdScalarData`: the data, hidden input `n` bits; its native primitives are `hardCost`-query
  programs over the bit oracle (`implementsOn_psdScalarData_spec`, so `q ≤ 2 Q_A`, line 4125);
* `psdScalarData_hardInstance`, `psdScalarData_posSemidef`: the instance properties and
  `D_x ⪰ 0`.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

namespace ODELowerBoundExtensions.Psd

noncomputable section
open SparseHamiltonian NativeSparseBlockEncoding OracleCircuit SparseLowerBounds
  SparseLowerBounds.Hamiltonian
open scoped ComplexOrder

set_option synthInstance.maxSize 1024

variable {n s : ℕ} {u : ℝ}

/-! ### The words on each block (any hidden bits `x`) -/

section CoreWords

variable (x : Fin n → Bool)

/-- Diagonal core word `2^{F+σ}` (entry `1/2`); it reads no bit. -/
theorem psdScalarTable_value_diag (i : Fin (n + 1)) :
    (psdScalarTable n s u).value x (Sum.inl i, Sum.inl i) = 2 ^ (psdBits n u + padExp s) := by
  have ha : (psdScalarTable n s u).addr (Sum.inl i, Sum.inl i) = none := by
    simp only [psdScalarTable, scalarAddr, dif_neg (show ¬ ((i : ℕ) = i + 1) by omega)]
  rw [BitTable.value_of_addr_none _ _ ha]
  simp only [psdScalarTable, psdScalarWord, if_true]

/-- Forward edge `k = i'`: the word `-(-1)^{x_k} N_k 2^σ`. -/
theorem psdScalarTable_value_succ {i i' : Fin (n + 1)} (h : (i : ℕ) = i' + 1) :
    (psdScalarTable n s u).value x (Sum.inl i, Sum.inl i') =
      -((if x ⟨i', by have := i.isLt; omega⟩ then -1 else 1) * (psdNum n u i' : ℤ) *
        2 ^ padExp s) := by
  have ha : (psdScalarTable n s u).addr (Sum.inl i, Sum.inl i') =
      some ⟨i', by have := i.isLt; omega⟩ := by
    simp only [psdScalarTable, scalarAddr, dif_pos h]
  have hne : i ≠ i' := fun e => by subst e; omega
  rw [BitTable.value_of_addr_some _ _ ha]
  simp only [psdScalarTable, psdScalarWord, if_neg hne, if_pos h]

/-- Reverse edge `k = i`: the word `-(-1)^{x_k} N_k 2^σ`. -/
theorem psdScalarTable_value_pred {i i' : Fin (n + 1)} (h : (i' : ℕ) = i + 1) :
    (psdScalarTable n s u).value x (Sum.inl i, Sum.inl i') =
      -((if x ⟨i, by have := i'.isLt; omega⟩ then -1 else 1) * (psdNum n u i : ℤ) *
        2 ^ padExp s) := by
  have h' : ¬ (i : ℕ) = i' + 1 := by omega
  have ha : (psdScalarTable n s u).addr (Sum.inl i, Sum.inl i') =
      some ⟨i, by have := i'.isLt; omega⟩ := by
    simp only [psdScalarTable, scalarAddr, dif_neg h', dif_pos h]
  have hne : i ≠ i' := fun e => by subst e; omega
  rw [BitTable.value_of_addr_some _ _ ha]
  simp only [psdScalarTable, psdScalarWord, if_neg hne, if_neg h', if_pos h]

/-- Distant distinct core indices: the word `0`. -/
theorem psdScalarTable_value_far {i i' : Fin (n + 1)} (h0 : i ≠ i') (h1 : (i : ℕ) ≠ i' + 1)
    (h2 : (i' : ℕ) ≠ i + 1) : (psdScalarTable n s u).value x (Sum.inl i, Sum.inl i') = 0 := by
  simp only [BitTable.value, psdScalarTable, psdScalarWord, if_neg h0, if_neg h1, if_neg h2]

/-- The reference block: the eigenvalue-one word `2^B` at `(refOne, refOne)`. -/
theorem psdScalarTable_value_ref (r r' : Fin 2) :
    (psdScalarTable n s u).value x (Sum.inr (Sum.inl r), Sum.inr (Sum.inl r')) =
      if r = 1 ∧ r' = 1 then 2 ^ psdScalarBits n s u else 0 := rfl

/-- The padding block: the word `2^{F+1}` (entry `2^{-σ}`). -/
theorem psdScalarTable_value_pad (t t' : Fin s) :
    (psdScalarTable n s u).value x (Sum.inr (Sum.inr t), Sum.inr (Sum.inr t')) =
      2 ^ (psdBits n u + 1) := rfl

/-- Core-to-side words vanish. -/
theorem psdScalarTable_value_core_side (i : Fin (n + 1)) (r : Fin 2 ⊕ Fin s) :
    (psdScalarTable n s u).value x (Sum.inl i, Sum.inr r) = 0 := by
  cases r <;> rfl

/-- Side-to-core words vanish. -/
theorem psdScalarTable_value_side_core (r : Fin 2 ⊕ Fin s) (i : Fin (n + 1)) :
    (psdScalarTable n s u).value x (Sum.inr r, Sum.inl i) = 0 := by
  rcases r with r | r <;> rfl

/-- Reference-to-padding words vanish. -/
theorem psdScalarTable_value_ref_pad (r : Fin 2) (t : Fin s) :
    (psdScalarTable n s u).value x (Sum.inr (Sum.inl r), Sum.inr (Sum.inr t)) = 0 := rfl

/-- Padding-to-reference words vanish. -/
theorem psdScalarTable_value_pad_ref (t : Fin s) (r : Fin 2) :
    (psdScalarTable n s u).value x (Sum.inr (Sum.inr t), Sum.inr (Sum.inl r)) = 0 := rfl

end CoreWords

/-- **Signed edge words** at scale `2^B`, `B = F + σ + 1`: the word `-(-1)^y N_k 2^σ` is the
entry `-½ (-1)^y b'_k` of `(I - H'_x)/2`. -/
theorem psdScalarWord_div (k : ℕ) (y : Bool) :
    ((-((if y then -1 else 1) * (psdNum n u k : ℤ) * 2 ^ padExp s) : ℤ) : ℂ) /
        2 ^ psdScalarBits n s u =
      (1 / 2 : ℂ) * (0 - (psdWeight n u k : ℂ) * bitSign y) := by
  have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
  unfold psdWeight psdScalarBits
  cases y <;> simp only [bitSign, Bool.false_eq_true, if_false, if_true] <;> push_cast <;>
    rw [pow_succ, pow_add] <;> field_simp <;> ring

/-- **Exact decoding**: `word/2^B = D_x` entry on every block. -/
theorem psdScalarTable_decode (x : Fin n → Bool) (i i' : ScalarIndex n s) :
    (((psdScalarTable n s u).value x (i, i') : ℤ) : ℂ) / 2 ^ psdScalarBits n s u =
      psdScalarMat n s u x i i' := by
  unfold psdScalarMat
  rcases i with i | r | t <;> rcases i' with i' | r' | t'
  · rw [HardData.fullMatrix_core]
    simp only [psdCore, Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply, smul_eq_mul]
    by_cases h0 : i = i'
    · subst h0
      rw [psdScalarTable_value_diag x, HardData.scalarChain_far _ x (by omega) (by omega),
        if_pos rfl, psdScalarBits]
      push_cast
      rw [pow_succ]
      field_simp
      ring
    · rw [if_neg h0]
      by_cases h1 : (i : ℕ) = i' + 1
      · rw [psdScalarTable_value_succ x h1, HardData.scalarChain_succ _ x h1]
        exact psdScalarWord_div _ _
      · by_cases h2 : (i' : ℕ) = i + 1
        · rw [psdScalarTable_value_pred x h2, HardData.scalarChain_pred _ x h2]
          exact psdScalarWord_div _ _
        · rw [psdScalarTable_value_far x h0 h1 h2, HardData.scalarChain_far _ x h1 h2]
          simp
  · rw [psdScalarTable_value_core_side, HardData.fullMatrix_core_side]; simp
  · rw [psdScalarTable_value_core_side, HardData.fullMatrix_core_side]; simp
  · rw [psdScalarTable_value_side_core, HardData.fullMatrix_side_core]; simp
  · rw [psdScalarTable_value_ref, HardData.fullMatrix_ref]
    split_ifs
    · exact HardData.topWord_div _
    · simp
  · rw [psdScalarTable_value_ref_pad, HardData.fullMatrix_ref_pad]; simp
  · rw [psdScalarTable_value_side_core, HardData.fullMatrix_side_core]; simp
  · rw [psdScalarTable_value_pad_ref, HardData.fullMatrix_pad_ref]; simp
  · rw [psdScalarTable_value_pad, HardData.fullMatrix_pad, psdScalarBits,
      show psdBits n u + padExp s + 1 = psdBits n u + 1 + padExp s by omega]
    exact HardData.padWord_div _

/-! ### Coverage of the core rows -/

/-- A core row lists itself in slot `2` (the diagonal `1/2`), for `3 ≤ s`. -/
theorem psdScalarLoc_diag_mem (hn : 1 ≤ n) (hs : 3 ≤ s) (k : Fin (n + 1)) :
    (Sum.inl k : ScalarIndex n s) ∈ Set.range (psdScalarLoc n s hn k) :=
  ⟨⟨2, by omega⟩, by simp [psdScalarLoc, psdScalarLocFun]⟩

/-- **Adjacency coverage** of the core rows (both chain neighbours, slots `0` and `1`, as
`Hamiltonian.scalarLoc_adj_mem`). -/
theorem psdScalarLoc_adj_mem (hn : 1 ≤ n) (hs : 2 ≤ s) (k k' : Fin (n + 1))
    (h : (k' : ℕ) = k + 1 ∨ (k : ℕ) = k' + 1) :
    (Sum.inl k' : ScalarIndex n s) ∈ Set.range (psdScalarLoc n s hn k) := by
  obtain ⟨t, ht⟩ := scalarLoc_adj_mem hs k k' h
  refine ⟨t, ?_⟩
  change scalarLocFun n s k t = Sum.inl k' at ht
  change psdScalarLocFun n s k t = Sum.inl k'
  have ht2 : (t : ℕ) ≠ 2 := by
    intro h2
    rw [scalarLocFun, if_neg (by omega), if_neg (by omega)] at ht
    exact Sum.inr_ne_inl ht
  rw [psdScalarLocFun, if_neg ht2, ht]

/-- **Row coverage** (`3 ≤ s`). -/
theorem psdScalarLoc_row (hn : 1 ≤ n) (hs : 3 ≤ s) (x : Fin n → Bool) (i i' : ScalarIndex n s)
    (h : psdScalarMat n s u x i i' ≠ 0) :
    i' ∈ Set.range (fullLoc (by omega) (psdScalarLoc n s hn) i) := by
  unfold psdScalarMat at h
  rcases i with k | r | t <;> rcases i' with k' | r' | t'
  · rw [HardData.fullMatrix_core] at h
    by_cases h0 : k = k'
    · subst h0
      exact psdScalarLoc_diag_mem hn hs k
    · have adj : (k' : ℕ) = k + 1 ∨ (k : ℕ) = k' + 1 := by
        by_contra hc
        rw [not_or] at hc
        apply h
        simp only [psdCore, Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply, smul_eq_mul,
          if_neg h0, HardData.scalarChain_far _ x hc.2 hc.1, sub_zero, mul_zero]
      exact psdScalarLoc_adj_mem hn (by omega) k k' adj
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

/-- **Column coverage**. -/
theorem psdScalarLoc_col (hn : 1 ≤ n) (hs : 3 ≤ s) (x : Fin n → Bool) (i i' : ScalarIndex n s)
    (h : psdScalarMat n s u x i i' ≠ 0) :
    i ∈ Set.range (fullLoc (by omega) (psdScalarLoc n s hn) i') := by
  have e := congrFun (congrFun (psdScalarMat_realSymmetric (n := n) (s := s) u x).1 i) i'
  rw [Matrix.transpose_apply] at e
  exact psdScalarLoc_row hn hs x i' i (by rwa [e])

/-- **The PSD scalar family as native sparse data** (lines 4119-4121): hidden input `n` bits,
matrix `psdScalarMat n s u`, exact dyadic words, input-independent locators. -/
def psdScalarData (n s : ℕ) (u : ℝ) (hn : 1 ≤ n) (hs : 3 ≤ s) :
    Data (Fin n → Bool) (ScalarIndex n s) (Word (psdScalarBits n s u)) s :=
  bitData s (psdScalarBits n s u) (by omega) (padSlot _ s)
    (fullLoc (by omega) (psdScalarLoc n s hn)) (psdScalarTable n s u) (fun x => x)
    (psdScalarMat n s u) psdScalarTable_bound psdScalarTable_decode
    (psdScalarLoc_row hn hs) (psdScalarLoc_col hn hs)

/-- The native workspace of the PSD scalar data. -/
abbrev PsdScalarSpace (n s : ℕ) (u : ℝ) : Type :=
  SparseFlagEmbedding.Space (ScalarIndex n s × ScalarIndex n s) (Word (psdScalarBits n s u))

/-- The Boolean family of the PSD scalar data with a spectator register. -/
abbrev psdScalarSpecBoolean (Ω : Type*) [Fintype Ω] (n s : ℕ) (u : ℝ) :=
  bitSpecFamily Ω (psdScalarTable n s u) (Word (psdScalarBits n s u))

/-- The matrix of the PSD scalar data is `psdScalarMat`. -/
@[simp] theorem psdScalarData_matrix (hn : 1 ≤ n) (hs : 3 ≤ s) :
    (psdScalarData n s u hn hs).matrix = psdScalarMat n s u := rfl

/-- **Two Boolean queries per value call** (line 4125, `q ≤ 2 Q_A`): the native primitives of
the PSD scalar data, with a spectator register, are `hardCost`-query programs over the bit
oracle of the hidden bits. -/
theorem implementsOn_psdScalarData_spec (Ω : Type*) [Fintype Ω] (hn : 1 ≤ n) (hs : 3 ≤ s)
    (l : Query) :
    EncodedOracle.ImplementsOn (bitOracle (psdScalarSpecBoolean Ω n s u))
      (specOracles Ω (psdScalarData n s u hn hs) l)
      (ancillaEmbed (Joint Ω (PsdScalarSpace n s u))) (hardCost l) :=
  implementsOn_bitData_spec Ω _ _ _ _ _ _ _ _ _ _ l

/-- **The instance properties** of the PSD scalar data (lines 4074-4077, 4120-4121, 4132-4134). -/
theorem psdScalarData_hardInstance (hn : 1 ≤ n) (hs : 3 ≤ s) :
    HardInstance (psdScalarData n s u hn hs) := by
  have hP := fun x => psdScalarMat_props (n := n) hs u x
  have hR := fun x => psdScalarMat_realSymmetric (n := n) (s := s) u x
  refine
    { transpose_eq := fun x => (hR x).1
      real := fun x => (hR x).2
      isHermitian := fun x => isHermitian_of_realSymmetric (hR x)
      norm_eq_one := fun x => (hP x).1
      row_norm_le := fun x => (hP x).2.1
      col_norm_le := fun x => (hP x).2.2.1
      row_norm_attained := fun x => ⟨refOne, (hP x).2.2.2.1⟩
      col_norm_attained := fun x => ⟨refOne, ?_⟩
      row_sparsity_le := fun x => (hP x).2.2.2.2.1
      col_sparsity_le := fun x => (hP x).2.2.2.2.2.1
      row_sparsity_attained := fun x => (hP x).2.2.2.2.2.2.1
      col_sparsity_attained := fun x => (hP x).2.2.2.2.2.2.2
      scale_eq := rfl
      decode_eq := fun _ => rfl
      dyadic := fun x i i' =>
        ⟨(psdScalarTable n s u).value x (i, i'),
          (psdScalarTable_bound (i, i') ((psdScalarTable n s u).bit x (i, i'))).1,
          (psdScalarTable_bound (i, i') ((psdScalarTable n s u).bit x (i, i'))).2,
          (psdScalarTable_decode x i i').symm⟩
      locators_const := bitData_locators_const }
  calc ∑ i, ‖psdScalarMat n s u x i refOne‖ ^ 2 = ∑ i, ‖psdScalarMat n s u x refOne i‖ ^ 2 :=
        Finset.sum_congr rfl fun i _ => by rw [entry_symm_of_transpose (hR x).1 i refOne]
    _ = 1 := (hP x).2.2.2.1

/-- **`D_x ⪰ 0`** for every hidden input (lines 4120-4121). -/
theorem psdScalarData_posSemidef (hn : 1 ≤ n) (hs : 3 ≤ s) (x : Fin n → Bool) :
    ((psdScalarData n s u hn hs).matrix x).PosSemidef :=
  psdScalarMat_posSemidef u x

end

end ODELowerBoundExtensions.Psd
