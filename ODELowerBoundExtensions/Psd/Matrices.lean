import ODELowerBoundExtensions.Psd.SpinAmp

/-!
# The PSD generators of Theorem `odel:thm:psd`

Manuscript lines 4048-4077 and 4119-4121. On the index
types of the Hamiltonian lower bound (`Hamiltonian.SearchIndex`, `Hamiltonian.ScalarIndex`,
`FullIndex C s = C ⊕ (Fin 2 ⊕ Fin s)`) the PSD generators are

  `D_X = fullMatrix ((I - H'_X)/2) s = (I - H'_X)/2 ⊕ diag(0, 1) ⊕ 2^{-⌈log₂ s⌉} 𝟙𝟙ᵀ`:

* gadget family (`psdSearchMat`): `H'_X` the search-decorated chain
  `Hamiltonian.searchChain` with the rounded weights `psdWeight n u` of `B_n` and one gadget
  `U_{j_k}` per edge (adjoints on reverse edges), on `ℂ^{n+1} ⊗ ℂ^m`;
* scalar family (`psdScalarMat`): the gadgets replaced by the signs `(-1)^{x_k}`
  (`Hamiltonian.scalarChain`), lines 4119-4121.

The block `diag(0, 1)` is the isolated reference of eigenvalue zero and the isolated eigenvalue
one of lines 4074-4075. The last block is the **known positive semidefinite dense padding** of lines
4132-4134 (the padding block of `Hamiltonian.fullMatrix`, a nonnegative multiple of `𝟙𝟙ᵀ`): it
makes the maximum row and column sparsity exactly `s`, and it is never occupied by the start
vector. Properties (lines 4074-4077): real symmetric (so the generator is Hermitian, `H = 0`
and `G = D_X`), positive semidefinite (`psdSearchMat_posSemidef`; the diagonal is `1/2` on the
path block),
operator norm exactly one, every row and column of Euclidean norm at most one with maximum
exactly one (the eigenvalue-one vertex `refOne`), maximum row and column sparsity exactly `s`
(core rows have at most `2m + 1`, resp. `3`, nonzeros; padding rows exactly `s`). The bundles
`psdSearchMat_props`, `psdScalarMat_props` are `Hamiltonian.fullMatrix_props` applied to the
core `psdCore H'_X`.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

namespace ODELowerBoundExtensions.Psd

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.Hamiltonian
open scoped Matrix InnerProductSpace Matrix.Norms.L2Operator ComplexOrder

/-- **The gadget-family generator** (lines 4048-4077): `(I - H'_X)/2` on the decorated path
block with the rounded weights of `B_n`, the isolated eigenvalues `0` (reference) and `1`, and
the dense PSD padding. Hidden input: `n` one-hot strings of length `2^μ`. -/
def psdSearchMat (n μ s : ℕ) (u : ℝ) (j : Fin n → Fin (2 ^ μ)) :
    Matrix (SearchIndex n μ s) (SearchIndex n μ s) ℂ :=
  fullMatrix (psdCore (searchChain n (2 ^ μ) (psdWeight n u) j)) s

/-- **The scalar-family generator** (lines 4119-4121): the gadgets replaced by the signs
`(-1)^{x_k}`. Hidden input: `n` bits. -/
def psdScalarMat (n s : ℕ) (u : ℝ) (x : Fin n → Bool) :
    Matrix (ScalarIndex n s) (ScalarIndex n s) ℂ :=
  fullMatrix (psdCore (scalarChain n (psdWeight n u) x)) s

section Full

/-- A block-diagonal matrix with positive semidefinite diagonal blocks is positive
semidefinite (the quadratic form splits over `m ⊕ p`). -/
theorem posSemidef_fromBlocks_diag {m p : Type} [Fintype m] [Fintype p]
    {A : Matrix m m ℂ} {D : Matrix p p ℂ} (hA : A.PosSemidef) (hD : D.PosSemidef) :
    (Matrix.fromBlocks A 0 0 D).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (hA.1.fromBlocks (by simp) hD.1) fun x => ?_
  have hx : star x = Sum.elim (star (x ∘ Sum.inl)) (star (x ∘ Sum.inr)) := by
    ext (i | i) <;> rfl
  rw [Matrix.fromBlocks_mulVec, hx, sumElim_dotProduct_sumElim]
  simp only [Matrix.zero_mulVec, zero_add, add_zero]
  exact add_nonneg (hA.dotProduct_mulVec_nonneg _) (hD.dotProduct_mulVec_nonneg _)

/-- The isolated reference block `diag(0, 1)` is positive semidefinite. -/
theorem posSemidef_refBlock : refBlock.PosSemidef := by
  refine Matrix.PosSemidef.diagonal fun i => ?_
  fin_cases i <;> simp

/-- The dense padding block `2^{-⌈log₂ s⌉} 𝟙𝟙ᵀ` is positive semidefinite (lines 4132-4134). -/
theorem posSemidef_padBlock (s : ℕ) : (padBlock s).PosSemidef := by
  have h : padBlock s = ((2 : ℝ) ^ padExp s)⁻¹ •
      Matrix.vecMulVec (fun _ : Fin s => (1 : ℂ)) (star fun _ : Fin s => (1 : ℂ)) := by
    ext i i'
    simp [padBlock, Matrix.vecMulVec_apply, Complex.real_smul]
  rw [h]
  exact (Matrix.posSemidef_vecMulVec_self_star _).smul (by positivity)

variable {C : Type} [Fintype C] [DecidableEq C]

/-- The full matrix of a PSD core is PSD (`diag(0, 1)` and `2^{-σ} 𝟙𝟙ᵀ` are PSD). -/
theorem posSemidef_fullMatrix {H : Matrix C C ℂ} (hH : H.PosSemidef) (s : ℕ) :
    (fullMatrix H s).PosSemidef :=
  posSemidef_fromBlocks_diag hH (posSemidef_fromBlocks_diag posSemidef_refBlock
    (posSemidef_padBlock s))

omit [Fintype C] in
/-- Entries of `(I - H)/2`. -/
theorem psdCore_apply (H : Matrix C C ℂ) (c c' : C) :
    psdCore H c c' = (1 / 2 : ℂ) * ((if c = c' then 1 else 0) - H c c') := by
  simp [psdCore, Matrix.one_apply]

omit [Fintype C] in
/-- `(I - H)/2` is symmetric when `H` is. -/
theorem psdCore_transpose {H : Matrix C C ℂ} (hH : Hᵀ = H) : (psdCore H)ᵀ = psdCore H := by
  simp only [psdCore, Matrix.transpose_smul, Matrix.transpose_sub, Matrix.transpose_one, hH]

omit [Fintype C] in
/-- `(I - H)/2` has real entries when `H` has. -/
theorem star_psdCore_apply {H : Matrix C C ℂ} (hH : ∀ c c', star (H c c') = H c c')
    (c c' : C) : star (psdCore H c c') = psdCore H c c' := by
  rw [psdCore_apply, star_mul', star_sub, hH]
  congr 1
  · simp
  · congr 1
    split_ifs <;> simp

/-- Row masses of `(I - H)/2` for a core with zero diagonal and row masses at most one:
`(1 + Σ_j |H_ij|²)/4 ≤ 1/2 ≤ 1`. -/
theorem sum_sq_psdCore_le {H : Matrix C C ℂ} (hdiag : ∀ c, H c c = 0)
    (hrow : ∀ c, ∑ c', ‖H c c'‖ ^ 2 ≤ 1) (c : C) : ∑ c', ‖psdCore H c c'‖ ^ 2 ≤ 1 := by
  have hpt : ∀ c', ‖psdCore H c c'‖ ^ 2 =
      (1 / 4 : ℝ) * ((if c = c' then 1 else 0) + ‖H c c'‖ ^ 2) := fun c' => by
    rw [psdCore_apply]
    by_cases h : c = c'
    · subst h
      simp only [if_true, hdiag, sub_zero, mul_one, norm_zero]
      norm_num
    · simp only [if_neg h, zero_sub, norm_mul, norm_neg, mul_pow]
      norm_num
  simp only [hpt, ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  linarith [hrow c]

/-- A row of `(I - H)/2` has at most one more nonzero than the row of `H` (the diagonal). -/
theorem card_row_psdCore_le (H : Matrix C C ℂ) (c : C) :
    (Finset.univ.filter fun c' => psdCore H c c' ≠ 0).card ≤
      (Finset.univ.filter fun c' => H c c' ≠ 0).card + 1 := by
  refine (Finset.card_le_card fun c' hc' => ?_).trans (Finset.card_insert_le c _)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert] at hc' ⊢
  by_cases h : c' = c
  · exact Or.inl h
  · refine Or.inr fun h0 => hc' ?_
    rw [psdCore_apply, if_neg (Ne.symm h), h0]
    simp

end Full

variable {n μ s : ℕ}

/-- The gadget core `(I - H'_X)/2` has row sparsity at most `2m + 1` (lines 4076-4077: the two
neighbouring register blocks and the diagonal). -/
theorem card_row_psdSearchCore_le (u : ℝ) (j : Fin n → Fin (2 ^ μ)) (p : SearchCore n μ) :
    (Finset.univ.filter fun q =>
      psdCore (searchChain n (2 ^ μ) (psdWeight n u) j) p q ≠ 0).card ≤ 2 * 2 ^ μ + 1 :=
  (card_row_psdCore_le _ p).trans (Nat.add_le_add_right (card_row_searchChain_le _ j p) 1)

/-- The scalar core `(I - H'_x)/2` is three-sparse (lines 4120-4121). -/
theorem card_row_psdScalarCore_le (u : ℝ) (x : Fin n → Bool) (i : Fin (n + 1)) :
    (Finset.univ.filter fun i' => psdCore (scalarChain n (psdWeight n u) x) i i' ≠ 0).card ≤ 3 :=
  (card_row_psdCore_le _ i).trans (Nat.add_le_add_right (card_row_scalarChain_le _ x i) 1)

/-- The gadget-family generator is real symmetric. -/
theorem psdSearchMat_realSymmetric (u : ℝ) (j : Fin n → Fin (2 ^ μ)) :
    (psdSearchMat n μ s u j)ᵀ = psdSearchMat n μ s u j ∧
      ∀ i i', star (psdSearchMat n μ s u j i i') = psdSearchMat n μ s u j i i' :=
  ⟨fullMatrix_transpose (psdCore_transpose (searchChain_transpose _ _ _ _)) s,
    star_fullMatrix_apply (star_psdCore_apply fun p q => star_searchChain_apply _ _ p q) s⟩

/-- The scalar-family generator is real symmetric. -/
theorem psdScalarMat_realSymmetric (u : ℝ) (x : Fin n → Bool) :
    (psdScalarMat n s u x)ᵀ = psdScalarMat n s u x ∧
      ∀ i i', star (psdScalarMat n s u x i i') = psdScalarMat n s u x i i' :=
  ⟨fullMatrix_transpose (psdCore_transpose (scalarChain_transpose _ _ _)) s,
    star_fullMatrix_apply (star_psdCore_apply fun i i' => star_scalarChain_apply _ _ i i') s⟩

/-- **`D_X ⪰ 0`** for the gadget family (lines 4074-4075). -/
theorem psdSearchMat_posSemidef (u : ℝ) (j : Fin n → Fin (2 ^ μ)) :
    (psdSearchMat n μ s u j).PosSemidef := by
  refine posSemidef_fullMatrix (posSemidef_psdCore (isHermitian_searchChain _ _ _ _) ?_) s
  rw [norm_searchChain (by positivity)]
  exact norm_pathMatrix_psdWeight_le n u

/-- **`D_X ⪰ 0`** for the scalar family (lines 4120-4121). -/
theorem psdScalarMat_posSemidef (u : ℝ) (x : Fin n → Bool) :
    (psdScalarMat n s u x).PosSemidef := by
  refine posSemidef_fullMatrix (posSemidef_psdCore (isHermitian_scalarChain _ _ _) ?_) s
  rw [norm_scalarChain]
  exact norm_pathMatrix_psdWeight_le n u

/-- **Norm exactly one, row/column norms at most one with maximum exactly one, sparsity
exactly `s`** for the gadget family (lines 4074-4077, 4111-4112, 4132-4134), for
`2·2^μ + 1 ≤ s`. -/
theorem psdSearchMat_props (hs : 2 * 2 ^ μ + 1 ≤ s) (u : ℝ) (j : Fin n → Fin (2 ^ μ)) :
    ‖SparseStateOverlap.matrixOperator (psdSearchMat n μ s u j)‖ = 1 ∧
      (∀ i, ∑ i', ‖psdSearchMat n μ s u j i i'‖ ^ 2 ≤ 1) ∧
      (∀ i', ∑ i, ‖psdSearchMat n μ s u j i i'‖ ^ 2 ≤ 1) ∧
      ∑ i', ‖psdSearchMat n μ s u j refOne i'‖ ^ 2 = 1 ∧
      (∀ i, (Finset.univ.filter fun i' => psdSearchMat n μ s u j i i' ≠ 0).card ≤ s) ∧
      (∀ i', (Finset.univ.filter fun i => psdSearchMat n μ s u j i i' ≠ 0).card ≤ s) ∧
      (∃ i, (Finset.univ.filter fun i' => psdSearchMat n μ s u j i i' ≠ 0).card = s) ∧
      ∃ i', (Finset.univ.filter fun i => psdSearchMat n μ s u j i i' ≠ 0).card = s := by
  have hs1 : 1 ≤ s := by omega
  have hdiag : ∀ p, searchChain n (2 ^ μ) (psdWeight n u) j p p = 0 := fun p => by
    simp only [searchChain, Matrix.of_apply]
    rw [dif_neg (by omega), dif_neg (by omega)]
  refine fullMatrix_props hs1 (fun p q => ?_) ?_
    (sum_sq_psdCore_le hdiag
      (HsInstance.sum_sq_searchChain_le (fun k => (psdWeight_le n u k).1)
        (fun k _ => (psdWeight_le n u k).2) j))
    (fun p => (card_row_psdSearchCore_le u j p).trans hs)
  · have := congrFun (congrFun (psdCore_transpose
      (searchChain_transpose n (2 ^ μ) (psdWeight n u) j)) q) p
    rwa [Matrix.transpose_apply] at this
  · refine norm_psdCore_le ?_
    rw [norm_searchChain (by positivity)]
    exact norm_pathMatrix_psdWeight_le n u

/-- The same properties for the scalar family (three-sparse core, lines 4120-4121), for `3 ≤ s`. -/
theorem psdScalarMat_props (hs : 3 ≤ s) (u : ℝ) (x : Fin n → Bool) :
    ‖SparseStateOverlap.matrixOperator (psdScalarMat n s u x)‖ = 1 ∧
      (∀ i, ∑ i', ‖psdScalarMat n s u x i i'‖ ^ 2 ≤ 1) ∧
      (∀ i', ∑ i, ‖psdScalarMat n s u x i i'‖ ^ 2 ≤ 1) ∧
      ∑ i', ‖psdScalarMat n s u x refOne i'‖ ^ 2 = 1 ∧
      (∀ i, (Finset.univ.filter fun i' => psdScalarMat n s u x i i' ≠ 0).card ≤ s) ∧
      (∀ i', (Finset.univ.filter fun i => psdScalarMat n s u x i i' ≠ 0).card ≤ s) ∧
      (∃ i, (Finset.univ.filter fun i' => psdScalarMat n s u x i i' ≠ 0).card = s) ∧
      ∃ i', (Finset.univ.filter fun i => psdScalarMat n s u x i i' ≠ 0).card = s := by
  have hdiag : ∀ i, scalarChain n (psdWeight n u) x i i = 0 := fun i => by
    simp only [scalarChain, Matrix.of_apply]
    rw [dif_neg (by omega), dif_neg (by omega)]
  refine fullMatrix_props (by omega) (fun i i' => ?_) ?_
    (sum_sq_psdCore_le hdiag
      (HsInstance.sum_sq_scalarChain_le (fun k => (psdWeight_le n u k).1)
        (fun k _ => (psdWeight_le n u k).2) x))
    (fun i => (card_row_psdScalarCore_le u x i).trans hs)
  · have := congrFun (congrFun (psdCore_transpose
      (scalarChain_transpose n (psdWeight n u) x)) i') i
    rwa [Matrix.transpose_apply] at this
  · refine norm_psdCore_le ?_
    rw [norm_scalarChain]
    exact norm_pathMatrix_psdWeight_le n u

end

end ODELowerBoundExtensions.Psd
