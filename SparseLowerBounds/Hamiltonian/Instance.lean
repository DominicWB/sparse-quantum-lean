import SparseLowerBounds.Helpers.HsInstance.ChainRows

set_option synthInstance.maxHeartbeats 400000

section
/-!
# The hard Hamiltonians

Manuscript: the chain construction of Section `part:hsl` (reference vertices) and the end of the
proof of Theorem `hsl:thm:main` (dimension and exact sparsity). A core chain `H` on `C` is completed
to

  `fullMatrix H s = H ⊕ diag(0, 1) ⊕ 2^{-⌈log₂ s⌉} 𝟙𝟙ᵀ`

on `FullIndex C s = C ⊕ (Fin 2 ⊕ Fin s)`: an isolated zero-energy reference
vertex `r₀` (`refZero`), an isolated energy-one vertex (`refOne`), and the known
dense `s × s` padding block (`padBlock`), which has norm `s 2^{-⌈log₂ s⌉} ≤ 1`,
exact dyadic entries and exactly `s` nonzeros per row and column. The input
state never occupies the padding.

The three families' Hamiltonians (`searchHam`, `scalarHam`) use the rounded
dyadic weights of `Hamiltonian/Rounding`:

* search-decorated chain (time and mixed families) on
  `SearchCore n μ = Fin (n+1) × Fin (2^μ)`, weights `b'_k` of `a B_n`;
* signed scalar chain (precision family) on `Fin (n+1)`, weights `b'_k` of `B_n`.

Properties (Theorem `hsl:thm:main`): real symmetric; operator
norm exactly one; maximum row and column Euclidean norms exactly one (every
row/column norm at most one, the energy-one vertex attaining it, which is the
release's `hrow`/`hcol` promise with `η = 1`); maximum row and column sparsity
exactly `s`; dimension `(n+1)2^μ + 2 + s` and `n + 3 + s`.
-/

namespace SparseLowerBounds.Hamiltonian

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator

/-- Core indices, the two reference vertices and the padding block. -/
abbrev FullIndex (C : Type) (s : ℕ) : Type := C ⊕ (Fin 2 ⊕ Fin s)

/-- `⌈log₂ s⌉`. -/
def padExp (s : ℕ) : ℕ := Nat.clog 2 s

/-- The known padding block `2^{-⌈log₂ s⌉} 𝟙𝟙ᵀ` (the end of the proof of Theorem `hsl:thm:main`). -/
def padBlock (s : ℕ) : Matrix (Fin s) (Fin s) ℂ := Matrix.of fun _ _ => ((2 : ℂ) ^ padExp s)⁻¹

/-- The isolated reference vertices: energy `0` (`r₀`) and energy `1`. -/
def refBlock : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal ![0, 1]

/-- `H ⊕ diag(0, 1) ⊕ padBlock s`. -/
def fullMatrix {C : Type} [Fintype C] [DecidableEq C] (H : Matrix C C ℂ) (s : ℕ) :
    Matrix (FullIndex C s) (FullIndex C s) ℂ :=
  Matrix.fromBlocks H 0 0 (Matrix.fromBlocks refBlock 0 0 (padBlock s))

/-- The zero-energy reference vertex `r₀`. -/
def refZero {C : Type} {s : ℕ} : FullIndex C s := Sum.inr (Sum.inl 0)

/-- The energy-one vertex. -/
def refOne {C : Type} {s : ℕ} : FullIndex C s := Sum.inr (Sum.inl 1)

/-- The search core `ℂ^{n+1} ⊗ ℂ^{2^μ}`. -/
abbrev SearchCore (n μ : ℕ) : Type := Fin (n + 1) × Fin (2 ^ μ)

/-- Indices of the search families. -/
abbrev SearchIndex (n μ s : ℕ) : Type := FullIndex (SearchCore n μ) s

/-- Indices of the precision family. -/
abbrev ScalarIndex (n s : ℕ) : Type := FullIndex (Fin (n + 1)) s

/-- The search-family Hamiltonian: decorated chain with the rounded weights of
`a B_n`, plus reference vertices and padding. Hidden input: `n` one-hot strings
of length `2^μ`. -/
def searchHam (n μ s : ℕ) (a τ : ℝ) (j : Fin n → Fin (2 ^ μ)) :
    Matrix (SearchIndex n μ s) (SearchIndex n μ s) ℂ :=
  fullMatrix (searchChain n (2 ^ μ) (chainWeight n a τ) j) s

/-- The precision-family Hamiltonian: signed scalar chain with the rounded
weights of `B_n`, plus reference vertices and padding. Hidden input: `n` bits. -/
def scalarHam (n s : ℕ) (τ : ℝ) (x : Fin n → Bool) :
    Matrix (ScalarIndex n s) (ScalarIndex n s) ℂ :=
  fullMatrix (scalarChain n (chainWeight n 1 τ) x) s

/-! ### Block-diagonal matrices: exponential and norm -/

section Blocks

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- **Block-diagonal exponential**: `e^{-iτ(A ⊕ B)}` acts blockwise. No
Hermiticity is needed (`readout_expectation` holds for every core `H`). -/
theorem evolve_fromBlocks_zero (A : Matrix α α ℂ) (B : Matrix β β ℂ) (τ : ℝ)
    (v : EuclideanSpace ℂ (α ⊕ β)) :
    evolve (Matrix.fromBlocks A 0 0 B) τ v =
      WithLp.toLp 2 fun i => Sum.elim
        (fun a => evolve A τ (WithLp.toLp 2 fun a' => v (Sum.inl a')) a)
        (fun b => evolve B τ (WithLp.toLp 2 fun b' => v (Sum.inr b')) b) i :=
  HsInstance.evolve_fromBlocks_zero A B τ v

/-- The `L²` norm of a block-diagonal matrix is the larger block norm. -/
theorem norm_fromBlocks_zero (A : Matrix α α ℂ) (B : Matrix β β ℂ) :
    ‖Matrix.fromBlocks A 0 0 B‖ = max ‖A‖ ‖B‖ :=
  HsInstance.norm_fromBlocks_zero A B

end Blocks

/-! ### Reference vertices and padding (the chain construction of Section `part:hsl` and the end of the proof of Theorem `hsl:thm:main`) -/

/-- `s ≤ 2^{⌈log₂ s⌉}` (`Nat.le_pow_clog`). -/
theorem le_two_pow_padExp (s : ℕ) : s ≤ 2 ^ padExp s :=
  Nat.le_pow_clog (by norm_num) s

/-- Every padding entry is the nonzero dyadic `2^{-⌈log₂ s⌉}`. -/
theorem padBlock_apply_ne_zero (s : ℕ) (p q : Fin s) : padBlock s p q ≠ 0 := by
  simp [padBlock]

/-- **The padding block has norm `s 2^{-⌈log₂ s⌉} ≤ 1`** (the end of the proof of Theorem
`hsl:thm:main`; Schur test with `v = 1`). -/
theorem norm_padBlock_le (s : ℕ) : ‖padBlock s‖ ≤ 1 := by
  refine norm_le_of_schur (padBlock s) (fun _ _ => ((2 : ℝ) ^ padExp s)⁻¹) (fun _ _ => rfl)
    (fun _ _ => by simp [padBlock]) (fun _ => 1) (fun _ => one_pos) zero_le_one fun _ => ?_
  simp only [mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h : (s : ℝ) ≤ 2 ^ padExp s := by exact_mod_cast le_two_pow_padExp s
  rw [mul_inv_le_iff₀ (by positivity)]
  linarith

theorem norm_refBlock : ‖refBlock‖ = 1 := by
  rw [refBlock, Matrix.l2_opNorm_diagonal]
  apply le_antisymm
  · refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
    fin_cases i <;> simp
  · have := norm_le_pi_norm (![0, 1] : Fin 2 → ℂ) 1
    simpa using this

/-- `r₀` is a zero-energy eigenvector of the reference block. -/
theorem evolve_refBlock_single_zero (τ : ℝ) :
    evolve refBlock τ (EuclideanSpace.single 0 1) = EuclideanSpace.single 0 1 := by
  refine HsInstance.evolve_apply_of_matrixOperator_eq_zero refBlock _ ?_ τ
  ext i
  fin_cases i <;>
    simp [refBlock, SparseHamiltonian.SparseStateOverlap.matrixOperator_apply]

theorem padBlock_transpose (s : ℕ) : (padBlock s)ᵀ = padBlock s :=
  Matrix.ext fun _ _ => rfl

theorem sum_sq_padBlock_le (s : ℕ) (p : Fin s) : ∑ q, ‖padBlock s p q‖ ^ 2 ≤ 1 := by
  simp only [padBlock, Matrix.of_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, norm_inv, norm_pow, RCLike.norm_ofNat]
  have h : (s : ℝ) ≤ 2 ^ padExp s := by exact_mod_cast le_two_pow_padExp s
  have h1 : (1 : ℝ) ≤ 2 ^ padExp s := one_le_pow₀ (by norm_num)
  rw [inv_pow, mul_inv_le_iff₀ (by positivity)]
  nlinarith

theorem sum_sq_padBlock_col_le (s : ℕ) (q : Fin s) : ∑ p, ‖padBlock s p q‖ ^ 2 ≤ 1 :=
  sum_sq_padBlock_le s q

theorem card_padBlock_row (s : ℕ) (p : Fin s) :
    (Finset.univ.filter fun q => padBlock s p q ≠ 0).card = s := by
  rw [Finset.filter_true_of_mem (fun q _ => padBlock_apply_ne_zero s p q), Finset.card_univ,
    Fintype.card_fin]

theorem card_padBlock_col (s : ℕ) (q : Fin s) :
    (Finset.univ.filter fun p => padBlock s p q ≠ 0).card = s := by
  rw [Finset.filter_true_of_mem (fun p _ => padBlock_apply_ne_zero s p q), Finset.card_univ,
    Fintype.card_fin]

theorem sum_sq_refBlock_le (r : Fin 2) : ∑ r', ‖refBlock r r'‖ ^ 2 ≤ 1 := by
  fin_cases r <;> simp [refBlock, Fin.sum_univ_two]

theorem sum_sq_refBlock_col_le (r' : Fin 2) : ∑ r, ‖refBlock r r'‖ ^ 2 ≤ 1 := by
  fin_cases r' <;> simp [refBlock, Fin.sum_univ_two]

theorem card_refBlock_row_le (r : Fin 2) :
    (Finset.univ.filter fun r' => refBlock r r' ≠ 0).card ≤ 1 := by
  refine (Finset.card_le_card (t := {r}) fun x hx => ?_).trans (Finset.card_singleton r).le
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, refBlock] at hx
  rw [Finset.mem_singleton]
  by_contra h
  exact hx (Matrix.diagonal_apply_ne _ fun h' => h h'.symm)

theorem card_refBlock_col_le (r' : Fin 2) :
    (Finset.univ.filter fun r => refBlock r r' ≠ 0).card ≤ 1 := by
  refine (Finset.card_le_card (t := {r'}) fun x hx => ?_).trans (Finset.card_singleton r').le
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, refBlock] at hx
  rw [Finset.mem_singleton]
  by_contra h
  exact hx (Matrix.diagonal_apply_ne _ h)

section Full

variable {C : Type} [Fintype C] [DecidableEq C]

/-- The energy-one vertex makes the full norm exactly one once `‖H‖ ≤ 1` (the chain construction of
Section `part:hsl` and the end of the proof of Theorem `hsl:thm:main`). -/
theorem norm_fullMatrix {H : Matrix C C ℂ} (hH : ‖H‖ ≤ 1) (s : ℕ) : ‖fullMatrix H s‖ = 1 := by
  rw [fullMatrix, norm_fromBlocks_zero, norm_fromBlocks_zero, norm_refBlock,
    max_eq_left (norm_padBlock_le s), max_eq_right hH]

/-- The core block evolves on its own: `e^{-iτ fullMatrix H s}` maps the
core-supported vector of `v` to the core-supported vector of `e^{-iτH} v`
(this is `coreVec`, written out). -/
theorem evolve_fullMatrix_core (H : Matrix C C ℂ) (s : ℕ) (τ : ℝ) (v : EuclideanSpace ℂ C) :
    evolve (fullMatrix H s) τ (WithLp.toLp 2 fun i => Sum.elim (fun c => v c) (fun _ => 0) i) =
      WithLp.toLp 2 fun i => Sum.elim (fun c => evolve H τ v c) (fun _ => 0) i := by
  rw [fullMatrix, evolve_fromBlocks_zero]
  ext i
  cases i with
  | inl c => simp
  | inr b =>
    have h0 : (WithLp.toLp 2 fun _ : Fin 2 ⊕ Fin s => (0 : ℂ)) = 0 := rfl
    simp [h0]

theorem fullMatrix_transpose {H : Matrix C C ℂ} (hH : Hᵀ = H) (s : ℕ) :
    (fullMatrix H s)ᵀ = fullMatrix H s := by
  simp only [fullMatrix, Matrix.fromBlocks_transpose, Matrix.transpose_zero, hH, refBlock,
    Matrix.diagonal_transpose, padBlock_transpose]

theorem star_fullMatrix_apply {H : Matrix C C ℂ} (hH : ∀ c c', star (H c c') = H c c') (s : ℕ)
    (i i' : FullIndex C s) : star (fullMatrix H s i i') = fullMatrix H s i i' := by
  refine HsInstance.star_fromBlocks_apply hH (HsInstance.star_fromBlocks_apply ?_ ?_) i i'
  · intro r r'
    fin_cases r <;> fin_cases r' <;> simp [refBlock]
  · intro p q
    simp [padBlock]

/-- Row Euclidean norms at most one (padding rows: `s 4^{-⌈log₂ s⌉} ≤ 1`). -/
theorem sum_sq_fullMatrix_le {H : Matrix C C ℂ} (hH : ∀ c, ∑ c', ‖H c c'‖ ^ 2 ≤ 1) (s : ℕ)
    (i : FullIndex C s) : ∑ i', ‖fullMatrix H s i i'‖ ^ 2 ≤ 1 :=
  HsInstance.sum_sq_fromBlocks_row_le hH
    (HsInstance.sum_sq_fromBlocks_row_le sum_sq_refBlock_le (sum_sq_padBlock_le s)) i

/-- Column Euclidean norms at most one. -/
theorem sum_sq_fullMatrix_col_le {H : Matrix C C ℂ} (hH : ∀ c', ∑ c, ‖H c c'‖ ^ 2 ≤ 1) (s : ℕ)
    (i' : FullIndex C s) : ∑ i, ‖fullMatrix H s i i'‖ ^ 2 ≤ 1 :=
  HsInstance.sum_sq_fromBlocks_col_le hH
    (HsInstance.sum_sq_fromBlocks_col_le sum_sq_refBlock_col_le (sum_sq_padBlock_col_le s)) i'

/-- The energy-one vertex attains row norm one. -/
theorem sum_sq_fullMatrix_refOne (H : Matrix C C ℂ) (s : ℕ) :
    ∑ i', ‖fullMatrix H s refOne i'‖ ^ 2 = 1 := by
  rw [refOne, fullMatrix, HsInstance.sum_sq_fromBlocks_row_inr,
    HsInstance.sum_sq_fromBlocks_row_inl]
  simp [refBlock, Fin.sum_univ_two]

/-- Row sparsity at most `s` when every core row has at most `s` nonzeros. -/
theorem card_row_fullMatrix_le {H : Matrix C C ℂ} {s : ℕ} (hs : 1 ≤ s)
    (hH : ∀ c, (Finset.univ.filter fun c' => H c c' ≠ 0).card ≤ s) (i : FullIndex C s) :
    (Finset.univ.filter fun i' => fullMatrix H s i i' ≠ 0).card ≤ s :=
  HsInstance.card_fromBlocks_row_le hH (HsInstance.card_fromBlocks_row_le
    (fun r => (card_refBlock_row_le r).trans hs) (fun p => (card_padBlock_row s p).le)) i

theorem card_col_fullMatrix_le {H : Matrix C C ℂ} {s : ℕ} (hs : 1 ≤ s)
    (hH : ∀ c', (Finset.univ.filter fun c => H c c' ≠ 0).card ≤ s) (i' : FullIndex C s) :
    (Finset.univ.filter fun i => fullMatrix H s i i' ≠ 0).card ≤ s :=
  HsInstance.card_fromBlocks_col_le hH (HsInstance.card_fromBlocks_col_le
    (fun r => (card_refBlock_col_le r).trans hs) (fun p => (card_padBlock_col s p).le)) i'

/-- A padding row has exactly `s` nonzeros (the end of the proof of Theorem `hsl:thm:main`). -/
theorem card_row_fullMatrix_pad (H : Matrix C C ℂ) (s : ℕ) (p : Fin s) :
    (Finset.univ.filter fun i' => fullMatrix H s (Sum.inr (Sum.inr p)) i' ≠ 0).card = s := by
  rw [fullMatrix, HsInstance.card_fromBlocks_row_inr, HsInstance.card_fromBlocks_row_inr,
    card_padBlock_row]

theorem card_col_fullMatrix_pad (H : Matrix C C ℂ) (s : ℕ) (p : Fin s) :
    (Finset.univ.filter fun i => fullMatrix H s i (Sum.inr (Sum.inr p)) ≠ 0).card = s := by
  rw [fullMatrix, HsInstance.card_fromBlocks_col_inr, HsInstance.card_fromBlocks_col_inr,
    card_padBlock_col]

end Full

/-! ### Row masses and sparsity of the chains -/

/-- Row Euclidean norms of a decorated chain with weights `0 ≤ c_k ≤ b_k`:
row `(k, ·)` has mass `c_{k-1}² + c_k² ≤ 1` (gadget rows and columns are unit
vectors; `spinWeight_sq_add_sq_le`). -/
theorem sum_sq_searchChain_le {n m : ℕ} {c : ℕ → ℝ} (hc0 : ∀ k, 0 ≤ c k)
    (hc : ∀ k, k < n → c k ≤ spinWeight n k) (j : Fin n → Fin m) (p : Fin (n + 1) × Fin m) :
    ∑ q, ‖searchChain n m c j p q‖ ^ 2 ≤ 1 :=
  HsInstance.sum_sq_searchChain_le hc0 hc j p

theorem sum_sq_scalarChain_le {n : ℕ} {c : ℕ → ℝ} (hc0 : ∀ k, 0 ≤ c k)
    (hc : ∀ k, k < n → c k ≤ spinWeight n k) (x : Fin n → Bool) (i : Fin (n + 1)) :
    ∑ i', ‖scalarChain n c x i i'‖ ^ 2 ≤ 1 :=
  HsInstance.sum_sq_scalarChain_le hc0 hc x i

/-- A decorated-chain row meets at most two dense `m × m` blocks (the chain construction of Section
`part:hsl`: sparsity at most `2m`). -/
theorem card_row_searchChain_le {n m : ℕ} (c : ℕ → ℝ) (j : Fin n → Fin m)
    (p : Fin (n + 1) × Fin m) :
    (Finset.univ.filter fun q => searchChain n m c j p q ≠ 0).card ≤ 2 * m :=
  HsInstance.card_row_searchChain_le c j p

/-- The scalar chain is two-sparse (Lemma `hsl:lem:precision`). -/
theorem card_row_scalarChain_le {n : ℕ} (c : ℕ → ℝ) (x : Fin n → Bool) (i : Fin (n + 1)) :
    (Finset.univ.filter fun i' => scalarChain n c x i i' ≠ 0).card ≤ 2 :=
  HsInstance.card_row_scalarChain_le c x i

variable {n μ s : ℕ}

theorem card_searchIndex (n μ s : ℕ) :
    Fintype.card (SearchIndex n μ s) = (n + 1) * 2 ^ μ + 2 + s := by
  simp only [SearchIndex, FullIndex, SearchCore, Fintype.card_sum, Fintype.card_prod,
    Fintype.card_fin]
  ring

theorem card_scalarIndex (n s : ℕ) : Fintype.card (ScalarIndex n s) = n + 3 + s := by
  simp only [ScalarIndex, FullIndex, Fintype.card_sum, Fintype.card_fin]
  omega

/-- Real symmetric (Theorem `hsl:thm:main`). -/
theorem searchHam_realSymmetric (a τ : ℝ) (j : Fin n → Fin (2 ^ μ)) :
    (searchHam n μ s a τ j)ᵀ = searchHam n μ s a τ j ∧
      ∀ i i', star (searchHam n μ s a τ j i i') = searchHam n μ s a τ j i i' :=
  ⟨fullMatrix_transpose (searchChain_transpose _ _ _ _) s,
    star_fullMatrix_apply (fun p q => star_searchChain_apply _ _ p q) s⟩

theorem scalarHam_realSymmetric (τ : ℝ) (x : Fin n → Bool) :
    (scalarHam n s τ x)ᵀ = scalarHam n s τ x ∧
      ∀ i i', star (scalarHam n s τ x i i') = scalarHam n s τ x i i' :=
  ⟨fullMatrix_transpose (scalarChain_transpose _ _ _) s,
    star_fullMatrix_apply (fun i i' => star_scalarChain_apply _ _ i i') s⟩

/-- The common property bundle of `fullMatrix H s` for a symmetric core `H`
of norm, row masses at most one and row sparsity at most `s ≥ 1`. -/
theorem fullMatrix_props {C : Type} [Fintype C] [DecidableEq C] {H : Matrix C C ℂ}
    (hs : 1 ≤ s) (hsym : ∀ c c', H c c' = H c' c) (hnorm : ‖H‖ ≤ 1)
    (hrow : ∀ c, ∑ c', ‖H c c'‖ ^ 2 ≤ 1)
    (hcard : ∀ c, (Finset.univ.filter fun c' => H c c' ≠ 0).card ≤ s) :
    ‖SparseHamiltonian.SparseStateOverlap.matrixOperator (fullMatrix H s)‖ = 1 ∧
      (∀ i, ∑ i', ‖fullMatrix H s i i'‖ ^ 2 ≤ 1) ∧
      (∀ i', ∑ i, ‖fullMatrix H s i i'‖ ^ 2 ≤ 1) ∧
      ∑ i', ‖fullMatrix H s refOne i'‖ ^ 2 = 1 ∧
      (∀ i, (Finset.univ.filter fun i' => fullMatrix H s i i' ≠ 0).card ≤ s) ∧
      (∀ i', (Finset.univ.filter fun i => fullMatrix H s i i' ≠ 0).card ≤ s) ∧
      (∃ i, (Finset.univ.filter fun i' => fullMatrix H s i i' ≠ 0).card = s) ∧
      ∃ i', (Finset.univ.filter fun i => fullMatrix H s i i' ≠ 0).card = s := by
  have hcol : ∀ c', ∑ c, ‖H c c'‖ ^ 2 ≤ 1 := fun c' => by
    rw [show (∑ c, ‖H c c'‖ ^ 2) = ∑ c, ‖H c' c‖ ^ 2 from
      Finset.sum_congr rfl fun c _ => by rw [hsym]]
    exact hrow c'
  have hcardc : ∀ c', (Finset.univ.filter fun c => H c c' ≠ 0).card ≤ s := fun c' => by
    have : (Finset.univ.filter fun c => H c c' ≠ 0) = Finset.univ.filter fun c => H c' c ≠ 0 :=
      Finset.filter_congr fun c _ => by rw [hsym]
    rw [this]
    exact hcard c'
  refine ⟨?_, sum_sq_fullMatrix_le hrow s, sum_sq_fullMatrix_col_le hcol s,
    sum_sq_fullMatrix_refOne H s, card_row_fullMatrix_le hs hcard, card_col_fullMatrix_le hs hcardc,
    ⟨Sum.inr (Sum.inr ⟨0, hs⟩), card_row_fullMatrix_pad H s _⟩,
    ⟨Sum.inr (Sum.inr ⟨0, hs⟩), card_col_fullMatrix_pad H s _⟩⟩
  rw [norm_matrixOperator]
  exact norm_fullMatrix hnorm s

/-- **Norm exactly one, row/column norms exactly one, sparsity exactly `s`**
for the search family (Theorem `hsl:thm:main`), for `0 ≤ a ≤ 1` and
`2·2^μ ≤ s`. -/
theorem searchHam_props {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (τ : ℝ) (hs : 2 * 2 ^ μ ≤ s)
    (j : Fin n → Fin (2 ^ μ)) :
    ‖SparseHamiltonian.SparseStateOverlap.matrixOperator (searchHam n μ s a τ j)‖ = 1 ∧
      (∀ i, ∑ i', ‖searchHam n μ s a τ j i i'‖ ^ 2 ≤ 1) ∧
      (∀ i', ∑ i, ‖searchHam n μ s a τ j i i'‖ ^ 2 ≤ 1) ∧
      ∑ i', ‖searchHam n μ s a τ j refOne i'‖ ^ 2 = 1 ∧
      (∀ i, (Finset.univ.filter fun i' => searchHam n μ s a τ j i i' ≠ 0).card ≤ s) ∧
      (∀ i', (Finset.univ.filter fun i => searchHam n μ s a τ j i i' ≠ 0).card ≤ s) ∧
      (∃ i, (Finset.univ.filter fun i' => searchHam n μ s a τ j i i' ≠ 0).card = s) ∧
      ∃ i', (Finset.univ.filter fun i => searchHam n μ s a τ j i i' ≠ 0).card = s := by
  have hm0 : 0 < 2 ^ μ := by positivity
  have hs1 : 1 ≤ s := by have := Nat.one_le_two_pow (n := μ); omega
  have hc0 : ∀ k, 0 ≤ chainWeight n a τ k := fun k => (chainWeight_le ha0 τ k).1
  have hc : ∀ k, k < n → chainWeight n a τ k ≤ spinWeight n k := fun k _ =>
    (chainWeight_le ha0 τ k).2.trans (mul_le_of_le_one_left (spinWeight_nonneg n k) ha1)
  refine fullMatrix_props hs1 (fun p q => ?_) ?_ (HsInstance.sum_sq_searchChain_le hc0 hc j)
    (fun p => (HsInstance.card_row_searchChain_le _ j p).trans hs)
  · have := congrFun (congrFun (searchChain_transpose n (2 ^ μ) (chainWeight n a τ) j) q) p
    rwa [Matrix.transpose_apply] at this
  · rw [norm_searchChain hm0]
    exact norm_pathMatrix_chainWeight_le ha0 ha1 τ

/-- The same properties for the precision family, for `2 ≤ s`. -/
theorem scalarHam_props (τ : ℝ) (hs : 2 ≤ s) (x : Fin n → Bool) :
    ‖SparseHamiltonian.SparseStateOverlap.matrixOperator (scalarHam n s τ x)‖ = 1 ∧
      (∀ i, ∑ i', ‖scalarHam n s τ x i i'‖ ^ 2 ≤ 1) ∧
      (∀ i', ∑ i, ‖scalarHam n s τ x i i'‖ ^ 2 ≤ 1) ∧
      ∑ i', ‖scalarHam n s τ x refOne i'‖ ^ 2 = 1 ∧
      (∀ i, (Finset.univ.filter fun i' => scalarHam n s τ x i i' ≠ 0).card ≤ s) ∧
      (∀ i', (Finset.univ.filter fun i => scalarHam n s τ x i i' ≠ 0).card ≤ s) ∧
      (∃ i, (Finset.univ.filter fun i' => scalarHam n s τ x i i' ≠ 0).card = s) ∧
      ∃ i', (Finset.univ.filter fun i => scalarHam n s τ x i i' ≠ 0).card = s := by
  have hc0 : ∀ k, 0 ≤ chainWeight n 1 τ k := fun k => (chainWeight_le zero_le_one τ k).1
  have hc : ∀ k, k < n → chainWeight n 1 τ k ≤ spinWeight n k := fun k _ =>
    (chainWeight_le zero_le_one τ k).2.trans_eq (one_mul _)
  refine fullMatrix_props (by omega) (fun i i' => ?_) ?_
    (HsInstance.sum_sq_scalarChain_le hc0 hc x)
    (fun i => (HsInstance.card_row_scalarChain_le _ x i).trans hs)
  · have := congrFun (congrFun (scalarChain_transpose n (chainWeight n 1 τ) x) i') i
    rwa [Matrix.transpose_apply] at this
  · rw [norm_scalarChain]
    exact norm_pathMatrix_chainWeight_le zero_le_one le_rfl τ

end

end SparseLowerBounds.Hamiltonian
end
