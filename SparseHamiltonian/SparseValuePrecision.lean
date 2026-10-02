import SparseHamiltonian.AmplitudePolynomialSequence

/-!
# Entry precision for actual sparse Hamiltonian operators

Common sparse locators and pointwise entry errors give an operator error of
`s * δ`, including zero error and zero sparsity. A zero-preserving decoder
cannot create support, and a conjugation-preserving decoder preserves
Hermiticity. The resulting evolution bound concerns the actual matrix
operators. A finite decoder is an abstract finite value alphabet; no rounding
algorithm, bit complexity, or state-preparation query cost is asserted.
-/

namespace SparseHamiltonian.SparseValuePrecision

noncomputable section
open ContinuousLinearMap SparseStateOverlap
open scoped BigOperators InnerProduct

variable {I J : Type*} [Fintype I] [Fintype J]

/-- Matrix subtraction agrees with subtraction of the actual Euclidean operators. -/
theorem matrixOperator_sub (H G : Matrix I J ℂ) :
    matrixOperator (H - G) = matrixOperator H - matrixOperator G := by
  ext v i
  simp [matrixOperator_apply, sub_mul, Finset.sum_sub_distrib]

/-- The Schur bound also covers a zero common row/column bound. -/
theorem norm_matrixOperator_le_nonneg (H : Matrix I J ℂ) (α : ℝ) (hα : 0 ≤ α)
    (hRow : ∀ i, ∑ j, ‖H i j‖ ≤ α) (hCol : ∀ j, ∑ i, ‖H i j‖ ≤ α) :
    ‖matrixOperator H‖ ≤ α := by
  apply le_of_forall_pos_le_add
  intro ε hε
  exact SparseMatrixNorm.norm_matrixOperator_le H (α + ε) (by positivity)
    (fun i => (hRow i).trans (by linarith))
    (fun j => (hCol j).trans (by linarith))

omit [Fintype I] in
/-- A vector supported on at most `s` allowed positions has absolute sum at
most `s * δ` when every entry is at most `δ`. -/
theorem sum_norm_le_of_allowed (f : J → ℂ) (allowed : Finset J) (s : ℕ) (δ : ℝ)
    (hδ : 0 ≤ δ) (hCard : allowed.card ≤ s)
    (hOutside : ∀ j, j ∉ allowed → f j = 0) (hEntry : ∀ j, ‖f j‖ ≤ δ) :
    ∑ j, ‖f j‖ ≤ (s : ℝ) * δ := by
  classical
  have hSum : ∑ j, ‖f j‖ = ∑ j ∈ allowed, ‖f j‖ := by
    symm
    exact Finset.sum_subset (Finset.subset_univ _) (by
      intro j _ hj
      simp [hOutside j hj])
  rw [hSum]
  exact (sum_le_card_mul allowed (fun j => ‖f j‖) δ (fun j _ => hEntry j)).trans
    (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hCard) hδ)

omit [Fintype I] in
/-- The same first-moment bound can be stated directly using nonzero support. -/
theorem sum_norm_le_of_sparse (f : J → ℂ) (s : ℕ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hSparse : (nonzeroPositions f).card ≤ s) (hEntry : ∀ j, ‖f j‖ ≤ δ) :
    ∑ j, ‖f j‖ ≤ (s : ℝ) * δ := by
  classical
  apply sum_norm_le_of_allowed f (nonzeroPositions f) s δ hδ hSparse
  · intro j hj
    simpa only [nonzeroPositions, Finset.mem_filter, Finset.mem_univ,
      true_and, not_not] using hj
  · exact hEntry

/-- Pointwise error on a sparse difference bounds the actual operator error.
The nonnegative error allowance explicitly includes `δ = 0`. -/
theorem operator_error_le_of_sparse_difference (H G : Matrix I J ℂ) (s : ℕ) (δ : ℝ)
    (hδ : 0 ≤ δ)
    (hRow : ∀ i, (nonzeroPositions (fun j => H i j - G i j)).card ≤ s)
    (hCol : ∀ j, (nonzeroPositions (fun i => H i j - G i j)).card ≤ s)
    (hEntry : ∀ i j, ‖H i j - G i j‖ ≤ δ) :
    ‖matrixOperator H - matrixOperator G‖ ≤ (s : ℝ) * δ := by
  rw [← matrixOperator_sub]
  apply norm_matrixOperator_le_nonneg _ _ (by positivity)
  · intro i
    exact sum_norm_le_of_sparse _ s δ hδ (hRow i) (hEntry i)
  · intro j
    exact sum_norm_le_of_sparse _ s δ hδ (hCol j) (fun i => hEntry i j)

/-- Two matrices sharing row and column locators inherit the sharp `s * δ`
operator bound. The common locator, rather than two unrelated sparsity
promises, controls the support of their difference. -/
theorem operator_error_le_of_common_locators (H G : Matrix I J ℂ)
    (rows : I → Finset J) (cols : J → Finset I) (s : ℕ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hRowCard : ∀ i, (rows i).card ≤ s) (hColCard : ∀ j, (cols j).card ≤ s)
    (hRowH : ∀ i j, j ∉ rows i → H i j = 0)
    (hRowG : ∀ i j, j ∉ rows i → G i j = 0)
    (hColH : ∀ i j, i ∉ cols j → H i j = 0)
    (hColG : ∀ i j, i ∉ cols j → G i j = 0)
    (hEntry : ∀ i j, ‖H i j - G i j‖ ≤ δ) :
    ‖matrixOperator H - matrixOperator G‖ ≤ (s : ℝ) * δ := by
  rw [← matrixOperator_sub]
  apply norm_matrixOperator_le_nonneg _ _ (by positivity)
  · intro i
    apply sum_norm_le_of_allowed _ (rows i) s δ hδ (hRowCard i)
    · intro j hj
      simp [hRowH i j hj, hRowG i j hj]
    · exact hEntry i
  · intro j
    apply sum_norm_le_of_allowed _ (cols j) s δ hδ (hColCard j)
    · intro i hi
      simp [hColH i j hi, hColG i j hi]
    · exact fun i => hEntry i j

/-- Entrywise decoding through a finite value alphabet. The hypotheses are on
the encode/decode composite, so they describe actual decoded complex entries. -/
structure FiniteValueDecoder (Code : Type*) [Fintype Code] where
  encode : ℂ → Code
  decode : Code → ℂ
  zero_exact : decode (encode 0) = 0
  star_exact : ∀ z, decode (encode (star z)) = star (decode (encode z))

namespace FiniteValueDecoder
variable {Code : Type*} [Fintype Code]

/-- The complex value actually returned by a finite decoder. -/
def value (D : FiniteValueDecoder Code) (z : ℂ) : ℂ := D.decode (D.encode z)

@[simp] theorem value_zero (D : FiniteValueDecoder Code) : D.value 0 = 0 :=
  D.zero_exact

@[simp] theorem value_star (D : FiniteValueDecoder Code) (z : ℂ) :
    D.value (star z) = star (D.value z) := D.star_exact z

/-- The matrix containing the decoded values of the original entries. -/
def matrix (D : FiniteValueDecoder Code) (H : Matrix I J ℂ) : Matrix I J ℂ :=
  fun i j => D.value (H i j)

omit [Fintype I] in
/-- A finite decoder that preserves zero cannot create nonzero support. -/
theorem support_subset (D : FiniteValueDecoder Code) (f : J → ℂ) :
    nonzeroPositions (fun j => D.value (f j)) ⊆ nonzeroPositions f := by
  classical
  intro j hj
  simp only [nonzeroPositions, Finset.mem_filter, Finset.mem_univ, true_and] at *
  intro hf
  exact hj (by simp [hf])

omit [Fintype I] in
/-- The original and decoded values differ only on the original support. -/
theorem difference_support_subset (D : FiniteValueDecoder Code) (f : J → ℂ) :
    nonzeroPositions (fun j => f j - D.value (f j)) ⊆ nonzeroPositions f := by
  classical
  intro j hj
  simp only [nonzeroPositions, Finset.mem_filter, Finset.mem_univ, true_and] at *
  intro hf
  exact hj (by simp [hf])

omit [Fintype I] in
/-- Decoding preserves every row sparsity bound. -/
theorem row_sparse (D : FiniteValueDecoder Code) (H : Matrix I J ℂ) (s : ℕ)
    (hRow : ∀ i, (nonzeroPositions (H i)).card ≤ s) :
    ∀ i, (nonzeroPositions (D.matrix H i)).card ≤ s := by
  intro i
  exact (Finset.card_le_card (D.support_subset (H i))).trans (hRow i)

omit [Fintype J] in
/-- Decoding also preserves every column sparsity bound. -/
theorem column_sparse (D : FiniteValueDecoder Code) (H : Matrix I J ℂ) (s : ℕ)
    (hCol : ∀ j, (nonzeroPositions (fun i => H i j)).card ≤ s) :
    ∀ j, (nonzeroPositions (fun i => D.matrix H i j)).card ≤ s := by
  intro j
  exact (Finset.card_le_card (D.support_subset (fun i => H i j))).trans (hCol j)

/-- Error from finite entry decoding bounds the actual matrix operator error. -/
theorem operator_error_le (D : FiniteValueDecoder Code) (H : Matrix I J ℂ)
    (s : ℕ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hRow : ∀ i, (nonzeroPositions (H i)).card ≤ s)
    (hCol : ∀ j, (nonzeroPositions (fun i => H i j)).card ≤ s)
    (hEntry : ∀ i j, ‖H i j - D.value (H i j)‖ ≤ δ) :
    ‖matrixOperator H - matrixOperator (D.matrix H)‖ ≤ (s : ℝ) * δ := by
  apply operator_error_le_of_sparse_difference H (D.matrix H) s δ hδ
  · intro i
    exact (Finset.card_le_card (D.difference_support_subset (H i))).trans (hRow i)
  · intro j
    exact (Finset.card_le_card (D.difference_support_subset (fun i => H i j))).trans
      (hCol j)
  · exact hEntry

variable {n : Type*} [Fintype n]

omit [Fintype n] in
/-- Commutation with complex conjugation preserves matrix Hermiticity. -/
theorem isHermitian (D : FiniteValueDecoder Code) (H : Matrix n n ℂ)
    (hH : H.IsHermitian) : (D.matrix H).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  change star (D.value (H j i)) = D.value (H i j)
  rw [← D.value_star, hH.apply i j]

end FiniteValueDecoder

/-- The adjoint of the actual matrix operator is its conjugate transpose. -/
theorem matrixOperator_adjoint (H : Matrix I J ℂ) :
    (matrixOperator H)† = matrixOperator H.conjTranspose := by
  classical
  exact (congrArg (fun A => LinearMap.toContinuousLinearMap A)
    (Matrix.toEuclideanLin_conjTranspose_eq_adjoint H)).symm

variable {n : Type*} [Fintype n]

/-- A Hermitian matrix gives a self-adjoint operator on the Euclidean space. -/
theorem matrixOperator_star_eq (H : Matrix n n ℂ) (hH : H.IsHermitian) :
    star (matrixOperator H) = matrixOperator H := by
  rw [ContinuousLinearMap.star_eq_adjoint, matrixOperator_adjoint, hH.eq]

/-- Sparse entry approximation has time-linear evolution error for the
actual matrix exponentials, without a norm oracle or exponential prefactor. -/
theorem evolution_error_le_of_sparse_difference (H G : Matrix n n ℂ) (s : ℕ)
    (t δ : ℝ) (hδ : 0 ≤ δ) (hH : H.IsHermitian) (hG : G.IsHermitian)
    (hRow : ∀ i, (nonzeroPositions (fun j => H i j - G i j)).card ≤ s)
    (hCol : ∀ j, (nonzeroPositions (fun i => H i j - G i j)).card ≤ s)
    (hEntry : ∀ i j, ‖H i j - G i j‖ ≤ δ) :
    ‖NormedSpace.exp ((-Complex.I * (t : ℂ)) • matrixOperator H) -
      NormedSpace.exp ((-Complex.I * (t : ℂ)) • matrixOperator G)‖ ≤
      |t| * ((s : ℝ) * δ) := by
  exact (HamiltonianStability.evolution_error_le _ _ t
    (matrixOperator_star_eq H hH) (matrixOperator_star_eq G hG)).trans
      (mul_le_mul_of_nonneg_left
        (operator_error_le_of_sparse_difference H G s δ hδ hRow hCol hEntry)
        (abs_nonneg t))

/-- Common sparse locators also give the evolution estimate directly. -/
theorem evolution_error_le_of_common_locators (H G : Matrix n n ℂ)
    (rows cols : n → Finset n) (s : ℕ) (t δ : ℝ) (hδ : 0 ≤ δ)
    (hH : H.IsHermitian) (hG : G.IsHermitian)
    (hRowCard : ∀ i, (rows i).card ≤ s) (hColCard : ∀ j, (cols j).card ≤ s)
    (hRowH : ∀ i j, j ∉ rows i → H i j = 0)
    (hRowG : ∀ i j, j ∉ rows i → G i j = 0)
    (hColH : ∀ i j, i ∉ cols j → H i j = 0)
    (hColG : ∀ i j, i ∉ cols j → G i j = 0)
    (hEntry : ∀ i j, ‖H i j - G i j‖ ≤ δ) :
    ‖NormedSpace.exp ((-Complex.I * (t : ℂ)) • matrixOperator H) -
      NormedSpace.exp ((-Complex.I * (t : ℂ)) • matrixOperator G)‖ ≤
      |t| * ((s : ℝ) * δ) := by
  exact (HamiltonianStability.evolution_error_le _ _ t
    (matrixOperator_star_eq H hH) (matrixOperator_star_eq G hG)).trans
      (mul_le_mul_of_nonneg_left
        (operator_error_le_of_common_locators H G rows cols s δ hδ hRowCard hColCard
          hRowH hRowG hColH hColG hEntry) (abs_nonneg t))

/-- A finite decoder preserving zero and conjugation gives a Hermitian sparse
approximation with sharp evolution error from its certified entry accuracy. -/
theorem FiniteValueDecoder.evolution_error_le {Code : Type*} [Fintype Code]
    (D : FiniteValueDecoder Code) (H : Matrix n n ℂ) (s : ℕ) (t δ : ℝ)
    (hδ : 0 ≤ δ) (hH : H.IsHermitian)
    (hRow : ∀ i, (nonzeroPositions (H i)).card ≤ s)
    (hCol : ∀ j, (nonzeroPositions (fun i => H i j)).card ≤ s)
    (hEntry : ∀ i j, ‖H i j - D.value (H i j)‖ ≤ δ) :
    ‖NormedSpace.exp ((-Complex.I * (t : ℂ)) • matrixOperator H) -
      NormedSpace.exp ((-Complex.I * (t : ℂ)) • matrixOperator (D.matrix H))‖ ≤
      |t| * ((s : ℝ) * δ) := by
  exact (HamiltonianStability.evolution_error_le _ _ t
    (matrixOperator_star_eq H hH) (matrixOperator_star_eq _ (D.isHermitian H hH))).trans
      (mul_le_mul_of_nonneg_left (D.operator_error_le H s δ hδ hRow hCol hEntry)
        (abs_nonneg t))


/-- A simulator for the decoded matrix approximates the original Hamiltonian
in its complete encoded output, with additive finite-value error. -/
theorem FiniteValueDecoder.output_error_le {Code K : Type*} [Fintype Code]
    [NormedAddCommGroup K] [NormedSpace ℂ K]
    (D : FiniteValueDecoder Code) (H : Matrix n n ℂ)
    (S F : EuclideanSpace ℂ n →L[ℂ] K) (s : ℕ) (t ε δ : ℝ)
    (hδ : 0 ≤ δ) (hH : H.IsHermitian) (hF : ‖F‖ ≤ 1)
    (hRow : ∀ i, (nonzeroPositions (H i)).card ≤ s)
    (hCol : ∀ j, (nonzeroPositions (fun i => H i j)).card ≤ s)
    (hEntry : ∀ i j, ‖H i j - D.value (H i j)‖ ≤ δ)
    (hError : ‖S - F ∘L NormedSpace.exp
      ((-Complex.I * (t : ℂ)) • matrixOperator (D.matrix H))‖ ≤ ε) :
    ‖S - F ∘L NormedSpace.exp ((-Complex.I * (t : ℂ)) • matrixOperator H)‖ ≤
      ε + |t| * ((s : ℝ) * δ) := by
  apply HamiltonianStability.output_error_le S F (matrixOperator H)
    (matrixOperator (D.matrix H)) t ε ((s : ℝ) * δ) hF
    (matrixOperator_star_eq H hH) (matrixOperator_star_eq _ (D.isHermitian H hH)) hError
  rw [norm_sub_rev]
  exact D.operator_error_le H s δ hδ hRow hCol hEntry

end
end SparseHamiltonian.SparseValuePrecision
