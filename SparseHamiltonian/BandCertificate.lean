import SparseHamiltonian.BandCost

/-!
# A finite magnitude-band certificate for a sparse Hermitian matrix

This module combines the entrywise matrix decomposition with its explicit scalar
normalization budgets.  The certificate contains actual matrix equalities,
Hermiticity, sparsity, and row/column first-moment bounds.  It does not contain
an oracle implementation, a block-encoding existence claim, or a simulator.
-/

namespace SparseHamiltonian

open scoped BigOperators

variable {n : Type*} [Fintype n]

/-- The finite mathematical data and bounds supplied by the magnitude-band step.
The scalar `queryRatio` fields are tradeoff factors only, not circuit-query claims. -/
structure BandCertificate (H : Matrix n n ℂ) (s : ℕ) (η : ℝ) where
  cutoff : ℕ
  endpointLower : Real.sqrt (s : ℝ) ≤ (2 : ℝ) ^ cutoff
  endpointUpper : (2 : ℝ) ^ cutoff ≤ 2 * Real.sqrt (s : ℝ)
  decomposition : ∀ i k,
    (∑ j ∈ Finset.range cutoff, bandMatrix (BandCost.threshold η j) H i k) +
      tailMatrix (BandCost.threshold η cutoff) H i k = H i k
  bandHermitian : ∀ j, (bandMatrix (BandCost.threshold η j) H).IsHermitian
  tailHermitian : (tailMatrix (BandCost.threshold η cutoff) H).IsHermitian
  bandRowSparse : ∀ j i,
    (nonzeroPositions (bandMatrix (BandCost.threshold η j) H i)).card ≤ s
  bandColumnSparse : ∀ j k,
    (nonzeroPositions (fun i => bandMatrix (BandCost.threshold η j) H i k)).card ≤ s
  tailRowSparse : ∀ i,
    (nonzeroPositions (tailMatrix (BandCost.threshold η cutoff) H i)).card ≤ s
  tailColumnSparse : ∀ k,
    (nonzeroPositions (fun i => tailMatrix (BandCost.threshold η cutoff) H i k)).card ≤ s
  bandRowBound : ∀ j i,
    ∑ k, ‖bandMatrix (BandCost.threshold η j) H i k‖ ≤
      BandCost.normalization (s : ℝ) η j
  bandColumnBound : ∀ j k,
    ∑ i, ‖bandMatrix (BandCost.threshold η j) H i k‖ ≤
      BandCost.normalization (s : ℝ) η j
  tailRowBound : ∀ i,
    ∑ k, ‖tailMatrix (BandCost.threshold η cutoff) H i k‖ ≤
      BandCost.tailNormalization (s : ℝ) η cutoff
  tailColumnBound : ∀ k,
    ∑ i, ‖tailMatrix (BandCost.threshold η cutoff) H i k‖ ≤
      BandCost.tailNormalization (s : ℝ) η cutoff
  tailNormalizationBound :
    BandCost.tailNormalization (s : ℝ) η cutoff ≤ η * Real.sqrt (s : ℝ)
  normalizationBudget :
    (∑ j ∈ Finset.range cutoff, BandCost.normalization (s : ℝ) η j) +
      BandCost.tailNormalization (s : ℝ) η cutoff ≤ 5 * η * Real.sqrt (s : ℝ)
  weightedBudget :
    (∑ j ∈ Finset.range cutoff,
      BandCost.normalization (s : ℝ) η j * BandCost.queryRatio (s : ℝ) η j) +
      BandCost.tailNormalization (s : ℝ) η cutoff ≤
        (Real.sqrt 2 * (cutoff : ℝ) + 1) * η * Real.sqrt (s : ℝ)
  queryRatioBound : ∀ j, BandCost.queryRatio (s : ℝ) η j ≤ Real.sqrt (s : ℝ)

/-- Every sparse Hermitian matrix satisfying the row and column energy promises
has an actual finite magnitude-band certificate.  This is a matrix theorem;
none of its hypotheses assert a simulation or an encoding algorithm. -/
theorem exists_bandCertificate (H : Matrix n n ℂ) (s : ℕ) (η : ℝ)
    (hH : H.IsHermitian) (hs : 1 ≤ s) (hη : 0 < η)
    (hRowSparse : ∀ i, (nonzeroPositions (H i)).card ≤ s)
    (hColumnSparse : ∀ k, (nonzeroPositions (fun i => H i k)).card ≤ s)
    (hRowEnergy : ∀ i, ∑ k, ‖H i k‖ ^ 2 ≤ η ^ 2)
    (hColumnEnergy : ∀ k, ∑ i, ‖H i k‖ ^ 2 ≤ η ^ 2) :
    Nonempty (BandCertificate H s η) := by
  have hsReal : 1 ≤ (s : ℝ) := by exact_mod_cast hs
  obtain ⟨b, hbLower, hbUpper⟩ := BandCost.exists_dyadic_endpoint hsReal
  refine ⟨{
    cutoff := b
    endpointLower := hbLower
    endpointUpper := hbUpper
    decomposition := ?_
    bandHermitian := ?_
    tailHermitian := ?_
    bandRowSparse := ?_
    bandColumnSparse := ?_
    tailRowSparse := ?_
    tailColumnSparse := ?_
    bandRowBound := ?_
    bandColumnBound := ?_
    tailRowBound := ?_
    tailColumnBound := ?_
    tailNormalizationBound := BandCost.tail_le hsReal hη.le b hbLower
    normalizationBudget := BandCost.normalization_sum_le hsReal hη b hbLower hbUpper
    weightedBudget := BandCost.weighted_sum_le hsReal hη b hbLower
    queryRatioBound := BandCost.queryRatio_le hsReal hη
  }⟩
  · intro i k
    exact bandMatrix_decomposition H η hη.le hRowEnergy b i k
  · intro j
    exact bandMatrix_isHermitian H hH (BandCost.threshold η j)
  · exact tailMatrix_isHermitian H hH (BandCost.threshold η b)
  · intro j i
    exact magnitudeBand_sparse (BandCost.threshold η j) (H i) s (hRowSparse i)
  · intro j k
    exact magnitudeBand_sparse (BandCost.threshold η j) (fun i => H i k) s
      (hColumnSparse k)
  · intro i
    exact magnitudeTail_sparse (BandCost.threshold η b) (H i) s (hRowSparse i)
  · intro k
    exact magnitudeTail_sparse (BandCost.threshold η b) (fun i => H i k) s
      (hColumnSparse k)
  · intro j i
    exact bandMatrix_row_sum_le H (BandCost.threshold η j) η s
      (BandCost.threshold_pos hη j) hRowSparse hRowEnergy i
  · intro j k
    exact bandMatrix_column_sum_le H (BandCost.threshold η j) η s
      (BandCost.threshold_pos hη j) hColumnSparse hColumnEnergy k
  · intro i
    simpa only [BandCost.threshold, BandCost.tailNormalization, mul_div_assoc] using
      tailMatrix_row_sum_le H (BandCost.threshold η b) s
        (BandCost.threshold_pos hη b).le hRowSparse i
  · intro k
    simpa only [BandCost.threshold, BandCost.tailNormalization, mul_div_assoc] using
      tailMatrix_column_sum_le H (BandCost.threshold η b) s
        (BandCost.threshold_pos hη b).le hColumnSparse k

end SparseHamiltonian
