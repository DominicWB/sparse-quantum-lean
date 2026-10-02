import SparseHamiltonian.Imports

/-!
# Sparse magnitude bands

This file proves the finite-dimensional estimates behind the magnitude-band
decomposition.  These are mathematical bounds on actual complex matrices,
independent of the oracle implementation.
-/

namespace SparseHamiltonian

open scoped BigOperators

section FiniteSums

variable {ι : Type*}

/-- The elementary cardinality bound on a finite sum. -/
theorem sum_le_card_mul (S : Finset ι) (x : ι → ℝ) (a : ℝ)
    (h : ∀ i ∈ S, x i ≤ a) :
    ∑ i ∈ S, x i ≤ (S.card : ℝ) * a := by
  calc
    ∑ i ∈ S, x i ≤ ∑ _i ∈ S, a := Finset.sum_le_sum h
    _ = (S.card : ℝ) * a := by simp

/-- Entries in the band `(a/2,a]` have their first moment controlled by
their second moment. -/
theorem band_sum_le_energy (S : Finset ι) (x : ι → ℝ)
    (a η : ℝ) (ha : 0 < a)
    (hband : ∀ i ∈ S, a / 2 < x i)
    (henergy : ∑ i ∈ S, (x i) ^ 2 ≤ η ^ 2) :
    ∑ i ∈ S, x i ≤ 2 * η ^ 2 / a := by
  have hpoint : ∀ i ∈ S, a * x i ≤ 2 * (x i) ^ 2 := by
    intro i hi
    have hx := hband i hi
    have hx0 : 0 ≤ x i := by linarith
    have hprod := mul_nonneg hx0 (show 0 ≤ x i - a / 2 by linarith)
    nlinarith
  have hs := Finset.sum_le_sum hpoint
  simp only [← Finset.mul_sum] at hs
  apply (le_div_iff₀ ha).2
  nlinarith

/-- The two estimates used to choose the normalization of a magnitude band. -/
theorem band_sum_le_min (S : Finset ι) (x : ι → ℝ)
    (s : ℕ) (a η : ℝ) (ha : 0 < a)
    (hcard : S.card ≤ s)
    (hband : ∀ i ∈ S, a / 2 < x i ∧ x i ≤ a)
    (henergy : ∑ i ∈ S, (x i) ^ 2 ≤ η ^ 2) :
    ∑ i ∈ S, x i ≤ min ((s : ℝ) * a) (2 * η ^ 2 / a) := by
  apply le_min
  · calc
      ∑ i ∈ S, x i ≤ (S.card : ℝ) * a :=
        sum_le_card_mul S x a (fun i hi => (hband i hi).2)
      _ ≤ (s : ℝ) * a :=
        mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard) ha.le
  · exact band_sum_le_energy S x a η ha
      (fun i hi => (hband i hi).1) henergy

end FiniteSums

section ComplexVectors

variable {ι : Type*} [Fintype ι]

/-- Actual nonzero positions of a vector. -/
noncomputable def nonzeroPositions (f : ι → ℂ) : Finset ι := by
  classical
  exact Finset.univ.filter fun i => f i ≠ 0

/-- Positions belonging to the magnitude band `(a/2,a]`. -/
noncomputable def bandPositions (a : ℝ) (f : ι → ℂ) : Finset ι := by
  classical
  exact Finset.univ.filter fun i => a / 2 < ‖f i‖ ∧ ‖f i‖ ≤ a

/-- Entrywise magnitude mask. -/
noncomputable def magnitudeBand (a : ℝ) (f : ι → ℂ) (i : ι) : ℂ := by
  classical
  exact if a / 2 < ‖f i‖ ∧ ‖f i‖ ≤ a then f i else 0

/-- The low-magnitude tail, including zero entries. -/
noncomputable def magnitudeTail (a : ℝ) (f : ι → ℂ) (i : ι) : ℂ := by
  classical
  exact if ‖f i‖ ≤ a then f i else 0

theorem nonzeroPositions_magnitudeBand_subset (a : ℝ) (f : ι → ℂ) :
    nonzeroPositions (magnitudeBand a f) ⊆ nonzeroPositions f := by
  classical
  intro i hi
  simp only [nonzeroPositions, Finset.mem_filter, Finset.mem_univ, true_and] at *
  intro hf
  simp [magnitudeBand, hf] at hi

theorem nonzeroPositions_magnitudeTail_subset (a : ℝ) (f : ι → ℂ) :
    nonzeroPositions (magnitudeTail a f) ⊆ nonzeroPositions f := by
  classical
  intro i hi
  simp only [nonzeroPositions, Finset.mem_filter, Finset.mem_univ, true_and] at *
  intro hf
  simp [magnitudeTail, hf] at hi

theorem magnitudeBand_sparse (a : ℝ) (f : ι → ℂ) (s : ℕ)
    (hsparse : (nonzeroPositions f).card ≤ s) :
    (nonzeroPositions (magnitudeBand a f)).card ≤ s :=
  (Finset.card_le_card (nonzeroPositions_magnitudeBand_subset a f)).trans hsparse

theorem magnitudeTail_sparse (a : ℝ) (f : ι → ℂ) (s : ℕ)
    (hsparse : (nonzeroPositions f).card ≤ s) :
    (nonzeroPositions (magnitudeTail a f)).card ≤ s :=
  (Finset.card_le_card (nonzeroPositions_magnitudeTail_subset a f)).trans hsparse

theorem bandPositions_subset_nonzeroPositions (a : ℝ) (f : ι → ℂ)
    (ha : 0 < a) : bandPositions a f ⊆ nonzeroPositions f := by
  classical
  intro i hi
  simp only [bandPositions, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  simp only [nonzeroPositions, Finset.mem_filter, Finset.mem_univ, true_and]
  intro hz
  simp only [hz, norm_zero] at hi
  linarith [hi.1]

theorem sum_norm_magnitudeBand (a : ℝ) (f : ι → ℂ) :
    ∑ i, ‖magnitudeBand a f i‖ = ∑ i ∈ bandPositions a f, ‖f i‖ := by
  classical
  simp only [magnitudeBand, bandPositions, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

/-- A sparse complex vector's band obeys both the sparsity and energy bounds. -/
theorem sum_norm_magnitudeBand_le (a η : ℝ) (s : ℕ) (f : ι → ℂ)
    (ha : 0 < a)
    (hsparse : (nonzeroPositions f).card ≤ s)
    (henergy : ∑ i, ‖f i‖ ^ 2 ≤ η ^ 2) :
    ∑ i, ‖magnitudeBand a f i‖ ≤
      min ((s : ℝ) * a) (2 * η ^ 2 / a) := by
  classical
  rw [sum_norm_magnitudeBand]
  apply band_sum_le_min (bandPositions a f) (fun i => ‖f i‖) s a η ha
  · exact (Finset.card_le_card
      (bandPositions_subset_nonzeroPositions a f ha)).trans hsparse
  · intro i hi
    simpa only [bandPositions, Finset.mem_filter, Finset.mem_univ, true_and] using hi
  · calc
      ∑ i ∈ bandPositions a f, ‖f i‖ ^ 2 ≤ ∑ i, ‖f i‖ ^ 2 :=
        Finset.sum_le_univ_sum_of_nonneg (fun i => sq_nonneg ‖f i‖)
      _ ≤ η ^ 2 := henergy

/-- A sparse vector's low-magnitude tail has first moment at most `s*a`. -/
theorem sum_norm_magnitudeTail_le (a : ℝ) (s : ℕ) (f : ι → ℂ)
    (ha : 0 ≤ a) (hsparse : (nonzeroPositions f).card ≤ s) :
    ∑ i, ‖magnitudeTail a f i‖ ≤ (s : ℝ) * a := by
  classical
  have heq : ∑ i, ‖magnitudeTail a f i‖ =
      ∑ i ∈ nonzeroPositions f, ‖magnitudeTail a f i‖ := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    have hf : f i = 0 := by
      simpa only [nonzeroPositions, Finset.mem_filter, Finset.mem_univ,
        true_and, not_not] using hi
    simp [magnitudeTail, hf]
  rw [heq]
  calc
    ∑ i ∈ nonzeroPositions f, ‖magnitudeTail a f i‖ ≤
        ((nonzeroPositions f).card : ℝ) * a := by
      apply sum_le_card_mul
      intro i _
      unfold magnitudeTail
      split_ifs with h
      · exact h
      · simpa using ha
    _ ≤ (s : ℝ) * a :=
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hsparse) ha

omit [Fintype ι] in
/-- A band and the next smaller tail exactly partition the current tail. -/
theorem magnitudeBand_add_tail (a : ℝ) (f : ι → ℂ) (i : ι) (ha : 0 ≤ a) :
    magnitudeBand a f i + magnitudeTail (a / 2) f i = magnitudeTail a f i := by
  classical
  by_cases hlo : ‖f i‖ ≤ a / 2
  · have hhi : ‖f i‖ ≤ a := by linarith
    simp [magnitudeBand, magnitudeTail, hlo, hhi, not_lt.mpr hlo]
  · have hstrict : a / 2 < ‖f i‖ := lt_of_not_ge hlo
    by_cases hhi : ‖f i‖ ≤ a
    · simp [magnitudeBand, magnitudeTail, hlo, hhi, hstrict]
    · simp [magnitudeBand, magnitudeTail, hlo, hhi]

/-- The common dyadic threshold used in the sparse decomposition. -/
noncomputable def dyadicScale (η : ℝ) (j : ℕ) : ℝ := η / (2 : ℝ) ^ j

@[simp] theorem dyadicScale_zero (η : ℝ) : dyadicScale η 0 = η := by
  simp [dyadicScale]

theorem dyadicScale_succ (η : ℝ) (j : ℕ) :
    dyadicScale η (j + 1) = dyadicScale η j / 2 := by
  simp [dyadicScale, pow_succ, div_div]

theorem dyadicScale_nonneg (η : ℝ) (j : ℕ) (hη : 0 ≤ η) :
    0 ≤ dyadicScale η j := by
  exact div_nonneg hη (by positivity)

omit [Fintype ι] in
/-- Exact finite telescoping, with no discarded small-entry error. -/
theorem sum_magnitudeBands_add_tail (η : ℝ) (f : ι → ℂ) (i : ι)
    (hη : 0 ≤ η) (J : ℕ) :
    (∑ j ∈ Finset.range J, magnitudeBand (dyadicScale η j) f i) +
      magnitudeTail (dyadicScale η J) f i = magnitudeTail η f i := by
  induction J with
  | zero => simp
  | succ J ih =>
      rw [Finset.sum_range_succ, add_assoc, dyadicScale_succ,
        magnitudeBand_add_tail _ f i (dyadicScale_nonneg η J hη)]
      exact ih

omit [Fintype ι] in
theorem magnitudeTail_eq_self (a : ℝ) (f : ι → ℂ) (i : ι)
    (h : ‖f i‖ ≤ a) : magnitudeTail a f i = f i := by
  simp [magnitudeTail, h]

theorem norm_le_of_energy_le (η : ℝ) (f : ι → ℂ) (hη : 0 ≤ η)
    (henergy : ∑ j, ‖f j‖ ^ 2 ≤ η ^ 2) (i : ι) : ‖f i‖ ≤ η := by
  have hi : ‖f i‖ ^ 2 ≤ ∑ j, ‖f j‖ ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg ‖f j‖) (Finset.mem_univ i)
  nlinarith [norm_nonneg (f i)]

/-- The energy promise ensures the initial tail contains the whole vector. -/
theorem sum_magnitudeBands_add_tail_eq_self (η : ℝ) (f : ι → ℂ)
    (hη : 0 ≤ η) (henergy : ∑ j, ‖f j‖ ^ 2 ≤ η ^ 2) (J : ℕ) (i : ι) :
    (∑ j ∈ Finset.range J, magnitudeBand (dyadicScale η j) f i) +
      magnitudeTail (dyadicScale η J) f i = f i := by
  rw [sum_magnitudeBands_add_tail η f i hη J]
  exact magnitudeTail_eq_self η f i (norm_le_of_energy_le η f hη henergy i)

end ComplexVectors

section Matrices

variable {n : Type*} [Fintype n]

/-- The actual matrix obtained by applying a magnitude band entrywise. -/
noncomputable def bandMatrix (a : ℝ) (H : Matrix n n ℂ) : Matrix n n ℂ :=
  fun i => magnitudeBand a (H i)

/-- The actual matrix obtained by retaining only entries of magnitude at most `a`. -/
noncomputable def tailMatrix (a : ℝ) (H : Matrix n n ℂ) : Matrix n n ℂ :=
  fun i => magnitudeTail a (H i)

omit [Fintype n] in
/-- Magnitude filtering preserves Hermiticity; no spectral-norm promise on the
filtered matrix is assumed. -/
theorem bandMatrix_isHermitian (H : Matrix n n ℂ) (hH : H.IsHermitian) (a : ℝ) :
    (bandMatrix a H).IsHermitian := by
  classical
  apply Matrix.IsHermitian.ext
  intro i j
  have hn : ‖H j i‖ = ‖H i j‖ := by
    rw [← hH.apply i j]
    exact (Complex.norm_conj _).symm
  simp only [bandMatrix, magnitudeBand, hn]
  split_ifs
  · exact hH.apply i j
  · simp

omit [Fintype n] in
theorem tailMatrix_isHermitian (H : Matrix n n ℂ) (hH : H.IsHermitian) (a : ℝ) :
    (tailMatrix a H).IsHermitian := by
  classical
  apply Matrix.IsHermitian.ext
  intro i j
  have hn : ‖H j i‖ = ‖H i j‖ := by
    rw [← hH.apply i j]
    exact (Complex.norm_conj _).symm
  simp only [tailMatrix, magnitudeTail, hn]
  split_ifs
  · exact hH.apply i j
  · simp

theorem bandMatrix_row_sum_le (H : Matrix n n ℂ) (a η : ℝ) (s : ℕ)
    (ha : 0 < a)
    (hsparse : ∀ i, (nonzeroPositions (H i)).card ≤ s)
    (henergy : ∀ i, ∑ j, ‖H i j‖ ^ 2 ≤ η ^ 2) (i : n) :
    ∑ j, ‖bandMatrix a H i j‖ ≤
      min ((s : ℝ) * a) (2 * η ^ 2 / a) :=
  sum_norm_magnitudeBand_le a η s (H i) ha (hsparse i) (henergy i)

theorem bandMatrix_column_sum_le (H : Matrix n n ℂ) (a η : ℝ) (s : ℕ)
    (ha : 0 < a)
    (hsparse : ∀ j, (nonzeroPositions (fun i => H i j)).card ≤ s)
    (henergy : ∀ j, ∑ i, ‖H i j‖ ^ 2 ≤ η ^ 2) (j : n) :
    ∑ i, ‖bandMatrix a H i j‖ ≤
      min ((s : ℝ) * a) (2 * η ^ 2 / a) :=
  sum_norm_magnitudeBand_le a η s (fun i => H i j) ha (hsparse j) (henergy j)

theorem tailMatrix_row_sum_le (H : Matrix n n ℂ) (a : ℝ) (s : ℕ)
    (ha : 0 ≤ a) (hsparse : ∀ i, (nonzeroPositions (H i)).card ≤ s) (i : n) :
    ∑ j, ‖tailMatrix a H i j‖ ≤ (s : ℝ) * a :=
  sum_norm_magnitudeTail_le a s (H i) ha (hsparse i)

theorem tailMatrix_column_sum_le (H : Matrix n n ℂ) (a : ℝ) (s : ℕ)
    (ha : 0 ≤ a)
    (hsparse : ∀ j, (nonzeroPositions (fun i => H i j)).card ≤ s) (j : n) :
    ∑ i, ‖tailMatrix a H i j‖ ≤ (s : ℝ) * a :=
  sum_norm_magnitudeTail_le a s (fun i => H i j) ha (hsparse j)

/-- The exact entrywise matrix decomposition, retaining a final sparse tail. -/
theorem bandMatrix_decomposition (H : Matrix n n ℂ) (η : ℝ)
    (hη : 0 ≤ η) (henergy : ∀ i, ∑ j, ‖H i j‖ ^ 2 ≤ η ^ 2)
    (J : ℕ) (i k : n) :
    (∑ j ∈ Finset.range J, bandMatrix (dyadicScale η j) H i k) +
      tailMatrix (dyadicScale η J) H i k = H i k :=
  sum_magnitudeBands_add_tail_eq_self η (H i) hη (henergy i) J k

end Matrices

end SparseHamiltonian
