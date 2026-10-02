import SparseHamiltonian.LookupAmplitudePreparation

/-!
# Exact amplitudes for row/column sparse encodings

A real row amplitude and a phase-carrying column amplitude have product
`z / α`. Their squared norms are both `‖z‖ / α`; a row or column one-norm
bound therefore supplies exactly the normalization needed for state overlaps.
These are amplitude identities, not an oracle construction.
-/

namespace SparseHamiltonian.SparseEntryAmplitudes

noncomputable section
open scoped BigOperators ComplexConjugate

/-- A unit complex phase, with the zero entry assigned the harmless phase one. -/
def phase (z : ℂ) : ℂ := if z = 0 then 1 else z / (‖z‖ : ℂ)

@[simp] theorem norm_phase (z : ℂ) : ‖phase z‖ = 1 := by
  by_cases hz : z = 0
  · simp [phase, hz]
  · simp [phase, hz, Complex.norm_real,
      norm_ne_zero_iff.mpr hz]

theorem phase_mul_norm (z : ℂ) : phase z * (‖z‖ : ℂ) = z := by
  by_cases hz : z = 0
  · simp [phase, hz]
  · have hn : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hz
    simp [phase, hz, hn]

/-- Good amplitude for the row preparation. -/
def rowAmplitude (α : ℝ) (z : ℂ) : ℂ := (Real.sqrt (‖z‖ / α) : ℂ)

/-- Good amplitude for the column preparation, carrying the matrix-entry phase. -/
def columnAmplitude (α : ℝ) (z : ℂ) : ℂ := phase z * rowAmplitude α z

@[simp] theorem norm_rowAmplitude_sq (α : ℝ) (hα : 0 < α) (z : ℂ) :
    ‖rowAmplitude α z‖ ^ 2 = ‖z‖ / α := by
  simp only [rowAmplitude, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  exact Real.sq_sqrt (div_nonneg (norm_nonneg z) hα.le)

@[simp] theorem norm_columnAmplitude_sq (α : ℝ) (hα : 0 < α) (z : ℂ) :
    ‖columnAmplitude α z‖ ^ 2 = ‖z‖ / α := by
  simp [columnAmplitude, norm_rowAmplitude_sq α hα]

/-- Conjugating the row amplitude gives the desired complex matrix entry. -/
theorem overlap (α : ℝ) (hα : 0 < α) (z : ℂ) :
    conj (rowAmplitude α z) * columnAmplitude α z = z / (α : ℂ) := by
  have hs : (Real.sqrt (‖z‖ / α) : ℂ) ^ 2 = (‖z‖ : ℂ) / (α : ℂ) := by
    exact_mod_cast Real.sq_sqrt (div_nonneg (norm_nonneg z) hα.le)
  calc
    conj (rowAmplitude α z) * columnAmplitude α z =
        phase z * (Real.sqrt (‖z‖ / α) : ℂ) ^ 2 := by
      simp only [rowAmplitude, columnAmplitude, Complex.conj_ofReal]
      ring
    _ = phase z * ((‖z‖ : ℂ) / (α : ℂ)) := by rw [hs]
    _ = z / (α : ℂ) := by rw [← mul_div_assoc, phase_mul_norm]

/-- One-norm normalization controls the total row-preparation probability. -/
theorem row_sum_sq_le_one {J : Type*} [Fintype J] (α : ℝ) (hα : 0 < α)
    (v : J → ℂ) (hv : ∑ j, ‖v j‖ ≤ α) :
    ∑ j, ‖rowAmplitude α (v j)‖ ^ 2 ≤ 1 := by
  simp_rw [norm_rowAmplitude_sq α hα]
  rw [← Finset.sum_div]
  exact (div_le_one hα).2 hv

/-- The complex phases do not alter the column-preparation probability. -/
theorem column_sum_sq_le_one {J : Type*} [Fintype J] (α : ℝ) (hα : 0 < α)
    (v : J → ℂ) (hv : ∑ j, ‖v j‖ ≤ α) :
    ∑ j, ‖columnAmplitude α (v j)‖ ^ 2 ≤ 1 := by
  simp_rw [norm_columnAmplitude_sq α hα]
  rw [← Finset.sum_div]
  exact (div_le_one hα).2 hv

end
end SparseHamiltonian.SparseEntryAmplitudes
