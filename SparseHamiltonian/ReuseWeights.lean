import SparseHamiltonian.SmoothedReuse

/-!
# A finite branch list for coherent smoothing

The two signed families become an explicit finite branch index. The sole
zero-length branch has zero weight and is replaced by a one-slot branch, so
every actual uniform reuse preparation is a genuine isometry.
-/

namespace SparseHamiltonian.ReuseWeights

noncomputable section
open scoped BigOperators
open FilterCoefficients

abbrev Index (d : ℕ) := Fin (d + 1) ⊕ Fin (d + 1)

def weight (a : ℕ → ℝ) (d : ℕ) : Index d → ℝ :=
  Sum.elim (fun j => positiveWeight d a j) (fun j => negativeWeight d a j)

def length (d : ℕ) : Index d → ℕ :=
  Sum.elim (fun j => (j : ℕ) + d) (fun j => max 1 (j : ℕ))

theorem length_pos (d : ℕ) (hd : 0 < d) (i : Index d) : 0 < length d i := by
  cases i with
  | inl j => simp only [length, Sum.elim_inl]; omega
  | inr j => simp only [length, Sum.elim_inr]; omega

theorem length_le (d : ℕ) (hd : 0 < d) (i : Index d) : length d i ≤ 2 * d := by
  cases i with
  | inl j => simp only [length, Sum.elim_inl]; have := j.isLt; omega
  | inr j => simp only [length, Sum.elim_inr]; have := j.isLt; omega

/-- Splitting the branch list into the positive and negative families. -/
theorem sum_weights (a : ℕ → ℝ) (d : ℕ) :
    (∑ i : Index d, weight a d i) =
      ∑ j ∈ Finset.range (d + 1), (positiveWeight d a j + negativeWeight d a j) := by
  simp only [weight, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
  rw [Fin.sum_univ_eq_sum_range (fun j => positiveWeight d a j),
    Fin.sum_univ_eq_sum_range (fun j => negativeWeight d a j), Finset.sum_add_distrib]

theorem sum_abs_weights (a : ℕ → ℝ) (d : ℕ) :
    (∑ i : Index d, |weight a d i|) =
      ∑ j ∈ Finset.range (d + 1), (|positiveWeight d a j| + |negativeWeight d a j|) := by
  simp only [weight, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
  rw [Fin.sum_univ_eq_sum_range (fun j => |positiveWeight d a j|),
    Fin.sum_univ_eq_sum_range (fun j => |negativeWeight d a j|), Finset.sum_add_distrib]

/-- The actual averaging-polynomial branch list has absolute mass two. -/
theorem concrete_absolute_mass (L k : ℕ) (hL : 1 ≤ L) (hd : 0 < k * (L - 1)) :
    (∑ i : Index (k * (L - 1)), |weight (AveragingPolynomial.filter L k).coeff
      (k * (L - 1)) i|) = 2 := by
  rw [sum_abs_weights]
  exact AveragingPolynomial.smoothing_absolute_mass_two L k hL hd

theorem concrete_signed_mass (L k : ℕ) (hL : 1 ≤ L) (hd : 0 < k * (L - 1)) :
    (∑ i : Index (k * (L - 1)), weight (AveragingPolynomial.filter L k).coeff
      (k * (L - 1)) i) = 1 := by
  rw [sum_weights]
  exact AveragingPolynomial.smoothing_signed_mass_one L k hL hd

section Operators

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

omit [CompleteSpace P] in
/-- Replacing the zero-weight branch by a legal one-slot circuit does not
alter the coherent signed public sum. -/
theorem weighted_sum_eq (a : ℕ → ℝ) (d : ℕ) (R : ℕ → P →L[ℂ] P) :
    (∑ i : Index d, weight a d i • R (length d i)) = SmoothedReuse.weightedReuse a d R := by
  have hneg (j : Fin (d + 1)) :
      negativeWeight d a j • R (max 1 (j : ℕ)) = negativeWeight d a j • R j := by
    by_cases hj : (j : ℕ) = 0
    · simp [hj, negativeWeight]
    · rw [max_eq_right (Nat.one_le_iff_ne_zero.mpr hj)]
  simp only [weight, length, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, hneg]
  rw [Fin.sum_univ_eq_sum_range (fun j => positiveWeight d a j • R (j + d)),
    Fin.sum_univ_eq_sum_range (fun j => negativeWeight d a j • R j)]
  exact (Finset.sum_add_distrib).symm

end Operators

end
end SparseHamiltonian.ReuseWeights
