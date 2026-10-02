import SparseHamiltonian.OperatorResolvent

/-!
# Exact signed-LCU smoothing identities

The uncombined signed representation below has normalization exactly two for
nonnegative palindromic probability coefficients. Keeping the positive and
negative endpoint terms separate avoids an unnecessary case split: the
manuscript combines them and obtains the slightly sharper `2 - 2*a 0`.

The unnormalized geometric identities hold over arbitrary rings. The final
normalized identity is evaluated directly in an algebra with possibly
noncommutative multiplication, so it applies to the private operator.
-/

namespace SparseHamiltonian.FilterCoefficients

open scoped BigOperators

section RingIdentities

variable {R : Type*} [Ring R]

/-- An unnormalized finite geometric polynomial. -/
def geometricSum (n : ℕ) (z : R) : R := ∑ j ∈ Finset.range n, z ^ j

@[simp] theorem geometricSum_zero (z : R) : geometricSum 0 z = 0 := by
  simp [geometricSum]

theorem geometricSum_succ (n : ℕ) (z : R) :
    geometricSum (n + 1) z = geometricSum n z + z ^ n := by
  simp only [geometricSum, Finset.sum_range_succ]

theorem geometricSum_add (j d : ℕ) (z : R) :
    geometricSum (j + d) z = geometricSum j z + z ^ j * geometricSum d z := by
  simp only [geometricSum, Finset.sum_range_add, pow_add, Finset.mul_sum]

/-- Summation by parts: finite coefficient differences reconstruct a polynomial. -/
theorem difference_geometric_identity (b : ℕ → R) (N : ℕ) (z : R) :
    (∑ n ∈ Finset.range N, (b n - b (n + 1)) * geometricSum (n + 1) z) =
      (∑ n ∈ Finset.range N, b n * z ^ n) - b N * geometricSum N z := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ, geometricSum_succ]
      noncomm_ring

/-- When the terminal coefficient vanishes the boundary term is absent. -/
theorem difference_geometric_identity_terminal_zero (b : ℕ → R) (N : ℕ)
    (hterminal : b N = 0) (z : R) :
    (∑ n ∈ Finset.range N, (b n - b (n + 1)) * geometricSum (n + 1) z) =
      ∑ n ∈ Finset.range N, b n * z ^ n := by
  rw [difference_geometric_identity, hterminal]
  simp

/-- Multiplying by a geometric polynomial is a sum of shifted windows. -/
theorem smoothing_geometric_identity (a : ℕ → R) (d : ℕ) (z : R) :
    (∑ j ∈ Finset.range (d + 1), a j * z ^ j) * geometricSum d z =
      ∑ j ∈ Finset.range (d + 1),
        a j * (geometricSum (j + d) z - geometricSum j z) := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [geometricSum_add]
  noncomm_ring

end RingIdentities

section FieldIdentities

variable {K : Type*} [Field K] [CharZero K]

/-- The normalized finite geometric polynomial, with value zero for `n=0`. -/
def geometricAverage (n : ℕ) (z : K) : K := geometricSum n z / (n : K)

theorem length_mul_geometricAverage (n : ℕ) (z : K) :
    (n : K) * geometricAverage n z = geometricSum n z := by
  by_cases hn : n = 0
  · simp [hn]
  · have hn' : (n : K) ≠ 0 := Nat.cast_ne_zero.mpr hn
    unfold geometricAverage
    field_simp

/-- The signed coefficient used for the shorter reuse circuit. -/
def negativeWeight (d : ℕ) (a : ℕ → K) (j : ℕ) : K :=
  -((j : K) / (d : K)) * a j

/-- The positive coefficient used for the longer reuse circuit. -/
def positiveWeight (d : ℕ) (a : ℕ → K) (j : ℕ) : K :=
  (((j + d : ℕ) : K) / (d : K)) * a j

omit [CharZero K] in
@[simp] theorem negativeWeight_zero (d : ℕ) (a : ℕ → K) :
    negativeWeight d a 0 = 0 := by
  simp [negativeWeight]

/-- All nontrivial reuse circuits fit within the common length `2*d`. -/
theorem reuse_lengths_le (j d : ℕ) (hj : j ≤ d) :
    j ≤ 2 * d ∧ j + d ≤ 2 * d := by
  constructor <;> omega

theorem shifted_average_identity (j d : ℕ) (z : K) :
    (((j + d : ℕ) : K) / (d : K)) * geometricAverage (j + d) z -
      ((j : K) / (d : K)) * geometricAverage j z =
      z ^ j * geometricAverage d z := by
  calc
    _ = (((j + d : ℕ) : K) * geometricAverage (j + d) z -
          (j : K) * geometricAverage j z) / (d : K) := by ring
    _ = (geometricSum (j + d) z - geometricSum j z) / (d : K) := by
      rw [length_mul_geometricAverage, length_mul_geometricAverage]
    _ = z ^ j * geometricAverage d z := by
      rw [geometricSum_add]
      unfold geometricAverage
      ring

/-- Exact LCU smoothing, retaining separate signed terms of lengths `j` and
`j+d`. The length-zero term has zero weight. -/
theorem smoothing_average_identity (a : ℕ → K) (d : ℕ) (z : K) :
    (∑ j ∈ Finset.range (d + 1), a j * z ^ j) * geometricAverage d z =
      ∑ j ∈ Finset.range (d + 1),
        (positiveWeight d a j * geometricAverage (j + d) z +
          negativeWeight d a j * geometricAverage j z) := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  have h := shifted_average_identity j d z
  unfold positiveWeight negativeWeight
  calc
    a j * z ^ j * geometricAverage d z =
        a j * (z ^ j * geometricAverage d z) := by ring
    _ = a j * ((((j + d : ℕ) : K) / (d : K)) * geometricAverage (j + d) z -
        ((j : K) / (d : K)) * geometricAverage j z) := by rw [h]
    _ = _ := by ring

/-- Coefficient differences give the usual normalized-geometric reconstruction. -/
theorem weighted_difference_average_identity (b : ℕ → K) (N : ℕ)
    (hterminal : b N = 0) (z : K) :
    (∑ n ∈ Finset.range N,
      ((n + 1 : ℕ) : K) * (b n - b (n + 1)) * geometricAverage (n + 1) z) =
      ∑ n ∈ Finset.range N, b n * z ^ n := by
  calc
    _ = ∑ n ∈ Finset.range N, (b n - b (n + 1)) * geometricSum (n + 1) z := by
      apply Finset.sum_congr rfl
      intro n _
      rw [← length_mul_geometricAverage (n + 1) z]
      ring
    _ = _ := difference_geometric_identity_terminal_zero b N hterminal z

omit [CharZero K] in
/-- Signed mass of the coefficient-difference representation. -/
theorem weighted_difference_mass (b : ℕ → K) (N : ℕ) :
    (∑ n ∈ Finset.range N, ((n + 1 : ℕ) : K) * (b n - b (n + 1))) =
      (∑ n ∈ Finset.range N, b n) - (N : K) * b N := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
      simp only [Nat.cast_add, Nat.cast_one]
      ring

omit [CharZero K] in
theorem weighted_difference_mass_terminal_zero (b : ℕ → K) (N : ℕ)
    (hterminal : b N = 0) :
    (∑ n ∈ Finset.range N, ((n + 1 : ℕ) : K) * (b n - b (n + 1))) =
      ∑ n ∈ Finset.range N, b n := by
  rw [weighted_difference_mass, hterminal]
  simp

end FieldIdentities

section OperatorIdentities

variable {K A : Type*} [Field K] [CharZero K] [Ring A] [Algebra K A]

/-- Finite geometric averaging in an algebra whose multiplication need not
commute. In particular, `A` may be an operator algebra. -/
def operatorGeometricAverage (n : ℕ) (z : A) : A :=
  ((n : K)⁻¹) • geometricSum n z

theorem length_smul_operatorGeometricAverage (n : ℕ) (z : A) :
    (n : K) • operatorGeometricAverage (K := K) n z = geometricSum n z := by
  by_cases hn : n = 0
  · simp [hn]
  · have hn' : (n : K) ≠ 0 := Nat.cast_ne_zero.mpr hn
    unfold operatorGeometricAverage
    rw [smul_smul, mul_inv_cancel₀ hn', one_smul]

theorem shifted_operator_average_identity (j d : ℕ) (z : A) :
    (((j + d : ℕ) : K) / (d : K)) •
        operatorGeometricAverage (K := K) (j + d) z -
      ((j : K) / (d : K)) • operatorGeometricAverage (K := K) j z =
      z ^ j * operatorGeometricAverage (K := K) d z := by
  simp only [div_eq_inv_mul, mul_smul, length_smul_operatorGeometricAverage]
  rw [← smul_sub, geometricSum_add, add_sub_cancel_left]
  rw [operatorGeometricAverage, mul_smul_comm]

/-- The signed smoothing identity evaluated directly on a possibly
noncommutative operator. No commutativity of distinct operators is assumed. -/
theorem smoothing_average_operator_identity (a : ℕ → K) (d : ℕ) (z : A) :
    (∑ j ∈ Finset.range (d + 1), a j • z ^ j) *
        operatorGeometricAverage (K := K) d z =
      ∑ j ∈ Finset.range (d + 1),
        (positiveWeight d a j • operatorGeometricAverage (K := K) (j + d) z +
          negativeWeight d a j • operatorGeometricAverage (K := K) j z) := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [smul_mul_assoc, ← shifted_operator_average_identity]
  rw [smul_sub, smul_smul, smul_smul, sub_eq_add_neg, ← neg_smul]
  congr 1
  · congr 1
    unfold positiveWeight
    ring
  · congr 1
    unfold negativeWeight
    ring

end OperatorIdentities

section Normalization

/-- Reflection symmetry fixes the first moment of a normalized coefficient list. -/
theorem palindromic_first_moment (a : ℕ → ℝ) (d : ℕ)
    (hpal : ∀ j ≤ d, a (d - j) = a j)
    (hmass : ∑ j ∈ Finset.range (d + 1), a j = 1) :
    ∑ j ∈ Finset.range (d + 1), (j : ℝ) * a j = (d : ℝ) / 2 := by
  have hreflect :
      (∑ j ∈ Finset.range (d + 1), (j : ℝ) * a j) =
        ∑ j ∈ Finset.range (d + 1), ((d - j : ℕ) : ℝ) * a j := by
    calc
      _ = ∑ j ∈ Finset.range (d + 1),
          ((d - j : ℕ) : ℝ) * a (d - j) := by
        simpa using (Finset.sum_range_reflect (fun j => (j : ℝ) * a j) (d + 1)).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hpal j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))]
  have hpair :
      (∑ j ∈ Finset.range (d + 1), (j : ℝ) * a j) +
        (∑ j ∈ Finset.range (d + 1), ((d - j : ℕ) : ℝ) * a j) = (d : ℝ) := by
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ j ∈ Finset.range (d + 1), (d : ℝ) * a j := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [Nat.cast_sub (Nat.le_of_lt_succ (Finset.mem_range.mp hj))]
        ring
      _ = (d : ℝ) := by rw [← Finset.mul_sum, hmass, mul_one]
  linarith

theorem positiveWeight_nonneg (a : ℕ → ℝ) (d j : ℕ) (ha : 0 ≤ a j) :
    0 ≤ positiveWeight d a j := by
  unfold positiveWeight
  positivity

theorem negativeWeight_nonpos (a : ℕ → ℝ) (d j : ℕ) (ha : 0 ≤ a j) :
    negativeWeight d a j ≤ 0 := by
  unfold negativeWeight
  have h : 0 ≤ ((j : ℝ) / (d : ℝ)) * a j := by positivity
  linarith

theorem weight_pair_mass (a : ℕ → ℝ) (d j : ℕ) (hd : 0 < d) :
    positiveWeight d a j + negativeWeight d a j = a j := by
  have hd' : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd)
  unfold positiveWeight negativeWeight
  simp only [Nat.cast_add]
  field_simp
  ring

/-- Exact signed mass one: hence the desired public action is preserved. -/
theorem smoothing_signed_mass (a : ℕ → ℝ) (d : ℕ) (hd : 0 < d)
    (hmass : ∑ j ∈ Finset.range (d + 1), a j = 1) :
    ∑ j ∈ Finset.range (d + 1),
      (positiveWeight d a j + negativeWeight d a j) = 1 := by
  simpa only [weight_pair_mass a d _ hd] using hmass

theorem weight_pair_abs (a : ℕ → ℝ) (d j : ℕ) (hd : 0 < d)
    (ha : 0 ≤ a j) :
    |positiveWeight d a j| + |negativeWeight d a j| =
      a j + (2 / (d : ℝ)) * ((j : ℝ) * a j) := by
  rw [abs_of_nonneg (positiveWeight_nonneg a d j ha),
    abs_of_nonpos (negativeWeight_nonpos a d j ha)]
  have hd' : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd)
  unfold positiveWeight negativeWeight
  simp only [Nat.cast_add]
  field_simp
  ring

/-- Nonnegative palindromic coefficients admit exact smoothing with total
absolute LCU weight two, independent of the filter degree. -/
theorem smoothing_absolute_mass_two (a : ℕ → ℝ) (d : ℕ) (hd : 0 < d)
    (hnonneg : ∀ j ≤ d, 0 ≤ a j)
    (hpal : ∀ j ≤ d, a (d - j) = a j)
    (hmass : ∑ j ∈ Finset.range (d + 1), a j = 1) :
    ∑ j ∈ Finset.range (d + 1),
      (|positiveWeight d a j| + |negativeWeight d a j|) = 2 := by
  calc
    _ = ∑ j ∈ Finset.range (d + 1),
        (a j + (2 / (d : ℝ)) * ((j : ℝ) * a j)) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact weight_pair_abs a d j hd
        (hnonneg j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))
    _ = 1 + (2 / (d : ℝ)) * ((d : ℝ) / 2) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, hmass,
        palindromic_first_moment a d hpal hmass]
    _ = 2 := by
      have hd' : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd)
      field_simp
      ring

end Normalization

end SparseHamiltonian.FilterCoefficients
