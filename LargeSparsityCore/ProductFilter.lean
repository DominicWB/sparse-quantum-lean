import SparseHamiltonian.ReuseWeights
import SparseHamiltonian.OperatorPolynomial

set_option autoImplicit false

/-!
# The product filter `g_{B₀}^m g_p^k`

The filter of the large-sparsity core (`opt:eq:filter`) is the product of two repeated geometric
averages, `f(z) = g_{B₀}(z)^m g_p(z)^k` with `g_j(z) = (1 + z + ⋯ + z^{j-1})/j`, of degree
`d = m(B₀ - 1) + k(p - 1)`. Its coefficients are nonnegative, palindromic about `d` and sum to one
(`coeff_nonneg`, `coeff_palindromic`, `coeff_sum`), so the released signed smoothing has
absolute weight exactly two (`absolute_mass_two`, `opt:eq:smoothing`). On operators the
coefficient sum is the product of the two averaged geometric filters (`operator_eq`), and the
complex form of the polynomial evaluates to the scalar filter (`eval_cpoly`, `aeval_cpoly`).
-/

namespace LargeSparsityCore.ProductFilter

noncomputable section

open Polynomial SparseHamiltonian

/-- The product filter `g_B^m g_p^k` as a real polynomial. -/
def poly (B m p k : ℕ) : ℝ[X] := AveragingPolynomial.filter B m * AveragingPolynomial.filter p k

/-- The filter degree `d = m(B - 1) + k(p - 1)`. -/
def degree (B m p k : ℕ) : ℕ := m * (B - 1) + k * (p - 1)

variable (B m p k : ℕ)

theorem natDegree_le : (poly B m p k).natDegree ≤ degree B m p k :=
  natDegree_mul_le.trans (add_le_add (AveragingPolynomial.filter_natDegree_le B m)
    (AveragingPolynomial.filter_natDegree_le p k))

theorem coeff_nonneg (n : ℕ) : 0 ≤ (poly B m p k).coeff n :=
  AveragingPolynomial.mul_coeff_nonneg _ _ (AveragingPolynomial.filter_coeff_nonneg B m)
    (AveragingPolynomial.filter_coeff_nonneg p k) n

theorem eval_one (hB : 1 ≤ B) (hp : 1 ≤ p) : (poly B m p k).eval 1 = 1 := by
  rw [poly, eval_mul, AveragingPolynomial.filter_eval_one B m hB,
    AveragingPolynomial.filter_eval_one p k hp, one_mul]

theorem reflect_eq (hB : 1 ≤ B) (hp : 1 ≤ p) :
    (poly B m p k).reflect (degree B m p k) = poly B m p k := by
  rw [poly, degree, reflect_mul _ _ (AveragingPolynomial.filter_natDegree_le B m)
    (AveragingPolynomial.filter_natDegree_le p k), AveragingPolynomial.filter_reflect B m hB,
    AveragingPolynomial.filter_reflect p k hp]

theorem coeff_palindromic (hB : 1 ≤ B) (hp : 1 ≤ p) (j : ℕ) (hj : j ≤ degree B m p k) :
    (poly B m p k).coeff (degree B m p k - j) = (poly B m p k).coeff j := by
  have h := congrArg (fun q : ℝ[X] => q.coeff j) (reflect_eq B m p k hB hp)
  simpa only [coeff_reflect, revAt_le hj] using h

theorem coeff_sum (hB : 1 ≤ B) (hp : 1 ≤ p) :
    ∑ j ∈ Finset.range (degree B m p k + 1), (poly B m p k).coeff j = 1 := by
  have h := eval_eq_sum_range' (Nat.lt_succ_of_le (natDegree_le B m p k)) (1 : ℝ)
  simpa only [eval_one B m p k hB hp, one_pow, mul_one] using h.symm

/-- The signed smoothing of the product filter has absolute weight exactly two. -/
theorem absolute_mass_two (hB : 1 ≤ B) (hp : 1 ≤ p) (hd : 0 < degree B m p k) :
    (∑ i : ReuseWeights.Index (degree B m p k),
      |ReuseWeights.weight (poly B m p k).coeff (degree B m p k) i|) = 2 := by
  rw [ReuseWeights.sum_abs_weights]
  exact FilterCoefficients.smoothing_absolute_mass_two _ _ hd
    (fun j _ => coeff_nonneg B m p k j) (coeff_palindromic B m p k hB hp)
    (coeff_sum B m p k hB hp)

section Operators

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- The real coefficient sum of the product filter is the product of the two averaged
geometric filters. -/
theorem operator_eq (D : V →L[ℂ] V) :
    (∑ j ∈ Finset.range (degree B m p k + 1), (poly B m p k).coeff j • D ^ j) =
      averagedGeometricFilter D B ^ m * averagedGeometricFilter D p ^ k := by
  have h := aeval_eq_sum_range' (R := ℝ) (Nat.lt_succ_of_le (natDegree_le B m p k)) D
  rw [← h, poly, map_mul, OperatorPolynomial.filter_aeval, OperatorPolynomial.filter_aeval,
    OperatorPolynomial.real_average_eq, OperatorPolynomial.real_average_eq]

/-- The complex form of the product filter. -/
def cpoly : ℂ[X] := (poly B m p k).map (algebraMap ℝ ℂ)

theorem aeval_cpoly (D : V →L[ℂ] V) :
    aeval D (cpoly B m p k) =
      averagedGeometricFilter D B ^ m * averagedGeometricFilter D p ^ k := by
  rw [cpoly, aeval_map_algebraMap, poly, map_mul, OperatorPolynomial.filter_aeval,
    OperatorPolynomial.filter_aeval, OperatorPolynomial.real_average_eq,
    OperatorPolynomial.real_average_eq]

end Operators

theorem eval_cpoly (z : ℂ) :
    (cpoly B m p k).eval z = FilterCoefficients.geometricAverage B z ^ m *
      FilterCoefficients.geometricAverage p z ^ k := by
  rw [cpoly, eval_map, poly, eval₂_mul, AveragingPolynomial.filter_eval₂,
    AveragingPolynomial.filter_eval₂]

end

end LargeSparsityCore.ProductFilter
