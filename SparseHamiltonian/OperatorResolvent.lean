import SparseHamiltonian.Amplification

/-!
# Cyclic-clock resolvents in an operator-compatible norm

All estimates are stated in normed algebras, so they apply in particular to the
operator norm on bounded operators on a complex Hilbert space. They do not use
the default entrywise norm on a matrix space.

The finite resolvent is an exact two-sided inverse when `D^(2q) = -1`. Its norm
is at most `q` when `D` is a contraction. A separate Banach-algebra perturbation
lemma gives a genuine nearby inverse with controlled norm.
-/

namespace SparseHamiltonian
namespace OperatorResolvent

open scoped BigOperators

noncomputable section

section FiniteClock

variable {𝓐 : Type*} [NormedRing 𝓐]

/-- The explicitly finite cyclic-clock resolvent. -/
def finiteResolvent [NormedAlgebra ℂ 𝓐] (D : 𝓐) (q : ℕ) : 𝓐 :=
  (2 : ℂ)⁻¹ • ∑ j ∈ Finset.range (2 * q), D ^ j

theorem finiteResolvent_right_inverse [NormedAlgebra ℂ 𝓐] (D : 𝓐) (q : ℕ)
    (hCycle : D ^ (2 * q) = -1) :
    (1 - D) * finiteResolvent D q = 1 := by
  rw [finiteResolvent, mul_smul_comm, mul_neg_geom_sum, hCycle,
    sub_neg_eq_add, ← two_smul ℂ (1 : 𝓐), inv_smul_smul₀ two_ne_zero]

theorem finiteResolvent_left_inverse [NormedAlgebra ℂ 𝓐] (D : 𝓐) (q : ℕ)
    (hCycle : D ^ (2 * q) = -1) :
    finiteResolvent D q * (1 - D) = 1 := by
  rw [finiteResolvent, smul_mul_assoc, geom_sum_mul_neg, hCycle,
    sub_neg_eq_add, ← two_smul ℂ (1 : 𝓐), inv_smul_smul₀ two_ne_zero]

/-- Every power of a contraction is again a contraction, including exponent zero. -/
theorem contraction_pow_norm [NormOneClass 𝓐] (D : 𝓐) (hD : ‖D‖ ≤ 1) (j : ℕ) :
    ‖D ^ j‖ ≤ 1 :=
  (norm_pow_le D j).trans (pow_le_one₀ (norm_nonneg D) hD)

/-- The finite resolvent costs at most the clock length in operator norm. -/
theorem norm_finiteResolvent_le [NormedAlgebra ℂ 𝓐] [NormOneClass 𝓐]
    (D : 𝓐) (q : ℕ) (hD : ‖D‖ ≤ 1) :
    ‖finiteResolvent D q‖ ≤ q := by
  have hSum : ‖∑ j ∈ Finset.range (2 * q), D ^ j‖ ≤ (2 * q : ℕ) := by
    calc
      ‖∑ j ∈ Finset.range (2 * q), D ^ j‖ ≤
          ∑ j ∈ Finset.range (2 * q), ‖D ^ j‖ := norm_sum_le _ _
      _ ≤ ∑ _j ∈ Finset.range (2 * q), (1 : ℝ) :=
        Finset.sum_le_sum fun j _ ↦ contraction_pow_norm D hD j
      _ = (2 * q : ℕ) := by simp
  rw [finiteResolvent, norm_smul, norm_inv]
  norm_num only [Complex.norm_ofNat]
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hSum
  linarith

end FiniteClock

section Perturbation

variable {𝓐 : Type*} [NormedRing 𝓐] [NormOneClass 𝓐] [CompleteSpace 𝓐]

/-- A geometric-series inverse whose perturbation has norm at most one quarter. -/
theorem exists_inverse_one_sub_of_norm_le_quarter (T : 𝓐)
    (hT : ‖T‖ ≤ (1 : ℝ) / 4) :
    ∃ G : 𝓐, (1 - T) * G = 1 ∧ G * (1 - T) = 1 ∧ ‖G‖ ≤ 4 / 3 := by
  have hLt : ‖T‖ < 1 := by linarith
  refine ⟨∑' n : ℕ, T ^ n, mul_neg_geom_series T hLt,
    geom_series_mul_neg T hLt, ?_⟩
  have hG := tsum_geometric_le_of_norm_lt_one T hLt
  simp only [norm_one, sub_self, zero_add] at hG
  have hInv : (1 - ‖T‖)⁻¹ ≤ (4 : ℝ) / 3 := by
    rw [inv_le_iff_one_le_mul₀ (by linarith : 0 < 1 - ‖T‖)]
    linarith
  exact hG.trans hInv

/-- Explicit Neumann perturbation bound, valid in a noncommutative Banach algebra.
The result supplies both inverse identities, rather than merely asserting that
the spectrum avoids a neighborhood.
-/
theorem exists_inverse_add_of_norm_le
    (X R E : 𝓐) (Q : ℝ) (hQ : 0 < Q)
    (hRight : X * R = 1) (hLeft : R * X = 1)
    (hR : ‖R‖ ≤ Q) (hE : ‖E‖ ≤ 1 / (4 * Q)) :
    ∃ S : 𝓐, (X + E) * S = 1 ∧ S * (X + E) = 1 ∧ ‖S‖ ≤ 4 * Q / 3 := by
  have hRQ : Q * (1 / (4 * Q)) = (1 : ℝ) / 4 := by
    field_simp [ne_of_gt hQ]
  have hT : ‖-(R * E)‖ ≤ (1 : ℝ) / 4 := by
    rw [norm_neg]
    calc
      ‖R * E‖ ≤ ‖R‖ * ‖E‖ := norm_mul_le _ _
      _ ≤ Q * (1 / (4 * Q)) :=
        mul_le_mul hR hE (norm_nonneg _) (le_of_lt hQ)
      _ = (1 : ℝ) / 4 := hRQ
  obtain ⟨G, hGR, hGL, hG⟩ := exists_inverse_one_sub_of_norm_le_quarter (-(R * E)) hT
  simp only [sub_neg_eq_add] at hGR hGL
  have hFactor : X + E = X * (1 + R * E) := by
    rw [mul_add, mul_one, ← mul_assoc, hRight, one_mul]
  have hOther : R * (X + E) = 1 + R * E := by
    rw [mul_add, hLeft]
  refine ⟨G * R, ?_, ?_, ?_⟩
  · rw [hFactor]
    calc
      X * (1 + R * E) * (G * R) = X * ((1 + R * E) * G) * R := by
        simp only [mul_assoc]
      _ = 1 := by rw [hGR, mul_one, hRight]
  · calc
      G * R * (X + E) = G * (R * (X + E)) := mul_assoc _ _ _
      _ = 1 := by rw [hOther, hGL]
  · calc
      ‖G * R‖ ≤ ‖G‖ * ‖R‖ := norm_mul_le _ _
      _ ≤ (4 / 3 : ℝ) * Q := mul_le_mul hG hR (norm_nonneg _) (by norm_num)
      _ = 4 * Q / 3 := by ring

end Perturbation

section ComplexDisk

variable {𝓐 : Type*} [NormedRing 𝓐] [NormedAlgebra ℂ 𝓐]
  [NormOneClass 𝓐] [CompleteSpace 𝓐]

/-- A disk of radius `1/(4Q)` around one has resolvent norm at most `4Q/3`,
provided the resolvent at one has norm at most `Q`. -/
theorem exists_resolvent_in_disk
    (D R : 𝓐) (Q : ℝ) (hQ : 0 < Q)
    (hRight : (1 - D) * R = 1) (hLeft : R * (1 - D) = 1)
    (hR : ‖R‖ ≤ Q) (z : ℂ) (hz : ‖z - 1‖ ≤ 1 / (4 * Q)) :
    ∃ S : 𝓐, (z • (1 : 𝓐) - D) * S = 1 ∧
      S * (z • (1 : 𝓐) - D) = 1 ∧ ‖S‖ ≤ 4 * Q / 3 := by
  have hE : ‖(z - 1) • (1 : 𝓐)‖ ≤ 1 / (4 * Q) := by
    simpa only [norm_smul, norm_one, mul_one] using hz
  have hEq : (1 - D) + (z - 1) • (1 : 𝓐) = z • (1 : 𝓐) - D := by
    rw [sub_smul, one_smul]
    abel
  simpa only [hEq] using
    exists_inverse_add_of_norm_le (1 - D) R ((z - 1) • (1 : 𝓐)) Q hQ
      hRight hLeft hR hE

/-- The preceding disk bound specialized to an explicitly finite cyclic clock. -/
theorem cyclic_resolvent_in_disk
    (D : 𝓐) (q : ℕ) (Q : ℝ) (hQ : 0 < Q) (hq : (q : ℝ) ≤ Q)
    (hCycle : D ^ (2 * q) = -1) (hD : ‖D‖ ≤ 1)
    (z : ℂ) (hz : ‖z - 1‖ ≤ 1 / (4 * Q)) :
    ∃ S : 𝓐, (z • (1 : 𝓐) - D) * S = 1 ∧
      S * (z • (1 : 𝓐) - D) = 1 ∧ ‖S‖ ≤ 4 * Q / 3 :=
  exists_resolvent_in_disk D (finiteResolvent D q) Q hQ
    (finiteResolvent_right_inverse D q hCycle)
    (finiteResolvent_left_inverse D q hCycle)
    ((norm_finiteResolvent_le D q hD).trans hq) z hz

end ComplexDisk

/-- Concrete specialization to the genuine operator norm on bounded operators.
In particular this applies to every nonzero finite-dimensional complex Hilbert
space; no matrix-norm convention enters the statement. -/
theorem boundedOperator_cyclic_resolvent_in_disk
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] [Nontrivial E]
    (D : E →L[ℂ] E) (q : ℕ) (Q : ℝ) (hQ : 0 < Q) (hq : (q : ℝ) ≤ Q)
    (hCycle : D ^ (2 * q) = -1) (hD : ‖D‖ ≤ 1)
    (z : ℂ) (hz : ‖z - 1‖ ≤ 1 / (4 * Q)) :
    ∃ S : E →L[ℂ] E, (z • (1 : E →L[ℂ] E) - D) * S = 1 ∧
      S * (z • (1 : E →L[ℂ] E) - D) = 1 ∧ ‖S‖ ≤ 4 * Q / 3 :=
  cyclic_resolvent_in_disk D q Q hQ hq hCycle hD z hz

end

end OperatorResolvent
end SparseHamiltonian
