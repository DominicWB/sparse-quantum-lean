import SparseHamiltonian.CayleyTransfer

/-!
# Cubic error of a Cayley step

Exact rational cancellation and the exponential-series tail provide a
Banach-algebra proof of the local error. No scalar spectral theorem is used.
-/

namespace SparseHamiltonian.CayleyApproximation

open scoped BigOperators

section Banach
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] [NormOneClass A]

/-- The operator exponential Taylor tail is bounded by the scalar tail at the
operator norm. -/
theorem exp_tail_norm_le (X : A) (n : ℕ) :
    ‖NormedSpace.exp X - ∑ j ∈ Finset.range n, (j.factorial : ℂ)⁻¹ • X ^ j‖ ≤
      Real.exp ‖X‖ - ∑ j ∈ Finset.range n, ‖X‖ ^ j / (j.factorial : ℝ) := by
  have hA := NormedSpace.expSeries_summable' (𝕂 := ℂ) X
  have hAn := NormedSpace.norm_expSeries_summable' (𝕂 := ℂ) X
  have hR := Real.summable_pow_div_factorial ‖X‖
  have hsumA := hA.sum_add_tsum_nat_add n
  have hsumR := hR.sum_add_tsum_nat_add n
  rw [← congrFun (NormedSpace.exp_eq_tsum ℂ) X] at hsumA
  have hexpR : (∑' j : ℕ, ‖X‖ ^ j / (j.factorial : ℝ)) = Real.exp ‖X‖ := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum ℝ]
    simp only [smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [hexpR] at hsumR
  rw [← hsumA, add_sub_cancel_left, ← hsumR, add_sub_cancel_left]
  have hAnTail : Summable (fun j : ℕ => ‖((j + n).factorial : ℂ)⁻¹ • X ^ (j + n)‖) :=
    (summable_nat_add_iff n).mpr hAn
  have hRTail : Summable (fun j : ℕ => ‖X‖ ^ (j + n) / ((j + n).factorial : ℝ)) :=
    (summable_nat_add_iff n).mpr hR
  have hterm (j : ℕ) : ‖((j + n).factorial : ℂ)⁻¹ • X ^ (j + n)‖ ≤
      ‖X‖ ^ (j + n) / ((j + n).factorial : ℝ) := by
    rw [norm_smul, norm_inv, Complex.norm_natCast]
    simpa only [div_eq_mul_inv, mul_comm] using
      mul_le_mul_of_nonneg_left (norm_pow_le X (j + n))
        (inv_nonneg.mpr (Nat.cast_nonneg (j + n).factorial) :
          0 ≤ (((j + n).factorial : ℝ))⁻¹)
  exact (norm_tsum_le_tsum_norm hAnTail).trans
    (Summable.tsum_le_tsum hterm hAnTail hRTail)

/-- On the unit ball, the quadratic Taylor approximation has a cubic error. -/
theorem exp_quadratic_error (X : A) (hX : ‖X‖ ≤ 1) :
    ‖NormedSpace.exp X - (1 + X + (1 / 2 : ℂ) • X ^ 2)‖ ≤ (2 / 9 : ℝ) * ‖X‖ ^ 3 := by
  have h := exp_tail_norm_le X 3
  have hr := Real.exp_bound' (norm_nonneg X) hX (n := 3) (by norm_num)
  norm_num [Finset.sum_range_succ] at h hr
  calc
    _ ≤ Real.exp ‖X‖ - (1 + ‖X‖ + ‖X‖ ^ 2 / 2) := by simpa [one_div] using h
    _ ≤ (2 / 9 : ℝ) * ‖X‖ ^ 3 := by linarith

omit [CompleteSpace A] [NormOneClass A] in
/-- Exact rational remainder after the quadratic Taylor polynomial. -/
theorem cayley_quadratic_remainder (X R : A)
    (hR : (1 - (1 / 2 : ℂ) • X) * R = 1) :
    (1 + (1 / 2 : ℂ) • X) * R - (1 + X + (1 / 2 : ℂ) • X ^ 2) =
      (1 / 4 : ℂ) • (X ^ 3 * R) := by
  have hp : (1 + X + (1 / 2 : ℂ) • X ^ 2) * (1 - (1 / 2 : ℂ) • X) =
      1 + (1 / 2 : ℂ) • X - (1 / 4 : ℂ) • X ^ 3 := by
    simp only [mul_sub, add_mul, one_mul, mul_one,
      smul_mul_assoc, mul_smul_comm, pow_succ, pow_zero, mul_assoc]
    module
  have h := congrArg (· * R) hp
  rw [mul_assoc, hR, mul_one] at h
  simp only [sub_mul, smul_mul_assoc] at h
  rw [h]
  abel

omit [CompleteSpace A] in
/-- Rational cubic remainder with a bounded denominator inverse. -/
theorem cayley_quadratic_error (X R : A)
    (hR : (1 - (1 / 2 : ℂ) • X) * R = 1) (hRn : ‖R‖ ≤ 2) :
    ‖(1 + (1 / 2 : ℂ) • X) * R - (1 + X + (1 / 2 : ℂ) • X ^ 2)‖ ≤
      (1 / 2 : ℝ) * ‖X‖ ^ 3 := by
  rw [cayley_quadratic_remainder X R hR, norm_smul]
  norm_num
  have hm := norm_mul_le (X ^ 3) R
  have hp := norm_pow_le X 3
  have hb : ‖X ^ 3 * R‖ ≤ ‖X‖ ^ 3 * 2 := by
    calc
      _ ≤ ‖X ^ 3‖ * ‖R‖ := hm
      _ ≤ ‖X‖ ^ 3 * 2 := mul_le_mul hp hRn (norm_nonneg _) (by positivity)
  nlinarith

/-- A Cayley step differs from the operator exponential by at most a cubic
power of the generator norm. -/
theorem cayley_exp_error (X R : A) (hX : ‖X‖ ≤ 1)
    (hR : (1 - (1 / 2 : ℂ) • X) * R = 1) (hRn : ‖R‖ ≤ 2) :
    ‖(1 + (1 / 2 : ℂ) • X) * R - NormedSpace.exp X‖ ≤ ‖X‖ ^ 3 := by
  have h := norm_sub_le_norm_sub_add_norm_sub
    ((1 + (1 / 2 : ℂ) • X) * R) (1 + X + (1 / 2 : ℂ) • X ^ 2)
    (NormedSpace.exp X)
  have he := exp_quadratic_error X hX
  rw [norm_sub_rev (1 + X + (1 / 2 : ℂ) • X ^ 2)] at h
  nlinarith [cayley_quadratic_error X R hR hRn, pow_nonneg (norm_nonneg X) 3]

/-- A Neumann series constructs the needed bounded inverse. -/
theorem exists_half_inverse (X : A) (hX : ‖X‖ ≤ 1) :
    ∃ R : A, (1 - (1 / 2 : ℂ) • X) * R = 1 ∧
      R * (1 - (1 / 2 : ℂ) • X) = 1 ∧ ‖R‖ ≤ 2 := by
  let Y := (1 / 2 : ℂ) • X
  have hY : ‖Y‖ ≤ (1 / 2 : ℝ) := by
    dsimp [Y]
    rw [norm_smul]
    norm_num
    linarith
  have hYlt : ‖Y‖ < 1 := by linarith
  refine ⟨∑' n : ℕ, Y ^ n, mul_neg_geom_series Y hYlt,
    geom_series_mul_neg Y hYlt, ?_⟩
  have h := tsum_geometric_le_of_norm_lt_one Y hYlt
  simp only [norm_one, sub_self, zero_add] at h
  apply h.trans
  rw [inv_le_iff_one_le_mul₀ (by linarith : 0 < 1 - ‖Y‖)]
  linarith

end Banach

section Operators
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

omit [CompleteSpace V] in
/-- Powers of contractions accumulate at most linearly in one-step error. -/
theorem contraction_power_difference (U W : V →L[ℂ] V)
    (hU : ‖U‖ ≤ 1) (hW : ‖W‖ ≤ 1) (T : ℕ) :
    ‖U ^ T - W ^ T‖ ≤ (T : ℝ) * ‖U - W‖ := by
  induction T with
  | zero => simp
  | succ T ih =>
    have heq : U ^ (T + 1) - W ^ (T + 1) =
        U ^ T * (U - W) + (U ^ T - W ^ T) * W := by
      rw [pow_succ, pow_succ]
      noncomm_ring
    rw [heq]
    calc
      _ ≤ ‖U ^ T * (U - W)‖ + ‖(U ^ T - W ^ T) * W‖ := norm_add_le _ _
      _ ≤ ‖U ^ T‖ * ‖U - W‖ + ‖U ^ T - W ^ T‖ * ‖W‖ :=
        add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ 1 * ‖U - W‖ + ((T : ℝ) * ‖U - W‖) * 1 := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_right (contraction_pow_norm_le U hU T) (norm_nonneg _)
        · exact mul_le_mul ih hW (norm_nonneg _) (by positivity)
      _ = _ := by push_cast; ring

/-- The exponential of a skew-adjoint operator is a contraction. -/
theorem skew_exp_norm_le (X : V →L[ℂ] V) (hX : star X = -X) :
    ‖NormedSpace.exp X‖ ≤ 1 := by
  letI : NormedAlgebra ℚ (V →L[ℂ] V) := .restrictScalars ℚ ℂ _
  have hu := NormedSpace.exp_mem_unitary_of_mem_skewAdjoint (x := X)
    (skewAdjoint.mem_iff.mpr hX)
  have hs := (Unitary.mem_iff.mp hu).1
  have hn := CStarRing.norm_mul_self_le (NormedSpace.exp X)
  rw [hs] at hn
  have hI : ‖(1 : V →L[ℂ] V)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  nlinarith [norm_nonneg (NormedSpace.exp X)]

/-- A bounded Cayley inverse gives a cubic global discretisation bound. -/
theorem cayley_power_exp_error (X R : V →L[ℂ] V)
    (hX : ‖X‖ ≤ 1) (hSkew : star X = -X)
    (hR : (1 - (1 / 2 : ℂ) • X) * R = 1) (hRn : ‖R‖ ≤ 2) (T : ℕ) :
    ‖((1 + (1 / 2 : ℂ) • X) * R) ^ T - NormedSpace.exp (T • X)‖ ≤
      (T : ℝ) * ‖X‖ ^ 3 := by
  rcases subsingleton_or_nontrivial V with h | h
  · letI := h
    have hz : ((1 + (1 / 2 : ℂ) • X) * R) ^ T - NormedSpace.exp (T • X) = 0 :=
      Subsingleton.elim _ _
    rw [hz, norm_zero]
    positivity
  · letI := h
    letI : NormedAlgebra ℚ (V →L[ℂ] V) := .restrictScalars ℚ ℂ _
    rw [NormedSpace.exp_nsmul]
    exact (contraction_power_difference _ _
      (CayleyTransfer.skew_cayley_norm_le_one X R hSkew hR)
      (skew_exp_norm_le X hSkew) T).trans
      (mul_le_mul_of_nonneg_left (cayley_exp_error X R hX hR hRn) (Nat.cast_nonneg _))

/-- Every skew-adjoint operator in the unit ball has a Cayley approximation
with an actual bounded inverse and a cubic error at every number of steps. -/
theorem exists_cayley_power_approximation (X : V →L[ℂ] V)
    (hX : ‖X‖ ≤ 1) (hSkew : star X = -X) :
    ∃ R : V →L[ℂ] V, (1 - (1 / 2 : ℂ) • X) * R = 1 ∧
      R * (1 - (1 / 2 : ℂ) • X) = 1 ∧ ‖R‖ ≤ 2 ∧
      ∀ T : ℕ,
        ‖((1 + (1 / 2 : ℂ) • X) * R) ^ T - NormedSpace.exp (T • X)‖ ≤
          (T : ℝ) * ‖X‖ ^ 3 := by
  rcases subsingleton_or_nontrivial V with h | h
  · letI := h
    refine ⟨0, Subsingleton.elim _ _, Subsingleton.elim _ _, by simp, ?_⟩
    intro T
    have hz : ((1 + (1 / 2 : ℂ) • X) * 0) ^ T - NormedSpace.exp (T • X) = 0 :=
      Subsingleton.elim _ _
    rw [hz, norm_zero]
    positivity
  · letI := h
    obtain ⟨R, hr, hl, hn⟩ := exists_half_inverse X hX
    exact ⟨R, hr, hl, hn, cayley_power_exp_error X R hX hSkew hr hn⟩

omit [CompleteSpace V] in
/-- The inverse norm bound follows directly from its equation on the unit ball. -/
theorem half_inverse_norm_le (X R : V →L[ℂ] V) (hX : ‖X‖ ≤ 1)
    (hR : (1 - (1 / 2 : ℂ) • X) * R = 1) : ‖R‖ ≤ 2 := by
  have heq : R = 1 + (1 / 2 : ℂ) • (X * R) := by
    have h := hR
    simp only [sub_mul, one_mul, smul_mul_assoc] at h
    rw [← h]
    abel
  have hn := norm_add_le (1 : V →L[ℂ] V) ((1 / 2 : ℂ) • (X * R))
  rw [← heq, norm_smul] at hn
  norm_num at hn
  have hm := norm_mul_le X R
  have hmul : ‖X‖ * ‖R‖ ≤ ‖R‖ := by
    simpa using mul_le_mul_of_nonneg_right hX (norm_nonneg R)
  have hI : ‖(1 : V →L[ℂ] V)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  nlinarith

/-- The global cubic error needs only the actual inverse equation, since its
norm bound is derived from that equation. -/
theorem cayley_power_exp_error_of_inverse (X R : V →L[ℂ] V)
    (hX : ‖X‖ ≤ 1) (hSkew : star X = -X)
    (hR : (1 - (1 / 2 : ℂ) • X) * R = 1) (T : ℕ) :
    ‖((1 + (1 / 2 : ℂ) • X) * R) ^ T - NormedSpace.exp (T • X)‖ ≤
      (T : ℝ) * ‖X‖ ^ 3 :=
  cayley_power_exp_error X R hX hSkew hR (half_inverse_norm_le X R hX hR) T

/-- For a self-adjoint Hamiltonian contraction and `0 ≤ w ≤ 1`, `T` Cayley
steps approximate the actual Schrödinger exponential with error at most `T w³`.
The denominator inverse is the same one supplied by the clock construction. -/
theorem hamiltonian_cayley_error (H R : V →L[ℂ] V) (w : ℝ)
    (hw : 0 ≤ w) (hw1 : w ≤ 1) (hHerm : star H = H) (hH : ‖H‖ ≤ 1)
    (hR : CayleyTransfer.cayleyDenominator w H * R = 1) (T : ℕ) :
    ‖(CayleyTransfer.cayleyNumerator w H * R) ^ T -
      NormedSpace.exp ((-Complex.I * (T : ℂ) * (w : ℂ)) • H)‖ ≤ (T : ℝ) * w ^ 3 := by
  let X : V →L[ℂ] V := (-Complex.I * (w : ℂ)) • H
  have hXw : ‖X‖ ≤ w := by
    simp only [X, norm_smul, norm_mul, norm_neg, Complex.norm_I, one_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw]
    simpa using mul_le_mul_of_nonneg_left hH hw
  have hSkew : star X = -X := by
    simp only [X, star_smul, hHerm, star_mul, star_neg, Complex.star_def,
      Complex.conj_I, Complex.conj_ofReal]
    module
  have hDen : 1 - (1 / 2 : ℂ) • X = CayleyTransfer.cayleyDenominator w H := by
    simp only [X, CayleyTransfer.cayleyDenominator, smul_smul]
    module
  have hNum : 1 + (1 / 2 : ℂ) • X = CayleyTransfer.cayleyNumerator w H := by
    simp only [X, CayleyTransfer.cayleyNumerator, smul_smul]
    module
  have hExp : T • X = (-Complex.I * (T : ℂ) * (w : ℂ)) • H := by
    rw [← Nat.cast_smul_eq_nsmul ℂ]
    simp only [X, smul_smul]
    congr 1
    ring
  have h := cayley_power_exp_error_of_inverse X R (hXw.trans hw1) hSkew
    (hDen ▸ hR) T
  rw [hNum, hExp] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg X) hXw 3) (Nat.cast_nonneg _))

end Operators
end SparseHamiltonian.CayleyApproximation
