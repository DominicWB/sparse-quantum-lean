import SparseHamiltonian.PolynomialCompletionOdd

/-!
# Completion of real odd admissible QSP polynomials

This module extracts the squared-variable representation automatically, so the
caller supplies the original real polynomial, its parity, degree and scalar
interval/exterior bounds. Complementary polynomials and phases are conclusions.
-/

namespace SparseHamiltonian.PolynomialCompletionReal

noncomputable section
open Polynomial PolynomialCompletion PolynomialCompletionOdd PolynomialUnitarity

/-- Even coefficients of an odd real polynomial vanish. -/
theorem coeff_even_zero (p : ℝ[X]) (hp : p.comp (-X) = -p)
    (n : ℕ) (hn : Even n) : p.coeff n = 0 := by
  have hh := congrArg (fun q : ℝ[X] => q.coeff n) hp
  have hneg : (-X : ℝ[X]) = C (-1) * X := by simp
  rw [hneg, comp_C_mul_X_coeff, coeff_neg, hn.neg_one_pow] at hh
  linarith

/-- Extract the coefficients of odd powers and halve their exponent. -/
def core (p : ℝ[X]) : ℝ[X] := contract 2 p.divX

@[simp] theorem core_coeff (p : ℝ[X]) (n : ℕ) :
    (core p).coeff n = p.coeff (2 * n + 1) := by
  simp [core, coeff_contract (by decide : (2 : ℕ) ≠ 0), coeff_divX, mul_comm]

/-- Odd parity gives an exact representation `p(X)=X core(p)(X²)`. -/
theorem core_reconstruction (p : ℝ[X]) (hp : p.comp (-X) = -p) :
    p = X * (core p).comp (X ^ 2) := by
  have hdiv : (core p).comp (X ^ 2) = p.divX := by
    rw [← expand_eq_comp_X_pow]
    ext n
    rw [coeff_expand (by decide : 0 < (2 : ℕ))]
    split_ifs with hn
    · rw [core, coeff_contract (by decide : (2 : ℕ) ≠ 0), Nat.div_mul_cancel hn]
    · rw [coeff_divX]
      apply (coeff_even_zero p hp (n + 1) ?_).symm
      exact Nat.even_add_one.mpr (by simpa [even_iff_two_dvd] using hn)
  rw [hdiv]
  have hh := X_mul_divX_add p
  rw [coeff_even_zero p hp 0 (by decide), map_zero, add_zero] at hh
  exact hh.symm

/-- The extracted core has half the original odd degree budget. -/
theorem core_degree (p : ℝ[X]) (m : ℕ) (hd : p.natDegree ≤ 2 * m + 1) :
    (core p).natDegree ≤ m := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  rw [core_coeff]
  apply coeff_eq_zero_of_natDegree_lt
  omega

/-- Complexifying the extracted odd representation recovers the original polynomial. -/
theorem complexify_core (p : ℝ[X]) (hp : p.comp (-X) = -p) :
    complexify p = oddSignal (core p) := by
  conv_lhs => rw [core_reconstruction p hp]
  simp [complexify, oddSignal, Polynomial.map_comp]

/-- A real evaluation of the core representation. -/
theorem eval_core (p : ℝ[X]) (hp : p.comp (-X) = -p) (x : ℝ) :
    p.eval x = x * (core p).eval (x ^ 2) := by
  conv_lhs => rw [core_reconstruction p hp]
  simp

/-- Boundedness on the physical interval becomes the squared-variable inequality. -/
theorem inside_core (p : ℝ[X]) (hp : p.comp (-X) = -p)
    (hin : ∀ x : ℝ, |x| ≤ 1 → |p.eval x| ≤ 1) :
    ∀ y : ℝ, 0 ≤ y → y ≤ 1 → y * ((core p).eval y) ^ 2 ≤ 1 := by
  intro y hy hy1
  have hx : |Real.sqrt y| ≤ 1 := by
    rw [abs_of_nonneg (Real.sqrt_nonneg y)]
    exact Real.sqrt_le_one.mpr hy1
  have h := hin (Real.sqrt y) hx
  rw [eval_core p hp, Real.sq_sqrt hy] at h
  have hs : (Real.sqrt y * (core p).eval y) ^ 2 ≤ 1 := by
    nlinarith [abs_le.mp h]
  rw [mul_pow, Real.sq_sqrt hy] at hs
  exact hs

/-- The exterior inequality becomes the other half of the residual sign condition. -/
theorem outside_core (p : ℝ[X]) (hp : p.comp (-X) = -p)
    (hout : ∀ x : ℝ, 1 ≤ |x| → 1 ≤ |p.eval x|) :
    ∀ y : ℝ, 1 ≤ y → 1 ≤ y * ((core p).eval y) ^ 2 := by
  intro y hy
  have hy0 : 0 ≤ y := le_trans (by norm_num) hy
  have hx : 1 ≤ |Real.sqrt y| := by
    rw [abs_of_nonneg (Real.sqrt_nonneg y)]
    exact Real.one_le_sqrt.mpr hy
  have h := hout (Real.sqrt y) hx
  rw [eval_core p hp, Real.sq_sqrt hy0] at h
  have hs : 1 ≤ (Real.sqrt y * (core p).eval y) ^ 2 := by
    nlinarith [sq_abs (Real.sqrt y * (core p).eval y)]
  rw [mul_pow, Real.sq_sqrt hy0] at hs
  exact hs

/-- Full complementary-polynomial existence for real odd QSP polynomials.
The hypotheses are scalar admissibility conditions, not a completion certificate. -/
theorem completion (p : ℝ[X]) (m : ℕ) (hd : p.natDegree ≤ 2 * m + 1)
    (hp : p.comp (-X) = -p)
    (hin : ∀ x : ℝ, |x| ≤ 1 → |p.eval x| ≤ 1)
    (hout : ∀ x : ℝ, 1 ≤ |x| → 1 ≤ |p.eval x|) :
    ∃ q : ℂ[X], IsNormalized (complexify p) q ∧
      q.comp (-X) = q ∧ q.natDegree ≤ 2 * m := by
  rw [complexify_core p hp]
  exact exists_odd_completion (core p) m (core_degree p m hd)
    (inside_core p hp hin) (outside_core p hp hout)

/-- Exact phase synthesis now follows from a single real polynomial with the
required degree, parity and interval/exterior bounds. -/
theorem phase_list (p : ℝ[X]) (m : ℕ) (hd : p.natDegree ≤ 2 * m + 1)
    (hp : p.comp (-X) = -p)
    (hin : ∀ x : ℝ, |x| ≤ 1 → |p.eval x| ≤ 1)
    (hout : ∀ x : ℝ, 1 ≤ |x| → 1 ≤ |p.eval x|) :
    ∃ v u : AmplitudePolynomialSequence.UnitPhase,
      ∃ ss : List AmplitudePolynomialSequence.Phases,
      ss.length = m ∧ complexify p = C ((v : ℂ) * (u : ℂ)) *
        (AmplitudePolynomialSequence.polynomials ss).1 := by
  rw [complexify_core p hp]
  exact exists_phase_list (core p) m (core_degree p m hd)
    (inside_core p hp hin) (outside_core p hp hout)

end
end SparseHamiltonian.PolynomialCompletionReal
