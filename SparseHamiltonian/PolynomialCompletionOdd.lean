import SparseHamiltonian.PolynomialCompletion

/-!
# Parity-compatible complementary polynomials

Spectral factorization is applied in the squared signal variable. This ensures
that the complementary polynomial is even, rather than imposing parity after
an arbitrary factorization in the original variable. The scalar assumptions
are the exact endpoint and inside/outside constraints of real odd QSP.
-/

namespace SparseHamiltonian.PolynomialCompletionOdd

noncomputable section
open Polynomial PolynomialCompletion PolynomialUnitarity

/-- Odd signal polynomial represented in its squared variable. -/
def oddSignal (f : ℝ[X]) : ℂ[X] := X * (complexify f).comp (X ^ 2)

/-- Substitution of the squared signal makes every polynomial even. -/
theorem square_comp_even (q : ℂ[X]) : (q.comp (X ^ 2)).comp (-X) = q.comp (X ^ 2) := by
  rw [comp_assoc]
  simp

/-- The signal representation has exact odd parity. -/
theorem oddSignal_odd (f : ℝ[X]) : (oddSignal f).comp (-X) = -(oddSignal f) := by
  simp only [oddSignal, mul_comp, X_comp, square_comp_even]
  ring

/-- Composition with a real square commutes with coefficient conjugation. -/
theorem conjugate_square_comp (q : ℂ[X]) :
    conjugate (q.comp (X ^ 2)) = (conjugate q).comp (X ^ 2) := by
  simp [conjugate, Polynomial.map_comp]

/-- If a polynomial in the squared variable is nonnegative on the real line,
it has an even complex spectral factor, with the exact degree budget. -/
theorem exists_even_spectral_factor (g : ℝ[X]) (hg : ∀ y : ℝ, 0 ≤ g.eval y) :
    ∃ q : ℂ[X], (complexify g).comp (X ^ 2) = q * conjugate q ∧
      q.comp (-X) = q ∧ q.natDegree = g.natDegree := by
  obtain ⟨r, hr, hd⟩ := exists_spectral_factor_degree g hg
  refine ⟨r.comp (X ^ 2), ?_, square_comp_even r, ?_⟩
  · rw [hr, mul_comp, conjugate_square_comp]
  · rw [natDegree_comp, natDegree_pow, natDegree_X]
    omega

/-- A scalar residual identity supplies a parity-compatible QSP completion.
The complementary polynomial and its degree are constructed conclusions. -/
theorem complete_from_residual (f g : ℝ[X])
    (heq : 1 - X * f ^ 2 = (1 - X) * g)
    (hg : ∀ y : ℝ, 0 ≤ g.eval y) :
    ∃ q : ℂ[X], IsNormalized (oddSignal f) q ∧
      q.comp (-X) = q ∧ q.natDegree = g.natDegree := by
  obtain ⟨q, hq, hpar, hdeg⟩ := exists_even_spectral_factor g hg
  refine ⟨q, ?_, hpar, hdeg⟩
  have hh := congrArg (fun p : ℝ[X] => (complexify p).comp (X ^ 2)) heq
  simp only [complexify, Polynomial.map_sub, Polynomial.map_one, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_X, sub_comp, one_comp, mul_comp, X_comp,
    pow_comp] at hh
  change 1 - X ^ 2 * (complexify f).comp (X ^ 2) ^ 2 =
    (1 - X ^ 2) * (complexify g).comp (X ^ 2) at hh
  rw [hq] at hh
  change normForm (oddSignal f) q = 1
  simp only [normForm, oddSignal, conjugate_mul, conjugate_X, conjugate_square_comp,
    conjugate_complexify]
  linear_combination -hh


/-- The exact endpoint follows from the two sides of the required scalar bounds. -/
theorem endpoint (f : ℝ[X])
    (hin : ∀ y : ℝ, 0 ≤ y → y ≤ 1 → y * (f.eval y) ^ 2 ≤ 1)
    (hout : ∀ y : ℝ, 1 ≤ y → 1 ≤ y * (f.eval y) ^ 2) :
    (f.eval 1) ^ 2 = 1 := by
  have h₁ := hin 1 (by norm_num) le_rfl
  have h₂ := hout 1 le_rfl
  nlinarith

/-- Endpoint saturation makes the residual exactly divisible by `1-X`. -/
theorem exists_residual (f : ℝ[X]) (h : (f.eval 1) ^ 2 = 1) :
    ∃ g : ℝ[X], 1 - X * f ^ 2 = (1 - X) * g := by
  have hroot : (1 - X * f ^ 2).eval 1 = 0 := by simp [h]
  obtain ⟨g, hg⟩ := (dvd_iff_isRoot.mpr hroot : X - C 1 ∣ 1 - X * f ^ 2)
  refine ⟨-g, ?_⟩
  rw [hg]
  simp only [map_one]
  ring

/-- The residual is globally nonnegative, including negative squared-variable
arguments. Negative arguments are handled by the real square `(f y)^2`. -/
theorem residual_nonnegative (f g : ℝ[X])
    (heq : 1 - X * f ^ 2 = (1 - X) * g)
    (hin : ∀ y : ℝ, 0 ≤ y → y ≤ 1 → y * (f.eval y) ^ 2 ≤ 1)
    (hout : ∀ y : ℝ, 1 ≤ y → 1 ≤ y * (f.eval y) ^ 2) :
    ∀ y : ℝ, 0 ≤ g.eval y := by
  apply nonnegative_of_except_one g 1
  intro y hy
  have hh := congrArg (fun p : ℝ[X] => p.eval y) heq
  simp only [eval_sub, eval_one, eval_mul, eval_X, eval_pow] at hh
  rcases lt_or_gt_of_ne hy with hlt | hgt
  · have hnum : 0 ≤ 1 - y * (f.eval y) ^ 2 := by
      by_cases hy0 : 0 ≤ y
      · exact sub_nonneg.mpr (hin y hy0 hlt.le)
      · have hm := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hy0) (sq_nonneg (f.eval y))
        linarith
    rw [hh] at hnum
    exact nonneg_of_mul_nonneg_right hnum (sub_pos.mpr hlt)
  · have hnum : 1 - y * (f.eval y) ^ 2 ≤ 0 := sub_nonpos.mpr (hout y hgt.le)
    rw [hh] at hnum
    nlinarith

/-- Explicit degree bound for the odd signal polynomial. -/
theorem oddSignal_degree (f : ℝ[X]) (m : ℕ) (hf : f.natDegree ≤ m) :
    (oddSignal f).natDegree ≤ 2 * m + 1 := by
  have h := natDegree_mul_le (p := (X : ℂ[X]))
    (q := (complexify f).comp (X ^ 2))
  simp only [natDegree_X, natDegree_comp, natDegree_pow] at h
  have hm : (complexify f).natDegree = f.natDegree := by simp [complexify]
  unfold oddSignal
  omega

/-- A real odd polynomial satisfying the exact interval/exterior inequalities
has an even complementary polynomial. No complementary polynomial or phase
list is assumed; both follow from spectral factorization. -/
theorem exists_odd_completion (f : ℝ[X]) (m : ℕ) (hf : f.natDegree ≤ m)
    (hin : ∀ y : ℝ, 0 ≤ y → y ≤ 1 → y * (f.eval y) ^ 2 ≤ 1)
    (hout : ∀ y : ℝ, 1 ≤ y → 1 ≤ y * (f.eval y) ^ 2) :
    ∃ q : ℂ[X], IsNormalized (oddSignal f) q ∧
      q.comp (-X) = q ∧ q.natDegree ≤ 2 * m := by
  obtain ⟨g, hg⟩ := exists_residual f (endpoint f hin hout)
  obtain ⟨q, hq, hpar, _⟩ := complete_from_residual f g hg
    (residual_nonnegative f g hg hin hout)
  refine ⟨q, hq, hpar, ?_⟩
  by_cases hq0 : q = 0
  · simp [hq0]
  · have hd := degree_compatibility (oddSignal f) q hq hq0
    have hp := oddSignal_degree f m hf
    omega

/-- The real interval/exterior conditions now suffice to construct the exact
native phase-pair list, with its specified number of preparation iterations. -/
theorem exists_phase_list (f : ℝ[X]) (m : ℕ) (hf : f.natDegree ≤ m)
    (hin : ∀ y : ℝ, 0 ≤ y → y ≤ 1 → y * (f.eval y) ^ 2 ≤ 1)
    (hout : ∀ y : ℝ, 1 ≤ y → 1 ≤ y * (f.eval y) ^ 2) :
    ∃ v u : AmplitudePolynomialSequence.UnitPhase,
      ∃ ss : List AmplitudePolynomialSequence.Phases,
      ss.length = m ∧ oddSignal f = C ((v : ℂ) * (u : ℂ)) *
        (AmplitudePolynomialSequence.polynomials ss).1 := by
  obtain ⟨q, hn, hpar, hdeg⟩ := exists_odd_completion f m hf hin hout
  obtain ⟨v, u, ss, hlen, hgood, _⟩ := PhysicalPhaseSynthesis.paired_synthesis m
    (oddSignal f) q (oddSignal_degree f m hf) hdeg (oddSignal_odd f) hpar hn
  exact ⟨v, u, ss, hlen, hgood⟩

end
end SparseHamiltonian.PolynomialCompletionOdd
