import SparseHamiltonian.NativeSparsePhaseSequence

/-!
# Algebraic normalization of amplitude polynomial pairs

Coefficient conjugation turns the pointwise unitary constraint into a polynomial
identity over the entire complex plane. Its highest coefficient supplies the
modulus equality needed for degree-reducing phase synthesis. All normalization
statements here are proved directly from polynomial algebra.
-/

namespace SparseHamiltonian.PolynomialUnitarity

noncomputable section
open Polynomial AmplitudePolynomialSequence
open scoped ComplexConjugate

/-- Conjugate the coefficients, leaving the indeterminate fixed. -/
def conjugate (P : ℂ[X]) : ℂ[X] := P.map (starRingEnd ℂ)

@[simp] theorem conjugate_coeff (P : ℂ[X]) (n : ℕ) :
    (conjugate P).coeff n = conj (P.coeff n) := by simp [conjugate]

@[simp] theorem conjugate_add (P Q : ℂ[X]) :
    conjugate (P + Q) = conjugate P + conjugate Q := by simp [conjugate]

@[simp] theorem conjugate_sub (P Q : ℂ[X]) :
    conjugate (P - Q) = conjugate P - conjugate Q := by simp [conjugate]

@[simp] theorem conjugate_mul (P Q : ℂ[X]) :
    conjugate (P * Q) = conjugate P * conjugate Q := by simp [conjugate]

@[simp] theorem conjugate_C (a : ℂ) : conjugate (C a) = C (conj a) := by
  simp [conjugate]

@[simp] theorem conjugate_X : conjugate (X : ℂ[X]) = X := by simp [conjugate]

@[simp] theorem conjugate_one : conjugate (1 : ℂ[X]) = 1 := by simp [conjugate]

@[simp] theorem conjugate_pow (P : ℂ[X]) (n : ℕ) :
    conjugate (P ^ n) = conjugate P ^ n := by simp [conjugate]

@[simp] theorem conjugate_conjugate (P : ℂ[X]) : conjugate (conjugate P) = P := by
  ext n
  simp

/-- The squared column norm, with the bad-coordinate square root eliminated. -/
def normForm (P Q : ℂ[X]) : ℂ[X] :=
  P * conjugate P + (1 - X ^ 2) * Q * conjugate Q

/-- Algebraic completion constraint on a pair of amplitude polynomials. -/
def IsNormalized (P Q : ℂ[X]) : Prop := normForm P Q = 1

/-- The weighted reflection preserves the normalization form identically. -/
theorem normForm_reflect (P Q : ℂ[X]) :
    normForm (X * P + (1 - X ^ 2) * Q) (P - X * Q) = normForm P Q := by
  simp only [normForm, conjugate_add, conjugate_sub, conjugate_mul,
    conjugate_X, conjugate_one, conjugate_pow]
  ring

/-- A phase on the good polynomial preserves normalization. -/
theorem normForm_phase (a : UnitPhase) (P Q : ℂ[X]) :
    normForm (C (a : ℂ) * P) Q = normForm P Q := by
  have ha : (a : ℂ) * conj (a : ℂ) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, a.property]
    norm_num
  have hCa : C (a : ℂ) * C (conj (a : ℂ)) = (1 : ℂ[X]) := by
    rw [← C_mul, ha, C_1]
  simp only [normForm, conjugate_mul, conjugate_C]
  linear_combination P * conjugate P * hCa

/-- Each two-phase iteration preserves the polynomial normalization identity. -/
theorem normForm_next (a c : UnitPhase) (P Q : ℂ[X]) :
    normForm (nextGood a c P Q) (nextBad a c P Q) = normForm P Q := by
  have hG : nextGood a c P Q =
      X * (C (a : ℂ) * (X * (C (c : ℂ) * P) + (1 - X ^ 2) * Q)) +
        (1 - X ^ 2) * (C (c : ℂ) * P - X * Q) := by
    simp only [nextGood, map_sub, map_one]
    ring
  have hB : nextBad a c P Q =
      C (a : ℂ) * (X * (C (c : ℂ) * P) + (1 - X ^ 2) * Q) -
        X * (C (c : ℂ) * P - X * Q) := by
    simp only [nextBad, map_sub, map_one]
    ring
  rw [hG, hB, normForm_reflect, normForm_phase, normForm_reflect, normForm_phase]

/-- Exact normalization for every forward phase sequence, as a polynomial identity. -/
theorem polynomials_normalized (ss : List Phases) :
    IsNormalized (polynomials ss).1 (polynomials ss).2 := by
  induction ss with
  | nil => simp [IsNormalized, polynomials, normForm]; ring
  | cons s ss ih =>
      change normForm (nextGood s.1 s.2 (polynomials ss).1 (polynomials ss).2)
        (nextBad s.1 s.2 (polynomials ss).1 (polynomials ss).2) = 1
      rw [normForm_next]
      exact ih

/-- Coefficient conjugation does not increase the degree. -/
theorem conjugate_natDegree_le (P : ℂ[X]) : (conjugate P).natDegree ≤ P.natDegree :=
  natDegree_map_le

/-- The highest permitted coefficient cancels between the two norm squares. -/
theorem leading_coeff_mul_conj (P Q : ℂ[X]) (d : ℕ)
    (hP : P.natDegree ≤ d + 1) (hQ : Q.natDegree ≤ d)
    (h : IsNormalized P Q) :
    P.coeff (d + 1) * conj (P.coeff (d + 1)) = Q.coeff d * conj (Q.coeff d) := by
  have hPP : (P * conjugate P).coeff (2 * d + 2) =
      P.coeff (d + 1) * conj (P.coeff (d + 1)) := by
    convert coeff_mul_add_eq_of_natDegree_le hP ((conjugate_natDegree_le P).trans hP) using 1 <;>
      simp [show d + 1 + (d + 1) = 2 * d + 2 by omega]
  have hQQ : (Q * conjugate Q).coeff (2 * d) = Q.coeff d * conj (Q.coeff d) := by
    convert coeff_mul_add_eq_of_natDegree_le hQ ((conjugate_natDegree_le Q).trans hQ) using 1 <;>
      simp [two_mul]
  have hQQzero : (Q * conjugate Q).coeff (2 * d + 2) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    have := @natDegree_mul_le ℂ _ Q (conjugate Q)
    have := conjugate_natDegree_le Q
    omega
  have hform : normForm P Q = P * conjugate P + Q * conjugate Q -
      X ^ 2 * (Q * conjugate Q) := by unfold normForm; ring
  have hh := congrArg (fun f : ℂ[X] => f.coeff (2 * d + 2)) h
  change (normForm P Q).coeff (2 * d + 2) = (1 : ℂ[X]).coeff (2 * d + 2) at hh
  rw [hform, coeff_sub, coeff_add, hPP, hQQzero, coeff_X_pow_mul, hQQ] at hh
  rw [coeff_one, if_neg (by omega)] at hh
  linear_combination hh

/-- A normalized pair has equal moduli in the top permitted coefficients.
This also covers degree-deficient and identically-zero coefficients. -/
theorem leading_coeff_norm (P Q : ℂ[X]) (d : ℕ)
    (hP : P.natDegree ≤ d + 1) (hQ : Q.natDegree ≤ d)
    (h : IsNormalized P Q) : ‖P.coeff (d + 1)‖ = ‖Q.coeff d‖ := by
  have hh := leading_coeff_mul_conj P Q d hP hQ h
  rw [Complex.mul_conj', Complex.mul_conj'] at hh
  have hh' : ‖P.coeff (d + 1)‖ ^ 2 = ‖Q.coeff d‖ ^ 2 := by exact_mod_cast hh
  nlinarith [norm_nonneg (P.coeff (d + 1)), norm_nonneg (Q.coeff d)]

/-- On a real input, coefficient conjugation agrees with value conjugation. -/
theorem conjugate_eval_real (P : ℂ[X]) (x : ℝ) :
    (conjugate P).eval (x : ℂ) = conj (P.eval (x : ℂ)) := by
  simpa only [conjugate, Complex.conj_ofReal] using
    (eval_map_apply (f := starRingEnd ℂ) (p := P) (x : ℂ))

/-- Normalization holds on every real input, not just the physical signal interval. -/
theorem real_identity (P Q : ℂ[X]) (h : IsNormalized P Q) (x : ℝ) :
    ‖P.eval (x : ℂ)‖ ^ 2 + (1 - x ^ 2) * ‖Q.eval (x : ℂ)‖ ^ 2 = 1 := by
  have hh := congrArg (fun f : ℂ[X] => f.eval (x : ℂ)) h
  change (normForm P Q).eval (x : ℂ) = (1 : ℂ[X]).eval (x : ℂ) at hh
  simp only [normForm, eval_add, eval_mul, eval_sub, eval_one, eval_pow, eval_X,
    conjugate_eval_real] at hh
  rw [mul_assoc (1 - (x : ℂ) ^ 2), Complex.mul_conj', Complex.mul_conj'] at hh
  exact_mod_cast hh

/-- Any normalized completion forces modulus at most one on the signal interval. -/
theorem norm_le_one (P Q : ℂ[X]) (h : IsNormalized P Q) (x : ℝ) (hx : |x| ≤ 1) :
    ‖P.eval (x : ℂ)‖ ≤ 1 := by
  have hh := real_identity P Q h x
  have hx2 : x ^ 2 ≤ 1 := by nlinarith [abs_le.mp hx]
  nlinarith [sq_nonneg ‖Q.eval (x : ℂ)‖, norm_nonneg (P.eval (x : ℂ))]

/-- A normalized completion has modulus at least one outside the signal interval. -/
theorem one_le_norm (P Q : ℂ[X]) (h : IsNormalized P Q) (x : ℝ) (hx : 1 ≤ |x|) :
    1 ≤ ‖P.eval (x : ℂ)‖ := by
  have hh := real_identity P Q h x
  have hx2 : 1 ≤ x ^ 2 := by nlinarith [sq_abs x]
  nlinarith [sq_nonneg ‖Q.eval (x : ℂ)‖, norm_nonneg (P.eval (x : ℂ))]

/-- Saturation at the positive endpoint is necessary for polynomial completion. -/
theorem norm_eval_one (P Q : ℂ[X]) (h : IsNormalized P Q) : ‖P.eval 1‖ = 1 := by
  have hh := real_identity P Q h 1
  norm_num at hh
  rcases hh with hh | hh <;> nlinarith [norm_nonneg (P.eval 1)]

/-- Saturation at the negative endpoint is necessary for polynomial completion. -/
theorem norm_eval_neg_one (P Q : ℂ[X]) (h : IsNormalized P Q) : ‖P.eval (-1)‖ = 1 := by
  have hh := real_identity P Q h (-1)
  norm_num at hh
  rcases hh with hh | hh <;> nlinarith [norm_nonneg (P.eval (-1))]

/-- If the good polynomial vanishes at zero, the complementary value there is a phase. -/
theorem norm_eval_zero (P Q : ℂ[X]) (h : IsNormalized P Q) (hP : P.eval 0 = 0) :
    ‖Q.eval 0‖ = 1 := by
  have hh := real_identity P Q h 0
  simp only [Complex.ofReal_zero, hP, norm_zero, zero_pow (by decide : 2 ≠ 0),
    sub_zero, one_mul, zero_add] at hh
  nlinarith [norm_nonneg (Q.eval 0)]

/-- In particular, the good polynomial of a normalized pair cannot vanish identically. -/
theorem good_ne_zero (P Q : ℂ[X]) (h : IsNormalized P Q) : P ≠ 0 := by
  intro hP
  have hh := norm_eval_one P Q h
  simp [hP] at hh

/-- Odd good polynomials also force a nonzero complementary polynomial. -/
theorem bad_ne_zero (P Q : ℂ[X]) (h : IsNormalized P Q) (hP : P.eval 0 = 0) : Q ≠ 0 := by
  intro hQ
  have hh := norm_eval_zero P Q h hP
  simp [hQ] at hh

/-- A normalized constant good polynomial is necessarily a unit phase. -/
theorem constant_norm (z : ℂ) (Q : ℂ[X]) (h : IsNormalized (C z) Q) : ‖z‖ = 1 := by
  simpa using norm_eval_one (C z) Q h

/-- Nontrivial complementary polynomials force the good polynomial to have
exactly one larger degree. This is a consequence of normalization alone. -/
theorem degree_compatibility (P Q : ℂ[X]) (h : IsNormalized P Q) (hQ : Q ≠ 0) :
    P.natDegree = Q.natDegree + 1 := by
  have hQlead : Q.coeff Q.natDegree ≠ 0 := leadingCoeff_ne_zero.mpr hQ
  have hPlead : P.coeff P.natDegree ≠ 0 := leadingCoeff_ne_zero.mpr (good_ne_zero P Q h)
  have h₁ : Q.natDegree + 1 ≤ P.natDegree := by
    by_contra hh
    have hc := leading_coeff_norm P Q Q.natDegree (by omega) le_rfl h
    rw [coeff_eq_zero_of_natDegree_lt (by omega), norm_zero] at hc
    exact hQlead (norm_eq_zero.mp hc.symm)
  have h₂ : P.natDegree ≤ Q.natDegree + 1 := by
    by_contra hh
    have hd : P.natDegree - 1 + 1 = P.natDegree := by omega
    have hc := leading_coeff_norm P Q (P.natDegree - 1) (by omega) (by omega) h
    rw [hd, coeff_eq_zero_of_natDegree_lt (p := Q) (by omega), norm_zero] at hc
    exact hPlead (norm_eq_zero.mp hc)
  omega

end
end SparseHamiltonian.PolynomialUnitarity
