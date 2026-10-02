import SparseHamiltonian.ScheduledFractionalAmplifier

/-!
# Spectral factors of nonnegative real polynomials

A nonnegative real polynomial has a complex polynomial spectral factor. The
construction removes one conjugate pair of complex roots at a time. At a real
root, nonnegativity forces the derivative to vanish, so a squared linear factor
can be removed. This theorem is independent of any QSP phase-existence premise.
-/

namespace SparseHamiltonian.PolynomialCompletion

noncomputable section
open Polynomial PolynomialUnitarity
open scoped ComplexConjugate

/-- Real coefficients, viewed as complex coefficients. -/
def complexify (p : ℝ[X]) : ℂ[X] := p.map (algebraMap ℝ ℂ)

@[simp] theorem complexify_mul (p q : ℝ[X]) :
    complexify (p * q) = complexify p * complexify q := by simp [complexify]

@[simp] theorem complexify_C (a : ℝ) : complexify (C a) = C (a : ℂ) := by
  simp [complexify]

@[simp] theorem complexify_X : complexify (X : ℝ[X]) = X := by simp [complexify]

@[simp] theorem conjugate_complexify (p : ℝ[X]) :
    conjugate (complexify p) = complexify p := by
  ext n
  simp [complexify, conjugate]

@[simp] theorem complexify_eval_real (p : ℝ[X]) (x : ℝ) :
    (complexify p).eval (x : ℂ) = ((p.eval x : ℝ) : ℂ) := by
  exact eval_map_apply (f := algebraMap ℝ ℂ) (p := p) x

/-- A real zero of a globally nonnegative polynomial has zero derivative. -/
theorem derivative_eq_zero_of_nonnegative (p : ℝ[X])
    (hp : ∀ x : ℝ, 0 ≤ p.eval x) (x : ℝ) (hx : p.eval x = 0) :
    p.derivative.eval x = 0 := by
  have hm : IsLocalMin (fun y : ℝ => p.eval y) x := by
    apply Filter.Eventually.of_forall
    intro y
    simpa only [hx] using hp y
  exact hm.hasDerivAt_eq_zero (p.hasDerivAt x)

/-- Each real zero of a nonnegative polynomial supplies a squared linear factor. -/
theorem square_linear_dvd (p : ℝ[X]) (hp : ∀ x : ℝ, 0 ≤ p.eval x)
    (x : ℝ) (hx : p.eval x = 0) : (X - C x) ^ 2 ∣ p := by
  obtain ⟨q, hq⟩ := (dvd_iff_isRoot.mpr hx : X - C x ∣ p)
  have hd := derivative_eq_zero_of_nonnegative p hp x hx
  have hqx : q.eval x = 0 := by
    rw [hq] at hd
    simpa using hd
  obtain ⟨r, hr⟩ := (dvd_iff_isRoot.mpr hqx : X - C x ∣ q)
  exact ⟨r, by rw [hq, hr]; ring⟩

/-- A continuous polynomial nonnegative away from one point is nonnegative everywhere. -/
theorem nonnegative_of_except_one (p : ℝ[X]) (x : ℝ)
    (hp : ∀ y : ℝ, y ≠ x → 0 ≤ p.eval y) : ∀ y : ℝ, 0 ≤ p.eval y := by
  have hclosed : IsClosed {y : ℝ | 0 ≤ p.eval y} :=
    isClosed_le continuous_const p.continuous
  have hsub : ({x}ᶜ : Set ℝ) ⊆ {y : ℝ | 0 ≤ p.eval y} := by
    intro y hy
    exact hp y (by simpa using hy)
  have h := closure_minimal hsub hclosed
  rw [(dense_compl_singleton x).closure_eq] at h
  exact fun y => h (Set.mem_univ y)

/-- Removing a squared real linear factor preserves global nonnegativity. -/
theorem quotient_nonnegative (p q : ℝ[X]) (x : ℝ)
    (hp : ∀ y : ℝ, 0 ≤ p.eval y) (heq : p = (X - C x) ^ 2 * q) :
    ∀ y : ℝ, 0 ≤ q.eval y := by
  apply nonnegative_of_except_one q x
  intro y hy
  have h := hp y
  rw [heq] at h
  simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_C] at h
  exact nonneg_of_mul_nonneg_right h (sq_pos_of_ne_zero (sub_ne_zero.mpr hy))

/-- Quadratic factor associated with a complex-conjugate root pair. -/
def quadratic (z : ℂ) : ℝ[X] := X ^ 2 - C (2 * z.re) * X + C (‖z‖ ^ 2)

/-- The quadratic is exactly the norm square of a complex linear factor. -/
theorem quadratic_factor (z : ℂ) :
    complexify (quadratic z) = (X - C z) * conjugate (X - C z) := by
  have hm : complexify (quadratic z) =
      X ^ 2 - C (↑(2 * z.re) : ℂ) * X + C (↑(‖z‖ ^ 2) : ℂ) := by
    simp [complexify, quadratic]
  rw [hm, ← Complex.add_conj, map_add, Complex.ofReal_pow,
    ← Complex.mul_conj', map_mul]
  simp only [conjugate_sub, conjugate_X, conjugate_C]
  ring

/-- A nonreal conjugate pair gives a quadratic strictly positive on the real line. -/
theorem quadratic_pos (z : ℂ) (hz : z.im ≠ 0) (x : ℝ) :
    0 < (quadratic z).eval x := by
  simp only [quadratic, eval_add, eval_sub, eval_pow, eval_X, eval_mul, eval_C]
  rw [Complex.sq_norm, Complex.normSq_apply]
  have := sq_pos_of_ne_zero hz
  nlinarith [sq_nonneg (x - z.re)]

/-- The conjugate-pair factor has degree two. -/
theorem quadratic_degree (z : ℂ) : (quadratic z).natDegree = 2 := by
  have h := natDegree_quadratic (R := ℝ) (a := (1 : ℝ)) (b := -(2 * z.re))
    (c := ‖z‖ ^ 2) (by norm_num)
  simpa [quadratic, sub_eq_add_neg] using h


/-- Removing one conjugate pair, including a double real root, preserves
nonnegativity and decreases the degree by two. -/
theorem factor_step (p : ℝ[X]) (hp : ∀ x : ℝ, 0 ≤ p.eval x)
    (hd : 0 < p.natDegree) :
    ∃ q : ℝ[X], ∃ l : ℂ[X],
      (∀ x : ℝ, 0 ≤ q.eval x) ∧ q.natDegree < p.natDegree ∧
      complexify p = (l * conjugate l) * complexify q := by
  have hp0 : p ≠ 0 := ne_zero_of_natDegree_gt hd
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_aeval_eq_zero ℂ p
    (natDegree_pos_iff_degree_pos.mp hd).ne'
  by_cases hzim : z.im = 0
  · have hre : (z.re : ℂ) = z := by
      apply Complex.ext <;> simp [hzim]
    have hx : p.eval z.re = 0 := by
      have hz' : (complexify p).eval (z.re : ℂ) = 0 := by
        simpa only [complexify, ← eval₂_eq_eval_map, ← aeval_def, hre] using hz
      rw [complexify_eval_real] at hz'
      exact_mod_cast hz'
    obtain ⟨q, hq⟩ := square_linear_dvd p hp z.re hx
    refine ⟨q, X - C (z.re : ℂ), quotient_nonnegative p q z.re hp hq, ?_, ?_⟩
    · have hq0 : q ≠ 0 := by intro h; simp [h] at hq; exact hp0 hq
      have hdeg : p.natDegree = 2 + q.natDegree := by
        rw [hq, natDegree_mul (pow_ne_zero 2 (X_sub_C_ne_zero _)) hq0,
          natDegree_pow, natDegree_X_sub_C]
      omega
    · rw [hq]
      simp [complexify, conjugate_sub, conjugate_C, conjugate_X, pow_two]
  · obtain ⟨q, hq⟩ := p.quadratic_dvd_of_aeval_eq_zero_im_ne_zero hz hzim
    have hq' : p = quadratic z * q := hq
    refine ⟨q, X - C z, ?_, ?_, ?_⟩
    · intro x
      have h := hp x
      rw [hq', eval_mul] at h
      exact nonneg_of_mul_nonneg_right h (quadratic_pos z hzim x)
    · have hq0 : q ≠ 0 := by intro h; simp [h] at hq'; exact hp0 hq'
      have hf0 : quadratic z ≠ 0 := by
        intro h
        have hh := quadratic_degree z
        simp [h] at hh
      have hdeg : p.natDegree = 2 + q.natDegree := by
        rw [hq', natDegree_mul hf0 hq0, quadratic_degree]
      omega
    · rw [hq', complexify_mul, quadratic_factor]

/-- Every globally nonnegative real polynomial is the modulus square of a
complex polynomial. This includes zero polynomials and real roots. -/
theorem exists_spectral_factor (p : ℝ[X]) (hp : ∀ x : ℝ, 0 ≤ p.eval x) :
    ∃ q : ℂ[X], complexify p = q * conjugate q := by
  induction hd : p.natDegree using Nat.strong_induction_on generalizing p with
  | h n ih =>
    by_cases hn : n = 0
    · have heq : p = C (p.coeff 0) := eq_C_of_natDegree_eq_zero (hd.trans hn)
      have hc : 0 ≤ p.coeff 0 := by
        have hh := hp 0
        rw [heq, eval_C] at hh
        exact hh
      refine ⟨C (Real.sqrt (p.coeff 0) : ℂ), ?_⟩
      rw [heq, complexify_C, conjugate_C, Complex.conj_ofReal, ← C_mul]
      simp only [coeff_C_zero]
      congr 1
      exact_mod_cast (Real.mul_self_sqrt hc).symm
    · obtain ⟨r, l, hr, hrd, heq⟩ := factor_step p hp (by omega)
      obtain ⟨q, hq⟩ := ih r.natDegree (by omega) r hr rfl
      refine ⟨l * q, ?_⟩
      rw [heq, hq, conjugate_mul]
      ring

/-- Coefficient conjugation preserves natural degree exactly. -/
theorem conjugate_degree (p : ℂ[X]) : (conjugate p).natDegree = p.natDegree := by
  apply le_antisymm (conjugate_natDegree_le p)
  simpa only [conjugate_conjugate] using conjugate_natDegree_le (conjugate p)

/-- A spectral factor of a nonzero polynomial has exactly half its degree. -/
theorem spectral_factor_degree (p : ℝ[X]) (q : ℂ[X]) (hp : p ≠ 0)
    (hq : complexify p = q * conjugate q) : p.natDegree = 2 * q.natDegree := by
  have hpmap : complexify p ≠ 0 := by simpa [complexify] using hp
  have hq0 : q ≠ 0 := by intro h; simp [h] at hq; exact hpmap hq
  have hc0 : conjugate q ≠ 0 := by
    intro h
    have hh := congrArg conjugate h
    exact hq0 (by simpa [conjugate] using hh)
  have hd := congrArg natDegree hq
  simpa [complexify, natDegree_mul hq0 hc0, conjugate_degree, two_mul] using hd

/-- Nonnegativity supplies the spectral factor and the degree bound together. -/
theorem exists_spectral_factor_degree (p : ℝ[X]) (hp : ∀ x : ℝ, 0 ≤ p.eval x) :
    ∃ q : ℂ[X], complexify p = q * conjugate q ∧ 2 * q.natDegree = p.natDegree := by
  by_cases hp0 : p = 0
  · subst p
    exact ⟨0, by simp [complexify], by simp⟩
  · obtain ⟨q, hq⟩ := exists_spectral_factor p hp
    exact ⟨q, hq, (spectral_factor_degree p q hp0 hq).symm⟩

end
end SparseHamiltonian.PolynomialCompletion
