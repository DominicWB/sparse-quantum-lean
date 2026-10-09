import SparseHamiltonian.FractionalAngleSeriesIdentity

/-!
# The arcsine series and its Fourier form

For `|y| < 1`, `arcsin y = ∑_k a_k y^{2k+1}` with the explicit nonnegative
coefficients `a_k = coefficient 0 k` of the released fractional-angle
series (`a_k = C(2k,k)/(4^k (2k+1))`).  The identification uses the released
termwise derivatives and the differential equation `(1-y²) f'' = y f'`.

Hence for real `|θ| ≤ 1/2` the degree-`(2N-1)` truncation `p_N` satisfies
`|p_N(sin θ) - θ| ≤ 4^{-N}`.  Expanding each power of
`sin θ = (e^{iθ} - e^{-iθ})/(2i)` by the binomial theorem writes `p_N(sin θ)`
as `∑_{k<N} ∑_{r<2N} c_{k,r} e^{i(2k+1-2r)θ}` with coefficient one-norm
`∑_{k<N} a_k ≤ 2`.
-/

namespace SparseHamiltonian.GeneralODE.Arcsine

noncomputable section
open FractionalAngleCoefficients FractionalAngleSeriesDifferentiation FractionalAngleSeriesIdentity
open scoped BigOperators

/-- The released series at angle parameter zero is the arcsine. -/
theorem series_zero_eq_arcsin (y : ℝ) (hy : |y| < 1) : series 0 y = Real.arcsin y := by
  have ha : |(0 : ℝ)| ≤ 1 := by simp
  -- the first derivative is `1 / √(1 - t²)`
  have hfirst : ∀ t ∈ Set.Ioo (-1 : ℝ) 1, firstDerivative 0 t = 1 / Real.sqrt (1 - t ^ 2) := by
    let g : ℝ → ℝ := fun t => Real.sqrt (1 - t ^ 2) * firstDerivative 0 t
    have hg : ∀ t ∈ Set.Ioo (-1 : ℝ) 1, HasDerivAt g 0 t := by
      intro t ht
      have ht' : |t| < 1 := abs_lt.mpr ht
      have hpos : 0 < 1 - t ^ 2 := by
        have : t ^ 2 < 1 := by nlinarith [abs_lt.mp ht', sq_abs t, abs_nonneg t]
        linarith
      have hs : 0 < Real.sqrt (1 - t ^ 2) := Real.sqrt_pos.mpr hpos
      have hden : HasDerivAt (fun u : ℝ => 1 - u ^ 2) (-(2 * t)) t := by
        have := ((hasDerivAt_id t).pow 2).const_sub (1 : ℝ)
        simpa using this
      have hsqrt := hden.sqrt hpos.ne'
      have hprod := hsqrt.mul (hasDerivAt_firstDerivative 0 ha t ht')
      have hode := series_ode 0 ha t ht'
      refine hprod.congr_deriv ?_
      set s := Real.sqrt (1 - t ^ 2) with hsdef
      have hsq : s * s = 1 - t ^ 2 := Real.mul_self_sqrt hpos.le
      have e1 : -(2 * t) / (2 * s) * s = -t := by field_simp
      have h2 : (-(2 * t) / (2 * s) * firstDerivative 0 t + s * secondDerivative 0 t) * s = 0 := by
        calc (-(2 * t) / (2 * s) * firstDerivative 0 t + s * secondDerivative 0 t) * s
            = (-(2 * t) / (2 * s) * s) * firstDerivative 0 t +
                (s * s) * secondDerivative 0 t := by ring
          _ = (1 - t ^ 2) * secondDerivative 0 t - t * firstDerivative 0 t := by
                rw [e1, hsq]; ring
          _ = 0 := by linarith [hode]
      exact (mul_eq_zero.mp h2).resolve_right hs.ne'
    intro t ht
    have h0 : g 0 = 1 := by simp [g, firstDerivative_zero 0 ha]
    have heq := isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
      (fun t ht => (hg t ht).differentiableAt.differentiableWithinAt)
      (fun t ht => (hg t ht).deriv) ht (by norm_num : (0 : ℝ) ∈ Set.Ioo (-1) 1)
    rw [h0] at heq
    have hpos : 0 < 1 - t ^ 2 := by
      have : t ^ 2 < 1 := by nlinarith [ht.1, ht.2]
      linarith
    have hs : 0 < Real.sqrt (1 - t ^ 2) := Real.sqrt_pos.mpr hpos
    simp only [g] at heq
    field_simp
    linarith
  -- the difference with `arcsin` is constant
  have hd : ∀ t ∈ Set.Ioo (-1 : ℝ) 1, HasDerivAt (fun u => series 0 u - Real.arcsin u) 0 t := by
    intro t ht
    have h1 := hasDerivAt_series 0 ha t (abs_lt.mpr ht)
    have h2 := Real.hasDerivAt_arcsin (x := t) (by linarith [ht.1]) (by linarith [ht.2])
    have := h1.sub h2
    rw [hfirst t ht, sub_self] at this
    exact this
  have heq := isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
    (fun t ht => (hd t ht).differentiableAt.differentiableWithinAt)
    (fun t ht => (hd t ht).deriv) (abs_lt.mp hy) (by norm_num : (0 : ℝ) ∈ Set.Ioo (-1) 1)
  have h0 : series 0 0 - Real.arcsin 0 = 0 := by
    rw [FractionalAngleSeriesDifferentiation.series_zero, Real.arcsin_zero, sub_zero]
  have h1 : series 0 y - Real.arcsin y = 0 := by
    have h : series 0 y - Real.arcsin y = series 0 0 - Real.arcsin 0 := heq
    rw [h, h0]
  linarith

/-- Truncation error of the arcsine series at `sin θ`. -/
theorem correction_sin_sub_le (θ : ℝ) (hθ : |θ| ≤ 1 / 2) (N : ℕ) :
    |(correction 0 N).eval (Real.sin θ) - θ| ≤ (1 / 4) ^ N := by
  have ha : |(0 : ℝ)| ≤ 1 := by simp
  have hy : |Real.sin θ| ≤ 1 / 2 := (Real.abs_sin_le_abs).trans hθ
  have harc : series 0 (Real.sin θ) = θ := by
    rw [series_zero_eq_arcsin _ (by linarith)]
    apply Real.arcsin_sin
    · have := neg_abs_le θ; have := Real.pi_gt_three; linarith
    · have := le_abs_self θ; have := Real.pi_gt_three; linarith
  have ht := relative_tail 0 ha N (1 / 2) (Real.sin θ) (by norm_num) (by norm_num) hy
  rw [harc, abs_sub_comm] at ht
  calc |(correction 0 N).eval (Real.sin θ) - θ| ≤ 2 * (1 / 2) ^ (2 * N) * |Real.sin θ| := ht
    _ ≤ 2 * (1 / 2) ^ (2 * N) * (1 / 2) := by gcongr
    _ = (1 / 4) ^ N := by rw [pow_mul]; norm_num; ring

/-- The complex sine of a real angle. -/
theorem sin_ofReal_eq (θ : ℝ) :
    ((Real.sin θ : ℝ) : ℂ) =
      (2 * Complex.I)⁻¹ * (Complex.exp (θ * Complex.I) - Complex.exp (-(θ * Complex.I))) := by
  rw [Complex.ofReal_sin, Complex.sin]
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  field_simp
  rw [Complex.I_sq]
  ring

/-- Finite Fourier form of odd powers of `sin θ`. -/
theorem sin_pow_eq (θ : ℝ) (m : ℕ) :
    ((Real.sin θ : ℝ) : ℂ) ^ m =
      ∑ r ∈ Finset.range (m + 1), (((2 * Complex.I)⁻¹) ^ m * (m.choose r : ℂ) * (-1) ^ r) *
        Complex.exp (((m : ℂ) - 2 * r) * θ * Complex.I) := by
  rw [sin_ofReal_eq, mul_pow, sub_eq_neg_add, add_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  have hr' : r ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
  rw [neg_pow, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
  have hexp : Complex.exp (↑r * -(↑θ * Complex.I)) * Complex.exp (↑(m - r) * (↑θ * Complex.I)) =
      Complex.exp ((↑m - 2 * ↑r) * ↑θ * Complex.I) := by
    rw [← Complex.exp_add, Nat.cast_sub hr']
    congr 1
    ring
  calc (2 * Complex.I)⁻¹ ^ m * ((-1) ^ r * Complex.exp (↑r * -(↑θ * Complex.I)) *
        Complex.exp (↑(m - r) * (↑θ * Complex.I)) * ↑(m.choose r))
      = (2 * Complex.I)⁻¹ ^ m * (↑(m.choose r) * (-1) ^ r) *
          (Complex.exp (↑r * -(↑θ * Complex.I)) * Complex.exp (↑(m - r) * (↑θ * Complex.I))) := by
        ring
    _ = _ := by rw [hexp]; ring

/-- The arcsine-LCU coefficient of `e^{i(2k+1-2r)θ}`. -/
def lcuCoef (k r : ℕ) : ℂ :=
  (coefficient 0 k : ℂ) * ((2 * Complex.I)⁻¹) ^ (2 * k + 1) * ((2 * k + 1).choose r : ℂ) * (-1) ^ r

/-- Fourier frequencies. -/
def freq (k r : ℕ) : ℤ := 2 * k + 1 - 2 * r

/-- `p_N(sin θ)` as a finite combination of the evolutions `e^{i j θ}`. -/
theorem correction_sin_eq (θ : ℝ) (N : ℕ) :
    (((correction 0 N).eval (Real.sin θ) : ℝ) : ℂ) =
      ∑ k ∈ Finset.range N, ∑ r ∈ Finset.range (2 * N),
        lcuCoef k r * Complex.exp ((freq k r : ℂ) * θ * Complex.I) := by
  rw [correction_eval, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkN : 2 * k + 1 + 1 ≤ 2 * N := by have := Finset.mem_range.mp hk; omega
  rw [Complex.ofReal_mul, Complex.ofReal_pow, sin_pow_eq, Finset.mul_sum]
  rw [← Finset.sum_subset (Finset.range_subset_range.mpr hkN)]
  · apply Finset.sum_congr rfl
    intro r _
    unfold lcuCoef freq
    push_cast
    ring
  · intro r _ hr
    have hlt : 2 * k + 1 < r := by
      have := Finset.mem_range.not.mp hr; omega
    simp [lcuCoef, Nat.choose_eq_zero_of_lt hlt]

theorem norm_lcuCoef (k r : ℕ) :
    ‖lcuCoef k r‖ = coefficient 0 k * ((1 / 2) ^ (2 * k + 1) * ((2 * k + 1).choose r : ℝ)) := by
  have hc := coefficient_nonneg 0 (by simp) k
  have h2I : ‖(2 * Complex.I)⁻¹‖ = 1 / 2 := by
    rw [norm_inv, norm_mul, Complex.norm_I]; norm_num
  unfold lcuCoef
  rw [norm_mul, norm_mul, norm_mul, norm_pow, h2I, norm_pow, norm_neg, norm_one, one_pow, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc, Complex.norm_natCast]
  ring

/-- The coefficient one-norm of each power is one; the total is at most two. -/
theorem sum_norm_lcuCoef (N : ℕ) :
    ∑ k ∈ Finset.range N, ∑ r ∈ Finset.range (2 * N), ‖lcuCoef k r‖ =
      ∑ k ∈ Finset.range N, coefficient 0 k := by
  apply Finset.sum_congr rfl
  intro k hk
  have hkN : 2 * k + 1 + 1 ≤ 2 * N := by have := Finset.mem_range.mp hk; omega
  simp only [norm_lcuCoef]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  rw [← Finset.sum_subset (Finset.range_subset_range.mpr hkN)]
  · have hsum : ∑ r ∈ Finset.range (2 * k + 1 + 1), ((2 * k + 1).choose r : ℝ) = 2 ^ (2 * k + 1) := by
      exact_mod_cast Nat.sum_range_choose (2 * k + 1)
    rw [hsum, ← mul_pow]
    norm_num
  · intro r _ hr
    have hlt : 2 * k + 1 < r := by
      have := Finset.mem_range.not.mp hr; omega
    simp [Nat.choose_eq_zero_of_lt hlt]

theorem sum_coefficient_zero_le_two (N : ℕ) : ∑ k ∈ Finset.range N, coefficient 0 k ≤ 2 :=
  sum_coefficient_le_two 0 (by simp) N

theorem coefficient_zero_nonneg (k : ℕ) : 0 ≤ coefficient 0 k :=
  coefficient_nonneg 0 (by simp) k

end

end SparseHamiltonian.GeneralODE.Arcsine
