import SparseHamiltonian.ODEConstantForcing
import GeneralODE.Analysis.Runs

/-!
# Taylor polynomials of the exponential

`taylorExp K x = ∑_{k ≤ K} x^k / k!` in a complete normed `ℂ`-algebra with
`‖1‖ = 1`.  We prove the remainder bound
`‖exp x - taylorExp K x‖ ≤ ‖x‖^(K+1)/(K+1)! · e^‖x‖`, the stability bound
`‖taylorExp K y - taylorExp K z‖ ≤ ‖y - z‖ e^M` for `‖y‖, ‖z‖ ≤ M`, and the
corresponding statements for the constant-forcing response
`∫₀ʰ e^{uA} b du = h φ₁(hA) b` used by Theorem `ode:thm:general`.
-/

namespace SparseHamiltonian.GeneralODE.ExpBounds

noncomputable section
open NormedSpace
open scoped BigOperators Nat

section Algebra

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸]

/-- Degree-`K` Taylor polynomial of the exponential. -/
def taylorExp (K : ℕ) (x : 𝔸) : 𝔸 :=
  ∑ k ∈ Finset.range (K + 1), ((k ! : ℂ)⁻¹) • x ^ k

omit [NormedAlgebra ℂ 𝔸] [CompleteSpace 𝔸] in
theorem norm_pow_le_pow (x : 𝔸) (k : ℕ) : ‖x ^ k‖ ≤ ‖x‖ ^ k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · exact norm_pow_le' x hk

/-- Factorial splitting used for the exponential tail. -/
theorem factorial_mul_le (a b : ℕ) : (a ! : ℝ) * (b ! : ℝ) ≤ ((a + b) ! : ℝ) := by
  exact_mod_cast Nat.le_of_dvd (Nat.factorial_pos _) (Nat.factorial_mul_factorial_dvd_factorial_add a b)

/-- Real exponential series. -/
theorem real_exp_hasSum (r : ℝ) : HasSum (fun k : ℕ => r ^ k / (k ! : ℝ)) (Real.exp r) := by
  have h := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (𝔸 := ℝ) r
  rw [← Real.exp_eq_exp_ℝ] at h
  have hf : (fun k : ℕ => r ^ k / (k ! : ℝ)) = fun n : ℕ => ((n ! : ℝ)⁻¹) • r ^ n := by
    funext k
    simp [div_eq_inv_mul, smul_eq_mul]
  rw [hf]
  exact h

/-- Taylor remainder of the Banach-algebra exponential. -/
theorem norm_exp_sub_taylorExp_le (x : 𝔸) (K : ℕ) :
    ‖exp x - taylorExp K x‖ ≤ ‖x‖ ^ (K + 1) / ((K + 1) ! : ℝ) * Real.exp ‖x‖ := by
  have hS : HasSum (fun k : ℕ => ((k ! : ℂ)⁻¹) • x ^ k) (exp x) :=
    NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) x
  have hTail := (hasSum_nat_add_iff' (K + 1)).mpr hS
  have hBound : HasSum (fun k : ℕ => ‖x‖ ^ (K + 1) / ((K + 1) ! : ℝ) * (‖x‖ ^ k / (k ! : ℝ)))
      (‖x‖ ^ (K + 1) / ((K + 1) ! : ℝ) * Real.exp ‖x‖) :=
    (real_exp_hasSum ‖x‖).mul_left _
  have hle := hTail.norm_le_of_bounded hBound (fun k => by
    rw [norm_smul, norm_inv, Complex.norm_natCast]
    have hfact := factorial_mul_le (K + 1) k
    have hpos1 : (0 : ℝ) < ((K + 1) ! : ℝ) := by exact_mod_cast Nat.factorial_pos _
    have hpos2 : (0 : ℝ) < (k ! : ℝ) := by exact_mod_cast Nat.factorial_pos _
    have hpos3 : (0 : ℝ) < ((k + (K + 1)) ! : ℝ) := by exact_mod_cast Nat.factorial_pos _
    calc
      ((k + (K + 1)) ! : ℝ)⁻¹ * ‖x ^ (k + (K + 1))‖
          ≤ ((k + (K + 1)) ! : ℝ)⁻¹ * ‖x‖ ^ (k + (K + 1)) :=
            mul_le_mul_of_nonneg_left (norm_pow_le_pow x _) (inv_nonneg.mpr hpos3.le)
      _ ≤ (((K + 1) ! : ℝ) * (k ! : ℝ))⁻¹ * ‖x‖ ^ (k + (K + 1)) := by
            apply mul_le_mul_of_nonneg_right _ (pow_nonneg (norm_nonneg _) _)
            apply inv_anti₀ (mul_pos hpos1 hpos2)
            rw [add_comm k (K + 1)]
            exact hfact
      _ = ‖x‖ ^ (K + 1) / ((K + 1) ! : ℝ) * (‖x‖ ^ k / (k ! : ℝ)) := by
            rw [pow_add]; field_simp)
  have hsum : exp x - ∑ i ∈ Finset.range (K + 1), ((i ! : ℂ)⁻¹) • x ^ i =
      exp x - taylorExp K x := rfl
  rw [← hsum]
  exact hle

/-- The exponential is bounded by the exponential of the norm. -/
theorem norm_exp_le (x : 𝔸) : ‖exp x‖ ≤ Real.exp ‖x‖ := by
  have hS : HasSum (fun k : ℕ => ((k ! : ℂ)⁻¹) • x ^ k) (exp x) :=
    NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) x
  exact hS.norm_le_of_bounded (real_exp_hasSum ‖x‖) (fun k => by
    rw [norm_smul, norm_inv, Complex.norm_natCast, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left (norm_pow_le_pow x k)
      (inv_nonneg.mpr (by exact_mod_cast (Nat.factorial_pos k).le)))

/-- `‖e^x - 1‖ ≤ ‖x‖ e^‖x‖`. -/
theorem norm_exp_sub_one_le (x : 𝔸) : ‖exp x - 1‖ ≤ ‖x‖ * Real.exp ‖x‖ := by
  have h := norm_exp_sub_taylorExp_le x 0
  simpa [taylorExp] using h

omit [NormedAlgebra ℂ 𝔸] [CompleteSpace 𝔸] in
/-- Noncommutative difference of powers. -/
theorem norm_pow_sub_pow_le (y z : 𝔸) (M : ℝ) (hy : ‖y‖ ≤ M) (hz : ‖z‖ ≤ M) (k : ℕ) :
    ‖y ^ k - z ^ k‖ ≤ k * ‖y - z‖ * M ^ (k - 1) := by
  have hM : 0 ≤ M := (norm_nonneg _).trans hy
  induction k with
  | zero => simp
  | succ k ih =>
      have hid : y ^ (k + 1) - z ^ (k + 1) = y * (y ^ k - z ^ k) + (y - z) * z ^ k := by
        rw [pow_succ', pow_succ']; noncomm_ring
      rw [hid]
      calc
        ‖y * (y ^ k - z ^ k) + (y - z) * z ^ k‖
            ≤ ‖y‖ * ‖y ^ k - z ^ k‖ + ‖y - z‖ * ‖z ^ k‖ := by
              refine (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
        _ ≤ M * (k * ‖y - z‖ * M ^ (k - 1)) + ‖y - z‖ * M ^ k := by
              apply add_le_add
              · exact mul_le_mul hy ih (norm_nonneg _) hM
              · exact mul_le_mul_of_nonneg_left
                  ((norm_pow_le_pow z k).trans (pow_le_pow_left₀ (norm_nonneg _) hz k))
                  (norm_nonneg _)
        _ = ((k + 1 : ℕ) : ℝ) * ‖y - z‖ * M ^ (k + 1 - 1) := by
              rcases Nat.eq_zero_or_pos k with rfl | hk
              · simp
              · have : M * M ^ (k - 1) = M ^ k := by
                  rw [← pow_succ']; congr 1; omega
                push_cast
                calc
                  M * (↑k * ‖y - z‖ * M ^ (k - 1)) + ‖y - z‖ * M ^ k
                      = ↑k * ‖y - z‖ * (M * M ^ (k - 1)) + ‖y - z‖ * M ^ k := by ring
                  _ = _ := by rw [this]; ring

omit [CompleteSpace 𝔸] in
/-- Stability of the Taylor polynomial. -/
theorem norm_taylorExp_sub_le (y z : 𝔸) (M : ℝ) (hy : ‖y‖ ≤ M) (hz : ‖z‖ ≤ M) (K : ℕ) :
    ‖taylorExp K y - taylorExp K z‖ ≤ ‖y - z‖ * Real.exp M := by
  have hM : 0 ≤ M := (norm_nonneg _).trans hy
  unfold taylorExp
  rw [← Finset.sum_sub_distrib, Finset.sum_range_succ']
  simp only [pow_zero, sub_self, add_zero]
  calc
    ‖∑ j ∈ Finset.range K, (((j + 1) ! : ℂ)⁻¹ • y ^ (j + 1) -
        ((j + 1) ! : ℂ)⁻¹ • z ^ (j + 1))‖
        ≤ ∑ j ∈ Finset.range K, ‖((j + 1) ! : ℂ)⁻¹ • y ^ (j + 1) -
            ((j + 1) ! : ℂ)⁻¹ • z ^ (j + 1)‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range K, ‖y - z‖ * (M ^ j / (j ! : ℝ)) := by
        apply Finset.sum_le_sum
        intro j _
        rw [← smul_sub, norm_smul, norm_inv, Complex.norm_natCast]
        have h := norm_pow_sub_pow_le y z M hy hz (j + 1)
        have hpos : (0 : ℝ) < (j ! : ℝ) := by exact_mod_cast Nat.factorial_pos j
        have hfac : ((j + 1) ! : ℝ) = (j + 1 : ℝ) * (j ! : ℝ) := by
          rw [Nat.factorial_succ]; push_cast; ring
        calc
          ((j + 1) ! : ℝ)⁻¹ * ‖y ^ (j + 1) - z ^ (j + 1)‖
              ≤ ((j + 1) ! : ℝ)⁻¹ * (((j + 1 : ℕ) : ℝ) * ‖y - z‖ * M ^ (j + 1 - 1)) :=
                mul_le_mul_of_nonneg_left h (inv_nonneg.mpr (by positivity))
          _ = ‖y - z‖ * (M ^ j / (j ! : ℝ)) := by
                rw [hfac, show j + 1 - 1 = j by omega]
                push_cast
                field_simp
    _ = ‖y - z‖ * ∑ j ∈ Finset.range K, M ^ j / (j ! : ℝ) := (Finset.mul_sum _ _ _).symm
    _ ≤ ‖y - z‖ * Real.exp M :=
        mul_le_mul_of_nonneg_left (Real.sum_le_exp_of_nonneg hM K) (norm_nonneg _)

end Algebra

section Forcing

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

open ODEDissipative ODEConstantForcing

/-- Taylor polynomial of `h φ₁(hA) = ∫₀ʰ e^{uA} du`. -/
def phiTaylor (K : ℕ) (h : ℝ) (A : V →L[ℂ] V) : V →L[ℂ] V :=
  ∑ k ∈ Finset.range (K + 1), ((h ^ (k + 1) / ((k + 1) ! : ℝ) : ℝ) : ℂ) • A ^ k

/-- The exact one-step relation for constant forcing. -/
theorem solution_add (A : V →L[ℂ] V) (v b : V) (t h : ℝ) :
    solution A v b (t + h) = exp (h • A) (solution A v b t) + response A b h := by
  letI : NormedAlgebra ℚ (V →L[ℂ] V) := .restrictScalars ℚ ℂ _
  have htraj (w : V) (u : ℝ) : trajectory A w (u + h) = exp (h • A) (trajectory A w u) := by
    have hcomm : Commute (h • A) (u • A) := ((Commute.refl A).smul_left h).smul_right u
    simp only [trajectory]
    rw [add_smul, add_comm (u • A) (h • A), exp_add_of_commute hcomm]
    rfl
  have hc := trajectory_continuous A b
  have hresp : response A b (t + h) = response A b h + exp (h • A) (response A b t) := by
    simp only [response]
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := h)
      (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
    congr 1
    have hsub : (∫ s in h..t + h, trajectory A b s) =
        ∫ s in (0 : ℝ)..t, trajectory A b (s + h) := by
      rw [intervalIntegral.integral_comp_add_right (fun s => trajectory A b s) h, zero_add]
    rw [hsub]
    simp_rw [htraj b]
    exact (exp (h • A)).intervalIntegral_comp_comm (hc.intervalIntegrable _ _)
  simp only [solution]
  rw [htraj v t, hresp, map_add]
  abel

variable [Nontrivial V]

omit [Nontrivial V] in
/-- `∫₀ʰ taylorExp K (uA) b du` is the Taylor polynomial of `h φ₁(hA) b`. -/
theorem integral_taylorExp (K : ℕ) (h : ℝ) (A : V →L[ℂ] V) (b : V) :
    (∫ u in (0 : ℝ)..h, taylorExp K (u • A) b) = phiTaylor K h A b := by
  have hterm (k : ℕ) (u : ℝ) : (((k ! : ℂ)⁻¹) • (u • A) ^ k) b =
      (u ^ k) • (((k ! : ℂ)⁻¹) • (A ^ k) b) := by
    rw [smul_pow]
    simp only [smul_apply]
    rw [smul_comm]
  have hfun : (fun u : ℝ => taylorExp K (u • A) b) =
      fun u => ∑ k ∈ Finset.range (K + 1), (u ^ k) • (((k ! : ℂ)⁻¹) • (A ^ k) b) := by
    funext u
    simp only [taylorExp, sum_apply]
    exact Finset.sum_congr rfl (fun k _ => hterm k u)
  rw [hfun, intervalIntegral.integral_finsetSum]
  · simp only [phiTaylor, sum_apply, smul_apply]
    apply Finset.sum_congr rfl
    intro k _
    rw [intervalIntegral.integral_smul_const, integral_pow]
    simp only [zero_pow (Nat.succ_ne_zero k), sub_zero]
    rw [← Complex.coe_smul, smul_smul]
    congr 1
    have hpos : (k ! : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
    have hpos1 : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    push_cast [Nat.factorial_succ]
    field_simp
  · intro k _
    exact ((continuous_pow k).smul continuous_const).intervalIntegrable _ _

/-- Remainder of the source Taylor polynomial. -/
theorem norm_response_sub_phiTaylor_le (A : V →L[ℂ] V) (b : V) (h : ℝ) (hh : 0 ≤ h) (K : ℕ) :
    ‖response A b h - phiTaylor K h A b‖ ≤
      h * ((‖A‖ * h) ^ (K + 1) / ((K + 1) ! : ℝ) * Real.exp (‖A‖ * h)) * ‖b‖ := by
  rw [← integral_taylorExp K h A b]
  have hc := trajectory_continuous A b
  have hT : Continuous (fun u : ℝ => taylorExp K (u • A) b) := by
    have hA : Continuous fun u : ℝ => u • A := continuous_id.smul continuous_const
    have hpoly : Continuous fun u : ℝ => taylorExp K (u • A) := by
      unfold taylorExp
      fun_prop
    exact hpoly.clm_apply continuous_const
  rw [response, ← intervalIntegral.integral_sub (hc.intervalIntegrable _ _) (hT.intervalIntegrable _ _)]
  have hbound : ∀ u ∈ Set.uIoc (0 : ℝ) h, ‖trajectory A b u - taylorExp K (u • A) b‖ ≤
      ((‖A‖ * h) ^ (K + 1) / ((K + 1) ! : ℝ) * Real.exp (‖A‖ * h)) * ‖b‖ := by
    intro u hu
    rw [Set.uIoc_of_le hh] at hu
    have hu0 : 0 ≤ u := hu.1.le
    have huh : u ≤ h := hu.2
    have hnorm : ‖u • A‖ ≤ ‖A‖ * h := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hu0, mul_comm]
      exact mul_le_mul_of_nonneg_left huh (norm_nonneg _)
    have hrem := norm_exp_sub_taylorExp_le (u • A) K
    have hmono : ‖u • A‖ ^ (K + 1) / ((K + 1) ! : ℝ) * Real.exp ‖u • A‖ ≤
        (‖A‖ * h) ^ (K + 1) / ((K + 1) ! : ℝ) * Real.exp (‖A‖ * h) := by
      apply mul_le_mul _ (Real.exp_le_exp.mpr hnorm) (Real.exp_pos _).le (by positivity)
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact pow_le_pow_left₀ (norm_nonneg _) hnorm _
    calc
      ‖trajectory A b u - taylorExp K (u • A) b‖ = ‖(exp (u • A) - taylorExp K (u • A)) b‖ := by
          simp [trajectory]
      _ ≤ ‖exp (u • A) - taylorExp K (u • A)‖ * ‖b‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right (hrem.trans hmono) (norm_nonneg _)
  have h2 := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [sub_zero, abs_of_nonneg hh] at h2
  calc
    _ ≤ _ := h2
    _ = _ := by ring

/-- The response to constant forcing is close to `h b` for short steps. -/
theorem norm_response_ge (A : V →L[ℂ] V) (b : V) (h : ℝ) (hh : 0 ≤ h) :
    h * ‖b‖ * (1 - ‖A‖ * h * Real.exp (‖A‖ * h)) ≤ ‖response A b h‖ := by
  have hc := trajectory_continuous A b
  have hsplit : response A b h = h • b + ∫ u in (0 : ℝ)..h, (trajectory A b u - b) := by
    rw [intervalIntegral.integral_sub (hc.intervalIntegrable _ _) intervalIntegrable_const,
      intervalIntegral.integral_const, sub_zero, response]
    abel
  have hbound : ∀ u ∈ Set.uIoc (0 : ℝ) h, ‖trajectory A b u - b‖ ≤
      (‖A‖ * h * Real.exp (‖A‖ * h)) * ‖b‖ := by
    intro u hu
    rw [Set.uIoc_of_le hh] at hu
    have hu0 : 0 ≤ u := hu.1.le
    have hnorm : ‖u • A‖ ≤ ‖A‖ * h := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hu0, mul_comm]
      exact mul_le_mul_of_nonneg_left hu.2 (norm_nonneg _)
    calc
      ‖trajectory A b u - b‖ = ‖(exp (u • A) - 1) b‖ := by simp [trajectory]
      _ ≤ ‖exp (u • A) - 1‖ * ‖b‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (‖A‖ * h * Real.exp (‖A‖ * h)) * ‖b‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          exact (norm_exp_sub_one_le (u • A)).trans
            (mul_le_mul hnorm (Real.exp_le_exp.mpr hnorm) (Real.exp_pos _).le
              (by positivity))
  have h2 := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [sub_zero, abs_of_nonneg hh] at h2
  have h3 : ‖h • b‖ = h * ‖b‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hh]
  rw [hsplit]
  have h4 := norm_sub_norm_le (h • b) (-(∫ u in (0 : ℝ)..h, (trajectory A b u - b)))
  rw [sub_neg_eq_add, norm_neg] at h4
  nlinarith [h2, h3, h4]

end Forcing

end

end SparseHamiltonian.GeneralODE.ExpBounds
