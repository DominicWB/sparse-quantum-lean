import SparseHamiltonian.NativePolynomialSynthesis

/-!
# Constructive odd Chebyshev truncation and relative error

This module constructs finite odd Chebyshev polynomials and proves relative
error bounds from a geometric bound on the weighted expansion coefficients.
The error vanishes at the origin: it is proportional to `|x|`, rather than
merely an absolute uniform error. No amplitude multiplier or phase synthesis
is assumed or asserted here. Identifying a bounded multiplier with the
required coefficient bounds remains a separate analytic obligation.
-/

namespace SparseHamiltonian.OddChebyshevApproximation

noncomputable section
open Polynomial Polynomial.Chebyshev
open scoped BigOperators

/-- The elementary multiple-angle bound retains the small input factor. -/
theorem abs_sin_nat_mul (n : ℕ) (t : ℝ) :
    |Real.sin ((n : ℝ) * t)| ≤ (n : ℝ) * |Real.sin t| := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, Real.sin_add]
    calc
      |Real.sin ((n : ℝ) * t) * Real.cos t +
          Real.cos ((n : ℝ) * t) * Real.sin t| ≤
          |Real.sin ((n : ℝ) * t)| * |Real.cos t| +
            |Real.cos ((n : ℝ) * t)| * |Real.sin t| := by
              simpa only [abs_mul] using abs_add_le
                (Real.sin ((n : ℝ) * t) * Real.cos t)
                (Real.cos ((n : ℝ) * t) * Real.sin t)
      _ ≤ (n : ℝ) * |Real.sin t| * 1 + 1 * |Real.sin t| := by
        gcongr
        · exact Real.abs_cos_le_one t
        · exact Real.abs_cos_le_one ((n : ℝ) * t)
      _ = ((n : ℝ) + 1) * |Real.sin t| := by ring

/-- Odd Chebyshev polynomials admit a sine form around the origin. -/
theorem odd_chebyshev_sine (k : ℕ) (x : ℝ) (hx : |x| ≤ 1) :
    (T ℝ (2 * (k : ℤ) + 1)).eval x =
      (-1 : ℝ) ^ k * Real.sin ((2 * (k : ℝ) + 1) * Real.arcsin x) := by
  have hs : Real.cos (Real.pi / 2 - Real.arcsin x) = x := by
    rw [Real.cos_pi_div_two_sub, Real.sin_arcsin (abs_le.mp hx).1 (abs_le.mp hx).2]
  rw [← hs, T_real_cos]
  have he : ((2 * (k : ℤ) + 1 : ℤ) : ℝ) *
      (Real.pi / 2 - Real.arcsin x) =
      (Real.pi / 2 - (2 * (k : ℝ) + 1) * Real.arcsin x) + k * Real.pi := by
    push_cast
    ring
  rw [he, Real.cos_add_nat_mul_pi, Real.cos_pi_div_two_sub]
  rw [hs]

/-- Sharp relative bound, valid also at the two endpoints and at zero. -/
theorem abs_odd_chebyshev_le (k : ℕ) (x : ℝ) (hx : |x| ≤ 1) :
    |(T ℝ (2 * (k : ℤ) + 1)).eval x| ≤ (2 * (k : ℝ) + 1) * |x| := by
  rw [odd_chebyshev_sine k x hx, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  have h := abs_sin_nat_mul (2 * k + 1) (Real.arcsin x)
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
    Real.sin_arcsin (abs_le.mp hx).1 (abs_le.mp hx).2] using h

/-- An actual finite polynomial, with coefficients fixed independently of `x`. -/
def truncation (c : ℕ → ℝ) (N : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range N, C (c k) * T ℝ (2 * (k : ℤ) + 1)

@[simp] theorem truncation_eval (c : ℕ → ℝ) (N : ℕ) (x : ℝ) :
    (truncation c N).eval x =
      ∑ k ∈ Finset.range N, c k * (T ℝ (2 * (k : ℤ) + 1)).eval x := by
  simp [truncation, Polynomial.eval_finsetSum]

@[simp] theorem truncation_zero (c : ℕ → ℝ) : truncation c 0 = 0 := by
  simp [truncation]

/-- The polynomial is odd, even if some leading coefficients vanish. -/
theorem truncation_odd (c : ℕ → ℝ) (N : ℕ) :
    Function.Odd (fun x : ℝ => (truncation c N).eval x) := by
  intro x
  change (truncation c N).eval (-x) = -(truncation c N).eval x
  rw [truncation_eval, truncation_eval, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k _
  have ho : Odd (2 * (k : ℤ) + 1) := ⟨k, by ring⟩
  simp [T_eval_neg, Int.negOnePow_odd _ ho]


/-- With `N` terms the degree is at most `2N-1`; this convenient bound includes `N=0`. -/
theorem truncation_degree (c : ℕ → ℝ) (N : ℕ) :
    (truncation c N).natDegree ≤ 2 * N := by
  apply natDegree_sum_le_of_forall_le
  intro k hk
  have hkN := Finset.mem_range.mp hk
  apply natDegree_mul_le.trans
  rw [natDegree_C, zero_add, natDegree_T]
  have he : (2 * (k : ℤ) + 1).natAbs = 2 * k + 1 := by omega
  rw [he]
  omega


/-- The target represented by the complete odd Chebyshev expansion. -/
def series (c : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑' k : ℕ, c k * (T ℝ (2 * (k : ℤ) + 1)).eval x

/-- A coefficient bound gives a pointwise bound retaining the factor `|x|`. -/
theorem term_bound (c : ℕ → ℝ) (C r : ℝ)
    (hc : ∀ k : ℕ, |c k| * (2 * (k : ℝ) + 1) ≤ C * r ^ k)
    (k : ℕ) (x : ℝ) (hx : |x| ≤ 1) :
    ‖c k * (T ℝ (2 * (k : ℤ) + 1)).eval x‖ ≤ C * r ^ k * |x| := by
  rw [Real.norm_eq_abs, abs_mul]
  calc
    |c k| * |(T ℝ (2 * (k : ℤ) + 1)).eval x| ≤
        |c k| * ((2 * (k : ℝ) + 1) * |x|) :=
      mul_le_mul_of_nonneg_left (abs_odd_chebyshev_le k x hx) (abs_nonneg _)
    _ ≤ C * r ^ k * |x| := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (hc k) (abs_nonneg _)

/-- The expansion is absolutely convergent throughout `[-1,1]`. -/
theorem summable_series (c : ℕ → ℝ) (C r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hc : ∀ k : ℕ, |c k| * (2 * (k : ℝ) + 1) ≤ C * r ^ k)
    (x : ℝ) (hx : |x| ≤ 1) :
    Summable (fun k : ℕ => c k * (T ℝ (2 * (k : ℤ) + 1)).eval x) := by
  exact ((summable_geometric_of_lt_one hr0 hr1).mul_left C |>.mul_right |x|).of_norm_bounded
    (fun k => term_bound c C r hc k x hx)

/-- Closed form of the geometric majorant after dropping `N` terms. -/
theorem hasSum_tail_majorant (C r x : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (N : ℕ) :
    HasSum (fun k : ℕ => C * r ^ (k + N) * |x|)
      (C * r ^ N / (1 - r) * |x|) := by
  convert! (hasSum_geometric_of_lt_one hr0 hr1).mul_left (C * r ^ N * |x|) using 1
  · ext k
    rw [pow_add]
    ring
  · simp only [div_eq_mul_inv]
    ring

/-- The finite polynomial has a geometrically small *relative* tail.
This statement includes `x=0` without dividing by the signal. -/
theorem relative_tail (c : ℕ → ℝ) (C r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hc : ∀ k : ℕ, |c k| * (2 * (k : ℝ) + 1) ≤ C * r ^ k)
    (N : ℕ) (x : ℝ) (hx : |x| ≤ 1) :
    |series c x - (truncation c N).eval x| ≤
      (C * r ^ N / (1 - r)) * |x| := by
  have hs := summable_series c C r hr0 hr1 hc x hx
  have he : series c x - (truncation c N).eval x =
      ∑' k : ℕ, c (k + N) * (T ℝ (2 * ((k + N : ℕ) : ℤ) + 1)).eval x := by
    rw [series, truncation_eval]
    exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using (hs.sum_add_tsum_nat_add N).symm)
  rw [he, ← Real.norm_eq_abs]
  exact tsum_of_norm_bounded (hasSum_tail_majorant C r x hr0 hr1 N)
    (fun k => term_bound c C r hc (k + N) x hx)

/-- Retaining slack in the target bound makes the explicit truncation bounded by one. -/
theorem truncation_bounded (c : ℕ → ℝ) (C r δ : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hc : ∀ k : ℕ, |c k| * (2 * (k : ℝ) + 1) ≤ C * r ^ k)
    (N : ℕ) (hN : C * r ^ N / (1 - r) ≤ δ)
    (hf : ∀ x : ℝ, |x| ≤ 1 → |series c x| ≤ 1 - δ)
    (x : ℝ) (hx : |x| ≤ 1) : |(truncation c N).eval x| ≤ 1 := by
  have hC : 0 ≤ C := by
    have h := hc 0
    simp only [Nat.cast_zero, mul_zero, zero_add, mul_one, pow_zero] at h
    exact (abs_nonneg _).trans h
  have ht := relative_tail c C r hr0 hr1 hc N x hx
  have htail0 : 0 ≤ C * r ^ N / (1 - r) := by positivity
  calc
    |(truncation c N).eval x| ≤ |series c x| +
        |series c x - (truncation c N).eval x| := by
      have h := abs_sub_le ((truncation c N).eval x) (series c x) 0
      simpa only [sub_zero, abs_sub_comm ((truncation c N).eval x), add_comm] using h
    _ ≤ (1 - δ) + δ := by
      gcongr
      · exact hf x hx
      · exact ht.trans ((mul_le_of_le_one_right htail0 hx).trans hN)
    _ = 1 := by ring


/-- Explicit integer cutoff for an exponentially decreasing relative tail. -/
def cutoff (A γ δ : ℝ) : ℕ := ⌈Real.log (A / δ) / γ⌉₊

/-- The scheduled tail is at most `δ`; the cutoff grows only logarithmically in `1/δ`. -/
theorem cutoff_tail (A γ δ : ℝ) (hA : 0 < A) (hγ : 0 < γ) (hδ : 0 < δ) :
    A * Real.exp (-γ) ^ cutoff A γ δ ≤ δ := by
  have hN : Real.log (A / δ) ≤ (cutoff A γ δ : ℝ) * γ := by
    exact (div_le_iff₀ hγ).mp (Nat.le_ceil (Real.log (A / δ) / γ))
  have hpow : Real.exp (-γ) ^ cutoff A γ δ =
      Real.exp (-(cutoff A γ δ : ℝ) * γ) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have he : Real.exp (-(cutoff A γ δ : ℝ) * γ) ≤ δ / A := by
    calc
      Real.exp (-(cutoff A γ δ : ℝ) * γ) ≤ Real.exp (-Real.log (A / δ)) :=
        Real.exp_le_exp.mpr (by linarith)
      _ = δ / A := by rw [Real.exp_neg, Real.exp_log (div_pos hA hδ), inv_div]
  rw [hpow]
  calc
    A * Real.exp (-(cutoff A γ δ : ℝ) * γ) ≤ A * (δ / A) :=
      mul_le_mul_of_nonneg_left he hA.le
    _ = δ := by field_simp

/-- An explicit logarithmic upper bound on the integer degree schedule. -/
theorem cutoff_lt (A γ δ : ℝ) (hγ : 0 < γ) (hδ : 0 < δ) (hδA : δ ≤ A) :
    (cutoff A γ δ : ℝ) < Real.log (A / δ) / γ + 1 := by
  apply Nat.ceil_lt_add_one
  exact div_nonneg (Real.log_nonneg ((one_le_div hδ).mpr hδA)) hγ.le

/-- An explicit polynomial with logarithmic degree achieves the relative tail bound. -/
theorem scheduled_relative_tail (c : ℕ → ℝ) (C γ δ : ℝ)
    (hC : 0 < C) (hγ : 0 < γ) (hδ : 0 < δ)
    (hc : ∀ k : ℕ, |c k| * (2 * (k : ℝ) + 1) ≤ C * Real.exp (-γ) ^ k)
    (x : ℝ) (hx : |x| ≤ 1) :
    |series c x - (truncation c (cutoff (C / (1 - Real.exp (-γ))) γ δ)).eval x| ≤
      δ * |x| := by
  have hr0 : 0 ≤ Real.exp (-γ) := (Real.exp_pos _).le
  have hr1 : Real.exp (-γ) < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hγ)
  have hA : 0 < C / (1 - Real.exp (-γ)) := div_pos hC (sub_pos.mpr hr1)
  have he := cutoff_tail (C / (1 - Real.exp (-γ))) γ δ hA hγ hδ
  have htail := relative_tail c C (Real.exp (-γ)) hr0 hr1 hc
    (cutoff (C / (1 - Real.exp (-γ))) γ δ) x hx
  apply htail.trans
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg x)
  calc
    C * Real.exp (-γ) ^ cutoff (C / (1 - Real.exp (-γ))) γ δ /
        (1 - Real.exp (-γ)) =
        (C / (1 - Real.exp (-γ))) *
          Real.exp (-γ) ^ cutoff (C / (1 - Real.exp (-γ))) γ δ := by ring
    _ ≤ δ := he


/-- Ordinary exponential coefficient decay implies the weighted decay needed
for relative error, losing only a factor two in the exponential rate. -/
theorem weighted_exponential_decay (c : ℕ → ℝ) (C γ : ℝ)
    (hC : 0 ≤ C) (hγ : 0 < γ)
    (hc : ∀ k : ℕ, |c k| ≤ C * Real.exp (-2 * γ * k)) (k : ℕ) :
    |c k| * (2 * (k : ℝ) + 1) ≤
      (C * (1 + 2 / γ)) * Real.exp (-γ) ^ k := by
  have hb : (γ * k) * Real.exp (-(γ * k)) ≤ 1 := by
    exact (Real.mul_exp_neg_le_exp_neg_one (γ * k)).trans
      (Real.exp_le_one_iff.mpr (by norm_num))
  have hz : Real.exp (-(γ * k)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hγ.le (Nat.cast_nonneg k)))
  have hdiv : γ * (2 / γ) = 2 := by field_simp
  have hw : (2 * (k : ℝ) + 1) * Real.exp (-(γ * k)) ≤ 1 + 2 / γ := by
    apply (mul_le_mul_iff_right₀ hγ).mp
    nlinarith
  have he : Real.exp (-2 * γ * k) =
      Real.exp (-(γ * k)) * Real.exp (-(γ * k)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hp : Real.exp (-γ) ^ k = Real.exp (-(γ * k)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  calc
    |c k| * (2 * (k : ℝ) + 1) ≤
        (C * Real.exp (-2 * γ * k)) * (2 * (k : ℝ) + 1) :=
      mul_le_mul_of_nonneg_right (hc k) (by positivity)
    _ = (C * Real.exp (-(γ * k))) *
        ((2 * (k : ℝ) + 1) * Real.exp (-(γ * k))) := by rw [he]; ring
    _ ≤ (C * Real.exp (-(γ * k))) * (1 + 2 / γ) :=
      mul_le_mul_of_nonneg_left hw (mul_nonneg hC (Real.exp_pos _).le)
    _ = (C * (1 + 2 / γ)) * Real.exp (-γ) ^ k := by rw [hp]; ring


/-- The degree itself obeys the explicit reciprocal-rate/logarithmic-precision bound. -/
theorem scheduled_degree_lt (c : ℕ → ℝ) (A γ δ : ℝ)
    (hγ : 0 < γ) (hδ : 0 < δ) (hδA : δ ≤ A) :
    ((truncation c (cutoff A γ δ)).natDegree : ℝ) <
      2 * (Real.log (A / δ) / γ + 1) := by
  have hd : ((truncation c (cutoff A γ δ)).natDegree : ℝ) ≤
      2 * (cutoff A γ δ : ℝ) := by
    exact_mod_cast truncation_degree c (cutoff A γ δ)
  have hn := cutoff_lt A γ δ hγ hδ hδA
  linarith

/-- Relative approximation to a target linear gain transfers to the actual finite polynomial. -/
theorem scheduled_gain_error (c : ℕ → ℝ) (C γ δ g η x : ℝ)
    (hC : 0 < C) (hγ : 0 < γ) (hδ : 0 < δ)
    (hc : ∀ k : ℕ, |c k| * (2 * (k : ℝ) + 1) ≤ C * Real.exp (-γ) ^ k)
    (hx : |x| ≤ 1) (hf : |series c x - g * x| ≤ η * |x|) :
    |(truncation c (cutoff (C / (1 - Real.exp (-γ))) γ δ)).eval x - g * x| ≤
      (δ + η) * |x| := by
  have ht := scheduled_relative_tail c C γ δ hC hγ hδ hc x hx
  calc
    |(truncation c (cutoff (C / (1 - Real.exp (-γ))) γ δ)).eval x - g * x| ≤
        |(truncation c (cutoff (C / (1 - Real.exp (-γ))) γ δ)).eval x - series c x| +
          |series c x - g * x| := abs_sub_le _ _ _
    _ ≤ δ * |x| + η * |x| := by
      rw [abs_sub_comm ((truncation c _).eval x)]
      exact add_le_add ht hf
    _ = (δ + η) * |x| := by ring

/-- Global slack in the series is inherited by the scheduled polynomial. -/
theorem scheduled_bounded (c : ℕ → ℝ) (C γ δ : ℝ)
    (hC : 0 < C) (hγ : 0 < γ) (hδ : 0 < δ)
    (hc : ∀ k : ℕ, |c k| * (2 * (k : ℝ) + 1) ≤ C * Real.exp (-γ) ^ k)
    (hf : ∀ x : ℝ, |x| ≤ 1 → |series c x| ≤ 1 - δ)
    (x : ℝ) (hx : |x| ≤ 1) :
    |(truncation c (cutoff (C / (1 - Real.exp (-γ))) γ δ)).eval x| ≤ 1 := by
  have ht := scheduled_relative_tail c C γ δ hC hγ hδ hc x hx
  calc
    |(truncation c (cutoff (C / (1 - Real.exp (-γ))) γ δ)).eval x| ≤
        |series c x| +
        |series c x - (truncation c (cutoff (C / (1 - Real.exp (-γ))) γ δ)).eval x| := by
      have h := abs_sub_le
        ((truncation c (cutoff (C / (1 - Real.exp (-γ))) γ δ)).eval x) (series c x) 0
      simpa only [sub_zero,
        abs_sub_comm ((truncation c (cutoff (C / (1 - Real.exp (-γ))) γ δ)).eval x),
        add_comm] using h
    _ ≤ (1 - δ) + δ := add_le_add (hf x hx)
      (ht.trans (mul_le_of_le_one_right hδ.le hx))
    _ = 1 := by ring

end
end SparseHamiltonian.OddChebyshevApproximation
