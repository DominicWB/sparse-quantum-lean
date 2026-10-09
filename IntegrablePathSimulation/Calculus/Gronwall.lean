import Mathlib.Analysis.SpecialFunctions.Exponential
import IntegrablePathSimulation.Calculus.Product

set_option autoImplicit false

/-!
# Grönwall's inequality in integral form with an integrable coefficient

Mathlib's Grönwall inequalities (`Mathlib.Analysis.ODE.Gronwall`) bound functions through
pointwise one-sided derivatives with a constant coefficient. Propagators of merely integrable
paths (the paragraph after Theorem `hs:thm:time` of the manuscript, lines 1618-1632) need the
integral form with an integrable coefficient `k ≥ 0`:

* `le_mul_exp_of_le_add_integral`: if `φ` is continuous on `[a, b]` and
  `φ s ≤ c + ∫_a^s k φ` there, then `φ s ≤ c exp (∫_a^s k)`;
* `eq_zero_of_le_integral`: in particular a nonnegative continuous `φ` with
  `φ s ≤ ∫_a^s k φ` vanishes on `[a, b]`;
* `eq_zero_of_norm_le_integral`: the same for `‖D‖` with `D` continuous and vector-valued,
  the form used for uniqueness of propagators.
-/

namespace IntegrablePathSimulation.Calculus

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

/-- The partial sums `∑_{m < n} x^m / m!` of the exponential series converge to `exp x`. -/
theorem tendsto_sum_pow_div_factorial (x : ℝ) :
    Tendsto (fun n => ∑ m ∈ Finset.range n, x ^ m / (Nat.factorial m : ℝ)) atTop
      (𝓝 (Real.exp x)) := by
  rw [Real.exp_eq_exp_ℝ]
  exact (NormedSpace.expSeries_div_hasSum_exp x).tendsto_sum_nat

/-- **Grönwall's inequality, integral form with an integrable coefficient.** If `k ≥ 0` almost
everywhere on `[a, b]` is interval integrable, `φ` is continuous on `[a, b]` and
`φ s ≤ c + ∫_a^s k φ` for `s ∈ [a, b]`, then `φ s ≤ c exp (∫_a^s k)` on `[a, b]`. -/
theorem le_mul_exp_of_le_add_integral {φ k : ℝ → ℝ} {a b c : ℝ} (hab : a ≤ b)
    (hφ : ContinuousOn φ (Icc a b)) (hk : IntervalIntegrable k volume a b)
    (hk0 : ∀ᵐ u, u ∈ Icc a b → 0 ≤ k u)
    (hle : ∀ s ∈ Icc a b, φ s ≤ c + ∫ u in a..s, k u * φ u) :
    ∀ s ∈ Icc a b, φ s ≤ c * Real.exp (∫ u in a..s, k u) := by
  set K : ℝ → ℝ := fun s => ∫ v in a..s, k v with hKdef
  have hK : ∀ s ∈ Icc a b, K s = K a + ∫ u in a..s, k u := fun s _ => by simp [K]
  have hKc : ContinuousOn K (Icc a b) := continuousOn_of_eq_add_integral hab hk hK
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hφ
  have hkc : ∀ {ψ : ℝ → ℝ}, ContinuousOn ψ (Icc a b) → ∀ s ∈ Icc a b,
      IntervalIntegrable (fun u => k u * ψ u) volume a s := fun hψ s hs =>
    (hk.mul_continuousOn (by rwa [uIcc_of_le hab])).mono_set
      (by rw [uIcc_of_le hab, uIcc_of_le hs.1]; exact Icc_subset_Icc_right hs.2)
  have hTc : ∀ j : ℕ, ContinuousOn (fun u => K u ^ j / (Nat.factorial j : ℝ)) (Icc a b) :=
    fun j => (hKc.pow j).div_const _
  have hterm : ∀ j : ℕ, ∀ s ∈ Icc a b, ∫ u in a..s, k u * (K u ^ j / (Nat.factorial j : ℝ)) =
      K s ^ (j + 1) / (Nat.factorial (j + 1) : ℝ) := by
    intro j s hs
    have h : ∫ u in a..s, k u * K u ^ j = K s ^ (j + 1) / (j + 1) :=
      integral_mul_primitive_pow hab hk j s hs
    simp_rw [← mul_div_assoc]
    rw [intervalIntegral.integral_div, h, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ,
      div_div]
  set S : ℕ → ℝ → ℝ := fun n u => ∑ j ∈ Finset.range n, K u ^ j / (Nat.factorial j : ℝ)
    with hSdef
  have hSc : ∀ n, ContinuousOn (S n) (Icc a b) := fun n =>
    continuousOn_finsetSum _ fun j _ => hTc j
  have hS : ∀ n, ∀ s ∈ Icc a b, ∫ u in a..s, k u * S n u =
      ∑ j ∈ Finset.range n, K s ^ (j + 1) / (Nat.factorial (j + 1) : ℝ) := by
    intro n s hs
    simp only [S, Finset.mul_sum]
    rw [intervalIntegral.integral_finsetSum fun j _ => hkc (hTc j) s hs]
    exact Finset.sum_congr rfl fun j _ => hterm j s hs
  have hiter : ∀ n : ℕ, ∀ s ∈ Icc a b,
      φ s ≤ c * S n s + B * (K s ^ n / (Nat.factorial n : ℝ)) := by
    intro n
    induction n with
    | zero =>
      intro s hs
      simp only [S, Finset.range_zero, Finset.sum_empty, mul_zero, zero_add, pow_zero,
        Nat.factorial_zero, Nat.cast_one, div_one, mul_one]
      exact (le_abs_self _).trans (hB s hs)
    | succ n ih =>
      intro s hs
      have hPc : ContinuousOn (fun u => c * S n u + B * (K u ^ n / (Nat.factorial n : ℝ)))
          (Icc a b) := (continuousOn_const.mul (hSc n)).add (continuousOn_const.mul (hTc n))
      have hmono : ∫ u in a..s, k u * φ u ≤
          ∫ u in a..s, k u * (c * S n u + B * (K u ^ n / (Nat.factorial n : ℝ))) := by
        refine intervalIntegral.integral_mono_ae_restrict hs.1 (hkc hφ s hs) (hkc hPc s hs) ?_
        filter_upwards [ae_restrict_of_ae hk0, ae_restrict_mem measurableSet_Icc] with u h1 h2
        have hu : u ∈ Icc a b := ⟨h2.1, h2.2.trans hs.2⟩
        exact mul_le_mul_of_nonneg_left (ih u hu) (h1 hu)
      have hval : ∫ u in a..s, k u * (c * S n u + B * (K u ^ n / (Nat.factorial n : ℝ))) =
          c * ∑ j ∈ Finset.range n, K s ^ (j + 1) / (Nat.factorial (j + 1) : ℝ) +
            B * (K s ^ (n + 1) / (Nat.factorial (n + 1) : ℝ)) := by
        rw [intervalIntegral.integral_congr (g := fun u => c * (k u * S n u) +
            B * (k u * (K u ^ n / (Nat.factorial n : ℝ)))) fun u _ => by ring,
          intervalIntegral.integral_add ((hkc (hSc n) s hs).const_mul c)
            ((hkc (hTc n) s hs).const_mul B),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
          hS n s hs, hterm n s hs]
      have hsplit : S (n + 1) s =
          ∑ j ∈ Finset.range n, K s ^ (j + 1) / (Nat.factorial (j + 1) : ℝ) + 1 := by
        simp only [S]
        rw [Finset.sum_range_succ']
        simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]
      rw [hsplit]
      have h0 := hle s hs
      nlinarith [hmono, hval, h0]
  intro s hs
  have hsum : Tendsto (fun n => S n s) atTop (𝓝 (Real.exp (K s))) :=
    tendsto_sum_pow_div_factorial (K s)
  have hlim : Tendsto (fun n => c * S n s + B * (K s ^ n / (Nat.factorial n : ℝ))) atTop
      (𝓝 (c * Real.exp (K s) + B * 0)) :=
    (hsum.const_mul c).add ((Real.summable_pow_div_factorial (K s)).tendsto_atTop_zero.const_mul B)
  rw [mul_zero, add_zero] at hlim
  exact ge_of_tendsto' hlim fun n => hiter n s hs

/-- A nonnegative continuous `φ` with `φ s ≤ ∫_a^s k φ` on `[a, b]`, for an interval-integrable
`k ≥ 0`, vanishes on `[a, b]`. -/
theorem eq_zero_of_le_integral {φ k : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hφ : ContinuousOn φ (Icc a b)) (hφ0 : ∀ s ∈ Icc a b, 0 ≤ φ s)
    (hk : IntervalIntegrable k volume a b) (hk0 : ∀ᵐ u, u ∈ Icc a b → 0 ≤ k u)
    (hle : ∀ s ∈ Icc a b, φ s ≤ ∫ u in a..s, k u * φ u) :
    ∀ s ∈ Icc a b, φ s = 0 := by
  intro s hs
  have h := le_mul_exp_of_le_add_integral (c := 0) hab hφ hk hk0
    (fun s hs => by rw [zero_add]; exact hle s hs) s hs
  rw [zero_mul] at h
  exact le_antisymm h (hφ0 s hs)

/-- A continuous vector-valued `D` with `‖D s‖ ≤ ∫_a^s k ‖D‖` on `[a, b]`, for an
interval-integrable `k ≥ 0`, vanishes on `[a, b]`. -/
theorem eq_zero_of_norm_le_integral {E : Type*} [NormedAddCommGroup E] {D : ℝ → E}
    {k : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hD : ContinuousOn D (Icc a b))
    (hk : IntervalIntegrable k volume a b) (hk0 : ∀ᵐ u, u ∈ Icc a b → 0 ≤ k u)
    (hle : ∀ s ∈ Icc a b, ‖D s‖ ≤ ∫ u in a..s, k u * ‖D u‖) :
    ∀ s ∈ Icc a b, D s = 0 := by
  intro s hs
  exact norm_eq_zero.mp
    (eq_zero_of_le_integral hab hD.norm (fun s _ => norm_nonneg _) hk hk0 hle s hs)

end

end IntegrablePathSimulation.Calculus
