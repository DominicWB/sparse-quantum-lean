import OptimalPrecision.Taylor.Estimates
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Exponential tails and Taylor coefficients of `V · e^{Y}`

* `norm_exp_sub_sum_le`: in a complete normed `ℂ`-algebra,
  `‖e^Y - ∑_{m ≤ k} Y^m/m!‖ ≤ ‖Y‖^{k+1} e^{‖Y‖}`.
* `coeff_smul_exp`: if `Y(0) = 0`, then the `k`-th Taylor coefficient of
  `w ↦ V(w) e^{Y(w)}` only sees the terms `m ≤ k` of the exponential series,
  `[w^k] V e^{Y} = ∑_{m ≤ k} [w^k] V Y^m / m!`.

These are the analytic inputs for the word expansion of the transfer in the proof
of `opt:lem:tail` (`opt:eq:matching-jets`).
-/

namespace OptimalPrecision

noncomputable section

open Nat Finset Filter Metric
open scoped Topology

section ExpTail

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- `‖e^Y - ∑_{m ≤ k} Y^m/m!‖ ≤ ‖Y‖^{k+1} e^{‖Y‖}`. -/
theorem norm_exp_sub_sum_le (Y : A) (k : ℕ) :
    ‖NormedSpace.exp Y - ∑ m ∈ range (k + 1), ((m ! : ℂ)⁻¹) • Y ^ m‖ ≤
      ‖Y‖ ^ (k + 1) * Real.exp ‖Y‖ := by
  have h := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) Y
  have h2 := (hasSum_nat_add_iff' (k + 1)).mpr h
  have hg : HasSum (fun n : ℕ => ‖Y‖ ^ (k + 1) * (‖Y‖ ^ n / n !))
      (‖Y‖ ^ (k + 1) * Real.exp ‖Y‖) := by
    rw [Real.exp_eq_exp_ℝ]
    exact (NormedSpace.expSeries_div_hasSum_exp ‖Y‖).mul_left _
  refine h2.norm_le_of_bounded hg fun n => ?_
  rw [norm_smul, norm_inv, Complex.norm_natCast]
  have hpow : ‖Y ^ (n + (k + 1))‖ ≤ ‖Y‖ ^ (n + (k + 1)) := norm_pow_le' Y (by omega)
  have hfac : (n ! : ℝ) ≤ ((n + (k + 1)) ! : ℝ) := by exact_mod_cast Nat.factorial_le (by omega)
  have hn : (0 : ℝ) < n ! := by exact_mod_cast Nat.factorial_pos n
  calc ((n + (k + 1)) ! : ℝ)⁻¹ * ‖Y ^ (n + (k + 1))‖ ≤ (n ! : ℝ)⁻¹ * ‖Y‖ ^ (n + (k + 1)) :=
        mul_le_mul (inv_anti₀ hn hfac) hpow (norm_nonneg _) (by positivity)
    _ = ‖Y‖ ^ (k + 1) * (‖Y‖ ^ n / n !) := by rw [pow_add]; ring

/-- The sharper tail `‖e^Y - ∑_{m ≤ k} Y^m/m!‖ ≤ (‖Y‖^{k+1}/(k+1)!) e^{‖Y‖}`. -/
theorem norm_exp_sub_sum_le' (Y : A) (k : ℕ) :
    ‖NormedSpace.exp Y - ∑ m ∈ range (k + 1), ((m ! : ℂ)⁻¹) • Y ^ m‖ ≤
      ‖Y‖ ^ (k + 1) / ((k + 1) ! : ℝ) * Real.exp ‖Y‖ := by
  have h := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) Y
  have h2 := (hasSum_nat_add_iff' (k + 1)).mpr h
  have hg : HasSum (fun n : ℕ => ‖Y‖ ^ (k + 1) / ((k + 1) ! : ℝ) * (‖Y‖ ^ n / n !))
      (‖Y‖ ^ (k + 1) / ((k + 1) ! : ℝ) * Real.exp ‖Y‖) := by
    rw [Real.exp_eq_exp_ℝ]
    exact (NormedSpace.expSeries_div_hasSum_exp ‖Y‖).mul_left _
  refine h2.norm_le_of_bounded hg fun n => ?_
  rw [norm_smul, norm_inv, Complex.norm_natCast]
  have hpow : ‖Y ^ (n + (k + 1))‖ ≤ ‖Y‖ ^ (n + (k + 1)) := norm_pow_le' Y (by omega)
  have hfac : ((k + 1) ! : ℝ) * (n ! : ℝ) ≤ ((n + (k + 1)) ! : ℝ) := by
    have := Nat.le_of_dvd (Nat.factorial_pos _)
      (Nat.factorial_mul_factorial_dvd_factorial_add (k + 1) n)
    rw [show k + 1 + n = n + (k + 1) by ring] at this
    exact_mod_cast this
  have hn : (0 : ℝ) < n ! := by exact_mod_cast Nat.factorial_pos n
  have hk : (0 : ℝ) < (k + 1) ! := by exact_mod_cast Nat.factorial_pos (k + 1)
  calc ((n + (k + 1)) ! : ℝ)⁻¹ * ‖Y ^ (n + (k + 1))‖ ≤
      (((k + 1) ! : ℝ) * (n ! : ℝ))⁻¹ * ‖Y‖ ^ (n + (k + 1)) :=
        mul_le_mul (inv_anti₀ (by positivity) hfac) hpow (norm_nonneg _) (by positivity)
    _ = ‖Y‖ ^ (k + 1) / ((k + 1) ! : ℝ) * (‖Y‖ ^ n / n !) := by
        rw [pow_add, mul_inv]; field_simp

end ExpTail

section Local

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A function differentiable at the origin and vanishing there is `O(‖w‖)` on a ball. -/
theorem exists_norm_le_mul_of_differentiableAt {f : ℂ → E} (hf : DifferentiableAt ℂ f 0)
    (h0 : f 0 = 0) : ∃ r > 0, ∃ K, ∀ w : ℂ, ‖w‖ < r → ‖f w‖ ≤ K * ‖w‖ := by
  have h := hf.hasDerivAt.isBigO_sub
  simp only [h0, sub_zero] at h
  obtain ⟨K, hK⟩ := h.bound
  rw [Metric.eventually_nhds_iff_ball] at hK
  obtain ⟨r, hr, hball⟩ := hK
  exact ⟨r, hr, K, fun w hw => hball w (by simpa using hw)⟩

omit [NormedSpace ℂ E] in
/-- A function continuous at the origin is bounded on a ball. -/
theorem exists_norm_le_of_continuousAt {f : ℂ → E} (hf : ContinuousAt f 0) :
    ∃ r > 0, ∃ B, ∀ w : ℂ, ‖w‖ < r → ‖f w‖ ≤ B := by
  have h := hf.norm.eventually (gt_mem_nhds (lt_add_one ‖f 0‖))
  rw [Metric.eventually_nhds_iff_ball] at h
  obtain ⟨r, hr, hball⟩ := h
  exact ⟨r, hr, ‖f 0‖ + 1, fun w hw => (hball w (by simpa using hw)).le⟩

end Local

section Coefficients

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- **Taylor coefficients of `V e^Y` with `Y(0) = 0`**: only the terms `m ≤ k` of the
exponential series contribute to `[w^k]`. -/
theorem coeff_smul_exp {V : ℂ → ℂ} {Y : ℂ → A} {r : ℝ} (hr : 0 < r)
    (hV : DifferentiableOn ℂ V (ball 0 r)) (hY : DifferentiableOn ℂ Y (ball 0 r))
    (hY0 : Y 0 = 0) (k : ℕ) :
    coeff (fun w => V w • NormedSpace.exp (Y w)) k =
      ∑ m ∈ range (k + 1), ((m ! : ℂ)⁻¹) • coeff (fun w => V w • Y w ^ m) k := by
  have hmem : ball (0 : ℂ) r ∈ 𝓝 (0 : ℂ) := ball_mem_nhds 0 hr
  have hVd : DifferentiableAt ℂ V 0 := hV.differentiableAt hmem
  have hYd : DifferentiableAt ℂ Y 0 := hY.differentiableAt hmem
  obtain ⟨r₁, hr₁, K, hK⟩ := exists_norm_le_mul_of_differentiableAt hYd hY0
  obtain ⟨r₂, hr₂, B, hB⟩ := exists_norm_le_of_continuousAt hVd.continuousAt
  set ρ := min r (min r₁ r₂) with hρ
  have hρ0 : 0 < ρ := lt_min hr (lt_min hr₁ hr₂)
  have hρr : ρ ≤ r := min_le_left _ _
  have hρr₁ : ρ ≤ r₁ := (min_le_right _ _).trans (min_le_left _ _)
  have hρr₂ : ρ ≤ r₂ := (min_le_right _ _).trans (min_le_right _ _)
  have hsub : ball (0 : ℂ) ρ ⊆ ball 0 r := ball_subset_ball hρr
  -- differentiability of the pieces
  have hexp : ∀ x : A, DifferentiableAt ℂ (NormedSpace.exp : A → A) x :=
    fun x => (NormedSpace.exp_analytic (𝕂 := ℂ) x).differentiableAt
  have hf : DifferentiableOn ℂ (fun w => V w • NormedSpace.exp (Y w)) (ball 0 r) :=
    fun w hw => ((hV w hw).differentiableAt (isOpen_ball.mem_nhds hw) |>.smul
      ((hexp (Y w)).comp w
        ((hY w hw).differentiableAt (isOpen_ball.mem_nhds hw)))).differentiableWithinAt
  have hterm : ∀ m : ℕ, DifferentiableOn ℂ (fun w => V w • Y w ^ m) (ball 0 r) :=
    fun m => hV.smul (hY.pow m)
  set g : ℂ → A := fun w => ∑ m ∈ range (k + 1), ((m ! : ℂ)⁻¹) • (V w • Y w ^ m) with hg
  have hgd : DifferentiableOn ℂ g (ball 0 r) :=
    DifferentiableOn.fun_sum fun m _ => (hterm m).fun_const_smul _
  have hdiff : DifferentiableOn ℂ (fun w => V w • NormedSpace.exp (Y w) - g w) (ball 0 ρ) :=
    (hf.sub hgd).mono hsub
  -- the remainder bound
  set K' := max K 0
  have hbound : ∀ w : ℂ, ‖w‖ < ρ → ‖V w • NormedSpace.exp (Y w) - g w‖ ≤
      (max B 0 * K' ^ (k + 1) * Real.exp (K' * ρ)) * ‖w‖ ^ (k + 1) := by
    intro w hw
    have hYw : ‖Y w‖ ≤ K' * ‖w‖ :=
      (hK w (lt_of_lt_of_le hw hρr₁)).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (norm_nonneg _))
    have hVw : ‖V w‖ ≤ max B 0 := (hB w (lt_of_lt_of_le hw hρr₂)).trans (le_max_left _ _)
    have heq : V w • NormedSpace.exp (Y w) - g w =
        V w • (NormedSpace.exp (Y w) - ∑ m ∈ range (k + 1), ((m ! : ℂ)⁻¹) • Y w ^ m) := by
      simp only [hg, smul_sub, Finset.smul_sum]
      congr 1
      exact Finset.sum_congr rfl fun m _ => smul_comm _ _ _
    rw [heq, norm_smul]
    have h1 := norm_exp_sub_sum_le (Y w) k
    have hK'0 : 0 ≤ K' := le_max_right _ _
    have h2 : ‖Y w‖ ^ (k + 1) * Real.exp ‖Y w‖ ≤ (K' * ‖w‖) ^ (k + 1) * Real.exp (K' * ρ) := by
      apply mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hYw _) _ (by positivity) (by positivity)
      apply Real.exp_le_exp.mpr
      exact hYw.trans (mul_le_mul_of_nonneg_left hw.le hK'0)
    calc ‖V w‖ * ‖NormedSpace.exp (Y w) - ∑ m ∈ range (k + 1), ((m ! : ℂ)⁻¹) • Y w ^ m‖ ≤
        max B 0 * ((K' * ‖w‖) ^ (k + 1) * Real.exp (K' * ρ)) :=
          mul_le_mul hVw (h1.trans h2) (norm_nonneg _) (le_max_right _ _)
      _ = (max B 0 * K' ^ (k + 1) * Real.exp (K' * ρ)) * ‖w‖ ^ (k + 1) := by ring
  have hz := coeff_eq_zero_of_norm_le_pow hρ0 hdiff hbound (le_refl k)
  -- linearity of the coefficient
  have hfa : AnalyticAt ℂ (fun w => V w • NormedSpace.exp (Y w)) 0 := hf.analyticAt hmem
  have hga : AnalyticAt ℂ g 0 := hgd.analyticAt hmem
  rw [coeff_sub hfa hga, sub_eq_zero] at hz
  rw [hz, hg, coeff_sum _ fun m _ => ((hterm m).analyticAt hmem).fun_const_smul]
  exact Finset.sum_congr rfl fun m _ => coeff_const_smul_field _ _ k

end Coefficients

end

end OptimalPrecision
