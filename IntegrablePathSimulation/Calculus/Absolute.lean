import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

set_option autoImplicit false

/-!
# Absolutely continuous Banach-valued functions and integral equations

Propagators of merely integrable paths (the paragraph "Regularity and coherent parameters"
after Theorem `hs:thm:time` of the manuscript, lines 1618-1632) are absolutely continuous
rather than differentiable. Mathlib proves the fundamental theorem of calculus for absolutely
continuous real functions and the Lebesgue differentiation theorem for Banach-valued
primitives; this module supplies the Banach-valued facts used for operator-valued
propagators.

* `absolutelyContinuousOnInterval_of_dist_le`: increments dominated by a constant times those
  of an absolutely continuous real function give an absolutely continuous function.
* `absolutelyContinuousOnInterval_primitive`: the primitive `x ↦ ∫_c^x f` of an
  interval-integrable Banach-valued `f` is absolutely continuous.
* `eq_add_integral_of_ae_hasDerivAt`: an absolutely continuous Banach-valued `F` with
  `F' = f` almost everywhere and `f` interval integrable satisfies `F s = F a + ∫_a^s f`.
* `absolutelyContinuousOnInterval_of_eq_add_integral`, `continuousOn_of_eq_add_integral`,
  `ae_hasDerivAt_of_eq_add_integral`: a solution of `F s = F a + ∫_a^s f` on `[a, b]` is
  absolutely continuous, continuous, and has derivative `f` almost everywhere on `[a, b]`.
-/

namespace IntegrablePathSimulation.Calculus

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

/-- **Domination.** A function whose increments on `[a, b]` are at most `C` times those of an
absolutely continuous real function is absolutely continuous on `[a, b]`. -/
theorem absolutelyContinuousOnInterval_of_dist_le {X : Type*} [PseudoMetricSpace X]
    {f : ℝ → X} {g : ℝ → ℝ} {a b C : ℝ} (hg : AbsolutelyContinuousOnInterval g a b)
    (hfg : ∀ x ∈ uIcc a b, ∀ y ∈ uIcc a b, dist (f x) (f y) ≤ C * dist (g x) (g y)) :
    AbsolutelyContinuousOnInterval f a b := by
  unfold AbsolutelyContinuousOnInterval at hg ⊢
  apply squeeze_zero' (Eventually.of_forall fun _ => Finset.sum_nonneg fun _ _ => dist_nonneg)
    ?_ (by simpa using hg.const_mul C)
  rw [eventually_inf_principal]
  filter_upwards with E hE
  simp only [AbsolutelyContinuousOnInterval.disjWithin, mem_setOf_eq] at hE
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i hi => hfg _ (hE.1 i hi).1 _ (hE.1 i hi).2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Increments of the primitive `x ↦ ∫_c^x f` are bounded by the increments of the primitive
of `‖f‖`, for points of `[a, b]` and an interval-integrable `f` on `[a, b]`. -/
theorem dist_integral_le_dist_integral_norm {f : ℝ → E} {a b c x y : ℝ}
    (hf : IntervalIntegrable f volume a b) (hc : c ∈ uIcc a b) (hx : x ∈ uIcc a b)
    (hy : y ∈ uIcc a b) :
    dist (∫ v in c..x, f v) (∫ v in c..y, f v) ≤
      dist (∫ v in c..x, ‖f v‖) (∫ v in c..y, ‖f v‖) := by
  have hcx := hf.mono_set (uIcc_subset_uIcc hc hx)
  have hcy := hf.mono_set (uIcc_subset_uIcc hc hy)
  rw [dist_eq_norm, Real.dist_eq, intervalIntegral.integral_interval_sub_left hcx hcy,
    intervalIntegral.integral_interval_sub_left hcx.norm hcy.norm]
  exact intervalIntegral.norm_integral_le_abs_integral_norm

/-- The primitive `x ↦ ∫_c^x f` of an interval-integrable Banach-valued function is absolutely
continuous on `[a, b]`, for every base point `c ∈ [a, b]`. -/
theorem absolutelyContinuousOnInterval_primitive {f : ℝ → E} {a b c : ℝ}
    (hf : IntervalIntegrable f volume a b) (hc : c ∈ uIcc a b) :
    AbsolutelyContinuousOnInterval (fun x => ∫ v in c..x, f v) a b := by
  refine absolutelyContinuousOnInterval_of_dist_le (C := 1)
    (g := fun x => ∫ v in c..x, ‖f v‖)
    (hf.norm.absolutelyContinuousOnInterval_intervalIntegral hc) fun x hx y hy => ?_
  rw [one_mul]
  exact dist_integral_le_dist_integral_norm hf hc hx hy

/-- **Fundamental theorem of calculus for absolutely continuous Banach-valued functions.**
If `F` is absolutely continuous on `[a, b]`, has derivative `f u` at almost every
`u ∈ [a, b]`, and `f` is interval integrable, then `F s = F a + ∫_a^s f` on `[a, b]`. -/
theorem eq_add_integral_of_ae_hasDerivAt [CompleteSpace E] {F f : ℝ → E} {a b : ℝ}
    (hF : AbsolutelyContinuousOnInterval F a b) (hf : IntervalIntegrable f volume a b)
    (hderiv : ∀ᵐ u, u ∈ uIcc a b → HasDerivAt F (f u) u) :
    ∀ s ∈ uIcc a b, F s = F a + ∫ u in a..s, f u := by
  intro s hs
  have hΨ := hF.sub (absolutelyContinuousOnInterval_primitive hf (left_mem_uIcc (a := a) (b := b)))
  obtain ⟨K, hK⟩ := hΨ.const_of_ae_hasDerivAt_zero (by
    filter_upwards [hderiv, hf.ae_hasDerivAt_integral] with x h1 h2 hx
    have h := (h1 hx).sub (h2 hx a left_mem_uIcc)
    rw [sub_self] at h
    exact h)
  have ha := hK a left_mem_uIcc
  have hs' := hK s hs
  simp only [Pi.sub_apply, intervalIntegral.integral_same, sub_zero] at ha hs'
  rw [ha, ← hs', sub_add_cancel]

/-- A solution of `F s = F a + ∫_a^s f` on `[a, b]` is absolutely continuous on `[a, b]`. -/
theorem absolutelyContinuousOnInterval_of_eq_add_integral {F f : ℝ → E} {a b : ℝ}
    (hab : a ≤ b) (hf : IntervalIntegrable f volume a b)
    (hF : ∀ s ∈ Icc a b, F s = F a + ∫ u in a..s, f u) :
    AbsolutelyContinuousOnInterval F a b := by
  refine absolutelyContinuousOnInterval_of_dist_le (C := 1)
    (g := fun x => ∫ v in a..x, ‖f v‖)
    (hf.norm.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc)
    fun x hx y hy => ?_
  have hx' : x ∈ Icc a b := by rwa [uIcc_of_le hab] at hx
  have hy' : y ∈ Icc a b := by rwa [uIcc_of_le hab] at hy
  rw [hF x hx', hF y hy', dist_add_left, one_mul]
  exact dist_integral_le_dist_integral_norm hf left_mem_uIcc hx hy

/-- A solution of `F s = F a + ∫_a^s f` on `[a, b]` is continuous on `[a, b]`. -/
theorem continuousOn_of_eq_add_integral {F f : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hf : IntervalIntegrable f volume a b)
    (hF : ∀ s ∈ Icc a b, F s = F a + ∫ u in a..s, f u) :
    ContinuousOn F (Icc a b) := by
  simpa [uIcc_of_le hab] using
    (absolutelyContinuousOnInterval_of_eq_add_integral hab hf hF).continuousOn

/-- A solution of `F s = F a + ∫_a^s f` on `[a, b]` has derivative `f u` at almost every
`u ∈ [a, b]` (Lebesgue differentiation). -/
theorem ae_hasDerivAt_of_eq_add_integral [CompleteSpace E] {F f : ℝ → E} {a b : ℝ}
    (hab : a ≤ b) (hf : IntervalIntegrable f volume a b)
    (hF : ∀ s ∈ Icc a b, F s = F a + ∫ u in a..s, f u) :
    ∀ᵐ u, u ∈ Icc a b → HasDerivAt F (f u) u := by
  have h₁ : ∀ᵐ x : ℝ, x ≠ a := by simp [ae_iff, measure_singleton]
  have h₂ : ∀ᵐ x : ℝ, x ≠ b := by simp [ae_iff, measure_singleton]
  filter_upwards [hf.ae_hasDerivAt_integral, h₁, h₂] with x hx hxa hxb hxI
  have hxI' : x ∈ uIcc a b := by rwa [uIcc_of_le hab]
  have hIoo : x ∈ Ioo a b := ⟨lt_of_le_of_ne hxI.1 (Ne.symm hxa), lt_of_le_of_ne hxI.2 hxb⟩
  have hev : F =ᶠ[𝓝 x] fun y => F a + ∫ u in a..y, f u := by
    filter_upwards [Ioo_mem_nhds hIoo.1 hIoo.2] with y hy using hF y (Ioo_subset_Icc_self hy)
  exact ((hx hxI' a left_mem_uIcc).const_add (F a)).congr_of_eventuallyEq hev

end

end IntegrablePathSimulation.Calculus
