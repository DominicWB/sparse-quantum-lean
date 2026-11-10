import IntegrablePathSimulation.Calculus.Absolute

set_option autoImplicit false

/-!
# The product rule for integral equations

If `F s = F a + ∫_a^s f` and `G s = G a + ∫_a^s g` on `[a, b]`, with `f` and `g` interval integrable
and values in a complete normed `ℝ`-algebra, then `F s G s = F a G a + ∫_a^s (f G + F g)` on
`[a, b]` (`mul_eq_add_integral`). This is the product rule for absolutely continuous functions, in
the form used for propagators of integrable paths (the paragraph after Theorem `hs:thm:time` of the
manuscript): the unitary Duhamel formula and the unitarity of the propagator follow from it.

For real functions it gives the power identity
`∫_a^s k(u) K(u)^n du = K(s)^{n+1} / (n + 1)`, `K(s) = ∫_a^s k`
(`integral_mul_primitive_pow`), which bounds the Picard iterates by `K^n / n!` and proves the
integral form of Grönwall's inequality.
-/

namespace IntegrablePathSimulation.Calculus

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

/-- Increments of a solution of `F s = F a + ∫_a^s f` on `[a, b]`: for `y ≤ x` in `[a, b]`,
`‖F x - F y‖ ≤ ∫_y^x ‖f‖`. -/
theorem norm_sub_le_integral_norm_of_eq_add_integral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {F f : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hf : IntervalIntegrable f volume a b) (hF : ∀ s ∈ Icc a b, F s = F a + ∫ u in a..s, f u)
    {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) (hyx : y ≤ x) :
    ‖F x - F y‖ ≤ ∫ u in y..x, ‖f u‖ := by
  have hsub : ∀ s ∈ Icc a b, IntervalIntegrable f volume a s := fun s hs =>
    hf.mono_set (by rw [uIcc_of_le hab, uIcc_of_le hs.1]; exact Icc_subset_Icc_right hs.2)
  rw [hF x hx, hF y hy, add_sub_add_left_eq_sub,
    intervalIntegral.integral_interval_sub_left (hsub x hx) (hsub y hy)]
  exact intervalIntegral.norm_integral_le_integral_norm hyx

omit [CompleteSpace A] in
/-- The integrand `f G + F g` of the product rule is interval integrable. -/
theorem intervalIntegrable_mul_add {F G f g : ℝ → A} {a b : ℝ} (hab : a ≤ b)
    (hf : IntervalIntegrable f volume a b) (hg : IntervalIntegrable g volume a b)
    (hF : ∀ s ∈ Icc a b, F s = F a + ∫ u in a..s, f u)
    (hG : ∀ s ∈ Icc a b, G s = G a + ∫ u in a..s, g u) :
    IntervalIntegrable (fun u => f u * G u + F u * g u) volume a b := by
  have hF' := continuousOn_of_eq_add_integral hab hf hF
  have hG' := continuousOn_of_eq_add_integral hab hg hG
  rw [← uIcc_of_le hab] at hF' hG'
  exact (hf.mul_continuousOn hG').add (hg.continuousOn_mul hF')

/-- **Product rule for integral equations.** If `F s = F a + ∫_a^s f` and
`G s = G a + ∫_a^s g` on `[a, b]` with interval-integrable `f`, `g`, then
`F s G s = F a G a + ∫_a^s (f G + F g)` on `[a, b]`. -/
theorem mul_eq_add_integral {F G f g : ℝ → A} {a b : ℝ} (hab : a ≤ b)
    (hf : IntervalIntegrable f volume a b) (hg : IntervalIntegrable g volume a b)
    (hF : ∀ s ∈ Icc a b, F s = F a + ∫ u in a..s, f u)
    (hG : ∀ s ∈ Icc a b, G s = G a + ∫ u in a..s, g u) :
    ∀ s ∈ Icc a b, F s * G s = F a * G a + ∫ u in a..s, (f u * G u + F u * g u) := by
  have hF' := continuousOn_of_eq_add_integral hab hf hF
  have hG' := continuousOn_of_eq_add_integral hab hg hG
  obtain ⟨BF, hBF⟩ := isCompact_Icc.exists_bound_of_continuousOn hF'
  obtain ⟨BG, hBG⟩ := isCompact_Icc.exists_bound_of_continuousOn hG'
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hBF0 : 0 ≤ BF := (norm_nonneg _).trans (hBF a ha)
  have hBG0 : 0 ≤ BG := (norm_nonneg _).trans (hBG a ha)
  have hwi : IntervalIntegrable (fun v => BG * ‖f v‖ + BF * ‖g v‖) volume a b :=
    (hf.norm.const_mul BG).add (hg.norm.const_mul BF)
  have hsub : ∀ {φ : ℝ → ℝ} {x y : ℝ}, IntervalIntegrable φ volume a b → x ∈ Icc a b →
      y ∈ Icc a b → IntervalIntegrable φ volume y x := fun hφ hx hy =>
    hφ.mono_set (uIcc_subset_uIcc (by rw [uIcc_of_le hab]; exact hy)
      (by rw [uIcc_of_le hab]; exact hx))
  have key : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, y ≤ x →
      dist (F x * G x) (F y * G y) ≤
        1 * dist (∫ v in a..x, (BG * ‖f v‖ + BF * ‖g v‖))
          (∫ v in a..y, (BG * ‖f v‖ + BF * ‖g v‖)) := by
    intro x hx y hy hyx
    have h1 := norm_sub_le_integral_norm_of_eq_add_integral hab hf hF hx hy hyx
    have h2 := norm_sub_le_integral_norm_of_eq_add_integral hab hg hG hx hy hyx
    have hfi : IntervalIntegrable (fun u => ‖f u‖) volume y x := hsub hf.norm hx hy
    have hgi : IntervalIntegrable (fun u => ‖g u‖) volume y x := hsub hg.norm hx hy
    rw [one_mul, Real.dist_eq,
      intervalIntegral.integral_interval_sub_left (hsub hwi hx ha) (hsub hwi hy ha),
      abs_of_nonneg (intervalIntegral.integral_nonneg hyx fun u _ =>
        add_nonneg (mul_nonneg hBG0 (norm_nonneg _)) (mul_nonneg hBF0 (norm_nonneg _))),
      dist_eq_norm, intervalIntegral.integral_add (hfi.const_mul BG) (hgi.const_mul BF),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    have hfn : 0 ≤ ∫ u in y..x, ‖f u‖ :=
      intervalIntegral.integral_nonneg hyx fun u _ => norm_nonneg _
    calc ‖F x * G x - F y * G y‖ = ‖(F x - F y) * G x + F y * (G x - G y)‖ := by
          congr 1; noncomm_ring
      _ ≤ ‖F x - F y‖ * ‖G x‖ + ‖F y‖ * ‖G x - G y‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
      _ ≤ (∫ u in y..x, ‖f u‖) * BG + BF * ∫ u in y..x, ‖g u‖ :=
          add_le_add (mul_le_mul h1 (hBG x hx) (norm_nonneg _) hfn)
            (mul_le_mul (hBF y hy) h2 (norm_nonneg _) hBF0)
      _ = BG * (∫ u in y..x, ‖f u‖) + BF * ∫ u in y..x, ‖g u‖ := by ring
  have hAC : AbsolutelyContinuousOnInterval (fun s => F s * G s) a b := by
    refine absolutelyContinuousOnInterval_of_dist_le (C := 1)
      (absolutelyContinuousOnInterval_primitive hwi left_mem_uIcc) ?_
    intro x hx y hy
    rw [uIcc_of_le hab] at hx hy
    rcases le_total y x with h | h
    · exact key x hx y hy h
    · rw [dist_comm, dist_comm (∫ v in a..x, (BG * ‖f v‖ + BF * ‖g v‖))]
      exact key y hy x hx h
  have hderiv : ∀ᵐ u, u ∈ uIcc a b →
      HasDerivAt (fun s => F s * G s) (f u * G u + F u * g u) u := by
    filter_upwards [ae_hasDerivAt_of_eq_add_integral hab hf hF,
      ae_hasDerivAt_of_eq_add_integral hab hg hG] with u h1 h2 hu
    rw [uIcc_of_le hab] at hu
    exact (h1 hu).mul (h2 hu)
  intro s hs
  exact eq_add_integral_of_ae_hasDerivAt hAC (intervalIntegrable_mul_add hab hf hg hF hG) hderiv
    s (by rwa [uIcc_of_le hab])

/-- **Power identity.** For an interval-integrable real `k` and `K(s) = ∫_a^s k`,
`∫_a^s k(u) K(u)^n du = K(s)^{n+1} / (n + 1)` on `[a, b]`. -/
theorem integral_mul_primitive_pow {k : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hk : IntervalIntegrable k volume a b) (n : ℕ) :
    ∀ s ∈ Icc a b, ∫ u in a..s, k u * (∫ v in a..u, k v) ^ n =
      (∫ v in a..s, k v) ^ (n + 1) / (n + 1) := by
  set K : ℝ → ℝ := fun s => ∫ v in a..s, k v with hKdef
  have hK : ∀ s ∈ Icc a b, K s = K a + ∫ u in a..s, k u := fun s _ => by simp [K]
  have hKa : K a = 0 := by simp [K]
  have hKc : ContinuousOn K (uIcc a b) := by
    rw [uIcc_of_le hab]; exact continuousOn_of_eq_add_integral hab hk hK
  have hint : ∀ m : ℕ, IntervalIntegrable (fun u => k u * K u ^ m) volume a b :=
    fun m => hk.mul_continuousOn (hKc.pow m)
  have hpow : ∀ m : ℕ, ∀ s ∈ Icc a b,
      K s ^ (m + 1) = ∫ u in a..s, ((m : ℝ) + 1) * (k u * K u ^ m) := by
    intro m
    induction m with
    | zero => intro s _; simp [K]
    | succ m ih =>
      intro s hs
      have hF : ∀ s ∈ Icc a b, K s ^ (m + 1) =
          K a ^ (m + 1) + ∫ u in a..s, ((m : ℝ) + 1) * (k u * K u ^ m) := by
        intro s hs; rw [hKa, zero_pow (Nat.succ_ne_zero m), zero_add]; exact ih s hs
      have h := mul_eq_add_integral (A := ℝ) (F := fun s => K s ^ (m + 1)) (G := K)
        (f := fun u => ((m : ℝ) + 1) * (k u * K u ^ m)) (g := k) hab
        ((hint m).const_mul ((m : ℝ) + 1)) hk hF hK s hs
      beta_reduce at h
      rw [hKa, mul_zero, zero_add] at h
      rw [pow_succ, h]
      refine intervalIntegral.integral_congr fun u _ => ?_
      push_cast; ring
  intro s hs
  have h := hpow n s hs
  rw [intervalIntegral.integral_const_mul] at h
  show ∫ u in a..s, k u * K u ^ n = K s ^ (n + 1) / (n + 1)
  rw [h, mul_div_cancel_left₀ _ (by positivity : (n : ℝ) + 1 ≠ 0)]

end

end IntegrablePathSimulation.Calculus
