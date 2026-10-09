import IntegrablePathSimulation.Propagator.Basic
import IntegrablePathSimulation.Calculus.Product

set_option autoImplicit false

/-!
# Existence of propagators of integrable paths

For an interval-integrable path `H` on `[0, T]` the Picard terms

  `picardTerm H 0 = 1`,  `picardTerm H (n + 1) s = ∫_0^s (-i) H(u) picardTerm H n u du`

are continuous and obey `‖picardTerm H n s‖ ≤ K(s)^n / n!` with `K(s) = ∫_0^s ‖H‖`
(`norm_picardTerm_le`, from the power identity `Calculus.integral_mul_primitive_pow`). Their
sum `picardSeries H` therefore converges uniformly on `[0, T]` and is a propagator
(`isPropagator_picardSeries`, `exists_isPropagator`). This is the existence half of the
Carathéodory theory behind the paragraph after Theorem `hs:thm:time` of the manuscript
(lines 1618-1632); no continuity or regularity of `H` is used.
-/

namespace IntegrablePathSimulation.Propagator

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-- The Picard terms of `U = 1 + ∫_0 (-i) H U`: `picardTerm H 0 = 1` and
`picardTerm H (n + 1) s = ∫_0^s (-i) H(u) picardTerm H n u du`. -/
def picardTerm (H : ℝ → P →L[ℂ] P) : ℕ → ℝ → P →L[ℂ] P
  | 0 => fun _ => 1
  | n + 1 => fun s => ∫ u in (0 : ℝ)..s, (-Complex.I) • (H u * picardTerm H n u)

/-- The Picard series `∑_n picardTerm H n s`. It is the Dyson series of the time-ordered
exponential `𝒯 exp (-i ∫_0^s H(u) du)` of the manuscript (equation `hs:eq:timeerror`,
lines 1431-1435) in iterated-integral form: the `n`-th term is the integral of
`(-i)^n H(u_n) ⋯ H(u_1)` over `0 ≤ u_1 ≤ ⋯ ≤ u_n ≤ s`, written as `n` nested integrals. -/
def picardSeries (H : ℝ → P →L[ℂ] P) (s : ℝ) : P →L[ℂ] P :=
  ∑' n, picardTerm H n s

variable {H : ℝ → P →L[ℂ] P} {T : ℝ}

omit [CompleteSpace P] in
/-- Every Picard term is continuous on `[0, T]`. -/
theorem picardTerm_continuousOn (hT : 0 ≤ T) (hint : IntervalIntegrable H volume 0 T)
    (n : ℕ) : ContinuousOn (picardTerm H n) (Icc 0 T) := by
  induction n with
  | zero => exact continuousOn_const
  | succ n ih =>
    have hi : IntervalIntegrable (fun u => (-Complex.I) • (H u * picardTerm H n u)) volume 0 T :=
      (hint.mul_continuousOn (by rwa [uIcc_of_le hT])).smul (-Complex.I)
    have hc := intervalIntegral.continuousOn_primitive_interval' hi left_mem_uIcc
    rw [uIcc_of_le hT] at hc
    exact hc

omit [CompleteSpace P] in
/-- The integrand `-i H(u) picardTerm H n u` of the next Picard term is interval integrable on
`[0, T]`. -/
theorem intervalIntegrable_picardIntegrand (hT : 0 ≤ T)
    (hint : IntervalIntegrable H volume 0 T) (n : ℕ) :
    IntervalIntegrable (fun u => (-Complex.I) • (H u * picardTerm H n u)) volume 0 T :=
  (hint.mul_continuousOn (by rw [uIcc_of_le hT]; exact picardTerm_continuousOn hT hint n)).smul
    (-Complex.I)

/-- Restriction of interval integrability from `[0, T]` to `[0, s]` for `s ∈ [0, T]`. -/
theorem intervalIntegrable_zero_of_mem_Icc {E : Type*} [NormedAddCommGroup E] {f : ℝ → E}
    {s : ℝ} (hf : IntervalIntegrable f volume 0 T) (hs : s ∈ Icc 0 T) :
    IntervalIntegrable f volume 0 s :=
  hf.mono_set (by
    rw [uIcc_of_le hs.1, uIcc_of_le (hs.1.trans hs.2)]
    exact Icc_subset_Icc le_rfl hs.2)

omit [CompleteSpace P] in
/-- **Picard bound**: `‖picardTerm H n s‖ ≤ (∫_0^s ‖H‖)^n / n!` on `[0, T]`. -/
theorem norm_picardTerm_le (hT : 0 ≤ T) (hint : IntervalIntegrable H volume 0 T) (n : ℕ) :
    ∀ s ∈ Icc 0 T, ‖picardTerm H n s‖ ≤ (∫ u in (0 : ℝ)..s, ‖H u‖) ^ n / n.factorial := by
  induction n with
  | zero =>
    intro s _
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]
    exact ContinuousLinearMap.norm_id_le
  | succ n ih =>
    intro s hs
    have hKc : ContinuousOn (fun u => ∫ v in (0 : ℝ)..u, ‖H v‖) (Icc 0 T) := by
      have hc := intervalIntegral.continuousOn_primitive_interval' hint.norm left_mem_uIcc
      rwa [uIcc_of_le hT] at hc
    have hsub : Icc 0 s ⊆ Icc 0 T := Icc_subset_Icc le_rfl hs.2
    have hgi : IntervalIntegrable
        (fun u => ‖H u‖ * (∫ v in (0 : ℝ)..u, ‖H v‖) ^ n / n.factorial) volume 0 s := by
      have := (intervalIntegrable_zero_of_mem_Icc hint.norm hs).mul_continuousOn
        (g := fun u => (∫ v in (0 : ℝ)..u, ‖H v‖) ^ n)
        (by rw [uIcc_of_le hs.1]; exact (hKc.mono hsub).pow n)
      exact this.div_const _
    calc ‖picardTerm H (n + 1) s‖
        = ‖∫ u in (0 : ℝ)..s, (-Complex.I) • (H u * picardTerm H n u)‖ := rfl
      _ ≤ ∫ u in (0 : ℝ)..s, ‖H u‖ * (∫ v in (0 : ℝ)..u, ‖H v‖) ^ n / n.factorial := by
        refine intervalIntegral.norm_integral_le_of_norm_le hs.1 (ae_of_all _ fun u hu => ?_) hgi
        have hu' : u ∈ Icc 0 T := ⟨hu.1.le, hu.2.trans hs.2⟩
        rw [norm_smul, norm_neg, Complex.norm_I, one_mul, mul_div_assoc]
        exact (norm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_left (ih u hu') (norm_nonneg _))
      _ = (∫ u in (0 : ℝ)..s, ‖H u‖ * (∫ v in (0 : ℝ)..u, ‖H v‖) ^ n) / n.factorial :=
        intervalIntegral.integral_div _ _
      _ = (∫ u in (0 : ℝ)..s, ‖H u‖) ^ (n + 1) / (n + 1).factorial := by
        rw [Calculus.integral_mul_primitive_pow hT hint.norm n s hs, Nat.factorial_succ]
        push_cast
        rw [div_div, mul_comm]

/-- The Picard series is a propagator of every interval-integrable path. -/
theorem isPropagator_picardSeries (hT : 0 ≤ T) (hint : IntervalIntegrable H volume 0 T) :
    IsPropagator H (picardSeries H) T := by
  set K : ℝ := ∫ u in (0 : ℝ)..T, ‖H u‖ with hK
  have hKs : ∀ s ∈ Icc 0 T, 0 ≤ ∫ u in (0 : ℝ)..s, ‖H u‖ ∧ ∫ u in (0 : ℝ)..s, ‖H u‖ ≤ K :=
    fun s hs => ⟨intervalIntegral.integral_nonneg hs.1 (fun _ _ => norm_nonneg _),
      intervalIntegral.integral_mono_interval le_rfl hs.1 hs.2
        (ae_of_all _ fun _ => norm_nonneg _) hint.norm⟩
  have hbd : ∀ n, ∀ s ∈ Icc 0 T, ‖picardTerm H n s‖ ≤ K ^ n / n.factorial := fun n s hs =>
    (norm_picardTerm_le hT hint n s hs).trans
      (div_le_div_of_nonneg_right (pow_le_pow_left₀ (hKs s hs).1 (hKs s hs).2 n) (by positivity))
  have hsum := Real.summable_pow_div_factorial K
  have hts : ∀ s ∈ Icc 0 T, Summable (fun n => picardTerm H n s) := fun s hs =>
    hsum.of_norm_bounded (fun n => hbd n s hs)
  have hcont : ContinuousOn (picardSeries H) (Icc 0 T) :=
    continuousOn_tsum (picardTerm_continuousOn hT hint) hsum hbd
  have h0 : picardSeries H 0 = 1 := by
    unfold picardSeries
    rw [tsum_eq_single 0]
    · rfl
    · intro n hn
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
      exact intervalIntegral.integral_same
  refine ⟨h0, hint.mul_continuousOn (by rwa [uIcc_of_le hT]), fun s hs => ?_⟩
  rw [h0]
  have hsI : ∀ u ∈ uIoc (0 : ℝ) s, u ∈ Icc 0 T := fun u hu => by
    rw [uIoc_of_le hs.1] at hu
    exact ⟨hu.1.le, hu.2.trans hs.2⟩
  have hHS : HasSum (fun n => ∫ u in (0 : ℝ)..s, (-Complex.I) • (H u * picardTerm H n u))
      (∫ u in (0 : ℝ)..s, (-Complex.I) • (H u * picardSeries H u)) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (F := fun n u => (-Complex.I) • (H u * picardTerm H n u))
      (fun n u => ‖H u‖ * (K ^ n / n.factorial))
      (fun n => (intervalIntegrable_zero_of_mem_Icc
        (intervalIntegrable_picardIntegrand hT hint n) hs).aestronglyMeasurable_restrict_uIoc)
      (fun n => ae_of_all _ fun u hu => ?_)
      (ae_of_all _ fun u _ => hsum.mul_left ‖H u‖) ?_
      (ae_of_all _ fun u hu =>
        (((hts u (hsI u hu)).hasSum.mul_left (H u)).const_smul (-Complex.I)))
    · rw [norm_smul, norm_neg, Complex.norm_I, one_mul]
      exact (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_left (hbd n u (hsI u hu)) (norm_nonneg _))
    · simp_rw [tsum_mul_left]
      exact (intervalIntegrable_zero_of_mem_Icc hint.norm hs).mul_const _
  have hU : picardSeries H s = picardTerm H 0 s + ∑' n, picardTerm H (n + 1) s :=
    (hts s hs).tsum_eq_zero_add
  rw [hU]
  exact congrArg (picardTerm H 0 s + ·) hHS.tsum_eq

/-- **Existence**: every interval-integrable path has a propagator on `[0, T]`. -/
theorem exists_isPropagator (hT : 0 ≤ T) (hint : IntervalIntegrable H volume 0 T) :
    ∃ U : ℝ → P →L[ℂ] P, IsPropagator H U T :=
  ⟨picardSeries H, isPropagator_picardSeries hT hint⟩

end

end IntegrablePathSimulation.Propagator
