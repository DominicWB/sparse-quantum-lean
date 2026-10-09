import GateEfficientODE.Grid.Strip
import Mathlib.Analysis.Fourier.PoissonSummation

/-!
# Exponential convergence of the trapezoidal rule on the real line

Let `φ` be holomorphic on the closed strip `|Im z| ≤ a` with the Cauchy
envelope `‖φ z‖ ≤ C / (c² + (Re z)²)`.  Then for every step `h > 0`

  `‖h ∑_{n ∈ ℤ} φ (n h) - ∫ φ‖ ≤ 2 (C π / c) / (exp (2π a / h) - 1)`

(`trapezoid_error`).  The proof applies Mathlib's Poisson summation formula to
`x ↦ h φ (h x)`: the error is the sum of the Fourier coefficients at the
nonzero integers, each bounded by `exp (-2π a |n| / h) C π / c` through a
horizontal contour shift (`fourier_norm_le`).

* `trapezoid_error_op`: the same bound for operator-valued `Φ`, by pairing
  with vectors.
* `cauchy_sum_le`: the trapezoidal sums of the Cauchy density satisfy
  `∑_n h / (π (1 + (n h)²)) ≤ 1 + 4 / (exp (π / h) - 1)`.
-/

namespace SparseHamiltonian.StripQuadrature

noncomputable section
open Complex MeasureTheory Filter Set Asymptotics
open scoped Interval Topology Real FourierTransform InnerProduct

/-! ### The Cauchy envelope -/

theorem envelope_eq (C c x : ℝ) (hc : 0 < c) :
    C / (c ^ 2 + x ^ 2) = (C / c ^ 2) * (1 + (x / c) ^ 2)⁻¹ := by
  have hc2 : 0 < c ^ 2 := by positivity
  rw [div_pow, ← div_eq_mul_inv]
  field_simp

theorem envelope_integrable (C c : ℝ) (hc : 0 < c) :
    Integrable (fun x : ℝ => C / (c ^ 2 + x ^ 2)) := by
  have h := (integrable_inv_one_add_sq.comp_div hc.ne').const_mul (C / c ^ 2)
  refine h.congr (Eventually.of_forall (fun x => ?_))
  simp only [envelope_eq C c x hc]

theorem envelope_integral (C c : ℝ) (hc : 0 < c) :
    ∫ x : ℝ, C / (c ^ 2 + x ^ 2) = C * π / c := by
  simp_rw [envelope_eq C c _ hc]
  rw [integral_const_mul, Measure.integral_comp_div (fun y : ℝ => (1 + y ^ 2)⁻¹) c,
    integral_univ_inv_one_add_sq, abs_of_pos hc, smul_eq_mul]
  field_simp

theorem sq_tendsto_atTop : Tendsto (fun x : ℝ => x ^ 2) atTop atTop :=
  tendsto_pow_atTop two_ne_zero

theorem sq_tendsto_atBot : Tendsto (fun x : ℝ => x ^ 2) atBot atTop := by
  have h := (tendsto_pow_atTop (α := ℝ) two_ne_zero).comp tendsto_neg_atBot_atTop
  refine h.congr (fun x => ?_)
  simp

theorem envelope_tendsto_atTop (C c : ℝ) :
    Tendsto (fun x : ℝ => C / (c ^ 2 + x ^ 2)) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_left _ _ sq_tendsto_atTop)

theorem envelope_tendsto_atBot (C c : ℝ) :
    Tendsto (fun x : ℝ => C / (c ^ 2 + x ^ 2)) atBot (𝓝 0) :=
  tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_left _ _ sq_tendsto_atBot)

/-- The envelope is summable along every arithmetic progression. -/
theorem envelope_summable (C c h : ℝ) (hh : 0 < h) :
    Summable (fun n : ℤ => C / (c ^ 2 + ((n : ℝ) * h) ^ 2)) := by
  refine Summable.of_norm_bounded_eventually
    ((Real.summable_abs_int_rpow one_lt_two).mul_left (|C| / h ^ 2)) ?_
  have hfin : {n : ℤ | ¬ ‖C / (c ^ 2 + ((n : ℝ) * h) ^ 2)‖ ≤
      |C| / h ^ 2 * |(n : ℝ)| ^ (-(2 : ℝ))} ⊆ {0} := by
    intro n hn
    by_contra hne
    apply hn
    have hx0 : (n : ℝ) ≠ 0 := by exact_mod_cast hne
    have hpow : |(n : ℝ)| ^ (-(2 : ℝ)) = ((n : ℝ) ^ 2)⁻¹ := by
      rw [Real.rpow_neg (abs_nonneg _), Real.rpow_two, sq_abs]
    rw [hpow, Real.norm_eq_abs, abs_div]
    have hx2 : 0 < (n : ℝ) ^ 2 := by positivity
    have hden : 0 < c ^ 2 + ((n : ℝ) * h) ^ 2 := by positivity
    rw [abs_of_pos hden, div_le_iff₀ hden]
    have hle : h ^ 2 * (n : ℝ) ^ 2 ≤ c ^ 2 + ((n : ℝ) * h) ^ 2 := by nlinarith [sq_nonneg c]
    have e : |C| / h ^ 2 * ((n : ℝ) ^ 2)⁻¹ * (h ^ 2 * (n : ℝ) ^ 2) = |C| := by
      field_simp
    have hmono : |C| / h ^ 2 * ((n : ℝ) ^ 2)⁻¹ * (h ^ 2 * (n : ℝ) ^ 2) ≤
        |C| / h ^ 2 * ((n : ℝ) ^ 2)⁻¹ * (c ^ 2 + ((n : ℝ) * h) ^ 2) :=
      mul_le_mul_of_nonneg_left hle (by positivity)
    linarith
  exact Set.Finite.subset (Set.finite_singleton 0) hfin

/-- On the strip `|Im z| ≤ 1/2` the Cauchy denominator stays away from zero. -/
theorem denominator_lower (z : ℂ) (hz : |z.im| ≤ 1 / 2) :
    π * (1 / 4 + z.re ^ 2) ≤ ‖(π : ℂ) * (1 + z ^ 2)‖ := by
  have hre : ((π : ℂ) * (1 + z ^ 2)).re = π * (1 + z.re ^ 2 - z.im ^ 2) := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re,
      Complex.one_re, Complex.add_im, Complex.one_im, pow_two, Complex.mul_im, zero_mul, sub_zero]
    ring
  have hy : z.im ^ 2 ≤ 1 / 4 := by
    have := abs_le.mp hz
    nlinarith
  calc π * (1 / 4 + z.re ^ 2) ≤ π * (1 + z.re ^ 2 - z.im ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ Real.pi_pos.le
        linarith
    _ = ((π : ℂ) * (1 + z ^ 2)).re := hre.symm
    _ ≤ ‖(π : ℂ) * (1 + z ^ 2)‖ := Complex.re_le_norm _

/-! ### Two-sided geometric sums -/

theorem hasSum_two_sided (r : ℝ) (h0 : 0 ≤ r) (h1 : r < 1) :
    HasSum (fun n : ℤ => if n = 0 then 0 else r ^ n.natAbs) (2 * (r / (1 - r))) := by
  have hpos : HasSum (fun n : ℕ => if (n : ℤ) = 0 then (0 : ℝ) else r ^ ((n : ℤ).natAbs))
      (r / (1 - r)) := by
    have hg := hasSum_geometric_of_lt_one h0 h1
    have hd := hg.sub (hasSum_ite_eq (0 : ℕ) (1 : ℝ))
    have he : (1 - r)⁻¹ - 1 = r / (1 - r) := by
      have : (1 - r) ≠ 0 := by linarith
      field_simp
      ring
    rw [he] at hd
    refine hd.congr_fun (fun n => ?_)
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hn'' : n ≠ 0 := hn.ne'
      simp [hn'']
  have hneg : HasSum (fun n : ℕ => if (-(n + 1 : ℤ)) = 0 then (0 : ℝ)
      else r ^ ((-(n + 1 : ℤ)).natAbs)) (r / (1 - r)) := by
    have hg := (hasSum_geometric_of_lt_one h0 h1).mul_left r
    have he : r * (1 - r)⁻¹ = r / (1 - r) := by rw [div_eq_mul_inv]
    rw [he] at hg
    refine hg.congr_fun (fun n => ?_)
    have hne : (-(n + 1 : ℤ)) ≠ 0 := by omega
    have habs : (-(n + 1 : ℤ)).natAbs = n + 1 := by omega
    simp only [hne, if_false, habs, pow_succ]
    ring
  have h := HasSum.of_nat_of_neg_add_one
    (f := fun n : ℤ => if n = 0 then (0 : ℝ) else r ^ n.natAbs) hpos hneg
  have e : r / (1 - r) + r / (1 - r) = 2 * (r / (1 - r)) := by ring
  rw [e] at h
  exact h

theorem geometric_ratio (t : ℝ) (ht : 0 < t) :
    Real.exp (-t) / (1 - Real.exp (-t)) = 1 / (Real.exp t - 1) := by
  have h1 : Real.exp (-t) < 1 := by
    rw [Real.exp_lt_one_iff]; linarith
  have h2 : 1 < Real.exp t := Real.one_lt_exp_iff.mpr ht
  have h3 : Real.exp (-t) * Real.exp t = 1 := by rw [← Real.exp_add]; simp
  have hne1 : 1 - Real.exp (-t) ≠ 0 := by linarith
  have hne2 : Real.exp t - 1 ≠ 0 := by linarith
  field_simp
  nlinarith [h3]

/-! ### The scalar trapezoidal rule -/

/-- **Trapezoidal rule on the real line**, for a function holomorphic on the
closed strip `|Im z| ≤ a` with a Cauchy envelope. -/
theorem trapezoid_error (φ : ℂ → ℂ) {a h C c : ℝ} (ha : 0 < a) (hh : 0 < h) (hc : 0 < c)
    (hd : ∀ z : ℂ, |z.im| ≤ a → DifferentiableAt ℂ φ z)
    (hG : ∀ z : ℂ, |z.im| ≤ a → ‖φ z‖ ≤ C / (c ^ 2 + z.re ^ 2)) :
    Summable (fun n : ℤ => φ ((n : ℂ) * h)) ∧
    ‖(h : ℂ) * ∑' n : ℤ, φ ((n : ℂ) * h) - ∫ x : ℝ, φ x‖ ≤
      2 * (C * π / c) / (Real.exp (2 * π * a / h) - 1) := by
  have hC : 0 ≤ C := by
    have h0 := hG 0 (by simpa using ha.le)
    have hc2 : 0 < c ^ 2 + (0 : ℂ).re ^ 2 := by simp; positivity
    have := (norm_nonneg _).trans h0
    exact (div_nonneg_iff.mp this).elim (fun h => h.1) (fun h => absurd h.2 (not_le.mpr hc2))
  -- the rescaled function
  set b : ℝ := a / h with hbdef
  have hb : 0 < b := div_pos ha hh
  let ψ : ℂ → ℂ := fun z => (h : ℂ) * φ ((h : ℂ) * z)
  let Gψ : ℝ → ℝ := fun x => h * (C / (c ^ 2 + (h * x) ^ 2))
  have hmul_im : ∀ z : ℂ, ((h : ℂ) * z).im = h * z.im := by
    intro z; simp
  have hmul_re : ∀ z : ℂ, ((h : ℂ) * z).re = h * z.re := by
    intro z; simp
  have hstrip : ∀ z : ℂ, |z.im| ≤ b → |((h : ℂ) * z).im| ≤ a := by
    intro z hz
    rw [hmul_im, abs_mul, abs_of_pos hh]
    have := mul_le_mul_of_nonneg_left hz hh.le
    rwa [hbdef, mul_div_cancel₀ _ hh.ne'] at this
  have hψd : ∀ z : ℂ, |z.im| ≤ b → DifferentiableAt ℂ ψ z := by
    intro z hz
    have h1 : DifferentiableAt ℂ (fun z : ℂ => (h : ℂ) * z) z :=
      (differentiableAt_id.const_mul _)
    exact (differentiableAt_const _).mul ((hd _ (hstrip z hz)).comp z h1)
  have hψG : ∀ z : ℂ, |z.im| ≤ b → ‖ψ z‖ ≤ Gψ z.re := by
    intro z hz
    have h1 := hG _ (hstrip z hz)
    rw [hmul_re] at h1
    simp only [ψ, Gψ, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh]
    exact mul_le_mul_of_nonneg_left h1 hh.le
  have hGψi : Integrable Gψ :=
    ((envelope_integrable C c hc).comp_mul_left' hh.ne').const_mul h
  have hGψint : ∫ x, Gψ x = C * π / c := by
    simp only [Gψ]
    rw [integral_const_mul, Measure.integral_comp_mul_left (fun y : ℝ => C / (c ^ 2 + y ^ 2)) h,
      envelope_integral C c hc, abs_of_pos (inv_pos.mpr hh), smul_eq_mul]
    field_simp
  have hGψtop : Tendsto Gψ atTop (𝓝 0) := by
    have h1 := (envelope_tendsto_atTop C c).comp (tendsto_id.const_mul_atTop hh)
    simpa [Gψ] using h1.const_mul h
  have hGψbot : Tendsto Gψ atBot (𝓝 0) := by
    have h1 := (envelope_tendsto_atBot C c).comp (tendsto_id.const_mul_atBot hh)
    simpa [Gψ] using h1.const_mul h
  -- the function on the real line
  let f : ℝ → ℂ := fun x => ψ x
  have hfcont : Continuous f := by
    refine continuous_iff_continuousAt.mpr (fun x => ?_)
    have h1 : DifferentiableAt ℂ ψ (x : ℂ) := hψd _ (by simpa using hb.le)
    exact ContinuousAt.comp (g := ψ) (f := fun t : ℝ => (t : ℂ)) h1.continuousAt
      continuous_ofReal.continuousAt
  have hF : ∀ ξ : ℝ, ‖𝓕 f ξ‖ ≤ Real.exp (-(2 * π * b * |ξ|)) * (C * π / c) := by
    intro ξ
    have h1 := fourier_norm_le ψ b hb.le hψd Gψ hψG hGψi hGψtop hGψbot ξ
    rwa [hGψint] at h1
  -- decay of `f`
  have hO : f =O[cocompact ℝ] (fun x : ℝ => |x| ^ (-(2 : ℝ))) := by
    refine IsBigO.of_bound (C / h) ?_
    have hmem : ({0}ᶜ : Set ℝ) ∈ cocompact ℝ := isCompact_singleton.compl_mem_cocompact
    filter_upwards [hmem] with x hx
    have hx0 : x ≠ 0 := hx
    have h1 := hψG (x : ℂ) (by simpa using hb.le)
    simp only [Complex.ofReal_re] at h1
    have hpow : ‖|x| ^ (-(2 : ℝ))‖ = (x ^ 2)⁻¹ := by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg x) _),
        Real.rpow_neg (abs_nonneg x), Real.rpow_two, sq_abs]
    rw [hpow]
    refine h1.trans ?_
    simp only [Gψ]
    have hx2 : 0 < x ^ 2 := by positivity
    have hden : h ^ 2 * x ^ 2 ≤ c ^ 2 + (h * x) ^ 2 := by nlinarith [sq_nonneg c]
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    have : C / h * (x ^ 2)⁻¹ * (c ^ 2 + (h * x) ^ 2) ≥ C / h * (x ^ 2)⁻¹ * (h ^ 2 * x ^ 2) :=
      mul_le_mul_of_nonneg_left hden (by positivity)
    have e : C / h * (x ^ 2)⁻¹ * (h ^ 2 * x ^ 2) = h * C := by
      field_simp
    linarith
  -- summability of the Fourier coefficients
  set r : ℝ := Real.exp (-(2 * π * b)) with hrdef
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by
    rw [hrdef, Real.exp_lt_one_iff]
    have := Real.pi_pos
    nlinarith
  have hrpow : ∀ n : ℤ, Real.exp (-(2 * π * b * |(n : ℝ)|)) = r ^ n.natAbs := by
    intro n
    rw [hrdef, ← Real.exp_nat_mul]
    congr 1
    rw [Nat.cast_natAbs, Int.cast_abs]
    ring
  have hgeo := hasSum_two_sided r hr0 hr1
  have hsum_abs : Summable (fun n : ℤ => r ^ n.natAbs) := by
    have hp : Summable (fun n : ℕ => r ^ ((n : ℤ).natAbs)) := by
      simpa using summable_geometric_of_lt_one hr0 hr1
    have hn : Summable (fun n : ℕ => r ^ ((-(n + 1 : ℤ)).natAbs)) := by
      have : (fun n : ℕ => r ^ ((-(n + 1 : ℤ)).natAbs)) = fun n : ℕ => r * r ^ n := by
        funext n
        have habs : (-(n + 1 : ℤ)).natAbs = n + 1 := by omega
        rw [habs, pow_succ, mul_comm]
      rw [this]
      exact (summable_geometric_of_lt_one hr0 hr1).mul_left r
    exact Summable.of_nat_of_neg_add_one hp hn
  have hFsum : Summable (fun n : ℤ => 𝓕 f n) := by
    refine Summable.of_norm_bounded (hsum_abs.mul_left (C * π / c)) (fun n => ?_)
    have h1 := hF n
    rw [hrpow n] at h1
    linarith
  -- Poisson summation
  have hP := Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable hfcont one_lt_two hO hFsum 0
  have hfour : ∀ n : ℤ, fourier n ((0 : ℝ) : UnitAddCircle) = 1 := by
    intro n
    rw [fourier_coe_apply]
    simp
  simp only [zero_add, hfour, mul_one] at hP
  -- the left side is the trapezoidal sum
  have hfn : ∀ n : ℤ, f n = (h : ℂ) * φ ((n : ℂ) * h) := by
    intro n
    simp only [f, ψ]
    congr 2
    push_cast
    ring
  -- summability of the trapezoidal terms
  have hsumφ : Summable (fun n : ℤ => φ ((n : ℂ) * h)) := by
    refine Summable.of_norm_bounded (envelope_summable C c h hh) (fun n => ?_)
    have h1 := hG ((n : ℂ) * h) (by simpa using ha.le)
    simpa using h1
  refine ⟨hsumφ, ?_⟩
  have hlhs : (h : ℂ) * ∑' n : ℤ, φ ((n : ℂ) * h) = ∑' n : ℤ, f n := by
    rw [← tsum_mul_left]
    exact tsum_congr (fun n => (hfn n).symm)
  -- the zero coefficient is the integral
  have hF0 : 𝓕 f 0 = ∫ x : ℝ, φ x := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    simp only [mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_smul]
    simp only [f, ψ]
    rw [integral_const_mul]
    have h1 := Measure.integral_comp_mul_left (fun y : ℝ => φ y) h
    simp only [Complex.ofReal_mul] at h1
    rw [h1, abs_of_pos (inv_pos.mpr hh)]
    rw [Complex.real_smul, ← mul_assoc, Complex.ofReal_inv,
      mul_inv_cancel₀ (by exact_mod_cast hh.ne'), one_mul]
  rw [hlhs, hP, hFsum.tsum_eq_add_tsum_ite 0, Int.cast_zero, hF0, add_sub_cancel_left]
  -- bound the remaining coefficients
  have hbound : ∀ n : ℤ, ‖(if n = 0 then 0 else 𝓕 f n)‖ ≤
      (C * π / c) * (if n = 0 then 0 else r ^ n.natAbs) := by
    intro n
    split_ifs
    · simp
    · have h1 := hF n
      rw [hrpow n] at h1
      linarith
  have hsum2 : Summable (fun n : ℤ => (C * π / c) * (if n = 0 then 0 else r ^ n.natAbs)) :=
    (hgeo.summable).mul_left _
  calc ‖∑' n : ℤ, (if n = 0 then 0 else 𝓕 f n)‖
      ≤ ∑' n : ℤ, (C * π / c) * (if n = 0 then 0 else r ^ n.natAbs) :=
        tsum_of_norm_bounded (hsum2.hasSum) hbound
    _ = (C * π / c) * (2 * (r / (1 - r))) := by
        rw [tsum_mul_left, hgeo.tsum_eq]
    _ = 2 * (C * π / c) / (Real.exp (2 * π * a / h) - 1) := by
        have ht : 0 < 2 * π * b := by have := Real.pi_pos; positivity
        rw [hrdef, geometric_ratio _ ht]
        have e : 2 * π * b = 2 * π * a / h := by rw [hbdef]; ring
        rw [e]
        ring

/-! ### Operator-valued functions -/

/-- An operator bound from bounds on all matrix elements. -/
theorem opNorm_le_of_inner {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (A : V →L[ℂ] V) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ u v : V, ‖inner ℂ v (A u)‖ ≤ B * (‖v‖ * ‖u‖)) : ‖A‖ ≤ B := by
  refine ContinuousLinearMap.opNorm_le_bound _ hB (fun u => ?_)
  have h1 := h u (A u)
  rw [inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal, abs_norm] at h1
  by_cases hz : ‖A u‖ = 0
  · rw [hz]
    positivity
  · have hpos : 0 < ‖A u‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    have h2 : ‖A u‖ * ‖A u‖ ≤ (B * ‖u‖) * ‖A u‖ := by nlinarith
    exact le_of_mul_le_mul_right h2 hpos

/-- **Trapezoidal rule for operator-valued functions** on a strip. -/
theorem trapezoid_error_op {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [CompleteSpace V] (Φ : ℂ → V →L[ℂ] V) {a h C c : ℝ} (ha : 0 < a) (hh : 0 < h) (hc : 0 < c)
    (hd : ∀ z : ℂ, |z.im| ≤ a → DifferentiableAt ℂ Φ z)
    (hG : ∀ z : ℂ, |z.im| ≤ a → ‖Φ z‖ ≤ C / (c ^ 2 + z.re ^ 2)) :
    Summable (fun n : ℤ => Φ ((n : ℂ) * h)) ∧ Integrable (fun x : ℝ => Φ x) ∧
    ‖(h : ℂ) • ∑' n : ℤ, Φ ((n : ℂ) * h) - ∫ x : ℝ, Φ x‖ ≤
      2 * (C * π / c) / (Real.exp (2 * π * a / h) - 1) := by
  have hC : 0 ≤ C := by
    have h0 := hG 0 (by simpa using ha.le)
    have hc2 : 0 < c ^ 2 + (0 : ℂ).re ^ 2 := by simp; positivity
    have := (norm_nonneg _).trans h0
    exact (div_nonneg_iff.mp this).elim (fun h => h.1) (fun h => absurd h.2 (not_le.mpr hc2))
  have hsum : Summable (fun n : ℤ => Φ ((n : ℂ) * h)) := by
    refine Summable.of_norm_bounded (envelope_summable C c h hh) (fun n => ?_)
    have h1 := hG ((n : ℂ) * h) (by simpa using ha.le)
    simpa using h1
  have hcont : Continuous (fun x : ℝ => Φ x) := by
    refine continuous_iff_continuousAt.mpr (fun x => ?_)
    have h1 : DifferentiableAt ℂ Φ (x : ℂ) := hd _ (by simpa using ha.le)
    exact ContinuousAt.comp (g := Φ) (f := fun t : ℝ => (t : ℂ)) h1.continuousAt
      continuous_ofReal.continuousAt
  have hint : Integrable (fun x : ℝ => Φ x) := by
    refine (envelope_integrable C c hc).mono' hcont.aestronglyMeasurable
      (Eventually.of_forall (fun x => ?_))
    have h1 := hG (x : ℂ) (by simpa using ha.le)
    simpa using h1
  refine ⟨hsum, hint, ?_⟩
  have hErr : 0 ≤ 2 * (C * π / c) / (Real.exp (2 * π * a / h) - 1) := by
    have h1 : 1 < Real.exp (2 * π * a / h) := by
      apply Real.one_lt_exp_iff.mpr
      have := Real.pi_pos
      positivity
    have h2 : 0 < Real.exp (2 * π * a / h) - 1 := by linarith
    positivity
  apply opNorm_le_of_inner _ hErr
  intro u v
  let L : (V →L[ℂ] V) →L[ℂ] ℂ := (innerSL ℂ v).comp (ContinuousLinearMap.apply ℂ V u)
  have hL : ∀ X : V →L[ℂ] V, L X = inner ℂ v (X u) := fun X => rfl
  let φ : ℂ → ℂ := fun z => L (Φ z)
  have hφd : ∀ z : ℂ, |z.im| ≤ a → DifferentiableAt ℂ φ z := fun z hz =>
    (L.differentiable.differentiableAt).comp z (hd z hz)
  have hφG : ∀ z : ℂ, |z.im| ≤ a →
      ‖φ z‖ ≤ (‖v‖ * ‖u‖ * C) / (c ^ 2 + z.re ^ 2) := by
    intro z hz
    have h1 := hG z hz
    have h2 : ‖φ z‖ ≤ ‖v‖ * (‖Φ z‖ * ‖u‖) := by
      simp only [φ, hL]
      refine (norm_inner_le_norm _ _).trans ?_
      exact mul_le_mul_of_nonneg_left ((Φ z).le_opNorm u) (norm_nonneg _)
    have hden : 0 < c ^ 2 + z.re ^ 2 := by positivity
    calc ‖φ z‖ ≤ ‖v‖ * (‖Φ z‖ * ‖u‖) := h2
      _ ≤ ‖v‖ * ((C / (c ^ 2 + z.re ^ 2)) * ‖u‖) := by
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ = (‖v‖ * ‖u‖ * C) / (c ^ 2 + z.re ^ 2) := by ring
  obtain ⟨_, hscalar⟩ := trapezoid_error φ ha hh hc hφd hφG
  have hident : inner ℂ v (((h : ℂ) • ∑' n : ℤ, Φ ((n : ℂ) * h) - ∫ x : ℝ, Φ x) u) =
      (h : ℂ) * ∑' n : ℤ, φ ((n : ℂ) * h) - ∫ x : ℝ, φ x := by
    rw [← hL, map_sub, map_smul, smul_eq_mul, L.map_tsum hsum, ← L.integral_comp_comm hint]
  rw [hident]
  refine hscalar.trans (le_of_eq ?_)
  ring

/-- **Trapezoidal sums of the Cauchy density.** -/
theorem cauchy_sum_le (h : ℝ) (hh : 0 < h) :
    Summable (fun n : ℤ => h / (π * (1 + ((n : ℝ) * h) ^ 2))) ∧
    ∑' n : ℤ, h / (π * (1 + ((n : ℝ) * h) ^ 2)) ≤ 1 + 4 / (Real.exp (π / h) - 1) := by
  let φ : ℂ → ℂ := fun z => ((π : ℂ) * (1 + z ^ 2))⁻¹
  have hden : ∀ z : ℂ, |z.im| ≤ 1 / 2 → (π : ℂ) * (1 + z ^ 2) ≠ 0 := by
    intro z hz h0
    have h1 := denominator_lower z hz
    rw [h0, norm_zero] at h1
    have : 0 < π * (1 / 4 + z.re ^ 2) := by have := Real.pi_pos; positivity
    linarith
  have hφd : ∀ z : ℂ, |z.im| ≤ 1 / 2 → DifferentiableAt ℂ φ z := by
    intro z hz
    have h1 : DifferentiableAt ℂ (fun z : ℂ => (π : ℂ) * (1 + z ^ 2)) z := by fun_prop
    exact h1.inv (hden z hz)
  have hφG : ∀ z : ℂ, |z.im| ≤ 1 / 2 →
      ‖φ z‖ ≤ (1 / π) / ((1 / 2) ^ 2 + z.re ^ 2) := by
    intro z hz
    have h1 := denominator_lower z hz
    have hpos : 0 < π * (1 / 4 + z.re ^ 2) := by have := Real.pi_pos; positivity
    simp only [φ, norm_inv]
    calc ‖(π : ℂ) * (1 + z ^ 2)‖⁻¹ ≤ (π * (1 / 4 + z.re ^ 2))⁻¹ :=
          inv_anti₀ hpos h1
      _ = (1 / π) / ((1 / 2) ^ 2 + z.re ^ 2) := by
          have := Real.pi_pos
          field_simp
          ring
  obtain ⟨hsumC, hbound⟩ := trapezoid_error φ (by norm_num : (0 : ℝ) < 1 / 2) hh
    (by norm_num : (0 : ℝ) < 1 / 2) hφd hφG
  have hreal : ∀ n : ℤ, (h : ℂ) * φ ((n : ℂ) * h) =
      ((h / (π * (1 + ((n : ℝ) * h) ^ 2)) : ℝ) : ℂ) := by
    intro n
    simp only [φ]
    push_cast
    rw [div_eq_mul_inv]
  have hsumR : Summable (fun n : ℤ => h / (π * (1 + ((n : ℝ) * h) ^ 2))) := by
    have h1 : Summable (fun n : ℤ => (h : ℂ) * φ ((n : ℂ) * h)) := hsumC.mul_left _
    simp only [hreal] at h1
    exact Complex.summable_ofReal.mp h1
  refine ⟨hsumR, ?_⟩
  have hint : ∫ x : ℝ, φ x = 1 := by
    have h1 : ∀ x : ℝ, φ x = (((π * (1 + x ^ 2))⁻¹ : ℝ) : ℂ) := by
      intro x
      simp only [φ]
      push_cast
      rfl
    simp only [h1]
    rw [integral_complex_ofReal]
    have h2 : ∫ x : ℝ, (π * (1 + x ^ 2))⁻¹ = 1 := by
      simp_rw [mul_inv]
      rw [integral_const_mul, integral_univ_inv_one_add_sq]
      field_simp
    rw [h2]
    simp
  have hlhs : (h : ℂ) * ∑' n : ℤ, φ ((n : ℂ) * h) =
      ((∑' n : ℤ, h / (π * (1 + ((n : ℝ) * h) ^ 2)) : ℝ) : ℂ) := by
    rw [← tsum_mul_left, Complex.ofReal_tsum]
    exact tsum_congr hreal
  rw [hlhs, hint] at hbound
  have he : 2 * (1 / π * π / (1 / 2)) / (Real.exp (2 * π * (1 / 2) / h) - 1) =
      4 / (Real.exp (π / h) - 1) := by
    have := Real.pi_pos
    have e1 : 2 * π * (1 / 2) / h = π / h := by ring
    rw [e1]
    field_simp
    ring
  rw [he] at hbound
  have h3 : ((∑' n : ℤ, h / (π * (1 + ((n : ℝ) * h) ^ 2)) : ℝ) : ℂ) - 1 =
      (((∑' n : ℤ, h / (π * (1 + ((n : ℝ) * h) ^ 2))) - 1 : ℝ) : ℂ) := by push_cast; ring
  rw [h3, Complex.norm_real, Real.norm_eq_abs] at hbound
  have := (abs_le.mp hbound).2
  linarith

end

end SparseHamiltonian.StripQuadrature
