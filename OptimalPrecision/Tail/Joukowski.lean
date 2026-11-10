import OptimalPrecision.Taylor.Estimates
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Growth of a polynomial bounded on `[0, 1]` (the Joukowski bound)

For a polynomial `p(z) = ∑_{m < n} z^m P_m` with coefficients in a complex Banach
space, `‖p(x)‖ ≤ A` on `0 ≤ x ≤ 1` implies (`opt:eq:joukowski`)

  `‖p(z)‖ ≤ A exp(2 (n-1) √|z|)`.

The proof applies the maximum principle to the polynomial
`g(v) = ∑_m v^{n-1-m} ((v + 1)²/4)^m P_m = v^{n-1} p((2 + v + 1/v)/4)` on the
unit disk: on `|v| = 1` the argument `(2 + v + 1/v)/4 = (1 + Re v)/2` lies in
`[0, 1]`. A point `z` is reached from the root `v` of `v + 1/v = 4z - 2` with
`|v| ≤ 1`, and `|1/v| ≤ (√(1+|z|) + √|z|)² ≤ e^{2√|z|}`.

Cauchy's estimate on the circle `|z| = (M/n)²` then gives the factorial tail
(`norm_tail_le`).
-/

namespace OptimalPrecision

noncomputable section

open Complex Metric Finset Nat
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- The polynomial `p(z) = ∑_{m < n} z^m P_m`. -/
def polyEval (n : ℕ) (P : ℕ → E) (z : ℂ) : E := ∑ m ∈ range n, z ^ m • P m

omit [CompleteSpace E] in
theorem differentiable_polyEval (n : ℕ) (P : ℕ → E) : Differentiable ℂ (polyEval n P) := by
  unfold polyEval
  exact Differentiable.fun_sum fun m _ => (differentiable_id.pow m).smul_const (P m)

theorem coeff_polyEval (n : ℕ) (P : ℕ → E) {m : ℕ} (hm : m < n) : coeff (polyEval n P) m = P m := by
  have hpow : ∀ i : ℕ, AnalyticAt ℂ (fun z : ℂ => z ^ i) 0 := fun i => analyticAt_id.pow i
  have han : ∀ i ∈ range n, AnalyticAt ℂ (fun z : ℂ => z ^ i • P i) 0 :=
    fun i _ => (hpow i).smul analyticAt_const
  unfold polyEval
  rw [coeff_sum _ han, Finset.sum_eq_single m]
  · rw [coeff_smul_const (hpow m), coeff_pow, if_pos rfl, one_smul]
  · intro i _ hi; rw [coeff_smul_const (hpow i), coeff_pow, if_neg (Ne.symm hi), zero_smul]
  · intro h; exact absurd (Finset.mem_range.mpr hm) h

/-! ### Elementary inequalities -/

/-- `(√(1+ρ) + √ρ)² = 1 + 2ρ + 2√(ρ² + ρ) ≤ e^{2√ρ}`. -/
theorem joukowski_radius_le {ρ : ℝ} (hρ : 0 ≤ ρ) :
    1 + 2 * ρ + 2 * Real.sqrt (ρ ^ 2 + ρ) ≤ Real.exp (2 * Real.sqrt ρ) := by
  set s := Real.sqrt ρ
  have hs : 0 ≤ s := Real.sqrt_nonneg ρ
  have hs2 : s ^ 2 = ρ := Real.sq_sqrt hρ
  have h1 : Real.sqrt (ρ ^ 2 + ρ) = s * Real.sqrt (1 + ρ) := by
    rw [show ρ ^ 2 + ρ = ρ * (1 + ρ) by ring, Real.sqrt_mul hρ]
  have h2 : Real.sqrt (1 + ρ) ≤ 1 + ρ / 2 := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith
  have h3 : Real.sqrt (1 + ρ) + s ≤ Real.exp s := by
    have := Real.quadratic_le_exp_of_nonneg hs
    nlinarith
  have h4 : 0 ≤ Real.sqrt (1 + ρ) := Real.sqrt_nonneg _
  have h5 : Real.sqrt (1 + ρ) ^ 2 = 1 + ρ := Real.sq_sqrt (by positivity)
  calc 1 + 2 * ρ + 2 * Real.sqrt (ρ ^ 2 + ρ) = (Real.sqrt (1 + ρ) + s) ^ 2 := by
        rw [h1]; nlinarith
    _ ≤ Real.exp s ^ 2 := pow_le_pow_left₀ (by positivity) h3 2
    _ = Real.exp (2 * s) := by rw [← Real.exp_nat_mul]; ring_nf

/-- If `(R - 1)² ≤ 4ρR`, then `R ≤ 1 + 2ρ + 2√(ρ² + ρ)`. -/
theorem le_joukowski_radius {R ρ : ℝ} (hρ : 0 ≤ ρ) (h : (R - 1) ^ 2 ≤ 4 * ρ * R) :
    R ≤ 1 + 2 * ρ + 2 * Real.sqrt (ρ ^ 2 + ρ) := by
  set t := Real.sqrt (ρ ^ 2 + ρ)
  have ht : 0 ≤ t := Real.sqrt_nonneg _
  have ht2 : t ^ 2 = ρ ^ 2 + ρ := Real.sq_sqrt (by positivity)
  by_contra hcon
  push Not at hcon
  have h1 : 2 * t < R - 1 - 2 * ρ := by linarith
  have h2 : (2 * t) ^ 2 < (R - 1 - 2 * ρ) ^ 2 := by
    apply pow_lt_pow_left₀ h1 (by positivity) (by norm_num)
  nlinarith

/-! ### The Joukowski bound -/

omit [CompleteSpace E] in
/-- **Growth of a polynomial bounded on `[0, 1]`** (`opt:eq:joukowski`). -/
theorem norm_polyEval_le (n : ℕ) (P : ℕ → E) {A : ℝ}
    (hA : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → ‖polyEval n P (x : ℂ)‖ ≤ A) (z : ℂ) :
    ‖polyEval n P z‖ ≤ A * Real.exp (2 * ((n : ℝ) - 1) * Real.sqrt ‖z‖) := by
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0 le_rfl zero_le_one)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [polyEval]; positivity
  set d := n - 1 with hd
  have hnd : n = d + 1 := by omega
  -- the auxiliary polynomial `g(v) = v^d p((2 + v + 1/v)/4)`
  set g : ℂ → E := fun v => ∑ m ∈ range n, (v ^ (d - m) * ((v ^ 2 + 2 * v + 1) / 4) ^ m) • P m
    with hg
  have hgd : Differentiable ℂ g := by
    rw [hg]
    exact Differentiable.fun_sum fun m _ =>
      ((differentiable_id.pow _).mul ((((differentiable_id.pow 2).add
        (differentiable_const _ |>.mul differentiable_id)).add
          (differentiable_const _)).div_const _ |>.pow _)).smul_const _
  have hg_eq : ∀ v : ℂ, v ≠ 0 → g v = v ^ d • polyEval n P ((2 + v + v⁻¹) / 4) := by
    intro v hv
    rw [hg, polyEval, Finset.smul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hmd : m ≤ d := by have := Finset.mem_range.mp hm; omega
    rw [smul_smul]
    congr 1
    have e : (v ^ 2 + 2 * v + 1) / 4 = v * ((2 + v + v⁻¹) / 4) := by field_simp; ring
    rw [e, mul_pow, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hmd]
  -- on the unit circle
  have hcircle : ∀ v ∈ frontier (ball (0 : ℂ) 1), ‖g v‖ ≤ A := by
    intro v hv
    rw [frontier_ball (0 : ℂ) one_ne_zero, mem_sphere_zero_iff_norm] at hv
    have hv0 : v ≠ 0 := by intro h; rw [h, norm_zero] at hv; norm_num at hv
    have hinv : v⁻¹ = (starRingEnd ℂ) v := by
      have hns : normSq v = 1 := by rw [Complex.normSq_eq_norm_sq, hv, one_pow]
      rw [inv_def, hns, inv_one, Complex.ofReal_one, mul_one]
    set x : ℝ := (1 + v.re) / 2
    have hx : (2 + v + v⁻¹) / 4 = (x : ℂ) := by
      rw [hinv]
      apply Complex.ext
      · simp [x]; ring
      · simp [x]
    have hre : |v.re| ≤ 1 := (Complex.abs_re_le_norm v).trans hv.le
    have hx0 : 0 ≤ x := by simp only [x]; linarith [(abs_le.mp hre).1]
    have hx1 : x ≤ 1 := by simp only [x]; linarith [(abs_le.mp hre).2]
    rw [hg_eq v hv0, hx, norm_smul, norm_pow, hv, one_pow, one_mul]
    exact hA x hx0 hx1
  have hdisk : ∀ v : ℂ, ‖v‖ ≤ 1 → ‖g v‖ ≤ A := by
    intro v hv
    exact Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball
      hgd.diffContOnCl hcircle (by rw [closure_ball (0 : ℂ) one_ne_zero]; simpa using hv)
  -- a root `v` of `v + 1/v = 4z - 2` with `|v| ≤ 1`
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_eq_mul_self ((4 * z - 2) ^ 2 - 4)
  set v₁ := ((4 * z - 2) + s) / 2
  set v₂ := ((4 * z - 2) - s) / 2
  have hprod : v₁ * v₂ = 1 := by simp only [v₁, v₂]; linear_combination (1 / 4 : ℂ) * hs
  have hsum : v₁ + v₂ = 4 * z - 2 := by simp only [v₁, v₂]; ring
  have key : ∀ v u : ℂ, v * u = 1 → v + u = 4 * z - 2 → ‖v‖ ≤ 1 →
      ‖polyEval n P z‖ ≤ A * Real.exp (2 * ((n : ℝ) - 1) * Real.sqrt ‖z‖) := by
    intro v u hvu hvs hv
    have hv0 : v ≠ 0 := by intro h; rw [h, zero_mul] at hvu; exact zero_ne_one hvu
    have hu : u = v⁻¹ := eq_inv_of_mul_eq_one_right hvu
    have hz : (2 + v + v⁻¹) / 4 = z := by rw [← hu]; linear_combination (1 / 4 : ℂ) * hvs
    have hgv := hdisk v hv
    rw [hg_eq v hv0, hz, norm_smul, norm_pow] at hgv
    have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv0
    -- `‖u‖ ≥ 1` and `(‖u‖ - 1)² ≤ 4‖z‖‖u‖`
    have hnu : ‖u‖ * ‖v‖ = 1 := by rw [← norm_mul, mul_comm, hvu, norm_one]
    have hu1 : 1 ≤ ‖u‖ := by
      by_contra h; push Not at h; nlinarith [norm_nonneg u]
    have hu0 : u ≠ 0 := by intro h; rw [h, norm_zero] at hu1; norm_num at hu1
    have hquad : (u + 1) ^ 2 = 4 * z * u := by
      have : u + v = 4 * z - 2 := by rw [add_comm]; exact hvs
      linear_combination u * this - hvu
    have hR : (‖u‖ - 1) ^ 2 ≤ 4 * ‖z‖ * ‖u‖ := by
      have h1 : ‖u‖ - 1 ≤ ‖u + 1‖ := by
        have := norm_sub_norm_le u (-1); rw [sub_neg_eq_add, norm_neg, norm_one] at this; exact this
      have h2 : ‖u + 1‖ ^ 2 = 4 * ‖z‖ * ‖u‖ := by
        rw [← norm_pow, hquad, norm_mul, norm_mul]; norm_num
      calc (‖u‖ - 1) ^ 2 ≤ ‖u + 1‖ ^ 2 := pow_le_pow_left₀ (by linarith) h1 2
        _ = 4 * ‖z‖ * ‖u‖ := h2
    have hrad := (le_joukowski_radius (norm_nonneg z) hR).trans
      (joukowski_radius_le (norm_nonneg z))
    -- `‖p(z)‖ = ‖u‖^d ‖g(v)‖`
    have hpz : ‖polyEval n P z‖ ≤ ‖u‖ ^ d * A := by
      have e : ‖polyEval n P z‖ = ‖u‖ ^ d * (‖v‖ ^ d * ‖polyEval n P z‖) := by
        rw [← mul_assoc, ← mul_pow, hnu, one_pow, one_mul]
      rw [e]; exact mul_le_mul_of_nonneg_left hgv (by positivity)
    calc ‖polyEval n P z‖ ≤ ‖u‖ ^ d * A := hpz
      _ ≤ Real.exp (2 * Real.sqrt ‖z‖) ^ d * A :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hrad d) hA0
      _ = A * Real.exp (2 * ((n : ℝ) - 1) * Real.sqrt ‖z‖) := by
          rw [← Real.exp_nat_mul, hnd]; push_cast; ring_nf
  by_cases h1 : ‖v₁‖ ≤ 1
  · exact key v₁ v₂ hprod hsum h1
  · push Not at h1
    have h2 : ‖v₂‖ ≤ 1 := by
      have : ‖v₁‖ * ‖v₂‖ = 1 := by rw [← norm_mul, hprod, norm_one]
      by_contra h; push Not at h; nlinarith [norm_nonneg v₂]
    exact key v₂ v₁ (by rw [mul_comm]; exact hprod) (by rw [add_comm]; exact hsum) h2

/-! ### The factorial tail -/

/-- **Tail of a polynomial bounded on `[0, 1]`**: with `ρ = (M/n)²` and
`n² δ / M² ≤ 1/2`, `‖∑_{M ≤ m < n} δ^m P_m‖ ≤ 2A (e² n² δ / M²)^M`. -/
theorem norm_tail_le (n M : ℕ) (P : ℕ → E) {A : ℝ}
    (hA : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → ‖polyEval n P (x : ℂ)‖ ≤ A) (hM : 0 < M) (hMn : M ≤ n)
    {δ : ℝ} (hδ : 0 ≤ δ) (hratio : (n : ℝ) ^ 2 * δ / (M : ℝ) ^ 2 ≤ 1 / 2) :
    ‖∑ m ∈ Ico M n, (δ : ℂ) ^ m • P m‖ ≤
      2 * A * (Real.exp 2 * (n : ℝ) ^ 2 * δ / (M : ℝ) ^ 2) ^ M := by
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0 le_rfl zero_le_one)
  have hn : 0 < n := lt_of_lt_of_le hM hMn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  set ρ : ℝ := ((M : ℝ) / n) ^ 2 with hρ
  have hρ0 : 0 < ρ := by positivity
  have hsqrt : Real.sqrt ρ = (M : ℝ) / n := by rw [hρ, Real.sqrt_sq (by positivity)]
  -- coefficient bound from Cauchy's estimate on `|z| = ρ`
  set B := A * Real.exp (2 * (M : ℝ)) with hB
  have hcircle : ∀ z ∈ sphere (0 : ℂ) ρ, ‖polyEval n P z‖ ≤ B := by
    intro z hz
    rw [mem_sphere_zero_iff_norm] at hz
    refine (norm_polyEval_le n P hA z).trans ?_
    rw [hB, hz, hsqrt]
    apply mul_le_mul_of_nonneg_left _ hA0
    apply Real.exp_le_exp.mpr
    have : ((n : ℝ) - 1) * ((M : ℝ) / n) ≤ M := by
      rw [sub_mul, one_mul, mul_div_cancel₀ _ hn'.ne']
      have : 0 ≤ (M : ℝ) / n := by positivity
      linarith
    linarith
  have hcoeff : ∀ m, m < n → ‖P m‖ ≤ B / ρ ^ m := by
    intro m hm
    rw [← coeff_polyEval n P hm]
    exact norm_coeff_le hρ0 (differentiable_polyEval n P).diffContOnCl hcircle m
  -- geometric sum with ratio `δ/ρ ≤ 1/2`
  set r := δ / ρ with hr
  have hr_eq : r = (n : ℝ) ^ 2 * δ / (M : ℝ) ^ 2 := by
    rw [hr, hρ, div_pow]; field_simp
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r ≤ 1 / 2 := by rw [hr_eq]; exact hratio
  have hterm : ∀ m ∈ Ico M n, ‖(δ : ℂ) ^ m • P m‖ ≤ B * r ^ m := by
    intro m hm
    have hmn := (Finset.mem_Ico.mp hm).2
    rw [norm_smul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hδ]
    calc δ ^ m * ‖P m‖ ≤ δ ^ m * (B / ρ ^ m) :=
          mul_le_mul_of_nonneg_left (hcoeff m hmn) (by positivity)
      _ = B * r ^ m := by rw [hr, div_pow]; field_simp
  have hgeom : ∑ m ∈ Ico M n, r ^ m ≤ r ^ M / (1 - r) :=
    geom_sum_Ico_le_of_lt_one hr0 (by linarith)
  have hB0 : 0 ≤ B := by positivity
  calc ‖∑ m ∈ Ico M n, (δ : ℂ) ^ m • P m‖ ≤ ∑ m ∈ Ico M n, ‖(δ : ℂ) ^ m • P m‖ :=
        norm_sum_le _ _
    _ ≤ ∑ m ∈ Ico M n, B * r ^ m := Finset.sum_le_sum hterm
    _ = B * ∑ m ∈ Ico M n, r ^ m := by rw [Finset.mul_sum]
    _ ≤ B * (r ^ M / (1 - r)) := mul_le_mul_of_nonneg_left hgeom hB0
    _ ≤ B * (2 * r ^ M) := by
        apply mul_le_mul_of_nonneg_left _ hB0
        rw [div_le_iff₀ (by linarith)]
        nlinarith [pow_nonneg hr0 M]
    _ = 2 * A * (Real.exp 2 * r) ^ M := by
        rw [hB, mul_pow, ← Real.exp_nat_mul]; ring_nf
    _ = 2 * A * (Real.exp 2 * (n : ℝ) ^ 2 * δ / (M : ℝ) ^ 2) ^ M := by
        rw [hr_eq]; ring_nf

end

end OptimalPrecision
