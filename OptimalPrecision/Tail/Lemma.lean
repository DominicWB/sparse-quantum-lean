import OptimalPrecision.Tail.Jets
import OptimalPrecision.Tail.Joukowski
import OptimalPrecision.Taylor.Fejer
import Mathlib.Analysis.InnerProductSpace.Rayleigh

/-!
# Lemma `opt:lem:tail`: the operator tail estimate

Let `λ_1, …, λ_n` be clock weights with the conclusions of Theorem
`opt:thm:weights` (`n ≤ K_* qM`, `∑ |λ_j| ≤ A_*`, exact moments below degree `M`),
with `A_* = 3000` and `K_* = 27`. For operators with `0 ⪯ D ⪯ δI` and
`-D ⪯ C ⪯ D`, put `Q(C, D) = ∑_j λ_j Ces_j(F)`, `T = aq = q²M` and `b = Tδ`.
If `M ≥ 2K_*² b`, then

  `‖Q(C, D) - e^{-iTC}‖ ≤ 2(A_* + 1)(e² K_*² b / M)^M`   (`opt:eq:factorial-tail`).

Proof for `δ > 0` (`tail_estimate_of_pos`, as in the paper): along the scaling
`x ↦ (x C/δ, x D/δ)`, `0 ≤ x ≤ 1`, the transfer is contractive, so the Fejér contraction
bounds the clock polynomial `P(x)` by `A_*` on `[0, 1]`; the moments fix its first `M`
Taylor coefficients (`clockCoeff_eq`); the Joukowski bound and Cauchy's estimate on
`|z| = (M/n)²` control the remaining coefficients; and the exponential series supplies the
matching tail. For `δ = 0` the hypotheses force `C = D = 0` (`tail_estimate`).
-/

namespace OptimalPrecision.Tail

noncomputable section

open Complex Metric Finset Nat ContinuousLinearMap
open scoped Topology InnerProductSpace ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- A symmetric operator with `|Re⟪Tx, x⟫| ≤ c ‖x‖²` has norm at most `c`. -/
theorem norm_le_of_abs_re_inner_le {T : H →L[ℂ] H} (hT : T.IsSymmetric) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ x, |(⟪T x, x⟫_ℂ).re| ≤ c * ‖x‖ ^ 2) : ‖T‖ ≤ c := by
  rw [norm_eq_iSup_rayleighQuotient T hT]
  refine ciSup_le fun x => ?_
  rw [rayleighQuotient, reApplyInnerSelf, abs_div,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖x‖ ^ 2)]
  rcases eq_or_ne x 0 with rfl | hx
  · simp [hc]
  · have hx2 : 0 < ‖x‖ ^ 2 := by positivity
    rw [div_le_iff₀ hx2]
    exact h x

omit [CompleteSpace H] in
theorem re_inner_smul_one_sub (T : H →L[ℂ] H) (δ : ℝ) (x : H) :
    RCLike.re ⟪((δ : ℂ) • (1 : H →L[ℂ] H) - T) x, x⟫_ℂ = δ * ‖x‖ ^ 2 - RCLike.re ⟪T x, x⟫_ℂ := by
  simp only [sub_apply, smul_apply, one_apply_eq_self, inner_sub_left, inner_smul_left, map_sub,
    inner_self_eq_norm_sq_to_K, Complex.conj_ofReal]
  congr 1
  simp only [RCLike.re_to_complex]
  norm_cast
  rw [Complex.re_ofReal_mul]
  congr 1

omit [CompleteSpace H] in
/-- The bounds `0 ⪯ D ⪯ δI`, `-D ⪯ C ⪯ D` give `‖C‖ ≤ δ`. -/
theorem norm_le_of_sandwich {C D : H →L[ℂ] H} {δ : ℝ} (hδ : 0 ≤ δ) (hD0 : 0 ≤ D)
    (hDδ : D ≤ (δ : ℂ) • (1 : H →L[ℂ] H)) (hCl : -D ≤ C) (hCu : C ≤ D) : ‖C‖ ≤ δ := by
  rw [ContinuousLinearMap.le_def] at hDδ hCl hCu
  rw [ContinuousLinearMap.nonneg_iff_isPositive] at hD0
  have hsym : C.IsSymmetric := by
    have h := hD0.isSymmetric.sub hCu.isSymmetric
    have e : (D : H →ₗ[ℂ] H) - ((D - C : H →L[ℂ] H) : H →ₗ[ℂ] H) = (C : H →ₗ[ℂ] H) := by
      ext x; simp
    rw [← e]; exact h
  refine norm_le_of_abs_re_inner_le hsym hδ fun x => ?_
  have h1 := hCu.re_inner_nonneg_left x
  have h2 := hCl.re_inner_nonneg_left x
  have h3 := hDδ.re_inner_nonneg_left x
  rw [re_inner_smul_one_sub] at h3
  simp only [sub_neg_eq_add, sub_apply, add_apply, inner_sub_left, inner_add_left, map_sub,
    map_add] at h1 h2
  rw [abs_le]
  constructor <;> simp only [RCLike.re_to_complex] at h1 h2 h3 ⊢ <;> linarith

omit [CompleteSpace H] in
/-- The positivity hypotheses along the scaling `x ↦ (x C/δ, x D/δ)`. -/
theorem scaled_positive {C D : H →L[ℂ] H} {δ : ℝ} (hδ : 0 < δ)
    (hDδ : D ≤ (δ : ℂ) • (1 : H →L[ℂ] H)) (hCl : -D ≤ C) (hCu : C ≤ D) {x : ℝ} (hx0 : 0 ≤ x)
    (hx1 : x ≤ 1) :
    (1 - (x : ℂ) • ((δ⁻¹ : ℂ) • D)).IsPositive ∧
      ((x : ℂ) • ((δ⁻¹ : ℂ) • D) + (x : ℂ) • ((δ⁻¹ : ℂ) • C)).IsPositive ∧
      ((x : ℂ) • ((δ⁻¹ : ℂ) • D) - (x : ℂ) • ((δ⁻¹ : ℂ) • C)).IsPositive := by
  rw [ContinuousLinearMap.le_def] at hDδ hCl hCu
  have hc : (0 : ℂ) ≤ ((x / δ : ℝ) : ℂ) := by
    rw [Complex.zero_le_real]; positivity
  have hc1 : (0 : ℂ) ≤ ((1 - x : ℝ) : ℂ) := by
    rw [Complex.zero_le_real]; linarith
  have hδ' : (δ : ℂ) ≠ 0 := by exact_mod_cast hδ.ne'
  have e0 : ∀ T : H →L[ℂ] H, (x : ℂ) • ((δ⁻¹ : ℂ) • T) = ((x / δ : ℝ) : ℂ) • T := by
    intro T; rw [smul_smul]; push_cast; ring_nf
  refine ⟨?_, ?_, ?_⟩
  · have e : 1 - (x : ℂ) • ((δ⁻¹ : ℂ) • D) =
        ((1 - x : ℝ) : ℂ) • (1 : H →L[ℂ] H) + ((x / δ : ℝ) : ℂ) • ((δ : ℂ) • 1 - D) := by
      rw [e0, smul_sub, smul_smul]
      have : ((x / δ : ℝ) : ℂ) * (δ : ℂ) = (x : ℂ) := by push_cast; field_simp
      rw [this]
      push_cast
      module
    rw [e]
    exact (isPositive_one.smul_of_nonneg hc1).add (hDδ.smul_of_nonneg hc)
  · rw [e0, e0, ← smul_add]
    have : D + C = C - -D := by abel
    rw [this]
    exact hCl.smul_of_nonneg hc
  · rw [e0, e0, ← smul_sub]
    exact hCu.smul_of_nonneg hc

/-- `M! ≥ (M/e)^M`, in the form `b^M/M! ≤ (e b/M)^M`. -/
theorem pow_div_factorial_le {b : ℝ} (hb : 0 ≤ b) {M : ℕ} (hM : 0 < M) :
    b ^ M / (M ! : ℝ) ≤ (Real.exp 1 * b / M) ^ M := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have h := Real.pow_div_factorial_le_exp (M : ℝ) hM'.le M
  have hf : (0 : ℝ) < M ! := by exact_mod_cast Nat.factorial_pos M
  have hMM : (0 : ℝ) < (M : ℝ) ^ M := by positivity
  rw [div_le_iff₀ hf] at h ⊢
  calc b ^ M = (b / M) ^ M * (M : ℝ) ^ M := by rw [div_pow]; field_simp
    _ ≤ (b / M) ^ M * (Real.exp M * M !) := by
        apply mul_le_mul_of_nonneg_left h (by positivity)
    _ = (Real.exp 1 * b / M) ^ M * M ! := by
        rw [show Real.exp M = Real.exp 1 ^ M by rw [← Real.exp_nat_mul]; ring_nf, mul_div_assoc,
          mul_pow]
        ring

/-- Lemma `opt:lem:tail` for `δ > 0`, the case of the paper's proof (`C = δ C₀`,
`D = δ D₀`). -/
theorem tail_estimate_of_pos {q : ℝ} (hq : 1 ≤ q) {M : ℕ} (hM : 1 ≤ M) {n : ℕ} {lam : ℕ → ℝ}
    (hn : (n : ℝ) ≤ 27 * (q * M)) (hlam : ∑ j ∈ Icc 1 n, |lam j| ≤ 3000)
    (hmom : ∀ k m : ℕ, m ≤ k → k < M →
      ∑ j ∈ Icc 1 n, (lam j : ℂ) *
          ces (fun w => Complex.exp (-(((q * M : ℝ) : ℂ) * xi w)) * Rfun q w ^ k * xi w ^ m) j =
        if m = 0 then 1 else 0)
    {C D : H →L[ℂ] H} {δ : ℝ} (hδ : 0 < δ) (hD0 : 0 ≤ D)
    (hDδ : D ≤ (δ : ℂ) • (1 : H →L[ℂ] H)) (hCl : -D ≤ C) (hCu : C ≤ D)
    (hMb : 2 * 27 ^ 2 * (q ^ 2 * M * δ) ≤ M) :
    ‖∑ j ∈ Icc 1 n, (lam j : ℂ) • ces (Fop (q * M) q C D) j -
        NormedSpace.exp ((-(I * ((q ^ 2 * M : ℝ) : ℂ))) • C)‖ ≤
      2 * (3000 + 1) * (Real.exp 2 * 27 ^ 2 * (q ^ 2 * M * δ) / M) ^ M := by
  have hq0 : 0 < q := by linarith
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := by linarith
  set a : ℝ := q * M with ha
  set b : ℝ := q ^ 2 * M * δ with hb
  have hb0 : 0 ≤ b := by positivity
  set X : ℝ := (Real.exp 2 * 27 ^ 2 * b / M) ^ M with hX
  have hX0 : 0 ≤ X := by positivity
  -- moments in clock form
  have hmom' : ∀ k s, s ≤ k → k < M → mom a q n lam k s = if s = 0 then 1 else 0 := by
    intro k s hsk hkM
    rw [← hmom k s hsk hkM]
    rfl
  -- the horizon is at least `M`
  have hMn : M ≤ n := by
    by_contra h
    push Not at h
    have h1 := hmom' n 0 (Nat.zero_le n) h
    rw [if_pos rfl, mom, Finset.sum_eq_zero] at h1
    · exact zero_ne_one h1
    · intro j hj
      rw [ces_vRx_eq_zero hq0 a 0 (Finset.mem_Icc.mp hj).2, mul_zero]
  -- normalized operators and the clock polynomial
  set C₀ : H →L[ℂ] H := (δ⁻¹ : ℂ) • C
  set D₀ : H →L[ℂ] H := (δ⁻¹ : ℂ) • D
  have hδ' : (δ : ℂ) ≠ 0 := by exact_mod_cast hδ.ne'
  have hC : C = (δ : ℂ) • C₀ := by simp only [C₀, smul_smul, mul_inv_cancel₀ hδ', one_smul]
  have hD : D = (δ : ℂ) • D₀ := by simp only [D₀, smul_smul, mul_inv_cancel₀ hδ', one_smul]
  set P : ℕ → (H →L[ℂ] H) := clockCoeff a q n lam C₀ D₀
  have hpoly : ∀ z : ℂ, clock a q n lam (z • C₀) (z • D₀) = polyEval n P z :=
    fun z => clock_smul hq0 a n lam C₀ D₀ z
  -- the polynomial is bounded by `A_*` on `[0, 1]`
  have hA : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → ‖polyEval n P (x : ℂ)‖ ≤ 3000 := by
    intro x hx0 hx1
    obtain ⟨p1, p2, p3⟩ := scaled_positive hδ hDδ hCl hCu hx0 hx1
    rw [← hpoly, clock]
    have hces : ∀ j, ‖ces (Fop a q ((x : ℂ) • C₀) ((x : ℂ) • D₀)) j‖ ≤ 1 := by
      intro j
      refine norm_ces_le (differentiableOn_Fop hq0 _ _) (fun w hw => ?_) j
      exact norm_Fop_le_one (by positivity) hq0 p1 p2 p3 hw
    calc ‖∑ j ∈ Icc 1 n, (lam j : ℂ) • ces (Fop a q ((x : ℂ) • C₀) ((x : ℂ) • D₀)) j‖ ≤
        ∑ j ∈ Icc 1 n, ‖(lam j : ℂ) • ces (Fop a q ((x : ℂ) • C₀) ((x : ℂ) • D₀)) j‖ :=
          norm_sum_le _ _
      _ ≤ ∑ j ∈ Icc 1 n, |lam j| := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
          calc |lam j| * ‖ces (Fop a q ((x : ℂ) • C₀) ((x : ℂ) • D₀)) j‖ ≤ |lam j| * 1 :=
                mul_le_mul_of_nonneg_left (hces j) (abs_nonneg _)
            _ = |lam j| := mul_one _
      _ ≤ 3000 := hlam
  -- the ratio condition
  have hn0 : 0 < n := lt_of_lt_of_le (by omega) hMn
  have hratio : (n : ℝ) ^ 2 * δ / (M : ℝ) ^ 2 ≤ 27 ^ 2 * b / M := by
    have hn2 : (n : ℝ) ^ 2 ≤ (27 * (q * M)) ^ 2 := pow_le_pow_left₀ (by positivity) hn 2
    have e : 27 ^ 2 * b / M = (27 * (q * M)) ^ 2 * δ / (M : ℝ) ^ 2 := by
      rw [hb]; field_simp
    rw [e]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_right hn2 hδ.le
  have hhalf : 27 ^ 2 * b / M ≤ 1 / 2 := by
    rw [div_le_iff₀ hM0]; linarith
  -- the tail of the polynomial
  have htail := norm_tail_le n M P hA (by omega) hMn hδ.le (hratio.trans hhalf)
  -- the jets
  have hjets : ∀ m, m < M →
      (δ : ℂ) ^ m • P m = ((m ! : ℂ)⁻¹) • ((-(I * ((q ^ 2 * M : ℝ) : ℂ))) • C) ^ m := by
    intro m hm
    have h := clockCoeff_eq a n lam C₀ D₀ (q := q) (m := m) (fun s hs => hmom' m s hs hm)
    simp only [P]
    rw [h, smul_comm, ← smul_pow, smul_comm (δ : ℂ), ← hC]
    congr 3
    rw [ha]
    push_cast
    ring
  -- assemble
  have hQ : ∑ j ∈ Icc 1 n, (lam j : ℂ) • ces (Fop (q * M) q C D) j = polyEval n P (δ : ℂ) := by
    rw [← hpoly, hC, hD]
    rfl
  have hsplit : polyEval n P (δ : ℂ) = ∑ m ∈ range M, (δ : ℂ) ^ m • P m +
      ∑ m ∈ Ico M n, (δ : ℂ) ^ m • P m := by
    rw [polyEval, Finset.sum_range_add_sum_Ico _ hMn]
  set Y : H →L[ℂ] H := (-(I * ((q ^ 2 * M : ℝ) : ℂ))) • C
  have hjsum : ∑ m ∈ range M, (δ : ℂ) ^ m • P m = ∑ m ∈ range M, ((m ! : ℂ)⁻¹) • Y ^ m :=
    Finset.sum_congr rfl fun m hm => hjets m (Finset.mem_range.mp hm)
  -- exponential tail
  have hY : ‖Y‖ ≤ b := by
    have hCδ := norm_le_of_sandwich hδ.le hD0 hDδ hCl hCu
    rw [norm_smul, norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc q ^ 2 * M * ‖C‖ ≤ q ^ 2 * M * δ := mul_le_mul_of_nonneg_left hCδ (by positivity)
      _ = b := rfl
  obtain ⟨k, hk⟩ : ∃ k, M = k + 1 := ⟨M - 1, by omega⟩
  have hexp := norm_exp_sub_sum_le' Y k
  rw [← hk] at hexp
  have hexp2 : ‖NormedSpace.exp Y - ∑ m ∈ range M, ((m ! : ℂ)⁻¹) • Y ^ m‖ ≤ X := by
    refine hexp.trans ?_
    have h1 : ‖Y‖ ^ M / (M ! : ℝ) ≤ b ^ M / (M ! : ℝ) :=
      div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hY M) (by positivity)
    have h2 := pow_div_factorial_le hb0 (show 0 < M by omega)
    have h3 : Real.exp ‖Y‖ ≤ Real.exp (b / M) ^ M := by
      rw [← Real.exp_nat_mul, mul_div_cancel₀ _ hM0.ne']
      exact Real.exp_le_exp.mpr hY
    have h4 : Real.exp (b / M) ≤ Real.exp 1 * 27 ^ 2 := by
      have : b / M ≤ 1 := by
        rw [div_le_one hM0]; linarith
      calc Real.exp (b / M) ≤ Real.exp 1 := Real.exp_le_exp.mpr this
        _ ≤ Real.exp 1 * 27 ^ 2 := le_mul_of_one_le_right (Real.exp_pos 1).le (by norm_num)
    calc ‖Y‖ ^ M / (M ! : ℝ) * Real.exp ‖Y‖ ≤ (Real.exp 1 * b / M) ^ M * Real.exp (b / M) ^ M :=
          mul_le_mul (h1.trans h2) h3 (Real.exp_pos _).le (by positivity)
      _ = (Real.exp 1 * b / M * Real.exp (b / M)) ^ M := by rw [mul_pow]
      _ ≤ (Real.exp 1 * b / M * (Real.exp 1 * 27 ^ 2)) ^ M := by
          apply pow_le_pow_left₀ (by positivity)
          exact mul_le_mul_of_nonneg_left h4 (by positivity)
      _ = X := by
          rw [hX, show Real.exp 2 = Real.exp 1 * Real.exp 1 by rw [← Real.exp_add]; norm_num]
          ring_nf
  -- the polynomial tail in terms of `b`
  have htail2 : ‖∑ m ∈ Ico M n, (δ : ℂ) ^ m • P m‖ ≤ 2 * 3000 * X := by
    refine htail.trans ?_
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply pow_le_pow_left₀ (by positivity)
    have e1 : Real.exp 2 * (n : ℝ) ^ 2 * δ / (M : ℝ) ^ 2 =
        Real.exp 2 * ((n : ℝ) ^ 2 * δ / (M : ℝ) ^ 2) := by ring
    have e2 : Real.exp 2 * 27 ^ 2 * b / M = Real.exp 2 * (27 ^ 2 * b / M) := by ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_left hratio (Real.exp_pos 2).le
  rw [hQ, hsplit, hjsum]
  calc ‖∑ m ∈ range M, ((m ! : ℂ)⁻¹) • Y ^ m + ∑ m ∈ Ico M n, (δ : ℂ) ^ m • P m -
        NormedSpace.exp Y‖ =
      ‖∑ m ∈ Ico M n, (δ : ℂ) ^ m • P m -
        (NormedSpace.exp Y - ∑ m ∈ range M, ((m ! : ℂ)⁻¹) • Y ^ m)‖ := by
        congr 1; abel
    _ ≤ ‖∑ m ∈ Ico M n, (δ : ℂ) ^ m • P m‖ +
        ‖NormedSpace.exp Y - ∑ m ∈ range M, ((m ! : ℂ)⁻¹) • Y ^ m‖ := norm_sub_le _ _
    _ ≤ 2 * 3000 * X + X := add_le_add htail2 hexp2
    _ ≤ 2 * (3000 + 1) * X := by nlinarith

/-- **Lemma `opt:lem:tail`**, the operator tail estimate (`opt:eq:factorial-tail`), with
`A_* = 3000`, `K_* = 27`, `T = q²M` and `b = Tδ`, for every `δ ≥ 0`. For `δ = 0` the
hypotheses force `C = D = 0`, and the moment `k = m = 0` makes the clock exact. -/
theorem tail_estimate {q : ℝ} (hq : 1 ≤ q) {M : ℕ} (hM : 1 ≤ M) {n : ℕ} {lam : ℕ → ℝ}
    (hn : (n : ℝ) ≤ 27 * (q * M)) (hlam : ∑ j ∈ Icc 1 n, |lam j| ≤ 3000)
    (hmom : ∀ k m : ℕ, m ≤ k → k < M →
      ∑ j ∈ Icc 1 n, (lam j : ℂ) *
          ces (fun w => Complex.exp (-(((q * M : ℝ) : ℂ) * xi w)) * Rfun q w ^ k * xi w ^ m) j =
        if m = 0 then 1 else 0)
    {C D : H →L[ℂ] H} {δ : ℝ} (hδ : 0 ≤ δ) (hD0 : 0 ≤ D)
    (hDδ : D ≤ (δ : ℂ) • (1 : H →L[ℂ] H)) (hCl : -D ≤ C) (hCu : C ≤ D)
    (hMb : 2 * 27 ^ 2 * (q ^ 2 * M * δ) ≤ M) :
    ‖∑ j ∈ Icc 1 n, (lam j : ℂ) • ces (Fop (q * M) q C D) j -
        NormedSpace.exp ((-(I * ((q ^ 2 * M : ℝ) : ℂ))) • C)‖ ≤
      2 * (3000 + 1) * (Real.exp 2 * 27 ^ 2 * (q ^ 2 * M * δ) / M) ^ M := by
  rcases hδ.lt_or_eq with hδ | rfl
  · exact tail_estimate_of_pos hq hM hn hlam hmom hδ hD0 hDδ hCl hCu hMb
  have hD : D = 0 := le_antisymm (by simpa using hDδ) hD0
  subst hD
  have hC : C = 0 := le_antisymm (by simpa using hCu) (by simpa using hCl)
  subst hC
  have hq0 : 0 < q := by linarith
  have hF : Fop (q * M) q (0 : H →L[ℂ] H) 0 =
      fun w => vRx (q * M) q 0 0 w • (1 : H →L[ℂ] H) := by
    funext w
    rw [Fop_eq]
    simp [Xop, vRx]
  have h0 : ∑ j ∈ Icc 1 n, (lam j : ℂ) * ces (vRx (q * M) q 0 0) j = 1 := by
    have h := hmom 0 0 le_rfl (by omega)
    rw [if_pos rfl] at h
    exact h
  have han : AnalyticAt ℂ (vRx (q * M) q 0 0) 0 := analyticAt_vRx hq0 _ 0 0 (by simp)
  simp_rw [hF, ces_smul_const han, smul_smul, ← Finset.sum_smul]
  rw [h0, one_smul, smul_zero, NormedSpace.exp_zero, sub_self, norm_zero]
  positivity

end

end OptimalPrecision.Tail
