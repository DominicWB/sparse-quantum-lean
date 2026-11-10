import OptimalPrecision.Weights.Exact
import OptimalPrecision.Weights.ChiBound

/-!
# Theorem `opt:thm:weights`: an explicit finite moment construction

For every real `q ≥ 1` and integer `M ≥ 1`, with `a = qM` and `V = e^{-aξ}`,
there are real weights `λ_1, …, λ_n` with

  `n ≤ 27a`,  `∑_j |λ_j| ≤ 3000`,  `∑_j λ_j Ces_j(V R^k ξ^m) = δ_{m0}` (`0 ≤ m ≤ k < M`).

The weights are `λ_{k+1} = ((k+1)/2)(-1)^k β_k` (`opt:eq:weights`), where `β` are
the Laguerre coordinates of `ψ = 4∫_0^∞ e^{-v} φ(t+v) dv` and `φ` is the
difference of the delayed gamma mixtures (`opt:eq:phi`).

* exact moments: `lamSum_moment` (`Weights.Exact`);
* clock length: `Gamma.Dstar_add_one_le`;
* total variation: `sum_abs_le` (Parseval and Cauchy–Schwarz,
  `Weights.LaguerreL2`) and `J_chi_le` (`Weights.ChiBound`).
-/

namespace OptimalPrecision

noncomputable section

open Nat Finset Polynomial
open scoped Polynomial
open ExpPoly Dual Gamma

/-! ### `(𝔏 + 1)ψ = 4(tφ + tφ' + φ)` -/

/-- With `Q = 4 (1 + x)^{-1} P`, `(𝔏 + 1) Q = 4 (X P' + P)`. -/
theorem Lop_add_self_op (P : ℝ[X]) :
    Lop ((4 : ℝ) • op ((1 + xs : PowerSeries ℝ)⁻¹) P) +
        (4 : ℝ) • op ((1 + xs : PowerSeries ℝ)⁻¹) P =
      (4 : ℝ) • (X * derivative P + P) := by
  set R0 := op ((1 + xs : PowerSeries ℝ)⁻¹) P
  have h2 : PowerSeries.constantCoeff (1 + xs : PowerSeries ℝ) ≠ 0 := by
    rw [map_add, map_one, constantCoeff_xs]; norm_num
  have hP : P = 2 * R0 - derivative R0 := by
    have := op_inv_cancel h2 P
    rw [op_add_left, op_one, op_xs] at this
    rw [← this]; ring
  rw [map_smul, ← smul_add]
  congr 1
  rw [hP, Lop_apply]
  simp only [derivative_sub, derivative_mul, derivative_ofNat, zero_mul, zero_add]
  ring

/-! ### The weights -/

/-- The clock length `n = D_* + 1`. -/
def clockLength (q : ℝ) (M : ℕ) : ℕ := Dstar q M + 1

/-- The signed clock weights `λ_j` of `opt:eq:weights`. -/
def clockWeight (q : ℝ) (M : ℕ) (j : ℕ) : ℝ := lamOf (clockLength q M) (beta q M) j

theorem sum_abs_lamOf (n : ℕ) (β : ℕ → ℝ) :
    ∑ j ∈ Icc 1 n, |lamOf n β j| = ∑ k ∈ range n, ((k + 1 : ℝ) / 2) * |β k| := by
  have hIcc : Icc 1 n = (range n).map ⟨(· + 1), add_left_injective 1⟩ := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk]
    constructor
    · intro h; exact ⟨j - 1, by omega, by omega⟩
    · rintro ⟨k, hk, rfl⟩; omega
  rw [hIcc, Finset.sum_map]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn := Finset.mem_range.mp hk
  simp only [Function.Embedding.coeFn_mk, lamOf, if_pos (show 1 ≤ k + 1 ∧ k + 1 ≤ n by omega),
    Nat.add_sub_cancel]
  rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, mul_one,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) / 2)]
  push_cast
  ring

variable {q : ℝ} {M : ℕ}

/-- The `L²` bound for `χ` with the gamma-mixture data. -/
theorem J_chi_mixture_le (hq : 1 ≤ q) (hM : 1 ≤ M) :
    J ((X * derivative (PR q M) + PR q M) * (X * derivative (PR q M) + PR q M)) ≤
      6512 / (q * M) := by
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  set a : ℝ := q * M with ha_def
  have ha : 1 ≤ a := by nlinarith
  have ha0 : 0 < a := by linarith
  set N := Dstar q M
  set l : ℕ := ell a
  have hlpos : 0 < l := ell_pos ha0
  have hla : a ≤ (l : ℝ) := Nat.le_ceil a
  have hl0 : (0 : ℝ) < l := by linarith
  set L : ℝ := (l : ℝ)⁻¹ with hL
  have hL0 : 0 ≤ L := by positivity
  set d : ℕ → ℝ := fun j => (diffR q M).coeff j with hd
  set w : ℕ → ℝ := fun j => L * ((C2 q M).coeff j + (C1 q M).coeff j) with hw
  have hdj : ∀ j, d j = L * ((C2 q M).coeff j - (C1 q M).coeff j) := by
    intro j; simp only [hd, diffR, coeff_C_mul, Polynomial.coeff_sub, hL]; rfl
  have hdeg1 := natDegree_C1_le_Dstar hq hM
  have hdeg2 := natDegree_C2_le hq hM
  have hdw : ∀ j, |d j| ≤ w j := by
    intro j
    rw [hdj, abs_mul, abs_of_nonneg hL0]
    apply mul_le_mul_of_nonneg_left _ hL0
    have h1 := coeff_C1_nonneg (M := M) hq j
    have h2 := coeff_C2_nonneg (M := M) hq j
    rw [abs_le]; constructor <;> linarith
  have hwω : ∀ j, w j ≤ 2 * L ^ 2 := by
    intro j
    simp only [hw]
    have h1 := coeff_C1_le (M := M) hq j
    have h2 := coeff_C2_le (M := M) hq j
    have : (C2 q M).coeff j + (C1 q M).coeff j ≤ 2 * L := by rw [hL]; linarith
    calc L * ((C2 q M).coeff j + (C1 q M).coeff j) ≤ L * (2 * L) :=
          mul_le_mul_of_nonneg_left this hL0
      _ = 2 * L ^ 2 := by ring
  have hw0 : ∀ j, 0 ≤ w j := fun j =>
    mul_nonneg hL0 (add_nonneg (coeff_C2_nonneg hq j) (coeff_C1_nonneg hq j))
  have hwσ : ∑ j ∈ range (N + 1), w j ≤ 2 * L := by
    simp only [hw]
    rw [← Finset.mul_sum, Finset.sum_add_distrib, sum_coeff_C2 hq hM, sum_coeff_C1 hq hM]
    linarith
  have hdD : d (N + 1) = 0 := by
    rw [hdj, coeff_eq_zero_of_natDegree_lt (by omega), coeff_eq_zero_of_natDegree_lt (by omega)]
    ring
  have hwD : w (N + 1) = 0 := by
    simp only [hw]
    rw [coeff_eq_zero_of_natDegree_lt (by omega), coeff_eq_zero_of_natDegree_lt (by omega)]
    ring
  have hd0 : 12 * a ≤ (d0 a : ℝ) := Nat.le_ceil _
  have hd01 : 1 ≤ d0 a := by
    have : (1 : ℝ) ≤ d0 a := by linarith
    exact_mod_cast this
  have hvan : ∀ j, j ≤ d0 a - 1 → d j = 0 := by
    intro j hj
    have hj' : j < d0 a := by omega
    rw [hdj, coeff_C1_of_lt hj', coeff_C2_of_lt hj']
    ring
  have hk0 : 11 * a ≤ ((d0 a - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hd01]; push_cast; linarith
  have hJ := J_chi_le (D := N) (k0 := d0 a - 1) ha hdw hwω (by positivity) hw0 hwσ hdD hwD hvan hk0
  have hPR : PR q M = shifted a (Real.exp a) d N := rfl
  rw [hPR]
  refine hJ.trans ?_
  -- numerical bound
  have hN : ((N + 1 : ℕ) : ℝ) ≤ 27 * a := Dstar_add_one_le hq hM
  push_cast at hN
  have hLa : L ≤ a⁻¹ := by rw [hL]; exact inv_anti₀ ha0 hla
  have hL2 : L ^ 2 ≤ (a⁻¹) ^ 2 := pow_le_pow_left₀ hL0 hLa 2
  have hL3 : L ^ 3 ≤ (a⁻¹) ^ 3 := pow_le_pow_left₀ hL0 hLa 3
  have hai : 0 < a⁻¹ := inv_pos.mpr ha0
  have haa : a * a⁻¹ = 1 := mul_inv_cancel₀ ha0.ne'
  -- first term: `a ((a+1) 2L²)² ≤ 16/a`
  have t1 : a * ((a + 1) * (2 * L ^ 2)) ^ 2 ≤ 16 * a⁻¹ := by
    have hb : (a + 1) * (2 * L ^ 2) ≤ 4 * a⁻¹ := by
      calc (a + 1) * (2 * L ^ 2) ≤ (2 * a) * (2 * (a⁻¹) ^ 2) := by
            apply mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
        _ = 4 * a⁻¹ * (a * a⁻¹) := by ring
        _ = 4 * a⁻¹ := by rw [haa, mul_one]
    have hb0 : 0 ≤ (a + 1) * (2 * L ^ 2) := by positivity
    calc a * ((a + 1) * (2 * L ^ 2)) ^ 2 ≤ a * (4 * a⁻¹) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hb0 hb 2) ha0.le
      _ = 16 * a⁻¹ * (a * a⁻¹) := by ring
      _ = 16 * a⁻¹ := by rw [haa, mul_one]
  -- second term: `2 (2L²)(2L) ((a+N+1)² + N + 2) ≤ 6496/a`
  have t2 : 2 * (2 * L ^ 2) * (2 * L) * ((a + N + 1) ^ 2 + N + 2) ≤ 6496 * a⁻¹ := by
    have hS : (a + N + 1) ^ 2 + N + 2 ≤ 812 * a ^ 2 := by
      have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      have h1 : a + N + 1 ≤ 28 * a := by linarith
      have h2 : (a + N + 1) ^ 2 ≤ (28 * a) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
      nlinarith
    calc 2 * (2 * L ^ 2) * (2 * L) * ((a + N + 1) ^ 2 + N + 2) =
        8 * L ^ 3 * ((a + N + 1) ^ 2 + N + 2) := by ring
      _ ≤ 8 * (a⁻¹) ^ 3 * (812 * a ^ 2) := by
          apply mul_le_mul (by linarith) hS (by positivity) (by positivity)
      _ = 6496 * a⁻¹ * (a * a⁻¹) ^ 2 := by ring
      _ = 6496 * a⁻¹ := by rw [haa, one_pow, mul_one]
  rw [div_eq_mul_inv]
  linarith

/-- **Total variation**: `∑_j |λ_j| ≤ 3000` (`opt:eq:clock-size`). -/
theorem sum_abs_clockWeight_le (hq : 1 ≤ q) (hM : 1 ≤ M) :
    ∑ j ∈ Icc 1 (clockLength q M), |clockWeight q M j| ≤ 3000 := by
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have ha : 1 ≤ q * M := by nlinarith
  have ha0 : 0 < q * M := by linarith
  unfold clockWeight
  rw [sum_abs_lamOf, clockLength]
  set N := Dstar q M
  have hχ : Lop (∑ k ∈ range (N + 1), beta q M k • lag k) +
      ∑ k ∈ range (N + 1), beta q M k • lag k = (4 : ℝ) • (X * derivative (PR q M) + PR q M) := by
    rw [← beta_spec, QR, Lop_add_self_op]
  have h1 := sum_abs_le N (beta q M) _ hχ
  have hJ := J_chi_mixture_le hq hM
  have hN : ((N + 1 : ℕ) : ℝ) ≤ 27 * (q * M) := Dstar_add_one_le hq hM
  push_cast at hN
  have hJ0 : 0 ≤ J ((X * derivative (PR q M) + PR q M) * (X * derivative (PR q M) + PR q M)) := by
    rw [← integral_sq_eq_J]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Ioi fun t _ => sq_nonneg _
  set Jv := J ((X * derivative (PR q M) + PR q M) * (X * derivative (PR q M) + PR q M))
  refine h1.trans ?_
  rw [← Real.sqrt_mul (by positivity)]
  have hprod : ((N : ℝ) + 1) * (2 * Jv) ≤ 3000 ^ 2 := by
    have : 2 * Jv ≤ 2 * (6512 / (q * M)) := by linarith
    calc ((N : ℝ) + 1) * (2 * Jv) ≤ (27 * (q * M)) * (2 * (6512 / (q * M))) :=
          mul_le_mul hN this (by positivity) (by positivity)
      _ = 351648 := by field_simp; ring
      _ ≤ 3000 ^ 2 := by norm_num
  calc Real.sqrt (((N : ℝ) + 1) * (2 * Jv)) ≤ Real.sqrt (3000 ^ 2) := Real.sqrt_le_sqrt hprod
    _ = 3000 := Real.sqrt_sq (by norm_num)

/-- **Clock length**: `n ≤ 27a` (`opt:eq:clock-size`). -/
theorem clockLength_le (hq : 1 ≤ q) (hM : 1 ≤ M) : (clockLength q M : ℝ) ≤ 27 * (q * M) :=
  Dstar_add_one_le hq hM

/-- **Exact moments** `opt:eq:clock-moments`. -/
theorem clock_moments (hq : 1 ≤ q) (hM : 1 ≤ M) {k m : ℕ} (hmk : m ≤ k) (hkM : k < M) :
    ∑ j ∈ Icc 1 (clockLength q M), (clockWeight q M j : ℂ) *
        ces (fun w => Complex.exp (-(((q * M : ℝ) : ℂ) * xi w)) * Rfun q w ^ k * xi w ^ m) j =
      if m = 0 then 1 else 0 := by
  have h := lamSum_moment hq hM hmk hkM
  rw [lamSum] at h
  have hf : (fun w => Complex.exp (-(((q * M : ℝ) : ℂ) * xi w)) * Rfun q w ^ k * xi w ^ m) =
      fun w => vt ((q * M : ℝ) : ℂ) w * (Rfun q w ^ k * xi w ^ m) := by
    funext w; rw [vt]; ring
  rw [hf]
  exact h

/-- **Theorem `opt:thm:weights`.** For every real `q ≥ 1` and integer `M ≥ 1`, with
`a = qM`, there are real weights `λ_1, …, λ_n` with `n ≤ 27a`, `∑ |λ_j| ≤ 3000`, and
`∑_j λ_j Ces_j(V R^k ξ^m) = δ_{m0}` for `0 ≤ m ≤ k < M`. -/
theorem exists_clock_weights (q : ℝ) (hq : 1 ≤ q) (M : ℕ) (hM : 1 ≤ M) :
    ∃ (n : ℕ) (lam : ℕ → ℝ), (n : ℝ) ≤ 27 * (q * M) ∧ ∑ j ∈ Icc 1 n, |lam j| ≤ 3000 ∧
      ∀ k m : ℕ, m ≤ k → k < M →
        ∑ j ∈ Icc 1 n, (lam j : ℂ) *
            ces (fun w => Complex.exp (-(((q * M : ℝ) : ℂ) * xi w)) * Rfun q w ^ k * xi w ^ m) j =
          if m = 0 then 1 else 0 :=
  ⟨clockLength q M, clockWeight q M, clockLength_le hq hM, sum_abs_clockWeight_le hq hM,
    fun _ _ hmk hkM => clock_moments hq hM hmk hkM⟩

end

end OptimalPrecision
