import GeneralODE.Theorem
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The query bound of Theorem `ode:thm:general` in closed form

For a solver with `f(κ, δ) = c κ log(2/δ)` calls (the near-optimal scaling of
Costa et al.), every factor of the explicit budget `matrixBudget` is bounded
in terms of `𝓛 = 1 + log((1 + ΛT) C̄ g / ε)`:

* `κ ≤ 4382 C̄ (1 + ΛT)` and `log(2/δ) ≤ 7 𝓛`;
* the Taylor degree is at most `34 𝓛`;
* the native block encoding costs at most `1327104 · 192 √s 𝓛` queries.

Hence the protocol of `general` uses at most
`C c (g/√q₀) C̄ (1 + ΛT) √s 𝓛³` native matrix queries and at most
`C' c (g/√q₀) C̄ (1 + ΛT) 𝓛` calls of each source interface, with explicit
absolute constants `C = 159443481054412800` and `C' = 18404400`
(`general_query_bound`).  This is the bound
`Õ(√s ḡ C̄ (1 + ΛT))` of the manuscript.
-/

namespace SparseHamiltonian.GeneralODE.Complexity

noncomputable section
open NativeSparseBlockEncoding Solver SparseStateOverlap ODEStateNormalization OracleCircuit
open scoped Nat

/-- The polylogarithmic factor `1 + log((1 + ΛT) C̄ g / ε)`. -/
def logFactor (Λ T Cbar g ε : ℝ) : ℝ := 1 + Real.log ((1 + Λ * T) * Cbar * g / ε)

theorem two_pow_le_exp (k : ℕ) : (2 : ℝ) ^ k ≤ Real.exp k := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  calc (2 : ℝ) ^ k ≤ Real.exp 1 ^ k := pow_le_pow_left₀ (by norm_num) h2 k
    _ = Real.exp k := by rw [← Real.exp_nat_mul, mul_one]

theorem log_le_of_le_two_pow {y : ℝ} (hy : 0 < y) (k : ℕ) (h : y ≤ 2 ^ k) : Real.log y ≤ k := by
  rw [Real.log_le_iff_le_exp hy]
  exact h.trans (two_pow_le_exp k)

theorem half_le_log_two : (1 / 2 : ℝ) ≤ Real.log 2 := by
  have := Real.log_two_gt_d9
  linarith

theorem pow_clog_lt (n : ℕ) (hn : 1 ≤ n) : 2 ^ Nat.clog 2 n < 2 * n := by
  rcases Nat.lt_or_ge 1 n with h1 | h1
  · have h := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) h1
    have hpos : 0 < Nat.clog 2 n := Nat.clog_pos (by norm_num) h1
    have e : 2 ^ Nat.clog 2 n = 2 * 2 ^ (Nat.clog 2 n).pred := by
      conv_lhs => rw [← Nat.succ_pred_eq_of_pos hpos]
      rw [pow_succ]
      ring
    omega
  · have : n = 1 := by omega
    subst this
    simp

section Bounds

variable {Λ T Cbar g ε : ℝ}

theorem ratio_ge_two (hΛ : 0 < Λ) (hT : 0 < T) (hC : 1 ≤ Cbar) (hg : 1 ≤ g) (hε : 0 < ε)
    (hε1 : ε ≤ 1 / 2) : 2 ≤ (1 + Λ * T) * Cbar * g / ε := by
  have h1 : 1 ≤ (1 + Λ * T) * Cbar * g := by
    have : 1 ≤ 1 + Λ * T := by nlinarith
    have : 1 ≤ (1 + Λ * T) * Cbar := by nlinarith
    nlinarith
  rw [le_div_iff₀ hε]
  linarith

theorem log_ratio_nonneg (hΛ : 0 < Λ) (hT : 0 < T) (hC : 1 ≤ Cbar) (hg : 1 ≤ g) (hε : 0 < ε)
    (hε1 : ε ≤ 1 / 2) : 0 ≤ Real.log ((1 + Λ * T) * Cbar * g / ε) :=
  Real.log_nonneg (by linarith [ratio_ge_two hΛ hT hC hg hε hε1])

theorem one_le_logFactor (hΛ : 0 < Λ) (hT : 0 < T) (hC : 1 ≤ Cbar) (hg : 1 ≤ g) (hε : 0 < ε)
    (hε1 : ε ≤ 1 / 2) : 1 ≤ logFactor Λ T Cbar g ε := by
  unfold logFactor
  linarith [log_ratio_nonneg hΛ hT hC hg hε hε1]

theorem steps_le_add (hΛ : 0 < Λ) (hT : 0 < T) : (Plan.steps Λ T : ℝ) ≤ 12 * (Λ * T) + 1 := by
  have h2 : Real.sqrt 2 ≤ 3 / 2 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hαT : 0 ≤ Plan.alpha Λ * T := (mul_pos (Plan.alpha_pos hΛ) hT).le
  have hceil : (Plan.steps Λ T : ℝ) < Plan.alpha Λ * T + 1 := Nat.ceil_lt_add_one hαT
  have hα : Plan.alpha Λ * T ≤ 12 * (Λ * T) := by
    unfold Plan.alpha
    have : 0 ≤ Λ * T := by positivity
    nlinarith
  linarith

theorem steps_le (hΛ : 0 < Λ) (hT : 0 < T) : (Plan.steps Λ T : ℝ) ≤ 12 * (1 + Λ * T) := by
  have := steps_le_add hΛ hT
  linarith

/-- `m/ϑ ≤ 20160 (1 + ΛT) C̄ g / ε`. -/
theorem ratio_le (hΛ : 0 < Λ) (hT : 0 < T) (hC : 1 ≤ Cbar) (hg : 1 ≤ g) (hε : 0 < ε) :
    (Plan.steps Λ T : ℝ) / Plan.budget Cbar g ε ≤ 20160 * ((1 + Λ * T) * Cbar * g / ε) := by
  have hs := steps_le hΛ hT
  have hC0 : 0 < Cbar := by linarith
  have hg0 : 0 < g := by linarith
  unfold Plan.budget
  rw [div_div_eq_mul_div]
  have : (Plan.steps Λ T : ℝ) * (1680 * Cbar * g) ≤ 12 * (1 + Λ * T) * (1680 * Cbar * g) :=
    mul_le_mul_of_nonneg_right hs (by positivity)
  calc (Plan.steps Λ T : ℝ) * (1680 * Cbar * g) / ε ≤ 12 * (1 + Λ * T) * (1680 * Cbar * g) / ε :=
        div_le_div_of_nonneg_right this hε.le
    _ = 20160 * ((1 + Λ * T) * Cbar * g / ε) := by ring

theorem one_le_ratio (hΛ : 0 < Λ) (hT : 0 < T) (hC : 1 ≤ Cbar) (hg : 1 ≤ g) (hε : 0 < ε)
    (hε1 : ε ≤ 1 / 2) : 1 ≤ (Plan.steps Λ T : ℝ) / Plan.budget Cbar g ε := by
  have hb := Plan.budget_pos hC hg hε
  have hb1 := Plan.budget_le hC hg hε hε1
  have hs : (1 : ℝ) ≤ Plan.steps Λ T := by exact_mod_cast Plan.steps_pos hΛ hT
  rw [le_div_iff₀ hb]
  linarith

/-- The Taylor degree is at most `34 𝓛`. -/
theorem degree_le (hΛ : 0 < Λ) (hT : 0 < T) (hC : 1 ≤ Cbar) (hg : 1 ≤ g) (hε : 0 < ε)
    (hε1 : ε ≤ 1 / 2) : (Plan.degree Λ T Cbar g ε : ℝ) ≤ 34 * logFactor Λ T Cbar g ε := by
  set u := (Plan.steps Λ T : ℝ) / Plan.budget Cbar g ε with hu
  set Q := (1 + Λ * T) * Cbar * g / ε with hQ
  have hu1 : 1 ≤ u := one_le_ratio hΛ hT hC hg hε hε1
  have huQ : u ≤ 20160 * Q := ratio_le hΛ hT hC hg hε
  have hQ2 : 2 ≤ Q := ratio_ge_two hΛ hT hC hg hε hε1
  have hn1 : 1 ≤ ⌈u⌉₊ := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr (by linarith)).ne'
  have hpow : (2 : ℝ) ^ Plan.degree Λ T Cbar g ε < 4 * u := by
    have h := pow_clog_lt ⌈u⌉₊ hn1
    have h' : ((2 ^ Plan.degree Λ T Cbar g ε : ℕ) : ℝ) < ((2 * ⌈u⌉₊ : ℕ) : ℝ) := by
      exact_mod_cast h
    push_cast at h'
    have hc : (⌈u⌉₊ : ℝ) < u + 1 := Nat.ceil_lt_add_one (by linarith)
    linarith
  have hlog : (Plan.degree Λ T Cbar g ε : ℝ) * Real.log 2 < Real.log (4 * u) := by
    rw [← Real.log_pow]
    exact Real.log_lt_log (by positivity) hpow
  have hlog4u : Real.log (4 * u) ≤ 17 + Real.log Q := by
    have h1 : Real.log (4 * u) ≤ Real.log (80640 * Q) :=
      Real.log_le_log (by positivity) (by linarith)
    rw [Real.log_mul (x := 80640) (y := Q) (by norm_num) (by positivity)] at h1
    have h2 : Real.log 80640 ≤ 17 := log_le_of_le_two_pow (by norm_num) 17 (by norm_num)
    linarith
  have hl2 := half_le_log_two
  have hL := log_ratio_nonneg hΛ hT hC hg hε hε1
  have hK0 : (0 : ℝ) ≤ Plan.degree Λ T Cbar g ε := Nat.cast_nonneg _
  have hK : (Plan.degree Λ T Cbar g ε : ℝ) ≤ 2 * (17 + Real.log Q) := by
    nlinarith
  unfold logFactor
  rw [← hQ]
  linarith

/-- `log(2/δ) ≤ 7 𝓛` for the solver accuracy `δ = ε/(40g)`. -/
theorem log_delta_le (hΛ : 0 < Λ) (hT : 0 < T) (hC : 1 ≤ Cbar) (hg : 1 ≤ g) (hε : 0 < ε)
    (hε1 : ε ≤ 1 / 2) : Real.log (2 / Plan.delta g ε) ≤ 7 * logFactor Λ T Cbar g ε := by
  have hg0 : 0 < g := by linarith
  have hQ2 := ratio_ge_two hΛ hT hC hg hε hε1
  have hL := log_ratio_nonneg hΛ hT hC hg hε hε1
  have heq : 2 / Plan.delta g ε = 80 * (g / ε) := by
    unfold Plan.delta
    field_simp
    ring
  have hgQ : g / ε ≤ (1 + Λ * T) * Cbar * g / ε := by
    apply div_le_div_of_nonneg_right _ hε.le
    have h1 : 1 ≤ 1 + Λ * T := by nlinarith [mul_pos hΛ hT]
    have : 1 ≤ (1 + Λ * T) * Cbar := by nlinarith
    nlinarith
  have h1 : Real.log (2 / Plan.delta g ε) ≤ Real.log (80 * ((1 + Λ * T) * Cbar * g / ε)) := by
    rw [heq]
    exact Real.log_le_log (by positivity) (by linarith)
  rw [Real.log_mul (by norm_num) (by positivity)] at h1
  have h2 : Real.log 80 ≤ 7 := log_le_of_le_two_pow (by norm_num) 7 (by norm_num)
  unfold logFactor
  linarith

/-- `κ ≤ 4382 C̄ (1 + ΛT)`. -/
theorem kappa_le (hΛ : 0 < Λ) (hT : 0 < T) (hC : 1 ≤ Cbar) :
    Plan.kappa Λ T Cbar ≤ 4382 * (Cbar * (1 + Λ * T)) := by
  have hs := steps_le_add hΛ hT
  have he := Real.exp_one_lt_d9
  have hΛT : 0 ≤ Λ * T := by positivity
  have hC0 : 0 ≤ Cbar := by linarith
  unfold Plan.kappa History.kappaH
  have h1 : (2 : ℝ) + 2 ^ 2 * Real.exp 1 ≤ 13 := by norm_num; linarith
  have h2 : 2 * (Plan.steps Λ T : ℝ) + 1 ≤ 24 * (1 + Λ * T) := by linarith
  have h3 : 2 * Cbar * (2 * (Plan.steps Λ T : ℝ) + 1) * (2 + 2 ^ 2 * Real.exp 1) ≤
      2 * Cbar * (24 * (1 + Λ * T)) * 13 := by
    have hpos : 0 ≤ 2 * (Plan.steps Λ T : ℝ) + 1 := by positivity
    have hpos2 : 0 ≤ (2 : ℝ) + 2 ^ 2 * Real.exp 1 := by positivity
    calc 2 * Cbar * (2 * (Plan.steps Λ T : ℝ) + 1) * (2 + 2 ^ 2 * Real.exp 1)
        ≤ 2 * Cbar * (24 * (1 + Λ * T)) * (2 + 2 ^ 2 * Real.exp 1) := by gcongr
      _ ≤ 2 * Cbar * (24 * (1 + Λ * T)) * 13 := by gcongr
  have h4 : 1 ≤ Cbar * (1 + Λ * T) := by nlinarith
  nlinarith

/-- The precision logarithm of the native block encoding is at most `26 𝓛`. -/
theorem nativeLog_le (hΛ : 0 < Λ) (hT : 0 < T) (hC : 1 ≤ Cbar) (hg : 1 ≤ g) (hε : 0 < ε)
    (hε1 : ε ≤ 1 / 2) :
    ImprovedPrecisionBudget.targetLog (Plan.nativeError Λ T Cbar g ε) ≤
      26 * logFactor Λ T Cbar g ε := by
  set u := (Plan.steps Λ T : ℝ) / Plan.budget Cbar g ε with hu
  set Q := (1 + Λ * T) * Cbar * g / ε with hQ
  set K : ℝ := (Plan.degree Λ T Cbar g ε : ℝ) with hK
  have hu1 : 1 ≤ u := one_le_ratio hΛ hT hC hg hε hε1
  have huQ : u ≤ 20160 * Q := ratio_le hΛ hT hC hg hε
  have hQ2 : 2 ≤ Q := ratio_ge_two hΛ hT hC hg hε hε1
  have hL := log_ratio_nonneg hΛ hT hC hg hε hε1
  have h𝓛 := one_le_logFactor hΛ hT hC hg hε hε1
  have hKle := degree_le hΛ hT hC hg hε hε1
  have hK0 : 0 ≤ K := Nat.cast_nonneg _
  have hb := Plan.budget_pos hC hg hε
  have hs : (0 : ℝ) < Plan.steps Λ T := by exact_mod_cast Plan.steps_pos hΛ hT
  have heq : 2 / Plan.nativeError Λ T Cbar g ε = 8 * ((K + 1) * u) := by
    unfold Plan.nativeError
    rw [hu, ← hK]
    field_simp
    ring
  unfold ImprovedPrecisionBudget.targetLog
  rw [heq, Real.log_mul (by norm_num) (by positivity), Real.log_mul (by positivity) (by positivity)]
  have h8 : Real.log 8 ≤ 3 := log_le_of_le_two_pow (by norm_num) 3 (by norm_num)
  have hK1 : Real.log (K + 1) ≤ 6 + logFactor Λ T Cbar g ε := by
    have h1 : Real.log (K + 1) ≤ Real.log (35 * logFactor Λ T Cbar g ε) :=
      Real.log_le_log (by positivity) (by linarith)
    rw [Real.log_mul (by norm_num) (by positivity)] at h1
    have h2 : Real.log 35 ≤ 6 := log_le_of_le_two_pow (by norm_num) 6 (by norm_num)
    have h3 : Real.log (logFactor Λ T Cbar g ε) ≤ logFactor Λ T Cbar g ε := by
      have := Real.log_le_sub_one_of_pos (show 0 < logFactor Λ T Cbar g ε by linarith)
      linarith
    linarith
  have hlu : Real.log u ≤ 15 + Real.log Q := by
    have h1 : Real.log u ≤ Real.log (20160 * Q) := Real.log_le_log (by linarith) huQ
    rw [Real.log_mul (by norm_num) (by positivity)] at h1
    have h2 : Real.log 20160 ≤ 15 := log_le_of_le_two_pow (by norm_num) 15 (by norm_num)
    linarith
  have hQL : Real.log Q ≤ logFactor Λ T Cbar g ε := by
    unfold logFactor
    rw [← hQ]
    linarith
  linarith

theorem nativeLog_nonneg (hΛ : 0 < Λ) (hT : 0 < T) (hC : 1 ≤ Cbar) (hg : 1 ≤ g) (hε : 0 < ε)
    (hε1 : ε ≤ 1 / 2) :
    0 ≤ ImprovedPrecisionBudget.targetLog (Plan.nativeError Λ T Cbar g ε) := by
  unfold ImprovedPrecisionBudget.targetLog
  apply Real.log_nonneg
  have h1 := Plan.nativeError_le hΛ hT hC hg hε hε1
  have h0 := Plan.nativeError_pos hΛ hT hC hg hε
  rw [le_div_iff₀ h0]
  linarith

/-- The native block encoding costs at most `192 √s 𝓛` (times `1327104`). -/
theorem shape_le (s : ℕ) (hs : 1 ≤ s) (hΛ : 0 < Λ) (hT : 0 < T) (hC : 1 ≤ Cbar) (hg : 1 ≤ g)
    (hε : 0 < ε) (hε1 : ε ≤ 1 / 2) :
    ImprovedPrecisionBudget.shape (2 * (s : ℝ)) (2 * (Plan.arcDegree Λ T Cbar g ε : ℝ))
        (ImprovedPrecisionBudget.targetLog (Plan.nativeError Λ T Cbar g ε)) ≤
      192 * (Real.sqrt s * logFactor Λ T Cbar g ε) := by
  set 𝓛 := logFactor Λ T Cbar g ε with h𝓛def
  set ℓ := ImprovedPrecisionBudget.targetLog (Plan.nativeError Λ T Cbar g ε) with hℓ
  have hℓle : ℓ ≤ 26 * 𝓛 := nativeLog_le hΛ hT hC hg hε hε1
  have hℓ0 : 0 ≤ ℓ := nativeLog_nonneg hΛ hT hC hg hε hε1
  have h𝓛 : 1 ≤ 𝓛 := one_le_logFactor hΛ hT hC hg hε hε1
  have hKle := degree_le hΛ hT hC hg hε hε1
  have hA : (Plan.arcDegree Λ T Cbar g ε : ℝ) ≤ 35 * 𝓛 := by
    unfold Plan.arcDegree
    push_cast
    linarith
  have hA0 : (0 : ℝ) ≤ Plan.arcDegree Λ T Cbar g ε := Nat.cast_nonneg _
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hss : 1 ≤ Real.sqrt s := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hs1
  have h2 : Real.sqrt 2 ≤ 3 / 2 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  unfold ImprovedPrecisionBudget.shape
  have hfirst : Real.sqrt (2 * (s : ℝ)) * (2 * (Plan.arcDegree Λ T Cbar g ε : ℝ)) ≤
      105 * (Real.sqrt s * 𝓛) := by
    rw [Real.sqrt_mul (by norm_num)]
    have hsq0 : 0 ≤ Real.sqrt (s : ℝ) := Real.sqrt_nonneg _
    have : Real.sqrt 2 * Real.sqrt s ≤ 3 / 2 * Real.sqrt s := mul_le_mul_of_nonneg_right h2 hsq0
    have h70 : 2 * (Plan.arcDegree Λ T Cbar g ε : ℝ) ≤ 70 * 𝓛 := by linarith
    calc Real.sqrt 2 * Real.sqrt s * (2 * (Plan.arcDegree Λ T Cbar g ε : ℝ))
        ≤ 3 / 2 * Real.sqrt s * (70 * 𝓛) := by
          apply mul_le_mul this h70 (by positivity) (by positivity)
      _ = 105 * (Real.sqrt s * 𝓛) := by ring
  have hsecond : Real.sqrt (2 * (s : ℝ) * (2 * (Plan.arcDegree Λ T Cbar g ε : ℝ)) * ℓ) ≤
      61 * (Real.sqrt s * 𝓛) := by
    rw [Real.sqrt_le_left (by positivity)]
    have hprod : 2 * (s : ℝ) * (2 * (Plan.arcDegree Λ T Cbar g ε : ℝ)) * ℓ ≤
        2 * (s : ℝ) * (70 * 𝓛) * (26 * 𝓛) := by
      have h70 : 2 * (Plan.arcDegree Λ T Cbar g ε : ℝ) ≤ 70 * 𝓛 := by linarith
      have hsnn : (0 : ℝ) ≤ 2 * s := by positivity
      apply mul_le_mul (mul_le_mul_of_nonneg_left h70 hsnn) hℓle hℓ0 (by positivity)
    have hsq : Real.sqrt (s : ℝ) ^ 2 = s := Real.sq_sqrt (by positivity)
    calc 2 * (s : ℝ) * (2 * (Plan.arcDegree Λ T Cbar g ε : ℝ)) * ℓ
        ≤ 2 * (s : ℝ) * (70 * 𝓛) * (26 * 𝓛) := hprod
      _ = 3640 * (Real.sqrt s ^ 2 * 𝓛 ^ 2) := by rw [hsq]; ring
      _ ≤ 3721 * (Real.sqrt s ^ 2 * 𝓛 ^ 2) := by
          apply mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      _ = (61 * (Real.sqrt s * 𝓛)) ^ 2 := by ring
  have hthird : ℓ ≤ 26 * (Real.sqrt s * 𝓛) := by
    have : 𝓛 ≤ Real.sqrt s * 𝓛 := by nlinarith
    linarith
  linarith

end Bounds

section Budget

variable {Λ T Cbar g ε : ℝ}

/-- The matrix-query budget for `f(κ, δ) = c κ log(2/δ)`, factor by factor. -/
theorem matrixBudget_le (c q₀ : ℝ) (hc : 0 ≤ c) (hq₀ : 0 < q₀) (s : ℕ) (hs : 1 ≤ s)
    (hΛ : 0 < Λ) (hT : 0 < T) (hC : 1 ≤ Cbar) (hg : 1 ≤ g) (hε : 0 < ε) (hε1 : ε ≤ 1 / 2) :
    matrixBudget (fun κ δ => c * κ * Real.log (2 / δ)) q₀ s Λ T Cbar g ε ≤
      159443481054412800 * (c * (g / Real.sqrt q₀) * (Cbar * (1 + Λ * T)) * Real.sqrt s *
        logFactor Λ T Cbar g ε ^ 3) := by
  set 𝓛 := logFactor Λ T Cbar g ε with h𝓛def
  have h𝓛 : 1 ≤ 𝓛 := one_le_logFactor hΛ hT hC hg hε hε1
  have hκ := kappa_le hΛ hT hC
  have hκ0 : 0 ≤ Plan.kappa Λ T Cbar := by linarith [Plan.one_le_kappa (Λ := Λ) (T := T) hC]
  have hδ := log_delta_le hΛ hT hC hg hε hε1
  have hδ0 : 0 ≤ Real.log (2 / Plan.delta g ε) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ (Plan.delta_pos hg hε)]
    linarith [Plan.delta_le hg hε hε1]
  have hK := degree_le hΛ hT hC hg hε hε1
  have hK0 : (0 : ℝ) ≤ Plan.degree Λ T Cbar g ε := Nat.cast_nonneg _
  have hsh := shape_le s hs hΛ hT hC hg hε hε1
  have hsh0 : 0 ≤ ImprovedPrecisionBudget.shape (2 * (s : ℝ))
      (2 * (Plan.arcDegree Λ T Cbar g ε : ℝ))
      (ImprovedPrecisionBudget.targetLog (Plan.nativeError Λ T Cbar g ε)) := by
    unfold ImprovedPrecisionBudget.shape
    have := nativeLog_nonneg hΛ hT hC hg hε hε1
    positivity
  have hsq : 0 ≤ Real.sqrt (s : ℝ) := Real.sqrt_nonneg _
  have hq : 0 < Real.sqrt q₀ := Real.sqrt_pos.mpr hq₀
  have hg0 : 0 < g := by linarith
  have hCT : 0 ≤ Cbar * (1 + Λ * T) := by
    have : 0 ≤ Λ * T := by positivity
    have : 0 ≤ Cbar := by linarith
    positivity
  unfold matrixBudget Plan.gain
  set G := 5 * g / Real.sqrt q₀ with hG
  have hG0 : 0 ≤ G := by positivity
  have hf : c * Plan.kappa Λ T Cbar * Real.log (2 / Plan.delta g ε) ≤
      c * (4382 * (Cbar * (1 + Λ * T))) * (7 * 𝓛) := by
    apply mul_le_mul (mul_le_mul_of_nonneg_left hκ hc) hδ hδ0 (by positivity)
  have hrest : 3 * ((Plan.degree Λ T Cbar g ε : ℝ) * (1327104 *
      ImprovedPrecisionBudget.shape (2 * (s : ℝ)) (2 * (Plan.arcDegree Λ T Cbar g ε : ℝ))
        (ImprovedPrecisionBudget.targetLog (Plan.nativeError Λ T Cbar g ε)))) ≤
      3 * ((34 * 𝓛) * (1327104 * (192 * (Real.sqrt s * 𝓛)))) := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply mul_le_mul hK (mul_le_mul_of_nonneg_left hsh (by norm_num)) (by positivity)
      (by positivity)
  calc 40 * G * (c * Plan.kappa Λ T Cbar * Real.log (2 / Plan.delta g ε) *
        (3 * ((Plan.degree Λ T Cbar g ε : ℝ) * (1327104 *
          ImprovedPrecisionBudget.shape (2 * (s : ℝ)) (2 * (Plan.arcDegree Λ T Cbar g ε : ℝ))
            (ImprovedPrecisionBudget.targetLog (Plan.nativeError Λ T Cbar g ε))))))
      ≤ 40 * G * (c * (4382 * (Cbar * (1 + Λ * T))) * (7 * 𝓛) *
        (3 * ((34 * 𝓛) * (1327104 * (192 * (Real.sqrt s * 𝓛)))))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply mul_le_mul hf hrest (by positivity) (by positivity)
    _ = 159443481054412800 * (c * (g / Real.sqrt q₀) * (Cbar * (1 + Λ * T)) * Real.sqrt s *
        𝓛 ^ 3) := by
        rw [hG]
        field_simp
        ring

/-- The source budget for `f(κ, δ) = c κ log(2/δ)`. -/
theorem sourceBudget_le (c q₀ : ℝ) (hc : 0 ≤ c) (hq₀ : 0 < q₀)
    (hΛ : 0 < Λ) (hT : 0 < T) (hC : 1 ≤ Cbar) (hg : 1 ≤ g) (hε : 0 < ε) (hε1 : ε ≤ 1 / 2) :
    sourceBudget (fun κ δ => c * κ * Real.log (2 / δ)) q₀ Λ T Cbar g ε ≤
      18404400 * (c * (g / Real.sqrt q₀) * (Cbar * (1 + Λ * T)) * logFactor Λ T Cbar g ε) := by
  have hκ := kappa_le hΛ hT hC
  have hδ := log_delta_le hΛ hT hC hg hε hε1
  have hδ0 : 0 ≤ Real.log (2 / Plan.delta g ε) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ (Plan.delta_pos hg hε)]
    linarith [Plan.delta_le hg hε hε1]
  have hq : 0 < Real.sqrt q₀ := Real.sqrt_pos.mpr hq₀
  have hg0 : 0 < g := by linarith
  have hCT : 0 ≤ Cbar * (1 + Λ * T) := by
    have : 0 ≤ Λ * T := by positivity
    have : 0 ≤ Cbar := by linarith
    positivity
  have h𝓛 := one_le_logFactor hΛ hT hC hg hε hε1
  unfold sourceBudget Plan.gain
  have hf : c * Plan.kappa Λ T Cbar * Real.log (2 / Plan.delta g ε) ≤
      c * (4382 * (Cbar * (1 + Λ * T))) * (7 * logFactor Λ T Cbar g ε) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hκ hc) hδ hδ0 (by positivity)
  calc 40 * (5 * g / Real.sqrt q₀) * (3 * (c * Plan.kappa Λ T Cbar *
        Real.log (2 / Plan.delta g ε)))
      ≤ 40 * (5 * g / Real.sqrt q₀) * (3 * (c * (4382 * (Cbar * (1 + Λ * T))) *
        (7 * logFactor Λ T Cbar g ε))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith
    _ = 18404400 * (c * (g / Real.sqrt q₀) * (Cbar * (1 + Λ * T)) * logFactor Λ T Cbar g ε) := by
        field_simp
        ring

end Budget

variable {n : Type} [Fintype n] [DecidableEq n]
variable {X Z : Type} [Fintype Z] [AddCommGroup Z] [DecidableEq Z] {s : ℕ}

set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
/-- **Theorem `ode:thm:general` with a near-optimal solver.**  If the
block-input solver uses `c κ log(2/δ)` calls, one protocol makes at most
`C c (g/√q₀) C̄ (1 + ΛT) √s 𝓛³` native matrix queries and at most
`C' c (g/√q₀) C̄ (1 + ΛT) 𝓛` calls of each source, in every history, where
`𝓛 = 1 + log((1 + ΛT) C̄ g / ε)`; on every valid input it succeeds with
probability at least `175/256` and its conditional output is within trace
distance `ε` of `x(T)/‖x(T)‖`. -/
theorem general_query_bound (c q₀ : ℝ) (hc : 0 ≤ c)
    (hsolver : BlockSolver (fun κ δ => c * κ * Real.log (2 / δ)) q₀)
    (hq₀ : 0 < q₀) (hq₀1 : q₀ ≤ 1) (D : Data X n Z s) (Λ T Cbar g ε r₀ rb : ℝ)
    (hΛ : 0 < Λ) (hT : 0 < T) (hC : 1 ≤ Cbar) (hg : 1 ≤ g) (hε : 0 < ε) (hε1 : ε ≤ 1 / 2)
    (hA : ∀ x, ‖matrixOperator (D.matrix x)‖ ≤ Λ)
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ₀ : ∀ y, IsUnitary (J₀ y)) (hJb : ∀ y, IsUnitary (Jb y))
    (seed : EuclideanSpace ℂ n) (hseed : ‖seed‖ = 1) :
    ∃ (Tn d w : ℕ) (prot : ODERepeatProtocol.Protocol
        (physicalOracle D J₀ Jb (Plan.arcDegree Λ T Cbar g ε) Tn d (Plan.steps Λ T)
          (Plan.degree Λ T Cbar g ε) w) (EuclideanSpace ℂ n)),
      (prot.worstCost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) : ℝ) ≤
          159443481054412800 * (c * (g / Real.sqrt q₀) * (Cbar * (1 + Λ * T)) * Real.sqrt s *
            logFactor Λ T Cbar g ε ^ 3) ∧
      (∀ b : Bool, (prot.worstCost (ODESourceQueryBudget.sourceWeight b) : ℝ) ≤
          18404400 * (c * (g / Real.sqrt q₀) * (Cbar * (1 + Λ * T)) * logFactor Λ T Cbar g ε)) ∧
      ∀ (x : X) (v b : EuclideanSpace ℂ n), ‖v‖ = r₀ → ‖b‖ = rb →
        (v ≠ 0 → J₀ x seed = unitDirection v) → (b ≠ 0 → Jb x seed = unitDirection b) →
        (∀ t, 0 ≤ t → t ≤ T → ‖NormedSpace.exp (t • ODEPublicSourceMesh.generator D x)‖ ≤ Cbar) →
        (∀ t, 0 ≤ t → t ≤ T →
          ‖ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b t‖ ≤
            g * ‖ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T‖) →
        ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T ≠ 0 →
        Amplify.Outcome prot x
          (ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T) ε := by
  obtain ⟨Tn, d, w, prot, h1, h2, h3⟩ := general _ q₀ hsolver hq₀ hq₀1 D Λ T Cbar g ε r₀ rb
    hΛ hT hC hg hε hε1 hA J₀ Jb hJ₀ hJb seed hseed
  refine ⟨Tn, d, w, prot, h1.trans ?_, fun b => (h2 b).trans ?_, h3⟩
  · exact matrixBudget_le c q₀ hc hq₀ s D.slots_pos hΛ hT hC hg hε hε1
  · exact sourceBudget_le c q₀ hc hq₀ hΛ hT hC hg hε hε1

end

end SparseHamiltonian.GeneralODE.Complexity
