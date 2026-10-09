import GateEfficientQuadrature.Certificate
import TimeDependentODE.Continuous.Existence

/-!
# The quadrature normalisation against the continuous source mass

Theorem `ode:thm:gates` normalises the source preparation by the quadrature mass
`B_m = ‖x₀‖ + ∑_i w_i ‖b(v_i)‖`, and its certificates `ode:eq:gate-source-certificates` require
`0 < B_m ≤ 2B` for the continuous mass `B = ‖x₀‖ + ∫_0^T ‖b(v)‖ dv`. For the left-endpoint
quadrature the proof argues: "Since `v ↦ ‖b(v)‖` is `L_b`-Lipschitz, the same quadrature
estimate gives `|B_m - B| ≤ T² L_b / (2m) ≤ ν B`, `(1 - ν) B ≤ B_m ≤ (1 + ν) B`. As `B > 0` and
`0 < ν < 1`, this proves both `B_m > 0` and `B_m ≤ 2B`, including when `x₀ = 0`."

* `contMass x₀ b T = ‖x₀‖ + ∫_0^T ‖b‖` (the paper's `B`) and
  `quadMass x₀ f T n = ‖x₀‖ + ∑_{q < n} (T / n) ‖f_q‖`, written `B_n` (the paper's `B_m` with
  `m = n` nodes).
* `mass_left`: for an `L`-Lipschitz forcing and samples `f_q` with `‖b(q T / n) - f_q‖ ≤ δ`,
  `|quadMass - contMass| ≤ L T² / (2n) + T δ`.
* `mass_bounds`: `|B_n - B| ≤ ν B` with `B > 0`, `ν < 1` gives
  `(1 - ν) B ≤ B_n ≤ (1 + ν) B`, `0 < B_n` and `B_n ≤ 2B`.
* `nodes_sufficient`: `n ≥ T² C / (2 ν B)` gives `T² C / (2n) ≤ ν B` (the paper's
  `m ≥ max{1, T² C_b / (2 ν B)}`).
-/

set_option autoImplicit false

namespace SparseHamiltonian.GateQuad

noncomputable section
open Set
open scoped BigOperators

variable {V : Type*} [NormedAddCommGroup V]

/-- The continuous source mass `B = ‖x₀‖ + ∫_0^T ‖b(v)‖ dv` of Theorem `ode:thm:gates`. -/
def contMass (x0 : V) (b : ℝ → V) (T : ℝ) : ℝ := ‖x0‖ + ∫ u in (0 : ℝ)..T, ‖b u‖

/-- The normalisation `B_n = ‖x₀‖ + ∑_{q < n} (T / n) ‖f_q‖` of the left-endpoint quadrature with
`n` nodes and samples `f_q` (the paper's `B_m` with `m = n` nodes). -/
def quadMass (x0 : V) (f : ℕ → V) (T : ℝ) (n : ℕ) : ℝ :=
  ‖x0‖ + ∑ q ∈ Finset.range n, T / n * ‖f q‖

/-- `∫_a^{a+h} (δ + L (u - a)) du = δ h + L h² / 2`. -/
theorem integral_affine (a h L δ : ℝ) :
    ∫ u in a..a + h, (δ + L * (u - a)) = δ * h + L * h ^ 2 / 2 := by
  have hF : ∀ u ∈ uIcc a (a + h), HasDerivAt (fun t : ℝ => δ * t + L * ((t - a) ^ 2 / 2))
      (δ + L * (u - a)) u := by
    intro u _
    have h1 := ((hasDerivAt_id u).const_mul δ).add
      (((((hasDerivAt_id u).sub_const a).pow 2).div_const 2).const_mul L)
    exact h1.congr_deriv (by norm_num)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF
    (by apply Continuous.intervalIntegrable; fun_prop)]
  ring

/-- **The quadrature mass against the continuous mass.** For an `L`-Lipschitz forcing on
`[0, T]` and samples `f_q` (`q < n`) with `‖b(q T / n) - f_q‖ ≤ δ`,
`|B_n - B| ≤ L T² / (2n) + T δ`. -/
theorem mass_left {b : ℝ → V} {f : ℕ → V} {T L δ : ℝ} {n : ℕ} (hT : 0 ≤ T) (hn : 0 < n)
    (hbL : ∀ u ∈ Icc 0 T, ∀ u' ∈ Icc 0 T, ‖b u - b u'‖ ≤ L * |u - u'|)
    (hbf : ∀ q < n, ‖b (q * T / n) - f q‖ ≤ δ) (x0 : V) :
    |quadMass x0 f T n - contMass x0 b T| ≤ L * T ^ 2 / (2 * n) + T * δ := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  unfold quadMass contMass
  set h : ℝ := T / n with hh_def
  have hh : 0 ≤ h := div_nonneg hT hnR.le
  have hnode : ∀ k : ℕ, (k : ℝ) * T / n = k * h := by
    intro k
    rw [hh_def]
    ring
  have hnh : (n : ℝ) * h = T := by
    rw [hh_def]
    field_simp
  have hcont : ContinuousOn (fun u => ‖b u‖) (Icc 0 T) :=
    (TimeDependentODE.continuousOn_of_norm_sub_le b hbL).norm
  have hsubI : ∀ k < n, Icc ((k : ℝ) * h) (((k + 1 : ℕ) : ℝ) * h) ⊆ Icc 0 T := by
    intro k hk
    apply Icc_subset_Icc (mul_nonneg (Nat.cast_nonneg k) hh)
    rw [← hnh]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hh
  have hle : ∀ k : ℕ, (k : ℝ) * h ≤ ((k + 1 : ℕ) : ℝ) * h := by
    intro k
    push_cast
    linarith
  have hint : ∀ k < n, IntervalIntegrable (fun u => ‖b u‖) MeasureTheory.volume
      ((k : ℝ) * h) (((k + 1 : ℕ) : ℝ) * h) := fun k hk =>
    ContinuousOn.intervalIntegrable_of_Icc (hle k) (hcont.mono (hsubI k hk))
  have hsplit : ∫ u in (0 : ℝ)..T, ‖b u‖ =
      ∑ k ∈ Finset.range n, ∫ u in ((k : ℝ) * h)..(((k + 1 : ℕ) : ℝ) * h), ‖b u‖ := by
    have h1 := intervalIntegral.sum_integral_adjacent_intervals
      (a := fun k : ℕ => (k : ℝ) * h) hint
    simp only [Nat.cast_zero, zero_mul, hnh] at h1
    exact h1.symm
  -- every interval
  have hterm : ∀ k < n, |h * ‖f k‖ - ∫ u in ((k : ℝ) * h)..(((k + 1 : ℕ) : ℝ) * h), ‖b u‖| ≤
      L * h ^ 2 / 2 + δ * h := by
    intro k hk
    have hend : ((k + 1 : ℕ) : ℝ) * h = (k : ℝ) * h + h := by
      push_cast
      ring
    have hconst : h * ‖f k‖ = ∫ _ in ((k : ℝ) * h)..(((k + 1 : ℕ) : ℝ) * h), ‖f k‖ := by
      rw [intervalIntegral.integral_const, hend, smul_eq_mul]
      ring
    rw [hconst, ← intervalIntegral.integral_sub intervalIntegrable_const (hint k hk)]
    have hbound := intervalIntegral.norm_integral_le_of_norm_le (μ := MeasureTheory.volume)
      (hle k)
      (f := fun u => ‖f k‖ - ‖b u‖) (g := fun u => δ + L * (u - (k : ℝ) * h))
      (MeasureTheory.ae_of_all _ (fun u hu => by
        have huI : u ∈ Icc 0 T := hsubI k hk (Ioc_subset_Icc_self hu)
        have hkI : (k : ℝ) * h ∈ Icc 0 T :=
          hsubI k hk ⟨le_rfl, hle k⟩
        have h1 : ‖b ((k : ℝ) * h) - f k‖ ≤ δ := by
          rw [← hnode k]
          exact hbf k hk
        have h2 := hbL ((k : ℝ) * h) hkI u huI
        rw [abs_sub_comm, abs_of_nonneg (by linarith [hu.1])] at h2
        calc ‖‖f k‖ - ‖b u‖‖ = |‖f k‖ - ‖b u‖| := Real.norm_eq_abs _
          _ ≤ ‖f k - b u‖ := abs_norm_sub_norm_le _ _
          _ = ‖(b ((k : ℝ) * h) - b u) - (b ((k : ℝ) * h) - f k)‖ := by congr 1; abel
          _ ≤ ‖b ((k : ℝ) * h) - b u‖ + ‖b ((k : ℝ) * h) - f k‖ := norm_sub_le _ _
          _ ≤ L * (u - (k : ℝ) * h) + δ := add_le_add h2 h1
          _ = δ + L * (u - (k : ℝ) * h) := by ring))
      (by apply Continuous.intervalIntegrable; fun_prop)
    rw [Real.norm_eq_abs, hend, integral_affine] at hbound
    rw [hend]
    linarith
  rw [hsplit]
  have hdiff : ‖x0‖ + ∑ q ∈ Finset.range n, h * ‖f q‖ -
      (‖x0‖ + ∑ k ∈ Finset.range n, ∫ u in ((k : ℝ) * h)..(((k + 1 : ℕ) : ℝ) * h), ‖b u‖) =
      ∑ k ∈ Finset.range n, (h * ‖f k‖ -
        ∫ u in ((k : ℝ) * h)..(((k + 1 : ℕ) : ℝ) * h), ‖b u‖) := by
    rw [Finset.sum_sub_distrib]
    ring
  rw [hdiff]
  calc |∑ k ∈ Finset.range n, (h * ‖f k‖ -
        ∫ u in ((k : ℝ) * h)..(((k + 1 : ℕ) : ℝ) * h), ‖b u‖)|
      ≤ ∑ k ∈ Finset.range n, |h * ‖f k‖ -
        ∫ u in ((k : ℝ) * h)..(((k + 1 : ℕ) : ℝ) * h), ‖b u‖| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.range n, (L * h ^ 2 / 2 + δ * h) :=
        Finset.sum_le_sum (fun k hk => hterm k (Finset.mem_range.mp hk))
    _ = L * T ^ 2 / (2 * n) + T * δ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hh_def]
        field_simp

/-- **The two-sided mass comparison.** `|B_n - B| ≤ ν B` with `B > 0` and `ν < 1` gives
`(1 - ν) B ≤ B_n ≤ (1 + ν) B`, hence `0 < B_n` and `B_n ≤ 2B`. -/
theorem mass_bounds {B Bm ν : ℝ} (hB : 0 < B) (hν1 : ν < 1)
    (h : |Bm - B| ≤ ν * B) :
    (1 - ν) * B ≤ Bm ∧ Bm ≤ (1 + ν) * B ∧ 0 < Bm ∧ Bm ≤ 2 * B := by
  obtain ⟨h1, h2⟩ := abs_le.mp h
  refine ⟨by linarith, by linarith, ?_, ?_⟩
  · have : 0 < (1 - ν) * B := mul_pos (by linarith) hB
    linarith
  · nlinarith

/-- **The number of nodes.** `n ≥ T² C / (2 ν B)` with `ν B > 0` gives `T² C / (2n) ≤ ν B`. -/
theorem nodes_sufficient {T C ν B : ℝ} {n : ℕ} (hn : 0 < n) (hνB : 0 < ν * B)
    (hm : T ^ 2 * C / (2 * ν * B) ≤ n) : T ^ 2 * C / (2 * n) ≤ ν * B := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have h2 : 0 < 2 * ν * B := by linarith
  rw [div_le_iff₀ h2] at hm
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-- **A power-of-two number of nodes.** For every real `X` some power of two `2^k` satisfies
`max 1 X ≤ 2^k < 2 (⌈X⌉₊ + 1)` (`⌈X⌉₊` the natural ceiling), so the label register of the
quadrature has `k < log₂ (2 (⌈X⌉₊ + 1))` bits. -/
theorem exists_pow_two_nodes (X : ℝ) :
    ∃ k : ℕ, 1 ≤ 2 ^ k ∧ X ≤ ((2 ^ k : ℕ) : ℝ) ∧ 2 ^ k < 2 * (⌈X⌉₊ + 1) := by
  set N := ⌈X⌉₊ + 1 with hN_def
  refine ⟨Nat.clog 2 N, Nat.one_le_two_pow, ?_, ?_⟩
  · have h1 : N ≤ 2 ^ Nat.clog 2 N := Nat.le_pow_clog (by norm_num) N
    have h2 : X ≤ (⌈X⌉₊ : ℝ) := Nat.le_ceil X
    have h3 : ((⌈X⌉₊ : ℕ) : ℝ) + 1 ≤ ((2 ^ Nat.clog 2 N : ℕ) : ℝ) := by
      exact_mod_cast h1
    linarith
  · by_cases hN : N = 1
    · rw [hN]
      norm_num
    · have hN1 : 1 < N := by omega
      have hc : 0 < Nat.clog 2 N := Nat.clog_pos (by norm_num) hN1
      have hlt := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) hN1
      have e : 2 ^ Nat.clog 2 N = 2 * 2 ^ (Nat.clog 2 N).pred := by
        rw [← pow_succ', Nat.add_one, Nat.succ_pred_eq_of_pos hc]
      omega

end

end SparseHamiltonian.GateQuad
