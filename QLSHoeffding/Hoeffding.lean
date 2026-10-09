import SparseLinearSystems.Statistics.BinomialTail
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Hoeffding's inequality for the binomial law

The repeated probability tests of Section `qls` use Hoeffding's inequality (equation
`qls:eq:hoeffding`): for `S` binomial with parameters `n, p` and every `t ≥ 0`,

`P(|S - n p| ≥ n t) ≤ 2 exp(-2 n t²)`,

so `n ≥ log(2/ζ)/(2t²)` repetitions estimate `p` within `t` except with probability `ζ`. The
released `SparseLinearSystems.BinomialTail` proves the weaker `2 exp(-n t²/4)` for `t ≤ 2`
(eight times the repetition count).

* `log_mgf_le` (**Hoeffding's lemma for a Bernoulli variable**):
  `log(1 - p + p e^θ) ≤ p θ + θ²/8` for `0 ≤ p ≤ 1` and every real `θ`. The function
  `g(θ) = θ²/8 - log(1 - p + p e^θ) + p θ` has `g(0) = g'(0) = 0` and
  `g'' = 1/4 - u(1 - u) ≥ 0` with `u = p e^θ/(1 - p + p e^θ)`, so `g'` is monotone and `g ≥ 0`.
* `mgf_le_sharp`: `Σ_k P(S = k) e^{θk} ≤ exp(n (p θ + θ²/8))`.
* `upper_tail_sharp`, `lower_tail_sharp`, `two_sided_sharp`: the Chernoff bounds at `θ = ±4t`,
  `exp(-2 n t²)` on each side, for every `t ≥ 0`.
* `two_sided_le_of_count_sharp`: `n ≥ log(2/ζ)/(2t²)` gives inaccurate mass at most `ζ`.
-/

set_option autoImplicit false

namespace QLSHoeffding

open Finset Real SparseLinearSystems.BinomialTail

noncomputable section

/-! ### Hoeffding's lemma for a Bernoulli variable -/

section Lemma

variable {p : ℝ}

/-- The moment generating function base `1 - p + p e^θ` is positive. -/
theorem base_pos (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (θ : ℝ) : 0 < 1 - p + p * exp θ := by
  rcases eq_or_lt_of_le hp1 with h | h
  · subst h
    simp [exp_pos]
  · have h1 : 0 ≤ p * exp θ := mul_nonneg hp0 (exp_pos θ).le
    linarith

/-- The tilted success probability `u(θ) = p e^θ / (1 - p + p e^θ)`. -/
def tilt (p θ : ℝ) : ℝ := p * exp θ / (1 - p + p * exp θ)

theorem hasDerivAt_base (p θ : ℝ) :
    HasDerivAt (fun θ => 1 - p + p * exp θ) (p * exp θ) θ := by
  have h := ((hasDerivAt_exp θ).const_mul p).const_add (1 - p)
  simpa using h

theorem hasDerivAt_tilt (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (θ : ℝ) :
    HasDerivAt (tilt p) (tilt p θ * (1 - tilt p θ)) θ := by
  have hb := base_pos hp0 hp1 θ
  have h := ((hasDerivAt_exp θ).const_mul p).div (hasDerivAt_base p θ) hb.ne'
  refine h.congr_deriv ?_
  unfold tilt
  field_simp

theorem tilt_mul_le (p θ : ℝ) : tilt p θ * (1 - tilt p θ) ≤ 1 / 4 := by
  nlinarith [sq_nonneg (tilt p θ - 1 / 2)]

theorem tilt_zero : tilt p 0 = p := by
  unfold tilt
  simp

/-- The derivative `θ/4 - u(θ) + p` of `θ²/8 - log(1 - p + p e^θ) + p θ`. -/
def slope (p θ : ℝ) : ℝ := θ / 4 - tilt p θ + p

theorem hasDerivAt_slope (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (θ : ℝ) :
    HasDerivAt (slope p) (1 / 4 - tilt p θ * (1 - tilt p θ)) θ := by
  have h1 : HasDerivAt (fun θ : ℝ => θ / 4) (1 / 4) θ := by
    simpa using (hasDerivAt_id θ).div_const 4
  have h := (h1.sub (hasDerivAt_tilt hp0 hp1 θ)).add_const p
  exact h

theorem slope_monotone (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : Monotone (slope p) := by
  apply monotone_of_deriv_nonneg
  · exact fun θ => (hasDerivAt_slope hp0 hp1 θ).differentiableAt
  · intro θ
    rw [(hasDerivAt_slope hp0 hp1 θ).deriv]
    linarith [tilt_mul_le p θ]

theorem slope_zero : slope p 0 = 0 := by
  unfold slope
  rw [tilt_zero]
  ring

/-- `g(θ) = θ²/8 - log(1 - p + p e^θ) + p θ`. -/
def gap (p θ : ℝ) : ℝ := θ ^ 2 / 8 - Real.log (1 - p + p * exp θ) + p * θ

theorem hasDerivAt_gap (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (θ : ℝ) :
    HasDerivAt (gap p) (slope p θ) θ := by
  have hb := base_pos hp0 hp1 θ
  have h1 : HasDerivAt (fun θ : ℝ => θ ^ 2 / 8) (θ / 4) θ := by
    refine ((hasDerivAt_pow 2 θ).div_const 8).congr_deriv ?_
    norm_num
    ring
  have h2 := (hasDerivAt_base p θ).log hb.ne'
  have h3 : HasDerivAt (fun θ : ℝ => p * θ) p θ := by
    simpa using (hasDerivAt_id θ).const_mul p
  have h := (h1.sub h2).add h3
  refine h.congr_deriv ?_
  unfold slope tilt
  ring

theorem gap_zero : gap p 0 = 0 := by
  unfold gap
  simp

theorem gap_nonneg (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (θ : ℝ) : 0 ≤ gap p θ := by
  have hd : ∀ x, HasDerivAt (gap p) (slope p x) x := hasDerivAt_gap hp0 hp1
  have hdiff : Differentiable ℝ (gap p) := fun x => (hd x).differentiableAt
  have hmono := slope_monotone hp0 hp1
  have h0 : slope p 0 = 0 := slope_zero
  rcases le_total 0 θ with hθ | hθ
  · have hM : MonotoneOn (gap p) (Set.Ici 0) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ici 0) hdiff.continuous.continuousOn
        hdiff.differentiableOn
      intro x hx
      rw [interior_Ici] at hx
      rw [(hd x).deriv, ← h0]
      exact hmono (le_of_lt hx)
    have := hM (Set.self_mem_Ici) hθ hθ
    rwa [gap_zero] at this
  · have hA : AntitoneOn (gap p) (Set.Iic 0) := by
      apply antitoneOn_of_deriv_nonpos (convex_Iic 0) hdiff.continuous.continuousOn
        hdiff.differentiableOn
      intro x hx
      rw [interior_Iic] at hx
      rw [(hd x).deriv, ← h0]
      exact hmono (le_of_lt hx)
    have := hA hθ (Set.self_mem_Iic) hθ
    rwa [gap_zero] at this

/-- **Hoeffding's lemma for a Bernoulli variable**: `log(1 - p + p e^θ) ≤ p θ + θ²/8`. -/
theorem log_mgf_le (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (θ : ℝ) :
    Real.log (1 - p + p * exp θ) ≤ p * θ + θ ^ 2 / 8 := by
  have h := gap_nonneg hp0 hp1 θ
  unfold gap at h
  linarith

/-- `p e^θ + (1 - p) ≤ exp(p θ + θ²/8)`. -/
theorem mgf_base_le_sharp (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (θ : ℝ) :
    p * exp θ + (1 - p) ≤ exp (p * θ + θ ^ 2 / 8) := by
  have h := log_mgf_le hp0 hp1 θ
  have hb := base_pos hp0 hp1 θ
  calc p * exp θ + (1 - p) = exp (Real.log (1 - p + p * exp θ)) := by
        rw [exp_log hb]
        ring
    _ ≤ exp (p * θ + θ ^ 2 / 8) := exp_le_exp.mpr h

end Lemma

/-! ### Binomial tails -/

/-- The exponential moment of the binomial law: `Σ_k P(S = k) e^{θk} ≤ exp(n (p θ + θ²/8))`. -/
theorem mgf_le_sharp (n : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (θ : ℝ) :
    ∑ k ∈ range (n + 1), binom n p k * exp (θ * k) ≤ exp (n * (p * θ + θ ^ 2 / 8)) := by
  have hrw : ∀ k : ℕ, exp (θ * k) = exp θ ^ k := by
    intro k
    rw [← exp_nat_mul, mul_comm]
  simp_rw [hrw]
  rw [sum_binom_mul_pow]
  have hbase : 0 ≤ p * exp θ + (1 - p) := by
    have := exp_pos θ
    nlinarith
  calc (p * exp θ + (1 - p)) ^ n ≤ exp (p * θ + θ ^ 2 / 8) ^ n :=
        pow_le_pow_left₀ hbase (mgf_base_le_sharp hp0 hp1 θ) n
    _ = exp (n * (p * θ + θ ^ 2 / 8)) := by rw [← exp_nat_mul]

/-- **Upper tail**: `P(S ≥ n(p + t)) ≤ exp(-2 n t²)` for every `t ≥ 0`. -/
theorem upper_tail_sharp (n : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {t : ℝ} (ht0 : 0 ≤ t) :
    ∑ k ∈ range (n + 1), (if (n : ℝ) * (p + t) ≤ k then binom n p k else 0) ≤
      exp (-(2 * n * t ^ 2)) := by
  set θ := 4 * t with hθ
  have hθ0 : 0 ≤ θ := by rw [hθ]; linarith
  have hterm : ∀ k ∈ range (n + 1),
      (if (n : ℝ) * (p + t) ≤ k then binom n p k else 0) ≤
        exp (-(θ * (n * (p + t)))) * (binom n p k * exp (θ * k)) := by
    intro k _
    have hb := binom_nonneg n hp0 hp1 k
    split_ifs with hk
    · have : 1 ≤ exp (-(θ * (n * (p + t)))) * exp (θ * k) := by
        rw [← exp_add]
        apply one_le_exp
        nlinarith
      nlinarith [exp_pos (-(θ * (n * (p + t)))), exp_pos (θ * k)]
    · positivity
  calc _ ≤ ∑ k ∈ range (n + 1), exp (-(θ * (n * (p + t)))) * (binom n p k * exp (θ * k)) :=
        sum_le_sum hterm
    _ = exp (-(θ * (n * (p + t)))) * ∑ k ∈ range (n + 1), binom n p k * exp (θ * k) := by
        rw [mul_sum]
    _ ≤ exp (-(θ * (n * (p + t)))) * exp (n * (p * θ + θ ^ 2 / 8)) :=
        mul_le_mul_of_nonneg_left (mgf_le_sharp n hp0 hp1 θ) (exp_pos _).le
    _ = exp (-(2 * n * t ^ 2)) := by
        rw [← exp_add]
        congr 1
        rw [hθ]
        ring

/-- **Lower tail**: `P(S ≤ n(p - t)) ≤ exp(-2 n t²)` for every `t ≥ 0`. -/
theorem lower_tail_sharp (n : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {t : ℝ} (ht0 : 0 ≤ t) :
    ∑ k ∈ range (n + 1), (if (k : ℝ) ≤ n * (p - t) then binom n p k else 0) ≤
      exp (-(2 * n * t ^ 2)) := by
  set θ := -(4 * t) with hθ
  have hterm : ∀ k ∈ range (n + 1),
      (if (k : ℝ) ≤ n * (p - t) then binom n p k else 0) ≤
        exp (-(θ * (n * (p - t)))) * (binom n p k * exp (θ * k)) := by
    intro k _
    have hb := binom_nonneg n hp0 hp1 k
    split_ifs with hk
    · have : 1 ≤ exp (-(θ * (n * (p - t)))) * exp (θ * k) := by
        rw [← exp_add]
        apply one_le_exp
        rw [hθ]
        nlinarith
      nlinarith [exp_pos (-(θ * (n * (p - t)))), exp_pos (θ * k)]
    · positivity
  calc _ ≤ ∑ k ∈ range (n + 1), exp (-(θ * (n * (p - t)))) * (binom n p k * exp (θ * k)) :=
        sum_le_sum hterm
    _ = exp (-(θ * (n * (p - t)))) * ∑ k ∈ range (n + 1), binom n p k * exp (θ * k) := by
        rw [mul_sum]
    _ ≤ exp (-(θ * (n * (p - t)))) * exp (n * (p * θ + θ ^ 2 / 8)) :=
        mul_le_mul_of_nonneg_left (mgf_le_sharp n hp0 hp1 θ) (exp_pos _).le
    _ = exp (-(2 * n * t ^ 2)) := by
        rw [← exp_add]
        congr 1
        rw [hθ]
        ring

/-- **Hoeffding's inequality for the binomial law**: `P(|S - n p| ≥ n t) ≤ 2 exp(-2 n t²)` for
every `t ≥ 0` (equation `qls:eq:hoeffding`). -/
theorem two_sided_sharp (n : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {t : ℝ} (ht0 : 0 ≤ t) :
    ∑ k ∈ range (n + 1), (if (n : ℝ) * t ≤ |(k : ℝ) - n * p| then binom n p k else 0) ≤
      2 * exp (-(2 * n * t ^ 2)) := by
  have hu := upper_tail_sharp n hp0 hp1 ht0
  have hl := lower_tail_sharp n hp0 hp1 ht0
  have hterm : ∀ k ∈ range (n + 1),
      (if (n : ℝ) * t ≤ |(k : ℝ) - n * p| then binom n p k else 0) ≤
        (if (n : ℝ) * (p + t) ≤ k then binom n p k else 0) +
          (if (k : ℝ) ≤ n * (p - t) then binom n p k else 0) := by
    intro k _
    have hb := binom_nonneg n hp0 hp1 k
    by_cases h1 : (n : ℝ) * t ≤ |(k : ℝ) - n * p|
    · rw [if_pos h1]
      rcases le_abs'.mp h1 with h | h
      · have hk : (k : ℝ) ≤ n * (p - t) := by linarith
        rw [if_pos hk]
        split_ifs <;> linarith
      · have hk : (n : ℝ) * (p + t) ≤ k := by linarith
        rw [if_pos hk]
        split_ifs <;> linarith
    · rw [if_neg h1]
      split_ifs <;> linarith
  calc _ ≤ ∑ k ∈ range (n + 1), ((if (n : ℝ) * (p + t) ≤ k then binom n p k else 0) +
          (if (k : ℝ) ≤ n * (p - t) then binom n p k else 0)) := sum_le_sum hterm
    _ = _ := sum_add_distrib
    _ ≤ exp (-(2 * n * t ^ 2)) + exp (-(2 * n * t ^ 2)) := add_le_add hu hl
    _ = 2 * exp (-(2 * n * t ^ 2)) := by ring

/-- **The repetition count of equation `qls:eq:hoeffding`**: `n ≥ log(2/ζ)/(2t²)` repetitions
estimate `p` within `t` except with probability `ζ`. -/
theorem two_sided_le_of_count_sharp (n : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {t ζ : ℝ}
    (ht0 : 0 < t) (hζ : 0 < ζ) (hn : Real.log (2 / ζ) / (2 * t ^ 2) ≤ n) :
    ∑ k ∈ range (n + 1), (if (n : ℝ) * t ≤ |(k : ℝ) - n * p| then binom n p k else 0) ≤ ζ := by
  refine (two_sided_sharp n hp0 hp1 ht0.le).trans ?_
  have ht2' : 0 < 2 * t ^ 2 := by positivity
  have h1 : Real.log (2 / ζ) ≤ 2 * n * t ^ 2 := by
    rw [div_le_iff₀ ht2'] at hn
    linarith
  have h2 : exp (-(2 * n * t ^ 2)) ≤ ζ / 2 := by
    rw [show ζ / 2 = exp (Real.log (ζ / 2)) from (Real.exp_log (by positivity)).symm]
    apply exp_le_exp.mpr
    have : Real.log (ζ / 2) = -Real.log (2 / ζ) := by
      rw [← Real.log_inv, inv_div]
    linarith
  linarith

end

end QLSHoeffding
