import OptimalPrecision.Weights.Transfer
import Mathlib.Analysis.Analytic.Polynomial

/-!
# The clock profile of a transfer `e^{-tξ(w)} g(w)`

Fix real Laguerre coordinates `β_0, …, β_{n-1}` and the signed clock weights
`λ_{k+1} = ((k+1)/2) (-1)^k β_k` (`opt:eq:weights`). For `g` holomorphic near
the origin, the signed clock functional

  `Λ(e^{-tξ} g) = ∑_{j=1}^n λ_j Ces_j(e^{-tξ} g)`

is the value at `t` of an exponential polynomial `e^{-t} prof(g)(t)`, where the
polynomial `prof(g)` depends only on the Taylor coefficients of `g`. This file
proves:

* `lamSum_eq`: the conversion `∑_j λ_j Ces_j F = ½ ∑_k (-1)^k β_k ∑_{l ≤ k} (k+1-l) [w^l]F`;
* `lamSum_vt_mul`: `Λ(e^{-tξ} g) = e^{-t} prof(g)(t)` for every `t`;
* `prof_xi_mul`: `prof(ξ g) = x prof(g)` with `x = -∂` (from `op_xs_lagE`);
* `prof_aeval_mul`: `prof(P(ξ) g) = P(x) prof(g)` for every polynomial `P`.

The profile of the constant function, `prof(1) = ¼ (x^{-2} + x^{-1}) ∑_k β_k lag_k`,
is `prof_one` in `Weights.Exact`.
-/

namespace OptimalPrecision

noncomputable section

open Nat Finset Filter Complex Polynomial
open scoped Topology Polynomial
open ExpPoly

section Profile

variable (n : ℕ) (β : ℕ → ℝ)

/-- The signed clock weights `λ_{k+1} = ((k+1)/2) (-1)^k β_k`, `λ_j = 0` otherwise. -/
def lamOf (j : ℕ) : ℝ :=
  if 1 ≤ j ∧ j ≤ n then ((j : ℝ) / 2) * (-1) ^ (j - 1) * β (j - 1) else 0

/-- The signed clock functional `∑_{j=1}^n λ_j Ces_j F`. -/
def lamSum (F : ℂ → ℂ) : ℂ := ∑ j ∈ Icc 1 n, (lamOf n β j : ℂ) * ces F j

/-- Conversion of the uniform clocks into the coefficient pairing. -/
theorem lamSum_eq (F : ℂ → ℂ) :
    lamSum n β F = (1 / 2 : ℂ) * ∑ k ∈ range n, ((-1 : ℂ) ^ k * β k) *
      ∑ l ∈ range (k + 1), ((k + 1 - l : ℕ) : ℂ) * coeff F l := by
  unfold lamSum
  -- reindex `j = k + 1`
  have hIcc : Icc 1 n = (range n).map ⟨(· + 1), add_left_injective 1⟩ := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk]
    constructor
    · intro h; exact ⟨j - 1, by omega, by omega⟩
    · rintro ⟨k, hk, rfl⟩; omega
  rw [hIcc, Finset.sum_map, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn := Finset.mem_range.mp hk
  simp only [Function.Embedding.coeFn_mk, lamOf, if_pos (show 1 ≤ k + 1 ∧ k + 1 ≤ n by omega),
    Nat.add_sub_cancel, ces]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l hl => ?_
  have hlk := Finset.mem_range.mp hl
  have hk1 : ((k + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  rw [smul_eq_mul]
  push_cast
  have hcast : ((k + 1 - l : ℕ) : ℂ) = (k : ℂ) + 1 - l := by
    push_cast [Nat.cast_sub (by omega : l ≤ k + 1)]; ring
  rw [hcast]
  field_simp

/-- The profile polynomial of a coefficient sequence `κ`. -/
def prof (κ : ℕ → ℂ) : ℂ[X] :=
  (1 / 2 : ℂ) • ∑ k ∈ range n, ((-1 : ℂ) ^ k * β k) •
    ∑ l ∈ range (k + 1), ((k + 1 - l : ℕ) : ℂ) • ∑ i ∈ range (l + 1), κ i • lagE (l - i)

theorem prof_add (κ ν : ℕ → ℂ) : prof n β (κ + ν) = prof n β κ + prof n β ν := by
  simp only [prof, Pi.add_apply, add_smul, Finset.sum_add_distrib, smul_add]

theorem prof_smul (c : ℂ) (κ : ℕ → ℂ) : prof n β (c • κ) = c • prof n β κ := by
  simp only [prof, Pi.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ =>
    Finset.sum_congr rfl fun i _ => ?_
  congr 1
  ring

/-- **The profile computes the clock** on `e^{-tξ} g`. -/
theorem lamSum_vt_mul {g : ℂ → ℂ} (hg : AnalyticAt ℂ g 0) (t : ℂ) :
    lamSum n β (fun w => vt t w * g w) = ev t (prof n β (coeff g)) := by
  rw [lamSum_eq, prof, ev_smul, ev_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [ev_smul, ev_sum]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [ev_smul, ev_sum]
  congr 1
  rw [show (fun w => vt t w * g w) = (fun w => g w * vt t w) by funext w; ring,
    coeff_mul hg (analyticAt_vt t)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ev_smul, coeff_vt]

/-! ### Multiplication by `ξ` -/

/-- Taylor coefficients of `ξ`. -/
theorem coeff_xi (a : ℕ) : coeff xi a = (xic a : ℂ) := by
  have hball : Metric.ball (0 : ℂ) 1 ∈ 𝓝 (0 : ℂ) := Metric.ball_mem_nhds 0 one_pos
  -- `ξ = -1 + 2/(1+w)` and `[w^a] 1/(1+w) = (-1)^a`
  have hinv : ∀ a : ℕ, coeff (fun w : ℂ => (1 + w)⁻¹) a = (-1) ^ a := by
    intro a
    have han : AnalyticAt ℂ (fun w : ℂ => (1 + w)⁻¹) 0 :=
      (analyticAt_const.add analyticAt_id).inv (by simp)
    induction a with
    | zero => simp [coeff_zero_eq]
    | succ a ih =>
      -- `(1 + w) (1+w)⁻¹ = 1` gives `c_{a+1} + c_a = 0`
      have h1 : (fun w : ℂ => (1 + w)⁻¹ + w * (1 + w)⁻¹) =ᶠ[𝓝 0] (fun _ => (1 : ℂ)) := by
        filter_upwards [hball] with w hw
        have := one_add_ne_zero_of_norm_lt (by simpa using hw)
        field_simp
      have h2 := coeff_congr h1 (a + 1)
      have hwan : AnalyticAt ℂ (fun w : ℂ => w * (1 + w)⁻¹) 0 := analyticAt_id.fun_mul han
      rw [coeff_add han hwan, coeff_X_mul han, coeff_const, if_neg
        (Nat.succ_ne_zero a), ih] at h2
      rw [pow_succ]
      linear_combination h2
  have hξ : xi =ᶠ[𝓝 0] fun w => (2 : ℂ) • (1 + w)⁻¹ - (fun _ => (1 : ℂ)) w := by
    filter_upwards [hball] with w hw
    have := one_add_ne_zero_of_norm_lt (by simpa using hw)
    simp only [xi, smul_eq_mul]
    field_simp
    ring
  have han : AnalyticAt ℂ (fun w : ℂ => (1 + w)⁻¹) 0 :=
    (analyticAt_const.add analyticAt_id).inv (by simp)
  have h2an : AnalyticAt ℂ (fun w : ℂ => (2 : ℂ) • (1 + w)⁻¹) 0 := han.fun_const_smul
  rw [coeff_congr hξ, coeff_sub h2an analyticAt_const,
    coeff_const_smul_field, hinv, coeff_const]
  rcases a with _ | a
  · simp [xic]; norm_num
  · simp [xic]

/-- Triangle reindexing of a Cauchy convolution against `E`. -/
theorem conv_assoc (ξc κ : ℕ → ℂ) (l : ℕ) :
    ∑ i ∈ range (l + 1), (∑ a ∈ range (i + 1), ξc a * κ (i - a)) • (lagE (l - i) : ℂ[X]) =
      ∑ b ∈ range (l + 1), κ b • ∑ a ∈ range (l - b + 1), ξc a • (lagE (l - b - a) : ℂ[X]) := by
  have h1 : ∀ i ∈ range (l + 1), (∑ a ∈ range (i + 1), ξc a * κ (i - a)) • (lagE (l - i) : ℂ[X]) =
      ∑ b ∈ range (i + 1), (κ b * ξc (i - b)) • (lagE (l - (b + (i - b))) : ℂ[X]) := by
    intro i hi
    rw [Finset.sum_smul, ← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun b hb => ?_
    have hbi := Finset.mem_range.mp hb
    rw [show i + 1 - 1 - b = i - b by omega, show i - (i - b) = b by omega, mul_comm,
      show b + (i - b) = i by omega]
  rw [Finset.sum_congr rfl h1, Finset.sum_range_diag_flip (l + 1)
    (fun b a => (κ b * ξc a) • (lagE (l - (b + a)) : ℂ[X]))]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [Finset.smul_sum]
  have hbl := Finset.mem_range.mp hb
  rw [show l + 1 - b = l - b + 1 by omega]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [smul_smul, show l - (b + a) = l - b - a by omega]

/-- **Multiplication by `ξ` acts as `x = -∂` on the profile.** -/
theorem prof_xi_mul {g : ℂ → ℂ} (hg : AnalyticAt ℂ g 0) :
    prof n β (coeff (fun w => xi w * g w)) = op xs (prof n β (coeff g)) := by
  have hcoeff : coeff (fun w => xi w * g w) =
      fun i => ∑ a ∈ range (i + 1), (xic a : ℂ) * coeff g (i - a) := by
    funext i
    rw [coeff_mul analyticAt_xi hg]
    simp only [coeff_xi]
  rw [hcoeff]
  unfold prof
  rw [op_smul_right, op_sum_right]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [op_smul_right, op_sum_right]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [op_smul_right, op_sum_right, conv_assoc]
  congr 1
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [op_smul_right, op_xs_lagE]
  have hbl := Finset.mem_range.mp hb
  congr 1

theorem analyticAt_eval_xi (p : ℂ[X]) : AnalyticAt ℂ (fun w => p.eval (xi w)) 0 := by
  simpa only [Polynomial.coe_aeval_eq_eval] using analyticAt_xi.aeval_polynomial p

/-- **Polynomials in `ξ` act as polynomials in `x`.** -/
theorem prof_aeval_mul (P : ℂ[X]) {g : ℂ → ℂ} (hg : AnalyticAt ℂ g 0) :
    prof n β (coeff (fun w => P.eval (xi w) * g w)) =
      op (Polynomial.aeval (xs : PowerSeries ℂ) P) (prof n β (coeff g)) := by
  induction P using Polynomial.induction_on' with
  | add p r hp hr =>
    have hp' : AnalyticAt ℂ (fun w => p.eval (xi w) * g w) 0 :=
      (analyticAt_eval_xi p).fun_mul hg
    have hr' : AnalyticAt ℂ (fun w => r.eval (xi w) * g w) 0 :=
      (analyticAt_eval_xi r).fun_mul hg
    have : (fun w => (p + r).eval (xi w) * g w) =
        fun w => p.eval (xi w) * g w + r.eval (xi w) * g w := by
      funext w; simp [add_mul]
    rw [this, show coeff (fun w => p.eval (xi w) * g w + r.eval (xi w) * g w) =
      coeff (fun w => p.eval (xi w) * g w) + coeff (fun w => r.eval (xi w) * g w) by
        funext i; exact coeff_add hp' hr' i, prof_add, hp, hr, map_add, op_add_left]
  | monomial j c =>
    induction j generalizing g with
    | zero =>
      have : (fun w => (monomial 0 c).eval (xi w) * g w) = fun w => c • g w := by
        funext w; simp
      rw [this, show coeff (fun w => c • g w) = c • coeff g by
        funext i; exact coeff_const_smul_field c g i, prof_smul]
      simp only [monomial_zero_left, aeval_C]
      rw [show (algebraMap ℂ (PowerSeries ℂ)) c = c • (1 : PowerSeries ℂ) by
        rw [Algebra.algebraMap_eq_smul_one], op_smul_left, op_one]
    | succ j ih =>
      have hξg : AnalyticAt ℂ (fun w => xi w * g w) 0 := analyticAt_xi.fun_mul hg
      have : (fun w => (monomial (j + 1) c).eval (xi w) * g w) =
          fun w => (monomial j c).eval (xi w) * (xi w * g w) := by
        funext w; simp [pow_succ]; ring
      rw [this, ih hξg, prof_xi_mul n β hg, ← op_mul]
      congr 1
      simp only [aeval_monomial, pow_succ]
      ring

end Profile

end

end OptimalPrecision
