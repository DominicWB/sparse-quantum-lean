import OptimalPrecision.Taylor.Basic
import Mathlib.Analysis.Complex.Liouville
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Cauchy estimates and the Fejér contraction of the uniform clock

* `norm_coeff_le`: Cauchy's estimate `‖[w^k] f‖ ≤ B / ρ^k`.
* `coeff_eq_zero_of_norm_le_pow`: a function vanishing to order `m + 1` at the
  origin has zero Taylor coefficients up to order `m`.
* `norm_ces_le`: for `f` holomorphic on the open unit disk with `‖f‖ ≤ B`
  there, every uniform clock functional obeys `‖Ces_j f‖ ≤ B`. This is the
  operator-norm bound `opt:eq:interval-bound` of the proof of `opt:lem:tail`;
  the positive Fejér kernel is sampled at roots of unity, so no contour
  integral is used.
-/

namespace OptimalPrecision

noncomputable section

open Nat Finset Filter Metric Complex
open scoped Topology Real

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- Cauchy's estimate for Taylor coefficients at the origin. -/
theorem norm_coeff_le {f : ℂ → E} {ρ B : ℝ} (hρ : 0 < ρ)
    (hf : DiffContOnCl ℂ f (ball 0 ρ)) (hB : ∀ z ∈ sphere (0 : ℂ) ρ, ‖f z‖ ≤ B) (k : ℕ) :
    ‖coeff f k‖ ≤ B / ρ ^ k := by
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hρ hf hB
  have hk : (0 : ℝ) < k ! := by exact_mod_cast Nat.factorial_pos k
  rw [coeff, norm_smul, norm_inv, RCLike.norm_natCast, inv_mul_le_iff₀ hk]
  calc ‖iteratedDeriv k f 0‖ ≤ k ! * B / ρ ^ k := h
    _ = k ! * (B / ρ ^ k) := by ring

/-- Cauchy's estimate for a function holomorphic on a larger open ball. -/
theorem norm_coeff_le_of_ball {f : ℂ → E} {r ρ B : ℝ} (hρ : 0 < ρ) (hρr : ρ < r)
    (hf : DifferentiableOn ℂ f (ball 0 r)) (hB : ∀ z : ℂ, ‖z‖ = ρ → ‖f z‖ ≤ B) (k : ℕ) :
    ‖coeff f k‖ ≤ B / ρ ^ k :=
  norm_coeff_le hρ (hf.diffContOnCl_ball (closedBall_subset_ball hρr))
    (fun z hz => hB z (by simpa using hz)) k

/-- A holomorphic function with `‖f w‖ ≤ C ‖w‖^(m+1)` near the origin has
vanishing Taylor coefficients of order at most `m`. -/
theorem coeff_eq_zero_of_norm_le_pow {f : ℂ → E} {r C : ℝ} {m : ℕ} (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (ball 0 r))
    (hC : ∀ w : ℂ, ‖w‖ < r → ‖f w‖ ≤ C * ‖w‖ ^ (m + 1)) {k : ℕ} (hk : k ≤ m) :
    coeff f k = 0 := by
  have hC0 : ∀ ρ : ℝ, 0 < ρ → ρ < r → ρ ≤ 1 → ‖coeff f k‖ ≤ |C| * ρ := by
    intro ρ hρ hρr hρ1
    have h := norm_coeff_le_of_ball (B := |C| * ρ ^ (m + 1)) hρ hρr hf
      (fun z hz => (hC z (hz ▸ hρr)).trans (by
        rw [hz]; exact mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))) k
    calc ‖coeff f k‖ ≤ |C| * ρ ^ (m + 1) / ρ ^ k := h
      _ = |C| * ρ * ρ ^ (m - k) := by
          have hρk : ρ ^ k ≠ 0 := pow_ne_zero _ hρ.ne'
          rw [show m + 1 = (m - k) + 1 + k by omega, pow_add, pow_succ]
          field_simp
      _ ≤ |C| * ρ * 1 := by
          apply mul_le_mul_of_nonneg_left (pow_le_one₀ hρ.le hρ1) (by positivity)
      _ = |C| * ρ := mul_one _
  apply norm_le_zero_iff.mp
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set ρ : ℝ := min (r / 2) (min 1 (ε / (|C| + 1))) with hρdef
  have hρ : 0 < ρ := by
    simp only [hρdef, lt_min_iff]
    exact ⟨by linarith, by norm_num, by positivity⟩
  have hρr : ρ < r := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hρ1 : ρ ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hρε : ρ ≤ ε / (|C| + 1) := (min_le_right _ _).trans (min_le_right _ _)
  have := hC0 ρ hρ hρr hρ1
  have hCρ : |C| * ρ ≤ ε := by
    calc |C| * ρ ≤ (|C| + 1) * ρ := by nlinarith [abs_nonneg C]
      _ ≤ (|C| + 1) * (ε / (|C| + 1)) := by
          apply mul_le_mul_of_nonneg_left hρε (by positivity)
      _ = ε := by field_simp
  linarith

/-- Taylor expansion at the origin on the unit disk, in coefficient form. -/
theorem hasSum_coeff {f : ℂ → E} {r : ℝ} (hf : DifferentiableOn ℂ f (ball 0 r)) {z : ℂ}
    (hz : ‖z‖ < r) : HasSum (fun k => z ^ k • coeff f k) (f z) := by
  have h := Complex.hasSum_taylorSeries_on_ball hf (z := z) (by simpa using hz)
  simp only [sub_zero] at h
  convert h using 2 with k
  rw [coeff, smul_comm]

end

end OptimalPrecision
