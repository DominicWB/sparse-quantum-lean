import SparseHamiltonian.ManuscriptPrecision

/-!
# Query-count arithmetic for Corollary `hs:cor:unitary`

Real-number inequalities used by the unitary-implementation endpoints. Throughout
`ℓ = log (1 / ε)` with `0 < ε ≤ 1 / 2`, so `ℓ ≥ log 2 > 0`.

* `exact_shape_le`: the bound of Theorem `hs:thm:main`
  (`ImprovedSparseHamiltonian.simulation_log_one`) at `s = N`, `η = 1`, `t = π/2` is at most
  `497664 π (√N + √(N ℓ) + ℓ)`.
* `inexact_shape_le`: the same bound at `η = 2` and precision `ε/2` is at most
  `995328 π (√N + √(N ℓ) + ℓ)`.
* `sqrt_le_absorb`: `√N ≤ (log 2)^{-1/2} √(N ℓ)`, written with `(√(log 2))⁻¹`; this absorbs the
  first term (`three_term_le_two_term`), as in the proof of Corollary `hs:cor:unitary`.
* `three_term_le_root`: for `ℓ ≤ N` the three-term count is `O(√(N ℓ))`, the order of
  `hs:eq:unitarybound` there; `two_term_le_hybrid`: `√(N ℓ) + ℓ` exceeds
  `√(N ℓ) + ℓ/log(e + ℓ/N)` by at most the factor `log(e + ℓ/N)`.
* `duhamel_term_eq_half` and `card_mul_sq_le_one`: the entrywise allowance `ξ = ε/(π N)` gives the
  Duhamel term `(π/2) N ξ = ε/2` and `N ξ² ≤ 1`; `energy_le_four` turns the latter into the row
  and column norm bound `η = 2`.
-/

set_option autoImplicit false

namespace SparseHamiltonian.UnitaryPrecision

noncomputable section
open scoped BigOperators

/-- The logarithm `ℓ = log (1 / ε)` is at least `log 2` on the manuscript precision range. -/
theorem log_two_le_log_one (ε : ℝ) (hε : 0 < ε) (hεHalf : ε ≤ 1 / 2) :
    Real.log 2 ≤ Real.log (1 / ε) := by
  apply Real.log_le_log (by norm_num)
  rw [le_div_iff₀ hε]
  linarith

/-- In particular `ℓ = log (1 / ε)` is nonnegative. -/
theorem log_one_nonneg (ε : ℝ) (hε : 0 < ε) (hεHalf : ε ≤ 1 / 2) :
    0 ≤ Real.log (1 / ε) :=
  (Real.log_nonneg (by norm_num)).trans (log_two_le_log_one ε hε hεHalf)

/-- The bound of Theorem `hs:thm:main` at `η = 1`, `t = π/2` and sparsity `N`, in the form
`497664 π (√N + √(N ℓ) + ℓ)`. Only `√(π/2) ≤ π/2` and `1 ≤ π/2` are used. -/
theorem exact_shape_le (N ℓ : ℝ) (hℓ : 0 ≤ ℓ) :
    995328 * (Real.sqrt N * (1 * |Real.pi / 2|) +
        Real.sqrt (N * (1 * |Real.pi / 2|) * ℓ) + ℓ) ≤
      497664 * Real.pi * (Real.sqrt N + Real.sqrt (N * ℓ) + ℓ) := by
  have hpi : (1 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_gt_three]
  have hpi0 : (0 : ℝ) ≤ Real.pi / 2 := by linarith
  have hsplit : Real.sqrt (N * (1 * |Real.pi / 2|) * ℓ) =
      Real.sqrt (Real.pi / 2) * Real.sqrt (N * ℓ) := by
    rw [one_mul, abs_of_nonneg hpi0,
      show N * (Real.pi / 2) * ℓ = Real.pi / 2 * (N * ℓ) by ring, Real.sqrt_mul hpi0]
  have hroot : Real.sqrt (Real.pi / 2) ≤ Real.pi / 2 := by
    rw [Real.sqrt_le_left hpi0]
    nlinarith
  have hmix : Real.sqrt (Real.pi / 2) * Real.sqrt (N * ℓ) ≤
      Real.pi / 2 * Real.sqrt (N * ℓ) :=
    mul_le_mul_of_nonneg_right hroot (Real.sqrt_nonneg _)
  have hlog : ℓ ≤ Real.pi / 2 * ℓ := le_mul_of_one_le_left hℓ hpi
  rw [hsplit, one_mul, abs_of_nonneg hpi0]
  calc
    995328 * (Real.sqrt N * (Real.pi / 2) +
        Real.sqrt (Real.pi / 2) * Real.sqrt (N * ℓ) + ℓ) ≤
      995328 * (Real.sqrt N * (Real.pi / 2) + Real.pi / 2 * Real.sqrt (N * ℓ) +
        Real.pi / 2 * ℓ) := by
      have := add_le_add (add_le_add (le_refl (Real.sqrt N * (Real.pi / 2))) hmix) hlog
      linarith
    _ = 497664 * Real.pi * (Real.sqrt N + Real.sqrt (N * ℓ) + ℓ) := by ring

/-- The bound of Theorem `hs:thm:main` at `η = 2`, `t = π/2`, precision `ε/2` and sparsity
`N`, in the form `995328 π (√N + √(N ℓ) + ℓ)` with `ℓ = log (1 / ε)`. It uses
`log (2 / ε) ≤ 2 ℓ` (`ManuscriptPrecision.log_two_le_twice_log_one`), `√(2π) ≤ π` and
`2 ≤ π`. -/
theorem inexact_shape_le (N ε : ℝ) (hN : 0 ≤ N) (hε : 0 < ε) (hεHalf : ε ≤ 1 / 2) :
    995328 * (Real.sqrt N * (2 * |Real.pi / 2|) +
        Real.sqrt (N * (2 * |Real.pi / 2|) * Real.log (1 / (ε / 2))) +
          Real.log (1 / (ε / 2))) ≤
      995328 * Real.pi *
        (Real.sqrt N + Real.sqrt (N * Real.log (1 / ε)) + Real.log (1 / ε)) := by
  have hpi0 : (0 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_gt_three]
  have hpi2 : (2 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hℓ := log_one_nonneg ε hε hεHalf
  have hhalf : Real.log (1 / (ε / 2)) = Real.log (2 / ε) := by
    congr 1
    field_simp
  have hB : Real.log (2 / ε) ≤ 2 * Real.log (1 / ε) :=
    ManuscriptPrecision.log_two_le_twice_log_one ε hε hεHalf
  have hB0 : 0 ≤ Real.log (2 / ε) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hε]
    linarith
  have htime : 2 * |Real.pi / 2| = Real.pi := by
    rw [abs_of_nonneg hpi0]
    ring
  rw [hhalf, htime]
  have hroot : Real.sqrt (N * Real.pi * Real.log (2 / ε)) ≤
      Real.pi * Real.sqrt (N * Real.log (1 / ε)) := by
    have hmono : Real.sqrt (N * Real.pi * Real.log (2 / ε)) ≤
        Real.sqrt (2 * Real.pi * (N * Real.log (1 / ε))) := by
      apply Real.sqrt_le_sqrt
      have := mul_le_mul_of_nonneg_left hB (mul_nonneg hN Real.pi_pos.le)
      linarith
    have hsplit : Real.sqrt (2 * Real.pi * (N * Real.log (1 / ε))) =
        Real.sqrt (2 * Real.pi) * Real.sqrt (N * Real.log (1 / ε)) :=
      Real.sqrt_mul (by positivity) _
    have hconst : Real.sqrt (2 * Real.pi) ≤ Real.pi := by
      rw [Real.sqrt_le_left Real.pi_pos.le]
      nlinarith
    rw [hsplit] at hmono
    exact hmono.trans (mul_le_mul_of_nonneg_right hconst (Real.sqrt_nonneg _))
  have hlog : Real.log (2 / ε) ≤ Real.pi * Real.log (1 / ε) := by
    have := mul_le_mul_of_nonneg_right hpi2 hℓ
    linarith
  calc
    995328 * (Real.sqrt N * Real.pi + Real.sqrt (N * Real.pi * Real.log (2 / ε)) +
        Real.log (2 / ε)) ≤
      995328 * (Real.sqrt N * Real.pi + Real.pi * Real.sqrt (N * Real.log (1 / ε)) +
        Real.pi * Real.log (1 / ε)) := by
      have := add_le_add (add_le_add (le_refl (Real.sqrt N * Real.pi)) hroot) hlog
      linarith
    _ = 995328 * Real.pi *
        (Real.sqrt N + Real.sqrt (N * Real.log (1 / ε)) + Real.log (1 / ε)) := by ring

/-- The absorption step of Corollary `hs:cor:unitary`: since `ℓ = log (1 / ε) ≥ log 2 > 0`,
`√N ≤ (log 2)^{-1/2} √(N ℓ)`. -/
theorem sqrt_le_absorb (N ε : ℝ) (hN : 0 ≤ N) (hε : 0 < ε) (hεHalf : ε ≤ 1 / 2) :
    Real.sqrt N ≤ (Real.sqrt (Real.log 2))⁻¹ * Real.sqrt (N * Real.log (1 / ε)) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hroot2 : 0 < Real.sqrt (Real.log 2) := Real.sqrt_pos.mpr hlog2
  have hmono : Real.sqrt (Real.log 2) ≤ Real.sqrt (Real.log (1 / ε)) :=
    Real.sqrt_le_sqrt (log_two_le_log_one ε hε hεHalf)
  rw [Real.sqrt_mul hN, inv_mul_eq_div, le_div_iff₀ hroot2]
  exact mul_le_mul_of_nonneg_left hmono (Real.sqrt_nonneg N)

/-- The three-term count `C (√N + √(N ℓ) + ℓ)` is at most the two-term count
`C (1 + (log 2)^{-1/2}) (√(N ℓ) + ℓ)`. -/
theorem three_term_le_two_term (C N ε : ℝ) (hC : 0 ≤ C) (hN : 0 ≤ N) (hε : 0 < ε)
    (hεHalf : ε ≤ 1 / 2) :
    C * (Real.sqrt N + Real.sqrt (N * Real.log (1 / ε)) + Real.log (1 / ε)) ≤
      C * (1 + (Real.sqrt (Real.log 2))⁻¹) *
        (Real.sqrt (N * Real.log (1 / ε)) + Real.log (1 / ε)) := by
  have hAbsorb := sqrt_le_absorb N ε hN hε hεHalf
  have hℓ := log_one_nonneg ε hε hεHalf
  have hc : 0 ≤ (Real.sqrt (Real.log 2))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hcℓ : 0 ≤ (Real.sqrt (Real.log 2))⁻¹ * Real.log (1 / ε) := mul_nonneg hc hℓ
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hC
  nlinarith

/-- In the regime `ℓ ≤ N` (`ε ≥ e^{-N}`) the three-term count is `O(√(N ℓ))`, which is the order
of `hs:eq:unitarybound` there. -/
theorem three_term_le_root (C N ε : ℝ) (hC : 0 ≤ C) (hN : 0 ≤ N) (hε : 0 < ε)
    (hεHalf : ε ≤ 1 / 2) (hℓN : Real.log (1 / ε) ≤ N) :
    C * (Real.sqrt N + Real.sqrt (N * Real.log (1 / ε)) + Real.log (1 / ε)) ≤
      C * (2 + (Real.sqrt (Real.log 2))⁻¹) * Real.sqrt (N * Real.log (1 / ε)) := by
  have hAbsorb := sqrt_le_absorb N ε hN hε hεHalf
  have hℓ := log_one_nonneg ε hε hεHalf
  have hlin : Real.log (1 / ε) ≤ Real.sqrt (N * Real.log (1 / ε)) := by
    calc
      Real.log (1 / ε) = Real.sqrt (Real.log (1 / ε) * Real.log (1 / ε)) :=
        (Real.sqrt_mul_self hℓ).symm
      _ ≤ Real.sqrt (N * Real.log (1 / ε)) :=
        Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hℓN hℓ)
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hC
  nlinarith

/-- For every `ε`, the formalised additive term exceeds that of `hs:eq:unitarybound` by at most
the factor `log(e + ℓ/N)`. -/
theorem two_term_le_hybrid (N ℓ : ℝ) (hN : 0 < N) (hℓ : 0 ≤ ℓ) :
    Real.sqrt (N * ℓ) + ℓ ≤
      Real.log (Real.exp 1 + ℓ / N) *
        (Real.sqrt (N * ℓ) + ℓ / Real.log (Real.exp 1 + ℓ / N)) := by
  have hge : 1 ≤ Real.log (Real.exp 1 + ℓ / N) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have : 0 ≤ ℓ / N := div_nonneg hℓ hN.le
    linarith
  have hpos : 0 < Real.log (Real.exp 1 + ℓ / N) := by linarith
  rw [mul_add, mul_div_cancel₀ _ hpos.ne']
  have := mul_le_mul_of_nonneg_right hge (Real.sqrt_nonneg (N * ℓ))
  linarith

/-- The entrywise allowance `ξ = ε/(π N)` makes the Duhamel term `(π/2) N ξ` exactly `ε/2`. -/
theorem duhamel_term_eq_half (N ε : ℝ) (hN : 0 < N) :
    |Real.pi / 2| * (N * (ε / (Real.pi * N))) = ε / 2 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  rw [abs_of_pos (by positivity)]
  field_simp

/-- The entrywise allowance `ξ = ε/(π N)` satisfies `N ξ² ≤ 1` for `N ≥ 1`, `ε ≤ 1/2`. -/
theorem card_mul_sq_le_one (N ε : ℝ) (hN : 1 ≤ N) (hε : 0 < ε) (hεHalf : ε ≤ 1 / 2) :
    N * (ε / (Real.pi * N)) ^ 2 ≤ 1 := by
  have hpi : 3 < Real.pi := Real.pi_gt_three
  have hN0 : 0 < N := by linarith
  have hident : N * (ε / (Real.pi * N)) ^ 2 = ε ^ 2 / (Real.pi ^ 2 * N) := by
    field_simp
  rw [hident, div_le_one (by positivity)]
  nlinarith

/-- A vector within `ξ` entrywise of a vector of Euclidean norm at most one has squared norm at
most `2² = 4` when `(card ι) ξ² ≤ 1`. -/
theorem energy_le_four {ι : Type*} [Fintype ι] (u v : ι → ℂ) (ξ : ℝ)
    (hu : ∑ j, ‖u j‖ ^ 2 ≤ 1) (hv : ∀ j, ‖v j - u j‖ ≤ ξ)
    (hξ : (Fintype.card ι : ℝ) * ξ ^ 2 ≤ 1) :
    ∑ j, ‖v j‖ ^ 2 ≤ (2 : ℝ) ^ 2 := by
  have hpoint (j : ι) : ‖v j‖ ^ 2 ≤ 2 * ‖u j‖ ^ 2 + 2 * ξ ^ 2 := by
    have htri : ‖v j‖ ≤ ‖u j‖ + ξ := by
      calc
        ‖v j‖ = ‖u j + (v j - u j)‖ := by rw [add_sub_cancel]
        _ ≤ ‖u j‖ + ‖v j - u j‖ := norm_add_le _ _
        _ ≤ ‖u j‖ + ξ := by linarith [hv j]
    have hsq : ‖v j‖ ^ 2 ≤ (‖u j‖ + ξ) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) htri 2
    nlinarith [sq_nonneg (‖u j‖ - ξ)]
  calc
    ∑ j, ‖v j‖ ^ 2 ≤ ∑ j, (2 * ‖u j‖ ^ 2 + 2 * ξ ^ 2) :=
      Finset.sum_le_sum (fun j _ => hpoint j)
    _ = 2 * ∑ j, ‖u j‖ ^ 2 + 2 * ((Fintype.card ι : ℝ) * ξ ^ 2) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul]
      ring
    _ ≤ (2 : ℝ) ^ 2 := by nlinarith

end
end SparseHamiltonian.UnitaryPrecision
