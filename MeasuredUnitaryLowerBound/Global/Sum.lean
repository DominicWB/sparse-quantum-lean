import UnitaryImplementationExtensions.Search

set_option autoImplicit false

/-!
# Summed pair gaps: the real inequality behind the endpoint search bound

The lower half of Corollary `hs:cor:unitary` of the manuscript (error range
`0 < ε ≤ 1/2`; the reduction to unstructured search) at the endpoint
`ε = 1/2` of trace-distance accuracy cannot use a uniform pair gap: an output
`(|m⟩⟨m| + |m'⟩⟨m'|)/2` is within trace distance `1/2` of both `|m⟩` and `|m'⟩`. The gaps
`g(x, x')` of the pair observables are nonnegative only on average over the pairs. This module
turns averaged gaps into a lower bound on the summed kernel deficit
`∑_{x ≠ x'} (1 - k(x, x'))`, the quantity bounded by the adversary progress.

* `sq_sum_adversary_le`: Cauchy-Schwarz over the `N (N - 1)` ordered pairs `x ≠ x'`.
* `sum_le_of_gaps`: if `k(x, x') ≤ 1` and `k(x, x') ≤ 1 - g(x, x')²/8` whenever
  `g(x, x') ≥ 0`, for all `x ≠ x'`, and `∑_{x ≠ x'} g(x, x') ≥ 2 N b` with `b ≥ 0`, then
  `N b² ≤ 2 (N - 1) ∑_{x ≠ x'} (1 - k(x, x'))`.

The pair weights are the all-pairs search adversary
`UnitaryImplementationExtensions.Search.adversary` (`1` off the diagonal, `0` on it).
-/

namespace MeasuredUnitaryLowerBound.Global

noncomputable section
open UnitaryImplementationExtensions

/-- The all-pairs search adversary has total weight `N (N - 1)`. -/
theorem adversary_total {N : ℕ} :
    ∑ x : Fin N, ∑ x' : Fin N, Search.adversary N x x' = (N : ℝ) * ((N : ℝ) - 1) := by
  classical
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · subst h0; simp
  have hrow : ∀ m : Fin N, ∑ m', Search.adversary N m m' = (N : ℝ) - 1 := by
    intro m
    have hterm : ∀ m', Search.adversary N m m' = if m' = m then 0 else 1 := by
      intro m'
      by_cases h : m' = m
      · simp [Search.adversary, h]
      · simp [Search.adversary, h, Ne.symm h]
    rw [Finset.sum_congr rfl fun m' _ => hterm m', Finset.sum_ite, Finset.sum_const_zero,
      zero_add, Finset.sum_const, nsmul_eq_mul, mul_one, Finset.filter_ne' Finset.univ m,
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin,
      Nat.cast_sub (by omega), Nat.cast_one]
  rw [Finset.sum_congr rfl fun m _ => hrow m, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]

/-- **Cauchy-Schwarz over the ordered pairs.** For any real function `f` on pairs,
`(∑_{x ≠ x'} f(x, x'))² ≤ N (N - 1) ∑_{x ≠ x'} f(x, x')²`. -/
theorem sq_sum_adversary_le {N : ℕ} (f : Fin N → Fin N → ℝ) :
    (∑ x, ∑ x', Search.adversary N x x' * f x x') ^ 2 ≤
      (N : ℝ) * ((N : ℝ) - 1) * ∑ x, ∑ x', Search.adversary N x x' * f x x' ^ 2 := by
  classical
  have hsq : ∀ x x' : Fin N, Search.adversary N x x' ^ 2 = Search.adversary N x x' := by
    intro x x'; unfold Search.adversary; split_ifs <;> norm_num
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin N × Fin N))
    (fun p => Search.adversary N p.1 p.2) (fun p => Search.adversary N p.1 p.2 * f p.1 p.2)
  have e1 : ∀ x x' : Fin N, Search.adversary N x x' * (Search.adversary N x x' * f x x') =
      Search.adversary N x x' * f x x' := by
    intro x x'; rw [← mul_assoc, ← sq, hsq]
  have e2 : ∀ x x' : Fin N, (Search.adversary N x x' * f x x') ^ 2 =
      Search.adversary N x x' * f x x' ^ 2 := by
    intro x x'; rw [mul_pow, hsq]
  simp only [Fintype.sum_prod_type, e1, e2, hsq, adversary_total] at hcs
  exact hcs

/-- **Summed kernel deficit from averaged gaps.** Let `k, g` be real functions on the pairs of
`Fin N`, `N ≥ 2`, with `k(x, x') ≤ 1` for `x ≠ x'`, and `k(x, x') ≤ 1 - g(x, x')²/8` whenever
`x ≠ x'` and `g(x, x') ≥ 0`. If the gaps sum to at least `2 N b` over the ordered pairs, with
`b ≥ 0`, then `N b² ≤ 2 (N - 1) ∑_{x ≠ x'} (1 - k(x, x'))`. -/
theorem sum_le_of_gaps {N : ℕ} (hN : 2 ≤ N) (k g : Fin N → Fin N → ℝ) {b : ℝ} (hb : 0 ≤ b)
    (hk : ∀ x x', x ≠ x' → k x x' ≤ 1)
    (hkg : ∀ x x', x ≠ x' → 0 ≤ g x x' → k x x' ≤ 1 - g x x' ^ 2 / 8)
    (hsum : 2 * (N : ℝ) * b ≤ ∑ x, ∑ x', Search.adversary N x x' * g x x') :
    (N : ℝ) * b ^ 2 ≤
      2 * ((N : ℝ) - 1) * ∑ x, ∑ x', Search.adversary N x x' * (1 - k x x') := by
  classical
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have h1 : ∑ x, ∑ x', Search.adversary N x x' * g x x' ≤
      ∑ x, ∑ x', Search.adversary N x x' * max (g x x') 0 := by
    refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun x' _ => ?_
    by_cases h : x = x'
    · simp [Search.adversary, h]
    · simp only [Search.adversary, h, if_false, one_mul]
      exact le_max_left _ _
  have h2 : ∑ x, ∑ x', Search.adversary N x x' * max (g x x') 0 ^ 2 ≤
      8 * ∑ x, ∑ x', Search.adversary N x x' * (1 - k x x') := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun x _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun x' _ => ?_
    by_cases h : x = x'
    · simp [Search.adversary, h]
    · simp only [Search.adversary, h, if_false, one_mul]
      rcases le_total 0 (g x x') with hg | hg
      · rw [max_eq_left hg]; linarith [hkg x x' h hg]
      · rw [max_eq_right hg]; linarith [hk x x' h]
  have hcs := sq_sum_adversary_le (fun x x' => max (g x x') 0)
  set G := ∑ x, ∑ x', Search.adversary N x x' * max (g x x') 0
  set D := ∑ x, ∑ x', Search.adversary N x x' * (1 - k x x')
  have hG : 2 * (N : ℝ) * b ≤ G := hsum.trans h1
  have hb0 : 0 ≤ 2 * (N : ℝ) * b := by positivity
  have hsq : (2 * (N : ℝ) * b) ^ 2 ≤ G ^ 2 := pow_le_pow_left₀ hb0 hG 2
  have hNN : 0 ≤ (N : ℝ) * ((N : ℝ) - 1) := by nlinarith
  have h3 : (2 * (N : ℝ) * b) ^ 2 ≤ (N : ℝ) * ((N : ℝ) - 1) * (8 * D) :=
    hsq.trans (hcs.trans (mul_le_mul_of_nonneg_left h2 hNN))
  have h4 : (4 * (N : ℝ)) * ((N : ℝ) * b ^ 2) ≤
      (4 * (N : ℝ)) * (2 * ((N : ℝ) - 1) * D) := by
    nlinarith
  exact le_of_mul_le_mul_left h4 (by positivity)

end
end MeasuredUnitaryLowerBound.Global
