import SparseLowerBounds.Helpers.SpinChain.Solution

set_option synthInstance.maxHeartbeats 400000

section
/-!
# Spin-chain weights `b_k = √((k+1)(n-k))/n`

Helper module of group spin-chain (`SparseLowerBounds.Hamiltonian.SpinChain`).
`weight` is the same term as `Hamiltonian.spinWeight` (so the lemmas apply to it
by unfolding). Bounds, the ladder identities
`n b_k √binom(n,k) = (k+1) √binom(n,k+1)` and
`n b_k √binom(n,k+1) = (n-k) √binom(n,k)`, the real row identity behind
`B_n √binom = √binom`, and the component identity of the explicit solution.
-/

namespace SparseLowerBounds.Helpers.SpinChain

/-- The spin-chain weight, the same term as `Hamiltonian.spinWeight`. -/
noncomputable def weight (n k : ℕ) : ℝ := Real.sqrt (((k + 1) * (n - k) : ℕ) : ℝ) / n

theorem weight_nonneg (n k : ℕ) : 0 ≤ weight n k := by
  exact div_nonneg (Real.sqrt_nonneg _) (Nat.cast_nonneg _)

/-- `b_k ≤ 1`: `(k+1)(n-k) ≤ ((n+1)/2)² ≤ n²`. -/
theorem weight_le_one (n k : ℕ) : weight n k ≤ 1 := by
  unfold weight
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [div_le_one hnR, Real.sqrt_le_left hnR.le]
  have h : (k + 1) * (n - k) ≤ n ^ 2 := by
    rcases lt_or_ge k n with hk | hk
    · rw [sq]
      exact Nat.mul_le_mul (by omega) (Nat.sub_le n k)
    · rw [Nat.sub_eq_zero_of_le hk, mul_zero]
      exact Nat.zero_le _
  exact_mod_cast h

/-- Every genuine edge weight is positive (line 2277). -/
theorem weight_pos {n k : ℕ} (hk : k < n) : 0 < weight n k := by
  unfold weight
  have hn : 0 < n := by omega
  refine div_pos (Real.sqrt_pos.2 ?_) (by exact_mod_cast hn)
  exact_mod_cast Nat.mul_pos (Nat.succ_pos k) (Nat.sub_pos_of_lt hk)

/-- `b_k ≥ 1/√n` for `k < n`, since `(k+1)(n-k) - n = k(n-k-1) ≥ 0`; this is
the `½ min_k b_k ≥ 1/(2√n)` behind the rounding precision of eq. `hsl:eq:round`. -/
theorem inv_sqrt_le_weight {n k : ℕ} (hk : k < n) : (Real.sqrt n)⁻¹ ≤ weight n k := by
  have hn : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnat : n ≤ (k + 1) * (n - k) := by
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hk
    have e : k + d + 1 - k = d + 1 := by omega
    rw [e]
    nlinarith
  have hX : (n : ℝ) ≤ (((k + 1) * (n - k) : ℕ) : ℝ) := by exact_mod_cast hnat
  unfold weight
  rw [inv_eq_one_div, div_le_div_iff₀ (Real.sqrt_pos.2 hnR) hnR, one_mul]
  calc (n : ℝ) = Real.sqrt n * Real.sqrt n := (Real.mul_self_sqrt hnR.le).symm
    _ ≤ Real.sqrt (((k + 1) * (n - k) : ℕ) : ℝ) * Real.sqrt n :=
      mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hX) (Real.sqrt_nonneg _)

/-- Two consecutive weights meet at a vertex with squared mass at most one:
`b_k² + b_{k+1}² ≤ 1` (for every `n, k`; `n² - n - 2j(n-j) ≥ 0` with
`j = k+1 < n`). This gives row/column Euclidean norms at most one for the
chains (lines 2113-2114, 2282-2283). -/
theorem weight_sq_add_sq_le (n k : ℕ) : weight n k ^ 2 + weight n (k + 1) ^ 2 ≤ 1 := by
  unfold weight
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [div_pow, div_pow, Real.sq_sqrt (Nat.cast_nonneg _), Real.sq_sqrt (Nat.cast_nonneg _),
    ← add_div, div_le_one (by positivity)]
  have h : (k + 1) * (n - k) + (k + 1 + 1) * (n - (k + 1)) ≤ n ^ 2 := by
    by_cases hk : k + 1 < n
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hk
      have e1 : k + 1 + d + 1 - k = d + 2 := by omega
      have e2 : k + 1 + d + 1 - (k + 1) = d + 1 := by omega
      rw [e1, e2]
      nlinarith
    · have e2 : n - (k + 1) = 0 := by omega
      rw [e2, mul_zero, add_zero]
      rcases lt_or_ge k n with hk' | hk'
      · rw [sq]
        exact Nat.mul_le_mul (by omega) (Nat.sub_le n k)
      · rw [Nat.sub_eq_zero_of_le hk', mul_zero]
        exact Nat.zero_le _
  exact_mod_cast h

/-- The ladder identity `n b_k √binom(n,k) = (k+1) √binom(n,k+1)`, from
`(n-k) binom(n,k) = (k+1) binom(n,k+1)`. -/
theorem weight_mul_sqrt_choose {n k : ℕ} (hk : k < n) :
    (n : ℝ) * weight n k * Real.sqrt (n.choose k) = (k + 1) * Real.sqrt (n.choose (k + 1)) := by
  have hnR : (n : ℝ) ≠ 0 := by
    have : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    exact this.ne'
  have hnat : (k + 1) * (n - k) * n.choose k = (k + 1) ^ 2 * n.choose (k + 1) := by
    have h := Nat.choose_succ_right_eq n k
    calc (k + 1) * (n - k) * n.choose k = (k + 1) * (n.choose k * (n - k)) := by ring
      _ = (k + 1) * (n.choose (k + 1) * (k + 1)) := by rw [h]
      _ = (k + 1) ^ 2 * n.choose (k + 1) := by ring
  have h1 : (n : ℝ) * (Real.sqrt (((k + 1) * (n - k) : ℕ) : ℝ) / n) =
      Real.sqrt (((k + 1) * (n - k) : ℕ) : ℝ) := by
    field_simp
  unfold weight
  rw [h1, ← Real.sqrt_mul (Nat.cast_nonneg _), ← Nat.cast_mul, hnat, Nat.cast_mul,
    Real.sqrt_mul (Nat.cast_nonneg _), Nat.cast_pow, Real.sqrt_sq (Nat.cast_nonneg _)]
  push_cast
  ring

/-- The ladder identity `n b_k √binom(n,k+1) = (n-k) √binom(n,k)`. -/
theorem weight_mul_sqrt_choose_succ {n k : ℕ} (hk : k < n) :
    (n : ℝ) * weight n k * Real.sqrt (n.choose (k + 1)) = ((n : ℝ) - k) * Real.sqrt (n.choose k) := by
  have hnR : (n : ℝ) ≠ 0 := by
    have : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    exact this.ne'
  have hnat : (k + 1) * (n - k) * n.choose (k + 1) = (n - k) ^ 2 * n.choose k := by
    have h := Nat.choose_succ_right_eq n k
    calc (k + 1) * (n - k) * n.choose (k + 1) = (n - k) * (n.choose (k + 1) * (k + 1)) := by ring
      _ = (n - k) * (n.choose k * (n - k)) := by rw [h]
      _ = (n - k) ^ 2 * n.choose k := by ring
  have h1 : (n : ℝ) * (Real.sqrt (((k + 1) * (n - k) : ℕ) : ℝ) / n) =
      Real.sqrt (((k + 1) * (n - k) : ℕ) : ℝ) := by
    field_simp
  unfold weight
  rw [h1, ← Real.sqrt_mul (Nat.cast_nonneg _), ← Nat.cast_mul, hnat, Nat.cast_mul,
    Real.sqrt_mul (Nat.cast_nonneg _), Nat.cast_pow, Real.sqrt_sq (Nat.cast_nonneg _),
    Nat.cast_sub hk.le]

variable {n : ℕ}

/-- `B_n v = v` row by row, for `v_k = √binom(n,k)`, in real form. -/
theorem binom_row (hn : 1 ≤ n) (i : ℕ) (hi : i ≤ n) :
    (if 0 < i then weight n (i - 1) * Real.sqrt (n.choose (i - 1)) else 0) +
      (if i < n then weight n i * Real.sqrt (n.choose (i + 1)) else 0) =
      Real.sqrt (n.choose i) := by
  have hnR : (n : ℝ) ≠ 0 := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    exact this.ne'
  have e1 : (n : ℝ) * (if 0 < i then weight n (i - 1) * Real.sqrt (n.choose (i - 1)) else 0) =
      (i : ℝ) * Real.sqrt (n.choose i) := by
    split_ifs with h
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      rw [Nat.add_sub_cancel, ← mul_assoc, weight_mul_sqrt_choose (by omega)]
      push_cast
      ring
    · have : i = 0 := by omega
      subst this
      simp
  have e2 : (n : ℝ) * (if i < n then weight n i * Real.sqrt (n.choose (i + 1)) else 0) =
      ((n : ℝ) - i) * Real.sqrt (n.choose i) := by
    split_ifs with h
    · rw [← mul_assoc, weight_mul_sqrt_choose_succ h]
    · have : i = n := by omega
      subst this
      simp
  have key : (n : ℝ) * ((if 0 < i then weight n (i - 1) * Real.sqrt (n.choose (i - 1)) else 0) +
      (if i < n then weight n i * Real.sqrt (n.choose (i + 1)) else 0)) =
      n * Real.sqrt (n.choose i) := by
    rw [mul_add, e1, e2]
    ring
  exact mul_left_cancel₀ hnR key

/-- Ladder identity scaled by `a/n` (successor neighbour). -/
theorem ladder_succ_real (a : ℝ) {k : ℕ} (hk : k < n) :
    a * weight n k * Real.sqrt (n.choose (k + 1)) =
      Real.sqrt (n.choose k) * (a / n) * ((n : ℝ) - k) := by
  have hnR : (n : ℝ) ≠ 0 := by
    have : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    exact this.ne'
  have h := weight_mul_sqrt_choose_succ hk
  calc a * weight n k * Real.sqrt (n.choose (k + 1))
      = (a / n) * ((n : ℝ) * weight n k * Real.sqrt (n.choose (k + 1))) := by
        rw [div_mul_eq_mul_div, eq_div_iff hnR]
        ring
    _ = _ := by rw [h]; ring

/-- Ladder identity scaled by `a/n` (predecessor neighbour). -/
theorem ladder_real (a : ℝ) {j : ℕ} (hj : j < n) :
    a * weight n j * Real.sqrt (n.choose j) =
      Real.sqrt (n.choose (j + 1)) * (a / n) * ((j : ℝ) + 1) := by
  have hnR : (n : ℝ) ≠ 0 := by
    have : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    exact this.ne'
  have h := weight_mul_sqrt_choose hj
  calc a * weight n j * Real.sqrt (n.choose j)
      = (a / n) * ((n : ℝ) * weight n j * Real.sqrt (n.choose j)) := by
        rw [div_mul_eq_mul_div, eq_div_iff hnR]
        ring
    _ = _ := by rw [h]; ring

/-- The component identity behind `hasDerivAt_spinSolution`, with `c = cos θ`,
`z = -i sin θ` abstracted. -/
theorem spin_row (a : ℝ) (c z : ℂ) {k : ℕ} (hk : k ≤ n) :
    ((Real.sqrt (n.choose k) : ℝ) : ℂ) * ((a / n : ℝ) : ℂ) * (-Complex.I) *
        (((n - k : ℕ) : ℂ) * c ^ (n - k - 1) * z ^ (k + 1) +
          (k : ℂ) * c ^ (n - k + 1) * z ^ (k - 1)) =
      -Complex.I *
        ((if 0 < k then ((a * weight n (k - 1) : ℝ) : ℂ) *
            (((Real.sqrt (n.choose (k - 1)) : ℝ) : ℂ) * c ^ (n - (k - 1)) * z ^ (k - 1))
            else 0) +
          (if k < n then ((a * weight n k : ℝ) : ℂ) *
            (((Real.sqrt (n.choose (k + 1)) : ℝ) : ℂ) * c ^ (n - (k + 1)) * z ^ (k + 1))
            else 0)) := by
  have e1 : (if 0 < k then ((a * weight n (k - 1) : ℝ) : ℂ) *
        (((Real.sqrt (n.choose (k - 1)) : ℝ) : ℂ) * c ^ (n - (k - 1)) * z ^ (k - 1)) else 0) =
      ((Real.sqrt (n.choose k) : ℝ) : ℂ) * ((a / n : ℝ) : ℂ) *
        ((k : ℂ) * c ^ (n - k + 1) * z ^ (k - 1)) := by
    split_ifs with h
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      have hl := congrArg (fun x : ℝ => (x : ℂ)) (ladder_real a (show j < n by omega))
      simp only [Nat.add_sub_cancel] at hl ⊢
      have hp : n - j = n - (j + 1) + 1 := by omega
      rw [hp]
      push_cast at hl ⊢
      linear_combination (c ^ (n - (j + 1) + 1) * z ^ j) * hl
    · have : k = 0 := by omega
      subst this
      simp
  have e2 : (if k < n then ((a * weight n k : ℝ) : ℂ) *
        (((Real.sqrt (n.choose (k + 1)) : ℝ) : ℂ) * c ^ (n - (k + 1)) * z ^ (k + 1)) else 0) =
      ((Real.sqrt (n.choose k) : ℝ) : ℂ) * ((a / n : ℝ) : ℂ) *
        (((n - k : ℕ) : ℂ) * c ^ (n - k - 1) * z ^ (k + 1)) := by
    split_ifs with h
    · have hl := congrArg (fun x : ℝ => (x : ℂ)) (ladder_succ_real a h)
      have hp : n - k - 1 = n - (k + 1) := by omega
      rw [hp, Nat.cast_sub h.le]
      push_cast at hl ⊢
      linear_combination (c ^ (n - (k + 1)) * z ^ (k + 1)) * hl
    · have : n - k = 0 := by omega
      rw [this]
      simp
  rw [e1, e2]
  ring

end SparseLowerBounds.Helpers.SpinChain
end
