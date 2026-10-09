import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.NoncommRing

/-!
# Powers of a perturbed element

If every power of `X` up to `N` is bounded by `C`, then every power of
`X + R` up to `N` is bounded by `C (1 + C ‖R‖)^j`.  The proof is the discrete
Gronwall argument applied to the noncommutative telescoping identity
`(X + R)^j = X^j + ∑_{i<j} X^(j-1-i) R (X + R)^i`.  No commutation between `X`
and `R` is needed.  This is the estimate behind `‖V^j‖ ≤ 2 C̄` in the proof of
Theorem `ode:thm:general`.
-/

namespace SparseHamiltonian.GeneralODE.Runs

open scoped BigOperators

variable {𝔸 : Type*} [NormedRing 𝔸]

/-- Noncommutative telescoping for powers of a sum. -/
theorem add_pow_eq (X R : 𝔸) (j : ℕ) :
    (X + R) ^ j = X ^ j + ∑ i ∈ Finset.range j, X ^ (j - 1 - i) * R * (X + R) ^ i := by
  induction j with
  | zero => simp
  | succ j ih =>
      have hsum : ∑ i ∈ Finset.range j, X * (X ^ (j - 1 - i) * R * (X + R) ^ i) =
          ∑ i ∈ Finset.range j, X ^ (j + 1 - 1 - i) * R * (X + R) ^ i := by
        apply Finset.sum_congr rfl
        intro i hi
        have hij : i < j := Finset.mem_range.mp hi
        have hexp : j + 1 - 1 - i = (j - 1 - i) + 1 := by omega
        rw [hexp, pow_succ', mul_assoc, mul_assoc, mul_assoc]
      have h0 : j + 1 - 1 - j = 0 := by omega
      calc
        (X + R) ^ (j + 1) = X * (X + R) ^ j + R * (X + R) ^ j := by
          rw [pow_succ', add_mul]
        _ = X * X ^ j + ∑ i ∈ Finset.range j, X * (X ^ (j - 1 - i) * R * (X + R) ^ i) +
              R * (X + R) ^ j := by
          rw [ih, mul_add, Finset.mul_sum, ← ih]
        _ = X ^ (j + 1) + ∑ i ∈ Finset.range (j + 1), X ^ (j + 1 - 1 - i) * R * (X + R) ^ i := by
          rw [hsum, Finset.sum_range_succ, h0, pow_zero, one_mul, ← pow_succ']
          abel

/-- Discrete Gronwall bound for perturbed powers. -/
theorem norm_add_pow_le (X R : 𝔸) (C : ℝ) (N : ℕ)
    (hX : ∀ j, j ≤ N → ‖X ^ j‖ ≤ C) :
    ∀ j, j ≤ N → ‖(X + R) ^ j‖ ≤ C * (1 + C * ‖R‖) ^ j := by
  have hC : 0 ≤ C := (norm_nonneg _).trans (hX 0 (Nat.zero_le N))
  have hq : 0 ≤ C * ‖R‖ := mul_nonneg hC (norm_nonneg R)
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    rw [add_pow_eq X R j]
    have hterm : ∀ i ∈ Finset.range j,
        ‖X ^ (j - 1 - i) * R * (X + R) ^ i‖ ≤
          C * ‖R‖ * (C * (1 + C * ‖R‖) ^ i) := by
      intro i hi
      have hij : i < j := Finset.mem_range.mp hi
      have hpow : ‖X ^ (j - 1 - i)‖ ≤ C := hX _ (by omega)
      have hprev : ‖(X + R) ^ i‖ ≤ C * (1 + C * ‖R‖) ^ i := ih i hij (by omega)
      calc
        ‖X ^ (j - 1 - i) * R * (X + R) ^ i‖
            ≤ ‖X ^ (j - 1 - i)‖ * ‖R‖ * ‖(X + R) ^ i‖ := by
              calc
                _ ≤ ‖X ^ (j - 1 - i) * R‖ * ‖(X + R) ^ i‖ := norm_mul_le _ _
                _ ≤ ‖X ^ (j - 1 - i)‖ * ‖R‖ * ‖(X + R) ^ i‖ :=
                    mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
        _ ≤ C * ‖R‖ * (C * (1 + C * ‖R‖) ^ i) := by
              apply mul_le_mul (mul_le_mul_of_nonneg_right hpow (norm_nonneg _)) hprev
                (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))
    have hgeom : ∑ i ∈ Finset.range j, C * ‖R‖ * (C * (1 + C * ‖R‖) ^ i) =
        C * ((1 + C * ‖R‖) ^ j - 1) := by
      have h := geom_sum_mul (1 + C * ‖R‖) j
      have hrw : ∑ i ∈ Finset.range j, C * ‖R‖ * (C * (1 + C * ‖R‖) ^ i) =
          C * ((∑ i ∈ Finset.range j, (1 + C * ‖R‖) ^ i) * (1 + C * ‖R‖ - 1)) := by
        rw [Finset.sum_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [hrw, h]
    calc
      ‖X ^ j + ∑ i ∈ Finset.range j, X ^ (j - 1 - i) * R * (X + R) ^ i‖
          ≤ ‖X ^ j‖ + ‖∑ i ∈ Finset.range j, X ^ (j - 1 - i) * R * (X + R) ^ i‖ :=
            norm_add_le _ _
      _ ≤ C + ∑ i ∈ Finset.range j, C * ‖R‖ * (C * (1 + C * ‖R‖) ^ i) := by
            apply add_le_add (hX j hj)
            exact (norm_sum_le _ _).trans (Finset.sum_le_sum hterm)
      _ = C * (1 + C * ‖R‖) ^ j := by rw [hgeom]; ring

/-- A uniform form: with `C (N ‖R‖) ≤ log 2`-type control one obtains `2C`. -/
theorem norm_add_pow_le_of_exp (X R : 𝔸) (C : ℝ) (N : ℕ)
    (hX : ∀ j, j ≤ N → ‖X ^ j‖ ≤ C) (j : ℕ) (hj : j ≤ N) :
    ‖(X + R) ^ j‖ ≤ C * Real.exp (C * ‖R‖ * N) := by
  have hC : 0 ≤ C := (norm_nonneg _).trans (hX 0 (Nat.zero_le N))
  have h := norm_add_pow_le X R C N hX j hj
  have hq : 0 ≤ C * ‖R‖ := mul_nonneg hC (norm_nonneg R)
  calc
    ‖(X + R) ^ j‖ ≤ C * (1 + C * ‖R‖) ^ j := h
    _ ≤ C * Real.exp (C * ‖R‖) ^ j := by
        apply mul_le_mul_of_nonneg_left _ hC
        apply pow_le_pow_left₀ (by linarith)
        have := Real.add_one_le_exp (C * ‖R‖)
        linarith
    _ = C * Real.exp (C * ‖R‖ * j) := by
        rw [← Real.exp_nat_mul]; ring_nf
    _ ≤ C * Real.exp (C * ‖R‖ * N) := by
        apply mul_le_mul_of_nonneg_left _ hC
        apply Real.exp_le_exp.mpr
        apply mul_le_mul_of_nonneg_left _ hq
        exact_mod_cast hj

end SparseHamiltonian.GeneralODE.Runs
