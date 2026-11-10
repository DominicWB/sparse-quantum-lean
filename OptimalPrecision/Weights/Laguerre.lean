import OptimalPrecision.Weights.Operator

/-!
# Rescaled Laguerre polynomials

`lag k = L_k(2X)`, where `L_k(y) = ∑_j C(k,j) (-y)^j / j!`, so that the Laguerre
functions of Appendix A are `ℓ_k(t) = e^{-t} lag k (t)`. The identities proved
here are polynomial identities over any field of characteristic zero:

* `derivative_lag`: `lag_k' = -2 ∑_{m<k} lag_m` (hockey stick);
* `X_mul_derivative_lag`: `X lag_{k+1}' = (k+1) (lag_{k+1} - lag_k)` (absorption);
* `lag_recurrence`: `(k+2) lag_{k+2} = (2k+3) lag_{k+1} - 2X lag_{k+1} - (k+1) lag_k`;
* `lag_ode`: `X lag_k'' + (1 - 2X) lag_k' + 2k lag_k = 0`, i.e. `𝔏 ℓ_k = (2k+1) ℓ_k`;
* `op_xs_lag`: `x lag_k = lag_k + 2 ∑_{m<k} lag_m` for `x = 1 - D` (`-∂`).
-/

namespace OptimalPrecision.ExpPoly

noncomputable section

open Polynomial Finset Nat
open scoped Polynomial

variable {K : Type*} [Field K] [CharZero K]

/-- Coefficients of `L_k(2X)`. -/
def lagCoeff (k j : ℕ) : K := (k.choose j : K) * (-2) ^ j / (j ! : K)

/-- The rescaled Laguerre polynomial `L_k(2X)`. -/
def lag (k : ℕ) : K[X] := ∑ j ∈ range (k + 1), C (lagCoeff k j) * X ^ j

theorem lagCoeff_eq_zero {k j : ℕ} (h : k < j) : (lagCoeff k j : K) = 0 := by
  simp [lagCoeff, Nat.choose_eq_zero_of_lt h]

theorem coeff_lag (k j : ℕ) : (lag k : K[X]).coeff j = lagCoeff k j := by
  simp only [lag, finsetSum_coeff, coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  split_ifs with hj
  · rfl
  · rw [lagCoeff_eq_zero]
    simp only [Finset.mem_range, not_lt] at hj
    omega

omit [CharZero K] in
theorem lag_zero : (lag 0 : K[X]) = 1 := by
  simp [lag, lagCoeff]

theorem eval_zero_lag (k : ℕ) : (lag k : K[X]).eval 0 = 1 := by
  rw [← coeff_zero_eq_eval_zero, coeff_lag]
  simp [lagCoeff]

omit [CharZero K] in
theorem natDegree_lag_le (k : ℕ) : (lag k : K[X]).natDegree ≤ k := by
  apply natDegree_sum_le_of_forall_le
  intro j hj
  refine (natDegree_C_mul_le _ _).trans ?_
  rw [natDegree_X_pow]
  exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)

theorem lagCoeff_self_ne_zero (k : ℕ) : (lagCoeff k k : K) ≠ 0 := by
  simp only [lagCoeff, Nat.choose_self, Nat.cast_one, one_mul]
  have h2 : ((-2 : K)) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
  have hk : (k ! : K) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
  exact div_ne_zero h2 hk

theorem natDegree_lag (k : ℕ) : (lag k : K[X]).natDegree = k := by
  apply le_antisymm (natDegree_lag_le k)
  apply le_natDegree_of_ne_zero
  rw [coeff_lag]
  exact lagCoeff_self_ne_zero k

/-- The Laguerre polynomials over `K` are the images of those over `ℚ`-subfields;
in particular they are compatible with ring homomorphisms. -/
theorem lag_map {L : Type*} [Field L] [CharZero L] (f : K →+* L) (k : ℕ) :
    (lag k : K[X]).map f = lag k := by
  ext j
  simp [coeff_map, coeff_lag, lagCoeff, map_ofNat]

/-- Hockey stick in the form `∑_{m<k} C(m,j) = C(k,j+1)`. -/
theorem sum_range_choose_eq (k j : ℕ) :
    ∑ m ∈ range k, (m.choose j : K) = (k.choose (j + 1) : K) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih, Nat.choose_succ_succ' k j]
    push_cast
    ring

/-- `lag_k' = -2 ∑_{m<k} lag_m`. -/
theorem derivative_lag (k : ℕ) :
    derivative (lag k : K[X]) = (-2 : K) • ∑ m ∈ range k, lag m := by
  ext j
  rw [coeff_derivative, coeff_lag, coeff_smul, finsetSum_coeff]
  simp only [coeff_lag]
  have hsum : ∑ m ∈ range k, (lagCoeff m j : K) =
      (k.choose (j + 1) : K) * (-2) ^ j / (j ! : K) := by
    simp only [lagCoeff, mul_div_assoc]
    rw [← Finset.sum_mul, sum_range_choose_eq]
  rw [hsum, lagCoeff]
  have hj : (j ! : K) ≠ 0 := by exact_mod_cast (Nat.factorial_pos j).ne'
  have hj1 : ((j + 1 : ℕ) ! : K) = ((j : K) + 1) * (j ! : K) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hj1' : (j : K) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
  rw [hj1, smul_eq_mul]
  field_simp
  ring

/-- `X lag_{k+1}' = (k+1) (lag_{k+1} - lag_k)`. -/
theorem X_mul_derivative_lag (k : ℕ) :
    X * derivative (lag (k + 1) : K[X]) = ((k + 1 : ℕ) : K) • (lag (k + 1) - lag k) := by
  ext j
  rw [coeff_smul, coeff_sub, coeff_lag, coeff_lag]
  rcases j with _ | j
  · simp [lagCoeff]
  · rw [coeff_X_mul, coeff_derivative, coeff_lag]
    simp only [lagCoeff, smul_eq_mul]
    have hpascal : ((k + 1).choose (j + 1) : K) - (k.choose (j + 1) : K) = (k.choose j : K) := by
      rw [Nat.choose_succ_succ' k j]; push_cast; ring
    have habs : ((k : K) + 1) * (k.choose j : K) =
        ((k + 1).choose (j + 1) : K) * ((j : K) + 1) := by
      exact_mod_cast Nat.add_one_mul_choose_eq k j
    have key : ((k + 1).choose (j + 1) : K) * (-2) ^ (j + 1) / ((j + 1 : ℕ) ! : K) -
        (k.choose (j + 1) : K) * (-2) ^ (j + 1) / ((j + 1 : ℕ) ! : K) =
        (k.choose j : K) * (-2) ^ (j + 1) / ((j + 1 : ℕ) ! : K) := by
      rw [← hpascal]; ring
    rw [key]
    push_cast
    linear_combination (-((-2 : K) ^ (j + 1) / ((j + 1) ! : K))) * habs

/-- `lag_{k+1}' = lag_k' - 2 lag_k`. -/
theorem derivative_lag_succ (k : ℕ) :
    derivative (lag (k + 1) : K[X]) = derivative (lag k) - (2 : K) • lag k := by
  rw [derivative_lag, derivative_lag, Finset.sum_range_succ, smul_add]
  rw [show (-2 : K) • (lag k : K[X]) = -((2 : K) • lag k) by rw [neg_smul]]
  abel

/-- The three-term recurrence. -/
theorem lag_recurrence (k : ℕ) :
    ((k + 2 : ℕ) : K) • (lag (k + 2) : K[X]) =
      ((2 * k + 3 : ℕ) : K) • lag (k + 1) - (2 : K) • (X * lag (k + 1)) -
        ((k + 1 : ℕ) : K) • lag k := by
  have h1 := X_mul_derivative_lag (K := K) (k + 1)
  have h2 := X_mul_derivative_lag (K := K) k
  have h3 := derivative_lag_succ (K := K) (k + 1)
  rw [h3, mul_sub, h2, mul_smul_comm] at h1
  -- h1 : (k+1)(lag(k+1) - lag k) - 2 (X lag(k+1)) = (k+2)(lag(k+2) - lag(k+1))
  have e1 : ((k + 1 + 1 : ℕ) : K) = ((k + 2 : ℕ) : K) := by push_cast; ring
  have e2 : ((2 * k + 3 : ℕ) : K) = ((k + 1 : ℕ) : K) + ((k + 2 : ℕ) : K) := by
    push_cast; ring
  rw [e1] at h1
  rw [e2, add_smul]
  rw [smul_sub, smul_sub] at h1
  linear_combination (exp := 1) -h1

/-- The rescaled Laguerre differential equation `X y'' + (1 - 2X) y' + 2k y = 0`. -/
theorem lag_ode (k : ℕ) :
    X * derivative (derivative (lag k : K[X])) + (1 - (2 : K) • X) * derivative (lag k) +
      ((2 * k : ℕ) : K) • lag k = 0 := by
  rcases k with _ | k
  · simp [lag_zero]
  · have hA := X_mul_derivative_lag (K := K) k
    have hB := derivative_lag_succ (K := K) k
    have hdA := congrArg derivative hA
    rw [derivative_mul, derivative_X, one_mul, derivative_smul, derivative_sub] at hdA
    simp only [Polynomial.smul_eq_C_mul] at hA hB hdA ⊢
    have e : (C (((2 * (k + 1) : ℕ) : K)) : K[X]) = C 2 * C (((k + 1 : ℕ) : K)) := by
      rw [← C_mul]; congr 1; push_cast; ring
    rw [e]
    linear_combination hdA + C (((k + 1 : ℕ) : K)) * hB - C (2 : K) * hA

/-- `x lag_k = lag_k + 2 ∑_{m<k} lag_m`. -/
theorem op_xs_lag (k : ℕ) :
    op xs (lag k : K[X]) = lag k + (2 : K) • ∑ m ∈ range k, lag m := by
  rw [op_xs, derivative_lag, sub_eq_add_neg, ← neg_smul, neg_neg]

/-- **Finite Laguerre expansion.** Every polynomial of degree at most `N` is a
combination of `lag 0, …, lag N` (the leading coefficient of `lag k` is nonzero). -/
theorem exists_lag_expansion (N : ℕ) :
    ∀ Q : K[X], Q.natDegree ≤ N → ∃ β : ℕ → K, Q = ∑ k ∈ range (N + 1), β k • lag k := by
  induction N with
  | zero =>
    intro Q hQ
    refine ⟨fun _ => Q.coeff 0, ?_⟩
    rw [Finset.sum_range_one, lag_zero, eq_C_of_natDegree_le_zero hQ, smul_eq_C_mul, mul_one,
      coeff_C_zero]
  | succ N ih =>
    intro Q hQ
    set γ : K := Q.coeff (N + 1) / lagCoeff (N + 1) (N + 1)
    have hQ' : (Q - γ • lag (N + 1)).natDegree ≤ N := by
      rw [natDegree_le_iff_coeff_eq_zero]
      intro j hj
      rw [coeff_sub, coeff_smul, coeff_lag, smul_eq_mul]
      rcases Nat.lt_or_ge (N + 1) j with h | h
      · rw [coeff_eq_zero_of_natDegree_lt (by omega), lagCoeff_eq_zero h, mul_zero, sub_zero]
      · have hj' : j = N + 1 := by omega
        subst hj'
        simp only [γ]
        rw [div_mul_cancel₀ _ (lagCoeff_self_ne_zero (N + 1)), sub_self]
    obtain ⟨β, hβ⟩ := ih _ hQ'
    refine ⟨fun k => if k = N + 1 then γ else β k, ?_⟩
    rw [Finset.sum_range_succ]
    dsimp only
    rw [if_pos rfl]
    have : ∑ k ∈ range (N + 1), (if k = N + 1 then γ else β k) • (lag k : K[X]) =
        ∑ k ∈ range (N + 1), β k • lag k := by
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [if_neg (by have := Finset.mem_range.mp hk; omega)]
    rw [this, ← hβ]
    abel

end

end OptimalPrecision.ExpPoly
