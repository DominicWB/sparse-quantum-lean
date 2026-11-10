import OptimalPrecision.Weights.Laguerre

/-!
# Clock coefficients in the Laguerre basis

With `E_l = (-1)^l (lag_l - lag_{l-1})` (the polynomial part of
`[w^l] e^{-t ξ(w)}`) and the clock coefficient polynomials

  `S_k = ∑_{l ≤ k} (k + 1 - l) E_l`   (`[w^k] e^{-tξ(w)} / (1 - w)^2 = e^{-t} S_k(t)`),

this file proves the two identities of Appendix A.2 that convert the clock into
Laguerre coordinates:

* `op_xs_lagE`: `x E_l = ∑_{a ≤ l} ξ_a E_{l-a}` with `ξ_0 = 1`, `ξ_a = 2(-1)^a`
  (multiplication of the transfer by `ξ(w)` is `-∂`);
* `cesPoly_signed` and `op_ramp_lag`: `2 (-1)^k S_k = R_k = (x^{-2} + x^{-1}) lag_k`,
  i.e. `[w^k] S = 2 (-1)^k ⟨𝔟, ℓ_k⟩` for the ramp profile (`opt:eq:laguerre-gf`).
-/

namespace OptimalPrecision.ExpPoly

noncomputable section

open Polynomial Finset Nat
open scoped Polynomial

variable {K : Type*} [Field K] [CharZero K]

/-- `E_l = (-1)^l (lag_l - lag_{l-1})`, with `E_0 = lag_0 = 1`. -/
def lagE (l : ℕ) : K[X] :=
  if l = 0 then 1 else ((-1 : K) ^ l) • (lag l - lag (l - 1))

omit [CharZero K] in
theorem lagE_zero : (lagE 0 : K[X]) = 1 := by simp [lagE]

omit [CharZero K] in
theorem lagE_succ (l : ℕ) :
    (lagE (l + 1) : K[X]) = ((-1 : K) ^ (l + 1)) • (lag (l + 1) - lag l) := by
  simp [lagE]

/-- Coefficients of `ξ(w) = (1-w)/(1+w)`. -/
def xic (a : ℕ) : K := if a = 0 then 1 else 2 * (-1) ^ a

/-- `x E_l` explicitly. -/
theorem op_xs_lagE_formula (l : ℕ) :
    op xs (lagE (l + 1) : K[X]) = ((-1 : K) ^ (l + 1)) • (lag (l + 1) + lag l) := by
  rw [lagE_succ, op_smul_right, op_sub_right, op_xs_lag, op_xs_lag, Finset.sum_range_succ]
  congr 1
  simp only [smul_add, two_smul]
  abel

theorem op_xs_lagE_zero : op xs (lagE 0 : K[X]) = 1 := by
  rw [lagE_zero, ← lag_zero, op_xs_lag]; simp [lag_zero]

/-- `∑_{a ≤ l} ξ_a E_{l-a}`. -/
def xiConv (l : ℕ) : K[X] := ∑ a ∈ range (l + 1), (xic a : K) • (lagE (l - a) : K[X])

omit [CharZero K] in
theorem xic_zero : (xic 0 : K) = 1 := by simp [xic]

omit [CharZero K] in
/-- `ξ_{b+1} = -ξ_b - [b = 0]`. -/
theorem xic_succ (b : ℕ) : (xic (b + 1) : K) = -xic b - if b = 0 then 1 else 0 := by
  rcases b with _ | b
  · simp [xic]; norm_num
  · simp only [xic, Nat.succ_ne_zero, if_false, pow_succ]; ring

omit [CharZero K] in
theorem xiConv_succ (l : ℕ) :
    (xiConv (l + 1) : K[X]) = lagE (l + 1) - xiConv l - lagE l := by
  unfold xiConv
  rw [Finset.sum_range_succ' _ (l + 1), xic_zero, one_smul, Nat.sub_zero]
  have hterm : ∀ b ∈ range (l + 1), (xic (b + 1) : K) • (lagE (l + 1 - (b + 1)) : K[X]) =
      -((xic b : K) • (lagE (l - b) : K[X])) - if b = 0 then lagE l else 0 := by
    intro b _
    rw [show l + 1 - (b + 1) = l - b by omega, xic_succ, sub_smul, neg_smul]
    split_ifs with hb
    · subst hb; simp
    · simp
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
    Finset.sum_ite_eq']
  simp only [Finset.mem_range, Nat.zero_lt_succ, if_true]
  abel

/-- **Multiplication by `ξ` is `-∂`** (`x E_l = ∑_{a ≤ l} ξ_a E_{l-a}`). -/
theorem op_xs_lagE (l : ℕ) : op xs (lagE l : K[X]) = xiConv l := by
  induction l with
  | zero => rw [op_xs_lagE_zero]; simp [xiConv, xic, lagE_zero]
  | succ l ih =>
    rw [xiConv_succ, ← ih, op_xs_lagE_formula]
    rcases l with _ | l
    · rw [op_xs_lagE_zero, lagE_zero, lagE_succ, lag_zero]
      simp only [zero_add, pow_one, neg_one_smul]
      abel
    · rw [op_xs_lagE_formula, lagE_succ, lagE_succ]
      have hs : (-1 : K) ^ (l + 1 + 1) = -((-1 : K) ^ (l + 1)) := by rw [pow_succ]; ring
      rw [hs]
      simp only [neg_smul, smul_add, smul_sub]
      abel

/-! ### The clock polynomials -/

/-- `S_k = ∑_{l ≤ k} (k + 1 - l) E_l`. -/
def cesPoly (k : ℕ) : K[X] := ∑ l ∈ range (k + 1), ((k + 1 - l : ℕ) : K) • lagE l

/-- `W_k = ∑_{l ≤ k} E_l`. -/
def sumE (k : ℕ) : K[X] := ∑ l ∈ range (k + 1), lagE l

omit [CharZero K] in
theorem cesPoly_succ (k : ℕ) : (cesPoly (k + 1) : K[X]) = cesPoly k + sumE (k + 1) := by
  unfold cesPoly sumE
  rw [Finset.sum_range_succ _ (k + 1)]
  rw [show ((k + 1 + 1 - (k + 1) : ℕ) : K) = 1 by norm_num, one_smul]
  have : ∑ l ∈ range (k + 1), ((k + 1 + 1 - l : ℕ) : K) • (lagE l : K[X]) =
      ∑ l ∈ range (k + 1), ((k + 1 - l : ℕ) : K) • lagE l +
        ∑ l ∈ range (k + 1), lagE l := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l hl => ?_
    have hl' := Finset.mem_range.mp hl
    rw [show k + 1 + 1 - l = (k + 1 - l) + 1 by omega]
    push_cast
    rw [add_smul, one_smul]
  rw [this, Finset.sum_range_succ (fun l => (lagE l : K[X])) (k + 1)]
  abel

/-- `T_k = 2 ∑_{m ≤ k} lag_m`. -/
def lagT (k : ℕ) : K[X] := (2 : K) • ∑ m ∈ range (k + 1), lag m

/-- `S'_k = 2 ∑_{m ≤ k} (-1)^{k-m} lag_m` (the signed partial sums). -/
def lagS : ℕ → K[X]
  | 0 => (2 : K) • lag 0
  | k + 1 => (2 : K) • lag (k + 1) - lagS k

/-- `R_k = 2 ∑_{m ≤ k} (-1)^{k-m} (2(k-m)+1) lag_m`, by its recursion. -/
def lagR : ℕ → K[X]
  | 0 => (2 : K) • lag 0
  | k + 1 => (2 : K) • lag (k + 1) - lagR k - (2 : K) • lagS k

omit [CharZero K] in
theorem lagT_succ (k : ℕ) : (lagT (k + 1) : K[X]) = (2 : K) • lag (k + 1) + lagT k := by
  unfold lagT; rw [Finset.sum_range_succ, smul_add]; abel

theorem op_xs_lag_succ (k : ℕ) : op xs (lag (k + 1) : K[X]) = lag (k + 1) + lagT k := by
  rw [op_xs_lag]; rfl

theorem op_xs_lag_zero' : op xs (lag 0 : K[X]) = lag 0 := by
  rw [op_xs_lag]; simp

theorem op_xs_lagS (k : ℕ) : op xs (lagS k : K[X]) = lagT k := by
  induction k with
  | zero => simp [lagS, lagT, op_smul_right, op_xs_lag_zero']
  | succ k ih =>
    simp only [lagS]
    rw [op_sub_right, op_smul_right, op_xs_lag_succ, ih, lagT_succ, smul_add,
      two_smul K (lagT k)]
    abel

theorem op_xs_lagR (k : ℕ) : op xs (lagR k : K[X]) = lagS k := by
  induction k with
  | zero => simp [lagR, lagS, op_smul_right, op_xs_lag_zero']
  | succ k ih =>
    simp only [lagR, lagS]
    rw [op_sub_right, op_sub_right, op_smul_right, op_smul_right, op_xs_lag_succ, ih,
      op_xs_lagS, smul_add]
    simp only [two_smul]
    abel

theorem op_one_add_xs_lag (k : ℕ) : op (1 + xs) (lag k : K[X]) = lagT k := by
  rw [op_add_left, op_one]
  rcases k with _ | k
  · rw [op_xs_lag_zero']; simp [lagT, two_smul]
  · rw [op_xs_lag_succ, lagT_succ, two_smul]; abel

omit [CharZero K] in
theorem constantCoeff_xs_sq : PowerSeries.constantCoeff ((xs : PowerSeries K) * xs) ≠ 0 := by
  rw [map_mul, constantCoeff_xs, one_mul]; exact one_ne_zero

/-- The Laguerre form of the ramp profile: `(x^{-2} + x^{-1}) lag_k = R_k`. -/
theorem op_ramp_lag (k : ℕ) :
    op ((xs : PowerSeries K)⁻¹ ^ 2 + xs⁻¹) (lag k) = lagR k := by
  apply op_injective constantCoeff_xs_sq
  rw [← op_mul, op_mul xs xs (lagR k), op_xs_lagR, op_xs_lagS]
  have hx : (xs : PowerSeries K) * xs⁻¹ = 1 :=
    PowerSeries.mul_inv_cancel _ (by rw [constantCoeff_xs]; exact one_ne_zero)
  have : (xs : PowerSeries K) * xs * (xs⁻¹ ^ 2 + xs⁻¹) = 1 + xs := by
    calc (xs : PowerSeries K) * xs * (xs⁻¹ ^ 2 + xs⁻¹) =
        (xs * xs⁻¹) * (xs * xs⁻¹) + xs * (xs * xs⁻¹) := by ring
      _ = 1 + xs := by rw [hx]; ring
  rw [this, op_one_add_xs_lag]

omit [CharZero K] in
theorem sumE_signed (k : ℕ) :
    ((-1 : K) ^ k) • (sumE k : K[X]) = lagS k - lag k := by
  induction k with
  | zero => simp [sumE, lagE_zero, lagS, lag_zero, two_smul]
  | succ k ih =>
    unfold sumE at ih ⊢
    rw [Finset.sum_range_succ, smul_add, lagE_succ, smul_smul, ← pow_add, ← two_mul,
      pow_mul, neg_one_sq, one_pow, one_smul, pow_succ, mul_neg_one, neg_smul, ih]
    simp only [lagS, two_smul]
    abel

omit [CharZero K] in
/-- **The clock coefficients in Laguerre form**: `2 (-1)^k S_k = R_k`. -/
theorem cesPoly_signed (k : ℕ) :
    (2 * (-1 : K) ^ k) • (cesPoly k : K[X]) = lagR k := by
  induction k with
  | zero => simp [cesPoly, lagE_zero, lagR, lag_zero]
  | succ k ih =>
    rw [cesPoly_succ, smul_add]
    have hW := sumE_signed (K := K) (k + 1)
    have e1 : (2 * (-1 : K) ^ (k + 1)) • (cesPoly k : K[X]) =
        -((2 * (-1 : K) ^ k) • cesPoly k) := by
      rw [pow_succ, ← neg_smul]; ring_nf
    have e2 : (2 * (-1 : K) ^ (k + 1)) • (sumE (k + 1) : K[X]) =
        (2 : K) • (((-1 : K) ^ (k + 1)) • sumE (k + 1)) := by
      rw [smul_smul]
    rw [e1, e2, ih, hW]
    simp only [lagR, lagS]
    simp only [smul_sub, two_smul]
    abel

end

end OptimalPrecision.ExpPoly
