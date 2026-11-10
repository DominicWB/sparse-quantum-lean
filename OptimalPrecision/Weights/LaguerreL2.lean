import OptimalPrecision.Weights.Laguerre
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Laguerre functions in `L²(0, ∞)`, algebraically

For exponential polynomials `f = e^{-t} π(t)`, `g = e^{-t} ρ(t)` the pairing
`∫_0^∞ f g dt` is `J(π ρ)`, where `J` is the linear functional on `ℝ[X]` with
moments `J(X^n) = n!/2^{n+1}` (`∫_0^∞ t^n e^{-2t} dt`; the identification with
the Lebesgue integral is in `Weights.Integral`). This file proves, purely
algebraically, the facts about the Laguerre functions `ℓ_k = e^{-t} lag_k` used
in the variation bound of Theorem `opt:thm:weights`:

* `J_derivative`: `J(π') = 2 J(π) - π(0)` (integration by parts);
* `J_Lop_mul`: the operator `𝔏 = -t∂² - ∂ + t` is symmetric;
* `Lop_lag`: `𝔏 ℓ_k = (2k+1) ℓ_k` (`opt:eq:laguerre-identities`);
* `J_lag_mul_lag`: `∫ ℓ_j ℓ_k = δ_{jk}/2` (`opt:eq:laguerre-identities`);
* `sum_abs_le`: if `ψ = ∑_{k ≤ N} β_k ℓ_k` and `(𝔏 + 1) ψ = 4χ`, then
  `∑_k ((k+1)/2) |β_k| ≤ √(N+1) √(2 ∫ χ²)` (Cauchy–Schwarz and Parseval).
-/

namespace OptimalPrecision.ExpPoly

noncomputable section

open Polynomial Finset Nat
open scoped Polynomial

/-! ### The moment functional -/

/-- `J(π) = ∫_0^∞ e^{-2t} π(t) dt`, through its moments `J(X^n) = n!/2^{n+1}`. -/
def J : ℝ[X] →ₗ[ℝ] ℝ :=
  Polynomial.lsum fun n => ((n ! : ℝ) / 2 ^ (n + 1)) • LinearMap.id

theorem J_monomial (n : ℕ) (c : ℝ) : J (monomial n c) = c * ((n ! : ℝ) / 2 ^ (n + 1)) := by
  simp [J, Polynomial.lsum_apply, mul_comm]

theorem J_C (c : ℝ) : J (C c) = c / 2 := by
  rw [← monomial_zero_left, J_monomial]; norm_num; ring

theorem J_one : J 1 = 1 / 2 := by
  rw [← C_1, J_C]

/-- **Integration by parts**: `J(π') = 2 J(π) - π(0)`. -/
theorem J_derivative (π : ℝ[X]) : J (derivative π) = 2 * J π - π.eval 0 := by
  induction π using Polynomial.induction_on' with
  | add p r hp hr => rw [derivative_add, map_add, hp, hr, map_add, eval_add]; ring
  | monomial n c =>
    rw [derivative_monomial, J_monomial, J_monomial, eval_monomial]
    rcases n with _ | n
    · simp; ring
    · rw [Nat.add_sub_cancel, zero_pow (Nat.succ_ne_zero n), mul_zero, sub_zero,
        Nat.factorial_succ]
      push_cast
      field_simp
      ring

/-! ### The Laguerre operator -/

/-- `𝔏 = -t∂² - ∂ + t` on polynomial parts: `π ↦ π - X π'' - (1 - 2X) π'`. -/
def Lop : ℝ[X] →ₗ[ℝ] ℝ[X] :=
  LinearMap.id - LinearMap.mulLeft ℝ (X : ℝ[X]) ∘ₗ derivative ∘ₗ derivative -
    LinearMap.mulLeft ℝ (1 - 2 * X : ℝ[X]) ∘ₗ derivative

theorem Lop_apply (π : ℝ[X]) :
    Lop π = π - X * derivative (derivative π) - (1 - 2 * X) * derivative π := rfl

/-- **Symmetry of `𝔏`**: `∫ (𝔏f) g = ∫ t f' g' + ∫ t f g`. -/
theorem J_Lop_mul (π ρ : ℝ[X]) :
    J (Lop π * ρ) = J (X * (derivative π - π) * (derivative ρ - ρ)) + J (X * π * ρ) := by
  set τ := X * (derivative π - π)
  have hτ : derivative τ = (derivative π - π) + X * (derivative (derivative π) - derivative π) := by
    simp only [τ, derivative_mul, derivative_X, one_mul, derivative_sub]
  have hL : Lop π * ρ = -(derivative τ * ρ) + τ * ρ + X * π * ρ := by
    rw [Lop_apply, hτ]; simp only [τ]; ring
  have hibp : J (derivative τ * ρ) = 2 * J (τ * ρ) - J (τ * derivative ρ) := by
    have h := J_derivative (τ * ρ)
    rw [derivative_mul, map_add] at h
    have h0 : (τ * ρ).eval 0 = 0 := by simp [τ]
    rw [h0, sub_zero] at h
    linarith
  rw [hL, map_add, map_add, map_neg, hibp]
  have : X * (derivative π - π) * (derivative ρ - ρ) = τ * derivative ρ - τ * ρ := by
    simp only [τ]; ring
  rw [this, map_sub]
  ring

theorem J_Lop_mul_comm (π ρ : ℝ[X]) : J (Lop π * ρ) = J (π * Lop ρ) := by
  rw [J_Lop_mul, mul_comm π (Lop ρ), J_Lop_mul]
  have e1 : X * (derivative π - π) * (derivative ρ - ρ) =
      X * (derivative ρ - ρ) * (derivative π - π) := by ring
  have e2 : X * π * ρ = X * ρ * π := by ring
  rw [e1, e2]

/-- `𝔏 ℓ_k = (2k+1) ℓ_k`. -/
theorem Lop_lag (k : ℕ) : Lop (lag k) = ((2 * k + 1 : ℕ) : ℝ) • lag k := by
  have h := lag_ode (K := ℝ) k
  rw [Lop_apply]
  simp only [Polynomial.smul_eq_C_mul, map_ofNat] at h ⊢
  have e : (C ((2 * k + 1 : ℕ) : ℝ) : ℝ[X]) = C ((2 * k : ℕ) : ℝ) + 1 := by
    rw [← C_1, ← C_add]; congr 1; push_cast; ring
  rw [e]
  linear_combination -h

/-! ### Orthogonality -/

theorem J_lag_mul_lag_of_ne {j k : ℕ} (h : j ≠ k) : J (lag j * lag k) = 0 := by
  have h1 := J_Lop_mul_comm (lag j) (lag k)
  rw [Lop_lag, Lop_lag, smul_mul_assoc, mul_smul_comm, map_smul, map_smul, smul_eq_mul,
    smul_eq_mul] at h1
  have hjk : ((2 * j + 1 : ℕ) : ℝ) ≠ ((2 * k + 1 : ℕ) : ℝ) := by
    intro h'
    have : 2 * j + 1 = 2 * k + 1 := by exact_mod_cast h'
    omega
  have : (((2 * j + 1 : ℕ) : ℝ) - ((2 * k + 1 : ℕ) : ℝ)) * J (lag j * lag k) = 0 := by
    rw [sub_mul, h1]; ring
  rcases mul_eq_zero.mp this with h2 | h2
  · exact absurd (sub_eq_zero.mp h2) hjk
  · exact h2

/-- `2X lag_k = (2k+1) lag_k - (k+1) lag_{k+1} - k lag_{k-1}`. -/
theorem two_X_mul_lag (k : ℕ) :
    (2 : ℝ) • (X * lag k : ℝ[X]) = ((2 * k + 1 : ℕ) : ℝ) • lag k - ((k + 1 : ℕ) : ℝ) • lag (k + 1) -
      (k : ℝ) • lag (k - 1) := by
  rcases k with _ | k
  · have h1 : (lag 1 : ℝ[X]) = 1 - C 2 * X := by
      ext j
      rw [coeff_lag]
      rcases j with _ | _ | j
      · simp [lagCoeff]
      · simp [lagCoeff, coeff_one]
      · simp only [lagCoeff_eq_zero (by omega : 1 < j + 2), coeff_sub, coeff_one, coeff_C_mul,
          coeff_X]
        simp
    simp [h1, lag_zero, Polynomial.smul_eq_C_mul]
  · have h := lag_recurrence (K := ℝ) k
    rw [Nat.add_sub_cancel]
    have e1 : ((k + 1 + 1 : ℕ) : ℝ) = ((k + 2 : ℕ) : ℝ) := by push_cast; ring
    have e2 : ((2 * (k + 1) + 1 : ℕ) : ℝ) = ((2 * k + 3 : ℕ) : ℝ) := by push_cast; ring
    rw [e1, e2, show k + 1 + 1 = k + 2 by ring]
    rw [h]
    abel

theorem J_lag_sq_succ (k : ℕ) : J (lag (k + 1) * lag (k + 1)) = J (lag k * lag k) := by
  have hA := congrArg (fun π => J (π * lag (k + 1))) (two_X_mul_lag k)
  have hB := congrArg (fun π => J (π * lag k)) (two_X_mul_lag (k + 1))
  simp only [sub_mul, smul_mul_assoc, map_sub, map_smul, smul_eq_mul] at hA hB
  have o1 : J (lag k * lag (k + 1)) = 0 := J_lag_mul_lag_of_ne (by omega)
  have o2 : J (lag (k - 1) * lag (k + 1)) = 0 := J_lag_mul_lag_of_ne (by omega)
  have o3 : J (lag (k + 1) * lag k) = 0 := J_lag_mul_lag_of_ne (by omega)
  have o4 : J (lag (k + 1 + 1) * lag k) = 0 := J_lag_mul_lag_of_ne (by omega)
  have e : k + 1 - 1 = k := by omega
  rw [e] at hB
  have hsym : J (X * lag k * lag (k + 1)) = J (X * lag (k + 1) * lag k) := by
    rw [show (X * lag k * lag (k + 1) : ℝ[X]) = X * lag (k + 1) * lag k by ring]
  rw [o1, o2] at hA
  rw [o3, o4] at hB
  have hk : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  have : ((k + 1 : ℕ) : ℝ) * J (lag (k + 1) * lag (k + 1)) =
      ((k + 1 : ℕ) : ℝ) * J (lag k * lag k) := by
    linarith
  exact mul_left_cancel₀ hk.ne' this

/-- `∫ ℓ_k² = 1/2`. -/
theorem J_lag_sq (k : ℕ) : J (lag k * lag k) = 1 / 2 := by
  induction k with
  | zero => rw [lag_zero, one_mul, J_one]
  | succ k ih => rw [J_lag_sq_succ, ih]

/-- `∫ ℓ_j ℓ_k = δ_{jk}/2`. -/
theorem J_lag_mul_lag (j k : ℕ) : J (lag j * lag k) = if j = k then 1 / 2 else 0 := by
  split_ifs with h
  · subst h; exact J_lag_sq j
  · exact J_lag_mul_lag_of_ne h

/-! ### Parseval and the variation bound -/

theorem J_expansion_mul_lag (N : ℕ) (γ : ℕ → ℝ) {j : ℕ} (hj : j ≤ N) :
    J ((∑ k ∈ range (N + 1), γ k • lag k) * lag j) = γ j / 2 := by
  rw [Finset.sum_mul, map_sum]
  simp only [smul_mul_assoc, map_smul, smul_eq_mul, J_lag_mul_lag]
  rw [Finset.sum_eq_single j]
  · simp; ring
  · intro k _ hk; simp [hk]
  · intro h; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hj)) h

/-- **Parseval** for finite Laguerre expansions. -/
theorem J_expansion_sq (N : ℕ) (γ : ℕ → ℝ) :
    J ((∑ k ∈ range (N + 1), γ k • lag k) * (∑ k ∈ range (N + 1), γ k • lag k)) =
      ∑ k ∈ range (N + 1), γ k ^ 2 / 2 := by
  conv_lhs => rw [Finset.mul_sum]
  rw [map_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [mul_smul_comm, map_smul,
    J_expansion_mul_lag N γ (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)), smul_eq_mul]
  ring

/-- **The variation bound** of `opt:thm:weights`: if `ψ = ∑_{k ≤ N} β_k ℓ_k` and
`(𝔏 + 1)ψ = 4χ`, then `∑_k ((k+1)/2)|β_k| ≤ √(N+1) · √(2 ∫ χ²)`. -/
theorem sum_abs_le (N : ℕ) (β : ℕ → ℝ) (χ : ℝ[X])
    (hχ : Lop (∑ k ∈ range (N + 1), β k • lag k) + ∑ k ∈ range (N + 1), β k • lag k =
      (4 : ℝ) • χ) :
    ∑ k ∈ range (N + 1), ((k + 1 : ℝ) / 2) * |β k| ≤
      Real.sqrt (N + 1) * Real.sqrt (2 * J (χ * χ)) := by
  -- `4χ = ∑ (2k+2) β_k ℓ_k`
  have hexp : (4 : ℝ) • χ = ∑ k ∈ range (N + 1), ((2 * k + 2 : ℝ) * β k) • lag k := by
    rw [← hχ, map_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, Lop_lag, smul_smul, ← add_smul]
    congr 1
    push_cast
    ring
  have hpars := J_expansion_sq N (fun k => (2 * k + 2 : ℝ) * β k)
  rw [← hexp] at hpars
  simp only [smul_mul_smul_comm, map_smul, smul_eq_mul] at hpars
  -- `∑ ((k+1) β_k)^2 = 8 J(χ²)`
  have hsq : ∑ k ∈ range (N + 1), (((k : ℝ) + 1) * β k) ^ 2 = 8 * J (χ * χ) := by
    have : ∑ k ∈ range (N + 1), (((k : ℝ) + 1) * β k) ^ 2 =
        (1 / 2) * ∑ k ∈ range (N + 1), ((2 * k + 2 : ℝ) * β k) ^ 2 / 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [this, ← hpars]
    ring
  -- Cauchy–Schwarz
  have hcs := sq_sum_le_card_mul_sum_sq (s := range (N + 1)) (f := fun k => |((k : ℝ) + 1) * β k|)
  simp only [Finset.card_range, sq_abs] at hcs
  rw [hsq] at hcs
  have hJ : 0 ≤ J (χ * χ) := by
    have h0 : 0 ≤ ∑ k ∈ range (N + 1), (((k : ℝ) + 1) * β k) ^ 2 :=
      Finset.sum_nonneg fun k _ => sq_nonneg _
    linarith
  have hS : ∑ k ∈ range (N + 1), ((k + 1 : ℝ) / 2) * |β k| =
      (1 / 2) * ∑ k ∈ range (N + 1), |((k : ℝ) + 1) * β k| := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (k : ℝ) + 1)]
    ring
  rw [hS]
  have hT : ∑ k ∈ range (N + 1), |((k : ℝ) + 1) * β k| ≤
      Real.sqrt ((N + 1 : ℕ) * (8 * J (χ * χ))) := by
    apply Real.le_sqrt_of_sq_le
    exact_mod_cast hcs
  have hsplit : Real.sqrt ((N + 1 : ℕ) * (8 * J (χ * χ))) =
      2 * (Real.sqrt (N + 1) * Real.sqrt (2 * J (χ * χ))) := by
    rw [← Real.sqrt_mul (by positivity)]
    rw [show ((N + 1 : ℕ) : ℝ) * (8 * J (χ * χ)) = 2 ^ 2 * ((N + 1) * (2 * J (χ * χ))) by
      push_cast; ring]
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
  rw [hsplit] at hT
  linarith

end

end OptimalPrecision.ExpPoly
