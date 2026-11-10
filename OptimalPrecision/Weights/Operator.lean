import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Power series in the derivative acting on polynomials

Exponential polynomials `t ↦ e^{-t} π(t)` are represented by their polynomial
part `π`. Differentiation becomes `π ↦ π' - π`, and the backward integrals
`∫_t^∞` and the resolvents `(-∂ - c)^{-1}` of the proof of
Theorem `opt:thm:weights` become power series in the derivative `D`. This file
defines the action

  `op s π = ∑ᵢ sᵢ D^i π`

of a formal power series `s` on polynomials over a field (a finite sum on each
polynomial), proves that it is a ring homomorphism into the linear
endomorphisms, and evaluates it on a polynomial presented by its Taylor
coefficients at a point. With `x = 1 - D` (the operator `-∂` on exponential
polynomials), all inverse operators of the proof are inverses of units in the
power series ring.
-/

namespace OptimalPrecision.ExpPoly

noncomputable section

open Polynomial Finset Nat
open scoped Polynomial

section Generic

variable {K : Type*} [Field K]

/-- `D^i` as a linear endomorphism of `K[X]`. -/
abbrev derivPow (i : ℕ) : K[X] →ₗ[K] K[X] := (derivative : K[X] →ₗ[K] K[X]) ^ i

theorem derivPow_apply (i : ℕ) (π : K[X]) : derivPow i π = derivative^[i] π := by
  simp [derivPow, Module.End.pow_apply]

theorem derivPow_eq_zero {π : K[X]} {i : ℕ} (h : π.natDegree < i) : derivPow i π = 0 := by
  rw [derivPow_apply]; exact iterate_derivative_eq_zero h

theorem natDegree_derivPow_le (π : K[X]) (i : ℕ) : (derivPow i π).natDegree ≤ π.natDegree := by
  rw [derivPow_apply]
  exact (natDegree_iterate_derivative π i).trans (Nat.sub_le _ _)

theorem derivPow_add (i j : ℕ) (π : K[X]) : derivPow (i + j) π = derivPow i (derivPow j π) := by
  simp [derivPow, pow_add, Module.End.mul_apply]

/-- The action of a power series in the derivative. -/
def op (s : PowerSeries K) (π : K[X]) : K[X] :=
  ∑ i ∈ range (π.natDegree + 1), PowerSeries.coeff i s • derivPow i π

/-- Any range beyond the degree computes the same finite sum. -/
theorem op_eq_sum (s : PowerSeries K) {π : K[X]} {M : ℕ} (hM : π.natDegree ≤ M) :
    op s π = ∑ i ∈ range (M + 1), PowerSeries.coeff i s • derivPow i π := by
  unfold op
  apply Finset.sum_subset
  · intro i hi
    simp only [Finset.mem_range] at hi ⊢
    omega
  · intro i _ hi
    simp only [Finset.mem_range, not_lt] at hi
    rw [derivPow_eq_zero (by omega), smul_zero]

theorem natDegree_op_le (s : PowerSeries K) (π : K[X]) : (op s π).natDegree ≤ π.natDegree := by
  unfold op
  apply natDegree_sum_le_of_forall_le
  intro i _
  exact (natDegree_smul_le _ _).trans (natDegree_derivPow_le π i)

theorem op_add_right (s : PowerSeries K) (π ρ : K[X]) : op s (π + ρ) = op s π + op s ρ := by
  set M := max π.natDegree ρ.natDegree
  rw [op_eq_sum s (M := M) (natDegree_add_le π ρ), op_eq_sum s (le_max_left _ _),
    op_eq_sum s (le_max_right _ _), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_add, smul_add]

theorem op_smul_right (s : PowerSeries K) (c : K) (π : K[X]) : op s (c • π) = c • op s π := by
  rw [op_eq_sum s (M := π.natDegree) (natDegree_smul_le c π), op, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_comm]

theorem op_sub_right (s : PowerSeries K) (π ρ : K[X]) : op s (π - ρ) = op s π - op s ρ := by
  rw [sub_eq_add_neg, op_add_right, ← neg_one_smul K ρ, op_smul_right, neg_one_smul,
    ← sub_eq_add_neg]

theorem op_sum_right {ι : Type*} (s : PowerSeries K) (t : Finset ι) (π : ι → K[X]) :
    op s (∑ i ∈ t, π i) = ∑ i ∈ t, op s (π i) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    simp [op]
  | insert i t hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, op_add_right, ih]

theorem op_add_left (s t : PowerSeries K) (π : K[X]) : op (s + t) π = op s π + op t π := by
  simp only [op, map_add, add_smul, Finset.sum_add_distrib]

theorem op_smul_left (c : K) (s : PowerSeries K) (π : K[X]) : op (c • s) π = c • op s π := by
  simp only [op, map_smul, smul_eq_mul, mul_smul, Finset.smul_sum]

theorem op_one (π : K[X]) : op 1 π = π := by
  rw [op, Finset.sum_eq_single 0]
  · simp
  · intro i _ hi
    rw [PowerSeries.coeff_one, if_neg hi, zero_smul]
  · intro h; simp at h

theorem op_X (π : K[X]) : op PowerSeries.X π = derivative π := by
  rw [op_eq_sum PowerSeries.X (M := π.natDegree + 1) (by omega), Finset.sum_eq_single 1]
  · simp [PowerSeries.coeff_X, derivPow]
  · intro i _ hi
    rw [PowerSeries.coeff_X, if_neg hi, zero_smul]
  · intro h; simp at h

/-- Multiplicativity: the action is a ring homomorphism. -/
theorem op_mul (s t : PowerSeries K) (π : K[X]) : op (s * t) π = op s (op t π) := by
  set M := π.natDegree
  have hdeg : (op t π).natDegree ≤ M := natDegree_op_le t π
  rw [op_eq_sum s hdeg, op_eq_sum (s * t) (le_refl M), op_eq_sum t (le_refl M)]
  have hR : ∑ a ∈ range (M + 1), PowerSeries.coeff a s •
      derivPow a (∑ b ∈ range (M + 1), PowerSeries.coeff b t • derivPow b π) =
      ∑ a ∈ range (M + 1), ∑ b ∈ range (M + 1),
        (PowerSeries.coeff a s * PowerSeries.coeff b t) • derivPow (a + b) π := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_smul, smul_smul, derivPow_add]
  rw [hR]
  have hL : ∑ i ∈ range (M + 1), PowerSeries.coeff i (s * t) • derivPow i π =
      ∑ i ∈ range (M + 1), ∑ a ∈ range (i + 1),
        (PowerSeries.coeff a s * PowerSeries.coeff (i - a) t) • derivPow (a + (i - a)) π := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_smul]
    refine Finset.sum_congr rfl fun a ha => ?_
    have : a + (i - a) = i := by
      have := Finset.mem_range.mp ha; omega
    rw [this]
  rw [hL, Finset.sum_range_diag_flip (M + 1)
    (fun a b => (PowerSeries.coeff a s * PowerSeries.coeff b t) • derivPow (a + b) π)]
  refine Finset.sum_congr rfl fun a ha => ?_
  apply Finset.sum_subset
  · intro b hb
    simp only [Finset.mem_range] at hb ⊢
    omega
  · intro b hb hb'
    simp only [Finset.mem_range, not_lt] at hb hb'
    have := Finset.mem_range.mp ha
    rw [derivPow_eq_zero (by omega), smul_zero]

theorem op_pow (s : PowerSeries K) (n : ℕ) (π : K[X]) : op (s ^ n) π = (op s)^[n] π := by
  induction n generalizing π with
  | zero => simp [op_one]
  | succ n ih => rw [pow_succ, op_mul, ih, Function.iterate_succ_apply]

/-- The operator `x = 1 - D`, i.e. `-∂` on exponential polynomials `e^{-t} π(t)`. -/
def xs : PowerSeries K := 1 - PowerSeries.X

theorem op_xs (π : K[X]) : op xs π = π - derivative π := by
  rw [xs, sub_eq_add_neg, op_add_left, ← neg_one_smul K PowerSeries.X, op_smul_left, op_one,
    op_X, neg_one_smul, ← sub_eq_add_neg]

theorem constantCoeff_xs : PowerSeries.constantCoeff (xs : PowerSeries K) = 1 := by
  simp [xs]

/-- An operator that is inverted on the power-series side is inverted on polynomials. -/
theorem op_inv_cancel {s : PowerSeries K} (hs : PowerSeries.constantCoeff s ≠ 0) (π : K[X]) :
    op s (op s⁻¹ π) = π := by
  rw [← op_mul, PowerSeries.mul_inv_cancel s hs, op_one]

theorem op_inv_cancel' {s : PowerSeries K} (hs : PowerSeries.constantCoeff s ≠ 0) (π : K[X]) :
    op s⁻¹ (op s π) = π := by
  rw [← op_mul, PowerSeries.inv_mul_cancel s hs, op_one]

/-- Injectivity of an invertible operator. -/
theorem op_injective {s : PowerSeries K} (hs : PowerSeries.constantCoeff s ≠ 0)
    {π ρ : K[X]} (h : op s π = op s ρ) : π = ρ := by
  rw [← op_inv_cancel' hs π, h, op_inv_cancel' hs ρ]

/-- Compatibility with a ring homomorphism of the coefficient field. -/
theorem op_map {L : Type*} [Field L] (f : K →+* L) (s : PowerSeries K) (π : K[X]) :
    (op s π).map f = op (PowerSeries.map f s) (π.map f) := by
  rw [op_eq_sum (PowerSeries.map f s) (M := π.natDegree) (natDegree_map_le), op,
    Polynomial.map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Polynomial.map_smul, derivPow_apply, derivPow_apply, iterate_derivative_map,
    PowerSeries.coeff_map]

/-- Ring homomorphisms of fields commute with inversion of power series. -/
theorem map_inv_powerSeries {L : Type*} [Field L] (f : K →+* L) (s : PowerSeries K) :
    PowerSeries.map f s⁻¹ = (PowerSeries.map f s)⁻¹ := by
  by_cases hs : PowerSeries.constantCoeff s = 0
  · have hfs : PowerSeries.constantCoeff (PowerSeries.map f s) = 0 := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
        PowerSeries.coeff_zero_eq_constantCoeff_apply, hs, map_zero]
    rw [PowerSeries.inv_eq_zero.mpr hs, PowerSeries.inv_eq_zero.mpr hfs, map_zero]
  · have hfs : PowerSeries.constantCoeff (PowerSeries.map f s) ≠ 0 := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
        PowerSeries.coeff_zero_eq_constantCoeff_apply]
      exact (map_ne_zero f).mpr hs
    rw [PowerSeries.eq_inv_iff_mul_eq_one hfs, ← map_mul, PowerSeries.inv_mul_cancel s hs, map_one]

theorem map_xs {L : Type*} [Field L] (f : K →+* L) :
    PowerSeries.map f (xs : PowerSeries K) = xs := by
  simp [xs]

variable [CharZero K]

/-- The polynomial with prescribed Taylor data `d₀, …, d_D` at `a`, scaled by `E`:
`E ∑_m (d_m / m!) (X - a)^m`. -/
def shifted (a E : K) (d : ℕ → K) (D : ℕ) : K[X] :=
  taylor (-a) (E • ∑ m ∈ range (D + 1), C (d m / (m ! : K)) * X ^ m)

omit [CharZero K] in
theorem taylor_shifted (a E : K) (d : ℕ → K) (D : ℕ) :
    taylor a (shifted a E d D) = E • ∑ m ∈ range (D + 1), C (d m / (m ! : K)) * X ^ m := by
  rw [shifted, taylor_taylor, add_neg_cancel, taylor_zero]

omit [CharZero K] in
theorem natDegree_shifted_le (a E : K) (d : ℕ → K) (D : ℕ) :
    (shifted a E d D).natDegree ≤ D := by
  rw [shifted, natDegree_taylor]
  refine (natDegree_smul_le _ _).trans ?_
  apply natDegree_sum_le_of_forall_le
  intro m hm
  refine (natDegree_C_mul_le _ _).trans ?_
  rw [natDegree_X_pow]
  exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)

omit [CharZero K] in
/-- Compatibility of the shifted polynomial with a ring homomorphism. -/
theorem shifted_map {L : Type*} [Field L] (f : K →+* L) (a E : K) (d : ℕ → K) (D : ℕ) :
    (shifted a E d D).map f = shifted (f a) (f E) (fun m => f (d m)) D := by
  simp only [shifted, taylor_apply, Polynomial.map_comp, Polynomial.map_smul, Polynomial.map_sum,
    Polynomial.map_mul, Polynomial.map_pow, map_C, map_X, Polynomial.map_add, Polynomial.map_neg,
    map_neg, map_div₀,
    map_natCast]

/-- `D^i` of the shifted polynomial, read at `a`, returns `E` times the `i`-th datum. -/
theorem eval_derivPow_shifted (a E : K) (d : ℕ → K) (D i : ℕ) :
    (derivPow i (shifted a E d D)).eval a = if i ≤ D then E * d i else 0 := by
  have hcoeff := taylor_coeff (r := a) (f := shifted a E d D) i
  rw [taylor_shifted] at hcoeff
  have hD : derivPow i (shifted a E d D) = (i ! : K) • hasseDeriv i (shifted a E d D) := by
    rw [derivPow_apply, ← factorial_smul_hasseDeriv]
    simp [nsmul_eq_mul, Polynomial.smul_eq_C_mul]
  rw [hD, eval_smul, ← hcoeff]
  simp only [coeff_smul, finsetSum_coeff, coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero,
    smul_eq_mul]
  have hi : (i ! : K) ≠ 0 := by exact_mod_cast (Nat.factorial_pos i).ne'
  split_ifs with hiD
  · rw [Finset.sum_ite_eq]
    rw [if_pos (Finset.mem_range.mpr (Nat.lt_succ_of_le hiD))]
    field_simp
  · rw [Finset.sum_ite_eq, if_neg (by simp [Finset.mem_range]; omega)]
    simp

/-- **Evaluation of a power series in the derivative** on the shifted polynomial. -/
theorem eval_op_shifted (a E : K) (d : ℕ → K) (D : ℕ) (s : PowerSeries K) :
    (op s (shifted a E d D)).eval a =
      E * ∑ i ∈ range (D + 1), PowerSeries.coeff i s * d i := by
  rw [op_eq_sum s (natDegree_shifted_le a E d D), eval_finsetSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [eval_smul, eval_derivPow_shifted, if_pos (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)),
    smul_eq_mul]
  ring

end Generic

/-! ### Evaluation of complex exponential polynomials -/

/-- The value at `t` of the exponential polynomial `e^{-t} π(t)`. -/
def ev (t : ℂ) (π : ℂ[X]) : ℂ := Complex.exp (-t) * π.eval t

theorem ev_add (t : ℂ) (π ρ : ℂ[X]) : ev t (π + ρ) = ev t π + ev t ρ := by
  simp [ev, mul_add]

theorem ev_sub (t : ℂ) (π ρ : ℂ[X]) : ev t (π - ρ) = ev t π - ev t ρ := by
  simp [ev, mul_sub]

theorem ev_smul (t c : ℂ) (π : ℂ[X]) : ev t (c • π) = c * ev t π := by
  simp [ev]; ring

theorem ev_sum {ι : Type*} (s : Finset ι) (t : ℂ) (π : ι → ℂ[X]) :
    ev t (∑ i ∈ s, π i) = ∑ i ∈ s, ev t (π i) := by
  simp [ev, eval_finsetSum, Finset.mul_sum]

/-- **The evaluation functional `L`.** With `E = e^a`, the value at `a` of
`s(D)` applied to the exponential polynomial with Taylor data `d` at `a` is the
pairing `∑_i s_i d_i`. -/
theorem ev_op_shifted (a : ℂ) (d : ℕ → ℂ) (D : ℕ) (s : PowerSeries ℂ) :
    ev a (op s (shifted a (Complex.exp a) d D)) =
      ∑ i ∈ range (D + 1), PowerSeries.coeff i s * d i := by
  rw [ev, eval_op_shifted, ← mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero,
    one_mul]

end

end OptimalPrecision.ExpPoly
