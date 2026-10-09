import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Algebra.Polynomial.Sequence
import Mathlib.Data.NNReal.Basic

set_option autoImplicit false

/-!
# Nonnegative Chebyshev combinations

`cone N` is the set of real polynomials `∑_{m ≤ N} c_m T_m` with all `c_m ≥ 0`, as a
submodule over `ℝ≥0`. This is the positivity notion of Proposition `qls:prop:chebyshev`:
after `x = cos θ`, `T_m(cos θ) = cos(m θ)` turns nonnegative Chebyshev coefficients into
nonnegative Laurent coefficients.

* `mul_mem`: the cones are closed under products, `cone M * cone N ⊆ cone (M + N)`, by
  `T_m T_n = (T_{m+n} + T_{|m-n|}) / 2`;
* `X_add_one_pow_mem`: `(x + 1)^k ∈ cone k` (from `X_add_one_mem` and `pow_mem`);
* `iterate_derivative_T_mem`: `T_d^{(k)} ∈ cone (d - k)` (Mathlib's
  `T_iterate_derivative_mem_span_T`, i.e. the expansions of `U_n` in the proof);
* `chebCoeff`: the coefficients in the Chebyshev basis `(T_m)_m` of `ℝ[X]`;
  `chebCoeff_nonneg` and `chebCoeff_eq_zero` read off positivity and the degree bound on the
  cone, and `eq_sum_chebCoeff` expands a cone element in `T_0, …, T_N`.
-/

namespace ChebyshevFilter

noncomputable section
open Polynomial NNReal
open Polynomial.Chebyshev (T)

/-- **Nonnegative Chebyshev combinations of degree at most `N`**: the `ℝ≥0`-span of
`T_0, …, T_N`. -/
def cone (N : ℕ) : Submodule ℝ≥0 ℝ[X] :=
  Submodule.span ℝ≥0 ((fun m : ℕ => T ℝ m) '' Set.Icc 0 N)

theorem T_mem_cone {m N : ℕ} (h : m ≤ N) : T ℝ m ∈ cone N :=
  Submodule.subset_span ⟨m, ⟨Nat.zero_le m, h⟩, rfl⟩

theorem cone_mono {M N : ℕ} (h : M ≤ N) : cone M ≤ cone N :=
  Submodule.span_mono (Set.image_mono (Set.Icc_subset_Icc le_rfl h))

theorem one_mem_cone (N : ℕ) : (1 : ℝ[X]) ∈ cone N := by
  simpa using T_mem_cone (m := 0) (Nat.zero_le N)

/-- A nonnegative real multiple stays in the cone. -/
theorem real_smul_mem {N : ℕ} {c : ℝ} (hc : 0 ≤ c) {p : ℝ[X]} (hp : p ∈ cone N) :
    c • p ∈ cone N := by
  have h := Submodule.smul_mem (cone N) (⟨c, hc⟩ : ℝ≥0) hp
  rwa [NNReal.smul_def] at h

/-- `C c * p` with `c ≥ 0` stays in the cone. -/
theorem C_mul_mem {N : ℕ} {c : ℝ} (hc : 0 ≤ c) {p : ℝ[X]} (hp : p ∈ cone N) :
    C c * p ∈ cone N := by
  rw [← smul_eq_C_mul]
  exact real_smul_mem hc hp

/-- `T_m T_n = (T_{m+n} + T_{|m-n|}) / 2`. -/
theorem T_mul_T_nat (m n : ℕ) :
    T ℝ m * T ℝ n = C (2⁻¹ : ℝ) * (T ℝ (m + n : ℕ) + T ℝ (((m : ℤ) - n).natAbs)) := by
  have h := Chebyshev.T_mul_T ℝ (m : ℤ) (n : ℤ)
  rw [Chebyshev.T_natAbs]
  have h2 : C (2⁻¹ : ℝ) * (2 : ℝ[X]) = 1 := by
    rw [show (2 : ℝ[X]) = C 2 from (map_ofNat C 2).symm, ← C_mul]
    norm_num
  push_cast
  linear_combination (C (2⁻¹ : ℝ)) * h - T ℝ (m : ℤ) * T ℝ (n : ℤ) * h2

theorem T_mul_T_mem {m n M N : ℕ} (hm : m ≤ M) (hn : n ≤ N) :
    T ℝ m * T ℝ n ∈ cone (M + N) := by
  rw [T_mul_T_nat]
  refine C_mul_mem (by norm_num) (Submodule.add_mem _ (T_mem_cone (by omega))
    (T_mem_cone (by omega)))

/-- **Products of nonnegative Chebyshev combinations** are nonnegative Chebyshev
combinations, and degrees add. -/
theorem mul_mem {M N : ℕ} {p q : ℝ[X]} (hp : p ∈ cone M) (hq : q ∈ cone N) :
    p * q ∈ cone (M + N) := by
  induction hp using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, hm, rfl⟩ := hx
    induction hq using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨n, hn, rfl⟩ := hy
      exact T_mul_T_mem hm.2 hn.2
    | zero => simp
    | add y z _ _ hy hz => rw [mul_add]; exact Submodule.add_mem _ hy hz
    | smul c y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hy
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hx

theorem pow_mem {N : ℕ} {p : ℝ[X]} (hp : p ∈ cone N) (k : ℕ) : p ^ k ∈ cone (k * N) := by
  induction k with
  | zero => simpa using one_mem_cone 0
  | succ k ih =>
    rw [pow_succ, Nat.succ_mul]
    exact mul_mem ih hp

theorem X_add_one_mem : (X + 1 : ℝ[X]) ∈ cone 1 := by
  have h1 : (X : ℝ[X]) = T ℝ ((1 : ℕ) : ℤ) := by simp
  have h0 : (1 : ℝ[X]) = T ℝ ((0 : ℕ) : ℤ) := by simp
  rw [h1, h0]
  exact Submodule.add_mem _ (T_mem_cone le_rfl) (T_mem_cone (Nat.zero_le 1))

/-- `(x + 1)^k` has nonnegative Chebyshev coefficients. -/
theorem X_add_one_pow_mem (k : ℕ) : (X + 1 : ℝ[X]) ^ k ∈ cone k := by
  simpa using pow_mem X_add_one_mem k

/-- **Differentiation preserves nonnegative Chebyshev coefficients**: `T_d^{(k)}` is a
nonnegative combination of `T_0, …, T_{d-k}`. -/
theorem iterate_derivative_T_mem (d k : ℕ) :
    derivative^[k] (T ℝ d) ∈ cone (d - k) :=
  Submodule.span_le_restrictScalars ℕ ℝ≥0 _ (Chebyshev.T_iterate_derivative_mem_span_T d k)

/-! ### Coefficients in the Chebyshev basis -/

theorem isUnit_leadingCoeff (i : ℕ) : IsUnit ((Chebyshev.chebyshevTsequence ℝ) i).leadingCoeff := by
  change IsUnit (T ℝ i).leadingCoeff
  rw [Chebyshev.leadingCoeff_T]
  exact isUnit_iff_ne_zero.mpr (pow_ne_zero _ two_ne_zero)

/-- The Chebyshev basis `(T_m)_{m ∈ ℕ}` of `ℝ[X]`. -/
def chebBasis : Module.Basis ℕ ℝ ℝ[X] :=
  (Chebyshev.chebyshevTsequence ℝ).basis isUnit_leadingCoeff

theorem chebBasis_apply (m : ℕ) : chebBasis m = T ℝ m :=
  (Chebyshev.chebyshevTsequence ℝ).basis_eq_self isUnit_leadingCoeff m

/-- The `m`th coefficient of `p` in the Chebyshev basis. -/
def chebCoeff (p : ℝ[X]) (m : ℕ) : ℝ := chebBasis.repr p m

theorem chebCoeff_T (n m : ℕ) : chebCoeff (T ℝ n) m = if n = m then 1 else 0 := by
  rw [chebCoeff, ← chebBasis_apply, Module.Basis.repr_self, Finsupp.single_apply]

/-- On the cone, Chebyshev coefficients are nonnegative and vanish beyond the degree bound. -/
theorem chebCoeff_cone {N : ℕ} {p : ℝ[X]} (hp : p ∈ cone N) :
    ∀ m, 0 ≤ chebCoeff p m ∧ (N < m → chebCoeff p m = 0) := by
  induction hp using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨n, hn, rfl⟩ := hx
    intro m
    rw [chebCoeff_T]
    refine ⟨by split_ifs <;> norm_num, fun hm => ?_⟩
    rw [if_neg (by have := hn.2; omega)]
  | zero => intro m; simp [chebCoeff]
  | add x y _ _ hx hy =>
    intro m
    simp only [chebCoeff, map_add, Finsupp.add_apply] at hx hy ⊢
    exact ⟨add_nonneg (hx m).1 (hy m).1, fun hm => by rw [(hx m).2 hm, (hy m).2 hm, add_zero]⟩
  | smul c x _ hx =>
    intro m
    rw [NNReal.smul_def]
    simp only [chebCoeff, map_smul, Finsupp.smul_apply, smul_eq_mul] at hx ⊢
    exact ⟨mul_nonneg c.2 (hx m).1, fun hm => by rw [(hx m).2 hm, mul_zero]⟩

theorem chebCoeff_nonneg {N : ℕ} {p : ℝ[X]} (hp : p ∈ cone N) (m : ℕ) : 0 ≤ chebCoeff p m :=
  (chebCoeff_cone hp m).1

theorem chebCoeff_eq_zero {N : ℕ} {p : ℝ[X]} (hp : p ∈ cone N) {m : ℕ} (hm : N < m) :
    chebCoeff p m = 0 :=
  (chebCoeff_cone hp m).2 hm

/-- A cone element is `∑_{m ≤ N} c_m T_m` with its Chebyshev coefficients `c_m`. -/
theorem eq_sum_chebCoeff {N : ℕ} {p : ℝ[X]} (hp : p ∈ cone N) :
    p = ∑ m ∈ Finset.range (N + 1), chebCoeff p m • T ℝ m := by
  have hsupp : (chebBasis.repr p).support ⊆ Finset.range (N + 1) := by
    intro m hm
    rw [Finsupp.mem_support_iff] at hm
    rw [Finset.mem_range]
    by_contra h
    exact hm (chebCoeff_eq_zero hp (by omega))
  conv_lhs => rw [← chebBasis.linearCombination_repr p]
  rw [Finsupp.linearCombination_apply, Finsupp.sum_of_support_subset _ hsupp]
  · simp only [chebBasis_apply, chebCoeff]
  · intro m _
    simp

end

end ChebyshevFilter
