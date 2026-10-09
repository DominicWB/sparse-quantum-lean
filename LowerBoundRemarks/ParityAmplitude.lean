import Mathlib.Algebra.Algebra.Operations
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Matrix.Basic
import Mathlib.Logic.Function.DependsOn

/-!
# Factorial suppression of linear-entry parity-amplitude encodings

This file formalises the structural remark that closes the subsection "What this establishes, and
what remains open" of Part `hsl` (after Theorem `hsl:thm:main`; manuscript
`sparse_quantum_algorithms.tex`, lines 2796-2813) of *Root-sparsity scaling for Hamiltonian
simulation, differential equations and linear-system solvers*.

## The remark

The lower bounds of Part `hsl` encode the parity `σ(X)` of `n` independent input blocks (the hidden
positions `j_1, …, j_n` of the search stages, or the bits of the scalar chain) in an amplitude of
`e^{-iτ H_X}`. The remark: suppose `‖H_X‖ ≤ 1` and each entry of `H_X` is linear in the membership
bits of independent input blocks. Under the independent uniform input distribution,
`E_X[σ(X) H_X^k] = 0` for `k < n`: every degree-`k` monomial misses some block, and its
correlation with that block's balanced parity vanishes. Consequently
`‖E_X[σ(X) e^{-iτ H_X}]‖ ≤ ∑_{k ≥ n} τ^k/k! ≤ e^τ τ^n/n!`.

## Formal setting

* Blocks form a finite type `B`, and `n = Fintype.card B`.
* Block `b` takes values in a finite type `Ω b`; an input is `X : ∀ b, Ω b`, and inputs are
  uniformly distributed, so `E_X[f X] = (Fintype.card (∀ b, Ω b) : ℂ)⁻¹ • ∑ X, f X`.
  (The `Ω b` need not be assumed nonempty: otherwise there are no inputs and everything is `0`.)
* Per-block signs `σ b : Ω b → ℝ` are balanced (`∑ ω, σ b ω = 0`) and, for the analytic bound,
  bounded (`|σ b ω| ≤ 1`). The parity is `parity σ X = ∏ b, σ b (X b)`.
* Hamiltonians are maps `H : (∀ b, Ω b) → A` into a `ℂ`-algebra `A`; for the analytic bound `A`
  is a complete normed `ℂ`-algebra with `‖1‖ = 1` (`NormOneClass`), e.g. square complex matrices
  with the spectral norm, or bounded operators on a nonzero Hilbert space.
* "Each entry is linear in the membership bits of independent blocks" is `IsBlockAffine H`:
  `H X = H₀ + ∑ b, F b (X b)`. An entry linear in the membership bits has the form
  `c₀ + ∑_{b,z} c_{b,z} [X_b = z]`, and `isBlockAffine_iff_membership` and
  `isBlockAffine_iff_entries` show that `IsBlockAffine` is exactly this condition, both in the
  literal form `H X = H₀ + ∑ b, ∑ z, [X b = z] • G b z` and entrywise for matrices.

## Main statements

* `moment_eq_zero`: if the signs are balanced and `H` is block-affine, then
  `∑ X, (parity σ X : ℂ) • H X ^ k = 0` for every `k < n` (`expect_moment_eq_zero` is the
  expectation form, `moment_eq_zero_membership` the literal membership-bit form).
* `exp_correlation_le_tsum`: if moreover `|σ b ω| ≤ 1`, `‖H X‖ ≤ 1` and `0 ≤ τ`, then
  `‖E_X[σ(X) e^{-iτ H_X}]‖ ≤ ∑' k, (if n ≤ k then τ^k/k! else 0)`.
* `exp_correlation_le`: under the same hypotheses, `‖E_X[σ(X) e^{-iτ H_X}]‖ ≤ e^τ τ^n/n!`
  (`exp_correlation_le_membership` is the literal membership-bit form).
* `matrix_exp_correlation_le`: the bound of the remark for square complex matrices with
  spectral norm `≤ 1` whose entries are affine functions of the membership bits.
* `hsl_moment_eq_zero`, `hsl_exp_correlation_le`: the `hsl` parity `σ(X) = (-1)^{j_1 + ⋯ + j_n}`
  with `j_b ∈ Fin m`, `m` even (`sum_hslSign` is the balancedness), averaged over the `m^n`
  inputs. The scalar precision family is `m = 2`; the search family has `m` a power of two.

## Proof outline

A function of the input depends on at most `j` blocks if it is unchanged when the blocks outside
some set of `≤ j` blocks change (Mathlib's `DependsOn`); `blockSpan j` is the `ℂ`-span of such
functions. Block-affine maps lie in `blockSpan 1` (`IsBlockAffine.mem_blockSpan`), pointwise
products add block degrees (`mul_mem_blockSpan`), so `H ^ k ∈ blockSpan k`
(`pow_mem_blockSpan`). A function of fewer than `n` blocks misses some block `b`; the involution
`swapAt b` shows that its correlation with the balanced sign of block `b` is zero
(`sum_smul_eq_zero_of_update_eq`, `sum_parity_smul_eq_zero_of_dependsOn`). For the exponential,
the series terms with `k < n` vanish by `moment_eq_zero`, every other term is bounded by `τ^k/k!`,
and `(j + n)! ≥ j! n!` gives the closed form (`tsum_tail_le`).

## Scope

This is a structural remark, not a lower bound. It bounds the parity correlation of *every*
encoding in this linear-entry class: such parity-amplitude reductions have factorially suppressed
correlation `≤ e^τ τ^n/n!` at short normalised time. It does not exclude different reductions or
different readouts, and it is not a proof that the remaining logarithmic gap of `hsl:thm:main` is
unavoidable.
-/

set_option autoImplicit false

namespace LowerBoundRemarks.ParityAmplitude

open Finset Function
open scoped Nat

/-! ### The setting -/

section Setting

variable {B : Type*} {Ω : B → Type*}

/-- The parity `σ(X) = ∏_b σ_b(X_b)` of an input `X = (X_b)_b`, built from per-block signs
`σ_b : Ω_b → ℝ`. -/
def parity [Fintype B] (σ : ∀ b, Ω b → ℝ) (X : ∀ b, Ω b) : ℝ :=
  ∏ b, σ b (X b)

/-- `H` is *block-affine*: `H X = H₀ + ∑_b F_b(X_b)` for a fixed offset `H₀` and fixed per-block
response maps `F_b : Ω_b → A`. This is exactly linearity in the membership bits `[X_b = z]`
(`isBlockAffine_iff_membership`, `isBlockAffine_iff_entries`). -/
def IsBlockAffine [Fintype B] {A : Type*} [AddCommMonoid A] (H : (∀ b, Ω b) → A) : Prop :=
  ∃ (H₀ : A) (F : ∀ b, Ω b → A), ∀ X, H X = H₀ + ∑ b, F b (X b)

/-- Functions of the input that depend on at most `j` of the blocks. -/
def fewBlockFns {A : Type*} (j : ℕ) : Set ((∀ b, Ω b) → A) :=
  {f | ∃ S : Finset B, S.card ≤ j ∧ DependsOn f (S : Set B)}

/-- Block degree at most `j`: the `ℂ`-span of the functions that depend on at most `j` blocks. -/
def blockSpan {A : Type*} [AddCommMonoid A] [Module ℂ A] (j : ℕ) :
    Submodule ℂ ((∀ b, Ω b) → A) :=
  Submodule.span ℂ (fewBlockFns j)

end Setting

/-! ### Block-affine maps are exactly the maps linear in the membership bits -/

section Membership

variable {B : Type*} [Fintype B] {Ω : B → Type*} [∀ b, Fintype (Ω b)] [∀ b, DecidableEq (Ω b)]

/-- `H` is block-affine iff it is literally a linear function of the membership bits:
`H X = H₀ + ∑_b ∑_z [X_b = z] G_{b,z}` for some `H₀` and `G`. -/
theorem isBlockAffine_iff_membership {A : Type*} [AddCommMonoid A] [Module ℂ A]
    {H : (∀ b, Ω b) → A} :
    IsBlockAffine H ↔ ∃ (H₀ : A) (G : ∀ b, Ω b → A),
      ∀ X, H X = H₀ + ∑ b, ∑ z, (if X b = z then (1 : ℂ) else 0) • G b z := by
  have key : ∀ (G : ∀ b, Ω b → A) (X : ∀ b, Ω b),
      ∑ b, ∑ z, (if X b = z then (1 : ℂ) else 0) • G b z = ∑ b, G b (X b) := by
    intro G X
    simp [ite_smul]
  simp only [IsBlockAffine, key]

/-- Literal membership-bit form: `H X = H₀ + ∑_b ∑_z [X_b = z] G_{b,z}` is block-affine. -/
theorem isBlockAffine_membership {A : Type*} [AddCommMonoid A] [Module ℂ A] (H₀ : A)
    (G : ∀ b, Ω b → A) :
    IsBlockAffine fun X : (∀ b, Ω b) =>
      H₀ + ∑ b, ∑ z, (if X b = z then (1 : ℂ) else 0) • G b z :=
  isBlockAffine_iff_membership.2 ⟨H₀, G, fun _ => rfl⟩

/-- Entrywise form: a matrix-valued `H` is block-affine iff every entry of `H X` is an affine
function `c₀ + ∑_{b,z} c_{b,z} [X_b = z]` of the membership bits. -/
theorem isBlockAffine_iff_entries {ι κ : Type*} {H : (∀ b, Ω b) → Matrix ι κ ℂ} :
    IsBlockAffine H ↔ ∃ (c₀ : ι → κ → ℂ) (c : ∀ b, Ω b → ι → κ → ℂ),
      ∀ X i j, H X i j = c₀ i j + ∑ b, ∑ z, c b z i j * (if X b = z then 1 else 0) := by
  constructor
  · rintro ⟨H₀, F, hF⟩
    refine ⟨H₀, fun b z => F b z, fun X i j => ?_⟩
    simp [hF, Matrix.sum_apply]
  · rintro ⟨c₀, c, hH⟩
    refine ⟨Matrix.of c₀, fun b ω => Matrix.of (c b ω), fun X => ?_⟩
    ext i j
    simp [hH, Matrix.sum_apply]

/-- If every matrix entry of `H X` is an affine function `c₀ + ∑_{b,z} c_{b,z} [X_b = z]` of the
membership bits, then `H` is block-affine. -/
theorem isBlockAffine_of_entries {ι κ : Type*} {H : (∀ b, Ω b) → Matrix ι κ ℂ}
    (c₀ : ι → κ → ℂ) (c : ∀ b, Ω b → ι → κ → ℂ)
    (hH : ∀ X i j, H X i j = c₀ i j + ∑ b, ∑ z, c b z i j * (if X b = z then 1 else 0)) :
    IsBlockAffine H :=
  isBlockAffine_iff_entries.2 ⟨c₀, c, hH⟩

end Membership

/-! ### Vanishing of low-degree parity correlations -/

section Vanishing

variable {B : Type*} [Fintype B] [DecidableEq B] {Ω : B → Type*} [∀ b, Fintype (Ω b)]

/-- The involution `(ω, X) ↦ (X_b, X[b ↦ ω])` of `Ω_b × inputs`. -/
def swapAt (b : B) : Equiv.Perm (Ω b × ∀ c, Ω c) :=
  Function.Involutive.toPerm (fun p => (p.2 b, Function.update p.2 b p.1)) fun p => by
    simp

/-- Summing against a balanced weight of block `b` kills every function that does not depend on
block `b`: `∑_X s(X_b) g(X) = 0` if `∑_ω s(ω) = 0` and `g` ignores `X_b`. -/
theorem sum_smul_eq_zero_of_update_eq {M : Type*} [AddCommGroup M] [Module ℂ M] (b : B)
    {s : Ω b → ℂ} (hs : ∑ ω, s ω = 0) {g : (∀ c, Ω c) → M}
    (hg : ∀ X ω, g (Function.update X b ω) = g X) :
    ∑ X, s (X b) • g X = 0 := by
  rcases isEmpty_or_nonempty (Ω b) with h | h
  · exact Finset.sum_eq_zero fun X _ => (IsEmpty.false (X b)).elim
  have key : ∑ p : Ω b × (∀ c, Ω c), s p.1 • g p.2 =
      ∑ p : Ω b × (∀ c, Ω c), s (p.2 b) • g p.2 := by
    refine Fintype.sum_equiv (swapAt b) _ _ fun p => ?_
    simp [swapAt, hg]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type] at key
  simp only [← Finset.smul_sum, ← Finset.sum_smul, hs, zero_smul, Finset.sum_const,
    Finset.card_univ] at key
  have hcard : (Fintype.card (Ω b) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [← Nat.cast_smul_eq_nsmul ℂ] at key
  exact (smul_eq_zero.mp key.symm).resolve_left hcard

/-- A function of fewer than `n = |B|` blocks has zero correlation with a product of balanced
block signs. -/
theorem sum_parity_smul_eq_zero_of_dependsOn {M : Type*} [AddCommGroup M] [Module ℂ M]
    {σ : ∀ b, Ω b → ℝ} (hσ : ∀ b, ∑ ω, σ b ω = 0) {S : Finset B}
    (hS : S.card < Fintype.card B) {f : (∀ b, Ω b) → M} (hf : DependsOn f (S : Set B)) :
    ∑ X, (parity σ X : ℂ) • f X = 0 := by
  obtain ⟨b, -, hb⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := S) (t := univ)
    (by simpa using hS)
  have hfac : ∀ X : (∀ c, Ω c), (parity σ X : ℂ) • f X =
      (σ b (X b) : ℂ) • (((∏ c ∈ univ.erase b, σ c (X c) : ℝ) : ℂ) • f X) := by
    intro X
    have hX : parity σ X = σ b (X b) * ∏ c ∈ univ.erase b, σ c (X c) :=
      (Finset.mul_prod_erase univ (fun c => σ c (X c)) (mem_univ b)).symm
    rw [hX, Complex.ofReal_mul, mul_smul]
  rw [Finset.sum_congr rfl fun X _ => hfac X]
  refine sum_smul_eq_zero_of_update_eq b (s := fun ω => (σ b ω : ℂ)) ?_ ?_
  · rw [← Complex.ofReal_sum, hσ b, Complex.ofReal_zero]
  · intro X ω
    have h1 : (∏ c ∈ univ.erase b, σ c (update X b ω c)) = ∏ c ∈ univ.erase b, σ c (X c) :=
      Finset.prod_congr rfl fun c hc => by rw [update_of_ne (ne_of_mem_erase hc)]
    have h2 : f (update X b ω) = f X :=
      hf fun c hc => update_of_ne (by rintro rfl; exact hb hc) _ _
    rw [h1, h2]

/-- Every function of block degree `j < n` has zero parity correlation. -/
theorem sum_parity_smul_eq_zero_of_mem {M : Type*} [AddCommGroup M] [Module ℂ M]
    {σ : ∀ b, Ω b → ℝ} (hσ : ∀ b, ∑ ω, σ b ω = 0) {j : ℕ} (hj : j < Fintype.card B)
    {f : (∀ b, Ω b) → M} (hf : f ∈ blockSpan j) :
    ∑ X, (parity σ X : ℂ) • f X = 0 := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨S, hS, hdep⟩ := hf
    exact sum_parity_smul_eq_zero_of_dependsOn hσ (hS.trans_lt hj) hdep
  | zero => simp
  | add f g _ _ hf hg =>
    simp only [Pi.add_apply, smul_add, Finset.sum_add_distrib, hf, hg, add_zero]
  | smul a f _ hf => simp only [Pi.smul_apply, smul_comm _ a, ← Finset.smul_sum, hf, smul_zero]

end Vanishing

/-! ### Block degree is subadditive under products -/

section Degree

variable {B : Type*} {Ω : B → Type*}

/-- Constant functions have block degree `0`, hence block degree at most `j` for every `j`. -/
theorem const_mem_blockSpan {A : Type*} [AddCommMonoid A] [Module ℂ A] (c : A) (j : ℕ) :
    (fun _ : (∀ b, Ω b) => c) ∈ blockSpan j :=
  Submodule.subset_span ⟨∅, by simp, by simpa using dependsOn_const c⟩

/-- A function of a single block has block degree `1`. -/
theorem block_mem_blockSpan {A : Type*} [AddCommMonoid A] [Module ℂ A] (b : B) (F : Ω b → A) :
    (fun X : (∀ c, Ω c) => F (X b)) ∈ blockSpan 1 :=
  Submodule.subset_span ⟨{b}, by simp, fun _ _ h => congrArg F (h b (by simp))⟩

/-- A block-affine function has block degree `1`. -/
theorem IsBlockAffine.mem_blockSpan [Fintype B] {A : Type*} [AddCommMonoid A] [Module ℂ A]
    {H : (∀ b, Ω b) → A} (hH : IsBlockAffine H) : H ∈ blockSpan 1 := by
  obtain ⟨H₀, F, hHF⟩ := hH
  have : H = (fun _ => H₀) + ∑ b, fun X : (∀ c, Ω c) => F b (X b) := by
    funext X
    simp [hHF, Finset.sum_apply]
  rw [this]
  exact add_mem (const_mem_blockSpan H₀ 1) (sum_mem fun b _ => block_mem_blockSpan b (F b))

/-- Block degree is subadditive: the pointwise product of functions of block degrees `i` and `j`
has block degree `i + j`. -/
theorem mul_mem_blockSpan {A : Type*} [Ring A] [Algebra ℂ A] {i j : ℕ} {f g : (∀ b, Ω b) → A}
    (hf : f ∈ blockSpan i) (hg : g ∈ blockSpan j) : f * g ∈ blockSpan (i + j) := by
  classical
  have hle : blockSpan (Ω := Ω) (A := A) i * blockSpan j ≤ blockSpan (i + j) := by
    rw [blockSpan, blockSpan, Submodule.span_mul_span]
    refine Submodule.span_mono ?_
    rintro _ ⟨f, ⟨S, hS, hfS⟩, g, ⟨T, hT, hgT⟩, rfl⟩
    refine ⟨S ∪ T, (card_union_le S T).trans (add_le_add hS hT), fun X Y hXY => ?_⟩
    simp only [Pi.mul_apply]
    rw [hfS fun b hb => hXY b (Finset.mem_coe.2 (Finset.mem_union_left T (Finset.mem_coe.1 hb))),
      hgT fun b hb => hXY b (Finset.mem_coe.2 (Finset.mem_union_right S (Finset.mem_coe.1 hb)))]
  exact hle (Submodule.mul_mem_mul hf hg)

/-- The `k`-th power of a function of block degree `1` has block degree `k`. -/
theorem pow_mem_blockSpan {A : Type*} [Ring A] [Algebra ℂ A] {H : (∀ b, Ω b) → A}
    (hH : H ∈ blockSpan 1) (k : ℕ) : H ^ k ∈ blockSpan k := by
  induction k with
  | zero => rw [pow_zero]; exact const_mem_blockSpan (1 : A) 0
  | succ k ih => rw [pow_succ]; exact mul_mem_blockSpan ih hH

end Degree

/-! ### Theorem 1: vanishing parity moments -/

section Moments

variable {B : Type*} [Fintype B] [DecidableEq B] {Ω : B → Type*} [∀ b, Fintype (Ω b)]

/-- **Vanishing parity moments.** If the block signs are balanced and `H` is block-affine (each
entry linear in the membership bits of independent blocks), then `∑_X σ(X) H_X^k = 0` for every
`k < n = |B|`. -/
theorem moment_eq_zero {A : Type*} [Ring A] [Algebra ℂ A] {σ : ∀ b, Ω b → ℝ}
    (hσ : ∀ b, ∑ ω, σ b ω = 0) {H : (∀ b, Ω b) → A} (hH : IsBlockAffine H) {k : ℕ}
    (hk : k < Fintype.card B) :
    ∑ X, (parity σ X : ℂ) • H X ^ k = 0 :=
  sum_parity_smul_eq_zero_of_mem hσ hk (pow_mem_blockSpan hH.mem_blockSpan k)

/-- Expectation form of `moment_eq_zero`: `E_X[σ(X) H_X^k] = 0` for `k < n` under the uniform
distribution on inputs. -/
theorem expect_moment_eq_zero {A : Type*} [Ring A] [Algebra ℂ A] {σ : ∀ b, Ω b → ℝ}
    (hσ : ∀ b, ∑ ω, σ b ω = 0) {H : (∀ b, Ω b) → A} (hH : IsBlockAffine H) {k : ℕ}
    (hk : k < Fintype.card B) :
    (Fintype.card (∀ b, Ω b) : ℂ)⁻¹ • ∑ X, (parity σ X : ℂ) • H X ^ k = 0 := by
  rw [moment_eq_zero hσ hH hk, smul_zero]

end Moments

/-! ### Theorem 2: factorial suppression of the parity correlation -/

section Exponential

/-- The exponential tail bound `∑_{k ≥ n} τ^k/k! ≤ e^τ τ^n/n!` for `τ ≥ 0`. -/
theorem tsum_tail_le {τ : ℝ} (hτ : 0 ≤ τ) (n : ℕ) :
    ∑' k, (if n ≤ k then τ ^ k / k ! else 0) ≤ Real.exp τ * τ ^ n / n ! := by
  set g : ℕ → ℝ := fun k => if n ≤ k then τ ^ k / k ! else 0 with hg
  have hgs : Summable g := by
    refine (Real.summable_pow_div_factorial τ).of_nonneg_of_le (fun k => ?_) (fun k => ?_)
    · simp only [hg]; split_ifs <;> positivity
    · simp only [hg]; split_ifs <;> first | exact le_rfl | positivity
  have hzero : ∑ i ∈ range n, g i = 0 :=
    sum_eq_zero fun i hi => if_neg (by simpa using hi)
  have h1 : HasSum (fun j => g (j + n)) (∑' k, g k) :=
    (hasSum_nat_add_iff n).mpr (by rw [hzero, add_zero]; exact hgs.hasSum)
  have h2 : HasSum (fun j => τ ^ n / n ! * (τ ^ j / j !)) (τ ^ n / n ! * Real.exp τ) := by
    have h := NormedSpace.expSeries_div_hasSum_exp τ
    rw [← Real.exp_eq_exp_ℝ] at h
    exact h.mul_left _
  have h3 : ∀ j, g (j + n) ≤ τ ^ n / n ! * (τ ^ j / j !) := by
    intro j
    have hfac : ((n ! : ℝ) * j !) ≤ ((j + n)! : ℝ) := by
      have := Nat.le_of_dvd (Nat.factorial_pos _)
        (Nat.factorial_mul_factorial_dvd_factorial_add j n)
      rw [mul_comm]
      exact_mod_cast this
    simp only [hg, le_add_iff_nonneg_left, zero_le, if_true]
    rw [pow_add, div_mul_div_comm, mul_comm (τ ^ n)]
    gcongr
  calc ∑' k, g k ≤ τ ^ n / n ! * Real.exp τ := hasSum_le h3 h1 h2
    _ = Real.exp τ * τ ^ n / n ! := by ring

/-- Averaging bound: `‖|ι|⁻¹ ∑_i v_i‖ ≤ C` whenever every `‖v_i‖ ≤ C`. -/
theorem norm_average_le {ι M : Type*} [Fintype ι] [SeminormedAddCommGroup M] [NormedSpace ℂ M]
    (v : ι → M) {C : ℝ} (hC : 0 ≤ C) (hv : ∀ i, ‖v i‖ ≤ C) :
    ‖(Fintype.card ι : ℂ)⁻¹ • ∑ i, v i‖ ≤ C := by
  rcases isEmpty_or_nonempty ι with h | h
  · simp [hC]
  have hcard : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  calc ‖(Fintype.card ι : ℂ)⁻¹ • ∑ i, v i‖
      ≤ (Fintype.card ι : ℝ)⁻¹ * ∑ i, ‖v i‖ := by
        rw [norm_smul, norm_inv, Complex.norm_natCast]
        gcongr
        exact norm_sum_le _ _
    _ ≤ (Fintype.card ι : ℝ)⁻¹ * ∑ _i : ι, C := by gcongr with i; exact hv i
    _ = C := by
        rw [sum_const, card_univ, nsmul_eq_mul]
        field_simp

variable {B : Type*} [Fintype B] [DecidableEq B] {Ω : B → Type*} [∀ b, Fintype (Ω b)]

/-- **Factorial suppression, series form.** If the block signs are balanced and bounded by `1`,
`H` is block-affine with `‖H X‖ ≤ 1`, and `τ ≥ 0`, then
`‖E_X[σ(X) e^{-iτ H_X}]‖ ≤ ∑_{k ≥ n} τ^k/k!`, where `E_X` is the uniform average over inputs. -/
theorem exp_correlation_le_tsum {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
    [NormOneClass A] {σ : ∀ b, Ω b → ℝ} (hσ : ∀ b, ∑ ω, σ b ω = 0) (hσ1 : ∀ b ω, |σ b ω| ≤ 1)
    {H : (∀ b, Ω b) → A} (hH : IsBlockAffine H) (hnorm : ∀ X, ‖H X‖ ≤ 1) {τ : ℝ} (hτ : 0 ≤ τ) :
    ‖(Fintype.card (∀ b, Ω b) : ℂ)⁻¹ •
        ∑ X, (parity σ X : ℂ) • NormedSpace.exp ((-Complex.I * τ) • H X)‖ ≤
      ∑' k, (if Fintype.card B ≤ k then τ ^ k / k ! else 0) := by
  set c : ℂ := -Complex.I * τ with hc
  have hcn : ‖c‖ = τ := by simp [hc, abs_of_nonneg hτ]
  have hpar : ∀ X, |parity σ X| ≤ 1 := fun X => by
    rw [parity, Finset.abs_prod]
    exact Finset.prod_le_one (fun b _ => abs_nonneg _) (fun b _ => hσ1 b (X b))
  -- the exponential series, averaged against the parity
  have hsum : HasSum (fun k => (Fintype.card (∀ b, Ω b) : ℂ)⁻¹ •
      ∑ X, (parity σ X : ℂ) • ((k ! : ℂ)⁻¹ • (c • H X) ^ k))
      ((Fintype.card (∀ b, Ω b) : ℂ)⁻¹ • ∑ X, (parity σ X : ℂ) • NormedSpace.exp (c • H X)) := by
    refine HasSum.const_smul _ (hasSum_sum fun X _ => ?_)
    exact (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (c • H X)).const_smul _
  -- the summable majorant
  have hgs : Summable fun k : ℕ => if Fintype.card B ≤ k then τ ^ k / k ! else 0 := by
    refine (Real.summable_pow_div_factorial τ).of_nonneg_of_le (fun k => ?_) (fun k => ?_)
    · split_ifs <;> positivity
    · split_ifs <;> first | exact le_rfl | positivity
  refine hsum.norm_le_of_bounded hgs.hasSum fun k => ?_
  by_cases hk : Fintype.card B ≤ k
  · -- a surviving term is bounded by `τ^k/k!`
    rw [if_pos hk]
    refine norm_average_le _ (by positivity) fun X => ?_
    rw [norm_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs, norm_inv,
      Complex.norm_natCast]
    have hpow : ‖(c • H X) ^ k‖ ≤ τ ^ k := by
      calc ‖(c • H X) ^ k‖ ≤ ‖c • H X‖ ^ k := norm_pow_le _ _
        _ ≤ τ ^ k := by
          gcongr
          rw [norm_smul, hcn]
          calc τ * ‖H X‖ ≤ τ * 1 := by gcongr; exact hnorm X
            _ = τ := mul_one τ
    calc |parity σ X| * ((k ! : ℝ)⁻¹ * ‖(c • H X) ^ k‖) ≤ 1 * ((k ! : ℝ)⁻¹ * τ ^ k) := by
          gcongr
          exact hpar X
      _ = τ ^ k / k ! := by ring
  · -- a term with `k < n` vanishes by `moment_eq_zero`
    rw [if_neg hk]
    have hk' : k < Fintype.card B := not_le.mp hk
    have : ∑ X, (parity σ X : ℂ) • ((k ! : ℂ)⁻¹ • (c • H X) ^ k) =
        ((k ! : ℂ)⁻¹ * c ^ k) • ∑ X, (parity σ X : ℂ) • H X ^ k := by
      rw [Finset.smul_sum]
      refine sum_congr rfl fun X _ => ?_
      simp only [smul_pow, smul_smul]
      congr 1
      ring
    rw [this, moment_eq_zero hσ hH hk', smul_zero, smul_zero, norm_zero]

/-- **Factorial suppression.** If the block signs are balanced and bounded by `1`, `H` is
block-affine (each entry linear in the membership bits of independent blocks) with `‖H X‖ ≤ 1`,
and `τ ≥ 0`, then `‖E_X[σ(X) e^{-iτ H_X}]‖ ≤ e^τ τ^n/n!`, where `n = |B|` and `E_X` is the
uniform average over inputs. -/
theorem exp_correlation_le {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
    [NormOneClass A] {σ : ∀ b, Ω b → ℝ} (hσ : ∀ b, ∑ ω, σ b ω = 0) (hσ1 : ∀ b ω, |σ b ω| ≤ 1)
    {H : (∀ b, Ω b) → A} (hH : IsBlockAffine H) (hnorm : ∀ X, ‖H X‖ ≤ 1) {τ : ℝ} (hτ : 0 ≤ τ) :
    ‖(Fintype.card (∀ b, Ω b) : ℂ)⁻¹ •
        ∑ X, (parity σ X : ℂ) • NormedSpace.exp ((-Complex.I * τ) • H X)‖ ≤
      Real.exp τ * τ ^ Fintype.card B / (Fintype.card B)! :=
  (exp_correlation_le_tsum hσ hσ1 hH hnorm hτ).trans (tsum_tail_le hτ _)

end Exponential

/-! ### Literal membership-bit and matrix forms -/

section Literal

variable {B : Type*} [Fintype B] [DecidableEq B] {Ω : B → Type*} [∀ b, Fintype (Ω b)]
  [∀ b, DecidableEq (Ω b)]

/-- `moment_eq_zero` for `H X = H₀ + ∑_b ∑_z [X_b = z] G_{b,z}`, i.e. with `H` written literally
as a linear function of the membership bits of the blocks. -/
theorem moment_eq_zero_membership {A : Type*} [Ring A] [Algebra ℂ A] {σ : ∀ b, Ω b → ℝ}
    (hσ : ∀ b, ∑ ω, σ b ω = 0) (H₀ : A) (G : ∀ b, Ω b → A) {k : ℕ}
    (hk : k < Fintype.card B) :
    ∑ X : (∀ b, Ω b), (parity σ X : ℂ) •
      (H₀ + ∑ b, ∑ z, (if X b = z then (1 : ℂ) else 0) • G b z) ^ k = 0 :=
  moment_eq_zero hσ (isBlockAffine_membership H₀ G) hk

/-- `exp_correlation_le` for `H X = H₀ + ∑_b ∑_z [X_b = z] G_{b,z}`, i.e. with `H` written
literally as a linear function of the membership bits of the blocks. -/
theorem exp_correlation_le_membership {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    [CompleteSpace A] [NormOneClass A] {σ : ∀ b, Ω b → ℝ} (hσ : ∀ b, ∑ ω, σ b ω = 0)
    (hσ1 : ∀ b ω, |σ b ω| ≤ 1) (H₀ : A) (G : ∀ b, Ω b → A)
    (hnorm : ∀ X : (∀ b, Ω b), ‖H₀ + ∑ b, ∑ z, (if X b = z then (1 : ℂ) else 0) • G b z‖ ≤ 1)
    {τ : ℝ} (hτ : 0 ≤ τ) :
    ‖(Fintype.card (∀ b, Ω b) : ℂ)⁻¹ • ∑ X : (∀ b, Ω b), (parity σ X : ℂ) •
        NormedSpace.exp ((-Complex.I * τ) •
          (H₀ + ∑ b, ∑ z, (if X b = z then (1 : ℂ) else 0) • G b z))‖ ≤
      Real.exp τ * τ ^ Fintype.card B / (Fintype.card B)! :=
  exp_correlation_le hσ hσ1 (isBlockAffine_membership H₀ G) hnorm hτ

open scoped Matrix.Norms.L2Operator in
/-- **The remark for matrices.** Let `H X` be a square complex matrix with spectral
(`ℓ²`-operator) norm at most `1`, each of whose entries is an affine function
`c₀ + ∑_{b,z} c_{b,z} [X_b = z]` of the membership bits of the blocks. Then
`‖E_X[σ(X) e^{-iτ H_X}]‖ ≤ e^τ τ^n/n!` in the spectral norm (`NormedSpace.exp` is the matrix
exponential). -/
theorem matrix_exp_correlation_le {ι : Type*} [Fintype ι] [DecidableEq ι] {σ : ∀ b, Ω b → ℝ}
    (hσ : ∀ b, ∑ ω, σ b ω = 0) (hσ1 : ∀ b ω, |σ b ω| ≤ 1) {H : (∀ b, Ω b) → Matrix ι ι ℂ}
    (c₀ : ι → ι → ℂ) (c : ∀ b, Ω b → ι → ι → ℂ)
    (hentry : ∀ X i j, H X i j = c₀ i j + ∑ b, ∑ z, c b z i j * (if X b = z then 1 else 0))
    (hnorm : ∀ X, ‖H X‖ ≤ 1) {τ : ℝ} (hτ : 0 ≤ τ) :
    ‖(Fintype.card (∀ b, Ω b) : ℂ)⁻¹ •
        ∑ X, (parity σ X : ℂ) • NormedSpace.exp ((-Complex.I * τ) • H X)‖ ≤
      Real.exp τ * τ ^ Fintype.card B / (Fintype.card B)! := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · have h0 : ∀ M : Matrix ι ι ℂ, ‖M‖ = 0 := fun M => by rw [Subsingleton.elim M 0, norm_zero]
    rw [h0]
    positivity
  · exact exp_correlation_le hσ hσ1 (isBlockAffine_of_entries c₀ c hentry) hnorm hτ

end Literal

/-! ### The `hsl` parity -/

section HSL

/-- The sign `(-1)^ω` of a hidden position `ω ∈ Fin m`. The parity of the `hsl` hard instances is
`σ(X) = (-1)^{j_1 + ⋯ + j_n} = ∏_b (-1)^{j_b}` (`parity_hslSign`). -/
def hslSign (m : ℕ) (ω : Fin m) : ℝ :=
  (-1) ^ (ω : ℕ)

/-- For even `m` the sign `(-1)^ω` is balanced on `Fin m`. -/
theorem sum_hslSign {m : ℕ} (hm : Even m) : ∑ ω : Fin m, hslSign m ω = 0 := by
  obtain ⟨r, rfl⟩ := hm
  simp only [hslSign]
  rw [Fin.sum_univ_eq_sum_range (fun i => (-1 : ℝ) ^ i) (r + r)]
  induction r with
  | zero => simp
  | succ r ih =>
    rw [show r + 1 + (r + 1) = r + r + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih]
    ring

/-- The sign `(-1)^ω` has absolute value `1`. -/
theorem abs_hslSign {m : ℕ} (ω : Fin m) : |hslSign m ω| = 1 := by
  simp [hslSign]

/-- The product of the block signs is the `hsl` parity `(-1)^{j_1 + ⋯ + j_n}`. -/
theorem parity_hslSign {n m : ℕ} (X : Fin n → Fin m) :
    parity (fun _ => hslSign m) X = (-1) ^ ∑ b, (X b : ℕ) := by
  simp [parity, hslSign, Finset.prod_pow_eq_pow_sum]

/-- `moment_eq_zero` for the `hsl` parity: `n` blocks with hidden positions `j_b ∈ Fin m`,
`m` even, and `σ(X) = (-1)^{j_1 + ⋯ + j_n}`. -/
theorem hsl_moment_eq_zero {A : Type*} [Ring A] [Algebra ℂ A] {n m : ℕ} (hm : Even m)
    {H : (Fin n → Fin m) → A} (hH : IsBlockAffine H) {k : ℕ} (hk : k < n) :
    ∑ X : Fin n → Fin m, ((-1 : ℂ) ^ ∑ b, (X b : ℕ)) • H X ^ k = 0 := by
  have h := moment_eq_zero (σ := fun _ => hslSign m) (fun _ => sum_hslSign hm) hH (k := k)
    (by simpa using hk)
  simpa [parity_hslSign] using h

/-- `exp_correlation_le` for the `hsl` parity: `n` blocks with hidden positions `j_b ∈ Fin m`,
`m` even, `σ(X) = (-1)^{j_1 + ⋯ + j_n}`, and the uniform average over the `m^n` inputs. -/
theorem hsl_exp_correlation_le {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
    [NormOneClass A] {n m : ℕ} (hm : Even m) {H : (Fin n → Fin m) → A} (hH : IsBlockAffine H)
    (hnorm : ∀ X, ‖H X‖ ≤ 1) {τ : ℝ} (hτ : 0 ≤ τ) :
    ‖((m : ℂ) ^ n)⁻¹ • ∑ X : Fin n → Fin m, ((-1 : ℂ) ^ ∑ b, (X b : ℕ)) •
        NormedSpace.exp ((-Complex.I * τ) • H X)‖ ≤ Real.exp τ * τ ^ n / n ! := by
  have h := exp_correlation_le (σ := fun _ => hslSign m) (fun _ => sum_hslSign hm)
    (fun _ ω => (abs_hslSign ω).le) hH hnorm hτ
  simpa [parity_hslSign] using h

end HSL

end LowerBoundRemarks.ParityAmplitude
