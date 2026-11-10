import ODELowerBoundExtensions.Dyson.Degree
import TimeDependentExtensions.ODE.Discretisation
import GeneralODE.Analysis.ExpBounds
import SparseHamiltonian.CayleyApproximation

set_option autoImplicit false

/-!
# The Dyson series of a piecewise-constant generator (`odel:lem:dyson`)

Manuscript: the proof of Lemma `odel:lem:dyson`. On a mesh with `M` cells, cell `r`
of duration `a r` with constant generator `X r`, the propagator is the ordered product
`exp(a_{M-1} X_{M-1}) ⋯ exp(a_0 X_0)` (`TimeDependent.evolution`, cell `0` acting first).
Expanding every exponential and collecting the terms of total degree `k` gives the Dyson series:
its degree-`k` part is the sum over the **configurations** `c` (occupation numbers
`c r ≥ 0` with `∑ c r = k`) of

  `∏_r a_r^{c_r}/c_r! · X_{M-1}^{c_{M-1}} ⋯ X_0^{c_0}`,

the time-ordered product of `k` factors with the multinomial weights of the proof
(`k!/∏ c_r!` sorted label sequences, times `1/k!`). Configurations replace sorted i.i.d. labels:
the same operator identity, without the multinomial count.

* `Cfg K M`: configurations of total degree at most `K` (a finite type, the LCU label set);
* `coef a c = ∏_r a_r^{c_r}/c_r!` and `cfgProduct X c = X_{M-1}^{c_{M-1}} ⋯ X_0^{c_0}`;
* `truncated a X K M = ∑_{c : Cfg K M} coef a c • cfgProduct X c`, the degree-`K` truncation;
* `truncated_error`: `‖∏ exp(a_r X_r) - truncated‖ ≤ ∑_{k>K} λ^k/k!`, `λ = ∑_r a_r ‖X_r‖`
  (proof of Lemma `odel:lem:dyson`, coefficient sequence `z^k/k!`);
* `sum_coef_le_exp`: the coefficient mass is at most `exp(∑_r a_r)` (proof of Lemma
  `odel:lem:dyson`).

The proof of `truncated_error` is an induction on the number of cells: `truncated_succ` splits
the configurations of `M + 1` cells by the occupation of the last cell (`Cfg.extend`,
`Cfg.restrict`), and the scalar identity `expTail_add` adds up the errors.
-/

namespace ODELowerBoundExtensions.Dyson

noncomputable section

open SparseHamiltonian
open SparseHamiltonian.TimeDependent (evolution)
open scoped Nat BigOperators

/-- **Configurations** of total degree at most `K` on `M` cells: occupation numbers
`c r ∈ {0, …, K}` with `∑_r c r ≤ K`. This finite type is the LCU label set of the Dyson
series truncated at degree `K` (proof of Lemma `odel:lem:dyson`). -/
abbrev Cfg (K M : ℕ) : Type := {c : Fin M → Fin (K + 1) // ∑ r, (c r : ℕ) ≤ K}

namespace Cfg

variable {K M : ℕ}

/-- The total degree `∑_r c r` (number of block-encoded factors). -/
def degree (c : Cfg K M) : ℕ := ∑ r, (c.1 r : ℕ)

/-- A configuration has total degree at most `K`. -/
theorem degree_le (c : Cfg K M) : c.degree ≤ K := c.2

/-- The occupation number of cell `r`, extended by `0` beyond the last cell. -/
def count (c : Cfg K M) (r : ℕ) : ℕ := if h : r < M then (c.1 ⟨r, h⟩ : ℕ) else 0

/-- The empty configuration (degree `0`). -/
def zero : Cfg K M := ⟨fun _ => 0, by simp⟩

/-- Extend a configuration of `M` cells and degree at most `K - j` by the occupation `j` of the
new last cell `M`. -/
def extend (j : ℕ) (hj : j ≤ K) (c : Cfg (K - j) M) : Cfg K (M + 1) :=
  ⟨Fin.snoc (α := fun _ => Fin (K + 1))
      (fun r => ⟨(c.1 r : ℕ), by have := (c.1 r).isLt; omega⟩) ⟨j, by omega⟩, by
    have h : ∑ r, (c.1 r : ℕ) ≤ K - j := c.2
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    omega⟩

/-- Restrict a configuration of `M + 1` cells whose last occupation is `j` to its first `M`
cells; the result has degree at most `K - j`. -/
def restrict (j : ℕ) (c : Cfg K (M + 1)) (h : (c.1 (Fin.last M) : ℕ) = j) : Cfg (K - j) M :=
  ⟨fun r => ⟨(c.1 r.castSucc : ℕ), by
      have h1 : ∑ i, (c.1 i : ℕ) ≤ K := c.2
      rw [Fin.sum_univ_castSucc] at h1
      have h2 : (c.1 r.castSucc : ℕ) ≤ ∑ i : Fin M, (c.1 i.castSucc : ℕ) :=
        Finset.single_le_sum (f := fun i : Fin M => (c.1 i.castSucc : ℕ))
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ r)
      omega⟩, by
    have h1 : ∑ i, (c.1 i : ℕ) ≤ K := c.2
    rw [Fin.sum_univ_castSucc] at h1
    simp only
    omega⟩

/-- The extended configuration has occupation `j` on the last cell. -/
theorem extend_last (j : ℕ) (hj : j ≤ K) (c : Cfg (K - j) M) :
    ((extend j hj c).1 (Fin.last M) : ℕ) = j := by
  simp [extend]

/-- Extending a restriction gives back the configuration. -/
theorem extend_restrict (j : ℕ) (hj : j ≤ K) (c : Cfg K (M + 1))
    (h : (c.1 (Fin.last M) : ℕ) = j) : extend j hj (restrict j c h) = c := by
  refine Subtype.ext (funext fun r => ?_)
  refine Fin.lastCases ?_ (fun i => ?_) r
  · exact Fin.ext (by simp [extend, h])
  · exact Fin.ext (by simp [extend, restrict])

/-- Restricting an extension gives back the configuration. -/
theorem restrict_extend (j : ℕ) (hj : j ≤ K) (c : Cfg (K - j) M) :
    restrict j (extend j hj c) (extend_last j hj c) = c :=
  Subtype.ext (funext fun r => Fin.ext (by simp [extend, restrict]))

/-- The occupation of the new last cell is `j`. -/
theorem count_extend_self (j : ℕ) (hj : j ≤ K) (c : Cfg (K - j) M) :
    (extend j hj c).count M = j := by
  have h : (⟨M, Nat.lt_succ_self M⟩ : Fin (M + 1)) = Fin.last M := rfl
  simp [count, h, extend]

/-- Below the last cell, extension does not change the occupations. -/
theorem count_extend_of_lt (j : ℕ) (hj : j ≤ K) (c : Cfg (K - j) M) {r : ℕ} (hr : r < M) :
    (extend j hj c).count r = c.count r := by
  have h : (⟨r, Nat.lt_succ_of_lt hr⟩ : Fin (M + 1)) = Fin.castSucc ⟨r, hr⟩ := rfl
  simp only [count, dif_pos hr, dif_pos (Nat.lt_succ_of_lt hr)]
  unfold extend
  rw [h]
  simp only [Fin.snoc_castSucc]

end Cfg

/-- The Dyson weight `∏_r a_r^{c_r}/c_r!` of a configuration (proof of Lemma `odel:lem:dyson`). -/
def coef {K M : ℕ} (a : ℕ → ℝ) (c : Cfg K M) : ℝ :=
  ∏ r : Fin M, a r ^ (c.1 r : ℕ) / ((c.1 r : ℕ)! : ℝ)

/-- The Dyson weight of nonnegative durations is nonnegative. -/
theorem coef_nonneg {K M : ℕ} (a : ℕ → ℝ) (ha : ∀ r, 0 ≤ a r) (c : Cfg K M) :
    0 ≤ coef a c :=
  Finset.prod_nonneg fun r _ => div_nonneg (pow_nonneg (ha r) _) (Nat.cast_nonneg _)

/-- The empty configuration has weight one. -/
theorem coef_zero {K M : ℕ} (a : ℕ → ℝ) : coef a (Cfg.zero : Cfg K M) = 1 := by
  simp [coef, Cfg.zero]

/-- The weight of an extended configuration picks up the factor `a_M^j/j!`. -/
theorem coef_extend {K M : ℕ} (a : ℕ → ℝ) (j : ℕ) (hj : j ≤ K) (c : Cfg (K - j) M) :
    coef a (Cfg.extend j hj c) = coef a c * (a M ^ j / (j ! : ℝ)) := by
  unfold coef
  rw [Fin.prod_univ_castSucc]
  simp [Cfg.extend]

/-- **Coefficient mass** (proof of Lemma `odel:lem:dyson`):
`∑_{c : Cfg K M} coef a c ≤ exp(∑_{r<M} a r)`. -/
theorem sum_coef_le_exp (a : ℕ → ℝ) (ha : ∀ r, 0 ≤ a r) (K M : ℕ) :
    ∑ c : Cfg K M, coef a c ≤ Real.exp (∑ r ∈ Finset.range M, a r) := by
  classical
  set f : (Fin M → Fin (K + 1)) → ℝ :=
    fun c => ∏ r : Fin M, a r ^ (c r : ℕ) / ((c r : ℕ)! : ℝ) with hf
  have hf0 : ∀ c, 0 ≤ f c := fun c =>
    Finset.prod_nonneg fun r _ => div_nonneg (pow_nonneg (ha r) _) (Nat.cast_nonneg _)
  have hsub : ∑ c : Cfg K M, coef a c =
      ∑ c ∈ Finset.univ.filter (fun c : Fin M → Fin (K + 1) => ∑ r, (c r : ℕ) ≤ K), f c := by
    rw [← Finset.sum_subtype_eq_sum_filter, Finset.subtype_univ]
    rfl
  have hrange : ∀ r : Fin M, ∑ j : Fin (K + 1), a r ^ (j : ℕ) / ((j : ℕ)! : ℝ) ≤
      Real.exp (a r) := fun r => by
    rw [Fin.sum_univ_eq_sum_range (fun j => a r ^ j / (j ! : ℝ)) (K + 1)]
    exact Real.sum_le_exp_of_nonneg (ha r) (K + 1)
  calc ∑ c : Cfg K M, coef a c
      ≤ ∑ c : Fin M → Fin (K + 1), f c := by
        rw [hsub]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun c _ _ => hf0 c
    _ = ∏ r : Fin M, ∑ j : Fin (K + 1), a r ^ (j : ℕ) / ((j : ℕ)! : ℝ) := by
        rw [Fintype.prod_sum]
    _ ≤ ∏ r : Fin M, Real.exp (a r) :=
        Finset.prod_le_prod (fun r _ => Finset.sum_nonneg fun j _ =>
          div_nonneg (pow_nonneg (ha r) _) (Nat.cast_nonneg _)) fun r _ => hrange r
    _ = Real.exp (∑ r ∈ Finset.range M, a r) := by
        rw [← Real.exp_sum, Fin.sum_univ_eq_sum_range (fun r => a r) M]

/-- The coefficient mass is at least the weight `1` of the empty configuration. -/
theorem one_le_sum_coef (a : ℕ → ℝ) (ha : ∀ r, 0 ≤ a r) (K M : ℕ) :
    1 ≤ ∑ c : Cfg K M, coef a c := by
  rw [← coef_zero a (K := K) (M := M)]
  exact Finset.single_le_sum (fun c _ => coef_nonneg a ha c) (Finset.mem_univ _)

/-- The scalar identity behind the induction on cells:
`∑_{k>K} (x+y)^k/k! = ∑_{j≤K} x^j/j! ∑_{i>K-j} y^i/i! + (∑_{j>K} x^j/j!) e^y`. -/
theorem expTail_add (x y : ℝ) (K : ℕ) :
    expTail (x + y) K =
      ∑ j ∈ Finset.range (K + 1), x ^ j / (j ! : ℝ) * expTail y (K - j) +
        expTail x K * Real.exp y := by
  have hbin : ∀ m : ℕ, (x + y) ^ m / (m ! : ℝ) =
      ∑ k ∈ Finset.range (m + 1), x ^ k / (k ! : ℝ) * (y ^ (m - k) / ((m - k)! : ℝ)) := by
    intro m
    rw [add_pow, Finset.sum_div]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hkm : k ≤ m := Nat.le_of_lt_succ (Finset.mem_range.1 hk)
    have h₂ := Nat.choose_mul_factorial_mul_factorial hkm
    have hk0 : (0 : ℝ) < (k ! : ℝ) := by exact_mod_cast Nat.factorial_pos _
    have hmk0 : (0 : ℝ) < ((m - k)! : ℝ) := by exact_mod_cast Nat.factorial_pos _
    have hc0 : (m.choose k : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hkm).ne'
    rw [← h₂, Nat.cast_mul, Nat.cast_mul]
    field_simp
  have hdouble : ∑ m ∈ Finset.range (K + 1), (x + y) ^ m / (m ! : ℝ) =
      ∑ j ∈ Finset.range (K + 1), ∑ i ∈ Finset.range (K - j + 1),
        x ^ j / (j ! : ℝ) * (y ^ i / (i ! : ℝ)) := by
    rw [Finset.sum_congr rfl fun m _ => hbin m,
      Finset.sum_range_diag_flip (K + 1) fun k i => x ^ k / (k ! : ℝ) * (y ^ i / (i ! : ℝ))]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjK : j ≤ K := Nat.le_of_lt_succ (Finset.mem_range.1 hj)
    rw [show K + 1 - j = K - j + 1 by omega]
  unfold expTail
  rw [hdouble, Real.exp_add]
  simp only [mul_sub, Finset.mul_sum, Finset.sum_sub_distrib, sub_mul, Finset.sum_mul]
  ring

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- The time-ordered product `X_{M-1}^{c_{M-1}} ⋯ X_0^{c_0}` of a configuration. -/
def cfgProduct {K M : ℕ} (X : ℕ → V →L[ℂ] V) (c : Cfg K M) : V →L[ℂ] V :=
  evolution (fun r => X r ^ c.count r) M

/-- **The Dyson series truncated at degree `K`** on `M` cells. -/
def truncated (a : ℕ → ℝ) (X : ℕ → V →L[ℂ] V) (K M : ℕ) : V →L[ℂ] V :=
  ∑ c : Cfg K M, coef a c • cfgProduct X c

omit [CompleteSpace V] in
/-- Every operator on a trivial space has norm zero. -/
theorem opNorm_eq_zero_of_subsingleton [Subsingleton V] (T : V →L[ℂ] V) : ‖T‖ = 0 := by
  have hT : T = 0 := ContinuousLinearMap.ext fun _ => Subsingleton.elim _ _
  rw [hT, norm_zero]

omit [CompleteSpace V] in
/-- `‖Y^n‖ ≤ ‖Y‖^n`, including `n = 0` on a possibly trivial space. -/
theorem norm_pow_le_norm_pow (Y : V →L[ℂ] V) (n : ℕ) : ‖Y ^ n‖ ≤ ‖Y‖ ^ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [pow_zero, pow_zero]
    exact ContinuousLinearMap.norm_id_le
  · exact norm_pow_le' Y hn

omit [CompleteSpace V] in
/-- Real scalars on the factors of an ordered product come out as their product. -/
theorem evolution_real_smul (κ : ℕ → ℝ) (A : ℕ → V →L[ℂ] V) (M : ℕ) :
    evolution (fun r => κ r • A r) M = (∏ r ∈ Finset.range M, κ r) • evolution A M := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [TimeDependent.evolution_succ, TimeDependent.evolution_succ, ih, smul_mul_smul_comm,
      Finset.prod_range_succ, mul_comm (κ M)]

omit [CompleteSpace V] in
/-- A real scalar on every factor comes out with the power `degree c`. -/
theorem cfgProduct_smul {K M : ℕ} (κ : ℝ) (Y : ℕ → V →L[ℂ] V) (c : Cfg K M) :
    cfgProduct (fun r => κ • Y r) c = (κ ^ c.degree) • cfgProduct Y c := by
  have hpow : (fun r => (κ • Y r) ^ c.count r) = fun r => (κ ^ c.count r) • Y r ^ c.count r :=
    funext fun r => smul_pow _ _ _
  have hdeg : ∑ r ∈ Finset.range M, c.count r = c.degree := by
    rw [← Fin.sum_univ_eq_sum_range (fun r => c.count r) M]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp [Cfg.count, r.isLt]
  unfold cfgProduct
  rw [hpow, evolution_real_smul, Finset.prod_pow_eq_pow_sum, hdeg]

omit [CompleteSpace V] in
/-- A product of contractions is a contraction. -/
theorem cfgProduct_norm_le_one {K M : ℕ} (Y : ℕ → V →L[ℂ] V) (hY : ∀ r, ‖Y r‖ ≤ 1)
    (c : Cfg K M) : ‖cfgProduct Y c‖ ≤ 1 :=
  TimeDependent.evolution_norm_le_one _ (fun r =>
    (norm_pow_le_norm_pow (Y r) _).trans (pow_le_one₀ (norm_nonneg _) (hY r))) M

omit [CompleteSpace V] in
/-- The product of an extended configuration picks up the factor `X_M^j` on the left. -/
theorem cfgProduct_extend {K M : ℕ} (X : ℕ → V →L[ℂ] V) (j : ℕ) (hj : j ≤ K)
    (c : Cfg (K - j) M) : cfgProduct X (Cfg.extend j hj c) = X M ^ j * cfgProduct X c := by
  unfold cfgProduct
  rw [TimeDependent.evolution_succ, Cfg.count_extend_self]
  congr 1
  exact TimeDependentExtensions.evolution_congr' _ _ M fun r hr => by
    rw [Cfg.count_extend_of_lt j hj c hr]

omit [CompleteSpace V] in
/-- Adding the last cell: the configurations of `M + 1` cells split by the occupation `j` of
the last cell. -/
theorem truncated_succ (a : ℕ → ℝ) (X : ℕ → V →L[ℂ] V) (K M : ℕ) :
    truncated a X K (M + 1) =
      ∑ j ∈ Finset.range (K + 1),
        (a M ^ j / (j ! : ℝ)) • (X M ^ j * truncated a X (K - j) M) := by
  classical
  unfold truncated
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.range (K + 1))
    (g := fun c : Cfg K (M + 1) => (c.1 (Fin.last M) : ℕ))
    (fun c _ => Finset.mem_range.2 (c.1 (Fin.last M)).isLt)]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjK : j ≤ K := Nat.le_of_lt_succ (Finset.mem_range.1 hj)
  rw [Finset.mul_sum, Finset.smul_sum]
  refine Finset.sum_bij' (fun c hc => Cfg.restrict j c (Finset.mem_filter.1 hc).2)
    (fun c _ => Cfg.extend j hjK c) (fun c _ => Finset.mem_univ _)
    (fun c _ => Finset.mem_filter.2 ⟨Finset.mem_univ _, Cfg.extend_last j hjK c⟩)
    (fun c hc => Cfg.extend_restrict j hjK c (Finset.mem_filter.1 hc).2)
    (fun c _ => Cfg.restrict_extend j hjK c) ?_
  intro c hc
  have hcj := (Finset.mem_filter.1 hc).2
  conv_lhs => rw [← Cfg.extend_restrict j hjK c hcj]
  rw [coef_extend, cfgProduct_extend, mul_smul_comm, smul_smul, mul_comm (coef a _)]

/-- The ordered product of the cell exponentials is bounded by `exp(∑_r a_r ‖X_r‖)`. -/
theorem evolution_exp_norm_le (a : ℕ → ℝ) (ha : ∀ r, 0 ≤ a r) (X : ℕ → V →L[ℂ] V) (M : ℕ) :
    ‖evolution (fun r => NormedSpace.exp (a r • X r)) M‖ ≤
      Real.exp (∑ r ∈ Finset.range M, a r * ‖X r‖) := by
  rcases subsingleton_or_nontrivial V with hV | hV
  · rw [opNorm_eq_zero_of_subsingleton]
    exact (Real.exp_pos _).le
  · induction M with
    | zero => simp
    | succ M ih =>
      rw [TimeDependent.evolution_succ, Finset.sum_range_succ, Real.exp_add,
        mul_comm (Real.exp (∑ r ∈ Finset.range M, a r * ‖X r‖))]
      refine (norm_mul_le _ _).trans (mul_le_mul ?_ ih (norm_nonneg _) (Real.exp_pos _).le)
      refine (GeneralODE.ExpBounds.norm_exp_le _).trans (le_of_eq ?_)
      rw [norm_smul, Real.norm_of_nonneg (ha M)]

/-- One cell: the truncated exponential series. -/
theorem exp_sub_partial_norm_le (a : ℝ) (ha : 0 ≤ a) (Y : V →L[ℂ] V) (K : ℕ) :
    ‖NormedSpace.exp (a • Y) - ∑ j ∈ Finset.range (K + 1), (a ^ j / (j ! : ℝ)) • Y ^ j‖ ≤
      expTail (a * ‖Y‖) K := by
  rcases subsingleton_or_nontrivial V with hV | hV
  · rw [opNorm_eq_zero_of_subsingleton]
    exact expTail_nonneg _ (mul_nonneg ha (norm_nonneg _)) K
  · have h := CayleyApproximation.exp_tail_norm_le (a • Y) (K + 1)
    have hterm : ∀ j : ℕ, ((j.factorial : ℂ)⁻¹ • (a • Y) ^ j) = (a ^ j / (j ! : ℝ)) • Y ^ j := by
      intro j
      rw [RCLike.real_smul_eq_coe_smul (K := ℂ) a Y,
        RCLike.real_smul_eq_coe_smul (K := ℂ) (a ^ j / (j ! : ℝ)) (Y ^ j), smul_pow, smul_smul]
      congr 1
      push_cast
      ring
    simp only [hterm] at h
    rw [norm_smul, Real.norm_of_nonneg ha] at h
    exact h

/-- **Truncation error of the Dyson series** (proof of Lemma `odel:lem:dyson`): for durations
`a r ≥ 0`, `‖exp(a_{M-1} X_{M-1}) ⋯ exp(a_0 X_0) - truncated a X K M‖ ≤ ∑_{k>K} λ^k/k!` with
`λ = ∑_{r<M} a_r ‖X_r‖`. -/
theorem truncated_error (a : ℕ → ℝ) (ha : ∀ r, 0 ≤ a r) (X : ℕ → V →L[ℂ] V) (K M : ℕ) :
    ‖evolution (fun r => NormedSpace.exp (a r • X r)) M - truncated a X K M‖ ≤
      expTail (∑ r ∈ Finset.range M, a r * ‖X r‖) K := by
  induction M generalizing K with
  | zero =>
    have h0 : truncated a X K 0 = 1 := by
      unfold truncated
      rw [Fintype.sum_eq_single Cfg.zero (fun c hc => (hc (Subsingleton.elim c _)).elim),
        coef_zero, one_smul]
      rfl
    rw [TimeDependent.evolution_zero, h0, sub_self, norm_zero]
    exact expTail_nonneg _ (by simp) K
  | succ M ih =>
    have hc : ∀ j : ℕ, 0 ≤ a M ^ j / (j ! : ℝ) := fun j =>
      div_nonneg (pow_nonneg (ha M) _) (Nat.cast_nonneg _)
    have hsplit :
        NormedSpace.exp (a M • X M) * evolution (fun r => NormedSpace.exp (a r • X r)) M -
          ∑ j ∈ Finset.range (K + 1),
            (a M ^ j / (j ! : ℝ)) • (X M ^ j * truncated a X (K - j) M) =
        ∑ j ∈ Finset.range (K + 1), (a M ^ j / (j ! : ℝ)) •
            (X M ^ j * (evolution (fun r => NormedSpace.exp (a r • X r)) M -
              truncated a X (K - j) M)) +
          (NormedSpace.exp (a M • X M) -
            ∑ j ∈ Finset.range (K + 1), (a M ^ j / (j ! : ℝ)) • X M ^ j) *
            evolution (fun r => NormedSpace.exp (a r • X r)) M := by
      simp only [mul_sub, smul_sub, Finset.sum_sub_distrib, sub_mul, Finset.sum_mul,
        smul_mul_assoc]
      abel
    rw [TimeDependent.evolution_succ, truncated_succ, hsplit]
    calc _ ≤ ∑ j ∈ Finset.range (K + 1), a M ^ j / (j ! : ℝ) *
            (‖X M‖ ^ j * expTail (∑ r ∈ Finset.range M, a r * ‖X r‖) (K - j)) +
          expTail (a M * ‖X M‖) K * Real.exp (∑ r ∈ Finset.range M, a r * ‖X r‖) := by
          refine (norm_add_le _ _).trans (add_le_add ((norm_sum_le _ _).trans
            (Finset.sum_le_sum fun j _ => ?_)) ?_)
          · rw [norm_smul, Real.norm_of_nonneg (hc j)]
            exact mul_le_mul_of_nonneg_left ((norm_mul_le _ _).trans
              (mul_le_mul (norm_pow_le_norm_pow _ _) (ih (K - j)) (norm_nonneg _)
                (pow_nonneg (norm_nonneg _) _))) (hc j)
          · exact (norm_mul_le _ _).trans (mul_le_mul (exp_sub_partial_norm_le _ (ha M) _ K)
              (evolution_exp_norm_le a ha X M) (norm_nonneg _)
              (expTail_nonneg _ (mul_nonneg (ha M) (norm_nonneg _)) K))
      _ = expTail (a M * ‖X M‖ + ∑ r ∈ Finset.range M, a r * ‖X r‖) K := by
          rw [expTail_add]
          congr 1
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [mul_pow]
          ring
      _ = expTail (∑ r ∈ Finset.range (M + 1), a r * ‖X r‖) K := by
          rw [Finset.sum_range_succ, add_comm]

end

end ODELowerBoundExtensions.Dyson
