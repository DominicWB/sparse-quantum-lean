import SparseLowerBounds.Helpers.Adversary.PhaseInner

set_option synthInstance.maxHeartbeats 400000

section
/-!
# The additive (positive-weight) adversary with Schur certificates

Manuscript lines 3743-3797 (proof of Lemma `odel:lem:outer`, "a direct positive
spectral-adversary construction ... the standard spectral-adversary theorem is
used as in [BSS]"). This module proves the bounded-error positive-weight
adversary theorem for Boolean programs (`OracleCircuit.Program` over the phase
oracles `x ↦ P.phase (y x)` of a projection family `P`, Query/PhaseOracle) on a
finite input set `X`, in an elementary form: no operator norms and no
Perron-Frobenius.

* **Progress** `W(ψ) = Σ_{x,x'} Γ x x' δ x δ x' Re ⟪ψ x, ψ x'⟫` for a
  nonnegative symmetric adversary matrix `Γ` and weights `δ` (`progress`).
* **Schur certificate** for the masked matrix `Γ ∘ Δ_i`
  (`(Γ ∘ Δ_i) x x' = Γ x x'` when the inputs differ at bit `i`, else `0`,
  `masked`): positive weights `μ` with `Σ_{x'} (Γ ∘ Δ_i) x x' μ x' ≤ λ μ x`
  (`SchurCert`). It bounds the bilinear form of `Γ ∘ Δ_i` by `λ`
  (`schur_bound`, the Schur test via `u u' ≤ (u² μ'/μ + u'² μ/μ')/2`), which is
  how the norm bounds `‖Γ ∘ Δ_{c,k,z}‖ ≤ √(M/2) d √(m/2)` of
  eq. `odel:eq:outermask` are used.
* **One query** changes the progress by at most `2 λ Σ_x δ_x² ‖ψ_x‖²`
  (`abs_progress_query_sub_le`), because
  `⟪O_x ψ, O_{x'} ψ'⟫ - ⟪ψ, ψ'⟫ = -2 Σ_{i : y x i ≠ y x' i} ⟪P_i ψ, P_i ψ'⟫` and
  `Σ_i ‖P_i ψ‖² ≤ ‖ψ‖²` (`Helpers.Adversary.norm_sq_eq_add_sum`); fixed gates
  leave it unchanged and inverse queries are queries (`ProjFamily.star_phase`),
  so a program changes it by at most `2 λ count Σ_x δ_x² ‖ψ_x‖²`
  (`abs_progress_program_sub_le`).
* **Observable gap** (`abs_re_inner_sub_le`, `norm_inner_le_of_gap`): for a
  contraction `A` and vectors of equal norm `r ≤ 1`,
  `|Re⟪ψ, Aψ⟫ - Re⟪φ, Aφ⟫| ≤ 2 √(2r² - 2|⟪ψ, φ⟫|)`, so an expectation gap `g`
  forces `|⟪ψ, φ⟫| ≤ r² - g²/8`; a decision with correlation `β` gives gap `2β`
  and `|⟪ψ_x, ψ_{x'}⟫| ≤ r² - β²/2`.
* **Count bounds** with uniform weights and a minimum degree `D ≤ Σ_{x'} Γ x x'`
  (no regularity of `Γ` is assumed): `count_ge` (`κ D ≤ 2 λ count` whenever
  `Γ`-joined final states have overlap at most `‖φ₀‖² - κ`) and the
  bounded-error decision form `decision_count_ge` (`(β²/2) D ≤ 2 λ count`).
-/

namespace SparseLowerBounds.PositiveAdversary

noncomputable section
open SparseHamiltonian OracleCircuit
open scoped InnerProductSpace

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {X I : Type*} [Fintype X] [Fintype I]

/-- The masked adversary matrix `Γ ∘ Δ_i`: the entry `Γ x x'` survives only
when the inputs differ at bit `i`. -/
def masked (Γ : X → X → ℝ) (y : X → I → Bool) (i : I) (x x' : X) : ℝ :=
  if y x i = y x' i then 0 else Γ x x'

/-- **Weighted Schur certificate** with constant `lam` for `Γ ∘ Δ_i`: positive
weights `μ` with `Σ_{x'} (Γ ∘ Δ_i) x x' μ x' ≤ lam μ x` for every `x`. -/
def SchurCert (Γ : X → X → ℝ) (y : X → I → Bool) (i : I) (lam : ℝ) : Prop :=
  ∃ μ : X → ℝ, (∀ x, 0 < μ x) ∧ ∀ x, ∑ x', masked Γ y i x x' * μ x' ≤ lam * μ x

/-- The adversary progress `W(ψ) = Σ_{x,x'} Γ x x' δ x δ x' Re ⟪ψ x, ψ x'⟫`. -/
def progress (Γ : X → X → ℝ) (δ : X → ℝ) (ψ : X → K) : ℝ :=
  ∑ x, ∑ x', Γ x x' * δ x * δ x' * (⟪ψ x, ψ x'⟫_ℂ).re

omit [Fintype X] [Fintype I] in
/-- The masked matrix is nonnegative. -/
theorem masked_nonneg (Γ : X → X → ℝ) (hΓ0 : ∀ x x', 0 ≤ Γ x x') (y : X → I → Bool) (i : I)
    (x x' : X) : 0 ≤ masked Γ y i x x' := by
  unfold masked
  split_ifs
  · exact le_rfl
  · exact hΓ0 x x'

omit [Fintype X] [Fintype I] in
/-- The masked matrix of a symmetric `Γ` is symmetric. -/
theorem masked_symm (Γ : X → X → ℝ) (hΓs : ∀ x x', Γ x x' = Γ x' x) (y : X → I → Bool)
    (i : I) (x x' : X) : masked Γ y i x x' = masked Γ y i x' x := by
  unfold masked
  by_cases h : y x i = y x' i
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (Ne.symm h), hΓs]

/-- Weighted AM-GM: `a b ≤ (a² μ'/μ + b² μ/μ')/2` for `μ, μ' > 0`. -/
theorem mul_le_amgm {a b μ μ' : ℝ} (hμ : 0 < μ) (hμ' : 0 < μ') :
    a * b ≤ (a ^ 2 / μ * μ' + b ^ 2 / μ' * μ) / 2 := by
  have h : (a ^ 2 / μ * μ' + b ^ 2 / μ' * μ) / 2 - a * b =
      (a * μ' - b * μ) ^ 2 / (2 * μ * μ') := by
    field_simp
    ring
  have : 0 ≤ (a * μ' - b * μ) ^ 2 / (2 * μ * μ') :=
    div_nonneg (sq_nonneg _) (mul_pos (mul_pos two_pos hμ) hμ').le
  linarith

omit [Fintype I] in
/-- **Schur test.** A symmetric nonnegative `Γ` with a Schur certificate for
`Γ ∘ Δ_i` has bilinear form at most `lam Σ u²` on every real vector. -/
theorem schur_bound (Γ : X → X → ℝ) (hΓ0 : ∀ x x', 0 ≤ Γ x x')
    (hΓs : ∀ x x', Γ x x' = Γ x' x) (y : X → I → Bool) (i : I) {lam : ℝ}
    (hc : SchurCert Γ y i lam) (u : X → ℝ) :
    ∑ x, ∑ x', masked Γ y i x x' * u x * u x' ≤ lam * ∑ x, u x ^ 2 := by
  obtain ⟨μ, hμ, hrow⟩ := hc
  have hf : ∀ x, ∑ x', masked Γ y i x x' * (u x ^ 2 / μ x) * μ x' ≤ lam * u x ^ 2 := by
    intro x
    have h1 : ∑ x', masked Γ y i x x' * (u x ^ 2 / μ x) * μ x' =
        u x ^ 2 / μ x * ∑ x', masked Γ y i x x' * μ x' := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun x' _ => by ring
    have h2 : u x ^ 2 / μ x * (lam * μ x) = lam * u x ^ 2 := by
      rw [div_mul_eq_mul_div, div_eq_iff (hμ x).ne']
      ring
    rw [h1, ← h2]
    exact mul_le_mul_of_nonneg_left (hrow x) (div_nonneg (sq_nonneg _) (hμ x).le)
  have hterm : ∀ x x', masked Γ y i x x' * u x * u x' ≤
      (masked Γ y i x x' * (u x ^ 2 / μ x) * μ x' +
        masked Γ y i x' x * (u x' ^ 2 / μ x') * μ x) / 2 := by
    intro x x'
    rw [masked_symm Γ hΓs y i x' x]
    calc masked Γ y i x x' * u x * u x' = masked Γ y i x x' * (u x * u x') := by ring
      _ ≤ masked Γ y i x x' * ((u x ^ 2 / μ x * μ x' + u x' ^ 2 / μ x' * μ x) / 2) :=
        mul_le_mul_of_nonneg_left (mul_le_amgm (hμ x) (hμ x')) (masked_nonneg Γ hΓ0 y i x x')
      _ = _ := by ring
  have hB : ∑ x, ∑ x', masked Γ y i x' x * (u x' ^ 2 / μ x') * μ x =
      ∑ x, ∑ x', masked Γ y i x x' * (u x ^ 2 / μ x) * μ x' := Finset.sum_comm
  calc ∑ x, ∑ x', masked Γ y i x x' * u x * u x'
      ≤ ∑ x, ∑ x', (masked Γ y i x x' * (u x ^ 2 / μ x) * μ x' +
          masked Γ y i x' x * (u x' ^ 2 / μ x') * μ x) / 2 :=
        Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun x' _ => hterm x x'
    _ = (∑ x, ∑ x', masked Γ y i x x' * (u x ^ 2 / μ x) * μ x' +
          ∑ x, ∑ x', masked Γ y i x' x * (u x' ^ 2 / μ x') * μ x) / 2 := by
        rw [← Finset.sum_add_distrib, Finset.sum_div]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [← Finset.sum_add_distrib, Finset.sum_div]
    _ = ∑ x, ∑ x', masked Γ y i x x' * (u x ^ 2 / μ x) * μ x' := by rw [hB]; ring
    _ ≤ ∑ x, lam * u x ^ 2 := Finset.sum_le_sum fun x _ => hf x
    _ = lam * ∑ x, u x ^ 2 := by rw [Finset.mul_sum]

omit [Fintype X] in
/-- `|Σ_i (-2) S_i| ≤ 2 Σ_i B_i` when `|S_i| ≤ B_i`. -/
theorem abs_sum_neg_two_mul_le {S B : I → ℝ} (h : ∀ i, |S i| ≤ B i) :
    |∑ i, -2 * S i| ≤ 2 * ∑ i, B i := by
  calc |∑ i, -2 * S i| ≤ ∑ i, |-2 * S i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, 2 * B i := Finset.sum_le_sum fun i _ => by
        rw [abs_mul, abs_neg, abs_two]
        exact mul_le_mul_of_nonneg_left (h i) two_pos.le
    _ = 2 * ∑ i, B i := by rw [Finset.mul_sum]

/-- **One query.** With certificates `lam` for every bit, a query of the phase
oracle changes the progress by at most `2 lam Σ_x δ_x² ‖ψ_x‖²`. -/
theorem abs_progress_query_sub_le (P : ProjFamily K I) (y : X → I → Bool)
    (Γ : X → X → ℝ) (hΓ0 : ∀ x x', 0 ≤ Γ x x') (hΓs : ∀ x x', Γ x x' = Γ x' x)
    {lam : ℝ} (hlam : 0 ≤ lam) (hcert : ∀ i, SchurCert Γ y i lam) (δ : X → ℝ) (ψ : X → K) :
    |progress Γ δ (fun x => P.phase (y x) (ψ x)) - progress Γ δ ψ| ≤
      2 * lam * ∑ x, δ x ^ 2 * ‖ψ x‖ ^ 2 := by
  have hpt : ∀ x x', Γ x x' * δ x * δ x' *
        (⟪P.phase (y x) (ψ x), P.phase (y x') (ψ x')⟫_ℂ).re -
      Γ x x' * δ x * δ x' * (⟪ψ x, ψ x'⟫_ℂ).re = ∑ i, -2 * (masked Γ y i x x' * δ x * δ x' *
        (⟪P.proj i (ψ x), P.proj i (ψ x')⟫_ℂ).re) := by
    intro x x'
    rw [← mul_sub, re_inner_phase_sub, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold masked
    split_ifs <;> ring
  have hswap : ∀ f : X → X → I → ℝ, ∑ x, ∑ x', ∑ i, f x x' i = ∑ i, ∑ x, ∑ x', f x x' i := by
    intro f
    calc ∑ x, ∑ x', ∑ i, f x x' i = ∑ x, ∑ i, ∑ x', f x x' i :=
          Finset.sum_congr rfl fun x _ => Finset.sum_comm
      _ = ∑ i, ∑ x, ∑ x', f x x' i := Finset.sum_comm
  have hdiff : progress Γ δ (fun x => P.phase (y x) (ψ x)) - progress Γ δ ψ =
      ∑ i, -2 * ∑ x, ∑ x', masked Γ y i x x' * δ x * δ x' *
        (⟪P.proj i (ψ x), P.proj i (ψ x')⟫_ℂ).re := by
    simp only [progress, ← Finset.sum_sub_distrib, hpt, Finset.mul_sum]
    exact hswap _
  have hT : ∀ i, |∑ x, ∑ x', masked Γ y i x x' * δ x * δ x' *
      (⟪P.proj i (ψ x), P.proj i (ψ x')⟫_ℂ).re| ≤
        lam * ∑ x, δ x ^ 2 * ‖P.proj i (ψ x)‖ ^ 2 := by
    intro i
    have hu := schur_bound Γ hΓ0 hΓs y i (hcert i) (fun x => |δ x| * ‖P.proj i (ψ x)‖)
    simp only [mul_pow, sq_abs] at hu
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_trans ?_ hu)
    refine Finset.sum_le_sum fun x _ => (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun x' _ => ?_)
    have hm := masked_nonneg Γ hΓ0 y i x x'
    have hc : |(⟪P.proj i (ψ x), P.proj i (ψ x')⟫_ℂ).re| ≤
        ‖P.proj i (ψ x)‖ * ‖P.proj i (ψ x')‖ :=
      (Complex.abs_re_le_norm _).trans (norm_inner_le_norm _ _)
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hm]
    calc masked Γ y i x x' * |δ x| * |δ x'| * |(⟪P.proj i (ψ x), P.proj i (ψ x')⟫_ℂ).re|
        ≤ masked Γ y i x x' * |δ x| * |δ x'| * (‖P.proj i (ψ x)‖ * ‖P.proj i (ψ x')‖) :=
          mul_le_mul_of_nonneg_left hc (mul_nonneg (mul_nonneg hm (abs_nonneg _)) (abs_nonneg _))
      _ = masked Γ y i x x' * (|δ x| * ‖P.proj i (ψ x)‖) * (|δ x'| * ‖P.proj i (ψ x')‖) := by
          ring
  have hre : ∑ i, lam * ∑ x, δ x ^ 2 * ‖P.proj i (ψ x)‖ ^ 2 =
      lam * ∑ x, δ x ^ 2 * ∑ i, ‖P.proj i (ψ x)‖ ^ 2 := by
    rw [← Finset.mul_sum, Finset.sum_comm]
    simp only [Finset.mul_sum]
  rw [hdiff]
  refine (abs_sum_neg_two_mul_le hT).trans ?_
  rw [hre, ← mul_assoc]
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left
    (sum_norm_proj_sq_le P (ψ x)) (sq_nonneg _)) (mul_nonneg two_pos.le hlam)

/-- **Program bound.** A Boolean program changes the progress by at most
`2 lam count Σ_x δ_x² ‖ψ_x‖²` (fixed gates: `0`; queries and inverse queries:
`abs_progress_query_sub_le`; norms are preserved by unitaries). -/
theorem abs_progress_program_sub_le (P : ProjFamily K I) (y : X → I → Bool)
    (Γ : X → X → ℝ) (hΓ0 : ∀ x x', 0 ≤ Γ x x') (hΓs : ∀ x x', Γ x x' = Γ x' x)
    {lam : ℝ} (hlam : 0 ≤ lam) (hcert : ∀ i, SchurCert Γ y i lam)
    (q : OracleCircuit.Program (fun x => P.phase (y x))) (δ : X → ℝ) (ψ : X → K) :
    |progress Γ δ (fun x => q.eval x (ψ x)) - progress Γ δ ψ| ≤
      2 * lam * q.count * ∑ x, δ x ^ 2 * ‖ψ x‖ ^ 2 := by
  induction q generalizing ψ with
  | fixed U hU =>
    show |progress Γ δ (fun x => U (ψ x)) - progress Γ δ ψ| ≤ 2 * lam * ((0 : ℕ) : ℝ) * _
    have h : progress Γ δ (fun x => U (ψ x)) = progress Γ δ ψ := by
      simp only [progress, inner_map_map_of_isUnitary hU]
    rw [h, sub_self, abs_zero, Nat.cast_zero, mul_zero, zero_mul]
  | query =>
    show |progress Γ δ (fun x => P.phase (y x) (ψ x)) - progress Γ δ ψ| ≤
      2 * lam * ((1 : ℕ) : ℝ) * _
    rw [Nat.cast_one, mul_one]
    exact abs_progress_query_sub_le P y Γ hΓ0 hΓs hlam hcert δ ψ
  | queryAdjoint =>
    show |progress Γ δ (fun x => star (P.phase (y x)) (ψ x)) - progress Γ δ ψ| ≤
      2 * lam * ((1 : ℕ) : ℝ) * _
    simp only [P.star_phase, Nat.cast_one, mul_one]
    exact abs_progress_query_sub_le P y Γ hΓ0 hΓs hlam hcert δ ψ
  | seq p r hp hr =>
    show |progress Γ δ (fun x => p.eval x (r.eval x (ψ x))) - progress Γ δ ψ| ≤
      2 * lam * ((p.count + r.count : ℕ) : ℝ) * _
    have hnorm : ∀ x, ‖r.eval x (ψ x)‖ = ‖ψ x‖ := fun x =>
      norm_map_of_isUnitary (r.eval_unitary (fun x => P.isUnitary_phase (y x)) x) (ψ x)
    have h1 := hp (fun x => r.eval x (ψ x))
    have h2 := hr ψ
    simp only [hnorm] at h1
    have h3 := abs_add_le
      (progress Γ δ (fun x => p.eval x (r.eval x (ψ x))) -
        progress Γ δ (fun x => r.eval x (ψ x)))
      (progress Γ δ (fun x => r.eval x (ψ x)) - progress Γ δ ψ)
    rw [sub_add_sub_cancel] at h3
    rw [Nat.cast_add]
    calc _ ≤ _ := h3
      _ ≤ 2 * lam * p.count * ∑ x, δ x ^ 2 * ‖ψ x‖ ^ 2 +
          2 * lam * r.count * ∑ x, δ x ^ 2 * ‖ψ x‖ ^ 2 := add_le_add h1 h2
      _ = _ := by ring

omit [CompleteSpace K] in
/-- **Observable gap** (the bounded-error step, lines 3795-3797): for a
contraction `A` and vectors of equal norm at most one,
`|Re⟪ψ, Aψ⟫ - Re⟪φ, Aφ⟫| ≤ 2 √(2‖ψ‖² - 2|⟪ψ, φ⟫|)`. -/
theorem abs_re_inner_sub_le {A : K →L[ℂ] K} (hA : ‖A‖ ≤ 1) {ψ φ : K} (hn : ‖ψ‖ = ‖φ‖)
    (h1 : ‖ψ‖ ≤ 1) :
    |(⟪ψ, A ψ⟫_ℂ).re - (⟪φ, A φ⟫_ℂ).re| ≤ 2 * Real.sqrt (2 * ‖ψ‖ ^ 2 - 2 * ‖⟪ψ, φ⟫_ℂ‖) := by
  -- phase-align `φ` against `ψ`
  obtain ⟨c, hc, hcz⟩ : ∃ c : ℂ, ‖c‖ = 1 ∧ c * ⟪ψ, φ⟫_ℂ = (‖⟪ψ, φ⟫_ℂ‖ : ℂ) := by
    by_cases hz : ⟪ψ, φ⟫_ℂ = 0
    · exact ⟨1, norm_one, by rw [hz, norm_zero, mul_zero, Complex.ofReal_zero]⟩
    · have hz' : (‖⟪ψ, φ⟫_ℂ‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
      refine ⟨(starRingEnd ℂ) ⟪ψ, φ⟫_ℂ / (‖⟪ψ, φ⟫_ℂ‖ : ℂ), ?_, ?_⟩
      · rw [norm_div, Complex.norm_conj]
        simp [hz]
      · rw [div_mul_eq_mul_div, Complex.conj_mul', sq, mul_div_assoc, div_self hz', mul_one]
  set φ' : K := c • φ with hφ'
  have hnφ' : ‖φ'‖ = ‖ψ‖ := by rw [hφ', norm_smul, hc, one_mul, hn]
  have hinner : ⟪ψ, φ'⟫_ℂ = (‖⟪ψ, φ⟫_ℂ‖ : ℂ) := by rw [hφ', inner_smul_right, hcz]
  have hexp : ⟪φ', A φ'⟫_ℂ = ⟪φ, A φ⟫_ℂ := by
    rw [hφ', map_smul, inner_smul_left, inner_smul_right, ← mul_assoc, Complex.conj_mul', hc]
    simp
  have hdist : ‖ψ - φ'‖ ^ 2 = 2 * ‖ψ‖ ^ 2 - 2 * ‖⟪ψ, φ⟫_ℂ‖ := by
    rw [norm_sub_sq (𝕜 := ℂ), hinner, hnφ']
    simp only [RCLike.re_to_complex, Complex.ofReal_re]
    ring
  have hkey : ⟪ψ, A ψ⟫_ℂ - ⟪φ', A φ'⟫_ℂ = ⟪ψ - φ', A ψ⟫_ℂ + ⟪φ', A (ψ - φ')⟫_ℂ := by
    rw [inner_sub_left, map_sub, inner_sub_right]
    ring
  have hAψ : ‖A ψ‖ ≤ 1 := (A.le_opNorm ψ).trans (mul_le_one₀ hA (norm_nonneg _) h1)
  have hAd : ‖A (ψ - φ')‖ ≤ ‖ψ - φ'‖ :=
    (A.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) hA)
  have hφ'1 : ‖φ'‖ ≤ 1 := hnφ'.trans_le h1
  have hbound : ‖⟪ψ, A ψ⟫_ℂ - ⟪φ', A φ'⟫_ℂ‖ ≤ 2 * ‖ψ - φ'‖ := by
    rw [hkey]
    calc _ ≤ ‖⟪ψ - φ', A ψ⟫_ℂ‖ + ‖⟪φ', A (ψ - φ')⟫_ℂ‖ := norm_add_le _ _
      _ ≤ ‖ψ - φ'‖ * ‖A ψ‖ + ‖φ'‖ * ‖A (ψ - φ')‖ :=
          add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
      _ ≤ ‖ψ - φ'‖ * 1 + 1 * ‖ψ - φ'‖ :=
          add_le_add (mul_le_mul_of_nonneg_left hAψ (norm_nonneg _))
            (mul_le_mul hφ'1 hAd (norm_nonneg _) zero_le_one)
      _ = 2 * ‖ψ - φ'‖ := by ring
  have hsq : ‖ψ - φ'‖ = Real.sqrt (2 * ‖ψ‖ ^ 2 - 2 * ‖⟪ψ, φ⟫_ℂ‖) := by
    rw [← hdist, Real.sqrt_sq (norm_nonneg _)]
  calc |(⟪ψ, A ψ⟫_ℂ).re - (⟪φ, A φ⟫_ℂ).re| = |(⟪ψ, A ψ⟫_ℂ - ⟪φ', A φ'⟫_ℂ).re| := by
        rw [Complex.sub_re, hexp]
    _ ≤ ‖⟪ψ, A ψ⟫_ℂ - ⟪φ', A φ'⟫_ℂ‖ := Complex.abs_re_le_norm _
    _ ≤ 2 * ‖ψ - φ'‖ := hbound
    _ = _ := by rw [hsq]

omit [CompleteSpace K] in
/-- **Observable gap, overlap form**: an expectation gap `g ≥ 0` of a
contraction forces `|⟪ψ, φ⟫| ≤ ‖ψ‖² - g²/8`. -/
theorem norm_inner_le_of_gap {A : K →L[ℂ] K} (hA : ‖A‖ ≤ 1) {ψ φ : K} (hn : ‖ψ‖ = ‖φ‖)
    (h1 : ‖ψ‖ ≤ 1) {g : ℝ} (hg : 0 ≤ g)
    (hgap : g ≤ |(⟪ψ, A ψ⟫_ℂ).re - (⟪φ, A φ⟫_ℂ).re|) :
    ‖⟪ψ, φ⟫_ℂ‖ ≤ ‖ψ‖ ^ 2 - g ^ 2 / 8 := by
  have hcs : ‖⟪ψ, φ⟫_ℂ‖ ≤ ‖ψ‖ ^ 2 :=
    calc ‖⟪ψ, φ⟫_ℂ‖ ≤ ‖ψ‖ * ‖φ‖ := norm_inner_le_norm ψ φ
      _ = ‖ψ‖ ^ 2 := by rw [← hn, sq]
  have hnn : 0 ≤ 2 * ‖ψ‖ ^ 2 - 2 * ‖⟪ψ, φ⟫_ℂ‖ := by linarith
  have h2 : g ^ 2 ≤ (2 * Real.sqrt (2 * ‖ψ‖ ^ 2 - 2 * ‖⟪ψ, φ⟫_ℂ‖)) ^ 2 :=
    pow_le_pow_left₀ hg (hgap.trans (abs_re_inner_sub_le hA hn h1)) 2
  rw [mul_pow, Real.sq_sqrt hnn] at h2
  linarith

/-- **Positive-weight adversary, uniform weights** (`δ = 1`). If `Γ` is
nonnegative and symmetric, every masked `Γ ∘ Δ_i` has a Schur certificate with
constant `lam ≥ 0`, every row sum of `Γ` is at least `D`, and the final states of
`Γ`-joined inputs have overlap at most `‖φ₀‖² - κ` (`κ ≥ 0`), then
`κ D ≤ 2 lam count`. -/
theorem count_ge [Nonempty X] (P : ProjFamily K I) (y : X → I → Bool) (Γ : X → X → ℝ)
    (hΓ0 : ∀ x x', 0 ≤ Γ x x') (hΓs : ∀ x x', Γ x x' = Γ x' x)
    {lam : ℝ} (hlam : 0 ≤ lam) (hcert : ∀ i, SchurCert Γ y i lam)
    {D : ℝ} (hdeg : ∀ x, D ≤ ∑ x', Γ x x')
    (q : OracleCircuit.Program (fun x => P.phase (y x))) (φ₀ : K) (hφ₀ : ‖φ₀‖ ≤ 1)
    {κ : ℝ} (hκ : 0 ≤ κ)
    (hsep : ∀ x x', Γ x x' ≠ 0 → ‖⟪q.eval x φ₀, q.eval x' φ₀⟫_ℂ‖ ≤ ‖φ₀‖ ^ 2 - κ) :
    κ * D ≤ 2 * lam * q.count := by
  have hprog := abs_progress_program_sub_le P y Γ hΓ0 hΓs hlam hcert q (fun _ => 1)
    (fun _ => φ₀)
  simp only [one_pow, one_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hprog
  have hφ : (⟪φ₀, φ₀⟫_ℂ).re = ‖φ₀‖ ^ 2 := by
    simpa only [RCLike.re_to_complex] using inner_self_eq_norm_sq (𝕜 := ℂ) φ₀
  have hinit : progress Γ (fun _ => 1) (fun _ => φ₀) = ∑ x, ∑ x', Γ x x' * ‖φ₀‖ ^ 2 := by
    simp only [progress, mul_one, hφ]
  have hfin : progress Γ (fun _ => 1) (fun x => q.eval x φ₀) ≤
      ∑ x, ∑ x', Γ x x' * (‖φ₀‖ ^ 2 - κ) := by
    simp only [progress, mul_one]
    refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun x' _ => ?_
    by_cases hΓ : Γ x x' = 0
    · rw [hΓ, zero_mul, zero_mul]
    · exact mul_le_mul_of_nonneg_left ((Complex.re_le_norm _).trans (hsep x x' hΓ)) (hΓ0 x x')
  have hsplit : ∑ x, ∑ x', Γ x x' * ‖φ₀‖ ^ 2 - ∑ x, ∑ x', Γ x x' * (‖φ₀‖ ^ 2 - κ) =
      κ * ∑ x, ∑ x', Γ x x' := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x' _ => by ring
  have hS : (Fintype.card X : ℝ) * D ≤ ∑ x, ∑ x', Γ x x' := by
    have h := Finset.sum_le_sum fun x (_ : x ∈ Finset.univ) => hdeg x
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using h
  have hcard : (0 : ℝ) < Fintype.card X := Nat.cast_pos.mpr Fintype.card_pos
  have hc0 : 0 ≤ 2 * lam * (q.count : ℝ) :=
    mul_nonneg (mul_nonneg two_pos.le hlam) (Nat.cast_nonneg _)
  have e1 : κ * ((Fintype.card X : ℝ) * D) ≤ κ * ∑ x, ∑ x', Γ x x' :=
    mul_le_mul_of_nonneg_left hS hκ
  have e2 : 2 * lam * q.count * ((Fintype.card X : ℝ) * ‖φ₀‖ ^ 2) ≤
      2 * lam * q.count * (Fintype.card X : ℝ) := by
    have h := mul_le_mul_of_nonneg_left (pow_le_one₀ (n := 2) (norm_nonneg φ₀) hφ₀) hcard.le
    rw [mul_one] at h
    exact mul_le_mul_of_nonneg_left h hc0
  have h3 := (abs_le.mp hprog).1
  have key : (Fintype.card X : ℝ) * (κ * D) ≤ (Fintype.card X : ℝ) * (2 * lam * q.count) := by
    have e3 : (Fintype.card X : ℝ) * (κ * D) = κ * ((Fintype.card X : ℝ) * D) := by ring
    have e4 : (Fintype.card X : ℝ) * (2 * lam * q.count) =
        2 * lam * q.count * (Fintype.card X : ℝ) := by ring
    rw [e3, e4]
    linarith
  exact le_of_mul_le_mul_left key hcard

/-- **Bounded-error decision form** (Lemma `odel:lem:outer`'s use of the
spectral-adversary theorem, lines 3795-3797). If `Γ` joins only inputs with
opposite answers `ans x' = -ans x`, `|ans x| = 1`, and a contraction `A` has
signed correlation at least `β ≥ 0` with the answer on every final state, then
`(β²/2) D ≤ 2 lam count`. -/
theorem decision_count_ge [Nonempty X] (P : ProjFamily K I) (y : X → I → Bool)
    (Γ : X → X → ℝ) (hΓ0 : ∀ x x', 0 ≤ Γ x x') (hΓs : ∀ x x', Γ x x' = Γ x' x)
    {lam : ℝ} (hlam : 0 ≤ lam) (hcert : ∀ i, SchurCert Γ y i lam)
    {D : ℝ} (hdeg : ∀ x, D ≤ ∑ x', Γ x x')
    (ans : X → ℝ) (hans : ∀ x, |ans x| = 1) (hopp : ∀ x x', Γ x x' ≠ 0 → ans x' = -ans x)
    (q : OracleCircuit.Program (fun x => P.phase (y x))) (φ₀ : K) (hφ₀ : ‖φ₀‖ ≤ 1)
    (A : K →L[ℂ] K) (hA : ‖A‖ ≤ 1) {β : ℝ} (hβ : 0 ≤ β)
    (hcorr : ∀ x, β ≤ ans x * (⟪q.eval x φ₀, A (q.eval x φ₀)⟫_ℂ).re) :
    β ^ 2 / 2 * D ≤ 2 * lam * q.count := by
  have hnorm : ∀ x, ‖q.eval x φ₀‖ = ‖φ₀‖ := fun x =>
    norm_map_of_isUnitary (q.eval_unitary (fun x => P.isUnitary_phase (y x)) x) φ₀
  refine count_ge P y Γ hΓ0 hΓs hlam hcert hdeg q φ₀ hφ₀ (by positivity) ?_
  intro x x' hΓ
  obtain ⟨e, he⟩ : ∃ e : X → ℝ, ∀ z, e z = (⟪q.eval z φ₀, A (q.eval z φ₀)⟫_ℂ).re :=
    ⟨_, fun _ => rfl⟩
  have hgap : 2 * β ≤ |(⟪q.eval x φ₀, A (q.eval x φ₀)⟫_ℂ).re -
      (⟪q.eval x' φ₀, A (q.eval x' φ₀)⟫_ℂ).re| := by
    have h1 := hcorr x
    have h2 := hcorr x'
    rw [← he x] at h1
    rw [← he x'] at h2
    rw [← he x, ← he x']
    rw [hopp x x' hΓ] at h2
    calc 2 * β ≤ ans x * e x + -ans x * e x' := by linarith
      _ = ans x * (e x - e x') := by ring
      _ ≤ |ans x * (e x - e x')| := le_abs_self _
      _ = |e x - e x'| := by rw [abs_mul, hans, one_mul]
  have h := norm_inner_le_of_gap hA ((hnorm x).trans (hnorm x').symm) ((hnorm x).trans_le hφ₀)
    (mul_nonneg two_pos.le hβ) hgap
  rw [hnorm x] at h
  calc _ ≤ ‖φ₀‖ ^ 2 - (2 * β) ^ 2 / 8 := h
    _ = ‖φ₀‖ ^ 2 - β ^ 2 / 2 := by ring

end

end SparseLowerBounds.PositiveAdversary
end
