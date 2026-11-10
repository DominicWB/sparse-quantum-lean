import SparseLowerBounds.Query.PositiveAdversary

set_option autoImplicit false

/-!
# Unstructured search at constant error

The lower-bound part of corollary `hs:cor:unitary` of the manuscript reduces to the `Ω(√N)` bound
for unstructured search with one marked element of `Fin N`. The package's search lemma
`hsl:lem:search` is a multiplicative-adversary bound for the search-parity correlation; the
constant-error search bound used here is derived from the bounded-error positive-weight adversary
`SparseLowerBounds.PositiveAdversary.count_ge`.

The oracle is a Boolean phase oracle `P.phase (markedString c m)` of an
arbitrary projection family `P` on an arbitrary Hilbert workspace, whose
positions `i` are marked exactly when `c i = m` (plain search is `c = id`).
Every query position therefore depends on the hidden `m` only through one
equality test, as in the entry oracle of the manuscript's search family. Fixed
gates are free and inverse queries are counted.

With `Γ m m' = 1` for `m ≠ m'`, every masked matrix `Γ ∘ Δ_i` is a star centred
at `c i`, with Schur constant `sqrt (N - 1)` (`schurCert`), and every row sum is
`N - 1`. If the final states of distinct instances have overlap at most
`‖φ₀‖² - κ`, then `κ sqrt (N - 1) ≤ 2 count` (`count_ge`). Unit states within
`ε ≤ 1` of orthonormal states have overlap at most `2 ε sqrt (1 - ε²/4)`
(`norm_inner_le_of_near`), which is below one for `0 ≤ ε ≤ 1/2`
(`near_factor_pos`).
-/

namespace UnitaryImplementationExtensions.Search

noncomputable section
open SparseLowerBounds SparseHamiltonian
open scoped InnerProductSpace

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {I : Type*} [Fintype I]

/-- The Boolean string of instance `m`: position `i` is marked iff `c i = m`. -/
def markedString {N : ℕ} (c : I → Fin N) (m : Fin N) : I → Bool :=
  fun i => decide (c i = m)

/-- The search adversary matrix: all pairs of distinct instances, weight one. -/
def adversary (N : ℕ) (m m' : Fin N) : ℝ :=
  if m = m' then 0 else 1

omit [Fintype I] in
/-- The masked adversary matrix at every position has Schur constant
`sqrt (N - 1)`, with weights `sqrt (N - 1)` at the centre `c i` and `1` elsewhere. -/
theorem schurCert {N : ℕ} (hN : 2 ≤ N) (c : I → Fin N) (i : I) :
    PositiveAdversary.SchurCert (adversary N) (markedString c) i
      (Real.sqrt ((N : ℝ) - 1)) := by
  classical
  have hN1 : (1 : ℝ) ≤ (N : ℝ) - 1 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hs : 0 < Real.sqrt ((N : ℝ) - 1) := Real.sqrt_pos.mpr (by linarith)
  refine ⟨fun m => if m = c i then Real.sqrt ((N : ℝ) - 1) else 1,
    fun m => by dsimp only; split_ifs <;> [exact hs; exact one_pos], fun m => ?_⟩
  dsimp only
  by_cases hm : m = c i
  · subst hm
    have hterm : ∀ m', PositiveAdversary.masked (adversary N) (markedString c) i (c i) m' *
        (if m' = c i then Real.sqrt ((N : ℝ) - 1) else 1) = if m' = c i then 0 else 1 := by
      intro m'
      by_cases h : m' = c i
      · simp [PositiveAdversary.masked, h]
      · simp [PositiveAdversary.masked, markedString, adversary, h, Ne.symm h]
    rw [Finset.sum_congr rfl fun m' _ => hterm m', Finset.sum_ite, Finset.sum_const_zero,
      zero_add, Finset.sum_const, nsmul_eq_mul, mul_one, Finset.filter_ne' Finset.univ (c i),
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin,
      if_pos rfl, Real.mul_self_sqrt (by linarith), Nat.cast_sub (by omega), Nat.cast_one]
  · have hterm : ∀ m', PositiveAdversary.masked (adversary N) (markedString c) i m m' *
        (if m' = c i then Real.sqrt ((N : ℝ) - 1) else 1) =
          if m' = c i then Real.sqrt ((N : ℝ) - 1) else 0 := by
      intro m'
      by_cases h : m' = c i
      · subst h
        simp [PositiveAdversary.masked, markedString, adversary, hm, Ne.symm hm]
      · simp [PositiveAdversary.masked, markedString, h, Ne.symm hm, Ne.symm h]
    rw [Finset.sum_congr rfl fun m' _ => hterm m', Finset.sum_ite_eq' Finset.univ (c i),
      if_pos (Finset.mem_univ _), if_neg hm, mul_one]

/-- **Search lower bound, overlap form.** For an oracle family that is the
phase oracle of the marked strings, a program whose final states on distinct
instances have overlap at most `‖φ₀‖² - κ` makes at least
`κ sqrt (N - 1) / 2` queries. -/
theorem count_ge {N : ℕ} (hN : 2 ≤ N) (P : ProjFamily K I) (c : I → Fin N)
    {O : Fin N → K →L[ℂ] K} (hO : ∀ m, O m = P.phase (markedString c m))
    (q : OracleCircuit.Program O) (φ₀ : K) (hφ₀ : ‖φ₀‖ ≤ 1) {κ : ℝ} (hκ : 0 ≤ κ)
    (hsep : ∀ m m', m ≠ m' → ‖⟪q.eval m φ₀, q.eval m' φ₀⟫_ℂ‖ ≤ ‖φ₀‖ ^ 2 - κ) :
    κ * Real.sqrt ((N : ℝ) - 1) ≤ 2 * q.count := by
  classical
  obtain rfl : O = fun m => P.phase (markedString c m) := funext hO
  haveI : Nonempty (Fin N) := ⟨⟨0, by omega⟩⟩
  have hN1 : (1 : ℝ) ≤ (N : ℝ) - 1 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hs : 0 < Real.sqrt ((N : ℝ) - 1) := Real.sqrt_pos.mpr (by linarith)
  have hdeg : ∀ m, (N : ℝ) - 1 ≤ ∑ m', adversary N m m' := by
    intro m
    have hterm : ∀ m', adversary N m m' = if m' = m then 0 else 1 := by
      intro m'
      by_cases h : m' = m
      · simp [adversary, h]
      · simp [adversary, h, Ne.symm h]
    rw [Finset.sum_congr rfl fun m' _ => hterm m', Finset.sum_ite, Finset.sum_const_zero,
      zero_add, Finset.sum_const, nsmul_eq_mul, mul_one, Finset.filter_ne' Finset.univ m,
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin,
      Nat.cast_sub (by omega), Nat.cast_one]
  have h := PositiveAdversary.count_ge P (markedString c) (adversary N)
    (fun m m' => by unfold adversary; split_ifs <;> norm_num)
    (fun m m' => by
      unfold adversary
      by_cases h : m = m'
      · simp [h]
      · simp [h, Ne.symm h])
    hs.le (fun i => schurCert hN c i) hdeg q φ₀ hφ₀ hκ
    (fun m m' hΓ => hsep m m' fun e => hΓ (by simp [adversary, e]))
  have hsq : (N : ℝ) - 1 = Real.sqrt ((N : ℝ) - 1) * Real.sqrt ((N : ℝ) - 1) :=
    (Real.mul_self_sqrt (by linarith)).symm
  have key : Real.sqrt ((N : ℝ) - 1) * (κ * Real.sqrt ((N : ℝ) - 1)) ≤
      Real.sqrt ((N : ℝ) - 1) * (2 * q.count) := by
    calc Real.sqrt ((N : ℝ) - 1) * (κ * Real.sqrt ((N : ℝ) - 1)) =
          κ * (Real.sqrt ((N : ℝ) - 1) * Real.sqrt ((N : ℝ) - 1)) := by
          ring
      _ = κ * ((N : ℝ) - 1) := by rw [← hsq]
      _ ≤ 2 * Real.sqrt ((N : ℝ) - 1) * q.count := h
      _ = Real.sqrt ((N : ℝ) - 1) * (2 * q.count) := by ring
  exact le_of_mul_le_mul_left key hs

omit [CompleteSpace K] in
/-- A unit vector within `ε ≤ 1` of a unit vector `u` has component orthogonal to
`u` of norm at most `ε sqrt (1 - ε² / 4)`. -/
theorem norm_sub_proj_le {a u : K} {ε : ℝ} (haN : ‖a‖ = 1) (hu : ‖u‖ = 1)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1) (ha : ‖a - u‖ ≤ ε) :
    ‖a - ⟪u, a⟫_ℂ • u‖ ≤ ε * Real.sqrt (1 - ε ^ 2 / 4) := by
  set α := ⟪u, a⟫_ℂ with hα
  have huu : ⟪u, u⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hu]; norm_num
  have horth : ⟪α • u, a - α • u⟫_ℂ = 0 := by
    rw [inner_smul_left, inner_sub_right, inner_smul_right, huu, ← hα]
    ring
  have hpy : ‖a‖ ^ 2 = ‖α‖ ^ 2 + ‖a - α • u‖ ^ 2 := by
    have h := norm_add_sq (𝕜 := ℂ) (α • u) (a - α • u)
    rw [add_sub_cancel, horth, map_zero, mul_zero, add_zero, norm_smul, hu, mul_one] at h
    exact h
  have hre : ‖u - a‖ ^ 2 = 2 - 2 * α.re := by
    have h := norm_sub_sq (𝕜 := ℂ) u a
    rw [hu, haN, RCLike.re_to_complex, ← hα] at h
    rw [h]; ring
  rw [norm_sub_rev] at ha
  have hsq : ‖u - a‖ ^ 2 ≤ ε ^ 2 := pow_le_pow_left₀ (norm_nonneg _) ha 2
  have hr : α.re ≤ ‖α‖ := Complex.re_le_norm α
  have hr0 : 1 - ε ^ 2 / 2 ≤ α.re := by linarith
  have hr1 : 0 ≤ 1 - ε ^ 2 / 2 := by nlinarith
  have hn : (1 - ε ^ 2 / 2) ^ 2 ≤ ‖α‖ ^ 2 := pow_le_pow_left₀ hr1 (hr0.trans hr) 2
  have hA : ‖a - α • u‖ ^ 2 ≤ (ε * Real.sqrt (1 - ε ^ 2 / 4)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by nlinarith)]
    rw [haN] at hpy
    nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _)
    (mul_nonneg hε0 (Real.sqrt_nonneg _)) two_ne_zero).mp hA

/-- Pythagoras for a star projection: `‖w‖² = ‖R w‖² + ‖w - R w‖²`. -/
theorem norm_sq_proj_add {R : K →L[ℂ] K} (h : IsStarProjection R) (w : K) :
    ‖w‖ ^ 2 = ‖R w‖ ^ 2 + ‖w - R w‖ ^ 2 := by
  have hRR : R (R w) = R w := by
    show (R * R) w = R w
    rw [h.isIdempotentElem.eq]
  have horth : ⟪R w, w - R w⟫_ℂ = 0 := by
    have hs : ⟪R w, w - R w⟫_ℂ = ⟪w, R (w - R w)⟫_ℂ := h.isSelfAdjoint.isSymmetric w (w - R w)
    rw [hs]
    rw [map_sub, hRR, sub_self, inner_zero_right]
  have hpy := norm_add_sq (𝕜 := ℂ) (R w) (w - R w)
  rw [add_sub_cancel, horth, map_zero, mul_zero, add_zero] at hpy
  exact hpy

/-- A unit vector with squared weight at least `1 - δ` in the range of a star
projection `R` lies within `sqrt δ` of that range. -/
theorem norm_sub_proj_apply_le {R : K →L[ℂ] K} (h : IsStarProjection R) {w : K}
    (hw : ‖w‖ = 1) {δ : ℝ} (hs : 1 - δ ≤ ‖R w‖ ^ 2) : ‖w - R w‖ ≤ Real.sqrt δ := by
  have hpy := norm_sq_proj_add h w
  rw [hw, one_pow] at hpy
  calc ‖w - R w‖ = Real.sqrt (‖w - R w‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt δ := Real.sqrt_le_sqrt (by linarith)

omit [CompleteSpace K] in
/-- Two unit vectors within `ε ≤ 1` of orthogonal unit vectors have overlap at
most `2 ε sqrt (1 - ε² / 4)`. -/
theorem norm_inner_le_of_near {a b u v : K} {ε : ℝ} (hε : ε ≤ 1)
    (haN : ‖a‖ = 1) (hbN : ‖b‖ = 1) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (huv : ⟪u, v⟫_ℂ = 0) (ha : ‖a - u‖ ≤ ε) (hbv : ‖b - v‖ ≤ ε) :
    ‖⟪a, b⟫_ℂ‖ ≤ 2 * ε * Real.sqrt (1 - ε ^ 2 / 4) := by
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans ha
  have hA : ‖a - ⟪u, a⟫_ℂ • u‖ ≤ ε * Real.sqrt (1 - ε ^ 2 / 4) :=
    norm_sub_proj_le haN hu hε0 hε ha
  have hB : ‖b - ⟪v, b⟫_ℂ • v‖ ≤ ε * Real.sqrt (1 - ε ^ 2 / 4) :=
    norm_sub_proj_le hbN hv hε0 hε hbv
  set a' := a - ⟪u, a⟫_ℂ • u with ha'
  set β := ⟪v, b⟫_ℂ with hβ
  set b' := b - β • v with hb'
  have hav : ⟪a, v⟫_ℂ = ⟪a', v⟫_ℂ := by
    rw [ha', inner_sub_left, inner_smul_left, huv, mul_zero, sub_zero]
  have hsplit : ⟪a, b⟫_ℂ = β * ⟪a', v⟫_ℂ + ⟪a, b'⟫_ℂ := by
    have hb : b = β • v + b' := by rw [hb']; abel
    conv_lhs => rw [hb]
    rw [inner_add_right, inner_smul_right, hav]
  have hβ1 : ‖β‖ ≤ 1 := by
    calc ‖β‖ ≤ ‖v‖ * ‖b‖ := norm_inner_le_norm v b
      _ = 1 := by rw [hv, hbN, one_mul]
  have h1 : ‖β * ⟪a', v⟫_ℂ‖ ≤ ‖a'‖ := by
    rw [norm_mul]
    calc ‖β‖ * ‖⟪a', v⟫_ℂ‖ ≤ 1 * (‖a'‖ * ‖v‖) :=
          mul_le_mul hβ1 (norm_inner_le_norm a' v) (norm_nonneg _) zero_le_one
      _ = ‖a'‖ := by rw [hv, one_mul, mul_one]
  have h2 : ‖⟪a, b'⟫_ℂ‖ ≤ ‖b'‖ := by
    calc ‖⟪a, b'⟫_ℂ‖ ≤ ‖a‖ * ‖b'‖ := norm_inner_le_norm a b'
      _ = ‖b'‖ := by rw [haN, one_mul]
  rw [hsplit]
  calc ‖β * ⟪a', v⟫_ℂ + ⟪a, b'⟫_ℂ‖ ≤ ‖β * ⟪a', v⟫_ℂ‖ + ‖⟪a, b'⟫_ℂ‖ := norm_add_le _ _
    _ ≤ ‖a'‖ + ‖b'‖ := add_le_add h1 h2
    _ ≤ 2 * ε * Real.sqrt (1 - ε ^ 2 / 4) := by linarith

/-- The overlap bound of `norm_inner_le_of_near` is below one on the whole
range `0 ≤ ε ≤ 1/2`. -/
theorem near_factor_pos {ε : ℝ} (hε : 0 ≤ ε) (hεHalf : ε ≤ 1 / 2) :
    0 < 1 - 2 * ε * Real.sqrt (1 - ε ^ 2 / 4) := by
  have hε2 : ε ^ 2 ≤ 1 / 4 := by nlinarith
  have ht0 : 0 ≤ 1 - ε ^ 2 / 4 := by nlinarith
  have hx0 : 0 ≤ 2 * ε * Real.sqrt (1 - ε ^ 2 / 4) :=
    mul_nonneg (mul_nonneg zero_le_two hε) (Real.sqrt_nonneg _)
  have hsq : (2 * ε * Real.sqrt (1 - ε ^ 2 / 4)) ^ 2 < 1 := by
    rw [mul_pow, Real.sq_sqrt ht0]
    nlinarith [mul_nonneg (sub_nonneg.mpr hε2) (by nlinarith : (0 : ℝ) ≤ 15 / 4 - ε ^ 2)]
  nlinarith

/-- Two unit vectors that each lie in one of two orthogonal projections up to
squared weight `δ` have overlap at most `2 sqrt δ`. -/
theorem norm_inner_le_of_success {a b : K} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    {R₁ R₂ : K →L[ℂ] K} (h₁ : IsStarProjection R₁) (h₂ : IsStarProjection R₂)
    (h₁₂ : R₁ * R₂ = 0) {δ : ℝ} (hδ : 0 ≤ δ)
    (hsa : 1 - δ ≤ ‖R₁ a‖ ^ 2) (hsb : 1 - δ ≤ ‖R₂ b‖ ^ 2) :
    ‖⟪a, b⟫_ℂ‖ ≤ 2 * Real.sqrt δ := by
  have hR1b : R₁ b = R₁ (b - R₂ b) := by
    have h0 : R₁ (R₂ b) = 0 := by
      show (R₁ * R₂) b = 0
      rw [h₁₂]
      rfl
    rw [map_sub, h0, sub_zero]
  have hsym : ⟪R₁ a, b⟫_ℂ = ⟪a, R₁ b⟫_ℂ := h₁.isSelfAdjoint.isSymmetric a b
  have hsplit : ⟪a, b⟫_ℂ = ⟪a, R₁ (b - R₂ b)⟫_ℂ + ⟪a - R₁ a, b⟫_ℂ := by
    rw [inner_sub_left, ← hR1b, ← hsym]
    ring
  have hca : ‖a - R₁ a‖ ≤ Real.sqrt δ := norm_sub_proj_apply_le h₁ ha hsa
  have hcb : ‖b - R₂ b‖ ≤ Real.sqrt δ := norm_sub_proj_apply_le h₂ hb hsb
  have e1 : ‖⟪a, R₁ (b - R₂ b)⟫_ℂ‖ ≤ Real.sqrt δ :=
    calc ‖⟪a, R₁ (b - R₂ b)⟫_ℂ‖ ≤ ‖a‖ * ‖R₁ (b - R₂ b)‖ := norm_inner_le_norm _ _
      _ ≤ 1 * ‖b - R₂ b‖ := by
          rw [ha]; exact mul_le_mul_of_nonneg_left
            ((R₁.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _)
              (IsStarProjection.norm_le R₁ h₁))) zero_le_one
      _ ≤ Real.sqrt δ := by rw [one_mul]; exact hcb
  have e2 : ‖⟪a - R₁ a, b⟫_ℂ‖ ≤ Real.sqrt δ :=
    calc ‖⟪a - R₁ a, b⟫_ℂ‖ ≤ ‖a - R₁ a‖ * ‖b‖ := norm_inner_le_norm _ _
      _ ≤ Real.sqrt δ := by rw [hb, mul_one]; exact hca
  rw [hsplit]
  calc ‖⟪a, R₁ (b - R₂ b)⟫_ℂ + ⟪a - R₁ a, b⟫_ℂ‖ ≤
        ‖⟪a, R₁ (b - R₂ b)⟫_ℂ‖ + ‖⟪a - R₁ a, b⟫_ℂ‖ := norm_add_le _ _
    _ ≤ 2 * Real.sqrt δ := by
      have hδ0 : 0 ≤ Real.sqrt δ ^ 2 := by rw [Real.sq_sqrt hδ]; exact hδ
      linarith

/-- **Unstructured search with constant success.** If, from a unit seed, a
program ends on every instance `m` in the range of the projection `R m` with
probability at least `1 - δ` for pairwise orthogonal projections
`R`, then it makes at least `(1 - 2 sqrt δ) sqrt (N - 1) / 2` queries. The
bound is informative for `δ < 1/4`. -/
theorem search_count_ge {N : ℕ} (hN : 2 ≤ N) (P : ProjFamily K I) (c : I → Fin N)
    {O : Fin N → K →L[ℂ] K} (hO : ∀ m, O m = P.phase (markedString c m))
    (q : OracleCircuit.Program O) (φ₀ : K) (hφ₀ : ‖φ₀‖ = 1)
    (R : Fin N → K →L[ℂ] K) (hR : ∀ m, IsStarProjection (R m))
    (hRo : ∀ m m', m ≠ m' → R m * R m' = 0) {δ : ℝ} (hδ : 0 ≤ δ)
    (hsucc : ∀ m, 1 - δ ≤ ‖R m (q.eval m φ₀)‖ ^ 2) :
    (1 - 2 * Real.sqrt δ) * Real.sqrt ((N : ℝ) - 1) ≤ 2 * q.count := by
  by_cases hneg : 1 - 2 * Real.sqrt δ < 0
  · have h0 : (1 - 2 * Real.sqrt δ) * Real.sqrt ((N : ℝ) - 1) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hneg.le (Real.sqrt_nonneg _)
    exact h0.trans (by positivity)
  · replace hneg := not_lt.mp hneg
    have hunit : ∀ m, ‖q.eval m φ₀‖ = 1 := by
      intro m
      have hU : OracleCircuit.IsUnitary (q.eval m) :=
        q.eval_unitary (fun m' => by rw [hO m']; exact P.isUnitary_phase _) m
      rw [PositiveAdversary.norm_map_of_isUnitary hU, hφ₀]
    refine count_ge hN P c hO q φ₀ hφ₀.le hneg fun m m' hmm => ?_
    rw [hφ₀, one_pow]
    have h := norm_inner_le_of_success (hunit m) (hunit m') (hR m) (hR m') (hRo m m' hmm) hδ
      (hsucc m) (hsucc m')
    linarith

end
end UnitaryImplementationExtensions.Search
