import SparseLinearSystems.Augmented.Operators

/-!
# The four-branch augmented walk (equations `qls:eq:composition`–`qls:eq:augsine`)

Given branch-zero data `(J₀, K₀)` with `J₀† K₀ J₀ = H₀/√s`,
`J₀† K₀² J₀ ≤ I` and `‖K₀‖ ≤ √s` (the conclusion of Lemma `qls:lem:entry` for
the sparse lift `H₀`), the four-branch construction

`J u = ½ (J₀ u ⊕ u ⊕ u ⊕ u)`,
`K = (a/8) K₀ ⊕ (σ/(8√s)) T₁ ⊕ (1/(8 r √s)) T₂ ⊕ 0`

satisfies the hypotheses of Lemma `qls:lem:walk` with `α = 32√s`,
`μ = 66/256` and `k₀ = √s`, for every norm guess `r ≥ 1/8`
(`augmented_hyp`).  The physical layout has no unused padding, so the padding
branch of the manuscript is the zero operator.  With the nonzero-eigenvalue gap
`g_σ` of `H_{σ,r}`, the walk satisfies the chord bound with
`χ_σ = 4 g_σ /(165 √s)` (`augmented_chord_gap`), i.e. equation `qls:eq:augsine`.

Notation: the regularization parameter is `σ` here and `ξ` in the manuscript, so a subscript `σ` (as
in `g_σ`, `r_σ`, `H_{σ,r}`) stands for the manuscript's subscript `ξ`.
-/

namespace SparseLinearSystems.Augmented

noncomputable section
open ContinuousLinearMap HilbertBlocks HilbertRegularization HilbertAugmentation
  FourBranchCompression
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 2048
open scoped InnerProduct ComplexConjugate

variable {V₀ : Type*} [NormedAddCommGroup V₀] [InnerProductSpace ℂ V₀] [FiniteDimensional ℂ V₀] [CompleteSpace V₀]
variable {P₀ : Type*} [NormedAddCommGroup P₀] [InnerProductSpace ℂ P₀] [FiniteDimensional ℂ P₀] [CompleteSpace P₀]

/-- Branch-zero properties: the conclusion of Lemma `qls:lem:entry` for `H₀`. -/
structure BranchProps (A : V₀ →L[ℂ] V₀) (s : ℝ) (J₀ : Pub V₀ →ₗᵢ[ℂ] P₀) (K₀ : P₀ →L[ℂ] P₀) :
    Prop where
  selfAdjoint : (K₀†) = K₀
  compression : (J₀.toContinuousLinearMap†) ∘L K₀ ∘L J₀.toContinuousLinearMap =
    ((Real.sqrt s : ℝ) : ℂ)⁻¹ • H0 A
  moment : ∀ u : Pub V₀, ‖K₀ (J₀ u)‖ ^ 2 ≤ ‖u‖ ^ 2
  bound : ∀ v : P₀, ‖K₀ v‖ ≤ Real.sqrt s * ‖v‖

/-- The private space of the four-branch walk. -/
abbrev Private (V₀ P₀ : Type*) := FourSpace P₀ (Pub V₀) (Pub V₀) (Pub V₀)

variable {A : V₀ →L[ℂ] V₀} {s : ℝ}

/-- `J u = ½ (J₀ u ⊕ u ⊕ u ⊕ u)`. -/
def walkJ (J₀ : Pub V₀ →ₗᵢ[ℂ] P₀) : Pub V₀ →ₗᵢ[ℂ] Private V₀ P₀ :=
  embedding J₀ (LinearIsometry.id) (LinearIsometry.id) (LinearIsometry.id)

/-- Branch weights. -/
def w0 (σ : ℝ) : ℝ := Real.sqrt (1 - σ ^ 2) / 8
def w1 (s σ : ℝ) : ℝ := σ / (8 * Real.sqrt s)
def w2 (s c : ℝ) : ℝ := c / (8 * Real.sqrt s)

/-- `K = (a/8) K₀ ⊕ (σ/(8√s)) T₁ ⊕ (c/(8√s)) T₂ ⊕ 0`, with `c = 1/r`. -/
def walkK (s : ℝ) (K₀ : P₀ →L[ℂ] P₀) (σ c : ℝ) (β : Sys V₀) :
    Private V₀ P₀ →L[ℂ] Private V₀ P₀ :=
  diagonal ((w0 σ : ℂ) • K₀) ((w1 s σ : ℂ) • T1) ((w2 s c : ℂ) • T2 β) 0

theorem real_smul_selfAdjoint {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (t : ℝ) (T : E →L[ℂ] E) (hT : (T†) = T) :
    (((t : ℂ) • T)†) = (t : ℂ) • T := by
  rw [map_smulₛₗ, hT, Complex.conj_ofReal]

omit [FiniteDimensional ℂ V₀] [FiniteDimensional ℂ P₀] in
theorem walkK_selfAdjoint (K₀ : P₀ →L[ℂ] P₀) (hK₀ : (K₀†) = K₀) (σ c : ℝ) (β : Sys V₀) :
    ((walkK s K₀ σ c β)†) = walkK s K₀ σ c β :=
  diagonal_selfadjoint _ _ _ _
    (real_smul_selfAdjoint _ _ hK₀)
    (real_smul_selfAdjoint _ _ T1_selfAdjoint)
    (real_smul_selfAdjoint _ _ (T2_selfAdjoint β))
    (by rw [map_zero])

theorem adjoint_id' {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] :
    ((LinearIsometry.id : E →ₗᵢ[ℂ] E).toContinuousLinearMap†) = 1 := by
  change ((ContinuousLinearMap.id ℂ E)†) = 1
  rw [ContinuousLinearMap.adjoint_id]; rfl

omit [FiniteDimensional ℂ V₀] in
theorem branchCompression_id (T : Pub V₀ →L[ℂ] Pub V₀) :
    branchCompression (LinearIsometry.id : Pub V₀ →ₗᵢ[ℂ] Pub V₀) T = T := by
  ext v
  simp only [branchCompression, comp_apply, adjoint_id', one_apply_eq_self,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometry.id_apply]

omit [FiniteDimensional ℂ P₀] [FiniteDimensional ℂ V₀] in
/-- First-moment compression `J† K J = H_{σ,r}/(32√s)`. -/
theorem walk_compression {J₀ : Pub V₀ →ₗᵢ[ℂ] P₀} {K₀ : P₀ →L[ℂ] P₀}
    (Sb : BranchProps A s J₀ K₀) (σ c : ℝ) (β : Sys V₀) :
    ((walkJ J₀).toContinuousLinearMap†) ∘L walkK s K₀ σ c β ∘L (walkJ J₀).toContinuousLinearMap =
      ((32 * Real.sqrt s : ℝ) : ℂ)⁻¹ •
        (((Real.sqrt (1 - σ ^ 2) : ℝ) : ℂ) • H0 A + (σ : ℂ) • T1 + (c : ℂ) • T2 β) := by
  have hb0 : branchCompression J₀ ((w0 σ : ℂ) • K₀) =
      ((w0 σ : ℂ) * ((Real.sqrt s : ℝ) : ℂ)⁻¹) • H0 A := by
    rw [branchCompression, smul_comp, comp_smul, Sb.compression, smul_smul]
  rw [walkJ, walkK, compression, compressed, hb0, branchCompression_id, branchCompression_id,
    branchCompression_id]
  simp only [w0, w1, w2]
  push_cast
  module

/-- Every branch generator has norm at most `√s`. -/
theorem diagonal_bound {Q₀ Q₁ Q₂ Q₃ : Type*}
    [NormedAddCommGroup Q₀] [InnerProductSpace ℂ Q₀] [NormedAddCommGroup Q₁]
    [InnerProductSpace ℂ Q₁] [NormedAddCommGroup Q₂] [InnerProductSpace ℂ Q₂]
    [NormedAddCommGroup Q₃] [InnerProductSpace ℂ Q₃]
    (K₀ : Q₀ →L[ℂ] Q₀) (K₁ : Q₁ →L[ℂ] Q₁) (K₂ : Q₂ →L[ℂ] Q₂) (K₃ : Q₃ →L[ℂ] Q₃)
    (k : ℝ) (hk : 0 ≤ k)
    (h₀ : ∀ v, ‖K₀ v‖ ≤ k * ‖v‖) (h₁ : ∀ v, ‖K₁ v‖ ≤ k * ‖v‖)
    (h₂ : ∀ v, ‖K₂ v‖ ≤ k * ‖v‖) (h₃ : ∀ v, ‖K₃ v‖ ≤ k * ‖v‖)
    (v : FourSpace Q₀ Q₁ Q₂ Q₃) : ‖diagonal K₀ K₁ K₂ K₃ v‖ ≤ k * ‖v‖ := by
  apply le_of_pow_le_pow_left₀ two_ne_zero (by positivity)
  rw [diagonal_apply]
  simp only [WithLp.prod_norm_sq_eq_of_L2, WithLp.toLp_fst, WithLp.toLp_snd, mul_pow]
  have e0 := pow_le_pow_left₀ (norm_nonneg _) (h₀ v.fst) 2
  have e1 := pow_le_pow_left₀ (norm_nonneg _) (h₁ v.snd.fst) 2
  have e2 := pow_le_pow_left₀ (norm_nonneg _) (h₂ v.snd.snd.fst) 2
  have e3 := pow_le_pow_left₀ (norm_nonneg _) (h₃ v.snd.snd.snd) 2
  rw [mul_pow] at e0 e1 e2 e3
  nlinarith

omit [FiniteDimensional ℂ P₀] [FiniteDimensional ℂ V₀] in
/-- **Hypotheses of the walk lemma for the augmented system.** -/
theorem augmented_hyp {J₀ : Pub V₀ →ₗᵢ[ℂ] P₀} {K₀ : P₀ →L[ℂ] P₀}
    (Sb : BranchProps A s J₀ K₀) (hs : 1 ≤ s) (σ : ℝ) (hσ₀ : 0 ≤ σ)
    (hσ₁ : σ ≤ 1) (r : ℝ) (hr : (1 : ℝ) / 8 ≤ r) (β : Sys V₀) (hβ : ‖β‖ ≤ 1) :
    WalkGap.Hyp (walkJ J₀).toContinuousLinearMap (walkK s K₀ σ (1 / r) β)
      (((Real.sqrt (1 - σ ^ 2) : ℝ) : ℂ) • H0 A + (σ : ℂ) • T1 + ((1 / r : ℝ) : ℂ) • T2 β)
      (32 * Real.sqrt s) (66 / 256) (Real.sqrt s) := by
  have hs0 : 0 < s := by linarith
  have hsq : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs0
  have hsq1 : 1 ≤ Real.sqrt s := by rw [Real.one_le_sqrt]; exact hs
  have hr0 : 0 < r := by linarith
  have hσw : 0 ≤ 1 - σ ^ 2 := by nlinarith
  have ha1 : Real.sqrt (1 - σ ^ 2) ≤ 1 := by
    rw [Real.sqrt_le_one]; linarith [sq_nonneg σ]
  have ha0 : 0 ≤ Real.sqrt (1 - σ ^ 2) := Real.sqrt_nonneg _
  refine
    { isometry := LinearIsometry.adjoint_comp_self _
      selfAdjoint := walkK_selfAdjoint K₀ Sb.selfAdjoint σ (1 / r) β
      alpha_pos := by positivity
      compression := ?_
      moment := ?_
      mu_nonneg := by norm_num
      bound := ?_
      k0_nonneg := hsq.le }
  · rw [walk_compression Sb]
  · intro u
    have h0 : ‖((w0 σ : ℂ) • K₀) (J₀ u)‖ ^ 2 ≤
        (Real.sqrt (1 - σ ^ 2) ^ 2 / 64) * ‖u‖ ^ 2 := by
      rw [smul_apply, norm_real_smul_sq, w0]
      have := Sb.moment u
      have hw : (Real.sqrt (1 - σ ^ 2) / 8) ^ 2 = Real.sqrt (1 - σ ^ 2) ^ 2 / 64 := by ring
      rw [hw]
      exact mul_le_mul_of_nonneg_left this (by positivity)
    have h1 : ‖((w1 s σ : ℂ) • T1) ((LinearIsometry.id : Pub V₀ →ₗᵢ[ℂ] Pub V₀) u)‖ ^ 2 ≤
        (σ ^ 2 / (64 * s)) * ‖u‖ ^ 2 := by
      rw [smul_apply, norm_real_smul_sq, w1]
      have hn := pow_le_pow_left₀ (norm_nonneg _) (T1_norm_le (V₀ := V₀) u) 2
      have hw : (σ / (8 * Real.sqrt s)) ^ 2 = σ ^ 2 / (64 * s) := by
        rw [div_pow, mul_pow, Real.sq_sqrt hs0.le]; ring
      rw [hw]
      exact mul_le_mul_of_nonneg_left hn (by positivity)
    have h2 : ‖((w2 s (1 / r) : ℂ) • T2 β) ((LinearIsometry.id : Pub V₀ →ₗᵢ[ℂ] Pub V₀) u)‖ ^ 2 ≤
        ((1 / r ^ 2) / (64 * s)) * ‖u‖ ^ 2 := by
      rw [smul_apply, norm_real_smul_sq, w2]
      have hn := pow_le_pow_left₀ (norm_nonneg _) (T2_norm_le β hβ u) 2
      have hw : (1 / r / (8 * Real.sqrt s)) ^ 2 = (1 / r ^ 2) / (64 * s) := by
        rw [div_pow, div_pow, mul_pow, Real.sq_sqrt hs0.le]; ring
      rw [hw]
      exact mul_le_mul_of_nonneg_left hn (by positivity)
    have h3 : ‖(0 : Pub V₀ →L[ℂ] Pub V₀) ((LinearIsometry.id : Pub V₀ →ₗᵢ[ℂ] Pub V₀) u)‖ ^ 2 ≤
        (1 / (64 * s)) * ‖u‖ ^ 2 := by
      have h0' : (0 : ℝ) ≤ (1 / (64 * s)) * ‖u‖ ^ 2 := by positivity
      simpa using h0'
    have hcomb := diagonal_embedding_norm_sq_le J₀ LinearIsometry.id LinearIsometry.id
      LinearIsometry.id _ _ _ _ _ _ _ _ u h0 h1 h2 h3
    have hcoef : ((Real.sqrt (1 - σ ^ 2) ^ 2 / 64 + σ ^ 2 / (64 * s) +
        (1 / r ^ 2) / (64 * s) + 1 / (64 * s)) / 4) =
        (s * (1 - σ ^ 2) + σ ^ 2 + 1 / r ^ 2 + 1) / (256 * s) := by
      rw [Real.sq_sqrt hσw]; field_simp; ring
    rw [hcoef] at hcomb
    have hscalar := AugmentedMoments.four_branch_moment_le s σ r hs hr
    rw [LinearIsometry.coe_toContinuousLinearMap, walkK, walkJ]
    have hfin := mul_le_mul_of_nonneg_right hscalar (sq_nonneg ‖u‖)
    refine le_trans ?_ hfin
    convert hcomb using 3
  · intro v
    apply diagonal_bound _ _ _ _ (Real.sqrt s) hsq.le
    · intro w
      rw [smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs, w0,
        abs_of_nonneg (by positivity)]
      have := Sb.bound w
      calc Real.sqrt (1 - σ ^ 2) / 8 * ‖K₀ w‖ ≤ 1 * ‖K₀ w‖ := by
            apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); linarith
        _ ≤ Real.sqrt s * ‖w‖ := by rw [one_mul]; exact this
    · intro w
      rw [smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs, w1,
        abs_of_nonneg (by positivity)]
      have hn := T1_norm_le (V₀ := V₀) w
      have hc : σ / (8 * Real.sqrt s) ≤ Real.sqrt s := by
        rw [div_le_iff₀ (by positivity)]; nlinarith
      calc σ / (8 * Real.sqrt s) * ‖T1 w‖ ≤ Real.sqrt s * ‖T1 w‖ :=
            mul_le_mul_of_nonneg_right hc (norm_nonneg _)
        _ ≤ Real.sqrt s * ‖w‖ := mul_le_mul_of_nonneg_left hn hsq.le
    · intro w
      rw [smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs, w2,
        abs_of_nonneg (by positivity)]
      have hn := T2_norm_le β hβ w
      have hc8 : 1 / r ≤ 8 := by rw [div_le_iff₀ hr0]; linarith
      have hc : 1 / r / (8 * Real.sqrt s) ≤ Real.sqrt s := by
        rw [div_le_iff₀ (by positivity)]; nlinarith
      calc 1 / r / (8 * Real.sqrt s) * ‖T2 β w‖ ≤ Real.sqrt s * ‖T2 β w‖ :=
            mul_le_mul_of_nonneg_right hc (norm_nonneg _)
        _ ≤ Real.sqrt s * ‖w‖ := mul_le_mul_of_nonneg_left hn hsq.le
    · intro w
      simp only [zero_apply, norm_zero]; positivity

/-! ### The walk gap for the augmented system -/

/-- The public gap lower bound `χ(g) = 4 g / (165 √s)` of equation `qls:eq:augtangent`. -/
def chi (s g : ℝ) : ℝ := 4 * g / (165 * Real.sqrt s)

/-- `b(g) = χ / √(1 + χ²)` of equation `qls:eq:augsine`. -/
def bLow (s g : ℝ) : ℝ := chi s g / Real.sqrt (1 + chi s g ^ 2)

theorem tStar_augmented (s g : ℝ) (hs : 0 < s) :
    WalkGap.tStar (32 * Real.sqrt s) (66 / 256) (Real.sqrt s) g =
      4 * g / ((161 + 4 * g) * Real.sqrt s) := by
  have hsq : Real.sqrt s ≠ 0 := (Real.sqrt_pos.mpr hs).ne'
  unfold WalkGap.tStar
  have e1 : Real.sqrt s * (g / (32 * Real.sqrt s)) = g / 32 := by field_simp
  have e2 : 32 * Real.sqrt s * (1 + 66 / 256 + g / 32) = ((161 + 4 * g) * Real.sqrt s) / 4 := by
    ring
  rw [e1, div_div, e2, div_div_eq_mul_div]
  ring

theorem chi_le_tStar (s g : ℝ) (hs : 0 < s) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) :
    chi s g ≤ WalkGap.tStar (32 * Real.sqrt s) (66 / 256) (Real.sqrt s) g := by
  rw [tStar_augmented s g hs, chi]
  have hsq : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  nlinarith

theorem chord_mono {t t' : ℝ} (h0 : 0 ≤ t) (h : t ≤ t') :
    2 * t / Real.sqrt (1 + t ^ 2) ≤ 2 * t' / Real.sqrt (1 + t' ^ 2) := by
  have hp : ∀ u : ℝ, 0 < Real.sqrt (1 + u ^ 2) := fun u => Real.sqrt_pos.mpr (by positivity)
  rw [div_le_div_iff₀ (hp t) (hp t')]
  have ht' : 0 ≤ t' := h0.trans h
  -- square both (nonnegative) sides
  apply le_of_pow_le_pow_left₀ two_ne_zero (by positivity)
  rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), mul_pow, mul_pow,
    Real.sq_sqrt (by positivity)]
  nlinarith [mul_le_mul h h h0 ht', sq_nonneg t, sq_nonneg t']

/-- **Equation `qls:eq:augsine`.**  Every eigenvalue `z ≠ 1` of the augmented
walk satisfies `|z - 1| ≥ 2 b(g)` for any public lower bound `g ≤ g_σ`. -/
theorem augmented_chord_gap {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [CompleteSpace E] {J : Pub V₀ →L[ℂ] E} {K : E →L[ℂ] E} {H : Pub V₀ →L[ℂ] Pub V₀}
    (h : WalkGap.Hyp J K H (32 * Real.sqrt s) (66 / 256) (Real.sqrt s)) (hs : 0 < s)
    (g Δ : ℝ) (hg0 : 0 < g) (hgΔ : g ≤ Δ) (hΔ1 : Δ ≤ 1)
    (hgap : ∀ (x : Pub V₀) (c : ℂ), x ≠ 0 → H x = c • x → c ≠ 0 → Δ ≤ ‖c‖)
    (z : ℂ) (v : E) (hv : v ≠ 0) (hWv : WalkGap.walk J h.cayley v = z • v) (hz1 : z ≠ 1) :
    2 * bLow s g ≤ ‖z - 1‖ := by
  have hΔ : 0 < Δ := lt_of_lt_of_le hg0 hgΔ
  have hc := h.chord_gap Δ hΔ hgap z v hv hWv hz1
  have hmono : WalkGap.tStar (32 * Real.sqrt s) (66 / 256) (Real.sqrt s) g ≤
      WalkGap.tStar (32 * Real.sqrt s) (66 / 256) (Real.sqrt s) Δ := by
    rw [tStar_augmented s g hs, tStar_augmented s Δ hs]
    have hsq : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos hsq hg0]
  have hchi := chi_le_tStar s g hs hg0.le (hgΔ.trans hΔ1)
  have hchi0 : 0 ≤ chi s g := by unfold chi; positivity
  calc 2 * bLow s g = 2 * chi s g / Real.sqrt (1 + chi s g ^ 2) := by rw [bLow]; ring
    _ ≤ 2 * WalkGap.tStar (32 * Real.sqrt s) (66 / 256) (Real.sqrt s) Δ /
          Real.sqrt (1 + WalkGap.tStar (32 * Real.sqrt s) (66 / 256) (Real.sqrt s) Δ ^ 2) :=
        chord_mono hchi0 (hchi.trans hmono)
    _ ≤ ‖z - 1‖ := hc

end

end SparseLinearSystems.Augmented
