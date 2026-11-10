import ChebyshevFilter.Augmented

set_option autoImplicit false

/-!
# Probability tests and the final projection with the Chebyshev filter

The manuscript uses the filter of Proposition `qls:prop:chebyshev` with `δ = 1/100` for the
probability tests on `J|e⟩` and with a precision-dependent `δ` for the final projection
(text after equation `qls:eq:filterprobability`). The released files prove the two
corresponding facts for the averaging filter (`Facts.test_fact`, `Facts.final_fact`); here
they are proved for the Chebyshev filter of degree `d_σ(δ)` (`augDegree`), with the same
statements otherwise:

* `augmented_test_fact`: at `δ = 1/100`, the filtered test probability
  `‖F(W_{σ,r}) J e‖²` lies in `[1/(2(1+q²)), 1/(1+q²) + 10⁻⁴]`, with `q = r_σ / r`;
* `augmented_final_fact`: at `σ = 0` and `g = 1/κ`, the decoded filtered amplitude is
  within `δ` of `c A⁻¹ b`, where `1/(r (1+μ)(1+q²)) ≤ c ≤ 1/(r (1+q²))`.

Notation: the regularization parameter is `σ` here and `ξ` in the manuscript, so a subscript `σ` (as
in `g_σ`, `r_σ`, `H_{σ,r}`) stands for the manuscript's subscript `ξ`.
-/

namespace ChebyshevFilter

noncomputable section
open SparseHamiltonian SparseLinearSystems SparseLinearSystems.Facts
open ContinuousLinearMap OracleCircuit HilbertAugmentation Augmented SparseBranch LogicalWalk
open scoped InnerProduct

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s : ℕ}

local notation "V0" => EuclideanSpace ℂ n

/-- **Test probabilities with the Chebyshev filter** (equations `qls:eq:probability`,
`qls:eq:filterprobability` at `δ = 1/100`). -/
theorem augmented_test_fact (D : NativeSparseBlockEncoding.Data X n Z s) (x : X)
    (hA1 : ‖Aop D x‖ ≤ 1) (κ : ℝ) (hκ : 1 ≤ κ) (hlow : ∀ v, ‖v‖ ≤ κ * ‖Aop D x v‖)
    (Ub : X → V0 →L[ℂ] V0) (sv : V0) (hb : ‖Ub x sv‖ ≤ 1) (σ : ℝ) (hσ₀ : 0 ≤ σ) (hσ₁ : σ ≤ 1)
    (r : ℝ) (hr : 1 / 8 ≤ r) (g : ℝ) (hg0 : 0 < g) (hg : g ≤ RegularizationGap.gap κ σ) :
    1 / (2 * (1 + (rSigma (equivOfLower (Aop D x) κ hlow) κ σ hκ
        (equivOfLower_symm_norm _ κ (by linarith) hlow) hσ₀ hσ₁ (betaOf (Ub x sv)) / r) ^ 2)) ≤
        ‖filterOp (WwO D Ub sv σ r x) (bLow (s : ℝ) g) (augDegree (s : ℝ) g (1 / 100))
          ((JwO D).toContinuousLinearMap eVec)‖ ^ 2 ∧
      ‖filterOp (WwO D Ub sv σ r x) (bLow (s : ℝ) g) (augDegree (s : ℝ) g (1 / 100))
          ((JwO D).toContinuousLinearMap eVec)‖ ^ 2 ≤
        1 / (1 + (rSigma (equivOfLower (Aop D x) κ hlow) κ σ hκ
          (equivOfLower_symm_norm _ κ (by linarith) hlow) hσ₀ hσ₁ (betaOf (Ub x sv)) / r) ^ 2) +
          1 / 10000 := by
  have hs : (0 : ℝ) < s := by exact_mod_cast D.slots_pos
  have hbpos := bLow_pos (s : ℝ) g hs hg0
  have hf := filterOp_probability_bounds (WwO_unitaryF D Ub sv σ r x) hbpos (bLow_lt_one _ _)
    (gapO D x hA1 κ hκ hlow Ub sv hb σ hσ₀ hσ₁ r hr g hg0 hg) (δ := 1 / 100) (by norm_num)
    (by norm_num) ((JwO D).toContinuousLinearMap eVec)
  rw [← augDegree_eq, norm_JwO_eVec, mul_one] at hf
  obtain ⟨hk0, hker⟩ := kernel_data D x κ hκ hlow Ub sv σ hσ₀ hσ₁ r
  have hsb := (hypO D x hA1 Ub sv hb σ hσ₀ hσ₁ r hr).seed_bounds _ eVec hk0 hker
    (kerVec_ne_zero _ κ hκ (equivOfLower_symm_norm _ κ (by linarith) hlow) σ hσ₀ hσ₁ r (Ub x sv))
    (kerVec_inner_eVec _ κ hκ (equivOfLower_symm_norm _ κ (by linarith) hlow) σ hσ₀ hσ₁ r
      (Ub x sv))
  have hn := kerVec_norm_sq (equivOfLower (Aop D x) κ hlow) κ hκ
    (equivOfLower_symm_norm _ κ (by linarith) hlow) σ hσ₀ hσ₁ r (Ub x sv)
  rw [hn, ← WwO_eq D x hA1 Ub sv hb σ hσ₀ hσ₁ r hr] at hsb
  set q := rSigma (equivOfLower (Aop D x) κ hlow) κ σ hκ
    (equivOfLower_symm_norm _ κ (by linarith) hlow) hσ₀ hσ₁ (betaOf (Ub x sv)) / r
  have hq := sq_nonneg q
  obtain ⟨hlo, hhi⟩ := hsb
  constructor
  · refine le_trans ?_ (hlo.trans hf.1)
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  · have h2 : ((1 : ℝ) / 100) ^ 2 = 1 / 10000 := by norm_num
    linarith [hf.2]

/-- **The final amplitude with the Chebyshev filter** (equation `qls:eq:finalprob` with filter
error `δ`), at `σ = 0` with the public gap `g = 1/κ`. -/
theorem augmented_final_fact (D : NativeSparseBlockEncoding.Data X n Z s) (x : X)
    (hA1 : ‖Aop D x‖ ≤ 1) (κ : ℝ) (hκ : 1 ≤ κ) (hlow : ∀ v, ‖v‖ ≤ κ * ‖Aop D x v‖)
    (Ub : X → V0 →L[ℂ] V0) (sv : V0) (hb : ‖Ub x sv‖ ≤ 1) (r : ℝ) (hr : 1 / 8 ≤ r) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ c : ℝ, 1 / (r * ((1 + 66 / 256) *
        (1 + (‖(equivOfLower (Aop D x) κ hlow).symm (Ub x sv)‖ / r) ^ 2))) ≤ c ∧
      c ≤ 1 / (r * (1 + (‖(equivOfLower (Aop D x) κ hlow).symm (Ub x sv)‖ / r) ^ 2)) ∧
      ‖(solEmb†) (((JwO D).toContinuousLinearMap†)
          (filterOp (WwO D Ub sv 0 r x) (bLow (s : ℝ) (1 / κ)) (augDegree (s : ℝ) (1 / κ) δ)
            ((JwO D).toContinuousLinearMap eVec))) -
        (c : ℂ) • (equivOfLower (Aop D x) κ hlow).symm (Ub x sv)‖ ≤ δ := by
  have h0 : (0 : ℝ) ≤ 0 := le_rfl
  have h1 : (0 : ℝ) ≤ 1 := zero_le_one
  have hκ0 : 0 < κ := by linarith
  have hs : (0 : ℝ) < s := by exact_mod_cast D.slots_pos
  have hr0 : 0 < r := by linarith
  obtain ⟨hk0, hker⟩ := kernel_data D x κ hκ hlow Ub sv 0 h0 h1 r
  obtain ⟨a, ha0, ha1, -, hamp⟩ := (hypO D x hA1 Ub sv hb 0 h0 h1 r hr).seed_facts _ eVec hk0
    hker
    (kerVec_ne_zero _ κ hκ (equivOfLower_symm_norm _ κ (by linarith) hlow) 0 h0 h1 r (Ub x sv))
    (kerVec_inner_eVec _ κ hκ (equivOfLower_symm_norm _ κ (by linarith) hlow) 0 h0 h1 r
      (Ub x sv))
  rw [← WwO_eq D x hA1 Ub sv hb 0 h0 h1 r hr] at hamp
  have hn := kerVec_norm_sq (equivOfLower (Aop D x) κ hlow) κ hκ
    (equivOfLower_symm_norm _ κ (by linarith) hlow) 0 h0 h1 r (Ub x sv)
  rw [rSigma_zero] at hn
  have hsol := solEmb_kerVec (equivOfLower (Aop D x) κ hlow) κ hκ
    (equivOfLower_symm_norm _ κ (by linarith) hlow) h0 h1 r (Ub x sv)
  generalize ‖kerVec (equivOfLower (Aop D x) κ hlow) κ hκ
    (equivOfLower_symm_norm _ κ (by linarith) hlow) 0 h0 h1 r (Ub x sv)‖ ^ 2 = m at hn ha1 hamp
  subst hn
  set q := ‖(equivOfLower (Aop D x) κ hlow).symm (Ub x sv)‖ / r with hq
  refine ⟨1 / (r * (1 + q ^ 2 + a)), ?_, ?_, ?_⟩
  · apply one_div_le_one_div_of_le (by positivity)
    apply mul_le_mul_of_nonneg_left _ hr0.le
    nlinarith [sq_nonneg q]
  · apply one_div_le_one_div_of_le (by positivity)
    apply mul_le_mul_of_nonneg_left _ hr0.le
    linarith
  · have hideal : (solEmb†) (((JwO D).toContinuousLinearMap†)
        (UnitaryFilter.fixedProj (WwO D Ub sv 0 r x) ((JwO D).toContinuousLinearMap eVec))) =
        (((1 / (r * (1 + q ^ 2 + a)) : ℝ) : ℂ)) •
          (equivOfLower (Aop D x) κ hlow).symm (Ub x sv) := by
      rw [hamp, map_smul, hsol, smul_smul]
      congr 1
      push_cast
      field_simp
    rw [← hideal, ← map_sub, ← map_sub]
    refine (adjoint_norm_le _ solEmb_isometry _).trans ?_
    refine (adjoint_norm_le _ (hypO D x hA1 Ub sv hb 0 h0 h1 r hr).isometry _).trans ?_
    have hgap := gapO D x hA1 κ hκ hlow Ub sv hb 0 h0 h1 r hr (1 / κ) (by positivity)
      (RegularizationGap.reciprocal_le_gap κ 0 hκ h0 h1)
    have hbpos := bLow_pos (s : ℝ) (1 / κ) hs (by positivity)
    have hf := norm_filterOp_sub_apply_le (WwO_unitaryF D Ub sv 0 r x) hbpos.le
      (bLow_lt_one _ _) hgap (augDegree (s : ℝ) (1 / κ) δ) ((JwO D).toContinuousLinearMap eVec)
    rw [norm_JwO_eVec, mul_one, sub_apply] at hf
    refine hf.trans ?_
    rw [augDegree_eq]
    exact inv_filterNorm_chebDegree_le hbpos (bLow_lt_one _ _) hδ0 hδ1.le

end

end ChebyshevFilter
