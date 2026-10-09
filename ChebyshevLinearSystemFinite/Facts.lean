import ChebyshevLinearSystemFinite.Degree
import ChebyshevFilter.Facts

set_option autoImplicit false

/-!
# Test probabilities and final amplitudes at every filter degree

The released filter facts (`ChebyshevFilter.augmented_test_fact`,
`ChebyshevFilter.augmented_final_fact`) are stated at the degree `d_σ(δ)` of a target `δ`. The
finite-gate allowance uses the degree `d_σ(δ) + 1` and its residual amplitude
`δ₀ = sech(2 (d_σ(δ) + 1) artanh b)` instead (equation `qls:eq:finitedegree`). Here, for the
filter of any degree `D` at the public gap `g` (residual amplitude `resid s g D`):

* `test_fact_deg`: the filtered test probability `‖F_{b,D}(W_{σ,r}) J e‖²` lies in
  `[1/(2(1 + q²)), 1/(1 + q²) + resid²]`, `q = r_σ/r` (equations `qls:eq:probability` and
  `qls:eq:filterprobability`);
* `final_fact_deg`: for `D ≥ 1`, the decoded filtered amplitude at `σ = 0` is within `resid`
  of `c A⁻¹ b` with `1/(r (1 + μ)(1 + q²)) ≤ c ≤ 1/(r (1 + q²))` (the released
  `augmented_final_fact` at the target `δ = resid`, whose degree is `D` by
  `augDegree_resid`).
-/

namespace ChebyshevLinearSystemFinite

noncomputable section
open SparseHamiltonian SparseLinearSystems SparseLinearSystems.Facts
open ContinuousLinearMap OracleCircuit HilbertAugmentation Augmented SparseBranch LogicalWalk
  ChebyshevFilter
open scoped InnerProduct

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s : ℕ}

local notation "V0" => EuclideanSpace ℂ n

/-- **Equation `qls:eq:filterprobability` at every degree**: under the hypotheses of the
released gap theorem `Facts.gapO`, the filtered probability of the degree-`D` filter exceeds
the projected probability `p_σ(r) = ‖P_{σ,r} J e‖²` by at most `δ₀² = resid s g D ²`. -/
theorem filter_proj_deg (D : NativeSparseBlockEncoding.Data X n Z s) (x : X)
    (hA1 : ‖Aop D x‖ ≤ 1) (κ : ℝ) (hκ : 1 ≤ κ) (hlow : ∀ v, ‖v‖ ≤ κ * ‖Aop D x v‖)
    (Ub : X → V0 →L[ℂ] V0) (sv : V0) (hb : ‖Ub x sv‖ ≤ 1) (σ : ℝ) (hσ₀ : 0 ≤ σ) (hσ₁ : σ ≤ 1)
    (r : ℝ) (hr : 1 / 8 ≤ r) (g : ℝ) (hg0 : 0 < g) (hg : g ≤ RegularizationGap.gap κ σ)
    (d : ℕ) :
    ‖UnitaryFilter.fixedProj (WwO D Ub sv σ r x) ((JwO D).toContinuousLinearMap eVec)‖ ^ 2 ≤
        ‖filterOp (WwO D Ub sv σ r x) (bLow (s : ℝ) g) d
          ((JwO D).toContinuousLinearMap eVec)‖ ^ 2 ∧
      ‖filterOp (WwO D Ub sv σ r x) (bLow (s : ℝ) g) d
          ((JwO D).toContinuousLinearMap eVec)‖ ^ 2 ≤
        ‖UnitaryFilter.fixedProj (WwO D Ub sv σ r x) ((JwO D).toContinuousLinearMap eVec)‖ ^ 2 +
          resid s g d ^ 2 := by
  have hs : (0 : ℝ) < s := by exact_mod_cast D.slots_pos
  have hbpos := bLow_pos (s : ℝ) g hs hg0
  have hW := WwO_unitaryF D Ub sv σ r x
  have hgap := gapO D x hA1 κ hκ hlow Ub sv hb σ hσ₀ hσ₁ r hr g hg0 hg
  have h1 := norm_filterOp_apply_sq hW (ChebyshevLinearSystem.bLow_mem (s : ℝ) g) d
    ((JwO D).toContinuousLinearMap eVec)
  have h2 := norm_filterOp_sub_apply_le hW hbpos.le (bLow_lt_one _ _) hgap d
    ((JwO D).toContinuousLinearMap eVec)
  rw [norm_JwO_eVec, mul_one] at h2
  have h3 : ‖(filterOp (WwO D Ub sv σ r x) (bLow (s : ℝ) g) d -
      UnitaryFilter.fixedProj (WwO D Ub sv σ r x)) ((JwO D).toContinuousLinearMap eVec)‖ ^ 2 ≤
      resid s g d ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h2 2
  have h4 := sq_nonneg ‖(filterOp (WwO D Ub sv σ r x) (bLow (s : ℝ) g) d -
      UnitaryFilter.fixedProj (WwO D Ub sv σ r x)) ((JwO D).toContinuousLinearMap eVec)‖
  rw [h1]
  constructor <;> linarith

/-- **Test probabilities at every degree** (equations `qls:eq:probability`,
`qls:eq:filterprobability`): under the hypotheses of the released gap theorem `Facts.gapO`,
the test probability of the degree-`D` filter lies in `[1/(2(1+q²)), 1/(1+q²) + δ₀²]`, with
`q = r_σ/r` and the residual amplitude `δ₀ = resid s g D`. -/
theorem test_fact_deg (D : NativeSparseBlockEncoding.Data X n Z s) (x : X)
    (hA1 : ‖Aop D x‖ ≤ 1) (κ : ℝ) (hκ : 1 ≤ κ) (hlow : ∀ v, ‖v‖ ≤ κ * ‖Aop D x v‖)
    (Ub : X → V0 →L[ℂ] V0) (sv : V0) (hb : ‖Ub x sv‖ ≤ 1) (σ : ℝ) (hσ₀ : 0 ≤ σ) (hσ₁ : σ ≤ 1)
    (r : ℝ) (hr : 1 / 8 ≤ r) (g : ℝ) (hg0 : 0 < g) (hg : g ≤ RegularizationGap.gap κ σ)
    (d : ℕ) :
    1 / (2 * (1 + (rSigma (equivOfLower (Aop D x) κ hlow) κ σ hκ
        (equivOfLower_symm_norm _ κ (by linarith) hlow) hσ₀ hσ₁ (betaOf (Ub x sv)) / r) ^ 2)) ≤
        ‖filterOp (WwO D Ub sv σ r x) (bLow (s : ℝ) g) d
          ((JwO D).toContinuousLinearMap eVec)‖ ^ 2 ∧
      ‖filterOp (WwO D Ub sv σ r x) (bLow (s : ℝ) g) d
          ((JwO D).toContinuousLinearMap eVec)‖ ^ 2 ≤
        1 / (1 + (rSigma (equivOfLower (Aop D x) κ hlow) κ σ hκ
          (equivOfLower_symm_norm _ κ (by linarith) hlow) hσ₀ hσ₁ (betaOf (Ub x sv)) / r) ^ 2) +
          resid s g d ^ 2 := by
  have hs : (0 : ℝ) < s := by exact_mod_cast D.slots_pos
  have hbpos := bLow_pos (s : ℝ) g hs hg0
  have hW := WwO_unitaryF D Ub sv σ r x
  have hgap := gapO D x hA1 κ hκ hlow Ub sv hb σ hσ₀ hσ₁ r hr g hg0 hg
  have h1 := norm_filterOp_apply_sq hW (ChebyshevLinearSystem.bLow_mem (s : ℝ) g) d
    ((JwO D).toContinuousLinearMap eVec)
  have h2 := norm_filterOp_sub_apply_le hW hbpos.le (bLow_lt_one _ _) hgap d
    ((JwO D).toContinuousLinearMap eVec)
  rw [norm_JwO_eVec, mul_one] at h2
  have h3 : ‖(filterOp (WwO D Ub sv σ r x) (bLow (s : ℝ) g) d -
      UnitaryFilter.fixedProj (WwO D Ub sv σ r x)) ((JwO D).toContinuousLinearMap eVec)‖ ^ 2 ≤
      resid s g d ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h2 2
  have h4 := sq_nonneg ‖(filterOp (WwO D Ub sv σ r x) (bLow (s : ℝ) g) d -
      UnitaryFilter.fixedProj (WwO D Ub sv σ r x)) ((JwO D).toContinuousLinearMap eVec)‖
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
  rw [h1]
  constructor
  · refine le_trans ?_ (hlo.trans (by linarith))
    apply one_div_le_one_div_of_le (by positivity)
    linarith
  · linarith

/-- **The final amplitude at every degree `D ≥ 1`** (equation `qls:eq:finalprob` with the
filter error): at `σ = 0` and the public gap `1/κ`, the decoded amplitude of the degree-`D`
filter is within `δ₀ = resid s (1/κ) D` of `c A⁻¹ b`, with
`1/(r (1 + μ)(1 + q²)) ≤ c ≤ 1/(r (1 + q²))`, `μ = 66/256`, `q = ‖A⁻¹ b‖/r`. -/
theorem final_fact_deg (D : NativeSparseBlockEncoding.Data X n Z s) (x : X)
    (hA1 : ‖Aop D x‖ ≤ 1) (κ : ℝ) (hκ : 1 ≤ κ) (hlow : ∀ v, ‖v‖ ≤ κ * ‖Aop D x v‖)
    (Ub : X → V0 →L[ℂ] V0) (sv : V0) (hb : ‖Ub x sv‖ ≤ 1) (r : ℝ) (hr : 1 / 8 ≤ r) (d : ℕ)
    (hd : 0 < d) :
    ∃ c : ℝ, 1 / (r * ((1 + 66 / 256) *
        (1 + (‖(equivOfLower (Aop D x) κ hlow).symm (Ub x sv)‖ / r) ^ 2))) ≤ c ∧
      c ≤ 1 / (r * (1 + (‖(equivOfLower (Aop D x) κ hlow).symm (Ub x sv)‖ / r) ^ 2)) ∧
      ‖(solEmb†) (((JwO D).toContinuousLinearMap†)
          (filterOp (WwO D Ub sv 0 r x) (bLow (s : ℝ) (1 / κ)) d
            ((JwO D).toContinuousLinearMap eVec))) -
        (c : ℂ) • (equivOfLower (Aop D x) κ hlow).symm (Ub x sv)‖ ≤ resid s (1 / κ) d := by
  have hs : (0 : ℝ) < s := by exact_mod_cast D.slots_pos
  have hκ0 : 0 < κ := by linarith
  have h := augmented_final_fact D x hA1 κ hκ hlow Ub sv hb r hr
    (δ := resid (s : ℝ) (1 / κ) d) (resid_pos _ _ _) (resid_lt_one hs (by positivity) hd)
  rwa [augDegree_resid hs (by positivity) d] at h

end

end ChebyshevLinearSystemFinite
