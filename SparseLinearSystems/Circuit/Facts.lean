import SparseLinearSystems.Circuit.Run
import SparseLinearSystems.Augmented.Analysis

/-!
# Spectral facts for the concrete walk

For one input `x` satisfying the linear-system promise (`‖A‖ ≤ 1`,
`‖v‖ ≤ κ ‖A v‖`, unitary `U_b`, unit public seed), the concrete walk
`W_{σ,r}` of `Circuit.LogicalWalk` satisfies the hypotheses of Lemma
`qls:lem:walk` (`concrete_hyp`).  Consequently:

* `test_fact`: the filtered test probability `‖f_N(W)(J e)‖²` lies in
  `[1/(2(1+q²)), 1/(1+q²) + 10⁻⁴]` whenever `N b(g) ≥ 100` for a public
  `0 < g ≤ g_σ`, with `q = r_σ / r`;
* `final_fact`: at `σ = 0`, the decoded filtered amplitude is within `100^{-k}`
  of `c A⁻¹ b`, where `1/(r (1+μ)(1+q²)) ≤ c ≤ 1/(r (1+q²))`.

Notation: the regularization parameter is `σ` here and `ξ` in the manuscript, so a subscript `σ` (as
in `g_σ`, `r_σ`, `H_{σ,r}`) stands for the manuscript's subscript `ξ`.
-/

namespace SparseLinearSystems.Facts

noncomputable section
open SparseHamiltonian
open ContinuousLinearMap OracleCircuit HilbertAugmentation Augmented SparseBranch LogicalWalk
open scoped InnerProduct
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 2048

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s : ℕ}

local notation "V0" => EuclideanSpace ℂ n

/-! ### The input matrix as an invertible operator -/

/-- An operator with `‖v‖ ≤ κ ‖T v‖`, as a continuous linear equivalence. -/
def equivOfLower (T : V0 →L[ℂ] V0) (κ : ℝ) (h : ∀ v, ‖v‖ ≤ κ * ‖T v‖) : V0 ≃L[ℂ] V0 :=
  (LinearEquiv.ofInjectiveEndo T.toLinearMap (fun v w hvw => by
    have hv := h (v - w)
    have hT : T (v - w) = 0 := by
      rw [map_sub]
      exact sub_eq_zero.mpr hvw
    rw [hT, norm_zero, mul_zero] at hv
    exact sub_eq_zero.mp (norm_le_zero_iff.mp hv))).toContinuousLinearEquiv

omit [DecidableEq n] in
@[simp] theorem equivOfLower_apply (T : V0 →L[ℂ] V0) (κ : ℝ) (h : ∀ v, ‖v‖ ≤ κ * ‖T v‖)
    (v : V0) : equivOfLower T κ h v = T v := rfl

omit [DecidableEq n] in
theorem equivOfLower_coe (T : V0 →L[ℂ] V0) (κ : ℝ) (h : ∀ v, ‖v‖ ≤ κ * ‖T v‖) :
    (equivOfLower T κ h).toContinuousLinearMap = T := by
  ext v
  rfl

omit [DecidableEq n] in
theorem equivOfLower_symm_norm (T : V0 →L[ℂ] V0) (κ : ℝ) (hκ : 0 ≤ κ)
    (h : ∀ v, ‖v‖ ≤ κ * ‖T v‖) : ‖(equivOfLower T κ h).symm.toContinuousLinearMap‖ ≤ κ := by
  apply ContinuousLinearMap.opNorm_le_bound _ hκ
  intro y
  have hy := h ((equivOfLower T κ h).symm y)
  rw [← equivOfLower_apply T κ h, ContinuousLinearEquiv.apply_symm_apply] at hy
  exact hy

/-! ### Row and column energies from the operator norm -/

omit [DecidableEq n] in
theorem column_energy (M : Matrix n n ℂ) (hM : ‖SparseStateOverlap.matrixOperator M‖ ≤ 1)
    (j : n) : ∑ i, ‖M i j‖ ^ 2 ≤ 1 := by
  classical
  have h := (SparseStateOverlap.matrixOperator M).le_opNorm (EuclideanSpace.single j (1 : ℂ))
  rw [PiLp.norm_single, norm_one, mul_one] at h
  have h1 : ‖SparseStateOverlap.matrixOperator M (EuclideanSpace.single j (1 : ℂ))‖ ≤ 1 :=
    h.trans hM
  have h2 : ‖SparseStateOverlap.matrixOperator M (EuclideanSpace.single j (1 : ℂ))‖ ^ 2 =
      ∑ i, ‖M i j‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    apply Finset.sum_congr rfl
    intro i _
    rw [SparseStateOverlap.matrixOperator_apply]
    simp
  rw [← h2]
  nlinarith [norm_nonneg (SparseStateOverlap.matrixOperator M (EuclideanSpace.single j (1 : ℂ)))]

omit [DecidableEq n] in
theorem row_energy (M : Matrix n n ℂ) (hM : ‖SparseStateOverlap.matrixOperator M‖ ≤ 1)
    (i : n) : ∑ j, ‖M i j‖ ^ 2 ≤ 1 := by
  set R := ∑ j, ‖M i j‖ ^ 2 with hR
  let w : V0 := WithLp.toLp 2 (fun j => star (M i j))
  have hw : ‖w‖ ^ 2 = R := by
    rw [EuclideanSpace.norm_sq_eq]
    apply Finset.sum_congr rfl
    intro j _
    simp [w]
  have hAw : SparseStateOverlap.matrixOperator M w i = (R : ℂ) := by
    rw [SparseStateOverlap.matrixOperator_apply, hR]
    push_cast
    apply Finset.sum_congr rfl
    intro j _
    simp only [w]
    rw [RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  have h1 : ‖SparseStateOverlap.matrixOperator M w i‖ ≤ ‖SparseStateOverlap.matrixOperator M w‖ :=
    PiLp.norm_apply_le _ i
  have h2 : ‖SparseStateOverlap.matrixOperator M w‖ ≤ ‖w‖ :=
    ((SparseStateOverlap.matrixOperator M).le_opNorm w).trans
      ((mul_le_mul_of_nonneg_right hM (norm_nonneg _)).trans (le_of_eq (one_mul _)))
  rw [hAw, Complex.norm_real, Real.norm_eq_abs] at h1
  have hR0 : 0 ≤ R := Finset.sum_nonneg fun j _ => sq_nonneg _
  have h3 : R ≤ ‖w‖ := by
    have := h1.trans h2
    rwa [abs_of_nonneg hR0] at this
  have h4 : R ^ 2 ≤ R := by
    have := pow_le_pow_left₀ hR0 h3 2
    rwa [hw] at this
  nlinarith

/-! ### The walk-lemma hypotheses -/

/-- The input matrix as an operator. -/
abbrev Aop (D : NativeSparseBlockEncoding.Data X n Z s) (x : X) : V0 →L[ℂ] V0 :=
  SparseStateOverlap.matrixOperator (D.matrix x)

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- **Lemma `qls:lem:walk` hypotheses for the concrete walk.** -/
theorem concrete_hyp (D : NativeSparseBlockEncoding.Data X n Z s) (x : X)
    (hA1 : ‖Aop D x‖ ≤ 1) (Ub : X → V0 →L[ℂ] V0) (sv : V0) (hb : ‖Ub x sv‖ ≤ 1)
    (σ : ℝ) (hσ₀ : 0 ≤ σ) (hσ₁ : σ ≤ 1) (r : ℝ) (hr : 1 / 8 ≤ r) :
    WalkGap.Hyp (Jw D).toContinuousLinearMap (Kw D Ub sv σ r x)
      (((Real.sqrt (1 - σ ^ 2) : ℝ) : ℂ) • H0 (Aop D x) + (σ : ℂ) • T1 +
        ((1 / r : ℝ) : ℂ) • T2 (betaOf (Ub x sv)))
      (32 * Real.sqrt (s : ℝ)) (66 / 256) (Real.sqrt (s : ℝ)) := by
  have Sb := branchProps D x (row_energy (D.matrix x) hA1) (column_energy (D.matrix x) hA1)
  have hs : (1 : ℝ) ≤ s := by exact_mod_cast D.slots_pos
  have hβ : ‖betaOf (Ub x sv)‖ ≤ 1 := by rw [norm_betaOf]; exact hb
  exact augmented_hyp Sb hs σ hσ₀ hσ₁ r hr (betaOf (Ub x sv)) hβ


/-! ### Consequences -/

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
theorem Ww_unitaryF (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (sv : V0) (σ r : ℝ) (x : X) : UnitaryFilter.Unitary (Ww D Ub sv σ r x) :=
  ⟨(Ww_unitary D Ub sv σ r x).1, (Ww_unitary D Ub sv σ r x).2⟩

/-- The adjoint of an isometry is a contraction. -/
theorem adjoint_norm_le {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (T : E →L[ℂ] F) (hT : (T†) ∘L T = 1) (y : F) : ‖(T†) y‖ ≤ ‖y‖ := by
  have hTn : ‖T‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro z
    rw [one_mul, T.norm_map_iff_adjoint_comp_self.mpr hT z]
  have h1 : ‖T†‖ ≤ 1 := by rw [ContinuousLinearMap.adjoint.norm_map]; exact hTn
  calc ‖(T†) y‖ ≤ ‖T†‖ * ‖y‖ := (T†).le_opNorm y
    _ ≤ 1 * ‖y‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ = ‖y‖ := one_mul _

theorem bLow_pos (s g : ℝ) (hs : 0 < s) (hg : 0 < g) : 0 < bLow s g := by
  unfold bLow chi
  have : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have h2 : 0 < Real.sqrt (1 + (4 * g / (165 * Real.sqrt s)) ^ 2) := Real.sqrt_pos.mpr (by positivity)
  positivity

/-! ### The opaque copy -/

/-- **The walk-lemma hypotheses in the opaque copy.** -/
theorem hypO (D : NativeSparseBlockEncoding.Data X n Z s) (x : X)
    (hA1 : ‖Aop D x‖ ≤ 1) (Ub : X → V0 →L[ℂ] V0) (sv : V0) (hb : ‖Ub x sv‖ ≤ 1)
    (σ : ℝ) (hσ₀ : 0 ≤ σ) (hσ₁ : σ ≤ 1) (r : ℝ) (hr : 1 / 8 ≤ r) :
    WalkGap.Hyp (JwO D).toContinuousLinearMap (opO (Kw D Ub sv σ r x))
      (((Real.sqrt (1 - σ ^ 2) : ℝ) : ℂ) • H0 (Aop D x) + (σ : ℂ) • T1 +
        ((1 / r : ℝ) : ℂ) • T2 (betaOf (Ub x sv)))
      (32 * Real.sqrt (s : ℝ)) (66 / 256) (Real.sqrt (s : ℝ)) :=
  (concrete_hyp D x hA1 Ub sv hb σ hσ₀ hσ₁ r hr).transport toO (JwO D).toContinuousLinearMap
    (fun _ => rfl) (LinearIsometry.adjoint_comp_self _)

/-- The opaque walk is the walk of the transported hypotheses. -/
theorem WwO_eq (D : NativeSparseBlockEncoding.Data X n Z s) (x : X)
    (hA1 : ‖Aop D x‖ ≤ 1) (Ub : X → V0 →L[ℂ] V0) (sv : V0) (hb : ‖Ub x sv‖ ≤ 1)
    (σ : ℝ) (hσ₀ : 0 ≤ σ) (hσ₁ : σ ≤ 1) (r : ℝ) (hr : 1 / 8 ≤ r) :
    WwO D Ub sv σ r x = WalkGap.walk (JwO D).toContinuousLinearMap
      (hypO D x hA1 Ub sv hb σ hσ₀ hσ₁ r hr).cayley :=
  conj_walk toO (Jw D).toContinuousLinearMap (JwO D).toContinuousLinearMap (fun _ => rfl)
    (Kw D Ub sv σ r x) (Kw_selfAdjoint D Ub sv σ r x)
    (hypO D x hA1 Ub sv hb σ hσ₀ hσ₁ r hr).selfAdjoint

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
theorem WwO_unitaryF (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (sv : V0) (σ r : ℝ) (x : X) : UnitaryFilter.Unitary (WwO D Ub sv σ r x) :=
  ⟨(WwO_unitary D Ub sv σ r x).1, (WwO_unitary D Ub sv σ r x).2⟩

/-- **Equation `qls:eq:augsine`** for the opaque walk. -/
theorem gapO (D : NativeSparseBlockEncoding.Data X n Z s) (x : X) (hA1 : ‖Aop D x‖ ≤ 1)
    (κ : ℝ) (hκ : 1 ≤ κ) (hlow : ∀ v, ‖v‖ ≤ κ * ‖Aop D x v‖) (Ub : X → V0 →L[ℂ] V0) (sv : V0)
    (hb : ‖Ub x sv‖ ≤ 1) (σ : ℝ) (hσ₀ : 0 ≤ σ) (hσ₁ : σ ≤ 1) (r : ℝ) (hr : 1 / 8 ≤ r) (g : ℝ)
    (hg0 : 0 < g) (hg : g ≤ RegularizationGap.gap κ σ) :
    ∀ (z : ℂ) (v : PrivO n), v ≠ 0 → WwO D Ub sv σ r x v = z • v → z ≠ 1 →
      2 * bLow (s : ℝ) g ≤ ‖z - 1‖ := by
  intro z v hv hWv hz1
  have h := hypO D x hA1 Ub sv hb σ hσ₀ hσ₁ r hr
  have hs : (0 : ℝ) < s := by exact_mod_cast D.slots_pos
  rw [WwO_eq D x hA1 Ub sv hb σ hσ₀ hσ₁ r hr] at hWv
  refine augmented_chord_gap h hs g (RegularizationGap.gap κ σ) hg0 hg
    (RegularizationGap.gap_le_one κ σ hκ hσ₀ hσ₁) ?_ z v hv hWv hz1
  intro y c hy hHy hc
  have hHy' : branchHam (equivOfLower (Aop D x) κ hlow) σ r (Ub x sv) y = c • y := by
    rw [branchHam, equivOfLower_coe]
    exact hHy
  exact branchHam_gap (equivOfLower (Aop D x) κ hlow) κ hκ
    (equivOfLower_symm_norm _ κ (by linarith) hlow) σ hσ₀ hσ₁ r (Ub x sv) y c hy hHy' hc

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- The kernel data of `H_{σ,r}` in the form required by `Hyp.seed_facts`. -/
theorem kernel_data (D : NativeSparseBlockEncoding.Data X n Z s) (x : X) (κ : ℝ) (hκ : 1 ≤ κ)
    (hlow : ∀ v, ‖v‖ ≤ κ * ‖Aop D x v‖) (Ub : X → V0 →L[ℂ] V0) (sv : V0)
    (σ : ℝ) (hσ₀ : 0 ≤ σ) (hσ₁ : σ ≤ 1) (r : ℝ) :
    (((Real.sqrt (1 - σ ^ 2) : ℝ) : ℂ) • H0 (Aop D x) + (σ : ℂ) • T1 +
        ((1 / r : ℝ) : ℂ) • T2 (betaOf (Ub x sv)) : Pub V0 →L[ℂ] Pub V0)
        (kerVec (equivOfLower (Aop D x) κ hlow) κ hκ
          (equivOfLower_symm_norm _ κ (by linarith) hlow) σ hσ₀ hσ₁ r (Ub x sv)) = 0 ∧
      ∀ u, (((Real.sqrt (1 - σ ^ 2) : ℝ) : ℂ) • H0 (Aop D x) + (σ : ℂ) • T1 +
        ((1 / r : ℝ) : ℂ) • T2 (betaOf (Ub x sv)) : Pub V0 →L[ℂ] Pub V0) u = 0 →
        ∃ c : ℂ, u = c • kerVec (equivOfLower (Aop D x) κ hlow) κ hκ
          (equivOfLower_symm_norm _ κ (by linarith) hlow) σ hσ₀ hσ₁ r (Ub x sv) := by
  have hcoe := equivOfLower_coe (Aop D x) κ hlow
  constructor
  · have h0 := branchHam_kerVec (equivOfLower (Aop D x) κ hlow) κ hκ
      (equivOfLower_symm_norm _ κ (by linarith) hlow) σ hσ₀ hσ₁ r (Ub x sv)
    rw [branchHam, hcoe] at h0
    exact h0
  · intro u hu
    apply branchHam_kernel (equivOfLower (Aop D x) κ hlow) κ hκ
      (equivOfLower_symm_norm _ κ (by linarith) hlow) σ hσ₀ hσ₁ r (Ub x sv) u
    rw [branchHam, hcoe]
    exact hu

theorem norm_JwO_eVec (D : NativeSparseBlockEncoding.Data X n Z s) :
    ‖(JwO D).toContinuousLinearMap eVec‖ = 1 := by
  rw [LinearIsometry.coe_toContinuousLinearMap, LinearIsometry.norm_map, Run.norm_eVec]

/-- **Test probabilities** (equations `qls:eq:probability`, `qls:eq:bernoulli`). -/
theorem test_fact (D : NativeSparseBlockEncoding.Data X n Z s) (x : X) (hA1 : ‖Aop D x‖ ≤ 1)
    (κ : ℝ) (hκ : 1 ≤ κ) (hlow : ∀ v, ‖v‖ ≤ κ * ‖Aop D x v‖) (Ub : X → V0 →L[ℂ] V0) (sv : V0)
    (hb : ‖Ub x sv‖ ≤ 1) (σ : ℝ) (hσ₀ : 0 ≤ σ) (hσ₁ : σ ≤ 1) (r : ℝ) (hr : 1 / 8 ≤ r) (g : ℝ)
    (hg0 : 0 < g) (hg : g ≤ RegularizationGap.gap κ σ) (N : ℕ)
    (hN : 100 ≤ (N : ℝ) * bLow (s : ℝ) g) :
    1 / (2 * (1 + (rSigma (equivOfLower (Aop D x) κ hlow) κ σ hκ
        (equivOfLower_symm_norm _ κ (by linarith) hlow) hσ₀ hσ₁ (betaOf (Ub x sv)) / r) ^ 2)) ≤
        ‖UnitaryFilter.filter (WwO D Ub sv σ r x) N 1 ((JwO D).toContinuousLinearMap eVec)‖ ^ 2 ∧
      ‖UnitaryFilter.filter (WwO D Ub sv σ r x) N 1 ((JwO D).toContinuousLinearMap eVec)‖ ^ 2 ≤
        1 / (1 + (rSigma (equivOfLower (Aop D x) κ hlow) κ σ hκ
          (equivOfLower_symm_norm _ κ (by linarith) hlow) hσ₀ hσ₁ (betaOf (Ub x sv)) / r) ^ 2) +
          1 / 10000 := by
  have hs : (0 : ℝ) < s := by exact_mod_cast D.slots_pos
  have hbpos := bLow_pos (s : ℝ) g hs hg0
  have hNpos : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · rw [h0, Nat.cast_zero, zero_mul] at hN; norm_num at hN
    · exact h0
  have hf := filter_bounds (WwO_unitaryF D Ub sv σ r x) (bLow (s : ℝ) g) hbpos
    (gapO D x hA1 κ hκ hlow Ub sv hb σ hσ₀ hσ₁ r hr g hg0 hg) N hNpos 1
    ((JwO D).toContinuousLinearMap eVec)
  rw [norm_JwO_eVec, mul_one, pow_one] at hf
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
  have hsmall : (1 / ((N : ℝ) * bLow (s : ℝ) g)) ^ 2 ≤ 1 / 10000 := by
    have h1 : 1 / ((N : ℝ) * bLow (s : ℝ) g) ≤ 1 / 100 :=
      one_div_le_one_div_of_le (by norm_num) hN
    have h2 : 0 ≤ 1 / ((N : ℝ) * bLow (s : ℝ) g) := by positivity
    nlinarith
  obtain ⟨hlo, hhi⟩ := hsb
  constructor
  · refine le_trans ?_ (hlo.trans hf.1)
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  · linarith [hf.2]

/-- **Final amplitude at `σ = 0`** (equation `qls:eq:finalprob` with the filter error). -/
theorem final_fact (D : NativeSparseBlockEncoding.Data X n Z s) (x : X) (hA1 : ‖Aop D x‖ ≤ 1)
    (κ : ℝ) (hκ : 1 ≤ κ) (hlow : ∀ v, ‖v‖ ≤ κ * ‖Aop D x v‖) (Ub : X → V0 →L[ℂ] V0) (sv : V0)
    (hb : ‖Ub x sv‖ ≤ 1) (r : ℝ) (hr : 1 / 8 ≤ r) (N : ℕ)
    (hN : 100 ≤ (N : ℝ) * bLow (s : ℝ) (1 / κ)) (k : ℕ) :
    ∃ c : ℝ, 1 / (r * ((1 + 66 / 256) *
        (1 + (‖(equivOfLower (Aop D x) κ hlow).symm (Ub x sv)‖ / r) ^ 2))) ≤ c ∧
      c ≤ 1 / (r * (1 + (‖(equivOfLower (Aop D x) κ hlow).symm (Ub x sv)‖ / r) ^ 2)) ∧
      ‖(solEmb†) (((JwO D).toContinuousLinearMap†)
          (UnitaryFilter.filter (WwO D Ub sv 0 r x) N k ((JwO D).toContinuousLinearMap eVec))) -
        (c : ℂ) • (equivOfLower (Aop D x) κ hlow).symm (Ub x sv)‖ ≤ (1 / 100) ^ k := by
  have h0 : (0 : ℝ) ≤ 0 := le_rfl
  have h1 : (0 : ℝ) ≤ 1 := zero_le_one
  have hκ0 : 0 < κ := by linarith
  have hs : (0 : ℝ) < s := by exact_mod_cast D.slots_pos
  have hr0 : 0 < r := by linarith
  obtain ⟨hk0, hker⟩ := kernel_data D x κ hκ hlow Ub sv 0 h0 h1 r
  obtain ⟨a, ha0, ha1, -, hamp⟩ := (hypO D x hA1 Ub sv hb 0 h0 h1 r hr).seed_facts _ eVec hk0 hker
    (kerVec_ne_zero _ κ hκ (equivOfLower_symm_norm _ κ (by linarith) hlow) 0 h0 h1 r (Ub x sv))
    (kerVec_inner_eVec _ κ hκ (equivOfLower_symm_norm _ κ (by linarith) hlow) 0 h0 h1 r
      (Ub x sv))
  rw [← WwO_eq D x hA1 Ub sv hb 0 h0 h1 r hr] at hamp
  have hn := kerVec_norm_sq (equivOfLower (Aop D x) κ hlow) κ hκ
    (equivOfLower_symm_norm _ κ (by linarith) hlow) 0 h0 h1 r (Ub x sv)
  rw [rSigma_zero] at hn
  have hsol := solEmb_kerVec (equivOfLower (Aop D x) κ hlow) κ hκ
    (equivOfLower_symm_norm _ κ (by linarith) hlow) h0 h1 r (Ub x sv)
  -- the scalar bookkeeping, with `m = ‖u₀‖²`
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
    have hNpos : 0 < N := by
      rcases Nat.eq_zero_or_pos N with h0' | h0'
      · rw [h0', Nat.cast_zero, zero_mul] at hN; norm_num at hN
      · exact h0'
    have hf := UnitaryFilter.filter_sub_proj_le (WwO_unitaryF D Ub sv 0 r x) _ hbpos hgap N hNpos k
      ((JwO D).toContinuousLinearMap eVec)
    rw [norm_JwO_eVec, mul_one] at hf
    refine hf.trans ?_
    apply pow_le_pow_left₀ (by positivity)
    exact one_div_le_one_div_of_le (by norm_num) hN

end

end SparseLinearSystems.Facts
