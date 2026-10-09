import SparseLinearSystems.Endpoint.Algorithm

/-!
# Correctness of the algorithm for one input

For an input satisfying the promise (`‖A‖ ≤ 1`, `‖v‖ ≤ κ ‖A v‖`, unitary
`U_b`, unit public seed):

* `rho_*`: the true norms `ρ_j = r_{σ_j}` obey the ladder of equation
  `qls:eq:normladder`;
* `test_bounds`: every test probability lies in
  `[1/(2(1+q²)), 1/(1+q²) + 10⁻⁴]`, `q = ρ_j / r`;
* `finalLeaf_good`: from a good estimate `ρ_m ≤ r ≤ 4 ρ_m`, the final leaf
  succeeds with probability at least `97/100` and outputs a state within
  `ε/50` of the normalised solution.
-/

namespace SparseLinearSystems.Endpoint

noncomputable section
open SparseHamiltonian
open ContinuousLinearMap OracleCircuit HilbertAugmentation Augmented SparseBranch LogicalWalk
  Cells Step Run Facts Protocol
open scoped InnerProduct
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 2048

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s : ℕ}

local notation "V0" => EuclideanSpace ℂ n

omit [DecidableEq n] in
theorem norm_source (Ub : X → V0 →L[ℂ] V0) (hUb : ∀ x, IsUnitary (Ub x)) (sv : V0)
    (hsv : ‖sv‖ = 1) (x : X) : ‖Ub x sv‖ = 1 := by
  rw [(Ub x).norm_map_iff_adjoint_comp_self.mpr (hUb x).1, hsv]

/-- The true regularised solution norms `ρ_j = r_{σ_j}` of one input. -/
def rho (D : NativeSparseBlockEncoding.Data X n Z s) (x : X) (κ : ℝ) (hκ : 1 ≤ κ)
    (hlow : ∀ v, ‖v‖ ≤ κ * ‖Aop D x v‖) (Ub : X → V0 →L[ℂ] V0) (sv : V0) (j : ℕ) : ℝ :=
  rSigma (equivOfLower (Aop D x) κ hlow) κ (sig j) hκ
    (equivOfLower_symm_norm _ κ (by linarith) hlow) (sig_nonneg j) (sig_le_one j)
    (betaOf (Ub x sv))

section Ladder

variable (D : NativeSparseBlockEncoding.Data X n Z s) (x : X) (κ : ℝ) (hκ : 1 ≤ κ)
  (hA1 : ‖Aop D x‖ ≤ 1) (hlow : ∀ v, ‖v‖ ≤ κ * ‖Aop D x v‖)
  (Ub : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
  (hUb : ∀ x, IsUnitary (Ub x)) (sv : EuclideanSpace ℂ n) (hsv : ‖sv‖ = 1)

include hUb hsv in
omit [DecidableEq n] in
theorem norm_beta : ‖betaOf (Ub x sv)‖ = 1 := by
  rw [norm_betaOf, norm_source Ub hUb sv hsv x]

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
theorem normA (hA1 : ‖Aop D x‖ ≤ 1) :
    ‖(equivOfLower (Aop D x) κ hlow).toContinuousLinearMap‖ ≤ 1 := by
  rw [equivOfLower_coe]; exact hA1

include hUb hsv in
omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
theorem rho_zero : rho D x κ hκ hlow Ub sv 0 = 1 := by
  unfold rho
  rw [rSigma_congr _ κ hκ _ (show sig 0 = 1 by simp [sig]) _ _ zero_le_one le_rfl,
    rSigma_one, norm_beta x Ub hUb sv hsv]

include hUb hsv hA1 in
omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
theorem rho_bounds (j : ℕ) : 1 ≤ rho D x κ hκ hlow Ub sv j ∧ rho D x κ hκ hlow Ub sv j ≤ κ := by
  have hβ := norm_beta x Ub hUb sv hsv
  constructor
  · have h := one_le_rSigma (equivOfLower (Aop D x) κ hlow) κ hκ
      (equivOfLower_symm_norm _ κ (by linarith) hlow) (normA D x κ hlow hA1) (sig j)
      (sig_nonneg j) (sig_le_one j) (betaOf (Ub x sv))
    rw [hβ] at h
    exact h
  · have h := rSigma_le_kappa (equivOfLower (Aop D x) κ hlow) κ hκ
      (equivOfLower_symm_norm _ κ (by linarith) hlow) (sig j) (sig_nonneg j) (sig_le_one j)
      (betaOf (Ub x sv))
    rw [hβ, mul_one] at h
    exact h

include hA1 in
omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
theorem rho_ladder (j : ℕ) (hj : 1 ≤ j) :
    rho D x κ hκ hlow Ub sv (j - 1) ≤ rho D x κ hκ hlow Ub sv j ∧
      rho D x κ hκ hlow Ub sv j ≤ 2 * rho D x κ hκ hlow Ub sv (j - 1) := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  have hsig := sig_succ i
  have hInv := equivOfLower_symm_norm (Aop D x) κ (by linarith) hlow
  have hA := normA D x κ hlow hA1
  have hle : sig (i + 1) ≤ sig i := by rw [hsig]; linarith [sig_nonneg i]
  have h1 := rSigma_anti (equivOfLower (Aop D x) κ hlow) κ hκ hInv hA (sig i) (sig (i + 1))
    (sig_nonneg i) (sig_le_one i) (sig_nonneg (i + 1)) (sig_le_one (i + 1)) hle
    (betaOf (Ub x sv))
  have h2 := rSigma_half_le (equivOfLower (Aop D x) κ hlow) κ hκ hInv (sig i) (sig_nonneg i)
    (sig_le_one i) (by linarith [sig_nonneg i]) (by linarith [sig_le_one i, sig_nonneg i])
    (betaOf (Ub x sv))
  have h3 := rSigma_congr (equivOfLower (Aop D x) κ hlow) κ hκ hInv hsig (sig_nonneg (i + 1))
    (sig_le_one (i + 1)) (by linarith [sig_nonneg i]) (by linarith [sig_le_one i, sig_nonneg i])
    (betaOf (Ub x sv))
  refine ⟨h1, ?_⟩
  show rSigma (equivOfLower (Aop D x) κ hlow) κ (sig (i + 1)) hκ hInv (sig_nonneg (i + 1))
    (sig_le_one (i + 1)) (betaOf (Ub x sv)) ≤ 2 * rSigma (equivOfLower (Aop D x) κ hlow) κ
      (sig i) hκ hInv (sig_nonneg i) (sig_le_one i) (betaOf (Ub x sv))
  rw [h3]
  exact h2

end Ladder

/-! ### Tests -/

theorem test_bounds (D : NativeSparseBlockEncoding.Data X n Z s) (x : X) (κ ε : ℝ)
    (hκ : 1 ≤ κ) (hA1 : ‖Aop D x‖ ≤ 1) (hlow : ∀ v, ‖v‖ ≤ κ * ‖Aop D x v‖)
    (Ub : X → V0 →L[ℂ] V0) (hUb : ∀ x, IsUnitary (Ub x)) (sv : V0) (hsv : ‖sv‖ = 1)
    (j : ℕ) (hjm : j ≤ stagesM κ) (r : ℝ) (hr : 1 / 8 ≤ r) :
    1 / (2 * (1 + (rho D x κ hκ hlow Ub sv j / r) ^ 2)) ≤
        (testRun D Ub sv κ ε j r).probability x ∧
      (testRun D Ub sv κ ε j r).probability x ≤
        1 / (1 + (rho D x κ hκ hlow Ub sv j / r) ^ 2) + 1 / 10000 := by
  have hb : ‖Ub x sv‖ ≤ 1 := (norm_source Ub hUb sv hsv x).le
  rw [testRun_probability D Ub hUb sv κ ε j r x, stageOf_of_le κ j hjm]
  exact test_fact D x hA1 κ hκ hlow Ub sv hb (sig j) (sig_nonneg j) (sig_le_one j) r hr (sig j)
    (sig_pos j) (RegularizationGap.sigma_le_gap κ (sig j) (sig_nonneg j) (sig_le_one j))
    (Ntest s j) (Ntest_spec s D.slots_pos j)

/-! ### The final leaf -/

theorem unitDirection_real_smul {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (c : ℝ) (hc : 0 < c) (y : E) :
    ODEStateNormalization.unitDirection ((c : ℂ) • y) = ODEStateNormalization.unitDirection y := by
  unfold ODEStateNormalization.unitDirection
  rw [Complex.coe_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hc, smul_smul]
  by_cases hy : ‖y‖ = 0
  · rw [hy, mul_zero, inv_zero, zero_mul]
  · congr 1
    field_simp

/-- `(1 - p)^n ≤ 1/(1 + n p)` for `0 ≤ p ≤ 1`. -/
theorem one_sub_pow_le (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (n : ℕ) :
    (1 - p) ^ n ≤ 1 / (1 + n * p) := by
  have h1 : 1 - p ≤ Real.exp (-p) := by linarith [Real.add_one_le_exp (-p)]
  have h2 : (1 - p) ^ n ≤ Real.exp (-p) ^ n := pow_le_pow_left₀ (by linarith) h1 n
  rw [← Real.exp_nat_mul, mul_neg, Real.exp_neg] at h2
  refine h2.trans ?_
  rw [one_div]
  apply inv_anti₀ (by positivity)
  linarith [Real.add_one_le_exp (n * p)]

/-- `q/(1 + q²) ≥ 4/17` on `[1/4, 4]`. -/
theorem q_ratio_lower (q : ℝ) (h1 : 1 / 4 ≤ q) (h2 : q ≤ 4) : 4 / 17 ≤ q / (1 + q ^ 2) := by
  rw [div_le_div_iff₀ (by norm_num) (by positivity)]
  nlinarith

/-- **The final leaf at a good estimate** (equations `qls:eq:qrange`,
`qls:eq:finalprob`): success at least `97/100` and output within `ε/50`. -/
theorem finalLeaf_good (D : NativeSparseBlockEncoding.Data X n Z s) (x : X) (κ ε : ℝ)
    (hκ : 1 ≤ κ) (hA1 : ‖Aop D x‖ ≤ 1) (hlow : ∀ v, ‖v‖ ≤ κ * ‖Aop D x v‖)
    (Ub : X → V0 →L[ℂ] V0) (hUb : ∀ x, IsUnitary (Ub x)) (sv : V0) (hsv : ‖sv‖ = 1)
    (hε : 0 < ε) (hε1 : ε ≤ 1 / 10) (r : ℝ)
    (hr1 : rho D x κ hκ hlow Ub sv (stagesM κ) ≤ r)
    (hr2 : r ≤ 4 * rho D x κ hκ hlow Ub sv (stagesM κ)) :
    97 / 100 ≤ (finalLeaf D Ub sv κ ε r).successMass x ∧
      ‖leafDir x (finalLeaf D Ub sv κ ε r) -
        ODEStateNormalization.unitDirection ((equivOfLower (Aop D x) κ hlow).symm (Ub x sv))‖ ≤
        ε / 50 := by
  have hκ0 : 0 < κ := by linarith
  have hρ := rho_bounds D x κ hκ hA1 hlow Ub hUb sv hsv (stagesM κ)
  have hr0 : 0 < r := by linarith
  have hr8 : 1 / 8 ≤ r := by linarith
  have hb : ‖Ub x sv‖ ≤ 1 := (norm_source Ub hUb sv hsv x).le
  have hInv := equivOfLower_symm_norm (Aop D x) κ hκ0.le hlow
  have hA := normA D x κ hlow hA1
  obtain ⟨c, hclo, -, herr⟩ := final_fact D x hA1 κ hκ hlow Ub sv hb r hr8 (Nfin s κ)
    (Nfin_spec s D.slots_pos κ hκ) (kfin ε)
  have hk := kfin_spec ε hε
  -- the solution norm relative to `ρ_m`
  have hy0 : ‖(equivOfLower (Aop D x) κ hlow).symm (Ub x sv)‖ =
      rSigma (equivOfLower (Aop D x) κ hlow) κ 0 hκ hInv le_rfl zero_le_one (betaOf (Ub x sv)) :=
    (rSigma_zero _ κ hκ hInv (Ub x sv)).symm
  have hlo := rSigma_anti (equivOfLower (Aop D x) κ hlow) κ hκ hInv hA (sig (stagesM κ)) 0
    (sig_nonneg _) (sig_le_one _) le_rfl zero_le_one (sig_nonneg _) (betaOf (Ub x sv))
  have hhi := rSigma_zero_le (equivOfLower (Aop D x) κ hlow) κ hκ hInv (sig (stagesM κ))
    (sig_nonneg _) (sig_le_one _) le_rfl zero_le_one (betaOf (Ub x sv))
  rw [← hy0] at hlo hhi
  change rho D x κ hκ hlow Ub sv (stagesM κ) ≤ _ at hlo
  change _ ≤ Real.sqrt (1 + κ ^ 2 * sig (stagesM κ) ^ 2) * rho D x κ hκ hlow Ub sv (stagesM κ)
    at hhi
  generalize hY : (equivOfLower (Aop D x) κ hlow).symm (Ub x sv) = y₀ at hlo hhi herr hclo ⊢
  generalize hR : rho D x κ hκ hlow Ub sv (stagesM κ) = ρ at hlo hhi hr1 hr2 hρ
  have hsm : κ * sig (stagesM κ) ≤ 1 := by
    have := sig_stages_le κ hκ
    rw [le_div_iff₀ hκ0] at this
    linarith
  have hsq : Real.sqrt (1 + κ ^ 2 * sig (stagesM κ) ^ 2) ≤ Real.sqrt 2 := by
    apply Real.sqrt_le_sqrt
    have h := pow_le_one₀ (mul_nonneg hκ0.le (sig_nonneg (stagesM κ))) hsm (n := 2)
    rw [mul_pow] at h
    linarith
  have hs2 : Real.sqrt 2 < 3 / 2 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hρ0 : 0 < ρ := by linarith [hρ.1]
  -- `q₀ = ‖y₀‖ / r ∈ [1/4, 3/2]`
  have hq1 : 1 / 4 ≤ ‖y₀‖ / r := by
    rw [le_div_iff₀ hr0]; linarith
  have hq2 : ‖y₀‖ / r ≤ 3 / 2 := by
    rw [div_le_iff₀ hr0]
    have : Real.sqrt (1 + κ ^ 2 * sig (stagesM κ) ^ 2) * ρ ≤ 3 / 2 * ρ :=
      mul_le_mul_of_nonneg_right (hsq.trans hs2.le) hρ0.le
    linarith
  -- `c ‖y₀‖ ≥ 1024/5474`
  have hcy : 1024 / 5474 ≤ c * ‖y₀‖ := by
    have hratio := q_ratio_lower (‖y₀‖ / r) hq1 (by linarith)
    have hpos : 0 < r * ((1 + 66 / 256) * (1 + (‖y₀‖ / r) ^ 2)) := by positivity
    have hc' : ‖y₀‖ / (r * ((1 + 66 / 256) * (1 + (‖y₀‖ / r) ^ 2))) ≤ c * ‖y₀‖ := by
      have := mul_le_mul_of_nonneg_right hclo (norm_nonneg y₀)
      rw [one_div_mul_eq_div] at this
      exact this
    have hrw : ‖y₀‖ / (r * ((1 + 66 / 256) * (1 + (‖y₀‖ / r) ^ 2))) =
        (‖y₀‖ / r / (1 + (‖y₀‖ / r) ^ 2)) / (1 + 66 / 256) := by
      field_simp
    rw [hrw] at hc'
    have : 4 / 17 / (1 + 66 / 256) ≤ ‖y₀‖ / r / (1 + (‖y₀‖ / r) ^ 2) / (1 + 66 / 256) :=
      div_le_div_of_nonneg_right hratio (by norm_num)
    have h4 : (1024 : ℝ) / 5474 = 4 / 17 / (1 + 66 / 256) := by norm_num
    linarith
  have hcpos : 0 < c := by
    by_contra hcon
    push Not at hcon
    have := mul_nonpos_of_nonpos_of_nonneg hcon (norm_nonneg y₀)
    linarith
  -- the decoded amplitude
  have herr' : ‖finalAmp D Ub sv κ ε r x - (c : ℂ) • y₀‖ ≤ ε / 1000 := by
    rw [finalAmp_eq D Ub hUb sv κ ε r x]
    exact herr.trans hk
  have hp1 := finalAmp_norm_sq_le D Ub hUb sv κ ε r x
  rw [finalLeaf_successMass, finalLeaf_leafDir]
  generalize finalAmp D Ub sv κ ε r x = a at herr' hp1 ⊢
  have hcy' : ‖(c : ℂ) • y₀‖ = c * ‖y₀‖ := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hcpos]
  have hanorm : 1024 / 5474 - ε / 1000 ≤ ‖a‖ := by
    have := norm_sub_norm_le ((c : ℂ) • y₀) a
    rw [norm_sub_rev] at this
    linarith
  constructor
  · have h1 : (1869 : ℝ) / 10000 ≤ ‖a‖ := by linarith
    have hp0 : 349 / 10000 ≤ ‖a‖ ^ 2 := by
      have := pow_le_pow_left₀ (by norm_num) h1 2
      linarith [show ((1869 : ℝ) / 10000) ^ 2 = 3493161 / 100000000 by norm_num]
    have hbd : 1 / (1 + ((1000 : ℕ) : ℝ) * ‖a‖ ^ 2) ≤ 3 / 100 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      push_cast
      linarith
    have hpow := one_sub_pow_le (‖a‖ ^ 2) (sq_nonneg _) hp1 1000
    generalize (1 - ‖a‖ ^ 2) ^ 1000 = P at hpow ⊢
    generalize 1 / (1 + ((1000 : ℕ) : ℝ) * ‖a‖ ^ 2) = B at hpow hbd
    linarith
  · rw [← unitDirection_real_smul c hcpos y₀]
    have hy0ne : (c : ℂ) • y₀ ≠ 0 := by
      intro h
      rw [h, norm_zero] at hcy'
      linarith
    have hane : a ≠ 0 := by
      intro h
      rw [h, norm_zero] at hanorm
      linarith
    refine (ODEStateNormalization.unitDirection_error_le _ _ hy0ne hane).trans ?_
    rw [hcy', div_le_iff₀ (by linarith)]
    have := mul_le_mul_of_nonneg_left hcy (by positivity : (0 : ℝ) ≤ ε / 50)
    linarith

/-! ### Success and output guarantee -/

/-- A good final leaf: success at least `97/100` and output within `ε/50`. -/
def GoodLeaf {O : Lbl → X → Phys n Z T →L[ℂ] Phys n Z T} (x : X) (v : V0) (ε : ℝ)
    (p : ODERepeatProtocol.Protocol O V0) : Prop :=
  97 / 100 ≤ p.successMass x ∧
    (p.successMass x ≠ 0 → ∃ ω : ℂ, ‖ω‖ = 1 ∧ ‖ω • leafDir x p - v‖ ≤ ε / 50)

/-- **Correctness for one input** (Theorem `qls:thm:main`, success and accuracy). -/
theorem correctness (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (hUb : ∀ x, IsUnitary (Ub x)) (sv : V0) (hsv : ‖sv‖ = 1) (κ ε : ℝ) (hκ : 1 ≤ κ)
    (hε : 0 < ε) (hε1 : ε ≤ 1 / 10) (x : X) (hA1 : ‖Aop D x‖ ≤ 1)
    (hlow : ∀ v, ‖v‖ ≤ κ * ‖Aop D x v‖) :
    2 / 3 ≤ (algorithm D Ub sv κ ε).successMass x ∧
      ∀ y : V0, Aop D x y = Ub x sv →
        ODEMixedOutput.IsDensity ((algorithm D Ub sv κ ε).conditionalDensity x) ∧
          ∃ h : ((algorithm D Ub sv κ ε).conditionalDensity x -
              ODEMixedOutput.pureOperator (ODEStateNormalization.unitDirection y)).toLinearMap.IsSymmetric,
            ODEMixedOutput.hermitianTraceDistance ((algorithm D Ub sv κ ε).conditionalDensity x)
              (ODEMixedOutput.pureOperator (ODEStateNormalization.unitDirection y)) h ≤ ε := by
  set v := ODEStateNormalization.unitDirection ((equivOfLower (Aop D x) κ hlow).symm (Ub x sv))
    with hv
  have hU : (algorithm D Ub sv κ ε).RunsUnitary x :=
    Estimator.stages_runsUnitary x _ _ _ _ κ (fun j r => testRun_unitary D Ub hUb sv κ ε j r x) _ _
  -- good leaves at good estimates
  have hgoodr : ∀ r, rho D x κ hκ hlow Ub sv (stagesM κ) ≤ r →
      r ≤ 4 * rho D x κ hκ hlow Ub sv (stagesM κ) → GoodLeaf x v ε (finalLeaf D Ub sv κ ε r) := by
    intro r hr1 hr2
    obtain ⟨hm, hd⟩ := finalLeaf_good D x κ ε hκ hA1 hlow Ub hUb sv hsv hε hε1 r hr1 hr2
    exact ⟨hm, fun _ => ⟨1, norm_one, by rw [one_smul]; exact hd⟩⟩
  -- the bad mass
  have hbad : (algorithm D Ub sv κ ε).reach (fun p => ¬ GoodLeaf x v ε p) x ≤ ε / 500 := by
    have h := Estimator.algorithm_bad_le x (testRun D Ub sv κ ε)
      (Tree.indicator (fun p => ¬ GoodLeaf x v ε p))
      (Tree.indicator_nonneg _) (Tree.indicator_le_one _) (finalLeaf D Ub sv κ ε) (reps κ ε)
      (stagesM κ) κ (rho D x κ hκ hlow Ub sv) (zeta κ ε)
      (rho_zero D x κ hκ hlow Ub hUb sv hsv)
      (fun j _ => rho_bounds D x κ hκ hA1 hlow Ub hUb sv hsv j)
      (fun j hj1 _ => rho_ladder D x κ hκ hA1 hlow Ub sv j hj1) (zeta_pos κ ε hε) (reps_spec κ ε)
      (fun j r => testRun_unitary D Ub hUb sv κ ε j r x)
      (fun j r _ hjm hr => test_bounds D x κ ε hκ hA1 hlow Ub hUb sv hsv j hjm r hr)
      (fun r hr1 hr2 => Tree.indicator_of_neg (not_not.mpr (hgoodr r hr1 hr2)))
    exact h.trans (sum_zeta_le κ ε hε)
  -- success
  have hleaf1 : (algorithm D Ub sv κ ε).AllLeaves (fun p =>
      0 ≤ p.successMass x ∧ (GoodLeaf x v ε p → 97 / 100 ≤ p.successMass x)) :=
    Estimator.stages_allLeaves _ _ _ _ κ _
      (fun r => ⟨(finalLeaf_spec D Ub hUb sv κ ε r x).1, fun hg => hg.1⟩) _ _
  have hsucc := Tree.successMass_ge x _ hU (97 / 100) (GoodLeaf x v ε) hleaf1
  have hcompl := Tree.reach_add_compl (GoodLeaf x v ε) x (algorithm D Ub sv κ ε)
  have hM : 2 / 3 ≤ (algorithm D Ub sv κ ε).successMass x := by
    nlinarith
  refine ⟨hM, ?_⟩
  intro y hy
  have hy' : (equivOfLower (Aop D x) κ hlow).symm (Ub x sv) = y := by
    rw [← hy, ← equivOfLower_apply (Aop D x) κ hlow y, ContinuousLinearEquiv.symm_apply_apply]
  rw [hy'] at hv
  rw [← hv]
  have hyne : y ≠ 0 := by
    intro h0
    have := norm_source Ub hUb sv hsv x
    rw [← hy, h0, map_zero, norm_zero] at this
    norm_num at this
  have hvn : ‖v‖ = 1 := by rw [hv]; exact ODEStateNormalization.unitDirection_norm y hyne
  have hleaf2 : (algorithm D Ub sv κ ε).AllLeaves (fun p =>
      0 ≤ p.successMass x ∧ p.successMass x ≤ 1 ∧
      (p.successMass x ≠ 0 → ‖leafDir x p‖ = 1) ∧
      p.successDensity x = ((p.successMass x : ℝ) : ℂ) • ODEMixedOutput.pureOperator (leafDir x p) ∧
      (GoodLeaf x v ε p → p.successMass x ≠ 0 →
        ∃ ω : ℂ, ‖ω‖ = 1 ∧ ‖ω • leafDir x p - v‖ ≤ ε / 50)) :=
    Estimator.stages_allLeaves _ _ _ _ κ _ (fun r => by
      obtain ⟨h0, h1, h2, h3⟩ := finalLeaf_spec D Ub hUb sv κ ε r x
      exact ⟨h0, h1, h2, h3, fun hg => hg.2⟩) _ _
  obtain ⟨hdens, hsym, hdist⟩ := Tree.output_guarantee x _ hU v hvn (ε / 50) (by positivity)
    (GoodLeaf x v ε) (leafDir x) hleaf2 (by linarith)
  refine ⟨hdens, hsym, hdist.trans ?_⟩
  have hR := Tree.reach_nonneg (fun p => ¬ GoodLeaf x v ε p) x _ hU
  have : (algorithm D Ub sv κ ε).reach (fun p => ¬ GoodLeaf x v ε p) x /
      (algorithm D Ub sv κ ε).successMass x ≤ (ε / 500) / (2 / 3) := by
    apply div_le_div₀ (by positivity) hbad (by norm_num) hM
  linarith

end

end SparseLinearSystems.Endpoint
