import ChebyshevLinearSystemFinite.Algorithm
import ChebyshevLinearSystem.Correctness

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 2048

/-!
# Correctness with approximate known gates, for one input

For an input satisfying the promise (`‖A‖ ≤ 1`, `‖v‖ ≤ κ ‖A v‖`, unitary `U_b`, unit public
seed), and implemented runs whose success vectors at that input differ from those of the ideal
runs by at most the allowances of the manuscript (its `e`; `AmpApprox` and `RunApprox` give
such bounds):

* `testRunF_bounds`: the ideal finite-degree test probability lies in
  `[1/(2(1 + q²)), 1/(1 + q²) + δ₀²]`, `q = ρ_j/r` (from `test_fact_deg`);
* `impl_bernoulli` (equation `qls:eq:bernoulli`): an implemented test whose success vector is
  within `e_test = (10⁻⁴ - δ₀²)/2` of the ideal one has probability within `2 e_test` of the
  ideal one (`probability_sub_le_of_amp`), so `|p_F - p_ξ(r)| ≤ δ₀² + 2 e_test = 10⁻⁴`;
  `impl_test_bounds`: its probability lies in `[1/(2(1 + q²)) - 10⁻⁴, 1/(1 + q²) + 10⁻⁴]`;
* `impl_final_amp`: an implemented final attempt whose decoded amplitude is within
  `e_fin = ε/1000 - δ₀` of the ideal one is within `δ₀ + e_fin = ε/1000` of the decoded exact
  projection `c A⁻¹ b`;
* `impl_final_good`: hence, from a good estimate `ρ_m ≤ r ≤ 4 ρ_m`, its final leaf succeeds
  with probability at least `97/100` and outputs a state within `ε/50` of the normalised
  solution (the released `ChebyshevLinearSystem.final_good_arith`);
* `impl_correctness`: unitary runs, success probability at least `2/3` and conditional trace
  distance at most `ε`, with the two-sided estimator analysis `algorithm_bad_le_tol` and the
  released `Protocol.Tree.successMass_ge`, `Protocol.Tree.output_guarantee`.

Notation: the regularization parameter is `σ` here and `ξ` in the manuscript, so a subscript `σ` (as
in `g_σ`, `r_σ`, `H_{σ,r}`) stands for the manuscript's subscript `ξ`.
-/

namespace ChebyshevLinearSystemFinite

noncomputable section
open ContinuousLinearMap SparseHamiltonian SparseLinearSystems OracleCircuit
  HilbertAugmentation Augmented SparseBranch LogicalWalk Step Facts Protocol Endpoint
  ChebyshevFilter ChebyshevLinearSystem
open scoped InnerProduct

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s : ℕ}

local notation "V0" => EuclideanSpace ℂ n

/-! ### Tests -/

/-- **The ideal finite-degree test** (equations `qls:eq:probability`,
`qls:eq:filterprobability`): its probability lies in `[1/(2(1+q²)), 1/(1+q²) + δ₀²]`,
`q = ρ_j/r`, `δ₀ = δ₀(σ_j)` at `δ = 1/100`. -/
theorem testRunF_bounds (D : NativeSparseBlockEncoding.Data X n Z s) (x : X) (κ ε : ℝ)
    (hκ : 1 ≤ κ) (hA1 : ‖Aop D x‖ ≤ 1) (hlow : ∀ v, ‖v‖ ≤ κ * ‖Aop D x v‖)
    (Ub : X → V0 →L[ℂ] V0) (hUb : ∀ x, IsUnitary (Ub x)) (sv : V0) (hsv : ‖sv‖ = 1)
    (j : ℕ) (hjm : j ≤ stagesM κ) (r : ℝ) (hr : 1 / 8 ≤ r) :
    1 / (2 * (1 + (rho D x κ hκ hlow Ub sv j / r) ^ 2)) ≤
        (testRunF D Ub sv κ ε j r).probability x ∧
      (testRunF D Ub sv κ ε j r).probability x ≤
        1 / (1 + (rho D x κ hκ hlow Ub sv j / r) ^ 2) + delta0 s (sig j) (1 / 100) ^ 2 := by
  have hb : ‖Ub x sv‖ ≤ 1 := (norm_source Ub hUb sv hsv x).le
  rw [probability_eq_amp, testRunF_amp D Ub hUb sv κ ε j r x, stageOf_of_le κ j hjm]
  exact test_fact_deg D x hA1 κ hκ hlow Ub sv hb (sig j) (sig_nonneg j) (sig_le_one j) r hr
    (sig j) (sig_pos j) (RegularizationGap.sigma_le_gap κ (sig j) (sig_nonneg j)
      (sig_le_one j)) (dTestF s j)

/-- **Test probabilities of every implementation** (equation `qls:eq:bernoulli`): an
implemented test whose success vector at the input is within `e_test = (10⁻⁴ - δ₀²)/2` of the
ideal one has `|p_F - p_ξ(r)| ≤ δ₀² + 2 e_test = 10⁻⁴`, so its probability lies in
`[1/(2(1+q²)) - 10⁻⁴, 1/(1+q²) + 10⁻⁴]`. -/
theorem impl_test_bounds (D : NativeSparseBlockEncoding.Data X n Z s) (x : X) (κ ε : ℝ)
    (hκ : 1 ≤ κ) (hA1 : ‖Aop D x‖ ≤ 1) (hlow : ∀ v, ‖v‖ ≤ κ * ‖Aop D x v‖)
    (Ub : X → V0 →L[ℂ] V0) (hUb : ∀ x, IsUnitary (Ub x)) (sv : V0) (hsv : ‖sv‖ = 1)
    (j : ℕ) (hjm : j ≤ stagesM κ) (r : ℝ) (hr : 1 / 8 ≤ r)
    (t : TestRun (physOracle D Ub (TcF s κ ε)) (PrivO n))
    (ht : ‖amp t x - amp (testRunF D Ub sv κ ε j r) x‖ ≤ eTest s (stageOf κ j)) :
    1 / (2 * (1 + (rho D x κ hκ hlow Ub sv j / r) ^ 2)) - 1 / 10000 ≤ t.probability x ∧
      t.probability x ≤ 1 / (1 + (rho D x κ hκ hlow Ub sv j / r) ^ 2) + 1 / 10000 := by
  have hp := probability_sub_le_of_amp (physOracle_unitary D Ub hUb _) x ht
  rw [stageOf_of_le κ j hjm] at hp
  have hideal := testRunF_bounds D x κ ε hκ hA1 hlow Ub hUb sv hsv j hjm r hr
  have h2e : 2 * eTest s j = 1 / 10000 - delta0 (s : ℝ) (sig j) (1 / 100) ^ 2 := by
    unfold eTest
    ring
  have hd0 := sq_nonneg (delta0 (s : ℝ) (sig j) (1 / 100))
  obtain ⟨h1, h2⟩ := abs_le.mp hp
  constructor <;> linarith [hideal.1, hideal.2]

/-- **Equation `qls:eq:bernoulli`**: an implemented test whose success vector at the input is
within `e_test` of the ideal one has `|p_F - p_ξ(r)| ≤ δ₀² + 2 e_test = 10⁻⁴`, where
`p_ξ(r) = ‖P_{ξ_j,r} J e‖²` is the exact probability of the eigenvalue-one projection. -/
theorem impl_bernoulli (D : NativeSparseBlockEncoding.Data X n Z s) (x : X) (κ ε : ℝ)
    (hκ : 1 ≤ κ) (hA1 : ‖Aop D x‖ ≤ 1) (hlow : ∀ v, ‖v‖ ≤ κ * ‖Aop D x v‖)
    (Ub : X → V0 →L[ℂ] V0) (hUb : ∀ x, IsUnitary (Ub x)) (sv : V0) (hsv : ‖sv‖ = 1)
    (j : ℕ) (hjm : j ≤ stagesM κ) (r : ℝ) (hr : 1 / 8 ≤ r)
    (t : TestRun (physOracle D Ub (TcF s κ ε)) (PrivO n))
    (ht : ‖amp t x - amp (testRunF D Ub sv κ ε j r) x‖ ≤ eTest s (stageOf κ j)) :
    |t.probability x - ‖UnitaryFilter.fixedProj (WwO D Ub sv (sig j) r x)
      ((JwO D).toContinuousLinearMap eVec)‖ ^ 2| ≤ 1 / 10000 := by
  have hb : ‖Ub x sv‖ ≤ 1 := (norm_source Ub hUb sv hsv x).le
  have hp := probability_sub_le_of_amp (physOracle_unitary D Ub hUb _) x ht
  rw [stageOf_of_le κ j hjm] at hp
  have hideal : ‖UnitaryFilter.fixedProj (WwO D Ub sv (sig j) r x)
        ((JwO D).toContinuousLinearMap eVec)‖ ^ 2 ≤ (testRunF D Ub sv κ ε j r).probability x ∧
      (testRunF D Ub sv κ ε j r).probability x ≤ ‖UnitaryFilter.fixedProj
        (WwO D Ub sv (sig j) r x) ((JwO D).toContinuousLinearMap eVec)‖ ^ 2 +
        delta0 s (sig j) (1 / 100) ^ 2 := by
    rw [probability_eq_amp, testRunF_amp D Ub hUb sv κ ε j r x, stageOf_of_le κ j hjm]
    exact filter_proj_deg D x hA1 κ hκ hlow Ub sv hb (sig j) (sig_nonneg j) (sig_le_one j) r hr
      (sig j) (sig_pos j) (RegularizationGap.sigma_le_gap κ (sig j) (sig_nonneg j)
        (sig_le_one j)) (dTestF s j)
  have h2e : 2 * eTest s j = 1 / 10000 - delta0 (s : ℝ) (sig j) (1 / 100) ^ 2 := by
    unfold eTest
    ring
  have hd0 := sq_nonneg (delta0 (s : ℝ) (sig j) (1 / 100))
  obtain ⟨h1, h2⟩ := abs_le.mp hp
  rw [abs_le]
  constructor <;> linarith [hideal.1, hideal.2]

/-! ### The final leaf -/

/-- **The final attempt of every implementation** (the final error after equation
`qls:eq:bernoulli`): if the implemented final attempt changes the decoded amplitude at the input
by at most `e_fin = δ - δ₀` (`δ = ε/1000`), its decoded amplitude is within `δ₀ + e_fin = δ` of
the decoded exact projection `c A⁻¹ b`, with `1/(r (1 + μ)(1 + q²)) ≤ c ≤ 1/(r (1 + q²))`,
`μ = 66/256`, `q = ‖A⁻¹ b‖/r`. -/
theorem impl_final_amp (D : NativeSparseBlockEncoding.Data X n Z s) (x : X) (κ ε : ℝ)
    (hκ : 1 ≤ κ) (hA1 : ‖Aop D x‖ ≤ 1) (hlow : ∀ v, ‖v‖ ≤ κ * ‖Aop D x v‖)
    (Ub : X → V0 →L[ℂ] V0) (hUb : ∀ x, IsUnitary (Ub x)) (sv : V0) (hsv : ‖sv‖ = 1)
    (r : ℝ) (hr : 1 / 8 ≤ r) (t : TestRun (physOracle D Ub (TcF s κ ε)) V0)
    (ht : ‖amp t x - amp (finalRunF D Ub sv κ ε r) x‖ ≤ eFin s κ ε) :
    ∃ c : ℝ, 1 / (r * ((1 + 66 / 256) *
        (1 + (‖(equivOfLower (Aop D x) κ hlow).symm (Ub x sv)‖ / r) ^ 2))) ≤ c ∧
      c ≤ 1 / (r * (1 + (‖(equivOfLower (Aop D x) κ hlow).symm (Ub x sv)‖ / r) ^ 2)) ∧
      ‖amp t x - (c : ℂ) • (equivOfLower (Aop D x) κ hlow).symm (Ub x sv)‖ ≤ ε / 1000 := by
  have hb : ‖Ub x sv‖ ≤ 1 := (norm_source Ub hUb sv hsv x).le
  obtain ⟨c, hclo, hchi, herr⟩ := final_fact_deg D x hA1 κ hκ hlow Ub sv hb r hr (dFinF s κ ε)
    (Nat.succ_pos _)
  refine ⟨c, hclo, hchi, ?_⟩
  have hideal : ‖amp (finalRunF D Ub sv κ ε r) x -
      (c : ℂ) • (equivOfLower (Aop D x) κ hlow).symm (Ub x sv)‖ ≤
      delta0 (s : ℝ) (1 / κ) (ε / 1000) := by
    rw [finalRunF_amp D Ub hUb sv κ ε r x]
    exact herr
  have e : amp t x - (c : ℂ) • (equivOfLower (Aop D x) κ hlow).symm (Ub x sv) =
      (amp t x - amp (finalRunF D Ub sv κ ε r) x) +
        (amp (finalRunF D Ub sv κ ε r) x -
          (c : ℂ) • (equivOfLower (Aop D x) κ hlow).symm (Ub x sv)) := by abel
  rw [e]
  refine (norm_add_le _ _).trans ?_
  unfold eFin at ht
  linarith

/-- **The final leaf of every implementation at a good estimate** (equations `qls:eq:qrange`,
`qls:eq:finalprob`): if the implemented final attempt changes the decoded amplitude at the input
by at most `e_fin = ε/1000 - δ₀`, the decoded amplitude is within `ε/1000` of `c A⁻¹ b`
(`impl_final_amp`), so `1000` attempts succeed with probability at least `97/100` and the
output is within `ε/50` of the normalised solution. -/
theorem impl_final_good (D : NativeSparseBlockEncoding.Data X n Z s) (x : X) (κ ε : ℝ)
    (hκ : 1 ≤ κ) (hA1 : ‖Aop D x‖ ≤ 1) (hlow : ∀ v, ‖v‖ ≤ κ * ‖Aop D x v‖)
    (Ub : X → V0 →L[ℂ] V0) (hUb : ∀ x, IsUnitary (Ub x)) (sv : V0) (hsv : ‖sv‖ = 1)
    (hε : 0 < ε) (hε1 : ε ≤ 1 / 10) (r : ℝ)
    (hr1 : rho D x κ hκ hlow Ub sv (stagesM κ) ≤ r)
    (hr2 : r ≤ 4 * rho D x κ hκ hlow Ub sv (stagesM κ))
    (t : TestRun (physOracle D Ub (TcF s κ ε)) V0)
    (ht : ‖amp t x - amp (finalRunF D Ub sv κ ε r) x‖ ≤ eFin s κ ε) :
    97 / 100 ≤ (repeatLeaf t 1000).successMass x ∧
      ‖leafDir x (repeatLeaf t 1000) -
        ODEStateNormalization.unitDirection ((equivOfLower (Aop D x) κ hlow).symm (Ub x sv))‖ ≤
        ε / 50 := by
  have hκ0 : 0 < κ := by linarith
  have hρ := rho_bounds D x κ hκ hA1 hlow Ub hUb sv hsv (stagesM κ)
  have hr8 : 1 / 8 ≤ r := by linarith
  have hInv := equivOfLower_symm_norm (Aop D x) κ hκ0.le hlow
  have hA := normA D x κ hlow hA1
  obtain ⟨c, hclo, -, herr'⟩ := impl_final_amp D x κ ε hκ hA1 hlow Ub hUb sv hsv r hr8 t ht
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
  have hsm : κ * sig (stagesM κ) ≤ 1 := by
    have := sig_stages_le κ hκ
    rw [le_div_iff₀ hκ0] at this
    linarith
  have hp1 : ‖amp t x‖ ^ 2 ≤ 1 := by
    have h := amp_norm_le t x (t.circuit.eval_unitary (physOracle_unitary D Ub hUb _) x)
    nlinarith [norm_nonneg (amp t x)]
  have hdir : leafDir x (repeatLeaf t 1000) =
      ODEStateNormalization.unitDirection (amp t x) := repeatLeaf_leafDir t 999 x
  rw [repeatLeaf_successMass, hdir]
  exact final_good_arith κ ε (sig (stagesM κ)) _ r c _ _ hκ hε hε1 (sig_nonneg _) hsm hρ.1 hr1
    hr2 hlo hhi hclo herr' hp1

/-! ### Success and output guarantee -/

/-- **Correctness for one input with approximate known gates** (Theorem `qls:thm:main`,
success and accuracy): every implementation whose tests and final attempts change the success
vector at the input by at most `e_test` and `e_fin` has unitary runs, success probability at
least `2/3` and conditional trace distance at most `ε` from the normalised solution. -/
theorem impl_correctness (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (hUb : ∀ x, IsUnitary (Ub x)) (sv : V0) (hsv : ‖sv‖ = 1) (κ ε : ℝ) (hκ : 1 ≤ κ)
    (hε : 0 < ε) (hε1 : ε ≤ 1 / 10)
    (test : ℕ → ℝ → TestRun (physOracle D Ub (TcF s κ ε)) (PrivO n))
    (fin : ℝ → TestRun (physOracle D Ub (TcF s κ ε)) V0)
    (x : X) (hA1 : ‖Aop D x‖ ≤ 1) (hlow : ∀ v, ‖v‖ ≤ κ * ‖Aop D x v‖)
    (htest : ∀ j r, ‖amp (test j r) x - amp (testRunF D Ub sv κ ε j r) x‖ ≤
      eTest s (stageOf κ j))
    (hfin : ∀ r, ‖amp (fin r) x - amp (finalRunF D Ub sv κ ε r) x‖ ≤ eFin s κ ε) :
    (implAlgorithm κ ε test fin).RunsUnitary x ∧
      2 / 3 ≤ (implAlgorithm κ ε test fin).successMass x ∧
      ∀ y : V0, Aop D x y = Ub x sv →
        ODEMixedOutput.IsDensity ((implAlgorithm κ ε test fin).conditionalDensity x) ∧
          ∃ h : ((implAlgorithm κ ε test fin).conditionalDensity x -
              ODEMixedOutput.pureOperator
                (ODEStateNormalization.unitDirection y)).toLinearMap.IsSymmetric,
            ODEMixedOutput.hermitianTraceDistance
              ((implAlgorithm κ ε test fin).conditionalDensity x)
              (ODEMixedOutput.pureOperator (ODEStateNormalization.unitDirection y)) h ≤ ε := by
  set v := ODEStateNormalization.unitDirection ((equivOfLower (Aop D x) κ hlow).symm (Ub x sv))
    with hv
  have hO := physOracle_unitary D Ub hUb (TcF s κ ε)
  have htU : ∀ j r, IsUnitary ((test j r).circuit.eval x) :=
    fun j r => (test j r).circuit.eval_unitary hO x
  have hU : (implAlgorithm κ ε test fin).RunsUnitary x :=
    Estimator.stages_runsUnitary x _ _ _ _ κ htU _ _
  -- good leaves at good estimates
  have hgoodr : ∀ r, rho D x κ hκ hlow Ub sv (stagesM κ) ≤ r →
      r ≤ 4 * rho D x κ hκ hlow Ub sv (stagesM κ) →
        GoodLeaf x v ε (repeatLeaf (fin r) 1000) := by
    intro r hr1 hr2
    obtain ⟨hm, hd⟩ := impl_final_good D x κ ε hκ hA1 hlow Ub hUb sv hsv hε hε1 r hr1 hr2
      (fin r) (hfin r)
    exact ⟨hm, fun _ => ⟨1, norm_one, by rw [one_smul]; exact hd⟩⟩
  -- the bad mass
  have hbad : (implAlgorithm κ ε test fin).reach (fun p => ¬ GoodLeaf x v ε p) x ≤ ε / 500 := by
    have h := algorithm_bad_le_tol x test (Tree.indicator (fun p => ¬ GoodLeaf x v ε p))
      (Tree.indicator_nonneg _) (Tree.indicator_le_one _) (fun r => repeatLeaf (fin r) 1000)
      (reps κ ε) (stagesM κ) κ (rho D x κ hκ hlow Ub sv) (zeta κ ε)
      (rho_zero D x κ hκ hlow Ub hUb sv hsv)
      (fun j _ => rho_bounds D x κ hκ hA1 hlow Ub hUb sv hsv j)
      (fun j hj1 _ => rho_ladder D x κ hκ hA1 hlow Ub sv j hj1) (zeta_pos κ ε hε)
      (reps_spec κ ε) htU
      (fun j r _ hjm hr => impl_test_bounds D x κ ε hκ hA1 hlow Ub hUb sv hsv j hjm r hr
        (test j r) (htest j r))
      (fun r hr1 hr2 => Tree.indicator_of_neg (not_not.mpr (hgoodr r hr1 hr2)))
    exact h.trans (sum_zeta_le κ ε hε)
  -- success
  have hleaf1 : (implAlgorithm κ ε test fin).AllLeaves (fun p =>
      0 ≤ p.successMass x ∧ (GoodLeaf x v ε p → 97 / 100 ≤ p.successMass x)) :=
    Estimator.stages_allLeaves _ _ _ _ κ _
      (fun r => ⟨(repeatLeaf_spec (fin r) 999 x ((fin r).circuit.eval_unitary hO x)).1,
        fun hg => hg.1⟩) _ _
  have hsucc := Tree.successMass_ge x _ hU (97 / 100) (GoodLeaf x v ε) hleaf1
  have hcompl := Tree.reach_add_compl (GoodLeaf x v ε) x (implAlgorithm κ ε test fin)
  have hM : 2 / 3 ≤ (implAlgorithm κ ε test fin).successMass x := by
    nlinarith
  refine ⟨hU, hM, ?_⟩
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
  have hleaf2 : (implAlgorithm κ ε test fin).AllLeaves (fun p =>
      0 ≤ p.successMass x ∧ p.successMass x ≤ 1 ∧
      (p.successMass x ≠ 0 → ‖leafDir x p‖ = 1) ∧
      p.successDensity x =
        ((p.successMass x : ℝ) : ℂ) • ODEMixedOutput.pureOperator (leafDir x p) ∧
      (GoodLeaf x v ε p → p.successMass x ≠ 0 →
        ∃ ω : ℂ, ‖ω‖ = 1 ∧ ‖ω • leafDir x p - v‖ ≤ ε / 50)) :=
    Estimator.stages_allLeaves _ _ _ _ κ _ (fun r => by
      obtain ⟨h0, h1, h2, h3⟩ := repeatLeaf_spec (fin r) 999 x ((fin r).circuit.eval_unitary hO x)
      exact ⟨h0, h1, h2, h3, fun hg => hg.2⟩) _ _
  obtain ⟨hdens, hsym, hdist⟩ := Tree.output_guarantee x _ hU v hvn (ε / 50) (by positivity)
    (GoodLeaf x v ε) (leafDir x) hleaf2 (by linarith)
  refine ⟨hdens, hsym, hdist.trans ?_⟩
  have hR := Tree.reach_nonneg (fun p => ¬ GoodLeaf x v ε p) x _ hU
  have : (implAlgorithm κ ε test fin).reach (fun p => ¬ GoodLeaf x v ε p) x /
      (implAlgorithm κ ε test fin).successMass x ≤ (ε / 500) / (2 / 3) := by
    apply div_le_div₀ (by positivity) hbad (by norm_num) hM
  linarith

end

end ChebyshevLinearSystemFinite
