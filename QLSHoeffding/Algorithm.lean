import QLSHoeffding.Schedule
import ChebyshevLinearSystemFinite.Correctness

/-!
# The finite-degree Chebyshev protocol with Hoeffding's repetition schedule

`implAlgorithmH κ ε test fin` is the protocol `ChebyshevLinearSystemFinite.implAlgorithm`
(the released classical control of the norm estimator: `m = ⌈log₂ ⌈κ⌉⌉` stages, five candidates
per stage, the thresholds and the clipping, then at most `1000` final attempts) with the
repetition counts `n_j = ⌈log(10/ζ_j)/(2 · 0.0099²)⌉` of equation `qls:eq:hoeffding`
(`repsH`) in place of the released `⌈4 log(2/ζ)/t²⌉`. `algorithmFH` is its exact-gate
instance with the ideal finite-degree runs.

`impl_correctnessH`: for every implementation whose tests and final attempts change the success
vector at the input by at most the manuscript's allowances `e_test`, `e_fin`, unitary runs,
success probability at least `2/3` and conditional trace distance at most `ε` from the
normalised solution, through the estimator analysis with tail budgets
(`algorithm_bad_le_tail`) and Hoeffding's inequality (`repsH_tailOK`).
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 2048

namespace QLSHoeffding

noncomputable section
open ContinuousLinearMap SparseHamiltonian SparseLinearSystems OracleCircuit
  HilbertAugmentation Augmented SparseBranch LogicalWalk Step Facts Protocol Endpoint
  ChebyshevFilter ChebyshevLinearSystem ChebyshevLinearSystemFinite
open scoped InnerProduct

/-! ### The protocol with implemented runs -/

section Generic

variable {K E F X L : Type*}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  {O : L → X → K →L[ℂ] K}

/-- **The protocol with Hoeffding's repetition schedule**: the classical control of the released
estimator with `n_j = repsH κ ε j` fresh runs per candidate, the implemented test runs
`test j r`, and the final leaf of at most `1000` fresh implemented final attempts `fin r`. -/
def implAlgorithmH (κ ε : ℝ) (test : ℕ → ℝ → TestRun O F) (fin : ℝ → TestRun O E) :
    Protocol.Tree O F E :=
  Estimator.algorithm test (fun r => repeatLeaf (fin r) 1000) (repsH κ ε) (stagesM κ) κ

end Generic

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s : ℕ}

local notation "V0" => EuclideanSpace ℂ n

/-- **The finite-degree algorithm with exact gates and Hoeffding's repetition schedule.** -/
def algorithmFH (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0) (sv : V0)
    (κ ε : ℝ) : Protocol.Tree (physOracle D Ub (TcF s κ ε)) (PrivO n) V0 :=
  implAlgorithmH κ ε (testRunF D Ub sv κ ε) (finalRunF D Ub sv κ ε)

/-- **Correctness for one input with Hoeffding's repetition schedule and approximate known
gates** (Theorem `qls:thm:main`, success and accuracy, with the count of equation
`qls:eq:hoeffding`): every implementation whose tests and final attempts change the success
vector at the input by at most `e_test` and `e_fin` has unitary runs, success probability at
least `2/3` and conditional trace distance at most `ε` from the normalised solution. -/
theorem impl_correctnessH (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (hUb : ∀ x, IsUnitary (Ub x)) (sv : V0) (hsv : ‖sv‖ = 1) (κ ε : ℝ) (hκ : 1 ≤ κ)
    (hε : 0 < ε) (hε1 : ε ≤ 1 / 10)
    (test : ℕ → ℝ → TestRun (physOracle D Ub (TcF s κ ε)) (PrivO n))
    (fin : ℝ → TestRun (physOracle D Ub (TcF s κ ε)) V0)
    (x : X) (hA1 : ‖Aop D x‖ ≤ 1) (hlow : ∀ v, ‖v‖ ≤ κ * ‖Aop D x v‖)
    (htest : ∀ j r, ‖amp (test j r) x - amp (testRunF D Ub sv κ ε j r) x‖ ≤
      eTest s (stageOf κ j))
    (hfin : ∀ r, ‖amp (fin r) x - amp (finalRunF D Ub sv κ ε r) x‖ ≤ eFin s κ ε) :
    (implAlgorithmH κ ε test fin).RunsUnitary x ∧
      2 / 3 ≤ (implAlgorithmH κ ε test fin).successMass x ∧
      ∀ y : V0, Aop D x y = Ub x sv →
        ODEMixedOutput.IsDensity ((implAlgorithmH κ ε test fin).conditionalDensity x) ∧
          ∃ h : ((implAlgorithmH κ ε test fin).conditionalDensity x -
              ODEMixedOutput.pureOperator
                (ODEStateNormalization.unitDirection y)).toLinearMap.IsSymmetric,
            ODEMixedOutput.hermitianTraceDistance
              ((implAlgorithmH κ ε test fin).conditionalDensity x)
              (ODEMixedOutput.pureOperator (ODEStateNormalization.unitDirection y)) h ≤ ε := by
  set v := ODEStateNormalization.unitDirection ((equivOfLower (Aop D x) κ hlow).symm (Ub x sv))
    with hv
  have hO := physOracle_unitary D Ub hUb (TcF s κ ε)
  have htU : ∀ j r, IsUnitary ((test j r).circuit.eval x) :=
    fun j r => (test j r).circuit.eval_unitary hO x
  have hU : (implAlgorithmH κ ε test fin).RunsUnitary x :=
    Estimator.stages_runsUnitary x _ _ _ _ κ htU _ _
  -- good leaves at good estimates
  have hgoodr : ∀ r, rho D x κ hκ hlow Ub sv (stagesM κ) ≤ r →
      r ≤ 4 * rho D x κ hκ hlow Ub sv (stagesM κ) →
        GoodLeaf x v ε (repeatLeaf (fin r) 1000) := by
    intro r hr1 hr2
    obtain ⟨hm, hd⟩ := impl_final_good D x κ ε hκ hA1 hlow Ub hUb sv hsv hε hε1 r hr1 hr2
      (fin r) (hfin r)
    exact ⟨hm, fun _ => ⟨1, norm_one, by rw [one_smul]; exact hd⟩⟩
  -- the bad mass, with Hoeffding's counts
  have hbad : (implAlgorithmH κ ε test fin).reach (fun p => ¬ GoodLeaf x v ε p) x ≤
      ε / 500 := by
    have h := algorithm_bad_le_tail x test (Tree.indicator (fun p => ¬ GoodLeaf x v ε p))
      (Tree.indicator_nonneg _) (Tree.indicator_le_one _) (fun r => repeatLeaf (fin r) 1000)
      (repsH κ ε) (stagesM κ) κ (rho D x κ hκ hlow Ub sv) (zeta κ ε)
      (rho_zero D x κ hκ hlow Ub hUb sv hsv)
      (fun j _ => rho_bounds D x κ hκ hA1 hlow Ub hUb sv hsv j)
      (fun j hj1 _ => rho_ladder D x κ hκ hA1 hlow Ub sv j hj1) (zeta_pos κ ε hε)
      (repsH_tailOK κ ε hε) htU
      (fun j r _ hjm hr => impl_test_bounds D x κ ε hκ hA1 hlow Ub hUb sv hsv j hjm r hr
        (test j r) (htest j r))
      (fun r hr1 hr2 => Tree.indicator_of_neg (not_not.mpr (hgoodr r hr1 hr2)))
    exact h.trans (sum_zeta_le κ ε hε)
  -- success
  have hleaf1 : (implAlgorithmH κ ε test fin).AllLeaves (fun p =>
      0 ≤ p.successMass x ∧ (GoodLeaf x v ε p → 97 / 100 ≤ p.successMass x)) :=
    Estimator.stages_allLeaves _ _ _ _ κ _
      (fun r => ⟨(repeatLeaf_spec (fin r) 999 x ((fin r).circuit.eval_unitary hO x)).1,
        fun hg => hg.1⟩) _ _
  have hsucc := Tree.successMass_ge x _ hU (97 / 100) (GoodLeaf x v ε) hleaf1
  have hcompl := Tree.reach_add_compl (GoodLeaf x v ε) x (implAlgorithmH κ ε test fin)
  have hM : 2 / 3 ≤ (implAlgorithmH κ ε test fin).successMass x := by
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
  have hleaf2 : (implAlgorithmH κ ε test fin).AllLeaves (fun p =>
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
  have : (implAlgorithmH κ ε test fin).reach (fun p => ¬ GoodLeaf x v ε p) x /
      (implAlgorithmH κ ε test fin).successMass x ≤ (ε / 500) / (2 / 3) := by
    apply div_le_div₀ (by positivity) hbad (by norm_num) hM
  linarith

end

end QLSHoeffding
