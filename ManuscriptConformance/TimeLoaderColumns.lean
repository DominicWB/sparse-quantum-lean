import ManuscriptConformance.RobustLoaderColumns
import ManuscriptConformance.ODETime
import RepresentedSampleODE.Zero
import RepresentedSampleODE.Regular

/-!
# Theorem `ode:thm:time` with a loader specified on its clean columns (item D1)

The conformance theorem `ManuscriptConformance.ode_thm_time` is built on
`RepresentedSampleODE.robust_approx_solver_nonneg_regular` with exact preparations (`δ = 0`). That
solver covers every `T ≥ 0`: the zero cases `T = 0` or `η_H + R η_D = 0` with the identity SELECT
(`robust_zero_core`), the others with the propagated SELECT (`robust_propagated_solver`). Both use
the public trial family `MeshNative.publicTrials`, but state it only existentially. Here both
families are exposed, and the column transfer of `MeshLoaderColumns` is applied to them.

The loading oracle is any unitary `Lo` on the whole branch register (source label, LCHS label and
data). It is specified only on the clean columns `|a, τ⟩|seed⟩` of the labels with nonzero source
vectors, with the released phase convention, and is not assumed to preserve the labels elsewhere.

* `mesh_zero_time_core_public`, `mesh_zero_generator_core_public`, `robust_zero_core_public`
  (`RobustPublicOutcome`): the released zero cores with their public trial family named. They are
  the released proofs; only the conclusion changes, and the instance budget is `RobustBudget` (it
  contains the released one, `RobustBudget.released`).
* `RobustPublicOutcome.columns`: the column transfer (`MeshOracles.columns_certificate`) of a
  public outcome for the label-controlled family `columnLoader Lo` to `RobustOutcomeColumns` for
  `Lo`.
* `robust_solver_nonneg_columns`: `RobustOutcomeColumns` for every `T ≥ 0`.
* `robust_solver_nonneg_regular_columns` (`RegularOutcomeColumns`): the same for integrable pieces
  (`RegularPieces`), mild solutions (`MildSolution`), the certificate on the propagated vector
  integral and the two sampling budgets of `ode:thm:time`. These are the hypotheses of
  `RegularApproxOutcome` with exact preparations.
* `ManuscriptConformance.ode_thm_time_columns`: Theorem `ode:thm:time` (the statement of
  `ode_thm_time`) for the protocol over `P_w`, `Lo`, `P_w†` and the sampled-time matrix oracle:
  success at least `2/3`, conditional trace distance at most `ε`, and the matrix-query and
  source-call bounds of `ode_thm_time` with the same constant.

Scope: the exact case of item D1. Approximate columns and the approximate-preparation forms
(`ode_thm_time_approx` and the forms on temporary work registers) keep the label-controlled
loader, and the released label-controlled forms are unchanged.
-/

set_option autoImplicit false

namespace SparseHamiltonian.RepresentedSampleODE

noncomputable section
open ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding Set MeasureTheory
open TimeDependentExtensions SparseHamiltonian.GeneralSourceExtensions
open SparseHamiltonian.TimeDependentODE (Accretive SolvesODE ratio accuracy radius precision
  lipschitz Index lchsCoefficients retarget)
open SparseHamiltonian.GeneralSourceODE (startTime sources phases phases_norm mass_sources
  phased_isometry phased_prepares nodeTable)
open SparseHamiltonian.GeneralSourceExtensions.Mesh (meshScale sampleError refinementError
  meshDurations meshDurations_nonneg meshDurations_le meshTable tableFamily IsMeshPropagator
  sampleError_nonneg refinementError_nonneg meshScale_nonneg branchEvolution_eq_tableFamily
  meshTarget meshDurations_eq_zero evolution_congr_one)
open SparseHamiltonian.TimeDependentODE.GaussianLCHS (productFamily)
open scoped BigOperators InnerProduct
set_option maxRecDepth 4096
set_option synthInstance.maxSize 8192

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s M : ℕ}

/-! ### The zero cases with their public trial family -/

set_option maxHeartbeats 8000000 in
/-- **`mesh_zero_time_core` with its public trial family exposed** (`RobustPublicOutcome`): at
`T = 0`, without positivity of the represented samples, the public trial family
`MeshNative.publicTrials` with the identity SELECT on `N` slots satisfies the released complete
certificate for every instance with `RobustBudget` (which contains the released budget,
`RobustBudget.released`). The released proof; only the conclusion names the trial family. -/
theorem mesh_zero_time_core_public (D : Data (X × Fin M) n Z s) (hM : 0 < M) (t : ℕ → ℝ)
    {N : ℕ} (hN : 0 < N) (etaH etaD T gbar cq ε : ℝ) {m : ℕ} (v : Fin m → ℝ) (ω : Fin m → ℂ)
    (hH : 0 ≤ etaH) (hDiss : 0 ≤ etaD) (hT0 : T = 0) (hg : 1 ≤ gbar) (hcq : 1 ≤ cq)
    (hε : 0 < ε) (hεOne : ε ≤ 1) (hmesh : IsMesh t M T) (hv : ∀ i, v i ∈ Icc 0 T)
    (Pw : X → GeneralSourceODE.Weights.LabelOp (Option (Fin m))) (hPw : ∀ x, IsUnitary (Pw x))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ : ∀ x a, IsUnitary (J x a))
    (seed : EuclideanSpace ℂ n) (hSeed : ‖seed‖ = 1) :
    RobustPublicOutcome D hM t N etaH etaD T gbar cq ε v ω Pw J seed := by
  have hT : 0 ≤ T := hT0.ge
  set g : ℝ := cq * gbar with hgdef
  have hg1 : 1 ≤ g := by nlinarith
  have hg' : 1 ≤ ratio g := by unfold ratio; linarith
  have hε' : 0 < accuracy ε := by unfold accuracy; linarith
  have hε'One : accuracy ε ≤ 1 := by unfold accuracy; linarith
  have hε'Half : accuracy ε ≤ 1 / 2 := by unfold accuracy; linarith
  have hν : 0 < precision g ε := ImprovedODEQueryBudget.precision_pos _ _ hg' hε'
  let σ : ℕ → Fin M := pieceOf t T N hM
  have hu0 : ∀ a r, 0 ≤ meshDurations t T v a r := meshDurations_nonneg hmesh hT v
  have huT : ∀ a r, meshDurations t T v a r ≤ T := meshDurations_le hmesh hT v
  -- One public Gaussian table for every product family.
  have hL : 0 ≤ lipschitz D T :=
    mul_nonneg hT (mul_nonneg (Nat.cast_nonneg s) D.scale_pos.le)
  obtain ⟨_hGrid, _hNodes, hMass, hApprox⟩ := TimeDependentODE.GaussianLCHS.table_certificate
    (fun y : X × Option (Fin m) => tableFamily D σ N (meshDurations t T v) y.1 y.2)
    (fun y z => GeneralSourceExtensions.Mesh.tableFamily_analyticAt D σ N _ y.1 y.2 z)
    (fun y z _ => by
      rw [tableFamily_zero_time D σ N hT0 v y.1 y.2 z]
      exact norm_one_op_le)
    (lipschitz D T) hL (fun y k l =>
      GeneralSourceExtensions.Mesh.tableFamily_lipschitz D σ hN _ hu0 huT y.1 y.2 k l)
    (ratio g) (accuracy ε) hg' hε' hε'One
  have hc : ODECoherentLCU.coefficientMass (lchsCoefficients D T g ε) = 3 :=
    ODECoefficientPadding.coefficientMass_eq _ 3 hMass
  -- Every branch product is the identity.
  have hOne : ∀ (x : X) (a' : GeneralSourceODE.Native.Label (Index D T g ε) m),
      MeshSelect.branchEvolution D σ N (nodeTable D T g ε m) (meshTable t T v) x a' = 1 := by
    intro x a'
    apply ZeroTimeRemarks.ODEMesh.branchEvolution_eq_one
    left
    intro r
    exact meshDurations_eq_zero hT0 v a'.1 r
  -- The identity SELECT on the clean encoding at the rescaling `γ = 1`.
  let i0 : Index D T g ε := Sum.inr false
  let ρ : ℝ := etaH + radius g ε * etaD
  let d := TimeDependentODE.Select.degree (s : ℝ) 1 ρ T (precision g ε) N
  let E : GeneralSourceODE.Native.SourceSpace (Index D T g ε) n m →L[ℂ]
      MeshNative.MatrixSpace (Index D T g ε) n Z m M N d :=
    MeshSelect.alignedInput D hM σ (GeneralSourceODE.Native.dummy hM i0 m) N 1 ρ T
      (precision g ε)
  have hEiso : E† ∘L E = 1 := ZeroTimeRemarks.ODEMesh.alignedInput_isometry D hM σ _ N 1 ρ T _
  let pN : MultiOracleCircuit.Program
      (MeshNative.matrixOracle (ι := Index D T g ε) D m N d) :=
    MultiOracleCircuit.Program.identity
  let c := lchsCoefficients D T g ε
  have hcpos : 0 < ODECoherentLCU.coefficientMass c := by
    change 0 < ODECoherentLCU.coefficientMass (lchsCoefficients D T g ε)
    rw [hc]
    norm_num
  have hsc : 0 < ODECoherentLCU.coefficientMass
      (GeneralSourceODE.Compiled.seedCoefficients (N := m) c) := by
    rw [GeneralSourceODE.Compiled.seedCoefficients_mass]
    exact hcpos
  have hSeedUnit := ODECompiledSource.seed_unit E
    (GeneralSourceODE.Compiled.seedCoefficients c) hEiso hsc seed hSeed
  have hOutput := ODECompiledSource.output_isometry E
    (GeneralSourceODE.Compiled.seedCoefficients c) hEiso hsc
  let q := MeshNative.publicTrials D hM i0 m N d pN Pw J (phases ω) E hEiso c seed
    hSeedUnit hOutput
  have hΘ : 0 ≤ ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) (ratio g) (accuracy ε) :=
    ImprovedODEQueryBudget.theta_nonneg _ _ _ _ (mul_nonneg hT hH) (mul_nonneg hT hDiss)
      hg' hε' hε'One
  have hLog : 0 ≤ ImprovedODEQueryBudget.logBudget (ratio g) (accuracy ε) :=
    le_trans zero_le_one (ImprovedODEQueryBudget.logBudget_ge_one _ _ hg' hε' hε'One)
  have hq : (pN.count : ℝ) ≤ 10616832 * ImprovedODEQueryBudget.queryShape (s : ℝ)
      (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) (ratio g) (accuracy ε))
      (ImprovedODEQueryBudget.logBudget (ratio g) (accuracy ε)) := by
    rw [MultiOracleCircuit.Program.count_identity, Nat.cast_zero]
    exact mul_nonneg (by norm_num) (ImprovedODEQueryBudget.queryShape_nonneg _ _ _ hΘ hLog)
  have hOracle := MeshNative.physicalOracle_unitary (ι := Index D T g ε) D m N d Pw hPw J hJ
    (phases ω) (phases_norm ω)
  refine ⟨d, E, hEiso, pN, hSeedUnit, hOutput, ?_⟩
  intro x G b sol bv U ζ _hG _hGint hU hW hLoad₀ hLoad hMassB hCert hTarget hB hRobust
  have hBudget := hRobust.released hmesh (by linarith)
  -- The represented target is the source sum.
  let z := sources (sol 0) bv ω
  let y := meshTarget D hM t T N v x (sol 0) bv ω
  set Bs := meshScale sol b t with hBs
  set K : ℝ := sampleError D x t G + refinementError D t T N with hK
  have hK0 : 0 ≤ K := add_nonneg (sampleError_nonneg D x hmesh G)
    (refinementError_nonneg D t T N)
  have hTargetErr : ‖(U 0 (sol 0) T + ∑ i, ω i • U (v i) (bv i) T) - y‖ ≤
      K * ODESourceBranches.mass z := by
    rw [zero_time_target_error D hM hT0 N G U hU v hv ω x (sol 0) bv, norm_zero]
    exact mul_nonneg hK0 (ODESourceBranches.mass_nonneg z)
  have hBs0 : 0 ≤ Bs := meshScale_nonneg hmesh sol b
  have hErr : ‖sol T - y‖ ≤ (ζ + cq * K) * Bs := by
    have hsplit : sol T - y =
        (sol T - U 0 (sol 0) T - ∑ i, ω i • U (v i) (bv i) T) +
          ((U 0 (sol 0) T + ∑ i, ω i • U (v i) (bv i) T) - y) := by
      abel
    rw [hsplit]
    have hMassK : K * ODESourceBranches.mass z ≤ cq * K * Bs := by
      calc
        K * ODESourceBranches.mass z ≤ K * (cq * Bs) := mul_le_mul_of_nonneg_left hMassB hK0
        _ = cq * K * Bs := by ring
    calc
      _ ≤ ‖sol T - U 0 (sol 0) T - ∑ i, ω i • U (v i) (bv i) T‖ +
          ‖(U 0 (sol 0) T + ∑ i, ω i • U (v i) (bv i) T) - y‖ := norm_add_le _ _
      _ ≤ ζ * Bs + K * ODESourceBranches.mass z := add_le_add hCert hTargetErr
      _ ≤ ζ * Bs + cq * K * Bs := add_le_add le_rfl hMassK
      _ = (ζ + cq * K) * Bs := by ring
  have hErrBudget : (ζ + cq * K) * Bs ≤ ε * Bs / (2000 * gbar) := by
    have h := mul_le_mul_of_nonneg_right hBudget hBs0
    calc
      (ζ + cq * K) * Bs ≤ ε / (2000 * gbar) * Bs := h
      _ = ε * Bs / (2000 * gbar) := by ring
  obtain ⟨hy, hBy, hDir⟩ := TimeDependentODE.Sampling.target_budget (sol T) y Bs gbar ε _ hg
    hε hεOne hTarget hB hErr hErrBudget
  have hNorm : ‖y‖ ≤ ODESourceBranches.mass z := by
    unfold y meshTarget ODESourceBranches.mass
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
    rw [tableFamily_zero_time D _ N hT0 v x, one_apply_eq_self]
  have hz : 0 < ODESourceBranches.mass z := ODESourceBranches.mass_pos_of_solution z y hy hNorm
  have hBudget' : ODESourceBranches.mass z ≤ ratio g * ‖y‖ := by
    have hcq0 : 0 ≤ cq := by linarith
    calc
      ODESourceBranches.mass z ≤ cq * Bs := hMassB
      _ ≤ cq * (2 * gbar * ‖y‖) := mul_le_mul_of_nonneg_left hBy hcq0
      _ = ratio g * ‖y‖ := by rw [hgdef]; unfold ratio; ring
  -- Hypotheses of the released actual-source certificate.
  have hJph : ∀ a, (GeneralSourceODE.Compiled.phased (J x) (phases ω) a)† ∘L
      GeneralSourceODE.Compiled.phased (J x) (phases ω) a = 1 :=
    phased_isometry (J x) (hJ x) ω
  have hPrep := phased_prepares (J x) (sol 0) bv ω seed hLoad₀ hLoad
  have hSim : ‖pN.eval x ∘L E - E ∘L WeightedClock.diagonal
      (fun a' : Option (Fin m) × Index D T g ε =>
        MeshSelect.branchEvolution D σ N (nodeTable D T g ε m) (meshTable t T v) x
          (a'.1, a'.2))‖ ≤ ImprovedODEQueryBudget.precision (ratio g) (accuracy ε) := by
    have hDiag : WeightedClock.diagonal
        (fun a' : Option (Fin m) × Index D T g ε =>
          MeshSelect.branchEvolution D σ N (nodeTable D T g ε m) (meshTable t T v) x
            (a'.1, a'.2)) = 1 := by
      simp only [hOne]
      exact WeightedClock.diagonal_one
    rw [hDiag, MultiOracleCircuit.Program.eval_identity, sub_eq_zero.mpr, norm_zero]
    · exact hν.le
    · rfl
  have hLCHS : ∀ a', ‖(∑ i, lchsCoefficients D T g ε i •
      MeshSelect.branchEvolution D σ N (nodeTable D T g ε m) (meshTable t T v) x (a', i)) -
        tableFamily D σ N (meshDurations t T v) x a' (-Complex.I)‖ ≤
          2 * ImprovedODEQueryBudget.precision (ratio g) (accuracy ε) := by
    intro a'
    have hsum : (∑ i, lchsCoefficients D T g ε i •
        MeshSelect.branchEvolution D σ N (nodeTable D T g ε m) (meshTable t T v) x (a', i)) =
          ∑ j, TimeDependentODE.GaussianLCHS.coefficients (lipschitz D T) (ratio g)
              (accuracy ε) j •
            tableFamily D σ N (meshDurations t T v) x a'
              (TimeDependentODE.GaussianLCHS.nodes (lipschitz D T) (ratio g) (accuracy ε) j :
                ℂ) := by
      have hbr : ∀ i, MeshSelect.branchEvolution D σ N (nodeTable D T g ε m)
          (meshTable t T v) x (a', i) =
            tableFamily D σ N (meshDurations t T v) x a' (nodeTable D T g ε m (a', i) : ℂ) :=
        fun i => branchEvolution_eq_tableFamily D σ N (meshDurations t T v) x
          (nodeTable D T g ε m) a' i
      simp only [hbr]
      exact TimeDependentODE.Sampling.padded_sum _ _ _
    rw [hsum]
    exact hApprox (x, a')
  have hQuad : ‖(∑ a', tableFamily D σ N (meshDurations t T v) x a' (-Complex.I) (z a')) - y‖ ≤
      ImprovedODEQueryBudget.precision (ratio g) (accuracy ε) * ODESourceBranches.mass z := by
    have hsum : (∑ a', tableFamily D σ N (meshDurations t T v) x a' (-Complex.I) (z a')) = y :=
      rfl
    rw [hsum, sub_self, norm_zero]
    exact mul_nonneg hν.le (ODESourceBranches.mass_nonneg z)
  have hCertS : ODEActualSourceError.Certificate E z c
      (GeneralSourceODE.Compiled.phased (J x) (phases ω)) (pN.eval x) seed y (ratio g)
        (accuracy ε) :=
    ODEActualSourceError.actual_source_certificate E hEiso z c hc
      (GeneralSourceODE.Compiled.phased (J x) (phases ω)) hJph seed hSeed hPrep (pN.eval x)
      (pN.eval_unitary (MeshNative.matrixOracle_unitary D m N d) x)
      (fun a' i => MeshSelect.branchEvolution D σ N (nodeTable D T g ε m)
        (meshTable t T v) x (a', i))
      (fun a' => tableFamily D σ N (meshDurations t T v) x a' (-Complex.I)) y (ratio g)
      (accuracy ε) hy hg' hε' hε'Half hNorm hBudget' hSim hLCHS hQuad
  -- The released primitive trial certificate, then the solution direction.
  have hTrial := MeshNative.trial_certificate D hM i0 m N d pN Pw hPw J hJ (phases ω)
    (phases_norm ω) E hEiso z c hcpos seed y hSeed
    (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) (ratio g) (accuracy ε))
    (ImprovedODEQueryBudget.logBudget (ratio g) (accuracy ε)) (ratio g) (accuracy ε) hg' x
    hz hW hCertS hq hSeedUnit hOutput
  have hFinal := retarget (η' := ε / 500) hTrial hDir (by unfold accuracy; linarith)
  exact ODECompleteTrial.of_trialCertificate
    (fun j => (q j).eval_unitary hOracle x) hε.le hTarget hFinal

set_option maxHeartbeats 8000000 in
open SparseHamiltonian.GeneralSourceExtensions.Mesh in
/-- **`mesh_zero_generator_core` with its public trial family exposed** (`RobustPublicOutcome`):
if `T = 0` or `η_H + R η_D = 0` and the represented dissipative parts are positive, the public
trial family `MeshNative.publicTrials` with the identity SELECT on `N` slots satisfies the released
complete certificate for every instance with `RobustBudget`. The released proof; only the
conclusion names the trial family. -/
theorem mesh_zero_generator_core_public (D : Data (X × Fin M) n Z s) (hM : 0 < M) (t : ℕ → ℝ)
    {N : ℕ} (hN : 0 < N) (etaH etaD T gbar cq ε : ℝ) {m : ℕ} (v : Fin m → ℝ) (ω : Fin m → ℂ)
    (hH : 0 ≤ etaH) (hDiss : 0 ≤ etaD) (hT : 0 ≤ T)
    (hZero : T = 0 ∨ etaH + radius (cq * gbar) ε * etaD = 0) (hg : 1 ≤ gbar) (hcq : 1 ≤ cq)
    (hε : 0 < ε) (hεOne : ε ≤ 1) (hmesh : IsMesh t M T) (hv : ∀ i, v i ∈ Icc 0 T)
    (hrH : ∀ y i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix y) i j‖ ^ 2 ≤ etaH ^ 2)
    (hrD : ∀ y i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix y) i j‖ ^ 2 ≤ etaD ^ 2)
    (hPSD : ∀ (y : X × Fin M) (w : EuclideanSpace ℂ n), 0 ≤ (inner ℂ w
      (SparseStateOverlap.matrixOperator (ODEMatrixEnergy.dissipativePart (D.matrix y)) w)).re)
    (Pw : X → GeneralSourceODE.Weights.LabelOp (Option (Fin m))) (hPw : ∀ x, IsUnitary (Pw x))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ : ∀ x a, IsUnitary (J x a))
    (seed : EuclideanSpace ℂ n) (hSeed : ‖seed‖ = 1) :
    RobustPublicOutcome D hM t N etaH etaD T gbar cq ε v ω Pw J seed := by
  set g : ℝ := cq * gbar with hgdef
  have hg1 : 1 ≤ g := by nlinarith
  have hg' : 1 ≤ ratio g := by unfold ratio; linarith
  have hε' : 0 < accuracy ε := by unfold accuracy; linarith
  have hε'One : accuracy ε ≤ 1 := by unfold accuracy; linarith
  have hε'Half : accuracy ε ≤ 1 / 2 := by unfold accuracy; linarith
  have hν : 0 < precision g ε := ImprovedODEQueryBudget.precision_pos _ _ hg' hε'
  let σ : ℕ → Fin M := pieceOf t T N hM
  have hu0 : ∀ a r, 0 ≤ meshDurations t T v a r := meshDurations_nonneg hmesh hT v
  have huT : ∀ a r, meshDurations t T v a r ≤ T := meshDurations_le hmesh hT v
  -- One public Gaussian table for every product family.
  have hL : 0 ≤ lipschitz D T :=
    mul_nonneg hT (mul_nonneg (Nat.cast_nonneg s) D.scale_pos.le)
  obtain ⟨_hGrid, _hNodes, hMass, hApprox⟩ := TimeDependentODE.GaussianLCHS.table_certificate
    (fun y : X × Option (Fin m) => tableFamily D σ N (meshDurations t T v) y.1 y.2)
    (fun y z => tableFamily_analyticAt D σ N _ y.1 y.2 z)
    (fun y z hz => tableFamily_norm_le_one D σ N _ hu0 hPSD y.1 y.2 z hz)
    (lipschitz D T) hL (fun y k l => tableFamily_lipschitz D σ hN _ hu0 huT y.1 y.2 k l)
    (ratio g) (accuracy ε) hg' hε' hε'One
  have hc : ODECoherentLCU.coefficientMass (lchsCoefficients D T g ε) = 3 :=
    ODECoefficientPadding.coefficientMass_eq _ 3 hMass
  -- Every branch product is the identity.
  have hOne : ∀ (x : X) (a' : GeneralSourceODE.Native.Label (Index D T g ε) m),
      MeshSelect.branchEvolution D σ N (nodeTable D T g ε m) (meshTable t T v) x a' = 1 := by
    intro x a'
    apply ZeroTimeRemarks.ODEMesh.branchEvolution_eq_one
    rcases hZero with hT0 | hρ
    · left
      intro r
      exact meshDurations_eq_zero hT0 v a'.1 r
    · right
      intro r
      have hRadius : 0 < radius g ε :=
        lt_of_lt_of_le (by norm_num : (0 : ℝ) < 4)
          (ODEGaussianParameters.radius_ge_four _ _ hg' hε' hε'One)
      exact ODEZeroEnergy.matrix_zero_of_effective_energy (D.matrix (x, r)) etaH etaD
        (radius g ε) hH hDiss hRadius hρ (hrH (x, r)) (hrD (x, r))
  -- The identity SELECT on the clean encoding at the rescaling `γ = 1`.
  let i0 : Index D T g ε := Sum.inr false
  let ρ : ℝ := etaH + radius g ε * etaD
  let d := TimeDependentODE.Select.degree (s : ℝ) 1 ρ T (precision g ε) N
  let E : GeneralSourceODE.Native.SourceSpace (Index D T g ε) n m →L[ℂ]
      MeshNative.MatrixSpace (Index D T g ε) n Z m M N d :=
    MeshSelect.alignedInput D hM σ (GeneralSourceODE.Native.dummy hM i0 m) N 1 ρ T
      (precision g ε)
  have hEiso : E† ∘L E = 1 := ZeroTimeRemarks.ODEMesh.alignedInput_isometry D hM σ _ N 1 ρ T _
  let pN : MultiOracleCircuit.Program
      (MeshNative.matrixOracle (ι := Index D T g ε) D m N d) :=
    MultiOracleCircuit.Program.identity
  let c := lchsCoefficients D T g ε
  have hcpos : 0 < ODECoherentLCU.coefficientMass c := by
    change 0 < ODECoherentLCU.coefficientMass (lchsCoefficients D T g ε)
    rw [hc]
    norm_num
  have hsc : 0 < ODECoherentLCU.coefficientMass
      (GeneralSourceODE.Compiled.seedCoefficients (N := m) c) := by
    rw [GeneralSourceODE.Compiled.seedCoefficients_mass]
    exact hcpos
  have hSeedUnit := ODECompiledSource.seed_unit E
    (GeneralSourceODE.Compiled.seedCoefficients c) hEiso hsc seed hSeed
  have hOutput := ODECompiledSource.output_isometry E
    (GeneralSourceODE.Compiled.seedCoefficients c) hEiso hsc
  let q := MeshNative.publicTrials D hM i0 m N d pN Pw J (phases ω) E hEiso c seed
    hSeedUnit hOutput
  have hΘ : 0 ≤ ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) (ratio g) (accuracy ε) :=
    ImprovedODEQueryBudget.theta_nonneg _ _ _ _ (mul_nonneg hT hH) (mul_nonneg hT hDiss)
      hg' hε' hε'One
  have hLog : 0 ≤ ImprovedODEQueryBudget.logBudget (ratio g) (accuracy ε) :=
    le_trans zero_le_one (ImprovedODEQueryBudget.logBudget_ge_one _ _ hg' hε' hε'One)
  have hq : (pN.count : ℝ) ≤ 10616832 * ImprovedODEQueryBudget.queryShape (s : ℝ)
      (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) (ratio g) (accuracy ε))
      (ImprovedODEQueryBudget.logBudget (ratio g) (accuracy ε)) := by
    rw [MultiOracleCircuit.Program.count_identity, Nat.cast_zero]
    exact mul_nonneg (by norm_num) (ImprovedODEQueryBudget.queryShape_nonneg _ _ _ hΘ hLog)
  have hOracle := MeshNative.physicalOracle_unitary (ι := Index D T g ε) D m N d Pw hPw J hJ
    (phases ω) (phases_norm ω)
  refine ⟨d, E, hEiso, pN, hSeedUnit, hOutput, ?_⟩
  intro x G b sol bv U ζ hG hGint hU hW hLoad₀ hLoad hMassB hCert hTarget hB hRobust
  have hBudget := hRobust.released hmesh (by linarith)
  -- The represented target.
  let z := sources (sol 0) bv ω
  let y := meshTarget D hM t T N v x (sol 0) bv ω
  set Bs := meshScale sol b t with hBs
  have hTargetErr := mesh_target_error D hM hPSD x hmesh hT hN G hG hGint U hU v hv ω
    (sol 0) bv
  set K : ℝ := sampleError D x t G + refinementError D t T N with hK
  have hK0 : 0 ≤ K := add_nonneg (sampleError_nonneg D x hmesh G)
    (refinementError_nonneg D t T N)
  have hBs0 : 0 ≤ Bs := meshScale_nonneg hmesh sol b
  have hErr : ‖sol T - y‖ ≤ (ζ + cq * K) * Bs := by
    have hsplit : sol T - y =
        (sol T - U 0 (sol 0) T - ∑ i, ω i • U (v i) (bv i) T) +
          ((U 0 (sol 0) T + ∑ i, ω i • U (v i) (bv i) T) - y) := by
      abel
    rw [hsplit]
    have hMassK : K * ODESourceBranches.mass z ≤ cq * K * Bs := by
      calc
        K * ODESourceBranches.mass z ≤ K * (cq * Bs) := mul_le_mul_of_nonneg_left hMassB hK0
        _ = cq * K * Bs := by ring
    calc
      _ ≤ ‖sol T - U 0 (sol 0) T - ∑ i, ω i • U (v i) (bv i) T‖ +
          ‖(U 0 (sol 0) T + ∑ i, ω i • U (v i) (bv i) T) - y‖ := norm_add_le _ _
      _ ≤ ζ * Bs + K * ODESourceBranches.mass z := add_le_add hCert hTargetErr
      _ ≤ ζ * Bs + cq * K * Bs := add_le_add le_rfl hMassK
      _ = (ζ + cq * K) * Bs := by ring
  have hErrBudget : (ζ + cq * K) * Bs ≤ ε * Bs / (2000 * gbar) := by
    have h := mul_le_mul_of_nonneg_right hBudget hBs0
    calc
      (ζ + cq * K) * Bs ≤ ε / (2000 * gbar) * Bs := h
      _ = ε * Bs / (2000 * gbar) := by ring
  obtain ⟨hy, hBy, hDir⟩ := TimeDependentODE.Sampling.target_budget (sol T) y Bs gbar ε _ hg
    hε hεOne hTarget hB hErr hErrBudget
  have hNorm : ‖y‖ ≤ ODESourceBranches.mass z :=
    meshTarget_norm_le D hM hmesh hT N v hPSD x (sol 0) bv ω
  have hz : 0 < ODESourceBranches.mass z := ODESourceBranches.mass_pos_of_solution z y hy hNorm
  have hBudget' : ODESourceBranches.mass z ≤ ratio g * ‖y‖ := by
    have hcq0 : 0 ≤ cq := by linarith
    calc
      ODESourceBranches.mass z ≤ cq * Bs := hMassB
      _ ≤ cq * (2 * gbar * ‖y‖) := mul_le_mul_of_nonneg_left hBy hcq0
      _ = ratio g * ‖y‖ := by rw [hgdef]; unfold ratio; ring
  -- Hypotheses of the released actual-source certificate.
  have hJph : ∀ a, (GeneralSourceODE.Compiled.phased (J x) (phases ω) a)† ∘L
      GeneralSourceODE.Compiled.phased (J x) (phases ω) a = 1 :=
    phased_isometry (J x) (hJ x) ω
  have hPrep := phased_prepares (J x) (sol 0) bv ω seed hLoad₀ hLoad
  have hSim : ‖pN.eval x ∘L E - E ∘L WeightedClock.diagonal
      (fun a' : Option (Fin m) × Index D T g ε =>
        MeshSelect.branchEvolution D σ N (nodeTable D T g ε m) (meshTable t T v) x
          (a'.1, a'.2))‖ ≤ ImprovedODEQueryBudget.precision (ratio g) (accuracy ε) := by
    have hDiag : WeightedClock.diagonal
        (fun a' : Option (Fin m) × Index D T g ε =>
          MeshSelect.branchEvolution D σ N (nodeTable D T g ε m) (meshTable t T v) x
            (a'.1, a'.2)) = 1 := by
      simp only [hOne]
      exact WeightedClock.diagonal_one
    rw [hDiag, MultiOracleCircuit.Program.eval_identity, sub_eq_zero.mpr, norm_zero]
    · exact hν.le
    · rfl
  have hLCHS : ∀ a', ‖(∑ i, lchsCoefficients D T g ε i •
      MeshSelect.branchEvolution D σ N (nodeTable D T g ε m) (meshTable t T v) x (a', i)) -
        tableFamily D σ N (meshDurations t T v) x a' (-Complex.I)‖ ≤
          2 * ImprovedODEQueryBudget.precision (ratio g) (accuracy ε) := by
    intro a'
    have hsum : (∑ i, lchsCoefficients D T g ε i •
        MeshSelect.branchEvolution D σ N (nodeTable D T g ε m) (meshTable t T v) x (a', i)) =
          ∑ j, TimeDependentODE.GaussianLCHS.coefficients (lipschitz D T) (ratio g)
              (accuracy ε) j •
            tableFamily D σ N (meshDurations t T v) x a'
              (TimeDependentODE.GaussianLCHS.nodes (lipschitz D T) (ratio g) (accuracy ε) j :
                ℂ) := by
      have hbr : ∀ i, MeshSelect.branchEvolution D σ N (nodeTable D T g ε m)
          (meshTable t T v) x (a', i) =
            tableFamily D σ N (meshDurations t T v) x a' (nodeTable D T g ε m (a', i) : ℂ) :=
        fun i => branchEvolution_eq_tableFamily D σ N (meshDurations t T v) x
          (nodeTable D T g ε m) a' i
      simp only [hbr]
      exact TimeDependentODE.Sampling.padded_sum _ _ _
    rw [hsum]
    exact hApprox (x, a')
  have hQuad : ‖(∑ a', tableFamily D σ N (meshDurations t T v) x a' (-Complex.I) (z a')) - y‖ ≤
      ImprovedODEQueryBudget.precision (ratio g) (accuracy ε) * ODESourceBranches.mass z := by
    have hsum : (∑ a', tableFamily D σ N (meshDurations t T v) x a' (-Complex.I) (z a')) = y :=
      rfl
    rw [hsum, sub_self, norm_zero]
    exact mul_nonneg hν.le (ODESourceBranches.mass_nonneg z)
  have hCertS : ODEActualSourceError.Certificate E z c
      (GeneralSourceODE.Compiled.phased (J x) (phases ω)) (pN.eval x) seed y (ratio g)
        (accuracy ε) :=
    ODEActualSourceError.actual_source_certificate E hEiso z c hc
      (GeneralSourceODE.Compiled.phased (J x) (phases ω)) hJph seed hSeed hPrep (pN.eval x)
      (pN.eval_unitary (MeshNative.matrixOracle_unitary D m N d) x)
      (fun a' i => MeshSelect.branchEvolution D σ N (nodeTable D T g ε m)
        (meshTable t T v) x (a', i))
      (fun a' => tableFamily D σ N (meshDurations t T v) x a' (-Complex.I)) y (ratio g)
      (accuracy ε) hy hg' hε' hε'Half hNorm hBudget' hSim hLCHS hQuad
  -- The released primitive trial certificate, then the solution direction.
  have hTrial := MeshNative.trial_certificate D hM i0 m N d pN Pw hPw J hJ (phases ω)
    (phases_norm ω) E hEiso z c hcpos seed y hSeed
    (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) (ratio g) (accuracy ε))
    (ImprovedODEQueryBudget.logBudget (ratio g) (accuracy ε)) (ratio g) (accuracy ε) hg' x
    hz hW hCertS hq hSeedUnit hOutput
  have hFinal := retarget (η' := ε / 500) hTrial hDir (by unfold accuracy; linarith)
  exact ODECompleteTrial.of_trialCertificate
    (fun j => (q j).eval_unitary hOracle x) hε.le hTarget hFinal

set_option maxHeartbeats 8000000 in
/-- **`robust_zero_core` with its public trial family exposed** (`RobustPublicOutcome`): if
`T = 0` or `η_H + R η_D = 0`, with represented samples of any sign, the public trial family with
the identity SELECT satisfies the released complete certificate for every instance with
`RobustBudget`. -/
theorem robust_zero_core_public (D : Data (X × Fin M) n Z s) (hM : 0 < M) (t : ℕ → ℝ) {N : ℕ}
    (hN : 0 < N) (etaH etaD T gbar cq ε : ℝ) {m : ℕ} (v : Fin m → ℝ) (ω : Fin m → ℂ)
    (hH : 0 ≤ etaH) (hDiss : 0 ≤ etaD) (hT : 0 ≤ T)
    (hZero : T = 0 ∨ etaH + radius (cq * gbar) ε * etaD = 0) (hg : 1 ≤ gbar) (hcq : 1 ≤ cq)
    (hε : 0 < ε) (hεOne : ε ≤ 1) (hmesh : IsMesh t M T) (hv : ∀ i, v i ∈ Icc 0 T)
    (hrH : ∀ y i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix y) i j‖ ^ 2 ≤ etaH ^ 2)
    (hrD : ∀ y i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix y) i j‖ ^ 2 ≤ etaD ^ 2)
    (Pw : X → GeneralSourceODE.Weights.LabelOp (Option (Fin m))) (hPw : ∀ x, IsUnitary (Pw x))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ : ∀ x a, IsUnitary (J x a))
    (seed : EuclideanSpace ℂ n) (hSeed : ‖seed‖ = 1) :
    RobustPublicOutcome D hM t N etaH etaD T gbar cq ε v ω Pw J seed := by
  rcases hZero with hT0 | hρ
  · exact mesh_zero_time_core_public D hM t hN etaH etaD T gbar cq ε v ω hH hDiss hT0 hg hcq hε
      hεOne hmesh hv Pw hPw J hJ seed hSeed
  · -- Every represented sample vanishes, so its dissipative part is positive.
    have hg' : 1 ≤ ratio (cq * gbar) := by unfold ratio; nlinarith
    have hε' : 0 < accuracy ε := by unfold accuracy; linarith
    have hε'One : accuracy ε ≤ 1 := by unfold accuracy; linarith
    have hRadius : 0 < radius (cq * gbar) ε :=
      lt_of_lt_of_le (by norm_num : (0 : ℝ) < 4)
        (ODEGaussianParameters.radius_ge_four _ _ hg' hε' hε'One)
    have hPSD : ∀ (y : X × Fin M) (w : EuclideanSpace ℂ n), 0 ≤ (inner ℂ w
        (SparseStateOverlap.matrixOperator (ODEMatrixEnergy.dissipativePart (D.matrix y))
          w)).re := by
      intro y w
      have h0 := ODEZeroEnergy.matrix_zero_of_effective_energy (D.matrix y) etaH etaD
        (radius (cq * gbar) ε) hH hDiss hRadius hρ (hrH y) (hrD y)
      have hz : ODEMatrixEnergy.dissipativePart (D.matrix y) = 0 := by
        rw [h0]
        ext i j
        simp [ODEMatrixEnergy.dissipativePart]
      rw [hz]
      simp [SparseStateOverlap.matrixOperator]
    exact mesh_zero_generator_core_public D hM t hN etaH etaD T gbar cq ε v ω hH hDiss hT
      (Or.inr hρ) hg hcq hε hεOne hmesh hv hrH hrD hPSD Pw hPw J hJ seed hSeed

/-! ### The column transfer for every `T ≥ 0` -/

set_option maxHeartbeats 8000000 in
/-- **The column transfer of a public outcome.** If the public trial family of the
label-controlled family `columnLoader Lo` (the clean columns of `Lo`, completed to unitaries) has
the released complete certificate on every instance (`RobustPublicOutcome`), then one public trial
family over the actual oracles `P_w`, `Lo`, `P_w†` has the guarantee `RobustOutcomeColumns`. The
proof is that of `robust_mesh_solver_columns`, through `MeshOracles.columns_certificate`; the
circuits do not call `columnLoader Lo`. -/
theorem RobustPublicOutcome.columns {D : Data (X × Fin M) n Z s} {hM : 0 < M} {t : ℕ → ℝ}
    {N : ℕ} {etaH etaD T gbar cq ε : ℝ} {m : ℕ} {v : Fin m → ℝ} {ω : Fin m → ℂ}
    {Pw : X → GeneralSourceODE.Weights.LabelOp (Option (Fin m))} (hPw : ∀ x, IsUnitary (Pw x))
    {Lo : X → GeneralSourceODE.Native.SourceSpace (Index D T (cq * gbar) ε) n m →L[ℂ]
      GeneralSourceODE.Native.SourceSpace (Index D T (cq * gbar) ε) n m}
    (hLo : ∀ x, IsUnitary (Lo x)) {seed : EuclideanSpace ℂ n} (hSeed : ‖seed‖ = 1)
    (hT : 0 ≤ T) (hg : 1 ≤ gbar) (hcq : 1 ≤ cq) (hε : 0 < ε) (hεOne : ε ≤ 1)
    (h : RobustPublicOutcome D hM t N etaH etaD T gbar cq ε v ω Pw
      (GeneralSourceODE.columnLoader Lo seed (Sum.inr false)) seed) :
    RobustOutcomeColumns D t N etaH etaD T gbar cq ε v ω Pw Lo seed := by
  -- A label-controlled family with the clean columns of `Lo`; it is not called by the circuits.
  let J := GeneralSourceODE.columnLoader Lo seed (Sum.inr false)
  have hJ : ∀ x a, IsUnitary (J x a) := fun x a => GeneralSourceODE.loadUnitary_unitary _ _
  obtain ⟨d, E, hE, p, hSeedU, hOut, hCert⟩ := h
  have hg1 : 1 ≤ ratio (cq * gbar) := by
    unfold ratio
    nlinarith
  obtain ⟨hMpos, -, -⟩ := ODEGroverAverage.chosenIterations_bounds (ratio (cq * gbar)) hg1
  have hcpos : 0 < ODECoherentLCU.coefficientMass (lchsCoefficients D T (cq * gbar) ε) := by
    rw [Mesh.lchsCoefficients_mass D hT (cq * gbar) ε hg1 hε hεOne]
    norm_num
  have hψ := MeshNative.seed_unit (ι := Index D T (cq * gbar) ε) D hM (Sum.inr false) m N d E hE
    (lchsCoefficients D T (cq * gbar) ε) hcpos seed hSeed
  have hF := MeshNative.output_isometry (ι := Index D T (cq * gbar) ε) D hM (Sum.inr false) m N d
    E hE (lchsCoefficients D T (cq * gbar) ε) hcpos
  have hActual := MeshOracles.actualOracleL_unitary (ι := Index D T (cq * gbar) ε) D m N d hPw hLo
  refine ⟨d, ODERepeatProtocol.ofCircuits (MeshOracles.actualTrialsL D m N d Pw Lo (phases ω)
      (phases_norm ω) (MeshNative.publicTrialsS (ι := Index D T (cq * gbar) ε) D hM (Sum.inr false)
        m N d p (GeneralSourceODE.Compiled.sourceFamilyL Pw Lo (phases ω)) E hE
        (lchsCoefficients D T (cq * gbar) ε) seed hSeedU hOut))
    (ODEGroverAverage.chosenIterations (ratio (cq * gbar))) hMpos _ hψ _ hF, rfl,
    fun j y => MultiOracleCircuit.Program.eval_unitary _ hActual y, ?_⟩
  intro x G b sol bv U ζ hG hGint hU hW hCol₀ hCol hMassB hCertS hTarget hB hBudget
  -- The clean columns of `J` are those of `Lo`.
  have hcolJ : ∀ (a : Option (Fin m)) (u : EuclideanSpace ℂ n), u ≠ 0 →
      (∀ τ : Index D T (cq * gbar) ε, Lo x (PiLp.single 2 (a, τ) seed) =
        PiLp.single 2 (a, τ) (ODEStateNormalization.unitDirection u)) →
      J x a seed = ODEStateNormalization.unitDirection u := by
    intro a u hu h
    change GeneralSourceODE.loadUnitary seed ((Lo x (PiLp.single 2 (a, Sum.inr false) seed))
      (a, Sum.inr false)) seed = _
    rw [h (Sum.inr false), PiLp.single_eq_same]
    exact GeneralSourceODE.loadUnitary_apply seed _ hSeed
      (ODEStateNormalization.unitDirection_norm u hu)
  have hLoad₀ : sol 0 ≠ 0 → J x none seed = ODEStateNormalization.unitDirection (sol 0) :=
    fun h0 => hcolJ none (sol 0) h0 (hCol₀ h0)
  have hLoad : ∀ i, ω i ≠ 0 → bv i ≠ 0 → J x (some i) seed =
      ODEStateNormalization.unitDirection (bv i) :=
    fun i hω hb => hcolJ (some i) (bv i) hb (hCol i hω hb)
  -- The certificate of the label-controlled family `J`.
  have hC := hCert x G b sol bv U ζ hG hGint hU hW hLoad₀ hLoad hMassB hCertS hTarget hB
    hBudget
  -- `Lo` and the label-controlled `J` agree on the seed branch state after `P_w`.
  have hagree : Lo x (GeneralSourceODE.Weights.act (Pw x) (ODEJointLCU.coefficientInput
      (GeneralSourceODE.Compiled.seedCoefficients (lchsCoefficients D T (cq * gbar) ε)) seed)) =
      GeneralSourceODE.Weights.loader (J x) (GeneralSourceODE.Weights.act (Pw x)
        (ODEJointLCU.coefficientInput
          (GeneralSourceODE.Compiled.seedCoefficients (lchsCoefficients D T (cq * gbar) ε))
          seed)) := by
    rw [GeneralSourceODE.Weights.act_seedInput]
    apply GeneralSourceODE.Weights.clean_congr
    intro bb hbb
    rw [GeneralSourceODE.Weights.loader_single]
    have hamp : GeneralSourceODE.Weights.amp (Pw x) bb.1 none ≠ 0 := fun h => hbb (by simp [h])
    rw [hW bb.1] at hamp
    have hz : sources (sol 0) bv ω bb.1 ≠ 0 := by
      intro h0
      apply hamp
      simp [ODESourceBranches.probability, h0]
    rcases bb with ⟨a, τ⟩
    cases a with
    | none =>
        have h0 : sol 0 ≠ 0 := hz
        dsimp only
        rw [hCol₀ h0 τ, hLoad₀ h0]
    | some i =>
        have h0 : ω i • bv i ≠ 0 := hz
        obtain ⟨hω, hb⟩ := smul_ne_zero_iff.mp h0
        dsimp only
        rw [hCol i hω hb τ, hLoad i hω hb]
  exact MeshOracles.columns_certificate (ι := Index D T (cq * gbar) ε) D hM (Sum.inr false) m N d
    p Pw hPw Lo hLo J hJ (phases ω) (phases_norm ω) E hE (lchsCoefficients D T (cq * gbar) ε) seed
    hSeedU hOut x hMpos hψ hF hC hagree

set_option maxHeartbeats 8000000 in
/-- **Theorem `ode:thm:time` with the general source interface on a mesh, represented samples of
any sign, every `T ≥ 0`, and a loader specified on its clean columns only (item D1, exact case).**
`robust_mesh_solver_columns` without the assumptions `T > 0` and `η_H + R η_D > 0`. In the zero
cases the public trial family has the identity SELECT (`robust_zero_core_public`); otherwise it is
that of `robust_propagated_solver_public`. -/
theorem robust_solver_nonneg_columns (D : Data (X × Fin M) n Z s) (hM : 0 < M) (t : ℕ → ℝ)
    {N : ℕ} (hN : 0 < N) (etaH etaD T gbar cq ε : ℝ) {m : ℕ} (v : Fin m → ℝ) (ω : Fin m → ℂ)
    (hH : 0 ≤ etaH) (hDiss : 0 ≤ etaD) (hT : 0 ≤ T) (hg : 1 ≤ gbar) (hcq : 1 ≤ cq)
    (hε : 0 < ε) (hεOne : ε ≤ 1) (hmesh : IsMesh t M T)
    (hClock : 8 * s * ((etaH + radius (cq * gbar) ε * etaD) * T) ≤ N)
    (hCayley : 3 * (Real.sqrt (2 * (s : ℝ)) *
      ((etaH + radius (cq * gbar) ε * etaD) * T)) ^ 3 ≤
        precision (cq * gbar) ε * (N : ℝ) ^ 2)
    (hv : ∀ i, v i ∈ Icc 0 T)
    (hrH : ∀ y i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix y) i j‖ ^ 2 ≤ etaH ^ 2)
    (hcH : ∀ y j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix y) i j‖ ^ 2 ≤ etaH ^ 2)
    (hrD : ∀ y i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix y) i j‖ ^ 2 ≤ etaD ^ 2)
    (hcD : ∀ y j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix y) i j‖ ^ 2 ≤ etaD ^ 2)
    (Pw : X → GeneralSourceODE.Weights.LabelOp (Option (Fin m))) (hPw : ∀ x, IsUnitary (Pw x))
    (Lo : X → GeneralSourceODE.Native.SourceSpace (Index D T (cq * gbar) ε) n m →L[ℂ]
      GeneralSourceODE.Native.SourceSpace (Index D T (cq * gbar) ε) n m)
    (hLo : ∀ x, IsUnitary (Lo x))
    (seed : EuclideanSpace ℂ n) (hSeed : ‖seed‖ = 1) :
    RobustOutcomeColumns D t N etaH etaD T gbar cq ε v ω Pw Lo seed := by
  have hJ : ∀ x a, IsUnitary (GeneralSourceODE.columnLoader Lo seed (Sum.inr false) x a) :=
    fun x a => GeneralSourceODE.loadUnitary_unitary _ _
  refine RobustPublicOutcome.columns (hM := hM) hPw hLo hSeed hT hg hcq hε hεOne ?_
  by_cases hZero : T = 0 ∨ etaH + radius (cq * gbar) ε * etaD = 0
  · exact robust_zero_core_public D hM t hN etaH etaD T gbar cq ε v ω hH hDiss hT hZero hg hcq
      hε hεOne hmesh hv hrH hrD Pw hPw (GeneralSourceODE.columnLoader Lo seed (Sum.inr false)) hJ
      seed hSeed
  · have hg' : 1 ≤ ratio (cq * gbar) := by unfold ratio; nlinarith
    have hε' : 0 < accuracy ε := by unfold accuracy; linarith
    have hε'One : accuracy ε ≤ 1 := by unfold accuracy; linarith
    have hR : 0 ≤ radius (cq * gbar) ε :=
      ImprovedODEQueryBudget.radius_nonneg _ _ hg' hε' hε'One
    have hTpos : 0 < T := lt_of_le_of_ne hT (fun h => hZero (Or.inl h.symm))
    have hρ : 0 < etaH + radius (cq * gbar) ε * etaD :=
      lt_of_le_of_ne (add_nonneg hH (mul_nonneg hR hDiss)) (fun h => hZero (Or.inr h.symm))
    exact robust_propagated_solver_public D hM t hN etaH etaD T gbar cq ε v ω hH hDiss hTpos hg
      hcq hε hεOne hmesh hρ hClock hCayley hv hrH hcH hrD hcD Pw hPw
      (GeneralSourceODE.columnLoader Lo seed (Sum.inr false)) hJ seed hSeed

/-! ### Integrable pieces, mild solutions and the sampling budgets of `ode:thm:time` -/

/-- **The guarantee for integrable pieces and mild solutions with a loader specified on its clean
columns.** One public trial family over the actual oracles `P_w`, `Lo`, `P_w†` on `N` slots and the
coherent sampled-time matrix oracle, chosen before every unknown instance. The instance hypotheses
are those of `RegularApproxOutcome` with exact preparations (`P = P_w x`, `δ = 0`), with the
loading hypotheses stated on the clean columns of `Lo`; four fresh trials satisfy
`ActualCertificate`. -/
def RegularOutcomeColumns (D : Data (X × Fin M) n Z s) (t : ℕ → ℝ) (N : ℕ)
    (etaH etaD T gbar cq ε : ℝ) {m : ℕ} (v : Fin m → ℝ) (ω : Fin m → ℂ)
    (Pw : X → GeneralSourceODE.Weights.LabelOp (Option (Fin m)))
    (Lo : X → GeneralSourceODE.Native.SourceSpace (Index D T (cq * gbar) ε) n m →L[ℂ]
      GeneralSourceODE.Native.SourceSpace (Index D T (cq * gbar) ε) n m)
    (seed : EuclideanSpace ℂ n) : Prop :=
  ∃ (d : ℕ) (tf : ODERepeatProtocol.TrialFamily
      (MeshOracles.actualOracleL (ι := Index D T (cq * gbar) ε) D m N d Pw Lo)
      (EuclideanSpace ℂ n)),
    tf.choices = ODEGroverAverage.chosenIterations (ratio (cq * gbar)) ∧
    (∀ j y, IsUnitary ((tf.circuit j).eval y)) ∧
    ∀ (x : X) (G : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
      (b : Fin M → ℝ → EuclideanSpace ℂ n) (sol : ℝ → EuclideanSpace ℂ n)
      (bv : Fin m → EuclideanSpace ℂ n)
      (U : ℝ → EuclideanSpace ℂ n → ℝ → EuclideanSpace ℂ n) (ζ : ℝ),
      (∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), Accretive (G r u)) →
      RegularPieces t G →
      MildSolution t T b sol U →
      IsMeshPropagator G t T U →
      GeneralSourceODE.Compiled.WeightPrep (Pw x) (sources (sol 0) bv ω) →
      (sol 0 ≠ 0 → ∀ τ : Index D T (cq * gbar) ε,
        Lo x (PiLp.single 2 (none, τ) seed) =
          PiLp.single 2 (none, τ) (ODEStateNormalization.unitDirection (sol 0))) →
      (∀ i, ω i ≠ 0 → bv i ≠ 0 → ∀ τ : Index D T (cq * gbar) ε,
        Lo x (PiLp.single 2 (some i, τ) seed) =
          PiLp.single 2 (some i, τ) (ODEStateNormalization.unitDirection (bv i))) →
      ODESourceBranches.mass (sources (sol 0) bv ω) ≤ cq * meshScale sol b t →
      ‖(∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1), U u (b r u) T) -
          ∑ i, ω i • U (v i) (bv i) T‖ ≤ ζ * meshScale sol b t →
      sol T ≠ 0 →
      meshScale sol b t ≤ gbar * ‖sol T‖ →
      ζ + cq * (sampleError D x t G + 2 * dissipativeError D x t G +
        2 * refinementError D t T N) ≤ ε / (2000 * gbar) →
      6 * radius (cq * gbar) ε * (dissipativeError D x t G + refinementError D t T N) ≤
        precision (cq * gbar) ε →
      GeneralSourceODE.Oracles.ActualCertificate
        (ODERepeatProtocol.Protocol.repeatTrials tf 4) x (sol T) (s : ℝ)
        (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) (ratio (cq * gbar)) (accuracy ε))
        (ImprovedODEQueryBudget.logBudget (ratio (cq * gbar)) (accuracy ε))
        (ratio (cq * gbar)) ε

set_option maxHeartbeats 8000000 in
/-- **Theorem `ode:thm:time` with the general source interface on a mesh, every `T ≥ 0`, the
certificate on the propagated vector integral, represented samples of any sign, integrable pieces,
mild solutions, and a loader specified on its clean columns only (item D1, exact case).** Under
the hypotheses of `robust_approx_solver_nonneg_regular`, with exact preparations and the
label-controlled `U_load` replaced by any unitary `Lo` on the whole branch register,
`RegularOutcomeColumns` holds. It comes from `robust_solver_nonneg_columns` through Duhamel's
formula of the mild solution and `robustBudget_of_path_int`, as in
`robust_approx_solver_nonneg_regular`. -/
theorem robust_solver_nonneg_regular_columns (D : Data (X × Fin M) n Z s) (hM : 0 < M)
    (t : ℕ → ℝ) {N : ℕ} (hN : 0 < N) (etaH etaD T gbar cq ε : ℝ) {m : ℕ} (v : Fin m → ℝ)
    (ω : Fin m → ℂ)
    (hH : 0 ≤ etaH) (hDiss : 0 ≤ etaD) (hT : 0 ≤ T) (hg : 1 ≤ gbar) (hcq : 1 ≤ cq)
    (hε : 0 < ε) (hεOne : ε ≤ 1) (hmesh : IsMesh t M T)
    (hClock : 8 * s * ((etaH + radius (cq * gbar) ε * etaD) * T) ≤ N)
    (hCayley : 3 * (Real.sqrt (2 * (s : ℝ)) *
      ((etaH + radius (cq * gbar) ε * etaD) * T)) ^ 3 ≤
        precision (cq * gbar) ε * (N : ℝ) ^ 2)
    (hv : ∀ i, v i ∈ Icc 0 T)
    (hrH : ∀ y i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix y) i j‖ ^ 2 ≤ etaH ^ 2)
    (hcH : ∀ y j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix y) i j‖ ^ 2 ≤ etaH ^ 2)
    (hrD : ∀ y i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix y) i j‖ ^ 2 ≤ etaD ^ 2)
    (hcD : ∀ y j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix y) i j‖ ^ 2 ≤ etaD ^ 2)
    (Pw : X → GeneralSourceODE.Weights.LabelOp (Option (Fin m))) (hPw : ∀ x, IsUnitary (Pw x))
    (Lo : X → GeneralSourceODE.Native.SourceSpace (Index D T (cq * gbar) ε) n m →L[ℂ]
      GeneralSourceODE.Native.SourceSpace (Index D T (cq * gbar) ε) n m)
    (hLo : ∀ x, IsUnitary (Lo x))
    (seed : EuclideanSpace ℂ n) (hSeed : ‖seed‖ = 1) :
    RegularOutcomeColumns D t N etaH etaD T gbar cq ε v ω Pw Lo seed := by
  obtain ⟨d, tf, hch, hU, hC⟩ := robust_solver_nonneg_columns D hM t hN etaH etaD T gbar cq ε v ω
    hH hDiss hT hg hcq hε hεOne hmesh hClock hCayley hv hrH hcH hrD hcD Pw hPw Lo hLo seed hSeed
  refine ⟨d, tf, hch, hU, fun x G b sol bv U ζ hG hreg hsol hUm hW hL0 hL' hMass hInt hTarget hB
    hB1 hB2 => ?_⟩
  have hD : sol T - U 0 (sol 0) T =
      ∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1), U u (b r u) T := by
    rw [hsol.2]
    abel
  have hCertP : ‖sol T - U 0 (sol 0) T - ∑ i, ω i • U (v i) (bv i) T‖ ≤
      ζ * meshScale sol b t := by
    rw [hD]
    exact hInt
  exact hC x G b sol bv U ζ hG hreg hUm hW hL0 hL' hMass hCertP hTarget hB
    (robustBudget_of_path_int D x hmesh G hG hreg hB1 hB2)

end

end SparseHamiltonian.RepresentedSampleODE

/-! ### The conformance theorem -/

namespace ManuscriptConformance

noncomputable section
open ContinuousLinearMap SparseHamiltonian NativeSparseBlockEncoding OracleCircuit Set
open SparseHamiltonian.GeneralSourceExtensions
open scoped InnerProduct InnerProductSpace

set_option maxRecDepth 4096
set_option synthInstance.maxSize 8192

universe u v w

set_option maxHeartbeats 16000000 in
/-- **Theorem `ode:thm:time` with a loader specified on its clean columns only (item D1, exact
case).** The statement of `ode_thm_time`, with the label-controlled `U_load` replaced by any
unitary `Lo` on the whole branch register (source label, LCHS label and data). `Lo` is specified
only on the clean columns `|a, τ⟩|seed⟩` of the labels with nonzero source vectors, for every LCHS
label `τ`: `Lo |none, τ⟩|seed⟩ = |none, τ⟩|x₀/‖x₀‖⟩` when `x₀ ≠ 0`, and
`Lo |some i, τ⟩|seed⟩ = |some i, τ⟩|b(v_i)/‖b(v_i)‖⟩` when `ω_i ≠ 0` and `b(v_i) ≠ 0`. It is not
assumed to preserve the labels elsewhere.

One protocol over the actual oracles `MeshOracles.actualOracleL` (the sampled-time matrix oracle
on `N` clock slots and the supplied `P_w`, `Lo`, `P_w†`), fixed before the instance, succeeds with
probability at least `2/3` and has conditional output within trace distance `ε` of
`x(T)/‖x(T)‖` on every instance. It has the matrix-query and source-call bounds of `ode_thm_time`
with the same constant `C = 2548039680`. Its trials call `Lo` and its inverse.

Formal restriction: `formal_classicalPropagator` (as in `ode_thm_time`). Conclusion form:
mixed-output. -/
theorem ode_thm_time_columns :
    ∃ C : ℝ, 0 < C ∧
      ∀ {X : Type u} {n : Type v} {Z : Type w} [Fintype n] [DecidableEq n] [Fintype Z]
        [AddCommGroup Z] [DecidableEq Z] {s M : ℕ} (D : Data (X × Fin M) n Z s), 0 < M →
        ∀ (t : ℕ → ℝ) (N : ℕ), 0 < N →
        ∀ (etaH etaD T gbar cq ε : ℝ) {m : ℕ} (v : Fin m → ℝ) (ω : Fin m → ℂ),
        0 ≤ etaH → 0 ≤ etaD → 0 ≤ T → 1 ≤ gbar → 1 ≤ cq → 0 < ε → ε ≤ 1 →
        TimeDependentExtensions.IsMesh t M T →
        8 * s * ((etaH + TimeDependentODE.radius (cq * gbar) ε * etaD) * T) ≤ N →
        3 * (Real.sqrt (2 * (s : ℝ)) *
          ((etaH + TimeDependentODE.radius (cq * gbar) ε * etaD) * T)) ^ 3 ≤
          TimeDependentODE.precision (cq * gbar) ε * (N : ℝ) ^ 2 →
        (∀ i, v i ∈ Icc 0 T) →
        (∀ y i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix y) i j‖ ^ 2 ≤ etaH ^ 2) →
        (∀ y j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix y) i j‖ ^ 2 ≤ etaH ^ 2) →
        (∀ y i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix y) i j‖ ^ 2 ≤ etaD ^ 2) →
        (∀ y j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix y) i j‖ ^ 2 ≤ etaD ^ 2) →
        ∀ (Pw : X → GeneralSourceODE.Weights.LabelOp (Option (Fin m))), (∀ x, IsUnitary (Pw x)) →
        ∀ (Lo : X → GeneralSourceODE.Native.SourceSpace
            (TimeDependentODE.Index D T (cq * gbar) ε) n m →L[ℂ]
          GeneralSourceODE.Native.SourceSpace (TimeDependentODE.Index D T (cq * gbar) ε) n m),
        (∀ x, IsUnitary (Lo x)) →
        ∀ seed : EuclideanSpace ℂ n, ‖seed‖ = 1 →
        ∃ (d : ℕ) (A : ODERepeatProtocol.Protocol
            (MeshOracles.actualOracleL (ι := TimeDependentODE.Index D T (cq * gbar) ε) D m N d Pw
              Lo)
            (EuclideanSpace ℂ n)),
          ∀ (x : X) (G : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
            (b : Fin M → ℝ → EuclideanSpace ℂ n) (sol : ℝ → EuclideanSpace ℂ n)
            (bv : Fin m → EuclideanSpace ℂ n)
            (U : ℝ → EuclideanSpace ℂ n → ℝ → EuclideanSpace ℂ n) (ζ : ℝ),
            (∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), TimeDependentODE.Accretive (G r u)) →
            RepresentedSampleODE.RegularPieces t G →
            RepresentedSampleODE.MildSolution t T b sol U →
            formal_classicalPropagator G t T U →
            GeneralSourceODE.Compiled.WeightPrep (Pw x) (GeneralSourceODE.sources (sol 0) bv ω) →
            (sol 0 ≠ 0 → ∀ τ : TimeDependentODE.Index D T (cq * gbar) ε,
              Lo x (PiLp.single 2 (none, τ) seed) =
                PiLp.single 2 (none, τ) (ODEStateNormalization.unitDirection (sol 0))) →
            (∀ i, ω i ≠ 0 → bv i ≠ 0 → ∀ τ : TimeDependentODE.Index D T (cq * gbar) ε,
              Lo x (PiLp.single 2 (some i, τ) seed) =
                PiLp.single 2 (some i, τ) (ODEStateNormalization.unitDirection (bv i))) →
            ODESourceBranches.mass (GeneralSourceODE.sources (sol 0) bv ω) ≤
              cq * Mesh.meshScale sol b t →
            ‖(∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1), U u (b r u) T) -
                ∑ i, ω i • U (v i) (bv i) T‖ ≤ ζ * Mesh.meshScale sol b t →
            sol T ≠ 0 →
            Mesh.meshScale sol b t ≤ gbar * ‖sol T‖ →
            ζ + cq * (Mesh.sampleError D x t G + 2 * RepresentedSampleODE.dissipativeError D x t G +
                2 * Mesh.refinementError D t T N) ≤ ε / (2000 * gbar) →
            6 * TimeDependentODE.radius (cq * gbar) ε *
                (RepresentedSampleODE.dissipativeError D x t G + Mesh.refinementError D t T N) ≤
              TimeDependentODE.precision (cq * gbar) ε →
            HeraldedOutput A x (ODEStateNormalization.unitDirection (sol T)) ε ∧
            (A.worstCost GeneralSourceODE.Oracles.matrixCalls : ℝ) ≤
              C * (cq * gbar) * (Real.sqrt s * (T * etaH + T * etaD *
                  Real.log (40000 * cq * gbar / ε)) +
                Real.sqrt (s * (T * etaH + T * etaD * Real.log (40000 * cq * gbar / ε)) *
                  Real.log (40000 * cq * gbar / ε)) + Real.log (40000 * cq * gbar / ε)) ∧
            (A.worstCost GeneralSourceODE.Oracles.sourceCalls : ℝ) ≤ C * (cq * gbar) := by
  refine ⟨2548039680, by norm_num, ?_⟩
  intro X n Z _ _ _ _ _ s M D hM t N hN etaH etaD T gbar cq ε m v ω hH hDiss hT hg hcq hε hεOne
    hmesh hClock hCayley hv hrH hcH hrD hcD Pw hPw Lo hLo seed hSeed
  obtain ⟨d, tf, -, -, hC⟩ := RepresentedSampleODE.robust_solver_nonneg_regular_columns D hM t hN
    etaH etaD T gbar cq ε v ω hH hDiss hT hg hcq hε hεOne hmesh hClock hCayley hv hrH hcH hrD hcD Pw
    hPw Lo hLo seed hSeed
  refine ⟨d, ODERepeatProtocol.Protocol.repeatTrials tf 4, fun x G b sol bv U ζ hG hreg hsol hUm
    hW hL0 hL hMass hInt hTarget hB hB1 hB2 => ?_⟩
  have hcert := hC x G b sol bv U ζ hG hreg hsol hUm hW hL0 hL hMass hInt hTarget hB hB1 hB2
  refine ⟨⟨hcert.success_two_thirds, hcert.output_density, hcert.conditional_error⟩, ?_, ?_⟩
  · refine hcert.matrix_queries.trans (le_of_eq ?_)
    rw [ImprovedODEQueryBudget.queryShape, ImprovedODEQueryBudget.theta, time_log_eq]
    unfold TimeDependentODE.ratio
    ring
  · refine hcert.source_calls.trans ?_
    unfold TimeDependentODE.ratio
    have : 0 ≤ cq * gbar := by positivity
    nlinarith

end

end ManuscriptConformance
