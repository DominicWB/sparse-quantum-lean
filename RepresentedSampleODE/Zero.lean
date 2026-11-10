import RepresentedSampleODE.Theorem
import GeneralSourceExtensions.Mesh.Zero

/-!
# The zero cases with represented samples of any sign

`GeneralSourceExtensions.Mesh.mesh_zero_core` (the identity SELECT when `T = 0` or
`η_H + R η_D = 0`) assumes positive represented dissipative parts. With `η_H + R η_D = 0` every
represented sample vanishes, so the assumption holds automatically. At `T = 0` every public duration
vanishes, every product family is the identity, and the represented target is the source sum
itself, so no positivity is needed:

* `tableFamily_zero_time`, `zero_time_target_error`: the families and the target at `T = 0`;
* `ZeroTrialOutcome`: the released `MeshPropagatedTrialOutcome` without the classical piecewise
  solution, which no core proof uses;
* `mesh_zero_time_core`: `ZeroTrialOutcome … 0` at `T = 0` without positivity;
* `mesh_zero_generator_core`: the released zero core for `ZeroTrialOutcome`;
* `RobustPropagatedTrialOutcome`: `RobustPropagatedOutcome` with a per-trial matrix budget;
* `robust_zero_core`: `RobustPropagatedTrialOutcome … 0` if `T = 0` or `η_H + R η_D = 0`.
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
  meshTarget meshDurations_eq_zero trial_matrix_cost evolution_congr_one)
open SparseHamiltonian.TimeDependentODE.GaussianLCHS (productFamily)
open scoped BigOperators InnerProduct
set_option maxRecDepth 4096
set_option synthInstance.maxSize 8192

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s M : ℕ}

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- At `T = 0` every product family of a public table is the identity. -/
theorem tableFamily_zero_time (D : Data (X × Fin M) n Z s) (σ : ℕ → Fin M) (N : ℕ)
    {t : ℕ → ℝ} {T : ℝ} (hT0 : T = 0) {m : ℕ} (v : Fin m → ℝ) (x : X) (a : Option (Fin m))
    (z : ℂ) : tableFamily D σ N (meshDurations t T v) x a z = 1 := by
  unfold tableFamily productFamily
  apply evolution_congr_one
  intro k _
  simp only [meshDurations_eq_zero hT0 v a (σ k), zero_div]
  unfold ODEComplexFrequency.evolution
  rw [zero_smul, NormedSpace.exp_zero]

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- At `T = 0` the represented target is the source sum, at distance zero from the propagated
source sum. -/
theorem zero_time_target_error (D : Data (X × Fin M) n Z s) (hM : 0 < M) {t : ℕ → ℝ} {T : ℝ}
    (hT0 : T = 0) (N : ℕ) (G : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (U : ℝ → EuclideanSpace ℂ n → ℝ → EuclideanSpace ℂ n) (hU : IsMeshPropagator G t T U)
    {m : ℕ} (v : Fin m → ℝ) (hv : ∀ i, v i ∈ Icc 0 T) (ω : Fin m → ℂ) (x : X)
    (x₀ : EuclideanSpace ℂ n) (bv : Fin m → EuclideanSpace ℂ n) :
    (U 0 x₀ T + ∑ i, ω i • U (v i) (bv i) T) - meshTarget D hM t T N v x x₀ bv ω = 0 := by
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT0.ge⟩
  have hU0 : U 0 x₀ T = x₀ := by
    have h := (hU 0 h0 x₀).1
    rw [hT0]
    exact h
  have hUi : ∀ i, U (v i) (bv i) T = bv i := by
    intro i
    have hvi : v i = T := le_antisymm (hv i).2 (hT0 ▸ (hv i).1)
    have h := (hU (v i) (hv i) (bv i)).1
    rwa [hvi] at h ⊢
  have hTarget : meshTarget D hM t T N v x x₀ bv ω = x₀ + ∑ i, ω i • bv i := by
    unfold meshTarget
    simp only [tableFamily_zero_time D _ N hT0 v x, one_apply_eq_self, Fintype.sum_option]
    rfl
  rw [hU0, hTarget]
  simp only [hUi, sub_self]

/-- **The zero-case trial outcome for every mild solution**: the released
`GeneralSourceExtensions.Mesh.MeshPropagatedTrialOutcome` without the classical piecewise solution
(`SolvesODE`), which no core proof uses: only `x(0)`, `x(T)` and the certificate in terms of them
enter. -/
def ZeroTrialOutcome (D : Data (X × Fin M) n Z s) (hM : 0 < M) (t : ℕ → ℝ) (N : ℕ)
    (etaH etaD T gbar cq ε : ℝ) {m : ℕ} (v : Fin m → ℝ) (ω : Fin m → ℂ)
    (Pw : X → GeneralSourceODE.Weights.LabelOp (Option (Fin m)))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (seed : EuclideanSpace ℂ n) (Qt : ℝ) : Prop :=
  ∃ (d : ℕ)
    (E : GeneralSourceODE.Native.SourceSpace (Index D T (cq * gbar) ε) n m →L[ℂ]
      MeshNative.MatrixSpace (Index D T (cq * gbar) ε) n Z m M N d)
    (_hE : E† ∘L E = 1)
    (q : ℕ → MultiOracleCircuit.Program
      (MeshNative.physicalOracle (ι := Index D T (cq * gbar) ε) D m N d Pw J (phases ω))),
    (∀ j y, IsUnitary ((q j).eval y)) ∧
    (∀ j, ((q j).cost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) : ℝ) ≤ Qt) ∧
    ∀ (x : X) (G : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
      (b : Fin M → ℝ → EuclideanSpace ℂ n) (sol : ℝ → EuclideanSpace ℂ n)
      (bv : Fin m → EuclideanSpace ℂ n)
      (U : ℝ → EuclideanSpace ℂ n → ℝ → EuclideanSpace ℂ n) (ζ : ℝ),
      (∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), Accretive (G r u)) →
      (∀ r : Fin M, IntervalIntegrable (G r) volume (t r) (t ((r : ℕ) + 1))) →
      IsMeshPropagator G t T U →
      GeneralSourceODE.Compiled.WeightPrep (Pw x) (sources (sol 0) bv ω) →
      (sol 0 ≠ 0 → J x none seed = ODEStateNormalization.unitDirection (sol 0)) →
      (∀ i, ω i ≠ 0 → bv i ≠ 0 → J x (some i) seed =
        ODEStateNormalization.unitDirection (bv i)) →
      ODESourceBranches.mass (sources (sol 0) bv ω) ≤ cq * meshScale sol b t →
      ‖sol T - U 0 (sol 0) T - ∑ i, ω i • U (v i) (bv i) T‖ ≤ ζ * meshScale sol b t →
      sol T ≠ 0 →
      meshScale sol b t ≤ gbar * ‖sol T‖ →
      ζ + cq * (sampleError D x t G + refinementError D t T N) ≤ ε / (2000 * gbar) →
      ODECompleteTrial.Certificate q
        (ODEGroverAverage.chosenIterations (ratio (cq * gbar)))
        (MeshNative.input D hM (Sum.inr false) m N d
          (ODECompiledSource.seed E
            (GeneralSourceODE.Compiled.seedCoefficients
              (lchsCoefficients D T (cq * gbar) ε)) seed))
        (MeshNative.input D hM (Sum.inr false) m N d ∘L
          ODECompiledSource.output E
            (GeneralSourceODE.Compiled.seedCoefficients (lchsCoefficients D T (cq * gbar) ε)))
        x (sol T) (s : ℝ)
        (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) (ratio (cq * gbar)) (accuracy ε))
        (ImprovedODEQueryBudget.logBudget (ratio (cq * gbar)) (accuracy ε))
        (ratio (cq * gbar)) ε

set_option maxHeartbeats 8000000 in
/-- **The identity SELECT on a mesh at `T = 0`, without positivity of the represented samples**
(two counted source interfaces): the public trial family with the identity SELECT on `N` slots
makes no matrix query in any trial and satisfies the released complete certificate for every
valid instance. -/
theorem mesh_zero_time_core (D : Data (X × Fin M) n Z s) (hM : 0 < M) (t : ℕ → ℝ) {N : ℕ}
    (hN : 0 < N) (etaH etaD T gbar cq ε : ℝ) {m : ℕ} (v : Fin m → ℝ) (ω : Fin m → ℂ)
    (hH : 0 ≤ etaH) (hDiss : 0 ≤ etaD) (hT0 : T = 0) (hg : 1 ≤ gbar) (hcq : 1 ≤ cq)
    (hε : 0 < ε) (hεOne : ε ≤ 1) (hmesh : IsMesh t M T) (hv : ∀ i, v i ∈ Icc 0 T)
    (Pw : X → GeneralSourceODE.Weights.LabelOp (Option (Fin m))) (hPw : ∀ x, IsUnitary (Pw x))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ : ∀ x a, IsUnitary (J x a))
    (seed : EuclideanSpace ℂ n) (hSeed : ‖seed‖ = 1) :
    ZeroTrialOutcome D hM t N etaH etaD T gbar cq ε v ω Pw J seed 0 := by
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
  have hCost : ∀ j, (q j).cost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) = 0 :=
    fun j => trial_matrix_cost D hM i0 m N d Pw J (phases ω) E hEiso c seed _ _ j
  refine ⟨d, E, hEiso, q, fun j y => (q j).eval_unitary hOracle y,
    fun j => by rw [hCost j, Nat.cast_zero], ?_⟩
  intro x G b sol bv U ζ _hG _hGint hU hW hLoad₀ hLoad hMassB hCert hTarget hB hBudget
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
/-- **The identity SELECT on a mesh in the zero cases, for every mild solution**: the released
`GeneralSourceExtensions.Mesh.mesh_zero_core`, whose proof does not use the classical solution, for
`ZeroTrialOutcome`. If `T = 0` or `η_H + R η_D = 0`, the public trial family with the identity
SELECT on `N` slots makes no matrix query in any trial and satisfies the released complete
certificate for every valid instance. -/
theorem mesh_zero_generator_core (D : Data (X × Fin M) n Z s) (hM : 0 < M) (t : ℕ → ℝ) {N : ℕ}
    (hN : 0 < N) (etaH etaD T gbar cq ε : ℝ) {m : ℕ} (v : Fin m → ℝ) (ω : Fin m → ℂ)
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
    ZeroTrialOutcome D hM t N etaH etaD T gbar cq ε v ω Pw J seed 0 := by
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
  have hCost : ∀ j, (q j).cost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) = 0 :=
    fun j => trial_matrix_cost D hM i0 m N d Pw J (phases ω) E hEiso c seed _ _ j
  refine ⟨d, E, hEiso, q, fun j y => (q j).eval_unitary hOracle y,
    fun j => by rw [hCost j, Nat.cast_zero], ?_⟩
  intro x G b sol bv U ζ hG hGint hU hW hLoad₀ hLoad hMassB hCert hTarget hB hBudget
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

/-- `RobustPropagatedOutcome` in which every trial circuit makes at most `Qt` matrix queries. -/
def RobustPropagatedTrialOutcome (D : Data (X × Fin M) n Z s) (hM : 0 < M) (t : ℕ → ℝ) (N : ℕ)
    (etaH etaD T gbar cq ε : ℝ) {m : ℕ} (v : Fin m → ℝ) (ω : Fin m → ℂ)
    (Pw : X → GeneralSourceODE.Weights.LabelOp (Option (Fin m)))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (seed : EuclideanSpace ℂ n) (Qt : ℝ) : Prop :=
  ∃ (d : ℕ)
    (E : GeneralSourceODE.Native.SourceSpace (Index D T (cq * gbar) ε) n m →L[ℂ]
      MeshNative.MatrixSpace (Index D T (cq * gbar) ε) n Z m M N d)
    (_hE : E† ∘L E = 1)
    (q : ℕ → MultiOracleCircuit.Program
      (MeshNative.physicalOracle (ι := Index D T (cq * gbar) ε) D m N d Pw J (phases ω))),
    (∀ j y, IsUnitary ((q j).eval y)) ∧
    (∀ j, ((q j).cost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) : ℝ) ≤ Qt) ∧
    ∀ (x : X) (G : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
      (b : Fin M → ℝ → EuclideanSpace ℂ n) (sol : ℝ → EuclideanSpace ℂ n)
      (bv : Fin m → EuclideanSpace ℂ n)
      (U : ℝ → EuclideanSpace ℂ n → ℝ → EuclideanSpace ℂ n) (ζ : ℝ),
      (∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), Accretive (G r u)) →
      (∀ r : Fin M, IntervalIntegrable (G r) volume (t r) (t ((r : ℕ) + 1))) →
      IsMeshPropagator G t T U →
      GeneralSourceODE.Compiled.WeightPrep (Pw x) (sources (sol 0) bv ω) →
      (sol 0 ≠ 0 → J x none seed = ODEStateNormalization.unitDirection (sol 0)) →
      (∀ i, ω i ≠ 0 → bv i ≠ 0 → J x (some i) seed =
        ODEStateNormalization.unitDirection (bv i)) →
      ODESourceBranches.mass (sources (sol 0) bv ω) ≤ cq * meshScale sol b t →
      ‖sol T - U 0 (sol 0) T - ∑ i, ω i • U (v i) (bv i) T‖ ≤ ζ * meshScale sol b t →
      sol T ≠ 0 →
      meshScale sol b t ≤ gbar * ‖sol T‖ →
      RobustBudget D x t G T N cq gbar ε ζ →
      ODECompleteTrial.Certificate q
        (ODEGroverAverage.chosenIterations (ratio (cq * gbar)))
        (MeshNative.input D hM (Sum.inr false) m N d
          (ODECompiledSource.seed E
            (GeneralSourceODE.Compiled.seedCoefficients
              (lchsCoefficients D T (cq * gbar) ε)) seed))
        (MeshNative.input D hM (Sum.inr false) m N d ∘L
          ODECompiledSource.output E
            (GeneralSourceODE.Compiled.seedCoefficients (lchsCoefficients D T (cq * gbar) ε)))
        x (sol T) (s : ℝ)
        (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) (ratio (cq * gbar)) (accuracy ε))
        (ImprovedODEQueryBudget.logBudget (ratio (cq * gbar)) (accuracy ε))
        (ratio (cq * gbar)) ε

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- `RobustBudget` contains the released budget `ζ + c_q (ΔG + ΔR) ≤ ε / (2000 ḡ)`. -/
theorem RobustBudget.released {D : Data (X × Fin M) n Z s} {x : X} {t : ℕ → ℝ}
    {G : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n} {T : ℝ} {N : ℕ}
    {cq gbar ε ζ : ℝ} (hmesh : IsMesh t M T) (hcq : 0 ≤ cq)
    (h : RobustBudget D x t G T N cq gbar ε ζ) :
    ζ + cq * (sampleError D x t G + refinementError D t T N) ≤ ε / (2000 * gbar) := by
  obtain ⟨κ, hκ, -, hB, -⟩ := h
  have h1 := negativity_nonneg hmesh hκ
  have h2 := refinementError_nonneg D t T N
  have h3 : cq * (sampleError D x t G + refinementError D t T N) ≤
      cq * (sampleError D x t G + 2 * negativity t κ + 2 * refinementError D t T N) :=
    mul_le_mul_of_nonneg_left (by linarith) hcq
  linarith

/-- The zero-case trial outcome gives the robust one: `RobustBudget` contains the released
budget. -/
theorem robust_of_released (D : Data (X × Fin M) n Z s) (hM : 0 < M) (t : ℕ → ℝ) (N : ℕ)
    (etaH etaD T gbar cq ε : ℝ) {m : ℕ} (v : Fin m → ℝ) (ω : Fin m → ℂ)
    (Pw : X → GeneralSourceODE.Weights.LabelOp (Option (Fin m)))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (seed : EuclideanSpace ℂ n) (Qt : ℝ) (hmesh : IsMesh t M T) (hcq : 0 ≤ cq)
    (h : ZeroTrialOutcome D hM t N etaH etaD T gbar cq ε v ω Pw J seed Qt) :
    RobustPropagatedTrialOutcome D hM t N etaH etaD T gbar cq ε v ω Pw J seed Qt := by
  obtain ⟨d, E, hE, q, hU, hCost, hC⟩ := h
  exact ⟨d, E, hE, q, hU, hCost, fun x G b sol bv U ζ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 =>
    hC x G b sol bv U ζ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 (h11.released hmesh hcq)⟩

set_option maxHeartbeats 8000000 in
/-- **The identity SELECT on a mesh in the zero cases, represented samples of any sign**: if
`T = 0` or `η_H + R η_D = 0`, the public trial family with the identity SELECT makes no matrix
query and satisfies the released complete certificate for every instance with `RobustBudget`. -/
theorem robust_zero_core (D : Data (X × Fin M) n Z s) (hM : 0 < M) (t : ℕ → ℝ) {N : ℕ}
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
    RobustPropagatedTrialOutcome D hM t N etaH etaD T gbar cq ε v ω Pw J seed 0 := by
  have hcq0 : 0 ≤ cq := by linarith
  rcases hZero with hT0 | hρ
  · exact robust_of_released D hM t N etaH etaD T gbar cq ε v ω Pw J seed 0 hmesh hcq0
      (mesh_zero_time_core D hM t hN etaH etaD T gbar cq ε v ω hH hDiss hT0 hg hcq hε hεOne
        hmesh hv Pw hPw J hJ seed hSeed)
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
    exact robust_of_released D hM t N etaH etaD T gbar cq ε v ω Pw J seed 0 hmesh hcq0
      (mesh_zero_generator_core D hM t hN etaH etaD T gbar cq ε v ω hH hDiss hT (Or.inr hρ) hg
        hcq hε hεOne hmesh hv hrH hrD hPSD Pw hPw J hJ seed hSeed)

end

end SparseHamiltonian.RepresentedSampleODE
