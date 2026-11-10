import ManuscriptConformance.MeshLoaderColumns
import RepresentedSampleODE.Integral

/-!
# Represented samples of any sign, with a loader specified on its clean columns (item D1)

`RepresentedSampleODE.robust_mesh_solver` and `robust_solver_integral` are the mesh general-source
solvers with represented samples of any sign: no positivity of the represented dissipative parts,
the analysis runs on their positive repairs (`RobustBudget`). Like the other general-source
solvers, they take the loading oracle as a label-controlled family `∑_a |a⟩⟨a| ⊗ J_a`. They use
the public trial family `MeshNative.publicTrials` of the mesh solvers, so the transfer of
`MeshLoaderColumns` applies. Here the loading oracle is any unitary `Lo` on the whole branch
register, specified only on the clean columns `|a, τ⟩|seed⟩` of the labels with nonzero source
vectors.

* `robust_propagated_solver_public` (`RobustPublicOutcome`): the released proof of
  `robust_propagated_solver` with the public trial family named in the conclusion.
* `robust_mesh_solver_columns` (`RobustOutcomeColumns`): the guarantee of `robust_mesh_solver`
  (success at least `2/3`, conditional trace distance at most `ε`, the same matrix-query bound and
  at most `40 g'` calls of each of `P_w`, `Lo` and `P_w†`) for every unitary loader with the stated
  clean columns, through `MeshOracles.columns_certificate`.
* `robust_solver_integral_columns` (`RobustIntegralOutcomeColumns`): the same for continuous pieces
  with the certificate on the propagated vector integral, as `robust_solver_integral`.

Scope: the exact case of item D1 for these endpoints with exact preparations. Approximate columns,
the approximate-preparation forms and the conformance theorems of `ode:thm:time` (built on the
approximate-preparation solver) keep the label-controlled loader.
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
  mesh_duhamel)
open scoped BigOperators InnerProduct
set_option maxRecDepth 4096
set_option synthInstance.maxSize 8192

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s M : ℕ}

/-- `RobustPropagatedOutcome` with its public trial family named: the compiled family
`MeshNative.publicTrials` of the SELECT program `p` on `N` slots, the supplied `P_w`, `J`, the
public phases, the clean encoding `E`, the LCHS coefficients and the seed. -/
def RobustPublicOutcome (D : Data (X × Fin M) n Z s) (hM : 0 < M) (t : ℕ → ℝ) (N : ℕ)
    (etaH etaD T gbar cq ε : ℝ) {m : ℕ} (v : Fin m → ℝ) (ω : Fin m → ℂ)
    (Pw : X → GeneralSourceODE.Weights.LabelOp (Option (Fin m)))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (seed : EuclideanSpace ℂ n) : Prop :=
  ∃ (d : ℕ)
    (E : GeneralSourceODE.Native.SourceSpace (Index D T (cq * gbar) ε) n m →L[ℂ]
      MeshNative.MatrixSpace (Index D T (cq * gbar) ε) n Z m M N d)
    (hE : E† ∘L E = 1)
    (p : MultiOracleCircuit.Program
      (MeshNative.matrixOracle (ι := Index D T (cq * gbar) ε) D m N d))
    (hSeedU : ‖ODECompiledSource.seed E
      (GeneralSourceODE.Compiled.seedCoefficients (lchsCoefficients D T (cq * gbar) ε)) seed‖ = 1)
    (hOutput : (ODECompiledSource.output E
        (GeneralSourceODE.Compiled.seedCoefficients (lchsCoefficients D T (cq * gbar) ε)))† ∘L
      ODECompiledSource.output E
        (GeneralSourceODE.Compiled.seedCoefficients (lchsCoefficients D T (cq * gbar) ε)) = 1),
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
      ODECompleteTrial.Certificate
        (MeshNative.publicTrials (ι := Index D T (cq * gbar) ε) D hM (Sum.inr false) m N d p Pw J
          (phases ω) E hE (lchsCoefficients D T (cq * gbar) ε) seed hSeedU hOutput)
        (ODEGroverAverage.chosenIterations (ratio (cq * gbar)))
        (MeshNative.input (ι := Index D T (cq * gbar) ε) D hM (Sum.inr false) m N d
          (ODECompiledSource.seed E
            (GeneralSourceODE.Compiled.seedCoefficients
              (lchsCoefficients D T (cq * gbar) ε)) seed))
        (MeshNative.input (ι := Index D T (cq * gbar) ε) D hM (Sum.inr false) m N d ∘L
          ODECompiledSource.output E
            (GeneralSourceODE.Compiled.seedCoefficients (lchsCoefficients D T (cq * gbar) ε)))
        x (sol T) (s : ℝ)
        (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) (ratio (cq * gbar)) (accuracy ε))
        (ImprovedODEQueryBudget.logBudget (ratio (cq * gbar)) (accuracy ε))
        (ratio (cq * gbar)) ε

set_option maxHeartbeats 8000000 in
/-- **`robust_propagated_solver` with its public trial family exposed.** The released proof; only
the conclusion names the trial family (`RobustPublicOutcome`), which `RobustPropagatedOutcome`
leaves existential. -/
theorem robust_propagated_solver_public (D : Data (X × Fin M) n Z s) (hM : 0 < M) (t : ℕ → ℝ)
    {N : ℕ} (hN : 0 < N) (etaH etaD T gbar cq ε : ℝ) {m : ℕ} (v : Fin m → ℝ) (ω : Fin m → ℂ)
    (hH : 0 ≤ etaH) (hDiss : 0 ≤ etaD) (hT : 0 < T) (hg : 1 ≤ gbar) (hcq : 1 ≤ cq)
    (hε : 0 < ε) (hεOne : ε ≤ 1) (hmesh : IsMesh t M T)
    (hρ : 0 < etaH + radius (cq * gbar) ε * etaD)
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
  have hνOne : precision g ε ≤ 1 :=
    (ImprovedODEQueryBudget.precision_le_one_ten_thousandth _ _ hg' hε'One).trans
      (by norm_num)
  have hR : 0 ≤ radius g ε := ImprovedODEQueryBudget.radius_nonneg _ _ hg' hε' hε'One
  let σ : ℕ → Fin M := pieceOf t T N hM
  have hu0 : ∀ a r, 0 ≤ meshDurations t T v a r := meshDurations_nonneg hmesh hT.le v
  have huT : ∀ a r, meshDurations t T v a r ≤ T := meshDurations_le hmesh hT.le v
  -- One public Gaussian table for every product family.
  have hL : 0 ≤ lipschitz D T :=
    mul_nonneg hT.le (mul_nonneg (Nat.cast_nonneg s) D.scale_pos.le)
  obtain ⟨_hGrid, hNodes, hMass, -⟩ := TimeDependentODE.GaussianLCHS.table_certificate
    (fun _ : Unit => fun _ : ℂ => (1 : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n))
    (fun _ _ => analyticAt_const) (fun _ _ _ => norm_one_op_le)
    (lipschitz D T) hL (fun _ k l => by
      rw [sub_self, norm_zero]
      exact mul_nonneg hL (abs_nonneg _))
    (ratio g) (accuracy ε) hg' hε' hε'One
  have hc : ODECoherentLCU.coefficientMass (lchsCoefficients D T g ε) = 3 :=
    ODECoefficientPadding.coefficientMass_eq _ 3 hMass
  -- One public SELECT program on `N` slots for the public node and duration tables.
  let i0 : Index D T g ε := Sum.inr false
  obtain ⟨γ, _hγ, _hγOne, _hWidth, hTables⟩ :=
    MeshSelect.select (ι := GeneralSourceODE.Native.Label (Index D T g ε) m) D hM σ hN
      (GeneralSourceODE.Native.dummy hM i0 m) etaH etaD (radius g ε) T (precision g ε)
      hH hDiss hρ hT hν hνOne hrH hcH hrD hcD hClock hCayley
  have hk : ∀ a, |nodeTable D T g ε m a| ≤ radius g ε := fun a =>
    ODECoefficientPadding.paddedNodes_bound _ _ hR hNodes a.2
  have hu : ∀ (a : GeneralSourceODE.Native.Label (Index D T g ε) m) (r : Fin M),
      0 ≤ meshTable t T v a r := fun a r => hu0 a.1 r
  have huT' : ∀ (a : GeneralSourceODE.Native.Label (Index D T g ε) m) (r : Fin M),
      meshTable t T v a r ≤ T := fun a r => huT a.1 r
  obtain ⟨p, hCount, hE, hAct⟩ := hTables (nodeTable D T g ε m) (meshTable t T v) hk hu huT'
  let d := TimeDependentODE.Select.degree (s : ℝ) γ (etaH + radius g ε * etaD) T
    (precision g ε) N
  let E : GeneralSourceODE.Native.SourceSpace (Index D T g ε) n m →L[ℂ]
      MeshNative.MatrixSpace (Index D T g ε) n Z m M N d :=
    MeshSelect.alignedInput D hM σ (GeneralSourceODE.Native.dummy hM i0 m) N γ
      (etaH + radius g ε * etaD) T (precision g ε)
  have hEiso : E† ∘L E = 1 := hE
  let pN : MultiOracleCircuit.Program
      (MeshNative.matrixOracle (ι := Index D T g ε) D m N d) := p
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
  have hq : (pN.count : ℝ) ≤ 10616832 * ImprovedODEQueryBudget.queryShape (s : ℝ)
      (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) (ratio g) (accuracy ε))
      (ImprovedODEQueryBudget.logBudget (ratio g) (accuracy ε)) :=
    ODEFinitePropagator.query_bound p.count (s : ℝ) etaH etaD T (ratio g) (accuracy ε)
      (Nat.cast_nonneg s) hH hDiss hT.le hg' hε' hε'One hCount
  have hOracle := MeshNative.physicalOracle_unitary (ι := Index D T g ε) D m N d Pw hPw J hJ
    (phases ω) (phases_norm ω)
  refine ⟨d, E, hEiso, pN, hSeedUnit, hOutput, ?_⟩
  intro x G b sol bv U ζ hG hGint hU hW hLoad₀ hLoad hMassB hCert hTarget hB hRobust
  obtain ⟨κ, hκ, hneg, hBudget, hBranch⟩ := hRobust
  -- The repaired target.
  let z := sources (sol 0) bv ω
  let y := robustTarget D hM t T N v x κ (sol 0) bv ω
  set Bs := meshScale sol b t with hBs
  have hTargetErr := robust_target_error D hM x κ hκ hneg hmesh hT.le hN G hG hGint U hU v hv ω
    (sol 0) bv
  set K : ℝ := sampleError D x t G + 2 * negativity t κ + 2 * refinementError D t T N with hK
  have hK0 : 0 ≤ K := by
    have h1 := sampleError_nonneg D x hmesh G
    have h2 := negativity_nonneg hmesh hκ
    have h3 := refinementError_nonneg D t T N
    rw [hK]
    linarith
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
    robustTarget_norm_le D hM hmesh hT.le N v x κ hκ hneg (sol 0) bv ω
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
          (a'.1, a'.2))‖ ≤ ImprovedODEQueryBudget.precision (ratio g) (accuracy ε) :=
    (hAct x).2
  -- The Gaussian table on the repaired family of this instance.
  obtain ⟨-, -, -, hApproxR⟩ := TimeDependentODE.GaussianLCHS.table_certificate
    (fun a' : Option (Fin m) => robustFamily D σ N (meshDurations t T v) x κ a')
    (fun a' z' => robustFamily_analyticAt D σ N _ x κ a' z')
    (fun a' z' hz => robustFamily_norm_le_one D σ N _ hu0 x κ hκ hneg a' z' hz)
    (lipschitz D T) hL (fun a' k l => robustFamily_lipschitz D σ hN _ hu0 huT x κ hκ a' k l)
    (ratio g) (accuracy ε) hg' hε' hε'One
  -- The represented SELECT branches as the Gaussian table sum of the represented family.
  have hsum : ∀ a', (∑ i, lchsCoefficients D T g ε i •
      MeshSelect.branchEvolution D σ N (nodeTable D T g ε m) (meshTable t T v) x (a', i)) =
        ∑ j, TimeDependentODE.GaussianLCHS.coefficients (lipschitz D T) (ratio g)
            (accuracy ε) j •
          tableFamily D σ N (meshDurations t T v) x a'
            (TimeDependentODE.GaussianLCHS.nodes (lipschitz D T) (ratio g) (accuracy ε) j :
              ℂ) := by
    intro a'
    have hbr : ∀ i, MeshSelect.branchEvolution D σ N (nodeTable D T g ε m)
        (meshTable t T v) x (a', i) =
          tableFamily D σ N (meshDurations t T v) x a' (nodeTable D T g ε m (a', i) : ℂ) :=
      fun i => branchEvolution_eq_tableFamily D σ N (meshDurations t T v) x
        (nodeTable D T g ε m) a' i
    simp only [hbr]
    exact TimeDependentODE.Sampling.padded_sum _ _ _
  -- The per-label targets: the branch sum corrected by the repaired-family table error.
  let Rsum : Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n := fun a' =>
    ∑ j, TimeDependentODE.GaussianLCHS.coefficients (lipschitz D T) (ratio g) (accuracy ε) j •
      robustFamily D σ N (meshDurations t T v) x κ a'
        (TimeDependentODE.GaussianLCHS.nodes (lipschitz D T) (ratio g) (accuracy ε) j : ℂ)
  let Bsum : Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n := fun a' =>
    ∑ i, lchsCoefficients D T g ε i •
      MeshSelect.branchEvolution D σ N (nodeTable D T g ε m) (meshTable t T v) x (a', i)
  let Sx : Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n := fun a' =>
    Bsum a' - (Rsum a' - robustFamily D σ N (meshDurations t T v) x κ a' (-Complex.I))
  have hLCHS : ∀ a', ‖(∑ i, lchsCoefficients D T g ε i •
      MeshSelect.branchEvolution D σ N (nodeTable D T g ε m) (meshTable t T v) x (a', i)) -
        Sx a'‖ ≤ 2 * ImprovedODEQueryBudget.precision (ratio g) (accuracy ε) := by
    intro a'
    have e : (∑ i, lchsCoefficients D T g ε i •
        MeshSelect.branchEvolution D σ N (nodeTable D T g ε m) (meshTable t T v) x (a', i)) -
          Sx a' = Rsum a' - robustFamily D σ N (meshDurations t T v) x κ a' (-Complex.I) := by
      simp only [Sx, Bsum]
      abel
    rw [e]
    exact hApproxR a'
  -- The branch comparison: the represented and repaired table sums agree within `ν`.
  have hNodesG : ∀ j, |TimeDependentODE.GaussianLCHS.nodes (lipschitz D T) (ratio g)
      (accuracy ε) j| ≤ radius g ε := hNodes
  have hBR : ∀ a', ‖Bsum a' - Rsum a'‖ ≤
      ImprovedODEQueryBudget.precision (ratio g) (accuracy ε) := by
    intro a'
    have e : Bsum a' - Rsum a' =
        ∑ j, TimeDependentODE.GaussianLCHS.coefficients (lipschitz D T) (ratio g) (accuracy ε) j •
          (tableFamily D σ N (meshDurations t T v) x a'
              (TimeDependentODE.GaussianLCHS.nodes (lipschitz D T) (ratio g) (accuracy ε) j :
                ℂ) -
            robustFamily D σ N (meshDurations t T v) x κ a'
              (TimeDependentODE.GaussianLCHS.nodes (lipschitz D T) (ratio g) (accuracy ε) j :
                ℂ)) := by
      simp only [Bsum, Rsum, hsum a', smul_sub, Finset.sum_sub_distrib]
    rw [e]
    set W : ℝ := 2 * radius g ε * (negativity t κ + refinementError D t T N) with hW
    have hterm : ∀ j, ‖TimeDependentODE.GaussianLCHS.coefficients (lipschitz D T) (ratio g)
        (accuracy ε) j • (tableFamily D σ N (meshDurations t T v) x a'
            (TimeDependentODE.GaussianLCHS.nodes (lipschitz D T) (ratio g) (accuracy ε) j :
              ℂ) -
          robustFamily D σ N (meshDurations t T v) x κ a'
            (TimeDependentODE.GaussianLCHS.nodes (lipschitz D T) (ratio g) (accuracy ε) j :
              ℂ))‖ ≤
        ‖TimeDependentODE.GaussianLCHS.coefficients (lipschitz D T) (ratio g) (accuracy ε) j‖ *
          W := by
      intro j
      rw [norm_smul]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      have h := tableFamily_sub_robustFamily D hM hmesh hT hN v x κ hκ a'
        (TimeDependentODE.GaussianLCHS.nodes (lipschitz D T) (ratio g) (accuracy ε) j)
      refine h.trans ?_
      have hΛ0 : 0 ≤ negativity t κ + refinementError D t T N :=
        add_nonneg (negativity_nonneg hmesh hκ) (refinementError_nonneg D t T N)
      rw [hW]
      have := hNodesG j
      nlinarith
    have hW0 : 0 ≤ W := by
      rw [hW]
      exact mul_nonneg (mul_nonneg (by norm_num) hR)
        (add_nonneg (negativity_nonneg hmesh hκ) (refinementError_nonneg D t T N))
    calc _ ≤ ∑ j, ‖TimeDependentODE.GaussianLCHS.coefficients (lipschitz D T) (ratio g)
            (accuracy ε) j‖ * W :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => hterm j)
      _ = ODECoherentLCU.coefficientMass (TimeDependentODE.GaussianLCHS.coefficients
            (lipschitz D T) (ratio g) (accuracy ε)) * W := by
          rw [ODECoherentLCU.coefficientMass, Finset.sum_mul]
      _ ≤ 3 * W := mul_le_mul_of_nonneg_right hMass hW0
      _ ≤ ImprovedODEQueryBudget.precision (ratio g) (accuracy ε) := by
          rw [hW]
          have h6 := hBranch
          change 6 * radius g ε * (negativity t κ + refinementError D t T N) ≤
            ImprovedODEQueryBudget.precision (ratio g) (accuracy ε) at h6
          linarith
  have hQuad : ‖(∑ a', Sx a' (z a')) - y‖ ≤
      ImprovedODEQueryBudget.precision (ratio g) (accuracy ε) * ODESourceBranches.mass z := by
    have e : (∑ a', Sx a' (z a')) - y = ∑ a', (Bsum a' - Rsum a') (z a') := by
      simp only [y, robustTarget, Sx, sub_apply, Finset.sum_sub_distrib]
      abel
    rw [e, ODESourceBranches.mass, Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a' _ => ?_)
    exact (le_opNorm _ _).trans (mul_le_mul_of_nonneg_right (hBR a') (norm_nonneg _))
  have hCertS : ODEActualSourceError.Certificate E z c
      (GeneralSourceODE.Compiled.phased (J x) (phases ω)) (pN.eval x) seed y (ratio g)
        (accuracy ε) :=
    ODEActualSourceError.actual_source_certificate E hEiso z c hc
      (GeneralSourceODE.Compiled.phased (J x) (phases ω)) hJph seed hSeed hPrep (pN.eval x)
      (hAct x).1
      (fun a' i => MeshSelect.branchEvolution D σ N (nodeTable D T g ε m)
        (meshTable t T v) x (a', i))
      Sx y (ratio g)
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

/-- **The guarantee of `robust_mesh_solver` for a loader specified on its clean columns.** One
public trial family over the actual oracles `P_w`, `Lo`, `P_w†` on `N` slots and the coherent
sampled-time matrix oracle, chosen before every unknown instance; the instance hypotheses fix `Lo`
only on the clean columns `|a, τ⟩|seed⟩` of the source labels with nonzero source vectors. All
other hypotheses and the guarantee are those of `RobustOutcome`. -/
def RobustOutcomeColumns (D : Data (X × Fin M) n Z s) (t : ℕ → ℝ) (N : ℕ)
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
      (∀ r : Fin M, IntervalIntegrable (G r) volume (t r) (t ((r : ℕ) + 1))) →
      IsMeshPropagator G t T U →
      GeneralSourceODE.Compiled.WeightPrep (Pw x) (sources (sol 0) bv ω) →
      (sol 0 ≠ 0 → ∀ τ : Index D T (cq * gbar) ε,
        Lo x (PiLp.single 2 (none, τ) seed) =
          PiLp.single 2 (none, τ) (ODEStateNormalization.unitDirection (sol 0))) →
      (∀ i, ω i ≠ 0 → bv i ≠ 0 → ∀ τ : Index D T (cq * gbar) ε,
        Lo x (PiLp.single 2 (some i, τ) seed) =
          PiLp.single 2 (some i, τ) (ODEStateNormalization.unitDirection (bv i))) →
      ODESourceBranches.mass (sources (sol 0) bv ω) ≤ cq * meshScale sol b t →
      ‖sol T - U 0 (sol 0) T - ∑ i, ω i • U (v i) (bv i) T‖ ≤ ζ * meshScale sol b t →
      sol T ≠ 0 →
      meshScale sol b t ≤ gbar * ‖sol T‖ →
      RobustBudget D x t G T N cq gbar ε ζ →
      GeneralSourceODE.Oracles.ActualCertificate
        (ODERepeatProtocol.Protocol.repeatTrials tf 4) x (sol T) (s : ℝ)
        (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) (ratio (cq * gbar)) (accuracy ε))
        (ImprovedODEQueryBudget.logBudget (ratio (cq * gbar)) (accuracy ε))
        (ratio (cq * gbar)) ε

set_option maxHeartbeats 8000000 in
/-- **Theorem `ode:thm:time` with the general source interface on a mesh, represented samples of
any sign, and a loader specified on its clean columns only (item D1, exact case).** Under the
hypotheses of `robust_mesh_solver`, with the label-controlled `U_load` replaced by any unitary `Lo`
on the whole branch register: one public family of trial circuits over the coherent sampled-time
matrix oracle on `N` slots and the supplied `P_w`, `Lo` and `P_w†` gives, by four fresh trials,
`x(T)/‖x(T)‖` with conditional trace distance at most `ε` and success probability at least `2/3`,
with at most `1274019840 g' (√s Θ + √(s Θ ℓ) + ℓ)` matrix queries and at most `40 g'` calls of
each of `P_w`, `Lo` and `P_w†` in every history, for every instance satisfying the hypotheses of
`RobustOutcome` with the loading hypotheses stated on the clean columns of `Lo`. -/
theorem robust_mesh_solver_columns (D : Data (X × Fin M) n Z s) (hM : 0 < M) (t : ℕ → ℝ) {N : ℕ}
    (hN : 0 < N) (etaH etaD T gbar cq ε : ℝ) {m : ℕ} (v : Fin m → ℝ) (ω : Fin m → ℂ)
    (hH : 0 ≤ etaH) (hDiss : 0 ≤ etaD) (hT : 0 < T) (hg : 1 ≤ gbar) (hcq : 1 ≤ cq)
    (hε : 0 < ε) (hεOne : ε ≤ 1) (hmesh : IsMesh t M T)
    (hρ : 0 < etaH + radius (cq * gbar) ε * etaD)
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
  -- A label-controlled family with the clean columns of `Lo`; it is not called by the circuits.
  let J := GeneralSourceODE.columnLoader Lo seed (Sum.inr false)
  have hJ : ∀ x a, IsUnitary (J x a) := fun x a => GeneralSourceODE.loadUnitary_unitary _ _
  obtain ⟨d, E, hE, p, hSeedU, hOut, hCert⟩ := robust_propagated_solver_public D hM t hN etaH
    etaD T gbar cq ε v ω hH hDiss hT hg hcq hε hεOne hmesh hρ hClock hCayley hv hrH hcH hrD hcD
    Pw hPw J hJ seed hSeed
  have hg1 : 1 ≤ ratio (cq * gbar) := by
    unfold ratio
    nlinarith
  obtain ⟨hMpos, -, -⟩ := ODEGroverAverage.chosenIterations_bounds (ratio (cq * gbar)) hg1
  have hcpos : 0 < ODECoherentLCU.coefficientMass (lchsCoefficients D T (cq * gbar) ε) := by
    rw [Mesh.lchsCoefficients_mass D hT.le (cq * gbar) ε hg1 hε hεOne]
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

/-- `RobustOutcomeColumns` for continuous pieces with the certificate on the propagated vector
integral. -/
def RobustIntegralOutcomeColumns (D : Data (X × Fin M) n Z s) (t : ℕ → ℝ) (N : ℕ)
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
      (∀ r : Fin M, ContinuousOn (G r) (Icc (t r) (t ((r : ℕ) + 1)))) →
      (∀ r : Fin M, ContinuousOn (b r) (Icc (t r) (t ((r : ℕ) + 1)))) →
      (∀ r : Fin M, SolvesODE (G r) (b r) sol (t r) (t ((r : ℕ) + 1))) →
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
      RobustBudget D x t G T N cq gbar ε ζ →
      GeneralSourceODE.Oracles.ActualCertificate
        (ODERepeatProtocol.Protocol.repeatTrials tf 4) x (sol T) (s : ℝ)
        (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) (ratio (cq * gbar)) (accuracy ε))
        (ImprovedODEQueryBudget.logBudget (ratio (cq * gbar)) (accuracy ε))
        (ratio (cq * gbar)) ε

set_option maxHeartbeats 8000000 in
/-- **`robust_solver_integral` with a loader specified on its clean columns only.** Under the
hypotheses of `robust_mesh_solver_columns`, for continuous generator and forcing pieces,
`RobustIntegralOutcomeColumns` holds: the certificate on the propagated vector integral replaces
the one on the propagated source sum (`Mesh.mesh_duhamel`), as in `robust_solver_integral`. -/
theorem robust_solver_integral_columns (D : Data (X × Fin M) n Z s) (hM : 0 < M) (t : ℕ → ℝ) {N : ℕ}
    (hN : 0 < N) (etaH etaD T gbar cq ε : ℝ) {m : ℕ} (v : Fin m → ℝ) (ω : Fin m → ℂ)
    (hH : 0 ≤ etaH) (hDiss : 0 ≤ etaD) (hT : 0 < T) (hg : 1 ≤ gbar) (hcq : 1 ≤ cq)
    (hε : 0 < ε) (hεOne : ε ≤ 1) (hmesh : IsMesh t M T)
    (hρ : 0 < etaH + radius (cq * gbar) ε * etaD)
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
    RobustIntegralOutcomeColumns D t N etaH etaD T gbar cq ε v ω Pw Lo seed := by
  obtain ⟨d, tf, hch, hU, hC⟩ := robust_mesh_solver_columns D hM t hN etaH etaD T gbar cq ε v ω hH
    hDiss hT hg hcq hε hεOne hmesh hρ hClock hCayley hv hrH hcH hrD hcD Pw hPw Lo hLo seed hSeed
  refine ⟨d, tf, hch, hU, fun x G b sol bv U ζ hG hGc hbc hsol hUm hW hL0 hL hMass hInt hTarget
    hB hBudget => ?_⟩
  have hD := mesh_duhamel hmesh hUm hG hGc b hbc sol hsol
  have hCertP : ‖sol T - U 0 (sol 0) T - ∑ i, ω i • U (v i) (bv i) T‖ ≤ ζ * meshScale sol b t := by
    rw [← hD]
    exact hInt
  exact hC x G b sol bv U ζ hG (fun r => (hGc r).intervalIntegrable_of_Icc
    (hmesh.mono (Nat.le_succ r))) hUm hW hL0 hL hMass hCertP hTarget hB hBudget

end

end SparseHamiltonian.RepresentedSampleODE
