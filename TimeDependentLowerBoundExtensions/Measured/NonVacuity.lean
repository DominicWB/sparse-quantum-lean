import TimeDependentLowerBoundExtensions.Measured.Uniform
import TimeDependentLowerBoundExtensions.Measured.Mesh
import TimeDependentLowerBoundExtensions.Measured.Select
import TimeDependentLowerBoundExtensions.Measured.Block
import TimeDependentLowerBoundExtensions.Coherent.NonVacuity
import TimeDependentLowerBoundExtensions.BlockEncoding.NonVacuity
import DeferredMeasurementLowerBounds.Helpers.TreeContainment.Steps

set_option autoImplicit false
set_option synthInstance.maxSize 4096

/-!
# The measured time-dependent lower bounds are not vacuous

The measured forms of Theorem `hsl:thm:main` in this directory (the manuscript, eq. `hsl:eq:main`;
measured algorithms, proof of Lemma `hsl:lem:precision`) assume success probability at least `2/3`
and eq. `hsl:eq:accuracy` against every propagator of the constant path. This module shows that the
released time-dependent simulators, run as measured algorithms, meet these hypotheses on constant
data.

* `programRun p`: a program `p`, run as a measured algorithm
  (`DeferredMeasurementLowerBounds.Model.ofProgram`) and followed by the output of the whole
  workspace.
* `programRun_meets`: if `‖p.eval x ∘ ι - ι ∘ exp(-iτH_x)‖ ≤ ε` on every input for an isometric
  encoding `ι`, then from the unit vector `ι ψ` the run succeeds with probability one, its
  conditional output read through `endpointReadout ι i₀` is `ε`-accurate for `U(τ) ψ` for every
  propagator `U` of the constant path from the identity, and its worst-case cost is the cost of
  `p` (operator-norm error implies eq. `hsl:eq:accuracy`).
* `released_uniform_measured`, `released_mesh_measured`, `released_integrable_measured`,
  `released_select_measured`, `released_block_measured`: the released uniform-mesh,
  general-mesh, integrable-path, duration-selection and block-encoding simulators on constant
  data supply programs over the oracle families of `main_max_measured_uniform`,
  `main_max_measured_mesh`, `main_max_measured_select` and `main_max_measured_block` whose runs
  meet these hypotheses (for the selection simulator on every branch of total duration `τ`).
-/

namespace TimeDependentLowerBoundExtensions.Measured

noncomputable section

open SparseHamiltonian NativeSparseBlockEncoding OracleCircuit ContinuousLinearMap
open SparseLowerBounds SparseLowerBounds.Hamiltonian SparseLowerBounds.Readout
open TimeDependentHamiltonianLowerBound (constData constPath)
open AdaptiveHamiltonianLowerBound (DensityAccurate)
open DeferredMeasurementLowerBounds.Model
open scoped InnerProduct InnerProductSpace

/-! ### Programs as measured algorithms -/

section Generic

variable {X N Z : Type} [Fintype N] [DecidableEq N] {s : ℕ}
variable {K L : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The identity is an isometry (the output map of `programRun`); the same fact as
`MeasuredUnitaryLowerBound.OperatorNorm.adjoint_one_comp_one`. -/
theorem adjoint_one_comp_one : (1 : K →L[ℂ] K)† ∘L (1 : K →L[ℂ] K) = 1 := by
  rw [← ContinuousLinearMap.star_eq_adjoint, star_one]
  rfl

/-- **A program run as a measured algorithm**: the known unitaries and calls of `p`
(`DeferredMeasurementLowerBounds.Model.ofProgram`), then the output of the whole workspace. It
is the same construction as `MeasuredUnitaryLowerBound.OperatorNorm.runAll`, restated so that
this library does not depend on that one. -/
def programRun {O : L → X → K →L[ℂ] K} (p : MultiOracleCircuit.Program O) : Measured O K :=
  ofProgram p (.output 1 adjoint_one_comp_one)

/-- **Endpoint error makes a program run meet the hypotheses of the measured forms** (Section
`hsl:sec:main`: an operator-norm error at most `ε` implies eq. `hsl:eq:accuracy`): if `p` is unitary
on every input, `ι` is an isometry, `H_x` is Hermitian and `‖p.eval x ∘ ι - ι ∘ exp(-iτH_x)‖ ≤ ε` on
every input, then from the unit vector `ι ψ` the run `programRun p` succeeds with probability one,
its conditional output read through the isometry `endpointReadout ι i₀` is `ε`-accurate for `U(τ) ψ`
for every propagator `U` of the constant path from the identity, and its worst-case cost is the cost
of `p` for every weight. -/
theorem programRun_meets [FiniteDimensional ℂ K] (D : Data X N Z s)
    (hH : ∀ x, (D.matrix x).IsHermitian) {O : L → X → K →L[ℂ] K}
    (p : MultiOracleCircuit.Program O) (hp : ∀ x, IsUnitary (p.eval x))
    (ι : EuclideanSpace ℂ N →L[ℂ] K) (hι : ι† ∘L ι = 1) (i₀ : N) {ψ : EuclideanSpace ℂ N}
    (hψ : ‖ψ‖ = 1) {τ ε : ℝ} (hτ : 0 ≤ τ)
    (hsim : ∀ x, ‖p.eval x ∘L ι - ι ∘L NormedSpace.exp ((-Complex.I * (τ : ℂ)) •
      SparseStateOverlap.matrixOperator (D.matrix x))‖ ≤ ε) :
    ‖ι ψ‖ = 1 ∧ (endpointReadout ι i₀)† ∘L endpointReadout ι i₀ = 1 ∧
      (∀ x, (programRun p).successMass x (ι ψ) = 1) ∧
      (∀ x, ∀ U : ℝ → (EuclideanSpace ℂ N →L[ℂ] EuclideanSpace ℂ N), U 0 = 1 →
        TimeDependent.SolvesOn (fun u => SparseStateOverlap.matrixOperator (constPath D x u))
          U 0 τ →
        DensityAccurate (endpointReadout ι i₀) ((programRun p).conditionalDensity x (ι ψ))
          (U τ ψ) ε) ∧
      ∀ w : L → ℕ, (programRun p).worstCost w = p.cost w := by
  have h1 : (1 : K →L[ℂ] K)† = 1 := by rw [← ContinuousLinearMap.star_eq_adjoint, star_one]
  have hιψ : ‖ι ψ‖ = 1 := by rw [Reduction.norm_encode ι hι, hψ]
  have hnorm : ∀ x, ‖p.eval x (ι ψ)‖ = 1 := by
    intro x
    have h := (hp x).1
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_def] at h
    rw [Reduction.norm_encode _ h, hιψ]
  have hmass : ∀ x, (programRun p).successMass x (ι ψ) = 1 := by
    intro x
    rw [programRun, successMass_ofProgram, successMass_output, h1,
      one_apply_eq_self, hnorm x, one_pow]
  have hcond : ∀ x, (programRun p).conditionalDensity x (ι ψ) =
      ODEMixedOutput.pureOperator (p.eval x (ι ψ)) := by
    intro x
    rw [Measured.conditionalDensity, hmass x, programRun, successDensity_ofProgram,
      successDensity_output, h1, one_apply_eq_self]
    simp
  refine ⟨hιψ, endpointReadout_isometry ι hι i₀, hmass, ?_, fun w => ?_⟩
  · refine (TimeDependentHamiltonianLowerBound.densityAccurate_propagator_iff D
      (endpointReadout ι i₀) (fun x => (programRun p).conditionalDensity x (ι ψ)) ψ hτ).2
      fun x => ?_
    rw [hcond x, AdaptiveHamiltonianLowerBound.densityAccurate_pure_iff]
    exact accurate_of_endpoint ι hι i₀ (p.eval x) (hp x).norm_le_one (evolve (D.matrix x) τ)
      hψ.le (by rw [norm_evolve_apply (hH x), hψ]) (hsim x)
  · rw [programRun, worstCost_ofProgram, worstCost_output, add_zero]

end Generic

/-! ### The released simulators on constant data -/

section Released

variable {X N Z : Type} [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z] [DecidableEq Z]
  {s : ℕ}

set_option maxRecDepth 8192 in
/-- **The released uniform-mesh simulator meets the hypotheses of `main_max_measured_uniform`**
on constant data: under the hypotheses of `TimeDependent.simulation` for the constant path
(`TimeDependentHamiltonianLowerBound.uniformHyp_const_zero`), the released program over
`TimeDependent.oracle (constData D M) γ η t ε`, run as a measured algorithm from the encoded
unit input, succeeds with probability one, is `ε`-accurate for `U(t) ψ` for every propagator `U`
of the constant path, and costs what the program costs. -/
theorem released_uniform_measured (D : Data X N Z s) (hH : ∀ x, (D.matrix x).IsHermitian)
    {η : ℝ} (hrow : ∀ x i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2)
    (hcol : ∀ x j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) {M : ℕ} {t ε : ℝ} (hη : 0 < η)
    (ht : 0 ≤ t) (hε : 0 < ε) (hεHalf : ε ≤ 1 / 2) (hM : 0 < M)
    (hMesh : 4 * s * (η * t) ≤ M)
    (hCayley : 9 * (Real.sqrt s * (η * t)) ^ 3 ≤ ε * (M : ℝ) ^ 2) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 1 ≤ γ * Real.sqrt (s : ℝ) ∧
      ∃ p : MultiOracleCircuit.Program (TimeDependent.oracle (constData D M) γ η t ε),
        (p.count : ℝ) ≤ 995328 *
          (Real.sqrt (s : ℝ) * (η * t) +
            Real.sqrt ((s : ℝ) * (η * t) * Real.log (1 / ε)) + Real.log (1 / ε)) ∧
        ∀ (i₀ : N) (ψ : EuclideanSpace ℂ N), ‖ψ‖ = 1 →
          ‖TimeDependent.input (constData D M) hM γ η t ε ψ‖ = 1 ∧
          (∀ x, (programRun p).successMass x
            (TimeDependent.input (constData D M) hM γ η t ε ψ) = 1) ∧
          (∀ x, ∀ U : ℝ → (EuclideanSpace ℂ N →L[ℂ] EuclideanSpace ℂ N), U 0 = 1 →
            TimeDependent.SolvesOn
              (fun u => SparseStateOverlap.matrixOperator (constPath D x u)) U 0 t →
            DensityAccurate (endpointReadout (TimeDependent.input (constData D M) hM γ η t ε) i₀)
              ((programRun p).conditionalDensity x
                (TimeDependent.input (constData D M) hM γ η t ε ψ)) (U t ψ) ε) ∧
          ∀ w, (programRun p).worstCost w = p.cost w := by
  obtain ⟨γ, hγ, hγ1, hγs, p, hc, hin, hp, hg⟩ :=
    (TimeDependentHamiltonianLowerBound.uniformHyp_const_zero D hH hrow hcol hη ht hε hεHalf hM
      hMesh hCayley).simulation
  refine ⟨γ, hγ, hγ1, hγs, p, hc, fun i₀ ψ hψ => ?_⟩
  obtain ⟨h1, -, h2, h3, h4⟩ := programRun_meets D hH p hp _ hin i₀ hψ ht
    ((TimeDependentHamiltonianLowerBound.uniform_criterion_iff D _ _ ht).1 hg)
  exact ⟨h1, h2, h3, h4⟩

set_option maxRecDepth 8192 in
/-- **The released general-mesh simulator meets the hypotheses of `main_max_measured_mesh`** on
constant data: under the hypotheses of `TimeDependentExtensions.Hamiltonian.simulation` for
constant data (`TimeDependentHamiltonianLowerBound.meshHyp_const`), the released program over
`TimeDependentExtensions.Hamiltonian.oracle (constData D M) Nsl γ η T ε`, run as a measured
algorithm from the encoded unit input, succeeds with probability one, is `ε`-accurate for
`U(T) ψ` for every propagator `U` of the constant path, and costs what the program costs. -/
theorem released_mesh_measured (D : Data X N Z s) (hH : ∀ x, (D.matrix x).IsHermitian)
    {η : ℝ} (hrow : ∀ x i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2)
    (hcol : ∀ x j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) {M : ℕ} {t : ℕ → ℝ} {T ε : ℝ}
    {Nsl : ℕ} (hM : 0 < M) (hη : 0 < η) (hT : 0 < T) (hε : 0 < ε) (hεHalf : ε ≤ 1 / 2)
    (hN : 0 < Nsl) (hmesh : TimeDependentExtensions.IsMesh t M T)
    (hClock : 4 * s * (η * T) ≤ Nsl)
    (hCayley : 9 * (Real.sqrt s * (η * T)) ^ 3 ≤ ε * (Nsl : ℝ) ^ 2)
    (hRefine : 9 * M * (Real.sqrt s * (η * T)) ≤ ε * Nsl) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 1 ≤ γ * Real.sqrt (s : ℝ) ∧
      ∃ p : MultiOracleCircuit.Program
          (TimeDependentExtensions.Hamiltonian.oracle (constData D M) Nsl γ η T ε),
        (p.count : ℝ) ≤ 995328 *
          (Real.sqrt (s : ℝ) * (η * T) +
            Real.sqrt ((s : ℝ) * (η * T) * Real.log (1 / ε)) + Real.log (1 / ε)) ∧
        ∀ (i₀ : N) (ψ : EuclideanSpace ℂ N), ‖ψ‖ = 1 →
          ‖TimeDependentExtensions.Hamiltonian.input (constData D M) hM t Nsl γ η T ε ψ‖ = 1 ∧
          (∀ x, (programRun p).successMass x
            (TimeDependentExtensions.Hamiltonian.input (constData D M) hM t Nsl γ η T ε ψ) = 1) ∧
          (∀ x, ∀ U : ℝ → (EuclideanSpace ℂ N →L[ℂ] EuclideanSpace ℂ N), U 0 = 1 →
            TimeDependent.SolvesOn
              (fun u => SparseStateOverlap.matrixOperator (constPath D x u)) U 0 T →
            DensityAccurate (endpointReadout
                (TimeDependentExtensions.Hamiltonian.input (constData D M) hM t Nsl γ η T ε) i₀)
              ((programRun p).conditionalDensity x
                (TimeDependentExtensions.Hamiltonian.input (constData D M) hM t Nsl γ η T ε ψ))
              (U T ψ) ε) ∧
          ∀ w, (programRun p).worstCost w = p.cost w := by
  obtain ⟨γ, hγ, hγ1, hγs, p, hc, hin, hp, hg⟩ :=
    (TimeDependentHamiltonianLowerBound.meshHyp_const D hH hrow hcol hM hη hT hε hεHalf hN hmesh
      hClock hCayley hRefine).simulation
  refine ⟨γ, hγ, hγ1, hγs, p, hc, fun i₀ ψ hψ => ?_⟩
  obtain ⟨h1, -, h2, h3, h4⟩ := programRun_meets D hH p hp _ hin i₀ hψ hT.le
    (TimeDependentHamiltonianLowerBound.endpoint_of_mesh D _ _
      (TimeDependentHamiltonianLowerBound.MeshGuarantee.criterion_const hH hε.le hg))
  exact ⟨h1, h2, h3, h4⟩

set_option maxRecDepth 8192 in
/-- **The released integrable-path simulator meets the hypotheses of `main_max_measured_mesh`**
on constant data: as `released_mesh_measured`, for the program of
`IntegrablePathSimulation.Hamiltonian.simulation` over the same family
`TimeDependentExtensions.Hamiltonian.oracle (constData D M) Nsl γ η T ε`. -/
theorem released_integrable_measured (D : Data X N Z s) (hH : ∀ x, (D.matrix x).IsHermitian)
    {η : ℝ} (hrow : ∀ x i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2)
    (hcol : ∀ x j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) {M : ℕ} {t : ℕ → ℝ} {T ε : ℝ}
    {Nsl : ℕ} (hM : 0 < M) (hη : 0 < η) (hT : 0 < T) (hε : 0 < ε) (hεHalf : ε ≤ 1 / 2)
    (hN : 0 < Nsl) (hmesh : TimeDependentExtensions.IsMesh t M T)
    (hClock : 4 * s * (η * T) ≤ Nsl)
    (hCayley : 9 * (Real.sqrt s * (η * T)) ^ 3 ≤ ε * (Nsl : ℝ) ^ 2)
    (hRefine : 9 * M * (Real.sqrt s * (η * T)) ≤ ε * Nsl) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 1 ≤ γ * Real.sqrt (s : ℝ) ∧
      ∃ p : MultiOracleCircuit.Program
          (TimeDependentExtensions.Hamiltonian.oracle (constData D M) Nsl γ η T ε),
        (p.count : ℝ) ≤ 995328 *
          (Real.sqrt (s : ℝ) * (η * T) +
            Real.sqrt ((s : ℝ) * (η * T) * Real.log (1 / ε)) + Real.log (1 / ε)) ∧
        ∀ (i₀ : N) (ψ : EuclideanSpace ℂ N), ‖ψ‖ = 1 →
          ‖TimeDependentExtensions.Hamiltonian.input (constData D M) hM t Nsl γ η T ε ψ‖ = 1 ∧
          (∀ x, (programRun p).successMass x
            (TimeDependentExtensions.Hamiltonian.input (constData D M) hM t Nsl γ η T ε ψ) = 1) ∧
          (∀ x, ∀ U : ℝ → (EuclideanSpace ℂ N →L[ℂ] EuclideanSpace ℂ N), U 0 = 1 →
            TimeDependent.SolvesOn
              (fun u => SparseStateOverlap.matrixOperator (constPath D x u)) U 0 T →
            DensityAccurate (endpointReadout
                (TimeDependentExtensions.Hamiltonian.input (constData D M) hM t Nsl γ η T ε) i₀)
              ((programRun p).conditionalDensity x
                (TimeDependentExtensions.Hamiltonian.input (constData D M) hM t Nsl γ η T ε ψ))
              (U T ψ) ε) ∧
          ∀ w, (programRun p).worstCost w = p.cost w := by
  obtain ⟨γ, hγ, hγ1, hγs, p, hc, hin, hp, hg⟩ :=
    (TimeDependentHamiltonianLowerBound.meshHyp_const D hH hrow hcol hM hη hT hε hεHalf hN hmesh
      hClock hCayley hRefine).simulation_integrable
  refine ⟨γ, hγ, hγ1, hγs, p, hc, fun i₀ ψ hψ => ?_⟩
  obtain ⟨h1, -, h2, h3, h4⟩ := programRun_meets D hH p hp _ hin i₀ hψ hT.le
    ((TimeDependentHamiltonianLowerBound.integrable_criterion_iff D _ _ hT.le).1
      (TimeDependentHamiltonianLowerBound.IntegrableGuarantee.criterion_const hH hε.le hg))
  exact ⟨h1, h2, h3, h4⟩

set_option maxRecDepth 8192 in
/-- **The released duration-selection simulator meets the hypotheses of
`main_max_measured_select`** on constant data: under the hypotheses of
`TimeDependentExtensions.Coherent.coherent_select`, for every public duration table the
released program over the selection family, run as a measured algorithm from the input
`E (|i₀⟩ ⊗ ψ)` of a branch `i₀` of total duration `τ` (`E` the clean isometric input encoding,
`Coherent.branchInj`), succeeds with probability one, is `ε`-accurate for `U(τ) ψ` for every
propagator `U` of the constant path, and costs what the program costs. -/
theorem released_select_measured {ι : Type} [Fintype ι] [DecidableEq ι] (D : Data X N Z s)
    (hH : ∀ x, (D.matrix x).IsHermitian) {η : ℝ}
    (hrow : ∀ x i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2)
    (hcol : ∀ x j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) {M : ℕ} (hM : 0 < M) (σ : ℕ → Fin M)
    {Nsl : ℕ} (hN : 0 < Nsl) (b0 : ι × Fin M) (T ε : ℝ) (hη : 0 < η) (hT : 0 < T)
    (hε : 0 < ε) (hεOne : ε ≤ 1) (hClock : 8 * s * (η * T) ≤ Nsl)
    (hCayley : 3 * (Real.sqrt (2 * (s : ℝ)) * (η * T)) ^ 3 ≤ ε * (Nsl : ℝ) ^ 2) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 1 ≤ γ * Real.sqrt (2 * (s : ℝ)) ∧
      ∀ u : ι → Fin M → ℝ, (∀ i r, 0 ≤ u i r) → (∀ i r, u i r ≤ T) →
      ∃ p : MultiOracleCircuit.Program
          (TimeDependentExtensions.MeshSelect.alignedOracle (ι := ι) (constData D M) Nsl γ η T ε),
        (p.count : ℝ) ≤ 663552 * ImprovedPrecisionBudget.shape (2 * (s : ℝ)) (η * T)
          (ImprovedPrecisionBudget.targetLog ε) ∧
        ∀ (i₀ : ι) (τ : ℝ), ∑ k ∈ Finset.range Nsl, u i₀ (σ k) / (Nsl : ℝ) = τ →
        ∀ (n₀ : N) (ψ : EuclideanSpace ℂ N), ‖ψ‖ = 1 →
          ‖(TimeDependentExtensions.MeshSelect.alignedInput (constData D M) hM σ b0 Nsl γ η T ε ∘L
            Coherent.branchInj ι N i₀) ψ‖ = 1 ∧
          (∀ x, (programRun p).successMass x
            ((TimeDependentExtensions.MeshSelect.alignedInput (constData D M) hM σ b0 Nsl γ η T ε
              ∘L Coherent.branchInj ι N i₀) ψ) = 1) ∧
          (∀ x, ∀ U : ℝ → (EuclideanSpace ℂ N →L[ℂ] EuclideanSpace ℂ N), U 0 = 1 →
            TimeDependent.SolvesOn
              (fun u => SparseStateOverlap.matrixOperator (constPath D x u)) U 0 τ →
            DensityAccurate (endpointReadout
                (TimeDependentExtensions.MeshSelect.alignedInput (constData D M) hM σ b0 Nsl γ η
                  T ε ∘L Coherent.branchInj ι N i₀) n₀)
              ((programRun p).conditionalDensity x
                ((TimeDependentExtensions.MeshSelect.alignedInput (constData D M) hM σ b0 Nsl γ η
                  T ε ∘L Coherent.branchInj ι N i₀) ψ)) (U τ ψ) ε) ∧
          ∀ w, (programRun p).worstCost w = p.cost w := by
  obtain ⟨γ, hγ, hγ1, hγs, hAll⟩ := Coherent.exists_selectProgram D hH hrow hcol hM σ hN b0 T ε
    hη hT hε hεOne hClock hCayley
  refine ⟨γ, hγ, hγ1, hγs, fun u hu huT => ?_⟩
  obtain ⟨p, hc, hin, hcrit⟩ := hAll u hu huT
  refine ⟨p, hc, fun i₀ τ hdur n₀ ψ hψ => ?_⟩
  have hτ : 0 ≤ τ := by
    rw [← hdur]
    exact Finset.sum_nonneg fun k _ => div_nonneg (hu _ _) (Nat.cast_nonneg _)
  have hiso : (TimeDependentExtensions.MeshSelect.alignedInput (constData D M) hM σ b0 Nsl γ η
      T ε ∘L Coherent.branchInj ι N i₀)† ∘L
      (TimeDependentExtensions.MeshSelect.alignedInput (constData D M) hM σ b0 Nsl γ η T ε ∘L
        Coherent.branchInj ι N i₀) = 1 := by
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_assoc,
      ← ContinuousLinearMap.comp_assoc _ _ (Coherent.branchInj ι N i₀), hin,
      ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp]
    exact Coherent.branchInj_isometry i₀
  have hp : ∀ x, IsUnitary (p.eval x) := MultiOracleCircuit.Program.eval_unitary p
    (TimeDependentExtensions.MeshSelect.alignedOracle_unitary (constData D M) Nsl γ η T ε)
  obtain ⟨h1, -, h2, h3, h4⟩ := programRun_meets D hH p hp _ hiso n₀ hψ hτ
    (Coherent.select_endpoint D M Nsl σ u i₀ hdur p.eval _ hcrit)
  exact ⟨h1, h2, h3, h4⟩

set_option maxRecDepth 8192 in
/-- **The released block-encoding simulator meets the hypotheses of `main_max_measured_block`**
on the constant block encodings: under the mesh and slot conditions of
`TimeDependentExtensions.BlockEncoding.simulation` at normalisation `α_BE = beAlpha D`, the
released program over `TimeDependentExtensions.BlockEncoding.alignedOracle (beConst D M) Nsl
(beAlpha D) T ε`, run as a measured algorithm from the encoded unit input, succeeds with
probability one, is `ε`-accurate for `U(T) ψ` for every propagator `U` of the constant path, and
costs what the program costs. -/
theorem released_block_measured (D : Data X N Z s) (hH : ∀ x, (D.matrix x).IsHermitian)
    {M : ℕ} (hM : 0 < M) (b₀ : BlockEncoding.BEBasis N Z) (t : ℕ → ℝ) (T ε : ℝ) (Nsl : ℕ)
    (hT : 0 < T) (hε : 0 < ε) (hεOne : ε ≤ 1) (hN : 0 < Nsl)
    (hmesh : TimeDependentExtensions.IsMesh t M T)
    (hClock : 4 * (BlockEncoding.beAlpha D * T) ≤ Nsl)
    (hCayley : 9 * (BlockEncoding.beAlpha D * T) ^ 3 ≤ ε * (Nsl : ℝ) ^ 2)
    (hRefine : 9 * M * (BlockEncoding.beAlpha D * T) ≤ ε * Nsl) :
    ∃ p : MultiOracleCircuit.Program (TimeDependentExtensions.BlockEncoding.alignedOracle
        (BlockEncoding.beConst D M) Nsl (BlockEncoding.beAlpha D) T ε),
      (p.count : ℝ) ≤ 2304 * (BlockEncoding.beAlpha D * T + 1 + Real.log (3 / ε)) ∧
      ∀ (i₀ : N) (ψ : EuclideanSpace ℂ N), ‖ψ‖ = 1 →
        ‖TimeDependentExtensions.BlockEncoding.alignedInput hM b₀ (BlockEncoding.beJ D)
          (BlockEncoding.beJ_isometry D) t Nsl (BlockEncoding.beAlpha D) T ε ψ‖ = 1 ∧
        (∀ x, (programRun p).successMass x
          (TimeDependentExtensions.BlockEncoding.alignedInput hM b₀ (BlockEncoding.beJ D)
            (BlockEncoding.beJ_isometry D) t Nsl (BlockEncoding.beAlpha D) T ε ψ) = 1) ∧
        (∀ x, ∀ U : ℝ → (EuclideanSpace ℂ N →L[ℂ] EuclideanSpace ℂ N), U 0 = 1 →
          TimeDependent.SolvesOn
            (fun u => SparseStateOverlap.matrixOperator (constPath D x u)) U 0 T →
          DensityAccurate (endpointReadout
              (TimeDependentExtensions.BlockEncoding.alignedInput hM b₀ (BlockEncoding.beJ D)
                (BlockEncoding.beJ_isometry D) t Nsl (BlockEncoding.beAlpha D) T ε) i₀)
            ((programRun p).conditionalDensity x
              (TimeDependentExtensions.BlockEncoding.alignedInput hM b₀ (BlockEncoding.beJ D)
                (BlockEncoding.beJ_isometry D) t Nsl (BlockEncoding.beAlpha D) T ε ψ))
            (U T ψ) ε) ∧
        ∀ w, (programRun p).worstCost w = p.cost w := by
  obtain ⟨p, hc, hin, hcrit⟩ := BlockEncoding.exists_beProgram D hM b₀ t T ε Nsl hT hε hεOne hN
    hmesh hClock hCayley hRefine
  refine ⟨p, hc, fun i₀ ψ hψ => ?_⟩
  have hp : ∀ x, IsUnitary (p.eval x) := MultiOracleCircuit.Program.eval_unitary p
    (BlockEncoding.alignedOracle_beConst_unitary D M Nsl (BlockEncoding.beAlpha D) T ε)
  obtain ⟨h1, -, h2, h3, h4⟩ := programRun_meets D hH p hp _ hin i₀ hψ hT.le
    (BlockEncoding.beCriterion_endpoint D hH M t hε.le p.eval _ hcrit)
  exact ⟨h1, h2, h3, h4⟩

end Released

end

end TimeDependentLowerBoundExtensions.Measured
