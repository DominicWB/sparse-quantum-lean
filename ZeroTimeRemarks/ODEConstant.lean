import SparseODE.ODECompleteSuccess
import ZeroTimeRemarks.Hamiltonian

/-!
# Theorem `ode:thm:main` at zero time or with a known zero generator

Theorem `ode:thm:main` of the accompanying paper is followed (after eq. `ode:eq:simple`) by "At
zero time or for a known zero generator, the solver assembles the initial and source terms directly.
It makes no matrix queries outside the supplied input and source preparations." The released
endpoint `SparseHamiltonian.ODECompleteEndpoint.solver` already treats both cases, by source-only
circuit families whose matrix oracle is a placeholder (`ZeroTimeOutcome`: one initial-state call per
trial; `ZeroEnergyOutcome`: `ODEDegenerateSource`). This file states both cases in the native sparse
oracle family of the positive branch (`ODECompleteEndpoint.PositiveOutcome`:
`ODEFinalNativeSource.physicalOracle`, with the same public seed, output flag, trial family and
complete certificate), with worst-case matrix-query count `0`, and gives one native statement for
every `T ≥ 0` and every pair of energy bounds.

**Direct source assembly.** The released positive branch loads the two sources, runs the
native SELECT program `p` of the LCHS branch evolutions and unloads the coefficients. If every
branch evolution is the identity, the identity program is an exact SELECT for any isometric
clean encoding. This holds at `T = 0` (all durations vanish) and for a known zero generator
(the public bounds `η_H = η_D = 0` force every instance matrix to vanish, so `A = 0` and the
target is `x₀ + T b`). The released LCHS table, quadrature and source certificates then give
the released trial certificate with no matrix query (`trial_matrix_cost`).

* `BudgetOutcome … Q`: the released `PositiveOutcome` in which the certified four-attempt
  protocol has worst-case matrix-query count at most `Q`; `outcome_of_budget`,
  `budget_of_outcome`.
* `zero_solver`: the cases `T = 0` and `η_H + R η_D = 0`, with `Q = 0`.
* `native_solver`, `solver_nonneg`: Theorem `ode:thm:main` in the native family for every
  `T ≥ 0`, with `Q = 0` in the zero cases and the released bound otherwise.
-/

set_option autoImplicit false

namespace SparseHamiltonian.ZeroTimeRemarks.ODEConstant

noncomputable section
open ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding
open scoped BigOperators InnerProduct
set_option maxRecDepth 4096
set_option synthInstance.maxSize 4096

variable {X n Z : Type*} [Fintype n] [DecidableEq n]
  [Fintype Z] [AddCommGroup Z] [DecidableEq Z] {s : ℕ}

/-- The clean encoding of the released native SELECT is an isometry for all public
parameters, including `T = 0` and `ρ = 0` (`ode:thm:main`). -/
theorem encoding_isometry {σ ι : Type*} [Fintype σ] [DecidableEq σ] [Fintype ι] [DecidableEq ι]
    (D : Data X n Z s) (i0 : σ × ι) (γ ρ T δ : ℝ) :
    (ODENativeSourceCertificate.encoding D i0 γ ρ T δ)† ∘L
      ODENativeSourceCertificate.encoding D i0 γ ρ T δ = 1 :=
  AlignedMultiOracleProgram.input_isometry _
    (NativeSparseAttenuation.isometry_comp _ _
      (SharpClockQuery.input_isometry _ _ _ _ _ (CayleyClockInterface.width_ge_one _ _))
      (ODEJointSimulation.embedding D i0 γ ρ T δ).adjoint_comp_self)

set_option maxHeartbeats 3000000 in
/-- With the identity SELECT, every trial of the released public family makes no native matrix
query: the compiler multiplies the count of the source-loaded preparation by `3 (2j + 1)`
(`ode:thm:main`). -/
theorem trial_matrix_cost {ι : Type*} [Fintype ι] [DecidableEq ι] (D : Data X n Z s) (i0 : ι)
    (N Tslots d : ℕ)
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (E : ODEFinalNativeSource.SourceSpace ι n N →L[ℂ]
      ODEFinalNativeSource.MatrixSpace ι n Z N Tslots d) (hE : E† ∘L E = 1)
    (a : Option (Fin N) × ι → ℂ) (v : EuclideanSpace ℂ n)
    (hSeed : ‖ODECompiledSource.seed E a v‖ = 1)
    (hOutput : (ODECompiledSource.output E a)† ∘L ODECompiledSource.output E a = 1) (j : ℕ) :
    (ODEFinalNativeSource.publicTrials D i0 N Tslots d MultiOracleCircuit.Program.identity
      J₀ Jb E hE a v hSeed hOutput j).cost
        (ODESourceQueryBudget.matrixWeight (fun _ => 1)) = 0 := by
  unfold ODEFinalNativeSource.publicTrials
  rw [ODEFinalNativeSource.compile_matrix_cost]
  unfold ODEPrimitiveSourceJoin.publicLogicalTrials
  rw [ODECountedAmplification.cost_eq]
  apply Nat.mul_eq_zero.mpr
  right
  apply Nat.mul_eq_zero.mpr
  right
  exact (ODECompiledSource.program_matrix_cost _ J₀ Jb E hE _).trans
    (MultiOracleCircuit.Program.cost_identity _)

set_option maxHeartbeats 3000000 in
/-- **The native outcome with a matrix-query budget** (`ode:thm:main`). One public trial family
over the native oracle family of the released positive branch, with its public seed and output
flag, chosen before the instance, such that for every valid instance the released complete
certificate `ODECompleteTrial.Certificate` holds and the certified four-attempt protocol has
worst-case matrix-query count at most `Q`, so every history makes at most `Q` native matrix
queries. Without the budget this is the released `ODECompleteEndpoint.PositiveOutcome`
(`outcome_of_budget`). -/
def BudgetOutcome (D : Data X n Z s) (etaH etaD T g ε r₀ rb : ℝ)
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (seed : EuclideanSpace ℂ n) (Q : ℝ) : Prop :=
  ∃ (Tslots d : ℕ)
    (E : ODEFinalNativeSource.SourceSpace
        (Fin (ODEPublicGaussianEndpoint.gridSize D T g ε) ⊕ Bool) n
        (ODEPublicSourceMesh.meshSize D T (ImprovedODEQueryBudget.precision g ε)) →L[ℂ]
      ODEFinalNativeSource.MatrixSpace
        (Fin (ODEPublicGaussianEndpoint.gridSize D T g ε) ⊕ Bool) n Z
        (ODEPublicSourceMesh.meshSize D T (ImprovedODEQueryBudget.precision g ε)) Tslots d)
    (q : ℕ → MultiOracleCircuit.Program
      (ODEFinalNativeSource.physicalOracle
        (ι := Fin (ODEPublicGaussianEndpoint.gridSize D T g ε) ⊕ Bool)
        D (ODEPublicSourceMesh.meshSize D T (ImprovedODEQueryBudget.precision g ε))
        Tslots d J₀ Jb)),
    (∀ j y, IsUnitary ((q j).eval y)) ∧
      ∀ (v b : EuclideanSpace ℂ n) (x : X),
        ‖v‖ = r₀ → ‖b‖ = rb →
        (v ≠ 0 → J₀ x seed = ODEStateNormalization.unitDirection v) →
        (b ≠ 0 → Jb x seed = ODEStateNormalization.unitDirection b) →
        ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T ≠ 0 →
        r₀ + T * rb ≤
          g * ‖ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T‖ →
        ∃ h : ODECompleteTrial.Certificate q (ODEGroverAverage.chosenIterations g)
          (ODEFinalNativeSource.input D (Sum.inr false)
            (ODEPublicSourceMesh.meshSize D T (ImprovedODEQueryBudget.precision g ε))
            Tslots d (ODECompiledSource.seed E
              (ODESourcePublicNorms.publicCoefficients r₀ rb T
                (ODEPublicSourceMesh.meshSize D T (ImprovedODEQueryBudget.precision g ε))
                (ODECoefficientPadding.paddedCoefficient
                  (ODEPublicGaussianEndpoint.coefficients D T g ε) 3)) seed))
          (ODEFinalNativeSource.input D (Sum.inr false)
            (ODEPublicSourceMesh.meshSize D T (ImprovedODEQueryBudget.precision g ε))
            Tslots d ∘L ODECompiledSource.output E
              (ODESourcePublicNorms.publicCoefficients r₀ rb T
                (ODEPublicSourceMesh.meshSize D T (ImprovedODEQueryBudget.precision g ε))
                (ODECoefficientPadding.paddedCoefficient
                  (ODEPublicGaussianEndpoint.coefficients D T g ε) 3)))
          x (ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T)
          (s : ℝ) (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) g ε)
          (ImprovedODEQueryBudget.logBudget g ε) g ε,
          ((ODECompleteTrial.algorithm h.trial).worstCost
            (ODESourceQueryBudget.matrixWeight (fun _ => 1)) : ℝ) ≤ Q

set_option maxHeartbeats 3000000 in
/-- **The released trial family with the identity SELECT** (`ode:thm:main`). For every label
type, clean encoding `E` and public coefficient table `a`, the released public trial family
`ODEFinalNativeSource.publicTrials` built on the identity program consists of unitary circuits
and, for every instance whose source certificate holds for the identity program with actual
coefficients `a`, satisfies the released complete certificate with worst-case matrix-query
count `0`. -/
theorem identity_trials {ι : Type*} [Fintype ι] [DecidableEq ι] (D : Data X n Z s) (i0 : ι)
    (N Tslots d : ℕ) (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ₀ : ∀ x, IsUnitary (J₀ x)) (hJb : ∀ x, IsUnitary (Jb x))
    (E : ODEFinalNativeSource.SourceSpace ι n N →L[ℂ]
      ODEFinalNativeSource.MatrixSpace ι n Z N Tslots d) (hE : E† ∘L E = 1)
    (c : ι → ℂ) (a : Option (Fin N) × ι → ℂ) (ha : 0 < ODECoherentLCU.coefficientMass a)
    (seed : EuclideanSpace ℂ n) (hSeed : ‖seed‖ = 1) (Θ ell g ε : ℝ) (hg : 1 ≤ g) (hε : 0 ≤ ε)
    (hShape : 0 ≤ ImprovedODEQueryBudget.queryShape (s : ℝ) Θ ell) :
    ∃ q : ℕ → MultiOracleCircuit.Program
        (ODEFinalNativeSource.physicalOracle (ι := ι) D N Tslots d J₀ Jb),
      (∀ j y, IsUnitary ((q j).eval y)) ∧
      ∀ (x : X) (z : Option (Fin N) → EuclideanSpace ℂ n) (target : EuclideanSpace ℂ n),
        ODEActualSourceError.Certificate E z c
          (ODESourcePreparations.branch (J₀ x) (Jb x) N)
          ((MultiOracleCircuit.Program.identity
            (O := ODEFinalNativeSource.matrixOracle (ι := ι) D N Tslots d)).eval x)
          seed target g ε →
        ODEActualSourceError.coefficients z c = a → target ≠ 0 →
        ∃ h : ODECompleteTrial.Certificate q (ODEGroverAverage.chosenIterations g)
          (ODEFinalNativeSource.input D i0 N Tslots d (ODECompiledSource.seed E a seed))
          (ODEFinalNativeSource.input D i0 N Tslots d ∘L ODECompiledSource.output E a)
          x target (s : ℝ) Θ ell g ε,
          ((ODECompleteTrial.algorithm h.trial).worstCost
            (ODESourceQueryBudget.matrixWeight (fun _ => 1)) : ℝ) ≤ 0 := by
  let pN : MultiOracleCircuit.Program
      (ODEFinalNativeSource.matrixOracle (ι := ι) D N Tslots d) :=
    MultiOracleCircuit.Program.identity
  let q := ODEFinalNativeSource.publicTrials D i0 N Tslots d pN J₀ Jb E hE a seed
    (ODECompiledSource.seed_unit E a hE ha seed hSeed)
    (ODECompiledSource.output_isometry E a hE ha)
  have hCost : ∀ j, (q j).cost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) = 0 :=
    fun j => trial_matrix_cost D i0 N Tslots d J₀ Jb E hE a seed _ _ j
  have hUnitary : ∀ j y, IsUnitary ((q j).eval y) := fun j y =>
    (q j).eval_unitary
      (ODEFinalNativeSource.physicalOracle_unitary (ι := ι) D N Tslots d J₀ Jb hJ₀ hJb) y
  refine ⟨q, hUnitary, fun x z target hCert hCoeff hTarget => ?_⟩
  have hq : (pN.count : ℝ) ≤ 10616832 * ImprovedODEQueryBudget.queryShape (s : ℝ) Θ ell := by
    rw [MultiOracleCircuit.Program.count_identity, Nat.cast_zero]
    exact mul_nonneg (by norm_num) hShape
  have hTrial := ODEUniformNativeSource.coefficient_trial_certificate
    D i0 N Tslots d pN J₀ Jb hJ₀ hJb E hE z c seed target hSeed Θ ell g ε hg x hCert hq a ha
    hCoeff
  have hFull := ODECompleteTrial.of_trialCertificate (fun j => hUnitary j x) hε hTarget hTrial
  refine ⟨hFull, ?_⟩
  have hW := ODERepeatProtocol.fourTrials_worstCost_le q (ODEGroverAverage.chosenIterations g)
    hFull.trial.cutoff_pos _ hFull.trial.seed_unit _ hFull.trial.output_isometry
    (ODESourceQueryBudget.matrixWeight (fun _ => 1)) 0
    (fun j _ => by rw [hCost j, Nat.cast_zero])
  rw [mul_zero] at hW
  exact hW

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- A branch evolution of zero duration is the identity (`ode:thm:main`). -/
theorem branchEvolution_eq_one_of_time {ι : Type*} (D : Data X n Z s) (k u : ι → ℝ) (x : X)
    (i : ι) (hu : u i = 0) : ODENativeLCU.branchEvolution D k u x i = 1 := by
  unfold ODENativeLCU.branchEvolution
  rw [hu]
  exact Hamiltonian.exp_eq_one 0 _ (Or.inl rfl)

set_option maxHeartbeats 4000000 in
/-- **Theorem `ode:thm:main` at zero time or with a known zero generator.** If `T = 0` or the
public energy bounds give `η_H + R η_D = 0` (`R` the public LCHS radius), the released trial
family with the identity SELECT satisfies `BudgetOutcome` with `Q = 0`: in the native oracle
family of the positive branch, with its public seed and flag, every valid instance has the
released complete certificate (success at least `175/256 > 2/3`, conditional trace distance at
most `ε`, at most `40 g` calls of each source interface), and the protocol makes no native
matrix query in any history. The column promises are not needed. -/
theorem zero_solver (D : Data X n Z s) (etaH etaD T g ε r₀ rb : ℝ)
    (hH : 0 ≤ etaH) (hDiss : 0 ≤ etaD) (hT : 0 ≤ T)
    (hZero : T = 0 ∨ etaH + ImprovedODEQueryBudget.radius g ε * etaD = 0)
    (hg : 1 ≤ g) (hε : 0 < ε) (hεHalf : ε ≤ 1 / 2)
    (h₀ : 0 ≤ r₀) (hb : 0 ≤ rb) (hB : 0 < r₀ + T * rb)
    (hrH : ∀ x i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ etaH ^ 2)
    (hrD : ∀ x i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ etaD ^ 2)
    (hPSD : ∀ (x : X) (w : EuclideanSpace ℂ n), 0 ≤ (inner ℂ w
      (SparseStateOverlap.matrixOperator (ODEMatrixEnergy.dissipativePart (D.matrix x)) w)).re)
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ₀ : ∀ x, IsUnitary (J₀ x)) (hJb : ∀ x, IsUnitary (Jb x))
    (seed : EuclideanSpace ℂ n) (hSeed : ‖seed‖ = 1) :
    BudgetOutcome D etaH etaD T g ε r₀ rb J₀ Jb seed 0 := by
  let ν : ℝ := ImprovedODEQueryBudget.precision g ε
  let N : ℕ := ODEPublicSourceMesh.meshSize D T ν
  let I := Fin (ODEPublicGaussianEndpoint.gridSize D T g ε) ⊕ Bool
  let c : I → ℂ := ODECoefficientPadding.paddedCoefficient
    (ODEPublicGaussianEndpoint.coefficients D T g ε) 3
  let k := ODEPublicGaussianEndpoint.nodes D T g ε
  let kTable : Option (Fin N) × I → ℝ :=
    fun a => ODECoefficientPadding.paddedNodes k a.2
  let uTable : Option (Fin N) × I → ℝ :=
    fun a => ODESourceBranches.duration T N a.1
  have hν : 0 < ν := ImprovedODEQueryBudget.precision_pos g ε hg hε
  have hN : 0 < N := ODEPublicSourceMesh.meshSize_pos D T ν
  have hεOne : ε ≤ 1 := hεHalf.trans (by norm_num)
  have hTable := ODEPublicGaussianEndpoint.table_certificate D hPSD T g ε hT hg hε hεOne
  have hc : ODECoherentLCU.coefficientMass c = 3 :=
    ODECoefficientPadding.coefficientMass_eq _ 3 hTable.2.2.1
  have hDuration : ∀ a : Option (Fin N),
      0 ≤ ODESourceBranches.duration T N a ∧ ODESourceBranches.duration T N a ≤ T := by
    intro a
    cases a with
    | none => exact ⟨hT, le_rfl⟩
    | some i => exact ⟨ODESourceQuadrature.time_nonneg T hT N i,
        ODESourceQuadrature.time_le T hT N hN i⟩
  -- Every branch evolution is the identity.
  have hOne : ∀ (x : X) (a : Option (Fin N) × I),
      ODENativeLCU.branchEvolution D kTable uTable x a = 1 := by
    intro x a
    rcases hZero with hT0 | hρ
    · apply branchEvolution_eq_one_of_time
      have h := hDuration a.1
      change ODESourceBranches.duration T N a.1 = 0
      rw [hT0] at h ⊢
      exact le_antisymm h.2 h.1
    · have hRadius : 0 < ImprovedODEQueryBudget.radius g ε :=
        lt_of_lt_of_le (by norm_num : (0 : ℝ) < 4)
          (ODEGaussianParameters.radius_ge_four g ε hg hε hεOne)
      have hMatrix := ODEZeroEnergy.matrix_zero_of_effective_energy (D.matrix x) etaH etaD
        (ImprovedODEQueryBudget.radius g ε) hH hDiss hRadius hρ (hrH x) (hrD x)
      exact ODEZeroEnergy.branchEvolution_eq_one_of_matrix_zero D kTable uTable x hMatrix a
  let ρ : ℝ := etaH + ImprovedODEQueryBudget.radius g ε * etaD
  let Tslots := ODENativeSimulation.slots (s : ℝ) 1 ρ T ν
  let d := ODENativeSimulation.degree (s : ℝ) 1 ρ T ν
  let E : ODEFinalNativeSource.SourceSpace I n N →L[ℂ]
      ODEFinalNativeSource.MatrixSpace I n Z N Tslots d :=
    ODENativeSourceCertificate.encoding (σ := Option (Fin N)) (ι := I)
      D (none, Sum.inr false) 1 ρ T ν
  have hEncoding : E† ∘L E = 1 := encoding_isometry D (none, Sum.inr false) 1 ρ T ν
  let a : Option (Fin N) × I → ℂ :=
    ODESourcePublicNorms.publicCoefficients r₀ rb T N c
  have ha : 0 < ODECoherentLCU.coefficientMass a := by
    rw [ODESourcePublicNorms.publicCoefficients_mass r₀ rb T N h₀ hb hT hN hB c hc]
    norm_num
  have hΘ : 0 ≤ ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) g ε :=
    ImprovedODEQueryBudget.theta_nonneg _ _ g ε (mul_nonneg hT hH) (mul_nonneg hT hDiss)
      hg hε hεOne
  have hL : 0 ≤ ImprovedODEQueryBudget.logBudget g ε :=
    le_trans zero_le_one (ImprovedODEQueryBudget.logBudget_ge_one g ε hg hε hεOne)
  obtain ⟨q, hUnitary, hTrials⟩ := identity_trials D (Sum.inr false) N Tslots d J₀ Jb hJ₀ hJb
    E hEncoding c a ha seed hSeed (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) g ε)
    (ImprovedODEQueryBudget.logBudget g ε) g ε hg hε.le
    (ImprovedODEQueryBudget.queryShape_nonneg _ _ _ hΘ hL)
  refine ⟨Tslots, d, E, q, hUnitary, ?_⟩
  intro v b x hv hbnorm hInitial hForcing hTarget hBudget
  have hA : ODEDissipative.Dissipative (ODEPublicSourceMesh.generator D x) :=
    ODEPublicSourceMesh.generator_dissipative D x (hPSD x)
  have hMesh := ODEPublicSourceMesh.branches_certificate D T ν hT hν x hA v b
  have hSourceBudget : ODESourceBranches.mass (ODESourceBranches.sourceVector v b T N) ≤
      g * ‖ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T‖ := by
    rw [hMesh.2.1, hv, hbnorm]
    exact hBudget
  have hPrep := ODESourcePreparations.branch_prepares (J₀ x) (Jb x) seed v b
    T hT N hInitial hForcing
  have hPaddedLCHS : ∀ a' : Option (Fin N),
      ‖(∑ i : I, c i • ODENativeLCU.branchEvolution D kTable uTable x (a', i)) -
        ODESourceBranches.propagation (ODEPublicSourceMesh.generator D x) T N a'‖ ≤ 2 * ν := by
    intro a'
    have hSum := ODESourcePadding.branch_sum_eq D
      (ODEPublicGaussianEndpoint.coefficients D T g ε) 3 k
      (ODESourceBranches.duration T N) x a'
    change ‖(∑ i : I, ODECoefficientPadding.paddedCoefficient
        (ODEPublicGaussianEndpoint.coefficients D T g ε) 3 i •
        ODENativeLCU.branchEvolution D
          (fun j : Option (Fin N) × I => ODECoefficientPadding.paddedNodes k j.2)
          (fun j => ODESourceBranches.duration T N j.1) x (a', i)) -
      ODESourceBranches.propagation (ODEPublicSourceMesh.generator D x) T N a'‖ ≤ 2 * ν
    rw [hSum]
    exact hTable.2.2.2 x (ODESourceBranches.duration T N a')
      (hDuration a').1 (hDuration a').2
  have hBranch : ∀ a' : Option (Fin N),
      (ODESourcePreparations.branch (J₀ x) (Jb x) N a')† ∘L
        ODESourcePreparations.branch (J₀ x) (Jb x) N a' = 1 :=
    ODESourcePreparations.branch_isometry (J₀ x) (Jb x) N (hJ₀ x).1 (hJb x).1
  have hSim : ‖(MultiOracleCircuit.Program.identity
        (O := ODEFinalNativeSource.matrixOracle (ι := I) D N Tslots d)).eval x ∘L E -
      E ∘L WeightedClock.diagonal (fun a' : Option (Fin N) × I =>
        ODENativeLCU.branchEvolution D kTable uTable x (a'.1, a'.2))‖ ≤ ν := by
    have hDiag : WeightedClock.diagonal
        (fun a' : Option (Fin N) × I =>
          ODENativeLCU.branchEvolution D kTable uTable x (a'.1, a'.2)) = 1 := by
      simp only [hOne]
      exact WeightedClock.diagonal_one
    rw [hDiag, MultiOracleCircuit.Program.eval_identity, sub_eq_zero.mpr, norm_zero]
    · exact hν.le
    · rfl
  have hCert : ODEActualSourceError.Certificate E
      (ODESourceBranches.sourceVector v b T N) c
      (ODESourcePreparations.branch (J₀ x) (Jb x) N)
      ((MultiOracleCircuit.Program.identity
        (O := ODEFinalNativeSource.matrixOracle (ι := I) D N Tslots d)).eval x) seed
      (ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T) g ε :=
    ODEActualSourceError.actual_source_certificate E hEncoding
      (ODESourceBranches.sourceVector v b T N) c hc
      (ODESourcePreparations.branch (J₀ x) (Jb x) N) hBranch seed hSeed hPrep
      _ isUnitary_one
      (fun a' i => ODENativeLCU.branchEvolution D kTable uTable x (a', i))
      (ODESourceBranches.propagation (ODEPublicSourceMesh.generator D x) T N)
      (ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T) g ε
      hTarget hg hε hεHalf hMesh.2.2.2.1 hSourceBudget hSim hPaddedLCHS hMesh.2.2.2.2
  have hCoeff : ODEActualSourceError.coefficients
      (ODESourceBranches.sourceVector v b T N) c = a :=
    ODESourcePublicNorms.actual_coefficients_eq v b r₀ rb T N hT hN hv hbnorm c
  exact hTrials x (ODESourceBranches.sourceVector v b T N)
    (ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T) hCert hCoeff hTarget

/-- Forgetting the budget gives the released positive-branch outcome (`ode:thm:main`). -/
theorem outcome_of_budget (D : Data X n Z s) (etaH etaD T g ε r₀ rb : ℝ)
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (seed : EuclideanSpace ℂ n) (Q : ℝ)
    (h : BudgetOutcome D etaH etaD T g ε r₀ rb J₀ Jb seed Q) :
    ODECompleteEndpoint.PositiveOutcome D etaH etaD T g ε r₀ rb J₀ Jb seed := by
  obtain ⟨Tslots, d, E, q, hU, hC⟩ := h
  exact ⟨Tslots, d, E, q, hU, fun v b x hv hb hI hF hT hB =>
    (hC v b x hv hb hI hF hT hB).fst⟩

/-- The released positive-branch outcome satisfies `BudgetOutcome` with `Q` the released
worst-case bound `1274019840 g (√s Θ + √(s Θ ℓ) + ℓ)` (`ode:thm:main`). -/
theorem budget_of_outcome (D : Data X n Z s) (etaH etaD T g ε r₀ rb : ℝ)
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (seed : EuclideanSpace ℂ n)
    (h : ODECompleteEndpoint.PositiveOutcome D etaH etaD T g ε r₀ rb J₀ Jb seed) :
    BudgetOutcome D etaH etaD T g ε r₀ rb J₀ Jb seed
      (1274019840 * g * ImprovedODEQueryBudget.queryShape (s : ℝ)
        (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) g ε)
        (ImprovedODEQueryBudget.logBudget g ε)) := by
  obtain ⟨Tslots, d, E, q, hU, hC⟩ := h
  exact ⟨Tslots, d, E, q, hU, fun v b x hv hb hI hF hT hB =>
    ⟨hC v b x hv hb hI hF hT hB, (hC v b x hv hb hI hF hT hB).matrix_queries⟩⟩

set_option maxHeartbeats 3000000 in
/-- **Theorem `ode:thm:main` in the native family for every `T ≥ 0`.** Under the public
hypotheses of the released `ODEUniformPositiveEndpoint.positive_time_solver` with `0 ≤ T` in
place of `0 < T` and without the positivity of `ρ = η_H + R η_D`, `BudgetOutcome` holds with
`Q = if T = 0 ∨ ρ = 0 then 0 else 1274019840 g (√s Θ + √(s Θ ℓ) + ℓ)`: the worst-case
matrix-query count is `0` if `T = 0` or `ρ = 0` and the released bound otherwise. -/
theorem native_solver (D : Data X n Z s) (etaH etaD T g ε r₀ rb : ℝ)
    (hH : 0 ≤ etaH) (hDiss : 0 ≤ etaD) (hT : 0 ≤ T)
    (hg : 1 ≤ g) (hε : 0 < ε) (hεHalf : ε ≤ 1 / 2)
    (h₀ : 0 ≤ r₀) (hb : 0 ≤ rb) (hB : 0 < r₀ + T * rb)
    (hrH : ∀ x i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ etaH ^ 2)
    (hcH : ∀ x j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ etaH ^ 2)
    (hrD : ∀ x i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ etaD ^ 2)
    (hcD : ∀ x j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ etaD ^ 2)
    (hPSD : ∀ (x : X) (w : EuclideanSpace ℂ n), 0 ≤ (inner ℂ w
      (SparseStateOverlap.matrixOperator (ODEMatrixEnergy.dissipativePart (D.matrix x)) w)).re)
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ₀ : ∀ x, IsUnitary (J₀ x)) (hJb : ∀ x, IsUnitary (Jb x))
    (seed : EuclideanSpace ℂ n) (hSeed : ‖seed‖ = 1) :
    BudgetOutcome D etaH etaD T g ε r₀ rb J₀ Jb seed
      (if T = 0 ∨ etaH + ImprovedODEQueryBudget.radius g ε * etaD = 0 then 0 else
        1274019840 * g * ImprovedODEQueryBudget.queryShape (s : ℝ)
          (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) g ε)
          (ImprovedODEQueryBudget.logBudget g ε)) := by
  by_cases hZero : T = 0 ∨ etaH + ImprovedODEQueryBudget.radius g ε * etaD = 0
  · rw [if_pos hZero]
    exact zero_solver D etaH etaD T g ε r₀ rb hH hDiss hT hZero hg hε hεHalf h₀ hb hB hrH hrD
      hPSD J₀ Jb hJ₀ hJb seed hSeed
  · rw [if_neg hZero]
    have hεOne : ε ≤ 1 := hεHalf.trans (by norm_num)
    have hR : 0 ≤ ImprovedODEQueryBudget.radius g ε :=
      ImprovedODEQueryBudget.radius_nonneg g ε hg hε hεOne
    have hTpos : 0 < T := lt_of_le_of_ne hT (fun h => hZero (Or.inl h.symm))
    have hρ : 0 < etaH + ImprovedODEQueryBudget.radius g ε * etaD :=
      lt_of_le_of_ne (add_nonneg hH (mul_nonneg hR hDiss)) (fun h => hZero (Or.inr h.symm))
    exact budget_of_outcome D etaH etaD T g ε r₀ rb J₀ Jb seed
      (ODECompleteEndpoint.of_positive D etaH etaD T g ε r₀ rb J₀ Jb seed hε.le
        (ODEUniformPositiveEndpoint.positive_time_solver D etaH etaD T g ε r₀ rb hH hDiss hρ
          hTpos hg hε hεHalf h₀ hb hB hrH hcH hrD hcD hPSD J₀ Jb hJ₀ hJb seed hSeed))

set_option maxHeartbeats 3000000 in
/-- **Theorem `ode:thm:main` for every `T ≥ 0`, in the native family, from the hypotheses of the
released `ODECompleteEndpoint.solver`.** The supplied nonzero solution only certifies the public
scalar inequalities `g ≥ 1` and `r₀ + T r_b > 0`; one native trial family serves every valid
instance, with the released complete certificate and
`Q = if T = 0 ∨ η_H + R η_D = 0 then 0 else 1274019840 g (√s Θ + √(s Θ ℓ) + ℓ)`, as in
`native_solver`. -/
theorem solver_nonneg (D : Data X n Z s) (etaH etaD T g ε r₀ rb : ℝ)
    (hH : 0 ≤ etaH) (hDiss : 0 ≤ etaD) (hT : 0 ≤ T)
    (hε : 0 < ε) (hεHalf : ε ≤ 1 / 2)
    (hrH : ∀ x i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ etaH ^ 2)
    (hcH : ∀ x j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ etaH ^ 2)
    (hrD : ∀ x i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ etaD ^ 2)
    (hcD : ∀ x j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ etaD ^ 2)
    (hPSD : ∀ (x : X) (w : EuclideanSpace ℂ n), 0 ≤ (inner ℂ w
      (SparseStateOverlap.matrixOperator (ODEMatrixEnergy.dissipativePart (D.matrix x)) w)).re)
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ₀ : ∀ y, IsUnitary (J₀ y)) (hJb : ∀ y, IsUnitary (Jb y))
    (seed : EuclideanSpace ℂ n) (hSeed : ‖seed‖ = 1)
    (x : X) (v b : EuclideanSpace ℂ n) (hv : ‖v‖ = r₀) (hb : ‖b‖ = rb)
    (hTarget : ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T ≠ 0)
    (hBudget : (r₀ + T * rb) /
      ‖ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T‖ ≤ g) :
    BudgetOutcome D etaH etaD T g ε r₀ rb J₀ Jb seed
      (if T = 0 ∨ etaH + ImprovedODEQueryBudget.radius g ε * etaD = 0 then 0 else
        1274019840 * g * ImprovedODEQueryBudget.queryShape (s : ℝ)
          (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) g ε)
          (ImprovedODEQueryBudget.logBudget g ε)) := by
  have h₀ : 0 ≤ r₀ := by
    rw [← hv]
    exact norm_nonneg v
  have hbNonneg : 0 ≤ rb := by
    rw [← hb]
    exact norm_nonneg b
  have hB : 0 < r₀ + T * rb :=
    ODEUniformMain.source_mass_pos D T r₀ rb hT x v b hv hb (hPSD x) hTarget
  have hRatio := ODEConstantForcing.normalization_ratio_ge_one
    (ODEPublicSourceMesh.generator D x)
    (ODEPublicSourceMesh.generator_dissipative D x (hPSD x)) v b T hT hTarget
  rw [hv, hb] at hRatio
  exact native_solver D etaH etaD T g ε r₀ rb hH hDiss hT (hRatio.trans hBudget) hε hεHalf
    h₀ hbNonneg hB hrH hcH hrD hcD hPSD J₀ Jb hJ₀ hJb seed hSeed

end
end SparseHamiltonian.ZeroTimeRemarks.ODEConstant
