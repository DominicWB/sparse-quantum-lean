import TimeDependentODE.Corollaries
import ZeroTimeRemarks.TimeUniform

/-!
# Theorem `ode:thm:time` (uniform meshes) at zero time or with a known zero generator

The released endpoint `SparseHamiltonian.TimeDependentODE.solver` of Theorem `ode:thm:time`
assumes `T > 0` and `ρ = η_H + R η_D > 0`; its statement file lists the zero-time and
zero-energy branches as not formalised. Theorem `ode:thm:time` inherits the remark after
`ode:thm:main` that zero time or a known zero generator needs no matrix queries. This file
proves both cases in the same coherent sampled-time oracle family
`TimeDependentODE.NativeSource.physicalOracle`, with the same public seed, output flag, trial
family and complete certificate as `TimeDependentODE.Outcome`, and gives the combined
statement for every `T ≥ 0`.

**Direct source assembly.** The released trial family loads the initial state and the `M`
forcing samples (left-endpoint quadrature of `x₀ + ∫ b`), runs the coherent sampled-time SELECT
of the ordered LCHS branch products and unloads the coefficients. At `T = 0` every slot duration
vanishes; with public bounds `η_H = η_D = 0` every represented sample vanishes. In both cases
every branch product is the identity, the identity program is an exact SELECT for the released
clean encoding at any rescaling, and the released discretisation, quadrature, LCHS table and
source certificates give the released trial certificate with no matrix query.

* `BudgetOutcome … Q`: the released `TimeDependentODE.Outcome` in which the certified
  four-attempt protocol has worst-case matrix-query count at most `Q`; `outcome_of_budget`,
  `budget_of_outcome`.
* `zero_solver`: `T = 0` or `η_H + R η_D = 0`, with `Q = 0`.
* `solver_nonneg`: Theorem `ode:thm:time` on uniform meshes for every `T ≥ 0`, with `Q = 0` in
  the zero cases and the released bound otherwise.
-/

set_option autoImplicit false

namespace SparseHamiltonian.ZeroTimeRemarks.ODETime

noncomputable section
open ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding
open scoped BigOperators InnerProduct
set_option maxRecDepth 4096
set_option synthInstance.maxSize 4096

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s M : ℕ}

/-- The clean encoding of the released coherent sampled-time SELECT is an isometry for all
public parameters (`ode:thm:time`). -/
theorem alignedInput_isometry {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : Data (X × Fin M) n Z s) (hM : 0 < M) (b0 : ι × Fin M) (γ ρ T ε : ℝ) :
    (TimeDependentODE.Select.alignedInput D hM b0 γ ρ T ε)† ∘L
      TimeDependentODE.Select.alignedInput D hM b0 γ ρ T ε = 1 :=
  AlignedMultiOracleProgram.input_isometry _
    (NativeSparseAttenuation.isometry_comp _ _
      (SharpClockQuery.input_isometry _ _ _ _ _ (CayleyClockInterface.width_ge_one _ _))
      (TimeDependentODE.embedding D hM b0 M _).adjoint_comp_self)

set_option maxHeartbeats 3000000 in
/-- With the identity SELECT, every trial of the released public family makes no matrix query
(`ode:thm:time`). -/
theorem trial_matrix_cost {ι : Type*} [Fintype ι] [DecidableEq ι] (D : Data (X × Fin M) n Z s)
    (hM : 0 < M) (i0 : ι) (d : ℕ)
    (J₀ : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (Jb : X → Fin M → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (E : TimeDependentODE.NativeSource.SourceSpace ι n M →L[ℂ]
      TimeDependentODE.NativeSource.MatrixSpace ι n Z M d) (hE : E† ∘L E = 1)
    (a : Option (Fin M) × ι → ℂ) (v : EuclideanSpace ℂ n)
    (hSeed : ‖ODECompiledSource.seed E a v‖ = 1)
    (hOutput : (ODECompiledSource.output E a)† ∘L ODECompiledSource.output E a = 1) (j : ℕ) :
    (TimeDependentODE.NativeSource.publicTrials D hM i0 d MultiOracleCircuit.Program.identity
      J₀ Jb E hE a v hSeed hOutput j).cost
        (ODESourceQueryBudget.matrixWeight (fun _ => 1)) = 0 := by
  unfold TimeDependentODE.NativeSource.publicTrials
  rw [ODECoordinateNativeControl.compile_matrix_cost]
  unfold TimeDependentODE.SourceTD.publicLogicalTrials
  rw [ODECountedAmplification.cost_eq]
  apply Nat.mul_eq_zero.mpr
  right
  apply Nat.mul_eq_zero.mpr
  right
  exact (TimeDependentODE.SourceTD.program_matrix_cost _ J₀ Jb E hE _).trans
    (MultiOracleCircuit.Program.cost_identity _)

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- An ordered branch product is the identity if all its slot durations vanish or all
represented samples of the instance vanish (`ode:thm:time`). -/
theorem branchEvolution_eq_one {ι : Type*} (D : Data (X × Fin M) n Z s) (hM : 0 < M)
    (k : ι → ℝ) (u : ι → Fin M → ℝ) (x : X) (i : ι)
    (h : (∀ r, u i r = 0) ∨ ∀ r, D.matrix (x, r) = 0) :
    TimeDependentODE.Select.branchEvolution D hM k u x i = 1 := by
  unfold TimeDependentODE.Select.branchEvolution
  have hfac : ∀ t : ℕ, NormedSpace.exp ((-Complex.I *
      ((u i (TimeDependent.Sampled.sampleIndex hM t) / M : ℝ) : ℂ)) •
        SparseStateOverlap.matrixOperator (ODEMatrixEnergy.lchsHamiltonian
          (D.matrix (x, TimeDependent.Sampled.sampleIndex hM t)) (k i))) = 1 := by
    intro t
    apply Hamiltonian.exp_eq_one
    rcases h with hu | hD
    · left
      rw [hu, zero_div]
    · right
      rw [hD, ODEZeroEnergy.lchsHamiltonian_zero, NativeZeroSimulation.matrixOperator_zero]
  simp only [hfac]
  exact TimeUniform.evolution_one M

set_option maxHeartbeats 3000000 in
/-- **The released outcome of `ode:thm:time` with a matrix-query budget.** One public trial
family over the coherent sampled-time oracle family `TimeDependentODE.NativeSource.physicalOracle`,
with the released public seed and output flag, chosen before the instance, such that for every
valid instance (the instance hypotheses of `TimeDependentODE.Outcome`) the released complete
certificate holds and the certified four-attempt protocol has worst-case matrix-query count at
most `Q`, so every history makes at most `Q` matrix queries. Without the budget this is
`TimeDependentODE.Outcome` (`outcome_of_budget`). -/
def BudgetOutcome (D : Data (X × Fin M) n Z s) (hM : 0 < M) (etaH etaD T g ε r₀ : ℝ)
    (rb : Fin M → ℝ) (J₀ : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (Jb : X → Fin M → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (seed : EuclideanSpace ℂ n) (Q : ℝ) : Prop :=
  ∃ (d : ℕ)
    (E : TimeDependentODE.NativeSource.SourceSpace (TimeDependentODE.Index D T g ε) n M →L[ℂ]
      TimeDependentODE.NativeSource.MatrixSpace (TimeDependentODE.Index D T g ε) n Z M d)
    (q : ℕ → MultiOracleCircuit.Program
      (TimeDependentODE.NativeSource.physicalOracle (ι := TimeDependentODE.Index D T g ε)
        D d J₀ Jb)),
    (∀ j y, IsUnitary ((q j).eval y)) ∧
    ∀ (x : X) (G : ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
      (b sol : ℝ → EuclideanSpace ℂ n) (bs : Fin M → EuclideanSpace ℂ n)
      (βG δG βb δb bmax : ℝ), 0 ≤ βG → 0 ≤ βb →
      (∀ u ∈ Set.Icc 0 T, TimeDependentODE.Accretive (G u)) →
      (∀ u ∈ Set.Icc 0 T, ∀ v ∈ Set.Icc 0 T, ‖G u - G v‖ ≤ βG * |u - v|) →
      (∀ r : Fin M, ‖G ((r : ℕ) * T / M) -
        SparseStateOverlap.matrixOperator (D.matrix (x, r))‖ ≤ δG) →
      (∀ u ∈ Set.Icc 0 T, ∀ v ∈ Set.Icc 0 T, ‖b u - b v‖ ≤ βb * |u - v|) →
      (∀ r : Fin M, ‖b ((r : ℕ) * T / M) - bs r‖ ≤ δb) →
      (∀ u ∈ Set.Icc 0 T, ‖b u‖ ≤ bmax) →
      TimeDependentODE.SolvesODE G b sol 0 T →
      ‖sol 0‖ = r₀ → (∀ r, ‖bs r‖ = rb r) →
      (sol 0 ≠ 0 → J₀ x seed = ODEStateNormalization.unitDirection (sol 0)) →
      (∀ r, bs r ≠ 0 → Jb x r seed = ODEStateNormalization.unitDirection (bs r)) →
      sol T ≠ 0 →
      TimeDependentODE.PublicSource.mass r₀ T rb ≤ g * ‖sol T‖ →
      TimeDependentODE.Sampling.discretisation D T βG δG βb δb bmax r₀ ≤
        ε * TimeDependentODE.PublicSource.mass r₀ T rb / (2000 * g) →
      ∃ h : ODECompleteTrial.Certificate q
          (ODEGroverAverage.chosenIterations (TimeDependentODE.ratio g))
          (TimeDependentODE.NativeSource.input D hM (Sum.inr false) d
            (ODECompiledSource.seed E (TimeDependentODE.coefficients D T g ε r₀ rb) seed))
          (TimeDependentODE.NativeSource.input D hM (Sum.inr false) d ∘L
            ODECompiledSource.output E (TimeDependentODE.coefficients D T g ε r₀ rb))
          x (sol T) (s : ℝ)
          (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) (TimeDependentODE.ratio g)
            (TimeDependentODE.accuracy ε))
          (ImprovedODEQueryBudget.logBudget (TimeDependentODE.ratio g)
            (TimeDependentODE.accuracy ε)) (TimeDependentODE.ratio g) ε,
        ((ODECompleteTrial.algorithm h.trial).worstCost
          (ODESourceQueryBudget.matrixWeight (fun _ => 1)) : ℝ) ≤ Q

set_option maxHeartbeats 3000000 in
/-- **The released trial family with the identity SELECT** (`ode:thm:time`). For every label
type, clean encoding `E` and public coefficient table `a`, the released public trial family
`TimeDependentODE.NativeSource.publicTrials` built on the identity program consists of unitary
circuits and, for every instance whose source certificate holds for the identity program, with
actual coefficients `a` and a discretised target `y` within direction `ε/1000` of the target,
satisfies the released complete certificate with worst-case matrix-query count `0`. -/
theorem identity_trials {ι : Type*} [Fintype ι] [DecidableEq ι] (D : Data (X × Fin M) n Z s)
    (hM : 0 < M) (i0 : ι) (d : ℕ) (J₀ : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (Jb : X → Fin M → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ₀ : ∀ x, IsUnitary (J₀ x)) (hJb : ∀ x r, IsUnitary (Jb x r))
    (E : TimeDependentODE.NativeSource.SourceSpace ι n M →L[ℂ]
      TimeDependentODE.NativeSource.MatrixSpace ι n Z M d) (hE : E† ∘L E = 1)
    (c : ι → ℂ) (a : Option (Fin M) × ι → ℂ) (ha : 0 < ODECoherentLCU.coefficientMass a)
    (seed : EuclideanSpace ℂ n) (hSeed : ‖seed‖ = 1) (Θ ell g ε : ℝ)
    (hg : 1 ≤ TimeDependentODE.ratio g) (hε : 0 ≤ ε)
    (hShape : 0 ≤ ImprovedODEQueryBudget.queryShape (s : ℝ) Θ ell) :
    ∃ q : ℕ → MultiOracleCircuit.Program
        (TimeDependentODE.NativeSource.physicalOracle (ι := ι) D d J₀ Jb),
      (∀ j y, IsUnitary ((q j).eval y)) ∧
      ∀ (x : X) (z : Option (Fin M) → EuclideanSpace ℂ n) (y target : EuclideanSpace ℂ n),
        ODEActualSourceError.Certificate E z c (TimeDependentODE.SourceTD.branchTD (J₀ x) (Jb x))
          ((MultiOracleCircuit.Program.identity
            (O := TimeDependentODE.NativeSource.matrixOracle (ι := ι) D d)).eval x)
          seed y (TimeDependentODE.ratio g) (TimeDependentODE.accuracy ε) →
        ODEActualSourceError.coefficients z c = a →
        ‖ODEStateNormalization.unitDirection y -
          ODEStateNormalization.unitDirection target‖ ≤ ε / 1000 →
        target ≠ 0 →
        ∃ h : ODECompleteTrial.Certificate q
          (ODEGroverAverage.chosenIterations (TimeDependentODE.ratio g))
          (TimeDependentODE.NativeSource.input D hM i0 d (ODECompiledSource.seed E a seed))
          (TimeDependentODE.NativeSource.input D hM i0 d ∘L ODECompiledSource.output E a)
          x target (s : ℝ) Θ ell (TimeDependentODE.ratio g) ε,
          ((ODECompleteTrial.algorithm h.trial).worstCost
            (ODESourceQueryBudget.matrixWeight (fun _ => 1)) : ℝ) ≤ 0 := by
  let pN : MultiOracleCircuit.Program
      (TimeDependentODE.NativeSource.matrixOracle (ι := ι) D d) :=
    MultiOracleCircuit.Program.identity
  let q := TimeDependentODE.NativeSource.publicTrials D hM i0 d pN J₀ Jb E hE a seed
    (ODECompiledSource.seed_unit E a hE ha seed hSeed)
    (ODECompiledSource.output_isometry E a hE ha)
  have hCost : ∀ j, (q j).cost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) = 0 :=
    fun j => trial_matrix_cost D hM i0 d J₀ Jb E hE a seed _ _ j
  have hUnitary : ∀ j y, IsUnitary ((q j).eval y) := fun j y => (q j).eval_unitary
    (TimeDependentODE.NativeSource.physicalOracle_unitary D d J₀ Jb hJ₀ hJb) y
  refine ⟨q, hUnitary, fun x z y target hCert hCoeff hDir hTarget => ?_⟩
  have hq : (pN.count : ℝ) ≤ 10616832 * ImprovedODEQueryBudget.queryShape (s : ℝ) Θ ell := by
    rw [MultiOracleCircuit.Program.count_identity, Nat.cast_zero]
    exact mul_nonneg (by norm_num) hShape
  have hTrial := TimeDependentODE.NativeSource.coefficient_trial_certificate D hM i0 d pN
    J₀ Jb hJ₀ hJb E hE z c seed y hSeed Θ ell (TimeDependentODE.ratio g)
    (TimeDependentODE.accuracy ε) hg x hCert hq a ha hCoeff
  have hFinal := TimeDependentODE.retarget (η' := ε / 500) hTrial hDir
    (by unfold TimeDependentODE.accuracy; linarith)
  have hFull := ODECompleteTrial.of_trialCertificate (fun j => hUnitary j x) hε hTarget hFinal
  refine ⟨hFull, ?_⟩
  have hW := ODERepeatProtocol.fourTrials_worstCost_le q
    (ODEGroverAverage.chosenIterations (TimeDependentODE.ratio g))
    hFull.trial.cutoff_pos _ hFull.trial.seed_unit _ hFull.trial.output_isometry
    (ODESourceQueryBudget.matrixWeight (fun _ => 1)) 0
    (fun j _ => by rw [hCost j, Nat.cast_zero])
  rw [mul_zero] at hW
  exact hW

set_option maxHeartbeats 4000000 in
/-- **Theorem `ode:thm:time` at zero time or with a known zero generator (uniform meshes).**
If `T = 0` or the public energy bounds give `η_H + R η_D = 0`, the released trial family with
the identity SELECT satisfies `BudgetOutcome` with `Q = 0`: in the coherent sampled-time
oracle family, with the released public seed and flag, every valid instance has the released
complete certificate (success at least `175/256 > 2/3`, conditional trace distance at most `ε`,
at most `40 g'` calls of each source interface, `g' = 2 g`), and the protocol makes no matrix
query in any history. The mesh conditions and the column promises are not needed. -/
theorem zero_solver (D : Data (X × Fin M) n Z s) (hM : 0 < M)
    (etaH etaD T g ε r₀ : ℝ) (rb : Fin M → ℝ)
    (hH : 0 ≤ etaH) (hDiss : 0 ≤ etaD) (hT : 0 ≤ T)
    (hZero : T = 0 ∨ etaH + TimeDependentODE.radius g ε * etaD = 0) (hg : 1 ≤ g)
    (hε : 0 < ε) (hεOne : ε ≤ 1)
    (h₀ : 0 ≤ r₀) (hb : ∀ r, 0 ≤ rb r) (hB : 0 < TimeDependentODE.PublicSource.mass r₀ T rb)
    (hrH : ∀ y i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix y) i j‖ ^ 2 ≤ etaH ^ 2)
    (hrD : ∀ y i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix y) i j‖ ^ 2 ≤ etaD ^ 2)
    (hPSD : ∀ (y : X × Fin M) (w : EuclideanSpace ℂ n), 0 ≤ (inner ℂ w
      (SparseStateOverlap.matrixOperator (ODEMatrixEnergy.dissipativePart (D.matrix y)) w)).re)
    (J₀ : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (Jb : X → Fin M → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ₀ : ∀ x, IsUnitary (J₀ x)) (hJb : ∀ x r, IsUnitary (Jb x r))
    (seed : EuclideanSpace ℂ n) (hSeed : ‖seed‖ = 1) :
    BudgetOutcome D hM etaH etaD T g ε r₀ rb J₀ Jb seed 0 := by
  have hg' : 1 ≤ TimeDependentODE.ratio g := by unfold TimeDependentODE.ratio; linarith
  have hε' : 0 < TimeDependentODE.accuracy ε := by
    unfold TimeDependentODE.accuracy; linarith
  have hε'One : TimeDependentODE.accuracy ε ≤ 1 := by
    unfold TimeDependentODE.accuracy; linarith
  have hε'Half : TimeDependentODE.accuracy ε ≤ 1 / 2 := by
    unfold TimeDependentODE.accuracy; linarith
  have hν : 0 < TimeDependentODE.precision g ε :=
    ImprovedODEQueryBudget.precision_pos _ _ hg' hε'
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hh : 0 ≤ T / M := div_nonneg hT hMR.le
  -- One public Gaussian table for every product family.
  have hL : 0 ≤ TimeDependentODE.lipschitz D T :=
    mul_nonneg hT (mul_nonneg (Nat.cast_nonneg s) D.scale_pos.le)
  obtain ⟨_hGrid, _hNodes, hMass, hApprox⟩ := TimeDependentODE.GaussianLCHS.table_certificate
    (fun y : X × Option (Fin M) => TimeDependentODE.Sampling.family D hM T y.1 y.2)
    (fun y z => TimeDependentODE.Sampling.family_analyticAt D hM T y.1 y.2 z)
    (fun y z hz => TimeDependentODE.Sampling.family_norm_le_one D hM T hT hPSD y.1 y.2 z hz)
    (TimeDependentODE.lipschitz D T) hL
    (fun y k l => TimeDependentODE.Sampling.family_lipschitz D hM T hT y.1 y.2 k l)
    (TimeDependentODE.ratio g) (TimeDependentODE.accuracy ε) hg' hε' hε'One
  have hc : ODECoherentLCU.coefficientMass (TimeDependentODE.lchsCoefficients D T g ε) = 3 :=
    ODECoefficientPadding.coefficientMass_eq _ 3 hMass
  -- Every branch product is the identity.
  have hOne : ∀ (x : X) (a' : TimeDependentODE.NativeSource.Label
      (TimeDependentODE.Index D T g ε) M),
      TimeDependentODE.Select.branchEvolution D hM (TimeDependentODE.nodeTable D T g ε)
        (TimeDependentODE.Sampling.durationTable T) x a' = 1 := by
    intro x a'
    apply branchEvolution_eq_one
    rcases hZero with hT0 | hρ
    · left
      intro r
      change T * TimeDependentODE.mask (TimeDependentODE.Sampling.start a'.1) (r : ℕ) = 0
      exact mul_eq_zero_of_left hT0 _
    · right
      intro r
      have hRadius : 0 < TimeDependentODE.radius g ε :=
        lt_of_lt_of_le (by norm_num : (0 : ℝ) < 4)
          (ODEGaussianParameters.radius_ge_four _ _ hg' hε' hε'One)
      exact ODEZeroEnergy.matrix_zero_of_effective_energy (D.matrix (x, r)) etaH etaD
        (TimeDependentODE.radius g ε) hH hDiss hRadius hρ (hrH (x, r)) (hrD (x, r))
  -- The identity SELECT on the released clean encoding at the rescaling `γ = 1`.
  let i0 : TimeDependentODE.Index D T g ε := Sum.inr false
  let ρ : ℝ := etaH + TimeDependentODE.radius g ε * etaD
  let d := TimeDependentODE.Select.degree (s : ℝ) 1 ρ T (TimeDependentODE.precision g ε) M
  let E : TimeDependentODE.NativeSource.SourceSpace (TimeDependentODE.Index D T g ε) n M →L[ℂ]
      TimeDependentODE.NativeSource.MatrixSpace (TimeDependentODE.Index D T g ε) n Z M d :=
    TimeDependentODE.Select.alignedInput D hM (TimeDependentODE.NativeSource.dummy hM i0) 1 ρ T
      (TimeDependentODE.precision g ε)
  have hEiso : E† ∘L E = 1 := alignedInput_isometry D hM _ 1 ρ T _
  let a := TimeDependentODE.coefficients D T g ε r₀ rb
  have ha : 0 < ODECoherentLCU.coefficientMass a := by
    rw [show a = TimeDependentODE.PublicSource.coefficients r₀ T rb
        (TimeDependentODE.lchsCoefficients D T g ε) from rfl,
      TimeDependentODE.PublicSource.coefficients_mass r₀ T rb h₀ hT hb hB _ hc]
    norm_num
  have hΘ : 0 ≤ ImprovedODEQueryBudget.theta (T * etaH) (T * etaD)
      (TimeDependentODE.ratio g) (TimeDependentODE.accuracy ε) :=
    ImprovedODEQueryBudget.theta_nonneg _ _ _ _ (mul_nonneg hT hH) (mul_nonneg hT hDiss)
      hg' hε' hε'One
  have hLog : 0 ≤ ImprovedODEQueryBudget.logBudget (TimeDependentODE.ratio g)
      (TimeDependentODE.accuracy ε) :=
    le_trans zero_le_one (ImprovedODEQueryBudget.logBudget_ge_one _ _ hg' hε' hε'One)
  obtain ⟨q, hUnitary, hTrials⟩ := identity_trials D hM i0 d J₀ Jb hJ₀ hJb E hEiso
    (TimeDependentODE.lchsCoefficients D T g ε) a ha seed hSeed
    (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) (TimeDependentODE.ratio g)
      (TimeDependentODE.accuracy ε))
    (ImprovedODEQueryBudget.logBudget (TimeDependentODE.ratio g) (TimeDependentODE.accuracy ε))
    g ε hg' hε.le (ImprovedODEQueryBudget.queryShape_nonneg _ _ _ hΘ hLog)
  refine ⟨d, E, q, hUnitary, ?_⟩
  intro x G b sol bs βG δG βb δb bmax hβG hβb hG hGLip hGs hbLip hbs hbB hsol h0 hbn
    hInitial hForcing hTarget hBudget hDisc
  -- The discretised target of the represented samples.
  let Gs := TimeDependentODE.Sampling.generator D hM x
  let z := TimeDependentODE.Sampling.sources (sol 0) (T / M) bs
  let y := TimeDependentODE.Sampling.target Gs (T / M) (sol 0) bs
  have hErr := TimeDependentODE.Sampling.discretisation_error D hM hPSD x T hT G b sol bs
    βG δG βb δb bmax hβG hβb hG hGLip hGs hbLip hbs hbB hsol
  rw [h0] at hErr
  obtain ⟨hy, hBy, hDir⟩ := TimeDependentODE.Sampling.target_budget (sol T) y
    (TimeDependentODE.PublicSource.mass r₀ T rb) g ε _ hg hε hεOne hTarget hBudget hErr hDisc
  have hzNorm : ∀ a', ‖z a'‖ = TimeDependentODE.PublicSource.norms r₀ T rb a' :=
    TimeDependentODE.Sampling.sources_norm (sol 0) T hT bs r₀ rb h0 hbn
  have hMassZ : ODESourceBranches.mass z = TimeDependentODE.PublicSource.mass r₀ T rb :=
    TimeDependentODE.PublicSource.mass_eq z r₀ T rb hzNorm
  have hCoeff : ODEActualSourceError.coefficients z
      (TimeDependentODE.lchsCoefficients D T g ε) = a :=
    TimeDependentODE.PublicSource.actual_coefficients_eq z r₀ T rb hzNorm _
  have hJ : ∀ a', (TimeDependentODE.SourceTD.branchTD (J₀ x) (Jb x) a')† ∘L
      TimeDependentODE.SourceTD.branchTD (J₀ x) (Jb x) a' = 1 := by
    intro a'
    cases a' with
    | none => exact (hJ₀ x).1
    | some r => exact (hJb x r).1
  have hPrep : ∀ a', z a' ≠ 0 →
      TimeDependentODE.SourceTD.branchTD (J₀ x) (Jb x) a' seed =
        ODEStateNormalization.unitDirection (z a') := by
    intro a' hz
    cases a' with
    | none => exact hInitial hz
    | some r =>
        have hzr : (T / M) • bs r ≠ 0 := hz
        have hbr : bs r ≠ 0 := by
          intro h
          apply hzr
          rw [h, smul_zero]
        have hpos : 0 < T / M := by
          rcases hh.lt_or_eq with hlt | heq
          · exact hlt
          · exfalso
            apply hzr
            rw [← heq, zero_smul]
        change Jb x r seed = ODEStateNormalization.unitDirection ((T / M) • bs r)
        rw [TimeDependentODE.Sampling.unitDirection_smul (T / M) hpos (bs r)]
        exact hForcing r hbr
  have hNorm : ‖y‖ ≤ ODESourceBranches.mass z :=
    TimeDependentODE.Sampling.target_norm_le Gs
      (TimeDependentODE.Sampling.generator_accretive D hM hPSD x) (T / M) hh (sol 0) bs
  have hBudget' : ODESourceBranches.mass z ≤ TimeDependentODE.ratio g * ‖y‖ := by
    rw [hMassZ]
    unfold TimeDependentODE.ratio
    exact hBy
  have hSim : ‖(MultiOracleCircuit.Program.identity (O := TimeDependentODE.NativeSource.matrixOracle
        (ι := TimeDependentODE.Index D T g ε) D d)).eval x ∘L E - E ∘L WeightedClock.diagonal
      (fun a' : Option (Fin M) × TimeDependentODE.Index D T g ε =>
        TimeDependentODE.Select.branchEvolution D hM (TimeDependentODE.nodeTable D T g ε)
          (TimeDependentODE.Sampling.durationTable T) x (a'.1, a'.2))‖ ≤
        ImprovedODEQueryBudget.precision (TimeDependentODE.ratio g)
          (TimeDependentODE.accuracy ε) := by
    have hDiag : WeightedClock.diagonal
        (fun a' : Option (Fin M) × TimeDependentODE.Index D T g ε =>
          TimeDependentODE.Select.branchEvolution D hM (TimeDependentODE.nodeTable D T g ε)
            (TimeDependentODE.Sampling.durationTable T) x (a'.1, a'.2)) = 1 := by
      simp only [hOne]
      exact WeightedClock.diagonal_one
    rw [hDiag, MultiOracleCircuit.Program.eval_identity, sub_eq_zero.mpr, norm_zero]
    · exact hν.le
    · rfl
  have hLCHS : ∀ a', ‖(∑ i, TimeDependentODE.lchsCoefficients D T g ε i •
      TimeDependentODE.Select.branchEvolution D hM (TimeDependentODE.nodeTable D T g ε)
        (TimeDependentODE.Sampling.durationTable T) x (a', i)) -
        TimeDependentODE.Sampling.family D hM T x a' (-Complex.I)‖ ≤
          2 * ImprovedODEQueryBudget.precision (TimeDependentODE.ratio g)
            (TimeDependentODE.accuracy ε) := by
    intro a'
    have hsum : (∑ i, TimeDependentODE.lchsCoefficients D T g ε i •
        TimeDependentODE.Select.branchEvolution D hM (TimeDependentODE.nodeTable D T g ε)
          (TimeDependentODE.Sampling.durationTable T) x (a', i)) =
          ∑ j, TimeDependentODE.GaussianLCHS.coefficients (TimeDependentODE.lipschitz D T)
              (TimeDependentODE.ratio g) (TimeDependentODE.accuracy ε) j •
            TimeDependentODE.Sampling.family D hM T x a'
              (TimeDependentODE.GaussianLCHS.nodes (TimeDependentODE.lipschitz D T)
                (TimeDependentODE.ratio g) (TimeDependentODE.accuracy ε) j : ℂ) := by
      simp only [TimeDependentODE.Sampling.branchEvolution_eq_family]
      exact TimeDependentODE.Sampling.padded_sum _ _ _
    rw [hsum]
    exact hApprox (x, a')
  have hQuad : ‖(∑ a', TimeDependentODE.Sampling.family D hM T x a' (-Complex.I) (z a')) - y‖ ≤
      ImprovedODEQueryBudget.precision (TimeDependentODE.ratio g)
        (TimeDependentODE.accuracy ε) * ODESourceBranches.mass z := by
    have hsum : (∑ a', TimeDependentODE.Sampling.family D hM T x a' (-Complex.I) (z a')) =
        y := by
      apply Finset.sum_congr rfl
      intro a' _
      rw [TimeDependentODE.Sampling.family_neg_I]
    rw [hsum, sub_self, norm_zero]
    exact mul_nonneg hν.le (ODESourceBranches.mass_nonneg z)
  have hCert : ODEActualSourceError.Certificate E z (TimeDependentODE.lchsCoefficients D T g ε)
      (TimeDependentODE.SourceTD.branchTD (J₀ x) (Jb x))
      ((MultiOracleCircuit.Program.identity (O := TimeDependentODE.NativeSource.matrixOracle
        (ι := TimeDependentODE.Index D T g ε) D d)).eval x) seed y
        (TimeDependentODE.ratio g) (TimeDependentODE.accuracy ε) :=
    ODEActualSourceError.actual_source_certificate E hEiso z
      (TimeDependentODE.lchsCoefficients D T g ε) hc
      (TimeDependentODE.SourceTD.branchTD (J₀ x) (Jb x)) hJ seed hSeed hPrep _
      isUnitary_one
      (fun a' i => TimeDependentODE.Select.branchEvolution D hM
        (TimeDependentODE.nodeTable D T g ε) (TimeDependentODE.Sampling.durationTable T) x (a', i))
      (fun a' => TimeDependentODE.Sampling.family D hM T x a' (-Complex.I)) y
      (TimeDependentODE.ratio g) (TimeDependentODE.accuracy ε)
      hy hg' hε' hε'Half hNorm hBudget' hSim hLCHS hQuad
  exact hTrials x z y (sol T) hCert hCoeff hDir hTarget

/-- Forgetting the budget gives the released outcome of `ode:thm:time`. -/
theorem outcome_of_budget (D : Data (X × Fin M) n Z s) (hM : 0 < M)
    (etaH etaD T g ε r₀ : ℝ) (rb : Fin M → ℝ)
    (J₀ : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (Jb : X → Fin M → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (seed : EuclideanSpace ℂ n) (Q : ℝ)
    (h : BudgetOutcome D hM etaH etaD T g ε r₀ rb J₀ Jb seed Q) :
    TimeDependentODE.Outcome D hM etaH etaD T g ε r₀ rb J₀ Jb seed := by
  obtain ⟨d, E, q, hU, hC⟩ := h
  exact ⟨d, E, q, hU, fun x G b sol bs βG δG βb δb bmax h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
    h13 h14 h15 h16 => (hC x G b sol bs βG δG βb δb bmax h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
      h13 h14 h15 h16).fst⟩

/-- The released outcome of `ode:thm:time` satisfies `BudgetOutcome` with `Q` the released
worst-case bound `1274019840 g' (√s Θ + √(s Θ ℓ) + ℓ)`. -/
theorem budget_of_outcome (D : Data (X × Fin M) n Z s) (hM : 0 < M)
    (etaH etaD T g ε r₀ : ℝ) (rb : Fin M → ℝ)
    (J₀ : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (Jb : X → Fin M → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (seed : EuclideanSpace ℂ n)
    (h : TimeDependentODE.Outcome D hM etaH etaD T g ε r₀ rb J₀ Jb seed) :
    BudgetOutcome D hM etaH etaD T g ε r₀ rb J₀ Jb seed
      (1274019840 * TimeDependentODE.ratio g * ImprovedODEQueryBudget.queryShape (s : ℝ)
        (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) (TimeDependentODE.ratio g)
          (TimeDependentODE.accuracy ε))
        (ImprovedODEQueryBudget.logBudget (TimeDependentODE.ratio g)
          (TimeDependentODE.accuracy ε))) := by
  obtain ⟨d, E, q, hU, hC⟩ := h
  refine ⟨d, E, q, hU, fun x G b sol bs βG δG βb δb bmax h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
    h13 h14 h15 h16 => ?_⟩
  have hc := hC x G b sol bs βG δG βb δb bmax h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
    h16
  exact ⟨hc, hc.matrix_queries⟩

set_option maxHeartbeats 3000000 in
/-- **Theorem `ode:thm:time` on uniform meshes for every `T ≥ 0`.** Under the hypotheses of the
released `TimeDependentODE.solver` with `0 ≤ T` in place of `0 < T` and without the positivity
of `ρ = η_H + R η_D`, `BudgetOutcome` holds with
`Q = if T = 0 ∨ ρ = 0 then 0 else 1274019840 g' (√s Θ + √(s Θ ℓ) + ℓ)`, `g' = 2 g`. -/
theorem solver_nonneg (D : Data (X × Fin M) n Z s) (hM : 0 < M)
    (etaH etaD T g ε r₀ : ℝ) (rb : Fin M → ℝ)
    (hH : 0 ≤ etaH) (hDiss : 0 ≤ etaD) (hT : 0 ≤ T) (hg : 1 ≤ g)
    (hε : 0 < ε) (hεOne : ε ≤ 1)
    (hMesh : 8 * s * ((etaH + TimeDependentODE.radius g ε * etaD) * T) ≤ M)
    (hCayley : 3 * (Real.sqrt (2 * (s : ℝ)) *
      ((etaH + TimeDependentODE.radius g ε * etaD) * T)) ^ 3 ≤
        TimeDependentODE.precision g ε * (M : ℝ) ^ 2)
    (h₀ : 0 ≤ r₀) (hb : ∀ r, 0 ≤ rb r) (hB : 0 < TimeDependentODE.PublicSource.mass r₀ T rb)
    (hrH : ∀ y i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix y) i j‖ ^ 2 ≤ etaH ^ 2)
    (hcH : ∀ y j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix y) i j‖ ^ 2 ≤ etaH ^ 2)
    (hrD : ∀ y i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix y) i j‖ ^ 2 ≤ etaD ^ 2)
    (hcD : ∀ y j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix y) i j‖ ^ 2 ≤ etaD ^ 2)
    (hPSD : ∀ (y : X × Fin M) (w : EuclideanSpace ℂ n), 0 ≤ (inner ℂ w
      (SparseStateOverlap.matrixOperator (ODEMatrixEnergy.dissipativePart (D.matrix y)) w)).re)
    (J₀ : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (Jb : X → Fin M → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ₀ : ∀ x, IsUnitary (J₀ x)) (hJb : ∀ x r, IsUnitary (Jb x r))
    (seed : EuclideanSpace ℂ n) (hSeed : ‖seed‖ = 1) :
    BudgetOutcome D hM etaH etaD T g ε r₀ rb J₀ Jb seed
      (if T = 0 ∨ etaH + TimeDependentODE.radius g ε * etaD = 0 then 0 else
        1274019840 * TimeDependentODE.ratio g * ImprovedODEQueryBudget.queryShape (s : ℝ)
          (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) (TimeDependentODE.ratio g)
            (TimeDependentODE.accuracy ε))
          (ImprovedODEQueryBudget.logBudget (TimeDependentODE.ratio g)
            (TimeDependentODE.accuracy ε))) := by
  by_cases hZero : T = 0 ∨ etaH + TimeDependentODE.radius g ε * etaD = 0
  · rw [if_pos hZero]
    exact zero_solver D hM etaH etaD T g ε r₀ rb hH hDiss hT hZero hg hε hεOne h₀ hb hB hrH
      hrD hPSD J₀ Jb hJ₀ hJb seed hSeed
  · rw [if_neg hZero]
    have hg' : 1 ≤ TimeDependentODE.ratio g := by unfold TimeDependentODE.ratio; linarith
    have hε' : 0 < TimeDependentODE.accuracy ε := by
      unfold TimeDependentODE.accuracy; linarith
    have hε'One : TimeDependentODE.accuracy ε ≤ 1 := by
      unfold TimeDependentODE.accuracy; linarith
    have hR : 0 ≤ TimeDependentODE.radius g ε :=
      ImprovedODEQueryBudget.radius_nonneg _ _ hg' hε' hε'One
    have hTpos : 0 < T := lt_of_le_of_ne hT (fun h => hZero (Or.inl h.symm))
    have hρ : 0 < etaH + TimeDependentODE.radius g ε * etaD :=
      lt_of_le_of_ne (add_nonneg hH (mul_nonneg hR hDiss)) (fun h => hZero (Or.inr h.symm))
    exact budget_of_outcome D hM etaH etaD T g ε r₀ rb J₀ Jb seed
      (TimeDependentODE.solver D hM etaH etaD T g ε r₀ rb hH hDiss hTpos hg hε hεOne hρ hMesh
        hCayley h₀ hb hB hrH hcH hrD hcD hPSD J₀ Jb hJ₀ hJb seed hSeed)

end
end SparseHamiltonian.ZeroTimeRemarks.ODETime
