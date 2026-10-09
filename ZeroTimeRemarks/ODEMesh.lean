import TimeDependentExtensions.ODE.Corollaries
import ZeroTimeRemarks.ODETime

/-!
# Theorem `ode:thm:time` on general meshes at zero time or with a known zero generator

The released general-mesh endpoint `TimeDependentExtensions.ODE.solver` of Theorem
`ode:thm:time` (nonuniform meshes, breakpoints, integrated certificates and the certified source
quadrature on the mesh) assumes `T > 0` and `ρ = η_H + R η_D > 0`; its statement file lists
the degenerate cases as not formalised. This file proves them in the same coherent sampled-time
oracle family `TimeDependentExtensions.MeshSource.physicalOracle` on `N` slots, with the same
public seed, output flag, trial family and complete certificate as
`TimeDependentExtensions.ODE.Outcome`, and gives the combined statement for every `T ≥ 0`.

The construction is that of `ZeroTimeRemarks/ODETime.lean`: the released source assembly
(the initial state and the mesh forcing samples `Δ_q b̃_q`, the source quadrature of
`x₀ + ∫ b`) with the identity SELECT, which is exact when every branch product is the identity.
For `T = 0` the mesh collapses to `t_r = 0` (`r ≤ M`), every forcing source and every slot
duration vanishes and the discretised target is the initial state (`target_zero`); for a known
zero generator the released certified target error applies unchanged.

* `BudgetOutcome … Q`: the released `TimeDependentExtensions.ODE.Outcome` in which the certified
  four-attempt protocol has worst-case matrix-query count at most `Q`; `outcome_of_budget`,
  `budget_of_outcome`.
* `zero_solver`: `T = 0` or `η_H + R η_D = 0`, with `Q = 0`.
* `solver_nonneg`: the general-mesh form of Theorem `ode:thm:time` for every `T ≥ 0`, with
  `Q = 0` in the zero cases and the released bound otherwise.
-/

set_option autoImplicit false

namespace SparseHamiltonian.ZeroTimeRemarks.ODEMesh

noncomputable section
open ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding TimeDependentExtensions
open MeasureTheory Set
open scoped BigOperators InnerProduct
set_option maxRecDepth 4096
set_option synthInstance.maxSize 8192

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s M : ℕ}

/-- The clean encoding of the released SELECT on `N` slots is an isometry for all public
parameters (`ode:thm:time`). -/
theorem alignedInput_isometry {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : Data (X × Fin M) n Z s) (hM : 0 < M) (σ : ℕ → Fin M) (b0 : ι × Fin M) (N : ℕ)
    (γ ρ T ε : ℝ) :
    (MeshSelect.alignedInput D hM σ b0 N γ ρ T ε)† ∘L
      MeshSelect.alignedInput D hM σ b0 N γ ρ T ε = 1 :=
  AlignedMultiOracleProgram.input_isometry _
    (NativeSparseAttenuation.isometry_comp _ _
      (SharpClockQuery.input_isometry _ _ _ _ _ (CayleyClockInterface.width_ge_one _ _))
      (MeshSelect.embedding D hM σ b0 N _).adjoint_comp_self)

set_option maxHeartbeats 3000000 in
/-- With the identity SELECT, every trial of the released public family on `N` slots makes no
matrix query (`ode:thm:time`). -/
theorem trial_matrix_cost {ι : Type*} [Fintype ι] [DecidableEq ι] (D : Data (X × Fin M) n Z s)
    (hM : 0 < M) (i0 : ι) (N d : ℕ)
    (J₀ : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (Jb : X → Fin M → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (E : TimeDependentODE.NativeSource.SourceSpace ι n M →L[ℂ]
      MeshSource.MatrixSpace ι n Z M N d) (hE : E† ∘L E = 1)
    (a : Option (Fin M) × ι → ℂ) (v : EuclideanSpace ℂ n)
    (hSeed : ‖ODECompiledSource.seed E a v‖ = 1)
    (hOutput : (ODECompiledSource.output E a)† ∘L ODECompiledSource.output E a = 1) (j : ℕ) :
    (MeshSource.publicTrials D hM i0 N d MultiOracleCircuit.Program.identity
      J₀ Jb E hE a v hSeed hOutput j).cost
        (ODESourceQueryBudget.matrixWeight (fun _ => 1)) = 0 := by
  unfold MeshSource.publicTrials
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
/-- A branch product on `N` slots is the identity if all its durations vanish or all
represented samples of the instance vanish (`ode:thm:time`). -/
theorem branchEvolution_eq_one {ι : Type*} (D : Data (X × Fin M) n Z s) (σ : ℕ → Fin M)
    (N : ℕ) (k : ι → ℝ) (u : ι → Fin M → ℝ) (x : X) (i : ι)
    (h : (∀ r, u i r = 0) ∨ ∀ r, D.matrix (x, r) = 0) :
    MeshSelect.branchEvolution D σ N k u x i = 1 := by
  unfold MeshSelect.branchEvolution
  have hfac : ∀ t : ℕ, NormedSpace.exp ((-Complex.I * ((u i (σ t) / N : ℝ) : ℂ)) •
      SparseStateOverlap.matrixOperator (ODEMatrixEnergy.lchsHamiltonian
        (D.matrix (x, σ t)) (k i))) = 1 := by
    intro t
    apply Hamiltonian.exp_eq_one
    rcases h with hu | hD
    · left
      rw [hu, zero_div]
    · right
      rw [hD, ODEZeroEnergy.lchsHamiltonian_zero, NativeZeroSimulation.matrixOperator_zero]
  simp only [hfac]
  exact TimeUniform.evolution_one N

omit [DecidableEq n] in
/-- `exp (c • A) = 1` for a vanishing real scalar `c` (`ode:thm:time`). -/
theorem exp_real_smul_zero (c : ℝ) (A : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hc : c = 0) : NormedSpace.exp (c • A) = 1 := by
  have hz : c • A = 0 := by
    subst hc
    ext v i
    simp only [_root_.smul_apply, zero_apply, PiLp.zero_apply, zero_smul]
  rw [hz]
  exact NormedSpace.exp_zero

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- **The discretised target at `T = 0`.** On a mesh of `[0, 0]` every forcing source
`Δ_q b̃_q` vanishes and every slot duration vanishes, so the released discretised target is
the initial state (`ode:thm:time`). -/
theorem target_zero (D : Data (X × Fin M) n Z s) (hM : 0 < M) (t : ℕ → ℝ) (N : ℕ) (x : X)
    (y0 : EuclideanSpace ℂ n) (bs : Fin M → EuclideanSpace ℂ n) (hmesh : IsMesh t M 0) :
    MeshSampling.target D hM t 0 N x y0 bs = y0 := by
  have hfam : ∀ a, MeshSampling.family D (pieceOf t 0 N hM) N 0 x a (-Complex.I) = 1 := by
    intro a
    rw [MeshSampling.family_neg_I]
    have h1 : ∀ k : ℕ, NormedSpace.exp ((0 / (N : ℝ) * TimeDependentODE.mask
        (TimeDependentODE.Sampling.start a) (pieceOf t 0 N hM k)) •
          (-MeshSampling.generator D (pieceOf t 0 N hM) x k)) = 1 :=
      fun k => exp_real_smul_zero _ _ (by rw [zero_div, zero_mul])
    simp only [h1]
    exact TimeUniform.evolution_one N
  have hsrc : ∀ q : Fin M, MeshSampling.sources y0 t bs (some q) = 0 := by
    intro q
    have h1 : t ((q : ℕ) + 1) = 0 :=
      le_antisymm (hmesh.le_last (Nat.succ_le_of_lt q.isLt)) (hmesh.nonneg _)
    have h2 : t (q : ℕ) = 0 := le_antisymm (hmesh.le_last q.isLt.le) (hmesh.nonneg _)
    change (t ((q : ℕ) + 1) - t q) • bs q = 0
    rw [h1, h2, sub_self, zero_smul]
  unfold MeshSampling.target
  rw [Fintype.sum_option]
  simp only [hfam, hsrc, one_apply_eq_self, map_zero, Finset.sum_const_zero, add_zero]
  rfl

set_option maxHeartbeats 3000000 in
/-- **The released general-mesh outcome of `ode:thm:time` with a matrix-query budget.** One
public trial family over `TimeDependentExtensions.MeshSource.physicalOracle` on `N` slots, with
the released public seed and output flag, chosen before the instance, such that for every valid
instance (the instance hypotheses of `TimeDependentExtensions.ODE.Outcome`) the released
complete certificate holds and the certified four-attempt protocol has worst-case matrix-query
count at most `Q`, so every history makes at most `Q` matrix queries. Without the budget this is
`TimeDependentExtensions.ODE.Outcome` (`outcome_of_budget`). -/
def BudgetOutcome (D : Data (X × Fin M) n Z s) (hM : 0 < M) (t : ℕ → ℝ) (N : ℕ)
    (etaH etaD T g ε r₀ : ℝ) (rb : Fin M → ℝ)
    (J₀ : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (Jb : X → Fin M → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (seed : EuclideanSpace ℂ n) (Q : ℝ) : Prop :=
  ∃ (d : ℕ)
    (E : TimeDependentODE.NativeSource.SourceSpace (TimeDependentODE.Index D T g ε) n M →L[ℂ]
      MeshSource.MatrixSpace (TimeDependentODE.Index D T g ε) n Z M N d)
    (q : ℕ → MultiOracleCircuit.Program
      (MeshSource.physicalOracle (ι := TimeDependentODE.Index D T g ε) D N d J₀ Jb)),
    (∀ j y, IsUnitary ((q j).eval y)) ∧
    ∀ (x : X) (G : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
      (b : Fin M → ℝ → EuclideanSpace ℂ n) (sol : ℝ → EuclideanSpace ℂ n)
      (bs : Fin M → EuclideanSpace ℂ n) (bmax : ℝ),
      (∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), TimeDependentODE.Accretive (G r u)) →
      (∀ r : Fin M, IntervalIntegrable (G r) volume (t r) (t ((r : ℕ) + 1))) →
      (∀ r : Fin M, IntervalIntegrable (b r) volume (t r) (t ((r : ℕ) + 1))) →
      (∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), ‖b r u‖ ≤ bmax) →
      (∀ r : Fin M, TimeDependentODE.SolvesODE (G r) (b r) sol (t r) (t ((r : ℕ) + 1))) →
      ‖sol 0‖ = r₀ → (∀ r, ‖bs r‖ = rb r) →
      (sol 0 ≠ 0 → J₀ x seed = ODEStateNormalization.unitDirection (sol 0)) →
      (∀ r, bs r ≠ 0 → Jb x r seed = ODEStateNormalization.unitDirection (bs r)) →
      sol T ≠ 0 →
      MeshSampling.mass r₀ t rb ≤ g * ‖sol T‖ →
      (r₀ + bmax * T) * (∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1),
          ‖G r u - SparseStateOverlap.matrixOperator (D.matrix (x, r))‖) +
        (∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1), ‖b r u - bs r‖) +
          ODE.publicError D t T N r₀ rb ≤ ε * MeshSampling.mass r₀ t rb / (2000 * g) →
      ∃ h : ODECompleteTrial.Certificate q
          (ODEGroverAverage.chosenIterations (TimeDependentODE.ratio g))
          (MeshSource.input D hM (Sum.inr false) N d
            (ODECompiledSource.seed E (ODE.coefficients D t T g ε r₀ rb) seed))
          (MeshSource.input D hM (Sum.inr false) N d ∘L
            ODECompiledSource.output E (ODE.coefficients D t T g ε r₀ rb))
          x (sol T) (s : ℝ)
          (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) (TimeDependentODE.ratio g)
            (TimeDependentODE.accuracy ε))
          (ImprovedODEQueryBudget.logBudget (TimeDependentODE.ratio g)
            (TimeDependentODE.accuracy ε)) (TimeDependentODE.ratio g) ε,
        ((ODECompleteTrial.algorithm h.trial).worstCost
          (ODESourceQueryBudget.matrixWeight (fun _ => 1)) : ℝ) ≤ Q

set_option maxHeartbeats 3000000 in
/-- **The released trial family on `N` slots with the identity SELECT** (`ode:thm:time`). For
every label type, clean encoding `E` and public coefficient table `a`, the released public trial
family `TimeDependentExtensions.MeshSource.publicTrials` built on the identity program consists
of unitary circuits and, for every instance whose source certificate holds for the identity
program, with actual coefficients `a` and a discretised target `y` within direction `ε/1000` of
the target, satisfies the released complete certificate with worst-case matrix-query count
`0`. -/
theorem identity_trials {ι : Type*} [Fintype ι] [DecidableEq ι] (D : Data (X × Fin M) n Z s)
    (hM : 0 < M) (i0 : ι) (N d : ℕ) (J₀ : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (Jb : X → Fin M → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ₀ : ∀ x, IsUnitary (J₀ x)) (hJb : ∀ x r, IsUnitary (Jb x r))
    (E : TimeDependentODE.NativeSource.SourceSpace ι n M →L[ℂ]
      MeshSource.MatrixSpace ι n Z M N d) (hE : E† ∘L E = 1)
    (c : ι → ℂ) (a : Option (Fin M) × ι → ℂ) (ha : 0 < ODECoherentLCU.coefficientMass a)
    (seed : EuclideanSpace ℂ n) (hSeed : ‖seed‖ = 1) (Θ ell g ε : ℝ)
    (hg : 1 ≤ TimeDependentODE.ratio g) (hε : 0 ≤ ε)
    (hShape : 0 ≤ ImprovedODEQueryBudget.queryShape (s : ℝ) Θ ell) :
    ∃ q : ℕ → MultiOracleCircuit.Program
        (MeshSource.physicalOracle (ι := ι) D N d J₀ Jb),
      (∀ j y, IsUnitary ((q j).eval y)) ∧
      ∀ (x : X) (z : Option (Fin M) → EuclideanSpace ℂ n) (y target : EuclideanSpace ℂ n),
        ODEActualSourceError.Certificate E z c (TimeDependentODE.SourceTD.branchTD (J₀ x) (Jb x))
          ((MultiOracleCircuit.Program.identity
            (O := MeshSource.matrixOracle (ι := ι) D N d)).eval x)
          seed y (TimeDependentODE.ratio g) (TimeDependentODE.accuracy ε) →
        ODEActualSourceError.coefficients z c = a →
        ‖ODEStateNormalization.unitDirection y -
          ODEStateNormalization.unitDirection target‖ ≤ ε / 1000 →
        target ≠ 0 →
        ∃ h : ODECompleteTrial.Certificate q
          (ODEGroverAverage.chosenIterations (TimeDependentODE.ratio g))
          (MeshSource.input D hM i0 N d (ODECompiledSource.seed E a seed))
          (MeshSource.input D hM i0 N d ∘L ODECompiledSource.output E a)
          x target (s : ℝ) Θ ell (TimeDependentODE.ratio g) ε,
          ((ODECompleteTrial.algorithm h.trial).worstCost
            (ODESourceQueryBudget.matrixWeight (fun _ => 1)) : ℝ) ≤ 0 := by
  let pN : MultiOracleCircuit.Program (MeshSource.matrixOracle (ι := ι) D N d) :=
    MultiOracleCircuit.Program.identity
  let q := MeshSource.publicTrials D hM i0 N d pN J₀ Jb E hE a seed
    (ODECompiledSource.seed_unit E a hE ha seed hSeed)
    (ODECompiledSource.output_isometry E a hE ha)
  have hCost : ∀ j, (q j).cost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) = 0 :=
    fun j => trial_matrix_cost D hM i0 N d J₀ Jb E hE a seed _ _ j
  have hUnitary : ∀ j y, IsUnitary ((q j).eval y) := fun j y => (q j).eval_unitary
    (MeshSource.physicalOracle_unitary D N d J₀ Jb hJ₀ hJb) y
  refine ⟨q, hUnitary, fun x z y target hCert hCoeff hDir hTarget => ?_⟩
  have hq : (pN.count : ℝ) ≤ 10616832 * ImprovedODEQueryBudget.queryShape (s : ℝ) Θ ell := by
    rw [MultiOracleCircuit.Program.count_identity, Nat.cast_zero]
    exact mul_nonneg (by norm_num) hShape
  have hTrial := MeshSource.coefficient_trial_certificate D hM i0 N d pN
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

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- The certified error of the general-mesh theorem is nonnegative (`ode:thm:time`). -/
theorem certified_error_nonneg (D : Data (X × Fin M) n Z s) (t : ℕ → ℝ) (T : ℝ) (N : ℕ)
    (r₀ : ℝ) (rb : Fin M → ℝ) (hmesh : IsMesh t M T) (hT : 0 ≤ T) (h₀ : 0 ≤ r₀)
    (hb : ∀ r, 0 ≤ rb r) (x : X) (G : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (b : Fin M → ℝ → EuclideanSpace ℂ n) (bs : Fin M → EuclideanSpace ℂ n) (bmax : ℝ)
    (hbmax : 0 ≤ bmax) :
    0 ≤ (r₀ + bmax * T) * (∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1),
          ‖G r u - SparseStateOverlap.matrixOperator (D.matrix (x, r))‖) +
        (∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1), ‖b r u - bs r‖) +
          ODE.publicError D t T N r₀ rb := by
  have hI1 : 0 ≤ ∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1),
      ‖G r u - SparseStateOverlap.matrixOperator (D.matrix (x, r))‖ :=
    Finset.sum_nonneg fun r _ =>
      intervalIntegral.integral_nonneg (hmesh.mono (Nat.le_succ r)) fun _ _ => norm_nonneg _
  have hI2 : 0 ≤ ∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1), ‖b r u - bs r‖ :=
    Finset.sum_nonneg fun r _ =>
      intervalIntegral.integral_nonneg (hmesh.mono (Nat.le_succ r)) fun _ _ => norm_nonneg _
  have hmass : 0 ≤ MeshSampling.mass r₀ t rb := by
    unfold MeshSampling.mass
    exact add_nonneg h₀ (Finset.sum_nonneg fun q _ =>
      mul_nonneg (hmesh.length_nonneg q) (hb q))
  have hP : 0 ≤ ODE.publicError D t T N r₀ rb := by
    unfold ODE.publicError
    apply mul_nonneg (mul_nonneg (Nat.cast_nonneg s) D.scale_pos.le)
    apply add_nonneg
    · exact div_nonneg (Finset.sum_nonneg fun q _ => mul_nonneg (sq_nonneg _) (hb q))
        (by norm_num)
    · exact mul_nonneg (mul_nonneg (Nat.cast_nonneg M) (div_nonneg hT (Nat.cast_nonneg N)))
        hmass
  have hr : 0 ≤ r₀ + bmax * T := add_nonneg h₀ (mul_nonneg hbmax hT)
  positivity

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
/-- **The general-mesh form of Theorem `ode:thm:time` at zero time or with a known zero
generator.** If `T = 0` or the public energy bounds give `η_H + R η_D = 0`, the released trial
family on `N` slots with the identity SELECT satisfies `BudgetOutcome` with `Q = 0`: with the
released public seed and flag, every valid instance has the released complete certificate
(success at least `175/256 > 2/3`, conditional trace distance at most `ε`, at most `40 g'` calls
of each source interface, `g' = 2 g`), and the protocol makes no matrix query in any history.
The slot conditions and the column promises are not needed. -/
theorem zero_solver (D : Data (X × Fin M) n Z s) (hM : 0 < M) (t : ℕ → ℝ) {N : ℕ} (hN : 0 < N)
    (etaH etaD T g ε r₀ : ℝ) (rb : Fin M → ℝ)
    (hH : 0 ≤ etaH) (hDiss : 0 ≤ etaD) (hT : 0 ≤ T)
    (hZero : T = 0 ∨ etaH + TimeDependentODE.radius g ε * etaD = 0) (hg : 1 ≤ g)
    (hε : 0 < ε) (hεOne : ε ≤ 1) (hmesh : IsMesh t M T)
    (h₀ : 0 ≤ r₀) (hb : ∀ r, 0 ≤ rb r) (hB : 0 < MeshSampling.mass r₀ t rb)
    (hrH : ∀ y i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix y) i j‖ ^ 2 ≤ etaH ^ 2)
    (hrD : ∀ y i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix y) i j‖ ^ 2 ≤ etaD ^ 2)
    (hPSD : ∀ (y : X × Fin M) (w : EuclideanSpace ℂ n), 0 ≤ (inner ℂ w
      (SparseStateOverlap.matrixOperator (ODEMatrixEnergy.dissipativePart (D.matrix y)) w)).re)
    (J₀ : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (Jb : X → Fin M → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ₀ : ∀ x, IsUnitary (J₀ x)) (hJb : ∀ x r, IsUnitary (Jb x r))
    (seed : EuclideanSpace ℂ n) (hSeed : ‖seed‖ = 1) :
    BudgetOutcome D hM t N etaH etaD T g ε r₀ rb J₀ Jb seed 0 := by
  have hg' : 1 ≤ TimeDependentODE.ratio g := by unfold TimeDependentODE.ratio; linarith
  have hε' : 0 < TimeDependentODE.accuracy ε := by
    unfold TimeDependentODE.accuracy; linarith
  have hε'One : TimeDependentODE.accuracy ε ≤ 1 := by
    unfold TimeDependentODE.accuracy; linarith
  have hε'Half : TimeDependentODE.accuracy ε ≤ 1 / 2 := by
    unfold TimeDependentODE.accuracy; linarith
  have hν : 0 < TimeDependentODE.precision g ε :=
    ImprovedODEQueryBudget.precision_pos _ _ hg' hε'
  let σ : ℕ → Fin M := pieceOf t T N hM
  -- One public Gaussian table for every product family.
  have hL : 0 ≤ TimeDependentODE.lipschitz D T :=
    mul_nonneg hT (mul_nonneg (Nat.cast_nonneg s) D.scale_pos.le)
  obtain ⟨_hGrid, _hNodes, hMass, hApprox⟩ := TimeDependentODE.GaussianLCHS.table_certificate
    (fun y : X × Option (Fin M) => MeshSampling.family D σ N T y.1 y.2)
    (fun y z => MeshSampling.family_analyticAt D σ N T y.1 y.2 z)
    (fun y z hz => MeshSampling.family_norm_le_one D σ N T hT hPSD y.1 y.2 z hz)
    (TimeDependentODE.lipschitz D T) hL
    (fun y k l => MeshSampling.family_lipschitz D σ hN T hT y.1 y.2 k l)
    (TimeDependentODE.ratio g) (TimeDependentODE.accuracy ε) hg' hε' hε'One
  have hc : ODECoherentLCU.coefficientMass (TimeDependentODE.lchsCoefficients D T g ε) = 3 :=
    ODECoefficientPadding.coefficientMass_eq _ 3 hMass
  -- Every branch product is the identity.
  have hOne : ∀ (x : X) (a' : TimeDependentODE.NativeSource.Label
      (TimeDependentODE.Index D T g ε) M),
      MeshSelect.branchEvolution D σ N (TimeDependentODE.nodeTable D T g ε)
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
  let d := TimeDependentODE.Select.degree (s : ℝ) 1 ρ T (TimeDependentODE.precision g ε) N
  let E : TimeDependentODE.NativeSource.SourceSpace (TimeDependentODE.Index D T g ε) n M →L[ℂ]
      MeshSource.MatrixSpace (TimeDependentODE.Index D T g ε) n Z M N d :=
    MeshSelect.alignedInput D hM σ (TimeDependentODE.NativeSource.dummy hM i0) N 1 ρ T
      (TimeDependentODE.precision g ε)
  have hEiso : E† ∘L E = 1 := alignedInput_isometry D hM σ _ N 1 ρ T _
  let a := ODE.coefficients D t T g ε r₀ rb
  have ha : 0 < ODECoherentLCU.coefficientMass a := by
    rw [show a = MeshSampling.coefficients r₀ t rb
        (TimeDependentODE.lchsCoefficients D T g ε) from rfl,
      MeshSampling.coefficients_mass r₀ t rb h₀ hmesh.mono hb hB _ hc]
    norm_num
  have hΘ : 0 ≤ ImprovedODEQueryBudget.theta (T * etaH) (T * etaD)
      (TimeDependentODE.ratio g) (TimeDependentODE.accuracy ε) :=
    ImprovedODEQueryBudget.theta_nonneg _ _ _ _ (mul_nonneg hT hH) (mul_nonneg hT hDiss)
      hg' hε' hε'One
  have hLog : 0 ≤ ImprovedODEQueryBudget.logBudget (TimeDependentODE.ratio g)
      (TimeDependentODE.accuracy ε) :=
    le_trans zero_le_one (ImprovedODEQueryBudget.logBudget_ge_one _ _ hg' hε' hε'One)
  obtain ⟨q, hUnitary, hTrials⟩ := identity_trials D hM i0 N d J₀ Jb hJ₀ hJb E hEiso
    (TimeDependentODE.lchsCoefficients D T g ε) a ha seed hSeed
    (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) (TimeDependentODE.ratio g)
      (TimeDependentODE.accuracy ε))
    (ImprovedODEQueryBudget.logBudget (TimeDependentODE.ratio g) (TimeDependentODE.accuracy ε))
    g ε hg' hε.le (ImprovedODEQueryBudget.queryShape_nonneg _ _ _ hΘ hLog)
  refine ⟨d, E, q, hUnitary, ?_⟩
  intro x G b sol bs bmax hG hGint hbint hbB hsol h0 hbn hInitial hForcing hTarget hBudget
    hDisc
  have hbmax : 0 ≤ bmax :=
    (norm_nonneg _).trans (hbB ⟨0, hM⟩ (t 0) ⟨le_rfl, hmesh.mono (Nat.zero_le 1)⟩)
  -- The discretised target of the represented samples.
  let z := MeshSampling.sources (sol 0) t bs
  let y := MeshSampling.target D hM t T N x (sol 0) bs
  have hzNorm : ∀ a', ‖z a'‖ = MeshSampling.norms r₀ t rb a' :=
    MeshSampling.sources_norm (sol 0) t hmesh.mono bs r₀ rb h0 hbn
  have hMassZ : ODESourceBranches.mass z = MeshSampling.mass r₀ t rb :=
    MeshSampling.mass_eq z r₀ t rb hzNorm
  have hErr : ‖sol T - y‖ ≤ (r₀ + bmax * T) * (∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1),
        ‖G r u - SparseStateOverlap.matrixOperator (D.matrix (x, r))‖) +
      (∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1), ‖b r u - bs r‖) +
        ODE.publicError D t T N r₀ rb := by
    by_cases hT0 : T = 0
    · have hy : y = sol 0 := by
        change MeshSampling.target D hM t T N x (sol 0) bs = sol 0
        subst hT0
        exact target_zero D hM t N x (sol 0) bs hmesh
      have hsolT : sol T = sol 0 := congrArg sol hT0
      rw [hy, hsolT, sub_self, norm_zero]
      exact certified_error_nonneg D t T N r₀ rb hmesh hT h₀ hb x G b bs bmax hbmax
    · have hTpos : 0 < T := lt_of_le_of_ne hT (Ne.symm hT0)
      have h := MeshSampling.target_error D hM hPSD x hmesh hTpos hN G b sol bs bmax hbmax hG
        hGint hbint hbB hsol
      have hsum : ∑ a', ‖MeshSampling.sources (sol 0) t bs a'‖ =
          MeshSampling.mass r₀ t rb := by
        rw [← hMassZ]
        rfl
      rw [hsum, h0] at h
      simp only [hbn] at h
      exact h
  obtain ⟨hy, hBy, hDir⟩ := TimeDependentODE.Sampling.target_budget (sol T) y
    (MeshSampling.mass r₀ t rb) g ε _ hg hε hεOne hTarget hBudget hErr hDisc
  have hCoeff : ODEActualSourceError.coefficients z
      (TimeDependentODE.lchsCoefficients D T g ε) = a :=
    MeshSampling.actual_coefficients_eq z r₀ t rb hzNorm _
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
        have hbr : bs r ≠ 0 := by
          intro h
          apply hz
          change (t ((r : ℕ) + 1) - t r) • bs r = 0
          rw [h, smul_zero]
        have hΔ : 0 < t ((r : ℕ) + 1) - t r := by
          rcases (hmesh.length_nonneg r).lt_or_eq with h | h
          · exact h
          · exfalso
            apply hz
            change (t ((r : ℕ) + 1) - t r) • bs r = 0
            rw [← h, zero_smul]
        change Jb x r seed = ODEStateNormalization.unitDirection
          ((t ((r : ℕ) + 1) - t r) • bs r)
        rw [TimeDependentODE.Sampling.unitDirection_smul _ hΔ (bs r)]
        exact hForcing r hbr
  have hNorm : ‖y‖ ≤ ODESourceBranches.mass z :=
    MeshSampling.target_norm_le D hM t T hT N hPSD x (sol 0) bs
  have hBudget' : ODESourceBranches.mass z ≤ TimeDependentODE.ratio g * ‖y‖ := by
    rw [hMassZ]
    unfold TimeDependentODE.ratio
    exact hBy
  have hSim : ‖(MultiOracleCircuit.Program.identity (O := MeshSource.matrixOracle
        (ι := TimeDependentODE.Index D T g ε) D N d)).eval x ∘L E - E ∘L WeightedClock.diagonal
      (fun a' : Option (Fin M) × TimeDependentODE.Index D T g ε =>
        MeshSelect.branchEvolution D σ N (TimeDependentODE.nodeTable D T g ε)
          (TimeDependentODE.Sampling.durationTable T) x (a'.1, a'.2))‖ ≤
        ImprovedODEQueryBudget.precision (TimeDependentODE.ratio g)
          (TimeDependentODE.accuracy ε) := by
    have hDiag : WeightedClock.diagonal
        (fun a' : Option (Fin M) × TimeDependentODE.Index D T g ε =>
          MeshSelect.branchEvolution D σ N (TimeDependentODE.nodeTable D T g ε)
            (TimeDependentODE.Sampling.durationTable T) x (a'.1, a'.2)) = 1 := by
      simp only [hOne]
      exact WeightedClock.diagonal_one
    rw [hDiag, MultiOracleCircuit.Program.eval_identity, sub_eq_zero.mpr, norm_zero]
    · exact hν.le
    · rfl
  have hLCHS : ∀ a', ‖(∑ i, TimeDependentODE.lchsCoefficients D T g ε i •
      MeshSelect.branchEvolution D σ N (TimeDependentODE.nodeTable D T g ε)
        (TimeDependentODE.Sampling.durationTable T) x (a', i)) -
        MeshSampling.family D σ N T x a' (-Complex.I)‖ ≤
          2 * ImprovedODEQueryBudget.precision (TimeDependentODE.ratio g)
            (TimeDependentODE.accuracy ε) := by
    intro a'
    have hsum : (∑ i, TimeDependentODE.lchsCoefficients D T g ε i •
        MeshSelect.branchEvolution D σ N (TimeDependentODE.nodeTable D T g ε)
          (TimeDependentODE.Sampling.durationTable T) x (a', i)) =
          ∑ j, TimeDependentODE.GaussianLCHS.coefficients (TimeDependentODE.lipschitz D T)
              (TimeDependentODE.ratio g) (TimeDependentODE.accuracy ε) j •
            MeshSampling.family D σ N T x a'
              (TimeDependentODE.GaussianLCHS.nodes (TimeDependentODE.lipschitz D T)
                (TimeDependentODE.ratio g) (TimeDependentODE.accuracy ε) j : ℂ) := by
      simp only [MeshSampling.branchEvolution_eq_family]
      exact TimeDependentODE.Sampling.padded_sum _ _ _
    rw [hsum]
    exact hApprox (x, a')
  have hQuad : ‖(∑ a', MeshSampling.family D σ N T x a' (-Complex.I) (z a')) - y‖ ≤
      ImprovedODEQueryBudget.precision (TimeDependentODE.ratio g)
        (TimeDependentODE.accuracy ε) * ODESourceBranches.mass z := by
    rw [show (∑ a', MeshSampling.family D σ N T x a' (-Complex.I) (z a')) = y from rfl,
      sub_self, norm_zero]
    exact mul_nonneg hν.le (ODESourceBranches.mass_nonneg z)
  have hCert : ODEActualSourceError.Certificate E z (TimeDependentODE.lchsCoefficients D T g ε)
      (TimeDependentODE.SourceTD.branchTD (J₀ x) (Jb x))
      ((MultiOracleCircuit.Program.identity (O := MeshSource.matrixOracle
        (ι := TimeDependentODE.Index D T g ε) D N d)).eval x) seed y
        (TimeDependentODE.ratio g) (TimeDependentODE.accuracy ε) :=
    ODEActualSourceError.actual_source_certificate E hEiso z
      (TimeDependentODE.lchsCoefficients D T g ε) hc
      (TimeDependentODE.SourceTD.branchTD (J₀ x) (Jb x)) hJ seed hSeed hPrep _
      isUnitary_one
      (fun a' i => MeshSelect.branchEvolution D σ N (TimeDependentODE.nodeTable D T g ε)
        (TimeDependentODE.Sampling.durationTable T) x (a', i))
      (fun a' => MeshSampling.family D σ N T x a' (-Complex.I)) y
      (TimeDependentODE.ratio g) (TimeDependentODE.accuracy ε)
      hy hg' hε' hε'Half hNorm hBudget' hSim hLCHS hQuad
  exact hTrials x z y (sol T) hCert hCoeff hDir hTarget

/-- Forgetting the budget gives the released general-mesh outcome of `ode:thm:time`. -/
theorem outcome_of_budget (D : Data (X × Fin M) n Z s) (hM : 0 < M) (t : ℕ → ℝ) (N : ℕ)
    (etaH etaD T g ε r₀ : ℝ) (rb : Fin M → ℝ)
    (J₀ : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (Jb : X → Fin M → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (seed : EuclideanSpace ℂ n) (Q : ℝ)
    (h : BudgetOutcome D hM t N etaH etaD T g ε r₀ rb J₀ Jb seed Q) :
    ODE.Outcome D hM t N etaH etaD T g ε r₀ rb J₀ Jb seed := by
  obtain ⟨d, E, q, hU, hC⟩ := h
  exact ⟨d, E, q, hU, fun x G b sol bs bmax h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 =>
    (hC x G b sol bs bmax h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12).fst⟩

/-- The released general-mesh outcome of `ode:thm:time` satisfies `BudgetOutcome` with `Q` the
released worst-case bound `1274019840 g' (√s Θ + √(s Θ ℓ) + ℓ)`. -/
theorem budget_of_outcome (D : Data (X × Fin M) n Z s) (hM : 0 < M) (t : ℕ → ℝ) (N : ℕ)
    (etaH etaD T g ε r₀ : ℝ) (rb : Fin M → ℝ)
    (J₀ : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (Jb : X → Fin M → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (seed : EuclideanSpace ℂ n)
    (h : ODE.Outcome D hM t N etaH etaD T g ε r₀ rb J₀ Jb seed) :
    BudgetOutcome D hM t N etaH etaD T g ε r₀ rb J₀ Jb seed
      (1274019840 * TimeDependentODE.ratio g * ImprovedODEQueryBudget.queryShape (s : ℝ)
        (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) (TimeDependentODE.ratio g)
          (TimeDependentODE.accuracy ε))
        (ImprovedODEQueryBudget.logBudget (TimeDependentODE.ratio g)
          (TimeDependentODE.accuracy ε))) := by
  obtain ⟨d, E, q, hU, hC⟩ := h
  refine ⟨d, E, q, hU, fun x G b sol bs bmax h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 => ?_⟩
  have hc := hC x G b sol bs bmax h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  exact ⟨hc, hc.matrix_queries⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
/-- **The general-mesh form of Theorem `ode:thm:time` for every `T ≥ 0`.** Under the
hypotheses of the released `TimeDependentExtensions.ODE.solver` with `0 ≤ T` in place of
`0 < T` and without the positivity of `ρ = η_H + R η_D`, `BudgetOutcome` holds with
`Q = if T = 0 ∨ ρ = 0 then 0 else 1274019840 g' (√s Θ + √(s Θ ℓ) + ℓ)`, `g' = 2 g`. -/
theorem solver_nonneg (D : Data (X × Fin M) n Z s) (hM : 0 < M) (t : ℕ → ℝ) {N : ℕ}
    (hN : 0 < N) (etaH etaD T g ε r₀ : ℝ) (rb : Fin M → ℝ)
    (hH : 0 ≤ etaH) (hDiss : 0 ≤ etaD) (hT : 0 ≤ T) (hg : 1 ≤ g)
    (hε : 0 < ε) (hεOne : ε ≤ 1) (hmesh : IsMesh t M T)
    (hClock : 8 * s * ((etaH + TimeDependentODE.radius g ε * etaD) * T) ≤ N)
    (hCayley : 3 * (Real.sqrt (2 * (s : ℝ)) *
      ((etaH + TimeDependentODE.radius g ε * etaD) * T)) ^ 3 ≤
        TimeDependentODE.precision g ε * (N : ℝ) ^ 2)
    (h₀ : 0 ≤ r₀) (hb : ∀ r, 0 ≤ rb r) (hB : 0 < MeshSampling.mass r₀ t rb)
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
    BudgetOutcome D hM t N etaH etaD T g ε r₀ rb J₀ Jb seed
      (if T = 0 ∨ etaH + TimeDependentODE.radius g ε * etaD = 0 then 0 else
        1274019840 * TimeDependentODE.ratio g * ImprovedODEQueryBudget.queryShape (s : ℝ)
          (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) (TimeDependentODE.ratio g)
            (TimeDependentODE.accuracy ε))
          (ImprovedODEQueryBudget.logBudget (TimeDependentODE.ratio g)
            (TimeDependentODE.accuracy ε))) := by
  by_cases hZero : T = 0 ∨ etaH + TimeDependentODE.radius g ε * etaD = 0
  · rw [if_pos hZero]
    exact zero_solver D hM t hN etaH etaD T g ε r₀ rb hH hDiss hT hZero hg hε hεOne hmesh h₀ hb
      hB hrH hrD hPSD J₀ Jb hJ₀ hJb seed hSeed
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
    exact budget_of_outcome D hM t N etaH etaD T g ε r₀ rb J₀ Jb seed
      (ODE.solver D hM t hN etaH etaD T g ε r₀ rb hH hDiss hTpos hg hε hεOne hmesh hρ hClock
        hCayley h₀ hb hB hrH hcH hrD hcD hPSD J₀ Jb hJ₀ hJb seed hSeed)

end
end SparseHamiltonian.ZeroTimeRemarks.ODEMesh
