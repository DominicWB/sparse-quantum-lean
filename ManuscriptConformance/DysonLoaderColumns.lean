import ManuscriptConformance.SourceLoaderColumns
import DysonFullClass.Theorem

/-!
# Lemma `odel:lem:dyson` on the full class with a loader specified on its clean columns (item D1)

The full-class Dyson solver `DysonFullClass.full_dyson` (Lemma `odel:lem:dyson`) runs the released
general-source pipeline: `P_w`, then the label-controlled `U_load = ∑_a |a⟩⟨a| ⊗ J_a` and the public
phases, then its matrix program, then `P_w†` on the label; randomised amplification of this actual
preparation with its actual inverse; the three-query control compiler; the four-trial wrapper.
Here the loader is any unitary `Lo` on the whole branch register (source label, Dyson LCU label and
data), specified only on the clean columns `|a, τ⟩|seed⟩` of the labels with nonzero source vectors.

* `trialCertificate_of_seed`: the released primitive trial certificate depends on a trial family
  only through its evaluations on the seed and its counts.
* `compiledTrials`, `compiledTrials_seed_congr`, `compiledTrials_matrix_cost`,
  `compiledTrials_source_cost`, `compiledTrials_total_cost`: the compiled amplified trials of the
  source-loaded program, for any counted interfaces, matrix access with a basis-image promise and
  layouts. They depend on the interfaces only through the seed column (from
  `GeneralSourceODE.Compiled.program_seed_congr`, `amplified_seed_congr`), with the same counts.
* `compiledTrials_shape`: the compiled trials have the amplification shape
  (`DysonSingleProgram.GroverShape`) of `full_dyson_shape`, for any counted interfaces.
* `herald_certificate_columns`: `herald_certificate` for the loader `Lo`, when `Lo` and `loader J`
  agree on the seed branch state after `P_w`.
* `full_dyson_shape_columns`: `full_dyson_shape` (with the amplification shape, the unit seed and
  the isometric output) for the loader `Lo`.
* `full_dyson_columns` (`FullValidColumns`, `fullOracleL`): the guarantee of `full_dyson` (the
  released complete certificate with cutoff `chosenIterations g'`, `g' = c_q ḡ e^z`, shape
  `K/589824` and accuracy `ε`) for one public trial family over the native calls of the original
  access and the counted interfaces with the loader `Lo`, for every valid instance with the
  loading hypotheses stated on the clean columns of `Lo`, from `full_dyson_shape_columns`. Its
  proof is the released proof of `full_dyson_shape` with `herald_certificate_columns` in place of
  `herald_certificate`, for the label-controlled family `GeneralSourceODE.columnLoader Lo` with
  the same columns.

The single-program and separate-primitive forms are in `DysonLoaderActual`.

Scope: the exact case of item D1 for this endpoint. Approximate columns (`DysonFullClass.Approx`)
are not treated. The released label-controlled form is unchanged.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 4096

namespace DysonFullClass

noncomputable section
open SparseHamiltonian ContinuousLinearMap OracleCircuit ODEStateNormalization
open SparseHamiltonian.GeneralSourceODE
open SparseHamiltonian.GeneralSourceODE.Compiled
open scoped InnerProduct BigOperators
set_option maxRecDepth 4096

/-! ### The released trial certificate transfers through the seed evaluations -/

section Transfer

variable {P R X L L' : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- **The released primitive trial certificate depends on a trial family only through its
evaluations on the seed and its counts.** -/
theorem trialCertificate_of_seed {V : (L ⊕ Bool) → X → R →L[ℂ] R} {V' : (L ⊕ Bool) → X → R →L[ℂ] R}
    {q : ℕ → MultiOracleCircuit.Program V} (q' : ℕ → MultiOracleCircuit.Program V') {M : ℕ}
    {ψ : R} {F : P →L[ℂ] R} {x : X} {target : P} {s Θ ell g η : ℝ}
    (h : ODEPrimitiveSourceJoin.TrialCertificate q M ψ F x target s Θ ell g η)
    (hEval : ∀ j, (q' j).eval x ψ = (q j).eval x ψ)
    (hMat : ∀ j, (q' j).cost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) =
      (q j).cost (ODESourceQueryBudget.matrixWeight (fun _ => 1)))
    (hSrc : ∀ j b, (q' j).cost (ODESourceQueryBudget.sourceWeight b) =
      (q j).cost (ODESourceQueryBudget.sourceWeight b))
    (hTot : ∀ j, (q' j).cost ODESourceQueryBudget.sourceTotalWeight =
      (q j).cost ODESourceQueryBudget.sourceTotalWeight) :
    ODEPrimitiveSourceJoin.TrialCertificate q' M ψ F x target s Θ ell g η where
  cutoff_pos := h.cutoff_pos
  cutoff_le := h.cutoff_le
  seed_unit := h.seed_unit
  output_isometry := h.output_isometry
  matrix_queries := fun j hj => by rw [hMat j]; exact h.matrix_queries j hj
  source_queries := fun j hj b => by rw [hSrc j b]; exact h.source_queries j hj b
  total_source_queries := fun j hj => by rw [hTot j]; exact h.total_source_queries j hj
  mean_success := by simp_rw [hEval]; exact h.mean_success
  direction_error := fun j hj hne => by
    rw [hEval j] at hne ⊢
    exact h.direction_error j hj hne

end Transfer


/-! ### The compiled trials for any counted interfaces -/

section Compiled

variable {ι P K X L : Type*} [Fintype ι]
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {N : ℕ} {O : L → X → K →L[ℂ] K}
  {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- The compiled amplified trials of the source-loaded program with the counted interfaces `S`
(for `S = sourceFamily Pw J φ`, the trial family of `herald_certificate`). -/
def compiledTrials (eA : Branch ι P N ≃ₗᵢ[ℂ] EuclideanSpace ℂ A)
    (eB : K ≃ₗᵢ[ℂ] EuclideanSpace ℂ B) (p : MultiOracleCircuit.Program O)
    (S : Bool → X → Branch ι P N →L[ℂ] Branch ι P N) (a0 : A) (b0 : B)
    (E : Branch ι P N →L[ℂ] K) (hE : E† ∘L E = 1) (c : ι → ℂ) (v : P)
    (hSeed : ‖ODECompiledSource.seed E (seedCoefficients c) v‖ = 1)
    (hOutput : (ODECompiledSource.output E (seedCoefficients c))† ∘L
      ODECompiledSource.output E (seedCoefficients c) = 1) :
    ℕ → MultiOracleCircuit.Program (ODECoordinateNativeControl.physicalOracle eA eB O S) :=
  fun j => ODECoordinateNativeControl.compile eA eB O S a0 b0
    (ODECountedAmplification.program (program p S E hE)
      (ODECompiledSource.output E (seedCoefficients c)) hOutput
      (ODECompiledSource.seed E (seedCoefficients c) v) hSeed j)

/-- **The compiled trials depend on the counted interfaces only through the seed column.** -/
theorem compiledTrials_seed_congr (eA : Branch ι P N ≃ₗᵢ[ℂ] EuclideanSpace ℂ A)
    (eB : K ≃ₗᵢ[ℂ] EuclideanSpace ℂ B) (p : MultiOracleCircuit.Program O)
    (hO : ∀ l x, IsUnitary (O l x))
    (S S' : Bool → X → Branch ι P N →L[ℂ] Branch ι P N)
    (hS : ∀ b x, IsUnitary (S b x)) (hS' : ∀ b x, IsUnitary (S' b x)) (a0 : A) (b0 : B)
    (image : L → X → B)
    (hvalid : ∀ l x, eB.conjStarAlgEquiv (O l x) (EuclideanSpace.single b0 1) =
      EuclideanSpace.single (image l x) 1)
    (E : Branch ι P N →L[ℂ] K) (hE : E† ∘L E = 1) (c : ι → ℂ) (v : P)
    (hSeed : ‖ODECompiledSource.seed E (seedCoefficients c) v‖ = 1)
    (hOutput : (ODECompiledSource.output E (seedCoefficients c))† ∘L
      ODECompiledSource.output E (seedCoefficients c) = 1) (x : X)
    (htrue : S true x = S' true x)
    (hfalse : S false x (ODEJointLCU.coefficientInput (seedCoefficients c) v) =
      S' false x (ODEJointLCU.coefficientInput (seedCoefficients c) v)) (j : ℕ) :
    (compiledTrials eA eB p S a0 b0 E hE c v hSeed hOutput j).eval x
        (ODECoordinateNativeControl.input eA eB a0 b0
          (ODECompiledSource.seed E (seedCoefficients c) v)) =
      (compiledTrials eA eB p S' a0 b0 E hE c v hSeed hOutput j).eval x
        (ODECoordinateNativeControl.input eA eB a0 b0
          (ODECompiledSource.seed E (seedCoefficients c) v)) := by
  have key : ∀ (T : Bool → X → Branch ι P N →L[ℂ] Branch ι P N)
      (_hT : ∀ b x, IsUnitary (T b x)),
      (compiledTrials eA eB p T a0 b0 E hE c v hSeed hOutput j).eval x
          (ODECoordinateNativeControl.input eA eB a0 b0
            (ODECompiledSource.seed E (seedCoefficients c) v)) =
        ODECoordinateNativeControl.input eA eB a0 b0
          ((ODECountedAmplification.program (program p T E hE)
            (ODECompiledSource.output E (seedCoefficients c)) hOutput
            (ODECompiledSource.seed E (seedCoefficients c) v) hSeed j).eval x
            (ODECompiledSource.seed E (seedCoefficients c) v)) := by
    intro T hT
    rw [← comp_apply, compiledTrials,
      ODECoordinateNativeControl.compile_eval eA eB O T hO hT a0 b0 image hvalid, comp_apply]
  rw [key S hS, key S' hS',
    Compiled.amplified_seed_congr p hO S S' hS hS' E hE _ hOutput _ hSeed x
      (Compiled.program_seed_congr p S S' E hE _ v x htrue hfalse) j]

/-- Matrix counts of the compiled trials, for any counted interfaces. -/
theorem compiledTrials_matrix_cost (eA : Branch ι P N ≃ₗᵢ[ℂ] EuclideanSpace ℂ A)
    (eB : K ≃ₗᵢ[ℂ] EuclideanSpace ℂ B) (p : MultiOracleCircuit.Program O)
    (S : Bool → X → Branch ι P N →L[ℂ] Branch ι P N) (a0 : A) (b0 : B)
    (E : Branch ι P N →L[ℂ] K) (hE : E† ∘L E = 1) (c : ι → ℂ) (v : P)
    (hSeed : ‖ODECompiledSource.seed E (seedCoefficients c) v‖ = 1)
    (hOutput : (ODECompiledSource.output E (seedCoefficients c))† ∘L
      ODECompiledSource.output E (seedCoefficients c) = 1) (w : L → ℕ) (j : ℕ) :
    (compiledTrials eA eB p S a0 b0 E hE c v hSeed hOutput j).cost
        (ODESourceQueryBudget.matrixWeight w) = 3 * ((2 * j + 1) * p.cost w) := by
  unfold compiledTrials
  rw [ODECoordinateNativeControl.compile_matrix_cost, ODECountedAmplification.cost_eq,
    program_matrix_cost]

/-- Interface counts of the compiled trials, for any counted interfaces. -/
theorem compiledTrials_source_cost (eA : Branch ι P N ≃ₗᵢ[ℂ] EuclideanSpace ℂ A)
    (eB : K ≃ₗᵢ[ℂ] EuclideanSpace ℂ B) (p : MultiOracleCircuit.Program O)
    (S : Bool → X → Branch ι P N →L[ℂ] Branch ι P N) (a0 : A) (b0 : B)
    (E : Branch ι P N →L[ℂ] K) (hE : E† ∘L E = 1) (c : ι → ℂ) (v : P)
    (hSeed : ‖ODECompiledSource.seed E (seedCoefficients c) v‖ = 1)
    (hOutput : (ODECompiledSource.output E (seedCoefficients c))† ∘L
      ODECompiledSource.output E (seedCoefficients c) = 1) (b : Bool) (j : ℕ) :
    (compiledTrials eA eB p S a0 b0 E hE c v hSeed hOutput j).cost
        (ODESourceQueryBudget.sourceWeight b) = 2 * j + 1 := by
  unfold compiledTrials
  rw [ODECoordinateNativeControl.compile_source_cost, ODECountedAmplification.cost_eq,
    program_source_cost, mul_one]

/-- Total interface counts of the compiled trials, for any counted interfaces. -/
theorem compiledTrials_total_cost (eA : Branch ι P N ≃ₗᵢ[ℂ] EuclideanSpace ℂ A)
    (eB : K ≃ₗᵢ[ℂ] EuclideanSpace ℂ B) (p : MultiOracleCircuit.Program O)
    (S : Bool → X → Branch ι P N →L[ℂ] Branch ι P N) (a0 : A) (b0 : B)
    (E : Branch ι P N →L[ℂ] K) (hE : E† ∘L E = 1) (c : ι → ℂ) (v : P)
    (hSeed : ‖ODECompiledSource.seed E (seedCoefficients c) v‖ = 1)
    (hOutput : (ODECompiledSource.output E (seedCoefficients c))† ∘L
      ODECompiledSource.output E (seedCoefficients c) = 1) (j : ℕ) :
    (compiledTrials eA eB p S a0 b0 E hE c v hSeed hOutput j).cost
        ODESourceQueryBudget.sourceTotalWeight = (2 * j + 1) * 2 := by
  unfold compiledTrials
  rw [ODECoordinateNativeControl.compile_source_total_cost, ODECountedAmplification.cost_eq,
    program_source_total_cost]

/-- **The compiled trials have the amplification shape** (`DysonSingleProgram.GroverShape`), for
any counted interfaces: the `j`-th trial is `(U₁ a U₂ a† U₃)^j a` for the compiled source-loaded
program `a` and the public fixed reflections `U₁ U₂ U₃` of `full_dyson_shape`, and its `w`-cost is
`(2j + 1)` times that of `a`. -/
theorem compiledTrials_shape (eA : Branch ι P N ≃ₗᵢ[ℂ] EuclideanSpace ℂ A)
    (eB : K ≃ₗᵢ[ℂ] EuclideanSpace ℂ B) (p : MultiOracleCircuit.Program O)
    (S : Bool → X → Branch ι P N →L[ℂ] Branch ι P N) (a0 : A) (b0 : B)
    (E : Branch ι P N →L[ℂ] K) (hE : E† ∘L E = 1) (c : ι → ℂ) (v : P)
    (hSeed : ‖ODECompiledSource.seed E (seedCoefficients c) v‖ = 1)
    (hOutput : (ODECompiledSource.output E (seedCoefficients c))† ∘L
      ODECompiledSource.output E (seedCoefficients c) = 1) (w : L ⊕ Bool → ℕ) :
    DysonSingleProgram.GroverShape (compiledTrials eA eB p S a0 b0 E hE c v hSeed hOutput) w
      (ODECoordinateNativeControl.compile eA eB O S a0 b0 (program p S E hE)) w
      (SubspaceOracle.lift (ODECoordinateNativeControl.input eA eB a0 b0) (-1))
      (SubspaceOracle.lift (ODECoordinateNativeControl.input eA eB a0 b0)
        (PhaseSubspaceGates.phase (ODEGroverRay.projector
          (ODECompiledSource.seed E (seedCoefficients c) v)) (-1)))
      (SubspaceOracle.lift (ODECoordinateNativeControl.input eA eB a0 b0)
        (PhaseSubspaceGates.phase (ODEHeraldedSuccess.successProjector
          (ODECompiledSource.output E (seedCoefficients c))) (-1))) :=
  DysonSingleProgram.Explicit.groverShape_compile
    (ODECoordinateNativeControl.input eA eB a0 b0)
    (ODECoordinateNativeControl.input_isometry eA eB a0 b0)
    (ODECoordinateNativeControl.letter eA eB O S b0) (program p S E hE)
    (ODEGroverRay.projector (ODECompiledSource.seed E (seedCoefficients c) v))
    (ODEHeraldedSuccess.successProjector (ODECompiledSource.output E (seedCoefficients c)))
    (ODEGroverRay.projector_isOrthogonalProjection _ hSeed)
    (ODEHeraldedSuccess.successProjector_isOrthogonalProjection _ hOutput) w

set_option maxHeartbeats 2000000 in
/-- **The released complete certificate for a loader specified on its clean columns.** Under the
hypotheses of `herald_certificate` for a label-controlled family `J`, the four-trial protocol of
the compiled trials with the loader `Lo` in its place has the released complete certificate, for
every unitary `Lo` with `Lo (P_w ⊗ 1)|seed state⟩ = loader J (P_w ⊗ 1)|seed state⟩`. -/
theorem herald_certificate_columns (p : MultiOracleCircuit.Program O)
    (hO : ∀ l x, IsUnitary (O l x))
    (Pw : X → Weights.LabelOp (Option (Fin N))) (hPw : ∀ x, IsUnitary (Pw x))
    (J : X → Option (Fin N) → P →L[ℂ] P) (hJ : ∀ x a, IsUnitary (J x a))
    (Lo : X → Branch ι P N →L[ℂ] Branch ι P N) (hLo : ∀ x, IsUnitary (Lo x))
    (φ : Option (Fin N) → ℂ) (hφ : ∀ a, ‖φ a‖ = 1)
    (E : Branch ι P N →L[ℂ] K) (hE : E† ∘L E = 1)
    (z : Option (Fin N) → P) (c : ι → ℂ) (hc : 0 < ODECoherentLCU.coefficientMass c)
    (v target : P) (hv : ‖v‖ = 1) (s Θ ell g ε : ℝ) (hg : 1 ≤ g) (hε : 0 ≤ ε)
    (htarget : target ≠ 0) (x : X)
    (hz : 0 < ODESourceBranches.mass z) (hW : WeightPrep (Pw x) z)
    (hLower : 1 / (4 * g) ≤
      ‖ODEActualSourceError.decoded E z c (phased (J x) φ) (p.eval x) v‖)
    (hUpper : ‖ODEActualSourceError.decoded E z c (phased (J x) φ) (p.eval x) v‖ ≤ 1 / 2)
    (hDir : ‖unitDirection (ODEActualSourceError.decoded E z c (phased (J x) φ) (p.eval x) v) -
      unitDirection target‖ ≤ ε / 500)
    (hq : (p.count : ℝ) ≤ 10616832 * ImprovedODEQueryBudget.queryShape s Θ ell)
    [FiniteDimensional ℂ P]
    (eA : Branch ι P N ≃ₗᵢ[ℂ] EuclideanSpace ℂ A)
    (eB : K ≃ₗᵢ[ℂ] EuclideanSpace ℂ B) (a0 : A) (b0 : B)
    (image : L → X → B)
    (hvalid : ∀ l x, eB.conjStarAlgEquiv (O l x) (EuclideanSpace.single b0 1) =
      EuclideanSpace.single (image l x) 1)
    (hSeed : ‖ODECompiledSource.seed E (seedCoefficients c) v‖ = 1)
    (hOutput : (ODECompiledSource.output E (seedCoefficients c))† ∘L
      ODECompiledSource.output E (seedCoefficients c) = 1)
    (hagree : Lo x (Weights.act (Pw x)
        (ODEJointLCU.coefficientInput (seedCoefficients c) v)) =
      Weights.loader (J x) (Weights.act (Pw x)
        (ODEJointLCU.coefficientInput (seedCoefficients c) v))) :
    ODECompleteTrial.Certificate
      (compiledTrials eA eB p (sourceFamilyL Pw Lo φ) a0 b0 E hE c v hSeed hOutput)
      (ODEGroverAverage.chosenIterations g)
      (ODECoordinateNativeControl.input eA eB a0 b0
        (ODECompiledSource.seed E (seedCoefficients c) v))
      (ODECoordinateNativeControl.input eA eB a0 b0 ∘L
        ODECompiledSource.output E (seedCoefficients c))
      x target s Θ ell g ε := by
  have hJcert := herald_trial_certificate p hO Pw hPw J hJ φ hφ E hE z c hc v target hv s Θ ell g
    ε hg x hz hW hLower hUpper hDir hq eA eB a0 b0 image hvalid hSeed hOutput
  have hfalse : sourceFamilyL (ι := ι) Pw Lo φ false x
      (ODEJointLCU.coefficientInput (seedCoefficients c) v) =
      sourceFamily (ι := ι) Pw J φ false x
        (ODEJointLCU.coefficientInput (seedCoefficients c) v) := by
    rw [sourceFamilyL_false, sourceFamily_false]
    unfold prepL prep
    simp only [comp_apply]
    rw [hagree]
  have hSL := sourceFamilyL_unitary (ι := ι) hPw hLo hφ
  have hSJ := sourceFamily_unitary (ι := ι) hPw hJ hφ
  have hL : ODEPrimitiveSourceJoin.TrialCertificate
      (compiledTrials eA eB p (sourceFamilyL Pw Lo φ) a0 b0 E hE c v hSeed hOutput)
      (ODEGroverAverage.chosenIterations g)
      (ODECoordinateNativeControl.input eA eB a0 b0
        (ODECompiledSource.seed E (seedCoefficients c) v))
      (ODECoordinateNativeControl.input eA eB a0 b0 ∘L
        ODECompiledSource.output E (seedCoefficients c))
      x target s Θ ell g (ε / 500) := by
    refine trialCertificate_of_seed _ hJcert (fun j => ?_) (fun j => ?_) (fun j b => ?_)
      (fun j => ?_)
    · have h := compiledTrials_seed_congr eA eB p hO (sourceFamilyL Pw Lo φ)
        (sourceFamily Pw J φ) hSL hSJ a0 b0 image hvalid E hE c v hSeed hOutput x
        ((sourceFamilyL_true Pw Lo φ x).trans (sourceFamily_true Pw J φ x).symm) hfalse j
      convert h using 2
      rfl
    · change (compiledTrials eA eB p (sourceFamilyL Pw Lo φ) a0 b0 E hE c v hSeed hOutput
          j).cost _ =
        (compiledTrials eA eB p (sourceFamily Pw J φ) a0 b0 E hE c v hSeed hOutput j).cost _
      rw [compiledTrials_matrix_cost, compiledTrials_matrix_cost]
    · change (compiledTrials eA eB p (sourceFamilyL Pw Lo φ) a0 b0 E hE c v hSeed hOutput
          j).cost _ =
        (compiledTrials eA eB p (sourceFamily Pw J φ) a0 b0 E hE c v hSeed hOutput j).cost _
      rw [compiledTrials_source_cost, compiledTrials_source_cost]
    · change (compiledTrials eA eB p (sourceFamilyL Pw Lo φ) a0 b0 E hE c v hSeed hOutput
          j).cost _ =
        (compiledTrials eA eB p (sourceFamily Pw J φ) a0 b0 E hE c v hSeed hOutput j).cost _
      rw [compiledTrials_total_cost, compiledTrials_total_cost]
  exact ODECompleteTrial.of_trialCertificate
    (fun j => MultiOracleCircuit.Program.eval_unitary _
      (ODECoordinateNativeControl.physicalOracle_unitary eA eB O _ hO hSL) x)
    hε htarget hL

end Compiled

end

/-! ### The full-class solver with a loader on its clean columns -/

noncomputable section
open SparseHamiltonian ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding Set
open MeasureTheory TimeDependentExtensions
open SparseHamiltonian.TimeDependentODE (Accretive)
open SparseHamiltonian.GeneralSourceExtensions.Mesh (meshScale meshScale_nonneg IsMeshPropagator
  endMap endMap_apply)
open SparseHamiltonian.GeneralSourceODE (sources phases phases_norm startTime mass_sources
  phased_prepares phased_isometry)
open SparseHamiltonian.GeneralSourceODE.Compiled (WeightPrep seedCoefficients phased
  publicLogicalTrials sourceFamily sourceFamilyL sourceFamilyL_unitary)
open ODELowerBoundExtensions.Dyson
open scoped InnerProduct BigOperators ODELowerBoundExtensions.Dyson

variable {X n Z : Type} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s Ks M m : ℕ}

/-- **The access of the full-class Dyson solver with the loader `Lo`**: the masked coherent
sampled-time native calls of `D₀` and the two counted interfaces with `Lo` in place of the
label-controlled loader (`false` the preparation `P_w`, `Lo` and the public phases; `true` the
label unpreparation `P_w†`). -/
abbrev fullOracleL (D : Data (X × Fin Ks) n Z s) (K M m : ℕ)
    (Pw : X → GeneralSourceODE.Weights.LabelOp (Option (Fin m)))
    (Lo : X → GeneralSourceODE.Native.SourceSpace (FIota K M) n m →L[ℂ]
      GeneralSourceODE.Native.SourceSpace (FIota K M) n m) (ω : Fin m → ℂ) :=
  ODECoordinateNativeControl.physicalOracle
    (GeneralSourceODE.Native.sourceLayout (ι := FIota K M) (n := n) m)
    (matrixLayout (n := n) (Z := Z) (Ks := Ks) (OmegaG (FLab K M m) K))
    (matrixOracle (OmegaG (FLab K M m) K) D)
    (sourceFamilyL (ι := FIota K M) Pw Lo (phases ω))

/-- **The valid instances for a loader specified on its clean columns**: `FullValidAt` with the
supplied weight preparation `P_w(x)` and the loading hypotheses stated on the clean columns
`|a, τ⟩|seed⟩` of `Lo` (for every Dyson LCU label `τ`). -/
def FullValidColumns (D₀ : Data (X × Fin Ks) n Z s) {M : ℕ} (σ : Fin M → Fin Ks) (t : ℕ → ℝ)
    (T η g cq ε : ℝ) (hη : 0 < η) {m : ℕ} (v : Fin m → ℝ) (ω : Fin m → ℂ)
    (Pw : X → GeneralSourceODE.Weights.LabelOp (Option (Fin m)))
    (Lo : X → GeneralSourceODE.Native.SourceSpace (FIota (fullDegree s η T g cq ε) M) n m →L[ℂ]
      GeneralSourceODE.Native.SourceSpace (FIota (fullDegree s η T g cq ε) M) n m)
    (seed : EuclideanSpace ℂ n) (x : X) (y : EuclideanSpace ℂ n) : Prop :=
  ∃ (G : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (b : Fin M → ℝ → EuclideanSpace ℂ n) (sol : ℝ → EuclideanSpace ℂ n)
    (bv : Fin m → EuclideanSpace ℂ n) (U : ℝ → EuclideanSpace ℂ n → ℝ → EuclideanSpace ℂ n)
    (ζ : ℝ),
    (∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), Accretive (G r u)) ∧
    RepresentedSampleODE.RegularPieces t G ∧
    RepresentedSampleODE.MildSolution t T b sol U ∧
    IsMeshPropagator G t T U ∧
    WeightPrep (Pw x) (sources (sol 0) bv ω) ∧
    (sol 0 ≠ 0 → ∀ τ : FIota (fullDegree s η T g cq ε) M,
      Lo x (PiLp.single 2 (none, τ) seed) =
        PiLp.single 2 (none, τ) (ODEStateNormalization.unitDirection (sol 0))) ∧
    (∀ i, ω i ≠ 0 → bv i ≠ 0 → ∀ τ : FIota (fullDegree s η T g cq ε) M,
      Lo x (PiLp.single 2 (some i, τ) seed) =
        PiLp.single 2 (some i, τ) (ODEStateNormalization.unitDirection (bv i))) ∧
    ODESourceBranches.mass (sources (sol 0) bv ω) ≤ cq * meshScale sol b t ∧
    ‖(∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1), U u (b r u) T) - ∑ i, ω i • U (v i) (bv i) T‖ ≤
      ζ * meshScale sol b t ∧
    sol T ≠ 0 ∧
    meshScale sol b t ≤ g * ‖sol T‖ ∧
    ζ + cq * (Real.exp (cellError σ (clipData D₀ η hη) x t G) - 1) ≤ ε / (2000 * g) ∧
    sol T = y

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
/-- **Lemma `odel:lem:dyson` on the full time-dependent class, with a loader specified on its
clean columns only (item D1, exact case), with the amplification shape**: `full_dyson_shape` for the
counted interfaces over the supplied `P_w` and a unitary loader `Lo` on the whole branch register
and the valid instances of `FullValidColumns`. One public trial family, unit seed and isometric
output over `fullOracleL D₀`, the compiled amplification of one public preparation `a` (the compiled
source/matrix preparation with `Lo`) with the public fixed reflections `U₁ U₂ U₃` of
`full_dyson_shape` (`DysonSingleProgram.GroverShape` for the matrix weight and for both source
interfaces), unitary trials and, on every valid instance, the released complete certificate. -/
theorem full_dyson_shape_columns (D₀ : Data (X × Fin Ks) n Z s) (hM : 0 < M) (σ : Fin M → Fin Ks)
    (t : ℕ → ℝ) (T η g cq ε : ℝ) (hmesh : IsMesh t M T) (hT : 0 < T) (hη : 0 < η)
    (hg : 1 ≤ g) (hcq : 1 ≤ cq) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (v : Fin m → ℝ) (hv : ∀ i, v i ∈ Icc 0 T) (ω : Fin m → ℂ)
    (Pw : X → GeneralSourceODE.Weights.LabelOp (Option (Fin m))) (hPw : ∀ x, IsUnitary (Pw x))
    (Lo : X → GeneralSourceODE.Native.SourceSpace (FIota (fullDegree s η T g cq ε) M) n m →L[ℂ]
      GeneralSourceODE.Native.SourceSpace (FIota (fullDegree s η T g cq ε) M) n m)
    (hLo : ∀ x, IsUnitary (Lo x)) (seed : EuclideanSpace ℂ n) (hSeed : ‖seed‖ = 1) :
    ∃ (q : ℕ → MultiOracleCircuit.Program
        (fullOracleL D₀ (fullDegree s η T g cq ε) M m Pw Lo ω))
      (ψ : FSpace Ks n Z (fullDegree s η T g cq ε) M m)
      (F : EuclideanSpace ℂ n →L[ℂ] FSpace Ks n Z (fullDegree s η T g cq ε) M m)
      (a : MultiOracleCircuit.Program (fullOracleL D₀ (fullDegree s η T g cq ε) M m Pw Lo ω))
      (U₁ U₂ U₃ : FSpace Ks n Z (fullDegree s η T g cq ε) M m →L[ℂ]
        FSpace Ks n Z (fullDegree s η T g cq ε) M m),
      DysonSingleProgram.GroverShape q (ODESourceQueryBudget.matrixWeight (fun _ => 1)) a
        (ODESourceQueryBudget.matrixWeight (fun _ => 1)) U₁ U₂ U₃ ∧
      (∀ b, DysonSingleProgram.GroverShape q (ODESourceQueryBudget.sourceWeight b) a
        (ODESourceQueryBudget.sourceWeight b) U₁ U₂ U₃) ∧
      ‖ψ‖ = 1 ∧ F† ∘L F = 1 ∧
      (∀ j x, IsUnitary ((q j).eval x)) ∧
      ∀ x y, FullValidColumns D₀ σ t T η g cq ε hη v ω Pw Lo seed x y →
        ODECompleteTrial.Certificate q
          (ODEGroverAverage.chosenIterations (fullAmp s η T g cq)) ψ F x y
          (s : ℝ) 0 (fullShape (fullDegree s η T g cq ε)) (fullAmp s η T g cq) ε := by
  classical
  obtain ⟨i₀⟩ : Nonempty n := by
    by_contra hn
    rw [not_nonempty_iff] at hn
    have h0 : seed = 0 := by
      ext i
      exact isEmptyElim i
    rw [h0, norm_zero] at hSeed
    exact zero_ne_one hSeed
  have hKs : 0 < Ks := Fin.pos (σ ⟨0, hM⟩)
  set D := clipData D₀ η hη with hDdef
  revert hLo Lo
  set K := fullDegree s η T g cq ε with hKdef
  intro Lo hLo
  let J := GeneralSourceODE.columnLoader Lo seed ((Sum.inr false, false) : FIota K M)
  have hJ : ∀ x a, IsUnitary (J x a) := fun x a => GeneralSourceODE.loadUnitary_unitary _ _
  set g' := fullAmp s η T g cq with hg'def
  have hs : 0 < s := D₀.slots_pos
  have hz : 0 < zParam s η T := zParam_pos hs hη hT
  have hDscale : D.scale = η := rfl
  have hzD : (s : ℝ) * D.scale * T = zParam s η T := by rw [hDscale]; rfl
  have hg1 : 1 ≤ g' := one_le_fullAmp hη.le hT.le hg hcq
  have hcqg : 1 ≤ cq * g := by nlinarith
  set p : MultiOracleCircuit.Program (matrixOracle (OmegaG (FLab K M m) K) D₀) :=
    fProgram hM hKs σ D K t v with hpdef
  set E := gEncoding hKs D K (FLab K M m) with hEdef
  have hE : E† ∘L E = 1 := gEncoding_isometry hKs D K
  set c := fTable D t T K M with hcdef
  have hcmass : ODECoherentLCU.coefficientMass c = 2 * Real.exp (zParam s η T) := by
    rw [hcdef, fTable_mass hmesh D K, hzD]
  have hc : 0 < ODECoherentLCU.coefficientMass c := by rw [hcmass]; positivity
  have hpos : 0 < ODECoherentLCU.coefficientMass (seedCoefficients (N := m) c) := by
    rw [GeneralSourceODE.Compiled.seedCoefficients_mass]; exact hc
  have hSeedU := ODECompiledSource.seed_unit E (seedCoefficients c) hE hpos seed hSeed
  have hOut := ODECompiledSource.output_isometry E (seedCoefficients c) hE hpos
  have hO : ∀ l x, IsUnitary (matrixOracle (OmegaG (FLab K M m) K) D₀ l x) :=
    matrixOracle_unitary (OmegaG (FLab K M m) K) D₀
  let ω₀ : OmegaG (FLab K M m) K := ((none, (Sum.inr false, false)), fun _ => false)
  let a0 : GeneralSourceODE.Native.SourceBasis (FIota K M) n m := ((none, (Sum.inr false, false)), i₀)
  refine ⟨compiledTrials (GeneralSourceODE.Native.sourceLayout (ι := FIota K M) (n := n) m)
      (matrixLayout (n := n) (Z := Z) (Ks := Ks) (OmegaG (FLab K M m) K)) p
      (sourceFamilyL (ι := FIota K M) Pw Lo (phases ω)) a0 (matrixClean hKs D₀ ω₀) E hE c seed
      hSeedU hOut,
    ODECoordinateNativeControl.input
      (GeneralSourceODE.Native.sourceLayout (ι := FIota K M) (n := n) m)
      (matrixLayout (n := n) (Z := Z) (Ks := Ks) (OmegaG (FLab K M m) K)) a0
      (matrixClean hKs D₀ ω₀) (ODECompiledSource.seed E (seedCoefficients c) seed),
    ODECoordinateNativeControl.input
      (GeneralSourceODE.Native.sourceLayout (ι := FIota K M) (n := n) m)
      (matrixLayout (n := n) (Z := Z) (Ks := Ks) (OmegaG (FLab K M m) K)) a0
      (matrixClean hKs D₀ ω₀) ∘L ODECompiledSource.output E (seedCoefficients c),
    ODECoordinateNativeControl.compile
      (GeneralSourceODE.Native.sourceLayout (ι := FIota K M) (n := n) m)
      (matrixLayout (n := n) (Z := Z) (Ks := Ks) (OmegaG (FLab K M m) K))
      (matrixOracle (OmegaG (FLab K M m) K) D₀)
      (sourceFamilyL (ι := FIota K M) Pw Lo (phases ω)) a0 (matrixClean hKs D₀ ω₀)
      (GeneralSourceODE.Compiled.program p (sourceFamilyL (ι := FIota K M) Pw Lo (phases ω))
        E hE),
    SubspaceOracle.lift (ODECoordinateNativeControl.input
      (GeneralSourceODE.Native.sourceLayout (ι := FIota K M) (n := n) m)
      (matrixLayout (n := n) (Z := Z) (Ks := Ks) (OmegaG (FLab K M m) K)) a0
      (matrixClean hKs D₀ ω₀)) (-1),
    SubspaceOracle.lift (ODECoordinateNativeControl.input
      (GeneralSourceODE.Native.sourceLayout (ι := FIota K M) (n := n) m)
      (matrixLayout (n := n) (Z := Z) (Ks := Ks) (OmegaG (FLab K M m) K)) a0
      (matrixClean hKs D₀ ω₀))
      (PhaseSubspaceGates.phase (ODEGroverRay.projector
        (ODECompiledSource.seed E (seedCoefficients c) seed)) (-1)),
    SubspaceOracle.lift (ODECoordinateNativeControl.input
      (GeneralSourceODE.Native.sourceLayout (ι := FIota K M) (n := n) m)
      (matrixLayout (n := n) (Z := Z) (Ks := Ks) (OmegaG (FLab K M m) K)) a0
      (matrixClean hKs D₀ ω₀))
      (PhaseSubspaceGates.phase (ODEHeraldedSuccess.successProjector
        (ODECompiledSource.output E (seedCoefficients c))) (-1)),
    compiledTrials_shape
      (GeneralSourceODE.Native.sourceLayout (ι := FIota K M) (n := n) m)
      (matrixLayout (n := n) (Z := Z) (Ks := Ks) (OmegaG (FLab K M m) K)) p
      (sourceFamilyL (ι := FIota K M) Pw Lo (phases ω)) a0 (matrixClean hKs D₀ ω₀) E hE c seed
      hSeedU hOut (ODESourceQueryBudget.matrixWeight (fun _ => 1)),
    fun b => compiledTrials_shape
      (GeneralSourceODE.Native.sourceLayout (ι := FIota K M) (n := n) m)
      (matrixLayout (n := n) (Z := Z) (Ks := Ks) (OmegaG (FLab K M m) K)) p
      (sourceFamilyL (ι := FIota K M) Pw Lo (phases ω)) a0 (matrixClean hKs D₀ ω₀) E hE c seed
      hSeedU hOut (ODESourceQueryBudget.sourceWeight b),
    ?_, ?_, ?_, ?_⟩
  · exact ((ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).mpr
      (ODECoordinateNativeControl.input_isometry
        (GeneralSourceODE.Native.sourceLayout (ι := FIota K M) (n := n) m)
        (matrixLayout (n := n) (Z := Z) (Ks := Ks) (OmegaG (FLab K M m) K)) a0
        (matrixClean hKs D₀ ω₀)) _).trans hSeedU
  · exact NativeSparseAttenuation.isometry_comp
      (ODECompiledSource.output E (seedCoefficients c))
      (ODECoordinateNativeControl.input
        (GeneralSourceODE.Native.sourceLayout (ι := FIota K M) (n := n) m)
        (matrixLayout (n := n) (Z := Z) (Ks := Ks) (OmegaG (FLab K M m) K)) a0
        (matrixClean hKs D₀ ω₀)) hOut
      (ODECoordinateNativeControl.input_isometry
        (GeneralSourceODE.Native.sourceLayout (ι := FIota K M) (n := n) m)
        (matrixLayout (n := n) (Z := Z) (Ks := Ks) (OmegaG (FLab K M m) K)) a0
        (matrixClean hKs D₀ ω₀))
  · intro j x
    exact MultiOracleCircuit.Program.eval_unitary _
      (ODECoordinateNativeControl.physicalOracle_unitary _ _ _ _ hO
        (sourceFamilyL_unitary hPw hLo (phases_norm ω))) x
  rintro x y ⟨G, b, sol, bv, U, ζ, hG, hGint, hmild, hU, hW, hCol0, hColb, hmassB, hsrc, hsolT,
    hBg, hbudget, rfl⟩
  -- The clean columns of `J` are those of `Lo`.
  have hcolJ : ∀ (a : Option (Fin m)) (u : EuclideanSpace ℂ n), u ≠ 0 →
      (∀ τ : FIota K M, Lo x (PiLp.single 2 (a, τ) seed) =
        PiLp.single 2 (a, τ) (ODEStateNormalization.unitDirection u)) →
      J x a seed = ODEStateNormalization.unitDirection u := by
    intro a u hu h
    change GeneralSourceODE.loadUnitary seed
      ((Lo x (PiLp.single 2 (a, ((Sum.inr false, false) : FIota K M)) seed))
        (a, ((Sum.inr false, false) : FIota K M))) seed = _
    rw [h _, PiLp.single_eq_same]
    exact GeneralSourceODE.loadUnitary_apply seed _ hSeed
      (ODEStateNormalization.unitDirection_norm u hu)
  have hJ0 : sol 0 ≠ 0 → J x none seed = ODEStateNormalization.unitDirection (sol 0) :=
    fun h0 => hcolJ none (sol 0) h0 (hCol0 h0)
  have hJb : ∀ i, ω i ≠ 0 → bv i ≠ 0 → J x (some i) seed =
      ODEStateNormalization.unitDirection (bv i) :=
    fun i hω hb => hcolJ (some i) (bv i) hb (hColb i hω hb)
  -- `Lo` and the label-controlled `J` agree on the seed branch state after `P_w`.
  have hagree : Lo x (GeneralSourceODE.Weights.act (Pw x)
      (ODEJointLCU.coefficientInput (seedCoefficients c) seed)) =
      GeneralSourceODE.Weights.loader (J x) (GeneralSourceODE.Weights.act (Pw x)
        (ODEJointLCU.coefficientInput (seedCoefficients c) seed)) := by
    rw [GeneralSourceODE.Weights.act_seedInput]
    apply GeneralSourceODE.Weights.clean_congr
    intro bb hbb
    rw [GeneralSourceODE.Weights.loader_single]
    have hamp : GeneralSourceODE.Weights.amp (Pw x) bb.1 none ≠ 0 := fun h => hbb (by simp [h])
    rw [hW bb.1] at hamp
    have hz' : sources (sol 0) bv ω bb.1 ≠ 0 := by
      intro h0
      apply hamp
      simp [ODESourceBranches.probability, h0]
    rcases bb with ⟨a, τ⟩
    cases a with
    | none =>
        have h0 : sol 0 ≠ 0 := hz'
        dsimp only
        rw [hCol0 h0 τ, hJ0 h0]
    | some i =>
        have h0 : ω i • bv i ≠ 0 := hz'
        obtain ⟨hω, hb⟩ := smul_ne_zero_iff.mp h0
        dsimp only
        rw [hColb i hω hb τ, hJb i hω hb]
  set z := sources (sol 0) bv ω with hzdef
  set B := meshScale sol b t with hBdef
  have hB : 0 < B := meshScale_pos_of_valid hmesh G hG U hU b sol hmild hT.le v hv bv ω cq ζ
    hmassB hsrc hsolT
  set Ecell := cellError σ D x t G with hEcell
  have hE0 : 0 ≤ Ecell := cellError_nonneg σ D x hmesh G
  have hexpE : 0 ≤ Real.exp Ecell - 1 := by linarith [Real.one_le_exp hE0]
  -- the error of the assembled quadrature
  have herr0 := dysonTarget_error hmesh hT.le σ D x G hG hGint U hU b sol hmild v hv bv ω ζ hsrc K
  rw [hzD] at herr0
  have hKtail : expTail (zParam s η T) K ≤ ε / (2000 * (cq * g)) :=
    expTail_truncDegree_le _ _ ε hz hcqg hε hε1
  have hKtail0 : 0 ≤ expTail (zParam s η T) K := expTail_nonneg _ hz.le K
  have hζB : ζ * B + ODESourceBranches.mass z * ((Real.exp Ecell - 1) + expTail (zParam s η T) K) ≤
      ε * B / (1000 * g) := by
    have hBq : ODESourceBranches.mass z * ((Real.exp Ecell - 1) + expTail (zParam s η T) K) ≤
        cq * B * ((Real.exp Ecell - 1) + expTail (zParam s η T) K) :=
      mul_le_mul_of_nonneg_right hmassB (by linarith)
    have hg0 : 0 < g := by linarith
    have htail : cq * B * expTail (zParam s η T) K ≤ ε * B / (2000 * g) := by
      have h := mul_le_mul_of_nonneg_left hKtail (by positivity : (0 : ℝ) ≤ cq * B)
      calc cq * B * expTail (zParam s η T) K ≤ cq * B * (ε / (2000 * (cq * g))) := h
        _ = ε * B / (2000 * g) := by field_simp
    have hbud : ζ * B + cq * B * (Real.exp Ecell - 1) ≤ ε * B / (2000 * g) := by
      have h := mul_le_mul_of_nonneg_right hbudget hB.le
      calc ζ * B + cq * B * (Real.exp Ecell - 1) = (ζ + cq * (Real.exp Ecell - 1)) * B := by ring
        _ ≤ ε / (2000 * g) * B := h
        _ = ε * B / (2000 * g) := by ring
    calc ζ * B + ODESourceBranches.mass z * ((Real.exp Ecell - 1) + expTail (zParam s η T) K)
        ≤ ζ * B + cq * B * ((Real.exp Ecell - 1) + expTail (zParam s η T) K) := by linarith
      _ = (ζ * B + cq * B * (Real.exp Ecell - 1)) + cq * B * expTail (zParam s η T) K := by ring
      _ ≤ ε * B / (2000 * g) + ε * B / (2000 * g) := add_le_add hbud htail
      _ = ε * B / (1000 * g) := by ring
  have herr : ‖dysonTarget σ D x t K v (sol 0) bv ω - sol T‖ ≤ ε * B / (1000 * g) :=
    herr0.trans hζB
  -- positivity of the source mass
  have hy := dysonTarget_norm_le hmesh σ D x K v (sol 0) bv ω
  rw [hzD] at hy
  have hg0 : 0 < g := by linarith
  have hsolT0 : 0 < ‖sol T‖ := norm_pos_iff.mpr hsolT
  have hBsol : ε * B / (1000 * g) ≤ ‖sol T‖ / 1000 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hyne : 0 < ‖dysonTarget σ D x t K v (sol 0) bv ω‖ := by
    have := norm_sub_norm_le (sol T) (dysonTarget σ D x t K v (sol 0) bv ω)
    rw [norm_sub_rev] at this
    linarith
  have hzpos : 0 < ODESourceBranches.mass z := by
    have h1 : 0 < ODESourceBranches.mass z * Real.exp (zParam s η T) := lt_of_lt_of_le hyne hy
    exact pos_of_mul_pos_left h1 (Real.exp_pos _).le
  have hm : 0 < ODESourceBranches.mass z * Real.exp (zParam s η T) := by positivity
  obtain ⟨h1, h2, h3⟩ := herald_window (dysonTarget σ D x t K v (sol 0) bv ω) (sol T)
    (ODESourceBranches.mass z * Real.exp (zParam s η T)) B g ε hB hm hg hε hε1 hBg hy herr
  -- the decoded vector of the actual preparation
  have hprep := phased_prepares (J x) (sol 0) bv ω seed hJ0 hJb
  have hdec : ODEActualSourceError.decoded E z c (phased (J x) (phases ω)) (p.eval x) seed =
      ((2 * (ODESourceBranches.mass z * Real.exp (zParam s η T)) : ℝ) : ℂ)⁻¹ •
        dysonTarget σ D x t K v (sol 0) bv ω := by
    have h := fDecoded hmesh hM hKs σ D K v ω x (J x) z hzpos seed hprep (T := T)
    rw [hzD] at h
    rw [show (2 * (ODESourceBranches.mass z * Real.exp (zParam s η T)) : ℝ) =
      2 * Real.exp (zParam s η T) * ODESourceBranches.mass z by ring]
    exact h
  have hampLe : g * (ODESourceBranches.mass z * Real.exp (zParam s η T)) / B ≤ g' := by
    rw [div_le_iff₀ hB, hg'def, fullAmp]
    have := mul_le_mul_of_nonneg_right hmassB (Real.exp_pos (zParam s η T)).le
    nlinarith [Real.exp_pos (zParam s η T)]
  have hLower : 1 / (4 * g') ≤
      ‖ODEActualSourceError.decoded E z c (phased (J x) (phases ω)) (p.eval x) seed‖ := by
    rw [hdec]
    refine le_trans ?_ h1
    apply one_div_le_one_div_of_le
    · have : 0 < g * (ODESourceBranches.mass z * Real.exp (zParam s η T)) / B := by positivity
      linarith
    · linarith
  have hUpper : ‖ODEActualSourceError.decoded E z c (phased (J x) (phases ω)) (p.eval x) seed‖ ≤
      1 / 2 := by rw [hdec]; exact h2
  have hDir : ‖ODEStateNormalization.unitDirection
      (ODEActualSourceError.decoded E z c (phased (J x) (phases ω)) (p.eval x) seed) -
        ODEStateNormalization.unitDirection (sol T)‖ ≤ ε / 500 := by rw [hdec]; exact h3
  have hq : (p.count : ℝ) ≤ 10616832 * ImprovedODEQueryBudget.queryShape (s : ℝ) 0 (fullShape K) := by
    have hcount : p.count = 18 * K := fProgram_count hM hKs σ D K t v
    rw [hcount, queryShape_zero]
    unfold fullShape
    push_cast
    apply le_of_eq
    ring
  exact herald_certificate_columns p hO Pw hPw J hJ Lo hLo (phases ω) (phases_norm ω) E hE z c hc
    seed (sol T) hSeed (s : ℝ) 0 (fullShape K) g' ε hg1 hε.le hsolT x hzpos hW hLower hUpper hDir
    hq (GeneralSourceODE.Native.sourceLayout (ι := FIota K M) (n := n) m)
    (matrixLayout (n := n) (Z := Z) (Ks := Ks) (OmegaG (FLab K M m) K)) a0 (matrixClean hKs D₀ ω₀)
    (matrixImage hKs D₀ ω₀) (matrix_valid hKs D₀ ω₀) hSeedU hOut hagree

/-- **Lemma `odel:lem:dyson` on the full time-dependent class, with a loader specified on its
clean columns only (item D1, exact case).** For every public specification there are one public
trial family, unit seed and isometric output over `fullOracleL D₀` (native calls of the original
access, the counted interfaces with the supplied `P_w` and a unitary loader `Lo` on the whole branch
register) such that every valid instance of `FullValidColumns` carries the released complete
certificate of `full_dyson`: cutoff `chosenIterations g'`, `g' = c_q ḡ e^z`, shape `K/589824`
(`18 K` native calls per preparation) and accuracy `ε`. -/
theorem full_dyson_columns (D₀ : Data (X × Fin Ks) n Z s) (hM : 0 < M) (σ : Fin M → Fin Ks)
    (t : ℕ → ℝ) (T η g cq ε : ℝ) (hmesh : IsMesh t M T) (hT : 0 < T) (hη : 0 < η)
    (hg : 1 ≤ g) (hcq : 1 ≤ cq) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (v : Fin m → ℝ) (hv : ∀ i, v i ∈ Icc 0 T) (ω : Fin m → ℂ)
    (Pw : X → GeneralSourceODE.Weights.LabelOp (Option (Fin m))) (hPw : ∀ x, IsUnitary (Pw x))
    (Lo : X → GeneralSourceODE.Native.SourceSpace (FIota (fullDegree s η T g cq ε) M) n m →L[ℂ]
      GeneralSourceODE.Native.SourceSpace (FIota (fullDegree s η T g cq ε) M) n m)
    (hLo : ∀ x, IsUnitary (Lo x)) (seed : EuclideanSpace ℂ n) (hSeed : ‖seed‖ = 1) :
    ∃ (q : ℕ → MultiOracleCircuit.Program
        (fullOracleL D₀ (fullDegree s η T g cq ε) M m Pw Lo ω))
      (ψ : FSpace Ks n Z (fullDegree s η T g cq ε) M m)
      (F : EuclideanSpace ℂ n →L[ℂ] FSpace Ks n Z (fullDegree s η T g cq ε) M m),
      (∀ j x, IsUnitary ((q j).eval x)) ∧
      ∀ x y, FullValidColumns D₀ σ t T η g cq ε hη v ω Pw Lo seed x y →
        ODECompleteTrial.Certificate q
          (ODEGroverAverage.chosenIterations (fullAmp s η T g cq)) ψ F x y
          (s : ℝ) 0 (fullShape (fullDegree s η T g cq ε)) (fullAmp s η T g cq) ε := by
  obtain ⟨q, ψ, F, -, -, -, -, -, -, -, -, hU, hC⟩ := full_dyson_shape_columns D₀ hM σ t T η g cq ε
    hmesh hT hη hg hcq hε hε1 v hv ω Pw hPw Lo hLo seed hSeed
  exact ⟨q, ψ, F, hU, hC⟩

end

end DysonFullClass
