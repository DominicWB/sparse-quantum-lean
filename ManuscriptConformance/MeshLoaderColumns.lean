import ManuscriptConformance.SourceLoaderColumns
import GeneralSourceExtensions.Mesh.Actual
import GeneralSourceExtensions.Mesh.Integral

/-!
# The mesh general-source ODE solver with a loader specified on its clean columns (item D1)

`GeneralSourceExtensions.Mesh.mesh_solver` (`ode:thm:time` with the source interface on a public
mesh with breakpoints, the clock on `N` slots, interval-integrable generator pieces and the
integrated sample error) takes the loading oracle as a label-controlled family
`U_load = ∑_a |a⟩⟨a| ⊗ J_a`, like the uniform-mesh solver. As `SourceLoaderColumns` does for the
uniform mesh, this module replaces it by any unitary `Lo` on the whole branch register, specified
only on the clean columns `|a, τ⟩|seed⟩` of the labels with nonzero source vectors.

* `MeshNative.physicalOracleS`, `publicTrialsS`, `publicTrials_eq_publicTrialsS`,
  `publicTrialsS_seed_congr`, `publicTrialsS_matrix_cost`, `publicTrialsS_source_cost`: the
  compiled trials on `N` slots depend on the counted interfaces only through the seed column, with
  the same counts (from `GeneralSourceODE.Compiled.program_seed_congr`, `amplified_seed_congr`).
* `MeshOracles.actualOracleL`, `actualOracle_eq_actualOracleL`, `actualOracleL_unitary`,
  `implementationL` (with `implementationL_eval` and the count lemmas), `actualTrialsL`: the actual
  oracles `P_w`, `Lo`, `P_w†` on `N` slots.
* `MeshOracles.columns_certificate`: the complete certificate of a label-controlled family
  transfers to the protocol over `P_w`, `Lo`, `P_w†` when `Lo` and `loader J` agree on the seed
  branch state after `P_w`.
* `Mesh.mesh_propagated_solver_public` (`MeshPublicOutcome`): the released proof of
  `Mesh.mesh_propagated_solver` with the public trial family `MeshNative.publicTrials` named in
  the conclusion.
* `Mesh.mesh_solver_columns` (`MeshOutcomeColumns`): the guarantee of `Mesh.mesh_solver` (success
  at least `2/3`, conditional trace distance at most `ε`, the same matrix-query bound and at most
  `40 g'` calls of each of `P_w`, `Lo` and `P_w†`) for every unitary loader with the stated clean
  columns.
* `Mesh.mesh_solver_integral_columns` (`MeshIntegralOutcomeColumns`): the same with continuous
  pieces and the certificate on the propagated vector integral, as `Mesh.mesh_solver_integral`.

Scope: the exact case of item D1 for the mesh endpoints with exact preparations. Approximate
columns, the approximate-preparation forms and the conformance theorems of `ode:thm:time` (built
on the approximate-preparation solver) keep the label-controlled loader.
-/

set_option autoImplicit false

namespace SparseHamiltonian.GeneralSourceExtensions.MeshNative

noncomputable section
open ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding
open GeneralSourceODE
open GeneralSourceODE.Native (Label SourceBasis SourceSpace sourceLayout sourceBasis dummy
  sourceFamily)
open scoped InnerProduct BigOperators
set_option maxRecDepth 4096
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 2000000

variable {ι X n Z : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z] [DecidableEq Z]
  {s M m : ℕ}

/-- The primitive oracles with the counted interfaces `S`. -/
abbrev physicalOracleS (D : Data (X × Fin M) n Z s) (m N d : ℕ)
    (S : Bool → X → SourceSpace ι n m →L[ℂ] SourceSpace ι n m) :
    Query ⊕ Bool → X → PhysicalSpace ι n Z m M N d →L[ℂ] PhysicalSpace ι n Z m M N d :=
  ODECoordinateNativeControl.physicalOracle
    (A := SourceBasis ι n m) (B := MatrixBasis ι n Z m M N d)
    (H := SourceSpace ι n m) (K := MatrixSpace ι n Z m M N d) (X := X) (L := Query)
    (sourceLayout (ι := ι) (n := n) m)
    (matrixLayout (ι := ι) (n := n) (Z := Z) m M N d)
    (matrixOracle (ι := ι) D m N d) S

/-- The compiled public trial family of `publicTrials`, for any counted interfaces `S`. -/
def publicTrialsS (D : Data (X × Fin M) n Z s) (hM : 0 < M) (i0 : ι) (m N d : ℕ)
    (p : MultiOracleCircuit.Program (matrixOracle (ι := ι) D m N d))
    (S : Bool → X → SourceSpace ι n m →L[ℂ] SourceSpace ι n m)
    (E : SourceSpace ι n m →L[ℂ] MatrixSpace ι n Z m M N d) (hE : E† ∘L E = 1)
    (c : ι → ℂ) (seed : EuclideanSpace ℂ n)
    (hSeed : ‖ODECompiledSource.seed E (Compiled.seedCoefficients c) seed‖ = 1)
    (hOutput : (ODECompiledSource.output E (Compiled.seedCoefficients c))† ∘L
      ODECompiledSource.output E (Compiled.seedCoefficients c) = 1) :
    ℕ → MultiOracleCircuit.Program (physicalOracleS (ι := ι) D m N d S) :=
  fun j => ODECoordinateNativeControl.compile
    (A := SourceBasis ι n m) (B := MatrixBasis ι n Z m M N d)
    (H := SourceSpace ι n m) (K := MatrixSpace ι n Z m M N d) (X := X) (L := Query)
    (sourceLayout (ι := ι) (n := n) m)
    (matrixLayout (ι := ι) (n := n) (Z := Z) m M N d)
    (matrixOracle (ι := ι) D m N d) S
    (sourceBasis D i0 m) (matrixBasis D hM i0 m N d)
    (ODECountedAmplification.program (Compiled.program p S E hE)
      (ODECompiledSource.output E (Compiled.seedCoefficients c)) hOutput
      (ODECompiledSource.seed E (Compiled.seedCoefficients c) seed) hSeed j)

/-- The released public trial family is the case of the label-controlled interfaces. -/
theorem publicTrials_eq_publicTrialsS (D : Data (X × Fin M) n Z s) (hM : 0 < M) (i0 : ι)
    (m N d : ℕ) (p : MultiOracleCircuit.Program (matrixOracle (ι := ι) D m N d))
    (Pw : X → Weights.LabelOp (Option (Fin m)))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (φ : Option (Fin m) → ℂ)
    (E : SourceSpace ι n m →L[ℂ] MatrixSpace ι n Z m M N d) (hE : E† ∘L E = 1)
    (c : ι → ℂ) (seed : EuclideanSpace ℂ n)
    (hSeed : ‖ODECompiledSource.seed E (Compiled.seedCoefficients c) seed‖ = 1)
    (hOutput : (ODECompiledSource.output E (Compiled.seedCoefficients c))† ∘L
      ODECompiledSource.output E (Compiled.seedCoefficients c) = 1) :
    publicTrials D hM i0 m N d p Pw J φ E hE c seed hSeed hOutput =
      publicTrialsS D hM i0 m N d p (sourceFamily Pw J φ) E hE c seed hSeed hOutput := rfl

/-- **The compiled trials depend on the counted interfaces only through the seed column.** -/
theorem publicTrialsS_seed_congr (D : Data (X × Fin M) n Z s) (hM : 0 < M) (i0 : ι)
    (m N d : ℕ) (p : MultiOracleCircuit.Program (matrixOracle (ι := ι) D m N d))
    (S S' : Bool → X → SourceSpace ι n m →L[ℂ] SourceSpace ι n m)
    (hS : ∀ b x, IsUnitary (S b x)) (hS' : ∀ b x, IsUnitary (S' b x))
    (E : SourceSpace ι n m →L[ℂ] MatrixSpace ι n Z m M N d) (hE : E† ∘L E = 1)
    (c : ι → ℂ) (seed : EuclideanSpace ℂ n)
    (hSeed : ‖ODECompiledSource.seed E (Compiled.seedCoefficients c) seed‖ = 1)
    (hOutput : (ODECompiledSource.output E (Compiled.seedCoefficients c))† ∘L
      ODECompiledSource.output E (Compiled.seedCoefficients c) = 1) (x : X)
    (htrue : S true x = S' true x)
    (hfalse : S false x (ODEJointLCU.coefficientInput (Compiled.seedCoefficients c) seed) =
      S' false x (ODEJointLCU.coefficientInput (Compiled.seedCoefficients c) seed)) (j : ℕ) :
    (publicTrialsS D hM i0 m N d p S E hE c seed hSeed hOutput j).eval x
        (input D hM i0 m N d (ODECompiledSource.seed E (Compiled.seedCoefficients c) seed)) =
      (publicTrialsS D hM i0 m N d p S' E hE c seed hSeed hOutput j).eval x
        (input D hM i0 m N d (ODECompiledSource.seed E (Compiled.seedCoefficients c) seed)) := by
  have key : ∀ (T : Bool → X → SourceSpace ι n m →L[ℂ] SourceSpace ι n m)
      (_hT : ∀ b x, IsUnitary (T b x)),
      (publicTrialsS D hM i0 m N d p T E hE c seed hSeed hOutput j).eval x ∘L input D hM i0 m N d =
        input D hM i0 m N d ∘L
          (ODECountedAmplification.program (Compiled.program p T E hE)
            (ODECompiledSource.output E (Compiled.seedCoefficients c)) hOutput
            (ODECompiledSource.seed E (Compiled.seedCoefficients c) seed) hSeed j).eval x := by
    intro T hT
    exact ODECoordinateNativeControl.compile_eval
      (A := SourceBasis ι n m) (B := MatrixBasis ι n Z m M N d)
      (H := SourceSpace ι n m) (K := MatrixSpace ι n Z m M N d) (X := X) (L := Query)
      (sourceLayout (ι := ι) (n := n) m)
      (matrixLayout (ι := ι) (n := n) (Z := Z) m M N d)
      (matrixOracle (ι := ι) D m N d) T (matrixOracle_unitary (ι := ι) D m N d) hT
      (sourceBasis D i0 m) (matrixBasis D hM i0 m N d) (matrixImage D hM i0 m N d)
      (matrix_valid D hM i0 m N d)
      (ODECountedAmplification.program (Compiled.program p T E hE)
        (ODECompiledSource.output E (Compiled.seedCoefficients c)) hOutput
        (ODECompiledSource.seed E (Compiled.seedCoefficients c) seed) hSeed j) x
  have key' : ∀ (T : Bool → X → SourceSpace ι n m →L[ℂ] SourceSpace ι n m)
      (_hT : ∀ b x, IsUnitary (T b x)),
      (publicTrialsS D hM i0 m N d p T E hE c seed hSeed hOutput j).eval x
          (input D hM i0 m N d (ODECompiledSource.seed E (Compiled.seedCoefficients c) seed)) =
        input D hM i0 m N d
          ((ODECountedAmplification.program (Compiled.program p T E hE)
            (ODECompiledSource.output E (Compiled.seedCoefficients c)) hOutput
            (ODECompiledSource.seed E (Compiled.seedCoefficients c) seed) hSeed j).eval x
            (ODECompiledSource.seed E (Compiled.seedCoefficients c) seed)) := by
    intro T hT
    rw [← comp_apply, key T hT, comp_apply]
  rw [key' S hS, key' S' hS',
    Compiled.amplified_seed_congr p (matrixOracle_unitary (ι := ι) D m N d) S S' hS hS' E hE _
      hOutput _ hSeed x
      (Compiled.program_seed_congr p S S' E hE _ seed x htrue hfalse) j]

/-- Matrix counts of the compiled trials, for any counted interfaces. -/
theorem publicTrialsS_matrix_cost (D : Data (X × Fin M) n Z s) (hM : 0 < M) (i0 : ι)
    (m N d : ℕ) (p : MultiOracleCircuit.Program (matrixOracle (ι := ι) D m N d))
    (S : Bool → X → SourceSpace ι n m →L[ℂ] SourceSpace ι n m)
    (E : SourceSpace ι n m →L[ℂ] MatrixSpace ι n Z m M N d) (hE : E† ∘L E = 1)
    (c : ι → ℂ) (seed : EuclideanSpace ℂ n)
    (hSeed : ‖ODECompiledSource.seed E (Compiled.seedCoefficients c) seed‖ = 1)
    (hOutput : (ODECompiledSource.output E (Compiled.seedCoefficients c))† ∘L
      ODECompiledSource.output E (Compiled.seedCoefficients c) = 1) (w : Query → ℕ) (j : ℕ) :
    (publicTrialsS D hM i0 m N d p S E hE c seed hSeed hOutput j).cost
        (ODESourceQueryBudget.matrixWeight w) = 3 * ((2 * j + 1) * p.cost w) := by
  unfold publicTrialsS
  rw [ODECoordinateNativeControl.compile_matrix_cost, ODECountedAmplification.cost_eq,
    Compiled.program_matrix_cost]

/-- Interface counts of the compiled trials, for any counted interfaces. -/
theorem publicTrialsS_source_cost (D : Data (X × Fin M) n Z s) (hM : 0 < M) (i0 : ι)
    (m N d : ℕ) (p : MultiOracleCircuit.Program (matrixOracle (ι := ι) D m N d))
    (S : Bool → X → SourceSpace ι n m →L[ℂ] SourceSpace ι n m)
    (E : SourceSpace ι n m →L[ℂ] MatrixSpace ι n Z m M N d) (hE : E† ∘L E = 1)
    (c : ι → ℂ) (seed : EuclideanSpace ℂ n)
    (hSeed : ‖ODECompiledSource.seed E (Compiled.seedCoefficients c) seed‖ = 1)
    (hOutput : (ODECompiledSource.output E (Compiled.seedCoefficients c))† ∘L
      ODECompiledSource.output E (Compiled.seedCoefficients c) = 1) (b : Bool) (j : ℕ) :
    (publicTrialsS D hM i0 m N d p S E hE c seed hSeed hOutput j).cost
        (ODESourceQueryBudget.sourceWeight b) = 2 * j + 1 := by
  unfold publicTrialsS
  rw [ODECoordinateNativeControl.compile_source_cost, ODECountedAmplification.cost_eq,
    Compiled.program_source_cost, mul_one]


end

end SparseHamiltonian.GeneralSourceExtensions.MeshNative

namespace SparseHamiltonian.GeneralSourceExtensions.MeshOracles

noncomputable section
open ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding
open GeneralSourceODE
open GeneralSourceODE.Oracles (sourcePhysical_mul matrixCalls calls sourceCalls)
open scoped InnerProduct BigOperators
set_option maxRecDepth 4096
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 2000000

variable {ι X n Z : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z] [DecidableEq Z]
  {s M m : ℕ}

/-- The actual primitive oracles with the loader `Lo`: the coherent sampled-time matrix calls,
and `P_w`, `Lo`, `P_w†`, each with its enable control. -/
def actualOracleL (D : Data (X × Fin M) n Z s) (m N d : ℕ)
    (Pw : X → Weights.LabelOp (Option (Fin m)))
    (Lo : X → Native.SourceSpace ι n m →L[ℂ] Native.SourceSpace ι n m) :
    Query ⊕ SourceCall → X →
      MeshNative.PhysicalSpace ι n Z m M N d →L[ℂ] MeshNative.PhysicalSpace ι n Z m M N d :=
  Sum.elim
    (fun l => NativeMaskedOracle.oracle (ι := Native.SourceBasis ι n m)
      (fun x => (MeshNative.matrixLayout (ι := ι) (n := n) (Z := Z) m M N d).conjStarAlgEquiv
        (MeshNative.matrixOracle (ι := ι) D m N d l x)))
    (fun k x => ODESectorTensor.sourcePhysical (B := MeshNative.MatrixBasis ι n Z m M N d)
      ((Native.sourceLayout (ι := ι) (n := n) m).conjStarAlgEquiv
        (Oracles.sourceOperationL Pw Lo k x)))

omit [DecidableEq ι] [DecidableEq Z] in
/-- The released actual oracles are those with the label-controlled loader. -/
theorem actualOracle_eq_actualOracleL (D : Data (X × Fin M) n Z s) (m N d : ℕ)
    (Pw : X → Weights.LabelOp (Option (Fin m)))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) :
    actualOracle (ι := ι) D m N d Pw J =
      actualOracleL D m N d Pw (fun x => Weights.loader (J x)) := by
  funext l x
  rcases l with l | k
  · rfl
  · cases k <;> rfl

omit [DecidableEq ι] [DecidableEq Z] in
theorem actualOracleL_unitary (D : Data (X × Fin M) n Z s) (m N d : ℕ)
    {Pw : X → Weights.LabelOp (Option (Fin m))} (hPw : ∀ x, IsUnitary (Pw x))
    {Lo : X → Native.SourceSpace ι n m →L[ℂ] Native.SourceSpace ι n m}
    (hLo : ∀ x, IsUnitary (Lo x)) :
    ∀ l x, IsUnitary (actualOracleL (ι := ι) D m N d Pw Lo l x) := by
  intro l x
  cases l with
  | inl l =>
      exact NativeMaskedOracle.oracle_unitary _
        (fun y => (MeshNative.matrixOracle_unitary (ι := ι) D m N d l y).transport
          (MeshNative.matrixLayout (ι := ι) (n := n) (Z := Z) m M N d)) x
  | inr k =>
      exact ODESectorTensor.sourcePhysical_unitary _
        ((Oracles.sourceOperationL_unitary hPw hLo k x).transport
          (Native.sourceLayout (ι := ι) (n := n) m))

/-- Each counted interface call as a program over the actual oracles with the loader `Lo`:
`P_w`, then `Lo`, then the public phases; and `P_w†`. -/
def implementationL (D : Data (X × Fin M) n Z s) (m N d : ℕ)
    (Pw : X → Weights.LabelOp (Option (Fin m)))
    (Lo : X → Native.SourceSpace ι n m →L[ℂ] Native.SourceSpace ι n m)
    (φ : Option (Fin m) → ℂ) (hφ : ∀ a, ‖φ a‖ = 1) :
    Query ⊕ Bool → MultiOracleCircuit.Program (actualOracleL (ι := ι) D m N d Pw Lo)
  | .inl l => .query (.inl l)
  | .inr false => .seq (.fixed (phaseGate m M N d φ) (phaseGate_unitary m M N d hφ))
      (.seq (.query (.inr .load)) (.query (.inr .weight)))
  | .inr true => .query (.inr .unweight)

/-- The implementations are exact. -/
theorem implementationL_eval (D : Data (X × Fin M) n Z s) (m N d : ℕ)
    (Pw : X → Weights.LabelOp (Option (Fin m)))
    (Lo : X → Native.SourceSpace ι n m →L[ℂ] Native.SourceSpace ι n m)
    (φ : Option (Fin m) → ℂ) (hφ : ∀ a, ‖φ a‖ = 1) (l : Query ⊕ Bool) (x : X) :
    (implementationL (ι := ι) D m N d Pw Lo φ hφ l).eval x =
      MeshNative.physicalOracleS (ι := ι) D m N d (Compiled.sourceFamilyL Pw Lo φ) l x := by
  rcases l with l | b
  · rfl
  · cases b with
    | true => rfl
    | false =>
        change phaseGate m M N d φ *
            (ODESectorTensor.sourcePhysical (B := MeshNative.MatrixBasis ι n Z m M N d)
              ((Native.sourceLayout (ι := ι) (n := n) m).conjStarAlgEquiv (Lo x)) *
            ODESectorTensor.sourcePhysical (B := MeshNative.MatrixBasis ι n Z m M N d)
              ((Native.sourceLayout (ι := ι) (n := n) m).conjStarAlgEquiv
                (Weights.act (Pw x)))) =
          ODESectorTensor.sourcePhysical (B := MeshNative.MatrixBasis ι n Z m M N d)
            ((Native.sourceLayout (ι := ι) (n := n) m).conjStarAlgEquiv
              (Compiled.prepL (Pw x) (Lo x) φ))
        rw [phaseGate, ← sourcePhysical_mul, ← sourcePhysical_mul, ← map_mul, ← map_mul]
        rfl

omit [DecidableEq ι] [DecidableEq Z] in
theorem implementationL_matrix (D : Data (X × Fin M) n Z s) (m N d : ℕ)
    (Pw : X → Weights.LabelOp (Option (Fin m)))
    (Lo : X → Native.SourceSpace ι n m →L[ℂ] Native.SourceSpace ι n m)
    (φ : Option (Fin m) → ℂ) (hφ : ∀ a, ‖φ a‖ = 1) (l : Query ⊕ Bool) :
    (implementationL (ι := ι) D m N d Pw Lo φ hφ l).cost matrixCalls =
      ODESourceQueryBudget.matrixWeight (fun _ => 1) l := by
  rcases l with l | b
  · rfl
  · cases b <;> rfl

omit [DecidableEq ι] [DecidableEq Z] in
theorem implementationL_weight (D : Data (X × Fin M) n Z s) (m N d : ℕ)
    (Pw : X → Weights.LabelOp (Option (Fin m)))
    (Lo : X → Native.SourceSpace ι n m →L[ℂ] Native.SourceSpace ι n m)
    (φ : Option (Fin m) → ℂ) (hφ : ∀ a, ‖φ a‖ = 1) (l : Query ⊕ Bool) :
    (implementationL (ι := ι) D m N d Pw Lo φ hφ l).cost (calls .weight) =
      ODESourceQueryBudget.sourceWeight false l := by
  rcases l with l | b
  · rfl
  · cases b <;> rfl

omit [DecidableEq ι] [DecidableEq Z] in
theorem implementationL_load (D : Data (X × Fin M) n Z s) (m N d : ℕ)
    (Pw : X → Weights.LabelOp (Option (Fin m)))
    (Lo : X → Native.SourceSpace ι n m →L[ℂ] Native.SourceSpace ι n m)
    (φ : Option (Fin m) → ℂ) (hφ : ∀ a, ‖φ a‖ = 1) (l : Query ⊕ Bool) :
    (implementationL (ι := ι) D m N d Pw Lo φ hφ l).cost (calls .load) =
      ODESourceQueryBudget.sourceWeight false l := by
  rcases l with l | b
  · rfl
  · cases b <;> rfl

omit [DecidableEq ι] [DecidableEq Z] in
theorem implementationL_unweight (D : Data (X × Fin M) n Z s) (m N d : ℕ)
    (Pw : X → Weights.LabelOp (Option (Fin m)))
    (Lo : X → Native.SourceSpace ι n m →L[ℂ] Native.SourceSpace ι n m)
    (φ : Option (Fin m) → ℂ) (hφ : ∀ a, ‖φ a‖ = 1) (l : Query ⊕ Bool) :
    (implementationL (ι := ι) D m N d Pw Lo φ hφ l).cost (calls .unweight) =
      ODESourceQueryBudget.sourceWeight true l := by
  rcases l with l | b
  · rfl
  · cases b <;> rfl

omit [DecidableEq ι] [DecidableEq Z] in
theorem implementationL_source (D : Data (X × Fin M) n Z s) (m N d : ℕ)
    (Pw : X → Weights.LabelOp (Option (Fin m)))
    (Lo : X → Native.SourceSpace ι n m →L[ℂ] Native.SourceSpace ι n m)
    (φ : Option (Fin m) → ℂ) (hφ : ∀ a, ‖φ a‖ = 1) (l : Query ⊕ Bool) :
    (implementationL (ι := ι) D m N d Pw Lo φ hφ l).cost sourceCalls =
      2 * ODESourceQueryBudget.sourceWeight false l +
        ODESourceQueryBudget.sourceWeight true l := by
  rcases l with l | b
  · rfl
  · cases b <;> rfl

/-- The trial family over the actual oracles with the loader `Lo`. -/
def actualTrialsL (D : Data (X × Fin M) n Z s) (m N d : ℕ)
    (Pw : X → Weights.LabelOp (Option (Fin m)))
    (Lo : X → Native.SourceSpace ι n m →L[ℂ] Native.SourceSpace ι n m)
    (φ : Option (Fin m) → ℂ) (hφ : ∀ a, ‖φ a‖ = 1)
    (q : ℕ → MultiOracleCircuit.Program
      (MeshNative.physicalOracleS (ι := ι) D m N d (Compiled.sourceFamilyL Pw Lo φ))) :
    ℕ → MultiOracleCircuit.Program (actualOracleL (ι := ι) D m N d Pw Lo) :=
  fun j => (q j).substitute (implementationL D m N d Pw Lo φ hφ)


section Columns

variable {ι X n Z : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z] [DecidableEq Z]
  {s M m : ℕ}

/-- **The complete certificate transfers from a label-controlled loader to any loader with the
same value on the seed branch state after `P_w`.** If the public trial family with the
label-controlled interfaces `loader J` has the released complete certificate, then the
four-attempt protocol over the actual oracles `P_w`, `Lo`, `P_w†` has the complete certificate
`ActualCertificate`, for every unitary `Lo` with
`Lo (P_w ⊗ 1)|seed state⟩ = loader J (P_w ⊗ 1)|seed state⟩`. -/
theorem columns_certificate (D : Data (X × Fin M) n Z s) (hM : 0 < M) (i0 : ι) (m N d : ℕ)
    (p : MultiOracleCircuit.Program (MeshNative.matrixOracle (ι := ι) D m N d))
    (Pw : X → Weights.LabelOp (Option (Fin m))) (hPw : ∀ x, IsUnitary (Pw x))
    (Lo : X → Native.SourceSpace ι n m →L[ℂ] Native.SourceSpace ι n m)
    (hLo : ∀ x, IsUnitary (Lo x))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ : ∀ x a, IsUnitary (J x a)) (φ : Option (Fin m) → ℂ) (hφ : ∀ a, ‖φ a‖ = 1)
    (E : Native.SourceSpace ι n m →L[ℂ] MeshNative.MatrixSpace ι n Z m M N d) (hE : E† ∘L E = 1)
    (c : ι → ℂ) (seed : EuclideanSpace ℂ n)
    (hSeed : ‖ODECompiledSource.seed E (Compiled.seedCoefficients c) seed‖ = 1)
    (hOutput : (ODECompiledSource.output E (Compiled.seedCoefficients c))† ∘L
      ODECompiledSource.output E (Compiled.seedCoefficients c) = 1)
    (x : X) {Mc : ℕ} (hMc : 0 < Mc) {target : EuclideanSpace ℂ n} {s' Θ ell g ε : ℝ}
    (hψ : ‖MeshNative.input D hM i0 m N d
      (ODECompiledSource.seed E (Compiled.seedCoefficients c) seed)‖ = 1)
    (hF : (MeshNative.input D hM i0 m N d ∘L
        ODECompiledSource.output E (Compiled.seedCoefficients c))† ∘L
      (MeshNative.input D hM i0 m N d ∘L
        ODECompiledSource.output E (Compiled.seedCoefficients c)) = 1)
    (hCert : ODECompleteTrial.Certificate
      (MeshNative.publicTrials D hM i0 m N d p Pw J φ E hE c seed hSeed hOutput) Mc
      (MeshNative.input D hM i0 m N d (ODECompiledSource.seed E (Compiled.seedCoefficients c) seed))
      (MeshNative.input D hM i0 m N d ∘L ODECompiledSource.output E (Compiled.seedCoefficients c))
      x target s' Θ ell g ε)
    (hagree : Lo x (Weights.act (Pw x)
        (ODEJointLCU.coefficientInput (Compiled.seedCoefficients c) seed)) =
      Weights.loader (J x) (Weights.act (Pw x)
        (ODEJointLCU.coefficientInput (Compiled.seedCoefficients c) seed))) :
    Oracles.ActualCertificate (ODERepeatProtocol.fourTrials (actualTrialsL D m N d Pw Lo φ hφ
        (MeshNative.publicTrialsS D hM i0 m N d p (Compiled.sourceFamilyL Pw Lo φ) E hE c seed hSeed
          hOutput)) Mc hMc _ hψ _ hF) x target s' Θ ell g ε := by
  rw [MeshNative.publicTrials_eq_publicTrialsS] at hCert
  have hfalse : Compiled.sourceFamilyL (ι := ι) Pw Lo φ false x
      (ODEJointLCU.coefficientInput (Compiled.seedCoefficients c) seed) =
      Native.sourceFamily (ι := ι) Pw J φ false x
        (ODEJointLCU.coefficientInput (Compiled.seedCoefficients c) seed) := by
    rw [Compiled.sourceFamilyL_false, Native.sourceFamily, Compiled.sourceFamily_false]
    unfold Compiled.prepL Compiled.prep
    simp only [comp_apply]
    rw [hagree]
  have hEval : ∀ j, (actualTrialsL D m N d Pw Lo φ hφ
      (MeshNative.publicTrialsS D hM i0 m N d p (Compiled.sourceFamilyL Pw Lo φ) E hE c seed hSeed
        hOutput) j).eval x =
      (MeshNative.publicTrialsS D hM i0 m N d p (Compiled.sourceFamilyL Pw Lo φ) E hE c seed hSeed
        hOutput j).eval x := fun j =>
    MultiOracleCircuit.Program.eval_substitute _ _ (implementationL_eval D m N d Pw Lo φ hφ) x
  apply Oracles.actual_certificate_seed hCert _ hMc hψ hF
  · intro j
    rw [hEval j]
    have h := MeshNative.publicTrialsS_seed_congr D hM i0 m N d p (Compiled.sourceFamilyL Pw Lo φ)
      (Native.sourceFamily Pw J φ)
      (Compiled.sourceFamilyL_unitary hPw hLo hφ) (Compiled.sourceFamily_unitary hPw hJ hφ)
      E hE c seed hSeed hOutput x
      ((Compiled.sourceFamilyL_true Pw Lo φ x).trans (Compiled.sourceFamily_true Pw J φ x).symm)
      hfalse j
    convert h using 2
  · intro j
    simp only [actualTrialsL, MultiOracleCircuit.Program.cost_substitute, implementationL_matrix,
      MeshNative.publicTrialsS_matrix_cost]
  · intro j
    simp only [actualTrialsL, MultiOracleCircuit.Program.cost_substitute, implementationL_weight,
      MeshNative.publicTrialsS_source_cost]
  · intro j
    simp only [actualTrialsL, MultiOracleCircuit.Program.cost_substitute, implementationL_load,
      MeshNative.publicTrialsS_source_cost]
  · intro j
    simp only [actualTrialsL, MultiOracleCircuit.Program.cost_substitute,
      implementationL_unweight, MeshNative.publicTrialsS_source_cost]
  · intro j
    simp only [actualTrialsL, MultiOracleCircuit.Program.cost_substitute]
    rw [funext (implementationL_source D m N d Pw Lo φ hφ), Oracles.cost_add,
      NativeHermitianDilation.cost_scale]
    simp only [MeshNative.publicTrialsS_source_cost]

end Columns


end

end SparseHamiltonian.GeneralSourceExtensions.MeshOracles

namespace SparseHamiltonian.GeneralSourceExtensions.Mesh

noncomputable section
open ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding Set MeasureTheory
open TimeDependentExtensions
open SparseHamiltonian.TimeDependentODE (Accretive SolvesODE ratio accuracy radius precision
  lipschitz Index lchsCoefficients retarget)
open SparseHamiltonian.GeneralSourceODE (startTime sources phases phases_norm mass_sources
  phased_isometry phased_prepares nodeTable)
open scoped BigOperators InnerProduct
set_option maxRecDepth 4096
set_option synthInstance.maxSize 8192

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s M : ℕ}

/-- `Mesh.MeshPropagatedOutcome` with its public trial family named: the compiled family
`MeshNative.publicTrials` of the SELECT program `p` on `N` slots, the supplied `P_w`, `J`, the
public phases, the clean encoding `E`, the LCHS coefficients and the seed. -/
def MeshPublicOutcome (D : Data (X × Fin M) n Z s) (hM : 0 < M) (t : ℕ → ℝ) (N : ℕ)
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
      (∀ r : Fin M, SolvesODE (G r) (b r) sol (t r) (t ((r : ℕ) + 1))) →
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
/-- **`Mesh.mesh_propagated_solver` with its public trial family exposed.** The released proof;
only the conclusion names the trial family (`MeshPublicOutcome`), which `MeshPropagatedOutcome`
leaves existential. -/
theorem mesh_propagated_solver_public (D : Data (X × Fin M) n Z s) (hM : 0 < M) (t : ℕ → ℝ) {N : ℕ}
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
    (hPSD : ∀ (y : X × Fin M) (w : EuclideanSpace ℂ n), 0 ≤ (inner ℂ w
      (SparseStateOverlap.matrixOperator (ODEMatrixEnergy.dissipativePart (D.matrix y)) w)).re)
    (Pw : X → GeneralSourceODE.Weights.LabelOp (Option (Fin m))) (hPw : ∀ x, IsUnitary (Pw x))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ : ∀ x a, IsUnitary (J x a))
    (seed : EuclideanSpace ℂ n) (hSeed : ‖seed‖ = 1) :
    MeshPublicOutcome D hM t N etaH etaD T gbar cq ε v ω Pw J seed := by
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
  obtain ⟨_hGrid, hNodes, hMass, hApprox⟩ := TimeDependentODE.GaussianLCHS.table_certificate
    (fun y : X × Option (Fin m) => tableFamily D σ N (meshDurations t T v) y.1 y.2)
    (fun y z => tableFamily_analyticAt D σ N _ y.1 y.2 z)
    (fun y z hz => tableFamily_norm_le_one D σ N _ hu0 hPSD y.1 y.2 z hz)
    (lipschitz D T) hL (fun y k l => tableFamily_lipschitz D σ hN _ hu0 huT y.1 y.2 k l)
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
  intro x G b sol bv U ζ hG hGint _hsol hU hW hLoad₀ hLoad hMassB hCert hTarget hB hBudget
  -- The represented target.
  let z := sources (sol 0) bv ω
  let y := meshTarget D hM t T N v x (sol 0) bv ω
  set Bs := meshScale sol b t with hBs
  have hTargetErr := mesh_target_error D hM hPSD x hmesh hT.le hN G hG hGint U hU v hv ω
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
    meshTarget_norm_le D hM hmesh hT.le N v hPSD x (sol 0) bv ω
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
      (hAct x).1
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

/-- **The guarantee of `Mesh.mesh_solver` for a loader specified on its clean columns.** One
public trial family over the actual oracles `P_w`, `Lo`, `P_w†` on `N` slots and the coherent
sampled-time matrix oracle, chosen before every unknown instance. The loader `Lo` is a unitary on
the whole branch register; the instance hypotheses fix it only on the clean columns
`|a, τ⟩|seed⟩` of the source labels with nonzero source vectors, where it must prepare
`x(0)/‖x(0)‖` and `b_i/‖b_i‖` and keep the labels. All other hypotheses and the guarantee are
those of `Mesh.MeshOutcome`. -/
def MeshOutcomeColumns (D : Data (X × Fin M) n Z s) (t : ℕ → ℝ) (N : ℕ)
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
      ‖sol T - U 0 (sol 0) T - ∑ i, ω i • U (v i) (bv i) T‖ ≤ ζ * meshScale sol b t →
      sol T ≠ 0 →
      meshScale sol b t ≤ gbar * ‖sol T‖ →
      ζ + cq * (sampleError D x t G + refinementError D t T N) ≤ ε / (2000 * gbar) →
      GeneralSourceODE.Oracles.ActualCertificate
        (ODERepeatProtocol.Protocol.repeatTrials tf 4) x (sol T) (s : ℝ)
        (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) (ratio (cq * gbar)) (accuracy ε))
        (ImprovedODEQueryBudget.logBudget (ratio (cq * gbar)) (accuracy ε))
        (ratio (cq * gbar)) ε

set_option maxHeartbeats 8000000 in
/-- **Theorem `ode:thm:time` with the general source interface on a mesh, with a loader specified
on its clean columns only (item D1, exact case).** Under the hypotheses of `Mesh.mesh_solver`, with
the label-controlled `U_load` replaced by any unitary `Lo` on the whole branch register: one public
family of trial circuits over the coherent sampled-time matrix oracle on `N` slots and the supplied
`P_w`, `Lo` and `P_w†` gives, by four fresh trials, `x(T)/‖x(T)‖` with conditional trace distance
at most `ε` and success probability at least `2/3`, with at most
`1274019840 g' (√s Θ + √(s Θ ℓ) + ℓ)` matrix queries and at most `40 g'` calls of each of `P_w`,
`Lo` and `P_w†` in every history, for every instance satisfying the hypotheses of
`Mesh.MeshOutcome` with the loading hypotheses stated on the clean columns of `Lo`. The certificate
is that of the released proof for the label-controlled family `GeneralSourceODE.columnLoader Lo`
with the same columns (`MeshOracles.columns_certificate`). -/
theorem mesh_solver_columns (D : Data (X × Fin M) n Z s) (hM : 0 < M) (t : ℕ → ℝ) {N : ℕ}
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
    (hPSD : ∀ (y : X × Fin M) (w : EuclideanSpace ℂ n), 0 ≤ (inner ℂ w
      (SparseStateOverlap.matrixOperator (ODEMatrixEnergy.dissipativePart (D.matrix y)) w)).re)
    (Pw : X → GeneralSourceODE.Weights.LabelOp (Option (Fin m))) (hPw : ∀ x, IsUnitary (Pw x))
    (Lo : X → GeneralSourceODE.Native.SourceSpace (Index D T (cq * gbar) ε) n m →L[ℂ]
      GeneralSourceODE.Native.SourceSpace (Index D T (cq * gbar) ε) n m)
    (hLo : ∀ x, IsUnitary (Lo x))
    (seed : EuclideanSpace ℂ n) (hSeed : ‖seed‖ = 1) :
    MeshOutcomeColumns D t N etaH etaD T gbar cq ε v ω Pw Lo seed := by
  -- A label-controlled family with the clean columns of `Lo`; it is not called by the circuits.
  let J := GeneralSourceODE.columnLoader Lo seed (Sum.inr false)
  have hJ : ∀ x a, IsUnitary (J x a) := fun x a => GeneralSourceODE.loadUnitary_unitary _ _
  obtain ⟨d, E, hE, p, hSeedU, hOut, hCert⟩ := mesh_propagated_solver_public D hM t hN etaH etaD
    T gbar cq ε v ω hH hDiss hT hg hcq hε hεOne hmesh hρ hClock hCayley hv hrH hcH hrD hcD hPSD
    Pw hPw J hJ seed hSeed
  have hg1 : 1 ≤ ratio (cq * gbar) := by
    unfold ratio
    nlinarith
  obtain ⟨hMpos, -, -⟩ := ODEGroverAverage.chosenIterations_bounds (ratio (cq * gbar)) hg1
  have hcpos : 0 < ODECoherentLCU.coefficientMass (lchsCoefficients D T (cq * gbar) ε) := by
    rw [lchsCoefficients_mass D hT.le (cq * gbar) ε hg1 hε hεOne]
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
  intro x G b sol bv U ζ hG hGint hsol hU hW hCol₀ hCol hMassB hCertS hTarget hB hBudget
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
  have hC := hCert x G b sol bv U ζ hG hGint hsol hU hW hLoad₀ hLoad hMassB hCertS hTarget hB
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


/-- `MeshOutcomeColumns` for continuous pieces with the certificate on the propagated vector
integral. -/
def MeshIntegralOutcomeColumns (D : Data (X × Fin M) n Z s) (t : ℕ → ℝ) (N : ℕ)
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
      ζ + cq * (sampleError D x t G + refinementError D t T N) ≤ ε / (2000 * gbar) →
      GeneralSourceODE.Oracles.ActualCertificate
        (ODERepeatProtocol.Protocol.repeatTrials tf 4) x (sol T) (s : ℝ)
        (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) (ratio (cq * gbar)) (accuracy ε))
        (ImprovedODEQueryBudget.logBudget (ratio (cq * gbar)) (accuracy ε))
        (ratio (cq * gbar)) ε

set_option maxHeartbeats 8000000 in
/-- **Theorem `ode:thm:time` with the general source interface on a mesh, with the certificate on
the propagated vector integral and a loader specified on its clean columns only.** Under the
hypotheses of `mesh_solver_columns`, for continuous generator and forcing pieces,
`MeshIntegralOutcomeColumns` holds: the certificate
`‖∑_r ∫_{t_r}^{t_{r+1}} U(T, v) b_r(v) dv - ∑ ω_i U(T, v_i) b_i‖ ≤ ζ B` replaces the one on the
propagated source sum (`Mesh.mesh_duhamel`), as in `Mesh.mesh_solver_integral`. -/
theorem mesh_solver_integral_columns (D : Data (X × Fin M) n Z s) (hM : 0 < M) (t : ℕ → ℝ) {N : ℕ}
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
    (hPSD : ∀ (y : X × Fin M) (w : EuclideanSpace ℂ n), 0 ≤ (inner ℂ w
      (SparseStateOverlap.matrixOperator (ODEMatrixEnergy.dissipativePart (D.matrix y)) w)).re)
    (Pw : X → GeneralSourceODE.Weights.LabelOp (Option (Fin m))) (hPw : ∀ x, IsUnitary (Pw x))
    (Lo : X → GeneralSourceODE.Native.SourceSpace (Index D T (cq * gbar) ε) n m →L[ℂ]
      GeneralSourceODE.Native.SourceSpace (Index D T (cq * gbar) ε) n m)
    (hLo : ∀ x, IsUnitary (Lo x))
    (seed : EuclideanSpace ℂ n) (hSeed : ‖seed‖ = 1) :
    MeshIntegralOutcomeColumns D t N etaH etaD T gbar cq ε v ω Pw Lo seed := by
  obtain ⟨d, tf, hch, hU, hC⟩ := mesh_solver_columns D hM t hN etaH etaD T gbar cq ε v ω hH hDiss
    hT hg hcq hε hεOne hmesh hρ hClock hCayley hv hrH hcH hrD hcD hPSD Pw hPw Lo hLo seed hSeed
  refine ⟨d, tf, hch, hU, fun x G b sol bv U ζ hG hGc hbc hsol hUm hW hL0 hL hMass hInt hTarget
    hB hBudget => ?_⟩
  have hD := mesh_duhamel hmesh hUm hG hGc b hbc sol hsol
  have hCertP : ‖sol T - U 0 (sol 0) T - ∑ i, ω i • U (v i) (bv i) T‖ ≤ ζ * meshScale sol b t := by
    rw [← hD]
    exact hInt
  exact hC x G b sol bv U ζ hG (fun r => (hGc r).intervalIntegrable_of_Icc
    (hmesh.mono (Nat.le_succ r))) hsol hUm hW hL0 hL hMass hCertP hTarget hB hBudget

end

end SparseHamiltonian.GeneralSourceExtensions.Mesh
