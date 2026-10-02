import SparseODE.CoherentDiagonalExp

/-!
# One native active circuit on the full coherent ODE system

The public LCHS/source label is made part of the payload before the generic
chronological compiler is applied. Thus the compiler acts on the direct-sum
public/private system required by the common sharp simulator. Flattening adds
no queries and the native dummy-input construction adds exactly a factor of
three. No controlled native oracle is assumed.

-/

namespace SparseHamiltonian.ODEJointNative

noncomputable section
open ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding
open scoped InnerProduct
set_option maxRecDepth 4096
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 2000000

section AbstractIsometries

variable {P V : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- Package an abstract bounded isometry before instantiating the large native
register types. The norm proof never unfolds a concrete sparse preparation. -/
def isometryOfAdjoint (E : P →L[ℂ] V) (hE : E† ∘L E = 1) : P →ₗᵢ[ℂ] V where
  toLinearMap := E.toLinearMap
  norm_map' := E.norm_map_iff_adjoint_comp_self.mpr hE

/-- Abstract isometry identity, with both Hilbert spaces fixed explicitly at
its concrete applications below. -/
theorem isometry_adjoint (E : P →ₗᵢ[ℂ] V) :
    E.toContinuousLinearMap† ∘L E.toContinuousLinearMap = 1 :=
  E.adjoint_comp_self

end AbstractIsometries

variable {ι X n Z : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype n] [DecidableEq n]
  [Fintype Z] [AddCommGroup Z] [DecidableEq Z] {s : ℕ}

abbrev Public (ι n : Type*) [Fintype ι] [Fintype n] :=
  PiLp 2 (fun _ : ι => EuclideanSpace ℂ n)

abbrev Private (ι n : Type*) [Fintype ι] [Fintype n] :=
  PiLp 2 (fun _ : ι => ODETaggedMoments.PrivateSpace n)

/-- The coherent branch label precedes the already compiled native payload. -/
abbrev Basis (ι n Z : Type*) := ι × ODENativeCayley.Basis n Z

instance instDecidableEqBasis : DecidableEq (Basis ι n Z) :=
  @instDecidableEqProd _ _ inferInstance
    (inferInstance : DecidableEq (ODENativeCayley.Basis n Z))

/-- Fixed register coordinates, independent of all simulation parameters. -/
def layout : PiLp 2 (fun _ : ι => EuclideanSpace ℂ (ODENativeCayley.Basis n Z))
    ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Basis ι n Z) :=
  RegisterEquivalences.productFlatten ι (ODENativeCayley.Basis n Z)

/-- A primitive native query with the entire coherent branch as a spectator. -/
abbrev cayleyOracle (D : Data X n Z s) (l : Query) (x : X) :
    EuclideanSpace ℂ (Basis ι n Z) →L[ℂ] EuclideanSpace ℂ (Basis ι n Z) :=
  (layout (ι := ι) (n := n) (Z := Z)).conjStarAlgEquiv
    (ODECoherentCayley.oracle (ι := ι) D l x)

omit [DecidableEq ι] [DecidableEq Z] in
/-- The transported query is exactly the same original native query with a
spectator branch register. Only fixed register coordinates are unfolded. -/
theorem cayleyOracle_eq_spectator (D : Data X n Z s) (l : Query) (x : X) :
    cayleyOracle (ι := ι) D l x =
      LookupFromBasisOracle.spectator (S := ι) (ODENativeCayley.oracle D l x) := by
  rfl

omit [DecidableEq ι] [DecidableEq Z] in
theorem cayleyOracle_unitary (D : Data X n Z s) (l : Query) (x : X) :
    IsUnitary (cayleyOracle (ι := ι) D l x) := by
  rw [cayleyOracle_eq_spectator]
  exact LookupFromBasisOracle.spectator_unitary _ (ODENativeCayley.oracle_unitary D l x)

/-- The dummy input is public. Its image is used only as a validity witness. -/
def cleanBasis (D : Data X n Z s) (i0 : ι) : Basis ι n Z :=
  (i0, ODENativeCayley.cleanBasis D)

def image (D : Data X n Z s) (i0 : ι) (l : Query) (x : X) : Basis ι n Z :=
  (i0, ODENativeCayley.image D l x)

theorem valid (D : Data X n Z s) (i0 : ι) (l : Query) (x : X) :
    cayleyOracle D l x (EuclideanSpace.single (cleanBasis D i0) 1) =
      EuclideanSpace.single (image D i0 l x) 1 := by
  rw [cayleyOracle_eq_spectator]
  exact LookupFromBasisOracle.spectator_single (ODENativeCayley.oracle D l x)
    (ODENativeCayley.cleanBasis D) (ODENativeCayley.image D l x) 1
    (ODENativeCayley.valid D l x) i0

/-- The literal twenty-four-query coherent circuit, in flattened coordinates. -/
def cayleyProgram (D : Data X n Z s) (k γ : ι → ℝ) (ρ : ℝ) :
    MultiOracleCircuit.Program (cayleyOracle (ι := ι) D) := by
  let p := MultiOracleCircuit.Program.transport
    (O := ODECoherentCayley.oracle (ι := ι) D)
    (layout (ι := ι) (n := n) (Z := Z)) (ODECoherentCayley.program D k γ ρ)
  with_reducible exact p

omit [DecidableEq ι] in
@[simp] theorem cayleyProgram_count (D : Data X n Z s) (k γ : ι → ℝ) (ρ : ℝ) :
    (cayleyProgram D k γ ρ).count = 24 := by
  simp only [cayleyProgram, MultiOracleCircuit.Program.count_transport,
    ODECoherentCayley.program_count]

omit [DecidableEq ι] in
@[simp] theorem cayleyProgram_cost (D : Data X n Z s) (k γ : ι → ℝ) (ρ : ℝ)
    (w : Query → ℕ) :
    (cayleyProgram D k γ ρ).cost w =
      6 * w .rowLocation + 6 * w .columnLocation + 12 * w .value := by
  simp only [cayleyProgram, MultiOracleCircuit.Program.cost_transport,
    ODECoherentCayley.program_cost]

/-- The two generator parameters are public functions of the coherent label. -/
def logicalAction (D : Data X n Z s) (k γ : ι → ℝ) (ρ : ℝ) (x : X) :
    Private ι n →L[ℂ] Private ι n :=
  WeightedClock.diagonal (fun i => ODEFixedTaggedMoments.action D x
    (ODEMatrixEnergy.lchsHamiltonian (D.matrix x) (k i)) ρ (γ i))

/-- Turn the already proved coherent clean isometry into an isometric map. -/
def coherentClean (D : Data X n Z s) :
    Private ι n →ₗᵢ[ℂ]
      PiLp 2 (fun _ : ι => EuclideanSpace ℂ (ODENativeCayley.Basis n Z)) :=
  isometryOfAdjoint (P := Private ι n)
    (V := PiLp 2 (fun _ : ι => EuclideanSpace ℂ (ODENativeCayley.Basis n Z)))
    (ODECoherentCayley.clean (ι := ι) D) (ODECoherentCayley.clean_isometry (ι := ι) D)

/-- The same preparation serves every node, duration and rescaling. -/
def clean (D : Data X n Z s) :
    Private ι n →ₗᵢ[ℂ] EuclideanSpace ℂ (Basis ι n Z) :=
  (layout (ι := ι) (n := n) (Z := Z)).toLinearIsometry.comp (coherentClean D)

omit [DecidableEq ι] in
theorem clean_isometry (D : Data X n Z s) :
    (clean (ι := ι) D).toContinuousLinearMap† ∘L
      (clean D).toContinuousLinearMap = 1 :=
  isometry_adjoint (P := Private ι n) (V := EuclideanSpace ℂ (Basis ι n Z))
    (clean (ι := ι) D)

omit [DecidableEq ι] in
/-- Transport only the abstract circuit and clean intertwining identity. -/
theorem cayleyProgram_intertwines (D : Data X n Z s) (k γ : ι → ℝ)
    (ρ : ℝ) (x : X) :
    (cayleyProgram D k γ ρ).eval x ∘L (clean D).toContinuousLinearMap =
      (clean D).toContinuousLinearMap ∘L logicalAction D k γ ρ x := by
  rw [cayleyProgram, MultiOracleCircuit.Program.eval_transport]
  apply ContinuousLinearMap.ext
  intro v
  change layout ((ODECoherentCayley.program D k γ ρ).eval x
    (layout.symm (layout (coherentClean D v)))) =
      layout (coherentClean D (logicalAction D k γ ρ x v))
  rw [LinearIsometryEquiv.symm_apply_apply]
  exact congrArg (layout (ι := ι) (n := n) (Z := Z))
    (congrArg (fun A : Private ι n →L[ℂ]
      PiLp 2 (fun _ : ι => EuclideanSpace ℂ (ODENativeCayley.Basis n Z)) => A v)
      (ODECoherentCayley.program_intertwines D k γ ρ x))

/-- The common boundary is the direct sum of the original public preparation. -/
def boundary (D : Data X n Z s) : Public ι n →L[ℂ] Private ι n :=
  CoherentQuerySchedule.rectangular (fun _ : ι => ODEFixedTaggedMoments.boundary D)

omit [DecidableEq ι] [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
theorem boundary_isometry (D : Data X n Z s) :
    (boundary (ι := ι) D)† ∘L boundary D = 1 :=
  CoherentQuerySchedule.rectangular_isometry _
    (fun _ : ι => ODEFixedTaggedMoments.boundary_isometry D)

def boundaryIsometry (D : Data X n Z s) : Public ι n →ₗᵢ[ℂ] Private ι n :=
  isometryOfAdjoint (P := Public ι n) (V := Private ι n)
    (boundary (ι := ι) D) (boundary_isometry (ι := ι) D)

/-- Public and private vectors use the same complete native payload. -/
def publicEmbedding (D : Data X n Z s) :
    Public ι n →ₗᵢ[ℂ] EuclideanSpace ℂ (Basis ι n Z) :=
  (clean D).comp (boundaryIsometry D)

def privateEmbedding (D : Data X n Z s) : Private ι n →ₗᵢ[ℂ]
    NativeMaskedOracle.Logical PUnit.{1} (Basis ι n Z) :=
  FlatMaskedAccess.singleton (clean D)

/-- The chronological label lies outside the joint coherent payload. -/
abbrev Physical (ι n Z : Type*) [Fintype ι] [Fintype n] [Fintype Z] (T d : ℕ) :=
  NativeMaskedOracle.Physical (ActiveRegisterLayout.Label PUnit.{1} T d) (Basis ι n Z)

abbrev oracle (D : Data X n Z s) (T d : ℕ) :
    Query → X → Physical ι n Z T d →L[ℂ] Physical ι n Z T d :=
  NativeWholeProgramActive.oracle (C := PUnit.{1}) (cayleyOracle (ι := ι) D) T d

/-- Fixed encoding for the common sharp simulator on the full direct sum. -/
def embedding (D : Data X n Z s) (i0 : ι) (T d : ℕ) :
    PiLp 2 (SmoothingLCU.BranchSpace (P := Public ι n)
      (V := ChronologicalResolvent.BlockOperator.H T (Private ι n)) d)
        →ₗᵢ[ℂ] Physical ι n Z T d :=
  NativeWholeProgramActive.cleanInput (C := PUnit.{1})
    (publicEmbedding D) (privateEmbedding D) (cleanBasis D i0) T d

theorem embedding_isometry (D : Data X n Z s) (i0 : ι) (T d : ℕ) :
    (embedding D i0 T d).toContinuousLinearMap† ∘L
      (embedding D i0 T d).toContinuousLinearMap = 1 :=
  (embedding D i0 T d).adjoint_comp_self

/-- Ordinary native calls implement one active joint-system Cayley layer. -/
def program (D : Data X n Z s) (i0 : ι) (k γ : ι → ℝ) (ρ : ℝ) (T d r : ℕ) :
    MultiOracleCircuit.Program (oracle (ι := ι) D T d) :=
  NativeWholeProgramActive.program (C := PUnit.{1}) (cayleyOracle D)
    (cleanBasis D i0) (cayleyProgram D k γ ρ) T d r

@[simp] theorem program_count (D : Data X n Z s) (i0 : ι) (k γ : ι → ℝ)
    (ρ : ℝ) (T d r : ℕ) : (program D i0 k γ ρ T d r).count = 72 := by
  rw [program, NativeWholeProgramActive.program_count, cayleyProgram_count]

theorem program_cost (D : Data X n Z s) (i0 : ι) (k γ : ι → ℝ)
    (ρ : ℝ) (T d r : ℕ) (w : Query → ℕ) :
    (program D i0 k γ ρ T d r).cost w =
      18 * w .rowLocation + 18 * w .columnLocation + 36 * w .value := by
  rw [program, NativeWholeProgramActive.program_cost, cayleyProgram_cost]
  ring

omit [DecidableEq ι] [DecidableEq Z] in
theorem oracle_unitary (D : Data X n Z s) (T d : ℕ) (l : Query) (x : X) :
    IsUnitary (oracle (ι := ι) D T d l x) :=
  NativeMaskedOracle.oracle_unitary (cayleyOracle (ι := ι) D l)
    (cayleyOracle_unitary D l) x

/-- Joint coherent semantics, matching the direct-sum moment certificate. -/
theorem program_intertwines (D : Data X n Z s) (i0 : ι) (k γ : ι → ℝ)
    (ρ : ℝ) (T d r : ℕ) (x : X) :
    (program D i0 k γ ρ T d r).eval x ∘L (embedding D i0 T d).toContinuousLinearMap =
      (embedding D i0 T d).toContinuousLinearMap ∘L
        ReuseLayerFactorization.activeClock (P := Public ι n)
          (logicalAction D k γ ρ x) T d r := by
  exact NativeWholeProgramActive.program_clean_intertwines
    (C := PUnit.{1}) (B := Basis ι n Z) (P := Public ι n) (V := Private ι n)
    (cayleyOracle D) (cayleyOracle_unitary D)
    (cleanBasis D i0) (image D i0) (valid D i0) (cayleyProgram D k γ ρ)
    (publicEmbedding D) (privateEmbedding D) (logicalAction D k γ ρ)
    (fun x => FlatMaskedAccess.singleton_intertwines
      (V := Private ι n) (B := Basis ι n Z)
      ((cayleyProgram D k γ ρ).eval x) (logicalAction D k γ ρ x) (clean D)
      (cayleyProgram_intertwines D k γ ρ x)) T d r x

/-- The active implementation hypothesis is discharged at 72 primitive calls,
independently of the cardinality of the public LCHS/source index set. -/
theorem implementsOn (D : Data X n Z s) (i0 : ι) (k γ : ι → ℝ)
    (ρ : ℝ) (T d r : ℕ) :
    LabeledEncodedOracle.ImplementsOn (oracle (ι := ι) D T d)
      (fun x => ReuseLayerFactorization.activeClock (P := Public ι n)
        (logicalAction D k γ ρ x) T d r)
      (embedding D i0 T d).toContinuousLinearMap 72 :=
  ⟨program D i0 k γ ρ T d r, program_intertwines D i0 k γ ρ T d r,
    (program_count D i0 k γ ρ T d r).le⟩

end
end SparseHamiltonian.ODEJointNative
