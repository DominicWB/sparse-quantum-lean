import GeneralSourceODE.Primitive
import GeneralSourceODE.Durations
import TimeDependentODE.Native.Source

/-!
# Native coordinates for the general-source circuits

General-source counterpart of `TimeDependentODE.NativeSource`. The source
labels are the initial label and the `m` public quadrature nodes, decoupled
from the `M` time samples of the coherent sampled-time SELECT. The source
register keeps the released Cartesian coordinates
(`ODEFinalNativeSource.sourceLayout`). The matrix register is the aligned
workspace of the SELECT on the branch labels `Option (Fin m) × ι`, flattened
by the released aligned layout. Its public dummy input uses the initial
source branch, a fixed LCHS label and the first sample; the phase-one basis
transition of every primitive call is derived from sparse access
(`matrix_valid`), not assumed.

The counted general-source trials are compiled to ordinary native queries by
the released coordinate compiler. With the public LCHS coefficients, the trial
family depends only on public data (`publicTrials`), and every pointwise
source certificate gives the released primitive trial certificate for that
same family (`trial_certificate`).
-/

namespace SparseHamiltonian.GeneralSourceODE.Native

noncomputable section
open ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding
open scoped InnerProduct BigOperators
set_option maxRecDepth 4096
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 2000000

variable {ι X n Z : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z] [DecidableEq Z]
  {s M m : ℕ}

/-- SELECT branch labels: a source label and an LCHS label. -/
abbrev Label (ι : Type*) (m : ℕ) := Option (Fin m) × ι

abbrev SourceBasis (ι n : Type*) (m : ℕ) := ODEFinalNativeSource.SourceBasis ι n m

abbrev SourceSpace (ι n : Type*) [Fintype ι] [Fintype n] (m : ℕ) :=
  ODEFinalNativeSource.SourceSpace ι n m

abbrev MatrixBasis (ι n Z : Type*) (m M d : ℕ) :=
  ODEFinalNativeBasis.AlignedBasis (ActiveRegisterLayout.Label PUnit.{1} M d)
    (TimeDependentODE.Basis (Label ι m) n Z M)

/-- The aligned workspace of the coherent sampled-time SELECT. -/
abbrev MatrixSpace (ι n Z : Type*) [Fintype ι] [Fintype n] [Fintype Z] (m M d : ℕ) :=
  CleanOutputAlignment.Double (TimeDependentODE.Physical (Label ι m) n Z M M d)

abbrev Logical (ι n Z : Type*) [Fintype ι] [Fintype n] [Fintype Z] (m M d : ℕ) :=
  ODESourceTransport.Space (SourceSpace ι n m) (MatrixSpace ι n Z m M d)

/-- The complete primitive workspace. -/
abbrev PhysicalSpace (ι n Z : Type*) [Fintype ι] [Fintype n] [Fintype Z] (m M d : ℕ) :=
  ODESectorTensor.Physical (SourceBasis ι n m) (MatrixBasis ι n Z m M d)

def sourceLayout (m : ℕ) :
    SourceSpace ι n m ≃ₗᵢ[ℂ] EuclideanSpace ℂ (SourceBasis ι n m) :=
  ODEFinalNativeSource.sourceLayout (ι := ι) (n := n) m

def matrixLayout (m M d : ℕ) :
    MatrixSpace ι n Z m M d ≃ₗᵢ[ℂ] EuclideanSpace ℂ (MatrixBasis ι n Z m M d) :=
  ODEFinalNativeBasis.alignedLayout (β := ActiveRegisterLayout.Label PUnit.{1} M d)
    (B := TimeDependentODE.Basis (Label ι m) n Z M)

/-- Coherent sampled-time native queries with the alignment spectator. -/
abbrev matrixOracle (D : Data (X × Fin M) n Z s) (m d : ℕ) :
    Query → X → MatrixSpace ι n Z m M d →L[ℂ] MatrixSpace ι n Z m M d :=
  AlignedMultiOracleProgram.oracle (TimeDependentODE.oracle (ι := Label ι m) D M d)

omit [DecidableEq ι] [DecidableEq Z] in
theorem matrixOracle_unitary (D : Data (X × Fin M) n Z s) (m d : ℕ) :
    ∀ l x, IsUnitary (matrixOracle (ι := ι) D m d l x) :=
  CoherentQuerySchedule.oracle_unitary (TimeDependentODE.oracle (ι := Label ι m) D M d)
    (TimeDependentODE.oracle_unitary (ι := Label ι m) D M d)

/-- The public source reference: initial branch, LCHS label `i0`, first sparse slot. -/
def sourceBasis (D : Data (X × Fin M) n Z s) (i0 : ι) (m : ℕ) : SourceBasis ι n m :=
  ((none, i0), D.slot ⟨0, D.slots_pos⟩)

/-- The public SELECT dummy address: initial branch, LCHS label `i0`, first sample. -/
def dummy (hM : 0 < M) (i0 : ι) (m : ℕ) : Label ι m × Fin M := ((none, i0), ⟨0, hM⟩)

def matrixBasis (D : Data (X × Fin M) n Z s) (hM : 0 < M) (i0 : ι) (m d : ℕ) :
    MatrixBasis ι n Z m M d :=
  ODEFinalNativeBasis.alignedClean (ODEFinalNativeBasis.clockBasis M d)
    (TimeDependentODE.cleanBasis D (dummy hM i0 m))

def matrixImage (D : Data (X × Fin M) n Z s) (hM : 0 < M) (i0 : ι) (m d : ℕ)
    (l : Query) (x : X) : MatrixBasis ι n Z m M d :=
  ODEFinalNativeBasis.alignedImage (ODEFinalNativeBasis.clockBasis M d)
    (TimeDependentODE.cleanBasis D (dummy hM i0 m))
    (TimeDependentODE.image D (dummy hM i0 m) l x)

/-- The native basis-image control promise is derived from sparse access. -/
theorem matrix_valid (D : Data (X × Fin M) n Z s) (hM : 0 < M) (i0 : ι) (m d : ℕ)
    (l : Query) (x : X) :
    (matrixLayout (ι := ι) (n := n) (Z := Z) m M d).conjStarAlgEquiv
        (matrixOracle D m d l x) (EuclideanSpace.single (matrixBasis D hM i0 m d) 1) =
      EuclideanSpace.single (matrixImage D hM i0 m d l x) 1 :=
  ODEFinalNativeBasis.aligned_valid (β := ActiveRegisterLayout.Label PUnit.{1} M d)
    (TimeDependentODE.cayleyOracle (ι := Label ι m) D) (ODEFinalNativeBasis.clockBasis M d)
    (TimeDependentODE.cleanBasis D (dummy hM i0 m))
    (TimeDependentODE.image D (dummy hM i0 m))
    (TimeDependentODE.valid D (dummy hM i0 m)) l x

/-- One fixed encoding serves every source-loaded preparation and trial. -/
def input (D : Data (X × Fin M) n Z s) (hM : 0 < M) (i0 : ι) (m d : ℕ) :
    Logical ι n Z m M d →L[ℂ] PhysicalSpace ι n Z m M d :=
  ODECoordinateNativeControl.input
    (A := SourceBasis ι n m) (B := MatrixBasis ι n Z m M d)
    (H := SourceSpace ι n m) (K := MatrixSpace ι n Z m M d)
    (sourceLayout (ι := ι) (n := n) m)
    (matrixLayout (ι := ι) (n := n) (Z := Z) m M d)
    (sourceBasis D i0 m) (matrixBasis D hM i0 m d)

theorem input_isometry (D : Data (X × Fin M) n Z s) (hM : 0 < M) (i0 : ι) (m d : ℕ) :
    (input D hM i0 m d)† ∘L input D hM i0 m d = 1 := by
  unfold input
  exact ODECoordinateNativeControl.input_isometry
    (A := SourceBasis ι n m) (B := MatrixBasis ι n Z m M d)
    (H := SourceSpace ι n m) (K := MatrixSpace ι n Z m M d)
    (sourceLayout (ι := ι) (n := n) m)
    (matrixLayout (ι := ι) (n := n) (Z := Z) m M d)
    (sourceBasis D i0 m) (matrixBasis D hM i0 m d)

/-- The two counted source interfaces: the preparation `U_load ∘ (P_w ⊗ 1)`
followed by the public phases, and the label unpreparation `P_w† ⊗ 1`. -/
abbrev sourceFamily (Pw : X → Weights.LabelOp (Option (Fin m)))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (φ : Option (Fin m) → ℂ) :
    Bool → X → SourceSpace ι n m →L[ℂ] SourceSpace ι n m :=
  Compiled.sourceFamily (ι := ι) Pw J φ

/-- Ordinary coherent sampled-time matrix calls with fixed spectators,
together with the two counted source interfaces. -/
abbrev physicalOracle (D : Data (X × Fin M) n Z s) (m d : ℕ)
    (Pw : X → Weights.LabelOp (Option (Fin m)))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (φ : Option (Fin m) → ℂ) :
    Query ⊕ Bool → X → PhysicalSpace ι n Z m M d →L[ℂ] PhysicalSpace ι n Z m M d :=
  ODECoordinateNativeControl.physicalOracle
    (A := SourceBasis ι n m) (B := MatrixBasis ι n Z m M d)
    (H := SourceSpace ι n m) (K := MatrixSpace ι n Z m M d) (X := X) (L := Query)
    (sourceLayout (ι := ι) (n := n) m)
    (matrixLayout (ι := ι) (n := n) (Z := Z) m M d)
    (matrixOracle (ι := ι) D m d)
    (sourceFamily (ι := ι) Pw J φ)

omit [DecidableEq ι] [DecidableEq Z] in
/-- Unitarity holds on the entire primitive workspace. -/
theorem physicalOracle_unitary (D : Data (X × Fin M) n Z s) (m d : ℕ)
    (Pw : X → Weights.LabelOp (Option (Fin m))) (hPw : ∀ x, IsUnitary (Pw x))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ : ∀ x a, IsUnitary (J x a)) (φ : Option (Fin m) → ℂ) (hφ : ∀ a, ‖φ a‖ = 1) :
    ∀ l x, IsUnitary (physicalOracle (ι := ι) D m d Pw J φ l x) :=
  ODECoordinateNativeControl.physicalOracle_unitary
    (A := SourceBasis ι n m) (B := MatrixBasis ι n Z m M d)
    (H := SourceSpace ι n m) (K := MatrixSpace ι n Z m M d) (X := X) (L := Query)
    (sourceLayout (ι := ι) (n := n) m)
    (matrixLayout (ι := ι) (n := n) (Z := Z) m M d)
    (matrixOracle (ι := ι) D m d)
    (sourceFamily (ι := ι) Pw J φ) (matrixOracle_unitary (ι := ι) D m d)
    (Compiled.sourceFamily_unitary hPw hJ hφ)

/-- The compiled public trial family. Its SELECT program, source interfaces,
public phases, encoding, LCHS coefficients and seed are public data; proofs
only justify the fixed reflections. -/
def publicTrials (D : Data (X × Fin M) n Z s) (hM : 0 < M) (i0 : ι) (m d : ℕ)
    (p : MultiOracleCircuit.Program (matrixOracle (ι := ι) D m d))
    (Pw : X → Weights.LabelOp (Option (Fin m)))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (φ : Option (Fin m) → ℂ)
    (E : SourceSpace ι n m →L[ℂ] MatrixSpace ι n Z m M d) (hE : E† ∘L E = 1)
    (c : ι → ℂ) (seed : EuclideanSpace ℂ n)
    (hSeed : ‖ODECompiledSource.seed E (Compiled.seedCoefficients c) seed‖ = 1)
    (hOutput : (ODECompiledSource.output E (Compiled.seedCoefficients c))† ∘L
      ODECompiledSource.output E (Compiled.seedCoefficients c) = 1) :
    ℕ → MultiOracleCircuit.Program (physicalOracle (ι := ι) D m d Pw J φ) :=
  fun j => ODECoordinateNativeControl.compile
    (A := SourceBasis ι n m) (B := MatrixBasis ι n Z m M d)
    (H := SourceSpace ι n m) (K := MatrixSpace ι n Z m M d) (X := X) (L := Query)
    (sourceLayout (ι := ι) (n := n) m)
    (matrixLayout (ι := ι) (n := n) (Z := Z) m M d)
    (matrixOracle (ι := ι) D m d) (sourceFamily (ι := ι) Pw J φ)
    (sourceBasis D i0 m) (matrixBasis D hM i0 m d)
    (Compiled.publicLogicalTrials p Pw J φ E hE c seed hSeed hOutput j)

/-- Every source certificate for the actual source vectors gives the released
primitive trial certificate for the public trial family. -/
theorem trial_certificate (D : Data (X × Fin M) n Z s) (hM : 0 < M)
    (i0 : ι) (m d : ℕ)
    (p : MultiOracleCircuit.Program (matrixOracle (ι := ι) D m d))
    (Pw : X → Weights.LabelOp (Option (Fin m))) (hPw : ∀ x, IsUnitary (Pw x))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ : ∀ x a, IsUnitary (J x a)) (φ : Option (Fin m) → ℂ) (hφ : ∀ a, ‖φ a‖ = 1)
    (E : SourceSpace ι n m →L[ℂ] MatrixSpace ι n Z m M d) (hE : E† ∘L E = 1)
    (z : Option (Fin m) → EuclideanSpace ℂ n) (c : ι → ℂ)
    (hc : 0 < ODECoherentLCU.coefficientMass c)
    (seed target : EuclideanSpace ℂ n) (hSeed : ‖seed‖ = 1)
    (Θ ell g ε : ℝ) (hg : 1 ≤ g) (x : X)
    (hz : 0 < ODESourceBranches.mass z) (hW : Compiled.WeightPrep (Pw x) z)
    (hCert : ODEActualSourceError.Certificate E z c
      (Compiled.phased (J x) φ) (p.eval x) seed target g ε)
    (hq : (p.count : ℝ) ≤ 10616832 * ImprovedODEQueryBudget.queryShape (s : ℝ) Θ ell)
    (hSeedUnit : ‖ODECompiledSource.seed E (Compiled.seedCoefficients c) seed‖ = 1)
    (hOutput : (ODECompiledSource.output E (Compiled.seedCoefficients c))† ∘L
      ODECompiledSource.output E (Compiled.seedCoefficients c) = 1) :
    ODEPrimitiveSourceJoin.TrialCertificate
      (publicTrials D hM i0 m d p Pw J φ E hE c seed hSeedUnit hOutput)
      (ODEGroverAverage.chosenIterations g)
      (input D hM i0 m d (ODECompiledSource.seed E (Compiled.seedCoefficients c) seed))
      (input D hM i0 m d ∘L ODECompiledSource.output E (Compiled.seedCoefficients c))
      x target (s : ℝ) Θ ell g (ε / 500) :=
  Compiled.public_source_certificate p (matrixOracle_unitary (ι := ι) D m d)
    Pw hPw J hJ φ hφ E hE z c hc seed target hSeed (s : ℝ) Θ ell g ε hg x hz hW hCert hq
    (sourceLayout (ι := ι) (n := n) m)
    (matrixLayout (ι := ι) (n := n) (Z := Z) m M d)
    (sourceBasis D i0 m) (matrixBasis D hM i0 m d)
    (matrixImage D hM i0 m d) (matrix_valid D hM i0 m d) hSeedUnit hOutput

/-- The public seed on the primitive workspace is a unit vector. -/
theorem seed_unit (D : Data (X × Fin M) n Z s) (hM : 0 < M) (i0 : ι) (m d : ℕ)
    (E : SourceSpace ι n m →L[ℂ] MatrixSpace ι n Z m M d) (hE : E† ∘L E = 1)
    (c : ι → ℂ) (hc : 0 < ODECoherentLCU.coefficientMass c)
    (seed : EuclideanSpace ℂ n) (hSeed : ‖seed‖ = 1) :
    ‖input D hM i0 m d (ODECompiledSource.seed E (Compiled.seedCoefficients c) seed)‖ = 1 := by
  have hsc : 0 < ODECoherentLCU.coefficientMass (Compiled.seedCoefficients (N := m) c) := by
    rw [Compiled.seedCoefficients_mass]
    exact hc
  rw [(input D hM i0 m d).norm_map_iff_adjoint_comp_self.mpr (input_isometry D hM i0 m d)]
  exact ODECompiledSource.seed_unit E _ hE hsc seed hSeed

/-- The public output flag on the primitive workspace is an isometry. -/
theorem output_isometry (D : Data (X × Fin M) n Z s) (hM : 0 < M) (i0 : ι) (m d : ℕ)
    (E : SourceSpace ι n m →L[ℂ] MatrixSpace ι n Z m M d) (hE : E† ∘L E = 1)
    (c : ι → ℂ) (hc : 0 < ODECoherentLCU.coefficientMass c) :
    (input D hM i0 m d ∘L ODECompiledSource.output E (Compiled.seedCoefficients c))† ∘L
      (input D hM i0 m d ∘L ODECompiledSource.output E (Compiled.seedCoefficients c)) = 1 := by
  have hsc : 0 < ODECoherentLCU.coefficientMass (Compiled.seedCoefficients (N := m) c) := by
    rw [Compiled.seedCoefficients_mass]
    exact hc
  exact NativeSparseAttenuation.isometry_comp _ _
    (ODECompiledSource.output_isometry E _ hE hsc) (input_isometry D hM i0 m d)

end

end SparseHamiltonian.GeneralSourceODE.Native
