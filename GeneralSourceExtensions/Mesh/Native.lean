import GeneralSourceODE.Native
import TimeDependentExtensions.ODE.Select

/-!
# Native coordinates for the general-source circuits on `N` slots

The released general-source layer (`SparseHamiltonian.GeneralSourceODE.Native`) uses the aligned
SELECT workspace with as many slots as samples. Here the matrix register is the aligned workspace
of the coherent sampled-time SELECT on `N` slots (`TimeDependentExtensions.MeshSelect`): the source
register, the source interfaces and the time register of the coherent sampled-time oracle keep the
released layout and the `M` samples; only the clock register has `N` slots. Everything else is
the released construction: the public dummy input with its phase-one basis transition derived
from sparse access (`matrix_valid`), the coordinate compiler of the counted source trials
(`publicTrials`), and the released primitive trial certificate (`trial_certificate`).
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

abbrev MatrixBasis (ι n Z : Type*) (m M N d : ℕ) :=
  ODEFinalNativeBasis.AlignedBasis (ActiveRegisterLayout.Label PUnit.{1} N d)
    (TimeDependentODE.Basis (Label ι m) n Z M)

/-- The aligned workspace of the coherent sampled-time SELECT on `N` slots. -/
abbrev MatrixSpace (ι n Z : Type*) [Fintype ι] [Fintype n] [Fintype Z] (m M N d : ℕ) :=
  CleanOutputAlignment.Double (TimeDependentODE.Physical (Label ι m) n Z M N d)

abbrev Logical (ι n Z : Type*) [Fintype ι] [Fintype n] [Fintype Z] (m M N d : ℕ) :=
  ODESourceTransport.Space (SourceSpace ι n m) (MatrixSpace ι n Z m M N d)

/-- The complete primitive workspace. -/
abbrev PhysicalSpace (ι n Z : Type*) [Fintype ι] [Fintype n] [Fintype Z] (m M N d : ℕ) :=
  ODESectorTensor.Physical (SourceBasis ι n m) (MatrixBasis ι n Z m M N d)

def matrixLayout (m M N d : ℕ) :
    MatrixSpace ι n Z m M N d ≃ₗᵢ[ℂ] EuclideanSpace ℂ (MatrixBasis ι n Z m M N d) :=
  ODEFinalNativeBasis.alignedLayout (β := ActiveRegisterLayout.Label PUnit.{1} N d)
    (B := TimeDependentODE.Basis (Label ι m) n Z M)

/-- Coherent sampled-time native queries with the alignment spectator. -/
abbrev matrixOracle (D : Data (X × Fin M) n Z s) (m N d : ℕ) :
    Query → X → MatrixSpace ι n Z m M N d →L[ℂ] MatrixSpace ι n Z m M N d :=
  AlignedMultiOracleProgram.oracle (TimeDependentODE.oracle (ι := Label ι m) D N d)

omit [DecidableEq ι] [DecidableEq Z] in
theorem matrixOracle_unitary (D : Data (X × Fin M) n Z s) (m N d : ℕ) :
    ∀ l x, IsUnitary (matrixOracle (ι := ι) D m N d l x) :=
  CoherentQuerySchedule.oracle_unitary (TimeDependentODE.oracle (ι := Label ι m) D N d)
    (TimeDependentODE.oracle_unitary (ι := Label ι m) D N d)

def matrixBasis (D : Data (X × Fin M) n Z s) (hM : 0 < M) (i0 : ι) (m N d : ℕ) :
    MatrixBasis ι n Z m M N d :=
  ODEFinalNativeBasis.alignedClean (ODEFinalNativeBasis.clockBasis N d)
    (TimeDependentODE.cleanBasis D (dummy hM i0 m))

def matrixImage (D : Data (X × Fin M) n Z s) (hM : 0 < M) (i0 : ι) (m N d : ℕ)
    (l : Query) (x : X) : MatrixBasis ι n Z m M N d :=
  ODEFinalNativeBasis.alignedImage (ODEFinalNativeBasis.clockBasis N d)
    (TimeDependentODE.cleanBasis D (dummy hM i0 m))
    (TimeDependentODE.image D (dummy hM i0 m) l x)

/-- The native basis-image control promise is derived from sparse access. -/
theorem matrix_valid (D : Data (X × Fin M) n Z s) (hM : 0 < M) (i0 : ι) (m N d : ℕ)
    (l : Query) (x : X) :
    (matrixLayout (ι := ι) (n := n) (Z := Z) m M N d).conjStarAlgEquiv
        (matrixOracle D m N d l x) (EuclideanSpace.single (matrixBasis D hM i0 m N d) 1) =
      EuclideanSpace.single (matrixImage D hM i0 m N d l x) 1 :=
  ODEFinalNativeBasis.aligned_valid (β := ActiveRegisterLayout.Label PUnit.{1} N d)
    (TimeDependentODE.cayleyOracle (ι := Label ι m) D) (ODEFinalNativeBasis.clockBasis N d)
    (TimeDependentODE.cleanBasis D (dummy hM i0 m))
    (TimeDependentODE.image D (dummy hM i0 m))
    (TimeDependentODE.valid D (dummy hM i0 m)) l x

/-- One fixed encoding serves every source-loaded preparation and trial. -/
def input (D : Data (X × Fin M) n Z s) (hM : 0 < M) (i0 : ι) (m N d : ℕ) :
    Logical ι n Z m M N d →L[ℂ] PhysicalSpace ι n Z m M N d :=
  ODECoordinateNativeControl.input
    (A := SourceBasis ι n m) (B := MatrixBasis ι n Z m M N d)
    (H := SourceSpace ι n m) (K := MatrixSpace ι n Z m M N d)
    (sourceLayout (ι := ι) (n := n) m)
    (matrixLayout (ι := ι) (n := n) (Z := Z) m M N d)
    (sourceBasis D i0 m) (matrixBasis D hM i0 m N d)

theorem input_isometry (D : Data (X × Fin M) n Z s) (hM : 0 < M) (i0 : ι) (m N d : ℕ) :
    (input D hM i0 m N d)† ∘L input D hM i0 m N d = 1 := by
  unfold input
  exact ODECoordinateNativeControl.input_isometry
    (A := SourceBasis ι n m) (B := MatrixBasis ι n Z m M N d)
    (H := SourceSpace ι n m) (K := MatrixSpace ι n Z m M N d)
    (sourceLayout (ι := ι) (n := n) m)
    (matrixLayout (ι := ι) (n := n) (Z := Z) m M N d)
    (sourceBasis D i0 m) (matrixBasis D hM i0 m N d)

/-- Ordinary coherent sampled-time matrix calls with fixed spectators, together with the two
counted source interfaces. -/
abbrev physicalOracle (D : Data (X × Fin M) n Z s) (m N d : ℕ)
    (Pw : X → Weights.LabelOp (Option (Fin m)))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (φ : Option (Fin m) → ℂ) :
    Query ⊕ Bool → X → PhysicalSpace ι n Z m M N d →L[ℂ] PhysicalSpace ι n Z m M N d :=
  ODECoordinateNativeControl.physicalOracle
    (A := SourceBasis ι n m) (B := MatrixBasis ι n Z m M N d)
    (H := SourceSpace ι n m) (K := MatrixSpace ι n Z m M N d) (X := X) (L := Query)
    (sourceLayout (ι := ι) (n := n) m)
    (matrixLayout (ι := ι) (n := n) (Z := Z) m M N d)
    (matrixOracle (ι := ι) D m N d)
    (sourceFamily (ι := ι) Pw J φ)

omit [DecidableEq ι] [DecidableEq Z] in
/-- Unitarity holds on the entire primitive workspace. -/
theorem physicalOracle_unitary (D : Data (X × Fin M) n Z s) (m N d : ℕ)
    (Pw : X → Weights.LabelOp (Option (Fin m))) (hPw : ∀ x, IsUnitary (Pw x))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ : ∀ x a, IsUnitary (J x a)) (φ : Option (Fin m) → ℂ) (hφ : ∀ a, ‖φ a‖ = 1) :
    ∀ l x, IsUnitary (physicalOracle (ι := ι) D m N d Pw J φ l x) :=
  ODECoordinateNativeControl.physicalOracle_unitary
    (A := SourceBasis ι n m) (B := MatrixBasis ι n Z m M N d)
    (H := SourceSpace ι n m) (K := MatrixSpace ι n Z m M N d) (X := X) (L := Query)
    (sourceLayout (ι := ι) (n := n) m)
    (matrixLayout (ι := ι) (n := n) (Z := Z) m M N d)
    (matrixOracle (ι := ι) D m N d)
    (sourceFamily (ι := ι) Pw J φ) (matrixOracle_unitary (ι := ι) D m N d)
    (Compiled.sourceFamily_unitary hPw hJ hφ)

/-- The compiled public trial family. Its SELECT program, source interfaces, public phases,
encoding, LCHS coefficients and seed are public data; proofs only justify the fixed reflections. -/
def publicTrials (D : Data (X × Fin M) n Z s) (hM : 0 < M) (i0 : ι) (m N d : ℕ)
    (p : MultiOracleCircuit.Program (matrixOracle (ι := ι) D m N d))
    (Pw : X → Weights.LabelOp (Option (Fin m)))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (φ : Option (Fin m) → ℂ)
    (E : SourceSpace ι n m →L[ℂ] MatrixSpace ι n Z m M N d) (hE : E† ∘L E = 1)
    (c : ι → ℂ) (seed : EuclideanSpace ℂ n)
    (hSeed : ‖ODECompiledSource.seed E (Compiled.seedCoefficients c) seed‖ = 1)
    (hOutput : (ODECompiledSource.output E (Compiled.seedCoefficients c))† ∘L
      ODECompiledSource.output E (Compiled.seedCoefficients c) = 1) :
    ℕ → MultiOracleCircuit.Program (physicalOracle (ι := ι) D m N d Pw J φ) :=
  fun j => ODECoordinateNativeControl.compile
    (A := SourceBasis ι n m) (B := MatrixBasis ι n Z m M N d)
    (H := SourceSpace ι n m) (K := MatrixSpace ι n Z m M N d) (X := X) (L := Query)
    (sourceLayout (ι := ι) (n := n) m)
    (matrixLayout (ι := ι) (n := n) (Z := Z) m M N d)
    (matrixOracle (ι := ι) D m N d) (sourceFamily (ι := ι) Pw J φ)
    (sourceBasis D i0 m) (matrixBasis D hM i0 m N d)
    (Compiled.publicLogicalTrials p Pw J φ E hE c seed hSeed hOutput j)

/-- Every source certificate for the actual source vectors gives the released primitive trial
certificate for the public trial family. -/
theorem trial_certificate (D : Data (X × Fin M) n Z s) (hM : 0 < M)
    (i0 : ι) (m N d : ℕ)
    (p : MultiOracleCircuit.Program (matrixOracle (ι := ι) D m N d))
    (Pw : X → Weights.LabelOp (Option (Fin m))) (hPw : ∀ x, IsUnitary (Pw x))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ : ∀ x a, IsUnitary (J x a)) (φ : Option (Fin m) → ℂ) (hφ : ∀ a, ‖φ a‖ = 1)
    (E : SourceSpace ι n m →L[ℂ] MatrixSpace ι n Z m M N d) (hE : E† ∘L E = 1)
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
      (publicTrials D hM i0 m N d p Pw J φ E hE c seed hSeedUnit hOutput)
      (ODEGroverAverage.chosenIterations g)
      (input D hM i0 m N d (ODECompiledSource.seed E (Compiled.seedCoefficients c) seed))
      (input D hM i0 m N d ∘L ODECompiledSource.output E (Compiled.seedCoefficients c))
      x target (s : ℝ) Θ ell g (ε / 500) :=
  Compiled.public_source_certificate p (matrixOracle_unitary (ι := ι) D m N d)
    Pw hPw J hJ φ hφ E hE z c hc seed target hSeed (s : ℝ) Θ ell g ε hg x hz hW hCert hq
    (sourceLayout (ι := ι) (n := n) m)
    (matrixLayout (ι := ι) (n := n) (Z := Z) m M N d)
    (sourceBasis D i0 m) (matrixBasis D hM i0 m N d)
    (matrixImage D hM i0 m N d) (matrix_valid D hM i0 m N d) hSeedUnit hOutput

/-- The public seed on the primitive workspace is a unit vector. -/
theorem seed_unit (D : Data (X × Fin M) n Z s) (hM : 0 < M) (i0 : ι) (m N d : ℕ)
    (E : SourceSpace ι n m →L[ℂ] MatrixSpace ι n Z m M N d) (hE : E† ∘L E = 1)
    (c : ι → ℂ) (hc : 0 < ODECoherentLCU.coefficientMass c)
    (seed : EuclideanSpace ℂ n) (hSeed : ‖seed‖ = 1) :
    ‖input D hM i0 m N d (ODECompiledSource.seed E (Compiled.seedCoefficients c) seed)‖ =
      1 := by
  have hsc : 0 < ODECoherentLCU.coefficientMass (Compiled.seedCoefficients (N := m) c) := by
    rw [Compiled.seedCoefficients_mass]
    exact hc
  rw [(input D hM i0 m N d).norm_map_iff_adjoint_comp_self.mpr (input_isometry D hM i0 m N d)]
  exact ODECompiledSource.seed_unit E _ hE hsc seed hSeed

/-- The public output flag on the primitive workspace is an isometry. -/
theorem output_isometry (D : Data (X × Fin M) n Z s) (hM : 0 < M) (i0 : ι) (m N d : ℕ)
    (E : SourceSpace ι n m →L[ℂ] MatrixSpace ι n Z m M N d) (hE : E† ∘L E = 1)
    (c : ι → ℂ) (hc : 0 < ODECoherentLCU.coefficientMass c) :
    (input D hM i0 m N d ∘L ODECompiledSource.output E (Compiled.seedCoefficients c))† ∘L
      (input D hM i0 m N d ∘L ODECompiledSource.output E (Compiled.seedCoefficients c)) =
        1 := by
  have hsc : 0 < ODECoherentLCU.coefficientMass (Compiled.seedCoefficients (N := m) c) := by
    rw [Compiled.seedCoefficients_mass]
    exact hc
  exact NativeSparseAttenuation.isometry_comp _ _
    (ODECompiledSource.output_isometry E _ hE hsc) (input_isometry D hM i0 m N d)

end

end SparseHamiltonian.GeneralSourceExtensions.MeshNative
