import TimeDependentExtensions.ODE.Select
import TimeDependentODE.Native.Source

set_option autoImplicit false

/-!
# Native coordinates for the source-loaded circuits on `N` slots

The released source layer (`SparseHamiltonian.TimeDependentODE.NativeSource`) uses the
aligned SELECT workspace with as many slots as samples. Here the matrix register is the
aligned workspace of the SELECT on `N` slots (`MeshSelect.Workspace`): the source register,
the source interfaces and the time register of the coherent sampled-time oracle keep the `M`
samples, and only the clock register has `N` slots. Everything else is the released
construction: the public dummy input (initial source branch, a fixed LCHS label and the
first sample) with its phase-one basis transition derived from sparse access
(`matrix_valid`), the coordinate compiler of the source trials (`publicTrials`), and the
released primitive trial certificate (`coefficient_trial_certificate`).
-/

namespace TimeDependentExtensions

namespace MeshSource

noncomputable section

open SparseHamiltonian ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding
open SparseHamiltonian.TimeDependentODE (cleanBasis image valid cayleyOracle Physical Basis
  oracle oracle_unitary)
open SparseHamiltonian.TimeDependentODE.SourceTD (sourceFamily sourceFamily_unitary
  publicLogicalTrials branchTD primitive_source_certificate)
open SparseHamiltonian.TimeDependentODE.NativeSource (Label SourceBasis SourceSpace
  sourceLayout sourceBasis dummy)
open scoped InnerProduct BigOperators
set_option maxRecDepth 4096
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 2000000

variable {ι X n Z : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z] [DecidableEq Z]
  {s M : ℕ}

abbrev MatrixBasis (ι n Z : Type*) (M N d : ℕ) :=
  ODEFinalNativeBasis.AlignedBasis (ActiveRegisterLayout.Label PUnit.{1} N d)
    (Basis (Label ι M) n Z M)

/-- The aligned workspace of the coherent sampled-time SELECT on `N` slots. -/
abbrev MatrixSpace (ι n Z : Type*) [Fintype ι] [Fintype n] [Fintype Z] (M N d : ℕ) :=
  CleanOutputAlignment.Double (Physical (Label ι M) n Z M N d)

abbrev Logical (ι n Z : Type*) [Fintype ι] [Fintype n] [Fintype Z] (M N d : ℕ) :=
  ODESourceTransport.Space (SourceSpace ι n M) (MatrixSpace ι n Z M N d)

/-- The complete primitive workspace. -/
abbrev PhysicalSpace (ι n Z : Type*) [Fintype ι] [Fintype n] [Fintype Z] (M N d : ℕ) :=
  ODESectorTensor.Physical (SourceBasis ι n M) (MatrixBasis ι n Z M N d)

def matrixLayout (M N d : ℕ) :
    MatrixSpace ι n Z M N d ≃ₗᵢ[ℂ] EuclideanSpace ℂ (MatrixBasis ι n Z M N d) :=
  ODEFinalNativeBasis.alignedLayout (β := ActiveRegisterLayout.Label PUnit.{1} N d)
    (B := Basis (Label ι M) n Z M)

/-- Coherent sampled-time native queries with the alignment spectator. -/
abbrev matrixOracle (D : Data (X × Fin M) n Z s) (N d : ℕ) :
    Query → X → MatrixSpace ι n Z M N d →L[ℂ] MatrixSpace ι n Z M N d :=
  AlignedMultiOracleProgram.oracle (oracle (ι := Label ι M) D N d)

omit [DecidableEq ι] [DecidableEq Z] in
theorem matrixOracle_unitary (D : Data (X × Fin M) n Z s) (N d : ℕ) :
    ∀ l x, IsUnitary (matrixOracle (ι := ι) D N d l x) :=
  CoherentQuerySchedule.oracle_unitary (oracle (ι := Label ι M) D N d)
    (oracle_unitary (ι := Label ι M) D N d)

def matrixBasis (D : Data (X × Fin M) n Z s) (hM : 0 < M) (i0 : ι) (N d : ℕ) :
    MatrixBasis ι n Z M N d :=
  ODEFinalNativeBasis.alignedClean (ODEFinalNativeBasis.clockBasis N d)
    (cleanBasis D (dummy hM i0))

def matrixImage (D : Data (X × Fin M) n Z s) (hM : 0 < M) (i0 : ι) (N d : ℕ)
    (l : Query) (x : X) : MatrixBasis ι n Z M N d :=
  ODEFinalNativeBasis.alignedImage (ODEFinalNativeBasis.clockBasis N d)
    (cleanBasis D (dummy hM i0)) (image D (dummy hM i0) l x)

/-- The native basis-image control promise is derived from sparse access. -/
theorem matrix_valid (D : Data (X × Fin M) n Z s) (hM : 0 < M) (i0 : ι) (N d : ℕ)
    (l : Query) (x : X) :
    (matrixLayout (ι := ι) (n := n) (Z := Z) M N d).conjStarAlgEquiv
        (matrixOracle D N d l x) (EuclideanSpace.single (matrixBasis D hM i0 N d) 1) =
      EuclideanSpace.single (matrixImage D hM i0 N d l x) 1 :=
  ODEFinalNativeBasis.aligned_valid (β := ActiveRegisterLayout.Label PUnit.{1} N d)
    (cayleyOracle (ι := Label ι M) D) (ODEFinalNativeBasis.clockBasis N d)
    (cleanBasis D (dummy hM i0)) (image D (dummy hM i0)) (valid D (dummy hM i0)) l x

/-- One fixed encoding serves every source-loaded preparation and trial. -/
def input (D : Data (X × Fin M) n Z s) (hM : 0 < M) (i0 : ι) (N d : ℕ) :
    Logical ι n Z M N d →L[ℂ] PhysicalSpace ι n Z M N d :=
  ODECoordinateNativeControl.input
    (A := SourceBasis ι n M) (B := MatrixBasis ι n Z M N d)
    (H := SourceSpace ι n M) (K := MatrixSpace ι n Z M N d)
    (sourceLayout (ι := ι) (n := n) M)
    (matrixLayout (ι := ι) (n := n) (Z := Z) M N d)
    (sourceBasis D i0) (matrixBasis D hM i0 N d)

theorem input_isometry (D : Data (X × Fin M) n Z s) (hM : 0 < M) (i0 : ι) (N d : ℕ) :
    (input D hM i0 N d)† ∘L input D hM i0 N d = 1 := by
  unfold input
  exact ODECoordinateNativeControl.input_isometry
    (A := SourceBasis ι n M) (B := MatrixBasis ι n Z M N d)
    (H := SourceSpace ι n M) (K := MatrixSpace ι n Z M N d)
    (sourceLayout (ι := ι) (n := n) M)
    (matrixLayout (ι := ι) (n := n) (Z := Z) M N d)
    (sourceBasis D i0) (matrixBasis D hM i0 N d)

/-- Ordinary coherent sampled-time matrix calls with fixed spectators, together with the two
supplied source interfaces. -/
abbrev physicalOracle (D : Data (X × Fin M) n Z s) (N d : ℕ)
    (J₀ : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (Jb : X → Fin M → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) :
    Query ⊕ Bool → X → PhysicalSpace ι n Z M N d →L[ℂ] PhysicalSpace ι n Z M N d :=
  ODECoordinateNativeControl.physicalOracle
    (A := SourceBasis ι n M) (B := MatrixBasis ι n Z M N d)
    (H := SourceSpace ι n M) (K := MatrixSpace ι n Z M N d) (X := X) (L := Query)
    (sourceLayout (ι := ι) (n := n) M)
    (matrixLayout (ι := ι) (n := n) (Z := Z) M N d)
    (matrixOracle (ι := ι) D N d)
    (sourceFamily (ι := ι) J₀ Jb)

omit [DecidableEq ι] [DecidableEq Z] in
/-- Unitarity holds on the entire primitive workspace. -/
theorem physicalOracle_unitary (D : Data (X × Fin M) n Z s) (N d : ℕ)
    (J₀ : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (Jb : X → Fin M → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ₀ : ∀ x, IsUnitary (J₀ x)) (hJb : ∀ x q, IsUnitary (Jb x q)) :
    ∀ l x, IsUnitary (physicalOracle (ι := ι) D N d J₀ Jb l x) :=
  ODECoordinateNativeControl.physicalOracle_unitary
    (A := SourceBasis ι n M) (B := MatrixBasis ι n Z M N d)
    (H := SourceSpace ι n M) (K := MatrixSpace ι n Z M N d) (X := X) (L := Query)
    (sourceLayout (ι := ι) (n := n) M)
    (matrixLayout (ι := ι) (n := n) (Z := Z) M N d)
    (matrixOracle (ι := ι) D N d)
    (sourceFamily (ι := ι) J₀ Jb) (matrixOracle_unitary (ι := ι) D N d)
    (sourceFamily_unitary (ι := ι) J₀ Jb hJ₀ hJb)

/-- The compiled public trial family. Its SELECT program, source interfaces, encoding,
coefficients and seed are public data; proofs only justify the fixed reflections. -/
def publicTrials (D : Data (X × Fin M) n Z s) (hM : 0 < M) (i0 : ι) (N d : ℕ)
    (p : MultiOracleCircuit.Program (matrixOracle (ι := ι) D N d))
    (J₀ : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (Jb : X → Fin M → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (E : SourceSpace ι n M →L[ℂ] MatrixSpace ι n Z M N d) (hE : E† ∘L E = 1)
    (a : Option (Fin M) × ι → ℂ) (seed : EuclideanSpace ℂ n)
    (hSeed : ‖ODECompiledSource.seed E a seed‖ = 1)
    (hOutput : (ODECompiledSource.output E a)† ∘L ODECompiledSource.output E a = 1) :
    ℕ → MultiOracleCircuit.Program (physicalOracle (ι := ι) D N d J₀ Jb) :=
  fun j => ODECoordinateNativeControl.compile
    (A := SourceBasis ι n M) (B := MatrixBasis ι n Z M N d)
    (H := SourceSpace ι n M) (K := MatrixSpace ι n Z M N d) (X := X) (L := Query)
    (sourceLayout (ι := ι) (n := n) M)
    (matrixLayout (ι := ι) (n := n) (Z := Z) M N d)
    (matrixOracle (ι := ι) D N d) (sourceFamily (ι := ι) J₀ Jb)
    (sourceBasis D i0) (matrixBasis D hM i0 N d)
    (publicLogicalTrials p J₀ Jb E hE a seed hSeed hOutput j)

/-- Every source certificate whose actual coefficients equal the public ones gives the
released primitive trial certificate for the public trial family. -/
theorem coefficient_trial_certificate (D : Data (X × Fin M) n Z s) (hM : 0 < M)
    (i0 : ι) (N d : ℕ)
    (p : MultiOracleCircuit.Program (matrixOracle (ι := ι) D N d))
    (J₀ : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (Jb : X → Fin M → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ₀ : ∀ x, IsUnitary (J₀ x)) (hJb : ∀ x q, IsUnitary (Jb x q))
    (E : SourceSpace ι n M →L[ℂ] MatrixSpace ι n Z M N d) (hE : E† ∘L E = 1)
    (z : Option (Fin M) → EuclideanSpace ℂ n) (c : ι → ℂ)
    (seed target : EuclideanSpace ℂ n) (hSeed : ‖seed‖ = 1)
    (Θ ell g ε : ℝ) (hg : 1 ≤ g) (x : X)
    (hCert : ODEActualSourceError.Certificate E z c
      (branchTD (J₀ x) (Jb x)) (p.eval x) seed target g ε)
    (hq : (p.count : ℝ) ≤ 10616832 * ImprovedODEQueryBudget.queryShape (s : ℝ) Θ ell)
    (a : Option (Fin M) × ι → ℂ) (ha : 0 < ODECoherentLCU.coefficientMass a)
    (hCoeff : ODEActualSourceError.coefficients z c = a) :
    ODEPrimitiveSourceJoin.TrialCertificate
      (publicTrials D hM i0 N d p J₀ Jb E hE a seed
        (ODECompiledSource.seed_unit E a hE ha seed hSeed)
        (ODECompiledSource.output_isometry E a hE ha))
      (ODEGroverAverage.chosenIterations g)
      (input D hM i0 N d (ODECompiledSource.seed E a seed))
      (input D hM i0 N d ∘L ODECompiledSource.output E a)
      x target (s : ℝ) Θ ell g (ε / 500) := by
  subst hCoeff
  exact primitive_source_certificate p (matrixOracle_unitary (ι := ι) D N d)
    J₀ Jb hJ₀ hJb E hE z c seed target (s : ℝ) Θ ell g ε hg x hCert hq
    (sourceLayout (ι := ι) (n := n) M)
    (matrixLayout (ι := ι) (n := n) (Z := Z) M N d)
    (sourceBasis D i0) (matrixBasis D hM i0 N d)
    (matrixImage D hM i0 N d) (matrix_valid D hM i0 N d)

end

end MeshSource

end TimeDependentExtensions
