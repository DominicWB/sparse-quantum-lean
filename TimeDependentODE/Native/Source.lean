import TimeDependentODE.Native.Select
import TimeDependentODE.Source.Public
import SparseODE.ODEFinalNativeSource

/-!
# Native coordinates for the time-dependent source-loaded circuits

Time-dependent counterpart of `SparseHamiltonian.ODEFinalNativeSource`. The
source register keeps the released Cartesian coordinates. The matrix register
is the aligned workspace of the coherent sampled-time SELECT
(`Select.Workspace`), flattened by the released aligned layout
(`ODEFinalNativeBasis.alignedLayout`). Its public dummy input uses the initial
source branch, a fixed LCHS label and the first sample; the phase-one basis
transition of every primitive call is derived from sparse access
(`matrix_valid`), not assumed.

The time-dependent source trials of `SourceTD` are compiled to ordinary
native queries by the released coordinate compiler
(`ODECoordinateNativeControl.compile`). With public coefficients, the trial
family depends only on public data (`publicTrials`), and every pointwise
source certificate gives the released primitive trial certificate for that
same family (`coefficient_trial_certificate`).
-/

namespace SparseHamiltonian.TimeDependentODE.NativeSource

noncomputable section
open ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding
open scoped InnerProduct BigOperators
set_option maxRecDepth 4096
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 2000000

variable {ι X n Z : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z] [DecidableEq Z]
  {s M : ℕ}

/-- SELECT branch labels: a source label and an LCHS label. -/
abbrev Label (ι : Type*) (M : ℕ) := Option (Fin M) × ι

abbrev SourceBasis (ι n : Type*) (M : ℕ) := ODEFinalNativeSource.SourceBasis ι n M

abbrev SourceSpace (ι n : Type*) [Fintype ι] [Fintype n] (M : ℕ) :=
  ODEFinalNativeSource.SourceSpace ι n M

abbrev MatrixBasis (ι n Z : Type*) (M d : ℕ) :=
  ODEFinalNativeBasis.AlignedBasis (ActiveRegisterLayout.Label PUnit.{1} M d)
    (Basis (Label ι M) n Z M)

/-- The aligned workspace of the coherent sampled-time SELECT. -/
abbrev MatrixSpace (ι n Z : Type*) [Fintype ι] [Fintype n] [Fintype Z] (M d : ℕ) :=
  CleanOutputAlignment.Double (Physical (Label ι M) n Z M M d)

abbrev Logical (ι n Z : Type*) [Fintype ι] [Fintype n] [Fintype Z] (M d : ℕ) :=
  ODESourceTransport.Space (SourceSpace ι n M) (MatrixSpace ι n Z M d)

/-- The complete primitive workspace. -/
abbrev PhysicalSpace (ι n Z : Type*) [Fintype ι] [Fintype n] [Fintype Z] (M d : ℕ) :=
  ODESectorTensor.Physical (SourceBasis ι n M) (MatrixBasis ι n Z M d)

def sourceLayout (M : ℕ) :
    SourceSpace ι n M ≃ₗᵢ[ℂ] EuclideanSpace ℂ (SourceBasis ι n M) :=
  ODEFinalNativeSource.sourceLayout (ι := ι) (n := n) M

def matrixLayout (M d : ℕ) :
    MatrixSpace ι n Z M d ≃ₗᵢ[ℂ] EuclideanSpace ℂ (MatrixBasis ι n Z M d) :=
  ODEFinalNativeBasis.alignedLayout (β := ActiveRegisterLayout.Label PUnit.{1} M d)
    (B := Basis (Label ι M) n Z M)

/-- Coherent sampled-time native queries with the alignment spectator. -/
abbrev matrixOracle (D : Data (X × Fin M) n Z s) (d : ℕ) :
    Query → X → MatrixSpace ι n Z M d →L[ℂ] MatrixSpace ι n Z M d :=
  AlignedMultiOracleProgram.oracle (oracle (ι := Label ι M) D M d)

omit [DecidableEq ι] [DecidableEq Z] in
theorem matrixOracle_unitary (D : Data (X × Fin M) n Z s) (d : ℕ) :
    ∀ l x, IsUnitary (matrixOracle (ι := ι) D d l x) :=
  CoherentQuerySchedule.oracle_unitary (oracle (ι := Label ι M) D M d)
    (oracle_unitary (ι := Label ι M) D M d)

/-- The public source reference: initial branch, LCHS label `i0`, first sparse slot. -/
def sourceBasis (D : Data (X × Fin M) n Z s) (i0 : ι) : SourceBasis ι n M :=
  ((none, i0), D.slot ⟨0, D.slots_pos⟩)

/-- The public SELECT dummy address: initial branch, LCHS label `i0`, first sample. -/
def dummy (hM : 0 < M) (i0 : ι) : Label ι M × Fin M := ((none, i0), ⟨0, hM⟩)

def matrixBasis (D : Data (X × Fin M) n Z s) (hM : 0 < M) (i0 : ι) (d : ℕ) :
    MatrixBasis ι n Z M d :=
  ODEFinalNativeBasis.alignedClean (ODEFinalNativeBasis.clockBasis M d)
    (cleanBasis D (dummy hM i0))

def matrixImage (D : Data (X × Fin M) n Z s) (hM : 0 < M) (i0 : ι) (d : ℕ)
    (l : Query) (x : X) : MatrixBasis ι n Z M d :=
  ODEFinalNativeBasis.alignedImage (ODEFinalNativeBasis.clockBasis M d)
    (cleanBasis D (dummy hM i0)) (image D (dummy hM i0) l x)

/-- The native basis-image control promise is derived from sparse access. -/
theorem matrix_valid (D : Data (X × Fin M) n Z s) (hM : 0 < M) (i0 : ι) (d : ℕ)
    (l : Query) (x : X) :
    (matrixLayout (ι := ι) (n := n) (Z := Z) M d).conjStarAlgEquiv
        (matrixOracle D d l x) (EuclideanSpace.single (matrixBasis D hM i0 d) 1) =
      EuclideanSpace.single (matrixImage D hM i0 d l x) 1 :=
  ODEFinalNativeBasis.aligned_valid (β := ActiveRegisterLayout.Label PUnit.{1} M d)
    (cayleyOracle (ι := Label ι M) D) (ODEFinalNativeBasis.clockBasis M d)
    (cleanBasis D (dummy hM i0)) (image D (dummy hM i0)) (valid D (dummy hM i0)) l x

/-- One fixed encoding serves every source-loaded preparation and trial. -/
def input (D : Data (X × Fin M) n Z s) (hM : 0 < M) (i0 : ι) (d : ℕ) :
    Logical ι n Z M d →L[ℂ] PhysicalSpace ι n Z M d :=
  ODECoordinateNativeControl.input
    (A := SourceBasis ι n M) (B := MatrixBasis ι n Z M d)
    (H := SourceSpace ι n M) (K := MatrixSpace ι n Z M d)
    (sourceLayout (ι := ι) (n := n) M)
    (matrixLayout (ι := ι) (n := n) (Z := Z) M d)
    (sourceBasis D i0) (matrixBasis D hM i0 d)

theorem input_isometry (D : Data (X × Fin M) n Z s) (hM : 0 < M) (i0 : ι) (d : ℕ) :
    (input D hM i0 d)† ∘L input D hM i0 d = 1 := by
  unfold input
  exact ODECoordinateNativeControl.input_isometry
    (A := SourceBasis ι n M) (B := MatrixBasis ι n Z M d)
    (H := SourceSpace ι n M) (K := MatrixSpace ι n Z M d)
    (sourceLayout (ι := ι) (n := n) M)
    (matrixLayout (ι := ι) (n := n) (Z := Z) M d)
    (sourceBasis D i0) (matrixBasis D hM i0 d)

/-- The two supplied source interfaces; the forcing one is label dependent. -/
abbrev sourceFamily (J₀ : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (Jb : X → Fin M → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) :
    Bool → X → SourceSpace ι n M →L[ℂ] SourceSpace ι n M :=
  SourceTD.sourceFamily (ι := ι) J₀ Jb

/-- Ordinary coherent sampled-time matrix calls with fixed spectators,
together with the two supplied source interfaces. -/
abbrev physicalOracle (D : Data (X × Fin M) n Z s) (d : ℕ)
    (J₀ : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (Jb : X → Fin M → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) :
    Query ⊕ Bool → X → PhysicalSpace ι n Z M d →L[ℂ] PhysicalSpace ι n Z M d :=
  ODECoordinateNativeControl.physicalOracle
    (A := SourceBasis ι n M) (B := MatrixBasis ι n Z M d)
    (H := SourceSpace ι n M) (K := MatrixSpace ι n Z M d) (X := X) (L := Query)
    (sourceLayout (ι := ι) (n := n) M)
    (matrixLayout (ι := ι) (n := n) (Z := Z) M d)
    (matrixOracle (ι := ι) D d)
    (sourceFamily (ι := ι) J₀ Jb)

omit [DecidableEq ι] [DecidableEq Z] in
/-- Unitarity holds on the entire primitive workspace. -/
theorem physicalOracle_unitary (D : Data (X × Fin M) n Z s) (d : ℕ)
    (J₀ : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (Jb : X → Fin M → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ₀ : ∀ x, IsUnitary (J₀ x)) (hJb : ∀ x q, IsUnitary (Jb x q)) :
    ∀ l x, IsUnitary (physicalOracle (ι := ι) D d J₀ Jb l x) :=
  ODECoordinateNativeControl.physicalOracle_unitary
    (A := SourceBasis ι n M) (B := MatrixBasis ι n Z M d)
    (H := SourceSpace ι n M) (K := MatrixSpace ι n Z M d) (X := X) (L := Query)
    (sourceLayout (ι := ι) (n := n) M)
    (matrixLayout (ι := ι) (n := n) (Z := Z) M d)
    (matrixOracle (ι := ι) D d)
    (sourceFamily (ι := ι) J₀ Jb) (matrixOracle_unitary (ι := ι) D d)
    (SourceTD.sourceFamily_unitary (ι := ι) J₀ Jb hJ₀ hJb)

/-- The compiled public trial family. Its SELECT program, source interfaces,
encoding, coefficients and seed are public data; proofs only justify the
fixed reflections. -/
def publicTrials (D : Data (X × Fin M) n Z s) (hM : 0 < M) (i0 : ι) (d : ℕ)
    (p : MultiOracleCircuit.Program (matrixOracle (ι := ι) D d))
    (J₀ : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (Jb : X → Fin M → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (E : SourceSpace ι n M →L[ℂ] MatrixSpace ι n Z M d) (hE : E† ∘L E = 1)
    (a : Option (Fin M) × ι → ℂ) (seed : EuclideanSpace ℂ n)
    (hSeed : ‖ODECompiledSource.seed E a seed‖ = 1)
    (hOutput : (ODECompiledSource.output E a)† ∘L ODECompiledSource.output E a = 1) :
    ℕ → MultiOracleCircuit.Program (physicalOracle (ι := ι) D d J₀ Jb) :=
  fun j => ODECoordinateNativeControl.compile
    (A := SourceBasis ι n M) (B := MatrixBasis ι n Z M d)
    (H := SourceSpace ι n M) (K := MatrixSpace ι n Z M d) (X := X) (L := Query)
    (sourceLayout (ι := ι) (n := n) M)
    (matrixLayout (ι := ι) (n := n) (Z := Z) M d)
    (matrixOracle (ι := ι) D d) (sourceFamily (ι := ι) J₀ Jb)
    (sourceBasis D i0) (matrixBasis D hM i0 d)
    (SourceTD.publicLogicalTrials p J₀ Jb E hE a seed hSeed hOutput j)

/-- Every source certificate whose actual coefficients equal the public ones
gives the released primitive trial certificate for the public trial family. -/
theorem coefficient_trial_certificate (D : Data (X × Fin M) n Z s) (hM : 0 < M)
    (i0 : ι) (d : ℕ)
    (p : MultiOracleCircuit.Program (matrixOracle (ι := ι) D d))
    (J₀ : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (Jb : X → Fin M → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ₀ : ∀ x, IsUnitary (J₀ x)) (hJb : ∀ x q, IsUnitary (Jb x q))
    (E : SourceSpace ι n M →L[ℂ] MatrixSpace ι n Z M d) (hE : E† ∘L E = 1)
    (z : Option (Fin M) → EuclideanSpace ℂ n) (c : ι → ℂ)
    (seed target : EuclideanSpace ℂ n) (hSeed : ‖seed‖ = 1)
    (Θ ell g ε : ℝ) (hg : 1 ≤ g) (x : X)
    (hCert : ODEActualSourceError.Certificate E z c
      (SourceTD.branchTD (J₀ x) (Jb x)) (p.eval x) seed target g ε)
    (hq : (p.count : ℝ) ≤ 10616832 * ImprovedODEQueryBudget.queryShape (s : ℝ) Θ ell)
    (a : Option (Fin M) × ι → ℂ) (ha : 0 < ODECoherentLCU.coefficientMass a)
    (hCoeff : ODEActualSourceError.coefficients z c = a) :
    ODEPrimitiveSourceJoin.TrialCertificate
      (publicTrials D hM i0 d p J₀ Jb E hE a seed
        (ODECompiledSource.seed_unit E a hE ha seed hSeed)
        (ODECompiledSource.output_isometry E a hE ha))
      (ODEGroverAverage.chosenIterations g)
      (input D hM i0 d (ODECompiledSource.seed E a seed))
      (input D hM i0 d ∘L ODECompiledSource.output E a)
      x target (s : ℝ) Θ ell g (ε / 500) := by
  subst hCoeff
  exact SourceTD.primitive_source_certificate p (matrixOracle_unitary (ι := ι) D d)
    J₀ Jb hJ₀ hJb E hE z c seed target (s : ℝ) Θ ell g ε hg x hCert hq
    (sourceLayout (ι := ι) (n := n) M)
    (matrixLayout (ι := ι) (n := n) (Z := Z) M d)
    (sourceBasis D i0) (matrixBasis D hM i0 d)
    (matrixImage D hM i0 d) (matrix_valid D hM i0 d)

end

end SparseHamiltonian.TimeDependentODE.NativeSource
