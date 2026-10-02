import SparseODE.ODEPrimitiveSourceJoin

/-!
# Native coordinates for source-loaded ODE circuits

The source branch and the final native simulator have explicit computational
coordinates. Their common reference inputs are public: the source reference
uses the initial branch and the first known sparse slot. The matrix reference
and its exact basis image are supplied by the original sparse access data.
Thus no controlled unknown matrix oracle or additional validity promise is
needed when compiling the source-loaded preparation and its Grover trials.

-/

namespace SparseHamiltonian.ODEFinalNativeSource

noncomputable section
open ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding
open scoped InnerProduct BigOperators
set_option maxRecDepth 4096
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 2000000

variable {ι X n Z : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z] [DecidableEq Z]
  {s : ℕ}

abbrev SourceBasis (ι n : Type*) (N : ℕ) := (Option (Fin N) × ι) × n

abbrev SourceSpace (ι n : Type*) [Fintype ι] [Fintype n] (N : ℕ) :=
  ODECompiledSource.Branch ι (EuclideanSpace ℂ n) N

abbrev MatrixBasis (ι n Z : Type*) (N T d : ℕ) :=
  ODEFinalNativeBasis.Basis (Option (Fin N) × ι) n Z T d

abbrev MatrixSpace (ι n Z : Type*) [Fintype ι] [Fintype n] [Fintype Z]
    (N T d : ℕ) :=
  ODEFinalNativeBasis.Physical (Option (Fin N) × ι) n Z T d

abbrev Logical (ι n Z : Type*) [Fintype ι] [Fintype n] [Fintype Z]
    (N T d : ℕ) :=
  ODESourceTransport.Space (SourceSpace ι n N) (MatrixSpace ι n Z N T d)

abbrev Physical (ι n Z : Type*) [Fintype ι] [Fintype n] [Fintype Z]
    (N T d : ℕ) :=
  ODESectorTensor.Physical (SourceBasis ι n N) (MatrixBasis ι n Z N T d)

def sourceLayout (N : ℕ) :
    SourceSpace ι n N ≃ₗᵢ[ℂ] EuclideanSpace ℂ (SourceBasis ι n N) :=
  ODEFinalNativeBasis.sourceLayout (σ := Option (Fin N)) (ι := ι) (n := n)

def matrixLayout (N T d : ℕ) :
    MatrixSpace ι n Z N T d ≃ₗᵢ[ℂ] EuclideanSpace ℂ (MatrixBasis ι n Z N T d) :=
  ODEFinalNativeBasis.layout (ι := Option (Fin N) × ι) (n := n) (Z := Z) T d

/-- The source/LCHS label is a spectator of the original sparse primitives. -/
abbrev matrixOracle (D : Data X n Z s) (N T d : ℕ) :
    Query → X → MatrixSpace ι n Z N T d →L[ℂ] MatrixSpace ι n Z N T d :=
  AlignedMultiOracleProgram.oracle
    (ODEJointNative.oracle (ι := Option (Fin N) × ι) D T d)

omit [DecidableEq ι] [DecidableEq Z] in
theorem matrixOracle_unitary (D : Data X n Z s) (N T d : ℕ) :
    ∀ l x, IsUnitary (matrixOracle (ι := ι) D N T d l x) :=
  CoherentQuerySchedule.oracle_unitary
    (ODEJointNative.oracle (ι := Option (Fin N) × ι) D T d)
    (ODEJointNative.oracle_unitary (ι := Option (Fin N) × ι) D T d)

/-- A public basis index is already present in the nonempty sparse slot list. -/
def sourceBasis (D : Data X n Z s) (i0 : ι) (N : ℕ) : SourceBasis ι n N :=
  ((none, i0), D.slot ⟨0, D.slots_pos⟩)

def matrixBasis (D : Data X n Z s) (i0 : ι) (N T d : ℕ) :
    MatrixBasis ι n Z N T d :=
  ODEFinalNativeBasis.cleanBasis D (none, i0) T d

def matrixImage (D : Data X n Z s) (i0 : ι) (N T d : ℕ) :
    Query → X → MatrixBasis ι n Z N T d :=
  ODEFinalNativeBasis.image D (none, i0) T d

/-- The native basis-image control promise is derived, not assumed. -/
theorem matrix_valid (D : Data X n Z s) (i0 : ι) (N T d : ℕ) (l : Query) (x : X) :
    (matrixLayout (ι := ι) (n := n) (Z := Z) N T d).conjStarAlgEquiv
        (matrixOracle D N T d l x) (EuclideanSpace.single (matrixBasis D i0 N T d) 1) =
      EuclideanSpace.single (matrixImage D i0 N T d l x) 1 :=
  ODEFinalNativeBasis.valid D (none, i0) T d l x

/-- One fixed encoding serves every source-loaded preparation and trial. -/
def input (D : Data X n Z s) (i0 : ι) (N T d : ℕ) :
    Logical ι n Z N T d →L[ℂ] Physical ι n Z N T d :=
  ODECoordinateNativeControl.input
    (A := SourceBasis ι n N) (B := MatrixBasis ι n Z N T d)
    (H := SourceSpace ι n N) (K := MatrixSpace ι n Z N T d)
    (sourceLayout (ι := ι) (n := n) N)
    (matrixLayout (ι := ι) (n := n) (Z := Z) N T d)
    (sourceBasis D i0 N) (matrixBasis D i0 N T d)

theorem input_isometry (D : Data X n Z s) (i0 : ι) (N T d : ℕ) :
    (input D i0 N T d)† ∘L input D i0 N T d = 1 := by
  unfold input
  exact ODECoordinateNativeControl.input_isometry
    (A := SourceBasis ι n N) (B := MatrixBasis ι n Z N T d)
    (H := SourceSpace ι n N) (K := MatrixSpace ι n Z N T d)
    (sourceLayout (ι := ι) (n := n) N)
    (matrixLayout (ι := ι) (n := n) (Z := Z) N T d)
    (sourceBasis D i0 N) (matrixBasis D i0 N T d)

abbrev sourceFamily (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (N : ℕ) : Bool → X → SourceSpace ι n N →L[ℂ] SourceSpace ι n N :=
  ODEPrimitiveSourceJoin.sourceFamily (ι := ι) J₀ Jb N

abbrev logicalOracle (D : Data X n Z s) (N T d : ℕ)
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) :
    Query ⊕ Bool → X → Logical ι n Z N T d →L[ℂ] Logical ι n Z N T d :=
  ODESectorCoordinates.oracle (matrixOracle (ι := ι) D N T d)
    (sourceFamily (ι := ι) J₀ Jb N)

/-- These are ordinary original matrix calls with fixed spectators, together
with the two supplied source interfaces. -/
abbrev physicalOracle (D : Data X n Z s) (N T d : ℕ)
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) :
    Query ⊕ Bool → X → Physical ι n Z N T d →L[ℂ] Physical ι n Z N T d :=
  ODECoordinateNativeControl.physicalOracle
    (A := SourceBasis ι n N) (B := MatrixBasis ι n Z N T d)
    (H := SourceSpace ι n N) (K := MatrixSpace ι n Z N T d) (X := X) (L := Query)
    (sourceLayout (ι := ι) (n := n) N)
    (matrixLayout (ι := ι) (n := n) (Z := Z) N T d)
    (matrixOracle (ι := ι) D N T d)
    (sourceFamily (ι := ι) J₀ Jb N)

omit [DecidableEq ι] [DecidableEq Z] in
/-- Unitarity holds on the entire primitive workspace, including inputs
outside the clean sector used in the correctness proof. -/
theorem physicalOracle_unitary (D : Data X n Z s) (N T d : ℕ)
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ₀ : ∀ x, IsUnitary (J₀ x)) (hJb : ∀ x, IsUnitary (Jb x)) :
    ∀ l x, IsUnitary (physicalOracle (ι := ι) D N T d J₀ Jb l x) :=
  ODECoordinateNativeControl.physicalOracle_unitary
    (A := SourceBasis ι n N) (B := MatrixBasis ι n Z N T d)
    (H := SourceSpace ι n N) (K := MatrixSpace ι n Z N T d) (X := X) (L := Query)
    (sourceLayout (ι := ι) (n := n) N)
    (matrixLayout (ι := ι) (n := n) (Z := Z) N T d)
    (matrixOracle (ι := ι) D N T d)
    (sourceFamily (ι := ι) J₀ Jb N) (matrixOracle_unitary (ι := ι) D N T d)
    (ODEPrimitiveSourceJoin.sourceFamily_unitary (ι := ι) J₀ Jb N hJ₀ hJb)

/-- Compile on the original source-loading space, with the public reference
states fixed by the original sparse data. -/
def compile (D : Data X n Z s) (i0 : ι) (N T d : ℕ)
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (q : MultiOracleCircuit.Program (logicalOracle (ι := ι) D N T d J₀ Jb)) :
    MultiOracleCircuit.Program (physicalOracle (ι := ι) D N T d J₀ Jb) :=
  ODECoordinateNativeControl.compile
    (A := SourceBasis ι n N) (B := MatrixBasis ι n Z N T d)
    (H := SourceSpace ι n N) (K := MatrixSpace ι n Z N T d) (X := X) (L := Query)
    (sourceLayout (ι := ι) (n := n) N)
    (matrixLayout (ι := ι) (n := n) (Z := Z) N T d)
    (matrixOracle (ι := ι) D N T d) (sourceFamily (ι := ι) J₀ Jb N)
    (sourceBasis D i0 N) (matrixBasis D i0 N T d) q

theorem compile_eval (D : Data X n Z s) (i0 : ι) (N T d : ℕ)
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ₀ : ∀ x, IsUnitary (J₀ x)) (hJb : ∀ x, IsUnitary (Jb x))
    (q : MultiOracleCircuit.Program (logicalOracle (ι := ι) D N T d J₀ Jb)) (x : X) :
    (compile D i0 N T d J₀ Jb q).eval x ∘L input D i0 N T d =
      input D i0 N T d ∘L q.eval x :=
  ODECoordinateNativeControl.compile_eval
    (A := SourceBasis ι n N) (B := MatrixBasis ι n Z N T d)
    (H := SourceSpace ι n N) (K := MatrixSpace ι n Z N T d) (X := X) (L := Query)
    (sourceLayout (ι := ι) (n := n) N)
    (matrixLayout (ι := ι) (n := n) (Z := Z) N T d)
    (matrixOracle (ι := ι) D N T d) (sourceFamily (ι := ι) J₀ Jb N)
    (matrixOracle_unitary (ι := ι) D N T d) (ODEPrimitiveSourceJoin.sourceFamily_unitary (ι := ι) J₀ Jb N hJ₀ hJb)
    (sourceBasis D i0 N) (matrixBasis D i0 N T d)
    (matrixImage D i0 N T d) (matrix_valid D i0 N T d) q x

theorem compile_matrix_cost (D : Data X n Z s) (i0 : ι) (N T d : ℕ)
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (q : MultiOracleCircuit.Program (logicalOracle (ι := ι) D N T d J₀ Jb))
    (w : Query → ℕ) :
    (compile D i0 N T d J₀ Jb q).cost (ODESourceQueryBudget.matrixWeight w) =
      3 * q.cost (ODESourceQueryBudget.matrixWeight w) :=
  ODECoordinateNativeControl.compile_matrix_cost
    (A := SourceBasis ι n N) (B := MatrixBasis ι n Z N T d)
    (H := SourceSpace ι n N) (K := MatrixSpace ι n Z N T d) (X := X) (L := Query)
    (sourceLayout (ι := ι) (n := n) N)
    (matrixLayout (ι := ι) (n := n) (Z := Z) N T d)
    (matrixOracle (ι := ι) D N T d) (sourceFamily (ι := ι) J₀ Jb N)
    (sourceBasis D i0 N) (matrixBasis D i0 N T d) q w

theorem compile_source_cost (D : Data X n Z s) (i0 : ι) (N T d : ℕ)
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (q : MultiOracleCircuit.Program (logicalOracle (ι := ι) D N T d J₀ Jb)) (b : Bool) :
    (compile D i0 N T d J₀ Jb q).cost (ODESourceQueryBudget.sourceWeight b) =
      q.cost (ODESourceQueryBudget.sourceWeight b) :=
  ODECoordinateNativeControl.compile_source_cost
    (A := SourceBasis ι n N) (B := MatrixBasis ι n Z N T d)
    (H := SourceSpace ι n N) (K := MatrixSpace ι n Z N T d) (X := X) (L := Query)
    (sourceLayout (ι := ι) (n := n) N)
    (matrixLayout (ι := ι) (n := n) (Z := Z) N T d)
    (matrixOracle (ι := ι) D N T d) (sourceFamily (ι := ι) J₀ Jb N)
    (sourceBasis D i0 N) (matrixBasis D i0 N T d) q b

theorem compile_source_total_cost (D : Data X n Z s) (i0 : ι) (N T d : ℕ)
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (q : MultiOracleCircuit.Program (logicalOracle (ι := ι) D N T d J₀ Jb)) :
    (compile D i0 N T d J₀ Jb q).cost ODESourceQueryBudget.sourceTotalWeight =
      q.cost ODESourceQueryBudget.sourceTotalWeight :=
  ODECoordinateNativeControl.compile_source_total_cost
    (A := SourceBasis ι n N) (B := MatrixBasis ι n Z N T d)
    (H := SourceSpace ι n N) (K := MatrixSpace ι n Z N T d) (X := X) (L := Query)
    (sourceLayout (ι := ι) (n := n) N)
    (matrixLayout (ι := ι) (n := n) (Z := Z) N T d)
    (matrixOracle (ι := ι) D N T d) (sourceFamily (ι := ι) J₀ Jb N)
    (sourceBasis D i0 N) (matrixBasis D i0 N T d) q

/-- The actual two-source preparation, followed by the primitive compiler. -/
def preparation (D : Data X n Z s) (i0 : ι) (N T d : ℕ)
    (p : MultiOracleCircuit.Program (matrixOracle (ι := ι) D N T d))
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (E : SourceSpace ι n N →L[ℂ] MatrixSpace ι n Z N T d) (hE : E† ∘L E = 1) :
    MultiOracleCircuit.Program (physicalOracle (ι := ι) D N T d J₀ Jb) :=
  compile D i0 N T d J₀ Jb (ODECompiledSource.program p J₀ Jb E hE)

/-- The compiled circuit loads the actual unknown sources and then applies
the native SELECT program. All additional references return to the same clean
encoding. This is an exact state identity, independent of analytic error bounds. -/
theorem preparation_state (D : Data X n Z s) (i0 : ι) (N T d : ℕ)
    (p : MultiOracleCircuit.Program (matrixOracle (ι := ι) D N T d))
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ₀ : ∀ x, IsUnitary (J₀ x)) (hJb : ∀ x, IsUnitary (Jb x))
    (E : SourceSpace ι n N →L[ℂ] MatrixSpace ι n Z N T d) (hE : E† ∘L E = 1)
    (c : Option (Fin N) × ι → ℂ) (v : EuclideanSpace ℂ n) (x : X) :
    (preparation D i0 N T d p J₀ Jb E hE).eval x
        (input D i0 N T d (ODECompiledSource.seed E c v)) =
      input D i0 N T d (ODESourceTransport.matrixEmbedding
        (p.eval x (ODEJointSourceLCU.input E c
          (fun a => ODESourcePreparations.branch (J₀ x) (Jb x) N a.1) v))) := by
  have hCompile := congrArg
    (fun U : Logical ι n Z N T d →L[ℂ] Physical ι n Z N T d =>
      U (ODECompiledSource.seed E c v))
    (compile_eval D i0 N T d J₀ Jb hJ₀ hJb
      (ODECompiledSource.program p J₀ Jb E hE) x)
  calc
    _ = input D i0 N T d
        ((ODECompiledSource.program p J₀ Jb E hE).eval x
          (ODECompiledSource.seed E c v)) := hCompile
    _ = _ := congrArg (input D i0 N T d)
      (ODECompiledSource.program_state p (matrixOracle_unitary (ι := ι) D N T d)
        J₀ Jb E hE c v x)

theorem preparation_matrix_cost (D : Data X n Z s) (i0 : ι) (N T d : ℕ)
    (p : MultiOracleCircuit.Program (matrixOracle (ι := ι) D N T d))
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (E : SourceSpace ι n N →L[ℂ] MatrixSpace ι n Z N T d) (hE : E† ∘L E = 1)
    (w : Query → ℕ) :
    (preparation D i0 N T d p J₀ Jb E hE).cost (ODESourceQueryBudget.matrixWeight w) =
      3 * p.cost w :=
  (compile_matrix_cost D i0 N T d J₀ Jb (ODECompiledSource.program p J₀ Jb E hE) w).trans
    (congrArg (fun a : ℕ => 3 * a) (ODECompiledSource.program_matrix_cost p J₀ Jb E hE w))

theorem preparation_source_cost (D : Data X n Z s) (i0 : ι) (N T d : ℕ)
    (p : MultiOracleCircuit.Program (matrixOracle (ι := ι) D N T d))
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (E : SourceSpace ι n N →L[ℂ] MatrixSpace ι n Z N T d) (hE : E† ∘L E = 1)
    (b : Bool) :
    (preparation D i0 N T d p J₀ Jb E hE).cost (ODESourceQueryBudget.sourceWeight b) = 1 :=
  (compile_source_cost D i0 N T d J₀ Jb (ODECompiledSource.program p J₀ Jb E hE) b).trans
    (ODECompiledSource.program_source_cost p J₀ Jb E hE b)

theorem preparation_source_total_cost (D : Data X n Z s) (i0 : ι) (N T d : ℕ)
    (p : MultiOracleCircuit.Program (matrixOracle (ι := ι) D N T d))
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (E : SourceSpace ι n N →L[ℂ] MatrixSpace ι n Z N T d) (hE : E† ∘L E = 1) :
    (preparation D i0 N T d p J₀ Jb E hE).cost ODESourceQueryBudget.sourceTotalWeight = 2 :=
  (compile_source_total_cost D i0 N T d J₀ Jb (ODECompiledSource.program p J₀ Jb E hE)).trans
    (ODECompiledSource.program_source_total_cost p J₀ Jb E hE)

/-- The public coefficient state on the primitive compiler's fixed workspace. -/
def seed (D : Data X n Z s) (i0 : ι) (N T d : ℕ)
    (E : SourceSpace ι n N →L[ℂ] MatrixSpace ι n Z N T d)
    (z : Option (Fin N) → EuclideanSpace ℂ n) (c : ι → ℂ) (v : EuclideanSpace ℂ n) :
    Physical ι n Z N T d :=
  input D i0 N T d (ODECompiledSource.seed E (ODEActualSourceError.coefficients z c) v)

/-- The same clean output for every sampled amplification trial. -/
def output (D : Data X n Z s) (i0 : ι) (N T d : ℕ)
    (E : SourceSpace ι n N →L[ℂ] MatrixSpace ι n Z N T d)
    (z : Option (Fin N) → EuclideanSpace ℂ n) (c : ι → ℂ) :
    EuclideanSpace ℂ n →L[ℂ] Physical ι n Z N T d :=
  input D i0 N T d ∘L ODECompiledSource.output E (ODEActualSourceError.coefficients z c)

/-- The existing source-counted Grover family compiled to ordinary native
matrix queries. All proof arguments justify fixed gates and do not insert
input-dependent actions into the circuit. -/
def trials (D : Data X n Z s) (i0 : ι) (N T d : ℕ)
    (p : MultiOracleCircuit.Program (matrixOracle (ι := ι) D N T d))
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ₀ : ∀ x, IsUnitary (J₀ x)) (hJb : ∀ x, IsUnitary (Jb x))
    (E : SourceSpace ι n N →L[ℂ] MatrixSpace ι n Z N T d) (hE : E† ∘L E = 1)
    (z : Option (Fin N) → EuclideanSpace ℂ n) (c : ι → ℂ)
    (v target : EuclideanSpace ℂ n) (g ε : ℝ) (x : X)
    (hCert : ODEActualSourceError.Certificate E z c
      (ODESourcePreparations.branch (J₀ x) (Jb x) N) (p.eval x) v target g ε) :
    ℕ → MultiOracleCircuit.Program (physicalOracle (ι := ι) D N T d J₀ Jb) :=
  fun j => compile D i0 N T d J₀ Jb
    (ODEPrimitiveSourceJoin.logicalTrials
      (ι := ι) (P := EuclideanSpace ℂ n) (K := MatrixSpace ι n Z N T d)
      (X := X) (L := Query) (N := N) (O := matrixOracle (ι := ι) D N T d)
      p (matrixOracle_unitary (ι := ι) D N T d) J₀ Jb hJ₀ hJb E hE z c v target g ε x hCert j)

/-- A source-error certificate and native SELECT count now imply a complete
primitive-access trial certificate. Every control, reference-state and
single-letter implementation premise is discharged from the original data. -/
theorem primitive_source_certificate (D : Data X n Z s) (i0 : ι) (N T d : ℕ)
    (p : MultiOracleCircuit.Program (matrixOracle (ι := ι) D N T d))
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ₀ : ∀ x, IsUnitary (J₀ x)) (hJb : ∀ x, IsUnitary (Jb x))
    (E : SourceSpace ι n N →L[ℂ] MatrixSpace ι n Z N T d) (hE : E† ∘L E = 1)
    (z : Option (Fin N) → EuclideanSpace ℂ n) (c : ι → ℂ)
    (v target : EuclideanSpace ℂ n) (Θ ell g ε : ℝ) (hg : 1 ≤ g) (x : X)
    (hCert : ODEActualSourceError.Certificate E z c
      (ODESourcePreparations.branch (J₀ x) (Jb x) N) (p.eval x) v target g ε)
    (hq : (p.count : ℝ) ≤ 10616832 * ImprovedODEQueryBudget.queryShape (s : ℝ) Θ ell) :
    ODEPrimitiveSourceJoin.TrialCertificate
      (trials D i0 N T d p J₀ Jb hJ₀ hJb E hE z c v target g ε x hCert)
      (ODEGroverAverage.chosenIterations g) (seed D i0 N T d E z c v)
      (output D i0 N T d E z c) x target (s : ℝ) Θ ell g (ε / 500) :=
  ODEPrimitiveSourceJoin.primitive_source_certificate
    (ι := ι) (P := EuclideanSpace ℂ n) (K := MatrixSpace ι n Z N T d)
    (X := X) (L := Query) (N := N) (O := matrixOracle (ι := ι) D N T d)
    (A := SourceBasis ι n N) (B := MatrixBasis ι n Z N T d)
    p (matrixOracle_unitary (ι := ι) D N T d) J₀ Jb hJ₀ hJb E hE z c v target (s : ℝ) Θ ell g ε hg x hCert hq
    (sourceLayout (ι := ι) (n := n) N)
    (matrixLayout (ι := ι) (n := n) (Z := Z) N T d)
    (sourceBasis D i0 N) (matrixBasis D i0 N T d)
    (matrixImage D i0 N T d) (matrix_valid D i0 N T d)

end
end SparseHamiltonian.ODEFinalNativeSource
