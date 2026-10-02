import SparseODE.ODEPrimitiveSourceJoinContinuation3

namespace SparseHamiltonian.ODEFinalNativeSource

noncomputable section
open ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding
open scoped InnerProduct

variable {ι X n Z : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z] [DecidableEq Z]
  {s : ℕ}

set_option maxRecDepth 4096 in
set_option synthInstance.maxSize 2048 in
set_option maxHeartbeats 2000000 in
/-- Compile the explicitly public logical family to the original sparse
matrix and supplied source interfaces. -/
def publicTrials (D : Data X n Z s) (i0 : ι) (N T d : ℕ)
    (p : MultiOracleCircuit.Program (matrixOracle (ι := ι) D N T d))
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (E : SourceSpace ι n N →L[ℂ] MatrixSpace ι n Z N T d) (hE : E† ∘L E = 1)
    (coeff : Option (Fin N) × ι → ℂ) (v : EuclideanSpace ℂ n)
    (hSeed : ‖ODECompiledSource.seed E coeff v‖ = 1)
    (hOutput : (ODECompiledSource.output E coeff)† ∘L
      ODECompiledSource.output E coeff = 1) :
    ℕ → MultiOracleCircuit.Program (physicalOracle (ι := ι) D N T d J₀ Jb) :=
  fun j => compile D i0 N T d J₀ Jb
    (ODEPrimitiveSourceJoin.publicLogicalTrials p J₀ Jb E hE coeff v hSeed hOutput j)

set_option maxRecDepth 4096 in
set_option synthInstance.maxSize 2048 in
set_option maxHeartbeats 2000000 in
/-- Compiler congruence transports the small logical constructor equality.
No physical circuit expansion is used. -/
theorem trials_eq_publicTrials (D : Data X n Z s) (i0 : ι) (N T d : ℕ)
    (p : MultiOracleCircuit.Program (matrixOracle (ι := ι) D N T d))
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ₀ : ∀ x, IsUnitary (J₀ x)) (hJb : ∀ x, IsUnitary (Jb x))
    (E : SourceSpace ι n N →L[ℂ] MatrixSpace ι n Z N T d) (hE : E† ∘L E = 1)
    (z : Option (Fin N) → EuclideanSpace ℂ n) (c : ι → ℂ)
    (v target : EuclideanSpace ℂ n) (g ε : ℝ) (x : X)
    (hCert : ODEActualSourceError.Certificate E z c
      (ODESourcePreparations.branch (J₀ x) (Jb x) N)
      (p.eval x) v target g ε)
    (coeff : Option (Fin N) × ι → ℂ)
    (hCoefficients : ODEActualSourceError.coefficients z c = coeff)
    (hSeed : ‖ODECompiledSource.seed E coeff v‖ = 1)
    (hOutput : (ODECompiledSource.output E coeff)† ∘L
      ODECompiledSource.output E coeff = 1) :
    trials D i0 N T d p J₀ Jb hJ₀ hJb E hE z c v target g ε x hCert =
      publicTrials D i0 N T d p J₀ Jb E hE coeff v hSeed hOutput := by
  have hLogical := ODEPrimitiveSourceJoin.logicalTrials_eq_publicLogicalTrials
    (ι := ι) (P := EuclideanSpace ℂ n) (K := MatrixSpace ι n Z N T d)
    (X := X) (L := Query) (N := N) (O := matrixOracle (ι := ι) D N T d)
    p (matrixOracle_unitary (ι := ι) D N T d) J₀ Jb hJ₀ hJb E hE
    z c v target g ε x hCert coeff hCoefficients hSeed hOutput
  let compileFamily :
      (ℕ → MultiOracleCircuit.Program (logicalOracle (ι := ι) D N T d J₀ Jb)) →
      (ℕ → MultiOracleCircuit.Program (physicalOracle (ι := ι) D N T d J₀ Jb)) :=
    fun q j => compile D i0 N T d J₀ Jb (q j)
  exact congrArg compileFamily hLogical

set_option maxRecDepth 4096 in
set_option synthInstance.maxSize 2048 in
/-- The physical initial state uses the same public coefficient function. -/
theorem seed_eq_of_coefficients (D : Data X n Z s) (i0 : ι) (N T d : ℕ)
    (E : SourceSpace ι n N →L[ℂ] MatrixSpace ι n Z N T d)
    (z : Option (Fin N) → EuclideanSpace ℂ n) (c : ι → ℂ)
    (v : EuclideanSpace ℂ n) (coeff : Option (Fin N) × ι → ℂ)
    (hCoefficients : ODEActualSourceError.coefficients z c = coeff) :
    seed D i0 N T d E z c v =
      input D i0 N T d (ODECompiledSource.seed E coeff v) := by
  exact congrArg
    (fun d' : Option (Fin N) × ι → ℂ =>
      input D i0 N T d (ODECompiledSource.seed E d' v)) hCoefficients

set_option maxRecDepth 4096 in
set_option synthInstance.maxSize 2048 in
/-- The physical output embedding uses the same public coefficient function. -/
theorem output_eq_of_coefficients (D : Data X n Z s) (i0 : ι) (N T d : ℕ)
    (E : SourceSpace ι n N →L[ℂ] MatrixSpace ι n Z N T d)
    (z : Option (Fin N) → EuclideanSpace ℂ n) (c : ι → ℂ)
    (coeff : Option (Fin N) × ι → ℂ)
    (hCoefficients : ODEActualSourceError.coefficients z c = coeff) :
    output D i0 N T d E z c =
      input D i0 N T d ∘L ODECompiledSource.output E coeff := by
  exact congrArg
    (fun d' : Option (Fin N) × ι → ℂ =>
      input D i0 N T d ∘L ODECompiledSource.output E d') hCoefficients

end
end SparseHamiltonian.ODEFinalNativeSource
