import SparseODE.ODEPrimitiveSourceJoinContinuation2

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
/-- The primitive sparse-access compiler preserves equality of the logical
families. No evaluation of a large circuit is needed for this argument. -/
theorem trials_input_independent (D : Data X n Z s) (i0 : ι) (N T d : ℕ)
    (p : MultiOracleCircuit.Program (matrixOracle (ι := ι) D N T d))
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ₀ : ∀ x, IsUnitary (J₀ x)) (hJb : ∀ x, IsUnitary (Jb x))
    (E : SourceSpace ι n N →L[ℂ] MatrixSpace ι n Z N T d) (hE : E† ∘L E = 1)
    (z : Option (Fin N) → EuclideanSpace ℂ n) (c : ι → ℂ)
    (v target₁ target₂ : EuclideanSpace ℂ n) (g ε : ℝ) (x₁ x₂ : X)
    (hCert₁ : ODEActualSourceError.Certificate E z c
      (ODESourcePreparations.branch (J₀ x₁) (Jb x₁) N)
      (p.eval x₁) v target₁ g ε)
    (hCert₂ : ODEActualSourceError.Certificate E z c
      (ODESourcePreparations.branch (J₀ x₂) (Jb x₂) N)
      (p.eval x₂) v target₂ g ε) :
    trials D i0 N T d p J₀ Jb hJ₀ hJb E hE z c v target₁ g ε x₁ hCert₁ =
      trials D i0 N T d p J₀ Jb hJ₀ hJb E hE z c v target₂ g ε x₂ hCert₂ := by
  have hLogical := ODEPrimitiveSourceJoin.logicalTrials_input_independent
    (ι := ι) (P := EuclideanSpace ℂ n) (K := MatrixSpace ι n Z N T d)
    (X := X) (L := Query) (N := N) (O := matrixOracle (ι := ι) D N T d)
    p (matrixOracle_unitary (ι := ι) D N T d) J₀ Jb hJ₀ hJb E hE
    z c v target₁ target₂ g ε x₁ x₂ hCert₁ hCert₂
  let compileFamily :
      (ℕ → MultiOracleCircuit.Program (logicalOracle (ι := ι) D N T d J₀ Jb)) →
      (ℕ → MultiOracleCircuit.Program (physicalOracle (ι := ι) D N T d J₀ Jb)) :=
    fun q j => compile D i0 N T d J₀ Jb (q j)
  exact congrArg compileFamily hLogical

end
end SparseHamiltonian.ODEFinalNativeSource
