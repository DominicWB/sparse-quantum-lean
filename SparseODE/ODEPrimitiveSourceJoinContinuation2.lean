import SparseODE.ODEPublicGaussianEndpointContinuation2

/-!
# Independence of the implemented trials from correctness witnesses

The unknown matrix input, target solution and source-error certificate enter
the trial constructors only through proofs. Their values do not change any
gate, oracle label or trial count. This is equality of circuit syntax, not
merely equality of the action on a selected state.

-/

namespace SparseHamiltonian.ODEPrimitiveSourceJoin

noncomputable section
open ContinuousLinearMap OracleCircuit
open scoped InnerProduct

variable {ι P K X L : Type*} [Fintype ι]
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {N : ℕ} {O : L → X → K →L[ℂ] K}

/-- Correctness certificates for different inputs and target vectors produce
the identical logical trial family. Only proof arguments differ. -/
theorem logicalTrials_input_independent (p : MultiOracleCircuit.Program O)
    (hO : ∀ l x, IsUnitary (O l x)) (J₀ Jb : X → P →L[ℂ] P)
    (hJ₀ : ∀ x, IsUnitary (J₀ x)) (hJb : ∀ x, IsUnitary (Jb x))
    (E : ODECompiledSource.Branch ι P N →L[ℂ] K) (hE : E† ∘L E = 1)
    (z : Option (Fin N) → P) (c : ι → ℂ) (v target₁ target₂ : P)
    (g ε : ℝ) (x₁ x₂ : X)
    (hCert₁ : ODEActualSourceError.Certificate E z c
      (ODESourcePreparations.branch (J₀ x₁) (Jb x₁) N)
      (p.eval x₁) v target₁ g ε)
    (hCert₂ : ODEActualSourceError.Certificate E z c
      (ODESourcePreparations.branch (J₀ x₂) (Jb x₂) N)
      (p.eval x₂) v target₂ g ε) :
    logicalTrials p hO J₀ Jb hJ₀ hJb E hE z c v target₁ g ε x₁ hCert₁ =
      logicalTrials p hO J₀ Jb hJ₀ hJb E hE z c v target₂ g ε x₂ hCert₂ := by
  rfl

end
end SparseHamiltonian.ODEPrimitiveSourceJoin
