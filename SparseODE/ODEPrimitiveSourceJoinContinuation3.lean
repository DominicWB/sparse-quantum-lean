import SparseODE.ODESourcePublicNorms

/-!
# Public coefficient constructors for the counted ODE trials

These constructors expose exactly the data used by the circuit. The source
directions, unknown matrix input and final target are absent. A pointwise
correctness certificate is related to the same public family by equality of
its coefficient function and proof irrelevance.

-/

namespace SparseHamiltonian.ODEPrimitiveSourceJoin

noncomputable section
open ContinuousLinearMap OracleCircuit
open scoped InnerProduct

variable {ι P K X L : Type*} [Fintype ι]
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {N : ℕ} {O : L → X → K →L[ℂ] K}

/-- Counted amplification using public coefficients and the supplied source
interfaces. All inputs to free reflections are specified explicitly. -/
def publicLogicalTrials (p : MultiOracleCircuit.Program O)
    (J₀ Jb : X → P →L[ℂ] P)
    (E : ODECompiledSource.Branch ι P N →L[ℂ] K) (hE : E† ∘L E = 1)
    (d : Option (Fin N) × ι → ℂ) (v : P)
    (hSeed : ‖ODECompiledSource.seed E d v‖ = 1)
    (hOutput : (ODECompiledSource.output E d)† ∘L ODECompiledSource.output E d = 1) :
    ℕ → MultiOracleCircuit.Program
      (ODESectorCoordinates.oracle O (sourceFamily (ι := ι) J₀ Jb N)) :=
  fun j => ODECountedAmplification.program
    (ODECompiledSource.program p J₀ Jb E hE)
    (ODECompiledSource.output E d) hOutput
    (ODECompiledSource.seed E d v) hSeed j

/-- The geometry proof justifies the public reflections but does not change
their circuit syntax. This argument unfolds only the trial constructors. -/
theorem logicalTrials_eq_publicLogicalTrials (p : MultiOracleCircuit.Program O)
    (hO : ∀ l x, IsUnitary (O l x)) (J₀ Jb : X → P →L[ℂ] P)
    (hJ₀ : ∀ x, IsUnitary (J₀ x)) (hJb : ∀ x, IsUnitary (Jb x))
    (E : ODECompiledSource.Branch ι P N →L[ℂ] K) (hE : E† ∘L E = 1)
    (z : Option (Fin N) → P) (c : ι → ℂ) (v target : P)
    (g ε : ℝ) (x : X)
    (hCert : ODEActualSourceError.Certificate E z c
      (ODESourcePreparations.branch (J₀ x) (Jb x) N)
      (p.eval x) v target g ε)
    (d : Option (Fin N) × ι → ℂ)
    (hCoefficients : ODEActualSourceError.coefficients z c = d)
    (hSeed : ‖ODECompiledSource.seed E d v‖ = 1)
    (hOutput : (ODECompiledSource.output E d)† ∘L ODECompiledSource.output E d = 1) :
    logicalTrials p hO J₀ Jb hJ₀ hJb E hE z c v target g ε x hCert =
      publicLogicalTrials p J₀ Jb E hE d v hSeed hOutput := by
  subst d
  unfold logicalTrials publicLogicalTrials
  rfl

end
end SparseHamiltonian.ODEPrimitiveSourceJoin
