import TimeDependentODE.Source.Primitive

/-!
# Public constructors for the counted time-dependent source trials

The unknown matrix input, the source directions, the target vector and the
source-error certificate enter `SourceTD.logicalTrials` only through proofs.
The constructor below uses exactly the public data of the circuit: the
SELECT program, the supplied source interfaces, the clean encoding, the
public coefficient function and the seed. A pointwise correctness certificate
gives the same family by equality of its coefficient function and proof
irrelevance (`logicalTrials_eq_publicLogicalTrials`).
-/

namespace SparseHamiltonian.TimeDependentODE.SourceTD

noncomputable section
open ContinuousLinearMap OracleCircuit
open scoped InnerProduct

variable {ι P K X L : Type*} [Fintype ι]
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {N : ℕ} {O : L → X → K →L[ℂ] K}

/-- Counted amplification using public coefficients and the supplied source
interfaces. All inputs to free reflections are explicit public data. -/
def publicLogicalTrials (p : MultiOracleCircuit.Program O)
    (J₀ : X → P →L[ℂ] P) (Jb : X → Fin N → P →L[ℂ] P)
    (E : ODECompiledSource.Branch ι P N →L[ℂ] K) (hE : E† ∘L E = 1)
    (d : Option (Fin N) × ι → ℂ) (v : P)
    (hSeed : ‖ODECompiledSource.seed E d v‖ = 1)
    (hOutput : (ODECompiledSource.output E d)† ∘L ODECompiledSource.output E d = 1) :
    ℕ → MultiOracleCircuit.Program
      (ODESectorCoordinates.oracle O (sourceFamily (ι := ι) J₀ Jb)) :=
  fun j => ODECountedAmplification.program
    (program p J₀ Jb E hE)
    (ODECompiledSource.output E d) hOutput
    (ODECompiledSource.seed E d v) hSeed j

/-- The geometry proof justifies the public reflections but does not change
their circuit syntax. -/
theorem logicalTrials_eq_publicLogicalTrials (p : MultiOracleCircuit.Program O)
    (hO : ∀ l x, IsUnitary (O l x)) (J₀ : X → P →L[ℂ] P)
    (Jb : X → Fin N → P →L[ℂ] P)
    (hJ₀ : ∀ x, IsUnitary (J₀ x)) (hJb : ∀ x q, IsUnitary (Jb x q))
    (E : ODECompiledSource.Branch ι P N →L[ℂ] K) (hE : E† ∘L E = 1)
    (z : Option (Fin N) → P) (c : ι → ℂ) (v target : P)
    (g ε : ℝ) (x : X)
    (hCert : ODEActualSourceError.Certificate E z c
      (branchTD (J₀ x) (Jb x)) (p.eval x) v target g ε)
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

end SparseHamiltonian.TimeDependentODE.SourceTD
