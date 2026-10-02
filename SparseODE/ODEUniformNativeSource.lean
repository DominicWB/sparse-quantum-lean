import SparseODE.ODEFinalNativeSourceContinuation3

/-!
# One public trial family for all promised ODE inputs

The native SELECT circuit is selected before the unknown input and the source
directions.  All coefficient preparation and both amplification reflections
depend only on the supplied source norms, the public seed and the canonical
encoding.  The same primitive circuit family therefore satisfies the full
trial certificate for every promised matrix and pair of source directions.

-/

namespace SparseHamiltonian.ODEUniformNativeSource

noncomputable section
open ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding
open scoped BigOperators InnerProduct
set_option maxRecDepth 4096
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 3000000

variable {ι X n Z : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype n] [DecidableEq n]
  [Fintype Z] [AddCommGroup Z] [DecidableEq Z] {s : ℕ}

/-- Every field of the primitive success, accuracy and query certificate
survives replacement by the single public-coefficient trial family. -/
theorem coefficient_trial_certificate (D : Data X n Z s) (i0 : ι) (N Tslots d : ℕ)
    (p : MultiOracleCircuit.Program
      (ODEFinalNativeSource.matrixOracle (ι := ι) D N Tslots d))
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ₀ : ∀ x, IsUnitary (J₀ x)) (hJb : ∀ x, IsUnitary (Jb x))
    (E : ODEFinalNativeSource.SourceSpace ι n N →L[ℂ]
      ODEFinalNativeSource.MatrixSpace ι n Z N Tslots d) (hE : E† ∘L E = 1)
    (z : Option (Fin N) → EuclideanSpace ℂ n) (c : ι → ℂ)
    (seed target : EuclideanSpace ℂ n) (hSeed : ‖seed‖ = 1)
    (Θ ell g ε : ℝ) (hg : 1 ≤ g) (x : X)
    (hCert : ODEActualSourceError.Certificate E z c
      (ODESourcePreparations.branch (J₀ x) (Jb x) N) (p.eval x) seed target g ε)
    (hq : (p.count : ℝ) ≤ 10616832 * ImprovedODEQueryBudget.queryShape (s : ℝ) Θ ell)
    (a : Option (Fin N) × ι → ℂ) (ha : 0 < ODECoherentLCU.coefficientMass a)
    (hCoeff : ODEActualSourceError.coefficients z c = a) :
    ODEPrimitiveSourceJoin.TrialCertificate
      (ODEFinalNativeSource.publicTrials D i0 N Tslots d p J₀ Jb E hE a seed
        (ODECompiledSource.seed_unit E a hE ha seed hSeed)
        (ODECompiledSource.output_isometry E a hE ha))
      (ODEGroverAverage.chosenIterations g)
      (ODEFinalNativeSource.input D i0 N Tslots d (ODECompiledSource.seed E a seed))
      (ODEFinalNativeSource.input D i0 N Tslots d ∘L ODECompiledSource.output E a)
      x target (s : ℝ) Θ ell g (ε / 500) := by
  have h := ODEFinalNativeSource.primitive_source_certificate D i0 N Tslots d p
    J₀ Jb hJ₀ hJb E hE z c seed target Θ ell g ε hg x hCert hq
  rw [ODEFinalNativeSource.trials_eq_publicTrials D i0 N Tslots d p
      J₀ Jb hJ₀ hJb E hE z c seed target g ε x hCert a hCoeff
      (ODECompiledSource.seed_unit E a hE ha seed hSeed)
      (ODECompiledSource.output_isometry E a hE ha),
    ODEFinalNativeSource.seed_eq_of_coefficients D i0 N Tslots d E z c seed a hCoeff,
    ODEFinalNativeSource.output_eq_of_coefficients D i0 N Tslots d E z c a hCoeff] at h
  exact h

end
end SparseHamiltonian.ODEUniformNativeSource
