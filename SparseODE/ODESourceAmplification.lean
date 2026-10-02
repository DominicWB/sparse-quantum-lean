import SparseODE.ODECountedAmplification

/-!
# Amplification of the derived ODE source certificate

The actual source-output certificate supplies the initial
amplitude and direction bounds. Randomized amplification preserves that
direction and gives constant success, with the improved sparse-query budget.

This closes the amplification interface for the supplied source preparations.
Constructing and counting the source-preparation oracles is still separate;
the physical seed and output embedding here are fixed with respect to the
unknown matrix input. Gaussian LCHS estimates also remain separate.
-/

namespace SparseHamiltonian.ODESourceAmplification

noncomputable section
open ContinuousLinearMap OracleCircuit ODEActualSourceError ODEStateNormalization
open scoped InnerProduct BigOperators

variable {σ ι P K : Type*} [Fintype σ] [Fintype ι]
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The derived source error, rather than a fresh vector-error assumption,
feeds the actual amplification theorem. -/
theorem source_randomized_certificate
    (E : ODEJointLCU.BranchSpace (σ × ι) P →L[ℂ] K)
    (z : σ → P) (c : ι → ℂ) (J : σ → P →L[ℂ] P)
    (W : K →L[ℂ] K) (hW : IsUnitary W) (v target : P) (g ε : ℝ)
    (hg : 1 ≤ g) (hCert : Certificate E z c J W v target g ε) :
    0 < ODEGroverAverage.chosenIterations g ∧
    (ODEGroverAverage.chosenIterations g : ℝ) ≤ 5 * g ∧
    (1 : ℝ) / 4 ≤ ODEGroverActual.meanProbability
      (output E z c) W (input E z c J v) (ODEGroverAverage.chosenIterations g) ∧
    ∀ j : ℕ, ODEGroverActual.decoded (output E z c) W (input E z c J v) j ≠ 0 →
      ∃ ω : ℂ, ‖ω‖ = 1 ∧
        ‖ω • unitDirection (ODEGroverActual.decoded
            (output E z c) W (input E z c J v) j) - unitDirection target‖ ≤ ε / 500 := by
  exact ODEGroverActual.randomized_certificate
    (output E z c) hCert.output_isometry W hW
    (input E z c J v) hCert.input_unit g hg
    hCert.amplitude_lower hCert.amplitude_upper.le target (ε / 500) hCert.direction_error

variable {X L : Type*} {O : L → X → K →L[ℂ] K}

/-- For a selected native program, the same physical source certificate gives
constant-success trials at the improved total sparse-query cost. The supplied
source input and output encoding do not depend on the unknown matrix input. -/
theorem counted_source_certificate
    (E : ODEJointLCU.BranchSpace (σ × ι) P →L[ℂ] K)
    (z : σ → P) (c : ι → ℂ) (J : σ → P →L[ℂ] P)
    (p : MultiOracleCircuit.Program O) (x : X) (hU : IsUnitary (p.eval x))
    (v target : P) (s Θ ell g ε : ℝ) (hg : 1 ≤ g)
    (hCert : Certificate E z c J (p.eval x) v target g ε)
    (hq : (p.count : ℝ) ≤ 10616832 * ImprovedODEQueryBudget.queryShape s Θ ell) :
    let F := output E z c
    let ψ := input E z c J v
    let M := ODEGroverAverage.chosenIterations g
    let q := fun j => ODECountedAmplification.program p F hCert.output_isometry
      ψ hCert.input_unit j
    0 < M ∧ (M : ℝ) ≤ 5 * g ∧
      (∀ j, j < M → ((q j).count : ℝ) ≤
        106168320 * g * ImprovedODEQueryBudget.queryShape s Θ ell) ∧
      (1 : ℝ) / 4 ≤
        (∑ j ∈ Finset.range M,
          ‖ODEHeraldedSuccess.successProjector F ((q j).eval x ψ)‖ ^ 2) / (M : ℝ) ∧
      ∀ j, j < M → (F†) ((q j).eval x ψ) ≠ 0 →
        ∃ ω : ℂ, ‖ω‖ = 1 ∧
          ‖ω • unitDirection ((F†) ((q j).eval x ψ)) - unitDirection target‖ ≤ ε / 500 := by
  dsimp only
  have hState (j : ℕ) :
      (ODECountedAmplification.program p (output E z c) hCert.output_isometry
        (input E z c J v) hCert.input_unit j).eval x (input E z c J v) =
      ODEGroverActual.trial (output E z c) (p.eval x) (input E z c J v) j :=
    ODECountedAmplification.state_eq p (output E z c) hCert.output_isometry
      (input E z c J v) hCert.input_unit j x hU
  obtain ⟨hM, hMUpper, hSuccess, hDirection⟩ :=
    source_randomized_certificate E z c J (p.eval x) hU v target g ε hg hCert
  refine ⟨hM, hMUpper, ?_, ?_, ?_⟩
  · intro j hj
    exact ODECountedAmplification.selected_query_bound p
      (output E z c) hCert.output_isometry (input E z c J v) hCert.input_unit
      s Θ ell g hg j hj hq
  · simpa only [ODEGroverActual.meanProbability, ODEGroverActual.probability,
      hState] using hSuccess
  · intro j _hj hNonzero
    have hn : ODEGroverActual.decoded
        (output E z c) (p.eval x) (input E z c J v) j ≠ 0 := by
      simpa only [hState, ODEGroverActual.decoded] using hNonzero
    simpa only [hState, ODEGroverActual.decoded] using hDirection j hn

end
end SparseHamiltonian.ODESourceAmplification
