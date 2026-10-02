import SparseODE.ImprovedSparseODE

/-!
# Explicit operational bounds for the final ODE trial family

These consequences retain the actual primitive trial circuits from the full
certificate. They expose the three matrix-query terms and the common-energy
specialization, together with the source counts, heralded success and stated
epsilon accuracy. No circuit is replaced by a scalar query-count witness.

-/

namespace SparseHamiltonian.ODEOperationalBounds

noncomputable section
open ContinuousLinearMap ODEStateNormalization ImprovedODEQueryBudget
open scoped BigOperators InnerProduct

variable {P R X L : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
  {O : (L ⊕ Bool) → X → R →L[ℂ] R}

/-- The full certificate gives an explicit worst-case matrix and source
query bound for every allowed trial, mean heralded success at least one
quarter, and epsilon-accurate normalized output on each successful trial.
The success average is the uniform average over the finite trial range. -/
theorem operational_guarantees
    (q : ℕ → MultiOracleCircuit.Program O) (M : ℕ)
    (ψ : R) (F : P →L[ℂ] R) (x : X) (target : P)
    (s etaH etaD T g ε : ℝ) (hε : 0 ≤ ε)
    (hCert : ODEPrimitiveSourceJoin.TrialCertificate q M ψ F x target s
      (theta (T * etaH) (T * etaD) g ε) (logBudget g ε) g (ε / 500)) :
    (∀ j, j < M →
      ((q j).cost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) : ℝ) ≤
        318504960 * g *
          (Real.sqrt s * theta (T * etaH) (T * etaD) g ε +
            Real.sqrt (s * theta (T * etaH) (T * etaD) g ε * logBudget g ε) +
            logBudget g ε)) ∧
    (∀ j, j < M → ∀ b : Bool,
      ((q j).cost (ODESourceQueryBudget.sourceWeight b) : ℝ) ≤ 10 * g) ∧
    (∀ j, j < M →
      ((q j).cost ODESourceQueryBudget.sourceTotalWeight : ℝ) ≤ 20 * g) ∧
    (1 : ℝ) / 4 ≤
      (∑ j ∈ Finset.range M,
        ‖ODEHeraldedSuccess.successProjector F ((q j).eval x ψ)‖ ^ 2) / (M : ℝ) ∧
    (∀ j, j < M → (F†) ((q j).eval x ψ) ≠ 0 →
      ∃ ω : ℂ, ‖ω‖ = 1 ∧
        ‖ω • unitDirection ((F†) ((q j).eval x ψ)) - unitDirection target‖ ≤ ε) := by
  refine ⟨?_, hCert.source_queries, hCert.total_source_queries,
    hCert.mean_success, ?_⟩
  · intro j hj
    exact hCert.matrix_queries j hj
  · intro j hj hNonzero
    obtain ⟨ω, hω, hDirection⟩ := hCert.direction_error j hj hNonzero
    have hTolerance : ε / 500 ≤ ε := by linarith
    exact ⟨ω, hω, hDirection.trans hTolerance⟩

/-- When the same energy bound is supplied for both Hermitian components,
every actual primitive trial satisfies the corresponding factored bound.
The supplied certificate still concerns its original circuit family. -/
theorem common_energy_queries
    (q : ℕ → MultiOracleCircuit.Program O) (M : ℕ)
    (ψ : R) (F : P →L[ℂ] R) (x : X) (target : P)
    (s η T g ε : ℝ) (hs : 0 ≤ s) (hη : 0 ≤ η) (hT : 0 ≤ T)
    (hg : 1 ≤ g) (hε : 0 < ε) (hεOne : ε ≤ 1)
    (hCert : ODEPrimitiveSourceJoin.TrialCertificate q M ψ F x target s
      (theta (T * η) (T * η) g ε) (logBudget g ε) g (ε / 500)) :
    ∀ j, j < M →
      ((q j).cost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) : ℝ) ≤
        637009920 * g * (Real.sqrt s * (T * η + Real.sqrt (T * η)) + 1) *
          logBudget g ε := by
  intro j hj
  have hg0 : 0 ≤ g := (by norm_num : (0 : ℝ) ≤ 1).trans hg
  have hShape := common_shape_le s (T * η) g ε hs (mul_nonneg hT hη) hg hε hεOne
  calc
    ((q j).cost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) : ℝ) ≤
        318504960 * g * queryShape s (theta (T * η) (T * η) g ε) (logBudget g ε) :=
      hCert.matrix_queries j hj
    _ ≤ 318504960 * g *
        (2 * (Real.sqrt s * (T * η + Real.sqrt (T * η)) + 1) * logBudget g ε) :=
      mul_le_mul_of_nonneg_left hShape (by positivity)
    _ = 637009920 * g * (Real.sqrt s * (T * η + Real.sqrt (T * η)) + 1) *
        logBudget g ε := by ring

end
end SparseHamiltonian.ODEOperationalBounds
