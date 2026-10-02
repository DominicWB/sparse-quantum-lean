import SparseODE.ODEGroverActual

/-!
# A counted randomized amplification experiment on the actual preparation

The iteration cutoff depends only on g. Each possible trial is an explicit
program over the same primitive oracles, with a worst-case linear query
bound. The average success and the successful output direction are proved
for those programs, using the actual implemented preparation.

The two reflection descriptions are fixed with respect to the oracle input.
If constructing them requires separate source-access calls, those operations
must first be included in the preparation model; this theorem does not
silently declare an oracle-dependent reflection to be free.

-/

namespace SparseHamiltonian.ODECountedAmplification

noncomputable section
open ContinuousLinearMap OracleCircuit
open scoped BigOperators InnerProduct
set_option maxHeartbeats 1000000

variable {P K X L : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {O : L → X → K →L[ℂ] K}

/-- An actual trial uses only the original preparation, its inverse, and
fixed seed/flag reflections. Its iteration count is chosen classically. -/
def program (p : MultiOracleCircuit.Program O) (F : P →L[ℂ] K)
    (hF : F† ∘L F = 1) (ψ : K) (hψ : ‖ψ‖ = 1) (j : ℕ) :
    MultiOracleCircuit.Program O :=
  ODEGroverProgram.amplified p (ODEGroverRay.projector ψ)
    (ODEHeraldedSuccess.successProjector F)
    (ODEGroverRay.projector_isOrthogonalProjection ψ hψ)
    (ODEHeraldedSuccess.successProjector_isOrthogonalProjection F hF) j

/-- The counted program has exactly the physical state analyzed above. -/
theorem state_eq (p : MultiOracleCircuit.Program O) (F : P →L[ℂ] K)
    (hF : F† ∘L F = 1) (ψ : K) (hψ : ‖ψ‖ = 1)
    (j : ℕ) (x : X) (hU : IsUnitary (p.eval x)) :
    (program p F hF ψ hψ j).eval x ψ = ODEGroverActual.trial F (p.eval x) ψ j := by
  have hEval := congrArg (fun U : K →L[ℂ] K => U ψ)
    (ODEGroverProgram.amplified_eval_grover p (ODEGroverRay.projector ψ)
      (ODEHeraldedSuccess.successProjector F)
      (ODEGroverRay.projector_isOrthogonalProjection ψ hψ)
      (ODEHeraldedSuccess.successProjector_isOrthogonalProjection F hF) j x hU)
  simpa only [program, ← ODEGroverRay.projector_transport (p.eval x) ψ,
    mul_apply_eq_comp, ODEGroverActual.trial,
    ODEGroverActual.actualG] using hEval

/-- Exact weighted costs allow each native label to be counted separately. -/
theorem cost_eq (p : MultiOracleCircuit.Program O) (F : P →L[ℂ] K)
    (hF : F† ∘L F = 1) (ψ : K) (hψ : ‖ψ‖ = 1)
    (j : ℕ) (w : L → ℕ) :
    (program p F hF ψ hψ j).cost w = (2 * j + 1) * p.cost w :=
  ODEGroverProgram.amplified_cost p _ _ _ _ j w

/-- Every sampled trial, rather than only its expected cost, obeys the
linear preparation-call bound. -/
theorem cost_le (p : MultiOracleCircuit.Program O) (F : P →L[ℂ] K)
    (hF : F† ∘L F = 1) (ψ : K) (hψ : ‖ψ‖ = 1)
    (g : ℝ) (hg : 1 ≤ g) (j : ℕ)
    (hj : j < ODEGroverAverage.chosenIterations g) (w : L → ℕ) :
    ((program p F hF ψ hψ j).cost w : ℝ) ≤ 10 * g * (p.cost w : ℝ) := by
  exact ODEGroverProgram.amplified_cost_le p _ _ _ _ j
    (ODEGroverAverage.chosenIterations g) g hj
    (ODEGroverAverage.chosenIterations_bounds g hg).2.2 w

/-- Constant heralded success and preserved direction for an explicitly
counted uniform experiment. The same finite family of programs works for
every unknown input x; neither the cutoff nor the programs use its amplitude. -/
theorem randomized_certificate (p : MultiOracleCircuit.Program O)
    (hO : ∀ l x, IsUnitary (O l x))
    (F : P →L[ℂ] K) (hF : F† ∘L F = 1) (ψ : K) (hψ : ‖ψ‖ = 1)
    (g η : ℝ) (hg : 1 ≤ g) (target : X → P)
    (hLower : ∀ x, 1 / (4 * g) ≤ ODEGroverActual.amplitude F (p.eval x) ψ)
    (hUpper : ∀ x, ODEGroverActual.amplitude F (p.eval x) ψ ≤ 1 / 2)
    (hError : ∀ x,
      ‖ODEStateNormalization.unitDirection ((F†) (p.eval x ψ)) -
        ODEStateNormalization.unitDirection (target x)‖ ≤ η) :
    let M := ODEGroverAverage.chosenIterations g
    0 < M ∧ (M : ℝ) ≤ 5 * g ∧
      (∀ j, j < M → ∀ w : L → ℕ,
        ((program p F hF ψ hψ j).cost w : ℝ) ≤ 10 * g * (p.cost w : ℝ)) ∧
      ∀ x,
        (1 : ℝ) / 4 ≤
          (∑ j ∈ Finset.range M,
            ‖ODEHeraldedSuccess.successProjector F
              ((program p F hF ψ hψ j).eval x ψ)‖ ^ 2) / (M : ℝ) ∧
        ∀ j, j < M → (F†) ((program p F hF ψ hψ j).eval x ψ) ≠ 0 →
          ∃ ω : ℂ, ‖ω‖ = 1 ∧
            ‖ω • ODEStateNormalization.unitDirection
                ((F†) ((program p F hF ψ hψ j).eval x ψ)) -
              ODEStateNormalization.unitDirection (target x)‖ ≤ η := by
  dsimp only
  obtain ⟨hM, _hCoverage, hMUpper⟩ := ODEGroverAverage.chosenIterations_bounds g hg
  refine ⟨hM, hMUpper, ?_, ?_⟩
  · intro j hj w
    exact cost_le p F hF ψ hψ g hg j hj w
  · intro x
    have hU := p.eval_unitary hO x
    have hState (j : ℕ) :
        (program p F hF ψ hψ j).eval x ψ =
          ODEGroverActual.trial F (p.eval x) ψ j :=
      state_eq p F hF ψ hψ j x hU
    obtain ⟨_hM, _hMUpper, hSuccess, hDirection⟩ :=
      ODEGroverActual.randomized_certificate F hF (p.eval x) hU ψ hψ
        g hg (hLower x) (hUpper x) (target x) η (hError x)
    constructor
    · simpa only [ODEGroverActual.meanProbability, ODEGroverActual.probability,
        hState] using hSuccess
    · intro j _hj hNonzero
      have hn : ODEGroverActual.decoded F (p.eval x) ψ j ≠ 0 := by
        simpa only [hState, ODEGroverActual.decoded] using hNonzero
      simpa only [hState, ODEGroverActual.decoded] using
        hDirection j hn

/-- Multiplying the proved selected-query bound by the actual circuit cost
retains the improved precision dependence. This is a worst-case trial bound. -/
theorem selected_query_bound (p : MultiOracleCircuit.Program O)
    (F : P →L[ℂ] K) (hF : F† ∘L F = 1) (ψ : K) (hψ : ‖ψ‖ = 1)
    (s Θ ell g : ℝ) (hg : 1 ≤ g) (j : ℕ)
    (hj : j < ODEGroverAverage.chosenIterations g)
    (hq : (p.count : ℝ) ≤ 10616832 * ImprovedODEQueryBudget.queryShape s Θ ell) :
    ((program p F hF ψ hψ j).count : ℝ) ≤
      106168320 * g * ImprovedODEQueryBudget.queryShape s Θ ell := by
  have hg0 : 0 ≤ g := by linarith
  have hCount : ((program p F hF ψ hψ j).count : ℝ) ≤ 10 * g * (p.count : ℝ) := by
    simpa using cost_le p F hF ψ hψ g hg j hj (fun _ => 1)
  calc
    _ ≤ 10 * g * (p.count : ℝ) := hCount
    _ ≤ 10 * g * (10616832 * ImprovedODEQueryBudget.queryShape s Θ ell) :=
      mul_le_mul_of_nonneg_left hq (mul_nonneg (by norm_num) hg0)
    _ = _ := by ring

end
end SparseHamiltonian.ODECountedAmplification
