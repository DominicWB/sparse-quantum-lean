import SparseHamiltonian.NativeWholeProgramActive

namespace SparseHamiltonian.NativeCleanConjugation

noncomputable section
open ContinuousLinearMap OracleCircuit
open scoped InnerProduct

variable {P K X L : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {O : L → X → K →L[ℂ] K}

/-- Input-dependent conjugation is implemented by actual forward and inverse
program calls; it is never counted as a fixed gate. -/
def program (pF pD : MultiOracleCircuit.Program O) : MultiOracleCircuit.Program O :=
  .seq pF.adjoint (.seq pD pF)

@[simp] theorem program_count (pF pD : MultiOracleCircuit.Program O) :
    (program pF pD).count = 2 * pF.count + pD.count := by
  simp only [program, MultiOracleCircuit.Program.count_seq,
    MultiOracleCircuit.Program.count_adjoint]
  omega

@[simp] theorem program_cost (pF pD : MultiOracleCircuit.Program O) (w : L → ℕ) :
    (program pF pD).cost w = 2 * pF.cost w + pD.cost w := by
  simp only [program, MultiOracleCircuit.Program.cost_seq,
    MultiOracleCircuit.Program.cost_adjoint]
  omega

/-- Clean implementations of the locator and edge action compose to a clean
implementation of their conjugation. The full-space locator must be unitary. -/
theorem program_intertwines (hO : ∀ l x, IsUnitary (O l x))
    (pF pD : MultiOracleCircuit.Program O) (E : P →L[ℂ] K)
    (F D : X → P →L[ℂ] P) (hF : ∀ x, IsUnitary (F x))
    (hLocate : ∀ x, pF.eval x ∘L E = E ∘L F x)
    (hEdge : ∀ x, pD.eval x ∘L E = E ∘L D x) (x : X) :
    (program pF pD).eval x ∘L E = E ∘L ((F x)† ∘L D x ∘L F x) := by
  have hAdj := EncodedOracle.adjoint_intertwines _ _ E
    (pF.eval_unitary hO x) (hF x) (hLocate x)
  simp only [star_eq_adjoint] at hAdj
  simp only [program, MultiOracleCircuit.Program.eval_seq,
    MultiOracleCircuit.Program.eval_adjoint, star_eq_adjoint, ← mul_def]
  change ((pF.eval x)† ∘L (pD.eval x ∘L pF.eval x)) ∘L E = _
  calc
    _ = (pF.eval x)† ∘L (pD.eval x ∘L (pF.eval x ∘L E)) := by
      simp only [comp_assoc]
    _ = (pF.eval x)† ∘L (pD.eval x ∘L (E ∘L F x)) := by rw [hLocate]
    _ = (pF.eval x)† ∘L ((pD.eval x ∘L E) ∘L F x) := by
      simp only [comp_assoc]
    _ = (pF.eval x)† ∘L ((E ∘L D x) ∘L F x) := by rw [hEdge]
    _ = ((pF.eval x)† ∘L E) ∘L (D x ∘L F x) := by
      simp only [comp_assoc]
    _ = (E ∘L (F x)†) ∘L (D x ∘L F x) := by rw [hAdj]
    _ = E ∘L ((F x)† ∘L D x ∘L F x) := by simp only [comp_assoc]

end
end SparseHamiltonian.NativeCleanConjugation
