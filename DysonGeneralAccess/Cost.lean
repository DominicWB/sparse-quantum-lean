import DysonSingleProgram.Parallel.Four

set_option autoImplicit false

/-!
# Weighted call counts of the coherent attempts

Lemma `odel:lem:dyson` of the manuscript counts only matrix queries; over an access with
source interfaces (labels `Sum.inr`) the call count `count` also counts source calls. The package
counts the coherent attempts and the parallel stages in total (`count_*`) and label by label
(`labelCount_*`); this module gives the same identities for every weight `w : L → ℕ`
(`MultiOracleCircuit.Program.cost`), with no finiteness assumption on the labels; the package's
`count_*` and `labelCount_*` identities are the instances with weight `1` and with the indicator
weight of one label.

* `cost_reflatten`: flattening two spectator registers keeps every weighted count;
* `cost_steps`, `cost_trial`: the attempt with a coherent cutoff `Fin M` costs
  `2(M - 1) + 1` times its preparation;
* `cost_step`, `cost_four`: a stage step adds one attempt; the four-attempt stage costs four
  attempts.
-/

namespace DysonGeneralAccess.Cost

noncomputable section
open SparseHamiltonian SparseLowerBounds OracleCircuit
open DysonSingleProgram DysonSingleProgram.Register DysonSingleProgram.Parallel

section Flatten

variable {X L W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
  {O : L → X → W →L[ℂ] W}

/-- Flattening keeps every weighted count. -/
@[simp] theorem cost_reflatten (Ω₁ Ω₂ : Type) [Fintype Ω₁] [Fintype Ω₂]
    (p : MultiOracleCircuit.Program (fiberOracle Ω₁ (fiberOracle Ω₂ O))) (w : L → ℕ) :
    (reflatten Ω₁ Ω₂ p).cost w = p.cost w := by
  unfold reflatten
  rw [MultiOracleCircuit.Program.cost_substitute, MultiOracleCircuit.Program.cost_transport]
  rfl

end Flatten

section Trial

variable {X L W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
  {O : L → X → W →L[ℂ] W} (M : ℕ) (a : MultiOracleCircuit.Program O) {U₁ U₂ U₃ : W →L[ℂ] W}
  (h₁ : IsUnitary U₁) (h₂ : IsUnitary U₂) (h₃ : IsUnitary U₃)

/-- Steps `0, …, n - 1` cost `2n` times the preparation, for every weight. -/
theorem cost_steps (w : L → ℕ) (n : ℕ) :
    (Coherent.steps M a h₁ h₂ h₃ n).cost w = n * (2 * a.cost w) := by
  induction n with
  | zero => simp [Coherent.steps]
  | succ n ih =>
    simp only [Coherent.steps, Coherent.step, MultiOracleCircuit.Program.cost_seq,
      MultiOracleCircuit.Program.cost_fixed, MultiOracleCircuit.Program.cost_adjoint,
      cost_spectate, ih]
    ring

/-- **The attempt with a coherent cutoff** costs `2(M - 1) + 1` times its preparation, for every
weight. -/
theorem cost_trial (w : L → ℕ) :
    (Coherent.trial M a h₁ h₂ h₃).cost w = (2 * (M - 1) + 1) * a.cost w := by
  rw [Coherent.trial, MultiOracleCircuit.Program.cost_seq, cost_steps, cost_spectate]
  ring

end Trial

section Stage

variable {X L : Type*} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  [CompleteSpace W] [FiniteDimensional ℂ W] {M : ℕ} {N : Type} [Fintype N] [DecidableEq N]
  {O : L → X → W →L[ℂ] W}

omit [DecidableEq N] in
/-- A stage step adds the weighted count of one attempt. -/
theorem cost_step (S : Stage O M N) (C : MultiOracleCircuit.Program (fiberOracle (Fin M) O))
    (μ : Joint (Fin M) W) (Fo : EuclideanSpace ℂ N →L[ℂ] W) (w : L → ℕ) :
    (S.step C μ Fo).prog.cost w = S.prog.cost w + C.cost w := by
  show (reflatten (Coord M W) S.I _).cost w = _
  rw [cost_reflatten]
  simp

/-- **The four-attempt stage** costs four attempts, for every weight. -/
theorem cost_four (C : MultiOracleCircuit.Program (fiberOracle (Fin M) O))
    (μ : Joint (Fin M) W) (Fo : EuclideanSpace ℂ N →L[ℂ] W) (i₀ : N) (w : L → ℕ) :
    (Stage.four C μ Fo i₀).prog.cost w = 4 * C.cost w := by
  have h0 : (Stage.base (O := O) (M := M) i₀).prog.cost w = 0 :=
    MultiOracleCircuit.Program.cost_identity w
  rw [Stage.four, cost_step, cost_step, cost_step, cost_step, h0]
  ring

end Stage

end

end DysonGeneralAccess.Cost
