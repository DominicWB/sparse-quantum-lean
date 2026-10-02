import SparseHamiltonian.CleanOutputAlignment

/-!
# Query-preserving alignment of clean input and output spaces

Every native query is extended by one untouched Boolean register. The syntax
contains the same labels and inverse directions as the source program. A
single fixed unitary after the lifted program aligns the clean output with
the clean input. Neither a controlled oracle nor an extra query is used.
-/

namespace SparseHamiltonian.AlignedMultiOracleProgram

noncomputable section
open ContinuousLinearMap OracleCircuit CleanOutputAlignment
open scoped InnerProduct

variable {P K : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {X L : Type*}

/-- The new Boolean register is untouched by each original primitive call. -/
abbrev oracle (O : L → X → K →L[ℂ] K) :=
  CoherentQuerySchedule.oracle (ι := Bool) O

/-- Apply the same program on both spectator sectors. -/
def diagonalProgram {O : L → X → K →L[ℂ] K} :
    MultiOracleCircuit.Program O → MultiOracleCircuit.Program (oracle O)
  | .fixed U hU => .fixed _
      (CoherentQuerySchedule.diagonal_unitary (fun _ : Bool => U) (fun _ => hU))
  | .query l => .query l
  | .queryAdjoint l => .queryAdjoint l
  | .seq p q => .seq (diagonalProgram p) (diagonalProgram q)

@[simp] theorem diagonalProgram_count {O : L → X → K →L[ℂ] K}
    (p : MultiOracleCircuit.Program O) :
    (diagonalProgram p).count = p.count := by
  induction p with
  | fixed U hU => rfl
  | query l => rfl
  | queryAdjoint l => rfl
  | seq p q hp hq =>
      simp only [diagonalProgram, MultiOracleCircuit.Program.count_seq, hp, hq]

@[simp] theorem diagonalProgram_cost {O : L → X → K →L[ℂ] K}
    (p : MultiOracleCircuit.Program O) (w : L → ℕ) :
    (diagonalProgram p).cost w = p.cost w := by
  induction p with
  | fixed U hU => rfl
  | query l => rfl
  | queryAdjoint l => rfl
  | seq p q hp hq =>
      simp only [diagonalProgram, MultiOracleCircuit.Program.cost_seq, hp, hq]

/-- This is an exact identity on the entire enlarged workspace. -/
theorem diagonalProgram_eval {O : L → X → K →L[ℂ] K}
    (p : MultiOracleCircuit.Program O) (x : X) :
    (diagonalProgram p).eval x = WeightedClock.diagonal (fun _ : Bool => p.eval x) := by
  induction p with
  | fixed U hU => rfl
  | query l => rfl
  | queryAdjoint l => exact WeightedClock.diagonal_adjoint _
  | seq p q hp hq =>
      simp only [diagonalProgram, MultiOracleCircuit.Program.eval_seq, hp, hq]
      exact WeightedClock.diagonal_comp _ _

/-- In particular the initial zero spectator remains zero. -/
theorem diagonalProgram_intertwines {O : L → X → K →L[ℂ] K}
    (p : MultiOracleCircuit.Program O) (x : X) :
    (diagonalProgram p).eval x ∘L includeZero = includeZero ∘L p.eval x := by
  rw [diagonalProgram_eval]
  apply ContinuousLinearMap.ext
  intro v
  apply PiLp.ext
  intro b
  cases b <;>
    simp only [comp_apply, WeightedClock.diagonal_apply,
      includeZero_apply_false, includeZero_apply_true, map_zero]

/-- The original fixed input preparation with a zero Boolean spectator. -/
def input (E : P →L[ℂ] K) : P →L[ℂ] Double K := includeZero ∘L E

theorem input_isometry (E : P →L[ℂ] K) (hE : E† ∘L E = 1) :
    (input E)† ∘L input E = 1 :=
  clean_isometry E hE

/-- The last fixed gate aligns the target output with the initial encoding. -/
def program {O : L → X → K →L[ℂ] K} (E F : P →L[ℂ] K)
    (hE : E† ∘L E = 1) (hF : F† ∘L F = 1)
    (p : MultiOracleCircuit.Program O) : MultiOracleCircuit.Program (oracle O) :=
  .seq (.fixed (align E F) (align_unitary E F hE hF)) (diagonalProgram p)

@[simp] theorem program_count {O : L → X → K →L[ℂ] K}
    (E F : P →L[ℂ] K) (hE : E† ∘L E = 1) (hF : F† ∘L F = 1)
    (p : MultiOracleCircuit.Program O) : (program E F hE hF p).count = p.count := by
  simp only [program, MultiOracleCircuit.Program.count_seq,
    MultiOracleCircuit.Program.count_fixed, zero_add, diagonalProgram_count]

@[simp] theorem program_cost {O : L → X → K →L[ℂ] K}
    (E F : P →L[ℂ] K) (hE : E† ∘L E = 1) (hF : F† ∘L F = 1)
    (p : MultiOracleCircuit.Program O) (w : L → ℕ) :
    (program E F hE hF p).cost w = p.cost w := by
  simp only [program, MultiOracleCircuit.Program.cost_seq,
    MultiOracleCircuit.Program.cost_fixed, zero_add, diagonalProgram_cost]

/-- Alignment preserves the full output operator error exactly. -/
theorem program_error {O : L → X → K →L[ℂ] K}
    (E F : P →L[ℂ] K) (hE : E† ∘L E = 1) (hF : F† ∘L F = 1)
    (p : MultiOracleCircuit.Program O) (x : X) (U : P →L[ℂ] P) :
    ‖(program E F hE hF p).eval x ∘L input E - input E ∘L U‖ =
      ‖p.eval x ∘L E - F ∘L U‖ := by
  have hClean := congrArg (fun A : K →L[ℂ] Double K => A ∘L E)
    (diagonalProgram_intertwines p x)
  simp only [comp_assoc] at hClean
  change ‖align E F ∘L ((diagonalProgram p).eval x ∘L (includeZero ∘L E)) -
      (includeZero ∘L E) ∘L U‖ = _
  rw [hClean]
  simpa only [comp_assoc] using align_error E F hE hF (p.eval x ∘L E) U

/-- Generic same-input/output certificate, with unchanged primitive query
count and unchanged costs of all native labels. The sole oracle enlargement
is the explicit spectator extension `diag(O,O)`. -/
theorem exists_aligned_program (O : L → X → K →L[ℂ] K)
    (hO : ∀ l x, IsUnitary (O l x)) (E F : P →L[ℂ] K)
    (hE : E† ∘L E = 1) (hF : F† ∘L F = 1)
    (p : MultiOracleCircuit.Program O) (U : X → P →L[ℂ] P) (ε : ℝ)
    (hError : ∀ x, ‖p.eval x ∘L E - F ∘L U x‖ ≤ ε) :
    ∃ q : MultiOracleCircuit.Program (oracle O),
      q.count = p.count ∧ (∀ w : L → ℕ, q.cost w = p.cost w) ∧
      (input E)† ∘L input E = 1 ∧
      ∀ x, IsUnitary (q.eval x) ∧
        ‖q.eval x ∘L input E - input E ∘L U x‖ ≤ ε := by
  refine ⟨program E F hE hF p, program_count E F hE hF p,
    program_cost E F hE hF p, input_isometry E hE, ?_⟩
  intro x
  refine ⟨(program E F hE hF p).eval_unitary
    (CoherentQuerySchedule.oracle_unitary O hO) x, ?_⟩
  rw [program_error]
  exact hError x

end
end SparseHamiltonian.AlignedMultiOracleProgram
