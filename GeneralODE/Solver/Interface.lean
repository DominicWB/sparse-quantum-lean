import GeneralODE.Block.HistoryProgram
import SparseHamiltonian.ODEStateNormalization
import SparseHamiltonian.NativeWholeProgramMask

/-!
# The block-input linear-system solver interface

This file states the only result from outside the paper that the general ODE
theorem uses: a near-optimal linear-system solver with block-encoded input
(Costa et al.; Dalzell).  It is a hypothesis `BlockSolver f q₀`, never an
axiom.

The solver acts on a workspace `PiLp 2 (Fin w → s × a)`: a classical solver
register `Fin w` and one copy of the oracle register `s × a` in every branch.
Its oracle family has two labels.  Label `false` applies the block encoding
`U` in every branch `i` with `ctrl i = true` and the identity elsewhere;
label `true` does the same with the state preparation `B`.  Inverse calls are
part of the program model.  Fixed gates are arbitrary unitaries of the whole
workspace, so controlled calls on any solver qubit, and uncontrolled calls,
are obtained by conjugating with fixed permutations.

`BlockSolver f q₀` says: for all finite registers, every clean ancilla `a₀`,
every unit input `e₀`, every condition-number bound `κ ≥ 1` and accuracy
`0 < δ ≤ 1/2`, there is one circuit, using at most `f κ δ` calls, and a fixed
isometric output decoder `out`, such that for every unitary `U` and `B` with
`B (e₀ ⊗ a₀) = β ⊗ a₀` (`‖β‖ = 1`), `‖v‖ ≤ κ ‖M v‖` for the block
`M = ⟨a₀| U |a₀⟩`, and `M x = β`, the decoded output has squared norm at least
`q₀` and its direction is within `δ` of the direction of `x`, up to a phase.
-/

namespace SparseHamiltonian.MultiOracleCircuit.Program

noncomputable section
open OracleCircuit

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {X Y L : Type*}

/-- Change the oracle input along a fixed map; the syntax is unchanged. -/
def reindex {O : L → Y → K →L[ℂ] K} (g : X → Y) :
    Program O → Program (fun l x => O l (g x))
  | .fixed U hU => .fixed U hU
  | .query l => .query l
  | .queryAdjoint l => .queryAdjoint l
  | .seq p q => .seq (reindex g p) (reindex g q)

@[simp] theorem eval_reindex {O : L → Y → K →L[ℂ] K} (g : X → Y) (p : Program O) (x : X) :
    (reindex g p).eval x = p.eval (g x) := by
  induction p with
  | fixed U hU => rfl
  | query l => rfl
  | queryAdjoint l => rfl
  | seq p q hp hq =>
      change (reindex g p).eval x * (reindex g q).eval x = p.eval (g x) * q.eval (g x)
      rw [hp, hq]

@[simp] theorem count_reindex {O : L → Y → K →L[ℂ] K} (g : X → Y) (p : Program O) :
    (reindex g p).count = p.count := by
  induction p with
  | fixed U hU => rfl
  | query l => rfl
  | queryAdjoint l => rfl
  | seq p q hp hq =>
      change (reindex g p).count + (reindex g q).count = p.count + q.count
      rw [hp, hq]

@[simp] theorem cost_reindex {O : L → Y → K →L[ℂ] K} (g : X → Y) (p : Program O) (w : L → ℕ) :
    (reindex g p).cost w = p.cost w := by
  induction p with
  | fixed U hU => rfl
  | query l => rfl
  | queryAdjoint l => rfl
  | seq p q hp hq =>
      change (reindex g p).cost w + (reindex g q).cost w = p.cost w + q.cost w
      rw [hp, hq]

/-- Weighted costs are bounded by the count times a uniform weight bound. -/
theorem cost_le_count_mul {O : L → X → K →L[ℂ] K} (p : Program O) (w : L → ℕ) (c : ℕ)
    (hw : ∀ l, w l ≤ c) : p.cost w ≤ p.count * c := by
  induction p with
  | fixed U hU => simp [cost, count]
  | query l => simpa [cost, count] using hw l
  | queryAdjoint l => simpa [cost, count] using hw l
  | seq p q hp hq =>
      change p.cost w + q.cost w ≤ (p.count + q.count) * c
      rw [Nat.add_mul]
      exact Nat.add_le_add hp hq

end

end SparseHamiltonian.MultiOracleCircuit.Program

namespace SparseHamiltonian.GeneralODE.Solver

noncomputable section
open ContinuousLinearMap OracleCircuit Registers
open scoped InnerProduct BigOperators

variable {s a : Type} [Fintype s] [Fintype a]

/-- The solver workspace: one copy of the oracle register per solver branch. -/
abbrev Space (s a : Type) [Fintype s] [Fintype a] (w : ℕ) :=
  NativeMaskedOracle.Logical (Fin w) (s × a)

/-- Oracle inputs of the solver: the block encoding and the preparation. -/
abbrev Input (s a : Type) [Fintype s] [Fintype a] :=
  (EuclideanSpace ℂ (s × a) →L[ℂ] EuclideanSpace ℂ (s × a)) ×
    (EuclideanSpace ℂ (s × a) →L[ℂ] EuclideanSpace ℂ (s × a))

/-- Label `false` is the masked block encoding, label `true` the masked
state preparation.  The mask `ctrl` is fixed by the solver circuit. -/
def solverOracle (s a : Type) [Fintype s] [Fintype a] (w : ℕ) (ctrl : Fin w → Bool) :
    Bool → Input s a → Space s a w →L[ℂ] Space s a w :=
  fun b UB => MaskedProgram.masked ctrl (if b then UB.2 else UB.1)

/-- `v ↦ v ⊗ |a₀⟩`. -/
def embed [DecidableEq a] (a₀ : a) : EuclideanSpace ℂ s →L[ℂ] EuclideanSpace ℂ (s × a) :=
  ketR (EuclideanSpace.single a₀ 1)

/-- The block `⟨a₀| U |a₀⟩` encoded by `U`. -/
def block [DecidableEq a] (a₀ : a) (U : EuclideanSpace ℂ (s × a) →L[ℂ] EuclideanSpace ℂ (s × a)) :
    EuclideanSpace ℂ s →L[ℂ] EuclideanSpace ℂ s :=
  blk (EuclideanSpace.single a₀ 1) (EuclideanSpace.single a₀ 1) U

/-- The solver's initial state: branch `w₀`, oracle register `v`. -/
def initial {w : ℕ} (w₀ : Fin w) (v : EuclideanSpace ℂ (s × a)) : Space s a w :=
  WithLp.toLp 2 (Pi.single (M := fun _ : Fin w => EuclideanSpace ℂ (s × a)) w₀ v)

/-- **Hypothesis.**  A block-input quantum linear-system solver with query
complexity `f κ δ` and heralded success probability at least `q₀`.  The
circuit and the decoder depend only on the registers, `a₀`, `e₀`, `κ` and
`δ`; they work for every unitary block encoding and preparation. -/
def BlockSolver (f : ℝ → ℝ → ℝ) (q₀ : ℝ) : Prop :=
  ∀ (s a : Type) [Fintype s] [DecidableEq s] [Fintype a] [DecidableEq a]
    (a₀ : a) (e₀ : EuclideanSpace ℂ s), ‖e₀‖ = 1 →
  ∀ κ δ : ℝ, 1 ≤ κ → 0 < δ → δ ≤ 1 / 2 →
  ∃ (w : ℕ) (w₀ : Fin w) (ctrl : Fin w → Bool)
    (S : MultiOracleCircuit.Program (solverOracle s a w ctrl))
    (out : EuclideanSpace ℂ s →L[ℂ] Space s a w),
    out† ∘L out = 1 ∧ (S.count : ℝ) ≤ f κ δ ∧
    ∀ U B : EuclideanSpace ℂ (s × a) →L[ℂ] EuclideanSpace ℂ (s × a),
      IsUnitary U → IsUnitary B →
      ∀ β x : EuclideanSpace ℂ s, ‖β‖ = 1 →
        B (embed a₀ e₀) = embed a₀ β →
        (∀ v, ‖v‖ ≤ κ * ‖block a₀ U v‖) →
        block a₀ U x = β →
        q₀ ≤ ‖(out†) (S.eval (U, B) (initial w₀ (embed a₀ e₀)))‖ ^ 2 ∧
        ∃ ω : ℂ, ‖ω‖ = 1 ∧
          ‖ω • ODEStateNormalization.unitDirection ((out†) (S.eval (U, B) (initial w₀ (embed a₀ e₀)))) -
            ODEStateNormalization.unitDirection x‖ ≤ δ

theorem solverOracle_unitary (w : ℕ) (ctrl : Fin w → Bool) (UB : Input s a)
    (hU : IsUnitary UB.1) (hB : IsUnitary UB.2) (b : Bool) :
    IsUnitary (solverOracle s a w ctrl b UB) := by
  unfold solverOracle
  cases b
  · exact MaskedProgram.masked_unitary _ _ hU
  · exact MaskedProgram.masked_unitary _ _ hB

theorem norm_initial {w : ℕ} (w₀ : Fin w) (v : EuclideanSpace ℂ (s × a)) :
    ‖(initial w₀ v : Space s a w)‖ = ‖v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [PiLp.norm_sq_eq_of_L2]
  unfold initial
  rw [Finset.sum_eq_single w₀]
  · simp
  · intro i _ hi
    simp [hi]
  · simp

theorem embed_isometry [DecidableEq a] (a₀ : a) :
    (embed (s := s) a₀)† ∘L embed a₀ = 1 :=
  ketR_isometry _ (by simp)

end

end SparseHamiltonian.GeneralODE.Solver
