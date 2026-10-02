import SparseHamiltonian.NativeHeterogeneousActiveClock

/-!
# Counted mixed-label native distributed-clock steps

One actual native program implements the clock extracted from the source
program's syntax. Its count is six calls per primitive label, independent of
the source query count or number of clock slots. Fixed shift and link gates
are lifted through the same clean encoding without native queries.
-/
namespace SparseHamiltonian.NativeMultiProgramClock

noncomputable section
open ContinuousLinearMap OracleCircuit MultiQueryClock
open scoped InnerProduct BigOperators
set_option maxHeartbeats 800000
set_option maxRecDepth 2000

variable {B X L : Type*} [Fintype B] [DecidableEq B] [Fintype L] [DecidableEq L]

/-- The fixed clean encoding for a source program's genuine clock slots. -/
abbrev input (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (a : B) (p : MultiOracleCircuit.Program F) :=
  NativeMaskedOracle.input (ι := Fin (p.count + 1 + 1)) a

/-- Physical clock circuit: visit the native labels, then perform the fixed
link gates and cyclic shift. The prefix gauge is never implemented. -/
def program (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (a : B) (p : MultiOracleCircuit.Program F) :
    MultiOracleCircuit.Program
      (NativeMaskedProgram.oracle (ι := Fin (p.count + 1 + 1)) F) :=
  .seq (.fixed _ (SubspaceOracle.lift_unitary (input F a p).toContinuousLinearMap
    (input F a p).adjoint_comp_self (fixedClockGate p) (fixedClockGate_unitary p)))
    (NativeMultiSelected.program F a (clockChoice p))

@[simp] theorem program_count
    (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (a : B) (p : MultiOracleCircuit.Program F) :
    (program F a p).count = 6 * Fintype.card L := by simp [program]

@[simp] theorem program_cost
    (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (a : B) (p : MultiOracleCircuit.Program F) (w : L → ℕ) :
    (program F a p).cost w = 6 * ∑ l, w l := by simp [program]

/-- Exactly six calls to each original primitive, counting both directions. -/
theorem program_labelCount
    (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (a : B) (p : MultiOracleCircuit.Program F) (l : L) :
    (program F a p).labelCount l = 6 := by
  rw [MultiOracleCircuit.Program.labelCount, program_cost]
  simp

/-- Complete coherent encoded action of the actual clock program. -/
theorem program_intertwines
    (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (hF : ∀ l x, IsUnitary (F l x)) (a : B) (image : L → X → B)
    (hvalid : ∀ l x, F l x (EuclideanSpace.single a 1) = EuclideanSpace.single (image l x) 1)
    (p : MultiOracleCircuit.Program F)
    (hInv : ∀ x v, p.eval x (p.eval x v) = v) (x : X) :
    (program F a p).eval x ∘L (input F a p).toContinuousLinearMap =
      (input F a p).toContinuousLinearMap ∘L programClock p hF hInv x := by
  let E := (input F a p).toContinuousLinearMap
  have hE : E† ∘L E = 1 := (input F a p).adjoint_comp_self
  change (SubspaceOracle.lift E (fixedClockGate p) ∘L
    (NativeMultiSelected.program F a (clockChoice p)).eval x) ∘L E = _
  rw [comp_assoc, NativeMultiSelected.program_intertwines F hF a image hvalid,
    ← comp_assoc, EncodedOracle.lift_comp E hE, comp_assoc]
  rw [programClock_factor]

/-- Physical unitarity holds outside the clean encoding as well. -/
theorem program_unitary
    (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (hF : ∀ l x, IsUnitary (F l x)) (a : B)
    (p : MultiOracleCircuit.Program F) (x : X) :
    IsUnitary ((program F a p).eval x) :=
  (program F a p).eval_unitary
    (fun l y => NativeMaskedOracle.oracle_unitary (F l) (hF l) y) x

end
end SparseHamiltonian.NativeMultiProgramClock
