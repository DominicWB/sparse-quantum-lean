import SparseHamiltonian.NativeSimulationPrecision

/-!
# Eighteen primitive sparse calls for a genuine mixed program clock

The original row locator, column locator and value lookup are the complete
native vocabulary. Their exact clean basis-image promises are derived from
the sparse data. No controlled primitive, inverse locator table, or coherent
selection among these labels is assumed.
-/
namespace SparseHamiltonian.NativeSparseClock

noncomputable section
open ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding NativeSparseMaskedAccess
open scoped InnerProduct

/-- The original sparse model has exactly three explicitly named primitives. -/
instance queryFintype : Fintype Query where
  elems := {.rowLocation, .columnLocation, .value}
  complete q := by cases q <;> simp

@[simp] theorem card_query : Fintype.card Query = 3 := by decide

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s : ℕ}

/-- Actual sparse clock program, with all native labels retained. -/
def program (D : Data X n Z s) (p : MultiOracleCircuit.Program (flatOracle D)) :=
  NativeMultiProgramClock.program (flatOracle D) (cleanBasis D) p

/-- The count is independent of sparsity, matrix dimension and clock length. -/
@[simp] theorem program_count (D : Data X n Z s)
    (p : MultiOracleCircuit.Program (flatOracle D)) : (program D p).count = 18 := by
  simp [program]

/-- Six actual calls to each locator and six to the value primitive. -/
theorem program_cost (D : Data X n Z s)
    (p : MultiOracleCircuit.Program (flatOracle D)) (w : Query → ℕ) :
    (program D p).cost w = 6 * (w .rowLocation + w .columnLocation + w .value) := by
  rw [program, NativeMultiProgramClock.program_cost]
  congr 1
  change Finset.sum {.rowLocation, .columnLocation, .value} w = _
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
    reduceCtorEq, or_self, not_false_eq_true, Finset.sum_singleton]
  omega

/-- The original sparse promises suffice for exact full clean-output correctness. -/
theorem program_intertwines (D : Data X n Z s)
    (p : MultiOracleCircuit.Program (flatOracle D))
    (hInv : ∀ x v, p.eval x (p.eval x v) = v) (x : X) :
    (program D p).eval x ∘L
      (NativeMultiProgramClock.input (flatOracle D) (cleanBasis D) p).toContinuousLinearMap =
      (NativeMultiProgramClock.input (flatOracle D) (cleanBasis D) p).toContinuousLinearMap ∘L
        MultiQueryClock.programClock p (flatOracle_unitary D) hInv x :=
  NativeMultiProgramClock.program_intertwines (flatOracle D) (flatOracle_unitary D)
    (cleanBasis D) (image D) (valid D) p hInv x

/-- No clean-subspace promise is needed to establish global physical unitarity. -/
theorem program_unitary (D : Data X n Z s)
    (p : MultiOracleCircuit.Program (flatOracle D)) (x : X) :
    IsUnitary ((program D p).eval x) :=
  NativeMultiProgramClock.program_unitary (flatOracle D) (flatOracle_unitary D) (cleanBasis D) p x

end
end SparseHamiltonian.NativeSparseClock
