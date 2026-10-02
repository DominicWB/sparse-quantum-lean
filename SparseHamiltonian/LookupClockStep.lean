import SparseHamiltonian.MaskedLookupCurry

/-!
# Two ordinary lookup queries implement a distributed program clock

Normal-form oracle polarities are compiled into one signed mask on the clock
register. Compute/copy/uncompute cancels arbitrary initial scratch contents,
so the two-query statement holds on the full clock workspace. It applies to
any uniform lookup program whose output is a Hermitian involution; no unknown
program gate or prefix gauge is treated as free.
-/

namespace SparseHamiltonian.LookupClockStep

noncomputable section
open ContinuousLinearMap OracleCircuit QueryClockLinks QueryClockStep ClockStepQuery
open MaskedLookupCurry

variable {X A Z : Type*} [Fintype A] [Fintype Z] [AddCommGroup Z]

/-- Signed integer weight encoding the three possible normal-form query letters. -/
def polarityWeight : Option Bool → ℤ
  | none => 0
  | some false => 1
  | some true => -1

/-- Each optional query is precisely a signed ordinary lookup. -/
theorem localSigned_polarity (b : Option Bool) (f : X → A → Z) (x : X) :
    localSigned (polarityWeight b) f x = optionalQuery (localSigned 1 f) b x := by
  cases b with
  | none => simp [polarityWeight, optionalQuery]
  | some b => cases b <;>
      simp [polarityWeight, optionalQuery, QueryNormalForm.NormalForm.queryOperator,
        localSigned_neg_one]

/-- Fixed signed mask on all actual clock slots; the return slot has weight zero. -/
def clockMask (f : X → A → Z) (p : Program (localSigned 1 f)) :
    Fin (p.count + 1 + 1) → ℤ :=
  Fin.lastCases 0 (fun j : Fin (p.count + 1) => polarityWeight (clockLinkData p j.val).2)

/-- The signed diagonal circuit is exactly the SELECT extracted from the program. -/
theorem signed_diagonal_eq_selected (f : X → A → Z)
    (p : Program (localSigned 1 f)) (x : X) :
    WeightedClock.diagonal (fun i => localSigned (clockMask f p i) f x) =
      selectedQueries p x := by
  apply ContinuousLinearMap.ext
  intro v
  apply PiLp.ext
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [clockMask, selectedQueries, paddedSelect]
  · simp only [WeightedClock.diagonal_apply, clockMask, Fin.lastCases_castSucc,
      localSigned_polarity, selectedQueries, paddedSelect]

/-- Forward, inverse, and idle program-clock links all share the same two
ordinary lookup calls, independently of the length of the original program. -/
theorem selectedQueries_two_queries (f : X → A → Z)
    (p : Program (localSigned 1 f)) :
    Implements (MaskedLookupCurry.oracle (I := Fin (p.count + 1 + 1)) f)
      (selectedQueries p) 2 := by
  exact (diagonal_two_queries (clockMask f p) f).congr
    (fun x => signed_diagonal_eq_selected f p x)

/-- One step of the actual distributed involution clock costs two calls to
an ordinary lookup oracle with spectator registers. The clock has `q+2` slots
for an original program with `q` queries. -/
theorem programClock_two_queries (f : X → A → Z)
    (p : Program (localSigned 1 f))
    (hInv : ∀ x v, p.eval x (p.eval x v) = v) :
    Implements (MaskedLookupCurry.oracle (I := Fin (p.count + 1 + 1)) f)
      (programClock p (localSigned_unitary 1 f) hInv) 2 :=
  programClock_implements p (localSigned_unitary 1 f) hInv _ 2
    (selectedQueries_two_queries f p)

/-- The bound is witnessed by a single uniform program, with no gauge oracle. -/
theorem exists_two_query_programClock (f : X → A → Z)
    (p : Program (localSigned 1 f))
    (hInv : ∀ x v, p.eval x (p.eval x v) = v) :
    ∃ c : Program (MaskedLookupCurry.oracle (I := Fin (p.count + 1 + 1)) f),
      c.count ≤ 2 ∧
      (∀ x, c.eval x = programClock p (localSigned_unitary 1 f) hInv x) ∧
      slots p ≤ 2 * (p.count + 1) := by
  obtain ⟨c, hEval, hCount⟩ := programClock_two_queries f p hInv
  exact ⟨c, hCount, hEval, slots_le_twice p⟩

end
end SparseHamiltonian.LookupClockStep
