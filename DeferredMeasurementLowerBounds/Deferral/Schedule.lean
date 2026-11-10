import DeferredMeasurementLowerBounds.Deferral.Selection
import SparseHamiltonian.OracleTransport

set_option autoImplicit false

/-!
# Aligned schedules of selected calls

The deferred program of a measured algorithm (proof of Lemma `qlsl:lem:xor`: "padding to their
worst-case query count") is built as an **aligned schedule** `Sched`: free segments
`seg 0, seg 1, …, seg len` (programs over the selection family using only uncounted patterns
and known unitaries, so of weight zero) separated by the counted slots `slot 0, …, slot (len - 1)`,
each one call pattern of counted labels. The program `prog` is
`seg len · slot (len-1) · … · slot 0 · seg 0` and has weight exactly `len` (`cost_prog`).

This module holds the general operations: the empty schedule, prepending a slot (`consSlot`) or a
free segment (`prependFree`), and their evaluations. Schedules of the subtrees of an instrument
are aligned slot by slot in `Deferral.Align` (`Sched.align`, `Sched.eval_align`).
-/

namespace DeferredMeasurementLowerBounds.Deferral

noncomputable section
open SparseHamiltonian SparseLowerBounds ContinuousLinearMap OracleCircuit
open DeferredMeasurementLowerBounds.Model
open scoped InnerProduct

variable {K X L : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- **An aligned schedule**: free segments of weight zero and counted slots. -/
structure Sched (O : L → X → K →L[ℂ] K) (counted : L → Prop) (R : Type*) [Fintype R] where
  /-- The number of counted slots. -/
  len : ℕ
  /-- The free segments; `seg j` runs before slot `j`, `seg len` last. -/
  seg : ℕ → MultiOracleCircuit.Program (selFamily O counted R)
  /-- The counted slots. -/
  slot : ℕ → Pat {l // counted l} R
  /-- Free segments use only weight-zero labels. -/
  seg_free : ∀ j, (seg j).cost selWeight = 0

namespace Sched

variable {O : L → X → K →L[ℂ] K} {counted : L → Prop}

section General

variable {R : Type*} [Fintype R]

/-- The program up to segment `j`: `seg j · slot (j-1) · … · slot 0 · seg 0`. -/
def go (S : Sched O counted R) : ℕ → MultiOracleCircuit.Program (selFamily O counted R)
  | 0 => S.seg 0
  | j + 1 => .seq (S.seg (j + 1)) (.seq (.query (.inl (S.slot j))) (S.go j))

/-- **The program of a schedule.** -/
def prog (S : Sched O counted R) : MultiOracleCircuit.Program (selFamily O counted R) :=
  S.go S.len

/-- A schedule's program has weight exactly its number of slots. -/
theorem cost_prog (S : Sched O counted R) : S.prog.cost selWeight = S.len := by
  have h : ∀ j, (S.go j).cost selWeight = j := by
    intro j
    induction j with
    | zero => exact S.seg_free 0
    | succ j ih =>
      simp only [go, MultiOracleCircuit.Program.cost_seq, MultiOracleCircuit.Program.cost_query,
        S.seg_free, ih, selWeight]
      omega
  exact h S.len

/-- The empty schedule. -/
def empty : Sched O counted R where
  len := 0
  seg _ := MultiOracleCircuit.Program.identity
  slot _ _ := none
  seg_free _ := rfl

/-- The empty schedule's program is the identity. -/
theorem eval_empty (x : X) : (empty : Sched O counted R).prog.eval x = 1 := rfl

/-- A counted slot before the schedule `S`. -/
def consSlot (π : Pat {l // counted l} R) (S : Sched O counted R) : Sched O counted R where
  len := S.len + 1
  seg j := match j with
    | 0 => MultiOracleCircuit.Program.identity
    | j + 1 => S.seg j
  slot j := match j with
    | 0 => π
    | j + 1 => S.slot j
  seg_free j := by
    cases j with
    | zero => rfl
    | succ j => exact S.seg_free j

/-- The program with a leading slot runs the slot first. -/
theorem eval_consSlot (π : Pat {l // counted l} R) (S : Sched O counted R) (x : X) :
    (consSlot π S).prog.eval x = S.prog.eval x * selFamily O counted R (.inl π) x := by
  have h : ∀ j, ((consSlot π S).go (j + 1)).eval x =
      (S.go j).eval x * selFamily O counted R (.inl π) x := by
    intro j
    induction j with
    | zero =>
      change (S.seg 0).eval x * (selFamily O counted R (.inl π) x * 1) = _
      rw [mul_one]
      rfl
    | succ j ih =>
      change (S.seg (j + 1)).eval x * (selFamily O counted R (.inl (S.slot j)) x *
        ((consSlot π S).go (j + 1)).eval x) = _
      rw [ih]
      simp only [go, MultiOracleCircuit.Program.eval_seq, MultiOracleCircuit.Program.eval_query,
        mul_assoc]
  exact h S.len

/-- A free program before the schedule `S`. -/
def prependFree (q : MultiOracleCircuit.Program (selFamily O counted R))
    (hq : q.cost selWeight = 0) (S : Sched O counted R) : Sched O counted R where
  len := S.len
  seg j := if j = 0 then .seq (S.seg 0) q else S.seg j
  slot := S.slot
  seg_free j := by
    split_ifs
    · rw [MultiOracleCircuit.Program.cost_seq, S.seg_free, hq]
    · exact S.seg_free j

/-- The program with a leading free program runs it first. -/
theorem eval_prependFree (q : MultiOracleCircuit.Program (selFamily O counted R))
    (hq : q.cost selWeight = 0) (S : Sched O counted R) (x : X) :
    (prependFree q hq S).prog.eval x = S.prog.eval x * q.eval x := by
  have h : ∀ j, ((prependFree q hq S).go j).eval x = (S.go j).eval x * q.eval x := by
    intro j
    induction j with
    | zero =>
      change (if (0 : ℕ) = 0 then MultiOracleCircuit.Program.seq (S.seg 0) q else S.seg 0).eval x
        = _
      rw [if_pos rfl]
      rfl
    | succ j ih =>
      change (if j + 1 = 0 then MultiOracleCircuit.Program.seq (S.seg 0) q
        else S.seg (j + 1)).eval x * (selFamily O counted R (.inl (S.slot j)) x *
        ((prependFree q hq S).go j).eval x) = _
      rw [if_neg (Nat.succ_ne_zero j), ih]
      simp only [go, MultiOracleCircuit.Program.eval_seq, MultiOracleCircuit.Program.eval_query,
        mul_assoc]
  exact h S.len

end General

end Sched

end

end DeferredMeasurementLowerBounds.Deferral
