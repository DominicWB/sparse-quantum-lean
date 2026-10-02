import SparseODE.ODENativeLayout

/-!
# Counted native locator program for the tagged ODE boundary

Two fixed masks send the four orientation/tag sectors through their original
row or column locator. A query-free address swap in the transposed tag then
produces the full locator used by the analytic moment construction. The value
words and flag register are spectators throughout this program.

-/

namespace SparseHamiltonian.ODENativeLocator

noncomputable section
open ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding
open ODENativeLayout
open scoped InnerProduct
set_option maxHeartbeats 1000000
set_option maxRecDepth 3000

variable {X n Z : Type*} [Fintype n] [DecidableEq n]
  [Fintype Z] [AddCommGroup Z] [DecidableEq Z] {s : ℕ}

/-- Address exchange with the native value and flag registers untouched. -/
def baseSwap :
    EuclideanSpace ℂ (NativeSparseMaskedAccess.Basis n Z) →L[ℂ]
      EuclideanSpace ℂ (NativeSparseMaskedAccess.Basis n Z) :=
  (NativeSparseMaskedAccess.layout (n := n) (Z := Z)).conjStarAlgEquiv
    (NativeHermitianOracle.physicalSwap (n := n) (Z := Z))

omit [DecidableEq n] [AddCommGroup Z] [DecidableEq Z] in
theorem baseSwap_unitary : IsUnitary (baseSwap (n := n) (Z := Z)) :=
  (NativeHermitianOracle.physicalSwap_unitary (n := n) (Z := Z)).transport
    (NativeSparseMaskedAccess.layout (n := n) (Z := Z))

omit [DecidableEq n] [AddCommGroup Z] [DecidableEq Z] in
@[simp] theorem baseSwap_apply
    (v : EuclideanSpace ℂ (NativeSparseMaskedAccess.Basis n Z))
    (e : n × n) (z : Z) (f : Fin 3) :
    baseSwap v ((e, z), f) = v ((e.swap, z), f) := rfl

omit [DecidableEq n] in
/-- Fixed coordinate exchange commutes with initialization of native scratch. -/
theorem baseSwap_edgeClean (v : SparseEdgeMoments.EdgeSpace n) :
    baseSwap (OrientedNativeLayout.edgeClean (Z := Z) v) =
      OrientedNativeLayout.edgeClean
        (NativeHermitianOracle.coordinateSwap (n := n) v) :=
  OrientedNativeLayout.location_edgeClean
    (fun _ : Unit => NativeHermitianOracle.coordinateSwap (n := n)) () v

/-- Only the transposed support tag receives the fixed address exchange. -/
def freeSwap : Space n Z →L[ℂ] Space n Z :=
  MaskedProgram.masked (fun b : Branch Z => b.1.2) (baseSwap (n := n) (Z := Z))

omit [DecidableEq n] [AddCommGroup Z] [DecidableEq Z] in
theorem freeSwap_unitary : IsUnitary (freeSwap (n := n) (Z := Z)) :=
  MaskedProgram.masked_unitary (fun b : Branch Z => b.1.2)
    (baseSwap (n := n) (Z := Z)) baseSwap_unitary

omit [DecidableEq n] [AddCommGroup Z] [DecidableEq Z] in
@[simp] theorem freeSwap_branch (v : Space n Z) (o a : Bool) (u : Z) :
    freeSwap v ((o, a), u) =
      if a then baseSwap (v ((o, a), u)) else v ((o, a), u) :=
  MaskedProgram.masked_apply _ _ _ _

omit [DecidableEq n] [AddCommGroup Z] [DecidableEq Z] in
/-- On arbitrary scratch, the tag controls only a known coordinate exchange. -/
@[simp] theorem freeSwap_apply (v : Space n Z) (o a : Bool) (u : Z)
    (e : n × n) (z : Z) (f : Fin 3) :
    freeSwap v ((o, a), u) ((e, z), f) =
      v ((o, a), u) (((if a then e.swap else e), z), f) := by
  cases a <;> simp only [freeSwap_branch, Bool.false_eq_true, if_false, if_true,
    baseSwap_apply]

/-- Fixed instruction order: row query, column query, then the free swap.
The orientation/tag mask never selects which native label is called. -/
def locatorProgram (D : Data X n Z s) : MultiOracleCircuit.Program (logicalOracle D) :=
  .seq (.fixed (freeSwap (n := n) (Z := Z)) freeSwap_unitary)
    (.seq (.query .columnLocation) (.query .rowLocation))

omit [DecidableEq Z] in
@[simp] theorem locatorProgram_count (D : Data X n Z s) :
    (locatorProgram D).count = 2 := rfl

omit [DecidableEq Z] in
@[simp] theorem locatorProgram_cost (D : Data X n Z s) (w : Query → ℕ) :
    (locatorProgram D).cost w = w .rowLocation + w .columnLocation := by
  change 0 + (w .columnLocation + w .rowLocation) = _
  omega

/-- The literal program implements the full locator, including padded and
invalid addresses. No agreement between row and column padding is needed. -/
theorem locatorProgram_intertwines (D : Data X n Z s) (x : X) :
    (locatorProgram D).eval x ∘L (clean (n := n) (Z := Z)).toContinuousLinearMap =
      clean.toContinuousLinearMap ∘L ODETaggedLocators.locator D x := by
  apply ContinuousLinearMap.ext
  intro v
  apply PiLp.ext
  intro b
  rcases b with ⟨⟨o, a⟩, u⟩
  cases o <;> cases a <;> by_cases hu : u = 0 <;>
    simp [locatorProgram, MultiOracleCircuit.Program.eval_seq,
      MultiOracleCircuit.Program.eval_fixed, MultiOracleCircuit.Program.eval_query,
      mul_apply_eq_comp, comp_apply, freeSwap_branch, logicalOracle,
      NativeMaskedProgram.logicalOracle, MaskedProgram.masked_apply, masks,
      clean_branch_parts, hu,
      ODETaggedLocators.locator_apply_false, ODETaggedLocators.locator_apply_true,
      ODETaggedLocators.leftLocator, ODETaggedLocators.rightLocator,
      FixedLocatorConjugation.leftPart_block, FixedLocatorConjugation.rightPart_block]
  · exact OrientedNativeLayout.row_edgeClean D x
      (FixedLocatorConjugation.leftPart (v false))
  · change baseSwap (n := n) (Z := Z)
        (NativeSparseMaskedAccess.flatOracle D Query.columnLocation x
          (OrientedNativeLayout.edgeClean (Z := Z)
            (FixedLocatorConjugation.rightPart (v false)))) = _
    rw [OrientedNativeLayout.column_edgeClean, baseSwap_edgeClean]
  · exact OrientedNativeLayout.column_edgeClean D x
      (FixedLocatorConjugation.leftPart (v true))
  · change baseSwap (n := n) (Z := Z)
        (NativeSparseMaskedAccess.flatOracle D Query.rowLocation x
          (OrientedNativeLayout.edgeClean (Z := Z)
            (FixedLocatorConjugation.rightPart (v true)))) = _
    rw [OrientedNativeLayout.row_edgeClean, baseSwap_edgeClean]

omit [DecidableEq Z] in
theorem locatorProgram_unitary (D : Data X n Z s) (x : X) :
    IsUnitary ((locatorProgram D).eval x) :=
  (locatorProgram D).eval_unitary (logicalOracle_unitary D) x

end
end SparseHamiltonian.ODENativeLocator
