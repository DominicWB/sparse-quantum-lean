import SparseODE.ODEPairedValueQuery

/-!
# Full locator transport for the tagged ODE boundary

All four tag/orientation sectors start in the same known slot frame.
The transport uses the supplied full unitary locator extensions, with a
fixed coordinate exchange in the transposed tag. No common padding or
support-union locator is assumed. This fragment proves the operator
factorization; counted primitive-query syntax is a separate obligation.
-/

namespace SparseHamiltonian.ODETaggedLocators

noncomputable section
open ContinuousLinearMap OracleCircuit SparseEdgeMoments
open ODETaggedSupport ODETaggedMoments
open scoped BigOperators InnerProduct
set_option maxHeartbeats 1000000

variable {n : Type*} [Fintype n] [DecidableEq n] {s : ℕ}

/-- A fixed address swap exchanges the two incidence orientations. -/
theorem coordinateSwap_column (loc : n → Fin s → n) :
    NativeHermitianOracle.coordinateSwap ∘L columnIncidence loc = rowIncidence loc := by
  apply ContinuousLinearMap.ext
  intro v
  apply PiLp.ext
  intro e
  rcases e with ⟨i, j⟩
  change columnIncidence loc v (j, i) = rowIncidence loc v (i, j)
  simp only [columnIncidence_apply, rowIncidence_apply]

theorem coordinateSwap_row (loc : n → Fin s → n) :
    NativeHermitianOracle.coordinateSwap ∘L rowIncidence loc = columnIncidence loc := by
  apply ContinuousLinearMap.ext
  intro v
  apply PiLp.ext
  intro e
  rcases e with ⟨i, j⟩
  change rowIncidence loc v (j, i) = columnIncidence loc v (i, j)
  simp only [columnIncidence_apply, rowIncidence_apply]

/-- The two support tags share the same input-independent slot preparation. -/
def fixedFrame (slot : Fin s ↪ n) :
    EuclideanSpace ℂ n →L[ℂ] TaggedSpace n :=
  stack (rowIncidence (fun _ => slot)) (rowIncidence (fun _ => slot))

theorem fixedFrame_gram (slot : Fin s ↪ n) :
    (fixedFrame slot)† ∘L fixedFrame slot =
      (2 * (s : ℂ)) • (1 : EuclideanSpace ℂ n →L[ℂ] _) := by
  have hslot : ∀ i : n, Function.Injective (fun k : Fin s => slot k) :=
    fun _ => slot.injective
  simp only [fixedFrame, stack_adjoint_stack,
    rowIncidence_gram (fun _ => slot) hslot]
  rw [← add_smul]
  congr 1
  ring

variable {X Z : Type*}

/-- On the left orientation the second tag uses the column locator followed
by a fixed coordinate exchange. Both blocks are full-space operators. -/
def leftLocator (D : NativeSparseBlockEncoding.Data X n Z s) (x : X) :
    TaggedSpace n →L[ℂ] TaggedSpace n :=
  FixedLocatorConjugation.block (D.rowOracle x)
    (NativeHermitianOracle.coordinateSwap ∘L D.columnOracle x)

/-- The complementary orientation uses the column locator and the swapped
row locator. Its action on every invalid address remains well defined. -/
def rightLocator (D : NativeSparseBlockEncoding.Data X n Z s) (x : X) :
    TaggedSpace n →L[ℂ] TaggedSpace n :=
  FixedLocatorConjugation.block (D.columnOracle x)
    (NativeHermitianOracle.coordinateSwap ∘L D.rowOracle x)

theorem leftLocator_unitary (D : NativeSparseBlockEncoding.Data X n Z s) (x : X) :
    IsUnitary (leftLocator D x) :=
  FixedLocatorConjugation.block_unitary _ _ (D.row_unitary x)
    (NativeHermitianOracle.coordinateSwap_unitary.mul (D.column_unitary x))

theorem rightLocator_unitary (D : NativeSparseBlockEncoding.Data X n Z s) (x : X) :
    IsUnitary (rightLocator D x) :=
  FixedLocatorConjugation.block_unitary _ _ (D.column_unitary x)
    (NativeHermitianOracle.coordinateSwap_unitary.mul (D.row_unitary x))

theorem leftLocator_frame (D : NativeSparseBlockEncoding.Data X n Z s) (x : X) :
    leftLocator D x ∘L fixedFrame D.slot = leftFrame (D.rowloc x) (D.colloc x) := by
  rw [leftLocator, fixedFrame, FixedLocatorConjugation.block_stack,
    FixedLocatorConjugation.rowOracle_slots, comp_assoc,
    FixedLocatorConjugation.columnOracle_slots, coordinateSwap_column]
  rfl

theorem rightLocator_frame (D : NativeSparseBlockEncoding.Data X n Z s) (x : X) :
    rightLocator D x ∘L fixedFrame D.slot = rightFrame (D.rowloc x) (D.colloc x) := by
  rw [rightLocator, fixedFrame, FixedLocatorConjugation.block_stack,
    FixedLocatorConjugation.columnOracle_slots, comp_assoc,
    FixedLocatorConjugation.rowOracle_slots, coordinateSwap_row]
  rfl

/-- The complete locator transport, controlled only on the known orientation
and support-tag registers. -/
def locator (D : NativeSparseBlockEncoding.Data X n Z s) (x : X) :
    PrivateSpace n →L[ℂ] PrivateSpace n :=
  WeightedClock.diagonal (fun b : Bool => if b then rightLocator D x else leftLocator D x)

@[simp] theorem locator_apply_false (D : NativeSparseBlockEncoding.Data X n Z s)
    (x : X) (v : PrivateSpace n) : locator D x v false = leftLocator D x (v false) := rfl

@[simp] theorem locator_apply_true (D : NativeSparseBlockEncoding.Data X n Z s)
    (x : X) (v : PrivateSpace n) : locator D x v true = rightLocator D x (v true) := rfl

theorem locator_unitary (D : NativeSparseBlockEncoding.Data X n Z s) (x : X) :
    IsUnitary (locator D x) := by
  apply CoherentQuerySchedule.diagonal_unitary
  intro b
  cases b
  · exact leftLocator_unitary D x
  · exact rightLocator_unitary D x

/-- A common public preparation for every matrix instance, LCHS node and
evolution duration. Its only inputs are the original slot labels and count. -/
def fixedBoundary (slot : Fin s ↪ n) :
    EuclideanSpace ℂ n →L[ℂ] PrivateSpace n :=
  boundaryWeight (2 * s) • pair (fixedFrame slot) (fixedFrame slot)

theorem fixedBoundary_isometry (slot : Fin s ↪ n) (hs : 0 < s) :
    (fixedBoundary slot)† ∘L fixedBoundary slot = 1 := by
  simp only [fixedBoundary, map_smulₛₗ, conj_boundaryWeight,
    smul_comp, comp_smul, smul_smul, pair_adjoint_pair, fixedFrame_gram]
  rw [← add_smul, smul_smul]
  have hc : (boundaryWeight (2 * s) * boundaryWeight (2 * s)) *
      (2 * (s : ℂ) + 2 * (s : ℂ)) = 1 := by
    convert boundaryWeight_sq (Nat.mul_pos (show 0 < (2 : ℕ) by decide) hs) using 1
    push_cast
    ring
  rw [hc, one_smul]

theorem locator_pair (D : NativeSparseBlockEncoding.Data X n Z s) (x : X)
    (A B : EuclideanSpace ℂ n →L[ℂ] TaggedSpace n) :
    locator D x ∘L pair A B =
      pair (leftLocator D x ∘L A) (rightLocator D x ∘L B) := by
  apply ContinuousLinearMap.ext
  intro v
  apply PiLp.ext
  intro b
  cases b <;> simp only [comp_apply, locator_apply_false, locator_apply_true,
    pair_false, pair_true]

/-- The original row and column locators, rather than a locator for their
support union, exactly produce the normalized tagged boundary. -/
theorem locator_boundary (D : NativeSparseBlockEncoding.Data X n Z s) (x : X) :
    locator D x ∘L fixedBoundary D.slot =
      ODETaggedMoments.boundary (D.rowloc x) (D.colloc x) := by
  rw [fixedBoundary, comp_smul, locator_pair, leftLocator_frame, rightLocator_frame]
  rfl

/-- Reversing the full unitary transport returns the same known public
boundary even when row-list and column-list padding are unrelated. -/
theorem locator_adjoint_boundary (D : NativeSparseBlockEncoding.Data X n Z s) (x : X) :
    (locator D x)† ∘L ODETaggedMoments.boundary (D.rowloc x) (D.colloc x) =
      fixedBoundary D.slot := by
  rw [← locator_boundary D x, ← comp_assoc]
  have h : (locator D x)† ∘L locator D x = 1 := (locator_unitary D x).1
  rw [h]
  simp only [one_def, id_comp]

/-- Combined full-space and known-boundary certificate for native sparse
data. No query count is assigned until the primitive circuit is compiled. -/
theorem native_locator_certificate (D : NativeSparseBlockEncoding.Data X n Z s)
    (x : X) :
    IsUnitary (locator D x) ∧
      (fixedBoundary D.slot)† ∘L fixedBoundary D.slot = 1 ∧
      locator D x ∘L fixedBoundary D.slot =
        ODETaggedMoments.boundary (D.rowloc x) (D.colloc x) ∧
      (locator D x)† ∘L ODETaggedMoments.boundary (D.rowloc x) (D.colloc x) =
        fixedBoundary D.slot :=
  ⟨locator_unitary D x, fixedBoundary_isometry D.slot D.slots_pos,
    locator_boundary D x, locator_adjoint_boundary D x⟩

end
end SparseHamiltonian.ODETaggedLocators
