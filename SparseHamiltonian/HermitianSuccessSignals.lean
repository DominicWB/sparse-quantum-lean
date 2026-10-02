import SparseHamiltonian.OddChebyshevApproximation

/-!
# A common success spectrum for Hermitian sparse preparations

The row and column location lists may have different orders and different zero
padding. Covering all nonzero entries is sufficient to identify their success
probabilities for a Hermitian matrix. Consequently the same fixed phase list
evaluates the same amplitude polynomial on both sides of the native sparse
block encoding. These are analytical identities, with no row-sum oracle.
-/

namespace SparseHamiltonian.HermitianSuccessSignals

noncomputable section
open ContinuousLinearMap SparseSuccessProjection NativeSparsePhaseSequence
open scoped ComplexConjugate InnerProduct

section Logical
variable {n : Type*} [Fintype n] [DecidableEq n] {s : ℕ}

omit [Fintype n] [DecidableEq n] in
/-- Hermiticity makes the magnitudes symmetric, without requiring real entries. -/
theorem norm_entry_transpose (H : Matrix n n ℂ) (hH : H.IsHermitian) (i j : n) :
    ‖H i j‖ = ‖H j i‖ := by
  rw [← hH.apply i j]
  exact norm_star _

/-- Different valid padding and list order give the same row success spectrum. -/
theorem rowSuccess_locator_independent (H : Matrix n n ℂ) (a : ℝ)
    (left right : n → Fin s → n)
    (hl : ∀ i j, H i j ≠ 0 → SparseSlotStates.selected left i j)
    (hr : ∀ i j, H i j ≠ 0 → SparseSlotStates.selected right i j) (i : n) :
    rowSuccess H a left i = rowSuccess H a right i := by
  rw [rowSuccess_all H a left hl, rowSuccess_all H a right hr]

/-- Column success likewise depends only on matrix entries, not zero padding. -/
theorem columnSuccess_locator_independent (H : Matrix n n ℂ) (a : ℝ)
    (left right : n → Fin s → n)
    (hl : ∀ i j, H i j ≠ 0 → SparseSlotStates.selected left j i)
    (hr : ∀ i j, H i j ≠ 0 → SparseSlotStates.selected right j i) (j : n) :
    columnSuccess H a left j = columnSuccess H a right j := by
  rw [columnSuccess_all H a left hl, columnSuccess_all H a right hr]

/-- Independent row and column lists have identical Hermitian success spectra.
No compatibility between their zero padding slots is assumed. -/
theorem rowSuccess_eq_columnSuccess (H : Matrix n n ℂ) (hH : H.IsHermitian) (a : ℝ)
    (rowloc colloc : n → Fin s → n)
    (hr : ∀ i j, H i j ≠ 0 → SparseSlotStates.selected rowloc i j)
    (hc : ∀ i j, H i j ≠ 0 → SparseSlotStates.selected colloc j i) (i : n) :
    rowSuccess H a rowloc i = columnSuccess H a colloc i := by
  rw [rowSuccess_all H a rowloc hr, columnSuccess_all H a colloc hc]
  congr 1
  exact Finset.sum_congr rfl (fun j _ => norm_entry_transpose H hH i j)

/-- The two fixed-good-projector compressions agree as operators. -/
theorem logical_compression_eq (H : Matrix n n ℂ) (hH : H.IsHermitian)
    (a : ℝ) (ha : 0 < a) (rowloc colloc : n → Fin s → n)
    (hr : ∀ i j, H i j ≠ 0 → SparseSlotStates.selected rowloc i j)
    (hc : ∀ i j, H i j ≠ 0 → SparseSlotStates.selected colloc j i) :
    (SparseSlotStates.row H a rowloc)† ∘L good ∘L SparseSlotStates.row H a rowloc =
      (SparseSlotStates.column H a colloc)† ∘L good ∘L SparseSlotStates.column H a colloc := by
  rw [SparseSuccessProjection.row_compression H a ha,
    SparseSuccessProjection.column_compression H a ha]
  congr 1
  funext i
  exact rowSuccess_eq_columnSuccess H hH a rowloc colloc hr hc i

end Logical

section Native
variable {X n Z : Type*} [Fintype n] [DecidableEq n] {s : ℕ}

/-- Native sparse data provide exactly the coverage promises needed above. -/
theorem native_success_eq (D : NativeSparseBlockEncoding.Data X n Z s) (x : X)
    (hH : (D.matrix x).IsHermitian) (i : n) :
    rowSuccess (D.matrix x) D.scale (D.rowloc x) i =
      columnSuccess (D.matrix x) D.scale (D.colloc x) i :=
  rowSuccess_eq_columnSuccess (D.matrix x) hH D.scale (D.rowloc x) (D.colloc x)
    (D.row_covers x) (D.column_covers x) i

/-- Both actual preparation circuits see the same nonnegative scalar signal. -/
theorem rowSignal_eq_columnSignal (D : NativeSparseBlockEncoding.Data X n Z s) (x : X)
    (hH : (D.matrix x).IsHermitian) (i : n) :
    rowSignal D x i = columnSignal D x i := by
  unfold rowSignal columnSignal
  rw [native_success_eq D x hH i]

/-- A common phase sequence has equal good amplitudes on corresponding labels. -/
theorem good_polynomial_eq (D : NativeSparseBlockEncoding.Data X n Z s) (x : X)
    (hH : (D.matrix x).IsHermitian) (ss : List AmplitudePolynomialSequence.Phases) (i : n) :
    (AmplitudePolynomialSequence.polynomials ss).1.eval (rowSignal D x i : ℂ) =
      (AmplitudePolynomialSequence.polynomials ss).1.eval (columnSignal D x i : ℂ) := by
  rw [rowSignal_eq_columnSignal D x hH i]

/-- The remaining polynomial and square-root factor also share the same signal. -/
theorem polynomial_column_eq (D : NativeSparseBlockEncoding.Data X n Z s) (x : X)
    (hH : (D.matrix x).IsHermitian) (ss : List AmplitudePolynomialSequence.Phases) (i : n) :
    AmplitudePolynomialSequence.column (rowSignal D x i)
        (AmplitudePolynomialSequence.polynomials ss).1
        (AmplitudePolynomialSequence.polynomials ss).2 =
      AmplitudePolynomialSequence.column (columnSignal D x i)
        (AmplitudePolynomialSequence.polynomials ss).1
        (AmplitudePolynomialSequence.polynomials ss).2 := by
  rw [rowSignal_eq_columnSignal D x hH i]

/-- A scalar relative approximation verified for the common row signal applies
unchanged to the column signal, including its zero endpoint. -/
theorem column_relative_bound (D : NativeSparseBlockEncoding.Data X n Z s) (x : X)
    (hH : (D.matrix x).IsHermitian) (ss : List AmplitudePolynomialSequence.Phases)
    (i : n) (gain : ℂ) (δ : ℝ)
    (herr : ‖(AmplitudePolynomialSequence.polynomials ss).1.eval (rowSignal D x i : ℂ) -
      gain * (rowSignal D x i : ℂ)‖ ≤ δ * |rowSignal D x i|) :
    ‖(AmplitudePolynomialSequence.polynomials ss).1.eval (columnSignal D x i : ℂ) -
      gain * (columnSignal D x i : ℂ)‖ ≤ δ * |columnSignal D x i| := by
  simpa only [rowSignal_eq_columnSignal D x hH i] using herr

variable [Fintype Z] [AddCommGroup Z] [DecidableEq Z]

/-- Equality survives the clean-value isometry into the full native workspace. -/
theorem native_compression_eq (D : NativeSparseBlockEncoding.Data X n Z s) (x : X)
    (hH : (D.matrix x).IsHermitian) :
    (rowState D x)† ∘L goodProjection ∘L rowState D x =
      (columnState D x)† ∘L goodProjection ∘L columnState D x := by
  rw [NativeSparsePhaseSequence.row_compression, NativeSparsePhaseSequence.column_compression]
  congr 1
  funext i
  exact native_success_eq D x hH i

/-- The physical column output may use the common row signal in its analytical plane. -/
theorem columnProgram_good_common_signal (D : NativeSparseBlockEncoding.Data X n Z s)
    (ss : List AmplitudePolynomialSequence.Phases) (x : X)
    (hH : (D.matrix x).IsHermitian) (i : n) :
    goodProjection ((columnProgram D ss).eval x
      ((NativeSparseBlockEncoding.input D).toContinuousLinearMap (EuclideanSpace.single i 1))) =
      (AmplitudePolynomialSequence.polynomials ss).1.eval (rowSignal D x i : ℂ) •
        PreparationInvariantPlane.goodDirection (columnState D x) goodProjection
          (EuclideanSpace.single i 1) (rowSignal D x i) := by
  rw [rowSignal_eq_columnSignal D x hH i]
  exact columnProgram_good D ss x i

end Native
end
end SparseHamiltonian.HermitianSuccessSignals
