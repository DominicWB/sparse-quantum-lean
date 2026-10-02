import SparseHamiltonian.SparseSuccessProjection

/-!
# Fresh-flag attenuation of the actual sparse-slot preparations

The distinct original row/column failure flags make the abstract orthogonality
hypothesis automatic, including padded zero slots. Quarter-gain attenuation
therefore reduces the full row/column overlap by exactly sixteen. It uses
fixed unitary gates and fresh orthogonal failure sectors, not a rotation of
previously occupied failure amplitude.
-/

namespace SparseHamiltonian.SparseFreshAttenuation

noncomputable section
open ContinuousLinearMap SparseSlotStates SparseSuccessProjection FreshFlagAttenuation
open scoped BigOperators InnerProduct
set_option maxHeartbeats 800000

variable {n : Type*} [Fintype n] [DecidableEq n] {s : ℕ}

/-- Original row failure has flag one and original column failure flag two.
Their overlap is zero without matching zero-padding entries across lists. -/
theorem old_failure_orthogonal (H : Matrix n n ℂ) (a : ℝ)
    (rowloc colloc : n → Fin s → n) :
    (row H a rowloc)† ∘L (1 - good) ∘L column H a colloc = 0 := by
  apply ContinuousLinearMap.ext
  intro v
  apply ext_inner_right ℂ
  intro u
  simp only [comp_apply, adjoint_inner_left, zero_apply, inner_zero_left,
    PiLp.inner_apply, Fintype.sum_prod_type, sub_apply, one_def, id_apply,
    PiLp.sub_apply, good_apply, row_apply, column_apply, RCLike.inner_apply]
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  by_cases hr : selected rowloc i j <;> by_cases hc : selected colloc j i <;>
    simp [hr, hc, Fin.sum_univ_succ, rowEntry, columnEntry]

/-- The concrete row preparation after query-free attenuation. -/
def attenuatedRow (H : Matrix n n ℂ) (a c : ℝ) (loc : n → Fin s → n) :
    EuclideanSpace ℂ n →L[ℂ] Triple (SparseSlotStates.Space n) :=
  rowPreparation good c ∘L row H a loc

/-- The concrete column preparation, with its separate new failure sector. -/
def attenuatedColumn (H : Matrix n n ℂ) (a c : ℝ) (loc : n → Fin s → n) :
    EuclideanSpace ℂ n →L[ℂ] Triple (SparseSlotStates.Space n) :=
  columnPreparation good c ∘L column H a loc

/-- Every real attenuation factor scales total overlap by its square. -/
theorem overlap (H : Matrix n n ℂ) (a c : ℝ) (rowloc colloc : n → Fin s → n) :
    (attenuatedRow H a c rowloc)† ∘L attenuatedColumn H a c colloc =
      ((c : ℂ) ^ 2) • ((row H a rowloc)† ∘L column H a colloc) :=
  prepared_overlap_full (good (n := n)) good_orthogonal c (row H a rowloc) (column H a colloc)
    (old_failure_orthogonal H a rowloc colloc)

/-- Exact sparse-matrix compression after attenuation. -/
theorem overlap_matrix (H : Matrix n n ℂ) (a : ℝ) (ha : 0 < a) (c : ℝ)
    (rowloc colloc : n → Fin s → n)
    (hrow : ∀ i j, H i j ≠ 0 → selected rowloc i j)
    (hcol : ∀ i j, H i j ≠ 0 → selected colloc j i) :
    (attenuatedRow H a c rowloc)† ∘L attenuatedColumn H a c colloc =
      ((c : ℂ) ^ 2) • SparseStateOverlap.matrixOperator
        (fun i j => H i j / ((s : ℂ) * a)) := by
  rw [overlap, overlap_eq_matrix H a ha rowloc colloc hrow hcol]

/-- Quarter attenuation gives the promised factor of sixteen with no remaining
old-failure orthogonality premise. -/
theorem quarter_overlap_matrix (H : Matrix n n ℂ) (a : ℝ) (ha : 0 < a)
    (rowloc colloc : n → Fin s → n)
    (hrow : ∀ i j, H i j ≠ 0 → selected rowloc i j)
    (hcol : ∀ i j, H i j ≠ 0 → selected colloc j i) :
    (attenuatedRow H a (1 / 4) rowloc)† ∘L attenuatedColumn H a (1 / 4) colloc =
      (1 / 16 : ℂ) • SparseStateOverlap.matrixOperator
        (fun i j => H i j / ((s : ℂ) * a)) := by
  rw [overlap_matrix H a ha (1 / 4) rowloc colloc hrow hcol]
  norm_num

end
end SparseHamiltonian.SparseFreshAttenuation
