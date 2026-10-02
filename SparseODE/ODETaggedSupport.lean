import SparseODE.ODEMatrixEnergy

/-!
# Two tagged copies of an original sparse support

The tags use the original row and column lists, interchanged in the second
tag.  Independently padded lists need not agree: the corresponding diagonal
entry vanishes whenever the original matrix entry vanishes.  Splitting an
entry equally when both supports contain it preserves cancellation and does
not increase row or column energy.

This fragment proves the concrete frame and boundary identities.  It does
not yet supply the native query program for the tagged Cayley rotation.
-/

namespace SparseHamiltonian.ODETaggedSupport

noncomputable section
open ContinuousLinearMap SparseSlotStates SparseEdgeMoments
open scoped BigOperators InnerProduct ComplexConjugate

variable {n : Type*} [Fintype n] [DecidableEq n] {s : ℕ}

/-- The tag supported on entries of the original matrix. -/
def tagZero (M K : Matrix n n ℂ) : Matrix n n ℂ := fun i j =>
  if M i j = 0 then 0 else if M j i = 0 then K i j else K i j / 2

/-- The tag supported on transposed entries of the original matrix. -/
def tagOne (M K : Matrix n n ℂ) : Matrix n n ℂ := fun i j =>
  if M j i = 0 then 0 else if M i j = 0 then K i j else K i j / 2

/-- A Boolean form of the two diagonal entries. -/
def tagValue (M K : Matrix n n ℂ) (a : Bool) : Matrix n n ℂ :=
  if a then tagOne M K else tagZero M K

omit [Fintype n] [DecidableEq n] in
@[simp] theorem tagValue_false (M K : Matrix n n ℂ) :
    tagValue M K false = tagZero M K := rfl

omit [Fintype n] [DecidableEq n] in
@[simp] theorem tagValue_true (M K : Matrix n n ℂ) :
    tagValue M K true = tagOne M K := rfl

omit [Fintype n] [DecidableEq n] in
theorem tagZero_eq_zero (M K : Matrix n n ℂ) (i j : n) (h : M i j = 0) :
    tagZero M K i j = 0 := by simp [tagZero, h]

omit [Fintype n] [DecidableEq n] in
theorem tagOne_eq_zero (M K : Matrix n n ℂ) (i j : n) (h : M j i = 0) :
    tagOne M K i j = 0 := by simp [tagOne, h]

omit [Fintype n] [DecidableEq n] in
theorem tagZero_ne_zero (M K : Matrix n n ℂ) (i j : n)
    (h : tagZero M K i j ≠ 0) : M i j ≠ 0 := by
  intro hm
  exact h (tagZero_eq_zero M K i j hm)

omit [Fintype n] [DecidableEq n] in
theorem tagOne_ne_zero (M K : Matrix n n ℂ) (i j : n)
    (h : tagOne M K i j ≠ 0) : M j i ≠ 0 := by
  intro hm
  exact h (tagOne_eq_zero M K i j hm)

omit [Fintype n] [DecidableEq n] in
/-- The only support promise is containment in the union of the two supports. -/
theorem tag_sum (M K : Matrix n n ℂ)
    (hK : ∀ i j, M i j = 0 → M j i = 0 → K i j = 0) (i j : n) :
    tagZero M K i j + tagOne M K i j = K i j := by
  by_cases h₀ : M i j = 0
  · by_cases h₁ : M j i = 0
    · simp [tagZero, tagOne, h₀, h₁, hK i j h₀ h₁]
    · simp [tagZero, tagOne, h₀, h₁]
  · by_cases h₁ : M j i = 0
    · simp [tagZero, tagOne, h₀, h₁]
    · simp only [tagZero, tagOne, h₀, h₁, if_false]
      ring

omit [Fintype n] [DecidableEq n] in
/-- Sharing an entry between the tags never duplicates its squared magnitude. -/
theorem tag_energy_le (M K : Matrix n n ℂ) (i j : n) :
    ‖tagZero M K i j‖ ^ 2 + ‖tagOne M K i j‖ ^ 2 ≤ ‖K i j‖ ^ 2 := by
  by_cases h₀ : M i j = 0
  · by_cases h₁ : M j i = 0
    · norm_num [tagZero, tagOne, h₀, h₁]
    · norm_num [tagZero, tagOne, h₀, h₁]
  · by_cases h₁ : M j i = 0
    · norm_num [tagZero, tagOne, h₀, h₁]
    · norm_num [tagZero, tagOne, h₀, h₁, norm_div]
      nlinarith [sq_nonneg ‖K i j‖]

omit [Fintype n] [DecidableEq n] in
theorem tagZero_norm_le (M K : Matrix n n ℂ) (i j : n) :
    ‖tagZero M K i j‖ ≤ ‖K i j‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  exact (le_add_of_nonneg_right (sq_nonneg ‖tagOne M K i j‖)).trans
    (tag_energy_le M K i j)

omit [Fintype n] [DecidableEq n] in
theorem tagOne_norm_le (M K : Matrix n n ℂ) (i j : n) :
    ‖tagOne M K i j‖ ≤ ‖K i j‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  exact (le_add_of_nonneg_left (sq_nonneg ‖tagZero M K i j‖)).trans
    (tag_energy_le M K i j)

omit [DecidableEq n] in
theorem row_energy_le (M K : Matrix n n ℂ) (i : n) :
    (∑ j, ‖tagZero M K i j‖ ^ 2) + (∑ j, ‖tagOne M K i j‖ ^ 2) ≤
      ∑ j, ‖K i j‖ ^ 2 := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun j _ => tag_energy_le M K i j

omit [DecidableEq n] in
theorem column_energy_le (M K : Matrix n n ℂ) (j : n) :
    (∑ i, ‖tagZero M K i j‖ ^ 2) + (∑ i, ‖tagOne M K i j‖ ^ 2) ≤
      ∑ i, ‖K i j‖ ^ 2 := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => tag_energy_le M K i j

/-- Here the two sum sectors are support tags, not generator orientations. -/
abbrev TaggedSpace (n : Type*) [Fintype n] := SparseEdgeMoments.OrientedSpace n

def leftFrame (rowloc colloc : n → Fin s → n) :
    EuclideanSpace ℂ n →L[ℂ] TaggedSpace n :=
  stack (rowIncidence rowloc) (rowIncidence colloc)

def rightFrame (rowloc colloc : n → Fin s → n) :
    EuclideanSpace ℂ n →L[ℂ] TaggedSpace n :=
  stack (columnIncidence colloc) (columnIncidence rowloc)

/-- Both tags use exactly the original `s` slots, so the frame weight is `2s`. -/
theorem leftFrame_gram (rowloc colloc : n → Fin s → n)
    (hrow : ∀ i, Function.Injective (rowloc i))
    (hcol : ∀ i, Function.Injective (colloc i)) :
    (leftFrame rowloc colloc)† ∘L leftFrame rowloc colloc =
      (2 * (s : ℂ)) • (1 : EuclideanSpace ℂ n →L[ℂ] _) := by
  rw [leftFrame, stack_adjoint_stack, rowIncidence_gram rowloc hrow,
    rowIncidence_gram colloc hcol, ← add_smul]
  congr 1
  ring

theorem rightFrame_gram (rowloc colloc : n → Fin s → n)
    (hrow : ∀ i, Function.Injective (rowloc i))
    (hcol : ∀ i, Function.Injective (colloc i)) :
    (rightFrame rowloc colloc)† ∘L rightFrame rowloc colloc =
      (2 * (s : ℂ)) • (1 : EuclideanSpace ℂ n →L[ℂ] _) := by
  rw [rightFrame, stack_adjoint_stack, columnIncidence_gram colloc hcol,
    columnIncidence_gram rowloc hrow, ← add_smul]
  congr 1
  ring

/-- The physical diagonal explicitly kills unmatched zero padding. -/
def diagonal (M K : Matrix n n ℂ) : TaggedSpace n →L[ℂ] TaggedSpace n :=
  RelativeAmplitudeError.complexDiagonal
    (Sum.elim (fun e : n × n => tagZero M K e.1 e.2)
      (fun e : n × n => tagOne M K e.1 e.2))

omit [DecidableEq n] in
theorem diagonal_stack (M K : Matrix n n ℂ)
    (A B : EuclideanSpace ℂ n →L[ℂ] EdgeSpace n) :
    diagonal M K ∘L stack A B =
      stack (edgeDiagonal (tagZero M K) ∘L A)
        (edgeDiagonal (tagOne M K) ∘L B) := by
  ext v e
  cases e <;> rfl

omit [DecidableEq n] in
theorem adjoint_diagonal_stack (M K : Matrix n n ℂ)
    (A B : EuclideanSpace ℂ n →L[ℂ] EdgeSpace n) :
    (diagonal M K)† ∘L stack A B =
      stack ((edgeDiagonal (tagZero M K))† ∘L A)
        ((edgeDiagonal (tagOne M K))† ∘L B) := by
  rw [diagonal, RelativeAmplitudeError.complexDiagonal_adjoint,
    edgeDiagonal_adjoint, edgeDiagonal_adjoint]
  ext v e
  cases e <;> rfl

omit [DecidableEq n] in
/-- An entry bound controls the entire diagonal, including all unused edges. -/
theorem diagonal_norm_le (M K : Matrix n n ℂ) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hK : ∀ i j, ‖K i j‖ ≤ ρ) : ‖diagonal M K‖ ≤ ρ := by
  apply RelativeAmplitudeError.norm_complexDiagonal_le _ ρ hρ
  intro e
  cases e with
  | inl e => exact (tagZero_norm_le M K e.1 e.2).trans (hK e.1 e.2)
  | inr e => exact (tagOne_norm_le M K e.1 e.2).trans (hK e.1 e.2)

/-- This is the exact overlap in the original lists; no union locator occurs. -/
theorem frame_overlap (M K : Matrix n n ℂ) (rowloc colloc : n → Fin s → n)
    (hrow : ∀ i j, M i j ≠ 0 → selected rowloc i j)
    (hcol : ∀ i j, M i j ≠ 0 → selected colloc j i)
    (hK : ∀ i j, M i j = 0 → M j i = 0 → K i j = 0) :
    (leftFrame rowloc colloc)† ∘L diagonal M K ∘L rightFrame rowloc colloc =
      SparseStateOverlap.matrixOperator K := by
  have h₀r : ∀ i j, tagZero M K i j ≠ 0 → selected rowloc i j :=
    fun i j h => hrow i j (tagZero_ne_zero M K i j h)
  have h₀c : ∀ i j, tagZero M K i j ≠ 0 → selected colloc j i :=
    fun i j h => hcol i j (tagZero_ne_zero M K i j h)
  have h₁r : ∀ i j, tagOne M K i j ≠ 0 → selected colloc i j :=
    fun i j h => hcol j i (tagOne_ne_zero M K i j h)
  have h₁c : ∀ i j, tagOne M K i j ≠ 0 → selected rowloc j i :=
    fun i j h => hrow j i (tagOne_ne_zero M K i j h)
  rw [leftFrame, rightFrame, diagonal_stack, stack_adjoint_stack,
    incidence_overlap (tagZero M K) rowloc colloc h₀r h₀c,
    incidence_overlap (tagOne M K) colloc rowloc h₁r h₁c]
  ext v i
  change (∑ j, tagZero M K i j * v j) + (∑ j, tagOne M K i j * v j) =
    ∑ j, K i j * v j
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [← add_mul, tag_sum M K hK i j]

/-- The two tagged column responses together retain the original energy bound. -/
theorem right_boundary_energy_le (M K : Matrix n n ℂ)
    (rowloc colloc : n → Fin s → n)
    (hrow : ∀ i j, M i j ≠ 0 → selected rowloc i j)
    (hcol : ∀ i j, M i j ≠ 0 → selected colloc j i)
    (ρ : ℝ) (hK : ∀ j, ∑ i, ‖K i j‖ ^ 2 ≤ ρ ^ 2)
    (v : EuclideanSpace ℂ n) :
    ‖diagonal M K (rightFrame rowloc colloc v)‖ ^ 2 ≤ ρ ^ 2 * ‖v‖ ^ 2 := by
  have h₀c : ∀ i j, tagZero M K i j ≠ 0 → selected colloc j i :=
    fun i j h => hcol i j (tagZero_ne_zero M K i j h)
  have h₁c : ∀ i j, tagOne M K i j ≠ 0 → selected rowloc j i :=
    fun i j h => hrow j i (tagOne_ne_zero M K i j h)
  have he := congrArg (fun T : EuclideanSpace ℂ n →L[ℂ] TaggedSpace n => T v)
    (diagonal_stack M K (columnIncidence colloc) (columnIncidence rowloc))
  change diagonal M K (rightFrame rowloc colloc v) =
    stack (edgeDiagonal (tagZero M K) ∘L columnIncidence colloc)
      (edgeDiagonal (tagOne M K) ∘L columnIncidence rowloc) v at he
  rw [he, stack_norm_sq]
  simp only [comp_apply]
  rw [diagonal_column_norm_sq (tagZero M K) colloc h₀c,
    diagonal_column_norm_sq (tagOne M K) rowloc h₁c]
  calc
    _ = ∑ j, ((∑ i, ‖tagZero M K i j‖ ^ 2) +
        (∑ i, ‖tagOne M K i j‖ ^ 2)) * ‖v j‖ ^ 2 := by
      simp only [add_mul, Finset.sum_add_distrib]
    _ ≤ ∑ j, ρ ^ 2 * ‖v j‖ ^ 2 :=
      Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right
        ((column_energy_le M K j).trans (hK j)) (sq_nonneg _)
    _ = ρ ^ 2 * ‖v‖ ^ 2 := by
      rw [← Finset.mul_sum, PiLp.norm_sq_eq_of_L2]

/-- The adjoint diagonal has the corresponding original row-energy bound. -/
theorem left_boundary_energy_le (M K : Matrix n n ℂ)
    (rowloc colloc : n → Fin s → n)
    (hrow : ∀ i j, M i j ≠ 0 → selected rowloc i j)
    (hcol : ∀ i j, M i j ≠ 0 → selected colloc j i)
    (ρ : ℝ) (hK : ∀ i, ∑ j, ‖K i j‖ ^ 2 ≤ ρ ^ 2)
    (v : EuclideanSpace ℂ n) :
    ‖((diagonal M K)†) (leftFrame rowloc colloc v)‖ ^ 2 ≤ ρ ^ 2 * ‖v‖ ^ 2 := by
  have h₀r : ∀ i j, tagZero M K i j ≠ 0 → selected rowloc i j :=
    fun i j h => hrow i j (tagZero_ne_zero M K i j h)
  have h₁r : ∀ i j, tagOne M K i j ≠ 0 → selected colloc i j :=
    fun i j h => hcol j i (tagOne_ne_zero M K i j h)
  have he := congrArg (fun T : EuclideanSpace ℂ n →L[ℂ] TaggedSpace n => T v)
    (adjoint_diagonal_stack M K (rowIncidence rowloc) (rowIncidence colloc))
  change ((diagonal M K)†) (leftFrame rowloc colloc v) =
    stack ((edgeDiagonal (tagZero M K))† ∘L rowIncidence rowloc)
      ((edgeDiagonal (tagOne M K))† ∘L rowIncidence colloc) v at he
  rw [he, stack_norm_sq]
  simp only [comp_apply]
  rw [adjointDiagonal_row_norm_sq (tagZero M K) rowloc h₀r,
    adjointDiagonal_row_norm_sq (tagOne M K) colloc h₁r]
  calc
    _ = ∑ i, ((∑ j, ‖tagZero M K i j‖ ^ 2) +
        (∑ j, ‖tagOne M K i j‖ ^ 2)) * ‖v i‖ ^ 2 := by
      simp only [add_mul, Finset.sum_add_distrib]
    _ ≤ ∑ i, ρ ^ 2 * ‖v i‖ ^ 2 :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right
        ((row_energy_le M K i).trans (hK i)) (sq_nonneg _)
    _ = ρ ^ 2 * ‖v‖ ^ 2 := by
      rw [← Finset.mul_sum, PiLp.norm_sq_eq_of_L2]

section Native
variable {X Z : Type*}

/-- The verified original sparse-data interface supplies all locator promises. -/
theorem native_frame_certificate (D : NativeSparseBlockEncoding.Data X n Z s)
    (x : X) (K : Matrix n n ℂ)
    (hK : ∀ i j, D.matrix x i j = 0 → D.matrix x j i = 0 → K i j = 0) :
    (leftFrame (D.rowloc x) (D.colloc x))† ∘L leftFrame (D.rowloc x) (D.colloc x) =
        (2 * (s : ℂ)) • (1 : EuclideanSpace ℂ n →L[ℂ] _) ∧
    (rightFrame (D.rowloc x) (D.colloc x))† ∘L rightFrame (D.rowloc x) (D.colloc x) =
        (2 * (s : ℂ)) • (1 : EuclideanSpace ℂ n →L[ℂ] _) ∧
    (leftFrame (D.rowloc x) (D.colloc x))† ∘L diagonal (D.matrix x) K ∘L
        rightFrame (D.rowloc x) (D.colloc x) = SparseStateOverlap.matrixOperator K :=
  ⟨leftFrame_gram _ _ (D.row_injective x) (D.column_injective x),
    rightFrame_gram _ _ (D.row_injective x) (D.column_injective x),
    frame_overlap _ _ _ _ (D.row_covers x) (D.column_covers x) hK⟩

theorem native_boundary_energy_certificate (D : NativeSparseBlockEncoding.Data X n Z s)
    (x : X) (K : Matrix n n ℂ) (ρ : ℝ)
    (hr : ∀ i, ∑ j, ‖K i j‖ ^ 2 ≤ ρ ^ 2)
    (hc : ∀ j, ∑ i, ‖K i j‖ ^ 2 ≤ ρ ^ 2) (v : EuclideanSpace ℂ n) :
    ‖((diagonal (D.matrix x) K)†) (leftFrame (D.rowloc x) (D.colloc x) v)‖ ^ 2 ≤
        ρ ^ 2 * ‖v‖ ^ 2 ∧
    ‖diagonal (D.matrix x) K (rightFrame (D.rowloc x) (D.colloc x) v)‖ ^ 2 ≤
        ρ ^ 2 * ‖v‖ ^ 2 :=
  ⟨left_boundary_energy_le _ _ _ _ (D.row_covers x) (D.column_covers x) ρ hr v,
    right_boundary_energy_le _ _ _ _ (D.row_covers x) (D.column_covers x) ρ hc v⟩

end Native
end
end SparseHamiltonian.ODETaggedSupport
