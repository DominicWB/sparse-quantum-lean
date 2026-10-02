import SparseHamiltonian.ExactEdgeCayley

/-!
# Concrete sparse edge incidence and boundary energies

These operators use the actual row and column locator lists.  The lists are
not assumed to agree on zero padding.  No preparation or moment certificate
is assumed.  This fragment does not yet count the implementation queries.
-/

namespace SparseHamiltonian.SparseEdgeMoments

noncomputable section
open ContinuousLinearMap SparseSlotStates
open scoped BigOperators InnerProduct ComplexConjugate

variable {n : Type*} [Fintype n] [DecidableEq n] {s : ℕ}

abbrev EdgeSpace (n : Type*) [Fintype n] := EuclideanSpace ℂ (n × n)

/-- A weighted incidence map, with the public row retained in the edge address. -/
def weightedRow (a : Matrix n n ℂ) : EuclideanSpace ℂ n →L[ℂ] EdgeSpace n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => WithLp.toLp 2 (fun e => a e.1 e.2 * v e.1)
      map_add' := by intro v w; ext e; simp [mul_add]
      map_smul' := by intro z v; ext e; simp [mul_left_comm] }

/-- The second orientation retains the public column. -/
def weightedColumn (a : Matrix n n ℂ) : EuclideanSpace ℂ n →L[ℂ] EdgeSpace n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => WithLp.toLp 2 (fun e => a e.1 e.2 * v e.2)
      map_add' := by intro v w; ext e; simp [mul_add]
      map_smul' := by intro z v; ext e; simp [mul_left_comm] }

omit [DecidableEq n] in
@[simp] theorem weightedRow_apply (a : Matrix n n ℂ) (v : EuclideanSpace ℂ n)
    (i j : n) : weightedRow a v (i,j) = a i j * v i := rfl

omit [DecidableEq n] in
@[simp] theorem weightedColumn_apply (a : Matrix n n ℂ) (v : EuclideanSpace ℂ n)
    (i j : n) : weightedColumn a v (i,j) = a i j * v j := rfl

theorem weightedRow_adjoint_apply (a : Matrix n n ℂ) (v : EdgeSpace n) (i : n) :
    ((weightedRow a)†) v i = ∑ j, star (a i j) * v (i,j) := by
  calc
    _ = inner ℂ (EuclideanSpace.single i (1 : ℂ)) (((weightedRow a)†) v) := by
      simp [EuclideanSpace.inner_single_left]
    _ = inner ℂ (weightedRow a (EuclideanSpace.single i (1 : ℂ))) v :=
      adjoint_inner_right _ _ _
    _ = _ := by
      simp [PiLp.inner_apply, Fintype.sum_prod_type, RCLike.inner_apply,
        PiLp.single_apply, apply_ite, mul_comm]

theorem weightedColumn_adjoint_apply (a : Matrix n n ℂ) (v : EdgeSpace n) (j : n) :
    ((weightedColumn a)†) v j = ∑ i, star (a i j) * v (i,j) := by
  calc
    _ = inner ℂ (EuclideanSpace.single j (1 : ℂ)) (((weightedColumn a)†) v) := by
      simp [EuclideanSpace.inner_single_left]
    _ = inner ℂ (weightedColumn a (EuclideanSpace.single j (1 : ℂ))) v :=
      adjoint_inner_right _ _ _
    _ = _ := by
      simp [PiLp.inner_apply, Fintype.sum_prod_type, RCLike.inner_apply,
        PiLp.single_apply, apply_ite, mul_comm]

omit [DecidableEq n] in
/-- The row energy appears diagonally, with no factor depending on dimension. -/
theorem weightedRow_norm_sq (a : Matrix n n ℂ) (v : EuclideanSpace ℂ n) :
    ‖weightedRow a v‖ ^ 2 = ∑ i, (∑ j, ‖a i j‖ ^ 2) * ‖v i‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [Fintype.sum_prod_type, weightedRow_apply, norm_mul, mul_pow,
    Finset.sum_mul]

omit [DecidableEq n] in
/-- The column version likewise has exactly the column energies. -/
theorem weightedColumn_norm_sq (a : Matrix n n ℂ) (v : EuclideanSpace ℂ n) :
    ‖weightedColumn a v‖ ^ 2 = ∑ j, (∑ i, ‖a i j‖ ^ 2) * ‖v j‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [Fintype.sum_prod_type, weightedColumn_apply, norm_mul, mul_pow]
  rw [Finset.sum_comm]
  simp only [Finset.sum_mul]

omit [DecidableEq n] in
theorem weightedRow_norm_le (a : Matrix n n ℂ) (η : ℝ) (hη : 0 ≤ η)
    (ha : ∀ i, ∑ j, ‖a i j‖ ^ 2 ≤ η ^ 2) (v : EuclideanSpace ℂ n) :
    ‖weightedRow a v‖ ≤ η * ‖v‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hη (norm_nonneg _))).mp
  rw [weightedRow_norm_sq, mul_pow, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (ha i) (sq_nonneg _)

omit [DecidableEq n] in
theorem weightedColumn_norm_le (a : Matrix n n ℂ) (η : ℝ) (hη : 0 ≤ η)
    (ha : ∀ j, ∑ i, ‖a i j‖ ^ 2 ≤ η ^ 2) (v : EuclideanSpace ℂ n) :
    ‖weightedColumn a v‖ ≤ η * ‖v‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hη (norm_nonneg _))).mp
  rw [weightedColumn_norm_sq, mul_pow, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (ha j) (sq_nonneg _)

/-- Every original locator slot, including zero padding, occurs in `L`. -/
def rowIncidence (loc : n → Fin s → n) : EuclideanSpace ℂ n →L[ℂ] EdgeSpace n :=
  weightedRow (fun i j => if selected loc i j then 1 else 0)

/-- Column padding can be chosen independently of row padding. -/
def columnIncidence (loc : n → Fin s → n) : EuclideanSpace ℂ n →L[ℂ] EdgeSpace n :=
  weightedColumn (fun i j => if selected loc j i then 1 else 0)

@[simp] theorem rowIncidence_apply (loc : n → Fin s → n)
    (v : EuclideanSpace ℂ n) (i j : n) :
    rowIncidence loc v (i,j) = if selected loc i j then v i else 0 := by
  by_cases h : selected loc i j <;> simp [rowIncidence, h]

@[simp] theorem columnIncidence_apply (loc : n → Fin s → n)
    (v : EuclideanSpace ℂ n) (i j : n) :
    columnIncidence loc v (i,j) = if selected loc j i then v j else 0 := by
  by_cases h : selected loc j i <;> simp [columnIncidence, h]

theorem rowIncidence_adjoint_apply (loc : n → Fin s → n) (v : EdgeSpace n) (i : n) :
    ((rowIncidence loc)†) v i = ∑ j, if selected loc i j then v (i,j) else 0 := by
  rw [rowIncidence, weightedRow_adjoint_apply]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : selected loc i j <;> simp [h]

theorem columnIncidence_adjoint_apply (loc : n → Fin s → n) (v : EdgeSpace n) (j : n) :
    ((columnIncidence loc)†) v j = ∑ i, if selected loc j i then v (i,j) else 0 := by
  rw [columnIncidence, weightedColumn_adjoint_apply]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : selected loc j i <;> simp [h]

/-- Injectivity is exactly what rules out repeated slot contributions. -/
theorem rowIncidence_gram (loc : n → Fin s → n)
    (hinj : ∀ i, Function.Injective (loc i)) :
    (rowIncidence loc)† ∘L rowIncidence loc = (s : ℂ) • (1 : EuclideanSpace ℂ n →L[ℂ] _) := by
  ext v i
  change (((rowIncidence loc)†) (rowIncidence loc v)) i = (s : ℂ) * v i
  rw [rowIncidence_adjoint_apply]
  have he (j : n) :
      (if selected loc i j then rowIncidence loc v (i,j) else 0) =
        if selected loc i j then v i else 0 := by
    by_cases h : selected loc i j <;> simp [h]
  simp_rw [he, sum_selected loc hinj]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem columnIncidence_gram (loc : n → Fin s → n)
    (hinj : ∀ j, Function.Injective (loc j)) :
    (columnIncidence loc)† ∘L columnIncidence loc = (s : ℂ) • (1 : EuclideanSpace ℂ n →L[ℂ] _) := by
  ext v j
  change (((columnIncidence loc)†) (columnIncidence loc v)) j = (s : ℂ) * v j
  rw [columnIncidence_adjoint_apply]
  have he (i : n) :
      (if selected loc j i then columnIncidence loc v (i,j) else 0) =
        if selected loc j i then v j else 0 := by
    by_cases h : selected loc j i <;> simp [h]
  simp_rw [he, sum_selected loc hinj]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- Entrywise multiplication on the physical edge space. -/
def edgeDiagonal (H : Matrix n n ℂ) : EdgeSpace n →L[ℂ] EdgeSpace n :=
  RelativeAmplitudeError.complexDiagonal (fun e => H e.1 e.2)

omit [DecidableEq n] in
@[simp] theorem edgeDiagonal_apply (H : Matrix n n ℂ) (v : EdgeSpace n) (i j : n) :
    edgeDiagonal H v (i,j) = H i j * v (i,j) := rfl

omit [DecidableEq n] in
theorem edgeDiagonal_adjoint (H : Matrix n n ℂ) :
    (edgeDiagonal H)† = edgeDiagonal (fun i j => star (H i j)) := by
  exact RelativeAmplitudeError.complexDiagonal_adjoint _

omit [DecidableEq n] in
theorem edgeDiagonal_norm_le (H : Matrix n n ℂ) (a : ℝ) (ha : 0 ≤ a)
    (hH : ∀ i j, ‖H i j‖ ≤ a) : ‖edgeDiagonal H‖ ≤ a :=
  RelativeAmplitudeError.norm_complexDiagonal_le _ a ha (fun e => hH e.1 e.2)

/-- The diagonal kills every unlisted entry because all nonzero entries are covered. -/
theorem diagonal_column (H : Matrix n n ℂ) (loc : n → Fin s → n)
    (hcovers : ∀ i j, H i j ≠ 0 → selected loc j i) :
    edgeDiagonal H ∘L columnIncidence loc = weightedColumn H := by
  ext v e
  rcases e with ⟨i,j⟩
  change H i j * (columnIncidence loc v (i,j)) = H i j * v j
  rw [columnIncidence_apply]
  by_cases h : selected loc j i
  · simp [h]
  · have hz : H i j = 0 := by by_contra hn; exact h (hcovers i j hn)
    simp [h, hz]

/-- The corresponding adjoint-diagonal action uses row coverage only. -/
theorem adjointDiagonal_row (H : Matrix n n ℂ) (loc : n → Fin s → n)
    (hcovers : ∀ i j, H i j ≠ 0 → selected loc i j) :
    (edgeDiagonal H)† ∘L rowIncidence loc = weightedRow (fun i j => star (H i j)) := by
  rw [edgeDiagonal_adjoint]
  ext v e
  rcases e with ⟨i,j⟩
  change star (H i j) * (rowIncidence loc v (i,j)) = star (H i j) * v i
  rw [rowIncidence_apply]
  by_cases h : selected loc i j
  · simp [h]
  · have hz : H i j = 0 := by by_contra hn; exact h (hcovers i j hn)
    simp [h, hz]

/-- The exact matrix overlap needs no equality between row and column padding. -/
theorem incidence_overlap (H : Matrix n n ℂ) (rowloc colloc : n → Fin s → n)
    (hrow : ∀ i j, H i j ≠ 0 → selected rowloc i j)
    (hcol : ∀ i j, H i j ≠ 0 → selected colloc j i) :
    (rowIncidence rowloc)† ∘L edgeDiagonal H ∘L columnIncidence colloc =
      SparseStateOverlap.matrixOperator H := by
  rw [diagonal_column H colloc hcol]
  ext v i
  change (((rowIncidence rowloc)†) (weightedColumn H v)) i = ∑ j, H i j * v j
  rw [rowIncidence_adjoint_apply]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : selected rowloc i j
  · simp [h]
  · have hz : H i j = 0 := by by_contra hn; exact h (hrow i j hn)
    simp [h, hz]

/-- The right-hand boundary response has exactly the column energies. -/
theorem diagonal_column_norm_sq (H : Matrix n n ℂ) (loc : n → Fin s → n)
    (hcovers : ∀ i j, H i j ≠ 0 → selected loc j i) (v : EuclideanSpace ℂ n) :
    ‖edgeDiagonal H (columnIncidence loc v)‖ ^ 2 =
      ∑ j, (∑ i, ‖H i j‖ ^ 2) * ‖v j‖ ^ 2 := by
  have h := congrArg (fun T : EuclideanSpace ℂ n →L[ℂ] EdgeSpace n => T v)
    (diagonal_column H loc hcovers)
  change edgeDiagonal H (columnIncidence loc v) = weightedColumn H v at h
  rw [h, weightedColumn_norm_sq]

/-- The left-hand response has the row energies, including all complex phases. -/
theorem adjointDiagonal_row_norm_sq (H : Matrix n n ℂ) (loc : n → Fin s → n)
    (hcovers : ∀ i j, H i j ≠ 0 → selected loc i j) (v : EuclideanSpace ℂ n) :
    ‖((edgeDiagonal H)†) (rowIncidence loc v)‖ ^ 2 =
      ∑ i, (∑ j, ‖H i j‖ ^ 2) * ‖v i‖ ^ 2 := by
  have h := congrArg (fun T : EuclideanSpace ℂ n →L[ℂ] EdgeSpace n => T v)
    (adjointDiagonal_row H loc hcovers)
  change ((edgeDiagonal H)†) (rowIncidence loc v) = weightedRow (fun i j => star (H i j)) v at h
  rw [h, weightedRow_norm_sq]
  simp only [norm_star]

section Native
variable {X Z : Type*}

/-- The actual sparse data supplies all incidence identities directly. -/
theorem native_incidence_certificate (D : NativeSparseBlockEncoding.Data X n Z s) (x : X) :
    (rowIncidence (D.rowloc x))† ∘L rowIncidence (D.rowloc x) =
        (s : ℂ) • (1 : EuclideanSpace ℂ n →L[ℂ] _) ∧
    (columnIncidence (D.colloc x))† ∘L columnIncidence (D.colloc x) =
        (s : ℂ) • (1 : EuclideanSpace ℂ n →L[ℂ] _) ∧
    (rowIncidence (D.rowloc x))† ∘L edgeDiagonal (D.matrix x) ∘L
        columnIncidence (D.colloc x) = SparseStateOverlap.matrixOperator (D.matrix x) :=
  ⟨rowIncidence_gram _ (D.row_injective x),
    columnIncidence_gram _ (D.column_injective x),
    incidence_overlap _ _ _ (D.row_covers x) (D.column_covers x)⟩

/-- Row/column Euclidean bounds control both concrete responses, without a spectral promise. -/
theorem native_boundary_energy_le (D : NativeSparseBlockEncoding.Data X n Z s)
    (x : X) (η : ℝ)
    (hrow : ∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2)
    (hcol : ∀ j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2)
    (v : EuclideanSpace ℂ n) :
    (‖((edgeDiagonal (D.matrix x))†) (rowIncidence (D.rowloc x) v)‖ ^ 2 +
      ‖edgeDiagonal (D.matrix x) (columnIncidence (D.colloc x) v)‖ ^ 2) / 2 ≤
        η ^ 2 * ‖v‖ ^ 2 := by
  rw [adjointDiagonal_row_norm_sq _ _ (D.row_covers x),
    diagonal_column_norm_sq _ _ (D.column_covers x), PiLp.norm_sq_eq_of_L2]
  have hr : (∑ i, (∑ j, ‖D.matrix x i j‖ ^ 2) * ‖v i‖ ^ 2) ≤
      η ^ 2 * ∑ i, ‖v i‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hrow i) (sq_nonneg _)
  have hc : (∑ j, (∑ i, ‖D.matrix x i j‖ ^ 2) * ‖v j‖ ^ 2) ≤
      η ^ 2 * ∑ j, ‖v j‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hcol j) (sq_nonneg _)
  linarith

end Native
end
end SparseHamiltonian.SparseEdgeMoments
