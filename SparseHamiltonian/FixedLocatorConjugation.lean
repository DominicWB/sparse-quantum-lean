import SparseHamiltonian.NativeCayleySimulation

/-!
# Full locator conjugation and an input-independent sparse boundary

The full unitary extensions in the sparse-access promise act separately on
both orientations.  Only their valid-slot action is used to identify the
boundary.  Row and column padding need not coincide.
-/

namespace SparseHamiltonian.FixedLocatorConjugation

noncomputable section
open ContinuousLinearMap OracleCircuit SparseEdgeMoments
open scoped BigOperators InnerProduct

variable {n : Type*} [Fintype n] [DecidableEq n] {s : ℕ}

/-- Restrict an oriented edge vector to its row sector. -/
def leftPart (v : OrientedSpace n) : EdgeSpace n :=
  WithLp.toLp 2 (fun e => v (.inl e))

/-- Restrict an oriented edge vector to its column sector. -/
def rightPart (v : OrientedSpace n) : EdgeSpace n :=
  WithLp.toLp 2 (fun e => v (.inr e))

/-- The direct sum of two full address-space operators. -/
def block (A B : EdgeSpace n →L[ℂ] EdgeSpace n) :
    OrientedSpace n →L[ℂ] OrientedSpace n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => WithLp.toLp 2 (Sum.elim
        (fun e => A (leftPart v) e) (fun e => B (rightPart v) e))
      map_add' := by
        intro v w
        have hl : leftPart (v + w) = leftPart v + leftPart w := rfl
        have hr : rightPart (v + w) = rightPart v + rightPart w := rfl
        ext e
        cases e <;> simp [hl, hr]
      map_smul' := by
        intro z v
        have hl : leftPart (z • v) = z • leftPart v := rfl
        have hr : rightPart (z • v) = z • rightPart v := rfl
        ext e
        cases e <;> simp [hl, hr] }

omit [DecidableEq n] in
@[simp] theorem block_inl (A B : EdgeSpace n →L[ℂ] EdgeSpace n)
    (v : OrientedSpace n) (e : n × n) :
    block A B v (.inl e) = A (leftPart v) e := rfl

omit [DecidableEq n] in
@[simp] theorem block_inr (A B : EdgeSpace n →L[ℂ] EdgeSpace n)
    (v : OrientedSpace n) (e : n × n) :
    block A B v (.inr e) = B (rightPart v) e := rfl

omit [DecidableEq n] in
@[simp] theorem leftPart_block (A B : EdgeSpace n →L[ℂ] EdgeSpace n)
    (v : OrientedSpace n) : leftPart (block A B v) = A (leftPart v) := by
  ext e
  rfl

omit [DecidableEq n] in
@[simp] theorem rightPart_block (A B : EdgeSpace n →L[ℂ] EdgeSpace n)
    (v : OrientedSpace n) : rightPart (block A B v) = B (rightPart v) := by
  ext e
  rfl

omit [DecidableEq n] in
@[simp] theorem block_one : block (1 : EdgeSpace n →L[ℂ] EdgeSpace n) 1 = 1 := by
  ext v e
  cases e <;> rfl

omit [DecidableEq n] in
theorem block_comp (A B C D : EdgeSpace n →L[ℂ] EdgeSpace n) :
    block A B ∘L block C D = block (A ∘L C) (B ∘L D) := by
  ext v e
  cases e <;> simp only [comp_apply, block_inl, block_inr,
    leftPart_block, rightPart_block]

omit [DecidableEq n] in
theorem inner_block_left (A B : EdgeSpace n →L[ℂ] EdgeSpace n)
    (v w : OrientedSpace n) :
    inner ℂ (block A B v) w =
      inner ℂ (A (leftPart v)) (leftPart w) +
        inner ℂ (B (rightPart v)) (rightPart w) := by
  simp only [PiLp.inner_apply, Fintype.sum_sum_type, block_inl, block_inr,
    leftPart, rightPart]

omit [DecidableEq n] in
theorem inner_block_right (A B : EdgeSpace n →L[ℂ] EdgeSpace n)
    (v w : OrientedSpace n) :
    inner ℂ v (block A B w) =
      inner ℂ (leftPart v) (A (leftPart w)) +
        inner ℂ (rightPart v) (B (rightPart w)) := by
  simp only [PiLp.inner_apply, Fintype.sum_sum_type, block_inl, block_inr,
    leftPart, rightPart]

omit [DecidableEq n] in
theorem block_adjoint (A B : EdgeSpace n →L[ℂ] EdgeSpace n) :
    (block A B)† = block (A†) (B†) := by
  apply ContinuousLinearMap.ext
  intro v
  apply ext_inner_right ℂ
  intro w
  simp only [adjoint_inner_left, inner_block_left, inner_block_right]

omit [DecidableEq n] in
theorem block_unitary (A B : EdgeSpace n →L[ℂ] EdgeSpace n)
    (hA : IsUnitary A) (hB : IsUnitary B) : IsUnitary (block A B) := by
  have hAl : A† ∘L A = 1 := hA.1
  have hAr : A ∘L A† = 1 := hA.2
  have hBl : B† ∘L B = 1 := hB.1
  have hBr : B ∘L B† = 1 := hB.2
  constructor
  · change (block A B)† ∘L block A B = 1
    rw [block_adjoint, block_comp, hAl, hBl, block_one]
  · change block A B ∘L (block A B)† = 1
    rw [block_adjoint, block_comp, hAr, hBr, block_one]

omit [DecidableEq n] in
@[simp] theorem leftPart_stack (A B : EuclideanSpace ℂ n →L[ℂ] EdgeSpace n)
    (v : EuclideanSpace ℂ n) : leftPart (stack A B v) = A v := by
  ext e
  rfl

omit [DecidableEq n] in
@[simp] theorem rightPart_stack (A B : EuclideanSpace ℂ n →L[ℂ] EdgeSpace n)
    (v : EuclideanSpace ℂ n) : rightPart (stack A B v) = B v := by
  ext e
  rfl

omit [DecidableEq n] in
theorem block_stack (A B : EdgeSpace n →L[ℂ] EdgeSpace n)
    (C D : EuclideanSpace ℂ n →L[ℂ] EdgeSpace n) :
    block A B ∘L stack C D = stack (A ∘L C) (B ∘L D) := by
  ext v e
  cases e <;> simp only [comp_apply, block_inl, block_inr,
    stack_inl, stack_inr, leftPart_stack, rightPart_stack]

/-- An unnormalized row incidence vector is the sum of its original slots. -/
theorem rowIncidence_eq_sum (loc : n → Fin s → n)
    (hinj : ∀ i, Function.Injective (loc i)) (v : EuclideanSpace ℂ n) :
    rowIncidence loc v =
      ∑ i, ∑ k : Fin s, EuclideanSpace.single (i, loc i k) (v i) := by
  apply PiLp.ext
  intro e
  rcases e with ⟨i, j⟩
  rw [rowIncidence_apply]
  simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.single_apply]
  have hsum : (∑ a : n, ∑ k : Fin s,
      if (i, j) = (a, loc a k) then v a else 0) =
      ∑ k : Fin s, if loc i k = j then v i else 0 := by
    rw [Finset.sum_eq_single i]
    · apply Finset.sum_congr rfl
      intro k _
      simp [eq_comm]
    · intro a _ ha
      apply Finset.sum_eq_zero
      intro k _
      simp [show i ≠ a from Ne.symm ha]
    · simp
  rw [hsum]
  exact (UniformSlotPreparation.sum_slot_ite ⟨loc i, hinj i⟩ j (v i)).symm

/-- The corresponding column sum uses the same physical `(row,column)` order. -/
theorem columnIncidence_eq_sum (loc : n → Fin s → n)
    (hinj : ∀ j, Function.Injective (loc j)) (v : EuclideanSpace ℂ n) :
    columnIncidence loc v =
      ∑ j, ∑ k : Fin s, EuclideanSpace.single (loc j k, j) (v j) := by
  apply PiLp.ext
  intro e
  rcases e with ⟨i, j⟩
  rw [columnIncidence_apply]
  simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.single_apply]
  have hsum : (∑ a : n, ∑ k : Fin s,
      if (i, j) = (loc a k, a) then v a else 0) =
      ∑ k : Fin s, if loc j k = i then v j else 0 := by
    rw [Finset.sum_eq_single j]
    · apply Finset.sum_congr rfl
      intro k _
      simp [eq_comm]
    · intro a _ ha
      apply Finset.sum_eq_zero
      intro k _
      simp [show j ≠ a from Ne.symm ha]
    · simp
  rw [hsum]
  exact (UniformSlotPreparation.sum_slot_ite ⟨loc j, hinj j⟩ i (v j)).symm

/-- Both sectors start in the same fixed, public uniform slot preparation. -/
def fixedBoundary (slot : Fin s ↪ n) :
    EuclideanSpace ℂ n →L[ℂ] OrientedSpace n :=
  boundaryWeight s • stack (rowIncidence (fun _ => slot)) (rowIncidence (fun _ => slot))

/-- The common boundary is independent of the unknown sparse input instance. -/
theorem fixedBoundary_isometry (slot : Fin s ↪ n) (hs : 0 < s) :
    (fixedBoundary slot)† ∘L fixedBoundary slot = 1 := by
  have hslot : ∀ i : n, Function.Injective (fun k : Fin s => slot k) :=
    fun _ => slot.injective
  simp only [fixedBoundary, map_smulₛₗ, conj_boundaryWeight, smul_comp, comp_smul,
    smul_smul, stack_adjoint_stack, rowIncidence_gram (fun _ => slot) hslot]
  rw [← add_smul, smul_smul]
  have hc : (boundaryWeight s * boundaryWeight s) * ((s : ℂ) + s) = 1 := by
    convert boundaryWeight_sq hs using 1; ring
  rw [hc, one_smul]

variable {X Z : Type*}

/-- The full row and column locator extensions, on orthogonal orientations. -/
def locator (D : NativeSparseBlockEncoding.Data X n Z s) (x : X) :
    OrientedSpace n →L[ℂ] OrientedSpace n :=
  block (D.rowOracle x) (D.columnOracle x)

theorem locator_unitary (D : NativeSparseBlockEncoding.Data X n Z s) (x : X) :
    IsUnitary (locator D x) :=
  block_unitary _ _ (D.row_unitary x) (D.column_unitary x)

/-- No promise about the action of a locator on invalid inputs is added. -/
theorem rowOracle_slots (D : NativeSparseBlockEncoding.Data X n Z s) (x : X) :
    D.rowOracle x ∘L rowIncidence (fun _ => D.slot) = rowIncidence (D.rowloc x) := by
  apply ContinuousLinearMap.ext
  intro v
  change D.rowOracle x (rowIncidence (fun _ => D.slot) v) = _
  rw [rowIncidence_eq_sum (fun _ => D.slot) (fun _ => D.slot.injective),
    rowIncidence_eq_sum (D.rowloc x) (D.row_injective x), map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _
  exact SparseSlotPreparation.basis_scaled (D.rowOracle x) _ _ (D.row_valid x i k) _

/-- The column locator also starts with `(public index,slot)` on its input. -/
theorem columnOracle_slots (D : NativeSparseBlockEncoding.Data X n Z s) (x : X) :
    D.columnOracle x ∘L rowIncidence (fun _ => D.slot) = columnIncidence (D.colloc x) := by
  apply ContinuousLinearMap.ext
  intro v
  change D.columnOracle x (rowIncidence (fun _ => D.slot) v) = _
  rw [rowIncidence_eq_sum (fun _ => D.slot) (fun _ => D.slot.injective),
    columnIncidence_eq_sum (D.colloc x) (D.column_injective x), map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _
  exact SparseSlotPreparation.basis_scaled (D.columnOracle x) _ _ (D.column_valid x j k) _

/-- The input-dependent sparse boundary is exactly a full locator applied to one
fixed public preparation.  Unmatched zero-padding slots cause no difficulty. -/
theorem locator_boundary (D : NativeSparseBlockEncoding.Data X n Z s) (x : X) :
    locator D x ∘L fixedBoundary D.slot = boundary (D.rowloc x) (D.colloc x) := by
  rw [fixedBoundary, comp_smul]
  change boundaryWeight s • (block (D.rowOracle x) (D.columnOracle x) ∘L
    stack (rowIncidence (fun _ => D.slot)) (rowIncidence (fun _ => D.slot))) = _
  rw [block_stack, rowOracle_slots, columnOracle_slots]
  rfl

/-- The reverse locator recovers the public preparation exactly. -/
theorem locator_adjoint_boundary (D : NativeSparseBlockEncoding.Data X n Z s) (x : X) :
    (locator D x)† ∘L boundary (D.rowloc x) (D.colloc x) = fixedBoundary D.slot := by
  rw [← locator_boundary D x, ← comp_assoc]
  have h : (locator D x)† ∘L locator D x = 1 := (locator_unitary D x).1
  rw [h]
  simp only [one_def, id_comp]

end
end SparseHamiltonian.FixedLocatorConjugation
