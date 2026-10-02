import SparseHamiltonian.FreshFlagAttenuation

/-!
# Good-flag projection and the sparse preparation success spectrum

The projector is fixed and checks only the physical good flag. Row sums below
are analytical quantities, not additional oracle inputs or free circuit gates.
-/

namespace SparseHamiltonian.SparseSuccessProjection

noncomputable section
open ContinuousLinearMap SparseSlotStates SparseEntryAmplitudes
open scoped BigOperators InnerProduct ComplexConjugate

variable {n : Type*} [Fintype n] {s : ℕ}

/-- Fixed projection onto the common good flag. -/
def good : SparseSlotStates.Space n →L[ℂ] SparseSlotStates.Space n :=
  WeightedClock.diagonal (fun b => if b.2 = 0 then 1 else 0)

@[simp] theorem good_apply (v : SparseSlotStates.Space n) (b : SparseSlotStates.Basis n) :
    good v b = if b.2 = 0 then v b else 0 := by
  simp only [good, WeightedClock.diagonal_apply]
  split_ifs <;> rfl

@[simp] theorem good_adjoint : (good (n := n))† = good := by
  simp only [good, WeightedClock.diagonal_adjoint]
  congr 1
  funext b
  split_ifs <;> simp

@[simp] theorem good_mul : (good (n := n)) * good = good := by
  ext v b
  change good (good v) b = good v b
  by_cases hb : b.2 = 0 <;> simp [hb]

/-- Both orthogonal-projection identities hold on the entire workspace. -/
theorem good_orthogonal : PhaseSubspaceGates.IsOrthogonalProjection (good (n := n)) :=
  ⟨good_adjoint, good_mul⟩

variable [DecidableEq n]

/-- Selected row success probability, including every zero padding slot. -/
def rowSuccess (H : Matrix n n ℂ) (a : ℝ) (loc : n → Fin s → n) (i : n) : ℝ :=
  ∑ j, if selected loc i j then ‖H i j‖ / ((s : ℝ) * a) else 0

/-- Selected column success probability. -/
def columnSuccess (H : Matrix n n ℂ) (a : ℝ) (loc : n → Fin s → n) (j : n) : ℝ :=
  ∑ i, if selected loc j i then ‖H i j‖ / ((s : ℝ) * a) else 0

/-- The analytical row success spectrum is a diagonal operator. -/
def diagonal (p : n → ℝ) : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n :=
  WeightedClock.diagonal (fun i => (p i : ℂ) • (1 : ℂ →L[ℂ] ℂ))

omit [Fintype n] [DecidableEq n] in
@[simp] theorem diagonal_apply (p : n → ℝ) (v : EuclideanSpace ℂ n) (i : n) :
    diagonal p v i = (p i : ℂ) * v i := rfl

theorem row_good_entry_inner (a : ℝ) (ha : 0 < a) (z u v : ℂ) :
    conj (weight s * rowAmplitude a z * u) * (weight s * rowAmplitude a z * v) =
      ((‖z‖ / ((s : ℝ) * a) : ℝ) : ℂ) * conj u * v := by
  calc
    _ = (conj (weight s) * weight s) *
        (conj (rowAmplitude a z) * rowAmplitude a z) * conj u * v := by
      simp only [map_mul]
      ring
    _ = _ := by
      rw [conj_weight_mul, mul_comm (conj (rowAmplitude a z)),
        Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_rowAmplitude_sq a ha]
      push_cast
      ring

theorem column_good_entry_inner (a : ℝ) (ha : 0 < a) (z u v : ℂ) :
    conj (weight s * columnAmplitude a z * u) *
        (weight s * columnAmplitude a z * v) =
      ((‖z‖ / ((s : ℝ) * a) : ℝ) : ℂ) * conj u * v := by
  calc
    _ = (conj (weight s) * weight s) *
        (conj (columnAmplitude a z) * columnAmplitude a z) * conj u * v := by
      simp only [map_mul]
      ring
    _ = _ := by
      rw [conj_weight_mul, mul_comm (conj (columnAmplitude a z)),
        Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_columnAmplitude_sq a ha]
      push_cast
      ring

/-- The row labels remain orthogonal even after projecting onto success. -/
theorem inner_row_good (H : Matrix n n ℂ) (a : ℝ) (ha : 0 < a)
    (loc : n → Fin s → n) (u v : EuclideanSpace ℂ n) :
    inner ℂ (row H a loc u) (good (row H a loc v)) =
      ∑ i, (rowSuccess H a loc i : ℂ) * conj (u i) * v i := by
  simp only [PiLp.inner_apply, Fintype.sum_prod_type, good_apply, row_apply,
    RCLike.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [rowSuccess, Complex.ofReal_sum, Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : selected loc i j
  · simpa [hij, Fin.sum_univ_succ, rowEntry, mul_comm] using
      row_good_entry_inner (s := s) a ha (H i j) (u i) (v i)
  · simp [hij]

/-- The analogous column calculation uses its original column label. -/
theorem inner_column_good (H : Matrix n n ℂ) (a : ℝ) (ha : 0 < a)
    (loc : n → Fin s → n) (u v : EuclideanSpace ℂ n) :
    inner ℂ (column H a loc u) (good (column H a loc v)) =
      ∑ j, (columnSuccess H a loc j : ℂ) * conj (u j) * v j := by
  simp only [PiLp.inner_apply, Fintype.sum_prod_type, good_apply, column_apply,
    RCLike.inner_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [columnSuccess, Complex.ofReal_sum, Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hij : selected loc j i
  · simpa [hij, Fin.sum_univ_succ, columnEntry, mul_comm] using
      column_good_entry_inner (s := s) a ha (H i j) (u j) (v j)
  · simp [hij]

/-- Exact diagonal compression, without any row-sum oracle assumption. -/
theorem row_compression_apply (H : Matrix n n ℂ) (a : ℝ) (ha : 0 < a)
    (loc : n → Fin s → n) (v : EuclideanSpace ℂ n) (i : n) :
    (((row H a loc)†) (good (row H a loc v))) i =
      (rowSuccess H a loc i : ℂ) * v i := by
  calc
    _ = inner ℂ (EuclideanSpace.single i (1 : ℂ))
        (((row H a loc)†) (good (row H a loc v))) := by
      simp [EuclideanSpace.inner_single_left]
    _ = inner ℂ (row H a loc (EuclideanSpace.single i (1 : ℂ)))
        (good (row H a loc v)) := adjoint_inner_right _ _ _
    _ = _ := by
      rw [inner_row_good H a ha loc]
      simp [PiLp.single_apply, apply_ite]

theorem column_compression_apply (H : Matrix n n ℂ) (a : ℝ) (ha : 0 < a)
    (loc : n → Fin s → n) (v : EuclideanSpace ℂ n) (j : n) :
    (((column H a loc)†) (good (column H a loc v))) j =
      (columnSuccess H a loc j : ℂ) * v j := by
  calc
    _ = inner ℂ (EuclideanSpace.single j (1 : ℂ))
        (((column H a loc)†) (good (column H a loc v))) := by
      simp [EuclideanSpace.inner_single_left]
    _ = inner ℂ (column H a loc (EuclideanSpace.single j (1 : ℂ)))
        (good (column H a loc v)) := adjoint_inner_right _ _ _
    _ = _ := by
      rw [inner_column_good H a ha loc]
      simp [PiLp.single_apply, apply_ite]

theorem row_compression (H : Matrix n n ℂ) (a : ℝ) (ha : 0 < a)
    (loc : n → Fin s → n) :
    (row H a loc)† ∘L good ∘L row H a loc = diagonal (rowSuccess H a loc) := by
  ext v i
  exact row_compression_apply H a ha loc v i

theorem column_compression (H : Matrix n n ℂ) (a : ℝ) (ha : 0 < a)
    (loc : n → Fin s → n) :
    (column H a loc)† ∘L good ∘L column H a loc = diagonal (columnSuccess H a loc) := by
  ext v j
  exact column_compression_apply H a ha loc v j

/-- The compression eigenvectors are the original row labels. -/
theorem row_compression_basis (H : Matrix n n ℂ) (a : ℝ) (ha : 0 < a)
    (loc : n → Fin s → n) (i : n) :
    ((row H a loc)†) (good (row H a loc (EuclideanSpace.single i 1))) =
      (rowSuccess H a loc i : ℂ) • EuclideanSpace.single i 1 := by
  apply PiLp.ext
  intro j
  rw [row_compression_apply H a ha loc]
  by_cases h : i = j
  · subst j
    simp
  · simp [h]

theorem column_compression_basis (H : Matrix n n ℂ) (a : ℝ) (ha : 0 < a)
    (loc : n → Fin s → n) (j : n) :
    ((column H a loc)†) (good (column H a loc (EuclideanSpace.single j 1))) =
      (columnSuccess H a loc j : ℂ) • EuclideanSpace.single j 1 := by
  apply PiLp.ext
  intro i
  rw [column_compression_apply H a ha loc]
  by_cases h : j = i
  · subst i
    simp
  · simp [h]

/-- Injective original locator slots give the exact success formula. -/
theorem rowSuccess_slots (H : Matrix n n ℂ) (a : ℝ) (loc : n → Fin s → n)
    (hinj : ∀ i, Function.Injective (loc i)) (i : n) :
    rowSuccess H a loc i = (∑ k, ‖H i (loc i k)‖) / ((s : ℝ) * a) := by
  rw [rowSuccess, sum_selected loc hinj, ← Finset.sum_div]

theorem columnSuccess_slots (H : Matrix n n ℂ) (a : ℝ) (loc : n → Fin s → n)
    (hinj : ∀ j, Function.Injective (loc j)) (j : n) :
    columnSuccess H a loc j = (∑ k, ‖H (loc j k) j‖) / ((s : ℝ) * a) := by
  rw [columnSuccess, sum_selected loc hinj, ← Finset.sum_div]

/-- If every nonzero entry is covered, padding has no effect on the analytical row sum. -/
theorem rowSuccess_all (H : Matrix n n ℂ) (a : ℝ) (loc : n → Fin s → n)
    (hcover : ∀ i j, H i j ≠ 0 → selected loc i j) (i : n) :
    rowSuccess H a loc i = (∑ j, ‖H i j‖) / ((s : ℝ) * a) := by
  rw [rowSuccess, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : selected loc i j
  · simp [h]
  · have hz : H i j = 0 := by by_contra hz; exact h (hcover i j hz)
    simp [h, hz]

theorem columnSuccess_all (H : Matrix n n ℂ) (a : ℝ) (loc : n → Fin s → n)
    (hcover : ∀ i j, H i j ≠ 0 → selected loc j i) (j : n) :
    columnSuccess H a loc j = (∑ i, ‖H i j‖) / ((s : ℝ) * a) := by
  rw [columnSuccess, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : selected loc j i
  · simp [h]
  · have hz : H i j = 0 := by by_contra hz; exact h (hcover i j hz)
    simp [h, hz]

theorem rowSuccess_nonneg (H : Matrix n n ℂ) (a : ℝ) (ha : 0 ≤ a)
    (loc : n → Fin s → n) (i : n) : 0 ≤ rowSuccess H a loc i := by
  apply Finset.sum_nonneg
  intro j _
  split_ifs
  · exact div_nonneg (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg s) ha)
  · exact le_rfl

theorem columnSuccess_nonneg (H : Matrix n n ℂ) (a : ℝ) (ha : 0 ≤ a)
    (loc : n → Fin s → n) (j : n) : 0 ≤ columnSuccess H a loc j := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact div_nonneg (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg s) ha)
  · exact le_rfl

/-- Entrywise normalization bounds each row success probability by one. -/
theorem rowSuccess_le_one (hs : 0 < s) (H : Matrix n n ℂ) (a : ℝ) (ha : 0 < a)
    (hH : ∀ i j, ‖H i j‖ ≤ a) (loc : n → Fin s → n)
    (hinj : ∀ i, Function.Injective (loc i)) (i : n) : rowSuccess H a loc i ≤ 1 := by
  rw [rowSuccess_slots H a loc hinj]
  apply (div_le_one (mul_pos (by exact_mod_cast hs) ha)).2
  calc
    ∑ k, ‖H i (loc i k)‖ ≤ ∑ _ : Fin s, a := Finset.sum_le_sum (fun _ _ => hH _ _)
    _ = _ := by simp

theorem columnSuccess_le_one (hs : 0 < s) (H : Matrix n n ℂ) (a : ℝ) (ha : 0 < a)
    (hH : ∀ i j, ‖H i j‖ ≤ a) (loc : n → Fin s → n)
    (hinj : ∀ j, Function.Injective (loc j)) (j : n) : columnSuccess H a loc j ≤ 1 := by
  rw [columnSuccess_slots H a loc hinj]
  apply (div_le_one (mul_pos (by exact_mod_cast hs) ha)).2
  calc
    ∑ k, ‖H (loc j k) j‖ ≤ ∑ _ : Fin s, a := Finset.sum_le_sum (fun _ _ => hH _ _)
    _ = _ := by simp

/-- This is the action of the full prepared-subspace projector on one good component. -/
theorem row_range_on_good (H : Matrix n n ℂ) (a : ℝ) (ha : 0 < a)
    (loc : n → Fin s → n) (i : n) :
    (row H a loc ∘L (row H a loc)†) (good (row H a loc (EuclideanSpace.single i 1))) =
      (rowSuccess H a loc i : ℂ) • row H a loc (EuclideanSpace.single i 1) := by
  simp only [comp_apply, row_compression_basis H a ha loc, map_smul]

theorem column_range_on_good (H : Matrix n n ℂ) (a : ℝ) (ha : 0 < a)
    (loc : n → Fin s → n) (j : n) :
    (column H a loc ∘L (column H a loc)†)
        (good (column H a loc (EuclideanSpace.single j 1))) =
      (columnSuccess H a loc j : ℂ) • column H a loc (EuclideanSpace.single j 1) := by
  simp only [comp_apply, column_compression_basis H a ha loc, map_smul]

omit [DecidableEq n] in
/-- Projected inner products may equivalently be computed before the first projection. -/
theorem inner_good (u v : SparseSlotStates.Space n) :
    inner ℂ (good u) (good v) = inner ℂ u (good v) := by
  rw [← adjoint_inner_right good u (good v), good_adjoint]
  have h : good (good v) = good v := congrArg (fun A : SparseSlotStates.Space n →L[ℂ]
      SparseSlotStates.Space n => A v) good_mul
  rw [h]

/-- The exact success probability is the squared norm of the physical good component. -/
theorem row_good_norm_sq (H : Matrix n n ℂ) (a : ℝ) (ha : 0 < a)
    (loc : n → Fin s → n) (i : n) :
    ‖good (row H a loc (EuclideanSpace.single i 1))‖ ^ 2 = rowSuccess H a loc i := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), inner_good, inner_row_good H a ha loc]
  simp [PiLp.single_apply, apply_ite]

theorem column_good_norm_sq (H : Matrix n n ℂ) (a : ℝ) (ha : 0 < a)
    (loc : n → Fin s → n) (j : n) :
    ‖good (column H a loc (EuclideanSpace.single j 1))‖ ^ 2 = columnSuccess H a loc j := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), inner_good, inner_column_good H a ha loc]
  simp [PiLp.single_apply, apply_ite]

/-- Distinct row labels have mutually orthogonal success components. -/
theorem row_good_orthogonal (H : Matrix n n ℂ) (a : ℝ) (ha : 0 < a)
    (loc : n → Fin s → n) (i j : n) (hij : i ≠ j) :
    inner ℂ (good (row H a loc (EuclideanSpace.single i 1)))
      (good (row H a loc (EuclideanSpace.single j 1))) = 0 := by
  rw [inner_good, inner_row_good H a ha loc]
  simp [PiLp.single_apply, apply_ite, Ne.symm hij]

theorem column_good_orthogonal (H : Matrix n n ℂ) (a : ℝ) (ha : 0 < a)
    (loc : n → Fin s → n) (i j : n) (hij : i ≠ j) :
    inner ℂ (good (column H a loc (EuclideanSpace.single i 1)))
      (good (column H a loc (EuclideanSpace.single j 1))) = 0 := by
  rw [inner_good, inner_column_good H a ha loc]
  simp [PiLp.single_apply, apply_ite, Ne.symm hij]

/-- A zero success probability has exactly zero good component. -/
theorem row_good_eq_zero (H : Matrix n n ℂ) (a : ℝ) (ha : 0 < a)
    (loc : n → Fin s → n) (i : n) (hp : rowSuccess H a loc i = 0) :
    good (row H a loc (EuclideanSpace.single i 1)) = 0 := by
  apply norm_eq_zero.mp
  have h := row_good_norm_sq H a ha loc i
  rw [hp] at h
  nlinarith [norm_nonneg (good (row H a loc (EuclideanSpace.single i 1)))]

theorem column_good_eq_zero (H : Matrix n n ℂ) (a : ℝ) (ha : 0 < a)
    (loc : n → Fin s → n) (j : n) (hp : columnSuccess H a loc j = 0) :
    good (column H a loc (EuclideanSpace.single j 1)) = 0 := by
  apply norm_eq_zero.mp
  have h := column_good_norm_sq H a ha loc j
  rw [hp] at h
  nlinarith [norm_nonneg (good (column H a loc (EuclideanSpace.single j 1)))]

/-- The remaining physical failure probability is exactly one minus success. -/
theorem row_bad_norm_sq (hs : 0 < s) (H : Matrix n n ℂ) (a : ℝ) (ha : 0 < a)
    (hH : ∀ i j, ‖H i j‖ ≤ a) (loc : n → Fin s → n)
    (hinj : ∀ i, Function.Injective (loc i)) (i : n) :
    ‖row H a loc (EuclideanSpace.single i 1) -
      good (row H a loc (EuclideanSpace.single i 1))‖ ^ 2 = 1 - rowSuccess H a loc i := by
  rw [norm_sub_sq (𝕜 := ℂ), row_norm hs H a ha hH loc hinj,
    row_good_norm_sq H a ha loc, inner_row_good H a ha loc]
  simp [PiLp.single_apply, apply_ite]
  ring

theorem column_bad_norm_sq (hs : 0 < s) (H : Matrix n n ℂ) (a : ℝ) (ha : 0 < a)
    (hH : ∀ i j, ‖H i j‖ ≤ a) (loc : n → Fin s → n)
    (hinj : ∀ j, Function.Injective (loc j)) (j : n) :
    ‖column H a loc (EuclideanSpace.single j 1) -
      good (column H a loc (EuclideanSpace.single j 1))‖ ^ 2 = 1 - columnSuccess H a loc j := by
  rw [norm_sub_sq (𝕜 := ℂ), column_norm hs H a ha hH loc hinj,
    column_good_norm_sq H a ha loc, inner_column_good H a ha loc]
  simp [PiLp.single_apply, apply_ite]
  ring

/-- Certain success means the full row preparation already lies in the good subspace. -/
theorem row_good_eq_self (hs : 0 < s) (H : Matrix n n ℂ) (a : ℝ) (ha : 0 < a)
    (hH : ∀ i j, ‖H i j‖ ≤ a) (loc : n → Fin s → n)
    (hinj : ∀ i, Function.Injective (loc i)) (i : n) (hp : rowSuccess H a loc i = 1) :
    good (row H a loc (EuclideanSpace.single i 1)) = row H a loc (EuclideanSpace.single i 1) := by
  symm
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  have h := row_bad_norm_sq hs H a ha hH loc hinj i
  rw [hp, sub_self] at h
  nlinarith

theorem column_good_eq_self (hs : 0 < s) (H : Matrix n n ℂ) (a : ℝ) (ha : 0 < a)
    (hH : ∀ i j, ‖H i j‖ ≤ a) (loc : n → Fin s → n)
    (hinj : ∀ j, Function.Injective (loc j)) (j : n) (hp : columnSuccess H a loc j = 1) :
    good (column H a loc (EuclideanSpace.single j 1)) =
      column H a loc (EuclideanSpace.single j 1) := by
  symm
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  have h := column_bad_norm_sq hs H a ha hH loc hinj j
  rw [hp, sub_self] at h
  nlinarith

end
end SparseHamiltonian.SparseSuccessProjection
