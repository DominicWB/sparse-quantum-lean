import SparseHamiltonian.UniformSlotPreparation

/-!
# Sparse-slot states with local failure amplitudes

Each of the `s` injectively addressed slots receives amplitude `1 / sqrt s`.
Its good and bad amplitudes depend only on the entry in that slot, including
zero-valued padding slots. Row and column failures use distinct physical flags.
These are finite-dimensional identities; this file makes no query-cost claim.
-/

namespace SparseHamiltonian.SparseSlotStates

noncomputable section
open ContinuousLinearMap SparseEntryAmplitudes ComplexAmplitudeRotation
open scoped BigOperators InnerProduct ComplexConjugate

variable {n : Type*} [Fintype n] [DecidableEq n] {s : ℕ}

/-- The two addresses and a good, row-failure, or column-failure flag. -/
abbrev Basis (n : Type*) := (n × n) × Fin 3

/-- The common physical Hilbert space of sparse-slot preparations. -/
abbrev Space (n : Type*) [Fintype n] := EuclideanSpace ℂ (Basis n)

/-- Membership in the exactly `s` addressed slots, retaining zero padding. -/
def selected (loc : n → Fin s → n) (i j : n) : Prop :=
  j ∈ Finset.univ.image (loc i)

instance (loc : n → Fin s → n) (i j : n) : Decidable (selected loc i j) :=
  inferInstanceAs (Decidable (j ∈ Finset.univ.image (loc i)))

omit [Fintype n] in
@[simp] theorem selected_loc (loc : n → Fin s → n) (i : n) (k : Fin s) :
    selected loc i (loc i k) := Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩

/-- The uniform coefficient of each retained slot. -/
def weight (s : ℕ) : ℂ := (Real.sqrt (s : ℝ) : ℂ)⁻¹

theorem norm_weight_sq (s : ℕ) : ‖weight s‖ ^ 2 = (s : ℝ)⁻¹ := by
  simp only [weight, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), inv_pow]
  rw [Real.sq_sqrt (Nat.cast_nonneg s)]

theorem conj_weight_mul (s : ℕ) : conj (weight s) * weight s = (s : ℂ)⁻¹ := by
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_weight_sq]
  simp

theorem rowAmplitude_norm_le (a : ℝ) (ha : 0 < a) (z : ℂ) (hz : ‖z‖ ≤ a) :
    ‖rowAmplitude a z‖ ≤ 1 := by
  have h := norm_rowAmplitude_sq a ha z
  have hd := (div_le_one ha).2 hz
  nlinarith [norm_nonneg (rowAmplitude a z)]

theorem columnAmplitude_norm_le (a : ℝ) (ha : 0 < a) (z : ℂ) (hz : ‖z‖ ≤ a) :
    ‖columnAmplitude a z‖ ≤ 1 := by
  simpa [columnAmplitude] using rowAmplitude_norm_le a ha z hz

/-- A row slot has its failure amplitude on flag one. -/
def rowEntry (a : ℝ) (z : ℂ) (f : Fin 3) : ℂ :=
  if f = 0 then rowAmplitude a z
  else if f = 1 then (badAmplitude (rowAmplitude a z) : ℂ) else 0

/-- A column slot has its failure amplitude on flag two. -/
def columnEntry (a : ℝ) (z : ℂ) (f : Fin 3) : ℂ :=
  if f = 0 then columnAmplitude a z
  else if f = 2 then (badAmplitude (columnAmplitude a z) : ℂ) else 0

theorem rowEntry_mass (a : ℝ) (ha : 0 < a) (z : ℂ) (hz : ‖z‖ ≤ a) :
    ∑ f, ‖rowEntry a z f‖ ^ 2 = 1 := by
  simpa [Fin.sum_univ_succ, rowEntry, Complex.norm_real, Real.norm_eq_abs,
    sq_abs] using probability_sum (rowAmplitude a z) (rowAmplitude_norm_le a ha z hz)

theorem columnEntry_mass (a : ℝ) (ha : 0 < a) (z : ℂ) (hz : ‖z‖ ≤ a) :
    ∑ f, ‖columnEntry a z f‖ ^ 2 = 1 := by
  simpa [Fin.sum_univ_succ, columnEntry, Complex.norm_real, Real.norm_eq_abs,
    sq_abs] using probability_sum (columnAmplitude a z)
      (columnAmplitude_norm_le a ha z hz)

theorem entry_overlap (a : ℝ) (ha : 0 < a) (z : ℂ) :
    ∑ f, conj (rowEntry a z f) * columnEntry a z f = z / (a : ℂ) := by
  simpa [Fin.sum_univ_succ, rowEntry, columnEntry] using overlap a ha z

/-- The coordinate form makes all per-slot good and bad amplitudes explicit. -/
def row (H : Matrix n n ℂ) (a : ℝ) (loc : n → Fin s → n) :
    EuclideanSpace ℂ n →L[ℂ] Space n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => WithLp.toLp 2 (fun b =>
        if selected loc b.1.1 b.1.2 then
          weight s * rowEntry a (H b.1.1 b.1.2) b.2 * v b.1.1 else 0)
      map_add' := by
        intro v w
        apply PiLp.ext
        intro b
        by_cases h : selected loc b.1.1 b.1.2 <;> simp [h, mul_add]
      map_smul' := by
        intro z v
        apply PiLp.ext
        intro b
        by_cases h : selected loc b.1.1 b.1.2 <;> simp [h, mul_left_comm] }

/-- Column addresses are placed in physical row/column order `(loc j k,j)`. -/
def column (H : Matrix n n ℂ) (a : ℝ) (loc : n → Fin s → n) :
    EuclideanSpace ℂ n →L[ℂ] Space n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => WithLp.toLp 2 (fun b =>
        if selected loc b.1.2 b.1.1 then
          weight s * columnEntry a (H b.1.1 b.1.2) b.2 * v b.1.2 else 0)
      map_add' := by
        intro v w
        apply PiLp.ext
        intro b
        by_cases h : selected loc b.1.2 b.1.1 <;> simp [h, mul_add]
      map_smul' := by
        intro z v
        apply PiLp.ext
        intro b
        by_cases h : selected loc b.1.2 b.1.1 <;> simp [h, mul_left_comm] }

@[simp] theorem row_apply (H : Matrix n n ℂ) (a : ℝ) (loc : n → Fin s → n)
    (v : EuclideanSpace ℂ n) (i j : n) (f : Fin 3) :
    row H a loc v ((i,j),f) =
      if selected loc i j then weight s * rowEntry a (H i j) f * v i else 0 := rfl

@[simp] theorem column_apply (H : Matrix n n ℂ) (a : ℝ) (loc : n → Fin s → n)
    (v : EuclideanSpace ℂ n) (i j : n) (f : Fin 3) :
    column H a loc v ((i,j),f) =
      if selected loc j i then weight s * columnEntry a (H i j) f * v j else 0 := rfl

@[simp] theorem row_apply_loc (H : Matrix n n ℂ) (a : ℝ) (loc : n → Fin s → n)
    (v : EuclideanSpace ℂ n) (i : n) (k : Fin s) (f : Fin 3) :
    row H a loc v ((i, loc i k), f) = weight s * rowEntry a (H i (loc i k)) f * v i := by
  simp

@[simp] theorem column_apply_loc (H : Matrix n n ℂ) (a : ℝ) (loc : n → Fin s → n)
    (v : EuclideanSpace ℂ n) (j : n) (k : Fin s) (f : Fin 3) :
    column H a loc v ((loc j k, j), f) =
      weight s * columnEntry a (H (loc j k) j) f * v j := by simp

/-- Injective addressing sums over exactly the retained slots. -/
theorem sum_selected {M : Type*} [AddCommMonoid M] (loc : n → Fin s → n)
    (hinj : ∀ i, Function.Injective (loc i)) (i : n) (t : n → M) :
    (∑ j, if selected loc i j then t j else 0) = ∑ k, t (loc i k) := by
  classical
  rw [show (∑ j, if selected loc i j then t j else 0) =
      ∑ j ∈ Finset.univ.image (loc i), t j by
        exact Finset.sum_ite_mem_eq _ _]
  exact Finset.sum_image (fun k _ l _ h => hinj i h)

/-- Summing all local flags leaves one probability unit in each addressed slot. -/
theorem row_norm_sq (H : Matrix n n ℂ) (a : ℝ) (ha : 0 < a)
    (hH : ∀ i j, ‖H i j‖ ≤ a) (loc : n → Fin s → n)
    (hinj : ∀ i, Function.Injective (loc i)) (v : EuclideanSpace ℂ n) :
    ‖row H a loc v‖ ^ 2 = ((s : ℝ)⁻¹ * s) * ‖v‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [Fintype.sum_prod_type, row_apply]
  have he (i j : n) :
      (∑ f, ‖if selected loc i j then weight s * rowEntry a (H i j) f * v i else 0‖ ^ 2) =
        if selected loc i j then ‖weight s‖ ^ 2 * ‖v i‖ ^ 2 else 0 := by
    by_cases hij : selected loc i j
    · simp only [hij, ↓reduceIte, norm_mul, mul_pow]
      rw [← Finset.sum_mul, ← Finset.mul_sum, rowEntry_mass a ha (H i j) (hH i j)]
      ring
    · simp [hij]
  simp_rw [he, sum_selected loc hinj]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, norm_weight_sq]
  rw [PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Columns retain the same per-slot normalization. -/
theorem column_norm_sq (H : Matrix n n ℂ) (a : ℝ) (ha : 0 < a)
    (hH : ∀ i j, ‖H i j‖ ≤ a) (loc : n → Fin s → n)
    (hinj : ∀ j, Function.Injective (loc j)) (v : EuclideanSpace ℂ n) :
    ‖column H a loc v‖ ^ 2 = ((s : ℝ)⁻¹ * s) * ‖v‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [Fintype.sum_prod_type, column_apply]
  have he (i j : n) :
      (∑ f, ‖if selected loc j i then weight s * columnEntry a (H i j) f * v j else 0‖ ^ 2) =
        if selected loc j i then ‖weight s‖ ^ 2 * ‖v j‖ ^ 2 else 0 := by
    by_cases hij : selected loc j i
    · simp only [hij, ↓reduceIte, norm_mul, mul_pow]
      rw [← Finset.sum_mul, ← Finset.mul_sum, columnEntry_mass a ha (H i j) (hH i j)]
      ring
    · simp [hij]
  simp_rw [he]
  rw [Finset.sum_comm]
  simp_rw [sum_selected loc hinj]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, norm_weight_sq]
  rw [PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Injective nonempty row slots give an isometry, regardless of zero padding. -/
theorem row_norm (hs : 0 < s) (H : Matrix n n ℂ) (a : ℝ) (ha : 0 < a)
    (hH : ∀ i j, ‖H i j‖ ≤ a) (loc : n → Fin s → n)
    (hinj : ∀ i, Function.Injective (loc i)) (v : EuclideanSpace ℂ n) :
    ‖row H a loc v‖ = ‖v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have hs' : (s : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hs
  rw [row_norm_sq H a ha hH loc hinj, inv_mul_cancel₀ hs', one_mul]

/-- Injective nonempty column slots likewise give an isometry. -/
theorem column_norm (hs : 0 < s) (H : Matrix n n ℂ) (a : ℝ) (ha : 0 < a)
    (hH : ∀ i j, ‖H i j‖ ≤ a) (loc : n → Fin s → n)
    (hinj : ∀ j, Function.Injective (loc j)) (v : EuclideanSpace ℂ n) :
    ‖column H a loc v‖ = ‖v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have hs' : (s : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hs
  rw [column_norm_sq H a ha hH loc hinj, inv_mul_cancel₀ hs', one_mul]

/-- The complete row state has the adjoint isometry identity. -/
theorem row_adjoint_comp (hs : 0 < s) (H : Matrix n n ℂ) (a : ℝ) (ha : 0 < a)
    (hH : ∀ i j, ‖H i j‖ ≤ a) (loc : n → Fin s → n)
    (hinj : ∀ i, Function.Injective (loc i)) :
    (row H a loc)† ∘L row H a loc = 1 :=
  (row H a loc).norm_map_iff_adjoint_comp_self.mp (row_norm hs H a ha hH loc hinj)

/-- The complete column state has the adjoint isometry identity. -/
theorem column_adjoint_comp (hs : 0 < s) (H : Matrix n n ℂ) (a : ℝ) (ha : 0 < a)
    (hH : ∀ i j, ‖H i j‖ ≤ a) (loc : n → Fin s → n)
    (hinj : ∀ j, Function.Injective (loc j)) :
    (column H a loc)† ∘L column H a loc = 1 :=
  (column H a loc).norm_map_iff_adjoint_comp_self.mp (column_norm hs H a ha hH loc hinj)

/-- Only the shared good flag contributes at any addressed matrix entry. -/
theorem weighted_entry_overlap (a : ℝ) (ha : 0 < a) (z u v : ℂ) :
    (∑ f, conj (weight s * rowEntry a z f * u) *
      (weight s * columnEntry a z f * v)) =
        (z / ((s : ℂ) * a)) * conj u * v := by
  calc
    _ = (conj (weight s) * weight s) *
        (∑ f, conj (rowEntry a z f) * columnEntry a z f) * conj u * v := by
      simp only [Finset.mul_sum, Finset.sum_mul, map_mul]
      apply Finset.sum_congr rfl
      intro f _
      ring
    _ = _ := by rw [conj_weight_mul, entry_overlap a ha]; ring

/-- Covering every nonzero matrix entry suffices; padding may have arbitrary zeros. -/
theorem inner_row_column (H : Matrix n n ℂ) (a : ℝ) (ha : 0 < a)
    (rowloc colloc : n → Fin s → n)
    (hrow : ∀ i j, H i j ≠ 0 → selected rowloc i j)
    (hcol : ∀ i j, H i j ≠ 0 → selected colloc j i)
    (u v : EuclideanSpace ℂ n) :
    inner ℂ (row H a rowloc u) (column H a colloc v) =
      ∑ i, ∑ j, (H i j / ((s : ℂ) * a)) * conj (u i) * v j := by
  simp only [PiLp.inner_apply, Fintype.sum_prod_type, row_apply, column_apply,
    RCLike.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hr : selected rowloc i j
  · by_cases hc : selected colloc j i
    · simp only [hr, hc, ↓reduceIte]
      simpa only [mul_comm] using weighted_entry_overlap a ha (H i j) (u i) (v j)
    · have hz : H i j = 0 := by by_contra hz; exact hc (hcol i j hz)
      simp [hc, hz]
  · have hz : H i j = 0 := by by_contra hz; exact hr (hrow i j hz)
    simp [hr, hz]

/-- Exact action of the row adjoint followed by the column preparation. -/
theorem adjoint_column_apply (H : Matrix n n ℂ) (a : ℝ) (ha : 0 < a)
    (rowloc colloc : n → Fin s → n)
    (hrow : ∀ i j, H i j ≠ 0 → selected rowloc i j)
    (hcol : ∀ i j, H i j ≠ 0 → selected colloc j i)
    (v : EuclideanSpace ℂ n) (i : n) :
    (((row H a rowloc)†) (column H a colloc v)) i =
      ∑ j, (H i j / ((s : ℂ) * a)) * v j := by
  calc
    _ = inner ℂ (EuclideanSpace.single i (1 : ℂ))
        (((row H a rowloc)†) (column H a colloc v)) := by
      simp [EuclideanSpace.inner_single_left]
    _ = inner ℂ (row H a rowloc (EuclideanSpace.single i (1 : ℂ)))
        (column H a colloc v) := adjoint_inner_right _ _ _
    _ = _ := by
      rw [inner_row_column H a ha rowloc colloc hrow hcol]
      simp [PiLp.single_apply, apply_ite]

/-- Sparse-slot overlap is exactly the matrix normalized by `s * a`. -/
theorem overlap_eq_matrix (H : Matrix n n ℂ) (a : ℝ) (ha : 0 < a)
    (rowloc colloc : n → Fin s → n)
    (hrow : ∀ i j, H i j ≠ 0 → selected rowloc i j)
    (hcol : ∀ i j, H i j ≠ 0 → selected colloc j i) :
    (row H a rowloc)† ∘L column H a colloc =
      SparseStateOverlap.matrixOperator (fun i j => H i j / ((s : ℂ) * a)) := by
  ext v i
  exact adjoint_column_apply H a ha rowloc colloc hrow hcol v i

/-- Two actual locally normalized sparse-slot isometries realize `H / (s*a)`. -/
theorem overlap_certificate (hs : 0 < s) (H : Matrix n n ℂ) (a : ℝ) (ha : 0 < a)
    (hH : ∀ i j, ‖H i j‖ ≤ a) (rowloc colloc : n → Fin s → n)
    (hrowinj : ∀ i, Function.Injective (rowloc i))
    (hcolinj : ∀ j, Function.Injective (colloc j))
    (hrow : ∀ i j, H i j ≠ 0 → selected rowloc i j)
    (hcol : ∀ i j, H i j ≠ 0 → selected colloc j i) :
    (row H a rowloc)† ∘L row H a rowloc = 1 ∧
      (column H a colloc)† ∘L column H a colloc = 1 ∧
      (row H a rowloc)† ∘L column H a colloc =
        SparseStateOverlap.matrixOperator (fun i j => H i j / ((s : ℂ) * a)) :=
  ⟨row_adjoint_comp hs H a ha hH rowloc hrowinj,
    column_adjoint_comp hs H a ha hH colloc hcolinj,
    overlap_eq_matrix H a ha rowloc colloc hrow hcol⟩

end
end SparseHamiltonian.SparseSlotStates
