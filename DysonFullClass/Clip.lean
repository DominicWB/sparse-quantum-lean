import ODELowerBoundExtensions.Dyson.Access
import SparseHamiltonian.SparseValuePrecision
import SparseHamiltonian.MagnitudeBands

set_option autoImplicit false

/-!
# Clipping the decoded entries to the public entry bound

Manuscript, proof of Lemma `odel:lem:dyson`: "If the supplied bound already gives
`|Ã_{j,ab}| ≤ η` for every entry, set `A_mesh(t) = Ã_j` on cell `j`. Otherwise radially project
each decoded entry onto the disk `|w| ≤ η` and use this clipped matrix on that cell. Every true
entry lies in the disk. Projection cannot increase its entrywise error, and the union of the
supports of `Ã_j` and `A(t)` has at most `2s` positions per row and column. Before clipping, each
entry error is at most `‖Ã_j - A(t)‖`. The maximum absolute row and column sums therefore bound the
clipped operator error by `2s ‖Ã_j - A(t)‖` [...] Clipping the decoded value uses no additional
matrix queries and does not enlarge its support."

* `radialClip η w`: the radial projection onto `|w| ≤ η`; `radialClip_zero` (so lists and padding
  stay valid), `norm_radialClip_le`, `radialClip_eq_zero_iff`, `radialClip_of_norm_le`, and
  `norm_radialClip_sub_le`: `|p_η(w) - a| ≤ |w - a|` for `|a| ≤ η`.
* `clipData D η`: the same native access (`oracles (clipData D η) = oracles D`, by `rfl`: the
  same row, column and value oracles and the same value word; only the fixed decoder of the
  controlled rotation changes to `p_η ∘ decode`), with entry bound `η` and represented matrix
  `p_η(D.matrix)`. The six-query block encoding of `clipData D η` therefore encodes
  `p_η(Ã)/(s η)` on the original access: the normalisation `z = s η T` is exact for any decoder
  scale.
* `clipData_matrix_of_le`: no clipping happens when the represented entries are already capped by
  `η`.
* `opMatrix`, `matrixOperator_opMatrix`: the matrix of an operator on `ℂ^n`;
  `norm_entry_sub_le`: entry errors are at most the operator-norm error.
* `clip_sub_le`: pointwise, `‖p_η(W) - A‖ ≤ 2 s ‖W - A‖` when `|A_ij| ≤ η` and both have at most
  `s` nonzeros per row and column (not an operator-norm nonexpansiveness claim).
* `data_row_sparse`, `data_column_sparse`: a represented sample has at most `s` nonzeros per row
  and column (its row and column lists).
-/

namespace DysonFullClass

noncomputable section

open SparseHamiltonian ContinuousLinearMap NativeSparseBlockEncoding SparseStateOverlap
open scoped BigOperators InnerProduct ComplexConjugate

/-! ### The radial projection -/

/-- **The radial projection** of a complex number onto the closed disk `|w| ≤ η`. -/
def radialClip (η : ℝ) (w : ℂ) : ℂ := if ‖w‖ ≤ η then w else ((η / ‖w‖ : ℝ) : ℂ) * w

theorem radialClip_of_norm_le {η : ℝ} {w : ℂ} (h : ‖w‖ ≤ η) : radialClip η w = w := if_pos h

/-- `p_η(0) = 0`: the clipped entry of a missing position stays zero. -/
theorem radialClip_zero {η : ℝ} (hη : 0 ≤ η) : radialClip η 0 = 0 :=
  radialClip_of_norm_le (by rw [norm_zero]; exact hη)

theorem norm_radialClip_le {η : ℝ} (hη : 0 ≤ η) (w : ℂ) : ‖radialClip η w‖ ≤ η := by
  unfold radialClip
  split_ifs with h
  · exact h
  · push Not at h
    have hw : 0 < ‖w‖ := lt_of_le_of_lt hη h
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hη hw.le),
      div_mul_cancel₀ η hw.ne']

theorem radialClip_eq_zero_iff {η : ℝ} (hη : 0 < η) (w : ℂ) : radialClip η w = 0 ↔ w = 0 := by
  constructor
  · intro h
    unfold radialClip at h
    split_ifs at h with h1
    · exact h
    · push Not at h1
      have hw : 0 < ‖w‖ := lt_trans hη h1
      rcases mul_eq_zero.mp h with h2 | h2
      · exfalso
        have : (η / ‖w‖ : ℝ) = 0 := by exact_mod_cast h2
        exact (div_pos hη hw).ne' this
      · exact h2
  · rintro rfl
    exact radialClip_zero hη.le

/-- **Projection does not increase the distance to a point of the disk**:
`|p_η(w) - a| ≤ |w - a|` for `|a| ≤ η`. -/
theorem norm_radialClip_sub_le {η : ℝ} (hη : 0 ≤ η) {a : ℂ} (ha : ‖a‖ ≤ η) (w : ℂ) :
    ‖radialClip η w - a‖ ≤ ‖w - a‖ := by
  unfold radialClip
  split_ifs with h
  · exact le_rfl
  · push Not at h
    set ρ := ‖w‖ with hρ
    have hρ0 : 0 < ρ := lt_of_le_of_lt hη h
    set κ : ℝ := η / ρ with hκ
    have hκ0 : 0 ≤ κ := div_nonneg hη hρ0.le
    have hκ1 : κ ≤ 1 := (div_le_one hρ0).mpr h.le
    have hκρ : κ * ρ = η := div_mul_cancel₀ η hρ0.ne'
    have hR : (w * conj a).re ≤ ρ * η := by
      calc (w * conj a).re ≤ ‖w * conj a‖ := Complex.re_le_norm _
        _ = ρ * ‖a‖ := by rw [norm_mul, Complex.norm_conj]
        _ ≤ ρ * η := mul_le_mul_of_nonneg_left ha hρ0.le
    have hN : Complex.normSq w = ρ ^ 2 := by rw [hρ, Complex.sq_norm]
    have hsq : ‖(κ : ℂ) * w - a‖ ^ 2 ≤ ‖w - a‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_sub, Complex.normSq_sub,
        Complex.normSq_mul, Complex.normSq_ofReal, hN]
      have hre : ((κ : ℂ) * w * conj a).re = κ * (w * conj a).re := by
        rw [mul_assoc, Complex.re_ofReal_mul]
      rw [hre]
      have key : 0 ≤ (1 - κ) * (ρ * (ρ - η)) := mul_nonneg (by linarith) (mul_nonneg hρ0.le
        (by linarith))
      nlinarith [mul_le_mul_of_nonneg_left hR (by linarith : (0 : ℝ) ≤ 2 * (1 - κ))]
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

/-! ### The clipped data: same oracles, clipped decoder -/

variable {X n Z : Type*} [Fintype n] [DecidableEq n] {s : ℕ}

/-- **The clipped data**: the same slots, tables, locators and oracles, the decoder `p_η ∘ decode`
of the controlled rotation, entry bound `η`, and represented matrix `p_η(D.matrix)`. -/
def clipData (D : Data X n Z s) (η : ℝ) (hη : 0 < η) : Data X n Z s where
  slot := D.slot
  slots_pos := D.slots_pos
  scale := η
  scale_pos := hη
  matrix := fun x i j => radialClip η (D.matrix x i j)
  table := D.table
  decode := fun a z => radialClip η (D.decode a z)
  decode_bound := fun _ _ => norm_radialClip_le hη.le _
  decoded := fun x i j => by rw [D.decoded]
  rowloc := D.rowloc
  colloc := D.colloc
  row_injective := D.row_injective
  column_injective := D.column_injective
  row_covers := fun x i j h => D.row_covers x i j fun h0 => h (by rw [h0]; exact radialClip_zero hη.le)
  column_covers := fun x i j h =>
    D.column_covers x i j fun h0 => h (by rw [h0]; exact radialClip_zero hη.le)
  rowOracle := D.rowOracle
  columnOracle := D.columnOracle
  row_unitary := D.row_unitary
  column_unitary := D.column_unitary
  row_valid := D.row_valid
  column_valid := D.column_valid

variable [Fintype Z] [AddCommGroup Z]

/-- **Clipping uses the original access**: the native oracles of the clipped data are those of
`D` (the same row, column and value calls); only the fixed rotation decoder differs. -/
theorem oracles_clipData (D : Data X n Z s) (η : ℝ) (hη : 0 < η) :
    oracles (clipData D η hη) = oracles D := rfl

omit [Fintype Z] [AddCommGroup Z] in
@[simp] theorem clipData_matrix (D : Data X n Z s) (η : ℝ) (hη : 0 < η) (x : X) (i j : n) :
    (clipData D η hη).matrix x i j = radialClip η (D.matrix x i j) := rfl

omit [Fintype Z] [AddCommGroup Z] in
@[simp] theorem clipData_scale (D : Data X n Z s) (η : ℝ) (hη : 0 < η) :
    (clipData D η hη).scale = η := rfl

omit [Fintype Z] [AddCommGroup Z] in
/-- **No clipping when the represented entries are capped**: if every represented entry has
modulus at most `η`, the clipped data represents the same matrices. -/
theorem clipData_matrix_of_le (D : Data X n Z s) (η : ℝ) (hη : 0 < η)
    (h : ∀ x i j, ‖D.matrix x i j‖ ≤ η) : (clipData D η hη).matrix = D.matrix := by
  funext x i j
  exact radialClip_of_norm_le (h x i j)

/-! ### Entries and supports -/

/-- The matrix of an operator on `ℂ^n`: `opMatrix G i j = (G e_j)_i`. -/
def opMatrix (G : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) : Matrix n n ℂ :=
  fun i j => G (EuclideanSpace.single j 1) i

omit [Fintype Z] [AddCommGroup Z] in
theorem matrixOperator_opMatrix (G : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) :
    matrixOperator (opMatrix G) = G := by
  ext v i
  rw [matrixOperator_apply]
  have hv : v = ∑ j, v j • EuclideanSpace.single j (1 : ℂ) := by
    ext k
    simp [Pi.single_apply]
  conv_rhs => rw [hv]
  rw [map_sum, WithLp.ofLp_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, PiLp.smul_apply, smul_eq_mul, mul_comm]
  rfl

omit [Fintype Z] [AddCommGroup Z] in
/-- An entry is at most the operator norm. -/
theorem norm_entry_le (W : Matrix n n ℂ) (i j : n) : ‖W i j‖ ≤ ‖matrixOperator W‖ := by
  have h : matrixOperator W (EuclideanSpace.single j 1) i = W i j := by
    rw [matrixOperator_apply]
    simp [PiLp.single_apply]
  calc ‖W i j‖ = ‖matrixOperator W (EuclideanSpace.single j 1) i‖ := by rw [h]
    _ ≤ ‖matrixOperator W (EuclideanSpace.single j 1)‖ := PiLp.norm_apply_le _ _
    _ ≤ ‖matrixOperator W‖ * ‖EuclideanSpace.single j (1 : ℂ)‖ := le_opNorm _ _
    _ = ‖matrixOperator W‖ := by rw [PiLp.norm_single, norm_one, mul_one]

omit [Fintype Z] [AddCommGroup Z] in
/-- Entry errors are at most the operator-norm error. -/
theorem norm_entry_sub_le (W A : Matrix n n ℂ) (i j : n) :
    ‖W i j - A i j‖ ≤ ‖matrixOperator W - matrixOperator A‖ := by
  rw [← SparseValuePrecision.matrixOperator_sub]
  exact norm_entry_le (W - A) i j

omit [Fintype Z] [AddCommGroup Z] in
/-- **The clipping bound** (proof of Lemma `odel:lem:dyson`): if `|A_ij| ≤ η` and both `W` and `A`
have at most `s` nonzeros in every row and column, then
`‖p_η(W) - A‖ ≤ 2 s ‖W - A‖` (operator norms). -/
theorem clip_sub_le (W A : Matrix n n ℂ) {η : ℝ} (hη : 0 ≤ η) (s : ℕ)
    (hA : ∀ i j, ‖A i j‖ ≤ η)
    (hWr : ∀ i, (Finset.univ.filter fun j => W i j ≠ 0).card ≤ s)
    (hWc : ∀ j, (Finset.univ.filter fun i => W i j ≠ 0).card ≤ s)
    (hAr : ∀ i, (Finset.univ.filter fun j => A i j ≠ 0).card ≤ s)
    (hAc : ∀ j, (Finset.univ.filter fun i => A i j ≠ 0).card ≤ s) :
    ‖matrixOperator (fun i j => radialClip η (W i j)) - matrixOperator A‖ ≤
      2 * s * ‖matrixOperator W - matrixOperator A‖ := by
  classical
  set δ := ‖matrixOperator W - matrixOperator A‖ with hδ
  have hδ0 : 0 ≤ δ := norm_nonneg _
  have hent : ∀ i j, ‖radialClip η (W i j) - A i j‖ ≤ δ := fun i j =>
    (norm_radialClip_sub_le hη (hA i j) (W i j)).trans (norm_entry_sub_le W A i j)
  rw [← SparseValuePrecision.matrixOperator_sub]
  have hcast : ((2 * s : ℕ) : ℝ) * δ = 2 * s * δ := by push_cast; ring
  rw [← hcast]
  apply SparseValuePrecision.norm_matrixOperator_le_nonneg _ _ (by positivity)
  · intro i
    refine SparseValuePrecision.sum_norm_le_of_allowed _
      ((Finset.univ.filter fun j => W i j ≠ 0) ∪ (Finset.univ.filter fun j => A i j ≠ 0))
      (2 * s) δ hδ0 ((Finset.card_union_le _ _).trans (by have := hWr i; have := hAr i; omega))
      ?_ (fun j => hent i j)
    intro j hj
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, not_or,
      not_not] at hj
    simp only [Matrix.sub_apply, hj.1, hj.2, radialClip_zero hη, sub_zero]
  · intro j
    refine SparseValuePrecision.sum_norm_le_of_allowed (fun i =>
        (fun i j => radialClip η (W i j)) i j - A i j)
      ((Finset.univ.filter fun i => W i j ≠ 0) ∪ (Finset.univ.filter fun i => A i j ≠ 0))
      (2 * s) δ hδ0 ((Finset.card_union_le _ _).trans (by have := hWc j; have := hAc j; omega))
      ?_ (fun i => hent i j)
    intro i hi
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, not_or,
      not_not] at hi
    simp only [hi.1, hi.2, radialClip_zero hη, sub_zero]

omit [Fintype Z] [AddCommGroup Z] in
/-- A represented sample has at most `s` nonzeros in every row (its row list). -/
theorem data_row_sparse (D : Data X n Z s) (x : X) (i : n) :
    (Finset.univ.filter fun j => D.matrix x i j ≠ 0).card ≤ s := by
  classical
  have hsub : (Finset.univ.filter fun j => D.matrix x i j ≠ 0) ⊆
      Finset.univ.image (D.rowloc x i) := by
    intro j hj
    exact D.row_covers x i j (Finset.mem_filter.mp hj).2
  calc _ ≤ (Finset.univ.image (D.rowloc x i)).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Fin s)).card := Finset.card_image_le
    _ = s := by simp

omit [Fintype Z] [AddCommGroup Z] in
/-- A represented sample has at most `s` nonzeros in every column (its column list). -/
theorem data_column_sparse (D : Data X n Z s) (x : X) (j : n) :
    (Finset.univ.filter fun i => D.matrix x i j ≠ 0).card ≤ s := by
  classical
  have hsub : (Finset.univ.filter fun i => D.matrix x i j ≠ 0) ⊆
      Finset.univ.image (D.colloc x j) := by
    intro i hi
    exact D.column_covers x i j (Finset.mem_filter.mp hi).2
  calc _ ≤ (Finset.univ.image (D.colloc x j)).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Fin s)).card := Finset.card_image_le
    _ = s := by simp

end

end DysonFullClass
