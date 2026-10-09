import SparseLinearSystems.Augmented.Solution
import SparseHamiltonian.NativeCayleyProgram

/-!
# The split boundary: a sparse Cayley representation of the dilation

Lemma `qls:lem:entry` is applied in the manuscript to the sparse lift `H₀`.
Here the same edge generator of the native Cayley circuit for `A` itself is
used with a different public isometry.  The *split boundary*

`J_split (w₀, w₁) = s^{-1/2} (L_slot w₀ ⊕ L_slot w₁)`

sends the first dilation sector to the row orientation and the second to the
column orientation.  After the locator conjugation used by
`NativeCayleyProgram`, its compression is the Hermitian dilation of `A`:

`J_split† G J_split = s^{-1/2} [[0, A], [A†, 0]]`   (`split_compression`),

with second moment `‖G J_split w‖ ≤ ‖w‖` (`split_moment`) whenever every row
and column of `A` has Euclidean norm at most one.  No derived sparse-access
structure is needed: the circuit is the 18-query `NativeCayleyProgram.program`.
-/

namespace SparseLinearSystems.SplitBoundary

noncomputable section
open ContinuousLinearMap SparseHamiltonian SparseHamiltonian.SparseEdgeMoments
  SparseHamiltonian.FixedLocatorConjugation
open scoped InnerProduct

variable {n : Type*} [Fintype n] [DecidableEq n] {s : ℕ}

local notation "Dbl" => HilbertRegularization.Double (EuclideanSpace ℂ n)

/-- Separate inputs for the two edge orientations. -/
def split (L R : EuclideanSpace ℂ n →L[ℂ] EdgeSpace n) : Dbl →L[ℂ] OrientedSpace n :=
  stack L 0 ∘L WithLp.fstL 2 ℂ (EuclideanSpace ℂ n) (EuclideanSpace ℂ n) +
    stack 0 R ∘L WithLp.sndL 2 ℂ (EuclideanSpace ℂ n) (EuclideanSpace ℂ n)

omit [DecidableEq n] in
@[simp] theorem split_inl (L R : EuclideanSpace ℂ n →L[ℂ] EdgeSpace n) (w : Dbl) (e : n × n) :
    split L R w (.inl e) = L w.fst e := by
  simp [split]

omit [DecidableEq n] in
@[simp] theorem split_inr (L R : EuclideanSpace ℂ n →L[ℂ] EdgeSpace n) (w : Dbl) (e : n × n) :
    split L R w (.inr e) = R w.snd e := by
  simp [split]

omit [DecidableEq n] in
theorem leftPart_split (L R : EuclideanSpace ℂ n →L[ℂ] EdgeSpace n) (w : Dbl) :
    leftPart (split L R w) = L w.fst := by
  ext e; exact split_inl L R w e

omit [DecidableEq n] in
theorem rightPart_split (L R : EuclideanSpace ℂ n →L[ℂ] EdgeSpace n) (w : Dbl) :
    rightPart (split L R w) = R w.snd := by
  ext e; exact split_inr L R w e

omit [DecidableEq n] in
theorem inner_split (L R L' R' : EuclideanSpace ℂ n →L[ℂ] EdgeSpace n) (w w' : Dbl) :
    inner ℂ (split L R w) (split L' R' w') =
      inner ℂ (L w.fst) (L' w'.fst) + inner ℂ (R w.snd) (R' w'.snd) := by
  simp only [PiLp.inner_apply, Fintype.sum_sum_type, split_inl, split_inr]

omit [DecidableEq n] in
theorem norm_sq_split (L R : EuclideanSpace ℂ n →L[ℂ] EdgeSpace n) (w : Dbl) :
    ‖split L R w‖ ^ 2 = ‖L w.fst‖ ^ 2 + ‖R w.snd‖ ^ 2 := by
  simp only [PiLp.norm_sq_eq_of_L2, Fintype.sum_sum_type, split_inl, split_inr]

omit [DecidableEq n] in
theorem block_split (A B : EdgeSpace n →L[ℂ] EdgeSpace n)
    (L R : EuclideanSpace ℂ n →L[ℂ] EdgeSpace n) :
    block A B ∘L split L R = split (A ∘L L) (B ∘L R) := by
  ext w e
  cases e with
  | inl e => simp only [comp_apply, block_inl, leftPart_split, split_inl]
  | inr e => simp only [comp_apply, block_inr, rightPart_split, split_inr]

/-- The fixed split boundary built from the public slot list. -/
def fixedSplit (slot : Fin s ↪ n) : Dbl →L[ℂ] OrientedSpace n :=
  (((Real.sqrt (s : ℝ))⁻¹ : ℝ) : ℂ) •
    split (rowIncidence (fun _ => slot)) (rowIncidence (fun _ => slot))

theorem gram_apply (loc : n → Fin s → n) (hinj : ∀ i, Function.Injective (loc i))
    (v w : EuclideanSpace ℂ n) :
    inner ℂ (rowIncidence loc v) (rowIncidence loc w) = (s : ℂ) * inner ℂ v w := by
  rw [← adjoint_inner_right, ← comp_apply, rowIncidence_gram loc hinj, smul_apply,
    one_apply_eq_self, inner_smul_right]

theorem gram_apply_column (loc : n → Fin s → n) (hinj : ∀ j, Function.Injective (loc j))
    (v w : EuclideanSpace ℂ n) :
    inner ℂ (columnIncidence loc v) (columnIncidence loc w) = (s : ℂ) * inner ℂ v w := by
  rw [← adjoint_inner_right, ← comp_apply, columnIncidence_gram loc hinj, smul_apply,
    one_apply_eq_self, inner_smul_right]

/-- The fixed split boundary is an isometry. -/
theorem fixedSplit_isometry (slot : Fin s ↪ n) (hs : 0 < s) :
    ((fixedSplit slot)†) ∘L fixedSplit slot = 1 := by
  apply (fixedSplit slot).norm_map_iff_adjoint_comp_self.mp
  intro w
  have hsr : (0 : ℝ) < s := by exact_mod_cast hs
  have hinj : ∀ _ : n, Function.Injective (fun k : Fin s => slot k) := fun _ => slot.injective
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [fixedSplit, smul_apply, norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
    sq_abs, inv_pow, Real.sq_sqrt hsr.le, norm_sq_split]
  have h1 : ‖rowIncidence (fun _ => slot) w.fst‖ ^ 2 = s * ‖w.fst‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ),
      gram_apply (fun _ => slot) hinj]
    simp
  have h2 : ‖rowIncidence (fun _ => slot) w.snd‖ ^ 2 = s * ‖w.snd‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ),
      gram_apply (fun _ => slot) hinj]
    simp
  rw [h1, h2, WithLp.prod_norm_sq_eq_of_L2]
  field_simp

variable {X Z : Type*}

/-- The actual locator maps the fixed split boundary to the incidence boundary. -/
theorem locator_fixedSplit (D : NativeSparseBlockEncoding.Data X n Z s) (x : X) :
    locator D x ∘L fixedSplit D.slot =
      (((Real.sqrt (s : ℝ))⁻¹ : ℝ) : ℂ) •
        split (rowIncidence (D.rowloc x)) (columnIncidence (D.colloc x)) := by
  rw [fixedSplit, comp_smul]
  change _ • (block (D.rowOracle x) (D.columnOracle x) ∘L _) = _
  rw [block_split, rowOracle_slots, columnOracle_slots]

omit [DecidableEq n] in
/-- The edge generator applied to a split vector. -/
theorem entryGenerator_split (H : Matrix n n ℂ) (L R : EuclideanSpace ℂ n →L[ℂ] EdgeSpace n)
    (w : Dbl) :
    entryGenerator H (split L R w) =
      split (edgeDiagonal H ∘L R) (((edgeDiagonal H)†) ∘L L)
        (WithLp.toLp 2 (w.snd, w.fst)) := by
  rw [edgeDiagonal_adjoint]
  ext e
  cases e with
  | inl e => rcases e with ⟨i, j⟩; simp [entryGenerator_inl, split_inl]
  | inr e => rcases e with ⟨i, j⟩; simp [entryGenerator_inr, split_inr]

/-- **Split compression.** -/
theorem split_compression (D : NativeSparseBlockEncoding.Data X n Z s) (x : X) :
    ((fixedSplit D.slot)†) ∘L FixedNativeCayleySimulation.generator D x ∘L fixedSplit D.slot =
      ((Real.sqrt (s : ℝ) : ℝ) : ℂ)⁻¹ •
        HilbertRegularization.dilation (SparseStateOverlap.matrixOperator (D.matrix x)) := by
  have hs : 0 < s := D.slots_pos
  have hsr : (0 : ℝ) < s := by exact_mod_cast hs
  have hsq : 0 < Real.sqrt (s : ℝ) := Real.sqrt_pos.mpr hsr
  unfold FixedNativeCayleySimulation.generator
  rw [UnitaryCayleyTransport.compression, locator_fixedSplit]
  apply ContinuousLinearMap.ext
  intro w
  apply ext_inner_left ℂ
  intro y
  set c : ℂ := (((Real.sqrt (s : ℝ))⁻¹ : ℝ) : ℂ)
  set Lr := rowIncidence (D.rowloc x)
  set Rc := columnIncidence (D.colloc x)
  rw [comp_apply, comp_apply, adjoint_inner_right, smul_apply, smul_apply, smul_apply,
    inner_smul_left, inner_smul_right, generator, smul_apply, inner_smul_right,
    map_smul, inner_smul_right, entryGenerator_split, inner_split]
  simp only [comp_apply]
  -- the two incidence overlaps
  have hA : ∀ u v : EuclideanSpace ℂ n, inner ℂ (Lr u) (edgeDiagonal (D.matrix x) (Rc v)) =
      inner ℂ u (SparseStateOverlap.matrixOperator (D.matrix x) v) := by
    intro u v
    rw [← adjoint_inner_right, ← comp_apply, ← comp_apply,
      ← incidence_overlap (D.matrix x) (D.rowloc x) (D.colloc x) (D.row_covers x)
        (D.column_covers x)]
    rfl
  have hAd : ∀ u v : EuclideanSpace ℂ n,
      inner ℂ (Rc u) (((edgeDiagonal (D.matrix x))†) (Lr v)) =
        inner ℂ u (((SparseStateOverlap.matrixOperator (D.matrix x))†) v) := by
    intro u v
    rw [← adjoint_inner_right, ← comp_apply, ← comp_apply,
      ← incidence_reverse_overlap (D.matrix x) (D.rowloc x) (D.colloc x) (D.row_covers x)
        (D.column_covers x)]
    rfl
  rw [hA, hAd, HilbertRegularization.dilation_apply, WithLp.prod_inner_apply]
  simp only [WithLp.ofLp_fst, WithLp.ofLp_snd, WithLp.toLp_fst, WithLp.toLp_snd,
    star_eq_adjoint]
  have hc : (starRingEnd ℂ) c * (c * ((Real.sqrt (s : ℝ) : ℂ))) =
      ((Real.sqrt (s : ℝ) : ℝ) : ℂ)⁻¹ := by
    simp only [c, Complex.conj_ofReal]
    have hne : (Real.sqrt (s : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsq.ne'
    push_cast
    field_simp
  rw [← hc]
  ring

/-- **Split second moment.** -/
theorem split_moment (D : NativeSparseBlockEncoding.Data X n Z s) (x : X)
    (hrow : ∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ 1) (hcol : ∀ j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ 1)
    (w : Dbl) :
    ‖FixedNativeCayleySimulation.generator D x (fixedSplit D.slot w)‖ ^ 2 ≤ ‖w‖ ^ 2 := by
  have hs : 0 < s := D.slots_pos
  have hsr : (0 : ℝ) < s := by exact_mod_cast hs
  have hsq : 0 < Real.sqrt (s : ℝ) := Real.sqrt_pos.mpr hsr
  have hU := locator_unitary D x
  unfold FixedNativeCayleySimulation.generator
  rw [UnitaryCayleyTransport.conjugate]
  change ‖((locator D x)†) (generator (D.matrix x) s (locator D x (fixedSplit D.slot w)))‖ ^ 2 ≤ _
  have hnorm : ∀ v : OrientedSpace n, ‖((locator D x)†) v‖ = ‖v‖ := by
    intro v
    have h1 : (((locator D x)†)†) ∘L ((locator D x)†) = 1 := by
      rw [adjoint_adjoint]; exact hU.2
    exact (((locator D x)†).norm_map_iff_adjoint_comp_self.mpr h1) v
  rw [hnorm]
  have hloc := congrArg (fun T : Dbl →L[ℂ] OrientedSpace n => T w) (locator_fixedSplit D x)
  simp only [comp_apply] at hloc
  rw [hloc, smul_apply]
  have hscal : generator (D.matrix x) s ((((Real.sqrt (s : ℝ))⁻¹ : ℝ) : ℂ) •
      split (rowIncidence (D.rowloc x)) (columnIncidence (D.colloc x)) w) =
      entryGenerator (D.matrix x)
        (split (rowIncidence (D.rowloc x)) (columnIncidence (D.colloc x)) w) := by
    rw [map_smul, generator, smul_apply, smul_smul]
    have hone : (((Real.sqrt (s : ℝ))⁻¹ : ℝ) : ℂ) * (Real.sqrt (s : ℝ) : ℂ) = 1 := by
      have hne : (Real.sqrt (s : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsq.ne'
      push_cast
      exact inv_mul_cancel₀ hne
    rw [hone, one_smul]
  rw [hscal, entryGenerator_split, norm_sq_split]
  simp only [comp_apply, WithLp.toLp_fst, WithLp.toLp_snd]
  rw [diagonal_column_norm_sq _ _ (D.column_covers x),
    adjointDiagonal_row_norm_sq _ _ (D.row_covers x), WithLp.prod_norm_sq_eq_of_L2,
    EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  have hr : (∑ i, (∑ j, ‖D.matrix x i j‖ ^ 2) * ‖w.fst i‖ ^ 2) ≤ ∑ i, ‖w.fst i‖ ^ 2 :=
    Finset.sum_le_sum fun i _ => by
      have := hrow i; nlinarith [sq_nonneg ‖w.fst i‖]
  have hc : (∑ j, (∑ i, ‖D.matrix x i j‖ ^ 2) * ‖w.snd j‖ ^ 2) ≤ ∑ j, ‖w.snd j‖ ^ 2 :=
    Finset.sum_le_sum fun j _ => by
      have := hcol j; nlinarith [sq_nonneg ‖w.snd j‖]
  linarith

end

end SparseLinearSystems.SplitBoundary
