import SparseHamiltonian.SparseEdgeMoments

namespace SparseHamiltonian.SparseEdgeMoments
noncomputable section
open ContinuousLinearMap SparseSlotStates
open scoped BigOperators InnerProduct ComplexConjugate
variable {n : Type*} [Fintype n] [DecidableEq n] {s : ℕ}

abbrev OrientedSpace (n : Type*) [Fintype n] :=
  EuclideanSpace ℂ ((n × n) ⊕ (n × n))

/-- The two edge orientations are orthogonal Hilbert sectors. -/
def stack (A B : EuclideanSpace ℂ n →L[ℂ] EdgeSpace n) :
    EuclideanSpace ℂ n →L[ℂ] OrientedSpace n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => WithLp.toLp 2 (Sum.elim (fun e => A v e) (fun e => B v e))
      map_add' := by intro v w; ext e; cases e <;> simp
      map_smul' := by intro z v; ext e; cases e <;> simp }

omit [DecidableEq n] in
@[simp] theorem stack_inl (A B : EuclideanSpace ℂ n →L[ℂ] EdgeSpace n)
    (v : EuclideanSpace ℂ n) (e : n × n) : stack A B v (.inl e) = A v e := rfl
omit [DecidableEq n] in
@[simp] theorem stack_inr (A B : EuclideanSpace ℂ n →L[ℂ] EdgeSpace n)
    (v : EuclideanSpace ℂ n) (e : n × n) : stack A B v (.inr e) = B v e := rfl

omit [DecidableEq n] in
theorem stack_norm_sq (A B : EuclideanSpace ℂ n →L[ℂ] EdgeSpace n)
    (v : EuclideanSpace ℂ n) : ‖stack A B v‖ ^ 2 = ‖A v‖ ^ 2 + ‖B v‖ ^ 2 := by
  simp only [PiLp.norm_sq_eq_of_L2, Fintype.sum_sum_type, stack_inl, stack_inr]

omit [DecidableEq n] in
theorem stack_inner (A B C D : EuclideanSpace ℂ n →L[ℂ] EdgeSpace n)
    (u v : EuclideanSpace ℂ n) :
    inner ℂ (stack A B u) (stack C D v) = inner ℂ (A u) (C v) + inner ℂ (B u) (D v) := by
  simp only [PiLp.inner_apply, Fintype.sum_sum_type, stack_inl, stack_inr]

omit [DecidableEq n] in
theorem stack_adjoint_stack (A B C D : EuclideanSpace ℂ n →L[ℂ] EdgeSpace n) :
    (stack A B)† ∘L stack C D = A† ∘L C + B† ∘L D := by
  apply ContinuousLinearMap.ext
  intro v
  apply ext_inner_left ℂ
  intro u
  simp only [comp_apply, adjoint_inner_right, add_apply, inner_add_right, stack_inner]

/-- The unscaled Hermitian edge generator exchanges the two orientations. -/
def entryGenerator (H : Matrix n n ℂ) : OrientedSpace n →L[ℂ] OrientedSpace n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => WithLp.toLp 2 (Sum.elim
        (fun e => H e.1 e.2 * v (.inr e))
        (fun e => star (H e.1 e.2) * v (.inl e)))
      map_add' := by intro v w; ext e; cases e <;> simp [mul_add]
      map_smul' := by intro z v; ext e; cases e <;> simp [mul_left_comm] }

omit [DecidableEq n] in
@[simp] theorem entryGenerator_inl (H : Matrix n n ℂ) (v : OrientedSpace n) (e : n × n) :
    entryGenerator H v (.inl e) = H e.1 e.2 * v (.inr e) := rfl
omit [DecidableEq n] in
@[simp] theorem entryGenerator_inr (H : Matrix n n ℂ) (v : OrientedSpace n) (e : n × n) :
    entryGenerator H v (.inr e) = star (H e.1 e.2) * v (.inl e) := rfl

omit [DecidableEq n] in
/-- Hermiticity of the edge generator holds even for a non-Hermitian input matrix. -/
theorem entryGenerator_adjoint (H : Matrix n n ℂ) : (entryGenerator H)† = entryGenerator H := by
  apply ContinuousLinearMap.ext
  intro v
  apply ext_inner_right ℂ
  intro w
  rw [adjoint_inner_left]
  simp only [PiLp.inner_apply, Fintype.sum_sum_type, entryGenerator_inl,
    entryGenerator_inr, RCLike.inner_apply, Complex.star_def, map_mul, Complex.conj_conj]
  simp only [mul_comm, mul_left_comm, mul_assoc, add_comm]

omit [DecidableEq n] in
theorem entryGenerator_stack (H : Matrix n n ℂ)
    (A B : EuclideanSpace ℂ n →L[ℂ] EdgeSpace n) :
    entryGenerator H ∘L stack A B =
      stack (edgeDiagonal H ∘L B) ((edgeDiagonal H)† ∘L A) := by
  rw [edgeDiagonal_adjoint]
  ext v e
  cases e with
  | inl e => rcases e with ⟨i,j⟩; rfl
  | inr e => rcases e with ⟨i,j⟩; rfl

omit [DecidableEq n] in
/-- A maximum-entry bound controls the full operator, including unused edges. -/
theorem entryGenerator_norm_le (H : Matrix n n ℂ) (a : ℝ) (ha : 0 ≤ a)
    (hH : ∀ i j, ‖H i j‖ ≤ a) : ‖entryGenerator H‖ ≤ a := by
  apply opNorm_le_bound _ ha
  intro v
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg ha (norm_nonneg _))).mp
  rw [mul_pow]
  simp only [PiLp.norm_sq_eq_of_L2, Fintype.sum_sum_type,
    entryGenerator_inl, entryGenerator_inr, norm_mul, norm_star, mul_pow]
  have hn (e : n × n) : ‖H e.1 e.2‖ ^ 2 ≤ a ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (hH e.1 e.2) 2
  calc
    _ ≤ (∑ e : n × n, a ^ 2 * ‖v (.inr e)‖ ^ 2) +
        (∑ e : n × n, a ^ 2 * ‖v (.inl e)‖ ^ 2) :=
      add_le_add
        (Finset.sum_le_sum fun e _ => mul_le_mul_of_nonneg_right (hn e) (sq_nonneg _))
        (Finset.sum_le_sum fun e _ => mul_le_mul_of_nonneg_right (hn e) (sq_nonneg _))
    _ = _ := by rw [← Finset.mul_sum, ← Finset.mul_sum]; ring

/-- The normalization depends only on the public slot count. -/
def boundaryWeight (s : ℕ) : ℂ := ((Real.sqrt (2 * (s : ℝ)))⁻¹ : ℝ)

@[simp] theorem star_boundaryWeight (s : ℕ) : star (boundaryWeight s) = boundaryWeight s := by
  simp [boundaryWeight]

/-- The semilinear adjoint API uses the conjugation ring endomorphism. -/
@[simp] theorem conj_boundaryWeight (s : ℕ) :
    (starRingEnd ℂ) (boundaryWeight s) = boundaryWeight s := by
  simp only [boundaryWeight, Complex.conj_ofReal]

theorem boundaryWeight_sq (hs : 0 < s) :
    boundaryWeight s * boundaryWeight s * (2 * (s : ℂ)) = 1 := by
  have hs' : (2 * (s : ℝ)) ≠ 0 := by positivity
  have hh : (Real.sqrt (2 * (s : ℝ)))⁻¹ * (Real.sqrt (2 * (s : ℝ)))⁻¹ *
      (2 * (s : ℝ)) = 1 := by
    rw [← pow_two, inv_pow, Real.sq_sqrt (by positivity), inv_mul_cancel₀ hs']
  unfold boundaryWeight
  exact_mod_cast hh

theorem boundaryWeight_norm_sq (s : ℕ) :
    ‖boundaryWeight s‖ ^ 2 = (2 * (s : ℝ))⁻¹ := by
  simp only [boundaryWeight, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    inv_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 * (s : ℝ))]

/-- The boundary consists of uniform amplitudes on the two original slot lists. -/
def boundary (rowloc colloc : n → Fin s → n) :
    EuclideanSpace ℂ n →L[ℂ] OrientedSpace n :=
  boundaryWeight s • stack (rowIncidence rowloc) (columnIncidence colloc)

theorem boundary_isometry (hs : 0 < s) (rowloc colloc : n → Fin s → n)
    (hrow : ∀ i, Function.Injective (rowloc i))
    (hcol : ∀ j, Function.Injective (colloc j)) :
    (boundary rowloc colloc)† ∘L boundary rowloc colloc = 1 := by
  simp only [boundary, map_smulₛₗ, conj_boundaryWeight, smul_comp, comp_smul,
    smul_smul, stack_adjoint_stack, rowIncidence_gram rowloc hrow,
    columnIncidence_gram colloc hcol]
  rw [← add_smul, smul_smul]
  have hc : (boundaryWeight s * boundaryWeight s) * ((s : ℂ) + s) = 1 := by
    convert boundaryWeight_sq hs using 1; ring
  rw [hc, one_smul]

/-- This is the manuscript's actual `K₀`, for an already normalized matrix. -/
def generator (H : Matrix n n ℂ) (s : ℕ) : OrientedSpace n →L[ℂ] OrientedSpace n :=
  (Real.sqrt (s : ℝ) : ℂ) • entryGenerator H

omit [DecidableEq n] in
theorem generator_adjoint (H : Matrix n n ℂ) (s : ℕ) :
    (generator H s)† = generator H s := by
  simp only [generator, map_smulₛₗ, Complex.conj_ofReal, entryGenerator_adjoint]

omit [DecidableEq n] in
theorem generator_norm_le (H : Matrix n n ℂ) (s : ℕ)
    (hH : ∀ i j, ‖H i j‖ ≤ 1) : ‖generator H s‖ ≤ Real.sqrt (s : ℝ) := by
  rw [generator, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  exact (mul_le_mul_of_nonneg_left (entryGenerator_norm_le H 1 zero_le_one hH)
    (Real.sqrt_nonneg _)).trans_eq (mul_one _)

/-- The two sparse incidence responses are exactly the action of `K₀J`. -/
theorem generator_boundary (H : Matrix n n ℂ) (rowloc colloc : n → Fin s → n) :
    generator H s ∘L boundary rowloc colloc =
      ((Real.sqrt (s : ℝ) : ℂ) * boundaryWeight s) •
        stack (edgeDiagonal H ∘L columnIncidence colloc)
          ((edgeDiagonal H)† ∘L rowIncidence rowloc) := by
  simp only [generator, boundary, smul_comp, comp_smul, smul_smul, entryGenerator_stack]
  rw [mul_comm (boundaryWeight s) (Real.sqrt (s : ℝ) : ℂ)]

theorem generator_boundary_norm_sq (hs : 0 < s) (H : Matrix n n ℂ)
    (rowloc colloc : n → Fin s → n) (v : EuclideanSpace ℂ n) :
    ‖generator H s (boundary rowloc colloc v)‖ ^ 2 =
      (‖edgeDiagonal H (columnIncidence colloc v)‖ ^ 2 +
        ‖((edgeDiagonal H)†) (rowIncidence rowloc v)‖ ^ 2) / 2 := by
  have h := congrArg (fun T : EuclideanSpace ℂ n →L[ℂ] OrientedSpace n => T v)
    (generator_boundary H rowloc colloc)
  change generator H s (boundary rowloc colloc v) = _ at h
  rw [h, smul_apply, norm_smul, mul_pow, norm_mul, mul_pow,
    Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (Nat.cast_nonneg s),
    boundaryWeight_norm_sq, stack_norm_sq]
  simp only [comp_apply]
  have hs' : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  field_simp [hs']

/-- The reverse overlap is the adjoint Hamiltonian, without a padding symmetry premise. -/
theorem incidence_reverse_overlap (H : Matrix n n ℂ) (rowloc colloc : n → Fin s → n)
    (hrow : ∀ i j, H i j ≠ 0 → selected rowloc i j)
    (hcol : ∀ i j, H i j ≠ 0 → selected colloc j i) :
    (columnIncidence colloc)† ∘L (edgeDiagonal H)† ∘L rowIncidence rowloc =
      (SparseStateOverlap.matrixOperator H)† := by
  have h := congrArg (fun T : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n => T†)
    (incidence_overlap H rowloc colloc hrow hcol)
  simpa only [adjoint_comp, adjoint_adjoint, comp_assoc] using h

/-- Scalar cancellation for the physical normalization of the first moment. -/
theorem boundary_first_moment_factor (hs : 0 < s) :
    (boundaryWeight s * ((Real.sqrt (s : ℝ) : ℂ) * boundaryWeight s)) * 2 =
      (Real.sqrt (s : ℝ) : ℂ)⁻¹ := by
  have hsreal : (0 : ℝ) < s := by exact_mod_cast hs
  have hr : (Real.sqrt (s : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 hsreal).ne'
  have hsq : (Real.sqrt (s : ℝ) : ℂ) * (Real.sqrt (s : ℝ) : ℂ) = (s : ℂ) := by
    have hh : Real.sqrt (s : ℝ) * Real.sqrt (s : ℝ) = (s : ℝ) := by
      simpa only [pow_two] using Real.sq_sqrt hsreal.le
    exact_mod_cast hh
  rw [← one_div]
  apply (eq_div_iff hr).2
  calc
    _ = boundaryWeight s * boundaryWeight s *
        (2 * ((Real.sqrt (s : ℝ) : ℂ) * (Real.sqrt (s : ℝ) : ℂ))) := by ring
    _ = 1 := by rw [hsq]; exact boundaryWeight_sq hs

/-- The full first moment is the normalized input Hamiltonian. -/
theorem generator_compression (hs : 0 < s) (H : Matrix n n ℂ) (hH : H.IsHermitian)
    (rowloc colloc : n → Fin s → n)
    (hrow : ∀ i j, H i j ≠ 0 → selected rowloc i j)
    (hcol : ∀ i j, H i j ≠ 0 → selected colloc j i) :
    (boundary rowloc colloc)† ∘L generator H s ∘L boundary rowloc colloc =
      (Real.sqrt (s : ℝ) : ℂ)⁻¹ • SparseStateOverlap.matrixOperator H := by
  rw [generator_boundary]
  simp only [boundary, map_smulₛₗ, conj_boundaryWeight, smul_comp, comp_smul,
    smul_smul, stack_adjoint_stack]
  rw [incidence_overlap H rowloc colloc hrow hcol,
    incidence_reverse_overlap H rowloc colloc hrow hcol,
    SparseValuePrecision.matrixOperator_adjoint, hH.eq,
    ← two_smul ℂ (SparseStateOverlap.matrixOperator H), smul_smul]
  congr 1
  convert boundary_first_moment_factor hs using 1; ring

section NativeOriented
variable {X Z : Type*}

theorem native_generator_boundary_norm_le (D : NativeSparseBlockEncoding.Data X n Z s)
    (x : X)
    (hrow : ∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ 1)
    (hcol : ∀ j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ 1) :
    ‖generator (D.matrix x) s ∘L boundary (D.rowloc x) (D.colloc x)‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro v
  rw [one_mul]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  change ‖generator (D.matrix x) s (boundary (D.rowloc x) (D.colloc x) v)‖ ^ 2 ≤ _
  rw [generator_boundary_norm_sq D.slots_pos]
  have h := native_boundary_energy_le D x 1 (by simpa using hrow) (by simpa using hcol) v
  simpa only [one_pow, one_mul, add_comm] using h

/-- Concrete native sparse data, rather than abstract moment assumptions,
supplies the complete normalized first/second-moment certificate. -/
theorem native_moment_certificate (D : NativeSparseBlockEncoding.Data X n Z s)
    (x : X) (hH : (D.matrix x).IsHermitian)
    (hrow : ∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ 1)
    (hcol : ∀ j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ 1) :
    (boundary (D.rowloc x) (D.colloc x))† ∘L boundary (D.rowloc x) (D.colloc x) = 1 ∧
    (generator (D.matrix x) s)† = generator (D.matrix x) s ∧
    ‖generator (D.matrix x) s‖ ≤ Real.sqrt (s : ℝ) ∧
    ‖generator (D.matrix x) s ∘L boundary (D.rowloc x) (D.colloc x)‖ ≤ 1 ∧
    (boundary (D.rowloc x) (D.colloc x))† ∘L generator (D.matrix x) s ∘L
      boundary (D.rowloc x) (D.colloc x) =
        (Real.sqrt (s : ℝ) : ℂ)⁻¹ • SparseStateOverlap.matrixOperator (D.matrix x) := by
  have hentry (i j : n) : ‖D.matrix x i j‖ ≤ 1 :=
    SparseHamiltonian.norm_le_of_energy_le 1 (D.matrix x i) zero_le_one
      (by simpa only [one_pow] using hrow i) j
  exact ⟨boundary_isometry D.slots_pos _ _ (D.row_injective x) (D.column_injective x),
    generator_adjoint _ _, generator_norm_le _ _ hentry,
    native_generator_boundary_norm_le D x hrow hcol,
    generator_compression D.slots_pos _ hH _ _ (D.row_covers x) (D.column_covers x)⟩

end NativeOriented
end
end SparseHamiltonian.SparseEdgeMoments
