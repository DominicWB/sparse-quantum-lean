import SparseODE.ImprovedODESourceOutput

/-!
# Normalized moments for the two-tag sparse construction

The generator and boundary below are concrete operators on two orientations
of the tagged edge space. Their norm, compression and boundary moment follow
from the original locator promises and actual row/column energy bounds.
No oracle implementation or LCHS approximation is assumed or claimed here.

-/

namespace SparseHamiltonian.ODETaggedMoments

noncomputable section
open ContinuousLinearMap SparseSlotStates ODETaggedSupport
open scoped BigOperators InnerProduct ComplexConjugate
set_option maxHeartbeats 1000000

section Pair
variable {P E : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- False is the left frame, true is the right frame. -/
def pair (A B : P →L[ℂ] E) : P →L[ℂ] HermitianDilation.Double E :=
  WeightedClock.boundary (fun _ : Bool => (1 : ℝ)) (fun b => if b then B else A)

omit [CompleteSpace P] [CompleteSpace E] in
@[simp] theorem pair_false (A B : P →L[ℂ] E) (v : P) : pair A B v false = A v := by
  simp [pair, WeightedClock.boundary_apply]

omit [CompleteSpace P] [CompleteSpace E] in
@[simp] theorem pair_true (A B : P →L[ℂ] E) (v : P) : pair A B v true = B v := by
  simp [pair, WeightedClock.boundary_apply]

omit [CompleteSpace P] [CompleteSpace E] in
theorem pair_norm_sq (A B : P →L[ℂ] E) (v : P) :
    ‖pair A B v‖ ^ 2 = ‖A v‖ ^ 2 + ‖B v‖ ^ 2 := by
  simp [PiLp.norm_sq_eq_of_L2, add_comm]

omit [CompleteSpace P] [CompleteSpace E] in
theorem pair_inner (A B C D : P →L[ℂ] E) (u v : P) :
    inner ℂ (pair A B u) (pair C D v) =
      inner ℂ (A u) (C v) + inner ℂ (B u) (D v) := by
  simp [PiLp.inner_apply, add_comm]

theorem pair_adjoint_pair (A B C D : P →L[ℂ] E) :
    (pair A B)† ∘L pair C D = A† ∘L C + B† ∘L D := by
  apply ContinuousLinearMap.ext
  intro v
  apply ext_inner_left ℂ
  intro u
  simp only [comp_apply, adjoint_inner_right, add_apply, inner_add_right, pair_inner]

omit [CompleteSpace P] in
/-- The doubled operator exchanges the two boundary responses. -/
theorem dilation_pair (U : E →L[ℂ] E) (A B : P →L[ℂ] E) :
    HermitianDilation.dilation U ∘L pair A B =
      pair (U ∘L B) (U† ∘L A) := by
  apply ContinuousLinearMap.ext
  intro v
  apply PiLp.ext
  intro b
  cases b <;> simp only [comp_apply, pair_false, pair_true,
    HermitianDilation.dilation_apply_false, HermitianDilation.dilation_apply_true]

/-- This estimate controls the entire doubled Hilbert space. -/
theorem dilation_norm_le (U : E →L[ℂ] E) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hU : ‖U‖ ≤ ρ) : ‖HermitianDilation.dilation U‖ ≤ ρ := by
  have hDiag : ‖WeightedClock.diagonal (fun b : Bool => if b then U† else U)‖ ≤ ρ := by
    apply WeightedClock.norm_diagonal_le _ ρ hρ
    intro b
    cases b
    · exact hU
    · change ‖U†‖ ≤ ρ
      simpa only [adjoint.norm_map] using hU
  have hSwap : ‖(HermitianDilation.swap : HermitianDilation.Double E →L[ℂ]
      HermitianDilation.Double E)‖ ≤ 1 :=
    OracleCircuit.IsUnitary.norm_le_one HermitianDilation.swap_unitary
  calc
    ‖HermitianDilation.dilation U‖ ≤
        ‖WeightedClock.diagonal (fun b : Bool => if b then U† else U)‖ *
          ‖(HermitianDilation.swap : HermitianDilation.Double E →L[ℂ]
            HermitianDilation.Double E)‖ := opNorm_comp_le _ _
    _ ≤ ρ * 1 := mul_le_mul hDiag hSwap
      (norm_nonneg (HermitianDilation.swap : HermitianDilation.Double E →L[ℂ]
        HermitianDilation.Double E)) hρ
    _ = ρ := mul_one _

end Pair

variable {n : Type*} [Fintype n] [DecidableEq n] {s : ℕ}

/-- The outer Boolean coordinate is the generator orientation, not its tag. -/
abbrev PrivateSpace (n : Type*) [Fintype n] :=
  HermitianDilation.Double (ODETaggedSupport.TaggedSpace n)

/-- Uniform normalization of all four original list sectors. -/
def boundary (rowloc colloc : n → Fin s → n) :
    EuclideanSpace ℂ n →L[ℂ] PrivateSpace n :=
  SparseEdgeMoments.boundaryWeight (2 * s) •
    pair (leftFrame rowloc colloc) (rightFrame rowloc colloc)

/-- The tagged Hermitian generator with the common public energy scale. -/
def generator (M K : Matrix n n ℂ) (s : ℕ) (ρ : ℝ) :
    PrivateSpace n →L[ℂ] PrivateSpace n :=
  ((Real.sqrt (2 * (s : ℝ)) / ρ : ℝ) : ℂ) •
    HermitianDilation.dilation (diagonal M K)

theorem boundary_isometry (hs : 0 < s) (rowloc colloc : n → Fin s → n)
    (hrow : ∀ i, Function.Injective (rowloc i))
    (hcol : ∀ j, Function.Injective (colloc j)) :
    (boundary rowloc colloc)† ∘L boundary rowloc colloc = 1 := by
  simp only [boundary, map_smulₛₗ, SparseEdgeMoments.conj_boundaryWeight,
    smul_comp, comp_smul, smul_smul, pair_adjoint_pair,
    leftFrame_gram rowloc colloc hrow hcol, rightFrame_gram rowloc colloc hrow hcol]
  rw [← add_smul, smul_smul]
  have hc : (SparseEdgeMoments.boundaryWeight (2 * s) *
      SparseEdgeMoments.boundaryWeight (2 * s)) *
      (2 * (s : ℂ) + 2 * (s : ℂ)) = 1 := by
    convert SparseEdgeMoments.boundaryWeight_sq
      (Nat.mul_pos (show 0 < (2 : ℕ) by decide) hs) using 1
    push_cast
    ring
  rw [hc, one_smul]

omit [DecidableEq n] in
theorem generator_adjoint (M K : Matrix n n ℂ) (s : ℕ) (ρ : ℝ) :
    (generator M K s ρ)† = generator M K s ρ := by
  simp only [generator, map_smulₛₗ, Complex.conj_ofReal,
    HermitianDilation.dilation_selfAdjoint]

omit [DecidableEq n] in
/-- The full-space norm grows with the square root of the number of slots. -/
theorem generator_norm_le (M K : Matrix n n ℂ) (s : ℕ) (ρ : ℝ) (hρ : 0 < ρ)
    (hK : ∀ i j, ‖K i j‖ ≤ ρ) :
    ‖generator M K s ρ‖ ≤ Real.sqrt (2 * (s : ℝ)) := by
  rw [generator, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (Real.sqrt_nonneg _) hρ.le)]
  calc
    _ ≤ (Real.sqrt (2 * (s : ℝ)) / ρ) * ρ :=
      mul_le_mul_of_nonneg_left
        (dilation_norm_le _ ρ hρ.le (diagonal_norm_le M K ρ hρ.le hK))
        (div_nonneg (Real.sqrt_nonneg _) hρ.le)
    _ = _ := div_mul_cancel₀ _ hρ.ne'

/-- The reverse tagged overlap follows by taking an adjoint. -/
theorem frame_reverse_overlap (M K : Matrix n n ℂ) (rowloc colloc : n → Fin s → n)
    (hrow : ∀ i j, M i j ≠ 0 → selected rowloc i j)
    (hcol : ∀ i j, M i j ≠ 0 → selected colloc j i)
    (hK : ∀ i j, M i j = 0 → M j i = 0 → K i j = 0) :
    (rightFrame rowloc colloc)† ∘L (diagonal M K)† ∘L leftFrame rowloc colloc =
      (SparseStateOverlap.matrixOperator K)† := by
  have h := congrArg (fun A : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n => A†)
    (frame_overlap M K rowloc colloc hrow hcol hK)
  simpa only [adjoint_comp, adjoint_adjoint, comp_assoc] using h

/-- Concrete formula for the generator applied to the normalized boundary. -/
theorem generator_boundary (M K : Matrix n n ℂ) (ρ : ℝ)
    (rowloc colloc : n → Fin s → n) :
    generator M K s ρ ∘L boundary rowloc colloc =
      (((Real.sqrt (2 * (s : ℝ)) / ρ : ℝ) : ℂ) *
          SparseEdgeMoments.boundaryWeight (2 * s)) •
        pair (diagonal M K ∘L rightFrame rowloc colloc)
          ((diagonal M K)† ∘L leftFrame rowloc colloc) := by
  simp only [generator, boundary, smul_comp, comp_smul, smul_smul, dilation_pair]
  rw [mul_comm (SparseEdgeMoments.boundaryWeight (2 * s))]

theorem first_moment_factor (hs : 0 < s) (ρ : ℝ) :
    (SparseEdgeMoments.boundaryWeight (2 * s) *
      (((Real.sqrt (2 * (s : ℝ)) / ρ : ℝ) : ℂ) *
        SparseEdgeMoments.boundaryWeight (2 * s))) * 2 =
      ((ρ : ℂ) * (Real.sqrt (2 * (s : ℝ)) : ℂ))⁻¹ := by
  have h := SparseEdgeMoments.boundary_first_moment_factor
    (Nat.mul_pos (show 0 < (2 : ℕ) by decide) hs)
  simp only [Nat.cast_mul, Nat.cast_ofNat] at h
  rw [Complex.ofReal_div]
  calc
    _ = ((SparseEdgeMoments.boundaryWeight (2 * s) *
        ((Real.sqrt (2 * (s : ℝ)) : ℂ) *
          SparseEdgeMoments.boundaryWeight (2 * s))) * 2) * (ρ : ℂ)⁻¹ := by ring
    _ = _ := by rw [h, mul_inv_rev]

/-- The first moment is the desired Hermitian branch, with its exact scale. -/
theorem generator_compression (hs : 0 < s) (M K : Matrix n n ℂ)
    (hHerm : K.IsHermitian) (ρ : ℝ) (rowloc colloc : n → Fin s → n)
    (hrow : ∀ i j, M i j ≠ 0 → selected rowloc i j)
    (hcol : ∀ i j, M i j ≠ 0 → selected colloc j i)
    (hK : ∀ i j, M i j = 0 → M j i = 0 → K i j = 0) :
    (boundary rowloc colloc)† ∘L generator M K s ρ ∘L boundary rowloc colloc =
      ((ρ : ℂ) * (Real.sqrt (2 * (s : ℝ)) : ℂ))⁻¹ •
        SparseStateOverlap.matrixOperator K := by
  rw [generator_boundary]
  simp only [boundary, map_smulₛₗ, SparseEdgeMoments.conj_boundaryWeight,
    smul_comp, comp_smul, smul_smul, pair_adjoint_pair]
  rw [frame_overlap M K rowloc colloc hrow hcol hK,
    frame_reverse_overlap M K rowloc colloc hrow hcol hK,
    SparseValuePrecision.matrixOperator_adjoint, hHerm.eq,
    ← two_smul ℂ (SparseStateOverlap.matrixOperator K), smul_smul]
  congr 1
  convert first_moment_factor hs ρ using 1; ring

/-- The response norm averages the two original energy contributions. -/
theorem generator_boundary_norm_sq (hs : 0 < s) (M K : Matrix n n ℂ)
    (ρ : ℝ) (hρ : 0 < ρ) (rowloc colloc : n → Fin s → n)
    (v : EuclideanSpace ℂ n) :
    ‖generator M K s ρ (boundary rowloc colloc v)‖ ^ 2 =
      (‖diagonal M K (rightFrame rowloc colloc v)‖ ^ 2 +
        ‖((diagonal M K)†) (leftFrame rowloc colloc v)‖ ^ 2) / (2 * ρ ^ 2) := by
  have h := congrArg (fun A : EuclideanSpace ℂ n →L[ℂ] PrivateSpace n => A v)
    (generator_boundary M K ρ rowloc colloc)
  change generator M K s ρ (boundary rowloc colloc v) = _ at h
  rw [h, smul_apply, norm_smul, mul_pow, norm_mul, mul_pow,
    Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow,
    Real.sq_sqrt (by positivity : 0 ≤ 2 * (s : ℝ)),
    SparseEdgeMoments.boundaryWeight_norm_sq, pair_norm_sq]
  simp only [comp_apply, Nat.cast_mul, Nat.cast_ofNat]
  have hs' : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  field_simp [hs', hρ.ne']

/-- Only the original row/column energies enter the boundary moment. -/
theorem generator_boundary_norm_le (hs : 0 < s) (M K : Matrix n n ℂ)
    (ρ : ℝ) (hρ : 0 < ρ) (rowloc colloc : n → Fin s → n)
    (hrow : ∀ i j, M i j ≠ 0 → selected rowloc i j)
    (hcol : ∀ i j, M i j ≠ 0 → selected colloc j i)
    (hr : ∀ i, ∑ j, ‖K i j‖ ^ 2 ≤ ρ ^ 2)
    (hc : ∀ j, ∑ i, ‖K i j‖ ^ 2 ≤ ρ ^ 2) :
    ‖generator M K s ρ ∘L boundary rowloc colloc‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro v
  rw [one_mul]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  change ‖generator M K s ρ (boundary rowloc colloc v)‖ ^ 2 ≤ _
  rw [generator_boundary_norm_sq hs M K ρ hρ rowloc colloc v]
  apply (div_le_iff₀ (by positivity : 0 < 2 * ρ ^ 2)).2
  have hl := left_boundary_energy_le M K rowloc colloc hrow hcol ρ hr v
  have hr' := right_boundary_energy_le M K rowloc colloc hrow hcol ρ hc v
  nlinarith

section Native
variable {X Z : Type*}

/-- Complete normalized moment certificate for an actual original sparse oracle.
It imposes no support-union locator and no symmetry on independently padded lists. -/
theorem native_moment_certificate (D : NativeSparseBlockEncoding.Data X n Z s)
    (x : X) (K : Matrix n n ℂ) (hHerm : K.IsHermitian) (ρ : ℝ) (hρ : 0 < ρ)
    (hK : ∀ i j, D.matrix x i j = 0 → D.matrix x j i = 0 → K i j = 0)
    (hr : ∀ i, ∑ j, ‖K i j‖ ^ 2 ≤ ρ ^ 2)
    (hc : ∀ j, ∑ i, ‖K i j‖ ^ 2 ≤ ρ ^ 2) :
    (boundary (D.rowloc x) (D.colloc x))† ∘L boundary (D.rowloc x) (D.colloc x) = 1 ∧
    (generator (D.matrix x) K s ρ)† = generator (D.matrix x) K s ρ ∧
    ‖generator (D.matrix x) K s ρ‖ ≤ Real.sqrt (2 * (s : ℝ)) ∧
    ‖generator (D.matrix x) K s ρ ∘L boundary (D.rowloc x) (D.colloc x)‖ ≤ 1 ∧
    (boundary (D.rowloc x) (D.colloc x))† ∘L generator (D.matrix x) K s ρ ∘L
      boundary (D.rowloc x) (D.colloc x) =
        ((ρ : ℂ) * (Real.sqrt (2 * (s : ℝ)) : ℂ))⁻¹ •
          SparseStateOverlap.matrixOperator K := by
  have hentry (i j : n) : ‖K i j‖ ≤ ρ :=
    norm_le_of_energy_le ρ (K i) hρ.le (hr i) j
  exact ⟨boundary_isometry D.slots_pos _ _ (D.row_injective x) (D.column_injective x),
    generator_adjoint _ _ _ _, generator_norm_le _ _ _ _ hρ hentry,
    generator_boundary_norm_le D.slots_pos _ _ ρ hρ _ _
      (D.row_covers x) (D.column_covers x) hr hc,
    generator_compression D.slots_pos _ _ hHerm ρ _ _
      (D.row_covers x) (D.column_covers x) hK⟩

/-- Every LCHS node has these moments under the same public cutoff and scale.
Hermiticity and support containment are proved from the original matrix entries. -/
theorem native_lchs_moment_certificate (D : NativeSparseBlockEncoding.Data X n Z s)
    (x : X) (etaH etaD k R : ℝ) (hH : 0 ≤ etaH) (hD : 0 ≤ etaD)
    (hk : |k| ≤ R) (hρ : 0 < etaH + R * etaD)
    (hRowH : ∀ i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ etaH ^ 2)
    (hColH : ∀ j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ etaH ^ 2)
    (hRowD : ∀ i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ etaD ^ 2)
    (hColD : ∀ j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ etaD ^ 2) :
    let K := ODEMatrixEnergy.lchsHamiltonian (D.matrix x) k
    let ρ := etaH + R * etaD
    (boundary (D.rowloc x) (D.colloc x))† ∘L boundary (D.rowloc x) (D.colloc x) = 1 ∧
    (generator (D.matrix x) K s ρ)† = generator (D.matrix x) K s ρ ∧
    ‖generator (D.matrix x) K s ρ‖ ≤ Real.sqrt (2 * (s : ℝ)) ∧
    ‖generator (D.matrix x) K s ρ ∘L boundary (D.rowloc x) (D.colloc x)‖ ≤ 1 ∧
    (boundary (D.rowloc x) (D.colloc x))† ∘L generator (D.matrix x) K s ρ ∘L
      boundary (D.rowloc x) (D.colloc x) =
        ((ρ : ℂ) * (Real.sqrt (2 * (s : ℝ)) : ℂ))⁻¹ •
          SparseStateOverlap.matrixOperator K := by
  have hEnergy := ODEMatrixEnergy.lchs_energies_le_radius (D.matrix x)
    etaH etaD k R hH hD hk hRowH hColH hRowD hColD
  exact native_moment_certificate D x (ODEMatrixEnergy.lchsHamiltonian (D.matrix x) k)
    (ODEMatrixEnergy.lchsHamiltonian_isHermitian (D.matrix x) k) (etaH + R * etaD) hρ
    (fun i j hij hji => ODEMatrixEnergy.lchsHamiltonian_eq_zero (D.matrix x) k i j hij hji)
    hEnergy.1 hEnergy.2

end Native
end
end SparseHamiltonian.ODETaggedMoments
