import SparseHamiltonian.SparseMatrixNorm

/-!
# Hermitian involution dilation without loss of block-encoding precision

On a Boolean Hilbert register, `dilation U` has blocks `[[0,U],[U†,0]]`.
A unitary `U` gives an exact Hermitian involution on the entire doubled space.
Preparing the Boolean register in its fixed plus state compresses this dilation
to the Hermitian part of `U`; taking this Hermitian part does not increase
operator-norm error relative to a self-adjoint target.
-/

namespace SparseHamiltonian.HermitianDilation

noncomputable section
open ContinuousLinearMap OracleCircuit
open scoped InnerProduct
set_option maxHeartbeats 1000000

/-- One Boolean control register, equipped with its Hilbert direct-sum norm. -/
abbrev Double (K : Type*) := PiLp 2 (fun _ : Bool => K)

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Fixed exchange of the two Boolean control states. -/
def swap : Double K →L[ℂ] Double K :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ K (Equiv.swap false true)).toContinuousLinearEquiv.toContinuousLinearMap

omit [CompleteSpace K] in
@[simp] theorem swap_apply (x : Double K) (b : Bool) : swap x b = x (!b) := by
  cases b <;> simp [swap, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft']

/-- The fixed Boolean exchange is self-adjoint. -/
theorem swap_selfAdjoint : (swap : Double K →L[ℂ] Double K)† = swap := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℂ
  intro y
  rw [adjoint_inner_left]
  simp only [PiLp.inner_apply, Fintype.sum_bool, swap_apply, Bool.not_true, Bool.not_false]
  exact add_comm _ _

/-- The fixed Boolean exchange is a legal unitary gate. -/
theorem swap_unitary : IsUnitary (swap : Double K →L[ℂ] Double K) := by
  have hsq : (swap : Double K →L[ℂ] Double K) ∘L swap = 1 := by
    ext x b
    simp
  change (swap : Double K →L[ℂ] Double K)† ∘L swap = 1 ∧
    (swap : Double K →L[ℂ] Double K) ∘L swap† = 1
  rw [swap_selfAdjoint]
  exact ⟨hsq, hsq⟩

/-- The full-space Hermitian dilation, with `U` in the upper-right block. -/
def dilation (U : K →L[ℂ] K) : Double K →L[ℂ] Double K :=
  WeightedClock.diagonal (fun b : Bool => if b then U† else U) ∘L swap

@[simp] theorem dilation_apply_false (U : K →L[ℂ] K) (x : Double K) :
    dilation U x false = U (x true) := by simp [dilation]

@[simp] theorem dilation_apply_true (U : K →L[ℂ] K) (x : Double K) :
    dilation U x true = (U†) (x false) := by simp [dilation]

/-- The dilation is self-adjoint even when the original operator is not unitary. -/
theorem dilation_selfAdjoint (U : K →L[ℂ] K) : (dilation U)† = dilation U := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℂ
  intro y
  rw [adjoint_inner_left]
  simp only [PiLp.inner_apply, Fintype.sum_bool, dilation_apply_true, dilation_apply_false,
    adjoint_inner_left, adjoint_inner_right]
  exact add_comm _ _

/-- Unitarity of `U` gives an exact involution on every doubled-space vector. -/
theorem dilation_involution (U : K →L[ℂ] K) (hU : IsUnitary U) (x : Double K) :
    dilation U (dilation U x) = x := by
  apply PiLp.ext
  intro b
  cases b
  · simpa only [dilation_apply_false, dilation_apply_true, mul_apply_eq_comp,
      ContinuousLinearMap.star_eq_adjoint, one_def, id_apply] using
      congrArg (fun A : K →L[ℂ] K => A (x false)) hU.2
  · simpa only [dilation_apply_false, dilation_apply_true, mul_apply_eq_comp,
      ContinuousLinearMap.star_eq_adjoint, one_def, id_apply] using
      congrArg (fun A : K →L[ℂ] K => A (x true)) hU.1

/-- The operator-square form of the full-space involution. -/
theorem dilation_sq (U : K →L[ℂ] K) (hU : IsUnitary U) :
    dilation U ∘L dilation U = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  exact dilation_involution U hU x

/-- Both unitary identities follow from the exact involution and self-adjointness. -/
theorem dilation_unitary (U : K →L[ℂ] K) (hU : IsUnitary U) : IsUnitary (dilation U) := by
  change (dilation U)† ∘L dilation U = 1 ∧ dilation U ∘L (dilation U)† = 1
  rw [dilation_selfAdjoint]
  exact ⟨dilation_sq U hU, dilation_sq U hU⟩

/-- Fixed plus-state preparation on the Boolean control register. -/
def plus : K →L[ℂ] Double K :=
  WeightedClock.boundary (fun _ : Bool => (1 / 2 : ℝ)) (fun _ => 1)

omit [CompleteSpace K] in
@[simp] theorem plus_apply (x : K) (b : Bool) :
    plus x b = (Real.sqrt (1 / 2) : ℂ) • x := rfl

/-- Plus-state preparation is an isometry on the entire public space. -/
theorem plus_isometry : (plus : K →L[ℂ] Double K)† ∘L plus = 1 := by
  apply WeightedClock.boundary_isometry
  · intro b; norm_num
  · norm_num [Fintype.sum_bool]
  · intro b; simp only [one_def, adjoint_id, id_comp]

/-- Plus-state preparation as a genuine fixed linear isometry. -/
def plusIsometry : K →ₗᵢ[ℂ] Double K where
  toLinearMap := (plus : K →L[ℂ] Double K).toLinearMap
  norm_map' := (plus : K →L[ℂ] Double K).norm_map_iff_adjoint_comp_self.mpr plus_isometry

omit [CompleteSpace K] in
/-- The Boolean swap fixes the plus-prepared subspace exactly. -/
theorem swap_plus : (swap : Double K →L[ℂ] Double K) ∘L plus = plus := by
  ext x b
  simp

/-- The Hermitian part is normalized by one half. -/
def hermitianPart (A : K →L[ℂ] K) : K →L[ℂ] K := (2 : ℂ)⁻¹ • (A + A†)

/-- Compressing the exact Hermitian dilation gives the Hermitian part of `U`. -/
theorem plus_compression (U : K →L[ℂ] K) :
    (plus : K →L[ℂ] Double K)† ∘L dilation U ∘L plus = hermitianPart U := by
  rw [dilation, comp_assoc, swap_plus]
  have h := WeightedClock.boundary_compression (fun _ : Bool => (1 / 2 : ℝ))
    (fun _ => by norm_num) (fun b : Bool => if b then U† else U) (fun _ => (1 : K →L[ℂ] K))
  simpa [plus, hermitianPart, Fintype.sum_bool, add_comm, smul_add, one_def, id_comp, comp_id] using h

/-- Taking the Hermitian part does not amplify error against a self-adjoint target. -/
theorem hermitianPart_error (A H : K →L[ℂ] K) (hH : H† = H) :
    ‖hermitianPart A - H‖ ≤ ‖A - H‖ := by
  have hDiff : hermitianPart A - H = (2 : ℂ)⁻¹ • ((A - H) + (A - H)†) := by
    simp only [hermitianPart, map_sub, hH]
    module
  rw [hDiff, norm_smul]
  have hScalar : ‖(2 : ℂ)⁻¹‖ = (1 / 2 : ℝ) := by norm_num
  rw [hScalar]
  calc
    (1 / 2 : ℝ) * ‖(A - H) + (A - H)†‖ ≤
        (1 / 2 : ℝ) * (‖A - H‖ + ‖(A - H)†‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
    _ = ‖A - H‖ := by rw [adjoint.norm_map]; ring

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-- The fixed encoding into the doubled workspace. -/
def encodedPlus (E : P →L[ℂ] K) : P →L[ℂ] Double K := plus ∘L E

/-- Isometric public encodings remain isometric after adding the plus register. -/
theorem encodedPlus_isometry (E : P →L[ℂ] K) (hE : E† ∘L E = 1) :
    (encodedPlus E)† ∘L encodedPlus E = 1 := by
  apply norm_map_iff_adjoint_comp_self _ |>.mp
  intro v
  rw [encodedPlus, comp_apply,
    (plus : K →L[ℂ] Double K).norm_map_iff_adjoint_comp_self.mpr plus_isometry,
    E.norm_map_iff_adjoint_comp_self.mpr hE]

/-- Proper public subspaces compress to the Hermitian part of their original block. -/
theorem encodedPlus_compression (U : K →L[ℂ] K) (E : P →L[ℂ] K) :
    (encodedPlus E)† ∘L dilation U ∘L encodedPlus E =
      hermitianPart (E† ∘L U ∘L E) := by
  have hAssoc : (encodedPlus E)† ∘L dilation U ∘L encodedPlus E =
      E† ∘L (plus† ∘L dilation U ∘L plus) ∘L E := by
    simp only [encodedPlus, adjoint_comp, comp_assoc]
  rw [hAssoc, plus_compression]
  simp only [hermitianPart, smul_comp, comp_smul, add_comp, comp_add,
    adjoint_comp, adjoint_adjoint, comp_assoc]

/-- A block encoding close to a Hermitian target gives an equally accurate
compression of an exact full-space Hermitian involution. -/
theorem encodedPlus_error (U : K →L[ℂ] K) (E : P →L[ℂ] K)
    (H : P →L[ℂ] P) (hH : H† = H) (δ : ℝ)
    (hError : ‖E† ∘L U ∘L E - H‖ ≤ δ) :
    ‖(encodedPlus E)† ∘L dilation U ∘L encodedPlus E - H‖ ≤ δ := by
  rw [encodedPlus_compression]
  exact (hermitianPart_error _ H hH).trans hError

end
end SparseHamiltonian.HermitianDilation
