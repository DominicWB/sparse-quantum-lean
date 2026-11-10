import SignedFactorSimulation.Core
import SparseHamiltonian.HermitianDilation

/-!
# Attenuating the factor

"If `T < M`, use a known ancillary rotation to attenuate the supplied factor": with a flag
qubit, the known input `E' = (√κ |0⟩ + √(1-κ) |1⟩) ⊗ E`, the success projection
`Π' = |0⟩⟨0| ⊗ Π` and the reflection `Z' = I ⊗ Z`, the factor unitary `I ⊗ U` has the factor
`B' = |0⟩ ⊗ √κ B` (`atten_factor`), hence

  `C' = κ C`,  `D' = κ D`  (`atten_Cop`, `atten_Dop`).

The attenuated factor query `I ⊗ U` is one query of `U`: it acts as `U` on both copies of `W`.
After flattening, a factor query on `ℂ^ι ⊗ (ℂ² ⊗ W)` is the factor query on `ℂ^{ι × 2} ⊗ W`
(`flat2_dbl`).
-/

set_option autoImplicit false

namespace SignedFactorSimulation

noncomputable section

open Complex ContinuousLinearMap SparseHamiltonian SparseHamiltonian.OracleCircuit
open scoped InnerProduct InnerProductSpace ComplexOrder

variable {P W : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]

/-- A flag qubit and `W`. -/
abbrev Flagged (W : Type*) [NormedAddCommGroup W] [InnerProductSpace ℂ W] :=
  HermitianDilation.Double W

/-- `I ⊗ A` on the flag and `W`. -/
def dbl (A : W →L[ℂ] W) : Flagged W →L[ℂ] Flagged W :=
  WeightedClock.diagonal (fun _ : Bool => A)

/-- The flag weights `(κ, 1 - κ)` of the states `|0⟩`, `|1⟩`. -/
def flagWeight (κ : ℝ) (b : Bool) : ℝ := if b then 1 - κ else κ

/-- The attenuated input `(√κ |0⟩ + √(1-κ) |1⟩) ⊗ E`. -/
def flagIn (κ : ℝ) (E : P →L[ℂ] W) : P →L[ℂ] Flagged W :=
  WeightedClock.boundary (flagWeight κ) (fun _ => E)

/-- The inclusion `|0⟩ ⊗ ·`. -/
def flagIncl : W →L[ℂ] Flagged W :=
  WeightedClock.boundary (fun b : Bool => if b then 0 else 1) (fun _ => 1)

/-- The success projection `|0⟩⟨0| ⊗ Π`. -/
def flagProj (Pi : W →L[ℂ] W) : Flagged W →L[ℂ] Flagged W :=
  WeightedClock.diagonal (fun b : Bool => if b then 0 else Pi)

omit [CompleteSpace W] in
theorem dbl_comp (A B : W →L[ℂ] W) : dbl A ∘L dbl B = dbl (A ∘L B) :=
  WeightedClock.diagonal_comp _ _

theorem dbl_adjoint (A : W →L[ℂ] W) : (dbl A)† = dbl (A†) :=
  WeightedClock.diagonal_adjoint _

omit [CompleteSpace W] in
theorem dbl_one : dbl (1 : W →L[ℂ] W) = 1 := WeightedClock.diagonal_one

theorem dbl_unitary {A : W →L[ℂ] W} (hA : IsUnitary A) : IsUnitary (dbl A) := by
  have h1 : A† ∘L A = 1 := hA.1
  have h2 : A ∘L A† = 1 := hA.2
  constructor
  · change (dbl A)† ∘L dbl A = 1
    rw [dbl_adjoint, dbl_comp, h1, dbl_one]
  · change dbl A ∘L (dbl A)† = 1
    rw [dbl_adjoint, dbl_comp, h2, dbl_one]

theorem flagIn_isometry {κ : ℝ} (h0 : 0 ≤ κ) (h1 : κ ≤ 1) {E : P →L[ℂ] W} (hE : E† ∘L E = 1) :
    (flagIn κ E)† ∘L flagIn κ E = 1 := by
  apply WeightedClock.boundary_isometry
  · intro b; cases b <;> simp [flagWeight] <;> linarith
  · simp [flagWeight]
  · intro _; exact hE

theorem flagIncl_adjoint_apply (y : Flagged W) :
    ((flagIncl : W →L[ℂ] Flagged W)†) y = y false := by
  rw [flagIncl, WeightedClock.boundary_adjoint_apply, Fintype.sum_bool]
  simp

theorem flagProj_adjoint {Pi : W →L[ℂ] W} (h : Pi† = Pi) : (flagProj Pi)† = flagProj Pi := by
  rw [flagProj, WeightedClock.diagonal_adjoint]
  congr 1
  funext b
  cases b <;> simp [h]

omit [CompleteSpace W] in
theorem flagProj_idem {Pi : W →L[ℂ] W} (h : Pi * Pi = Pi) :
    flagProj Pi * flagProj Pi = flagProj Pi := by
  change flagProj Pi ∘L flagProj Pi = flagProj Pi
  rw [flagProj, WeightedClock.diagonal_comp]
  congr 1
  funext b
  cases b
  · exact h
  · simp

/-- **The attenuated factor interface**: `E' = (√κ|0⟩ + √(1-κ)|1⟩) ⊗ E`, `Π' = |0⟩⟨0| ⊗ Π`,
`Z' = I ⊗ Z`. -/
def Known.atten (K : Known P W) {κ : ℝ} (h0 : 0 ≤ κ) (h1 : κ ≤ 1) : Known P (Flagged W) where
  E := flagIn κ K.E
  proj := flagProj K.proj
  Z := dbl K.Z
  E_isometry := flagIn_isometry h0 h1 K.E_isometry
  proj_adjoint := flagProj_adjoint K.proj_adjoint
  proj_idem := flagProj_idem K.proj_idem
  Z_adjoint := by rw [dbl_adjoint, K.Z_adjoint]
  Z_sq := by
    change dbl K.Z ∘L dbl K.Z = 1
    rw [dbl_comp]
    have h : K.Z ∘L K.Z = 1 := K.Z_sq
    rw [h, dbl_one]
  Z_comm := by
    change dbl K.Z ∘L flagProj K.proj = flagProj K.proj ∘L dbl K.Z
    rw [dbl, flagProj, WeightedClock.diagonal_comp, WeightedClock.diagonal_comp]
    congr 1
    funext b
    cases b
    · exact K.Z_comm
    · simp

/-- The attenuated factor is `|0⟩ ⊗ √κ B`. -/
theorem Known.atten_factor (K : Known P W) {κ : ℝ} (h0 : 0 ≤ κ) (h1 : κ ≤ 1) (U : W →L[ℂ] W) :
    (K.atten h0 h1).factor (dbl U) = flagIncl ∘L ((Real.sqrt κ : ℂ) • K.factor U) := by
  ext p b
  cases b
  · simp [Known.factor, Known.atten, flagProj, dbl, flagIn, flagIncl, flagWeight]
  · simp [Known.factor, Known.atten, flagProj, dbl, flagIn, flagIncl, flagWeight]

theorem flagIncl_conj (A : W →L[ℂ] W) :
    (flagIncl : W →L[ℂ] Flagged W)† ∘L dbl A ∘L flagIncl = A := by
  ext w
  simp only [comp_apply, flagIncl_adjoint_apply, dbl]
  simp [flagIncl]

theorem flagIncl_isometry : (flagIncl : W →L[ℂ] Flagged W)† ∘L flagIncl = 1 := by
  have h := flagIncl_conj (W := W) 1
  rwa [dbl_one, one_comp'] at h

theorem sqrt_sq_complex {κ : ℝ} (h0 : 0 ≤ κ) :
    (Real.sqrt κ : ℂ) * (starRingEnd ℂ) (Real.sqrt κ : ℂ) = (κ : ℂ) := by
  rw [Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt h0]

theorem flagIncl_conj_right {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℂ Q]
    [CompleteSpace Q] (A : W →L[ℂ] W) (X : Q →L[ℂ] W) :
    (flagIncl : W →L[ℂ] Flagged W)† ∘L (dbl A ∘L (flagIncl ∘L X)) = A ∘L X := by
  rw [← comp_assoc, ← comp_assoc, comp_assoc _ _ flagIncl, flagIncl_conj]

/-- `C' = κ C`. -/
theorem Known.atten_Cop (K : Known P W) {κ : ℝ} (h0 : 0 ≤ κ) (h1 : κ ≤ 1) (U : W →L[ℂ] W) :
    (K.atten h0 h1).Cop (dbl U) = (κ : ℂ) • K.Cop U := by
  rw [Known.Cop, K.atten_factor h0 h1, Known.Cop]
  change ((flagIncl ∘L ((Real.sqrt κ : ℂ) • K.factor U))†) ∘L dbl K.Z ∘L
    (flagIncl ∘L ((Real.sqrt κ : ℂ) • K.factor U)) = _
  simp only [adjoint_comp, map_smulₛₗ, smul_comp, comp_smul, smul_smul, comp_assoc,
    flagIncl_conj_right, sqrt_sq_complex h0]

/-- `D' = κ D`. -/
theorem Known.atten_Dop (K : Known P W) {κ : ℝ} (h0 : 0 ≤ κ) (h1 : κ ≤ 1) (U : W →L[ℂ] W) :
    (K.atten h0 h1).Dop (dbl U) = (κ : ℂ) • K.Dop U := by
  rw [Known.Dop, K.atten_factor h0 h1, Known.Dop]
  have h := flagIncl_conj_right (W := W) 1 (K.factor U)
  rw [dbl_one, one_comp', one_comp'] at h
  simp only [adjoint_comp, map_smulₛₗ, smul_comp, comp_smul, smul_smul, comp_assoc, h,
    sqrt_sq_complex h0]

/-! ### Flattening the flag -/

/-- The known flattening `ℂ^ι ⊗ (ℂ² ⊗ W) ≅ ℂ^{ι × 2} ⊗ W`. -/
def flat2 (W : Type*) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (ι : Type) [Fintype ι] :
    PiLp 2 (fun _ : ι => Flagged W) ≃ₗᵢ[ℂ] PiLp 2 (fun _ : (Σ _ : ι, Bool) => W) :=
  (LinearIsometryEquiv.piLpCurry ℂ 2 (fun (_ : ι) (_ : Bool) => W)).symm

theorem flat2_dbl (ι : Type) [Fintype ι] (U : W →L[ℂ] W) :
    (flat2 W ι).conjStarAlgEquiv (WeightedClock.diagonal (fun _ : ι => dbl U)) =
      WeightedClock.diagonal (fun _ : (Σ _ : ι, Bool) => U) := by
  ext z ⟨i, b⟩
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, WeightedClock.diagonal_apply]
  simp [flat2, dbl]
  rfl

end

end SignedFactorSimulation
