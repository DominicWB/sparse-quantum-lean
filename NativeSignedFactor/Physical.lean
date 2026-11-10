import NativeSignedFactor.Factor

set_option autoImplicit false

/-!
# The physical native factor unitary

The logical factor program uses masked native calls on the orientation register: the row locator
acts only on the row orientation and the column locator only on the column orientation. The released
compilation (`SparseHamiltonian.NativeMaskedProgram.compile`) replaces each masked call by three
calls of the original native oracle with spectator registers, using the in-place, phase-one locator
promise at one fixed clean basis state; no controlled oracle is assumed. The physical factor program
therefore uses `12` native calls (`physProgram_count`): three row-locator, three column-locator and
six value calls (`physProgram_cost`). It intertwines the clean encoding (`physProgram_intertwines`),
and the factor structure transported along the encoding (`physKnown`) has the same compressions
(`phys_Cop`, `phys_Dop_le`).
-/

namespace NativeSignedFactor

noncomputable section

open ContinuousLinearMap SparseHamiltonian OracleCircuit NativeSparseBlockEncoding
open OrientedNativeLayout SparseEdgeMoments SignedFactorSimulation
open scoped InnerProduct

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s : ℕ}

/-- The physical workspace of the factor unitary: the logical workspace with the clean control,
dummy and reference registers of the native-control construction. -/
abbrev Phys (n Z : Type*) [Fintype n] [Fintype Z] :=
  NativeMaskedOracle.Physical Bool (NativeSparseMaskedAccess.Basis n Z)

/-- The physical oracle family: each original native primitive (row locator, column locator,
value oracle) on its register, with every other register a spectator. -/
abbrev physOracle (D : Data X n Z s) : Query → X → Phys n Z →L[ℂ] Phys n Z :=
  NativeMaskedProgram.oracle (ι := Bool) (NativeSparseMaskedAccess.flatOracle D)

omit [DecidableEq Z] in
theorem physOracle_unitary (D : Data X n Z s) (l : Query) (x : X) :
    IsUnitary (physOracle D l x) :=
  NativeMaskedOracle.oracle_unitary _ (NativeSparseMaskedAccess.flatOracle_unitary D l) x

/-- The known clean encoding of the logical workspace. -/
def embed (D : Data X n Z s) : Space n Z →L[ℂ] Phys n Z :=
  (NativeMaskedOracle.input (ι := Bool)
    (NativeSparseMaskedAccess.cleanBasis D)).toContinuousLinearMap

theorem embed_isometry (D : Data X n Z s) : (embed D)† ∘L embed D = 1 :=
  LinearIsometry.adjoint_comp_self _

/-- The physical factor program: the compiled logical factor program. -/
def physProgram (D : Data X n Z s) (κ : ℝ) : MultiOracleCircuit.Program (physOracle D) :=
  NativeMaskedProgram.compile (NativeSparseMaskedAccess.flatOracle D)
    (NativeSparseMaskedAccess.cleanBasis D) id masks (factorProgram D κ)

/-- Twelve native calls, counting adjoints. -/
@[simp] theorem physProgram_count (D : Data X n Z s) (κ : ℝ) :
    (physProgram D κ).count = 12 := by
  rw [physProgram, NativeMaskedProgram.compile_count, factorProgram_count]

/-- Three row-locator, three column-locator and six value calls. -/
theorem physProgram_cost (D : Data X n Z s) (κ : ℝ) (w : Query → ℕ) :
    (physProgram D κ).cost w = 3 * w .rowLocation + 3 * w .columnLocation + 6 * w .value := by
  rw [physProgram, NativeMaskedProgram.compile_cost, factorProgram_cost]
  simp only [id]
  ring

/-- The physical factor program intertwines the clean encoding with the logical factor. -/
theorem physProgram_intertwines (D : Data X n Z s) (κ : ℝ) (x : X) :
    (physProgram D κ).eval x ∘L embed D = embed D ∘L (factorProgram D κ).eval x :=
  NativeSparseMaskedAccess.compile_eval D id masks (factorProgram D κ) x

/-- The physical factor unitary is unitary on the whole physical workspace. -/
theorem physProgram_unitary (D : Data X n Z s) (κ : ℝ) (x : X) :
    IsUnitary ((physProgram D κ).eval x) :=
  NativeMaskedProgram.compile_unitary _ (NativeSparseMaskedAccess.flatOracle_unitary D) _ _ _ _ x

/-- The physical factor structure: input `embed ∘ input`, success projection and reflection
transported along the clean encoding. All of its data are known. -/
def physKnown (D : Data X n Z s) : Known (EuclideanSpace ℂ n) (Phys n Z) :=
  transport (known D) (embed D) (embed_isometry D)

/-- **Signed compression** of the physical native factor: `B† Z B = H/(sκ)`. -/
theorem phys_Cop (D : Data X n Z s) {κ : ℝ} (hκ : 0 < κ) (x : X)
    (hH : (D.matrix x).IsHermitian) (hentry : ∀ i j, ‖D.matrix x i j‖ ≤ κ) :
    (physKnown D).Cop ((physProgram D κ).eval x) =
      ((((s : ℝ) * κ)⁻¹ : ℝ) : ℂ) • SparseStateOverlap.matrixOperator (D.matrix x) := by
  rw [physKnown, transport_Cop _ _ (physProgram_intertwines D κ x)]
  exact Cop_eq D hκ x hH hentry

/-- The Hamiltonian of the physical native factor: `H = sκ B† Z B`. -/
theorem phys_ham (D : Data X n Z s) {κ : ℝ} (hκ : 0 < κ) (x : X)
    (hH : (D.matrix x).IsHermitian) (hentry : ∀ i j, ‖D.matrix x i j‖ ≤ κ) :
    (physKnown D).ham ((s : ℝ) * κ) ((physProgram D κ).eval x) =
      SparseStateOverlap.matrixOperator (D.matrix x) := by
  have hlam : (s : ℝ) * κ ≠ 0 := (mul_pos (by exact_mod_cast D.slots_pos) hκ).ne'
  rw [Known.ham, phys_Cop D hκ x hH hentry, smul_smul, ← Complex.ofReal_mul,
    mul_inv_cancel₀ hlam, Complex.ofReal_one, one_smul]

/-- The physical factor has the same norm bound as the logical one. -/
theorem phys_norm_factor_sq_le (D : Data X n Z s) {κ η : ℝ} (hκ : 0 < κ) (hη : 0 ≤ η) (x : X)
    (hrow : ∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2)
    (hcol : ∀ j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) (v : EuclideanSpace ℂ n) :
    ‖(physKnown D).factor ((physProgram D κ).eval x) v‖ ^ 2 ≤
      η / (Real.sqrt (s : ℝ) * κ) * ‖v‖ ^ 2 := by
  rw [physKnown, transport_factor _ _ (physProgram_intertwines D κ x), comp_apply, embed,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometry.norm_map]
  exact norm_factor_sq_le D hκ hη x hrow hcol v

/-- The norm bound of the physical factor, in the form used by `Dop_le_of_bound`. -/
theorem phys_bound (D : Data X n Z s) {κ η : ℝ} (hκ : 0 < κ) (hη : 0 ≤ η) (x : X)
    (hrow : ∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2)
    (hcol : ∀ j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) :
    NormBound ((physKnown D).factor ((physProgram D κ).eval x))
      (η / (Real.sqrt (s : ℝ) * κ)) := by
  intro v
  exact phys_norm_factor_sq_le D hκ hη x hrow hcol v

/-- **Successful weight** of the physical native factor: `B† B ⪯ η/(√s κ) I`. -/
theorem phys_Dop_le (D : Data X n Z s) {κ η : ℝ} (hκ : 0 < κ) (hη : 0 ≤ η) (x : X)
    (hrow : ∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2)
    (hcol : ∀ j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) :
    (physKnown D).Dop ((physProgram D κ).eval x) ≤
      ((η / (Real.sqrt (s : ℝ) * κ) : ℝ) : ℂ) • (1 : EuclideanSpace ℂ n →L[ℂ] _) := by
  rw [physKnown, transport_Dop _ _ (physProgram_intertwines D κ x)]
  exact Dop_le D hκ hη x hrow hcol

/-- **Exact successful weight** of the physical native factor: `B† B = D_H/(sκ)`. -/
theorem phys_Dop_eq (D : Data X n Z s) {κ : ℝ} (hκ : 0 < κ) (x : X)
    (hH : (D.matrix x).IsHermitian) (hentry : ∀ i j, ‖D.matrix x i j‖ ≤ κ) :
    (physKnown D).Dop ((physProgram D κ).eval x) =
      ((((s : ℝ) * κ)⁻¹ : ℝ) : ℂ) • SparseStateOverlap.matrixOperator
        (Matrix.diagonal (fun i => ((∑ j, ‖D.matrix x i j‖ : ℝ) : ℂ))) := by
  rw [physKnown, transport_Dop _ _ (physProgram_intertwines D κ x)]
  exact Dop_eq D hκ x hH hentry

/-- The case `κ = η` of the successful weight (`opt:eq:whole-factor`): `B† B ⪯ s^{-1/2} I`. -/
theorem phys_Dop_le_eta (D : Data X n Z s) {η : ℝ} (hη : 0 < η) (x : X)
    (hrow : ∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2)
    (hcol : ∀ j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) :
    (physKnown D).Dop ((physProgram D η).eval x) ≤
      (((Real.sqrt (s : ℝ))⁻¹ : ℝ) : ℂ) • (1 : EuclideanSpace ℂ n →L[ℂ] _) := by
  have h := phys_Dop_le D hη hη.le x hrow hcol
  have hs : (0 : ℝ) < Real.sqrt (s : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast D.slots_pos)
  have he : η / (Real.sqrt (s : ℝ) * η) = (Real.sqrt (s : ℝ))⁻¹ := by
    field_simp
  rwa [he] at h

end

end NativeSignedFactor
