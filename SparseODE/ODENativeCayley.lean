import SparseODE.FlatBranchNativeAccess

/-!
# A counted native sparse circuit for the tagged ODE Cayley action

The program combines the actual locator and paired-value circuits, then
eliminates their branch controls using the original sparse basis promises.
Every instruction retains a fixed row, column or value label. The private
clean encoding is independent of the unknown matrix and all LCHS parameters.

-/

namespace SparseHamiltonian.ODENativeCayley

noncomputable section
open ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding
open scoped InnerProduct
set_option maxRecDepth 4096
set_option maxHeartbeats 1500000

variable {X n Z : Type*} [Fintype n] [DecidableEq n]
  [Fintype Z] [AddCommGroup Z] [DecidableEq Z] {s : ℕ}

/-- Locate, compute both entries and rotate, then undo the locator transport. -/
def logicalProgram (D : Data X n Z s) (k γ ρ : ℝ) :
    MultiOracleCircuit.Program (ODENativeLayout.logicalOracle D) :=
  NativeCleanConjugation.program (ODENativeLocator.locatorProgram D)
    (ODENativeValue.program D k γ ρ)

omit [DecidableEq Z] in
@[simp] theorem logicalProgram_count (D : Data X n Z s) (k γ ρ : ℝ) :
    (logicalProgram D k γ ρ).count = 8 := by
  rw [logicalProgram, NativeCleanConjugation.program_count,
    ODENativeLocator.locatorProgram_count, ODENativeValue.program_count]

omit [DecidableEq Z] in
@[simp] theorem logicalProgram_cost (D : Data X n Z s) (k γ ρ : ℝ)
    (w : Query → ℕ) :
    (logicalProgram D k γ ρ).cost w =
      2 * w .rowLocation + 2 * w .columnLocation + 4 * w .value := by
  rw [logicalProgram, NativeCleanConjugation.program_cost,
    ODENativeLocator.locatorProgram_cost, ODENativeValue.program_cost]
  omega

/-- Exact clean action of the conjugated circuit on all tagged edges. -/
theorem logicalProgram_intertwines (D : Data X n Z s) (k γ ρ : ℝ) (x : X) :
    (logicalProgram D k γ ρ).eval x ∘L
        (ODENativeLayout.clean (n := n) (Z := Z)).toContinuousLinearMap =
      (ODENativeLayout.clean (n := n) (Z := Z)).toContinuousLinearMap ∘L
        ODEFixedTaggedMoments.action D x
          (ODEMatrixEnergy.lchsHamiltonian (D.matrix x) k) ρ γ := by
  have h := NativeCleanConjugation.program_intertwines
    (ODENativeLayout.logicalOracle_unitary D)
    (ODENativeLocator.locatorProgram D) (ODENativeValue.program D k γ ρ)
    (ODENativeLayout.clean (n := n) (Z := Z)).toContinuousLinearMap
    (ODETaggedLocators.locator D)
    (fun y => ODETaggedCayley.action (D.matrix y)
      (ODEMatrixEnergy.lchsHamiltonian (D.matrix y) k) s ρ γ)
    (ODETaggedLocators.locator_unitary D)
    (ODENativeLocator.locatorProgram_intertwines D)
    (ODENativeValue.program_intertwines D k γ ρ) x
  simpa only [logicalProgram, ODEFixedTaggedMoments.action,
    UnitaryCayleyTransport.conjugate, star_eq_adjoint, mul_def, comp_assoc] using h

/-- Three ordinary native calls implement each controlled logical letter. -/
def compiledProgram (D : Data X n Z s) (k γ ρ : ℝ) :
    MultiOracleCircuit.Program
      (NativeMaskedProgram.oracle (ι := ODENativeLayout.Branch Z)
        (NativeSparseMaskedAccess.flatOracle D)) :=
  NativeMaskedProgram.compile (NativeSparseMaskedAccess.flatOracle D)
    (NativeSparseMaskedAccess.cleanBasis D) id ODENativeLayout.masks
    (logicalProgram D k γ ρ)

/-- Known control, dummy and reference registers are appended uniformly. -/
def compiledClean (D : Data X n Z s) :
    ODETaggedMoments.PrivateSpace n →ₗᵢ[ℂ]
      NativeMaskedOracle.Physical (ODENativeLayout.Branch Z)
        (NativeSparseMaskedAccess.Basis n Z) :=
  (NativeMaskedOracle.input (ι := ODENativeLayout.Branch Z)
    (NativeSparseMaskedAccess.cleanBasis D)).comp
    (ODENativeLayout.clean (n := n) (Z := Z))

@[simp] theorem compiledProgram_count (D : Data X n Z s) (k γ ρ : ℝ) :
    (compiledProgram D k γ ρ).count = 24 := by
  rw [compiledProgram, NativeMaskedProgram.compile_count, logicalProgram_count]

@[simp] theorem compiledProgram_cost (D : Data X n Z s) (k γ ρ : ℝ)
    (w : Query → ℕ) :
    (compiledProgram D k γ ρ).cost w =
      6 * w .rowLocation + 6 * w .columnLocation + 12 * w .value := by
  rw [compiledProgram, NativeMaskedProgram.compile_cost, logicalProgram_cost]
  simp only [id_eq]
  omega

/-- All coherent control is discharged by the original valid-slot promises. -/
theorem compiledProgram_intertwines (D : Data X n Z s)
    (k γ ρ : ℝ) (x : X) :
    (compiledProgram D k γ ρ).eval x ∘L (compiledClean D).toContinuousLinearMap =
      (compiledClean D).toContinuousLinearMap ∘L ODEFixedTaggedMoments.action D x
        (ODEMatrixEnergy.lchsHamiltonian (D.matrix x) k) ρ γ := by
  let E := (NativeMaskedOracle.input (ι := ODENativeLayout.Branch Z)
    (NativeSparseMaskedAccess.cleanBasis D)).toContinuousLinearMap
  let C := (ODENativeLayout.clean (n := n) (Z := Z)).toContinuousLinearMap
  have hp : (compiledProgram D k γ ρ).eval x ∘L E =
      E ∘L (logicalProgram D k γ ρ).eval x :=
    NativeSparseMaskedAccess.compile_eval D id ODENativeLayout.masks
      (logicalProgram D k γ ρ) x
  change (compiledProgram D k γ ρ).eval x ∘L (E ∘L C) =
    (E ∘L C) ∘L ODEFixedTaggedMoments.action D x
      (ODEMatrixEnergy.lchsHamiltonian (D.matrix x) k) ρ γ
  calc
    _ = ((compiledProgram D k γ ρ).eval x ∘L E) ∘L C := by simp only [comp_assoc]
    _ = (E ∘L (logicalProgram D k γ ρ).eval x) ∘L C := by rw [hp]
    _ = E ∘L ((logicalProgram D k γ ρ).eval x ∘L C) := by simp only [comp_assoc]
    _ = E ∘L (C ∘L ODEFixedTaggedMoments.action D x
        (ODEMatrixEnergy.lchsHamiltonian (D.matrix x) k) ρ γ) := by
      rw [logicalProgram_intertwines]
    _ = _ := by simp only [comp_assoc]

/-- A computational basis for the complete common physical workspace. -/
abbrev Basis (n Z : Type*) :=
  FlatBranchNativeAccess.Basis (ODENativeLayout.Branch Z)
    (NativeSparseMaskedAccess.Basis n Z)

instance instDecidableEqBasis : DecidableEq (Basis n Z) :=
  @instDecidableEqProd _ _
    (@instDecidableEqProd _ _
      (@instDecidableEqProd _ _ inferInstance inferInstance) inferInstance)
    (@instDecidableEqProd _ _
      (@instDecidableEqProd _ _
        (@instDecidableEqProd _ _ inferInstance inferInstance) inferInstance) inferInstance)

/-- Flattening only changes fixed register coordinates of the native calls. -/
abbrev oracle (D : Data X n Z s) :=
  FlatBranchNativeAccess.flatOracle (ι := ODENativeLayout.Branch Z)
    (NativeSparseMaskedAccess.flatOracle D)

omit [DecidableEq Z] in
theorem oracle_unitary (D : Data X n Z s) (l : Query) (x : X) :
    IsUnitary (oracle D l x) :=
  FlatBranchNativeAccess.flatOracle_unitary (NativeSparseMaskedAccess.flatOracle D)
    (NativeSparseMaskedAccess.flatOracle_unitary D) l x

def cleanBasis (D : Data X n Z s) : Basis n Z :=
  FlatBranchNativeAccess.cleanBasis ((false, false), (0 : Z))
    (NativeSparseMaskedAccess.cleanBasis D)

/-- The unknown basis image is only an analytical witness for later controls. -/
def image (D : Data X n Z s) (l : Query) (x : X) : Basis n Z :=
  FlatBranchNativeAccess.imageBasis ((false, false), (0 : Z))
    (NativeSparseMaskedAccess.cleanBasis D) (NativeSparseMaskedAccess.image D l x)

theorem valid (D : Data X n Z s) (l : Query) (x : X) :
    oracle D l x (EuclideanSpace.single (cleanBasis D) 1) =
      EuclideanSpace.single (image D l x) 1 :=
  FlatBranchNativeAccess.valid (NativeSparseMaskedAccess.flatOracle D)
    ((false, false), (0 : Z)) (NativeSparseMaskedAccess.cleanBasis D)
    (NativeSparseMaskedAccess.image D) (NativeSparseMaskedAccess.valid D) l x

/-- The final literal program uses only the original row, column and value calls. -/
def program (D : Data X n Z s) (k γ ρ : ℝ) :
    MultiOracleCircuit.Program (oracle D) :=
  FlatBranchNativeAccess.flatten (NativeSparseMaskedAccess.flatOracle D)
    (compiledProgram D k γ ρ)

def clean (D : Data X n Z s) :
    ODETaggedMoments.PrivateSpace n →ₗᵢ[ℂ] EuclideanSpace ℂ (Basis n Z) :=
  FlatBranchNativeAccess.embedding (compiledClean D)

theorem clean_isometry (D : Data X n Z s) :
    (clean D).toContinuousLinearMap† ∘L (clean D).toContinuousLinearMap = 1 :=
  (clean D).adjoint_comp_self

@[simp] theorem program_count (D : Data X n Z s) (k γ ρ : ℝ) :
    (program D k γ ρ).count = 24 := by
  rw [program, FlatBranchNativeAccess.flatten_count, compiledProgram_count]

@[simp] theorem program_cost (D : Data X n Z s) (k γ ρ : ℝ) (w : Query → ℕ) :
    (program D k γ ρ).cost w =
      6 * w .rowLocation + 6 * w .columnLocation + 12 * w .value := by
  rw [program, FlatBranchNativeAccess.flatten_cost, compiledProgram_cost]

@[simp] theorem program_row_count (D : Data X n Z s) (k γ ρ : ℝ) :
    (program D k γ ρ).labelCount .rowLocation = 6 := by
  rw [MultiOracleCircuit.Program.labelCount, program_cost]
  decide

@[simp] theorem program_column_count (D : Data X n Z s) (k γ ρ : ℝ) :
    (program D k γ ρ).labelCount .columnLocation = 6 := by
  rw [MultiOracleCircuit.Program.labelCount, program_cost]
  decide

@[simp] theorem program_value_count (D : Data X n Z s) (k γ ρ : ℝ) :
    (program D k γ ρ).labelCount .value = 12 := by
  rw [MultiOracleCircuit.Program.labelCount, program_cost]
  decide

/-- Exact full-output semantics, with every scratch register restored. -/
theorem program_intertwines (D : Data X n Z s) (k γ ρ : ℝ) (x : X) :
    (program D k γ ρ).eval x ∘L (clean D).toContinuousLinearMap =
      (clean D).toContinuousLinearMap ∘L ODEFixedTaggedMoments.action D x
        (ODEMatrixEnergy.lchsHamiltonian (D.matrix x) k) ρ γ :=
  FlatBranchNativeAccess.flatten_intertwines (NativeSparseMaskedAccess.flatOracle D)
    (compiledProgram D k γ ρ) (compiledClean D)
    (ODEFixedTaggedMoments.action D x
      (ODEMatrixEnergy.lchsHamiltonian (D.matrix x) k) ρ γ)
    x (compiledProgram_intertwines D k γ ρ x)

theorem program_unitary (D : Data X n Z s) (k γ ρ : ℝ) (x : X) :
    IsUnitary ((program D k γ ρ).eval x) :=
  (program D k γ ρ).eval_unitary (oracle_unitary D) x

end
end SparseHamiltonian.ODENativeCayley
