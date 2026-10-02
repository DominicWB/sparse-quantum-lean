import SparseHamiltonian.FlatMaskedAccessContinuation2

/-!
# An exact Cayley circuit in the original three sparse primitives

The locator and entry rotation share one fixed clean encoding. Their literal
composition implements the locator-conjugated Cayley action. Each logical
masked call is replaced by three ordinary calls to the same native primitive;
all orientation, dummy, and value scratch registers are restored. Flattening
changes only the register layout and preserves each individual query count.

-/

namespace SparseHamiltonian.NativeCayleyProgram

noncomputable section
open ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding
open scoped InnerProduct
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

variable {X n Z : Type*} [Fintype n] [DecidableEq n]
  [Fintype Z] [AddCommGroup Z] [DecidableEq Z] {s : ℕ}

/-- Two locator calls, two entry-value calls, and the two inverse locator calls.
The dependence on the unknown sparse matrix occurs only in query instructions. -/
def logicalProgram (D : Data X n Z s) (γ : ℝ) :
    MultiOracleCircuit.Program (OrientedNativeLayout.logicalOracle D) :=
  NativeCleanConjugation.program (OrientedNativeLayout.locatorProgram D)
    (OrientedNativeValue.program D γ)

omit [DecidableEq Z] in
@[simp] theorem logicalProgram_count (D : Data X n Z s) (γ : ℝ) :
    (logicalProgram D γ).count = 6 := by
  rw [logicalProgram, NativeCleanConjugation.program_count,
    OrientedNativeLayout.locatorProgram_count, OrientedNativeValue.program_count]

omit [DecidableEq Z] in
/-- The two uses of each original primitive include inverse-query directions. -/
@[simp] theorem logicalProgram_cost (D : Data X n Z s) (γ : ℝ)
    (w : Query → ℕ) :
    (logicalProgram D γ).cost w =
      2 * w .rowLocation + 2 * w .columnLocation + 2 * w .value := by
  rw [logicalProgram, NativeCleanConjugation.program_cost,
    OrientedNativeLayout.locatorProgram_cost, OrientedNativeValue.program_cost]
  omega

/-- The exact full-output relation, prior to replacing masked calls by native
calls. It is valid for every real rescaling, independently of analytic bounds. -/
theorem logicalProgram_intertwines (D : Data X n Z s) (γ : ℝ) (x : X) :
    (logicalProgram D γ).eval x ∘L
        (OrientedNativeLayout.clean (n := n) (Z := Z)).toContinuousLinearMap =
      (OrientedNativeLayout.clean (n := n) (Z := Z)).toContinuousLinearMap ∘L
        FixedNativeCayleySimulation.action D x γ := by
  have h := NativeCleanConjugation.program_intertwines
    (OrientedNativeLayout.logicalOracle_unitary D)
    (OrientedNativeLayout.locatorProgram D) (OrientedNativeValue.program D γ)
    (OrientedNativeLayout.clean (n := n) (Z := Z)).toContinuousLinearMap
    (FixedLocatorConjugation.locator D)
    (fun y => OrientedEdgeCayley.action (D.matrix y) s γ)
    (FixedLocatorConjugation.locator_unitary D)
    (OrientedNativeLayout.locatorProgram_intertwines D)
    (OrientedNativeValue.program_intertwines D γ) x
  simpa only [logicalProgram, FixedNativeCayleySimulation.action,
    UnitaryCayleyTransport.conjugate, star_eq_adjoint, mul_def, comp_assoc] using h

/-- Actual native sparse queries with spectator registers. Every instruction
has a fixed row, column, or value label; orientation never selects the label. -/
def compiledProgram (D : Data X n Z s) (γ : ℝ) :
    MultiOracleCircuit.Program
      (NativeMaskedProgram.oracle (ι := Bool) (NativeSparseMaskedAccess.flatOracle D)) :=
  NativeMaskedProgram.compile (NativeSparseMaskedAccess.flatOracle D)
    (NativeSparseMaskedAccess.cleanBasis D) id OrientedNativeLayout.masks
    (logicalProgram D γ)

/-- The complete clean encoding is fixed independently of `x` and `γ`. -/
def compiledClean (D : Data X n Z s) :
    SparseEdgeMoments.OrientedSpace n →ₗᵢ[ℂ]
      NativeMaskedOracle.Physical Bool (NativeSparseMaskedAccess.Basis n Z) :=
  (NativeMaskedOracle.input (ι := Bool) (NativeSparseMaskedAccess.cleanBasis D)).comp
    (OrientedNativeLayout.clean (n := n) (Z := Z))

@[simp] theorem compiledProgram_count (D : Data X n Z s) (γ : ℝ) :
    (compiledProgram D γ).count = 18 := by
  rw [compiledProgram, NativeMaskedProgram.compile_count, logicalProgram_count]

@[simp] theorem compiledProgram_cost (D : Data X n Z s) (γ : ℝ)
    (w : Query → ℕ) :
    (compiledProgram D γ).cost w =
      6 * w .rowLocation + 6 * w .columnLocation + 6 * w .value := by
  rw [compiledProgram, NativeMaskedProgram.compile_cost, logicalProgram_cost]
  simp only [id_eq]
  omega

/-- Controlled-native access is eliminated using the original sparse-data
basis promises. No new oracle-control assumption occurs in the statement. -/
theorem compiledProgram_intertwines (D : Data X n Z s) (γ : ℝ) (x : X) :
    (compiledProgram D γ).eval x ∘L (compiledClean D).toContinuousLinearMap =
      (compiledClean D).toContinuousLinearMap ∘L
        FixedNativeCayleySimulation.action D x γ := by
  let E := (NativeMaskedOracle.input (ι := Bool)
    (NativeSparseMaskedAccess.cleanBasis D)).toContinuousLinearMap
  let C := (OrientedNativeLayout.clean (n := n) (Z := Z)).toContinuousLinearMap
  have hp : (compiledProgram D γ).eval x ∘L E =
      E ∘L (logicalProgram D γ).eval x :=
    NativeSparseMaskedAccess.compile_eval D id OrientedNativeLayout.masks
      (logicalProgram D γ) x
  change (compiledProgram D γ).eval x ∘L (E ∘L C) =
    (E ∘L C) ∘L FixedNativeCayleySimulation.action D x γ
  calc
    _ = ((compiledProgram D γ).eval x ∘L E) ∘L C := by
      simp only [comp_assoc]
    _ = (E ∘L (logicalProgram D γ).eval x) ∘L C := by rw [hp]
    _ = E ∘L ((logicalProgram D γ).eval x ∘L C) := by
      simp only [comp_assoc]
    _ = E ∘L (C ∘L FixedNativeCayleySimulation.action D x γ) := by
      rw [logicalProgram_intertwines]
    _ = _ := by simp only [comp_assoc]

theorem compiledProgram_unitary (D : Data X n Z s) (γ : ℝ) (x : X) :
    IsUnitary ((compiledProgram D γ).eval x) :=
  (compiledProgram D γ).eval_unitary
    (fun l y => NativeMaskedOracle.oracle_unitary
      (NativeSparseMaskedAccess.flatOracle D l)
      (NativeSparseMaskedAccess.flatOracle_unitary D l) y) x

/-- Computational basis for the physical orientation and native scratch. -/
abbrev Basis (n Z : Type*) :=
  FlatMaskedAccess.Basis (NativeSparseMaskedAccess.Basis n Z)

/-- Derive equality explicitly through the four spectator product layers.
This also serves the unfolded `NativeDilationLayout.Basis` spelling used by
the native-control compiler; no equality oracle or additional promise is used. -/
instance instDecidableEqBasis : DecidableEq (Basis n Z) :=
  @instDecidableEqProd _ _ inferInstance
    (@instDecidableEqProd _ _
      (@instDecidableEqProd _ _
        (@instDecidableEqProd _ _ inferInstance inferInstance) inferInstance) inferInstance)

/-- This oracle family is just the original three native queries, with
spectator registers and a fixed permutation of register coordinates. -/
abbrev oracle (D : Data X n Z s) :=
  FlatMaskedAccess.flatOracle (NativeSparseMaskedAccess.flatOracle D)

omit [DecidableEq Z] in
theorem oracle_unitary (D : Data X n Z s) (l : Query) (x : X) :
    IsUnitary (oracle D l x) :=
  FlatMaskedAccess.flatOracle_unitary (NativeSparseMaskedAccess.flatOracle D)
    (NativeSparseMaskedAccess.flatOracle_unitary D) l x

/-- The common basis input needed by the outer chronological mask compiler. -/
def cleanBasis (D : Data X n Z s) : Basis n Z :=
  FlatMaskedAccess.cleanBasis (NativeSparseMaskedAccess.cleanBasis D)

/-- This image is used only in the proof of native control and never in gates. -/
def image (D : Data X n Z s) (l : Query) (x : X) : Basis n Z :=
  FlatMaskedAccess.imageBasis (NativeSparseMaskedAccess.cleanBasis D)
    (NativeSparseMaskedAccess.image D l x)

/-- The original valid-slot promises suffice again after flattening. -/
theorem valid (D : Data X n Z s) (l : Query) (x : X) :
    oracle D l x (EuclideanSpace.single (cleanBasis D) 1) =
      EuclideanSpace.single (image D l x) 1 :=
  FlatMaskedAccess.valid (NativeSparseMaskedAccess.flatOracle D)
    (NativeSparseMaskedAccess.cleanBasis D) (NativeSparseMaskedAccess.image D)
    (NativeSparseMaskedAccess.valid D) l x

/-- The exact primitive sparse circuit, ready for chronological reuse. -/
def program (D : Data X n Z s) (γ : ℝ) :
    MultiOracleCircuit.Program (oracle D) :=
  FlatMaskedAccess.flatten (NativeSparseMaskedAccess.flatOracle D)
    (compiledProgram D γ)

/-- Fixed clean embedding; it depends only on public register and slot data. -/
def clean (D : Data X n Z s) :
    SparseEdgeMoments.OrientedSpace n →ₗᵢ[ℂ] EuclideanSpace ℂ (Basis n Z) :=
  FlatMaskedAccess.embedding (compiledClean D)

theorem clean_isometry (D : Data X n Z s) :
    (clean D).toContinuousLinearMap† ∘L (clean D).toContinuousLinearMap = 1 :=
  (clean D).adjoint_comp_self

@[simp] theorem program_count (D : Data X n Z s) (γ : ℝ) :
    (program D γ).count = 18 := by
  rw [program, FlatMaskedAccess.flatten_count, compiledProgram_count]

@[simp] theorem program_cost (D : Data X n Z s) (γ : ℝ) (w : Query → ℕ) :
    (program D γ).cost w =
      6 * w .rowLocation + 6 * w .columnLocation + 6 * w .value := by
  rw [program, FlatMaskedAccess.flatten_cost, compiledProgram_cost]

@[simp] theorem program_row_count (D : Data X n Z s) (γ : ℝ) :
    (program D γ).labelCount .rowLocation = 6 := by
  rw [MultiOracleCircuit.Program.labelCount, program_cost]
  decide

@[simp] theorem program_column_count (D : Data X n Z s) (γ : ℝ) :
    (program D γ).labelCount .columnLocation = 6 := by
  rw [MultiOracleCircuit.Program.labelCount, program_cost]
  decide

@[simp] theorem program_value_count (D : Data X n Z s) (γ : ℝ) :
    (program D γ).labelCount .value = 6 := by
  rw [MultiOracleCircuit.Program.labelCount, program_cost]
  decide

/-- Exact operator identity on the full clean private space, including padded
edges. The physical circuit is an explicit eighteen-query native program. -/
theorem program_intertwines (D : Data X n Z s) (γ : ℝ) (x : X) :
    (program D γ).eval x ∘L (clean D).toContinuousLinearMap =
      (clean D).toContinuousLinearMap ∘L FixedNativeCayleySimulation.action D x γ :=
  FlatMaskedAccess.flatten_intertwines (NativeSparseMaskedAccess.flatOracle D)
    (compiledProgram D γ) (compiledClean D) (FixedNativeCayleySimulation.action D x γ)
    x (compiledProgram_intertwines D γ x)

theorem program_unitary (D : Data X n Z s) (γ : ℝ) (x : X) :
    IsUnitary ((program D γ).eval x) :=
  (program D γ).eval_unitary (oracle_unitary D) x

end
end SparseHamiltonian.NativeCayleyProgram
