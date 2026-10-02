import SparseODE.CommonQueryShapeContinuation3

namespace SparseHamiltonian.ODENativeCircuitShape

noncomputable section
open ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding CommonQueryShape
open scoped InnerProduct
set_option maxRecDepth 4096
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 1500000

variable {X n Z : Type*} [Fintype n] [DecidableEq n]
  [Fintype Z] [AddCommGroup Z] [DecidableEq Z] {s : ℕ}

omit [DecidableEq Z] in
/-- Only the middle fixed rotation of the paired-entry circuit changes. The
compute and uncompute circuits remain identical syntax on both sides. -/
theorem taggedValueProgram_shape (D : Data X n Z s) (k γ ρ : ℝ) :
    singleErase Query.value (ODETaggedValueProgram.program D k γ ρ) =
      singleErase Query.value (ODETaggedValueProgram.program D 0 0 ρ) := by
  simp only [ODETaggedValueProgram.program, ODEPairedValueQuery.program, singleErase]

omit [DecidableEq Z] in
/-- Both register relabellings preserve that already proved small shape. -/
theorem taggedValueOracle_shape (D : Data X n Z s) (k γ ρ : ℝ) :
    singleErase Query.value (ODETaggedValueOracle.program D k γ ρ) =
      singleErase Query.value (ODETaggedValueOracle.program D 0 0 ρ) := by
  rw [ODETaggedValueOracle.program, ODETaggedValueOracle.program,
    singleErase_retarget, singleErase_retarget,
    singleErase_transport, singleErase_transport]
  exact taggedValueProgram_shape D k γ ρ

omit [DecidableEq Z] in
/-- Encoding the clean subspace preserves the four-letter native value shape. -/
theorem singleValue_shape (D : Data X n Z s) (k γ ρ : ℝ) :
    singleErase Query.value (ODENativeValue.singleProgram D k γ ρ) =
      singleErase Query.value (ODENativeValue.singleProgram D 0 0 ρ) := by
  rw [ODENativeValue.singleProgram, ODENativeValue.singleProgram,
    singleErase_compile_query, singleErase_compile_query]
  exact taggedValueOracle_shape D k γ ρ

omit [DecidableEq Z] in
/-- The native value label is the same at every public parameter. -/
theorem value_shape (D : Data X n Z s) (k γ ρ : ℝ) :
    erase (ODENativeValue.program D k γ ρ) =
      erase (ODENativeValue.program D 0 0 ρ) := by
  rw [ODENativeValue.program, ODENativeValue.program,
    erase_embed_single, erase_embed_single]
  exact singleValue_shape D k γ ρ

omit [DecidableEq Z] in
/-- The common forward/inverse locator circuits do not alter shape equality. -/
theorem logicalCayley_shape (D : Data X n Z s) (k γ ρ : ℝ) :
    erase (ODENativeCayley.logicalProgram D k γ ρ) =
      erase (ODENativeCayley.logicalProgram D 0 0 ρ) := by
  unfold ODENativeCayley.logicalProgram
  exact native_clean_conjugation_shape_eq
    (ODENativeLocator.locatorProgram D)
    (ODENativeValue.program D k γ ρ) (ODENativeValue.program D 0 0 ρ)
    (value_shape D k γ ρ)

/-- The dummy-input construction is applied to equal logical shapes. -/
theorem compiledCayley_shape (D : Data X n Z s) (k γ ρ : ℝ) :
    erase (ODENativeCayley.compiledProgram D k γ ρ) =
      erase (ODENativeCayley.compiledProgram D 0 0 ρ) := by
  unfold ODENativeCayley.compiledProgram
  exact native_masked_compile_shape_eq (NativeSparseMaskedAccess.flatOracle D)
    (NativeSparseMaskedAccess.cleanBasis D) id ODENativeLayout.masks
    (ODENativeCayley.logicalProgram D k γ ρ)
    (ODENativeCayley.logicalProgram D 0 0 ρ) (logicalCayley_shape D k γ ρ)

/-- Exact parameter independence for the actual complete 24-query circuit. -/
theorem cayley_shape (D : Data X n Z s) (k γ ρ : ℝ) :
    erase (ODENativeCayley.program D k γ ρ) =
      erase (ODENativeCayley.program D 0 0 ρ) := by
  unfold ODENativeCayley.program
  exact flatten_shape_eq (NativeSparseMaskedAccess.flatOracle D)
    (ODENativeCayley.compiledProgram D k γ ρ)
    (ODENativeCayley.compiledProgram D 0 0 ρ) (compiledCayley_shape D k γ ρ)

/-- Exact parameter independence for the complete 72-query active circuit. -/
theorem active_shape (D : Data X n Z s) (k γ ρ : ℝ) (T d r : ℕ) :
    erase (ODENativeActive.program D k γ ρ T d r) =
      erase (ODENativeActive.program D 0 0 ρ T d r) := by
  unfold ODENativeActive.program
  exact whole_active_shape_eq (C := PUnit.{1}) (ODENativeCayley.oracle D)
    (ODENativeCayley.cleanBasis D)
    (ODENativeCayley.program D k γ ρ) (ODENativeCayley.program D 0 0 ρ)
    T d r (cayley_shape D k γ ρ)

end
end SparseHamiltonian.ODENativeCircuitShape
