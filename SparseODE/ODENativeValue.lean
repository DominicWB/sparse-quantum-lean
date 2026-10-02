import SparseODE.ODENativeLocator

/-!
# Four native value calls in the common locator/value workspace

The Cayley value program is lifted through a fixed isometric
register encoding. Each value query becomes one original native value query,
with all other registers spectators. Fixed gates are extended as identity on
the complementary subspace. Query syntax records the value label explicitly.
-/

namespace SparseHamiltonian.ODENativeValue

noncomputable section
open ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding
open scoped InnerProduct
set_option maxHeartbeats 1000000
set_option maxRecDepth 3000

variable {X n Z : Type*} [Fintype n] [DecidableEq n]
  [Fintype Z] [AddCommGroup Z] [DecidableEq Z] {s : ℕ}

/-- Lift only the fixed gate syntax; every oracle letter stays a single
query to the native value primitive in the common physical workspace. -/
def singleProgram (D : Data X n Z s) (k γ ρ : ℝ) :
    OracleCircuit.Program (ODENativeLayout.logicalOracle D .value) :=
  EncodedOracle.compile
    (ODENativeLayout.valueEmbedding (n := n) (Z := Z)).toContinuousLinearMap
    (ODENativeLayout.valueEmbedding (n := n) (Z := Z)).adjoint_comp_self
    (.query : OracleCircuit.Program (ODENativeLayout.logicalOracle D .value))
    (ODETaggedValueOracle.program D k γ ρ)

omit [DecidableEq Z] in
/-- Isometric compilation introduces no extra value queries. -/
theorem singleProgram_count (D : Data X n Z s) (k γ ρ : ℝ) :
    (singleProgram D k γ ρ).count = 4 := by
  rw [singleProgram, EncodedOracle.compile_count,
    ODETaggedValueOracle.program_count, OracleCircuit.Program.count_query]

omit [DecidableEq Z] in
/-- Correctness of the entire lifted program on the encoded value workspace. -/
theorem singleProgram_intertwines (D : Data X n Z s) (k γ ρ : ℝ) (x : X) :
    (singleProgram D k γ ρ).eval x ∘L
        (ODENativeLayout.valueEmbedding (n := n) (Z := Z)).toContinuousLinearMap =
      (ODENativeLayout.valueEmbedding (n := n) (Z := Z)).toContinuousLinearMap ∘L
        (ODETaggedValueOracle.program D k γ ρ).eval x := by
  exact EncodedOracle.compile_eval
    (ODENativeLayout.valueEmbedding (n := n) (Z := Z)).toContinuousLinearMap
    (ODENativeLayout.valueEmbedding (n := n) (Z := Z)).adjoint_comp_self
    (.query : OracleCircuit.Program (ODENativeLayout.logicalOracle D .value))
    (fun x => ODENativeLayout.logicalOracle_unitary D .value x)
    (ODETaggedValueOracle.oracle_unitary D)
    (ODENativeLayout.value_intertwines D)
    (ODETaggedValueOracle.program D k γ ρ) x

/-- Give every occurrence of the original value primitive its literal label. -/
def program (D : Data X n Z s) (k γ ρ : ℝ) :
    MultiOracleCircuit.Program (ODENativeLayout.logicalOracle D) :=
  MultiOracleCircuit.Program.embed .value (singleProgram D k γ ρ)

omit [DecidableEq Z] in
theorem program_eval (D : Data X n Z s) (k γ ρ : ℝ) (x : X) :
    (program D k γ ρ).eval x = (singleProgram D k γ ρ).eval x := by
  simp only [program, MultiOracleCircuit.Program.eval_embed]

omit [DecidableEq Z] in
/-- The program has four native queries in total. -/
theorem program_count (D : Data X n Z s) (k γ ρ : ℝ) :
    (program D k γ ρ).count = 4 := by
  rw [program, MultiOracleCircuit.Program.count_embed, singleProgram_count]

omit [DecidableEq Z] in
/-- Only the value label contributes, for arbitrary assigned primitive costs. -/
theorem program_cost (D : Data X n Z s) (k γ ρ : ℝ) (w : Query → ℕ) :
    (program D k γ ρ).cost w = 4 * w .value := by
  rw [program, MultiOracleCircuit.Program.cost_embed, singleProgram_count]

omit [DecidableEq Z] in
theorem program_labelCount (D : Data X n Z s) (k γ ρ : ℝ) (l : Query) :
    (program D k γ ρ).labelCount l = if Query.value = l then 4 else 0 := by
  rw [MultiOracleCircuit.Program.labelCount, program_cost]
  by_cases h : Query.value = l <;> simp [h]

omit [DecidableEq Z] in
/-- The complete physical operation is unitary, including dirty ancillas. -/
theorem program_unitary (D : Data X n Z s) (k γ ρ : ℝ) (x : X) :
    IsUnitary ((program D k γ ρ).eval x) :=
  (program D k γ ρ).eval_unitary (ODENativeLayout.logicalOracle_unitary D) x

/-- One fixed clean encoding for the analytic tagged private space. It has
no dependence on the unknown matrix or the simulation parameters. -/
def clean : ODETaggedMoments.PrivateSpace n →ₗᵢ[ℂ] ODENativeLayout.Space n Z :=
  (ODENativeLayout.valueEmbedding (n := n) (Z := Z)).comp
    (ODETaggedValueOracle.clean (n := n) (Z := Z))

omit [DecidableEq n] in
theorem clean_isometry :
    (clean (n := n) (Z := Z)).toContinuousLinearMap† ∘L
      (clean (n := n) (Z := Z)).toContinuousLinearMap = 1 :=
  LinearIsometry.adjoint_comp_self _

/-- The native program realizes the exact analytic tagged Cayley action on
the common clean encoding and restores all value work registers. -/
theorem program_intertwines (D : Data X n Z s) (k γ ρ : ℝ) (x : X) :
    (program D k γ ρ).eval x ∘L (clean (n := n) (Z := Z)).toContinuousLinearMap =
      (clean (n := n) (Z := Z)).toContinuousLinearMap ∘L
        ODETaggedCayley.action (D.matrix x)
          (ODEMatrixEnergy.lchsHamiltonian (D.matrix x) k) s ρ γ := by
  change (program D k γ ρ).eval x ∘L
      ((ODENativeLayout.valueEmbedding (n := n) (Z := Z)).toContinuousLinearMap ∘L
        (ODETaggedValueOracle.clean (n := n) (Z := Z)).toContinuousLinearMap) =
    ((ODENativeLayout.valueEmbedding (n := n) (Z := Z)).toContinuousLinearMap ∘L
        (ODETaggedValueOracle.clean (n := n) (Z := Z)).toContinuousLinearMap) ∘L _
  rw [program_eval, ← comp_assoc, singleProgram_intertwines, comp_assoc,
    ODETaggedValueOracle.program_intertwines, comp_assoc]

omit [DecidableEq Z] in
/-- Adjoint syntax retains the same label-by-label query count. -/
theorem adjoint_program_cost (D : Data X n Z s) (k γ ρ : ℝ) (w : Query → ℕ) :
    (program D k γ ρ).adjoint.cost w = 4 * w .value := by
  rw [MultiOracleCircuit.Program.cost_adjoint, program_cost]

/-- The inverse gate also restores the same fixed clean subspace. -/
theorem adjoint_program_intertwines (D : Data X n Z s) (k γ ρ : ℝ) (x : X) :
    (program D k γ ρ).adjoint.eval x ∘L
        (clean (n := n) (Z := Z)).toContinuousLinearMap =
      (clean (n := n) (Z := Z)).toContinuousLinearMap ∘L
        (ODETaggedCayley.action (D.matrix x)
          (ODEMatrixEnergy.lchsHamiltonian (D.matrix x) k) s ρ γ)† := by
  rw [MultiOracleCircuit.Program.eval_adjoint]
  exact EncodedOracle.adjoint_intertwines _ _ _
    (program_unitary D k γ ρ x)
    (ODETaggedCayley.action_unitary (D.matrix x)
      (ODEMatrixEnergy.lchsHamiltonian (D.matrix x) k) s ρ γ)
    (program_intertwines D k γ ρ x)

end
end SparseHamiltonian.ODENativeValue
