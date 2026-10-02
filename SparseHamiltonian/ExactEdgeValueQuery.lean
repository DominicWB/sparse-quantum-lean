import SparseHamiltonian.SparseEdgeMomentsContinuation2

/-!
# Exact two-value-query implementation of the sparse edge Cayley action

The decoder and the real rescaling parameter are public fixed data.  Every
entry-dependent edge Cayley gate is obtained by one ordinary value lookup,
one query-free decoded gate, and one inverse lookup.  In particular, the
count has no dependence on the number of sparse slots, the rescaling, or
an approximation tolerance.  All statements include coherent address inputs
and exact restoration of the value scratch register.

This component does not yet construct the orientation-dependent locator
conjugation or connect the sparse boundary moments to the simulation theorem.
-/

namespace SparseHamiltonian.ExactEdgeValueQuery

noncomputable section
open ContinuousLinearMap OracleCircuit
open scoped InnerProduct

variable {X n Z : Type*} [Fintype n] [DecidableEq n]
  [Fintype Z] [AddCommGroup Z] {s : ℕ}

/-- Address register carrying the two-dimensional edge orientation. -/
abbrev LogicalSpace (n : Type*) := PiLp 2 (fun _ : n × n => ExactEdgeCayley.Qubit)

/-- The physical value scratch register and the edge orientation. -/
abbrev Space (n Z : Type*) :=
  PiLp 2 (fun _ : (n × n) × Z => ExactEdgeCayley.Qubit)

/-- A public gate table.  It contains no unknown input instance. -/
def gates (D : NativeSparseBlockEncoding.Data X n Z s) (γ : ℝ)
    (a : n × n) (z : Z) : ExactEdgeCayley.Qubit →L[ℂ] ExactEdgeCayley.Qubit :=
  ExactEdgeCayley.action ((γ : ℂ) * D.decode a z)

omit [Fintype Z] [AddCommGroup Z] in
/-- The exact edge gate is legal for every decoder output and every scale. -/
theorem gates_unitary (D : NativeSparseBlockEncoding.Data X n Z s) (γ : ℝ)
    (a : n × n) (z : Z) : IsUnitary (gates D γ a z) :=
  ExactEdgeCayley.action_unitary _

/-- The desired direct sum depends on actual matrix entries, not encodings. -/
def logical (D : NativeSparseBlockEncoding.Data X n Z s) (γ : ℝ) (x : X) :
    LogicalSpace n →L[ℂ] LogicalSpace n :=
  WeightedClock.diagonal
    (fun a => ExactEdgeCayley.action ((γ : ℂ) * D.matrix x a.1 a.2))

omit [Fintype Z] [AddCommGroup Z] in
@[simp] theorem logical_apply (D : NativeSparseBlockEncoding.Data X n Z s)
    (γ : ℝ) (x : X) (v : LogicalSpace n) (a : n × n) :
    logical D γ x v a = ExactEdgeCayley.action ((γ : ℂ) * D.matrix x a.1 a.2) (v a) := rfl

omit [Fintype Z] [AddCommGroup Z] in
/-- The valid decoder promise identifies the selected gate with the matrix gate. -/
theorem logical_eq_lookup (D : NativeSparseBlockEncoding.Data X n Z s)
    (γ : ℝ) (x : X) :
    logical D γ x = LookupControlledGate.logical (gates D γ) D.table x := by
  ext v a
  rcases a with ⟨i,j⟩
  simp only [logical_apply, LookupControlledGate.logical_apply, gates, D.decoded]

omit [Fintype Z] [AddCommGroup Z] in
/-- This direct-sum family is unitary for all input instances. -/
theorem logical_unitary (D : NativeSparseBlockEncoding.Data X n Z s)
    (γ : ℝ) (x : X) : IsUnitary (logical D γ x) := by
  rw [logical_eq_lookup]
  exact LookupControlledGate.logical_unitary (gates D γ) (gates_unitary D γ) D.table x

/-- The ordinary additive value oracle, with the edge orientation as spectator. -/
def oracle (D : NativeSparseBlockEncoding.Data X n Z s) :
    X → Space n Z →L[ℂ] Space n Z :=
  LookupControlledGate.oracle D.table

/-- Explicit compute, decoded edge Cayley, and uncompute program. -/
def program (D : NativeSparseBlockEncoding.Data X n Z s) (γ : ℝ) :
    OracleCircuit.Program (oracle D) :=
  LookupControlledGate.program (gates D γ) (gates_unitary D γ) D.table

/-- The actual syntax has exactly two value calls, including the inverse call. -/
@[simp] theorem program_count (D : NativeSparseBlockEncoding.Data X n Z s) (γ : ℝ) :
    (program D γ).count = 2 := rfl

/-- The entire physical program is unitary, including dirty scratch inputs. -/
theorem program_unitary (D : NativeSparseBlockEncoding.Data X n Z s)
    (γ : ℝ) (x : X) : IsUnitary ((program D γ).eval x) :=
  (program D γ).eval_unitary (LookupControlledGate.oracle_unitary D.table) x

variable [DecidableEq Z]

/-- Fixed isometric embedding with a zero value register. -/
def clean : LogicalSpace n →ₗᵢ[ℂ] Space n Z :=
  CleanValueEmbedding.embedding (I := n × n) (K := ExactEdgeCayley.Qubit) (0 : Z)

omit [DecidableEq n] in
@[simp] theorem clean_apply (v : LogicalSpace n) (a : n × n) (z : Z) :
    clean v (a,z) = if z = 0 then v a else 0 :=
  CleanValueEmbedding.embedding_apply (0 : Z) v a z

/-- Exact coherent operator identity on the whole clean value subspace. -/
theorem program_intertwines (D : NativeSparseBlockEncoding.Data X n Z s)
    (γ : ℝ) (x : X) :
    (program D γ).eval x ∘L (clean (n := n) (Z := Z)).toContinuousLinearMap =
      clean.toContinuousLinearMap ∘L logical D γ x := by
  rw [logical_eq_lookup]
  exact LookupControlledGate.program_intertwines
    (gates D γ) (gates_unitary D γ) D.table x

/-- All matrix-address amplitudes receive exactly their prescribed Cayley gate;
the zero value scratch state is restored. -/
theorem program_clean_apply (D : NativeSparseBlockEncoding.Data X n Z s)
    (γ : ℝ) (x : X) (v : LogicalSpace n) (a : n × n) (z : Z) :
    (program D γ).eval x (clean v) (a,z) =
      if z = 0 then ExactEdgeCayley.action ((γ : ℂ) * D.matrix x a.1 a.2) (v a) else 0 := by
  have h := congrArg
    (fun F : LogicalSpace n →L[ℂ] Space n Z => F v (a,z))
    (program_intertwines D γ x)
  simpa only [comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    clean_apply, logical_apply] using h

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- Zero-valued padded addresses receive phase minus one, without requiring
matching row and column locator padding. -/
theorem logical_zero_entry (D : NativeSparseBlockEncoding.Data X n Z s)
    (γ : ℝ) (x : X) (v : LogicalSpace n) (i j : n) (hij : D.matrix x i j = 0) :
    logical D γ x v (i,j) = -(v (i,j)) := by
  simp [logical_apply, hij, ExactEdgeCayley.action_zero]

/-- A precise implementation certificate, with no hidden precision query cost. -/
theorem implementsOn (D : NativeSparseBlockEncoding.Data X n Z s) (γ : ℝ) :
    EncodedOracle.ImplementsOn (oracle D) (logical D γ)
      (clean (n := n) (Z := Z)).toContinuousLinearMap 2 :=
  ⟨program D γ, program_intertwines D γ, by rw [program_count]⟩

/-- The inverse exact edge action also takes exactly two value queries. -/
theorem adjoint_program_intertwines (D : NativeSparseBlockEncoding.Data X n Z s)
    (γ : ℝ) (x : X) :
    (program D γ).adjoint.eval x ∘L (clean (n := n) (Z := Z)).toContinuousLinearMap =
      clean.toContinuousLinearMap ∘L (logical D γ x)† := by
  rw [OracleCircuit.Program.eval_adjoint]
  exact EncodedOracle.adjoint_intertwines _ _ _
    (program_unitary D γ x) (logical_unitary D γ x) (program_intertwines D γ x)

omit [DecidableEq Z] in
@[simp] theorem adjoint_program_count
    (D : NativeSparseBlockEncoding.Data X n Z s) (γ : ℝ) :
    (program D γ).adjoint.count = 2 := by
  rw [OracleCircuit.Program.count_adjoint, program_count]

/-- The same program in the existing native location/value vocabulary.
Embedding names each value call separately; it grants no controlled oracle. -/
def nativeProgram (D : NativeSparseBlockEncoding.Data X n Z s) (γ : ℝ) :
    MultiOracleCircuit.Program (SparseSlotPreparation.oracles D.rowOracle D.table) :=
  MultiOracleCircuit.Program.embed .value (program D γ)

omit [DecidableEq Z] in
@[simp] theorem nativeProgram_count
    (D : NativeSparseBlockEncoding.Data X n Z s) (γ : ℝ) :
    (nativeProgram D γ).count = 2 := rfl

omit [DecidableEq Z] in
@[simp] theorem nativeProgram_value_count
    (D : NativeSparseBlockEncoding.Data X n Z s) (γ : ℝ) :
    (nativeProgram D γ).labelCount .value = 2 := rfl

omit [DecidableEq Z] in
@[simp] theorem nativeProgram_location_count
    (D : NativeSparseBlockEncoding.Data X n Z s) (γ : ℝ) :
    (nativeProgram D γ).labelCount .location = 0 := rfl

omit [DecidableEq Z] in
/-- A weighted primitive count suitable for later oracle substitution. -/
theorem nativeProgram_cost (D : NativeSparseBlockEncoding.Data X n Z s) (γ : ℝ)
    (w : SparseSlotPreparation.Query → ℕ) :
    (nativeProgram D γ).cost w = 2 * w .value := by
  change w .value + (0 + w .value) = 2 * w .value
  omega

/-- The common native workspace program has the same exact clean action. -/
theorem nativeProgram_intertwines (D : NativeSparseBlockEncoding.Data X n Z s)
    (γ : ℝ) (x : X) :
    (nativeProgram D γ).eval x ∘L (clean (n := n) (Z := Z)).toContinuousLinearMap =
      clean.toContinuousLinearMap ∘L logical D γ x := by
  rw [nativeProgram, MultiOracleCircuit.Program.eval_embed]
  exact program_intertwines D γ x

end
end SparseHamiltonian.ExactEdgeValueQuery
