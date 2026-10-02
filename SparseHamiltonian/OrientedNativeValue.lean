import SparseHamiltonian.OrientedNativeLayout

/-!
# Exact edge gates in the common native workspace

A single fixed gate uses the original sparse-entry decoder, with the value
register coherently computed and restored.  The orientation bit is its qubit
payload, and the old three-flag register is a spectator.  The resulting
program has two value calls and no locator calls.  It is uniform in the
unknown matrix instance and uses the common fixed oriented clean encoding.

-/

namespace SparseHamiltonian.OrientedNativeValue

noncomputable section
open ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding
open OrientedNativeLayout SparseEdgeMoments
open scoped InnerProduct
set_option maxHeartbeats 800000
set_option maxRecDepth 2000

variable {X n Z : Type*} [Fintype n] [DecidableEq n]
  [Fintype Z] [AddCommGroup Z] [DecidableEq Z] {s : ℕ}

/-- The edge rotation uses the original decoder and ignores the flag register.
No entry bounds or positivity hypotheses are required for this exact unitary. -/
def gate (D : Data X n Z s) (γ : ℝ) : Space n Z →L[ℂ] Space n Z :=
  (edgeLayout (n := n) (Z := Z)).symm.conjStarAlgEquiv
    (WeightedClock.diagonal (fun a : NativeSparseMaskedAccess.Basis n Z =>
      ExactEdgeCayley.action
        (((γ * Real.sqrt (s : ℝ) : ℝ) : ℂ) * D.decode a.1.1 a.1.2)))

omit [AddCommGroup Z] [DecidableEq Z] in
/-- Every code gives a full unitary, including codes not produced by the oracle. -/
theorem gate_unitary (D : Data X n Z s) (γ : ℝ) : IsUnitary (gate D γ) :=
  (NativeMaskedOracle.diagonal_unitary _
    (fun a : NativeSparseMaskedAccess.Basis n Z =>
      ExactEdgeCayley.action_unitary
        (((γ * Real.sqrt (s : ℝ) : ℝ) : ℂ) * D.decode a.1.1 a.1.2))).transport
    (edgeLayout (n := n) (Z := Z)).symm

omit [AddCommGroup Z] [DecidableEq Z] in
/-- Explicit coordinate action on arbitrary, possibly dirty, scratch registers. -/
@[simp] theorem gate_apply (D : Data X n Z s) (γ : ℝ)
    (v : Space n Z) (b : Bool) (e : n × n) (z : Z) (f : Fin 3) :
    gate D γ v b ((e, z), f) =
      ExactEdgeCayley.action
        (((γ * Real.sqrt (s : ℝ) : ℝ) : ℂ) * D.decode e z)
        (WithLp.toLp 2 (fun c : Bool => v c ((e, z), f))) b := rfl

/-- Literal compute, rotate, uncompute with a fixed native value label. -/
def program (D : Data X n Z s) (γ : ℝ) :
    MultiOracleCircuit.Program (logicalOracle D) :=
  .seq (.queryAdjoint .value)
    (.seq (.fixed (gate D γ) (gate_unitary D γ)) (.query .value))

omit [DecidableEq Z] in
@[simp] theorem program_count (D : Data X n Z s) (γ : ℝ) :
    (program D γ).count = 2 := rfl

omit [DecidableEq Z] in
/-- Separate costs show that neither locator is used in the edge program. -/
@[simp] theorem program_cost (D : Data X n Z s) (γ : ℝ) (w : Query → ℕ) :
    (program D γ).cost w = 2 * w .value := by
  change w .value + (0 + w .value) = 2 * w .value
  omega

omit [DecidableEq Z] in
@[simp] theorem program_row_count (D : Data X n Z s) (γ : ℝ) :
    (program D γ).labelCount .rowLocation = 0 := rfl

omit [DecidableEq Z] in
@[simp] theorem program_column_count (D : Data X n Z s) (γ : ℝ) :
    (program D γ).labelCount .columnLocation = 0 := rfl

omit [DecidableEq Z] in
@[simp] theorem program_value_count (D : Data X n Z s) (γ : ℝ) :
    (program D γ).labelCount .value = 2 := rfl

/-- Forward lookup makes one two-component orientation slice at each address.
The slice is zero unless both scratch registers have their computed values. -/
theorem computed_slice (D : Data X n Z s) (x : X) (v : OrientedSpace n)
    (e : n × n) (z : Z) (f : Fin 3) :
    WithLp.toLp 2 (fun b : Bool =>
      logicalOracle D .value x (clean v) b ((e, z), f)) =
      if z - D.table x e = 0 ∧ f = 0 then
        OrientedEdgeCayley.regroup v e else (0 : ExactEdgeCayley.Qubit) := by
  ext b
  change logicalOracle D .value x (clean v) b ((e, z), f) = _
  rw [logical_value_apply, clean_apply]
  by_cases h : z - D.table x e = 0 ∧ f = 0
  · rw [if_pos h, if_pos h]
    cases b <;> rfl
  · rw [if_neg h, if_neg h]
    rfl

/-- Before uncomputation, the gate changes only the oriented payload.  This
identity includes all addresses and retains the computed value exactly. -/
theorem computed_intertwines (D : Data X n Z s) (γ : ℝ) (x : X) :
    gate D γ ∘L logicalOracle D .value x ∘L
        (clean (n := n) (Z := Z)).toContinuousLinearMap =
      logicalOracle D .value x ∘L clean.toContinuousLinearMap ∘L
        OrientedEdgeCayley.action (D.matrix x) s γ := by
  ext v b a
  rcases a with ⟨⟨e, z⟩, f⟩
  change gate D γ (logicalOracle D .value x (clean v)) b ((e,z),f) =
    logicalOracle D .value x
      (clean (OrientedEdgeCayley.action (D.matrix x) s γ v)) b ((e,z),f)
  rw [gate_apply, computed_slice, logical_value_apply, clean_apply]
  by_cases h : z - D.table x e = 0 ∧ f = 0
  · rw [if_pos h, if_pos h]
    have hz : z = D.table x e := sub_eq_zero.mp h.1
    rw [hz, D.decoded]
    cases b <;> rfl
  · rw [if_neg h, if_neg h, map_zero]
    rfl

/-- Exact full clean-output semantics of the two native value calls. -/
theorem program_intertwines (D : Data X n Z s) (γ : ℝ) (x : X) :
    (program D γ).eval x ∘L
        (clean (n := n) (Z := Z)).toContinuousLinearMap =
      clean.toContinuousLinearMap ∘L
        OrientedEdgeCayley.action (D.matrix x) s γ := by
  apply ContinuousLinearMap.ext
  intro v
  have h := congrArg
    (fun T : OrientedSpace n →L[ℂ] Space n Z => T v)
    (computed_intertwines D γ x)
  change gate D γ (logicalOracle D .value x (clean v)) =
    logicalOracle D .value x
      (clean (OrientedEdgeCayley.action (D.matrix x) s γ v)) at h
  change ((logicalOracle D .value x)†)
      (gate D γ (logicalOracle D .value x (clean v))) =
    clean (OrientedEdgeCayley.action (D.matrix x) s γ v)
  rw [h]
  have hunit : (logicalOracle D .value x)† ∘L logicalOracle D .value x = 1 :=
    (logicalOracle_unitary D .value x).1
  have hcancel := congrArg (fun T : Space n Z →L[ℂ] Space n Z =>
    T (clean (OrientedEdgeCayley.action (D.matrix x) s γ v))) hunit
  exact hcancel

omit [DecidableEq Z] in
/-- The program remains unitary on the entire common workspace. -/
theorem program_unitary (D : Data X n Z s) (γ : ℝ) (x : X) :
    IsUnitary ((program D γ).eval x) :=
  (program D γ).eval_unitary (logicalOracle_unitary D) x

end
end SparseHamiltonian.OrientedNativeValue
