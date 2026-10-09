import UnitaryImplementationExtensions.ApproxData

set_option autoImplicit false

/-!
# Entry-only oracle reduction for approximately represented unitaries

The same reduction as `SparseHamiltonian.UnitaryEntryOracle`, for the access
model of `ApproxData.Data` (corollary `hs:cor:unitary` of the manuscript, lines
1769-1788). The only unknown primitive is one ordinary reversible entry query of
the original table, lifted by the released spectator map
`UnitaryEntryOracle.lift`; the known row and column locators become fixed gates
(`UnitaryEntryOracle.rowBase`, `UnitaryEntryOracle.columnBase`) and the value
query of the dilation is one entry query between two fixed routing gates
(`UnitaryEntryOracle.route`). For exact data the oracle is the released one
(`oracle_ofExact`). The reduction is restated here because the released one is
typed on exact unitary data.
-/

namespace UnitaryImplementationExtensions.ApproxOracle

noncomputable section
open SparseHamiltonian
open ContinuousLinearMap OracleCircuit UnitaryEntryData UnitaryEntryOracle
open NativeSparseBlockEncoding (Query)
open scoped InnerProduct
set_option maxRecDepth 8192
set_option synthInstance.maxSize 8192

variable {X n Z : Type*} [Fintype n] [DecidableEq n]
  [Fintype Z] [DecidableEq Z] [AddCommGroup Z]

/-- The plain entry query ignores the two Boolean flags. -/
def plainTable (D : ApproxData.Data X n Z) (x : X) (a : Index n × Index n) : Z :=
  D.table x (a.1.2, a.2.2)

/-- One ordinary entry call, in the released flat coordinates. -/
def flatEntry (D : ApproxData.Data X n Z) (x : X) :
    EuclideanSpace ℂ (Base n Z) →L[ℂ] EuclideanSpace ℂ (Base n Z) :=
  (NativeSparseMaskedAccess.layout (n := Index n) (Z := Z)).conjStarAlgEquiv
    (LookupControlledGate.oracle (K := SparseFlagEmbedding.Qutrit) (plainTable D) x)

omit [DecidableEq n] [DecidableEq Z] in
/-- One entry call is unitary. -/
theorem flatEntry_unitary (D : ApproxData.Data X n Z) (x : X) :
    IsUnitary (flatEntry D x) :=
  (LookupControlledGate.oracle_unitary (K := SparseFlagEmbedding.Qutrit)
    (plainTable D) x).transport NativeSparseMaskedAccess.layout

/-- One ordinary original-entry oracle with the simulator's spectators. -/
def oracle (D : ApproxData.Data X n Z) (γ η t ε : ℝ) (x : X) :
    UnitaryEntryOracle.Physical n Z γ η t ε →L[ℂ] UnitaryEntryOracle.Physical n Z γ η t ε :=
  lift γ η t ε (flatEntry D x)

omit [DecidableEq n] [DecidableEq Z] in
/-- The lifted entry oracle is unitary. -/
theorem oracle_unitary (D : ApproxData.Data X n Z) (γ η t ε : ℝ) (x : X) :
    IsUnitary (oracle D γ η t ε x) :=
  lift_unitary γ η t ε _ (flatEntry_unitary D x)

omit [DecidableEq n] [DecidableEq Z] in
/-- For exact data this is the released entry oracle. -/
theorem oracle_ofExact (D : UnitaryEntryData.Data X n Z) (γ η t ε : ℝ) :
    oracle (ApproxData.ofExact D) γ η t ε = UnitaryEntryOracle.oracle D γ η t ε :=
  rfl

section Compile
variable [Nonempty n]

/-- The released simulator labels for the dilation of the represented matrix,
including the final clean-output alignment. -/
abbrev nativeOracle (D : ApproxData.Data X n Z) (γ η t ε : ℝ) :=
  AlignedMultiOracleProgram.oracle
    (ImprovedSparseHamiltonian.oracle (ApproxData.toNative D) γ η t ε)

omit [DecidableEq Z] in
/-- The released simulator lifts each primitive by the same spectator map. -/
theorem nativeOracle_eq (D : ApproxData.Data X n Z) (γ η t ε : ℝ) (l : Query) (x : X) :
    nativeOracle D γ η t ε l x =
      lift γ η t ε (NativeSparseMaskedAccess.flatOracle (ApproxData.toNative D) l x) :=
  rfl

omit [DecidableEq Z] in
/-- One original lookup and two fixed routing gates implement the dilation
value oracle on its entire workspace. -/
theorem value_routing (D : ApproxData.Data X n Z) (x : X) :
    NativeSparseMaskedAccess.flatOracle (ApproxData.toNative D) .value x =
      route * (flatEntry D x * route) := by
  ext v a
  rcases a with ⟨⟨⟨⟨b, i⟩, ⟨c, j⟩⟩, z⟩, f⟩
  cases b <;> rfl

omit [DecidableEq Z] in
/-- The row-location primitive of the dilation is the fixed row base gate. -/
@[simp] theorem flat_row (D : ApproxData.Data X n Z) (x : X) :
    NativeSparseMaskedAccess.flatOracle (ApproxData.toNative D) .rowLocation x = rowBase :=
  rfl

omit [DecidableEq Z] in
/-- The column-location primitive of the dilation is the fixed column base gate. -/
@[simp] theorem flat_column (D : ApproxData.Data X n Z) (x : X) :
    NativeSparseMaskedAccess.flatOracle (ApproxData.toNative D) .columnLocation x =
      columnBase :=
  rfl

/-- Known locators become fixed gates; a value query is one entry query between
two fixed routing gates. -/
def letter (D : ApproxData.Data X n Z) (γ η t ε : ℝ) :
    Query → OracleCircuit.Program (oracle D γ η t ε)
  | .rowLocation => .fixed (lift γ η t ε rowBase)
      (lift_unitary γ η t ε _ rowBase_unitary)
  | .columnLocation => .fixed (lift γ η t ε columnBase)
      (lift_unitary γ η t ε _ columnBase_unitary)
  | .value => .seq (.fixed (lift γ η t ε route)
        (lift_unitary γ η t ε _ route_unitary))
      (.seq .query (.fixed (lift γ η t ε route)
        (lift_unitary γ η t ε _ route_unitary)))

omit [DecidableEq Z] in
/-- Each compiled letter is the corresponding released native primitive. -/
theorem letter_eval (D : ApproxData.Data X n Z) (γ η t ε : ℝ) (l : Query) (x : X) :
    (letter D γ η t ε l).eval x = nativeOracle D γ η t ε l x := by
  rw [nativeOracle_eq]
  cases l
  · rfl
  · rfl
  · change lift γ η t ε route *
      (lift γ η t ε (flatEntry D x) * lift γ η t ε route) = _
    rw [← lift_mul, ← lift_mul, ← value_routing]

/-- Exact compilation of a native program to original-entry queries. -/
def compile (D : ApproxData.Data X n Z) (γ η t ε : ℝ)
    (p : MultiOracleCircuit.Program (nativeOracle D γ η t ε)) :
    OracleCircuit.Program (oracle D γ η t ε) :=
  p.compile (letter D γ η t ε)

omit [DecidableEq Z] in
/-- Compilation preserves the whole physical operator. -/
theorem compile_eval (D : ApproxData.Data X n Z) (γ η t ε : ℝ)
    (p : MultiOracleCircuit.Program (nativeOracle D γ η t ε)) (x : X) :
    (compile D γ η t ε p).eval x = p.eval x :=
  p.eval_compile (letter D γ η t ε) (letter_eval D γ η t ε) x

omit [DecidableEq Z] in
/-- Compilation does not increase the query count. -/
theorem compile_count_le (D : ApproxData.Data X n Z) (γ η t ε : ℝ)
    (p : MultiOracleCircuit.Program (nativeOracle D γ η t ε)) :
    (compile D γ η t ε p).count ≤ p.count := by
  change (p.compile (letter D γ η t ε)).count ≤ p.count
  rw [MultiOracleCircuit.Program.count_compile]
  calc
    _ ≤ p.cost (fun _ => 1) := p.cost_mono (by
      intro l
      cases l
      · exact Nat.zero_le 1
      · exact Nat.zero_le 1
      · exact le_refl 1)
    _ = p.count := by simp

end Compile
end
end UnitaryImplementationExtensions.ApproxOracle
