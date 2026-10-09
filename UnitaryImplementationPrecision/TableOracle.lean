import UnitaryImplementationPrecision.Table

/-!
# Entry-only oracle for an inexact entry table

The physical oracle of a table is built exactly as the released one
(`UnitaryEntryOracle.oracle`): one ordinary reversible call of the original table, with the two
block flags and all simulator registers as spectators (`Table.flatEntry_eq_original`). The
compiler `Table.compile` turns a program over the native labels of `Table.toNative` into a
program over this single oracle: the known locators become the released fixed gates
`UnitaryEntryOracle.rowBase` and `UnitaryEntryOracle.columnBase`, and each value query becomes
one entry query between the released fixed routing gates `UnitaryEntryOracle.route`
(`Table.value_routing`). The whole physical operator is preserved (`Table.compile_eval`), and
the count is the number of value queries (`Table.compile_count`). For released data the
physical oracle, the compiled letters and the compiler are the released ones
(`Table.oracle_ofData`, `Table.letter_ofData`, `Table.compile_ofData`, all by `rfl`).
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option synthInstance.maxSize 8192

namespace SparseHamiltonian.UnitaryPrecision

noncomputable section
open ContinuousLinearMap OracleCircuit UnitaryEntryOracle
open NativeSparseBlockEncoding (Query)
open UnitaryEntryData (Index)
open scoped InnerProduct

namespace Table

variable {X n Z : Type*} [Fintype n] [DecidableEq n]
  [Fintype Z] [DecidableEq Z] [AddCommGroup Z]

/-- The plain entry query ignores the two Boolean flags. -/
def plainTable (T : Table X n Z) (x : X) (a : Index n × Index n) : Z :=
  T.table x (a.1.2, a.2.2)

/-- One ordinary call of the table, in the released flat coordinates. -/
def flatEntry (T : Table X n Z) (x : X) :
    EuclideanSpace ℂ (Base n Z) →L[ℂ] EuclideanSpace ℂ (Base n Z) :=
  (NativeSparseMaskedAccess.layout (n := Index n) (Z := Z)).conjStarAlgEquiv
    (LookupControlledGate.oracle (K := SparseFlagEmbedding.Qutrit) (plainTable T) x)

omit [DecidableEq n] [DecidableEq Z] in
/-- For released data this is the released entry call. -/
theorem flatEntry_ofData (D : UnitaryEntryData.Data X n Z) (x : X) :
    flatEntry (ofData D) x = UnitaryEntryOracle.flatEntry D x := rfl

omit [DecidableEq n] [DecidableEq Z] in
/-- The only unknown primitive is one call to the original table, with untouched spectator
registers, on the entire space. -/
theorem flatEntry_eq_original (T : Table X n Z) (x : X) :
    flatEntry T x =
      (LookupOracle.permutationUnitary (entryBasis (n := n) (Z := Z))).symm.conjStarAlgEquiv
        ((LookupOracle.permutationUnitary
          (LookupOracle.spectatorEquiv ((Bool × Bool) × Fin 3) T.table x)
            ).toLinearIsometry.toContinuousLinearMap) := by
  ext v a
  rcases a with ⟨⟨⟨⟨b, i⟩, ⟨c, j⟩⟩, z⟩, f⟩
  rfl

omit [DecidableEq n] [DecidableEq Z] in
/-- The table call is unitary on the entire flat workspace. -/
theorem flatEntry_unitary (T : Table X n Z) (x : X) : IsUnitary (flatEntry T x) :=
  (LookupControlledGate.oracle_unitary (K := SparseFlagEmbedding.Qutrit)
    (plainTable T) x).transport NativeSparseMaskedAccess.layout

section Native
variable [Nonempty n]

omit [DecidableEq Z] in
/-- One table call and two fixed routing gates implement the value oracle of the dilation on
its entire workspace. -/
theorem value_routing (T : Table X n Z) (x : X) :
    NativeSparseMaskedAccess.flatOracle (toNative T) .value x =
      route * (flatEntry T x * route) := by
  ext v a
  rcases a with ⟨⟨⟨⟨b, i⟩, ⟨c, j⟩⟩, z⟩, f⟩
  cases b <;> rfl

omit [DecidableEq Z] in
/-- The row locator of the dilation is the released fixed gate `UnitaryEntryOracle.rowBase`. -/
@[simp] theorem flat_row (T : Table X n Z) (x : X) :
    NativeSparseMaskedAccess.flatOracle (toNative T) .rowLocation x = rowBase := rfl

omit [DecidableEq Z] in
/-- The column locator of the dilation is the released fixed gate
`UnitaryEntryOracle.columnBase`. -/
@[simp] theorem flat_column (T : Table X n Z) (x : X) :
    NativeSparseMaskedAccess.flatOracle (toNative T) .columnLocation x = columnBase := rfl

end Native

/-- The table call with the simulator's spectators (the released `UnitaryEntryOracle.lift`). -/
def oracle (T : Table X n Z) (γ η t ε : ℝ) (x : X) :
    UnitaryEntryOracle.Physical n Z γ η t ε →L[ℂ] UnitaryEntryOracle.Physical n Z γ η t ε :=
  lift γ η t ε (flatEntry T x)

omit [DecidableEq n] [DecidableEq Z] in
/-- The physical table oracle is unitary on the entire workspace. -/
theorem oracle_unitary (T : Table X n Z) (γ η t ε : ℝ) (x : X) :
    IsUnitary (oracle T γ η t ε x) :=
  lift_unitary γ η t ε _ (flatEntry_unitary T x)

omit [DecidableEq n] [DecidableEq Z] in
/-- For released data this is the released physical oracle. -/
theorem oracle_ofData (D : UnitaryEntryData.Data X n Z) (γ η t ε : ℝ) :
    oracle (ofData D) γ η t ε = UnitaryEntryOracle.oracle D γ η t ε := rfl

section Compile
variable [Nonempty n]

/-- The simulator labels of the table's native interface, with the alignment spectator. -/
abbrev nativeOracle (T : Table X n Z) (γ η t ε : ℝ) :=
  AlignedMultiOracleProgram.oracle (ImprovedSparseHamiltonian.oracle (toNative T) γ η t ε)

omit [DecidableEq Z] in
/-- The released simulator lifts each native primitive through the same spectators. -/
theorem nativeOracle_eq (T : Table X n Z) (γ η t ε : ℝ) (l : Query) (x : X) :
    nativeOracle T γ η t ε l x =
      lift γ η t ε (NativeSparseMaskedAccess.flatOracle (toNative T) l x) := rfl

/-- Known locators become fixed gates; a value query is one table call between fixed routing
gates. -/
def letter (T : Table X n Z) (γ η t ε : ℝ) : Query → OracleCircuit.Program (oracle T γ η t ε)
  | .rowLocation => .fixed (lift γ η t ε rowBase) (lift_unitary γ η t ε _ rowBase_unitary)
  | .columnLocation => .fixed (lift γ η t ε columnBase)
      (lift_unitary γ η t ε _ columnBase_unitary)
  | .value => .seq (.fixed (lift γ η t ε route) (lift_unitary γ η t ε _ route_unitary))
      (.seq .query (.fixed (lift γ η t ε route) (lift_unitary γ η t ε _ route_unitary)))

omit [DecidableEq Z] in
/-- Each compiled letter implements its native primitive exactly, on the whole workspace. -/
theorem letter_eval (T : Table X n Z) (γ η t ε : ℝ) (l : Query) (x : X) :
    (letter T γ η t ε l).eval x = nativeOracle T γ η t ε l x := by
  rw [nativeOracle_eq]
  cases l
  · rfl
  · rfl
  · change lift γ η t ε route * (lift γ η t ε (flatEntry T x) * lift γ η t ε route) = _
    rw [← lift_mul, ← lift_mul, ← value_routing]

/-- Exact compilation of a native-label program to table queries. -/
def compile (T : Table X n Z) (γ η t ε : ℝ)
    (p : MultiOracleCircuit.Program (nativeOracle T γ η t ε)) :
    OracleCircuit.Program (oracle T γ η t ε) :=
  p.compile (letter T γ η t ε)

omit [DecidableEq Z] in
/-- Compilation preserves the entire physical operator. -/
theorem compile_eval (T : Table X n Z) (γ η t ε : ℝ)
    (p : MultiOracleCircuit.Program (nativeOracle T γ η t ε)) (x : X) :
    (compile T γ η t ε p).eval x = p.eval x :=
  p.eval_compile (letter T γ η t ε) (letter_eval T γ η t ε) x

omit [DecidableEq Z] in
/-- Only the value queries remain, each as one table query. -/
theorem compile_count (T : Table X n Z) (γ η t ε : ℝ)
    (p : MultiOracleCircuit.Program (nativeOracle T γ η t ε)) :
    (compile T γ η t ε p).count = p.labelCount .value := by
  change (p.compile (letter T γ η t ε)).count = _
  rw [MultiOracleCircuit.Program.count_compile]
  unfold MultiOracleCircuit.Program.labelCount
  congr 1
  funext l
  cases l <;> rfl

omit [DecidableEq Z] in
/-- In particular compilation adds no query. -/
theorem compile_count_le (T : Table X n Z) (γ η t ε : ℝ)
    (p : MultiOracleCircuit.Program (nativeOracle T γ η t ε)) :
    (compile T γ η t ε p).count ≤ p.count := by
  change (p.compile (letter T γ η t ε)).count ≤ p.count
  rw [MultiOracleCircuit.Program.count_compile]
  calc
    _ ≤ p.cost (fun _ => 1) := p.cost_mono (by intro l; cases l <;> simp [letter])
    _ = p.count := by simp

omit [DecidableEq n] [DecidableEq Z] [Nonempty n] in
/-- For released data the compiled letters are the released ones. -/
theorem letter_ofData (D : UnitaryEntryData.Data X n Z) (γ η t ε : ℝ) :
    letter (ofData D) γ η t ε = UnitaryEntryOracle.letter D γ η t ε := rfl

omit [DecidableEq Z] in
/-- For released data the compiler is the released one. -/
theorem compile_ofData (D : UnitaryEntryData.Data X n Z) (γ η t ε : ℝ) :
    compile (ofData D) γ η t ε = UnitaryEntryOracle.compile D γ η t ε := rfl

end Compile

end Table

end
end SparseHamiltonian.UnitaryPrecision
