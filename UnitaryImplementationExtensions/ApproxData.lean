import SparseHamiltonian.UnitaryImplementation

set_option autoImplicit false

/-!
# Entry tables that represent a unitary only approximately

Corollary `hs:cor:unitary` of the manuscript (lines 1769-1788) also allows a
reversible entry-value oracle whose represented entries have absolute error at
most `ε/(πN)`; the proof (lines 1814-1831) dilates the represented matrix `Ũ`.
This module records that access model. The oracle is the same ordinary
reversible table with a fixed bounded decoder as in
`SparseHamiltonian.UnitaryEntryData.Data`; the only change is the promise: the
decoded matrix `represented D x` need not be unitary, and a unitary target
`D.target x` is given instead. Exact data is the special case `ofExact`.

The Hermitian dilation `dilation M = [[0, M], [M†, 0]]` is the matrix of
`UnitaryEntryData.dilationMatrix` (`dilationMatrix_eq`). The dilation of the
represented matrix is supplied to the released native interface by `toNative`,
with the same fixed locators `UnitaryEntryData.loc`, row and column oracles and
`card n` slots as `UnitaryEntryData.toNative`. The target is packaged as exact
entry data `targetData` (with the instance itself as its table value), so that
the released dilation identities apply to it unchanged; this package is used
only for statements about the target, never as an oracle.

The native interface (`dilationTable`, `dilationDecode`, `toNative` and their
lemmas) restates `UnitaryEntryData.toNative` for a represented matrix that need
not be unitary, since the released interface is typed on exact unitary data;
the oracle itself is the released one (`ApproxOracle.oracle_ofExact`), and for
exact data the restated interface agrees with the released one
(`dilationTable_ofExact`, `dilationDecode_ofExact`, `toNative_ofExact_matrix`).
-/

namespace UnitaryImplementationExtensions.ApproxData

noncomputable section
open SparseHamiltonian
open ContinuousLinearMap OracleCircuit UnitaryEntryData
open scoped BigOperators InnerProduct
set_option maxRecDepth 4096
set_option synthInstance.maxSize 4096

/-- A reversible entry table with a fixed bounded decoder, together with the
unitary family that the decoded entries approximate. The decoder is fixed
independently of the instance; the entry error is a hypothesis of the theorems
that use the data. -/
structure Data (X n Z : Type*) [Fintype n] where
  /-- The unitary to be implemented. -/
  target : X → Matrix n n ℂ
  /-- The target is unitary for every instance. -/
  target_unitary : ∀ x, IsUnitary (SparseStateOverlap.matrixOperator (target x))
  /-- The value table supplied by the reversible entry oracle. -/
  table : X → (n × n) → Z
  /-- The fixed decoder of table values. -/
  decode : (n × n) → Z → ℂ
  /-- A fixed bound on every decoded value. -/
  scale : ℝ
  /-- The decoder bound is positive. -/
  scale_pos : 0 < scale
  /-- Every decoded value is bounded by `scale`. -/
  decode_bound : ∀ a z, ‖decode a z‖ ≤ scale

variable {X n Z : Type*} [Fintype n]

/-- The matrix exactly represented by the oracle, entry by entry. -/
def represented (D : Data X n Z) (x : X) : Matrix n n ℂ :=
  fun i j => D.decode (i, j) (D.table x (i, j))

/-- Exact unitary entry data is approximate data with the same table and decoder. -/
def ofExact (D : UnitaryEntryData.Data X n Z) : Data X n Z where
  target := D.matrix
  target_unitary := D.unitary
  table := D.table
  decode := D.decode
  scale := D.scale
  scale_pos := D.scale_pos
  decode_bound := D.decode_bound

/-- For exact data the represented matrix is the unitary itself. -/
theorem ofExact_represented (D : UnitaryEntryData.Data X n Z) :
    represented (ofExact D) = D.matrix := by
  funext x i j
  exact D.decoded x i j

/-- Entries of a unitary matrix have modulus at most one. -/
theorem target_entry_le_one (D : Data X n Z) (x : X) (i j : n) :
    ‖D.target x i j‖ ≤ 1 := by
  exact SparseHamiltonian.norm_le_of_energy_le 1 (fun k => D.target x k j) zero_le_one
    (SparseSpectralEnergy.column_energy_le (D.target x) 1
      (D.target_unitary x).norm_le_one j) i

/-- The target family as exact entry data. Its table value is the instance
itself; it is used only to apply the released dilation identities to the
target, never as an oracle. -/
def targetData (D : Data X n Z) : UnitaryEntryData.Data X n X where
  matrix := D.target
  unitary := D.target_unitary
  table := fun x _ => x
  decode := fun a x => D.target x a.1 a.2
  scale := 1
  scale_pos := one_pos
  decode_bound := fun a x => target_entry_le_one D x a.1 a.2
  decoded := fun _ _ _ => rfl

/-- The Boolean Hermitian dilation `[[0, M], [M†, 0]]` of a square matrix. -/
def dilation (M : Matrix n n ℂ) : Matrix (Index n) (Index n) ℂ :=
  fun i j => if i.1 = j.1 then 0 else if i.1 then star (M j.2 i.2) else M i.2 j.2

/-- The released dilation of exact entry data is `dilation` of its matrix. -/
theorem dilationMatrix_eq {Y W : Type*} (D : UnitaryEntryData.Data Y n W) (y : Y) :
    UnitaryEntryData.dilationMatrix D y = dilation (D.matrix y) :=
  rfl

/-- The dilation of the target is the released dilation of `targetData`. -/
theorem target_dilation_eq (D : Data X n Z) (x : X) :
    dilation (D.target x) = UnitaryEntryData.dilationMatrix (targetData D) x :=
  rfl

omit [Fintype n] in
/-- Every dilation is Hermitian. -/
theorem dilation_hermitian (M : Matrix n n ℂ) : (dilation M).IsHermitian := by
  apply Matrix.IsHermitian.ext
  rintro ⟨b, i⟩ ⟨c, j⟩
  cases b <;> cases c <;> simp [dilation]

omit [Fintype n] in
/-- The dilation is additive. -/
theorem dilation_sub (A B : Matrix n n ℂ) :
    dilation A - dilation B = dilation (A - B) := by
  ext ⟨b, i⟩ ⟨c, j⟩
  cases b <;> cases c <;> simp [dilation]

/-- All addresses use an unconditional original entry lookup. -/
def dilationTable (D : Data X n Z) (x : X) (a : Index n × Index n) : Z :=
  D.table x (address a)

/-- Conjugation and diagonal suppression belong to a fixed decoder. -/
def dilationDecode (D : Data X n Z) (a : Index n × Index n) (z : Z) : ℂ :=
  if a.1.1 = a.2.1 then 0 else if a.1.1 then star (D.decode (address a) z)
    else D.decode (address a) z

/-- The fixed decoder keeps the bound of the original decoder. -/
theorem dilationDecode_bound (D : Data X n Z) (a : Index n × Index n) (z : Z) :
    ‖dilationDecode D a z‖ ≤ D.scale := by
  unfold dilationDecode
  split
  · simpa using D.scale_pos.le
  · split
    · simpa only [norm_star] using D.decode_bound (address a) z
    · exact D.decode_bound (address a) z

/-- The dilated table decodes exactly to the dilation of the represented matrix. -/
theorem dilationDecoded (D : Data X n Z) (x : X) (i j : Index n) :
    dilationDecode D (i, j) (dilationTable D x (i, j)) =
      dilation (represented D x) i j := by
  rcases i with ⟨b, i⟩
  rcases j with ⟨c, j⟩
  cases b <;> cases c <;>
    simp [dilationDecode, dilationTable, address, dilation, represented]

/-- For exact data the dilated table is the released one. -/
theorem dilationTable_ofExact (D : UnitaryEntryData.Data X n Z) :
    dilationTable (ofExact D) = UnitaryEntryData.dilationTable D :=
  rfl

/-- For exact data the dilated decoder is the released one. -/
theorem dilationDecode_ofExact (D : UnitaryEntryData.Data X n Z) :
    dilationDecode (ofExact D) = UnitaryEntryData.dilationDecode D :=
  rfl

section Native
variable [DecidableEq n] [Nonempty n]

omit [Nonempty n] in
/-- The fixed locators enumerate the whole opposite block. -/
theorem row_covers (D : Data X n Z) (x : X) (i j : Index n)
    (h : dilation (represented D x) i j ≠ 0) : SparseSlotStates.selected loc i j := by
  have hflag : i.1 ≠ j.1 := by
    intro hij
    exact h (by simp [dilation, hij])
  have hloc : loc i ((Fintype.equivFin n) j.2) = j := by
    rcases i with ⟨b, i⟩
    rcases j with ⟨c, j⟩
    cases b <;> cases c <;> simp_all [loc]
  rw [← hloc]
  exact SparseSlotStates.selected_loc loc i _

/-- The dilation of the represented matrix as released native sparse data with
sparsity `card n`, fixed locators and the original decoder bound. -/
def toNative (D : Data X n Z) :
    NativeSparseBlockEncoding.Data X (Index n) Z (Fintype.card n) where
  slot := slot
  slots_pos := Fintype.card_pos
  scale := D.scale
  scale_pos := D.scale_pos
  matrix := fun x => dilation (represented D x)
  table := dilationTable D
  decode := dilationDecode D
  decode_bound := dilationDecode_bound D
  decoded := dilationDecoded D
  rowloc := fun _ => loc
  colloc := fun _ => loc
  row_injective := fun _ => loc_injective
  column_injective := fun _ => loc_injective
  row_covers := row_covers D
  column_covers := by
    intro x i j h
    apply row_covers D x j i
    intro hji
    have hHerm := (dilation_hermitian (represented D x)).apply i j
    rw [hji, star_zero] at hHerm
    exact h hHerm.symm
  rowOracle := fun _ => rowOracle
  columnOracle := fun _ => columnOracle
  row_unitary := fun _ => rowOracle_unitary
  column_unitary := fun _ => columnOracle_unitary
  row_valid := fun _ => rowOracle_valid
  column_valid := fun _ => columnOracle_valid

/-- The native matrix is the dilation of the represented matrix. -/
@[simp] theorem toNative_matrix (D : Data X n Z) (x : X) :
    (toNative D).matrix x = dilation (represented D x) := rfl

/-- The native table is the dilated table. -/
@[simp] theorem toNative_table (D : Data X n Z) :
    (toNative D).table = dilationTable D := rfl

/-- The native row oracle is the released fixed row locator. -/
@[simp] theorem toNative_rowOracle (D : Data X n Z) (x : X) :
    (toNative D).rowOracle x = rowOracle := rfl

/-- The native column oracle is the released fixed column locator. -/
@[simp] theorem toNative_columnOracle (D : Data X n Z) (x : X) :
    (toNative D).columnOracle x = columnOracle := rfl

/-- For exact data the native matrix is the released dilation. -/
theorem toNative_ofExact_matrix (D : UnitaryEntryData.Data X n Z) :
    (toNative (ofExact D)).matrix = (UnitaryEntryData.toNative D).matrix := by
  funext x
  rw [toNative_matrix, ofExact_represented]
  rfl

end Native
end
end UnitaryImplementationExtensions.ApproxData
