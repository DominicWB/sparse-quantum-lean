import SparseHamiltonian.UnitaryImplementation
import UnitaryImplementationPrecision.Budget

/-!
# Inexact entry tables and the dilation of the represented matrix

The released entry model `UnitaryEntryData.Data` is an ordinary reversible entry table with a
fixed bounded decoder, together with the promise that the represented (decoded) matrix is
unitary. An inexact entry oracle is the same kind of object without that promise: `Table`
has exactly the other fields, and its represented matrix `Ũ = T.matrix x` may be any matrix
(`Table.ofData` forgets the promise of released data). For a table, the dilation
`H̃_U = [[0, Ũ], [Ũ†, 0]]` (`Table.dilationMatrix`), its table (`Table.dilationTable`) and
decoder (`Table.dilationDecode`) use the formulas of `UnitaryEntryData.dilationMatrix`,
`UnitaryEntryData.dilationTable` and `UnitaryEntryData.dilationDecode`, and `Table.toNative`
uses the released known locators (`UnitaryEntryData.slot`, `UnitaryEntryData.loc`,
`UnitaryEntryData.rowOracle`, `UnitaryEntryData.columnOracle`). For released data all of these
are the released objects (`Table.ofData_dilationMatrix`, `Table.toNative_ofData`, by `rfl`).

The intended unitary `U` is not queried. To apply the released dilation lemmas to `H_U`,
`exactData U hU` presents a unitary family as released data whose table is the instance itself
(a ghost table, never queried).

Under the entrywise promise `|Ũ_ij - U_ij| ≤ ξ` with `N ξ² ≤ 1`, `H̃_U` obeys the row and
column norm promises of Theorem `hs:thm:main` with `η = 2` (`Table.dilation_row_energy_two`,
`Table.dilation_column_energy_two`), and `‖H̃_U - H_U‖ ≤ N ξ` (`Table.dilation_sub_norm_le`),
since both dilations vanish on the diagonal blocks: they share the known row and column
locators. Duhamel's bound follows (`Table.dilation_evolution_error_le`).
-/

set_option autoImplicit false

namespace SparseHamiltonian.UnitaryPrecision

noncomputable section
open ContinuousLinearMap OracleCircuit
open scoped BigOperators InnerProduct

/-- An ordinary reversible entry table with a fixed bounded decoder: the fields of the released
`UnitaryEntryData.Data` except its unitarity promise. The represented matrix `matrix x`, the
decoded table entries, may be any matrix; it is the matrix supplied by an inexact entry
oracle. -/
structure Table (X n Z : Type*) where
  matrix : X → Matrix n n ℂ
  table : X → (n × n) → Z
  decode : (n × n) → Z → ℂ
  scale : ℝ
  scale_pos : 0 < scale
  decode_bound : ∀ a z, ‖decode a z‖ ≤ scale
  decoded : ∀ x i j, decode (i, j) (table x (i, j)) = matrix x i j

namespace Table

open UnitaryEntryData (Index address)

variable {X n Z : Type*}

/-- Released exact entry data, with the unitarity promise forgotten. -/
def ofData [Fintype n] (D : UnitaryEntryData.Data X n Z) : Table X n Z where
  matrix := D.matrix
  table := D.table
  decode := D.decode
  scale := D.scale
  scale_pos := D.scale_pos
  decode_bound := D.decode_bound
  decoded := D.decoded

/-- The Boolean Hermitian dilation `[[0, Ũ], [Ũ†, 0]]` of the represented matrix. -/
def dilationMatrix (T : Table X n Z) (x : X) : Matrix (Index n) (Index n) ℂ :=
  fun i j => if i.1 = j.1 then 0 else if i.1 then star (T.matrix x j.2 i.2)
    else T.matrix x i.2 j.2

/-- Every address of the dilation looks up one original table entry. -/
def dilationTable (T : Table X n Z) (x : X) (a : Index n × Index n) : Z :=
  T.table x (address a)

/-- Conjugation and the zero diagonal blocks belong to a fixed decoder. -/
def dilationDecode (T : Table X n Z) (a : Index n × Index n) (z : Z) : ℂ :=
  if a.1.1 = a.2.1 then 0 else if a.1.1 then star (T.decode (address a) z)
    else T.decode (address a) z

/-- The fixed dilation decoder keeps the decoder bound. -/
theorem dilationDecode_bound (T : Table X n Z) (a : Index n × Index n) (z : Z) :
    ‖dilationDecode T a z‖ ≤ T.scale := by
  unfold dilationDecode
  split
  · simpa using T.scale_pos.le
  · split
    · simpa only [norm_star] using T.decode_bound (address a) z
    · exact T.decode_bound (address a) z

/-- Decoding the dilation table gives the dilation of the represented matrix. -/
@[simp] theorem dilationDecoded (T : Table X n Z) (x : X) (i j : Index n) :
    dilationDecode T (i, j) (dilationTable T x (i, j)) = dilationMatrix T x i j := by
  rcases i with ⟨b, i⟩
  rcases j with ⟨c, j⟩
  cases b <;> cases c <;>
    simp [dilationDecode, dilationTable, address, dilationMatrix, T.decoded]

/-- The dilation of any represented matrix is Hermitian. -/
theorem dilation_hermitian (T : Table X n Z) (x : X) : (dilationMatrix T x).IsHermitian := by
  apply Matrix.IsHermitian.ext
  rintro ⟨b, i⟩ ⟨c, j⟩
  cases b <;> cases c <;> simp [dilationMatrix]

/-- The dilation vanishes on both diagonal blocks. -/
theorem dilation_diag (T : Table X n Z) (x : X) (i j : Index n) (h : i.1 = j.1) :
    dilationMatrix T x i j = 0 := by
  simp [dilationMatrix, h]

/-- For released data the dilation is the released `UnitaryEntryData.dilationMatrix`. -/
theorem ofData_dilationMatrix [Fintype n] (D : UnitaryEntryData.Data X n Z) :
    dilationMatrix (ofData D) = UnitaryEntryData.dilationMatrix D := rfl

/-- For released data the dilation table is the released one. -/
theorem ofData_dilationTable [Fintype n] (D : UnitaryEntryData.Data X n Z) :
    dilationTable (ofData D) = UnitaryEntryData.dilationTable D := rfl

/-- For released data the dilation decoder is the released one. -/
theorem ofData_dilationDecode [Fintype n] (D : UnitaryEntryData.Data X n Z) :
    dilationDecode (ofData D) = UnitaryEntryData.dilationDecode D := rfl

section Native
variable [Fintype n] [DecidableEq n] [Nonempty n]

omit [Nonempty n] in
/-- The released row locator lists every position of the opposite block. -/
theorem row_covers (T : Table X n Z) (x : X) (i j : Index n)
    (h : dilationMatrix T x i j ≠ 0) : SparseSlotStates.selected UnitaryEntryData.loc i j := by
  have hflag : i.1 ≠ j.1 := fun hij => h (dilation_diag T x i j hij)
  have hloc : UnitaryEntryData.loc i ((Fintype.equivFin n) j.2) = j := by
    rcases i with ⟨b, i⟩
    rcases j with ⟨c, j⟩
    cases b <;> cases c <;> simp_all [UnitaryEntryData.loc]
  rw [← hloc]
  exact SparseSlotStates.selected_loc UnitaryEntryData.loc i _

/-- The table supplies the native sparse interface with sparsity `N = card n`, the fixed
decoder of the dilation and the released known locators, which are independent of the table. -/
def toNative (T : Table X n Z) :
    NativeSparseBlockEncoding.Data X (Index n) Z (Fintype.card n) where
  slot := UnitaryEntryData.slot
  slots_pos := Fintype.card_pos
  scale := T.scale
  scale_pos := T.scale_pos
  matrix := dilationMatrix T
  table := dilationTable T
  decode := dilationDecode T
  decode_bound := dilationDecode_bound T
  decoded := dilationDecoded T
  rowloc := fun _ => UnitaryEntryData.loc
  colloc := fun _ => UnitaryEntryData.loc
  row_injective := fun _ => UnitaryEntryData.loc_injective
  column_injective := fun _ => UnitaryEntryData.loc_injective
  row_covers := row_covers T
  column_covers := by
    intro x i j h
    apply row_covers T x j i
    intro hji
    have hHerm := (dilation_hermitian T x).apply i j
    rw [hji, star_zero] at hHerm
    exact h hHerm.symm
  rowOracle := fun _ => UnitaryEntryData.rowOracle
  columnOracle := fun _ => UnitaryEntryData.columnOracle
  row_unitary := fun _ => UnitaryEntryData.rowOracle_unitary
  column_unitary := fun _ => UnitaryEntryData.columnOracle_unitary
  row_valid := fun _ => UnitaryEntryData.rowOracle_valid
  column_valid := fun _ => UnitaryEntryData.columnOracle_valid

/-- The native matrix is the dilation `H̃_U` of the represented matrix. -/
@[simp] theorem toNative_matrix (T : Table X n Z) : (toNative T).matrix = dilationMatrix T :=
  rfl

/-- The native table is the dilation table. -/
@[simp] theorem toNative_table (T : Table X n Z) : (toNative T).table = dilationTable T := rfl

/-- For released data this is the released native interface. -/
theorem toNative_ofData (D : UnitaryEntryData.Data X n Z) :
    toNative (ofData D) = UnitaryEntryData.toNative D := rfl

end Native

end Table

section Ghost
variable {X n : Type*} [Fintype n]

/-- Every entry of a unitary matrix has modulus at most one. -/
theorem unitary_entry_norm_le_one (U : Matrix n n ℂ)
    (hU : IsUnitary (SparseStateOverlap.matrixOperator U)) (i j : n) : ‖U i j‖ ≤ 1 := by
  have hColumn : ∑ k, ‖U k j‖ ^ 2 ≤ (1 : ℝ) ^ 2 :=
    SparseSpectralEnergy.column_energy_le U 1 hU.norm_le_one j
  have hSingle : ‖U i j‖ ^ 2 ≤ ∑ k, ‖U k j‖ ^ 2 :=
    Finset.single_le_sum (f := fun k => ‖U k j‖ ^ 2) (fun k _ => by positivity)
      (Finset.mem_univ i)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) zero_le_one two_ne_zero).mp
    (hSingle.trans hColumn)

/-- A unitary family as released exact entry data. Its ghost table returns the instance itself
and is never queried: it only makes the released dilation lemmas
(`UnitaryEntryData.dilation_sq`, `UnitaryEntryData.dilation_includeOne`, the energies) available
for the intended unitary `U`. -/
def exactData (U : X → Matrix n n ℂ)
    (hU : ∀ x, IsUnitary (SparseStateOverlap.matrixOperator (U x))) :
    UnitaryEntryData.Data X n X where
  matrix := U
  unitary := hU
  table := fun x _ => x
  decode := fun a y => U y a.1 a.2
  scale := 1
  scale_pos := one_pos
  decode_bound := fun a y => unitary_entry_norm_le_one (U y) (hU y) a.1 a.2
  decoded := fun _ _ _ => rfl

/-- The represented matrix of the ghost data is the intended unitary. -/
@[simp] theorem exactData_matrix (U : X → Matrix n n ℂ)
    (hU : ∀ x, IsUnitary (SparseStateOverlap.matrixOperator (U x))) :
    (exactData U hU).matrix = U := rfl

end Ghost

namespace Table

open UnitaryEntryData (Index)

section Closeness
variable {X n Z : Type*} [Fintype n]

/-- Under the entrywise promise, every row of `H̃_U` has Euclidean norm at most `η = 2`. -/
theorem dilation_row_energy_two (T : Table X n Z) (U : X → Matrix n n ℂ)
    (hU : ∀ x, IsUnitary (SparseStateOverlap.matrixOperator (U x))) (ξ : ℝ)
    (hEntry : ∀ x i j, ‖T.matrix x i j - U x i j‖ ≤ ξ)
    (hξ : (Fintype.card n : ℝ) * ξ ^ 2 ≤ 1) (x : X) (i : Index n) :
    ∑ j, ‖dilationMatrix T x i j‖ ^ 2 ≤ (2 : ℝ) ^ 2 := by
  rcases i with ⟨b, i⟩
  cases b
  · simpa [dilationMatrix, Fintype.sum_prod_type, Fintype.sum_bool] using
      energy_le_four (fun j => U x i j) (fun j => T.matrix x i j) ξ
        (UnitaryEntryData.row_energy (exactData U hU) x i) (fun j => hEntry x i j) hξ
  · simpa [dilationMatrix, Fintype.sum_prod_type, Fintype.sum_bool] using
      energy_le_four (fun j => U x j i) (fun j => T.matrix x j i) ξ
        (UnitaryEntryData.column_energy (exactData U hU) x i) (fun j => hEntry x j i) hξ

/-- Under the entrywise promise, every column of `H̃_U` has Euclidean norm at most `η = 2`. -/
theorem dilation_column_energy_two (T : Table X n Z) (U : X → Matrix n n ℂ)
    (hU : ∀ x, IsUnitary (SparseStateOverlap.matrixOperator (U x))) (ξ : ℝ)
    (hEntry : ∀ x i j, ‖T.matrix x i j - U x i j‖ ≤ ξ)
    (hξ : (Fintype.card n : ℝ) * ξ ^ 2 ≤ 1) (x : X) (j : Index n) :
    ∑ i, ‖dilationMatrix T x i j‖ ^ 2 ≤ (2 : ℝ) ^ 2 := by
  rcases j with ⟨b, j⟩
  cases b
  · simpa [dilationMatrix, Fintype.sum_prod_type, Fintype.sum_bool] using
      energy_le_four (fun i => U x j i) (fun i => T.matrix x j i) ξ
        (UnitaryEntryData.row_energy (exactData U hU) x j) (fun i => hEntry x j i) hξ
  · simpa [dilationMatrix, Fintype.sum_prod_type, Fintype.sum_bool] using
      energy_le_four (fun i => U x i j) (fun i => T.matrix x i j) ξ
        (UnitaryEntryData.column_energy (exactData U hU) x j) (fun i => hEntry x i j) hξ

/-- The positions of the opposite block, which contain every nonzero entry of a dilation. -/
def opposite (i : Index n) : Finset (Index n) :=
  (Finset.univ : Finset n).map ⟨fun k => (!i.1, k), fun _ _ h => congrArg Prod.snd h⟩

/-- The opposite block has `N` positions. -/
theorem card_opposite (i : Index n) : (opposite i).card = Fintype.card n := by
  simp [opposite]

/-- Outside the opposite block both flags agree. -/
theorem flag_eq_of_not_mem_opposite (i j : Index n) (h : j ∉ opposite i) : i.1 = j.1 := by
  rcases i with ⟨b, i⟩
  rcases j with ⟨c, j⟩
  by_contra hne
  apply h
  simp only [opposite, Finset.mem_map, Finset.mem_univ, true_and,
    Function.Embedding.coeFn_mk, Prod.mk.injEq]
  cases b <;> cases c <;> simp_all

/-- Under the entrywise promise `‖Ũ_ij - U_ij‖ ≤ ξ`, the two dilations differ by at most `N ξ`
in operator norm (the Schur bound on the common locators of the opposite blocks). -/
theorem dilation_sub_norm_le (T : Table X n Z) (U : X → Matrix n n ℂ)
    (hU : ∀ x, IsUnitary (SparseStateOverlap.matrixOperator (U x))) (ξ : ℝ) (hξ : 0 ≤ ξ)
    (hEntry : ∀ x i j, ‖T.matrix x i j - U x i j‖ ≤ ξ) (x : X) :
    ‖SparseStateOverlap.matrixOperator (dilationMatrix T x) -
      SparseStateOverlap.matrixOperator
        (UnitaryEntryData.dilationMatrix (exactData U hU) x)‖ ≤
      (Fintype.card n : ℝ) * ξ := by
  apply SparseValuePrecision.operator_error_le_of_common_locators _ _ opposite opposite
    (Fintype.card n) ξ hξ
  · intro i
    exact (card_opposite i).le
  · intro j
    exact (card_opposite j).le
  · intro i j hj
    exact dilation_diag T x i j (flag_eq_of_not_mem_opposite i j hj)
  · intro i j hj
    simp [UnitaryEntryData.dilationMatrix, flag_eq_of_not_mem_opposite i j hj]
  · intro i j hi
    exact dilation_diag T x i j (flag_eq_of_not_mem_opposite j i hi).symm
  · intro i j hi
    simp [UnitaryEntryData.dilationMatrix, (flag_eq_of_not_mem_opposite j i hi).symm]
  · rintro ⟨b, i⟩ ⟨c, j⟩
    cases b <;> cases c
    · simpa [dilationMatrix, UnitaryEntryData.dilationMatrix] using hξ
    · simpa [dilationMatrix, UnitaryEntryData.dilationMatrix] using hEntry x i j
    · simpa [dilationMatrix, UnitaryEntryData.dilationMatrix, ← map_sub] using hEntry x j i
    · simpa [dilationMatrix, UnitaryEntryData.dilationMatrix] using hξ

/-- Duhamel's bound of Corollary `hs:cor:unitary`:
`‖e^{-i(π/2)H̃_U} - e^{-i(π/2)H_U}‖ ≤ (π/2) ‖H̃_U - H_U‖ ≤ (π/2) N ξ`. With `ξ = ε/(π N)` the
right-hand side is `ε/2` (`duhamel_term_eq_half`). -/
theorem dilation_evolution_error_le (T : Table X n Z) (U : X → Matrix n n ℂ)
    (hU : ∀ x, IsUnitary (SparseStateOverlap.matrixOperator (U x))) (ξ : ℝ) (hξ : 0 ≤ ξ)
    (hEntry : ∀ x i j, ‖T.matrix x i j - U x i j‖ ≤ ξ) (x : X) :
    ‖NormedSpace.exp ((-Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) •
        SparseStateOverlap.matrixOperator (dilationMatrix T x)) -
      NormedSpace.exp ((-Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) •
        SparseStateOverlap.matrixOperator
          (UnitaryEntryData.dilationMatrix (exactData U hU) x))‖ ≤
      Real.pi / 2 * ((Fintype.card n : ℝ) * ξ) := by
  have hpi : 0 < Real.pi / 2 := by linarith [Real.pi_pos]
  have h := HamiltonianStability.evolution_error_le _ _ (Real.pi / 2)
    (SparseValuePrecision.matrixOperator_star_eq _ (dilation_hermitian T x))
    (SparseValuePrecision.matrixOperator_star_eq _
      (UnitaryEntryData.dilation_hermitian (exactData U hU) x))
  rw [abs_of_pos hpi] at h
  exact h.trans (mul_le_mul_of_nonneg_left (dilation_sub_norm_le T U hU ξ hξ hEntry x) hpi.le)

end Closeness

end Table

end
end SparseHamiltonian.UnitaryPrecision
