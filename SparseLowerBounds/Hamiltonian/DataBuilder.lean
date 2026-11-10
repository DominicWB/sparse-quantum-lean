import SparseLowerBounds.Hamiltonian.Accuracy

set_option synthInstance.maxHeartbeats 400000

section
/-!
# Native sparse data from one-bit word tables

A generic builder of the release's `NativeSparseBlockEncoding.Data` for hard
families whose every entry is a known function of **at most one** hidden
Boolean bit (the chain construction of Section `part:hsl`: "Its entry calculation uses only the
queried membership bit and known constants"; "A value query requires at most two Boolean queries").

* **Words.** `Word B = ZMod (2^{B+1})` with the position-independent signed
  fixed-point decode `z ↦ valMinAbs z / 2^B` (`wordDecode`), which represents
  exactly the dyadic numbers `v/2^B` with `-2^B < v ≤ 2^B`; decode scale `1`
  (`word_valMinAbs_intCast`, `wordDecode_intCast`, `norm_wordDecode_le`).
* **Bit tables.** `BitTable I A`: for every address `a`, an optional bit
  position `addr a : Option I` and the integer word `word a y` for each value
  `y` of that bit. Under a hidden input with bits `y : I → Bool` the word is
  `T.value y a` (`false` is used when no bit is addressed).
* **Locators** are input-independent: the slots are a fixed embedding
  `slot : Fin s ↪ N`, row `i` uses the fixed injective list `loc i`, columns use
  the same lists (the hard matrices are symmetric). Their full in-place
  extensions are the permutation unitaries of `(i, c) ↦ (i, π_i c)` and
  `(j, c) ↦ (π_j c, j)`, where `π_i` is a fixed permutation of `N` extending
  `slot k ↦ loc i k` (`slotPerm`, via `Equiv.extendSubtype`); on the slots they
  are exactly the promised locators (`rowEquiv_slot`, `colEquiv_slot`).

`bitData` takes, as hypotheses, the word bounds, the decoding identity
`word/2^B = H`, and coverage of the support by the location lists.
-/

namespace SparseLowerBounds.Hamiltonian

noncomputable section
open SparseHamiltonian NativeSparseBlockEncoding

/-- The word alphabet `ℤ/2^{B+1}` (`B` fractional bits). -/
abbrev Word (B : ℕ) : Type := ZMod (2 ^ (B + 1))

/-- Position-independent signed fixed-point decode `z ↦ valMinAbs z / 2^B`. -/
def wordDecode (B : ℕ) (z : Word B) : ℂ := (ZMod.valMinAbs z : ℂ) / 2 ^ B

section Words

/-- An integer word in `(-2^B, 2^B]` is its own balanced representative in
`ℤ/2^{B+1}`. -/
theorem word_valMinAbs_intCast {B : ℕ} (w : ℤ) (h1 : -(2 : ℤ) ^ B < w) (h2 : w ≤ 2 ^ B) :
    ((w : Word B).valMinAbs) = w := by
  rw [ZMod.valMinAbs_spec]
  refine ⟨rfl, ?_, ?_⟩ <;> push_cast <;> rw [pow_succ] <;> linarith

/-- **Exact decode**: an integer word in `(-2^B, 2^B]` decodes to `w/2^B`. -/
theorem wordDecode_intCast {B : ℕ} (w : ℤ) (h1 : -(2 : ℤ) ^ B < w) (h2 : w ≤ 2 ^ B) :
    wordDecode B (w : Word B) = (w : ℂ) / 2 ^ B := by
  rw [wordDecode, word_valMinAbs_intCast w h1 h2]

/-- Every word decodes into the unit disc (decode scale `1`). -/
theorem norm_wordDecode_le (B : ℕ) (z : Word B) : ‖wordDecode B z‖ ≤ 1 := by
  have h := ZMod.valMinAbs_mem_Ioc z
  push_cast at h
  rw [pow_succ] at h
  obtain ⟨h1, h2⟩ := h
  have hk : (0 : ℝ) < 2 ^ B := by positivity
  rw [wordDecode, norm_div, norm_pow, Complex.norm_intCast, Complex.norm_ofNat, div_le_one hk]
  have e1 : -(2 : ℤ) ^ B ≤ z.valMinAbs := by linarith
  have e2 : z.valMinAbs ≤ (2 : ℤ) ^ B := by linarith
  have f1 : ((-(2 : ℤ) ^ B : ℤ) : ℝ) ≤ (z.valMinAbs : ℝ) := Int.cast_le.mpr e1
  have f2 : (z.valMinAbs : ℝ) ≤ (((2 : ℤ) ^ B : ℤ) : ℝ) := Int.cast_le.mpr e2
  push_cast at f1 f2
  exact abs_le.mpr ⟨f1, f2⟩

end Words

/-- A table of integer words, each depending on at most one Boolean bit. -/
structure BitTable (I A : Type*) where
  /-- The bit position the word of address `a` depends on (`none`: known word). -/
  addr : A → Option I
  /-- The integer word of address `a` for each value of its bit. -/
  word : A → Bool → ℤ

namespace BitTable

variable {I A : Type*}

/-- The value of the addressed bit under hidden bits `y` (`false` if none). -/
def bit (T : BitTable I A) (y : I → Bool) (a : A) : Bool :=
  match T.addr a with
  | none => false
  | some i => y i

/-- The word of address `a` under hidden bits `y`. -/
def value (T : BitTable I A) (y : I → Bool) (a : A) : ℤ := T.word a (T.bit y a)

section Facts

variable (T : BitTable I A) (y : I → Bool) {a : A}

/-- A known word reads no bit. -/
theorem bit_of_addr_none (h : T.addr a = none) : T.bit y a = false := by
  unfold bit
  rw [h]

/-- An addressed word reads its bit. -/
theorem bit_of_addr_some {i : I} (h : T.addr a = some i) : T.bit y a = y i := by
  unfold bit
  rw [h]

/-- The queried bit is set iff the address names a bit that is set. -/
theorem bit_eq_true_iff : T.bit y a = true ↔ ∃ i, T.addr a = some i ∧ y i = true := by
  unfold bit
  cases h : T.addr a with
  | none => simp
  | some i => simp

theorem value_of_addr_none (h : T.addr a = none) : T.value y a = T.word a false := by
  rw [value, T.bit_of_addr_none y h]

theorem value_of_addr_some {i : I} (h : T.addr a = some i) : T.value y a = T.word a (y i) := by
  rw [value, T.bit_of_addr_some y h]

end Facts

end BitTable

variable {N : Type*} [Fintype N] [DecidableEq N] {s : ℕ}

/-- A fixed permutation of `N` extending `slot k ↦ loc k`. -/
def slotPerm (slot : Fin s ↪ N) (loc : Fin s ↪ N) : Equiv.Perm N := by
  classical
  exact Equiv.extendSubtype
    ((Equiv.ofInjective slot slot.injective).symm.trans (Equiv.ofInjective loc loc.injective))

theorem slotPerm_slot (slot : Fin s ↪ N) (loc : Fin s ↪ N) (k : Fin s) :
    slotPerm slot loc (slot k) = loc k := by
  classical
  unfold slotPerm
  rw [Equiv.extendSubtype_apply_of_mem _ _ (Set.mem_range_self k)]
  simp

/-- Row location as a basis bijection: `(i, c) ↦ (i, π_i c)`. -/
def rowEquiv (slot : Fin s ↪ N) (loc : N → Fin s ↪ N) : N × N ≃ N × N :=
  Equiv.prodShear (Equiv.refl N) fun i => slotPerm slot (loc i)

/-- Column location: `(j, c) ↦ (π_j c, j)` (the release's column order). -/
def colEquiv (slot : Fin s ↪ N) (loc : N → Fin s ↪ N) : N × N ≃ N × N :=
  (rowEquiv slot loc).trans (Equiv.prodComm N N)

/-- The permutation unitary of a basis bijection. -/
def permCLM {α : Type*} [Fintype α] (e : α ≃ α) : EuclideanSpace ℂ α →L[ℂ] EuclideanSpace ℂ α :=
  (LookupOracle.permutationUnitary e).toLinearIsometry.toContinuousLinearMap

section Locators

theorem rowEquiv_apply (slot : Fin s ↪ N) (loc : N → Fin s ↪ N) (i c : N) :
    rowEquiv slot loc (i, c) = (i, slotPerm slot (loc i) c) := rfl

theorem colEquiv_apply (slot : Fin s ↪ N) (loc : N → Fin s ↪ N) (j c : N) :
    colEquiv slot loc (j, c) = (slotPerm slot (loc j) c, j) := rfl

/-- On the slots, the row bijection is the promised row locator. -/
theorem rowEquiv_slot (slot : Fin s ↪ N) (loc : N → Fin s ↪ N) (i : N) (k : Fin s) :
    rowEquiv slot loc (i, slot k) = (i, loc i k) := by
  rw [rowEquiv_apply, slotPerm_slot]

/-- On the slots, the column bijection is the promised column locator. -/
theorem colEquiv_slot (slot : Fin s ↪ N) (loc : N → Fin s ↪ N) (j : N) (k : Fin s) :
    colEquiv slot loc (j, slot k) = (loc j k, j) := by
  rw [colEquiv_apply, slotPerm_slot]

theorem permCLM_apply {α : Type*} [Fintype α] (e : α ≃ α) (v : EuclideanSpace ℂ α) (a : α) :
    permCLM e v a = v (e.symm a) := rfl

theorem permCLM_single {α : Type*} [Fintype α] [DecidableEq α] (e : α ≃ α) (a : α) (z : ℂ) :
    permCLM e (EuclideanSpace.single a z) = EuclideanSpace.single (e a) z :=
  LookupOracle.permutationUnitary_single e a z

theorem isUnitary_permCLM {α : Type*} [Fintype α] (e : α ≃ α) :
    OracleCircuit.IsUnitary (permCLM e) :=
  LookupOracle.permutationUnitary_unitary e

end Locators

/-- **Native sparse data from a one-bit word table.** Exact words with
position-independent decode (scale `1`), input-independent location lists
`loc` with fixed permutation extensions, matrix `H`. -/
def bitData {X I : Type*} (s B : ℕ) (hs : 0 < s) (slot : Fin s ↪ N) (loc : N → Fin s ↪ N)
    (T : BitTable I (N × N)) (y : X → I → Bool) (H : X → Matrix N N ℂ)
    (hbound : ∀ a b, -(2 : ℤ) ^ B < T.word a b ∧ T.word a b ≤ 2 ^ B)
    (hdec : ∀ x i j, ((T.value (y x) (i, j) : ℤ) : ℂ) / 2 ^ B = H x i j)
    (hrow : ∀ x i j, H x i j ≠ 0 → j ∈ Set.range (loc i))
    (hcol : ∀ x i j, H x i j ≠ 0 → i ∈ Set.range (loc j)) :
    Data X N (Word B) s where
  slot := slot
  slots_pos := hs
  scale := 1
  scale_pos := one_pos
  matrix := H
  table x a := ((T.value (y x) a : ℤ) : Word B)
  decode _ := wordDecode B
  decode_bound _ z := norm_wordDecode_le B z
  decoded x i j :=
    (wordDecode_intCast _ (hbound (i, j) _).1 (hbound (i, j) _).2).trans (hdec x i j)
  rowloc _ i k := loc i k
  colloc _ j k := loc j k
  row_injective _ i := (loc i).injective
  column_injective _ j := (loc j).injective
  row_covers x i j h := by
    obtain ⟨k, hk⟩ := hrow x i j h
    exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, hk⟩
  column_covers x i j h := by
    obtain ⟨k, hk⟩ := hcol x i j h
    exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, hk⟩
  rowOracle _ := permCLM (rowEquiv slot loc)
  columnOracle _ := permCLM (colEquiv slot loc)
  row_unitary _ := LookupOracle.permutationUnitary_unitary _
  column_unitary _ := LookupOracle.permutationUnitary_unitary _
  row_valid _ i k := (permCLM_single _ _ _).trans (by rw [rowEquiv_slot])
  column_valid _ j k := (permCLM_single _ _ _).trans (by rw [colEquiv_slot])

section Facts

variable {X I : Type*} {B : ℕ} {hs : 0 < s} {slot : Fin s ↪ N} {loc : N → Fin s ↪ N}
  {T : BitTable I (N × N)} {y : X → I → Bool} {H : X → Matrix N N ℂ}
  {hbound : ∀ a b, -(2 : ℤ) ^ B < T.word a b ∧ T.word a b ≤ 2 ^ B}
  {hdec : ∀ x i j, ((T.value (y x) (i, j) : ℤ) : ℂ) / 2 ^ B = H x i j}
  {hrow : ∀ x i j, H x i j ≠ 0 → j ∈ Set.range (loc i)}
  {hcol : ∀ x i j, H x i j ≠ 0 → i ∈ Set.range (loc j)}

@[simp] theorem bitData_matrix :
    (bitData s B hs slot loc T y H hbound hdec hrow hcol).matrix = H := rfl

/-- The value table is the word of the queried bit. -/
theorem bitData_table (x : X) (a : N × N) :
    (bitData s B hs slot loc T y H hbound hdec hrow hcol).table x a =
      ((T.value (y x) a : ℤ) : Word B) := rfl

/-- **Locators are input-independent** (the chain construction of Section `part:hsl`). -/
theorem bitData_locators_const (x x' : X) :
    (bitData s B hs slot loc T y H hbound hdec hrow hcol).rowloc x =
        (bitData s B hs slot loc T y H hbound hdec hrow hcol).rowloc x' ∧
      (bitData s B hs slot loc T y H hbound hdec hrow hcol).colloc x =
        (bitData s B hs slot loc T y H hbound hdec hrow hcol).colloc x' ∧
      (bitData s B hs slot loc T y H hbound hdec hrow hcol).rowOracle x =
        (bitData s B hs slot loc T y H hbound hdec hrow hcol).rowOracle x' ∧
      (bitData s B hs slot loc T y H hbound hdec hrow hcol).columnOracle x =
        (bitData s B hs slot loc T y H hbound hdec hrow hcol).columnOracle x' :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The row location oracle is the fixed permutation unitary of `rowEquiv`. -/
theorem bitData_rowOracle (x : X) :
    (bitData s B hs slot loc T y H hbound hdec hrow hcol).rowOracle x =
      permCLM (rowEquiv slot loc) := rfl

/-- The column location oracle is the fixed permutation unitary of `colEquiv`. -/
theorem bitData_columnOracle (x : X) :
    (bitData s B hs slot loc T y H hbound hdec hrow hcol).columnOracle x =
      permCLM (colEquiv slot loc) := rfl

/-- The decoder is the position-independent `wordDecode`. -/
theorem bitData_decode (a : N × N) :
    (bitData s B hs slot loc T y H hbound hdec hrow hcol).decode a = wordDecode B := rfl

end Facts

end

end SparseLowerBounds.Hamiltonian
end
