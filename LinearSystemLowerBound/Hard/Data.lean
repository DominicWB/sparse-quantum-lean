import LinearSystemLowerBound.Hard.Native

/-!
# Native sparse data for the hard family

`hardData` is a `NativeSparseBlockEncoding.Data` instance whose matrices are the hard
matrices `A_X`, with

* `s` slots for any `m + 1 ≤ s ≤ |N|`: every row lists its at most `m + 1` possible nonzero
  positions (the swapped diagonal and one clock block), padded by further positions; the
  lists are fixed permutations of the slot labels, so the in-place row and column location
  oracles are fixed basis permutations, **independent of the input** (`hardData_access`);
* an address-independent three-bit word encoding of the entries (`enc`, `dec`): the entries
  take the five values `0, 1/2, -r/m, r/2 - r/m, -r/2` (`hard_entry_cases`), and the value
  oracle adds the code of the entry, a fixed function of the entry (`hardData_table`).

This shows that the hypotheses of the lower bound are satisfiable; the lower bound itself
holds for every data with the hard matrices, input-independent locators and an
entry-determined table.
-/

namespace LinearSystemLowerBound.Hard

noncomputable section
open scoped BigOperators Matrix
open LinearSystemLowerBound SparseHamiltonian

/-! ### Permutations covering a row support -/

theorem exists_perm_cover {N : Type*} [Fintype N] [DecidableEq N] (A B : Finset N)
    (h : B.card ≤ A.card) : ∃ π : Equiv.Perm N, ∀ b ∈ B, ∃ a ∈ A, π a = b := by
  obtain ⟨B', hBB', -, hcard⟩ :=
    Finset.exists_subsuperset_card_eq (Finset.subset_univ B) h (Finset.card_le_univ A)
  have hc : Fintype.card {x // x ∈ A} = Fintype.card {x // x ∈ B'} := by
    simp [hcard]
  let e : {x // x ∈ A} ≃ {x // x ∈ B'} := Fintype.equivOfCardEq hc
  refine ⟨e.extendSubtype, fun b hb => ?_⟩
  refine ⟨(e.symm ⟨b, hBB' hb⟩ : N), (e.symm ⟨b, hBB' hb⟩).2, ?_⟩
  rw [Equiv.extendSubtype_apply_of_mem e _ (e.symm ⟨b, hBB' hb⟩).2]
  simp

variable {n m T s : ℕ} [NeZero m]

/-! ### Slots and locators -/

/-- A fixed slot embedding. -/
def slotEmb (hs : s ≤ Fintype.card (Idx T m)) : Fin s ↪ Idx T m :=
  (Function.Embedding.nonempty_of_card_le (by simpa using hs)).some

/-- A fixed permutation of the indices mapping the slots onto a superset of the support. -/
def rowPerm (hs : s ≤ Fintype.card (Idx T m)) (hms : m + 1 ≤ s) (i : Idx T m) :
    Equiv.Perm (Idx T m) :=
  Classical.choose (exists_perm_cover (Finset.univ.map (slotEmb hs)) (support i)
    (by simpa using (card_support_le i).trans hms))

omit [NeZero m] in
theorem rowPerm_cover (hs : s ≤ Fintype.card (Idx T m)) (hms : m + 1 ≤ s) (i : Idx T m)
    (j : Idx T m) (hj : j ∈ support i) : ∃ k, rowPerm hs hms i (slotEmb hs k) = j := by
  obtain ⟨a, ha, h⟩ := Classical.choose_spec (exists_perm_cover (Finset.univ.map (slotEmb hs))
    (support i) (by simpa using (card_support_le i).trans hms)) j hj
  obtain ⟨k, -, rfl⟩ := Finset.mem_map.mp ha
  exact ⟨k, h⟩

/-- The padded location list of a row (and, by symmetry, of a column). -/
def loc (hs : s ≤ Fintype.card (Idx T m)) (hms : m + 1 ≤ s) (i : Idx T m) (k : Fin s) :
    Idx T m :=
  rowPerm hs hms i (slotEmb hs k)

omit [NeZero m] in
theorem loc_injective (hs : s ≤ Fintype.card (Idx T m)) (hms : m + 1 ≤ s) (i : Idx T m) :
    Function.Injective (loc hs hms i) :=
  (rowPerm hs hms i).injective.comp (slotEmb hs).injective

/-- In-place row location as a basis permutation `(i, c) ↦ (i, π_i c)`. -/
def rowEquiv (hs : s ≤ Fintype.card (Idx T m)) (hms : m + 1 ≤ s) :
    (Idx T m × Idx T m) ≃ (Idx T m × Idx T m) :=
  Equiv.prodShear (Equiv.refl _) (rowPerm hs hms)

/-- In-place column location `(j, c) ↦ (π_j c, j)`. -/
def columnEquiv (hs : s ≤ Fintype.card (Idx T m)) (hms : m + 1 ≤ s) :
    (Idx T m × Idx T m) ≃ (Idx T m × Idx T m) :=
  (rowEquiv hs hms).trans (Equiv.prodComm _ _)

/-! ### Word encoding of the entries -/

/-- The entries take five values. -/
theorem gadget_cases (j a b : Fin m) : gadget j a b = 2 / m ∨ gadget j a b = 2 / m - 1 := by
  simp only [gadget, Matrix.of_apply]
  split_ifs <;> simp

theorem step_cases (x : Fin n → Fin m) (i : Fin T) (a b : Fin m) :
    step x i a b = 0 ∨ step x i a b = 1 ∨ step x i a b = 2 / m ∨ step x i a b = 2 / m - 1 := by
  unfold step
  split_ifs with hi
  · rcases gadget_cases (x ⟨i.val, hi⟩) a b with h | h <;> simp [h]
  · simp only [Matrix.one_apply]; split_ifs <;> simp

theorem dil_cases (x : Fin n → Fin m) (p q : Idx T m) :
    dil x p q = 0 ∨ dil x p q = 1 ∨ dil x p q = 2 / m ∨ dil x p q = 2 / m - 1 := by
  have hc : ∀ p' q' : Fin (T + 1) × Fin m, clock x p' q' = 0 ∨ clock x p' q' = 1 ∨
      clock x p' q' = 2 / m ∨ clock x p' q' = 2 / m - 1 := by
    intro p' q'
    simp only [clock, Matrix.of_apply]
    split_ifs
    · exact step_cases _ _ _ _
    · simp
  simp only [dil, Matrix.of_apply]
  split_ifs
  · exact hc _ _
  · exact hc _ _
  · simp

theorem dil_of_swap (x : Fin n → Fin m) (p q : Idx T m)
    (h : (swapM : Matrix (Idx T m) (Idx T m) ℂ) p q ≠ 0) : dil x p q = 0 := by
  simp only [swapM, Matrix.of_apply, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false,
    not_not] at h
  obtain ⟨h1, h2⟩ := h
  have hcl : ∀ t : Fin (T + 1) × Fin m, clock x t t = 0 := by
    intro t
    simp only [clock, Matrix.of_apply]
    rw [dif_neg (by omega)]
  rcases p with ⟨σ, t⟩
  rcases q with ⟨τ, t'⟩
  simp only at h1 h2
  subst h1 h2
  cases τ <;> simp [dil, hcl]

omit [NeZero m] in
theorem swap_cases (p q : Idx T m) :
    (swapM : Matrix (Idx T m) (Idx T m) ℂ) p q = 0 ∨
      (swapM : Matrix (Idx T m) (Idx T m) ℂ) p q = 1 := by
  simp only [swapM, Matrix.of_apply]
  split_ifs <;> simp

/-- **The entries of `A_X`** lie in `{0, 1/2, -r/m, r/2 - r/m, -r/2}`. -/
theorem hard_entry_cases (r : ℝ) (x : Fin n → Fin m) (p q : Idx T m) :
    hardMatrix r x p q = 0 ∨ hardMatrix r x p q = 1 / 2 ∨
      hardMatrix r x p q = -((r : ℂ) / m) ∨ hardMatrix r x p q = (r : ℂ) / 2 - (r : ℂ) / m ∨
      hardMatrix r x p q = -((r : ℂ) / 2) := by
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne m
  simp only [hardMatrix, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  rcases swap_cases p q with hs | hs
  · rw [hs]
    rcases dil_cases x p q with hd | hd | hd | hd <;> rw [hd]
    · left; ring
    · right; right; right; right; ring
    · right; right; left; field_simp; ring
    · right; right; right; left; field_simp; ring
  · rw [hs, dil_of_swap x p q (by rw [hs]; exact one_ne_zero)]
    right; left; ring

/-- The fixed word encoding of the entry values. -/
def enc (r : ℝ) (m : ℕ) (y : ℂ) : ZMod 8 :=
  if y = 1 / 2 then 1 else if y = -((r : ℂ) / m) then 2
  else if y = (r : ℂ) / 2 - (r : ℂ) / m then 3 else if y = -((r : ℂ) / 2) then 4 else 0

/-- The fixed, address-independent decoder of the words. -/
def dec (r : ℝ) (m : ℕ) (z : ZMod 8) : ℂ :=
  if z = 1 then 1 / 2 else if z = 2 then -((r : ℂ) / m)
  else if z = 3 then (r : ℂ) / 2 - (r : ℂ) / m else if z = 4 then -((r : ℂ) / 2) else 0

omit [NeZero m] in
theorem dec_enc (r : ℝ) (y : ℂ)
    (hy : y = 0 ∨ y = 1 / 2 ∨ y = -((r : ℂ) / m) ∨ y = (r : ℂ) / 2 - (r : ℂ) / m ∨
      y = -((r : ℂ) / 2)) : dec r m (enc r m y) = y := by
  unfold enc dec
  by_cases h1 : y = 1 / 2
  · rw [if_pos h1, if_pos rfl, h1]
  by_cases h2 : y = -((r : ℂ) / m)
  · rw [if_neg h1, if_pos h2, if_neg (by decide : (2 : ZMod 8) ≠ 1), if_pos rfl, h2]
  by_cases h3 : y = (r : ℂ) / 2 - (r : ℂ) / m
  · rw [if_neg h1, if_neg h2, if_pos h3, if_neg (by decide : (3 : ZMod 8) ≠ 1),
      if_neg (by decide : (3 : ZMod 8) ≠ 2), if_pos rfl, h3]
  by_cases h4 : y = -((r : ℂ) / 2)
  · rw [if_neg h1, if_neg h2, if_neg h3, if_pos h4, if_neg (by decide : (4 : ZMod 8) ≠ 1),
      if_neg (by decide : (4 : ZMod 8) ≠ 2), if_neg (by decide : (4 : ZMod 8) ≠ 3), if_pos rfl,
      h4]
  rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg (by decide : (0 : ZMod 8) ≠ 1),
    if_neg (by decide : (0 : ZMod 8) ≠ 2), if_neg (by decide : (0 : ZMod 8) ≠ 3),
    if_neg (by decide : (0 : ZMod 8) ≠ 4)]
  rcases hy with hy | hy | hy | hy | hy
  · exact hy.symm
  · exact absurd hy h1
  · exact absurd hy h2
  · exact absurd hy h3
  · exact absurd hy h4

omit [NeZero m] in
theorem norm_dec_le (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hm2 : 2 ≤ m) (z : ZMod 8) :
    ‖dec r m z‖ ≤ 1 := by
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm2
  have hm0 : (0 : ℝ) < m := by linarith
  have hrm : r / m ≤ 1 := by rw [div_le_one hm0]; linarith
  have hrm0 : 0 ≤ r / m := by positivity
  unfold dec
  split_ifs
  · norm_num
  · rw [norm_neg, show ((r : ℂ) / m) = ((r / m : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hrm0]
    exact hrm
  · rw [show (r : ℂ) / 2 - (r : ℂ) / m = ((r / 2 - r / m : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> nlinarith
  · rw [norm_neg, show ((r : ℂ) / 2) = ((r / 2 : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    linarith
  · simp

/-! ### The data -/

/-- **Native sparse data of the hard family.** -/
def hardData (hs : s ≤ Fintype.card (Idx T m)) (hms : m + 1 ≤ s) (hm2 : 2 ≤ m) (r : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    NativeSparseBlockEncoding.Data (Fin n → Fin m) (Idx T m) (ZMod 8) s where
  slot := slotEmb hs
  slots_pos := by omega
  scale := 1
  scale_pos := one_pos
  matrix := hardMatrix r
  table := fun x α => enc r m (hardMatrix r x α.1 α.2)
  decode := fun _ z => dec r m z
  decode_bound := fun _ z => norm_dec_le r hr0 hr1 hm2 z
  decoded := fun x i j => dec_enc r _ (hard_entry_cases r x i j)
  rowloc := fun _ => loc hs hms
  colloc := fun _ => loc hs hms
  row_injective := fun _ => loc_injective hs hms
  column_injective := fun _ => loc_injective hs hms
  row_covers := by
    intro x i j h
    obtain ⟨k, hk⟩ := rowPerm_cover hs hms i j (hard_support r x i j h)
    exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, hk⟩
  column_covers := by
    intro x i j h
    rw [hard_symm] at h
    obtain ⟨k, hk⟩ := rowPerm_cover hs hms j i (hard_support r x j i h)
    exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, hk⟩
  rowOracle := fun _ => (LookupOracle.permutationUnitary (rowEquiv hs hms)).toLinearIsometry.toContinuousLinearMap
  columnOracle := fun _ =>
    (LookupOracle.permutationUnitary (columnEquiv hs hms)).toLinearIsometry.toContinuousLinearMap
  row_unitary := fun _ => LookupOracle.permutationUnitary_unitary _
  column_unitary := fun _ => LookupOracle.permutationUnitary_unitary _
  row_valid := by
    intro x i k
    change LookupOracle.permutationUnitary (rowEquiv hs hms) _ = _
    rw [LookupOracle.permutationUnitary_single]
    rfl
  column_valid := by
    intro x j k
    change LookupOracle.permutationUnitary (columnEquiv hs hms) _ = _
    rw [LookupOracle.permutationUnitary_single]
    rfl

theorem hardData_matrix (hs : s ≤ Fintype.card (Idx T m)) (hms : m + 1 ≤ s) (hm2 : 2 ≤ m)
    (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    (hardData (n := n) hs hms hm2 r hr0 hr1).matrix = hardMatrix r := rfl

/-- The value oracle returns a fixed, address-independent word encoding of the entry. -/
theorem hardData_table (hs : s ≤ Fintype.card (Idx T m)) (hms : m + 1 ≤ s) (hm2 : 2 ≤ m)
    (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (x : Fin n → Fin m) (α : Idx T m × Idx T m) :
    (hardData hs hms hm2 r hr0 hr1).table x α =
      enc r m ((hardData hs hms hm2 r hr0 hr1).matrix x α.1 α.2) := rfl

/-- **The locators are input-independent** and the table entries depend on at most one bit. -/
theorem hardData_access (hs : s ≤ Fintype.card (Idx T m)) (hms : m + 1 ≤ s) (hm2 : 2 ≤ m)
    (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    Native.HardAccess (hardData (n := n) hs hms hm2 r hr0 hr1) where
  row_const := fun _ _ => rfl
  column_const := fun _ _ => rfl
  table_bit := fun α => (bitDetermined_hard r α.1 α.2).comp (enc r m)

end

end LinearSystemLowerBound.Hard
