import SparseLowerBounds.Hamiltonian.HardDataEntries

set_option synthInstance.maxHeartbeats 400000

section
/-!
# Hard data, part 1: shared locators and the signed scalar family

Manuscript: the chain construction of Section `part:hsl` (exact dyadic entries, reference
vertices, public locators, two Boolean queries per value call), Lemma `hsl:lem:precision` (the
signed scalar chain of the precision family) and the end of the proof of Theorem
`hsl:thm:main` (padding). Split off from
`Hamiltonian/HardData`, which imports this module; the search families and the
data at the main parameters are there.

**Locators shared by both families** (input-independent, the chain construction of Section
`part:hsl`): the slots are the padding block (`padSlot`); a reference row swaps itself with padding
slot `0` (`refLoc`); padding rows list the padding block; core rows use a family-specific list
(`fullLoc`).

**Scalar locators**: row `k` lists `k ± 1` in slots `0, 1` (`scalarLoc`; for
`n = 1` the predecessor is the cyclic successor). The family needs `s ≥ 2`.

**Scalar words**, `B = F + σ` with `F = chainBits n 1 τ` and
`σ = ⌈log₂ s⌉`: entry `b'_k (-1)^{x_k}` has word `(-1)^{x_k} N_k 2^σ`; padding
`2^F` (entry `2^{-σ}`); energy-one `2^B` (entry `1`). Every word lies in
`(-2^B, 2^B]`, so the position-independent decode `valMinAbs z/2^B` is exact.
The address of each word is its one bit (`scalarAddr`: bit `k` of the `k`-th
edge); known entries make no query.

**Proof steps** (helper statements): `scalarLocFun_zero`, `scalarLocFun_one`,
`refLoc_zero`, `ref/pad_mem_range_fullLoc` (coverage), `scalarTable_value_*`
(the word on each block of `FullIndex`), which with the entry and dyadic lemmas
of `Hamiltonian/HardDataEntries` give `scalarTable_decode`. Consumers:
`scalarData_table`, `scalarData_rowloc`, `scalarData_locators_const`.
-/

namespace SparseLowerBounds.Hamiltonian

noncomputable section
open SparseHamiltonian NativeSparseBlockEncoding

/-! ### Locators shared by the hard families -/


/-- The fixed slots: the padding block. -/
def padSlot (C : Type) (s : ℕ) : Fin s ↪ FullIndex C s :=
  ⟨fun t => Sum.inr (Sum.inr t), Sum.inr_injective.comp Sum.inr_injective⟩

/-- A reference row lists itself in place of padding slot `0`. -/
def refLoc {C : Type} [DecidableEq C] {s : ℕ} (hs : 0 < s) (r : Fin 2) : Fin s ↪ FullIndex C s :=
  (padSlot C s).trans (Equiv.swap (Sum.inr (Sum.inr ⟨0, hs⟩)) (Sum.inr (Sum.inl r))).toEmbedding

/-- Location lists of the full index set from those of the core rows. -/
def fullLoc {C : Type} [DecidableEq C] {s : ℕ} (hs : 0 < s) (coreLoc : C → Fin s ↪ FullIndex C s) :
    FullIndex C s → Fin s ↪ FullIndex C s
  | Sum.inl c => coreLoc c
  | Sum.inr (Sum.inl r) => refLoc hs r
  | Sum.inr (Sum.inr _) => padSlot C s

/-- The scalar row list of core row `k`. -/
def scalarLocFun (n s : ℕ) (k : Fin (n + 1)) (t : Fin s) : ScalarIndex n s :=
  if (t : ℕ) = 0 then Sum.inl ⟨((k : ℕ) + 1) % (n + 1), Nat.mod_lt _ (Nat.succ_pos n)⟩
  else if (t : ℕ) = 1 ∧ 2 ≤ n then Sum.inl ⟨((k : ℕ) + n) % (n + 1), Nat.mod_lt _ (Nat.succ_pos n)⟩
  else Sum.inr (Sum.inr t)

namespace HardDataScalar

/-- `a mod b` for `a < 2b`. -/
theorem mod_of_lt_two_mul {a b : ℕ} (h : a < 2 * b) : a % b = if a < b then a else a - b := by
  split_ifs with hab
  · exact Nat.mod_eq_of_lt hab
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

/-- For `n ≥ 2`, the cyclic successor and predecessor of a clock index differ. -/
theorem succ_mod_ne_add_mod {n k : ℕ} (hn : 2 ≤ n) (hk : k < n + 1) :
    (k + 1) % (n + 1) ≠ (k + n) % (n + 1) := by
  rw [mod_of_lt_two_mul (by omega : k + 1 < 2 * (n + 1)),
    mod_of_lt_two_mul (by omega : k + n < 2 * (n + 1))]
  split_ifs <;> omega

end HardDataScalar

theorem scalarLocFun_injective (n s : ℕ) (k : Fin (n + 1)) :
    Function.Injective (scalarLocFun n s k) := by
  intro t₁ t₂ h
  have hk := k.isLt
  have hne := fun hn : 2 ≤ n => HardDataScalar.succ_mod_ne_add_mod hn hk
  unfold scalarLocFun at h
  apply Fin.ext
  split_ifs at h <;> simp only [Sum.inl.injEq, Sum.inr.injEq, Fin.mk.injEq] at h <;> omega

/-- The scalar row lists. -/
def scalarLoc (n s : ℕ) (k : Fin (n + 1)) : Fin s ↪ ScalarIndex n s :=
  ⟨scalarLocFun n s k, scalarLocFun_injective n s k⟩

/-! #### Coverage: which slot lists which neighbour -/

section Coverage

@[simp] theorem padSlot_apply (C : Type) (s : ℕ) (t : Fin s) :
    padSlot C s t = Sum.inr (Sum.inr t) := rfl

/-- A reference row lists itself in slot `0`. -/
theorem refLoc_zero {C : Type} [DecidableEq C] {s : ℕ} (hs : 0 < s) (r : Fin 2) :
    refLoc (C := C) hs r ⟨0, hs⟩ = Sum.inr (Sum.inl r) := by
  simp [refLoc]

/-- The energy-one (and zero-energy) reference row lists itself. -/
theorem ref_mem_range_fullLoc {C : Type} [DecidableEq C] {s : ℕ} (hs : 0 < s)
    (coreLoc : C → Fin s ↪ FullIndex C s) (r : Fin 2) :
    (Sum.inr (Sum.inl r) : FullIndex C s) ∈ Set.range (fullLoc hs coreLoc (Sum.inr (Sum.inl r))) :=
  ⟨⟨0, hs⟩, refLoc_zero hs r⟩

/-- Padding rows list the whole padding block. -/
theorem pad_mem_range_fullLoc {C : Type} [DecidableEq C] {s : ℕ} (hs : 0 < s)
    (coreLoc : C → Fin s ↪ FullIndex C s) (t t' : Fin s) :
    (Sum.inr (Sum.inr t') : FullIndex C s) ∈ Set.range (fullLoc hs coreLoc (Sum.inr (Sum.inr t))) :=
  ⟨t', rfl⟩

variable {n s : ℕ}

/-- Slot `0` of scalar row `k` lists `(k + 1) mod (n+1)`. -/
theorem scalarLocFun_zero (k : Fin (n + 1)) (t : Fin s) (ht : (t : ℕ) = 0) :
    scalarLocFun n s k t = Sum.inl ⟨((k : ℕ) + 1) % (n + 1), Nat.mod_lt _ (Nat.succ_pos n)⟩ := by
  rw [scalarLocFun, if_pos ht]

/-- For `n ≥ 2`, slot `1` of scalar row `k` lists `(k + n) mod (n+1)`. -/
theorem scalarLocFun_one (hn : 2 ≤ n) (k : Fin (n + 1)) (t : Fin s) (ht : (t : ℕ) = 1) :
    scalarLocFun n s k t = Sum.inl ⟨((k : ℕ) + n) % (n + 1), Nat.mod_lt _ (Nat.succ_pos n)⟩ := by
  rw [scalarLocFun, if_neg (by omega), if_pos ⟨ht, hn⟩]

/-- **Adjacency coverage** of the scalar rows (both chain neighbours; slots `0`
and `1`). -/
theorem scalarLoc_adj_mem (hs : 2 ≤ s) (k k' : Fin (n + 1))
    (h : (k' : ℕ) = k + 1 ∨ (k : ℕ) = k' + 1) :
    (Sum.inl k' : ScalarIndex n s) ∈ Set.range (scalarLoc n s k) := by
  have hk := k.isLt
  have hk' := k'.isLt
  rcases h with h | h
  · refine ⟨⟨0, by omega⟩, (scalarLocFun_zero (s := s) k ⟨0, by omega⟩ rfl).trans ?_⟩
    refine congrArg Sum.inl (Fin.ext ?_)
    show ((k : ℕ) + 1) % (n + 1) = k'
    rw [← h, Nat.mod_eq_of_lt k'.isLt]
  · rcases Nat.lt_or_ge n 2 with hn | hn
    · -- `n = 1`: the predecessor `0` of `1` is its cyclic successor
      refine ⟨⟨0, by omega⟩, (scalarLocFun_zero (s := s) k ⟨0, by omega⟩ rfl).trans ?_⟩
      refine congrArg Sum.inl (Fin.ext ?_)
      show ((k : ℕ) + 1) % (n + 1) = k'
      have hk0 : (k' : ℕ) = 0 := by omega
      rw [h, hk0, show n + 1 = 2 by omega]
    · refine ⟨⟨1, by omega⟩, (scalarLocFun_one (s := s) hn k ⟨1, by omega⟩ rfl).trans ?_⟩
      refine congrArg Sum.inl (Fin.ext ?_)
      show ((k : ℕ) + n) % (n + 1) = k'
      rw [h, show (k' : ℕ) + 1 + n = k' + (n + 1) by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt k'.isLt]

end Coverage

variable {n s : ℕ} {τ : ℝ}

/-! ### Precision family -/

/-- Fractional bits of the scalar words, `B = F + ⌈log₂ s⌉`. -/
def scalarBits (n s : ℕ) (τ : ℝ) : ℕ := chainBits n 1 τ + padExp s

/-- The bit each scalar address depends on: bit `k` for edge `k`. -/
def scalarAddr (n s : ℕ) : ScalarIndex n s × ScalarIndex n s → Option (Fin n)
  | (Sum.inl i, Sum.inl i') =>
    if h : (i : ℕ) = i' + 1 then some ⟨i', by have := i.isLt; omega⟩
    else if h' : (i' : ℕ) = i + 1 then some ⟨i, by have := i'.isLt; omega⟩
    else none
  | _ => none

/-- The integer words of the scalar Hamiltonian at scale `2^B`. -/
def scalarWord (n s : ℕ) (τ : ℝ) : ScalarIndex n s × ScalarIndex n s → Bool → ℤ
  | (Sum.inl i, Sum.inl i'), y =>
    if (i : ℕ) = i' + 1 then (if y then -1 else 1) * (chainNum n 1 τ i' : ℤ) * 2 ^ padExp s
    else if (i' : ℕ) = i + 1 then (if y then -1 else 1) * (chainNum n 1 τ i : ℤ) * 2 ^ padExp s
    else 0
  | (Sum.inr (Sum.inl r), Sum.inr (Sum.inl r')), _ =>
    if r = 1 ∧ r' = 1 then 2 ^ scalarBits n s τ else 0
  | (Sum.inr (Sum.inr _), Sum.inr (Sum.inr _)), _ => 2 ^ chainBits n 1 τ
  | _, _ => 0

/-- The scalar word table. -/
def scalarTable (n s : ℕ) (τ : ℝ) : BitTable (Fin n) (ScalarIndex n s × ScalarIndex n s) :=
  ⟨scalarAddr n s, scalarWord n s τ⟩

/-! #### The scalar words on each block (any hidden bits `x`) -/

section ScalarWords

variable (x : Fin n → Bool)

/-- Forward edge `k = i'`: the word `(-1)^{x_k} N_k 2^σ`. -/
theorem scalarTable_value_succ {i i' : Fin (n + 1)} (h : (i : ℕ) = i' + 1) :
    (scalarTable n s τ).value x (Sum.inl i, Sum.inl i') =
      (if x ⟨i', by have := i.isLt; omega⟩ then -1 else 1) * (chainNum n 1 τ i' : ℤ) *
        2 ^ padExp s := by
  have ha : (scalarTable n s τ).addr (Sum.inl i, Sum.inl i') =
      some ⟨i', by have := i.isLt; omega⟩ := by
    simp only [scalarTable, scalarAddr, dif_pos h]
  rw [BitTable.value_of_addr_some _ _ ha]
  simp only [scalarTable, scalarWord, if_pos h]

/-- Reverse edge `k = i`: the word `(-1)^{x_k} N_k 2^σ`. -/
theorem scalarTable_value_pred {i i' : Fin (n + 1)} (h : (i' : ℕ) = i + 1) :
    (scalarTable n s τ).value x (Sum.inl i, Sum.inl i') =
      (if x ⟨i, by have := i'.isLt; omega⟩ then -1 else 1) * (chainNum n 1 τ i : ℤ) *
        2 ^ padExp s := by
  have h' : ¬ (i : ℕ) = i' + 1 := by omega
  have ha : (scalarTable n s τ).addr (Sum.inl i, Sum.inl i') =
      some ⟨i, by have := i'.isLt; omega⟩ := by
    simp only [scalarTable, scalarAddr, dif_neg h', dif_pos h]
  rw [BitTable.value_of_addr_some _ _ ha]
  simp only [scalarTable, scalarWord, if_neg h', if_pos h]

theorem scalarTable_value_far {i i' : Fin (n + 1)} (h1 : (i : ℕ) ≠ i' + 1)
    (h2 : (i' : ℕ) ≠ i + 1) : (scalarTable n s τ).value x (Sum.inl i, Sum.inl i') = 0 := by
  simp only [BitTable.value, scalarTable, scalarWord, if_neg h1, if_neg h2]

/-- The reference block: the energy-one word `2^B` at `(refOne, refOne)`. -/
theorem scalarTable_value_ref (r r' : Fin 2) :
    (scalarTable n s τ).value x (Sum.inr (Sum.inl r), Sum.inr (Sum.inl r')) =
      if r = 1 ∧ r' = 1 then 2 ^ scalarBits n s τ else 0 := rfl

/-- The padding block: the word `2^F` (entry `2^{-σ}`). -/
theorem scalarTable_value_pad (t t' : Fin s) :
    (scalarTable n s τ).value x (Sum.inr (Sum.inr t), Sum.inr (Sum.inr t')) =
      2 ^ chainBits n 1 τ := rfl

theorem scalarTable_value_core_side (i : Fin (n + 1)) (r : Fin 2 ⊕ Fin s) :
    (scalarTable n s τ).value x (Sum.inl i, Sum.inr r) = 0 := by
  cases r <;> rfl

theorem scalarTable_value_side_core (r : Fin 2 ⊕ Fin s) (i : Fin (n + 1)) :
    (scalarTable n s τ).value x (Sum.inr r, Sum.inl i) = 0 := by
  rcases r with r | r <;> rfl

theorem scalarTable_value_ref_pad (r : Fin 2) (t : Fin s) :
    (scalarTable n s τ).value x (Sum.inr (Sum.inl r), Sum.inr (Sum.inr t)) = 0 := rfl

theorem scalarTable_value_pad_ref (t : Fin s) (r : Fin 2) :
    (scalarTable n s τ).value x (Sum.inr (Sum.inr t), Sum.inr (Sum.inl r)) = 0 := rfl

end ScalarWords

theorem scalarTable_bound (ad : ScalarIndex n s × ScalarIndex n s) (y : Bool) :
    -(2 : ℤ) ^ scalarBits n s τ < (scalarTable n s τ).word ad y ∧
      (scalarTable n s τ).word ad y ≤ 2 ^ scalarBits n s τ := by
  have hB : (0 : ℤ) < 2 ^ scalarBits n s τ := by positivity
  have hF : ∀ k, ((chainNum n 1 τ k : ℤ) * 2 ^ padExp s) < 2 ^ scalarBits n s τ := by
    intro k
    rw [scalarBits, pow_add]
    have h' : (chainNum n 1 τ k : ℤ) < 2 ^ chainBits n 1 τ := by
      exact_mod_cast chainNum_lt n 1 τ k
    exact mul_lt_mul_of_pos_right h' (by positivity)
  have hN : ∀ k, (0 : ℤ) ≤ (chainNum n 1 τ k : ℤ) * 2 ^ padExp s := fun k => by positivity
  have hpad : (2 : ℤ) ^ chainBits n 1 τ ≤ 2 ^ scalarBits n s τ :=
    pow_le_pow_right₀ (by norm_num) (by unfold scalarBits; omega)
  have hF0 : (0 : ℤ) < 2 ^ chainBits n 1 τ := by positivity
  obtain ⟨i | r | t, i' | r' | t'⟩ := ad <;> simp only [scalarTable, scalarWord]
  · have e1 := hF i
    have e2 := hF i'
    have e3 := hN i
    have e4 := hN i'
    split_ifs <;> (try simp only [neg_mul, one_mul]) <;> constructor <;> linarith
  all_goals first
    | (constructor <;> linarith)
    | (split_ifs <;> constructor <;> linarith)

theorem scalarTable_decode (x : Fin n → Bool) (i i' : ScalarIndex n s) :
    (((scalarTable n s τ).value x (i, i') : ℤ) : ℂ) / 2 ^ scalarBits n s τ =
      scalarHam n s τ x i i' := by
  unfold scalarHam
  rcases i with i | r | t <;> rcases i' with i' | r' | t'
  · rw [HardData.fullMatrix_core]
    by_cases h1 : (i : ℕ) = i' + 1
    · rw [scalarTable_value_succ x h1, HardData.scalarChain_succ _ x h1]
      exact HardData.scalarWord_div _ _
    · by_cases h2 : (i' : ℕ) = i + 1
      · rw [scalarTable_value_pred x h2, HardData.scalarChain_pred _ x h2]
        exact HardData.scalarWord_div _ _
      · rw [scalarTable_value_far x h1 h2, HardData.scalarChain_far _ x h1 h2]
        simp
  · rw [scalarTable_value_core_side, HardData.fullMatrix_core_side]; simp
  · rw [scalarTable_value_core_side, HardData.fullMatrix_core_side]; simp
  · rw [scalarTable_value_side_core, HardData.fullMatrix_side_core]; simp
  · rw [scalarTable_value_ref, HardData.fullMatrix_ref]
    split_ifs
    · exact HardData.topWord_div _
    · simp
  · rw [scalarTable_value_ref_pad, HardData.fullMatrix_ref_pad]; simp
  · rw [scalarTable_value_side_core, HardData.fullMatrix_side_core]; simp
  · rw [scalarTable_value_pad_ref, HardData.fullMatrix_pad_ref]; simp
  · rw [scalarTable_value_pad, HardData.fullMatrix_pad]
    exact HardData.padWord_div _

theorem scalarLoc_row (hs : 2 ≤ s) (x : Fin n → Bool) (i i' : ScalarIndex n s)
    (h : scalarHam n s τ x i i' ≠ 0) :
    i' ∈ Set.range (fullLoc (by omega) (scalarLoc n s) i) := by
  unfold scalarHam at h
  rcases i with k | r | t <;> rcases i' with k' | r' | t'
  · rw [HardData.fullMatrix_core] at h
    have adj : (k' : ℕ) = k + 1 ∨ (k : ℕ) = k' + 1 := by
      by_contra hc
      rw [not_or] at hc
      exact h (HardData.scalarChain_far _ x hc.2 hc.1)
    exact scalarLoc_adj_mem hs k k' adj
  · exact (h (HardData.fullMatrix_core_side _ _ _)).elim
  · exact (h (HardData.fullMatrix_core_side _ _ _)).elim
  · exact (h (HardData.fullMatrix_side_core _ _ _)).elim
  · rw [HardData.fullMatrix_ref] at h
    split_ifs at h with hr
    · obtain ⟨rfl, rfl⟩ := hr
      exact ref_mem_range_fullLoc _ _ _
    · exact (h rfl).elim
  · exact (h (HardData.fullMatrix_ref_pad _ _ _)).elim
  · exact (h (HardData.fullMatrix_side_core _ _ _)).elim
  · exact (h (HardData.fullMatrix_pad_ref _ _ _)).elim
  · exact pad_mem_range_fullLoc _ _ _ _

theorem scalarLoc_col (hs : 2 ≤ s) (x : Fin n → Bool) (i i' : ScalarIndex n s)
    (h : scalarHam n s τ x i i' ≠ 0) :
    i ∈ Set.range (fullLoc (by omega) (scalarLoc n s) i') := by
  have e := congrFun (congrFun (scalarHam_realSymmetric (n := n) (s := s) τ x).1 i) i'
  rw [Matrix.transpose_apply] at e
  exact scalarLoc_row hs x i' i (by rwa [e])

/-- **The signed scalar family** (precision lower bound) as native sparse
data: hidden input `n` bits, matrix `scalarHam n s τ`, exact words,
input-independent locators. -/
def scalarData (n s : ℕ) (τ : ℝ) (hs : 2 ≤ s) :
    Data (Fin n → Bool) (ScalarIndex n s) (Word (scalarBits n s τ)) s :=
  bitData s (scalarBits n s τ) (by omega) (padSlot _ s) (fullLoc (by omega) (scalarLoc n s))
    (scalarTable n s τ) (fun x => x) (scalarHam n s τ) scalarTable_bound scalarTable_decode
    (scalarLoc_row hs) (scalarLoc_col hs)

/-- The native workspace of the scalar data. -/
abbrev ScalarSpace (n s : ℕ) (τ : ℝ) : Type :=
  SparseFlagEmbedding.Space (ScalarIndex n s × ScalarIndex n s) (Word (scalarBits n s τ))

@[simp] theorem scalarData_matrix (hs : 2 ≤ s) :
    (scalarData n s τ hs).matrix = scalarHam n s τ := rfl

/-- The value table of the scalar data: the word of the queried bit. -/
theorem scalarData_table (hs : 2 ≤ s) (x : Fin n → Bool)
    (ad : ScalarIndex n s × ScalarIndex n s) :
    (scalarData n s τ hs).table x ad =
      (((scalarTable n s τ).value x ad : ℤ) : Word (scalarBits n s τ)) := rfl

/-- The row lists of the scalar data. -/
theorem scalarData_rowloc (hs : 2 ≤ s) (x : Fin n → Bool) (i : ScalarIndex n s) (k : Fin s) :
    (scalarData n s τ hs).rowloc x i k = fullLoc (by omega) (scalarLoc n s) i k := rfl

/-- **The scalar locators are input-independent** (the chain construction of Section `part:hsl`). -/
theorem scalarData_locators_const (hs : 2 ≤ s) (x x' : Fin n → Bool) :
    (scalarData n s τ hs).rowloc x = (scalarData n s τ hs).rowloc x' ∧
      (scalarData n s τ hs).colloc x = (scalarData n s τ hs).colloc x' ∧
      (scalarData n s τ hs).rowOracle x = (scalarData n s τ hs).rowOracle x' ∧
      (scalarData n s τ hs).columnOracle x = (scalarData n s τ hs).columnOracle x' :=
  bitData_locators_const x x'

end

end SparseLowerBounds.Hamiltonian
end
