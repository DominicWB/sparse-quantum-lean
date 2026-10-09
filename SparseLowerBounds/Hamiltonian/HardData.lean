import SparseLowerBounds.Hamiltonian.HardDataScalar

set_option synthInstance.maxHeartbeats 400000

section
/-!
# The hard families as release sparse-access data

Manuscript lines 2254-2289 and 2476-2487. The hard Hamiltonians of
`Hamiltonian/Instance` are packaged as `NativeSparseBlockEncoding.Data` by the
one-bit builder `bitData`, so the release's native primitives are the oracles
the lower bound is about. The shared locators (`padSlot`, `refLoc`, `fullLoc`)
and the signed scalar family (`scalarData`) are in `Hamiltonian/HardDataScalar`;
this module adds the search-decorated families and the data at the main
parameters.

**Words.** With `F = chainBits n a τ` fractional bits for the rounded weights
`b'_k = N_k/2^F` (`N_k < 2^F`), `m = 2^μ` and `σ = ⌈log₂ s⌉`:

* search families, `B = F + μ + σ`: gadget entry `b'_k (2/m - y)` has word
  `N_k (2 - 2^μ y) 2^σ` for the queried membership bit `y`; padding word
  `2^{F+μ}` (entry `2^{-σ}`); energy-one vertex word `2^B` (entry `1`);
* precision family, `B = F + σ` (`Hamiltonian/HardDataScalar`): entry
  `b'_k (-1)^{x_k}` has word `(-1)^{x_k} N_k 2^σ`; padding `2^F`; energy-one `2^B`.

Every word lies in `(-2^B, 2^B]` (`μ ≥ 1` for the search families), so the
position-independent decode `valMinAbs z/2^B` is exact. The address of each
word is its one bit (`searchAddr`: string `k`, position `gadgetPos a b` of the
`k`-th edge block); known entries make no query.

**Locators** are input-independent (lines 2283-2285): the slots are the padding
block; chain row `(k, a)` lists `((k+1) mod (n+1), b)` in slots `b < m`,
`((k-1) mod (n+1), b)` in slots `m + b` (only if `n ≥ 2`), and padding indices
otherwise (`searchLoc`); a reference row swaps itself with padding slot `0`;
padding rows list the padding block. The search families need `s ≥ 2m`.

**Main parameters** (`timeData`, `mixedMainData`, `precisionMainData`): the
time family at `n = timeN τ`, `a = timeC τ`; the mixed and precision families
at `n = precN τ ε = ⌊r/4⌋`, `a = 1`; both search families at `m = 2^{hsMu s}`.

**Proof steps** (helper statements). Coverage: `searchLocFun_of_lt`,
`searchLocFun_of_lt_two_mul`, `searchLoc_succ_mem`, `searchLoc_pred_mem`
(which slot lists which clock neighbour; for `n = 1` the predecessor is the
cyclic successor) and `ref/pad_mem_range_fullLoc`. Words: `searchTable_value_*`
(the word on each block of `FullIndex`), which with the entry and dyadic lemmas
of `Hamiltonian/HardDataEntries` give the decodes. Consumers:
`searchData_table`, `searchData_locators_const`.
-/

namespace SparseLowerBounds.Hamiltonian

noncomputable section
open SparseHamiltonian NativeSparseBlockEncoding

/-! ### Search locators -/

/-- The search row list of core row `p = (k, a)`. -/
def searchLocFun (n μ s : ℕ) (p : SearchCore n μ) (t : Fin s) : SearchIndex n μ s :=
  if h : (t : ℕ) < 2 ^ μ then
    Sum.inl (⟨((p.1 : ℕ) + 1) % (n + 1), Nat.mod_lt _ (Nat.succ_pos n)⟩, ⟨t, h⟩)
  else if h' : (t : ℕ) < 2 * 2 ^ μ ∧ 2 ≤ n then
    Sum.inl (⟨((p.1 : ℕ) + n) % (n + 1), Nat.mod_lt _ (Nat.succ_pos n)⟩, ⟨t - 2 ^ μ, by omega⟩)
  else Sum.inr (Sum.inr t)

theorem searchLocFun_injective (n μ s : ℕ) (p : SearchCore n μ) :
    Function.Injective (searchLocFun n μ s p) := by
  intro t₁ t₂ h
  have hne := fun hn : 2 ≤ n => HardDataScalar.succ_mod_ne_add_mod hn p.1.isLt
  unfold searchLocFun at h
  apply Fin.ext
  split_ifs at h <;> simp only [Sum.inl.injEq, Sum.inr.injEq, Prod.mk.injEq, Fin.mk.injEq] at h <;>
    omega

/-- The search row lists. -/
def searchLoc (n μ s : ℕ) (p : SearchCore n μ) : Fin s ↪ SearchIndex n μ s :=
  ⟨searchLocFun n μ s p, searchLocFun_injective n μ s p⟩

/-! #### Coverage: which slot lists which neighbour -/

section Coverage

variable {n μ s : ℕ}

/-- Slot `t < 2^μ` of core row `p` lists `((p.1 + 1) mod (n+1), t)`. -/
theorem searchLocFun_of_lt (p : SearchCore n μ) (t : Fin s) (ht : (t : ℕ) < 2 ^ μ) :
    searchLocFun n μ s p t =
      Sum.inl (⟨((p.1 : ℕ) + 1) % (n + 1), Nat.mod_lt _ (Nat.succ_pos n)⟩, ⟨t, ht⟩) := by
  rw [searchLocFun, dif_pos ht]

/-- For `n ≥ 2`, slot `2^μ + b` of core row `p` lists `((p.1 + n) mod (n+1), b)`. -/
theorem searchLocFun_of_lt_two_mul (hn : 2 ≤ n) (p : SearchCore n μ) (t : Fin s)
    (ht : 2 ^ μ ≤ (t : ℕ)) (ht' : (t : ℕ) < 2 * 2 ^ μ) :
    searchLocFun n μ s p t =
      Sum.inl (⟨((p.1 : ℕ) + n) % (n + 1), Nat.mod_lt _ (Nat.succ_pos n)⟩,
        ⟨t - 2 ^ μ, by omega⟩) := by
  rw [searchLocFun, dif_neg (by omega), dif_pos ⟨ht', hn⟩]

/-- **Successor coverage**: core row `p` lists every `q` one clock step ahead
(in slot `q.2`). -/
theorem searchLoc_succ_mem (hs : 2 * 2 ^ μ ≤ s) (p q : SearchCore n μ)
    (h : (q.1 : ℕ) = p.1 + 1) :
    (Sum.inl q : SearchIndex n μ s) ∈ Set.range (searchLoc n μ s p) := by
  refine ⟨⟨q.2, by have := q.2.isLt; omega⟩,
    (searchLocFun_of_lt (s := s) p ⟨q.2, by have := q.2.isLt; omega⟩ q.2.isLt).trans ?_⟩
  refine congrArg Sum.inl (Prod.ext (Fin.ext ?_) rfl)
  show ((p.1 : ℕ) + 1) % (n + 1) = q.1
  rw [← h, Nat.mod_eq_of_lt q.1.isLt]

/-- **Predecessor coverage**: core row `p` lists every `q` one clock step behind
(in slot `2^μ + q.2` for `n ≥ 2`; for `n = 1` the predecessor is the cyclic
successor, slot `q.2`). -/
theorem searchLoc_pred_mem (hs : 2 * 2 ^ μ ≤ s) (p q : SearchCore n μ)
    (h : (p.1 : ℕ) = q.1 + 1) :
    (Sum.inl q : SearchIndex n μ s) ∈ Set.range (searchLoc n μ s p) := by
  have hp := p.1.isLt
  have hq := q.1.isLt
  rcases Nat.lt_or_ge n 2 with hn | hn
  · -- `n = 1`: the predecessor `0` of clock `1` is its cyclic successor
    refine ⟨⟨q.2, by have := q.2.isLt; omega⟩,
      (searchLocFun_of_lt (s := s) p ⟨q.2, by have := q.2.isLt; omega⟩ q.2.isLt).trans ?_⟩
    refine congrArg Sum.inl (Prod.ext (Fin.ext ?_) rfl)
    show ((p.1 : ℕ) + 1) % (n + 1) = q.1
    have hq0 : (q.1 : ℕ) = 0 := by omega
    rw [h, hq0, show n + 1 = 2 by omega]
  · refine ⟨⟨2 ^ μ + q.2, by have := q.2.isLt; omega⟩,
      (searchLocFun_of_lt_two_mul (s := s) hn p ⟨2 ^ μ + q.2, by have := q.2.isLt; omega⟩
        (by show 2 ^ μ ≤ 2 ^ μ + (q.2 : ℕ); omega)
        (by have := q.2.isLt; show 2 ^ μ + (q.2 : ℕ) < 2 * 2 ^ μ; omega)).trans ?_⟩
    refine congrArg Sum.inl (Prod.ext (Fin.ext ?_) (Fin.ext ?_))
    · show ((p.1 : ℕ) + n) % (n + 1) = q.1
      rw [h, show (q.1 : ℕ) + 1 + n = q.1 + (n + 1) by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt q.1.isLt]
    · show 2 ^ μ + (q.2 : ℕ) - 2 ^ μ = q.2
      omega

/-- **Adjacency coverage** of the search rows (both clock neighbours). -/
theorem searchLoc_adj_mem (hs : 2 * 2 ^ μ ≤ s) (p q : SearchCore n μ)
    (h : (q.1 : ℕ) = p.1 + 1 ∨ (p.1 : ℕ) = q.1 + 1) :
    (Sum.inl q : SearchIndex n μ s) ∈ Set.range (searchLoc n μ s p) :=
  h.elim (searchLoc_succ_mem hs p q) (searchLoc_pred_mem hs p q)

end Coverage

/-! ### Search families -/

/-- Fractional bits of the search words, `B = F + μ + ⌈log₂ s⌉`. -/
def searchBits (n μ s : ℕ) (a τ : ℝ) : ℕ := chainBits n a τ + μ + padExp s

/-- The bit each search address depends on: `(k, gadgetPos a b)` for the
`k`-th edge block. -/
def searchAddr (n μ s : ℕ) : SearchIndex n μ s × SearchIndex n μ s → Option (Fin n × Fin (2 ^ μ))
  | (Sum.inl p, Sum.inl q) =>
    if h : (p.1 : ℕ) = q.1 + 1 then
      some (⟨q.1, by have := p.1.isLt; omega⟩, LinearSystems.gadgetPos p.2 q.2)
    else if h' : (q.1 : ℕ) = p.1 + 1 then
      some (⟨p.1, by have := q.1.isLt; omega⟩, LinearSystems.gadgetPos q.2 p.2)
    else none
  | _ => none

/-- The integer words of the search Hamiltonian at scale `2^B`. -/
def searchWord (n μ s : ℕ) (a τ : ℝ) : SearchIndex n μ s × SearchIndex n μ s → Bool → ℤ
  | (Sum.inl p, Sum.inl q), y =>
    if (p.1 : ℕ) = q.1 + 1 then
      (chainNum n a τ q.1 : ℤ) * (2 - 2 ^ μ * (if y then 1 else 0)) * 2 ^ padExp s
    else if (q.1 : ℕ) = p.1 + 1 then
      (chainNum n a τ p.1 : ℤ) * (2 - 2 ^ μ * (if y then 1 else 0)) * 2 ^ padExp s
    else 0
  | (Sum.inr (Sum.inl r), Sum.inr (Sum.inl r')), _ =>
    if r = 1 ∧ r' = 1 then 2 ^ searchBits n μ s a τ else 0
  | (Sum.inr (Sum.inr _), Sum.inr (Sum.inr _)), _ => 2 ^ (chainBits n a τ + μ)
  | _, _ => 0

/-- The search word table. -/
def searchTable (n μ s : ℕ) (a τ : ℝ) :
    BitTable (Fin n × Fin (2 ^ μ)) (SearchIndex n μ s × SearchIndex n μ s) :=
  ⟨searchAddr n μ s, searchWord n μ s a τ⟩

/-- The membership bits `(k, a) ↦ [j k = a]` of `n` one-hot strings. -/
def oneHotBits {n m : ℕ} (j : Fin n → Fin m) (ka : Fin n × Fin m) : Bool := decide (j ka.1 = ka.2)

variable {n μ s : ℕ} {a τ : ℝ}

/-! #### The search words on each block (any hidden bits `y`) -/

section SearchWords

variable (y : Fin n × Fin (2 ^ μ) → Bool)

/-- Forward edge `k = q.1`: the word of membership bit `(k, gadgetPos p.2 q.2)`. -/
theorem searchTable_value_succ {p q : SearchCore n μ} (h : (p.1 : ℕ) = q.1 + 1) :
    (searchTable n μ s a τ).value y (Sum.inl p, Sum.inl q) =
      (chainNum n a τ q.1 : ℤ) *
        (2 - 2 ^ μ * (if y (⟨q.1, by have := p.1.isLt; omega⟩, LinearSystems.gadgetPos p.2 q.2)
          then 1 else 0)) * 2 ^ padExp s := by
  have ha : (searchTable n μ s a τ).addr (Sum.inl p, Sum.inl q) =
      some (⟨q.1, by have := p.1.isLt; omega⟩, LinearSystems.gadgetPos p.2 q.2) := by
    simp only [searchTable, searchAddr, dif_pos h]
  rw [BitTable.value_of_addr_some _ _ ha]
  simp only [searchTable, searchWord, if_pos h]

/-- Reverse edge `k = p.1`: the word of membership bit `(k, gadgetPos q.2 p.2)`. -/
theorem searchTable_value_pred {p q : SearchCore n μ} (h : (q.1 : ℕ) = p.1 + 1) :
    (searchTable n μ s a τ).value y (Sum.inl p, Sum.inl q) =
      (chainNum n a τ p.1 : ℤ) *
        (2 - 2 ^ μ * (if y (⟨p.1, by have := q.1.isLt; omega⟩, LinearSystems.gadgetPos q.2 p.2)
          then 1 else 0)) * 2 ^ padExp s := by
  have h' : ¬ (p.1 : ℕ) = q.1 + 1 := by omega
  have ha : (searchTable n μ s a τ).addr (Sum.inl p, Sum.inl q) =
      some (⟨p.1, by have := q.1.isLt; omega⟩, LinearSystems.gadgetPos q.2 p.2) := by
    simp only [searchTable, searchAddr, dif_neg h', dif_pos h]
  rw [BitTable.value_of_addr_some _ _ ha]
  simp only [searchTable, searchWord, if_neg h', if_pos h]

theorem searchTable_value_far {p q : SearchCore n μ} (h1 : (p.1 : ℕ) ≠ q.1 + 1)
    (h2 : (q.1 : ℕ) ≠ p.1 + 1) : (searchTable n μ s a τ).value y (Sum.inl p, Sum.inl q) = 0 := by
  simp only [BitTable.value, searchTable, searchWord, if_neg h1, if_neg h2]

/-- The reference block: the energy-one word `2^B` at `(refOne, refOne)`. -/
theorem searchTable_value_ref (r r' : Fin 2) :
    (searchTable n μ s a τ).value y (Sum.inr (Sum.inl r), Sum.inr (Sum.inl r')) =
      if r = 1 ∧ r' = 1 then 2 ^ searchBits n μ s a τ else 0 := rfl

/-- The padding block: the word `2^{F+μ}` (entry `2^{-σ}`). -/
theorem searchTable_value_pad (t t' : Fin s) :
    (searchTable n μ s a τ).value y (Sum.inr (Sum.inr t), Sum.inr (Sum.inr t')) =
      2 ^ (chainBits n a τ + μ) := rfl

theorem searchTable_value_core_side (p : SearchCore n μ) (r : Fin 2 ⊕ Fin s) :
    (searchTable n μ s a τ).value y (Sum.inl p, Sum.inr r) = 0 := by
  cases r <;> rfl

theorem searchTable_value_side_core (r : Fin 2 ⊕ Fin s) (p : SearchCore n μ) :
    (searchTable n μ s a τ).value y (Sum.inr r, Sum.inl p) = 0 := by
  rcases r with r | r <;> rfl

theorem searchTable_value_ref_pad (r : Fin 2) (t : Fin s) :
    (searchTable n μ s a τ).value y (Sum.inr (Sum.inl r), Sum.inr (Sum.inr t)) = 0 := rfl

theorem searchTable_value_pad_ref (t : Fin s) (r : Fin 2) :
    (searchTable n μ s a τ).value y (Sum.inr (Sum.inr t), Sum.inr (Sum.inl r)) = 0 := rfl

end SearchWords

theorem searchTable_bound (hμ : 1 ≤ μ) (ad : SearchIndex n μ s × SearchIndex n μ s) (y : Bool) :
    -(2 : ℤ) ^ searchBits n μ s a τ < (searchTable n μ s a τ).word ad y ∧
      (searchTable n μ s a τ).word ad y ≤ 2 ^ searchBits n μ s a τ := by
  have hB : (0 : ℤ) < 2 ^ searchBits n μ s a τ := by positivity
  have hμ2 : (2 : ℤ) ≤ 2 ^ μ := by
    have := Nat.pow_le_pow_right (by norm_num : 0 < 2) hμ
    exact_mod_cast this
  -- `N 2^σ ≥ 0`, `N 2^μ 2^σ < 2^B` and `2 N 2^σ ≤ N 2^μ 2^σ`
  have hN : ∀ k, (0 : ℤ) ≤ (chainNum n a τ k : ℤ) * 2 ^ padExp s := fun k => by positivity
  have hF : ∀ k, (chainNum n a τ k : ℤ) * 2 ^ μ * 2 ^ padExp s < 2 ^ searchBits n μ s a τ := by
    intro k
    rw [searchBits, pow_add, pow_add]
    have h' : (chainNum n a τ k : ℤ) < 2 ^ chainBits n a τ := by
      exact_mod_cast chainNum_lt n a τ k
    exact mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right h' (by positivity)) (by positivity)
  have hT : ∀ k, 2 * ((chainNum n a τ k : ℤ) * 2 ^ padExp s) ≤
      (chainNum n a τ k : ℤ) * 2 ^ μ * 2 ^ padExp s := fun k => by
    have := mul_le_mul_of_nonneg_right hμ2 (hN k)
    linarith [this]
  have hpad : (2 : ℤ) ^ (chainBits n a τ + μ) ≤ 2 ^ searchBits n μ s a τ :=
    pow_le_pow_right₀ (by norm_num) (by unfold searchBits; omega)
  have hF0 : (0 : ℤ) < 2 ^ (chainBits n a τ + μ) := by positivity
  obtain ⟨p | r | t, q | r' | t'⟩ := ad <;> simp only [searchTable, searchWord]
  · have e1 := hF p.1
    have e2 := hF q.1
    have e3 := hN p.1
    have e4 := hN q.1
    have e5 := hT p.1
    have e6 := hT q.1
    split_ifs <;> constructor <;> nlinarith
  all_goals first
    | (constructor <;> linarith)
    | (split_ifs <;> constructor <;> linarith)

/-- The gadget entry from the queried membership bit. -/
theorem gadget_oneHotBits (j : Fin n → Fin (2 ^ μ)) (k : Fin n) (u v : Fin (2 ^ μ)) :
    (2 / ((2 ^ μ : ℕ) : ℂ)) - (if oneHotBits j (k, LinearSystems.gadgetPos u v) then 1 else 0) =
      LinearSystems.gadget (2 ^ μ) (j k) u v := by
  simp only [LinearSystems.gadget, Matrix.of_apply, oneHotBits, decide_eq_true_eq]
  by_cases h : j k = LinearSystems.gadgetPos u v
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (Ne.symm h)]

theorem searchTable_decode (j : Fin n → Fin (2 ^ μ)) (i i' : SearchIndex n μ s) :
    (((searchTable n μ s a τ).value (oneHotBits j) (i, i') : ℤ) : ℂ) / 2 ^ searchBits n μ s a τ =
      searchHam n μ s a τ j i i' := by
  unfold searchHam
  rcases i with p | r | t <;> rcases i' with q | r' | t'
  · rw [HardData.fullMatrix_core]
    by_cases h1 : (p.1 : ℕ) = q.1 + 1
    · rw [searchTable_value_succ _ h1, HardData.searchChain_succ _ j h1, ← gadget_oneHotBits]
      exact HardData.searchWord_div _ _
    · by_cases h2 : (q.1 : ℕ) = p.1 + 1
      · rw [searchTable_value_pred _ h2, HardData.searchChain_pred _ j h2, ← gadget_oneHotBits]
        exact HardData.searchWord_div _ _
      · rw [searchTable_value_far _ h1 h2, HardData.searchChain_far _ j h1 h2]
        simp
  · rw [searchTable_value_core_side, HardData.fullMatrix_core_side]; simp
  · rw [searchTable_value_core_side, HardData.fullMatrix_core_side]; simp
  · rw [searchTable_value_side_core, HardData.fullMatrix_side_core]; simp
  · rw [searchTable_value_ref, HardData.fullMatrix_ref]
    split_ifs
    · exact HardData.topWord_div _
    · simp
  · rw [searchTable_value_ref_pad, HardData.fullMatrix_ref_pad]; simp
  · rw [searchTable_value_side_core, HardData.fullMatrix_side_core]; simp
  · rw [searchTable_value_pad_ref, HardData.fullMatrix_pad_ref]; simp
  · rw [searchTable_value_pad, HardData.fullMatrix_pad]
    exact HardData.padWord_div _

theorem pos_of_two_mul_two_pow_le (hs : 2 * 2 ^ μ ≤ s) : 0 < s :=
  lt_of_lt_of_le (by positivity) hs

theorem searchLoc_row (hs : 2 * 2 ^ μ ≤ s) (j : Fin n → Fin (2 ^ μ)) (i i' : SearchIndex n μ s)
    (h : searchHam n μ s a τ j i i' ≠ 0) :
    i' ∈ Set.range (fullLoc (pos_of_two_mul_two_pow_le hs) (searchLoc n μ s) i) := by
  unfold searchHam at h
  rcases i with p | r | t <;> rcases i' with q | r' | t'
  · rw [HardData.fullMatrix_core] at h
    have adj : (q.1 : ℕ) = p.1 + 1 ∨ (p.1 : ℕ) = q.1 + 1 := by
      by_contra hc
      rw [not_or] at hc
      exact h (HardData.searchChain_far _ j hc.2 hc.1)
    exact searchLoc_adj_mem hs p q adj
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

theorem searchLoc_col (hs : 2 * 2 ^ μ ≤ s) (j : Fin n → Fin (2 ^ μ)) (i i' : SearchIndex n μ s)
    (h : searchHam n μ s a τ j i i' ≠ 0) :
    i ∈ Set.range (fullLoc (pos_of_two_mul_two_pow_le hs) (searchLoc n μ s) i') := by
  have e := congrFun (congrFun (searchHam_realSymmetric (n := n) (μ := μ) (s := s) a τ j).1 i) i'
  rw [Matrix.transpose_apply] at e
  exact searchLoc_row hs j i' i (by rwa [e])

/-- **The search-decorated family** (time and mixed lower bounds) as native
sparse data: hidden input `n` one-hot strings of length `2^μ`, matrix
`searchHam n μ s a τ`, exact words, input-independent locators. -/
def searchData (n μ s : ℕ) (a τ : ℝ) (hμ : 1 ≤ μ) (hs : 2 * 2 ^ μ ≤ s) :
    Data (Fin n → Fin (2 ^ μ)) (SearchIndex n μ s) (Word (searchBits n μ s a τ)) s :=
  bitData s (searchBits n μ s a τ) (pos_of_two_mul_two_pow_le hs) (padSlot _ s)
    (fullLoc (pos_of_two_mul_two_pow_le hs) (searchLoc n μ s)) (searchTable n μ s a τ)
    oneHotBits (searchHam n μ s a τ) (searchTable_bound hμ) searchTable_decode
    (searchLoc_row hs) (searchLoc_col hs)

/-- The native workspace of the search data. -/
abbrev SearchSpace (n μ s : ℕ) (a τ : ℝ) : Type :=
  SparseFlagEmbedding.Space (SearchIndex n μ s × SearchIndex n μ s) (Word (searchBits n μ s a τ))

@[simp] theorem searchData_matrix (hμ : 1 ≤ μ) (hs : 2 * 2 ^ μ ≤ s) :
    (searchData n μ s a τ hμ hs).matrix = searchHam n μ s a τ := rfl

/-- The value table of the search data: the word of the queried membership bit. -/
theorem searchData_table (hμ : 1 ≤ μ) (hs : 2 * 2 ^ μ ≤ s) (j : Fin n → Fin (2 ^ μ))
    (ad : SearchIndex n μ s × SearchIndex n μ s) :
    (searchData n μ s a τ hμ hs).table j ad =
      (((searchTable n μ s a τ).value (oneHotBits j) ad : ℤ) : Word (searchBits n μ s a τ)) :=
  rfl

/-- The row lists of the search data. -/
theorem searchData_rowloc (hμ : 1 ≤ μ) (hs : 2 * 2 ^ μ ≤ s) (j : Fin n → Fin (2 ^ μ))
    (i : SearchIndex n μ s) (k : Fin s) :
    (searchData n μ s a τ hμ hs).rowloc j i k =
      fullLoc (pos_of_two_mul_two_pow_le hs) (searchLoc n μ s) i k := rfl

/-- **The search locators are input-independent** (lines 2283-2286). -/
theorem searchData_locators_const (hμ : 1 ≤ μ) (hs : 2 * 2 ^ μ ≤ s)
    (j j' : Fin n → Fin (2 ^ μ)) :
    (searchData n μ s a τ hμ hs).rowloc j = (searchData n μ s a τ hμ hs).rowloc j' ∧
      (searchData n μ s a τ hμ hs).colloc j = (searchData n μ s a τ hμ hs).colloc j' ∧
      (searchData n μ s a τ hμ hs).rowOracle j = (searchData n μ s a τ hμ hs).rowOracle j' ∧
      (searchData n μ s a τ hμ hs).columnOracle j = (searchData n μ s a τ hμ hs).columnOracle j' :=
  bitData_locators_const j j'

/-! ### The families at the parameters of Theorem `hsl:thm:main` -/

/-- **Time family** (lines 2379-2409): `n = timeN τ`, `a = timeC τ`,
`m = 2^{hsMu s}`. -/
def timeData (τ : ℝ) (s : ℕ) (hs : 32 ≤ s) :
    Data (Fin (timeN τ) → Fin (2 ^ hsMu s)) (SearchIndex (timeN τ) (hsMu s) s)
      (Word (searchBits (timeN τ) (hsMu s) s (timeC τ) τ)) s :=
  searchData (timeN τ) (hsMu s) s (timeC τ) τ (one_le_hsMu hs) (two_mul_hsM_le hs)

/-- **Mixed family** at the main parameters (lines 2439-2444): `n = precN τ ε`,
`a = 1`, `m = 2^{hsMu s}`. -/
def mixedMainData (τ ε : ℝ) (s : ℕ) (hs : 32 ≤ s) :
    Data (Fin (precN τ ε) → Fin (2 ^ hsMu s)) (SearchIndex (precN τ ε) (hsMu s) s)
      (Word (searchBits (precN τ ε) (hsMu s) s 1 τ)) s :=
  searchData (precN τ ε) (hsMu s) s 1 τ (one_le_hsMu hs) (two_mul_hsM_le hs)

/-- **Precision family** at the main parameters (lines 2435-2438):
`n = precN τ ε`. -/
def precisionMainData (τ ε : ℝ) (s : ℕ) (hs : 32 ≤ s) :
    Data (Fin (precN τ ε) → Bool) (ScalarIndex (precN τ ε) s) (Word (scalarBits (precN τ ε) s τ)) s :=
  scalarData (precN τ ε) s τ (by omega)

end

end SparseLowerBounds.Hamiltonian
end
