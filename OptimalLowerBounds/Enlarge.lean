import OptimalLowerBounds.Embedding

set_option synthInstance.maxHeartbeats 400000

/-!
# The enlarged hard families of Proposition `hsl:prop:two-norm`

The proof of Proposition `hsl:prop:two-norm` (section `twonorml:sec:lower`) uses
`H_X = μ H_X⁽⁰⁾ ⊗ 𝟙_m 𝟙_mᵀ` (eq. `twonorml:eq:enlargement`). Every original nonzero is repeated
`m` times in each enlarged row, so the sparsity is multiplied by `m`, and every row and column
Euclidean norm by `μ√m`. The isolated energy-one block becomes an `m × m` block with every entry
`μ` and every row and column norm `μ√m = η`, so it attains both new promises. The entries remain
dyadic, with no division by `m` in the entry formula. "A
value query to `H_X` costs at most two old value queries [...] The enlarged supports and locator
extensions are known. Thus the reduction has constant query overhead, including inverses."

The hard families of `hsl:thm:main` are built by the one-bit word-table builder
`SparseLowerBounds.Hamiltonian.bitData`. This module builds the enlargement of any such data
with a real coefficient `c ≠ 0` (`μ = |c|`; `c < 0` treats negative times):

* `enlargeTable T m`: the word of the enlarged address `((i, a), (j, b))` is the word of
  `(i, j)`, depending on the same hidden bit (`enlargeTable_value`);
* `enlargeSlot`, `enlargeLoc`: the slots `Fin (s * m) ≃ Fin s × Fin m` and the location lists
  `(i, a) ↦ ((loc i k, b))_{k, b}`, input-independent;
* `enlargeBit`: the `bitData` of the enlarged table with matrix `H ⊗ 𝟙𝟙ᵀ` (scale `1`);
* **`enlargeData`**: the same native data with the public decoder `z ↦ c · valMinAbs z / 2^B` (scale
  `|c|`) and matrix `c H ⊗ 𝟙𝟙ᵀ` (`enlargeMatrix`). Its native primitives are literally those of
  `enlargeBit` (`oracles_enlargeData`), so every value call costs two Boolean queries to the
  **same** hidden bits and every location call none (`implementsOn_enlargeData`,
  `implementsOn_enlargeData_spec`): the multiplication by `c` is in the public decoder, so the
  manuscript's "at most two old value queries" becomes one;
* `TwoNormInstance D c m`: the instance properties of the proposition (real symmetric, entries
  of modulus at most `|c|`, attained, row and column Euclidean norms at most `|c|√m`, attained,
  maximum sparsity exactly the sparsity parameter, exact words `c v/2^B`, input-independent
  locators); **`enlargeData_twoNormInstance`** from `HardInstance` and an entry of modulus one;
* the enlarged families `searchTwo`, `scalarTwo` and, at the parameters of `hsl:thm:main`,
  `timeTwo`, `mixedTwo`, `precisionTwo`, with their certificates (`searchTwoAccess`,
  `scalarTwoAccess`, …) and instance properties (`two_instances`).
-/

namespace OptimalLowerBounds

noncomputable section
set_option autoImplicit false
open SparseHamiltonian NativeSparseBlockEncoding OracleCircuit SparseLowerBounds
open SparseLowerBounds.Hamiltonian SparseLowerBounds.Hamiltonian.HsRelease Readout
open scoped InnerProduct InnerProductSpace Matrix
set_option maxRecDepth 4096
set_option synthInstance.maxSize 4096

/-! ### Enlarged tables, slots and lists -/

section Tables

variable {N : Type} {I : Type*}

/-- The original address `(i, j)` of an enlarged address `((i, a), (j, b))`. -/
def pairProj {m : ℕ} (A : (N × Fin m) × (N × Fin m)) : N × N := (A.1.1, A.2.1)

/-- **The enlarged word table**: the word of `((i, a), (j, b))` is that of `(i, j)`. -/
def enlargeTable (T : BitTable I (N × N)) (m : ℕ) : BitTable I ((N × Fin m) × (N × Fin m)) where
  addr A := T.addr (pairProj A)
  word A b := T.word (pairProj A) b

theorem enlargeTable_bit (T : BitTable I (N × N)) (m : ℕ) (y : I → Bool)
    (A : (N × Fin m) × (N × Fin m)) : (enlargeTable T m).bit y A = T.bit y (pairProj A) := rfl

theorem enlargeTable_value (T : BitTable I (N × N)) (m : ℕ) (y : I → Bool)
    (A : (N × Fin m) × (N × Fin m)) : (enlargeTable T m).value y A = T.value y (pairProj A) := rfl

/-- The enlarged slots: `k ↦ (slot k₁, k₂)`, `(k₁, k₂) = finProdFinEquiv.symm k`. -/
def enlargeSlot {s : ℕ} (slot : Fin s ↪ N) (m : ℕ) : Fin (s * m) ↪ N × Fin m where
  toFun k := (slot (finProdFinEquiv.symm k).1, (finProdFinEquiv.symm k).2)
  inj' := by
    intro k k' h
    simp only [Prod.mk.injEq] at h
    exact finProdFinEquiv.symm.injective (Prod.ext (slot.injective h.1) h.2)

theorem enlargeSlot_apply {s : ℕ} (slot : Fin s ↪ N) (m : ℕ) (k : Fin s) (b : Fin m) :
    enlargeSlot slot m (finProdFinEquiv (k, b)) = (slot k, b) := by
  simp only [enlargeSlot, Function.Embedding.coeFn_mk, Equiv.symm_apply_apply]

/-- The enlarged location lists: row `(i, a)` lists `(loc i k, b)`. -/
def enlargeLoc {s : ℕ} (loc : N → Fin s ↪ N) (m : ℕ) (ia : N × Fin m) : Fin (s * m) ↪ N × Fin m :=
  enlargeSlot (loc ia.1) m

theorem mem_range_enlargeLoc {s : ℕ} (loc : N → Fin s ↪ N) (m : ℕ) (ia : N × Fin m)
    {j : N} (hj : j ∈ Set.range (loc ia.1)) (b : Fin m) :
    (j, b) ∈ Set.range (enlargeLoc loc m ia) := by
  obtain ⟨k, hk⟩ := hj
  exact ⟨finProdFinEquiv (k, b), by rw [enlargeLoc, enlargeSlot_apply, hk]⟩

end Tables

/-! ### The enlarged data -/

section Data

variable {N : Type} [Fintype N] [DecidableEq N] {X I : Type*} {s B : ℕ}

/-- **The unscaled enlargement** `H ⊗ 𝟙𝟙ᵀ` of one-bit native data, as one-bit native data. -/
def enlargeBit (hs : 0 < s) (slot : Fin s ↪ N) (loc : N → Fin s ↪ N) (T : BitTable I (N × N))
    (y : X → I → Bool) (H : X → Matrix N N ℂ)
    (hbound : ∀ a b, -(2 : ℤ) ^ B < T.word a b ∧ T.word a b ≤ 2 ^ B)
    (hdec : ∀ x i j, ((T.value (y x) (i, j) : ℤ) : ℂ) / 2 ^ B = H x i j)
    (hrow : ∀ x i j, H x i j ≠ 0 → j ∈ Set.range (loc i))
    (hcol : ∀ x i j, H x i j ≠ 0 → i ∈ Set.range (loc j)) (m : ℕ) (hm : 0 < m) :
    Data X (N × Fin m) (Word B) (s * m) :=
  bitData (s * m) B (Nat.mul_pos hs hm) (enlargeSlot slot m) (enlargeLoc loc m)
    (enlargeTable T m) y (fun x => enlargeMatrix (H x) m 1)
    (fun A b => hbound (pairProj A) b)
    (fun x ia jb => by
      rw [enlargeTable_value, enlargeMatrix_apply, Complex.ofReal_one, one_mul]
      exact hdec x ia.1 jb.1)
    (fun x ia jb h => by
      rw [enlargeMatrix_apply, Complex.ofReal_one, one_mul] at h
      exact mem_range_enlargeLoc loc m ia (hrow x ia.1 jb.1 h) jb.2)
    (fun x ia jb h => by
      rw [enlargeMatrix_apply, Complex.ofReal_one, one_mul] at h
      exact mem_range_enlargeLoc loc m jb (hcol x ia.1 jb.1 h) ia.2)

/-- **The enlarged data** `c H ⊗ 𝟙𝟙ᵀ` (eq. `twonorml:eq:enlargement` with `c = μ`): the words,
locators and native primitives of `enlargeBit`, with the fixed public decoder
`z ↦ c · valMinAbs z / 2^B` of scale `|c|`. -/
def enlargeData (hs : 0 < s) (slot : Fin s ↪ N) (loc : N → Fin s ↪ N) (T : BitTable I (N × N))
    (y : X → I → Bool) (H : X → Matrix N N ℂ)
    (hbound : ∀ a b, -(2 : ℤ) ^ B < T.word a b ∧ T.word a b ≤ 2 ^ B)
    (hdec : ∀ x i j, ((T.value (y x) (i, j) : ℤ) : ℂ) / 2 ^ B = H x i j)
    (hrow : ∀ x i j, H x i j ≠ 0 → j ∈ Set.range (loc i))
    (hcol : ∀ x i j, H x i j ≠ 0 → i ∈ Set.range (loc j)) (m : ℕ) (hm : 0 < m) (c : ℝ)
    (hc : c ≠ 0) : Data X (N × Fin m) (Word B) (s * m) :=
  { enlargeBit hs slot loc T y H hbound hdec hrow hcol m hm with
    scale := |c|
    scale_pos := abs_pos.mpr hc
    matrix := fun x => enlargeMatrix (H x) m c
    decode := fun _ z => (c : ℂ) * wordDecode B z
    decode_bound := fun _ z => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_of_le_one_right (abs_nonneg c) (norm_wordDecode_le B z)
    decoded := fun x ia jb => by
      have h := (enlargeBit hs slot loc T y H hbound hdec hrow hcol m hm).decoded x ia jb
      change wordDecode B _ = enlargeMatrix (H x) m 1 ia jb at h
      rw [enlargeMatrix_apply, Complex.ofReal_one, one_mul] at h
      change (c : ℂ) * wordDecode B _ = enlargeMatrix (H x) m c ia jb
      rw [enlargeMatrix_apply, h]
    row_covers := fun x ia jb h => by
      refine (enlargeBit hs slot loc T y H hbound hdec hrow hcol m hm).row_covers x ia jb ?_
      change enlargeMatrix (H x) m 1 ia jb ≠ 0
      change enlargeMatrix (H x) m c ia jb ≠ 0 at h
      rw [enlargeMatrix_apply, Complex.ofReal_one, one_mul]
      rw [enlargeMatrix_apply] at h
      exact right_ne_zero_of_mul h
    column_covers := fun x ia jb h => by
      refine (enlargeBit hs slot loc T y H hbound hdec hrow hcol m hm).column_covers x ia jb ?_
      change enlargeMatrix (H x) m 1 ia jb ≠ 0
      change enlargeMatrix (H x) m c ia jb ≠ 0 at h
      rw [enlargeMatrix_apply, Complex.ofReal_one, one_mul]
      rw [enlargeMatrix_apply] at h
      exact right_ne_zero_of_mul h }

variable {hs : 0 < s} {slot : Fin s ↪ N} {loc : N → Fin s ↪ N} {T : BitTable I (N × N)}
  {y : X → I → Bool} {H : X → Matrix N N ℂ}
  {hbound : ∀ a b, -(2 : ℤ) ^ B < T.word a b ∧ T.word a b ≤ 2 ^ B}
  {hdec : ∀ x i j, ((T.value (y x) (i, j) : ℤ) : ℂ) / 2 ^ B = H x i j}
  {hrow : ∀ x i j, H x i j ≠ 0 → j ∈ Set.range (loc i)}
  {hcol : ∀ x i j, H x i j ≠ 0 → i ∈ Set.range (loc j)} {m : ℕ} {hm : 0 < m} {c : ℝ}
  {hc : c ≠ 0}

@[simp] theorem enlargeData_matrix :
    (enlargeData hs slot loc T y H hbound hdec hrow hcol m hm c hc).matrix =
      fun x => enlargeMatrix (H x) m c := rfl

/-- **The native primitives of the enlarged data are those of `enlargeBit`**: the coefficient
lives in the public decoder. -/
theorem oracles_enlargeData (l : Query) :
    oracles (enlargeData hs slot loc T y H hbound hdec hrow hcol m hm c hc) l =
      oracles (enlargeBit hs slot loc T y H hbound hdec hrow hcol m hm) l := by
  cases l <;> rfl

variable [Fintype I] [DecidableEq I]

/-- **Every native primitive of the enlarged data is a `hardCost`-query Boolean program** on the
clean-ancilla encoding, over the phase oracle of the same hidden bits (two queries per value call,
none per location call). -/
theorem implementsOn_enlargeData (l : Query) :
    EncodedOracle.ImplementsOn (fun x => (bitBooleanFamily (enlargeTable T m) (Word B)).phase (y x))
      (oracles (enlargeData hs slot loc T y H hbound hdec hrow hcol m hm c hc) l)
      (ancillaEmbed (SparseFlagEmbedding.Space ((N × Fin m) × (N × Fin m)) (Word B)))
      (hardCost l) := by
  rw [oracles_enlargeData]
  exact implementsOn_bitData _ _ _ _ _ _ _ _ _ _ l

/-- `implementsOn_enlargeData` with an untouched spectator register. -/
theorem implementsOn_enlargeData_spec (Ω : Type*) [Fintype Ω] (l : Query) :
    EncodedOracle.ImplementsOn (fun x => (bitSpecFamily Ω (enlargeTable T m) (Word B)).phase (y x))
      (specOracles Ω (enlargeData hs slot loc T y H hbound hdec hrow hcol m hm c hc) l)
      (ancillaEmbed (Joint Ω (SparseFlagEmbedding.Space ((N × Fin m) × (N × Fin m)) (Word B))))
      (hardCost l) := by
  have h : specOracles Ω (enlargeData hs slot loc T y H hbound hdec hrow hcol m hm c hc) l =
      specOracles Ω (enlargeBit hs slot loc T y H hbound hdec hrow hcol m hm) l := by
    cases l <;> rfl
  rw [h]
  exact implementsOn_bitData_spec Ω _ _ _ _ _ _ _ _ _ _ l

end Data

/-! ### The instance properties -/

/-- **The instance properties of Proposition `hsl:prop:two-norm`** for native data with words
`Word B` and coefficient `c` (`μ = |c|`, `η = |c|√m`): real symmetric (hence Hermitian); every
entry of modulus at most `|c|`, attained; row and column Euclidean norms at most `|c|√m`,
attained; maximum row and column sparsity exactly `s`; exact words with the
position-independent decoder `z ↦ c · valMinAbs z / 2^B` of scale `|c|`, every entry `c v/2^B`
with `-2^B < v ≤ 2^B`; input-independent location lists and locator extensions. -/
structure TwoNormInstance {X N : Type*} [Fintype N] [DecidableEq N] {B s : ℕ}
    (D : Data X N (Word B) s) (c : ℝ) (m : ℕ) : Prop where
  transpose_eq : ∀ x, (D.matrix x)ᵀ = D.matrix x
  real : ∀ x i j, star (D.matrix x i j) = D.matrix x i j
  isHermitian : ∀ x, (D.matrix x).IsHermitian
  entry_le : ∀ x i j, ‖D.matrix x i j‖ ≤ |c|
  entry_attained : ∀ x, ∃ i j, ‖D.matrix x i j‖ = |c|
  row_norm_le : ∀ x i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ (|c| * Real.sqrt m) ^ 2
  col_norm_le : ∀ x j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ (|c| * Real.sqrt m) ^ 2
  row_norm_attained : ∀ x, ∃ i, ∑ j, ‖D.matrix x i j‖ ^ 2 = (|c| * Real.sqrt m) ^ 2
  col_norm_attained : ∀ x, ∃ j, ∑ i, ‖D.matrix x i j‖ ^ 2 = (|c| * Real.sqrt m) ^ 2
  row_sparsity_le : ∀ x i, (Finset.univ.filter fun j => D.matrix x i j ≠ 0).card ≤ s
  col_sparsity_le : ∀ x j, (Finset.univ.filter fun i => D.matrix x i j ≠ 0).card ≤ s
  row_sparsity_attained : ∀ x, ∃ i, (Finset.univ.filter fun j => D.matrix x i j ≠ 0).card = s
  col_sparsity_attained : ∀ x, ∃ j, (Finset.univ.filter fun i => D.matrix x i j ≠ 0).card = s
  scale_eq : D.scale = |c|
  decode_eq : ∀ a z, D.decode a z = (c : ℂ) * wordDecode B z
  dyadic : ∀ x i j, ∃ v : ℤ, -(2 : ℤ) ^ B < v ∧ v ≤ 2 ^ B ∧
    D.matrix x i j = (c : ℂ) * ((v : ℂ) / 2 ^ B)
  locators_const : ∀ x x', D.rowloc x = D.rowloc x' ∧ D.colloc x = D.colloc x' ∧
    D.rowOracle x = D.rowOracle x' ∧ D.columnOracle x = D.columnOracle x'

section Instance

variable {N : Type} [Fintype N] [DecidableEq N] {X I : Type*} {s B : ℕ}

omit [DecidableEq N] in
/-- The nonzero entries of row `(i, a)` of `c H ⊗ 𝟙𝟙ᵀ` are those of row `i` of `H`, in every
block column. -/
theorem filter_enlarge_row (H : Matrix N N ℂ) (m : ℕ) {c : ℝ} (hc : c ≠ 0) (ia : N × Fin m) :
    (Finset.univ.filter fun jb : N × Fin m => enlargeMatrix H m c ia jb ≠ 0) =
      (Finset.univ.filter fun j => H ia.1 j ≠ 0) ×ˢ Finset.univ := by
  ext ⟨j, b⟩
  simp [enlargeMatrix_apply, hc]

omit [DecidableEq N] in
/-- The nonzero entries of column `(j, b)`. -/
theorem filter_enlarge_col (H : Matrix N N ℂ) (m : ℕ) {c : ℝ} (hc : c ≠ 0) (jb : N × Fin m) :
    (Finset.univ.filter fun ia : N × Fin m => enlargeMatrix H m c ia jb ≠ 0) =
      (Finset.univ.filter fun i => H i jb.1 ≠ 0) ×ˢ Finset.univ := by
  ext ⟨i, a⟩
  simp [enlargeMatrix_apply, hc]

omit [DecidableEq N] in
/-- Row masses of `c H ⊗ 𝟙𝟙ᵀ`: `m c²` times those of `H`. -/
theorem row_mass_enlarge (H : Matrix N N ℂ) (m : ℕ) (c : ℝ) (ia : N × Fin m) :
    ∑ jb : N × Fin m, ‖enlargeMatrix H m c ia jb‖ ^ 2 =
      (|c| * Real.sqrt m) ^ 2 * ∑ j, ‖H ia.1 j‖ ^ 2 := by
  rw [Fintype.sum_prod_type, mul_pow, Real.sq_sqrt (Nat.cast_nonneg m), Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [enlargeMatrix_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

omit [DecidableEq N] in
/-- Column masses of `c H ⊗ 𝟙𝟙ᵀ`. -/
theorem col_mass_enlarge (H : Matrix N N ℂ) (m : ℕ) (c : ℝ) (jb : N × Fin m) :
    ∑ ia : N × Fin m, ‖enlargeMatrix H m c ia jb‖ ^ 2 =
      (|c| * Real.sqrt m) ^ 2 * ∑ i, ‖H i jb.1‖ ^ 2 := by
  rw [Fintype.sum_prod_type, mul_pow, Real.sq_sqrt (Nat.cast_nonneg m), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [enlargeMatrix_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- **The enlarged data satisfy `TwoNormInstance`** whenever the original data satisfy
`HardInstance` and have an entry of modulus one on every input (the energy-one vertex). -/
theorem enlargeData_twoNormInstance (hs : 0 < s) (slot : Fin s ↪ N) (loc : N → Fin s ↪ N)
    (T : BitTable I (N × N)) (y : X → I → Bool) (H : X → Matrix N N ℂ)
    (hbound : ∀ a b, -(2 : ℤ) ^ B < T.word a b ∧ T.word a b ≤ 2 ^ B)
    (hdec : ∀ x i j, ((T.value (y x) (i, j) : ℤ) : ℂ) / 2 ^ B = H x i j)
    (hrow : ∀ x i j, H x i j ≠ 0 → j ∈ Set.range (loc i))
    (hcol : ∀ x i j, H x i j ≠ 0 → i ∈ Set.range (loc j))
    (hD : HardInstance (bitData s B hs slot loc T y H hbound hdec hrow hcol))
    (hone : ∀ x, ∃ i, ‖H x i i‖ = 1) (m : ℕ) (hm : 0 < m) (c : ℝ) (hc : c ≠ 0) :
    TwoNormInstance (enlargeData hs slot loc T y H hbound hdec hrow hcol m hm c hc) c m := by
  have hT : ∀ x, (H x)ᵀ = H x := hD.transpose_eq
  have hR : ∀ x i j, star (H x i j) = H x i j := hD.real
  have hent : ∀ x i j, ‖H x i j‖ ≤ 1 := fun x i j => by
    have h1 := (bitData s B hs slot loc T y H hbound hdec hrow hcol).decode_bound (i, j)
      ((bitData s B hs slot loc T y H hbound hdec hrow hcol).table x (i, j))
    rw [(bitData s B hs slot loc T y H hbound hdec hrow hcol).decoded x i j] at h1
    exact h1
  have a0 : Fin m := ⟨0, hm⟩
  have hsymm : ∀ x, (enlargeMatrix (H x) m c)ᵀ = enlargeMatrix (H x) m c := fun x => by
    ext ia jb
    rw [Matrix.transpose_apply, enlargeMatrix_apply, enlargeMatrix_apply,
      entry_symm_of_transpose (hT x) jb.1 ia.1]
  have hreal : ∀ x ia jb, star (enlargeMatrix (H x) m c ia jb) = enlargeMatrix (H x) m c ia jb :=
    fun x ia jb => by
      rw [enlargeMatrix_apply, star_mul', Complex.star_def, Complex.conj_ofReal]
      exact congrArg _ (hR x ia.1 jb.1)
  refine
    { transpose_eq := hsymm
      real := hreal
      isHermitian := fun x => isHermitian_of_realSymmetric ⟨hsymm x, hreal x⟩
      entry_le := fun x ia jb => ?_
      entry_attained := fun x => ?_
      row_norm_le := fun x ia => ?_
      col_norm_le := fun x jb => ?_
      row_norm_attained := fun x => ?_
      col_norm_attained := fun x => ?_
      row_sparsity_le := fun x ia => ?_
      col_sparsity_le := fun x jb => ?_
      row_sparsity_attained := fun x => ?_
      col_sparsity_attained := fun x => ?_
      scale_eq := rfl
      decode_eq := fun _ _ => rfl
      dyadic := fun x ia jb => ?_
      locators_const := fun _ _ => ⟨rfl, rfl, rfl, rfl⟩ }
  · change ‖enlargeMatrix (H x) m c ia jb‖ ≤ |c|
    rw [enlargeMatrix_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg c) (hent x ia.1 jb.1)
  · obtain ⟨i, hi⟩ := hone x
    refine ⟨(i, a0), (i, a0), ?_⟩
    change ‖enlargeMatrix (H x) m c (i, a0) (i, a0)‖ = |c|
    rw [enlargeMatrix_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs, hi, mul_one]
  · change ∑ jb, ‖enlargeMatrix (H x) m c ia jb‖ ^ 2 ≤ _
    rw [row_mass_enlarge]
    exact mul_le_of_le_one_right (sq_nonneg _) (hD.row_norm_le x ia.1)
  · change ∑ ia, ‖enlargeMatrix (H x) m c ia jb‖ ^ 2 ≤ _
    rw [col_mass_enlarge]
    exact mul_le_of_le_one_right (sq_nonneg _) (hD.col_norm_le x jb.1)
  · obtain ⟨i, hi⟩ := hD.row_norm_attained x
    refine ⟨(i, a0), ?_⟩
    change ∑ jb, ‖enlargeMatrix (H x) m c (i, a0) jb‖ ^ 2 = _
    rw [row_mass_enlarge]
    change _ * ∑ j, ‖H x i j‖ ^ 2 = _
    rw [show (∑ j, ‖H x i j‖ ^ 2) = 1 from hi, mul_one]
  · obtain ⟨j, hj⟩ := hD.col_norm_attained x
    refine ⟨(j, a0), ?_⟩
    change ∑ ia, ‖enlargeMatrix (H x) m c ia (j, a0)‖ ^ 2 = _
    rw [col_mass_enlarge]
    change _ * ∑ i, ‖H x i j‖ ^ 2 = _
    rw [show (∑ i, ‖H x i j‖ ^ 2) = 1 from hj, mul_one]
  · change (Finset.univ.filter fun jb => enlargeMatrix (H x) m c ia jb ≠ 0).card ≤ s * m
    rw [filter_enlarge_row (H x) m hc, Finset.card_product, Finset.card_univ, Fintype.card_fin]
    exact Nat.mul_le_mul_right m (hD.row_sparsity_le x ia.1)
  · change (Finset.univ.filter fun ia => enlargeMatrix (H x) m c ia jb ≠ 0).card ≤ s * m
    rw [filter_enlarge_col (H x) m hc, Finset.card_product, Finset.card_univ, Fintype.card_fin]
    exact Nat.mul_le_mul_right m (hD.col_sparsity_le x jb.1)
  · obtain ⟨i, hi⟩ := hD.row_sparsity_attained x
    refine ⟨(i, a0), ?_⟩
    change (Finset.univ.filter fun jb => enlargeMatrix (H x) m c (i, a0) jb ≠ 0).card = s * m
    rw [filter_enlarge_row (H x) m hc, Finset.card_product, Finset.card_univ, Fintype.card_fin]
    exact congrArg (· * m) hi
  · obtain ⟨j, hj⟩ := hD.col_sparsity_attained x
    refine ⟨(j, a0), ?_⟩
    change (Finset.univ.filter fun ia => enlargeMatrix (H x) m c ia (j, a0) ≠ 0).card = s * m
    rw [filter_enlarge_col (H x) m hc, Finset.card_product, Finset.card_univ, Fintype.card_fin]
    exact congrArg (· * m) hj
  · obtain ⟨v, hv1, hv2, hv⟩ := hD.dyadic x ia.1 jb.1
    refine ⟨v, hv1, hv2, ?_⟩
    change enlargeMatrix (H x) m c ia jb = _
    rw [enlargeMatrix_apply]
    exact congrArg _ hv

end Instance

/-! ### The enlarged hard families -/

/-- The energy-one vertex: `fullMatrix H s refOne refOne = 1`. -/
theorem fullMatrix_refOne {C : Type} [Fintype C] [DecidableEq C] (H : Matrix C C ℂ) (s : ℕ) :
    fullMatrix H s refOne refOne = 1 := by
  simp [fullMatrix, refOne, refBlock]

section Families

/-- **The enlarged search families**: `c · searchHam n μ s a τ ⊗ 𝟙𝟙ᵀ`, sparsity `s m`. -/
def searchTwo (n μ s : ℕ) (a τ : ℝ) (hμ : 1 ≤ μ) (hs : 2 * 2 ^ μ ≤ s) (m : ℕ) (hm : 0 < m)
    (c : ℝ) (hc : c ≠ 0) :
    Data (Fin n → Fin (2 ^ μ)) (SearchIndex n μ s × Fin m) (Word (searchBits n μ s a τ)) (s * m) :=
  enlargeData (pos_of_two_mul_two_pow_le hs) (padSlot _ s)
    (fullLoc (pos_of_two_mul_two_pow_le hs) (searchLoc n μ s)) (searchTable n μ s a τ)
    oneHotBits (searchHam n μ s a τ) (searchTable_bound hμ) searchTable_decode
    (searchLoc_row hs) (searchLoc_col hs) m hm c hc

/-- **The enlarged signed scalar family**: `c · scalarHam n s τ ⊗ 𝟙𝟙ᵀ`, sparsity `s m`. -/
def scalarTwo (n s : ℕ) (τ : ℝ) (hs : 2 ≤ s) (m : ℕ) (hm : 0 < m) (c : ℝ) (hc : c ≠ 0) :
    Data (Fin n → Bool) (ScalarIndex n s × Fin m) (Word (scalarBits n s τ)) (s * m) :=
  enlargeData (by omega) (padSlot _ s) (fullLoc (by omega) (scalarLoc n s)) (scalarTable n s τ)
    (fun x => x) (scalarHam n s τ) scalarTable_bound scalarTable_decode (scalarLoc_row hs)
    (scalarLoc_col hs) m hm c hc

variable {n μ s m : ℕ} {a τ c : ℝ}

@[simp] theorem searchTwo_matrix (hμ : 1 ≤ μ) (hs : 2 * 2 ^ μ ≤ s) (hm : 0 < m) (hc : c ≠ 0)
    (j : Fin n → Fin (2 ^ μ)) :
    (searchTwo n μ s a τ hμ hs m hm c hc).matrix j = enlargeMatrix (searchHam n μ s a τ j) m c :=
  rfl

@[simp] theorem scalarTwo_matrix (hs : 2 ≤ s) (hm : 0 < m) (hc : c ≠ 0) (x : Fin n → Bool) :
    (scalarTwo n s τ hs m hm c hc).matrix x = enlargeMatrix (scalarHam n s τ x) m c := rfl

/-- The native workspace of the enlarged search families. -/
abbrev SearchTwoSpace (n μ s : ℕ) (a τ : ℝ) (m : ℕ) : Type :=
  SparseFlagEmbedding.Space ((SearchIndex n μ s × Fin m) × (SearchIndex n μ s × Fin m))
    (Word (searchBits n μ s a τ))

/-- The native workspace of the enlarged scalar family. -/
abbrev ScalarTwoSpace (n s : ℕ) (τ : ℝ) (m : ℕ) : Type :=
  SparseFlagEmbedding.Space ((ScalarIndex n s × Fin m) × (ScalarIndex n s × Fin m))
    (Word (scalarBits n s τ))

/-- The enlarged search families' certificate: one-hot Boolean oracle of the same hidden input,
costs `hardCost`. -/
def searchTwoAccess (hμ : 1 ≤ μ) (hs : 2 * 2 ^ μ ≤ s) (hm : 0 < m) (hc : c ≠ 0) :
    PhaseAccess (Fin n × Fin (2 ^ μ)) oneHotPattern (oracles (searchTwo n μ s a τ hμ hs m hm c hc))
      hardCost :=
  PhaseAccess.ofImplementsOn
    (bitBooleanFamily (enlargeTable (searchTable n μ s a τ) m) (Word (searchBits n μ s a τ)))
    (ancillaEmbed _) ancillaEmbed_isometry implementsOn_enlargeData

/-- The enlarged scalar family's certificate: bit Boolean oracle of the same hidden bits. -/
def scalarTwoAccess (hs : 2 ≤ s) (hm : 0 < m) (hc : c ≠ 0) :
    PhaseAccess (Fin n) bitPattern (oracles (scalarTwo n s τ hs m hm c hc)) hardCost :=
  PhaseAccess.ofImplementsOn
    (bitBooleanFamily (enlargeTable (scalarTable n s τ) m) (Word (scalarBits n s τ)))
    (ancillaEmbed _) ancillaEmbed_isometry implementsOn_enlargeData

/-- The search families' energy-one vertex. -/
theorem searchHam_refOne (j : Fin n → Fin (2 ^ μ)) :
    ‖searchHam n μ s a τ j refOne refOne‖ = 1 := by
  rw [searchHam, fullMatrix_refOne, norm_one]

/-- The scalar family's energy-one vertex. -/
theorem scalarHam_refOne (x : Fin n → Bool) : ‖scalarHam n s τ x refOne refOne‖ = 1 := by
  rw [scalarHam, fullMatrix_refOne, norm_one]

/-- The enlarged search families satisfy `TwoNormInstance` for `0 ≤ a ≤ 1`. -/
theorem searchTwo_twoNormInstance (hμ : 1 ≤ μ) (hs : 2 * 2 ^ μ ≤ s) (ha0 : 0 ≤ a)
    (ha1 : a ≤ 1) (hm : 0 < m) (hc : c ≠ 0) :
    TwoNormInstance (searchTwo n μ s a τ hμ hs m hm c hc) c m :=
  enlargeData_twoNormInstance _ _ _ _ _ _ _ _ _ _ (searchData_hardInstance τ hμ hs ha0 ha1)
    (fun j => ⟨refOne, searchHam_refOne j⟩) m hm c hc

/-- The enlarged scalar family satisfies `TwoNormInstance`. -/
theorem scalarTwo_twoNormInstance (hs : 2 ≤ s) (hm : 0 < m) (hc : c ≠ 0) :
    TwoNormInstance (scalarTwo n s τ hs m hm c hc) c m :=
  enlargeData_twoNormInstance _ _ _ _ _ _ _ _ _ _ (scalarData_hardInstance τ hs)
    (fun x => ⟨refOne, scalarHam_refOne x⟩) m hm c hc

end Families

/-! ### The three families at the parameters of `hsl:thm:main` -/

section Main

variable {θ ε : ℝ} {s m : ℕ} {c : ℝ}

/-- **Enlarged time family** (`timeData θ s` enlarged by `m`, coefficient `c`). -/
def timeTwo (θ : ℝ) (s : ℕ) (hs : 32 ≤ s) (m : ℕ) (hm : 0 < m) (c : ℝ) (hc : c ≠ 0) :
    Data (Fin (timeN θ) → Fin (2 ^ hsMu s)) (SearchIndex (timeN θ) (hsMu s) s × Fin m)
      (Word (searchBits (timeN θ) (hsMu s) s (timeC θ) θ)) (s * m) :=
  searchTwo (timeN θ) (hsMu s) s (timeC θ) θ (one_le_hsMu hs) (two_mul_hsM_le hs) m hm c hc

/-- **Enlarged mixed family** (`mixedMainData θ ε s` enlarged). -/
def mixedTwo (θ ε : ℝ) (s : ℕ) (hs : 32 ≤ s) (m : ℕ) (hm : 0 < m) (c : ℝ) (hc : c ≠ 0) :
    Data (Fin (precN θ ε) → Fin (2 ^ hsMu s)) (SearchIndex (precN θ ε) (hsMu s) s × Fin m)
      (Word (searchBits (precN θ ε) (hsMu s) s 1 θ)) (s * m) :=
  searchTwo (precN θ ε) (hsMu s) s 1 θ (one_le_hsMu hs) (two_mul_hsM_le hs) m hm c hc

/-- **Enlarged precision family** (`precisionMainData θ ε s` enlarged). -/
def precisionTwo (θ ε : ℝ) (s : ℕ) (hs : 32 ≤ s) (m : ℕ) (hm : 0 < m) (c : ℝ) (hc : c ≠ 0) :
    Data (Fin (precN θ ε) → Bool) (ScalarIndex (precN θ ε) s × Fin m)
      (Word (scalarBits (precN θ ε) s θ)) (s * m) :=
  scalarTwo (precN θ ε) s θ (by omega) m hm c hc

/-- **The instance properties of Proposition `hsl:prop:two-norm`**: the three enlarged families
satisfy `TwoNormInstance` (entries at most `μ = |c|`, attained; row and column norms at most
`η = |c|√m`, attained; sparsity exactly `s m`; exact words; public locators). -/
theorem two_instances (h : HSRange θ s ε) (hm : 0 < m) (hc : c ≠ 0) :
    TwoNormInstance (timeTwo θ s h.s_ge m hm c hc) c m ∧
      TwoNormInstance (mixedTwo θ ε s h.s_ge m hm c hc) c m ∧
      TwoNormInstance (precisionTwo θ ε s h.s_ge m hm c hc) c m :=
  ⟨searchTwo_twoNormInstance _ _ (timeC_pos h.tau_pos).le (timeC_le_one θ) hm hc,
    searchTwo_twoNormInstance _ _ zero_le_one le_rfl hm hc, scalarTwo_twoNormInstance _ hm hc⟩

/-- **The enlarged Hamiltonians have operator norm at least `μ m`** (remark after
`hsl:prop:two-norm`: "The enlarged operator norm is exactly `μ m`, which can exceed `η = μ√m`.
This is consistent with the promise: a bound on every row and column Euclidean norm is not the
same bound on the operator norm"):
`|c| m ≤ ‖H_X‖` for the three families; with `eta_lt_opNorm_bound`, `η = |c|√m < ‖H_X‖` for
`m ≥ 2`. -/
theorem two_opNorm (h : HSRange θ s ε) (hm : 0 < m) (hc : c ≠ 0) :
    (∀ j, |c| * m ≤ ‖SparseStateOverlap.matrixOperator ((timeTwo θ s h.s_ge m hm c hc).matrix j)‖) ∧
      (∀ j, |c| * m ≤
        ‖SparseStateOverlap.matrixOperator ((mixedTwo θ ε s h.s_ge m hm c hc).matrix j)‖) ∧
      (∀ x, |c| * m ≤
        ‖SparseStateOverlap.matrixOperator ((precisionTwo θ ε s h.s_ge m hm c hc).matrix x)‖) := by
  obtain ⟨hT, hM, hP, -⟩ := hard_instances h
  refine ⟨fun j => ?_, fun j => ?_, fun x => ?_⟩
  · have := norm_enlarge_ge ((timeData θ s h.s_ge).matrix j) m hm c
    rwa [hT.norm_eq_one, mul_one] at this
  · have := norm_enlarge_ge ((mixedMainData θ ε s h.s_ge).matrix j) m hm c
    rwa [hM.norm_eq_one, mul_one] at this
  · have := norm_enlarge_ge ((precisionMainData θ ε s h.s_ge).matrix x) m hm c
    rwa [hP.norm_eq_one, mul_one] at this

/-- For `m ≥ 2` the operator norm bound `|c| m` exceeds the row and column norm `η = |c|√m`. -/
theorem eta_lt_opNorm_bound (hm : 2 ≤ m) (hc : c ≠ 0) : |c| * Real.sqrt m < |c| * m := by
  have hc0 : 0 < |c| := abs_pos.mpr hc
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hs : Real.sqrt m < m := by
    have h1 : Real.sqrt m * Real.sqrt m = m := Real.mul_self_sqrt (by linarith)
    have h2 : 1 < Real.sqrt m := by
      rw [← Real.sqrt_one]; exact Real.sqrt_lt_sqrt zero_le_one (by linarith)
    nlinarith
  exact mul_lt_mul_of_pos_left hs hc0

/-- The time family's certificate. -/
def timeTwoAccess (hs : 32 ≤ s) (hm : 0 < m) (hc : c ≠ 0) :
    PhaseAccess (Fin (timeN θ) × Fin (2 ^ hsMu s)) oneHotPattern
      (oracles (timeTwo θ s hs m hm c hc)) hardCost :=
  searchTwoAccess _ _ hm hc

/-- The mixed family's certificate. -/
def mixedTwoAccess (hs : 32 ≤ s) (hm : 0 < m) (hc : c ≠ 0) :
    PhaseAccess (Fin (precN θ ε) × Fin (2 ^ hsMu s)) oneHotPattern
      (oracles (mixedTwo θ ε s hs m hm c hc)) hardCost :=
  searchTwoAccess _ _ hm hc

/-- The precision family's certificate. -/
def precisionTwoAccess (hs : 32 ≤ s) (hm : 0 < m) (hc : c ≠ 0) :
    PhaseAccess (Fin (precN θ ε)) bitPattern (oracles (precisionTwo θ ε s hs m hm c hc)) hardCost :=
  scalarTwoAccess _ hm hc

end Main

end

end OptimalLowerBounds
