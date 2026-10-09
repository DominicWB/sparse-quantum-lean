import ODELowerBoundExtensions.Padding.ZeroPad

/-!
# Sampled-time data from a stage bit table

Manuscript lines 3852-3858 (the joint family's sparse
input) and 3899-3904 (its dense and zero padding). The joint family of Theorem `odel:thm:joint`
(`SparseLowerBounds.ODE.jointData`) stores on hidden stage `k < n` the word of a one-bit table
`jointTable`, selected by the membership bits `stageBits x k`, and the known word `0` on the idle
and source stages. Its padded variants change only the table, the known words of the idle and
source stages, the word length and the index type. This module builds the native sampled-time
data of any such stage table once (`stageData`), so that the dense padding (`Padding/JointDense`)
and the zero padding (`Padding/JointPad`) of the joint family are instances of it and share one
Boolean implementation (`Padding/StageCompile`).

**The builder.** For an index `N`, a bit table `T` on `N × N` with bits indexed by
`Fin M × Fin 2^μ`, known words `W₀` on the idle and source stages, a word length `B`, fixed
injective location lists `loc` with slots `slot`, and sampled matrices `H`:

* stage word (`stageWord`): `T.value (stageBits x k) a` on a hidden stage `k < n`, `W₀ a`
  otherwise; the table stores it in `Word B`;
* decode `z ↦ i · valMinAbs z / 2^B` (position independent, scale `1`, as `jointData` with
  `B = μ`), so the hypothesis `hdec` says that `H` is `i ·` the decoded words;
* input- and stage-independent locators with the fixed permutation extensions
  `Hamiltonian.permCLM (Hamiltonian.rowEquiv slot loc)` (as `jointData` and `bitData`).
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

namespace ODELowerBoundExtensions.Padding

noncomputable section
open SparseHamiltonian NativeSparseBlockEncoding SparseLowerBounds SparseLowerBounds.ODE
open SparseLowerBounds.Hamiltonian (BitTable Word wordDecode)

variable {N : Type*} [Fintype N] [DecidableEq N]

/-- **The stage word** of address `a` at the sampled point `p = (x, k)`: the word of the stage
bit table `T` under the membership bits of stage `k` on a hidden stage `k < n`, the known word
`W₀ a` on the idle and source stages. -/
def stageWord {M μ : ℕ} (n : ℕ) (T : BitTable (Fin M × Fin (2 ^ μ)) (N × N)) (W₀ : N × N → ℤ)
    (p : Promised M n (2 ^ μ) × Fin (n + 2)) (a : N × N) : ℤ :=
  if hk : (p.2 : ℕ) < n then T.value (stageBits p.1 ⟨p.2, hk⟩) a else W₀ a

/-- **Native sampled-time data from a stage bit table**: exact words `Word B` with decode
`i · valMinAbs/2^B` (scale `1`), the stage words `stageWord n T W₀`, input- and stage-independent
location lists `loc` with fixed permutation extensions, and matrices `H` (`hdec`: `H` is the
decoded table). -/
def stageData (M n μ s B : ℕ) (hs : 0 < s) (slot : Fin s ↪ N) (loc : N → Fin s ↪ N)
    (T : BitTable (Fin M × Fin (2 ^ μ)) (N × N)) (W₀ : N × N → ℤ)
    (H : Promised M n (2 ^ μ) × Fin (n + 2) → Matrix N N ℂ)
    (hbound : ∀ p a, -(2 : ℤ) ^ B < stageWord n T W₀ p a ∧ stageWord n T W₀ p a ≤ 2 ^ B)
    (hdec : ∀ p i j, Complex.I * ((stageWord n T W₀ p (i, j) : ℂ) / 2 ^ B) = H p i j)
    (hrow : ∀ p i j, H p i j ≠ 0 → j ∈ Set.range (loc i))
    (hcol : ∀ p i j, H p i j ≠ 0 → i ∈ Set.range (loc j)) :
    Data (Promised M n (2 ^ μ) × Fin (n + 2)) N (Word B) s where
  slot := slot
  slots_pos := hs
  scale := 1
  scale_pos := one_pos
  matrix := H
  table p a := ((stageWord n T W₀ p a : ℤ) : Word B)
  decode _ z := Complex.I * wordDecode B z
  decode_bound _ z := by
    rw [norm_mul, Complex.norm_I, one_mul]; exact Hamiltonian.norm_wordDecode_le B z
  decoded p i j := by
    rw [Hamiltonian.wordDecode_intCast _ (hbound p (i, j)).1 (hbound p (i, j)).2]
    exact hdec p i j
  rowloc _ i k := loc i k
  colloc _ j k := loc j k
  row_injective _ i := (loc i).injective
  column_injective _ j := (loc j).injective
  row_covers p i j h := by
    obtain ⟨k, hk⟩ := hrow p i j h
    exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, hk⟩
  column_covers p i j h := by
    obtain ⟨k, hk⟩ := hcol p i j h
    exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, hk⟩
  rowOracle _ := Hamiltonian.permCLM (Hamiltonian.rowEquiv slot loc)
  columnOracle _ := Hamiltonian.permCLM (Hamiltonian.colEquiv slot loc)
  row_unitary _ := LookupOracle.permutationUnitary_unitary _
  column_unitary _ := LookupOracle.permutationUnitary_unitary _
  row_valid _ i k :=
    (Hamiltonian.permCLM_single _ _ _).trans (by rw [Hamiltonian.rowEquiv_slot])
  column_valid _ j k :=
    (Hamiltonian.permCLM_single _ _ _).trans (by rw [Hamiltonian.colEquiv_slot])

section Facts

variable {M n μ s B : ℕ} {hs : 0 < s} {slot : Fin s ↪ N} {loc : N → Fin s ↪ N}
  {T : BitTable (Fin M × Fin (2 ^ μ)) (N × N)} {W₀ : N × N → ℤ}
  {H : Promised M n (2 ^ μ) × Fin (n + 2) → Matrix N N ℂ}
  {hbound : ∀ p a, -(2 : ℤ) ^ B < stageWord n T W₀ p a ∧ stageWord n T W₀ p a ≤ 2 ^ B}
  {hdec : ∀ p i j, Complex.I * ((stageWord n T W₀ p (i, j) : ℂ) / 2 ^ B) = H p i j}
  {hrow : ∀ p i j, H p i j ≠ 0 → j ∈ Set.range (loc i)}
  {hcol : ∀ p i j, H p i j ≠ 0 → i ∈ Set.range (loc j)}

/-- The sampled matrices of the builder are `H`. -/
@[simp] theorem stageData_matrix :
    (stageData M n μ s B hs slot loc T W₀ H hbound hdec hrow hcol).matrix = H := rfl

/-- The value table stores the stage word. -/
theorem stageData_table (p : Promised M n (2 ^ μ) × Fin (n + 2)) (a : N × N) :
    (stageData M n μ s B hs slot loc T W₀ H hbound hdec hrow hcol).table p a =
      ((stageWord n T W₀ p a : ℤ) : Word B) := rfl

/-- **The locators are public**: the location lists and the location oracles do not depend on
the input or the stage. -/
theorem stageData_locators_const (p p' : Promised M n (2 ^ μ) × Fin (n + 2)) :
    (stageData M n μ s B hs slot loc T W₀ H hbound hdec hrow hcol).rowloc p =
        (stageData M n μ s B hs slot loc T W₀ H hbound hdec hrow hcol).rowloc p' ∧
      (stageData M n μ s B hs slot loc T W₀ H hbound hdec hrow hcol).colloc p =
        (stageData M n μ s B hs slot loc T W₀ H hbound hdec hrow hcol).colloc p' ∧
      (stageData M n μ s B hs slot loc T W₀ H hbound hdec hrow hcol).rowOracle p =
        (stageData M n μ s B hs slot loc T W₀ H hbound hdec hrow hcol).rowOracle p' ∧
      (stageData M n μ s B hs slot loc T W₀ H hbound hdec hrow hcol).columnOracle p =
        (stageData M n μ s B hs slot loc T W₀ H hbound hdec hrow hcol).columnOracle p' :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **Exact dyadic entries**: every sampled entry is `i · v/2^B` with an integer
`-2^B < v ≤ 2^B`, the stored stage word. -/
theorem stageData_dyadic (p : Promised M n (2 ^ μ) × Fin (n + 2)) (i j : N) :
    ∃ v : ℤ, -(2 : ℤ) ^ B < v ∧ v ≤ 2 ^ B ∧
      (stageData M n μ s B hs slot loc T W₀ H hbound hdec hrow hcol).matrix p i j =
        Complex.I * ((v : ℂ) / 2 ^ B) :=
  ⟨stageWord n T W₀ p (i, j), (hbound p (i, j)).1, (hbound p (i, j)).2, (hdec p i j).symm⟩

end Facts

end

end ODELowerBoundExtensions.Padding
