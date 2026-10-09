import AdaptiveHamiltonianLowerBound.Access.Native
import SparseLowerBounds.Hamiltonian.HardData
import SparseLowerBounds.Query.Ancilla

set_option autoImplicit false

/-!
# The hard families of `hsl:thm:main` as native data with one-bit entries

The three hard families of the Hamiltonian-simulation lower bound are native sparse data
built by the one-bit word-table builder `SparseLowerBounds.Hamiltonian.bitData` (manuscript
lines 2254-2289): fixed permutation locators, and table words that depend on at most one
hidden bit.

* Time and mixed families (`timeData`, `mixedMainData`; inputs `j : Fin n → Fin m`): the word
  of an address reads the one-hot bit `[j k = b]` (`oneHotBits`), so the access conditions
  hold along the identity (`hardAccess_timeData`, `hardAccess_mixedMainData`).
* Precision family (`precisionMainData`; inputs `x : Fin n → Bool`): the word reads the bit
  `x k`. Along `toBits : (Fin n → Fin 2) → (Fin n → Bool)`, `toBits j k = [j k = 1]`, it reads
  the one-hot bit `[j k = 1]` (`hardAccess_precisionMainData`).

The released oracle families are admissible labels (`Access.Admissible`) with the weight
`valueWeight` that counts value calls only: the native primitives `oracles D`
(`admissible_oracles`, in the trivial layout `unitLayout`) and their spectator versions
`specOracles Ω D` (`admissible_specOracles`). So the worst-case count `T.worstCost w` of the
adaptive theorems specialises to the number of value queries `labelCount .value` of the
released non-adaptive theorems.
-/

namespace AdaptiveHamiltonianLowerBound

noncomputable section
open SparseHamiltonian ContinuousLinearMap
open LinearSystemLowerBound
open SparseLowerBounds.Hamiltonian

namespace Access

/-! ### One-bit tables -/

/-- The Boolean input `k ↦ [j k = 1]` of a one-hot input over `Fin 2`. -/
def toBits {n : ℕ} (j : Fin n → Fin 2) : Fin n → Bool := fun k => decide (j k = 1)

/-- A word of a one-bit table, read through hidden bits that are one-hot bits `[j c = q₀]`
of the input, is a fixed function of at most one bit of `j`. -/
theorem bitTable_value_bit {n m : ℕ} {I A β : Type*} (T : BitTable I A)
    (y : (Fin n → Fin m) → I → Bool)
    (hy : ∀ i, ∃ (c : Fin n) (q₀ : Fin m), ∀ j, y j i = decide (j c = q₀)) (a : A)
    (f : ℤ → β) : Hard.BitDetermined (fun j => f (T.value (y j) a)) := by
  cases h : T.addr a with
  | none =>
      exact Or.inl ⟨f (T.word a false), fun j => by
        show f (T.value (y j) a) = _
        rw [T.value_of_addr_none _ h]⟩
  | some i =>
      obtain ⟨c, q₀, hc⟩ := hy i
      refine Or.inr ⟨c, q₀, f (T.word a false), f (T.word a true), fun j => ?_⟩
      show f (T.value (y j) a) = _
      rw [T.value_of_addr_some _ h, hc j]
      by_cases hj : j c = q₀ <;> simp [hj]

/-- **The search data** satisfy the access conditions along the identity. -/
theorem hardAccess_searchData (n μ s : ℕ) (a τ : ℝ) (hμ : 1 ≤ μ) (hs : 2 * 2 ^ μ ≤ s) :
    HardAccess (searchData n μ s a τ hμ hs) (fun j => j) where
  row_const _ _ := rfl
  column_const _ _ := rfl
  table_bit α := bitTable_value_bit (searchTable n μ s a τ) oneHotBits
    (fun ka => ⟨ka.1, ka.2, fun _ => rfl⟩) α (fun z => (z : Word (searchBits n μ s a τ)))

theorem hardAccess_timeData (τ : ℝ) (s : ℕ) (hs : 32 ≤ s) :
    HardAccess (timeData τ s hs) (fun j => j) :=
  hardAccess_searchData _ _ _ _ _ _ _

theorem hardAccess_mixedMainData (τ ε : ℝ) (s : ℕ) (hs : 32 ≤ s) :
    HardAccess (mixedMainData τ ε s hs) (fun j => j) :=
  hardAccess_searchData _ _ _ _ _ _ _

/-- **The scalar data** satisfy the access conditions along `toBits`. -/
theorem hardAccess_scalarData (n s : ℕ) (τ : ℝ) (hs : 2 ≤ s) :
    HardAccess (scalarData n s τ hs) (toBits (n := n)) where
  row_const _ _ := rfl
  column_const _ _ := rfl
  table_bit α := bitTable_value_bit (scalarTable n s τ) (fun j => toBits j)
    (fun k => ⟨k, 1, fun _ => rfl⟩) α (fun z => (z : Word (scalarBits n s τ)))

theorem hardAccess_precisionMainData (τ ε : ℝ) (s : ℕ) (hs : 32 ≤ s) :
    HardAccess (precisionMainData τ ε s hs) (toBits (n := precN τ ε)) :=
  hardAccess_scalarData _ _ _ _

/-! ### The released oracle families are admissible -/

section Released

variable {X N Z : Type*} [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z] {s : ℕ}

/-- The weight counting value calls only (location calls are free). -/
def valueWeight : NativeSparseBlockEncoding.Query → ℕ
  | .rowLocation => 0
  | .columnLocation => 0
  | .value => 1

/-- `T.worstCost valueWeight` counts value calls: `valueWeight` is the weight of
`labelCount .value`. -/
theorem valueWeight_eq (q : NativeSparseBlockEncoding.Query) :
    valueWeight q = if q = .value then 1 else 0 := by
  cases q <;> rfl

/-- The trivial layout of a space as one spectator branch. -/
def unitLayout (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℂ V] :
    V ≃ₗᵢ[ℂ] PiLp 2 (fun _ : Unit => V) where
  toFun v := WithLp.toLp 2 (fun _ => v)
  invFun Ψ := Ψ ()
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl
  norm_map' v := by simp [PiLp.norm_eq_of_L2]

/-- **The native primitives are admissible** with `valueWeight`, for data with
input-independent locators. -/
theorem admissible_oracles (D : NativeSparseBlockEncoding.Data X N Z s)
    (hrow : ∀ x x', D.rowOracle x = D.rowOracle x')
    (hcol : ∀ x x', D.columnOracle x = D.columnOracle x')
    (q : NativeSparseBlockEncoding.Query) :
    Admissible D (NativeSparseBlockEncoding.oracles D q) (valueWeight q) := by
  cases q with
  | rowLocation =>
      refine Or.inr ⟨fun x x' => ?_, NativeSparseBlockEncoding.oracles_unitary D _⟩
      simp only [NativeSparseBlockEncoding.oracles, SparseFlagEmbedding.location, hrow x x']
  | columnLocation =>
      refine Or.inr ⟨fun x x' => ?_, NativeSparseBlockEncoding.oracles_unitary D _⟩
      simp only [NativeSparseBlockEncoding.oracles, SparseFlagEmbedding.location, hcol x x']
  | value =>
      refine Or.inl ⟨⟨Unit, inferInstance, unitLayout _, fun _ => some (.value, false),
        fun x => ?_⟩, le_rfl⟩
      ext v
      rfl

/-- **The spectator primitives are admissible** with `valueWeight`, for data with
input-independent locators. -/
theorem admissible_specOracles (Ω : Type) [Fintype Ω] (D : NativeSparseBlockEncoding.Data X N Z s)
    (hrow : ∀ x x', D.rowOracle x = D.rowOracle x')
    (hcol : ∀ x x', D.columnOracle x = D.columnOracle x')
    (q : NativeSparseBlockEncoding.Query) :
    Admissible D (SparseLowerBounds.specOracles Ω D q) (valueWeight q) := by
  cases q with
  | rowLocation =>
      refine Or.inr ⟨fun x x' => ?_, SparseLowerBounds.specOracles_unitary Ω D _⟩
      simp only [SparseLowerBounds.specOracles, NativeSparseBlockEncoding.oracles,
        SparseFlagEmbedding.location, hrow x x']
  | columnLocation =>
      refine Or.inr ⟨fun x x' => ?_, SparseLowerBounds.specOracles_unitary Ω D _⟩
      simp only [SparseLowerBounds.specOracles, NativeSparseBlockEncoding.oracles,
        SparseFlagEmbedding.location, hcol x x']
  | value =>
      refine Or.inl ⟨⟨Ω, inferInstance, LinearIsometryEquiv.refl ℂ _,
        fun _ => some (.value, false), fun x => ?_⟩, le_rfl⟩
      ext Ψ σ
      rfl

end Released

end Access

end

end AdaptiveHamiltonianLowerBound
