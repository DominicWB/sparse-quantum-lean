import SparseLowerBounds.Hamiltonian.Theorem

/-!
# Padding the hard Hamiltonian-simulation families to a common dimension

This file formalises the padding claims of Theorem `hsl:thm:main` (the Hamiltonian-simulation query
lower bound) of *Root-sparsity scaling for Hamiltonian simulation, differential equations and
linear-system solvers* (Section `part:hsl`): the remark that follows the theorem,

> We need not find one matrix on which all three mechanisms are simultaneously difficult. An
> algorithm that works on the whole promise class must work on each of our three families. Its
> worst-case query count is consequently at least the largest of their separate lower bounds. For
> three nonnegative numbers, that maximum is at least one third of their sum, which is enough for
> the stated joint bound.

the last clause of the theorem, "Dimension `O(s(τ+r+1))` suffices, with further known padding
allowed", and the end of its proof, "Further known zero padding equalises dimensions or accommodates
a qubit register". The theorem is `SparseLowerBounds.Hamiltonian.main_max` (max form),
assembled from the per-family bounds `time_main`, `mixed_main` and `precision_main` for the
families `timeData`, `mixedMainData` and `precisionMainData` on the index types
`SearchIndex (timeN τ) (hsMu s) s`, `SearchIndex (precN τ ε) (hsMu s) s` and
`ScalarIndex (precN τ ε) s`; `hard_instances` gives their instance properties and the dimension
bound `4 s (τ + r + 1)`. (`SparseLowerBounds/Statements.lean` lists the padding to a common
dimension as not formalised there.)

## Known padding

Let `P` be any finite type (the padding register).

* `padTable T P` extends a one-bit word table on `N × N` to `(N ⊕ P) × (N ⊕ P)`: addresses
  outside the original block read no bit (`padTable_addr_inl_inr`, `padTable_addr_inr`) and
  carry the word `0`.
* `padMat P H = H ⊕ 0_P` (`Matrix.fromBlocks H 0 0 0`), and `padLoc`: original rows keep their
  location lists, padding rows list the slots; all lists are fixed and injective.
* `padBitData` is the one-bit builder `bitData` applied to these, with its hypotheses derived
  from those of the original data (`padTable_bound`, `padTable_decode`, `padLoc_row`,
  `padLoc_col`). The padded hard families are `padSearchData` and `padScalarData`, and at the
  parameters of the theorem `timePadData`, `mixedPadData` and `precisionPadData`: `timeData`,
  `mixedMainData` and `precisionMainData` padded by `P`. The padded known input is `ψ_in ⊕ 0`,
  written `HsInstance.inlOp N P ψ_in` (extension by zero).
* `evolve_padMat`: `e^{-iτ(H ⊕ 0)} (ψ ⊕ 0) = (e^{-iτH} ψ) ⊕ 0`.

## Hardness is unaffected

An algorithm for a padded family is a program over the native primitives of the padded data
(spectator form, as in `time_main`) whose output is read through an isometry into the padded
system `ℂ^{N ⊕ P}` ⊗ garbage and is `ε`-accurate (`Readout.Accurate`) for the padded targets
`e^{-iτ(H_X ⊕ 0)} (ψ_in ⊕ 0)`.

* Queries: every primitive of the padded data is again a `hardCost`-query program over the
  Boolean oracle of the same hidden bits (`implementsOn_padBitData_spec`,
  `implementsOn_padSearchData_spec`, `implementsOn_padScalarData_spec`): two Boolean queries per
  value call, location calls free.
* Readout without loss: fix `i₀ : N`. The isometry
  `padReadout P G i₀ : ℂ^{N ⊕ P} ⊗ G → ℂ^N ⊗ (ℂ^{Option P} ⊗ G)` keeps the original coordinates
  and moves the padding coordinates into the garbage, attached to the system state `i₀`
  (`padReadout_isometry`). A system observable `M` is measured through it as
  `M ⊕ M_{i₀ i₀} 1_P` (`outObs_padReadout`), which is a Hermitian contraction when `M` is one
  (`isSelfAdjoint_blockObs`, `norm_blockObs_le`, `norm_obsMat_apply_le`) and has the same
  expectation on `ψ ⊕ 0` as `M` on `ψ` (`blockObs_inlOp`, `inner_inlOp`). So an output that is
  `ε`-accurate for `ψ ⊕ 0` through `e` is `ε`-accurate for `ψ` through `R ∘ e`, with the same
  `ε` (`accurate_padReadout`, `accurate_pad_evolve`), and `R ∘ e` is again an isometry
  (`padReadout_comp_isometry`).
* Hence the family lemmas `time_general`, `mixed_general` and `precision_general` (generic in
  the oracle family, the Boolean projection family, the encoding and the readout) apply to the
  padded algorithms with the readout `R ∘ e`, `i₀ = refZero`: `time_pad_spec`, `mixed_pad_spec`
  and `precision_pad_spec` at arbitrary family parameters, and `time_main_pad`, `mixed_main_pad`
  and `precision_main_pad` at the parameters of the theorem, with the constants of `time_main`,
  `mixed_main` and `precision_main`. Combined (`assembly`): `main_max_pad`,
  `c₀ (√s τ + √(sτr) + r) ≤ max(Q_T, Q_M, Q_P)` for any three paddings, `c₀ = log 2/(4096π)`.
* Instance properties: padding preserves `HardInstance` (`padBitData_hardInstance`,
  `padSearchData_hardInstance`, `padScalarData_hardInstance`), and `hard_instances_pad`: the
  three padded families are real symmetric with operator norm and maximum row and column
  Euclidean norms exactly one, maximum row and column sparsity exactly `s`, exact dyadic words
  with position-independent decode and input-independent locators, and have dimension at most
  `4 s (τ + r + 1) + |P|`.

## Worst case and one common dimension

* `third_sum_le_max`: the maximum of three nonnegative lower bounds is at least a third of their
  sum.
* `PadTo S Nd = Fin (Nd - |S|)` pads an index type `S` to dimension exactly `Nd` when `|S| ≤ Nd`
  (`card_padTo`); every `Nd ≥ 4 s (τ + r + 1)` is at least the dimension of each family
  (`card_le_of_dim`).
* `main_max_common_dimension`: for every `Nd` at least the three dimensions, the three families
  padded to dimension exactly `Nd` obey `c₀ (√s τ + √(sτr) + r) ≤ max(Q_T, Q_M, Q_P)`.
* `ForcesQueries`, `main_exists_pad` and `main_exists_common_dimension` (family form, as
  `main_exists`, with the seed bound and the isometric readout assumed for all three families):
  in dimension exactly `Nd`, one of the three padded families forces every accurate algorithm
  (seed of norm at most one, isometric readout) to make at least
  `mainBound τ ε s = c₀ (√s τ + √(sτr) + r)` value queries.

## Scope

Algorithms are the non-adaptive spectator-form programs of `time_main`. The forms without a
spectator register (`*_main_native`), the heralded and the endpoint forms are not restated for
the padded families. The padding block is the zero matrix; the padded matrices `H ⊕ 0_P` keep
every instance property because norm one and sparsity `s` are attained on the original block.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

namespace LowerBoundRemarks.HamiltonianPadding

noncomputable section
open SparseHamiltonian NativeSparseBlockEncoding OracleCircuit SparseLowerBounds
  SparseLowerBounds.Hamiltonian SparseLowerBounds.Readout
open scoped Matrix InnerProduct InnerProductSpace Matrix.Norms.L2Operator

universe u v

/-! ### Padded word tables, matrices and locators -/

section Table

variable {I N : Type*}

/-- **The padded word table.** On the original block, address `(inl i, inl j)` keeps the bit
position and the words of address `(i, j)` of `T`; every other address of `(N ⊕ P) × (N ⊕ P)`
reads no bit and carries the known word `0`. -/
def padTable (T : BitTable I (N × N)) (P : Type*) : BitTable I ((N ⊕ P) × (N ⊕ P)) where
  addr a := Sum.elim (fun i => Sum.elim (fun j => T.addr (i, j)) fun _ => none)
    (fun _ _ => none) a.1 a.2
  word a := Sum.elim (fun i => Sum.elim (fun j => T.word (i, j)) fun _ _ => 0)
    (fun _ _ _ => 0) a.1 a.2

variable (T : BitTable I (N × N)) (P : Type*) (y : I → Bool)

/-- On the original block the padded table reads the bit of the original address. -/
theorem padTable_addr_inl_inl (i j : N) :
    (padTable T P).addr (Sum.inl i, Sum.inl j) = T.addr (i, j) := rfl

/-- Addresses with a padding column read no bit. -/
theorem padTable_addr_inl_inr (i : N) (p : P) :
    (padTable T P).addr (Sum.inl i, Sum.inr p) = none := rfl

/-- Addresses with a padding row read no bit. -/
theorem padTable_addr_inr (p : P) (j : N ⊕ P) : (padTable T P).addr (Sum.inr p, j) = none := rfl

/-- On the original block the padded table has the original word. -/
theorem padTable_value_inl_inl (i j : N) :
    (padTable T P).value y (Sum.inl i, Sum.inl j) = T.value y (i, j) := rfl

/-- The word `0` at addresses with a padding column. -/
theorem padTable_value_inl_inr (i : N) (p : P) :
    (padTable T P).value y (Sum.inl i, Sum.inr p) = 0 := rfl

/-- The word `0` at addresses with a padding row. -/
theorem padTable_value_inr (p : P) (j : N ⊕ P) : (padTable T P).value y (Sum.inr p, j) = 0 := rfl

variable {T} in
/-- The padded words stay in the exactly decodable range `(-2^B, 2^B]`. -/
theorem padTable_bound {B : ℕ} (hbound : ∀ a b, -(2 : ℤ) ^ B < T.word a b ∧ T.word a b ≤ 2 ^ B) :
    ∀ a b, -(2 : ℤ) ^ B < (padTable T P).word a b ∧ (padTable T P).word a b ≤ 2 ^ B := by
  have h0 : -(2 : ℤ) ^ B < 0 ∧ (0 : ℤ) ≤ 2 ^ B := ⟨by simp, by positivity⟩
  rintro ⟨i | p, j | q⟩ b
  · exact hbound (i, j) b
  · exact h0
  · exact h0
  · exact h0

end Table

/-- **The padded matrix** `H ⊕ 0_P` (`Matrix.fromBlocks H 0 0 0`): the original matrix on the
original block, zero on and next to the padding block. -/
def padMat {N : Type*} (P : Type*) (H : Matrix N N ℂ) : Matrix (N ⊕ P) (N ⊕ P) ℂ :=
  Matrix.fromBlocks H 0 0 0

section Locators

variable {N : Type*} {s : ℕ}

/-- **The padded location lists**: an original row `inl i` uses the original list `loc i`
(embedded by `inl`), a padding row uses the slot list (embedded by `inl`). Both are fixed and
injective. -/
def padLoc (slot : Fin s ↪ N) (loc : N → Fin s ↪ N) (P : Type*) : N ⊕ P → Fin s ↪ N ⊕ P :=
  Sum.elim (fun i => (loc i).trans Function.Embedding.inl) fun _ =>
    slot.trans Function.Embedding.inl

/-- Row coverage of the padded matrix by the padded lists (only original rows have nonzero
entries). -/
theorem padLoc_row {X : Type*} {slot : Fin s ↪ N} {loc : N → Fin s ↪ N} {H : X → Matrix N N ℂ}
    (hrow : ∀ x i j, H x i j ≠ 0 → j ∈ Set.range (loc i)) (P : Type*) :
    ∀ x i j, padMat P (H x) i j ≠ 0 → j ∈ Set.range (padLoc slot loc P i) := by
  rintro x (i | p) (j | q) h
  · obtain ⟨k, hk⟩ := hrow x i j h
    exact ⟨k, by simp [padLoc, hk]⟩
  all_goals exact absurd rfl h

/-- Column coverage of the padded matrix by the padded lists. -/
theorem padLoc_col {X : Type*} {slot : Fin s ↪ N} {loc : N → Fin s ↪ N} {H : X → Matrix N N ℂ}
    (hcol : ∀ x i j, H x i j ≠ 0 → i ∈ Set.range (loc j)) (P : Type*) :
    ∀ x i j, padMat P (H x) i j ≠ 0 → i ∈ Set.range (padLoc slot loc P j) := by
  rintro x (i | p) (j | q) h
  · obtain ⟨k, hk⟩ := hcol x i j h
    exact ⟨k, by simp [padLoc, hk]⟩
  all_goals exact absurd rfl h

end Locators

/-- The padded words decode exactly to the padded matrix. -/
theorem padTable_decode {X I N : Type*} {B : ℕ} {T : BitTable I (N × N)} {y : X → I → Bool}
    {H : X → Matrix N N ℂ} (hdec : ∀ x i j, ((T.value (y x) (i, j) : ℤ) : ℂ) / 2 ^ B = H x i j)
    (P : Type*) :
    ∀ x i j, (((padTable T P).value (y x) (i, j) : ℤ) : ℂ) / 2 ^ B = padMat P (H x) i j := by
  rintro x (i | p) (j | q)
  · exact hdec x i j
  · simp [padTable_value_inl_inr, padMat]
  · simp [padTable_value_inr, padMat]
  · simp [padTable_value_inr, padMat]

/-! ### Padded native data -/

section Data

variable {N : Type*} [Fintype N] [DecidableEq N] {X I : Type*} (P : Type*) [Fintype P]
  [DecidableEq P]

/-- **Padded native sparse data.** The one-bit builder `bitData` applied to the padded table
`padTable T P`, the padded matrices `H x ⊕ 0_P`, the slots `inl ∘ slot` and the padded lists
`padLoc`; its hypotheses are derived from those of the original data. -/
def padBitData (s B : ℕ) (hs : 0 < s) (slot : Fin s ↪ N) (loc : N → Fin s ↪ N)
    (T : BitTable I (N × N)) (y : X → I → Bool) (H : X → Matrix N N ℂ)
    (hbound : ∀ a b, -(2 : ℤ) ^ B < T.word a b ∧ T.word a b ≤ 2 ^ B)
    (hdec : ∀ x i j, ((T.value (y x) (i, j) : ℤ) : ℂ) / 2 ^ B = H x i j)
    (hrow : ∀ x i j, H x i j ≠ 0 → j ∈ Set.range (loc i))
    (hcol : ∀ x i j, H x i j ≠ 0 → i ∈ Set.range (loc j)) :
    Data X (N ⊕ P) (Word B) s :=
  bitData s B hs (slot.trans Function.Embedding.inl) (padLoc slot loc P) (padTable T P) y
    (fun x => padMat P (H x)) (padTable_bound P hbound) (padTable_decode hdec P)
    (padLoc_row hrow P) (padLoc_col hcol P)

variable {s B : ℕ} {hs : 0 < s} {slot : Fin s ↪ N} {loc : N → Fin s ↪ N}
  {T : BitTable I (N × N)} {y : X → I → Bool} {H : X → Matrix N N ℂ}
  {hbound : ∀ a b, -(2 : ℤ) ^ B < T.word a b ∧ T.word a b ≤ 2 ^ B}
  {hdec : ∀ x i j, ((T.value (y x) (i, j) : ℤ) : ℂ) / 2 ^ B = H x i j}
  {hrow : ∀ x i j, H x i j ≠ 0 → j ∈ Set.range (loc i)}
  {hcol : ∀ x i j, H x i j ≠ 0 → i ∈ Set.range (loc j)}

/-- The matrices of the padded data are `H x ⊕ 0_P`. -/
@[simp] theorem padBitData_matrix :
    (padBitData P s B hs slot loc T y H hbound hdec hrow hcol).matrix =
      fun x => padMat P (H x) := rfl

/-- The value table of the padded data is the padded word table. -/
theorem padBitData_table (x : X) (a : (N ⊕ P) × (N ⊕ P)) :
    (padBitData P s B hs slot loc T y H hbound hdec hrow hcol).table x a =
      (((padTable T P).value (y x) a : ℤ) : Word B) := rfl

end Data

/-- **Two Boolean queries per value call for the padded data**, with an untouched spectator
register: `implementsOn_bitData_spec` for the padded table. The Boolean oracle is the phase
oracle of the same hidden bits `y x`, on the padded address family. -/
theorem implementsOn_padBitData_spec {N : Type*} [Fintype N] [DecidableEq N] {X I : Type*}
    [Fintype I] [DecidableEq I] (P : Type*) [Fintype P] [DecidableEq P] (Ω : Type*) [Fintype Ω]
    {s B : ℕ} (hs : 0 < s) (slot : Fin s ↪ N) (loc : N → Fin s ↪ N)
    (T : BitTable I (N × N)) (y : X → I → Bool) (H : X → Matrix N N ℂ)
    (hbound : ∀ a b, -(2 : ℤ) ^ B < T.word a b ∧ T.word a b ≤ 2 ^ B)
    (hdec : ∀ x i j, ((T.value (y x) (i, j) : ℤ) : ℂ) / 2 ^ B = H x i j)
    (hrow : ∀ x i j, H x i j ≠ 0 → j ∈ Set.range (loc i))
    (hcol : ∀ x i j, H x i j ≠ 0 → i ∈ Set.range (loc j)) (l : Query) :
    EncodedOracle.ImplementsOn (fun x => (bitSpecFamily Ω (padTable T P) (Word B)).phase (y x))
      (specOracles Ω (padBitData P s B hs slot loc T y H hbound hdec hrow hcol) l)
      (ancillaEmbed (Joint Ω (SparseFlagEmbedding.Space ((N ⊕ P) × (N ⊕ P)) (Word B))))
      (hardCost l) :=
  implementsOn_bitData_spec Ω hs _ _ (padTable T P) y _ (padTable_bound P hbound)
    (padTable_decode hdec P) (padLoc_row hrow P) (padLoc_col hcol P) l

/-! ### The padded evolution -/

section Evolution

variable {N : Type*} [Fintype N] [DecidableEq N] (P : Type*) [Fintype P] [DecidableEq P]

/-- **The padded evolution**: `e^{-iτ(H ⊕ 0)} (ψ ⊕ 0) = (e^{-iτH} ψ) ⊕ 0`, where
`HsInstance.inlOp N P` is the isometric extension by zero `ι : ℂ^N → ℂ^{N ⊕ P}`. -/
theorem evolve_padMat (H : Matrix N N ℂ) (τ : ℝ) (ψ : EuclideanSpace ℂ N) :
    evolve (padMat P H) τ (HsInstance.inlOp N P ψ) = HsInstance.inlOp N P (evolve H τ ψ) := by
  rw [padMat, evolve_fromBlocks_zero]
  ext k
  cases k with
  | inl i => simp
  | inr p =>
    have h0 : (WithLp.toLp 2 fun _ : P => (0 : ℂ)) = 0 := rfl
    simp [h0]

/-- The extension by zero preserves inner products. -/
theorem inner_inlOp (x y : EuclideanSpace ℂ N) :
    ⟪HsInstance.inlOp N P x, HsInstance.inlOp N P y⟫_ℂ = ⟪x, y⟫_ℂ := by
  rw [PiLp.inner_apply, PiLp.inner_apply, Fintype.sum_sum_type]
  simp

end Evolution

/-! ### Reading the padded output on the original system -/

section Readout

variable {N : Type*} [Fintype N] [DecidableEq N] (P : Type*) [Fintype P]
  (G : Type*) [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

/-- **The readout isometry** `R : ℂ^{N ⊕ P} ⊗ G → ℂ^N ⊗ (ℂ^{Option P} ⊗ G)`:
`(R v)_{i, none} = v_{inl i}`, `(R v)_{i₀, some p} = v_{inr p}` and `(R v)_{i, some p} = 0` for
`i ≠ i₀`. The padding coordinates are moved into the garbage register, attached to the fixed
system basis state `i₀`. -/
def padReadout (i₀ : N) : SysGarb (N ⊕ P) G →L[ℂ] SysGarb N (Joint (Option P) G) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : N => Joint (Option P) G)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi fun i =>
      (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Option P => G)).symm.toContinuousLinearMap ∘L
        ContinuousLinearMap.pi fun o =>
          Option.elim o (Joint.proj (Sum.inl i)) fun p =>
            if i = i₀ then Joint.proj (Sum.inr p) else 0

variable {P G}

omit [Fintype N] [CompleteSpace G] in
/-- The `none` component of the readout is the original block. -/
theorem padReadout_none (i₀ : N) (v : SysGarb (N ⊕ P) G) (i : N) :
    padReadout P G i₀ v i none = v (Sum.inl i) := rfl

omit [Fintype N] [CompleteSpace G] in
/-- The `some p` component of the readout is the padding coordinate `p`, at `i₀` only. -/
theorem padReadout_some (i₀ : N) (v : SysGarb (N ⊕ P) G) (i : N) (p : P) :
    padReadout P G i₀ v i (some p) = if i = i₀ then v (Sum.inr p) else 0 := by
  change (if i = i₀ then Joint.proj (Sum.inr p) else 0) v = _
  split_ifs <;> rfl

omit [CompleteSpace G] in
/-- The readout preserves norms. -/
theorem norm_padReadout (i₀ : N) (v : SysGarb (N ⊕ P) G) : ‖padReadout P G i₀ v‖ = ‖v‖ := by
  have h2 : ‖padReadout P G i₀ v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, Fintype.sum_sum_type]
    simp only [PiLp.norm_sq_eq_of_L2, Fintype.sum_option, padReadout_none, padReadout_some]
    rw [Finset.sum_add_distrib, Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun p _ => ?_
    simp [apply_ite (fun x : G => ‖x‖ ^ 2)]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h2

/-- **The readout is an isometry**: `R† R = 1`. -/
theorem padReadout_isometry (i₀ : N) : (padReadout P G i₀)† ∘L padReadout P G i₀ = 1 :=
  (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).1 (norm_padReadout i₀)

/-- A readout `e` followed by `R` is again an isometry. -/
theorem padReadout_comp_isometry {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (i₀ : N) (e : K →L[ℂ] SysGarb (N ⊕ P) G) (he : e† ∘L e = 1) :
    (padReadout P G i₀ ∘L e)† ∘L (padReadout P G i₀ ∘L e) = 1 := by
  refine (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).1 fun v => ?_
  rw [ContinuousLinearMap.comp_apply, norm_padReadout]
  exact (ContinuousLinearMap.norm_map_iff_adjoint_comp_self e).2 he v

end Readout

/-! ### Observables through the readout -/

section Observable

variable {N : Type*} [Fintype N] [DecidableEq N] {P : Type*} [Fintype P] [DecidableEq P]
  {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

/-- The matrix of an operator on `ℂ^S` (the inverse of `Matrix.toEuclideanCLM`). -/
abbrev obsMat {S : Type*} [Fintype S] [DecidableEq S]
    (M : EuclideanSpace ℂ S →L[ℂ] EuclideanSpace ℂ S) : Matrix S S ℂ :=
  (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := S)).symm M

omit [CompleteSpace G] in
/-- `⟪u, (M ⊗ 1) v⟫ = Σ_{i,i'} M_{i i'} ⟪u_i, v_{i'}⟫`. -/
theorem inner_liftObs_apply {S : Type*} [Fintype S] [DecidableEq S]
    (M : EuclideanSpace ℂ S →L[ℂ] EuclideanSpace ℂ S) (u v : SysGarb S G) :
    ⟪u, liftObs M v⟫_ℂ = ∑ i, ∑ i', obsMat M i i' * ⟪u i, v i'⟫_ℂ := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [liftObs, Joint.kernel_apply, inner_sum]
  refine Finset.sum_congr rfl fun i' _ => ?_
  rw [inner_smul_right]

variable (P) in
/-- **The block observable** `M ⊕ c 1_P` on `ℂ^{N ⊕ P}`. -/
def blockObs (M : EuclideanSpace ℂ N →L[ℂ] EuclideanSpace ℂ N) (c : ℂ) :
    EuclideanSpace ℂ (N ⊕ P) →L[ℂ] EuclideanSpace ℂ (N ⊕ P) :=
  Matrix.toEuclideanCLM (𝕜 := ℂ) (n := N ⊕ P) (Matrix.fromBlocks (obsMat M) 0 0 (c • 1))

/-- The matrix of the block observable. -/
theorem obsMat_blockObs (M : EuclideanSpace ℂ N →L[ℂ] EuclideanSpace ℂ N) (c : ℂ) :
    obsMat (blockObs P M c) = Matrix.fromBlocks (obsMat M) 0 0 (c • 1) :=
  StarAlgEquiv.symm_apply_apply _ _

omit [Fintype N] [DecidableEq P] [CompleteSpace G] in
/-- The garbage inner products of two readouts. -/
theorem inner_padReadout_apply (i₀ : N) (u v : SysGarb (N ⊕ P) G) (i i' : N) :
    ⟪padReadout P G i₀ u i, padReadout P G i₀ v i'⟫_ℂ = ⟪u (Sum.inl i), v (Sum.inl i')⟫_ℂ +
      if i = i₀ ∧ i' = i₀ then ∑ p, ⟪u (Sum.inr p), v (Sum.inr p)⟫_ℂ else 0 := by
  rw [PiLp.inner_apply, Fintype.sum_option, padReadout_none, padReadout_none]
  congr 1
  simp only [padReadout_some]
  by_cases h : i = i₀ ∧ i' = i₀
  · obtain ⟨rfl, rfl⟩ := h
    simp
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun p _ => ?_
    by_cases h1 : i = i₀
    · rw [if_pos h1, if_neg (fun h2 => h ⟨h1, h2⟩), inner_zero_right]
    · rw [if_neg h1, inner_zero_left]

omit [CompleteSpace G] in
/-- The sesquilinear form of `M ⊗ 1` through the readout is that of `(M ⊕ M_{i₀ i₀} 1_P) ⊗ 1`. -/
theorem inner_padReadout_liftObs (i₀ : N) (M : EuclideanSpace ℂ N →L[ℂ] EuclideanSpace ℂ N)
    (u v : SysGarb (N ⊕ P) G) :
    ⟪padReadout P G i₀ u, liftObs M (padReadout P G i₀ v)⟫_ℂ =
      ⟪u, liftObs (blockObs P M (obsMat M i₀ i₀)) v⟫_ℂ := by
  rw [inner_liftObs_apply, inner_liftObs_apply, obsMat_blockObs]
  simp only [inner_padReadout_apply, mul_add, Finset.sum_add_distrib, Fintype.sum_sum_type,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, zero_mul, Finset.sum_const_zero, add_zero,
    Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, ite_mul]
  congr 1
  rw [Finset.sum_eq_single i₀ (fun b _ hb => Finset.sum_eq_zero fun b' _ => if_neg fun h => hb h.1)
      (by simp),
    Finset.sum_eq_single i₀ (fun b' _ hb' => if_neg fun h => hb' h.2) (by simp),
    if_pos ⟨rfl, rfl⟩, Finset.mul_sum, zero_add]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- **Operator form**: `R† (M ⊗ 1_{Option P ⊗ G}) R = (M ⊕ M_{i₀ i₀} 1_P) ⊗ 1_G`. -/
theorem padReadout_adjoint_liftObs (i₀ : N) (M : EuclideanSpace ℂ N →L[ℂ] EuclideanSpace ℂ N) :
    (padReadout P G i₀)† ∘L liftObs M ∘L padReadout P G i₀ =
      liftObs (blockObs P M (obsMat M i₀ i₀)) := by
  ext1 v
  refine ext_inner_left ℂ fun u => ?_
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    ContinuousLinearMap.comp_apply]
  exact inner_padReadout_liftObs i₀ M u v

/-- **Measuring through the readout**: `outObs (R ∘ e) M = outObs e (M ⊕ M_{i₀ i₀} 1_P)`. -/
theorem outObs_padReadout {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (i₀ : N) (e : K →L[ℂ] SysGarb (N ⊕ P) G)
    (M : EuclideanSpace ℂ N →L[ℂ] EuclideanSpace ℂ N) :
    outObs (padReadout P G i₀ ∘L e) M = outObs e (blockObs P M (obsMat M i₀ i₀)) := by
  rw [outObs, outObs, ContinuousLinearMap.adjoint_comp, ← padReadout_adjoint_liftObs i₀ M]
  simp only [ContinuousLinearMap.comp_assoc]

/-- The block observable of a self-adjoint `M` with real `c` is self-adjoint. -/
theorem isSelfAdjoint_blockObs {M : EuclideanSpace ℂ N →L[ℂ] EuclideanSpace ℂ N}
    (hM : IsSelfAdjoint M) {c : ℂ} (hc : star c = c) : IsSelfAdjoint (blockObs P M c) := by
  refine IsSelfAdjoint.map ?_ (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := N ⊕ P))
  have hA : (obsMat M).IsHermitian := hM.map _
  refine Matrix.IsHermitian.fromBlocks hA (by simp) ?_
  show (c • (1 : Matrix P P ℂ))ᴴ = c • 1
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, hc]

/-- `‖M ⊕ c 1_P‖ ≤ max(‖M‖, |c|)`. -/
theorem norm_blockObs_le (M : EuclideanSpace ℂ N →L[ℂ] EuclideanSpace ℂ N) (c : ℂ) :
    ‖blockObs P M c‖ ≤ max ‖M‖ ‖c‖ := by
  rw [blockObs, Matrix.l2_opNorm_toEuclideanCLM, norm_fromBlocks_zero]
  refine max_le_max (le_of_eq ?_) ?_
  · rw [Matrix.cstar_norm_def, StarAlgEquiv.apply_symm_apply]
  · calc ‖c • (1 : Matrix P P ℂ)‖ ≤ ‖c‖ * ‖(1 : Matrix P P ℂ)‖ := norm_smul_le _ _
      _ ≤ ‖c‖ * 1 := by
          gcongr
          rw [Matrix.cstar_norm_def, map_one]
          exact ContinuousLinearMap.norm_id_le
      _ = ‖c‖ := mul_one _

omit [Fintype P] [DecidableEq P] [CompleteSpace G] in
/-- The entries of the matrix of `M`: `M_{i j} = (M e_j)_i`. -/
theorem obsMat_apply (M : EuclideanSpace ℂ N →L[ℂ] EuclideanSpace ℂ N) (i j : N) :
    obsMat M i j = M (EuclideanSpace.single j 1) i := by
  conv_rhs => rw [← StarAlgEquiv.apply_symm_apply (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := N)) M]
  rw [Helpers.SpinChain.toEuclideanCLM_apply_apply]
  simp

omit [Fintype P] [DecidableEq P] [CompleteSpace G] in
/-- An entry is bounded by the operator norm: `|M_{i j}| ≤ ‖M‖`. -/
theorem norm_obsMat_apply_le (M : EuclideanSpace ℂ N →L[ℂ] EuclideanSpace ℂ N) (i j : N) :
    ‖obsMat M i j‖ ≤ ‖M‖ := by
  rw [obsMat_apply]
  calc ‖M (EuclideanSpace.single j 1) i‖ ≤ ‖M (EuclideanSpace.single j 1)‖ :=
        PiLp.norm_apply_le _ _
    _ ≤ ‖M‖ * ‖(EuclideanSpace.single j 1 : EuclideanSpace ℂ N)‖ := M.le_opNorm _
    _ = ‖M‖ := by simp

/-- The block observable acts on padded vectors as `M`: `(M ⊕ c 1)(ψ ⊕ 0) = (M ψ) ⊕ 0`. -/
theorem blockObs_inlOp (M : EuclideanSpace ℂ N →L[ℂ] EuclideanSpace ℂ N) (c : ℂ)
    (ψ : EuclideanSpace ℂ N) :
    blockObs P M c (HsInstance.inlOp N P ψ) = HsInstance.inlOp N P (M ψ) := by
  ext k
  rcases k with i | p
  · rw [HsInstance.inlOp_apply_inl, blockObs, Helpers.SpinChain.toEuclideanCLM_apply_apply,
      Fintype.sum_sum_type]
    conv_rhs => rw [← StarAlgEquiv.apply_symm_apply (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := N)) M,
      Helpers.SpinChain.toEuclideanCLM_apply_apply]
    simp
  · rw [HsInstance.inlOp_apply_inr, blockObs, Helpers.SpinChain.toEuclideanCLM_apply_apply,
      Fintype.sum_sum_type]
    simp

/-- **Readout transfer without loss.** If the output `Φ`, read through `e` on the padded
system `N ⊕ P`, is `ε`-accurate for a padded target `ψ ⊕ 0`, then the same output, read through
`R ∘ e` on the original system `N`, is `ε`-accurate for `ψ`, with the same `ε`: every Hermitian
contraction `M` on `ℂ^N` is measured through `R` as the Hermitian contraction
`M ⊕ M_{i₀ i₀} 1_P` on `ℂ^{N ⊕ P}`, which has the same expectation on `ψ ⊕ 0` as `M` on `ψ`. -/
theorem accurate_padReadout {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (i₀ : N) (e : K →L[ℂ] SysGarb (N ⊕ P) G) (Φ : K)
    (ψ : EuclideanSpace ℂ N) (ε : ℝ) (h : Accurate e Φ (HsInstance.inlOp N P ψ) ε) :
    Accurate (padReadout P G i₀ ∘L e) Φ ψ ε := by
  intro M hM hM1
  have hA : (obsMat M).IsHermitian := hM.map _
  have hc : star (obsMat M i₀ i₀) = obsMat M i₀ i₀ := hA.apply i₀ i₀
  have hn : ‖blockObs P M (obsMat M i₀ i₀)‖ ≤ 1 :=
    (norm_blockObs_le M _).trans (max_le hM1 ((norm_obsMat_apply_le M i₀ i₀).trans hM1))
  have h' := h _ (isSelfAdjoint_blockObs hM hc) hn
  rw [blockObs_inlOp, inner_inlOp] at h'
  rw [outObs_padReadout]
  exact h'

/-- **Readout transfer for the padded evolution**: accuracy for the padded target
`e^{-iτ(H ⊕ 0)} (ψ ⊕ 0)` through `e` gives accuracy for `e^{-iτH} ψ` through `R ∘ e`. -/
theorem accurate_pad_evolve {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (i₀ : N) (e : K →L[ℂ] SysGarb (N ⊕ P) G) (Φ : K) (H : Matrix N N ℂ)
    (τ : ℝ) (ψ : EuclideanSpace ℂ N) (ε : ℝ)
    (h : Accurate e Φ (evolve (padMat P H) τ (HsInstance.inlOp N P ψ)) ε) :
    Accurate (padReadout P G i₀ ∘L e) Φ (evolve H τ ψ) ε := by
  rw [evolve_padMat] at h
  exact accurate_padReadout i₀ e Φ _ ε h

end Observable

/-! ### Instance properties of padded data -/

section Instances

variable {N : Type*} [Fintype N] [DecidableEq N] {X I : Type*} (P : Type*) [Fintype P]
  [DecidableEq P]

/-- **Padding preserves the instance properties** (`HardInstance`): real symmetric, operator
norm exactly one, row and column norms at most one with maximum one, sparsity at most `s` with
maximum `s`, exact dyadic words with position-independent decode, input-independent locators.
The padding block is zero, so every property is inherited from the original block. -/
theorem padBitData_hardInstance {s B : ℕ} {hs : 0 < s} {slot : Fin s ↪ N}
    {loc : N → Fin s ↪ N} {T : BitTable I (N × N)} {y : X → I → Bool} {H : X → Matrix N N ℂ}
    {hbound : ∀ a b, -(2 : ℤ) ^ B < T.word a b ∧ T.word a b ≤ 2 ^ B}
    {hdec : ∀ x i j, ((T.value (y x) (i, j) : ℤ) : ℂ) / 2 ^ B = H x i j}
    {hrow : ∀ x i j, H x i j ≠ 0 → j ∈ Set.range (loc i)}
    {hcol : ∀ x i j, H x i j ≠ 0 → i ∈ Set.range (loc j)}
    (hD : HardInstance (bitData s B hs slot loc T y H hbound hdec hrow hcol)) :
    HardInstance (padBitData P s B hs slot loc T y H hbound hdec hrow hcol) := by
  have hT : ∀ x, (padMat P (H x))ᵀ = padMat P (H x) := fun x => by
    have h1 : (H x)ᵀ = H x := hD.transpose_eq x
    rw [padMat, Matrix.fromBlocks_transpose, h1, Matrix.transpose_zero, Matrix.transpose_zero,
      Matrix.transpose_zero]
  have hR : ∀ x i j, star (padMat P (H x) i j) = padMat P (H x) i j := fun x =>
    HsInstance.star_fromBlocks_apply (hD.real x) (fun _ _ => by simp)
  have hN : ∀ x, ‖SparseStateOverlap.matrixOperator (padMat P (H x))‖ = 1 := fun x => by
    have h1 : ‖SparseStateOverlap.matrixOperator (H x)‖ = 1 := hD.norm_eq_one x
    rw [norm_matrixOperator] at h1 ⊢
    rw [padMat, norm_fromBlocks_zero, h1, norm_zero, max_eq_left zero_le_one]
  exact
    { transpose_eq := hT
      real := hR
      isHermitian := fun x => isHermitian_of_realSymmetric ⟨hT x, hR x⟩
      norm_eq_one := hN
      row_norm_le := fun x =>
        HsInstance.sum_sq_fromBlocks_row_le (hD.row_norm_le x) (fun _ => by simp)
      col_norm_le := fun x =>
        HsInstance.sum_sq_fromBlocks_col_le (hD.col_norm_le x) (fun _ => by simp)
      row_norm_attained := fun x => by
        obtain ⟨i, hi⟩ := hD.row_norm_attained x
        exact ⟨Sum.inl i, (HsInstance.sum_sq_fromBlocks_row_inl _ _ i).trans hi⟩
      col_norm_attained := fun x => by
        obtain ⟨j, hj⟩ := hD.col_norm_attained x
        exact ⟨Sum.inl j, (HsInstance.sum_sq_fromBlocks_col_inl _ _ j).trans hj⟩
      row_sparsity_le := fun x =>
        HsInstance.card_fromBlocks_row_le (hD.row_sparsity_le x) (fun _ => by simp)
      col_sparsity_le := fun x =>
        HsInstance.card_fromBlocks_col_le (hD.col_sparsity_le x) (fun _ => by simp)
      row_sparsity_attained := fun x => by
        obtain ⟨i, hi⟩ := hD.row_sparsity_attained x
        exact ⟨Sum.inl i, (HsInstance.card_fromBlocks_row_inl _ _ i).trans hi⟩
      col_sparsity_attained := fun x => by
        obtain ⟨j, hj⟩ := hD.col_sparsity_attained x
        exact ⟨Sum.inl j, (HsInstance.card_fromBlocks_col_inl _ _ j).trans hj⟩
      scale_eq := rfl
      decode_eq := fun _ => rfl
      dyadic := fun x i j => by
        rcases i with i | p <;> rcases j with j | q
        · exact hD.dyadic x i j
        all_goals exact ⟨0, by simp, by positivity, by simp [padMat]⟩
      locators_const := fun _ _ => ⟨rfl, rfl, rfl, rfl⟩ }

end Instances

/-! ### The padded hard families -/

section Families

/-- **The padded search-decorated data** (time and mixed families): `searchData n μ s a τ hμ hs`
padded by `P`, with matrices `searchHam n μ s a τ j ⊕ 0_P`. -/
def padSearchData (P : Type*) [Fintype P] [DecidableEq P] (n μ s : ℕ) (a τ : ℝ) (hμ : 1 ≤ μ)
    (hs : 2 * 2 ^ μ ≤ s) :
    Data (Fin n → Fin (2 ^ μ)) (SearchIndex n μ s ⊕ P) (Word (searchBits n μ s a τ)) s :=
  padBitData P s (searchBits n μ s a τ) (pos_of_two_mul_two_pow_le hs) (padSlot _ s)
    (fullLoc (pos_of_two_mul_two_pow_le hs) (searchLoc n μ s)) (searchTable n μ s a τ)
    oneHotBits (searchHam n μ s a τ) (searchTable_bound hμ) searchTable_decode
    (searchLoc_row hs) (searchLoc_col hs)

/-- **The padded signed scalar data** (precision family): `scalarData n s τ hs` padded by `P`,
with matrices `scalarHam n s τ x ⊕ 0_P`. -/
def padScalarData (P : Type*) [Fintype P] [DecidableEq P] (n s : ℕ) (τ : ℝ) (hs : 2 ≤ s) :
    Data (Fin n → Bool) (ScalarIndex n s ⊕ P) (Word (scalarBits n s τ)) s :=
  padBitData P s (scalarBits n s τ) (by omega) (padSlot _ s) (fullLoc (by omega) (scalarLoc n s))
    (scalarTable n s τ) (fun x => x) (scalarHam n s τ) scalarTable_bound scalarTable_decode
    (scalarLoc_row hs) (scalarLoc_col hs)

/-- The native workspace of the padded search data. -/
abbrev PadSearchSpace (P : Type*) (n μ s : ℕ) (a τ : ℝ) : Type _ :=
  SparseFlagEmbedding.Space ((SearchIndex n μ s ⊕ P) × (SearchIndex n μ s ⊕ P))
    (Word (searchBits n μ s a τ))

/-- The native workspace of the padded scalar data. -/
abbrev PadScalarSpace (P : Type*) (n s : ℕ) (τ : ℝ) : Type _ :=
  SparseFlagEmbedding.Space ((ScalarIndex n s ⊕ P) × (ScalarIndex n s ⊕ P))
    (Word (scalarBits n s τ))

variable {n μ s : ℕ} {a τ ε : ℝ} (P : Type*) [Fintype P] [DecidableEq P]
  {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

-- The nested spectator spaces over the search index exceed the default instance size.
set_option synthInstance.maxSize 1024

/-- The padded search matrices are `searchHam n μ s a τ j ⊕ 0_P`. -/
@[simp] theorem padSearchData_matrix (hμ : 1 ≤ μ) (hs : 2 * 2 ^ μ ≤ s) :
    (padSearchData P n μ s a τ hμ hs).matrix = fun j => padMat P (searchHam n μ s a τ j) := rfl

/-- The padded scalar matrices are `scalarHam n s τ x ⊕ 0_P`. -/
@[simp] theorem padScalarData_matrix (hs : 2 ≤ s) :
    (padScalarData P n s τ hs).matrix = fun x => padMat P (scalarHam n s τ x) := rfl

/-- The padded search data satisfy `HardInstance` for `0 ≤ a ≤ 1`. -/
theorem padSearchData_hardInstance (hμ : 1 ≤ μ) (hs : 2 * 2 ^ μ ≤ s) (ha0 : 0 ≤ a)
    (ha1 : a ≤ 1) : HardInstance (padSearchData P n μ s a τ hμ hs) :=
  padBitData_hardInstance P (searchData_hardInstance τ hμ hs ha0 ha1)

/-- The padded scalar data satisfy `HardInstance`. -/
theorem padScalarData_hardInstance (hs : 2 ≤ s) : HardInstance (padScalarData P n s τ hs) :=
  padBitData_hardInstance P (scalarData_hardInstance τ hs)

/-- The native primitives of the padded search data are `hardCost`-query programs over the
one-hot oracle of the padded address family (spectator form). -/
theorem implementsOn_padSearchData_spec (Ω : Type*) [Fintype Ω] (hμ : 1 ≤ μ)
    (hs : 2 * 2 ^ μ ≤ s) (l : Query) :
    EncodedOracle.ImplementsOn
      (oneHotOracle (bitSpecFamily Ω (padTable (searchTable n μ s a τ) P)
        (Word (searchBits n μ s a τ))))
      (specOracles Ω (padSearchData P n μ s a τ hμ hs) l)
      (ancillaEmbed (Joint Ω (PadSearchSpace P n μ s a τ))) (hardCost l) :=
  implementsOn_padBitData_spec P Ω (pos_of_two_mul_two_pow_le hs) (padSlot _ s)
    (fullLoc (pos_of_two_mul_two_pow_le hs) (searchLoc n μ s)) (searchTable n μ s a τ)
    oneHotBits (searchHam n μ s a τ) (searchTable_bound hμ) searchTable_decode
    (searchLoc_row hs) (searchLoc_col hs) l

/-- The native primitives of the padded scalar data are `hardCost`-query programs over the bit
oracle of the padded address family (spectator form). -/
theorem implementsOn_padScalarData_spec (Ω : Type*) [Fintype Ω] (hs : 2 ≤ s) (l : Query) :
    EncodedOracle.ImplementsOn
      (bitOracle (bitSpecFamily Ω (padTable (scalarTable n s τ) P) (Word (scalarBits n s τ))))
      (specOracles Ω (padScalarData P n s τ hs) l)
      (ancillaEmbed (Joint Ω (PadScalarSpace P n s τ))) (hardCost l) :=
  implementsOn_padBitData_spec P Ω (by omega) (padSlot _ s) (fullLoc (by omega) (scalarLoc n s))
    (scalarTable n s τ) (fun x => x) (scalarHam n s τ) scalarTable_bound scalarTable_decode
    (scalarLoc_row hs) (scalarLoc_col hs) l

/-- **The time bound for the padded time family** (`time_spec` padded): an algorithm over the
padded primitives (spectator form) that is `ε`-accurate (`ε ≤ 1/64`) for the padded targets
`e^{-iτ(H_j ⊕ 0)} (ψ_in ⊕ 0)` makes at least `c_T √s τ` value queries. -/
theorem time_pad_spec (Ω : Type*) [Fintype Ω] (hτ : 1 ≤ τ) (hs : 32 ≤ s) (hε : ε ≤ 1 / 64)
    (p : MultiOracleCircuit.Program (specOracles Ω (padSearchData P (timeN τ) (hsMu s) s (timeC τ)
      τ (one_le_hsMu hs) (two_mul_hsM_le hs))))
    (φ₀ : Joint Ω (PadSearchSpace P (timeN τ) (hsMu s) s (timeC τ) τ)) (hφ₀ : ‖φ₀‖ ≤ 1)
    (e : Joint Ω (PadSearchSpace P (timeN τ) (hsMu s) s (timeC τ) τ) →L[ℂ]
      SysGarb (SearchIndex (timeN τ) (hsMu s) s ⊕ P) G) (he : e† ∘L e = 1)
    (hacc : ∀ j, Accurate e (p.eval j φ₀)
      (evolve ((padSearchData P (timeN τ) (hsMu s) s (timeC τ) τ (one_le_hsMu hs)
        (two_mul_hsM_le hs)).matrix j) τ
        (HsInstance.inlOp _ P (searchInput (timeN τ) (hsMu s) s))) ε) :
    cT * Real.sqrt s * τ ≤ p.labelCount .value ∧ cT * Real.sqrt s * τ ≤ p.count := by
  have h := (time_general hτ hs hε
    (bitSpecFamily Ω (padTable (searchTable (timeN τ) (hsMu s) s (timeC τ) τ) P)
      (Word (searchBits (timeN τ) (hsMu s) s (timeC τ) τ))) (ancillaEmbed _)
    ancillaEmbed_isometry _ (specOracles_unitary Ω _) hardCost
    (implementsOn_padSearchData_spec P Ω (one_le_hsMu hs) (two_mul_hsM_le hs)) p φ₀ hφ₀
    (padReadout P G refZero ∘L e) (padReadout_comp_isometry _ e he)
    (fun j => accurate_pad_evolve _ e _ (searchHam (timeN τ) (hsMu s) s (timeC τ) τ j) τ _ ε
      (hacc j))).2
  exact native_bound_of_cost p (by linarith)

/-- **Lemma `hsl:lem:mixed` for the padded mixed family** (`mixed_spec` padded): for `n ≥ 2`,
`0 < τ ≤ n`, `m = 2^μ ≥ 16n/τ` and `ε ≤ (τ/(2n))^n/8`, an algorithm that is `ε`-accurate for the
padded targets makes at least `(log 2/96) √(m n τ)` value queries. -/
theorem mixed_pad_spec (Ω : Type*) [Fintype Ω] (hn : 2 ≤ n) (hτ : 0 < τ) (hτn : τ ≤ n)
    (hm : 16 * n / τ ≤ (2 : ℝ) ^ μ) (hμ : 1 ≤ μ) (hs : 2 * 2 ^ μ ≤ s)
    (hε : ε ≤ (τ / (2 * n)) ^ n / 8)
    (p : MultiOracleCircuit.Program (specOracles Ω (padSearchData P n μ s 1 τ hμ hs)))
    (φ₀ : Joint Ω (PadSearchSpace P n μ s 1 τ)) (hφ₀ : ‖φ₀‖ ≤ 1)
    (e : Joint Ω (PadSearchSpace P n μ s 1 τ) →L[ℂ] SysGarb (SearchIndex n μ s ⊕ P) G)
    (he : e† ∘L e = 1)
    (hacc : ∀ j, Accurate e (p.eval j φ₀)
      (evolve ((padSearchData P n μ s 1 τ hμ hs).matrix j) τ
        (HsInstance.inlOp _ P (searchInput n μ s))) ε) :
    Real.log 2 / 96 * Real.sqrt ((2 : ℝ) ^ μ * n * τ) ≤ p.labelCount .value ∧
      Real.log 2 / 96 * Real.sqrt ((2 : ℝ) ^ μ * n * τ) ≤ p.count := by
  have h := mixed_general hn hτ hτn hm hε
    (bitSpecFamily Ω (padTable (searchTable n μ s 1 τ) P) (Word (searchBits n μ s 1 τ)))
    (ancillaEmbed _) ancillaEmbed_isometry _ (specOracles_unitary Ω _) hardCost
    (implementsOn_padSearchData_spec P Ω hμ hs) p φ₀ hφ₀
    (padReadout P G refZero ∘L e) (padReadout_comp_isometry _ e he)
    (fun j => accurate_pad_evolve _ e _ (searchHam n μ s 1 τ j) τ _ ε (hacc j))
  exact native_bound_of_cost p (by linarith)

/-- **Lemma `hsl:lem:precision` for the padded precision family** (`precision_spec` padded):
for `n ≥ 1`, `0 < τ ≤ n`, `2 ≤ s` and `ε ≤ (τ/(2n))^n/8`, an algorithm that is `ε`-accurate for
the padded targets makes at least `n/4` value queries. No seed or readout norm hypothesis. -/
theorem precision_pad_spec (Ω : Type*) [Fintype Ω] (hn : 1 ≤ n) (hτ : 0 < τ) (hτn : τ ≤ n)
    (hs : 2 ≤ s) (hε : ε ≤ (τ / (2 * n)) ^ n / 8)
    (p : MultiOracleCircuit.Program (specOracles Ω (padScalarData P n s τ hs)))
    (φ₀ : Joint Ω (PadScalarSpace P n s τ))
    (e : Joint Ω (PadScalarSpace P n s τ) →L[ℂ] SysGarb (ScalarIndex n s ⊕ P) G)
    (hacc : ∀ x, Accurate e (p.eval x φ₀)
      (evolve ((padScalarData P n s τ hs).matrix x) τ
        (HsInstance.inlOp _ P (scalarInput n s))) ε) :
    (n : ℝ) / 4 ≤ p.labelCount .value ∧ (n : ℝ) / 4 ≤ p.count := by
  have h := precision_general hn hτ hτn hε
    (bitSpecFamily Ω (padTable (scalarTable n s τ) P) (Word (scalarBits n s τ)))
    (ancillaEmbed _) ancillaEmbed_isometry _ (specOracles_unitary Ω _) hardCost
    (implementsOn_padScalarData_spec P Ω hs) p φ₀ (padReadout P G refZero ∘L e)
    (fun x => accurate_pad_evolve _ e _ (scalarHam n s τ x) τ _ ε (hacc x))
  exact native_bound_of_cost p (by linarith)

end Families

/-! ### Theorem `hsl:thm:main` for the padded families -/

section Main

/-- **The padded time family**: `timeData τ s hs` padded by `P` (matrices
`H_j ⊕ 0_P`, `n = timeN τ`, `a = timeC τ`, `m = 2^{hsMu s}`). -/
def timePadData (τ : ℝ) (s : ℕ) (hs : 32 ≤ s) (P : Type*) [Fintype P] [DecidableEq P] :
    Data (Fin (timeN τ) → Fin (2 ^ hsMu s)) (SearchIndex (timeN τ) (hsMu s) s ⊕ P)
      (Word (searchBits (timeN τ) (hsMu s) s (timeC τ) τ)) s :=
  padSearchData P (timeN τ) (hsMu s) s (timeC τ) τ (one_le_hsMu hs) (two_mul_hsM_le hs)

/-- **The padded mixed family**: `mixedMainData τ ε s hs` padded by `P` (`n = precN τ ε`,
`a = 1`). -/
def mixedPadData (τ ε : ℝ) (s : ℕ) (hs : 32 ≤ s) (P : Type*) [Fintype P] [DecidableEq P] :
    Data (Fin (precN τ ε) → Fin (2 ^ hsMu s)) (SearchIndex (precN τ ε) (hsMu s) s ⊕ P)
      (Word (searchBits (precN τ ε) (hsMu s) s 1 τ)) s :=
  padSearchData P (precN τ ε) (hsMu s) s 1 τ (one_le_hsMu hs) (two_mul_hsM_le hs)

/-- **The padded precision family**: `precisionMainData τ ε s hs` padded by `P`
(`n = precN τ ε`). -/
def precisionPadData (τ ε : ℝ) (s : ℕ) (hs : 32 ≤ s) (P : Type*) [Fintype P] [DecidableEq P] :
    Data (Fin (precN τ ε) → Bool) (ScalarIndex (precN τ ε) s ⊕ P)
      (Word (scalarBits (precN τ ε) s τ)) s :=
  padScalarData P (precN τ ε) s τ (by omega)

variable {τ ε : ℝ} {s : ℕ} (P : Type*) [Fintype P] [DecidableEq P]
  {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

-- The nested spectator spaces over the search index exceed the default instance size.
set_option synthInstance.maxSize 1024

/-- **Instance properties of the padded families** (Theorem `hsl:thm:main`, "with further
known padding allowed"): for any paddings `PT`, `PM`, `PP`, the three padded families satisfy
`HardInstance` (real symmetric, operator norm and maximum row and column norms exactly one,
maximum row and column sparsity exactly `s`, exact dyadic words, input-independent locators),
and their dimensions are at most `4 s (τ + r + 1)` plus the padding size. -/
theorem hard_instances_pad (h : HSRange τ s ε) (PT PM PP : Type*) [Fintype PT] [DecidableEq PT]
    [Fintype PM] [DecidableEq PM] [Fintype PP] [DecidableEq PP] :
    HardInstance (timePadData τ s h.s_ge PT) ∧ HardInstance (mixedPadData τ ε s h.s_ge PM) ∧
      HardInstance (precisionPadData τ ε s h.s_ge PP) ∧
      (Fintype.card (SearchIndex (timeN τ) (hsMu s) s ⊕ PT) : ℝ) ≤
        4 * s * (τ + hsR τ ε + 1) + Fintype.card PT ∧
      (Fintype.card (SearchIndex (precN τ ε) (hsMu s) s ⊕ PM) : ℝ) ≤
        4 * s * (τ + hsR τ ε + 1) + Fintype.card PM ∧
      (Fintype.card (ScalarIndex (precN τ ε) s ⊕ PP) : ℝ) ≤
        4 * s * (τ + hsR τ ε + 1) + Fintype.card PP := by
  obtain ⟨-, -, -, h1, h2, h3⟩ := hard_instances h
  refine ⟨padSearchData_hardInstance PT _ _ (timeC_pos (by linarith [h.one_le_tau])).le
      (timeC_le_one τ), padSearchData_hardInstance PM _ _ zero_le_one le_rfl,
    padScalarData_hardInstance PP _, ?_, ?_, ?_⟩ <;>
  · rw [Fintype.card_sum, Nat.cast_add]
    linarith

/-- **Time family, padded** (eq. `hsl:eq:timelower`), spectator form: an algorithm that is
`ε`-accurate for the padded targets `e^{-iτ(H_j ⊕ 0)} (ψ_in ⊕ 0)` makes at least `c_T √s τ`
value queries, exactly as in `time_main`. -/
theorem time_main_pad (h : HSRange τ s ε) (Ω : Type*) [Fintype Ω]
    (p : MultiOracleCircuit.Program (specOracles Ω (timePadData τ s h.s_ge P)))
    (φ₀ : Joint Ω (PadSearchSpace P (timeN τ) (hsMu s) s (timeC τ) τ)) (hφ₀ : ‖φ₀‖ ≤ 1)
    (e : Joint Ω (PadSearchSpace P (timeN τ) (hsMu s) s (timeC τ) τ) →L[ℂ]
      SysGarb (SearchIndex (timeN τ) (hsMu s) s ⊕ P) G) (he : e† ∘L e = 1)
    (hacc : ∀ j, Accurate e (p.eval j φ₀)
      (evolve ((timePadData τ s h.s_ge P).matrix j) τ
        (HsInstance.inlOp _ P (searchInput (timeN τ) (hsMu s) s))) ε) :
    cT * Real.sqrt s * τ ≤ p.labelCount .value ∧ cT * Real.sqrt s * τ ≤ p.count :=
  time_pad_spec P Ω h.one_le_tau h.s_ge h.eps_le p φ₀ hφ₀ e he hacc

/-- **Mixed family, padded** (eq. `hsl:eq:mixrbound`), spectator form: if `L ≥ 64τ` and
`s ≥ 64n/τ`, an algorithm that is `ε`-accurate for the padded targets makes at least
`(log 2/(384√2)) √(sτr)` value queries, exactly as in `mixed_main`. -/
theorem mixed_main_pad (h : HSRange τ s ε) (hL : 64 * τ ≤ hsL ε)
    (hs : 64 * (precN τ ε : ℝ) / τ ≤ s) (Ω : Type*) [Fintype Ω]
    (p : MultiOracleCircuit.Program (specOracles Ω (mixedPadData τ ε s h.s_ge P)))
    (φ₀ : Joint Ω (PadSearchSpace P (precN τ ε) (hsMu s) s 1 τ)) (hφ₀ : ‖φ₀‖ ≤ 1)
    (e : Joint Ω (PadSearchSpace P (precN τ ε) (hsMu s) s 1 τ) →L[ℂ]
      SysGarb (SearchIndex (precN τ ε) (hsMu s) s ⊕ P) G) (he : e† ∘L e = 1)
    (hacc : ∀ j, Accurate e (p.eval j φ₀)
      (evolve ((mixedPadData τ ε s h.s_ge P).matrix j) τ
        (HsInstance.inlOp _ P (searchInput (precN τ ε) (hsMu s) s))) ε) :
    Real.log 2 / (384 * Real.sqrt 2) * Real.sqrt (s * τ * hsR τ ε) ≤ p.labelCount .value ∧
      Real.log 2 / (384 * Real.sqrt 2) * Real.sqrt (s * τ * hsR τ ε) ≤ p.count := by
  obtain ⟨hn, hrn, hτr, -⟩ := precN_range h hL
  have h16 := sixteen_eps_le h hL
  have hmix := mixed_pad_spec P (n := precN τ ε) (μ := hsMu s) (s := s) (τ := τ) (ε := ε) Ω hn
    (by linarith [h.one_le_tau]) (by linarith) (mixed_m_cond h hs) (one_le_hsMu h.s_ge)
    (two_mul_hsM_le h.s_ge) (by linarith [h.eps_pos]) p φ₀ hφ₀ e he hacc
  have hnum := mixrbound h hL
  exact ⟨hnum.trans hmix.1, hnum.trans hmix.2⟩

/-- **Precision family, padded** (eqs. `hsl:eq:rbound`, `hsl:eq:failedmix`), spectator form: if
`L ≥ 64τ`, an algorithm that is `ε`-accurate for the padded targets makes at least `r/32` value
queries, and at least `√(sτr)/(64√2)` when `s < 64n/τ`, exactly as in `precision_main`. -/
theorem precision_main_pad (h : HSRange τ s ε) (hL : 64 * τ ≤ hsL ε) (Ω : Type*) [Fintype Ω]
    (p : MultiOracleCircuit.Program (specOracles Ω (precisionPadData τ ε s h.s_ge P)))
    (φ₀ : Joint Ω (PadScalarSpace P (precN τ ε) s τ))
    (e : Joint Ω (PadScalarSpace P (precN τ ε) s τ) →L[ℂ]
      SysGarb (ScalarIndex (precN τ ε) s ⊕ P) G)
    (hacc : ∀ x, Accurate e (p.eval x φ₀)
      (evolve ((precisionPadData τ ε s h.s_ge P).matrix x) τ
        (HsInstance.inlOp _ P (scalarInput (precN τ ε) s))) ε) :
    hsR τ ε / 32 ≤ p.labelCount .value ∧ hsR τ ε / 32 ≤ p.count ∧
      ((s : ℝ) < 64 * precN τ ε / τ →
        Real.sqrt (s * τ * hsR τ ε) / (64 * Real.sqrt 2) ≤ p.labelCount .value) := by
  obtain ⟨hn, hrn, hτr, -⟩ := precN_range h hL
  have h16 := sixteen_eps_le h hL
  have hP := precision_pad_spec P (n := precN τ ε) (s := s) (τ := τ) (ε := ε) Ω (by omega)
    (by linarith [h.one_le_tau]) (by linarith) (le_trans (by norm_num) h.s_ge)
    (by linarith [h.eps_pos]) p φ₀ e hacc
  have hrb := rbound h hL
  exact ⟨hrb.trans hP.1, hrb.trans hP.2, fun hs' => (failedmix h hL hs').trans hP.1⟩

/-- **"For three nonnegative numbers, that maximum is at least one third of their sum"** (the remark
after Theorem `hsl:thm:main`): if `A ≤ Q_T`, `B ≤ Q_M` and `C ≤ Q_P`, then
`(A + B + C)/3 ≤ max(Q_T, Q_M, Q_P)`. The three terms of eq. `hsl:eq:main` are witnessed by
different families; this is the step that combines them (`assembly` is its quantitative form). -/
theorem third_sum_le_max {A B C QT QM QP : ℝ} (hA : A ≤ QT) (hB : B ≤ QM) (hC : C ≤ QP) :
    (A + B + C) / 3 ≤ max QT (max QM QP) := by
  have h1 := le_max_left QT (max QM QP)
  have h2 := (le_max_left QM QP).trans (le_max_right QT (max QM QP))
  have h3 := (le_max_right QM QP).trans (le_max_right QT (max QM QP))
  linarith

/-- **Theorem `hsl:thm:main`, eq. `hsl:eq:main`, for the padded families** (max form): for any
paddings `PT`, `PM`, `PP` and any three algorithms (spectator form), accurate for the padded
targets of the time, mixed and precision families respectively,
`c₀ (√s τ + √(sτr) + r) ≤ max(Q_T, Q_M, Q_P)`, `c₀ = log 2/(4096π)`, exactly as in `main_max`. -/
theorem main_max_pad (h : HSRange τ s ε) (PT PM PP : Type*) [Fintype PT] [DecidableEq PT]
    [Fintype PM] [DecidableEq PM] [Fintype PP] [DecidableEq PP] (ΩT ΩM ΩP : Type*)
    [Fintype ΩT] [Fintype ΩM] [Fintype ΩP] {GT GM GP : Type*}
    [NormedAddCommGroup GT] [InnerProductSpace ℂ GT] [CompleteSpace GT]
    [NormedAddCommGroup GM] [InnerProductSpace ℂ GM] [CompleteSpace GM]
    [NormedAddCommGroup GP] [InnerProductSpace ℂ GP] [CompleteSpace GP]
    (pT : MultiOracleCircuit.Program (specOracles ΩT (timePadData τ s h.s_ge PT)))
    (φT : Joint ΩT (PadSearchSpace PT (timeN τ) (hsMu s) s (timeC τ) τ)) (hφT : ‖φT‖ ≤ 1)
    (eT : Joint ΩT (PadSearchSpace PT (timeN τ) (hsMu s) s (timeC τ) τ) →L[ℂ]
      SysGarb (SearchIndex (timeN τ) (hsMu s) s ⊕ PT) GT) (heT : eT† ∘L eT = 1)
    (haccT : ∀ j, Accurate eT (pT.eval j φT)
      (evolve ((timePadData τ s h.s_ge PT).matrix j) τ
        (HsInstance.inlOp _ PT (searchInput (timeN τ) (hsMu s) s))) ε)
    (pM : MultiOracleCircuit.Program (specOracles ΩM (mixedPadData τ ε s h.s_ge PM)))
    (φM : Joint ΩM (PadSearchSpace PM (precN τ ε) (hsMu s) s 1 τ)) (hφM : ‖φM‖ ≤ 1)
    (eM : Joint ΩM (PadSearchSpace PM (precN τ ε) (hsMu s) s 1 τ) →L[ℂ]
      SysGarb (SearchIndex (precN τ ε) (hsMu s) s ⊕ PM) GM) (heM : eM† ∘L eM = 1)
    (haccM : ∀ j, Accurate eM (pM.eval j φM)
      (evolve ((mixedPadData τ ε s h.s_ge PM).matrix j) τ
        (HsInstance.inlOp _ PM (searchInput (precN τ ε) (hsMu s) s))) ε)
    (pP : MultiOracleCircuit.Program (specOracles ΩP (precisionPadData τ ε s h.s_ge PP)))
    (φP : Joint ΩP (PadScalarSpace PP (precN τ ε) s τ))
    (eP : Joint ΩP (PadScalarSpace PP (precN τ ε) s τ) →L[ℂ]
      SysGarb (ScalarIndex (precN τ ε) s ⊕ PP) GP)
    (haccP : ∀ x, Accurate eP (pP.eval x φP)
      (evolve ((precisionPadData τ ε s h.s_ge PP).matrix x) τ
        (HsInstance.inlOp _ PP (scalarInput (precN τ ε) s))) ε) :
    c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
      max (pT.labelCount .value : ℝ) (max (pM.labelCount .value : ℝ) (pP.labelCount .value)) := by
  refine assembly h (time_main_pad PT h ΩT pT φT hφT eT heT haccT).1 (fun hL => ?_)
    (fun hL hs => ?_)
  · have := precision_main_pad PP h hL ΩP pP φP eP haccP
    exact ⟨this.1, this.2.2⟩
  · exact (mixed_main_pad PM h hL hs ΩM pM φM hφM eM heM haccM).1

end Main

/-! ### A common dimension -/

section Common

/-- The padding register `Fin (Nd - |S|)` that brings an index type `S` to dimension `Nd`. -/
abbrev PadTo (S : Type*) [Fintype S] (Nd : ℕ) : Type := Fin (Nd - Fintype.card S)

/-- Padding by `PadTo S Nd` gives dimension exactly `Nd` when `|S| ≤ Nd`. -/
theorem card_padTo {S : Type*} [Fintype S] {Nd : ℕ} (h : Fintype.card S ≤ Nd) :
    Fintype.card (S ⊕ PadTo S Nd) = Nd := by
  rw [Fintype.card_sum, Fintype.card_fin]
  omega

variable {τ ε : ℝ} {s : ℕ}

/-- Every `Nd ≥ 4 s (τ + r + 1)` is at least the dimension of each of the three hard families
(`hard_instances`). -/
theorem card_le_of_dim (h : HSRange τ s ε) {Nd : ℕ} (hNd : 4 * s * (τ + hsR τ ε + 1) ≤ Nd) :
    Fintype.card (SearchIndex (timeN τ) (hsMu s) s) ≤ Nd ∧
      Fintype.card (SearchIndex (precN τ ε) (hsMu s) s) ≤ Nd ∧
      Fintype.card (ScalarIndex (precN τ ε) s) ≤ Nd := by
  obtain ⟨-, -, -, h1, h2, h3⟩ := hard_instances h
  exact ⟨Nat.cast_le.mp (h1.trans hNd), Nat.cast_le.mp (h2.trans hNd),
    Nat.cast_le.mp (h3.trans hNd)⟩

-- The nested spectator spaces over the search index exceed the default instance size.
set_option synthInstance.maxSize 1024

/-- **The three families in one common dimension** (the last clause of Theorem `hsl:thm:main` and
the end of its proof). Let `Nd` be at least the dimension of each family (for instance any
`Nd ≥ 4 s (τ + r + 1)`, `card_le_of_dim`), and pad family `X` by `PadTo N_X Nd = Fin (Nd - |N_X|)`.
Then all three padded index types have exactly `Nd` elements, and for any three algorithms
(spectator form), accurate for the padded targets of the time, mixed and precision families
respectively, `c₀ (√s τ + √(sτr) + r) ≤ max(Q_T, Q_M, Q_P)`. -/
theorem main_max_common_dimension (h : HSRange τ s ε) (Nd : ℕ)
    (hT : Fintype.card (SearchIndex (timeN τ) (hsMu s) s) ≤ Nd)
    (hM : Fintype.card (SearchIndex (precN τ ε) (hsMu s) s) ≤ Nd)
    (hP : Fintype.card (ScalarIndex (precN τ ε) s) ≤ Nd) (ΩT ΩM ΩP : Type*)
    [Fintype ΩT] [Fintype ΩM] [Fintype ΩP] {GT GM GP : Type*}
    [NormedAddCommGroup GT] [InnerProductSpace ℂ GT] [CompleteSpace GT]
    [NormedAddCommGroup GM] [InnerProductSpace ℂ GM] [CompleteSpace GM]
    [NormedAddCommGroup GP] [InnerProductSpace ℂ GP] [CompleteSpace GP]
    (pT : MultiOracleCircuit.Program (specOracles ΩT
      (timePadData τ s h.s_ge (PadTo (SearchIndex (timeN τ) (hsMu s) s) Nd))))
    (φT : Joint ΩT (PadSearchSpace (PadTo (SearchIndex (timeN τ) (hsMu s) s) Nd) (timeN τ)
      (hsMu s) s (timeC τ) τ)) (hφT : ‖φT‖ ≤ 1)
    (eT : Joint ΩT (PadSearchSpace (PadTo (SearchIndex (timeN τ) (hsMu s) s) Nd) (timeN τ)
      (hsMu s) s (timeC τ) τ) →L[ℂ]
      SysGarb (SearchIndex (timeN τ) (hsMu s) s ⊕ PadTo (SearchIndex (timeN τ) (hsMu s) s) Nd)
        GT) (heT : eT† ∘L eT = 1)
    (haccT : ∀ j, Accurate eT (pT.eval j φT)
      (evolve ((timePadData τ s h.s_ge (PadTo (SearchIndex (timeN τ) (hsMu s) s) Nd)).matrix j)
        τ (HsInstance.inlOp _ _ (searchInput (timeN τ) (hsMu s) s))) ε)
    (pM : MultiOracleCircuit.Program (specOracles ΩM
      (mixedPadData τ ε s h.s_ge (PadTo (SearchIndex (precN τ ε) (hsMu s) s) Nd))))
    (φM : Joint ΩM (PadSearchSpace (PadTo (SearchIndex (precN τ ε) (hsMu s) s) Nd) (precN τ ε)
      (hsMu s) s 1 τ)) (hφM : ‖φM‖ ≤ 1)
    (eM : Joint ΩM (PadSearchSpace (PadTo (SearchIndex (precN τ ε) (hsMu s) s) Nd) (precN τ ε)
      (hsMu s) s 1 τ) →L[ℂ]
      SysGarb (SearchIndex (precN τ ε) (hsMu s) s ⊕
        PadTo (SearchIndex (precN τ ε) (hsMu s) s) Nd) GM) (heM : eM† ∘L eM = 1)
    (haccM : ∀ j, Accurate eM (pM.eval j φM)
      (evolve ((mixedPadData τ ε s h.s_ge
        (PadTo (SearchIndex (precN τ ε) (hsMu s) s) Nd)).matrix j)
        τ (HsInstance.inlOp _ _ (searchInput (precN τ ε) (hsMu s) s))) ε)
    (pP : MultiOracleCircuit.Program (specOracles ΩP
      (precisionPadData τ ε s h.s_ge (PadTo (ScalarIndex (precN τ ε) s) Nd))))
    (φP : Joint ΩP (PadScalarSpace (PadTo (ScalarIndex (precN τ ε) s) Nd) (precN τ ε) s τ))
    (eP : Joint ΩP (PadScalarSpace (PadTo (ScalarIndex (precN τ ε) s) Nd) (precN τ ε) s τ) →L[ℂ]
      SysGarb (ScalarIndex (precN τ ε) s ⊕ PadTo (ScalarIndex (precN τ ε) s) Nd) GP)
    (haccP : ∀ x, Accurate eP (pP.eval x φP)
      (evolve ((precisionPadData τ ε s h.s_ge (PadTo (ScalarIndex (precN τ ε) s) Nd)).matrix x)
        τ (HsInstance.inlOp _ _ (scalarInput (precN τ ε) s))) ε) :
    Fintype.card (SearchIndex (timeN τ) (hsMu s) s ⊕
        PadTo (SearchIndex (timeN τ) (hsMu s) s) Nd) = Nd ∧
      Fintype.card (SearchIndex (precN τ ε) (hsMu s) s ⊕
        PadTo (SearchIndex (precN τ ε) (hsMu s) s) Nd) = Nd ∧
      Fintype.card (ScalarIndex (precN τ ε) s ⊕ PadTo (ScalarIndex (precN τ ε) s) Nd) = Nd ∧
      c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
        max (pT.labelCount .value : ℝ) (max (pM.labelCount .value : ℝ) (pP.labelCount .value)) :=
  ⟨card_padTo hT, card_padTo hM, card_padTo hP,
    main_max_pad h _ _ _ ΩT ΩM ΩP pT φT hφT eT heT haccT pM φM hφM eM heM haccM pP φP eP haccP⟩

/-! ### Family form -/

/-- The right-hand side `c₀ (√s τ + √(sτr) + r)` of eq. `hsl:eq:main`. -/
def mainBound (τ ε : ℝ) (s : ℕ) : ℝ :=
  c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)

/-- **A family forces `b` value queries** (spectator form): every program over the native
primitives of `D` acting on an untouched spectator register `ℂ^Ω`, run on an input-independent
seed of norm at most one and read through an isometry into system ⊗ garbage `G`, that is
`ε`-accurate for the targets `e^{-iτ D.matrix x} ψ` on every input `x`, makes at least `b` value
queries. -/
def ForcesQueries {X N Z : Type*} [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z]
    {s : ℕ} (D : Data X N Z s) (ψ : EuclideanSpace ℂ N) (τ ε b : ℝ) : Prop :=
  ∀ (Ω : Type u) [Fintype Ω] (G : Type v) [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [CompleteSpace G] (p : MultiOracleCircuit.Program (specOracles Ω D))
    (φ₀ : Joint Ω (SparseFlagEmbedding.Space (N × N) Z)), ‖φ₀‖ ≤ 1 →
    ∀ e : Joint Ω (SparseFlagEmbedding.Space (N × N) Z) →L[ℂ] SysGarb N G, e† ∘L e = 1 →
    (∀ x, Accurate e (p.eval x φ₀) (evolve (D.matrix x) τ ψ) ε) → b ≤ p.labelCount .value

/-- **Theorem `hsl:thm:main`, family form, for the padded families** (as `main_exists`, with the
seed bound and the isometric readout of `ForcesQueries` assumed for all three families): for
any paddings, one of the three padded families (chosen by the parameters) forces every accurate
algorithm to make at least `c₀ (√s τ + √(sτr) + r)` value queries. -/
theorem main_exists_pad (h : HSRange τ s ε) (PT PM PP : Type*) [Fintype PT] [DecidableEq PT]
    [Fintype PM] [DecidableEq PM] [Fintype PP] [DecidableEq PP] :
    ForcesQueries.{u, v} (timePadData τ s h.s_ge PT)
        (HsInstance.inlOp _ PT (searchInput (timeN τ) (hsMu s) s)) τ ε (mainBound τ ε s) ∨
      ForcesQueries.{u, v} (mixedPadData τ ε s h.s_ge PM)
        (HsInstance.inlOp _ PM (searchInput (precN τ ε) (hsMu s) s)) τ ε (mainBound τ ε s) ∨
      ForcesQueries.{u, v} (precisionPadData τ ε s h.s_ge PP)
        (HsInstance.inlOp _ PP (scalarInput (precN τ ε) s)) τ ε (mainBound τ ε s) := by
  by_contra hneg
  simp only [ForcesQueries] at hneg
  push Not at hneg
  obtain ⟨⟨ΩT, _, GT, _, _, _, pT, φT, hφT, eT, heT, haccT, hT⟩,
    ⟨ΩM, _, GM, _, _, _, pM, φM, hφM, eM, heM, haccM, hM⟩,
    ⟨ΩP, _, GP, _, _, _, pP, φP, -, eP, -, haccP, hP⟩⟩ := hneg
  have hmax := main_max_pad h PT PM PP ΩT ΩM ΩP pT φT hφT eT heT haccT pM φM hφM eM heM haccM
    pP φP eP haccP
  have := max_lt hT (max_lt hM hP)
  rw [mainBound] at this
  linarith

/-- **The worst case in one common dimension** (the last clause of Theorem `hsl:thm:main`, family
form): for every `Nd` at least the dimension of each family (e.g. `Nd ≥ 4 s (τ + r + 1)`,
`card_le_of_dim`), the three families padded by `PadTo N_X Nd` all have dimension exactly `Nd`,
and one of them forces every accurate algorithm to make at least `c₀ (√s τ + √(sτr) + r)` value
queries. So the worst-case query complexity in dimension `Nd` obeys eq. `hsl:eq:main`. -/
theorem main_exists_common_dimension (h : HSRange τ s ε) (Nd : ℕ)
    (hT : Fintype.card (SearchIndex (timeN τ) (hsMu s) s) ≤ Nd)
    (hM : Fintype.card (SearchIndex (precN τ ε) (hsMu s) s) ≤ Nd)
    (hP : Fintype.card (ScalarIndex (precN τ ε) s) ≤ Nd) :
    Fintype.card (SearchIndex (timeN τ) (hsMu s) s ⊕
        PadTo (SearchIndex (timeN τ) (hsMu s) s) Nd) = Nd ∧
      Fintype.card (SearchIndex (precN τ ε) (hsMu s) s ⊕
        PadTo (SearchIndex (precN τ ε) (hsMu s) s) Nd) = Nd ∧
      Fintype.card (ScalarIndex (precN τ ε) s ⊕ PadTo (ScalarIndex (precN τ ε) s) Nd) = Nd ∧
      (ForcesQueries.{u, v} (timePadData τ s h.s_ge (PadTo (SearchIndex (timeN τ) (hsMu s) s) Nd))
          (HsInstance.inlOp _ _ (searchInput (timeN τ) (hsMu s) s)) τ ε (mainBound τ ε s) ∨
        ForcesQueries.{u, v}
          (mixedPadData τ ε s h.s_ge (PadTo (SearchIndex (precN τ ε) (hsMu s) s) Nd))
          (HsInstance.inlOp _ _ (searchInput (precN τ ε) (hsMu s) s)) τ ε (mainBound τ ε s) ∨
        ForcesQueries.{u, v} (precisionPadData τ ε s h.s_ge (PadTo (ScalarIndex (precN τ ε) s) Nd))
          (HsInstance.inlOp _ _ (scalarInput (precN τ ε) s)) τ ε (mainBound τ ε s)) :=
  ⟨card_padTo hT, card_padTo hM, card_padTo hP, main_exists_pad h _ _ _⟩

end Common

end

end LowerBoundRemarks.HamiltonianPadding
