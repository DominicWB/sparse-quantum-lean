import OptimalLowerBounds.Denominator
import TimeDependentHamiltonianLowerBound.Adaptive
import DeferredMeasurementLowerBounds.Access.Native

set_option synthInstance.maxHeartbeats 400000

/-!
# Admissible access to the enlarged families: controls, inverses and the common oracle

The adaptive and measured forms of the lower bounds (`AdaptiveHamiltonianLowerBound`,
`DeferredMeasurementLowerBounds`) admit every oracle label that is **admissible** for the hard data
`D` (`AdaptiveHamiltonianLowerBound.Access.Admissible`): a native call (in a fixed isometric layout
of the workspace as a direct sum of copies of the native query space, every copy applies the
identity, one native query of `D` or its inverse; weight at least one) or an input-independent
unitary (any weight). This is the access of Theorem `hsl:thm:main` (Section `hsl:sec:main`: the
native sparse access, with inverses and controls), which the proof of Proposition
`hsl:prop:two-norm` keeps for the enlarged families: "A value query to `H_X` costs at most two old
value queries [...] The enlarged supports and locator extensions are known. Thus the reduction has
constant query overhead, including inverses." This module supplies the access facts for the enlarged
families.

* **Call forms** (`admissible_callFamily`): the plain, inverse, controlled and
  controlled-inverse forms (`AdaptiveODELowerBound.Access.callFamily`) of admissible labels are
  admissible with the weight of their label, for any data: each form is a record-diagonal of
  identity, forward and inverse branches of one native call (`formOp_eq_fiber`).
* **The common oracle of the upper bounds** (`admissible_common`): the physical oracle family
  `NativeSignedFactor.physOracle D` on every block of `ℂ^ι` (the query model of
  `NativeSignedFactor.Simulates`, used by Theorems `hs:thm:optimal` and `hs:thm:two-norm`) is in
  the normal form `U⁻¹ (1_Ω ⊗ oracles D l x) U` (`common_normal_form`), hence admissible with the
  value-query weight for data with input-independent locators, and so are its call forms
  (`admissible_common_calls`).
* **One-bit entries of the enlarged data** (`hardAccess_searchTwo`, `hardAccess_scalarTwo`, and
  for the time, mixed, precision and counterexample families `hardAccess_timeTwo`,
  `hardAccess_mixedTwo`, `hardAccess_precisionTwo`, `hardAccess_denomData`): the enlarged word
  table reads the same hidden bit as the original one, so the access conditions of the weight
  method (`AdaptiveHamiltonianLowerBound.Access.HardAccess`: input-independent locators, every
  word a fixed function of at most one bit) hold along the identity (search families) and along
  `toBits` (scalar families).
-/

namespace OptimalLowerBounds

noncomputable section
set_option autoImplicit false
open SparseHamiltonian NativeSparseBlockEncoding OracleCircuit SparseLowerBounds
open SparseLowerBounds.Hamiltonian
open AdaptiveHamiltonianLowerBound.Access (Admissible NativeCall HardAccess valueWeight toBits)
open AdaptiveODELowerBound.Access (CallForm formOp callFamily)
set_option maxRecDepth 4096
set_option synthInstance.maxSize 4096

/-! ### Call forms of admissible labels -/

section Calls

variable {X N Z : Type*} [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z] {s : ℕ}
  {K L : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The operator of a call form on the control branch `b`: the call (plain), its inverse
(inverse), and on control `1` the call or its inverse, on control `0` the identity (controlled
forms). -/
def formBranch : CallForm → Bool → (K →L[ℂ] K) → (K →L[ℂ] K)
  | .plain, _, U => U
  | .inverse, _, U => star U
  | .controlled, b, U => if b then U else 1
  | .controlledInverse, b, U => if b then star U else 1

/-- **Every call form is a record-diagonal over the control**: `formOp f U = Σ_b |b⟩⟨b| ⊗ U_b`
with `U_b` the identity, `U` or `U†` (`formBranch`). -/
theorem formOp_eq_fiber (f : CallForm) (U : K →L[ℂ] K) :
    formOp f U = Joint.fiber (fun b => formBranch f b U) := by
  cases f
  · rfl
  · rfl
  · ext Ψ b
    cases b <;> simp [formOp, AdaptiveODELowerBound.Access.ctrlOp, formBranch,
      MaskedProgram.masked_apply]
  · ext Ψ b
    cases b <;> simp [formOp, AdaptiveODELowerBound.Access.ctrlOp, formBranch,
      MaskedProgram.masked_apply]

/-- Every branch of a call form of a native call is a native call in the same layout. -/
theorem nativeCall_formBranch {D : Data X N Z s} {O : X → K →L[ℂ] K} (h : NativeCall D O)
    (f : CallForm) (b : Bool) : NativeCall D (fun x => formBranch f b (O x)) := by
  cases f <;> cases b
  · exact h
  · exact h
  · exact DeferredMeasurementLowerBounds.Access.nativeCall_star D h
  · exact DeferredMeasurementLowerBounds.Access.nativeCall_star D h
  · exact DeferredMeasurementLowerBounds.Access.nativeCall_one D h
  · exact h
  · exact DeferredMeasurementLowerBounds.Access.nativeCall_one D h
  · exact DeferredMeasurementLowerBounds.Access.nativeCall_star D h

/-- **The call forms of admissible labels are admissible**, with the weight of their label (any
data, any workspace): a call form of a native call is one native call in the layout
`ℂ^Bool ⊗ (layout of the call)`; a call form of an input-independent unitary is an
input-independent unitary. -/
theorem admissible_callFamily {D : Data X N Z s} {O : L → X → K →L[ℂ] K} {w : L → ℕ}
    (hO : ∀ l, Admissible D (O l) (w l)) (c : L × CallForm) :
    Admissible D (callFamily O c) (w c.1) := by
  obtain ⟨l, f⟩ := c
  rcases hO l with ⟨hN, hw⟩ | ⟨hconst, hunit⟩
  · refine Or.inl ⟨?_, hw⟩
    have e : callFamily O (l, f) = fun x => Joint.fiber (fun b => formBranch f b (O l x)) :=
      funext fun x => formOp_eq_fiber f (O l x)
    rw [e]
    exact DeferredMeasurementLowerBounds.Access.nativeCall_fiber D
      (U := fun b x => formBranch f b (O l x)) fun b => nativeCall_formBranch hN f b
  · exact Or.inr ⟨fun x x' => AdaptiveODELowerBound.Access.callFamily_const hconst f x x',
      fun x => AdaptiveODELowerBound.Access.formOp_unitary f (hunit x)⟩

end Calls

/-! ### The common oracle of the upper bounds -/

section Common

open ODELowerBoundExtensions.Release (IsWrap isWrap_spectator)

variable {X N Z : Type} [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z] [DecidableEq Z]
  {s : ℕ}

/-- **The fixed wrapper of the physical oracle** around one native primitive: the fixed
flattening `NativeSparseMaskedAccess.layout`, the control, dummy and reference registers of the
native-control workspace as spectators (`LookupFromBasisOracle.spectator`) and the dilation
branch `Bool` (all-active mask). -/
def physWrap (N Z : Type) [Fintype N] [DecidableEq N] [Fintype Z] [DecidableEq Z]
    (A : SparseFlagEmbedding.Space (N × N) Z →L[ℂ] SparseFlagEmbedding.Space (N × N) Z) :
    NativeSignedFactor.Phys N Z →L[ℂ] NativeSignedFactor.Phys N Z :=
  MaskedProgram.masked (fun _ : Bool => true)
    (LookupFromBasisOracle.spectator
      (S := (Bool × NativeSparseMaskedAccess.Basis N Z) × NativeSparseMaskedAccess.Basis N Z)
      ((NativeSparseMaskedAccess.layout (n := N) (Z := Z)).conjStarAlgEquiv A))

/-- `physWrap` consists of spectators and fixed relabellings only. -/
theorem isWrap_physWrap (N Z : Type) [Fintype N] [DecidableEq N] [Fintype Z] [DecidableEq Z] :
    IsWrap (physWrap N Z) :=
  ((isWrap_spectator _ _).precomp (NativeSparseMaskedAccess.layout (n := N) (Z := Z))).masked Bool

/-- The physical oracle is `physWrap` of the native primitive of the same label. -/
theorem physOracle_eq_wrap (D : Data X N Z s) (l : Query) (x : X) :
    NativeSignedFactor.physOracle D l x = physWrap N Z (oracles D l x) := rfl

/-- **Normal form of the common oracle** `CoherentQuerySchedule.oracle (ι := ι) (physOracle D)`:
there are a finite spectator register `Ω` and one fixed isometric identification `U` of the
common workspace with `ℂ^Ω ⊗ NSpace` such that every label is
`U⁻¹ (1_Ω ⊗ oracles D l x) U`: one call of the native primitive of the same label with untouched
spectators. -/
theorem common_normal_form (D : Data X N Z s) (ι : Type) [Fintype ι] :
    ∃ (Ω : Type) (_ : Fintype Ω)
      (U : CommonSpace ι N Z ≃ₗᵢ[ℂ] Joint Ω (SparseFlagEmbedding.Space (N × N) Z)),
      ∀ l x, CoherentQuerySchedule.oracle (ι := ι) (NativeSignedFactor.physOracle D) l x =
        U.symm.conjStarAlgEquiv (specOracles Ω D l x) := by
  obtain ⟨Ω, _, U, hU⟩ := (isWrap_physWrap N Z).diagonalConst ι
  exact ⟨Ω, inferInstance, U, fun l x => hU (oracles D l x)⟩

/-- **The common oracle of the upper bounds is admissible** with the value-query weight, for
data with input-independent locators. -/
theorem admissible_common (D : Data X N Z s) (hrow : ∀ x x', D.rowOracle x = D.rowOracle x')
    (hcol : ∀ x x', D.columnOracle x = D.columnOracle x') (ι : Type) [Fintype ι] (q : Query) :
    Admissible D (CoherentQuerySchedule.oracle (ι := ι) (NativeSignedFactor.physOracle D) q)
      (valueWeight q) :=
  TimeDependentHamiltonianLowerBound.admissible_of_normal_form D hrow hcol
    (common_normal_form D ι) q

/-- **The call forms of the common oracle are admissible** with the value-query weight of their
label (plain, inverse, controlled and controlled-inverse forms). -/
theorem admissible_common_calls (D : Data X N Z s)
    (hrow : ∀ x x', D.rowOracle x = D.rowOracle x')
    (hcol : ∀ x x', D.columnOracle x = D.columnOracle x') (ι : Type) [Fintype ι]
    (c : Query × CallForm) :
    Admissible D (callFamily (CoherentQuerySchedule.oracle (ι := ι)
      (NativeSignedFactor.physOracle D)) c) (valueWeight c.1) :=
  admissible_callFamily (admissible_common D hrow hcol ι) c

end Common

/-! ### One-bit entries of the enlarged data -/

section HardAccess

variable {n μ s m : ℕ} {a τ c : ℝ}

/-- **The enlarged search families satisfy the access conditions along the identity**: public
locators, and the word of `((i, a), (j, b))` is that of `(i, j)`, which reads at most the one-hot
bit `[j k = q]`. -/
theorem hardAccess_searchTwo (hμ : 1 ≤ μ) (hs : 2 * 2 ^ μ ≤ s) (hm : 0 < m) (hc : c ≠ 0) :
    HardAccess (searchTwo n μ s a τ hμ hs m hm c hc) (fun j => j) where
  row_const _ _ := rfl
  column_const _ _ := rfl
  table_bit α := AdaptiveHamiltonianLowerBound.Access.bitTable_value_bit
    (enlargeTable (searchTable n μ s a τ) m) oneHotBits (fun ka => ⟨ka.1, ka.2, fun _ => rfl⟩) α
    (fun z => (z : Word (searchBits n μ s a τ)))

/-- **The enlarged scalar family satisfies the access conditions along `toBits`**. -/
theorem hardAccess_scalarTwo (hs : 2 ≤ s) (hm : 0 < m) (hc : c ≠ 0) :
    HardAccess (scalarTwo n s τ hs m hm c hc) (toBits (n := n)) where
  row_const _ _ := rfl
  column_const _ _ := rfl
  table_bit α := AdaptiveHamiltonianLowerBound.Access.bitTable_value_bit
    (enlargeTable (scalarTable n s τ) m) (fun j => toBits j) (fun k => ⟨k, 1, fun _ => rfl⟩) α
    (fun z => (z : Word (scalarBits n s τ)))

variable {θ ε : ℝ}

/-- The enlarged time family satisfies the access conditions along the identity. -/
theorem hardAccess_timeTwo (hs : 32 ≤ s) (hm : 0 < m) (hc : c ≠ 0) :
    HardAccess (timeTwo θ s hs m hm c hc) (fun j => j) :=
  hardAccess_searchTwo _ _ hm hc

/-- The enlarged mixed family satisfies the access conditions along the identity. -/
theorem hardAccess_mixedTwo (hs : 32 ≤ s) (hm : 0 < m) (hc : c ≠ 0) :
    HardAccess (mixedTwo θ ε s hs m hm c hc) (fun j => j) :=
  hardAccess_searchTwo _ _ hm hc

/-- The enlarged precision family satisfies the access conditions along `toBits`. -/
theorem hardAccess_precisionTwo (hs : 32 ≤ s) (hm : 0 < m) (hc : c ≠ 0) :
    HardAccess (precisionTwo θ ε s hs m hm c hc) (toBits (n := precN θ ε)) :=
  hardAccess_scalarTwo _ hm hc

/-- The counterexample family of the denominator paragraph satisfies the access conditions
along `toBits`. -/
theorem hardAccess_denomData (k : ℕ) :
    HardAccess (denomData k) (toBits (n := precN (denomTheta k) (denomEps k))) :=
  hardAccess_scalarTwo _ _ _

end HardAccess

end

end OptimalLowerBounds
