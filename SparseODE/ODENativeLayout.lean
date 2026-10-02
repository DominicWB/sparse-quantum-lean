import SparseODE.ODETaggedValueOracle

/-!
# One native workspace for tagged ODE locators and value gates

The query label vocabulary remains the original row locator, column locator,
and entry-value oracle. A common fixed encoding puts the orientation, tag and
first value word in spectator registers and initializes only the native flag.
All logical masks below will subsequently be compiled using the verified
dummy-input construction for uncontrolled native queries.

-/

namespace SparseHamiltonian.ODENativeLayout

noncomputable section
open ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding
open scoped BigOperators InnerProduct
set_option maxHeartbeats 1000000
set_option maxRecDepth 3000

/-- The branch records `(orientation, tag)` and the first value word. -/
abbrev Branch (Z : Type*) := (Bool × Bool) × Z

abbrev Space (n Z : Type*) [Fintype n] [Fintype Z] :=
  NativeMaskedOracle.Logical (Branch Z) (NativeSparseMaskedAccess.Basis n Z)

/-- Fixed masks route each named locator to its two appropriate sectors.
The entry-value primitive acts in every branch. -/
def masks {Z : Type*} : Query → Branch Z → Bool
  | .rowLocation, b => b.1.1 == b.1.2
  | .columnLocation, b => !(b.1.1 == b.1.2)
  | .value, _ => true

@[simp] theorem masks_row {Z : Type*} (o a : Bool) (u : Z) :
    masks .rowLocation ((o, a), u) = (o == a) := rfl

@[simp] theorem masks_column {Z : Type*} (o a : Bool) (u : Z) :
    masks .columnLocation ((o, a), u) = !(o == a) := rfl

@[simp] theorem masks_value {Z : Type*} (b : Branch Z) : masks .value b = true := rfl

variable {X n Z : Type*} [Fintype n] [DecidableEq n]
  [Fintype Z] [AddCommGroup Z] [DecidableEq Z] {s : ℕ}

abbrev logicalOracle (D : Data X n Z s) : Query → X → Space n Z →L[ℂ] Space n Z :=
  NativeMaskedProgram.logicalOracle (NativeSparseMaskedAccess.flatOracle D) id masks

omit [DecidableEq Z] in
theorem logicalOracle_unitary (D : Data X n Z s) (q : Query) (x : X) :
    IsUnitary (logicalOracle D q x) :=
  MaskedProgram.masked_unitary (masks q) (NativeSparseMaskedAccess.flatOracle D q x)
    (NativeSparseMaskedAccess.flatOracle_unitary D q x)

omit [DecidableEq Z] in
/-- Coordinate form of the unchanged original value oracle on this workspace. -/
@[simp] theorem logical_value_apply (D : Data X n Z s) (x : X)
    (v : Space n Z) (b : Branch Z) (e : n × n) (z : Z) (f : Fin 3) :
    logicalOracle D .value x v b ((e, z), f) =
      v b ((e, z - D.table x e), f) := rfl

/-- Flatten the three Hilbert registers of the four-query value implementation. -/
def valueFlatten : ODETaggedValueOracle.Space n Z ≃ₗᵢ[ℂ]
    EuclideanSpace ℂ (((n × n) × Z) × ((Bool × Z) × Bool)) :=
  (LinearIsometryEquiv.piLpCongrRight 2 (fun _ : (n × n) × Z =>
    RegisterEquivalences.productFlatten (Bool × Z) Bool)).trans
      (RegisterEquivalences.productFlatten ((n × n) × Z) ((Bool × Z) × Bool))

/-- Rearrangement into spectator branch followed by native address and word. -/
def valueBasis : (((n × n) × Z) × ((Bool × Z) × Bool)) ≃
    (Branch Z × ((n × n) × Z)) where
  toFun w := (((w.2.2, w.2.1.1), w.2.1.2), w.1)
  invFun w := (w.2, ((w.1.1.2, w.1.2), w.1.1.1))
  left_inv := by intro w; rcases w with ⟨ez, ⟨⟨a, u⟩, o⟩⟩; rfl
  right_inv := by intro w; rcases w with ⟨⟨⟨o, a⟩, u⟩, ez⟩; rfl

/-- The value implementation embeds by an exact register permutation and
one clean three-state flag, independently of every unknown matrix entry. -/
def valueEmbedding : ODETaggedValueOracle.Space n Z →ₗᵢ[ℂ] Space n Z :=
  (RegisterEquivalences.workspaceCurry (Branch Z) ((n × n) × Z) (Fin 3)).toLinearIsometry.comp
    ((CleanValueEmbedding.embedding (I := Branch Z × ((n × n) × Z))
      (K := ℂ) (0 : Fin 3)).comp
      ((LookupOracle.permutationUnitary (valueBasis (n := n) (Z := Z))).toLinearIsometry.comp
        (valueFlatten (n := n) (Z := Z)).toLinearIsometry))

omit [DecidableEq n] [AddCommGroup Z] [DecidableEq Z] in
@[simp] theorem valueEmbedding_apply (v : ODETaggedValueOracle.Space n Z)
    (o a : Bool) (u : Z) (e : n × n) (z : Z) (f : Fin 3) :
    valueEmbedding v ((o, a), u) ((e, z), f) =
      if f = 0 then v (e, z) (a, u) o else 0 := rfl

omit [DecidableEq n] [AddCommGroup Z] [DecidableEq Z] in
theorem valueEmbedding_isometry :
    (valueEmbedding (n := n) (Z := Z)).toContinuousLinearMap† ∘L
      (valueEmbedding (n := n) (Z := Z)).toContinuousLinearMap = 1 :=
  LinearIsometry.adjoint_comp_self _

omit [DecidableEq Z] in
/-- A value call in the common workspace is precisely the original value
primitive used by the four-query tagged gate, under the fixed embedding. -/
theorem value_intertwines (D : Data X n Z s) (x : X) :
    logicalOracle D .value x ∘L
        (valueEmbedding (n := n) (Z := Z)).toContinuousLinearMap =
      valueEmbedding.toContinuousLinearMap ∘L ODETaggedValueOracle.oracle D x := by
  apply ContinuousLinearMap.ext
  intro v
  apply PiLp.ext
  intro b
  apply PiLp.ext
  intro q
  rcases b with ⟨⟨o, a⟩, u⟩
  rcases q with ⟨⟨e, z⟩, f⟩
  change logicalOracle D .value x (valueEmbedding v) ((o, a), u) ((e, z), f) =
    valueEmbedding (ODETaggedValueOracle.oracle D x v) ((o, a), u) ((e, z), f)
  rw [logical_value_apply, valueEmbedding_apply, valueEmbedding_apply]
  rfl

/-- Both value words and the native flag are restored in one fixed encoding. -/
def clean : ODETaggedMoments.PrivateSpace n →ₗᵢ[ℂ] Space n Z :=
  (valueEmbedding (n := n) (Z := Z)).comp
    (ODETaggedValueOracle.clean (n := n) (Z := Z))

omit [DecidableEq n] in
@[simp] theorem clean_apply (v : ODETaggedMoments.PrivateSpace n)
    (o a : Bool) (u : Z) (e : n × n) (z : Z) (f : Fin 3) :
    clean v ((o, a), u) ((e, z), f) =
      if u = 0 ∧ z = 0 ∧ f = 0 then v o (ODETaggedValueOracle.address a e) else 0 := by
  change valueEmbedding (ODETaggedValueOracle.clean v) ((o, a), u) ((e, z), f) = _
  rw [valueEmbedding_apply]
  change (if f = 0 then
      (if z = 0 then if u = 0 then ODETaggedCayley.regroup v
        (ODETaggedValueOracle.address a e) else 0 else 0) o else 0) = _
  by_cases hu : u = 0 <;> by_cases hz : z = 0 <;> by_cases hf : f = 0 <;>
    simp [hu, hz, hf]

/-- Restriction to either support tag preserves the physical edge order. -/
def tagPart (a : Bool) (v : ODETaggedSupport.TaggedSpace n) : SparseEdgeMoments.EdgeSpace n :=
  WithLp.toLp 2 (fun e => v (ODETaggedValueOracle.address a e))

omit [DecidableEq n] in
/-- A locator sees the existing clean edge encoding in the zero-scratch
branch and the zero vector in every other scratch branch. -/
theorem clean_branch (v : ODETaggedMoments.PrivateSpace n) (o a : Bool) (u : Z) :
    clean (Z := Z) v ((o, a), u) =
      if u = 0 then OrientedNativeLayout.edgeClean (tagPart a (v o)) else 0 := by
  apply PiLp.ext
  intro q
  rcases q with ⟨⟨e, z⟩, f⟩
  by_cases hu : u = 0 <;> by_cases hz : z = 0 <;> by_cases hf : f = 0 <;>
    simp [clean_apply, OrientedNativeLayout.edgeClean_apply, tagPart, hu, hz, hf]

omit [DecidableEq n] in
/-- Equivalent branch formula in the established sum-sector projections. -/
theorem clean_branch_parts (v : ODETaggedMoments.PrivateSpace n) (o a : Bool) (u : Z) :
    clean (Z := Z) v ((o, a), u) =
      if u = 0 then OrientedNativeLayout.edgeClean
        (if a then FixedLocatorConjugation.rightPart (v o)
          else FixedLocatorConjugation.leftPart (v o)) else 0 := by
  rw [clean_branch]
  have hPart : tagPart a (v o) =
      if a then FixedLocatorConjugation.rightPart (v o)
        else FixedLocatorConjugation.leftPart (v o) := by
    cases a <;> rfl
  rw [hPart]

omit [DecidableEq n] in
theorem clean_isometry :
    (clean (n := n) (Z := Z)).toContinuousLinearMap† ∘L
      (clean (n := n) (Z := Z)).toContinuousLinearMap = 1 :=
  LinearIsometry.adjoint_comp_self _

end
end SparseHamiltonian.ODENativeLayout
