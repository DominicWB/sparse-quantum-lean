import SparseHamiltonian.FixedNativeCayleyQuery

/-!
# A common native workspace for the exact oriented sparse Cayley action

The orientation is a spectator of the native primitives.  Two fixed masks
apply the row and column locators on their respective orientation sectors;
they do not assume an oracle selected coherently by its label.
-/
namespace SparseHamiltonian.OrientedNativeLayout

noncomputable section
open ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding SparseEdgeMoments
open scoped BigOperators InnerProduct
set_option maxHeartbeats 1000000
set_option maxRecDepth 3000

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z]
  [AddCommGroup Z] [DecidableEq Z] {s : ℕ}

abbrev Space (n Z : Type*) [Fintype n] [Fintype Z] :=
  NativeMaskedOracle.Logical Bool (NativeSparseMaskedAccess.Basis n Z)

/-- The value and flag registers are initialized in fixed zero basis states. -/
def edgeClean : EdgeSpace n →ₗᵢ[ℂ]
    EuclideanSpace ℂ (NativeSparseMaskedAccess.Basis n Z) :=
  (CleanValueEmbedding.embedding (I := (n × n) × Z) (K := ℂ) (0 : Fin 3)).comp
    (CleanValueEmbedding.embedding (I := n × n) (K := ℂ) (0 : Z))

omit [DecidableEq n] in
@[simp] theorem edgeClean_apply (v : EdgeSpace n) (e : n × n) (z : Z) (f : Fin 3) :
    edgeClean v ((e,z),f) = if z = 0 ∧ f = 0 then v e else 0 := by
  by_cases hz : z = 0 <;> by_cases hf : f = 0 <;>
    simp [edgeClean, hz, hf]

/-- Both orientations use the same clean value and flag encoding. -/
def clean : OrientedSpace n →ₗᵢ[ℂ] Space n Z where
  toLinearMap :=
    { toFun := fun v => WithLp.toLp 2 (fun b : Bool =>
        edgeClean (if b then FixedLocatorConjugation.rightPart v
          else FixedLocatorConjugation.leftPart v))
      map_add' := by
        intro v w
        ext b a
        rcases a with ⟨⟨e,z⟩,f⟩
        cases b <;> by_cases h : z = 0 ∧ f = 0 <;>
          simp [FixedLocatorConjugation.leftPart,
            FixedLocatorConjugation.rightPart, edgeClean_apply, h]
      map_smul' := by
        intro c v
        ext b a
        rcases a with ⟨⟨e,z⟩,f⟩
        cases b <;> by_cases h : z = 0 ∧ f = 0 <;>
          simp [FixedLocatorConjugation.leftPart,
            FixedLocatorConjugation.rightPart, edgeClean_apply, h] }
  norm_map' := by
    intro v
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [PiLp.norm_sq_eq_of_L2]
    simp only [Fintype.sum_bool]
    simp [FixedLocatorConjugation.leftPart, FixedLocatorConjugation.rightPart,
      PiLp.norm_sq_eq_of_L2, Fintype.sum_sum_type, add_comm]

omit [DecidableEq n] in
@[simp] theorem clean_false (v : OrientedSpace n) :
    clean (Z := Z) v false = edgeClean (FixedLocatorConjugation.leftPart v) := rfl

omit [DecidableEq n] in
@[simp] theorem clean_true (v : OrientedSpace n) :
    clean (Z := Z) v true = edgeClean (FixedLocatorConjugation.rightPart v) := rfl

omit [DecidableEq n] in
@[simp] theorem clean_apply (v : OrientedSpace n) (b : Bool)
    (e : n × n) (z : Z) (f : Fin 3) :
    clean v b ((e,z),f) =
      if z = 0 ∧ f = 0 then (if b then v (.inr e) else v (.inl e)) else 0 := by
  cases b <;> simp [FixedLocatorConjugation.leftPart,
    FixedLocatorConjugation.rightPart]

/-- Move the orientation from an outer spectator to the qubit at each address. -/
def edgeLayout : Space n Z ≃ₗᵢ[ℂ]
    PiLp 2 (fun _ : NativeSparseMaskedAccess.Basis n Z => ExactEdgeCayley.Qubit) :=
  (RegisterEquivalences.productFlatten Bool (NativeSparseMaskedAccess.Basis n Z)).trans
    ((LookupOracle.permutationUnitary
      (Equiv.prodComm Bool (NativeSparseMaskedAccess.Basis n Z))).trans
        (RegisterEquivalences.productFlatten (NativeSparseMaskedAccess.Basis n Z) Bool).symm)

omit [DecidableEq n] [AddCommGroup Z] [DecidableEq Z] in
@[simp] theorem edgeLayout_apply (v : Space n Z)
    (a : NativeSparseMaskedAccess.Basis n Z) (b : Bool) :
    edgeLayout v a b = v b a := rfl

omit [DecidableEq n] [AddCommGroup Z] [DecidableEq Z] in
@[simp] theorem edgeLayout_symm_apply
    (v : PiLp 2 (fun _ : NativeSparseMaskedAccess.Basis n Z => ExactEdgeCayley.Qubit))
    (b : Bool) (a : NativeSparseMaskedAccess.Basis n Z) :
    edgeLayout.symm v b a = v a b := rfl

/-- Masks depend only on the public orientation bit, never on the sparse input. -/
def masks : Query → Bool → Bool
  | .rowLocation, b => !b
  | .columnLocation, b => b
  | .value, _ => true

abbrev logicalOracle (D : Data X n Z s) : Query → X → Space n Z →L[ℂ] Space n Z :=
  NativeMaskedProgram.logicalOracle (NativeSparseMaskedAccess.flatOracle D) id masks

omit [DecidableEq Z] in
/-- These masks preserve unitarity of each full native oracle extension. -/
theorem logicalOracle_unitary (D : Data X n Z s) (l : Query) (x : X) :
    IsUnitary (logicalOracle D l x) :=
  MaskedProgram.masked_unitary (masks l) _
    (NativeSparseMaskedAccess.flatOracle_unitary D l x)

omit [DecidableEq Z] in
@[simp] theorem logical_value_apply (D : Data X n Z s) (x : X) (v : Space n Z)
    (b : Bool) (e : n × n) (z : Z) (f : Fin 3) :
    logicalOracle D .value x v b ((e,z),f) = v b ((e,z - D.table x e),f) := rfl

omit [DecidableEq n] in
/-- An arbitrary full address-space unitary acts coherently under the clean
encoding.  This identity does not require any valid-slot restriction. -/
theorem location_edgeClean
    (F : X → EdgeSpace n →L[ℂ] EdgeSpace n) (x : X) (v : EdgeSpace n) :
    (NativeSparseMaskedAccess.layout (n := n) (Z := Z)).conjStarAlgEquiv
      (SparseFlagEmbedding.location F x) (edgeClean v) = edgeClean (F x v) := by
  ext a
  rcases a with ⟨⟨e,z⟩,f⟩
  change F x (WithLp.toLp 2 (fun j => edgeClean v ((j,z),f))) e = _
  have hs : WithLp.toLp 2 (fun j : n × n => edgeClean v ((j,z),f)) =
      if z = 0 ∧ f = 0 then v else 0 := by
    ext j
    by_cases h : z = 0 ∧ f = 0 <;> simp [h]
  rw [hs, edgeClean_apply]
  by_cases h : z = 0 ∧ f = 0 <;> simp [h]

@[simp] theorem row_edgeClean (D : Data X n Z s) (x : X) (v : EdgeSpace n) :
    NativeSparseMaskedAccess.flatOracle D .rowLocation x (edgeClean v) =
      edgeClean (D.rowOracle x v) :=
  location_edgeClean D.rowOracle x v

@[simp] theorem column_edgeClean (D : Data X n Z s) (x : X) (v : EdgeSpace n) :
    NativeSparseMaskedAccess.flatOracle D .columnLocation x (edgeClean v) =
      edgeClean (D.columnOracle x v) :=
  location_edgeClean D.columnOracle x v

/-- The two locator labels are queried in a fixed chronological order. -/
def locatorProgram (D : Data X n Z s) : MultiOracleCircuit.Program (logicalOracle D) :=
  .seq (.query .columnLocation) (.query .rowLocation)

omit [DecidableEq Z] in
@[simp] theorem locatorProgram_count (D : Data X n Z s) :
    (locatorProgram D).count = 2 := rfl

omit [DecidableEq Z] in
@[simp] theorem locatorProgram_cost (D : Data X n Z s) (w : Query → ℕ) :
    (locatorProgram D).cost w = w .rowLocation + w .columnLocation := by
  change w .columnLocation + w .rowLocation = _
  omega

/-- Exact full-output semantics for the locator circuit. -/
theorem locatorProgram_intertwines (D : Data X n Z s) (x : X) :
    (locatorProgram D).eval x ∘L clean.toContinuousLinearMap =
      clean.toContinuousLinearMap ∘L FixedLocatorConjugation.locator D x := by
  apply ContinuousLinearMap.ext
  intro v
  change (locatorProgram D).eval x (clean v) =
    clean (FixedLocatorConjugation.locator D x v)
  apply PiLp.ext
  intro b
  cases b with
  | false =>
      change NativeSparseMaskedAccess.flatOracle D .rowLocation x
          (edgeClean (FixedLocatorConjugation.leftPart v)) =
        edgeClean (FixedLocatorConjugation.leftPart
          (FixedLocatorConjugation.locator D x v))
      rw [FixedLocatorConjugation.locator, FixedLocatorConjugation.leftPart_block]
      exact row_edgeClean D x (FixedLocatorConjugation.leftPart v)
  | true =>
      change NativeSparseMaskedAccess.flatOracle D .columnLocation x
          (edgeClean (FixedLocatorConjugation.rightPart v)) =
        edgeClean (FixedLocatorConjugation.rightPart
          (FixedLocatorConjugation.locator D x v))
      rw [FixedLocatorConjugation.locator, FixedLocatorConjugation.rightPart_block]
      exact column_edgeClean D x (FixedLocatorConjugation.rightPart v)

end
end SparseHamiltonian.OrientedNativeLayout
