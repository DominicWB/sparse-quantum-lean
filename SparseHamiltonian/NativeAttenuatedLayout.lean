import SparseHamiltonian.MultiOracleTransport

/-!
# Computational basis and native promises for the attenuated sparse workspace

Fresh attenuation flags are merely spectators of the native row, column and
value queries. A fixed sum-basis layout therefore inherits the original exact
basis-image promises without strengthening the sparse oracle model.
-/
namespace SparseHamiltonian.NativeAttenuatedLayout

noncomputable section
open ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding
open scoped InnerProduct
set_option maxRecDepth 2000
set_option maxHeartbeats 800000

abbrev OldBasis (n Z : Type*) := NativeSparseMaskedAccess.Basis n Z
abbrev Basis (n Z : Type*) := OldBasis n Z ⊕ (OldBasis n Z ⊕ OldBasis n Z)

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z]
  [AddCommGroup Z] [DecidableEq Z] {s : ℕ}

/-- Decidable equality is inherited componentwise across both sum layers. -/
instance instDecidableEqBasis : DecidableEq (Basis n Z) :=
  @instDecidableEqSum _ _ inferInstance
    (@instDecidableEqSum _ _ inferInstance inferInstance)

/-- Flatten the three fresh-flag sectors and the original sparse registers. -/
def layout : NativeSparseAttenuation.Workspace n Z ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Basis n Z) :=
  (LinearIsometryEquiv.withLpProdCongr 2 NativeSparseMaskedAccess.layout
    ((LinearIsometryEquiv.withLpProdCongr 2 NativeSparseMaskedAccess.layout
      NativeSparseMaskedAccess.layout).trans (RegisterEquivalences.sumFlatten _ _))).trans
    (RegisterEquivalences.sumFlatten _ _)

/-- The known common input lies in the first fresh sector. -/
def cleanBasis (D : Data X n Z s) : Basis n Z := .inl (NativeSparseMaskedAccess.cleanBasis D)

/-- The unknown native image also remains in that first sector. -/
def image (D : Data X n Z s) (l : Query) (x : X) : Basis n Z :=
  .inl (NativeSparseMaskedAccess.image D l x)

/-- Actual spectator-native queries in the fixed computational basis. -/
abbrev oracle (D : Data X n Z s) (l : Query) (x : X) :
    EuclideanSpace ℂ (Basis n Z) →L[ℂ] EuclideanSpace ℂ (Basis n Z) :=
  (layout (n := n) (Z := Z)).conjStarAlgEquiv (NativeSparseAttenuation.oracles D l x)

omit [AddCommGroup Z] in
/-- Flattening a clean fresh sector preserves the original basis state. -/
theorem fresh_single (b : OldBasis n Z) :
    layout (NativeSparseAttenuation.fresh
      (NativeSparseMaskedAccess.layout.symm (EuclideanSpace.single b (1 : ℂ)))) =
      EuclideanSpace.single (.inl b : Basis n Z) (1 : ℂ) := by
  ext c
  rcases c with a | (a | a) <;>
    simp [layout, NativeSparseAttenuation.fresh_apply,
      LinearIsometryEquiv.withLpProdCongr_apply]

omit [AddCommGroup Z] in
/-- Equivalent inverse-layout form of the clean basis identity. -/
theorem layout_symm_single (b : OldBasis n Z) :
    layout.symm (EuclideanSpace.single (.inl b : Basis n Z) (1 : ℂ)) =
      NativeSparseAttenuation.fresh
        (NativeSparseMaskedAccess.layout.symm (EuclideanSpace.single b (1 : ℂ))) := by
  apply layout.injective
  rw [layout.apply_symm_apply, fresh_single]

/-- Native basis witnesses require no additional assumption after attenuation. -/
theorem valid (D : Data X n Z s) (l : Query) (x : X) :
    oracle D l x (EuclideanSpace.single (cleanBasis D) 1) =
      EuclideanSpace.single (image D l x) 1 := by
  have h := NativeSparseMaskedAccess.valid D l x
  have hv : NativeSparseBlockEncoding.oracles D l x
      (NativeSparseMaskedAccess.layout.symm
        (EuclideanSpace.single (NativeSparseMaskedAccess.cleanBasis D) 1)) =
      NativeSparseMaskedAccess.layout.symm
        (EuclideanSpace.single (NativeSparseMaskedAccess.image D l x) 1) := by
    apply NativeSparseMaskedAccess.layout.injective
    exact h
  change layout (NativeSparseAttenuation.spectator (NativeSparseBlockEncoding.oracles D l x)
    (layout.symm (EuclideanSpace.single (.inl (NativeSparseMaskedAccess.cleanBasis D)) 1))) = _
  rw [layout_symm_single]
  have hs := congrArg (fun T : SparseFlagEmbedding.Space (n × n) Z →L[ℂ]
      NativeSparseAttenuation.Workspace n Z =>
        T (NativeSparseMaskedAccess.layout.symm
          (EuclideanSpace.single (NativeSparseMaskedAccess.cleanBasis D) 1)))
      (NativeSparseAttenuation.spectator_fresh (NativeSparseBlockEncoding.oracles D l x))
  change NativeSparseAttenuation.spectator (NativeSparseBlockEncoding.oracles D l x)
      (NativeSparseAttenuation.fresh
        (NativeSparseMaskedAccess.layout.symm
          (EuclideanSpace.single (NativeSparseMaskedAccess.cleanBasis D) 1))) =
      NativeSparseAttenuation.fresh
        (NativeSparseBlockEncoding.oracles D l x
          (NativeSparseMaskedAccess.layout.symm
            (EuclideanSpace.single (NativeSparseMaskedAccess.cleanBasis D) 1))) at hs
  rw [hs, hv, fresh_single]
  rfl

omit [DecidableEq Z] in
/-- The entire flattened native family is unitary. -/
theorem oracle_unitary (D : Data X n Z s) (l : Query) (x : X) : IsUnitary (oracle D l x) :=
  (NativeSparseAttenuation.oracles_unitary D l x).transport layout

/-- No queries are inserted by the public coordinate change. -/
def program (D : Data X n Z s)
    (p : MultiOracleCircuit.Program (NativeSparseAttenuation.oracles D)) :
    MultiOracleCircuit.Program (oracle D) := by
  let q := MultiOracleCircuit.Program.transport
    (H := NativeSparseAttenuation.Workspace n Z) (K := EuclideanSpace ℂ (Basis n Z))
    (O := NativeSparseAttenuation.oracles D) layout p
  with_reducible exact q

omit [DecidableEq Z] in
@[simp] theorem program_count (D : Data X n Z s)
    (p : MultiOracleCircuit.Program (NativeSparseAttenuation.oracles D)) :
    (program D p).count = p.count := MultiOracleCircuit.Program.count_transport _ _

omit [DecidableEq Z] in
@[simp] theorem program_cost (D : Data X n Z s)
    (p : MultiOracleCircuit.Program (NativeSparseAttenuation.oracles D)) (w : Query → ℕ) :
    (program D p).cost w = p.cost w := MultiOracleCircuit.Program.cost_transport _ _ _

/-- The sparse public input is represented in the same common flattened basis. -/
def input (D : Data X n Z s) : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ (Basis n Z) :=
  FlattenedLookupClockBounds.transportBoundary layout (NativeSparseAttenuation.input D).toContinuousLinearMap

theorem input_isometry (D : Data X n Z s) : (input D)† ∘L input D = 1 :=
  FlattenedLookupClockBounds.transportBoundary_isometry _ _
    (NativeSparseAttenuation.input_adjoint_comp D)

/-- Public matrix compression is unchanged by the fixed sparse layout. -/
theorem compression (D : Data X n Z s)
    (p : MultiOracleCircuit.Program (NativeSparseAttenuation.oracles D)) (x : X) :
    (input D)† ∘L (program D p).eval x ∘L input D =
      (NativeSparseAttenuation.input D).toContinuousLinearMap† ∘L p.eval x ∘L
        (NativeSparseAttenuation.input D).toContinuousLinearMap := by
  rw [program, MultiOracleCircuit.Program.eval_transport, input]
  exact FlattenedLookupClockBounds.transportBoundary_compression _ _ _

end
end SparseHamiltonian.NativeAttenuatedLayout
