import SparseHamiltonian.NativeMaskedProgram

/-!
# The native sparse data supply every masked-access promise

A fixed computational input works for the original row locator, column
locator and additive value oracle simultaneously. Only slot zero is used to
certify the dummy-control construction. No inverse-locator tables and no
additional promises off the valid locator subspace are needed.
-/
namespace SparseHamiltonian.NativeSparseMaskedAccess

noncomputable section
open ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding
open scoped InnerProduct
set_option maxHeartbeats 800000
set_option maxRecDepth 2000

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s : ℕ}

/-- Flatten only the existing native workspace; no oracle is changed. -/
abbrev Basis (n Z : Type*) := (((n × n) × Z) × Fin 3)

def layout : SparseFlagEmbedding.Space (n × n) Z ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Basis n Z) :=
  RegisterEquivalences.productFlatten ((n × n) × Z) (Fin 3)

/-- Each primitive in a computational basis layout. -/
abbrev flatOracle (D : Data X n Z s) (l : Query) (x : X) :
    EuclideanSpace ℂ (Basis n Z) →L[ℂ] EuclideanSpace ℂ (Basis n Z) :=
  (layout (n := n) (Z := Z)).conjStarAlgEquiv (oracles D l x)

omit [DecidableEq Z] in
/-- Full physical native unitarity is preserved by fixed flattening. -/
theorem flatOracle_unitary (D : Data X n Z s) (l : Query) (x : X) :
    IsUnitary (flatOracle D l x) :=
  (oracles_unitary D l x).transport layout

/-- One fixed original slot, available since the sparse list is nonempty. -/
def zeroSlot (D : Data X n Z s) : Fin s := ⟨0, D.slots_pos⟩

/-- A simultaneous phase-fixed valid input for all three native primitives. -/
def cleanBasis (D : Data X n Z s) : Basis n Z :=
  (((D.slot (zeroSlot D), D.slot (zeroSlot D)), 0), 0)

/-- Unknown basis images are analytical witnesses and never circuit inputs. -/
def image (D : Data X n Z s) : Query → X → Basis n Z
  | .rowLocation, x => (((D.slot (zeroSlot D), D.rowloc x (D.slot (zeroSlot D)) (zeroSlot D)), 0), 0)
  | .columnLocation, x => (((D.colloc x (D.slot (zeroSlot D)) (zeroSlot D), D.slot (zeroSlot D)), 0), 0)
  | .value, x => (((D.slot (zeroSlot D), D.slot (zeroSlot D)),
      D.table x (D.slot (zeroSlot D), D.slot (zeroSlot D))), 0)

omit [AddCommGroup Z] in
/-- Flattened location queries retain every exact basis-image promise. -/
theorem location_single
    (F : X → EuclideanSpace ℂ (n × n) →L[ℂ] EuclideanSpace ℂ (n × n))
    (x : X) (a b : n × n)
    (h : F x (EuclideanSpace.single a 1) = EuclideanSpace.single b 1)
    (z : Z) (f : Fin 3) :
    (layout (n := n) (Z := Z)).conjStarAlgEquiv
      (SparseFlagEmbedding.location F x) (EuclideanSpace.single ((a,z),f) 1) =
        EuclideanSpace.single ((b,z),f) 1 := by
  ext ⟨⟨a',z'⟩,f'⟩
  change F x (WithLp.toLp 2 (fun j =>
    (EuclideanSpace.single ((a,z),f) (1 : ℂ)) ((j,z'),f'))) a' = _
  have hs : WithLp.toLp 2 (fun j : n × n =>
      (EuclideanSpace.single ((a,z),f) (1 : ℂ)) ((j,z'),f')) =
      if z' = z ∧ f' = f then EuclideanSpace.single a 1 else 0 := by
    ext j
    by_cases hz : z' = z <;> by_cases hf : f' = f <;>
      simp [hz, hf, Prod.ext_iff]
  rw [hs]
  by_cases hz : z' = z <;> by_cases hf : f' = f <;>
    simp [hz, hf, h, Prod.ext_iff]

/-- Ordinary additive value access also has a phase-fixed basis transition. -/
theorem value_single (D : Data X n Z s) (x : X) (a : n × n) (z : Z) (f : Fin 3) :
    flatOracle D .value x (EuclideanSpace.single ((a,z),f) 1) =
      EuclideanSpace.single ((a,z + D.table x a),f) 1 := by
  ext ⟨⟨a',z'⟩,f'⟩
  change (EuclideanSpace.single ((a,z),f) (1 : ℂ)) ((a',z' - D.table x a'),f') = _
  by_cases ha : a' = a
  · subst a'
    simp only [PiLp.single_apply, Prod.ext_iff,
      sub_eq_iff_eq_add]
  · simp [ha, Prod.ext_iff]

/-- The required witness is derived for every primitive from the original data. -/
theorem valid (D : Data X n Z s) (l : Query) (x : X) :
    flatOracle D l x (EuclideanSpace.single (cleanBasis D) 1) =
      EuclideanSpace.single (image D l x) 1 := by
  cases l with
  | rowLocation =>
    exact location_single D.rowOracle x _ _
      (D.row_valid x (D.slot (zeroSlot D)) (zeroSlot D)) 0 0
  | columnLocation =>
    exact location_single D.columnOracle x _ _
      (D.column_valid x (D.slot (zeroSlot D)) (zeroSlot D)) 0 0
  | value => simpa only [cleanBasis, image, zero_add] using
      value_single D x (D.slot (zeroSlot D), D.slot (zeroSlot D)) 0 0

variable {ι M : Type*} [Fintype ι]

/-- Every masked native sparse program now has a genuine physical compilation,
with the original three labels and the common clean encoding. -/
theorem compile_eval (D : Data X n Z s)
    (label : M → Query) (active : M → ι → Bool)
    (p : MultiOracleCircuit.Program
      (NativeMaskedProgram.logicalOracle (flatOracle D) label active)) (x : X) :
    (NativeMaskedProgram.compile (flatOracle D) (cleanBasis D) label active p).eval x ∘L
      (NativeMaskedOracle.input (ι := ι) (cleanBasis D)).toContinuousLinearMap =
    (NativeMaskedOracle.input (cleanBasis D)).toContinuousLinearMap ∘L p.eval x :=
  NativeMaskedProgram.compile_eval (flatOracle D) (flatOracle_unitary D)
    (cleanBasis D) (image D) (valid D) label active p x

/-- Exact counts are independent of branch number, masks and locator completion. -/
theorem compile_cost (D : Data X n Z s)
    (label : M → Query) (active : M → ι → Bool)
    (p : MultiOracleCircuit.Program
      (NativeMaskedProgram.logicalOracle (flatOracle D) label active)) (w : Query → ℕ) :
    (NativeMaskedProgram.compile (flatOracle D) (cleanBasis D) label active p).cost w =
      p.cost (fun m => 3 * w (label m)) :=
  NativeMaskedProgram.compile_cost (flatOracle D) (cleanBasis D) label active p w

end
end SparseHamiltonian.NativeSparseMaskedAccess
