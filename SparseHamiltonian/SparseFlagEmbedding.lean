import SparseHamiltonian.SparseSlotPreparation

/-!
# Fixed embeddings of preparation flags

The row and column circuits use ordinary amplitude qubits. Fixed isometries
embed those flags in one physical three-flag space, sharing the good flag and
separating the two failures. A fixed clean-value embedding identifies their
complete outputs with the sparse-slot states.
-/

namespace SparseHamiltonian.SparseFlagEmbedding

noncomputable section
open ContinuousLinearMap ComplexAmplitudeRotation
open scoped BigOperators InnerProduct

/-- Shared good and separate row/column failure coordinates. -/
abbrev Qutrit := EuclideanSpace ℂ (Fin 3)

/-- Row flags map false to zero and true to one. -/
def rowFlag : Qubit →ₗᵢ[ℂ] Qutrit where
  toLinearMap :=
    { toFun := fun v => WithLp.toLp 2 (fun f =>
        if f = 0 then v false else if f = 1 then v true else 0)
      map_add' := by intro v w; ext f; fin_cases f <;> simp
      map_smul' := by intro z v; ext f; fin_cases f <;> simp }
  norm_map' := by
    intro v
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_succ, add_comm]

/-- Column flags map false to zero and true to two. -/
def columnFlag : Qubit →ₗᵢ[ℂ] Qutrit where
  toLinearMap :=
    { toFun := fun v => WithLp.toLp 2 (fun f =>
        if f = 0 then v false else if f = 2 then v true else 0)
      map_add' := by intro v w; ext f; fin_cases f <;> simp
      map_smul' := by intro z v; ext f; fin_cases f <;> simp }
  norm_map' := by
    intro v
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_succ, add_comm]

@[simp] theorem rowFlag_apply (v : Qubit) (f : Fin 3) :
    rowFlag v f = if f = 0 then v false else if f = 1 then v true else 0 := rfl

@[simp] theorem columnFlag_apply (v : Qubit) (f : Fin 3) :
    columnFlag v f = if f = 0 then v false else if f = 2 then v true else 0 := rfl

/-- Both fixed embeddings agree on the clean good flag. -/
theorem flags_clean (z : ℂ) :
    rowFlag (LookupAmplitudePreparation.cleanQubit z) =
      columnFlag (LookupAmplitudePreparation.cleanQubit z) := by
  ext f
  fin_cases f <;> simp

variable {X A Z : Type*} [Fintype A] [Fintype Z]

/-- Common physical layout: address, value, and the three-valued flag. -/
abbrev Space (A Z : Type*) := PiLp 2 (fun _ : A × Z => Qutrit)

/-- Apply one fixed flag isometry independently of all other registers. -/
def flagEmbedding (E : Qubit →ₗᵢ[ℂ] Qutrit) :
    LookupAmplitudePreparation.Space A Z →ₗᵢ[ℂ] Space A Z where
  toLinearMap :=
    { toFun := fun v => WithLp.toLp 2 (fun az => E (v az))
      map_add' := by intro v w; apply PiLp.ext; intro az; exact E.map_add _ _
      map_smul' := by intro z v; apply PiLp.ext; intro az; exact E.map_smul z _ }
  norm_map' := by
    intro v
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [PiLp.norm_sq_eq_of_L2, LinearMap.coe_mk, AddHom.coe_mk]
    apply Finset.sum_congr rfl
    intro az _
    calc
      _ = ‖E (v az)‖ ^ 2 := (PiLp.norm_sq_eq_of_L2 _ _).symm
      _ = ‖v az‖ ^ 2 := congrArg (fun r : ℝ => r ^ 2) (E.norm_map (v az))
      _ = _ := PiLp.norm_sq_eq_of_L2 _ _

@[simp] theorem flagEmbedding_apply (E : Qubit →ₗᵢ[ℂ] Qutrit)
    (v : LookupAmplitudePreparation.Space A Z) (a : A) (z : Z) :
    flagEmbedding E v (a,z) = E (v (a,z)) := rfl

/-- Fixed row flag encoding. -/
def rowEmbedding : LookupAmplitudePreparation.Space A Z →ₗᵢ[ℂ] Space A Z :=
  flagEmbedding rowFlag

/-- Fixed column flag encoding. -/
def columnEmbedding : LookupAmplitudePreparation.Space A Z →ₗᵢ[ℂ] Space A Z :=
  flagEmbedding columnFlag

@[simp] theorem rowEmbedding_apply (v : LookupAmplitudePreparation.Space A Z)
    (a : A) (z : Z) (f : Fin 3) :
    rowEmbedding v (a,z) f = if f = 0 then v (a,z) false
      else if f = 1 then v (a,z) true else 0 := rfl

@[simp] theorem columnEmbedding_apply (v : LookupAmplitudePreparation.Space A Z)
    (a : A) (z : Z) (f : Fin 3) :
    columnEmbedding v (a,z) f = if f = 0 then v (a,z) false
      else if f = 2 then v (a,z) true else 0 := rfl

/-- Fixed permutation exposing the value and three-valued flag as spectators. -/
def spectatorBasis : ((A × Z) × Fin 3) ≃ ((Z × Fin 3) × A) where
  toFun p := ((p.1.2, p.2), p.1.1)
  invFun p := ((p.2, p.1.1), p.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Fixed physical layout for extending native location oracles. -/
def spectatorLayout : Space A Z ≃ₗᵢ[ℂ]
    PiLp 2 (fun _ : Z × Fin 3 => EuclideanSpace ℂ A) :=
  (RegisterEquivalences.productFlatten (A × Z) (Fin 3)).trans
    ((LookupOracle.permutationUnitary (spectatorBasis (A := A) (Z := Z))).trans
      (RegisterEquivalences.productFlatten (Z × Fin 3) A).symm)

/-- The actual native oracle with unchanged value and three-valued flag registers. -/
def location (F : X → EuclideanSpace ℂ A →L[ℂ] EuclideanSpace ℂ A) (x : X) :
    Space A Z →L[ℂ] Space A Z :=
  (spectatorLayout (A := A) (Z := Z)).symm.conjStarAlgEquiv
    (WeightedClock.diagonal (fun _ : Z × Fin 3 => F x))

@[simp] theorem location_apply
    (F : X → EuclideanSpace ℂ A →L[ℂ] EuclideanSpace ℂ A) (x : X)
    (v : Space A Z) (a : A) (z : Z) (f : Fin 3) :
    location F x v (a,z) f = F x (WithLp.toLp 2 (fun a' => v (a',z) f)) a := rfl

/-- The common-space native call is unitary on its full physical space. -/
theorem location_unitary
    (F : X → EuclideanSpace ℂ A →L[ℂ] EuclideanSpace ℂ A)
    (hF : ∀ x, OracleCircuit.IsUnitary (F x)) (x : X) :
    OracleCircuit.IsUnitary (location (Z := Z) F x) := by
  have hd : OracleCircuit.IsUnitary (WeightedClock.diagonal (fun _ : Z × Fin 3 => F x)) := by
    constructor
    · exact WeightedClock.diagonal_isometry _ (fun _ => (hF x).1)
    · change WeightedClock.diagonal (fun _ : Z × Fin 3 => F x) ∘L
        (WeightedClock.diagonal (fun _ : Z × Fin 3 => F x))† = 1
      rw [WeightedClock.diagonal_adjoint, WeightedClock.diagonal_comp]
      have hh := (hF x).2
      change F x ∘L (F x)† = 1 at hh
      simp only [hh, WeightedClock.diagonal_one]
  exact hd.transport (spectatorLayout (A := A) (Z := Z)).symm

/-- Row flag encoding preserves the same native query, label, and direction. -/
theorem location_rowEmbedding
    (F : X → EuclideanSpace ℂ A →L[ℂ] EuclideanSpace ℂ A) (x : X) :
    location (Z := Z) F x ∘L rowEmbedding.toContinuousLinearMap =
      rowEmbedding.toContinuousLinearMap ∘L SparseSlotPreparation.location F x := by
  ext v az f
  rcases az with ⟨a,z⟩
  fin_cases f <;> simp [SparseSlotPreparation.location_apply]
  change F x 0 a = 0
  simp

/-- Column flag encoding likewise preserves the actual native call. -/
theorem location_columnEmbedding
    (F : X → EuclideanSpace ℂ A →L[ℂ] EuclideanSpace ℂ A) (x : X) :
    location (Z := Z) F x ∘L columnEmbedding.toContinuousLinearMap =
      columnEmbedding.toContinuousLinearMap ∘L SparseSlotPreparation.location F x := by
  ext v az f
  rcases az with ⟨a,z⟩
  fin_cases f <;> simp [SparseSlotPreparation.location_apply]
  change F x 0 a = 0
  simp

variable [AddCommGroup Z]

/-- The value call on the common space is the ordinary additive lookup. -/
def value (table : X → A → Z) (x : X) : Space A Z →L[ℂ] Space A Z :=
  LookupControlledGate.oracle (K := Qutrit) table x

/-- The same table oracle intertwines the row flag encoding exactly. -/
theorem value_rowEmbedding (table : X → A → Z) (x : X) :
    value table x ∘L (rowEmbedding (A := A) (Z := Z)).toContinuousLinearMap =
      rowEmbedding.toContinuousLinearMap ∘L LookupControlledGate.oracle (K := Qubit) table x := by
  ext v az f
  rcases az with ⟨a,z⟩
  rfl

/-- The same table oracle intertwines the column flag encoding exactly. -/
theorem value_columnEmbedding (table : X → A → Z) (x : X) :
    value table x ∘L (columnEmbedding (A := A) (Z := Z)).toContinuousLinearMap =
      columnEmbedding.toContinuousLinearMap ∘L LookupControlledGate.oracle (K := Qubit) table x := by
  ext v az f
  rcases az with ⟨a,z⟩
  rfl

/-- Ordinary additive lookup remains unitary for all three flag states. -/
theorem value_unitary (table : X → A → Z) (x : X) :
    OracleCircuit.IsUnitary (value table x) := LookupControlledGate.oracle_unitary table x

variable [DecidableEq Z]

/-- Flattening is reversed and one fixed clean value register is appended. -/
def clean : EuclideanSpace ℂ (A × Fin 3) →ₗᵢ[ℂ] Space A Z :=
  (CleanValueEmbedding.embedding (I := A) (K := Qutrit) (0 : Z)).comp
    (RegisterEquivalences.productFlatten A (Fin 3)).symm.toLinearIsometry

@[simp] theorem clean_apply (v : EuclideanSpace ℂ (A × Fin 3))
    (a : A) (z : Z) (f : Fin 3) :
    clean (Z := Z) v (a,z) f = if z = 0 then v (a,f) else 0 := by
  by_cases hz : z = 0 <;> simp [clean, hz]

/-- The common clean embedding is a genuine isometry. -/
theorem clean_adjoint_comp :
    (clean (A := A) (Z := Z)).toContinuousLinearMap† ∘L clean.toContinuousLinearMap = 1 :=
  LinearIsometry.adjoint_comp_self _

/-- Row and column flag encodings agree on the whole fixed initial subspace. -/
theorem embeddings_input (v : EuclideanSpace ℂ A) :
    rowEmbedding (LookupAmplitudePreparation.input (Z := Z) v) =
      columnEmbedding (LookupAmplitudePreparation.input (Z := Z) v) := by
  ext az f
  rcases az with ⟨a,z⟩
  fin_cases f <;> by_cases hz : z = 0 <;> simp [hz]

section SparseStates

variable {n : Type*} [Fintype n] [DecidableEq n] {s : ℕ}

/-- The complete counted row preparation is exactly the sparse-slot row state,
including every retained zero slot and its local failure amplitude. -/
theorem row_preparation
    (H : X → Matrix n n ℂ) (a : ℝ)
    (F : X → EuclideanSpace ℂ (n × n) →L[ℂ] EuclideanSpace ℂ (n × n))
    (decode : (n × n) → Z → ℂ) (hdecode : ∀ p z, ‖decode p z‖ ≤ 1)
    (table : X → (n × n) → Z) (slot : Fin s ↪ n) (hs : 0 < s)
    (loc : X → n → Fin s → n) (hinj : ∀ x i, Function.Injective (loc x i))
    (hvalid : ∀ x i k, F x (EuclideanSpace.single (i, slot k) 1) =
      EuclideanSpace.single (i, loc x i k) 1)
    (hentry : ∀ x i j, decode (i,j) (table x (i,j)) =
      SparseEntryAmplitudes.rowAmplitude a (H x i j)) (x : X) :
    (rowEmbedding (Z := Z)).toContinuousLinearMap ∘L
        SparseSlotPreparation.preparation F decode hdecode table
          (UniformSlotPreparation.embedding slot hs) x =
      clean.toContinuousLinearMap ∘L SparseSlotStates.row (H x) a (loc x) := by
  ext v az f
  rcases az with ⟨⟨i,j⟩,z⟩
  simp only [comp_apply, LinearIsometry.coe_toContinuousLinearMap, rowEmbedding_apply,
    SparseSlotPreparation.preparation_apply, clean_apply, SparseSlotStates.row_apply]
  simp_rw [SparseSlotPreparation.native_uniform_row F slot hs loc hinj hvalid, hentry]
  fin_cases f <;> by_cases hz : z = 0 <;>
    by_cases hsel : j ∈ Finset.univ.image (loc x i) <;>
    simp [hz, hsel, SparseSlotStates.selected, SparseSlotStates.rowEntry,
      UniformSlotPreparation.weight, SparseSlotStates.weight, mul_left_comm, mul_comm, mul_assoc]

/-- The complete counted column preparation matches the same common-space
slot construction, with its failure amplitude on flag two. -/
theorem column_preparation
    (H : X → Matrix n n ℂ) (a : ℝ)
    (F : X → EuclideanSpace ℂ (n × n) →L[ℂ] EuclideanSpace ℂ (n × n))
    (decode : (n × n) → Z → ℂ) (hdecode : ∀ p z, ‖decode p z‖ ≤ 1)
    (table : X → (n × n) → Z) (slot : Fin s ↪ n) (hs : 0 < s)
    (loc : X → n → Fin s → n) (hinj : ∀ x j, Function.Injective (loc x j))
    (hvalid : ∀ x j k, F x (EuclideanSpace.single (j, slot k) 1) =
      EuclideanSpace.single (loc x j k,j) 1)
    (hentry : ∀ x i j, decode (i,j) (table x (i,j)) =
      SparseEntryAmplitudes.columnAmplitude a (H x i j)) (x : X) :
    (columnEmbedding (Z := Z)).toContinuousLinearMap ∘L
        SparseSlotPreparation.preparation F decode hdecode table
          (UniformSlotPreparation.embedding slot hs) x =
      clean.toContinuousLinearMap ∘L SparseSlotStates.column (H x) a (loc x) := by
  ext v az f
  rcases az with ⟨⟨i,j⟩,z⟩
  simp only [comp_apply, LinearIsometry.coe_toContinuousLinearMap, columnEmbedding_apply,
    SparseSlotPreparation.preparation_apply, clean_apply, SparseSlotStates.column_apply]
  simp_rw [SparseSlotPreparation.native_uniform_column F slot hs loc hinj hvalid, hentry]
  fin_cases f <;> by_cases hz : z = 0 <;>
    by_cases hsel : i ∈ Finset.univ.image (loc x j) <;>
    simp [hz, hsel, SparseSlotStates.selected, SparseSlotStates.columnEntry,
      UniformSlotPreparation.weight, SparseSlotStates.weight, mul_left_comm, mul_comm, mul_assoc]

end SparseStates

end
end SparseHamiltonian.SparseFlagEmbedding
