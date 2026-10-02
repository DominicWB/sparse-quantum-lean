import SparseHamiltonian.SparseSlotStates

/-!
# Counted native-location sparse state preparation

A native in-place location oracle is extended only by untouched value and flag
registers. Its promised basis action is sufficient on a fixed uniform slot
input. The following value compute/rotate/uncompute circuit makes precisely two
value calls and cleans that register coherently. All initial maps and layout
changes are independent of the unknown input instance.
-/

namespace SparseHamiltonian.SparseSlotPreparation

noncomputable section
open ContinuousLinearMap OracleCircuit ComplexAmplitudeRotation
open scoped BigOperators InnerProduct

variable {X A Z : Type*} [Fintype A] [Fintype Z]

/-- Fixed layout change exposing the value and flag as spectators. -/
def spectatorBasis : ((A × Z) × Bool) ≃ ((Z × Bool) × A) where
  toFun p := ((p.1.2, p.2), p.1.1)
  invFun p := ((p.2, p.1.1), p.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The physical lookup layout and the location-oracle spectator layout are
related by a single fixed Hilbert equivalence. -/
def spectatorLayout : LookupAmplitudePreparation.Space A Z ≃ₗᵢ[ℂ]
    PiLp 2 (fun _ : Z × Bool => EuclideanSpace ℂ A) :=
  (RegisterEquivalences.productFlatten (A × Z) Bool).trans
    ((LookupOracle.permutationUnitary (spectatorBasis (A := A) (Z := Z))).trans
      (RegisterEquivalences.productFlatten (Z × Bool) A).symm)

@[simp] theorem spectatorLayout_apply (v : LookupAmplitudePreparation.Space A Z)
    (z : Z) (b : Bool) (a : A) : spectatorLayout v (z, b) a = v (a, z) b := rfl

@[simp] theorem spectatorLayout_symm_apply
    (v : PiLp 2 (fun _ : Z × Bool => EuclideanSpace ℂ A))
    (z : Z) (b : Bool) (a : A) : spectatorLayout.symm v (a, z) b = v (z, b) a := rfl

/-- One native location call, with the two other registers untouched. -/
def location (F : X → EuclideanSpace ℂ A →L[ℂ] EuclideanSpace ℂ A) (x : X) :
    LookupAmplitudePreparation.Space A Z →L[ℂ] LookupAmplitudePreparation.Space A Z :=
  (spectatorLayout (A := A) (Z := Z)).symm.conjStarAlgEquiv
    (WeightedClock.diagonal (fun _ : Z × Bool => F x))

@[simp] theorem location_apply
    (F : X → EuclideanSpace ℂ A →L[ℂ] EuclideanSpace ℂ A) (x : X)
    (v : LookupAmplitudePreparation.Space A Z) (a : A) (z : Z) (b : Bool) :
    location F x v (a, z) b =
      F x (WithLp.toLp 2 (fun a' => v (a', z) b)) a := rfl

/-- No behavior on unpromised basis inputs is needed beyond native unitarity. -/
theorem location_unitary
    (F : X → EuclideanSpace ℂ A →L[ℂ] EuclideanSpace ℂ A)
    (hF : ∀ x, IsUnitary (F x)) (x : X) :
    IsUnitary (location (Z := Z) F x) := by
  have hd : IsUnitary (WeightedClock.diagonal (fun _ : Z × Bool => F x)) := by
    constructor
    · exact WeightedClock.diagonal_isometry _ (fun _ => (hF x).1)
    · change WeightedClock.diagonal (fun _ : Z × Bool => F x) ∘L
        (WeightedClock.diagonal (fun _ : Z × Bool => F x))† = 1
      rw [WeightedClock.diagonal_adjoint, WeightedClock.diagonal_comp]
      have hh := (hF x).2
      change F x ∘L (F x)† = 1 at hh
      simp only [hh, WeightedClock.diagonal_one]
  exact hd.transport (spectatorLayout (A := A) (Z := Z)).symm

/-- Labels identify ordinary calls, not a coherently controlled SELECT oracle. -/
inductive Query where
  | location
  | value
  deriving DecidableEq

variable [AddCommGroup Z]

/-- The native location primitive and ordinary additive value primitive on the
same physical workspace. -/
def oracles (F : X → EuclideanSpace ℂ A →L[ℂ] EuclideanSpace ℂ A)
    (f : X → A → Z) : Query → X →
      LookupAmplitudePreparation.Space A Z →L[ℂ] LookupAmplitudePreparation.Space A Z
  | .location => location F
  | .value => LookupControlledGate.oracle (K := Qubit) f

/-- Execute one native location call, then the fixed-decoder two-value-query
program. Every fixed gate is uniform in the unknown input instance. -/
def program (F : X → EuclideanSpace ℂ A →L[ℂ] EuclideanSpace ℂ A)
    (decode : A → Z → ℂ) (hdecode : ∀ a z, ‖decode a z‖ ≤ 1)
    (f : X → A → Z) : MultiOracleCircuit.Program (oracles F f) :=
  .seq (MultiOracleCircuit.Program.embed .value
    (LookupAmplitudePreparation.program decode hdecode f)) (.query .location)

/-- The sparse preparation has exactly three physical queries in total. -/
@[simp] theorem program_count
    (F : X → EuclideanSpace ℂ A →L[ℂ] EuclideanSpace ℂ A)
    (decode : A → Z → ℂ) (hdecode : ∀ a z, ‖decode a z‖ ≤ 1) (f : X → A → Z) :
    (program F decode hdecode f).count = 3 := rfl

/-- Exactly one forward native location query occurs. -/
@[simp] theorem program_location_count
    (F : X → EuclideanSpace ℂ A →L[ℂ] EuclideanSpace ℂ A)
    (decode : A → Z → ℂ) (hdecode : ∀ a z, ‖decode a z‖ ≤ 1) (f : X → A → Z) :
    (program F decode hdecode f).labelCount .location = 1 := rfl

/-- One forward and one inverse value call are both counted. -/
@[simp] theorem program_value_count
    (F : X → EuclideanSpace ℂ A →L[ℂ] EuclideanSpace ℂ A)
    (decode : A → Z → ℂ) (hdecode : ∀ a z, ‖decode a z‖ ≤ 1) (f : X → A → Z) :
    (program F decode hdecode f).labelCount .value = 2 := rfl

/-- Separate implementation costs remain visible under later compilation. -/
theorem program_cost
    (F : X → EuclideanSpace ℂ A →L[ℂ] EuclideanSpace ℂ A)
    (decode : A → Z → ℂ) (hdecode : ∀ a z, ‖decode a z‖ ≤ 1) (f : X → A → Z)
    (w : Query → ℕ) :
    (program F decode hdecode f).cost w = w .location + 2 * w .value := by
  change w .value + (0 + w .value) + w .location = _
  omega

/-- Syntactic evaluation is the specified physical circuit. -/
theorem program_eval
    (F : X → EuclideanSpace ℂ A →L[ℂ] EuclideanSpace ℂ A)
    (decode : A → Z → ℂ) (hdecode : ∀ a z, ‖decode a z‖ ≤ 1) (f : X → A → Z)
    (x : X) :
    (program F decode hdecode f).eval x =
      (LookupAmplitudePreparation.program decode hdecode f).eval x ∘L location F x := by
  simp only [program, MultiOracleCircuit.Program.eval_seq,
    MultiOracleCircuit.Program.eval_embed, MultiOracleCircuit.Program.eval_query]
  rfl

/-- The counted program is unitary on the entire physical space, including
invalid location inputs and dirty value registers. -/
theorem program_unitary
    (F : X → EuclideanSpace ℂ A →L[ℂ] EuclideanSpace ℂ A)
    (hF : ∀ x, IsUnitary (F x))
    (decode : A → Z → ℂ) (hdecode : ∀ a z, ‖decode a z‖ ≤ 1) (f : X → A → Z)
    (x : X) : IsUnitary ((program F decode hdecode f).eval x) := by
  apply MultiOracleCircuit.Program.eval_unitary
  intro l x
  cases l with
  | location => exact location_unitary F hF x
  | value => exact LookupControlledGate.oracle_unitary f x

variable [DecidableEq Z]

/-- The spectator extension transports every coherent address vector while
keeping the value and flag registers clean. -/
theorem location_input
    (F : X → EuclideanSpace ℂ A →L[ℂ] EuclideanSpace ℂ A) (x : X)
    (v : EuclideanSpace ℂ A) :
    location (Z := Z) F x (LookupAmplitudePreparation.input v) =
      LookupAmplitudePreparation.input (F x v) := by
  ext az b
  rcases az with ⟨a, z⟩
  rw [location_apply]
  by_cases hz : z = 0
  · subst z
    cases b
    · have hv : (WithLp.toLp 2 (fun a' =>
          LookupAmplitudePreparation.input (Z := Z) v (a', 0) false) :
          EuclideanSpace ℂ A) = v := by ext; simp
      rw [hv]
      simp
    · have hv : (WithLp.toLp 2 (fun a' =>
          LookupAmplitudePreparation.input (Z := Z) v (a', 0) true) :
          EuclideanSpace ℂ A) = 0 := by ext; simp
      rw [hv, map_zero]
      simp
  · have hv : (WithLp.toLp 2 (fun a' =>
        LookupAmplitudePreparation.input (Z := Z) v (a', z) b) :
        EuclideanSpace ℂ A) = 0 := by ext; simp [hz]
    rw [hv, map_zero]
    simp [hz]

/-- A fixed initial isometry may prepare a coherent uniform slot state. -/
def input {I : Type*} [Fintype I]
    (E : EuclideanSpace ℂ I →ₗᵢ[ℂ] EuclideanSpace ℂ A) :
    EuclideanSpace ℂ I →ₗᵢ[ℂ] LookupAmplitudePreparation.Space A Z :=
  LookupAmplitudePreparation.input.comp E

/-- Full physical output of one location call and the explicit two-call value
preparation. -/
def preparation {I : Type*} [Fintype I]
    (F : X → EuclideanSpace ℂ A →L[ℂ] EuclideanSpace ℂ A)
    (decode : A → Z → ℂ) (hdecode : ∀ a z, ‖decode a z‖ ≤ 1)
    (f : X → A → Z) (E : EuclideanSpace ℂ I →ₗᵢ[ℂ] EuclideanSpace ℂ A)
    (x : X) : EuclideanSpace ℂ I →L[ℂ] LookupAmplitudePreparation.Space A Z :=
  (LookupAmplitudePreparation.program decode hdecode f).eval x ∘L
    location F x ∘L (input (Z := Z) E).toContinuousLinearMap

/-- The full state-preparation map is produced by the explicitly counted
program acting on one fixed input isometry. -/
theorem preparation_eq_program {I : Type*} [Fintype I]
    (F : X → EuclideanSpace ℂ A →L[ℂ] EuclideanSpace ℂ A)
    (decode : A → Z → ℂ) (hdecode : ∀ a z, ‖decode a z‖ ≤ 1)
    (f : X → A → Z) (E : EuclideanSpace ℂ I →ₗᵢ[ℂ] EuclideanSpace ℂ A)
    (x : X) :
    preparation F decode hdecode f E x =
      (program F decode hdecode f).eval x ∘L (input (Z := Z) E).toContinuousLinearMap := by
  unfold preparation
  rw [program_eval]
  exact (comp_assoc _ _ _).symm

/-- Coherent correctness of the complete output, including both flag branches. -/
theorem preparation_apply {I : Type*} [Fintype I]
    (F : X → EuclideanSpace ℂ A →L[ℂ] EuclideanSpace ℂ A)
    (decode : A → Z → ℂ) (hdecode : ∀ a z, ‖decode a z‖ ≤ 1)
    (f : X → A → Z) (E : EuclideanSpace ℂ I →ₗᵢ[ℂ] EuclideanSpace ℂ A)
    (x : X) (v : EuclideanSpace ℂ I) (a : A) (z : Z) (b : Bool) :
    preparation F decode hdecode f E x v (a, z) b =
      if z = 0 then F x (E v) a *
        (if b then (badAmplitude (decode a (f x a)) : ℂ) else decode a (f x a))
      else 0 := by
  change ((LookupAmplitudePreparation.program decode hdecode f).eval x
    (location F x (LookupAmplitudePreparation.input (E v)))) (a, z) b = _
  rw [location_input]
  exact LookupAmplitudePreparation.preparation_apply decode hdecode f x (F x (E v)) a z b

/-- The value register is returned to zero on every output branch. -/
theorem preparation_value_restored {I : Type*} [Fintype I]
    (F : X → EuclideanSpace ℂ A →L[ℂ] EuclideanSpace ℂ A)
    (decode : A → Z → ℂ) (hdecode : ∀ a z, ‖decode a z‖ ≤ 1)
    (f : X → A → Z) (E : EuclideanSpace ℂ I →ₗᵢ[ℂ] EuclideanSpace ℂ A)
    (x : X) (v : EuclideanSpace ℂ I) (a : A) (z : Z) (hz : z ≠ 0) (b : Bool) :
    preparation F decode hdecode f E x v (a, z) b = 0 := by
  simp [preparation_apply, hz]

/-- The full preparation preserves coherent norms; no success postselection is
used in the isometry statement. -/
theorem preparation_norm {I : Type*} [Fintype I]
    (F : X → EuclideanSpace ℂ A →L[ℂ] EuclideanSpace ℂ A)
    (hF : ∀ x, IsUnitary (F x))
    (decode : A → Z → ℂ) (hdecode : ∀ a z, ‖decode a z‖ ≤ 1)
    (f : X → A → Z) (E : EuclideanSpace ℂ I →ₗᵢ[ℂ] EuclideanSpace ℂ A)
    (x : X) (v : EuclideanSpace ℂ I) :
    ‖preparation F decode hdecode f E x v‖ = ‖v‖ := by
  change ‖(LookupAmplitudePreparation.program decode hdecode f).eval x
    (location F x (input (Z := Z) E v))‖ = _
  rw [((LookupAmplitudePreparation.program decode hdecode f).eval x).norm_map_iff_adjoint_comp_self.mpr
    (LookupAmplitudePreparation.program_unitary decode hdecode f x).1]
  rw [(location (Z := Z) F x).norm_map_iff_adjoint_comp_self.mpr
    (location_unitary F hF x).1]
  exact (input (Z := Z) E).norm_map v

/-- Both good and failure branches together define a genuine isometry. -/
theorem preparation_isometry {I : Type*} [Fintype I]
    (F : X → EuclideanSpace ℂ A →L[ℂ] EuclideanSpace ℂ A)
    (hF : ∀ x, IsUnitary (F x))
    (decode : A → Z → ℂ) (hdecode : ∀ a z, ‖decode a z‖ ≤ 1)
    (f : X → A → Z) (E : EuclideanSpace ℂ I →ₗᵢ[ℂ] EuclideanSpace ℂ A)
    (x : X) :
    (preparation F decode hdecode f E x)† ∘L preparation F decode hdecode f E x = 1 :=
  (preparation F decode hdecode f E x).norm_map_iff_adjoint_comp_self.mp
    (preparation_norm F hF decode hdecode f E x)

section ValidSlots

variable {I N : Type*} [Fintype I] [Fintype N] [DecidableEq I] [DecidableEq N] {s : ℕ}

omit [Fintype I] [Fintype N] in
/-- A native oracle's unit-amplitude basis promise extends to arbitrary complex
coefficients by linearity. -/
theorem basis_scaled
    (F : EuclideanSpace ℂ (I × N) →L[ℂ] EuclideanSpace ℂ (I × N))
    (b c : I × N)
    (h : F (EuclideanSpace.single b 1) = EuclideanSpace.single c 1) (z : ℂ) :
    F (EuclideanSpace.single b z) = EuclideanSpace.single c z := by
  have hs (q : I × N) : EuclideanSpace.single q z = z • EuclideanSpace.single q 1 := by
    ext p
    by_cases hp : p = q <;> simp [hp]
  rw [hs, map_smul, h, ← hs]

/-- A valid-slot promise completely determines the coherent located uniform
state, regardless of the oracle's action elsewhere. -/
theorem native_uniform_sum
    (F : X → EuclideanSpace ℂ (I × N) →L[ℂ] EuclideanSpace ℂ (I × N))
    (slot : Fin s ↪ N) (hs : 0 < s) (image : X → I → Fin s → I × N)
    (hvalid : ∀ x i k, F x (EuclideanSpace.single (i, slot k) 1) =
      EuclideanSpace.single (image x i k) 1)
    (x : X) (v : EuclideanSpace ℂ I) :
    F x (UniformSlotPreparation.embedding slot hs v) =
      ∑ i, ∑ k : Fin s, EuclideanSpace.single (image x i k)
        (v i * UniformSlotPreparation.weight s) := by
  rw [UniformSlotPreparation.embedding_eq_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _
  exact basis_scaled (F x) _ _ (hvalid x i k) _

/-- Exact address amplitudes after an in-place row locator. All `s` slots,
including zero-valued padding, keep the same uniform normalization. -/
theorem native_uniform_row
    (F : X → EuclideanSpace ℂ (I × N) →L[ℂ] EuclideanSpace ℂ (I × N))
    (slot : Fin s ↪ N) (hs : 0 < s) (loc : X → I → Fin s → N)
    (hinj : ∀ x i, Function.Injective (loc x i))
    (hvalid : ∀ x i k, F x (EuclideanSpace.single (i, slot k) 1) =
      EuclideanSpace.single (i, loc x i k) 1)
    (x : X) (v : EuclideanSpace ℂ I) (i : I) (j : N) :
    F x (UniformSlotPreparation.embedding slot hs v) (i, j) =
      if j ∈ Finset.univ.image (loc x i) then
        v i * UniformSlotPreparation.weight s else 0 := by
  rw [native_uniform_sum F slot hs (fun x i k => (i, loc x i k)) hvalid]
  simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.single_apply]
  have hsum : (∑ a : I, ∑ k : Fin s,
      if (i, j) = (a, loc x a k) then v a * UniformSlotPreparation.weight s else 0) =
      ∑ k : Fin s, if loc x i k = j then v i * UniformSlotPreparation.weight s else 0 := by
    rw [Finset.sum_eq_single i]
    · apply Finset.sum_congr rfl
      intro k _
      simp [eq_comm]
    · intro a _ ha
      apply Finset.sum_eq_zero
      intro k _
      simp [show i ≠ a from Ne.symm ha]
    · simp
  rw [hsum]
  exact UniformSlotPreparation.sum_slot_ite ⟨loc x i, hinj x i⟩ j _

/-- Exact address amplitudes for a column locator whose output uses the common
(row,column) physical order. -/
theorem native_uniform_column
    (F : X → EuclideanSpace ℂ (N × N) →L[ℂ] EuclideanSpace ℂ (N × N))
    (slot : Fin s ↪ N) (hs : 0 < s) (loc : X → N → Fin s → N)
    (hinj : ∀ x j, Function.Injective (loc x j))
    (hvalid : ∀ x j k, F x (EuclideanSpace.single (j, slot k) 1) =
      EuclideanSpace.single (loc x j k, j) 1)
    (x : X) (v : EuclideanSpace ℂ N) (i j : N) :
    F x (UniformSlotPreparation.embedding slot hs v) (i, j) =
      if i ∈ Finset.univ.image (loc x j) then
        v j * UniformSlotPreparation.weight s else 0 := by
  rw [native_uniform_sum F slot hs (fun x j k => (loc x j k, j)) hvalid]
  simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.single_apply]
  have hsum : (∑ a : N, ∑ k : Fin s,
      if (i, j) = (loc x a k, a) then v a * UniformSlotPreparation.weight s else 0) =
      ∑ k : Fin s, if loc x j k = i then v j * UniformSlotPreparation.weight s else 0 := by
    rw [Finset.sum_eq_single j]
    · apply Finset.sum_congr rfl
      intro k _
      simp [eq_comm]
    · intro a _ ha
      apply Finset.sum_eq_zero
      intro k _
      simp [show j ≠ a from Ne.symm ha]
    · simp
  rw [hsum]
  exact UniformSlotPreparation.sum_slot_ite ⟨loc x j, hinj x j⟩ i _

/-- The actual counted row preparation has the desired uniformly weighted
entry amplitude and its complete local failure amplitude. -/
theorem preparation_uniform_row_apply
    (F : X → EuclideanSpace ℂ (I × N) →L[ℂ] EuclideanSpace ℂ (I × N))
    (slot : Fin s ↪ N) (hs : 0 < s) (loc : X → I → Fin s → N)
    (hinj : ∀ x i, Function.Injective (loc x i))
    (hvalid : ∀ x i k, F x (EuclideanSpace.single (i, slot k) 1) =
      EuclideanSpace.single (i, loc x i k) 1)
    (decode : (I × N) → Z → ℂ) (hdecode : ∀ a z, ‖decode a z‖ ≤ 1)
    (f : X → (I × N) → Z)
    (x : X) (v : EuclideanSpace ℂ I) (i : I) (j : N) (z : Z) (b : Bool) :
    preparation F decode hdecode f (UniformSlotPreparation.embedding slot hs)
      x v ((i, j), z) b =
      if z = 0 ∧ j ∈ Finset.univ.image (loc x i) then
        v i * UniformSlotPreparation.weight s *
          (if b then (badAmplitude (decode (i, j) (f x (i, j))) : ℂ)
            else decode (i, j) (f x (i, j))) else 0 := by
  rw [preparation_apply, native_uniform_row F slot hs loc hinj hvalid]
  by_cases hz : z = 0 <;> by_cases hj : j ∈ Finset.univ.image (loc x i) <;>
    simp [hz, hj]

/-- The column preparation uses the same physical address order and retains
exactly the original `s` slots, with a clean value register. -/
theorem preparation_uniform_column_apply
    (F : X → EuclideanSpace ℂ (N × N) →L[ℂ] EuclideanSpace ℂ (N × N))
    (slot : Fin s ↪ N) (hs : 0 < s) (loc : X → N → Fin s → N)
    (hinj : ∀ x j, Function.Injective (loc x j))
    (hvalid : ∀ x j k, F x (EuclideanSpace.single (j, slot k) 1) =
      EuclideanSpace.single (loc x j k, j) 1)
    (decode : (N × N) → Z → ℂ) (hdecode : ∀ a z, ‖decode a z‖ ≤ 1)
    (f : X → (N × N) → Z)
    (x : X) (v : EuclideanSpace ℂ N) (i j : N) (z : Z) (b : Bool) :
    preparation F decode hdecode f (UniformSlotPreparation.embedding slot hs)
      x v ((i, j), z) b =
      if z = 0 ∧ i ∈ Finset.univ.image (loc x j) then
        v j * UniformSlotPreparation.weight s *
          (if b then (badAmplitude (decode (i, j) (f x (i, j))) : ℂ)
            else decode (i, j) (f x (i, j))) else 0 := by
  rw [preparation_apply, native_uniform_column F slot hs loc hinj hvalid]
  by_cases hz : z = 0 <;> by_cases hi : i ∈ Finset.univ.image (loc x j) <;>
    simp [hz, hi]

end ValidSlots

end
end SparseHamiltonian.SparseSlotPreparation
