import SparseHamiltonian.LookupFromBasisOracle

/-!
# In-place permutations from forward and inverse lookup channels

One tagged ordinary additive oracle provides a permutation and its inverse.
Compute-forward, swap, then subtract-inverse implements the permutation in
place on a fixed clean encoding. Two fixed tag flips select the channels and
restore the tag. Both channels are explicitly present in the oracle table;
no inverse-permutation access is inferred from forward lookup alone.
-/

namespace SparseHamiltonian.InPlaceFromLookup

noncomputable section
open ContinuousLinearMap LookupOracle OracleCircuit
open scoped InnerProduct

section Permutations
variable {X Z : Type*} [AddCommGroup Z]

/-- The tagged address is followed by one ordinary additive value target. -/
abbrev Workspace (Z : Type*) := (Bool × Z) × Z

/-- The supplied ordinary table contains explicit forward and inverse channels. -/
def table (π : X → Z ≃ Z) (x : X) (a : Bool × Z) : Z :=
  if a.1 then (π x).symm a.2 else π x a.2

omit [AddCommGroup Z] in
@[simp] theorem table_false (π : X → Z ≃ Z) (x : X) (z : Z) :
    table π x (false, z) = π x z := rfl

omit [AddCommGroup Z] in
@[simp] theorem table_true (π : X → Z ≃ Z) (x : X) (z : Z) :
    table π x (true, z) = (π x).symm z := rfl

/-- Fixed exchange of the address value and target, preserving the query tag. -/
def swapEquiv : Workspace Z ≃ Workspace Z where
  toFun v := ((v.1.1, v.2), v.1.2)
  invFun v := ((v.1.1, v.2), v.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Fixed exchange of the forward and inverse channel tags. -/
def flipEquiv : Workspace Z ≃ Workspace Z where
  toFun v := ((!v.1.1, v.1.2), v.2)
  invFun v := ((!v.1.1, v.1.2), v.2)
  left_inv v := by cases v with | mk a y => cases a with | mk b z => cases b <;> rfl
  right_inv v := by cases v with | mk a y => cases a with | mk b z => cases b <;> rfl

/-- Two ordinary tagged queries implement compute/swap/subtract-inverse. -/
def circuitEquiv (π : X → Z ≃ Z) (x : X) : Workspace Z ≃ Workspace Z :=
  (basisEquiv (table π) x).trans
    (swapEquiv.trans (flipEquiv.trans
      ((basisEquiv (table π) x).symm.trans flipEquiv)))

/-- The forward clean-input action restores both query tag and value scratch. -/
theorem circuitEquiv_clean (π : X → Z ≃ Z) (x : X) (z : Z) :
    circuitEquiv π x ((false, z), 0) = ((false, π x z), 0) := by
  simp [circuitEquiv, swapEquiv, flipEquiv, table]

/-- Exact inverse-circuit action on the forward-tag sector, including dirty values. -/
theorem circuitEquiv_symm_false (π : X → Z ≃ Z) (x : X) (z y : Z) :
    (circuitEquiv π x).symm ((false, z), y) =
      ((false, y + (π x).symm z), z - π x (y + (π x).symm z)) := by
  rfl

/-- The complete inverse circuit preserves the tag even outside the clean subspace. -/
theorem circuitEquiv_symm_tag (π : X → Z ≃ Z) (x : X) (v : Workspace Z) :
    ((circuitEquiv π x).symm v).1.1 = v.1.1 := by
  rcases v with ⟨⟨b, z⟩, y⟩
  cases b <;> rfl

/-- Dirty values cannot enter the clean subspace, by injectivity of the permutation. -/
theorem residual_zero_iff (π : X → Z ≃ Z) (x : X) (z y : Z) :
    z - π x (y + (π x).symm z) = 0 ↔ y = 0 := by
  constructor
  · intro h
    have h' : π x (y + (π x).symm z) = π x ((π x).symm z) := by
      rw [(π x).apply_symm_apply]
      exact (sub_eq_zero.mp h).symm
    have h'' := (π x).injective h'
    exact add_right_cancel (show y + (π x).symm z = 0 + (π x).symm z by simpa using h'')
  · intro h
    simp [h]

/-- Reindex a payload with two fixed ancillas into the ordinary tagged-oracle layout. -/
def cleanWiring : Z × (Bool × Z) ≃ Workspace Z where
  toFun v := ((v.2.1, v.1), v.2.2)
  invFun v := (v.1.2, v.1.1, v.2)
  left_inv _ := rfl
  right_inv _ := rfl

end Permutations

section Hilbert
variable {X Z : Type*} [Fintype Z] [AddCommGroup Z]

/-- One ordinary additive lookup with the explicit tagged permutation table. -/
def oracle (π : X → Z ≃ Z) (x : X) :
    EuclideanSpace ℂ (Workspace Z) →L[ℂ] EuclideanSpace ℂ (Workspace Z) :=
  (permutationUnitary (basisEquiv (table π) x)).toLinearIsometry.toContinuousLinearMap

/-- The exact physical compute/swap/subtract circuit. -/
def circuit (π : X → Z ≃ Z) (x : X) :
    EuclideanSpace ℂ (Workspace Z) →L[ℂ] EuclideanSpace ℂ (Workspace Z) :=
  (permutationUnitary (circuitEquiv π x)).toLinearIsometry.toContinuousLinearMap

/-- The logical in-place permutation on the payload alone. -/
def logical (π : X → Z ≃ Z) (x : X) : EuclideanSpace ℂ Z →L[ℂ] EuclideanSpace ℂ Z :=
  (permutationUnitary (π x)).toLinearIsometry.toContinuousLinearMap

/-- The tagged ordinary query is a unitary. -/
theorem oracle_unitary (π : X → Z ≃ Z) (x : X) : IsUnitary (oracle π x) :=
  permutationUnitary_unitary _

/-- The physical circuit is a unitary on all register states. -/
theorem circuit_unitary (π : X → Z ≃ Z) (x : X) : IsUnitary (circuit π x) :=
  permutationUnitary_unitary _

omit [AddCommGroup Z] in
/-- The logical in-place action is the actual permutation unitary. -/
theorem logical_unitary (π : X → Z ≃ Z) (x : X) : IsUnitary (logical π x) :=
  permutationUnitary_unitary _

/-- Every gate except the two tagged lookup calls is a fixed basis permutation. -/
theorem circuit_factorization (π : X → Z ≃ Z) (x : X) :
    circuit π x =
      (permutationUnitary (flipEquiv (Z := Z))).toLinearIsometry.toContinuousLinearMap *
      star (oracle π x) *
      (permutationUnitary (flipEquiv (Z := Z))).toLinearIsometry.toContinuousLinearMap *
      (permutationUnitary (swapEquiv (Z := Z))).toLinearIsometry.toContinuousLinearMap *
      oracle π x := by
  unfold oracle
  rw [ContinuousLinearMap.star_eq_adjoint, permutationUnitary_adjoint,
    ← permutationUnitary_symm]
  ext v w
  rfl

/-- Exact two-query implementation under one shared ordinary tagged oracle. -/
theorem circuit_two_queries (π : X → Z ≃ Z) : Implements (oracle π) (circuit π) 2 := by
  have hFlip := Implements.fixed (O := oracle π)
    (permutationUnitary (flipEquiv (Z := Z))).toLinearIsometry.toContinuousLinearMap
    (permutationUnitary_unitary (flipEquiv (Z := Z)))
  have hSwap := Implements.fixed (O := oracle π)
    (permutationUnitary (swapEquiv (Z := Z))).toLinearIsometry.toContinuousLinearMap
    (permutationUnitary_unitary (swapEquiv (Z := Z)))
  have h := (((hFlip.mul Implements.queryAdjoint).mul hFlip).mul hSwap).mul Implements.query
  exact h.congr fun x => (circuit_factorization π x).symm

variable [DecidableEq Z]

/-- The fixed encoding prepares the forward tag and a zero value target. -/
def cleanEmbedding : EuclideanSpace ℂ Z →ₗᵢ[ℂ] EuclideanSpace ℂ (Workspace Z) :=
  (permutationUnitary (cleanWiring (Z := Z))).toLinearIsometry.comp
    (CleanValueEmbedding.embedding (I := Z) (K := ℂ) (false, (0 : Z)))

@[simp] theorem cleanEmbedding_apply (v : EuclideanSpace ℂ Z) (b : Bool) (z y : Z) :
    cleanEmbedding v ((b, z), y) = if b = false ∧ y = 0 then v z else 0 := by
  change (if (b, y) = (false, 0) then v z else 0) = _
  simp only [Prod.mk.injEq]

/-- The prepared tag-and-scratch encoding is an exact isometry. -/
theorem cleanEmbedding_isometry :
    (cleanEmbedding (Z := Z)).toContinuousLinearMap† ∘L
      (cleanEmbedding (Z := Z)).toContinuousLinearMap = 1 := LinearIsometry.adjoint_comp_self _

/-- Exact coherent in-place action on the clean encoding, with both ancillas restored. -/
theorem circuit_clean (π : X → Z ≃ Z) (x : X) :
    circuit π x ∘L (cleanEmbedding (Z := Z)).toContinuousLinearMap =
      (cleanEmbedding (Z := Z)).toContinuousLinearMap ∘L logical π x := by
  ext v w
  rcases w with ⟨⟨b, z⟩, y⟩
  change cleanEmbedding v ((circuitEquiv π x).symm ((b, z), y)) =
    cleanEmbedding (logical π x v) ((b, z), y)
  cases b with
  | false =>
      rw [circuitEquiv_symm_false, cleanEmbedding_apply, cleanEmbedding_apply]
      simp only [true_and, residual_zero_iff]
      by_cases hy : y = 0
      · subst y
        simp [logical]
      · simp [hy]
  | true =>
      have hTag := circuitEquiv_symm_tag π x ((true, z), y)
      rw [cleanEmbedding_apply]
      change (if ((circuitEquiv π x).symm ((true, z), y)).1.1 = false ∧
          ((circuitEquiv π x).symm ((true, z), y)).2 = 0 then
          v ((circuitEquiv π x).symm ((true, z), y)).1.2 else 0) = _
      simp [hTag]

/-- In-place permutation access follows from the explicit forward-and-inverse
tagged table with two calls; it is not a consequence of forward lookup alone. -/
theorem inPlace_two_queries (π : X → Z ≃ Z) :
    EncodedOracle.ImplementsOn (oracle π) (logical π)
      (cleanEmbedding (Z := Z)).toContinuousLinearMap 2 :=
  EncodedOracle.ImplementsOn.of_full (circuit_two_queries π) (circuit_clean π)

/-- Logical inverse permutation access has the same encoded two-query bound. -/
theorem inPlace_adjoint_two_queries (π : X → Z ≃ Z) :
    EncodedOracle.ImplementsOn (oracle π) (fun x => star (logical π x))
      (cleanEmbedding (Z := Z)).toContinuousLinearMap 2 :=
  (inPlace_two_queries π).adjoint (oracle_unitary π) (logical_unitary π)

end Hilbert
end
end SparseHamiltonian.InPlaceFromLookup
