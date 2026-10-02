import SparseHamiltonian.CleanValueEmbedding

/-!
# Two-query lookup with fixed nonlinear value postprocessing

The ordinary lookup first computes a table value into scratch. A fixed reversible
copy gate adds an arbitrary known function of the address and scratch value into
the target, and the inverse ordinary lookup restores scratch. The desired
postprocessed lookup is obtained on clean scratch. For nonlinear postprocessing,
its action on dirty scratch is generally different and is stated explicitly.
-/

namespace SparseHamiltonian.PostprocessedLookup

noncomputable section
open ContinuousLinearMap LookupOracle OracleCircuit
open scoped InnerProduct

section Permutations
variable {X A Z W : Type*} [AddCommGroup Z] [AddCommGroup W]

/-- Address and postprocessed-value target, together with original-value scratch. -/
abbrev Workspace (A W Z : Type*) := (A × W) × Z

/-- Apply a fixed, possibly nonlinear map to each addressed table value. -/
def table (g : A → Z → W) (f : X → A → Z) (x : X) (a : A) : W := g a (f x a)

/-- Fixed register wiring for the ordinary lookup into scratch; target is a spectator. -/
def scratchWiring : Workspace A W Z ≃ W × (A × Z) where
  toFun v := (v.1.2, v.1.1, v.2)
  invFun v := ((v.2.1, v.1), v.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- One literal ordinary value query, with the postprocessed target unchanged. -/
def computeEquiv (f : X → A → Z) (x : X) : Workspace A W Z ≃ Workspace A W Z :=
  scratchWiring.trans ((spectatorEquiv W f x).trans scratchWiring.symm)

omit [AddCommGroup W] in
@[simp] theorem computeEquiv_apply (f : X → A → Z) (x : X)
    (a : A) (w : W) (z : Z) :
    computeEquiv f x ((a, w), z) = ((a, w), z + f x a) := rfl

omit [AddCommGroup W] in
@[simp] theorem computeEquiv_symm_apply (f : X → A → Z) (x : X)
    (a : A) (w : W) (z : Z) :
    (computeEquiv f x).symm ((a, w), z) = ((a, w), z - f x a) := rfl

/-- The reversible nonlinear copy gate is fixed and has no unknown-input argument. -/
def copyEquiv (g : A → Z → W) : Workspace A W Z ≃ Workspace A W Z where
  toFun v := ((v.1.1, v.1.2 + g v.1.1 v.2), v.2)
  invFun v := ((v.1.1, v.1.2 - g v.1.1 v.2), v.2)
  left_inv v := by simp
  right_inv v := by simp

/-- Compute a value, copy its postprocessing, and uncompute the value. -/
def circuitEquiv (g : A → Z → W) (f : X → A → Z) (x : X) :
    Workspace A W Z ≃ Workspace A W Z :=
  (computeEquiv f x).trans ((copyEquiv g).trans (computeEquiv f x).symm)

/-- Actual dirty-scratch action: scratch is restored, but it affects the processed value. -/
theorem circuitEquiv_apply (g : A → Z → W) (f : X → A → Z) (x : X)
    (a : A) (w : W) (z : Z) :
    circuitEquiv g f x ((a, w), z) = ((a, w + g a (z + f x a)), z) := by
  simp [circuitEquiv, copyEquiv]

/-- The inverse circuit has the corresponding exact full-space action. -/
theorem circuitEquiv_symm_apply (g : A → Z → W) (f : X → A → Z) (x : X)
    (a : A) (w : W) (z : Z) :
    (circuitEquiv g f x).symm ((a, w), z) = ((a, w - g a (z + f x a)), z) := by
  simp [circuitEquiv, copyEquiv]

/-- Clean scratch yields the desired postprocessed table without changing addresses. -/
theorem circuitEquiv_clean (g : A → Z → W) (f : X → A → Z) (x : X)
    (a : A) (w : W) :
    circuitEquiv g f x ((a, w), 0) = (basisEquiv (table g f) x (a, w), 0) := by
  simp [circuitEquiv_apply, table]

end Permutations

section Hilbert
variable {X A Z W : Type*} [Fintype A] [Fintype Z] [Fintype W]
  [AddCommGroup Z] [AddCommGroup W]

/-- The primitive oracle is an ordinary lookup into the original-value scratch. -/
def oracle (f : X → A → Z) (x : X) :
    EuclideanSpace ℂ (Workspace A W Z) →L[ℂ] EuclideanSpace ℂ (Workspace A W Z) :=
  (permutationUnitary (computeEquiv f x)).toLinearIsometry.toContinuousLinearMap

/-- The actual postprocessing circuit on the entire physical workspace. -/
def circuit (g : A → Z → W) (f : X → A → Z) (x : X) :
    EuclideanSpace ℂ (Workspace A W Z) →L[ℂ] EuclideanSpace ℂ (Workspace A W Z) :=
  (permutationUnitary (circuitEquiv g f x)).toLinearIsometry.toContinuousLinearMap

/-- The logical addition lookup for the postprocessed table. -/
def logical (g : A → Z → W) (f : X → A → Z) (x : X) :
    EuclideanSpace ℂ (A × W) →L[ℂ] EuclideanSpace ℂ (A × W) :=
  (permutationUnitary (basisEquiv (table g f) x)).toLinearIsometry.toContinuousLinearMap

omit [AddCommGroup W] in
/-- Both unitary identities for the primitive ordinary lookup. -/
theorem oracle_unitary (f : X → A → Z) (x : X) :
    IsUnitary (oracle (W := W) f x) := permutationUnitary_unitary _

/-- Both unitary identities for the whole physical circuit, including dirty scratch. -/
theorem circuit_unitary (g : A → Z → W) (f : X → A → Z) (x : X) :
    IsUnitary (circuit g f x) := permutationUnitary_unitary _

omit [Fintype Z] [AddCommGroup Z] in
/-- A nonlinear table still defines a unitary reversible addition lookup. -/
theorem logical_unitary (g : A → Z → W) (f : X → A → Z) (x : X) :
    IsUnitary (logical g f x) := permutationUnitary_unitary _

/-- The exact circuit contains two ordinary queries and one fixed reversible gate. -/
theorem circuit_factorization (g : A → Z → W) (f : X → A → Z) (x : X) :
    circuit g f x = star (oracle f x) *
      (permutationUnitary (copyEquiv g)).toLinearIsometry.toContinuousLinearMap * oracle f x := by
  unfold oracle
  rw [ContinuousLinearMap.star_eq_adjoint, permutationUnitary_adjoint,
    ← permutationUnitary_symm]
  ext v w
  rfl

/-- Uniform implementation of the physical circuit with two ordinary queries. -/
theorem circuit_two_queries (g : A → Z → W) (f : X → A → Z) :
    Implements (oracle f) (circuit g f) 2 := by
  have hCopy := Implements.fixed (O := oracle f)
    (permutationUnitary (copyEquiv g)).toLinearIsometry.toContinuousLinearMap
    (permutationUnitary_unitary (copyEquiv g))
  have h := (Implements.queryAdjoint.mul hCopy).mul Implements.query
  exact h.congr fun x => (circuit_factorization g f x).symm

omit [AddCommGroup W] in
/-- Reindexing explicitly identifies the primitive with an ordinary lookup and spectators. -/
theorem oracle_rewiring (f : X → A → Z) (x : X) :
    oracle (W := W) f x =
      (permutationUnitary (scratchWiring (A := A) (W := W) (Z := Z)).symm).toLinearIsometry.toContinuousLinearMap ∘L
      (permutationUnitary (spectatorEquiv W f x)).toLinearIsometry.toContinuousLinearMap ∘L
      (permutationUnitary (scratchWiring (A := A) (W := W) (Z := Z))).toLinearIsometry.toContinuousLinearMap := by
  ext v w
  rfl

variable [DecidableEq Z]

/-- Fixed preparation of the original-value scratch in its computational zero state. -/
def cleanEmbedding : EuclideanSpace ℂ (A × W) →ₗᵢ[ℂ]
    EuclideanSpace ℂ (Workspace A W Z) := ControlledLookup.cleanEmbedding

omit [AddCommGroup W] in
@[simp] theorem cleanEmbedding_apply (v : EuclideanSpace ℂ (A × W))
    (a : A) (w : W) (z : Z) :
    cleanEmbedding v ((a, w), z) = if z = 0 then v (a, w) else 0 := rfl

omit [AddCommGroup W] in
/-- The fixed clean preparation is an exact Hilbert-space isometry. -/
theorem cleanEmbedding_isometry :
    (cleanEmbedding (A := A) (W := W) (Z := Z)).toContinuousLinearMap† ∘L
      (cleanEmbedding (A := A) (W := W) (Z := Z)).toContinuousLinearMap = 1 :=
  LinearIsometry.adjoint_comp_self _

/-- Coherent correctness on the clean-scratch subspace, with scratch returned to zero. -/
theorem circuit_clean (g : A → Z → W) (f : X → A → Z) (x : X) :
    circuit g f x ∘L (cleanEmbedding (A := A) (W := W) (Z := Z)).toContinuousLinearMap =
      (cleanEmbedding (A := A) (W := W) (Z := Z)).toContinuousLinearMap ∘L logical g f x := by
  ext v b
  rcases b with ⟨⟨a, w⟩, z⟩
  change (if ((circuitEquiv g f x).symm ((a, w), z)).2 = 0 then
      v ((circuitEquiv g f x).symm ((a, w), z)).1 else 0) =
    if z = 0 then v ((basisEquiv (table g f) x).symm (a, w)) else 0
  rw [circuitEquiv_symm_apply]
  by_cases hz : z = 0
  · subst z
    simp [table]
  · simp [hz]

/-- The postprocessed lookup costs two ordinary queries on a fixed encoded subspace.
No assertion about implementing that same lookup on dirty scratch is needed. -/
theorem postprocessed_two_queries (g : A → Z → W) (f : X → A → Z) :
    EncodedOracle.ImplementsOn (oracle f) (logical g f)
      (cleanEmbedding (A := A) (W := W) (Z := Z)).toContinuousLinearMap 2 :=
  EncodedOracle.ImplementsOn.of_full (circuit_two_queries g f) (circuit_clean g f)

/-- Inverse postprocessed lookup has the same two-query clean-subspace cost. -/
theorem postprocessed_adjoint_two_queries (g : A → Z → W) (f : X → A → Z) :
    EncodedOracle.ImplementsOn (oracle f) (fun x => star (logical g f x))
      (cleanEmbedding (A := A) (W := W) (Z := Z)).toContinuousLinearMap 2 :=
  (postprocessed_two_queries g f).adjoint (oracle_unitary f) (logical_unitary g f)

/-- Any program using the processed lookup compiles with a factor-two query cost. -/
theorem compile_processed_program (g : A → Z → W) (f : X → A → Z)
    {F : X → EuclideanSpace ℂ (A × W) →L[ℂ] EuclideanSpace ℂ (A × W)} {q : ℕ}
    (h : Implements (logical g f) F q) :
    EncodedOracle.ImplementsOn (oracle f) F
      (cleanEmbedding (A := A) (W := W) (Z := Z)).toContinuousLinearMap (2 * q) := by
  simpa only [Nat.mul_comm] using
    EncodedOracle.ImplementsOn.trans cleanEmbedding_isometry
      (oracle_unitary f) (logical_unitary g f) (postprocessed_two_queries g f) h

end Hilbert
end
end SparseHamiltonian.PostprocessedLookup
