import SparseHamiltonian.LookupOracle

/-!
# Controlled lookup from two ordinary lookup calls

A scratch value register is computed, copied into the target when a Boolean
control is true, and uncomputed. The middle gate is independent of the table.
A final inverse-copy cancels arbitrary initial scratch contents. The resulting
two-query unitary implements controlled lookup exactly on the full workspace,
with scratch returned unchanged.
-/

namespace SparseHamiltonian.ControlledLookup

noncomputable section
open ContinuousLinearMap LookupOracle
open scoped InnerProduct

section Permutations
variable {X A Z : Type*} [AddCommGroup Z]

/-- Public registers: control, address, target. -/
abbrev Public (A Z : Type*) := Bool × (A × Z)

/-- Public registers together with one scratch value register. -/
abbrev Workspace (A Z : Type*) := Public A Z × Z

/-- The desired controlled addition lookup on the public registers. -/
def controlledEquiv (f : X → A → Z) (x : X) : Public A Z ≃ Public A Z where
  toFun v := (v.1, v.2.1, v.2.2 + if v.1 then f x v.2.1 else 0)
  invFun v := (v.1, v.2.1, v.2.2 - if v.1 then f x v.2.1 else 0)
  left_inv v := by simp
  right_inv v := by simp

@[simp] theorem controlledEquiv_apply (f : X → A → Z) (x : X)
    (b : Bool) (a : A) (z : Z) :
    controlledEquiv f x (b, a, z) = (b, a, z + if b then f x a else 0) := rfl

/-- Fixed rewiring exposes address and scratch as the ordinary lookup registers. -/
def scratchWiring : Workspace A Z ≃ (Bool × Z) × (A × Z) where
  toFun v := ((v.1.1, v.1.2.2), v.1.2.1, v.2)
  invFun v := ((v.1.1, v.2.1, v.1.2), v.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- One ordinary lookup into scratch; control and target are spectators. -/
def computeEquiv (f : X → A → Z) (x : X) : Workspace A Z ≃ Workspace A Z :=
  scratchWiring.trans ((spectatorEquiv (Bool × Z) f x).trans scratchWiring.symm)

@[simp] theorem computeEquiv_apply (f : X → A → Z) (x : X)
    (b : Bool) (a : A) (z y : Z) :
    computeEquiv f x ((b, a, z), y) = ((b, a, z), y + f x a) := rfl

@[simp] theorem computeEquiv_symm_apply (f : X → A → Z) (x : X)
    (b : Bool) (a : A) (z y : Z) :
    (computeEquiv f x).symm ((b, a, z), y) = ((b, a, z), y - f x a) := rfl

/-- The only middle gate: add scratch into target conditioned on a known register.
It has no table or unknown-input argument. -/
def copyEquiv : Workspace A Z ≃ Workspace A Z where
  toFun v := ((v.1.1, v.1.2.1, v.1.2.2 + if v.1.1 then v.2 else 0), v.2)
  invFun v := ((v.1.1, v.1.2.1, v.1.2.2 - if v.1.1 then v.2 else 0), v.2)
  left_inv v := by simp
  right_inv v := by simp

/-- Compute, copy, uncompute, and cancel the original scratch contribution. -/
def circuitEquiv (f : X → A → Z) (x : X) : Workspace A Z ≃ Workspace A Z :=
  (computeEquiv f x).trans
    (copyEquiv.trans ((computeEquiv f x).symm.trans copyEquiv.symm))

/-- Exact action even when scratch initially contains a nonzero value. -/
theorem circuitEquiv_apply (f : X → A → Z) (x : X)
    (b : Bool) (a : A) (z y : Z) :
    circuitEquiv f x ((b, a, z), y) =
      ((b, a, z + if b then f x a else 0), y) := by
  cases b <;> simp [circuitEquiv, copyEquiv]
  abel

/-- Clean scratch gives the desired controlled lookup and is returned unchanged. -/
theorem circuitEquiv_clean (f : X → A → Z) (x : X) (v : Public A Z) :
    circuitEquiv f x (v, 0) = (controlledEquiv f x v, 0) := by
  rcases v with ⟨b, a, z⟩
  simp [circuitEquiv_apply]

/-- The inverse of the complete circuit also preserves scratch. -/
theorem circuitEquiv_symm_apply (f : X → A → Z) (x : X)
    (b : Bool) (a : A) (z y : Z) :
    (circuitEquiv f x).symm ((b, a, z), y) =
      ((b, a, z - if b then f x a else 0), y) := by
  cases b <;> simp [circuitEquiv, copyEquiv, sub_add_eq_sub_sub]

end Permutations
section Hilbert
variable {B Z : Type*} [Fintype B] [Fintype Z] [AddCommGroup Z] [DecidableEq Z]

/-- Tensor in a clean scratch register in the computational zero state. -/
def cleanEmbedding : EuclideanSpace ℂ B →ₗᵢ[ℂ] EuclideanSpace ℂ (B × Z) where
  toLinearMap :=
    { toFun := fun v => WithLp.toLp 2 (fun w => if w.2 = 0 then v w.1 else 0)
      map_add' := by
        intro v w
        apply PiLp.ext
        intro i
        by_cases hi : i.2 = 0 <;> simp [hi]
      map_smul' := by
        intro z v
        apply PiLp.ext
        intro i
        by_cases hi : i.2 = 0 <;> simp [hi] }
  norm_map' := by
    intro v
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [PiLp.norm_sq_eq_of_L2]
    classical
    simp [Fintype.sum_prod_type, apply_ite]

@[simp] theorem cleanEmbedding_apply (v : EuclideanSpace ℂ B) (b : B) (z : Z) :
    cleanEmbedding (Z := Z) v (b, z) = if z = 0 then v b else 0 := rfl

/-- The clean embedding is an actual isometry, including all ancilla amplitudes. -/
theorem cleanEmbedding_adjoint_comp :
    (cleanEmbedding (B := B) (Z := Z)).toContinuousLinearMap† ∘L
      (cleanEmbedding (B := B) (Z := Z)).toContinuousLinearMap = 1 :=
  LinearIsometry.adjoint_comp_self _

end Hilbert

section QueryProgram
variable {X A Z : Type*} [Fintype A] [Fintype Z] [AddCommGroup Z]

/-- The workspace oracle makes one ordinary addition lookup into scratch. -/
def oracle (f : X → A → Z) (x : X) :
    EuclideanSpace ℂ (Workspace A Z) →L[ℂ] EuclideanSpace ℂ (Workspace A Z) :=
  (permutationUnitary (computeEquiv f x)).toLinearIsometry.toContinuousLinearMap

/-- The complete compute/copy/uncompute unitary. -/
def circuit (f : X → A → Z) (x : X) :
    EuclideanSpace ℂ (Workspace A Z) →L[ℂ] EuclideanSpace ℂ (Workspace A Z) :=
  (permutationUnitary (circuitEquiv f x)).toLinearIsometry.toContinuousLinearMap

/-- The oracle itself satisfies both unitary identities. -/
theorem oracle_unitary (f : X → A → Z) (x : X) :
    OracleCircuit.IsUnitary (oracle f x) :=
  permutationUnitary_unitary (computeEquiv f x)

/-- Factorization into two oracle calls and two fixed reversible gates. -/
theorem circuit_factorization (f : X → A → Z) (x : X) :
    circuit f x =
      (permutationUnitary (copyEquiv (A := A) (Z := Z)).symm).toLinearIsometry.toContinuousLinearMap *
      star (oracle f x) *
      (permutationUnitary (copyEquiv (A := A) (Z := Z))).toLinearIsometry.toContinuousLinearMap *
      oracle f x := by
  unfold oracle
  rw [ContinuousLinearMap.star_eq_adjoint, permutationUnitary_adjoint,
    ← permutationUnitary_symm]
  ext v w
  rfl

/-- Exact uniform query certificate; all free gates are independent of the table. -/
theorem circuit_two_queries (f : X → A → Z) :
    OracleCircuit.Implements (oracle f) (circuit f) 2 := by
  have hc := OracleCircuit.Implements.fixed
    (O := oracle f) (permutationUnitary (copyEquiv (A := A) (Z := Z))).toLinearIsometry.toContinuousLinearMap
    (permutationUnitary_unitary (copyEquiv (A := A) (Z := Z)))
  have hi := OracleCircuit.Implements.fixed
    (O := oracle f) (permutationUnitary (copyEquiv (A := A) (Z := Z)).symm).toLinearIsometry.toContinuousLinearMap
    (permutationUnitary_unitary (copyEquiv (A := A) (Z := Z)).symm)
  have h := ((hi.mul OracleCircuit.Implements.queryAdjoint).mul hc).mul
    OracleCircuit.Implements.query
  exact h.congr fun x => (circuit_factorization f x).symm

/-- Full-space correctness, with arbitrary scratch, including entangled states. -/
theorem circuit_eq_controlled (f : X → A → Z) (x : X) :
    circuit f x = (permutationUnitary
      (Equiv.prodCongr (controlledEquiv f x) (Equiv.refl Z))).toLinearIsometry.toContinuousLinearMap := by
  have he : circuitEquiv f x = Equiv.prodCongr (controlledEquiv f x) (Equiv.refl Z) := by
    apply Equiv.ext
    rintro ⟨⟨b, a, z⟩, y⟩
    exact circuitEquiv_apply f x b a z y
  unfold circuit
  rw [he]

/-- The controlled permutation with arbitrary untouched scratch costs two calls. -/
theorem controlled_two_queries (f : X → A → Z) :
    OracleCircuit.Implements (oracle f) (fun x => (permutationUnitary
      (Equiv.prodCongr (controlledEquiv f x) (Equiv.refl Z))).toLinearIsometry.toContinuousLinearMap) 2 :=
  (circuit_two_queries f).congr (circuit_eq_controlled f)

variable [DecidableEq Z]

/-- Coherent correctness with a clean scratch register: exact equality of operators. -/
theorem circuit_clean (f : X → A → Z) (x : X) :
    circuit f x ∘L (cleanEmbedding (B := Public A Z) (Z := Z)).toContinuousLinearMap =
      (cleanEmbedding (B := Public A Z) (Z := Z)).toContinuousLinearMap ∘L
        (permutationUnitary (controlledEquiv f x)).toLinearIsometry.toContinuousLinearMap := by
  ext v w
  rcases w with ⟨⟨b, a, z⟩, y⟩
  change (if ((circuitEquiv f x).symm ((b, a, z), y)).2 = 0 then
      v ((circuitEquiv f x).symm ((b, a, z), y)).1 else 0) =
    if y = 0 then v ((controlledEquiv f x).symm (b, a, z)) else 0
  rw [circuitEquiv_symm_apply]
  by_cases hy : y = 0
  · subst y
    simp [controlledEquiv]
  · simp [hy]

/-- The final unitary returns scratch to zero for every coherent input state. -/
theorem circuit_clean_apply (f : X → A → Z) (x : X)
    (v : EuclideanSpace ℂ (Public A Z)) :
    circuit f x (cleanEmbedding v) =
      cleanEmbedding (permutationUnitary (controlledEquiv f x) v) :=
  congrArg (fun F : EuclideanSpace ℂ (Public A Z) →L[ℂ] EuclideanSpace ℂ (Workspace A Z) => F v)
    (circuit_clean f x)

end QueryProgram
end
end SparseHamiltonian.ControlledLookup
