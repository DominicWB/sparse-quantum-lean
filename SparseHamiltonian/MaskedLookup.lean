import SparseHamiltonian.OracleTransport

/-!
# Uniform masked lookup with arbitrary spectator labels

A known integer mask on a spectator register controls how much of an ordinary
lookup value is added into its target.  The same ordinary scratch-lookup oracle
is used for every mask.  Compute/copy/uncompute/inverse-copy costs two queries
and returns arbitrary initial scratch contents unchanged, so the identity is
valid on the entire Hilbert space, including entangled scratch states.
-/

namespace SparseHamiltonian.MaskedLookup

noncomputable section
open ContinuousLinearMap LookupOracle
open scoped InnerProduct

section Permutations
variable {X I A Z : Type*} [AddCommGroup Z]

/-- Spectator label, address, and target value registers. -/
abbrev Public (I A Z : Type*) := I × (A × Z)

/-- Public registers with one ordinary value scratch register. -/
abbrev Workspace (I A Z : Type*) := Public I A Z × Z

/-- Lookup with a known integer weight on each spectator label. -/
def signedEquiv (m : I → ℤ) (f : X → A → Z) (x : X) :
    Public I A Z ≃ Public I A Z where
  toFun v := (v.1, v.2.1, v.2.2 + m v.1 • f x v.2.1)
  invFun v := (v.1, v.2.1, v.2.2 - m v.1 • f x v.2.1)
  left_inv v := by simp
  right_inv v := by simp

@[simp] theorem signedEquiv_apply (m : I → ℤ) (f : X → A → Z) (x : X)
    (i : I) (a : A) (z : Z) :
    signedEquiv m f x (i, a, z) = (i, a, z + m i • f x a) := rfl

@[simp] theorem signedEquiv_symm_apply (m : I → ℤ) (f : X → A → Z) (x : X)
    (i : I) (a : A) (z : Z) :
    (signedEquiv m f x).symm (i, a, z) = (i, a, z - m i • f x a) := rfl

/-- A fixed reindexing exposes address and scratch for an ordinary lookup. -/
def scratchWiring : Workspace I A Z ≃ (I × Z) × (A × Z) where
  toFun v := ((v.1.1, v.1.2.2), v.1.2.1, v.2)
  invFun v := ((v.1.1, v.2.1, v.1.2), v.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- One ordinary lookup into scratch. The label and target are spectators. -/
def computeEquiv (f : X → A → Z) (x : X) : Workspace I A Z ≃ Workspace I A Z :=
  scratchWiring.trans ((spectatorEquiv (I × Z) f x).trans scratchWiring.symm)

@[simp] theorem computeEquiv_apply (f : X → A → Z) (x : X)
    (i : I) (a : A) (z y : Z) :
    computeEquiv f x ((i, a, z), y) = ((i, a, z), y + f x a) := rfl

@[simp] theorem computeEquiv_symm_apply (f : X → A → Z) (x : X)
    (i : I) (a : A) (z y : Z) :
    (computeEquiv f x).symm ((i, a, z), y) = ((i, a, z), y - f x a) := rfl

/-- A table-independent copy gate, determined only by the known mask. -/
def copyEquiv (m : I → ℤ) : Workspace I A Z ≃ Workspace I A Z where
  toFun v := ((v.1.1, v.1.2.1, v.1.2.2 + m v.1.1 • v.2), v.2)
  invFun v := ((v.1.1, v.1.2.1, v.1.2.2 - m v.1.1 • v.2), v.2)
  left_inv v := by simp
  right_inv v := by simp

/-- Compute, weighted copy, uncompute, then cancel the initial scratch. -/
def circuitEquiv (m : I → ℤ) (f : X → A → Z) (x : X) :
    Workspace I A Z ≃ Workspace I A Z :=
  (computeEquiv f x).trans
    ((copyEquiv m).trans ((computeEquiv f x).symm.trans (copyEquiv m).symm))

/-- Full-space correctness: no clean-scratch assumption is needed. -/
theorem circuitEquiv_apply (m : I → ℤ) (f : X → A → Z) (x : X)
    (i : I) (a : A) (z y : Z) :
    circuitEquiv m f x ((i, a, z), y) = ((i, a, z + m i • f x a), y) := by
  simp [circuitEquiv, copyEquiv, smul_add]
  abel

/-- The entire permutation is weighted lookup tensored with scratch identity. -/
theorem circuitEquiv_eq (m : I → ℤ) (f : X → A → Z) (x : X) :
    circuitEquiv m f x = Equiv.prodCongr (signedEquiv m f x) (Equiv.refl Z) := by
  apply Equiv.ext
  rintro ⟨⟨i, a, z⟩, y⟩
  exact circuitEquiv_apply m f x i a z y

/-- Inverse execution also leaves every initial scratch value unchanged. -/
theorem circuitEquiv_symm_apply (m : I → ℤ) (f : X → A → Z) (x : X)
    (i : I) (a : A) (z y : Z) :
    (circuitEquiv m f x).symm ((i, a, z), y) =
      ((i, a, z - m i • f x a), y) := by
  rw [circuitEquiv_eq]
  rfl

/-- Integer representation of a Boolean active/inactive mask. -/
def maskWeight (m : I → Bool) (i : I) : ℤ := if m i then 1 else 0

/-- Lookup restricted to labels for which the fixed mask is active. -/
def maskedEquiv (m : I → Bool) (f : X → A → Z) (x : X) :
    Public I A Z ≃ Public I A Z := signedEquiv (maskWeight m) f x

@[simp] theorem maskedEquiv_apply (m : I → Bool) (f : X → A → Z) (x : X)
    (i : I) (a : A) (z : Z) :
    maskedEquiv m f x (i, a, z) = (i, a, z + if m i then f x a else 0) := by
  cases h : m i <;> simp [maskedEquiv, maskWeight, h]

/-- One signed mask can contain forward, inverse, and inactive labels. -/
def directionWeight (active inverse : I → Bool) (i : I) : ℤ :=
  if active i then (if inverse i then -1 else 1) else 0

/-- The weighted lookup has the expected three-way controlled action. -/
theorem directionEquiv_apply (active inverse : I → Bool) (f : X → A → Z) (x : X)
    (i : I) (a : A) (z : Z) :
    signedEquiv (directionWeight active inverse) f x (i, a, z) =
      (i, a, z + if active i then (if inverse i then -f x a else f x a) else 0) := by
  cases ha : active i <;> cases hi : inverse i <;>
    simp [directionWeight, ha, hi]

end Permutations

section QueryProgram
variable {X I A Z : Type*} [Fintype I] [Fintype A] [Fintype Z] [AddCommGroup Z]

/-- The common oracle interface, independent of every mask. -/
def oracle (f : X → A → Z) (x : X) :
    EuclideanSpace ℂ (Workspace I A Z) →L[ℂ] EuclideanSpace ℂ (Workspace I A Z) :=
  (permutationUnitary (computeEquiv f x)).toLinearIsometry.toContinuousLinearMap

/-- The concrete weighted-lookup circuit. -/
def circuit (m : I → ℤ) (f : X → A → Z) (x : X) :
    EuclideanSpace ℂ (Workspace I A Z) →L[ℂ] EuclideanSpace ℂ (Workspace I A Z) :=
  (permutationUnitary (circuitEquiv m f x)).toLinearIsometry.toContinuousLinearMap

/-- Both unitary identities for the common ordinary-lookup oracle. -/
theorem oracle_unitary (f : X → A → Z) (x : X) :
    OracleCircuit.IsUnitary (oracle (I := I) f x) :=
  permutationUnitary_unitary (computeEquiv f x)

/-- Both unitary identities for the complete weighted-lookup circuit. -/
theorem circuit_unitary (m : I → ℤ) (f : X → A → Z) (x : X) :
    OracleCircuit.IsUnitary (circuit m f x) :=
  permutationUnitary_unitary (circuitEquiv m f x)

/-- Two ordinary queries and two table-independent weighted-copy gates. -/
theorem circuit_factorization (m : I → ℤ) (f : X → A → Z) (x : X) :
    circuit m f x =
      (permutationUnitary (copyEquiv (A := A) (Z := Z) m).symm).toLinearIsometry.toContinuousLinearMap *
      star (oracle f x) *
      (permutationUnitary (copyEquiv (A := A) (Z := Z) m)).toLinearIsometry.toContinuousLinearMap *
      oracle f x := by
  unfold oracle
  rw [ContinuousLinearMap.star_eq_adjoint, permutationUnitary_adjoint,
    ← permutationUnitary_symm]
  ext v w
  rfl

/-- Every known mask is implemented using the same two-query oracle interface. -/
theorem circuit_two_queries (m : I → ℤ) (f : X → A → Z) :
    OracleCircuit.Implements (oracle f) (circuit m f) 2 := by
  have hc := OracleCircuit.Implements.fixed
    (O := oracle f) (permutationUnitary (copyEquiv (A := A) (Z := Z) m)).toLinearIsometry.toContinuousLinearMap
    (permutationUnitary_unitary (copyEquiv (A := A) (Z := Z) m))
  have hi := OracleCircuit.Implements.fixed
    (O := oracle f) (permutationUnitary (copyEquiv (A := A) (Z := Z) m).symm).toLinearIsometry.toContinuousLinearMap
    (permutationUnitary_unitary (copyEquiv (A := A) (Z := Z) m).symm)
  have h := ((hi.mul OracleCircuit.Implements.queryAdjoint).mul hc).mul
    OracleCircuit.Implements.query
  exact h.congr fun x => (circuit_factorization m f x).symm

/-- Exact operator identity on arbitrary, possibly entangled scratch states. -/
theorem circuit_eq_signed (m : I → ℤ) (f : X → A → Z) (x : X) :
    circuit m f x = (permutationUnitary
      (Equiv.prodCongr (signedEquiv m f x) (Equiv.refl Z))).toLinearIsometry.toContinuousLinearMap := by
  unfold circuit
  rw [circuitEquiv_eq]

/-- Weighted lookup tensored with scratch identity costs two common-oracle calls. -/
theorem signed_two_queries (m : I → ℤ) (f : X → A → Z) :
    OracleCircuit.Implements (oracle f) (fun x => (permutationUnitary
      (Equiv.prodCongr (signedEquiv m f x) (Equiv.refl Z))).toLinearIsometry.toContinuousLinearMap) 2 :=
  (circuit_two_queries m f).congr (circuit_eq_signed m f)

/-- Boolean masks of any finite spectator register cost two ordinary queries. -/
theorem masked_two_queries (m : I → Bool) (f : X → A → Z) :
    OracleCircuit.Implements (oracle f) (fun x => (permutationUnitary
      (Equiv.prodCongr (maskedEquiv m f x) (Equiv.refl Z))).toLinearIsometry.toContinuousLinearMap) 2 :=
  signed_two_queries (maskWeight m) f

/-- Forward, inverse, and inactive clock locations share one two-query circuit. -/
theorem direction_two_queries (active inverse : I → Bool) (f : X → A → Z) :
    OracleCircuit.Implements (oracle f) (fun x => (permutationUnitary
      (Equiv.prodCongr (signedEquiv (directionWeight active inverse) f x)
        (Equiv.refl Z))).toLinearIsometry.toContinuousLinearMap) 2 :=
  signed_two_queries (directionWeight active inverse) f

/-- Rewiring exposes the literal ordinary lookup, with label and target spectators. -/
theorem oracle_rewiring (f : X → A → Z) (x : X) :
    oracle (I := I) f x =
      (permutationUnitary (scratchWiring (I := I) (A := A) (Z := Z)).symm).toLinearIsometry.toContinuousLinearMap ∘L
      (permutationUnitary (spectatorEquiv (I × Z) f x)).toLinearIsometry.toContinuousLinearMap ∘L
      (permutationUnitary (scratchWiring (I := I) (A := A) (Z := Z))).toLinearIsometry.toContinuousLinearMap := by
  ext v w
  rfl

variable [DecidableEq Z]

/-- Clean-scratch correctness follows from the stronger full-space equality. -/
theorem circuit_clean (m : I → ℤ) (f : X → A → Z) (x : X) :
    circuit m f x ∘L
      (ControlledLookup.cleanEmbedding (B := Public I A Z) (Z := Z)).toContinuousLinearMap =
      (ControlledLookup.cleanEmbedding (B := Public I A Z) (Z := Z)).toContinuousLinearMap ∘L
        (permutationUnitary (signedEquiv m f x)).toLinearIsometry.toContinuousLinearMap := by
  ext v w
  rcases w with ⟨⟨i, a, z⟩, y⟩
  change (if ((circuitEquiv m f x).symm ((i, a, z), y)).2 = 0 then
      v ((circuitEquiv m f x).symm ((i, a, z), y)).1 else 0) =
    if y = 0 then v ((signedEquiv m f x).symm (i, a, z)) else 0
  rw [circuitEquiv_symm_apply]
  rfl

end QueryProgram
end
end SparseHamiltonian.MaskedLookup
