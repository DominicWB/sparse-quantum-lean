import SparseHamiltonian.InPlaceFromLookup

/-!
# Two-query table-controlled payload operations

A finite additive lookup computes a table entry into a clean value register.
One fixed gate controlled by the address and value acts on a Hilbert payload;
the inverse lookup restores the value register. The gate table is fixed across
all unknown inputs, and only the reversible lookup carries input dependence.
-/

namespace SparseHamiltonian.LookupControlledGate

noncomputable section
open ContinuousLinearMap OracleCircuit
open scoped InnerProduct

variable {X A Z K : Type*} [Fintype A] [Fintype Z] [AddCommGroup Z]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The value lookup with an arbitrary untouched Hilbert payload. -/
def oracleEquiv (f : X → A → Z) (x : X) :
    PiLp 2 (fun _ : A × Z => K) ≃ₗᵢ[ℂ] PiLp 2 (fun _ : A × Z => K) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ K (LookupOracle.basisEquiv f x)

/-- Ordinary addition lookup, represented on address, value, and payload. -/
def oracle (f : X → A → Z) (x : X) :
    PiLp 2 (fun _ : A × Z => K) →L[ℂ] PiLp 2 (fun _ : A × Z => K) :=
  (oracleEquiv f x).toLinearIsometry.toContinuousLinearMap

omit [CompleteSpace K] in
@[simp] theorem oracle_apply (f : X → A → Z) (x : X)
    (v : PiLp 2 (fun _ : A × Z => K)) (a : A) (z : Z) :
    oracle f x v (a, z) = v (a, z - f x a) := rfl

/-- The inverse lookup subtracts the value on kets and hence adds it in amplitudes. -/
@[simp] theorem oracle_adjoint_apply (f : X → A → Z) (x : X)
    (v : PiLp 2 (fun _ : A × Z => K)) (a : A) (z : Z) :
    ((oracle f x)†) v (a, z) = v (a, z + f x a) := by
  have h := congrArg
    (fun F : PiLp 2 (fun _ : A × Z => K) →L[ℂ] PiLp 2 (fun _ : A × Z => K) =>
      F ((oracleEquiv f x).symm v))
    (oracleEquiv (K := K) f x).toLinearIsometry.adjoint_comp_self
  change ((oracle f x)†) ((oracleEquiv f x) ((oracleEquiv f x).symm v)) =
    (oracleEquiv f x).symm v at h
  rw [LinearIsometryEquiv.apply_symm_apply] at h
  rw [h]
  simp only [oracleEquiv, LinearIsometryEquiv.piLpCongrLeft_symm]
  rfl

/-- This query primitive is a concrete two-sided unitary. -/
theorem oracle_unitary (f : X → A → Z) (x : X) :
    IsUnitary (oracle (K := K) f x) := by
  constructor
  · exact (oracleEquiv (K := K) f x).toLinearIsometry.adjoint_comp_self
  · change oracle (K := K) f x ∘L (oracle (K := K) f x)† = 1
    ext v az
    rcases az with ⟨a, z⟩
    simp only [comp_apply, oracle_apply, oracle_adjoint_apply, sub_add_cancel,
      one_def, id_apply]

/-- The value-controlled payload gate is a single fixed operator. -/
def controlled (G : A → Z → K →L[ℂ] K) :
    PiLp 2 (fun _ : A × Z => K) →L[ℂ] PiLp 2 (fun _ : A × Z => K) :=
  WeightedClock.diagonal (fun az => G az.1 az.2)

omit [CompleteSpace K] [Fintype A] [Fintype Z] [AddCommGroup Z] in
@[simp] theorem controlled_apply (G : A → Z → K →L[ℂ] K)
    (v : PiLp 2 (fun _ : A × Z => K)) (a : A) (z : Z) :
    controlled G v (a, z) = G a z (v (a, z)) := rfl

omit [AddCommGroup Z] in
/-- A fixed family of unitary payload gates is a legal fixed controlled gate. -/
theorem controlled_unitary (G : A → Z → K →L[ℂ] K)
    (hG : ∀ a z, IsUnitary (G a z)) : IsUnitary (controlled G) := by
  constructor
  · exact WeightedClock.diagonal_isometry _ (fun az => (hG az.1 az.2).1)
  · change controlled G ∘L (controlled G)† = 1
    unfold controlled
    rw [WeightedClock.diagonal_adjoint, WeightedClock.diagonal_comp]
    have hh (az : A × Z) : G az.1 az.2 ∘L (G az.1 az.2)† = 1 := (hG az.1 az.2).2
    simp only [hh, WeightedClock.diagonal_one]

/-- The desired logical operation uses the looked-up table entry at each address. -/
def logical (G : A → Z → K →L[ℂ] K) (f : X → A → Z) (x : X) :
    PiLp 2 (fun _ : A => K) →L[ℂ] PiLp 2 (fun _ : A => K) :=
  WeightedClock.diagonal (fun a => G a (f x a))

omit [CompleteSpace K] [Fintype A] [Fintype Z] [AddCommGroup Z] in
@[simp] theorem logical_apply (G : A → Z → K →L[ℂ] K) (f : X → A → Z) (x : X)
    (v : PiLp 2 (fun _ : A => K)) (a : A) :
    logical G f x v a = G a (f x a) (v a) := rfl

omit [Fintype Z] [AddCommGroup Z] in
/-- The desired logical action is unitary when all fixed payload gates are. -/
theorem logical_unitary (G : A → Z → K →L[ℂ] K)
    (hG : ∀ a z, IsUnitary (G a z)) (f : X → A → Z) (x : X) :
    IsUnitary (logical G f x) := by
  constructor
  · exact WeightedClock.diagonal_isometry _ (fun a => (hG a (f x a)).1)
  · change logical G f x ∘L (logical G f x)† = 1
    unfold logical
    rw [WeightedClock.diagonal_adjoint, WeightedClock.diagonal_comp]
    have hh (a : A) : G a (f x a) ∘L (G a (f x a))† = 1 := (hG a (f x a)).2
    simp only [hh, WeightedClock.diagonal_one]

/-- Compute, apply the fixed controlled gate, and uncompute. -/
def circuit (G : A → Z → K →L[ℂ] K) (f : X → A → Z) (x : X) :
    PiLp 2 (fun _ : A × Z => K) →L[ℂ] PiLp 2 (fun _ : A × Z => K) :=
  (oracle f x)† ∘L controlled G ∘L oracle f x

/-- Exact action on every value-register state, before restricting to clean input. -/
@[simp] theorem circuit_apply (G : A → Z → K →L[ℂ] K) (f : X → A → Z) (x : X)
    (v : PiLp 2 (fun _ : A × Z => K)) (a : A) (z : Z) :
    circuit G f x v (a, z) = G a (z + f x a) (v (a, z)) := by
  simp only [circuit, comp_apply, oracle_adjoint_apply, controlled_apply,
    oracle_apply, add_sub_cancel_right]

/-- The fixed gate contains no unknown input instance. -/
def program (G : A → Z → K →L[ℂ] K) (hG : ∀ a z, IsUnitary (G a z))
    (f : X → A → Z) : Program (oracle (K := K) f) :=
  .seq .queryAdjoint (.seq (.fixed (controlled G) (controlled_unitary G hG)) .query)

/-- The actual program makes exactly two ordinary oracle calls. -/
theorem program_count (G : A → Z → K →L[ℂ] K) (hG : ∀ a z, IsUnitary (G a z))
    (f : X → A → Z) : (program G hG f).count = 2 := rfl

/-- Program evaluation is the concrete compute/controlled-gate/uncompute circuit. -/
theorem program_eval (G : A → Z → K →L[ℂ] K) (hG : ∀ a z, IsUnitary (G a z))
    (f : X → A → Z) (x : X) : (program G hG f).eval x = circuit G f x := by
  change (oracle f x)† ∘L (controlled G ∘L oracle f x) = _
  exact (comp_assoc _ _ _).symm

/-- The physical circuit is a two-sided unitary on all value-register states. -/
theorem circuit_unitary (G : A → Z → K →L[ℂ] K) (hG : ∀ a z, IsUnitary (G a z))
    (f : X → A → Z) (x : X) : IsUnitary (circuit G f x) := by
  rw [← program_eval G hG f x]
  exact (program G hG f).eval_unitary (oracle_unitary f) x

variable [DecidableEq Z]

/-- The computed table value is uncomputed exactly: the value register returns
to zero, while the payload receives the gate selected by the unknown entry. -/
theorem circuit_clean_apply (G : A → Z → K →L[ℂ] K) (f : X → A → Z) (x : X)
    (v : PiLp 2 (fun _ : A => K)) (a : A) (z : Z) :
    circuit G f x (CleanValueEmbedding.embedding (0 : Z) v) (a, z) =
      if z = 0 then G a (f x a) (v a) else 0 := by
  classical
  rw [circuit_apply, CleanValueEmbedding.embedding_apply]
  by_cases hz : z = 0
  · subst z
    simp
  · simp [hz]

/-- Correctness holds as an exact encoded operator identity, including coherent
superpositions of addresses and arbitrary payload states. -/
theorem circuit_intertwines (G : A → Z → K →L[ℂ] K) (f : X → A → Z) (x : X) :
    circuit G f x ∘L (CleanValueEmbedding.embedding (I := A) (K := K) (0 : Z)).toContinuousLinearMap =
      (CleanValueEmbedding.embedding (I := A) (K := K) (0 : Z)).toContinuousLinearMap ∘L
        logical G f x := by
  ext v az
  rcases az with ⟨a, z⟩
  change circuit G f x (CleanValueEmbedding.embedding (0 : Z) v) (a, z) =
    CleanValueEmbedding.embedding (0 : Z) (logical G f x v) (a, z)
  rw [circuit_clean_apply, CleanValueEmbedding.embedding_apply, logical_apply]

/-- The explicit two-query program implements the desired logical gate on the
fixed clean-value encoding and returns the value register to that encoding. -/
theorem program_intertwines (G : A → Z → K →L[ℂ] K)
    (hG : ∀ a z, IsUnitary (G a z)) (f : X → A → Z) (x : X) :
    (program G hG f).eval x ∘L
      (CleanValueEmbedding.embedding (I := A) (K := K) (0 : Z)).toContinuousLinearMap =
      (CleanValueEmbedding.embedding (I := A) (K := K) (0 : Z)).toContinuousLinearMap ∘L
        logical G f x := by
  rw [program_eval]
  exact circuit_intertwines G f x

/-- A fixed finite table of payload unitaries can be selected by an unknown
lookup entry with exactly two calls, independently of address/value dimension. -/
theorem implementsOn (G : A → Z → K →L[ℂ] K)
    (hG : ∀ a z, IsUnitary (G a z)) (f : X → A → Z) :
    EncodedOracle.ImplementsOn (oracle (K := K) f) (logical G f)
      (CleanValueEmbedding.embedding (I := A) (K := K) (0 : Z)).toContinuousLinearMap 2 :=
  ⟨program G hG f, program_intertwines G hG f, by rw [program_count]⟩

end
end SparseHamiltonian.LookupControlledGate
