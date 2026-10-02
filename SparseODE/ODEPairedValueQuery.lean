import SparseODE.ODETaggedCayley

/-!
# Two original table entries with four counted value queries

The first value word is a spectator of the physical oracle. A fixed routing
exchanges the two words and applies a known address equivalence. Thus both
entries are obtained from the same original table, including the transposed
entry when the equivalence swaps the two matrix indices. No derived value
oracle and no input-dependent free gate is introduced.
-/

namespace SparseHamiltonian.ODEPairedValueQuery

noncomputable section
open ContinuousLinearMap OracleCircuit
open scoped InnerProduct

variable {X A Z K : Type*} [Fintype A] [Fintype Z] [AddCommGroup Z]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

abbrev Space (A Z K : Type*) := PiLp 2 (fun _ : (A × Z) × Z => K)
abbrev Public (A K : Type*) := PiLp 2 (fun _ : A => K)

/-- One ordinary value query, with the first value word untouched. -/
def oracle (f : X → A → Z) (x : X) : Space A Z K →L[ℂ] Space A Z K :=
  LookupControlledGate.oracle (K := K) (fun x az => f x az.1) x

omit [CompleteSpace K] in
@[simp] theorem oracle_apply (f : X → A → Z) (x : X)
    (v : Space A Z K) (a : A) (u z : Z) :
    oracle f x v ((a, u), z) = v ((a, u), z - f x a) := rfl

@[simp] theorem oracle_adjoint_apply (f : X → A → Z) (x : X)
    (v : Space A Z K) (a : A) (u z : Z) :
    ((oracle f x)†) v ((a, u), z) = v ((a, u), z + f x a) :=
  LookupControlledGate.oracle_adjoint_apply _ x v (a, u) z

theorem oracle_unitary (f : X → A → Z) (x : X) :
    IsUnitary (oracle (K := K) f x) :=
  LookupControlledGate.oracle_unitary _ x

/-- Known routing between the two value registers and the two addresses. -/
def routeBasis (e : A ≃ A) : ((A × Z) × Z) ≃ ((A × Z) × Z) where
  toFun w := ((e w.1.1, w.2), w.1.2)
  invFun w := ((e.symm w.1.1, w.2), w.1.2)
  left_inv w := by rcases w with ⟨⟨a, u⟩, z⟩; simp
  right_inv w := by rcases w with ⟨⟨a, u⟩, z⟩; simp

def routeEquiv (e : A ≃ A) : Space A Z K ≃ₗᵢ[ℂ] Space A Z K :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ K (routeBasis (Z := Z) e)

def route (e : A ≃ A) : Space A Z K →L[ℂ] Space A Z K :=
  (routeEquiv (Z := Z) (K := K) e).toLinearIsometry.toContinuousLinearMap

omit [AddCommGroup Z] [CompleteSpace K] in
@[simp] theorem route_apply (e : A ≃ A) (v : Space A Z K) (a : A) (u z : Z) :
    route e v ((a, u), z) = v ((e.symm a, z), u) := rfl

omit [AddCommGroup Z] in
@[simp] theorem route_adjoint_apply (e : A ≃ A) (v : Space A Z K)
    (a : A) (u z : Z) :
    ((route e)†) v ((a, u), z) = v ((e a, z), u) := by
  have h := congrArg
    (fun F : Space A Z K →L[ℂ] Space A Z K =>
      F ((routeEquiv (Z := Z) (K := K) e).symm v))
    (routeEquiv (Z := Z) (K := K) e).toLinearIsometry.adjoint_comp_self
  change ((route e)†) ((routeEquiv e) ((routeEquiv e).symm v)) =
    (routeEquiv e).symm v at h
  rw [LinearIsometryEquiv.apply_symm_apply] at h
  rw [h]
  simp only [routeEquiv, LinearIsometryEquiv.piLpCongrLeft_symm]
  rfl

omit [AddCommGroup Z] in
theorem route_unitary (e : A ≃ A) : IsUnitary (route (Z := Z) (K := K) e) := by
  constructor
  · exact (routeEquiv (Z := Z) (K := K) e).toLinearIsometry.adjoint_comp_self
  · change route (Z := Z) (K := K) e ∘L (route (Z := Z) (K := K) e)† = 1
    ext v w
    rcases w with ⟨⟨a, u⟩, z⟩
    simp only [comp_apply, route_apply, route_adjoint_apply,
      Equiv.apply_symm_apply, one_def, id_apply]

/-- Query-free register regrouping identifies our primitive with the original
address/value lookup and a larger untouched Hilbert payload. -/
def payloadLayout : Space A Z K ≃ₗᵢ[ℂ]
    PiLp 2 (fun _ : A × Z => PiLp 2 (fun _ : Z => K)) :=
  (routeEquiv (Z := Z) (K := K) (Equiv.refl A)).trans
    ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ K
      (Equiv.sigmaEquivProd (A × Z) Z).symm).trans
      (LinearIsometryEquiv.piLpCurry ℂ 2 (fun (_ : A × Z) (_ : Z) => K)))

omit [AddCommGroup Z] [CompleteSpace K] in
@[simp] theorem payloadLayout_apply (v : Space A Z K) (a : A) (u z : Z) :
    payloadLayout v (a, z) u = v ((a, u), z) := rfl

omit [CompleteSpace K] in
/-- The single counted primitive is exactly the original table oracle, with
one spectator register; its address is still `A`, not a pair of table entries. -/
theorem oracle_original_intertwines (f : X → A → Z) (x : X) :
    (payloadLayout (A := A) (Z := Z) (K := K)).toLinearIsometry.toContinuousLinearMap
        ∘L oracle f x =
      LookupControlledGate.oracle (K := PiLp 2 (fun _ : Z => K)) f x ∘L
        (payloadLayout (A := A) (Z := Z) (K := K)).toLinearIsometry.toContinuousLinearMap := by
  ext v az u
  rcases az with ⟨a, z⟩
  rfl

/-- The routed query computes the other entry in the first value word. -/
def routedOracle (e : A ≃ A) (f : X → A → Z) (x : X) :
    Space A Z K →L[ℂ] Space A Z K :=
  (route e)† ∘L oracle f x ∘L route e

@[simp] theorem routedOracle_apply (e : A ≃ A) (f : X → A → Z) (x : X)
    (v : Space A Z K) (a : A) (u z : Z) :
    routedOracle e f x v ((a, u), z) = v ((a, u - f x (e a)), z) := by
  simp only [routedOracle, comp_apply, route_adjoint_apply, oracle_apply,
    route_apply, Equiv.symm_apply_apply]

@[simp] theorem routedOracle_adjoint_apply (e : A ≃ A) (f : X → A → Z) (x : X)
    (v : Space A Z K) (a : A) (u z : Z) :
    ((routedOracle e f x)†) v ((a, u), z) = v ((a, u + f x (e a)), z) := by
  simp only [routedOracle, adjoint_comp, adjoint_adjoint, comp_apply,
    route_adjoint_apply, oracle_adjoint_apply, route_apply, Equiv.symm_apply_apply]

def routedProgram (e : A ≃ A) (f : X → A → Z) : Program (oracle (K := K) f) :=
  .seq (.fixed ((route e)†) (route_unitary e).adjoint)
    (.seq .query (.fixed (route e) (route_unitary e)))

theorem routedProgram_count (e : A ≃ A) (f : X → A → Z) :
    (routedProgram (K := K) e f).count = 1 := rfl

set_option maxHeartbeats 1000000 in
theorem routedProgram_eval (e : A ≃ A) (f : X → A → Z) (x : X) :
    (routedProgram (K := K) e f).eval x = routedOracle e f x := by
  simp only [routedProgram, Program.eval_seq, Program.eval_fixed,
    Program.eval_query, routedOracle, mul_def]

def compute (e : A ≃ A) (f : X → A → Z) (x : X) :
    Space A Z K →L[ℂ] Space A Z K :=
  routedOracle e f x ∘L oracle f x

@[simp] theorem compute_apply (e : A ≃ A) (f : X → A → Z) (x : X)
    (v : Space A Z K) (a : A) (u z : Z) :
    compute e f x v ((a, u), z) = v ((a, u - f x (e a)), z - f x a) := by
  simp only [compute, comp_apply, routedOracle_apply, oracle_apply]

@[simp] theorem compute_adjoint_apply (e : A ≃ A) (f : X → A → Z) (x : X)
    (v : Space A Z K) (a : A) (u z : Z) :
    ((compute e f x)†) v ((a, u), z) = v ((a, u + f x (e a)), z + f x a) := by
  simp only [compute, adjoint_comp, comp_apply, oracle_adjoint_apply,
    routedOracle_adjoint_apply]

def computeProgram (e : A ≃ A) (f : X → A → Z) : Program (oracle (K := K) f) :=
  .seq (routedProgram e f) .query

theorem computeProgram_count (e : A ≃ A) (f : X → A → Z) :
    (computeProgram (K := K) e f).count = 2 := rfl

theorem computeProgram_eval (e : A ≃ A) (f : X → A → Z) (x : X) :
    (computeProgram (K := K) e f).eval x = compute e f x := by
  simp only [computeProgram, Program.eval_seq, routedProgram_eval,
    Program.eval_query, compute, mul_def]

def controlled (G : A → Z → Z → K →L[ℂ] K) :
    Space A Z K →L[ℂ] Space A Z K :=
  LookupControlledGate.controlled (fun az z => G az.1 az.2 z)

omit [Fintype A] [Fintype Z] [AddCommGroup Z] [CompleteSpace K] in
@[simp] theorem controlled_apply (G : A → Z → Z → K →L[ℂ] K)
    (v : Space A Z K) (a : A) (u z : Z) :
    controlled G v ((a, u), z) = G a u z (v ((a, u), z)) := rfl

omit [AddCommGroup Z] in
theorem controlled_unitary (G : A → Z → Z → K →L[ℂ] K)
    (hG : ∀ a u z, IsUnitary (G a u z)) : IsUnitary (controlled G) :=
  LookupControlledGate.controlled_unitary _ (fun az z => hG az.1 az.2 z)

def logical (e : A ≃ A) (G : A → Z → Z → K →L[ℂ] K)
    (f : X → A → Z) (x : X) : Public A K →L[ℂ] Public A K :=
  WeightedClock.diagonal (fun a => G a (f x (e a)) (f x a))

omit [Fintype A] [Fintype Z] [AddCommGroup Z] [CompleteSpace K] in
@[simp] theorem logical_apply (e : A ≃ A) (G : A → Z → Z → K →L[ℂ] K)
    (f : X → A → Z) (x : X) (v : Public A K) (a : A) :
    logical e G f x v a = G a (f x (e a)) (f x a) (v a) := rfl

/-- Compute both words, rotate by their known decoded values, and uncompute. -/
def circuit (e : A ≃ A) (G : A → Z → Z → K →L[ℂ] K)
    (f : X → A → Z) (x : X) : Space A Z K →L[ℂ] Space A Z K :=
  (compute e f x)† ∘L controlled G ∘L compute e f x

@[simp] theorem circuit_apply (e : A ≃ A) (G : A → Z → Z → K →L[ℂ] K)
    (f : X → A → Z) (x : X) (v : Space A Z K) (a : A) (u z : Z) :
    circuit e G f x v ((a, u), z) =
      G a (u + f x (e a)) (z + f x a) (v ((a, u), z)) := by
  simp only [circuit, comp_apply, compute_adjoint_apply, controlled_apply,
    compute_apply, add_sub_cancel_right]

/-- All free gates depend on the known routing and decoded gate table only. -/
def program (e : A ≃ A) (G : A → Z → Z → K →L[ℂ] K)
    (hG : ∀ a u z, IsUnitary (G a u z)) (f : X → A → Z) :
    Program (oracle (K := K) f) :=
  .seq (computeProgram e f).adjoint
    (.seq (.fixed (controlled G) (controlled_unitary G hG)) (computeProgram e f))

/-- Exactly four original value calls, independently of precision and size. -/
theorem program_count (e : A ≃ A) (G : A → Z → Z → K →L[ℂ] K)
    (hG : ∀ a u z, IsUnitary (G a u z)) (f : X → A → Z) :
    (program e G hG f).count = 4 := by
  simp only [program, Program.count_seq, Program.count_adjoint,
    Program.count_fixed, computeProgram_count]

theorem program_eval (e : A ≃ A) (G : A → Z → Z → K →L[ℂ] K)
    (hG : ∀ a u z, IsUnitary (G a u z)) (f : X → A → Z) (x : X) :
    (program e G hG f).eval x = circuit e G f x := by
  simp only [program, Program.eval_seq, Program.eval_adjoint,
    Program.eval_fixed, computeProgram_eval]
  change (compute e f x)† ∘L (controlled G ∘L compute e f x) = _
  exact (comp_assoc _ _ _).symm

theorem circuit_unitary (e : A ≃ A) (G : A → Z → Z → K →L[ℂ] K)
    (hG : ∀ a u z, IsUnitary (G a u z)) (f : X → A → Z) (x : X) :
    IsUnitary (circuit e G f x) := by
  rw [← program_eval e G hG f x]
  exact (program e G hG f).eval_unitary (oracle_unitary f) x

variable [DecidableEq Z]

/-- Both value registers have one fixed clean initial and final state. -/
def clean : Public A K →ₗᵢ[ℂ] Space A Z K :=
  (CleanValueEmbedding.embedding (I := A × Z) (K := K) (0 : Z)).comp
    (CleanValueEmbedding.embedding (I := A) (K := K) (0 : Z))

omit [CompleteSpace K] in
@[simp] theorem clean_apply (v : Public A K) (a : A) (u z : Z) :
    clean (Z := Z) v ((a, u), z) = if z = 0 then if u = 0 then v a else 0 else 0 := rfl

theorem clean_isometry :
    (clean (A := A) (Z := Z) (K := K)).toContinuousLinearMap† ∘L
      (clean (A := A) (Z := Z) (K := K)).toContinuousLinearMap = 1 :=
  LinearIsometry.adjoint_comp_self _

/-- Exact coherent clean-subspace correctness, with no garbage depending on
the matrix entry or the initial payload state. -/
theorem circuit_intertwines (e : A ≃ A) (G : A → Z → Z → K →L[ℂ] K)
    (f : X → A → Z) (x : X) :
    circuit e G f x ∘L (clean (A := A) (Z := Z) (K := K)).toContinuousLinearMap =
      (clean (A := A) (Z := Z) (K := K)).toContinuousLinearMap ∘L logical e G f x := by
  ext v w
  rcases w with ⟨⟨a, u⟩, z⟩
  change circuit e G f x (clean v) ((a, u), z) =
    clean (logical e G f x v) ((a, u), z)
  rw [circuit_apply, clean_apply, clean_apply, logical_apply]
  by_cases hz : z = 0 <;> by_cases hu : u = 0 <;> simp [hz, hu]

theorem program_intertwines (e : A ≃ A) (G : A → Z → Z → K →L[ℂ] K)
    (hG : ∀ a u z, IsUnitary (G a u z)) (f : X → A → Z) (x : X) :
    (program e G hG f).eval x ∘L
        (clean (A := A) (Z := Z) (K := K)).toContinuousLinearMap =
      (clean (A := A) (Z := Z) (K := K)).toContinuousLinearMap ∘L logical e G f x := by
  rw [program_eval]
  exact circuit_intertwines e G f x

/-- Counted implementation certificate over the same original value family. -/
theorem implementsOn (e : A ≃ A) (G : A → Z → Z → K →L[ℂ] K)
    (hG : ∀ a u z, IsUnitary (G a u z)) (f : X → A → Z) :
    EncodedOracle.ImplementsOn (oracle (K := K) f) (logical e G f)
      (clean (A := A) (Z := Z) (K := K)).toContinuousLinearMap 4 :=
  ⟨program e G hG f, program_intertwines e G hG f, by rw [program_count]⟩

end
end SparseHamiltonian.ODEPairedValueQuery
