import SparseHamiltonian.NativeHermitianDilation

/-!
# A common computational basis for native Hermitian dilations

The query family after dilation is only the original query with spectator
registers. Its inherited fixed basis-image promise permits the native clock
compiler to use the same three-query masking construction again.
-/
namespace SparseHamiltonian.NativeDilationLayout

noncomputable section
open ContinuousLinearMap OracleCircuit
open scoped InnerProduct
set_option maxRecDepth 2000
set_option maxHeartbeats 800000

variable {B X L : Type*} [Fintype B] [DecidableEq B]

abbrev Basis (B : Type*) := Bool × NativeControlledOracle.Workspace B

/-- Flatten the physical Boolean branch and native spectator registers. -/
def layout : NativeMaskedOracle.Physical Bool B ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Basis B) :=
  RegisterEquivalences.productFlatten Bool (NativeControlledOracle.Workspace B)

/-- Original native labels act uniformly in every spectator sector. -/
abbrev oracle (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B) (l : L) (x : X) :
    EuclideanSpace ℂ (Basis B) →L[ℂ] EuclideanSpace ℂ (Basis B) :=
  (layout (B := B)).conjStarAlgEquiv (NativeHermitianDilation.oracle F l x)

/-- One fixed valid basis state for all native primitives. -/
def cleanBasis (a : B) : Basis B := (false, (((false, a), a), a))

/-- Only the payload basis label changes under a native query. -/
def imageBasis (a b : B) : Basis B := (false, (((false, a), a), b))

omit [DecidableEq B] in
/-- The spectator query family remains unitary on every basis sector. -/
theorem oracle_unitary (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (hF : ∀ l x, IsUnitary (F l x)) (l : L) (x : X) : IsUnitary (oracle F l x) :=
  (NativeMaskedOracle.oracle_unitary (F l) (hF l) x).transport layout

/-- Exact basis witnesses are inherited from the original primitives. -/
theorem valid (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (a : B) (image : L → X → B)
    (hvalid : ∀ l x, F l x (EuclideanSpace.single a 1) = EuclideanSpace.single (image l x) 1)
    (l : L) (x : X) :
    oracle F l x (EuclideanSpace.single (cleanBasis a) 1) =
      EuclideanSpace.single (imageBasis a (image l x)) 1 := by
  have hi : NativeControlledOracle.oracle (F l) x
      (EuclideanSpace.single (((false, a), a), a) 1) =
      EuclideanSpace.single (((false, a), a), image l x) 1 :=
    LookupFromBasisOracle.spectator_single (F l x) a (image l x) 1 (hvalid l x) ((false, a), a)
  ext ⟨b,w⟩
  change NativeControlledOracle.oracle (F l) x
    (WithLp.toLp 2 (fun q => (EuclideanSpace.single (cleanBasis a) (1 : ℂ)) (b,q))) w = _
  have hs : WithLp.toLp 2 (fun q : NativeControlledOracle.Workspace B =>
      (EuclideanSpace.single (cleanBasis a) (1 : ℂ)) (b,q)) =
      if b = false then EuclideanSpace.single (((false, a), a), a) 1 else 0 := by
    ext q
    cases b <;> simp [cleanBasis, Prod.ext_iff]
  rw [hs]
  cases b <;> simp [imageBasis, hi, Prod.ext_iff]

/-- Flatten the genuine native dilation without changing a single label or call. -/
def program (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (a : B) (p : MultiOracleCircuit.Program F) : MultiOracleCircuit.Program (oracle F) := by
  let q := MultiOracleCircuit.Program.transport
    (H := NativeMaskedOracle.Physical Bool B) (K := EuclideanSpace ℂ (Basis B))
    (O := NativeHermitianDilation.oracle F) layout (NativeHermitianDilation.program F a p)
  with_reducible exact q

@[simp] theorem program_count (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (a : B) (p : MultiOracleCircuit.Program F) : (program F a p).count = 6 * p.count := by
  simp [program]

@[simp] theorem program_cost (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (a : B) (p : MultiOracleCircuit.Program F) (w : L → ℕ) :
    (program F a p).cost w = 6 * p.cost w := by simp [program]

/-- Full-space unitarity in the register basis used by subsequent clocks. -/
theorem program_unitary (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (hF : ∀ l x, IsUnitary (F l x)) (a : B) (p : MultiOracleCircuit.Program F) (x : X) :
    IsUnitary ((program F a p).eval x) := by
  rw [program, MultiOracleCircuit.Program.eval_transport]
  exact (NativeHermitianDilation.program_unitary F hF a p x).transport layout

/-- The flattened native program remains exactly involutory everywhere. -/
theorem program_involution (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (hF : ∀ l x, IsUnitary (F l x)) (a : B) (p : MultiOracleCircuit.Program F) (x : X) :
    (program F a p).eval x ∘L (program F a p).eval x = 1 := by
  unfold program
  have h := MultiOracleCircuit.Program.involution_transport
    (H := NativeMaskedOracle.Physical Bool B) (K := EuclideanSpace ℂ (Basis B))
    (O := NativeHermitianDilation.oracle F) (layout (B := B))
    (NativeHermitianDilation.program F a p) x
    (NativeHermitianDilation.program_involution F hF a p x)
  simp only [mul_def] at h
  with_reducible exact h

/-- The exact self-adjointness identity is preserved in the flattened basis. -/
theorem program_selfAdjoint (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (a : B) (p : MultiOracleCircuit.Program F) (x : X) :
    ((program F a p).eval x)† = (program F a p).eval x := by
  unfold program
  have h := MultiOracleCircuit.Program.selfAdjoint_transport
    (H := NativeMaskedOracle.Physical Bool B) (K := EuclideanSpace ℂ (Basis B))
    (O := NativeHermitianDilation.oracle F) (layout (B := B))
    (NativeHermitianDilation.program F a p) x
    (NativeHermitianDilation.program_selfAdjoint F a p x)
  simp only [star_eq_adjoint] at h
  with_reducible exact h

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-- Public plus preparation and clean spectators in one computational basis. -/
def input (a : B) (E : P →L[ℂ] EuclideanSpace ℂ B) : P →L[ℂ] EuclideanSpace ℂ (Basis B) :=
  FlattenedLookupClockBounds.transportBoundary layout (NativeHermitianDilation.input a E)

theorem input_isometry (a : B) (E : P →L[ℂ] EuclideanSpace ℂ B) (hE : E† ∘L E = 1) :
    (input a E)† ∘L input a E = 1 := by
  unfold input
  have h := FlattenedLookupClockBounds.transportBoundary_isometry
    (P := P) (V := NativeMaskedOracle.Physical Bool B) (K := EuclideanSpace ℂ (Basis B))
    (layout (B := B)) (NativeHermitianDilation.input a E)
    (NativeHermitianDilation.input_isometry a E hE)
  with_reducible exact h

/-- Every Hermitian block is exactly preserved, with one common physical input. -/
theorem compression_eq (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (hF : ∀ l x, IsUnitary (F l x)) (a : B) (image : L → X → B)
    (hvalid : ∀ l x, F l x (EuclideanSpace.single a 1) = EuclideanSpace.single (image l x) 1)
    (p : MultiOracleCircuit.Program F) (E : P →L[ℂ] EuclideanSpace ℂ B) (x : X)
    (hH : (E† ∘L p.eval x ∘L E)† = E† ∘L p.eval x ∘L E) :
    (input a E)† ∘L (program F a p).eval x ∘L input a E = E† ∘L p.eval x ∘L E := by
  rw [program, MultiOracleCircuit.Program.eval_transport, input,
    FlattenedLookupClockBounds.transportBoundary_compression]
  exact NativeHermitianDilation.compression_eq F hF a image hvalid p E x hH

end
end SparseHamiltonian.NativeDilationLayout
