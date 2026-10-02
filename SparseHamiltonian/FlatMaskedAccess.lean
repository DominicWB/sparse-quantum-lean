import SparseHamiltonian.OrientedNativeValue

/-!
# Flat native access after Boolean masking

This is only a coordinate change of the original spectator query family.
The basis-image witness is inherited from the verified native layout; no
controlled query or coherent choice of native label is added to the model.
-/
namespace SparseHamiltonian.FlatMaskedAccess

noncomputable section
open ContinuousLinearMap OracleCircuit
open scoped InnerProduct
set_option maxRecDepth 2000
set_option maxHeartbeats 1000000

variable {B X L M : Type*} [Fintype B] [DecidableEq B]

abbrev Basis (B : Type*) := NativeDilationLayout.Basis B

/-- The existing native layout flattens the Boolean and spectator registers. -/
abbrev layout : NativeMaskedOracle.Physical Bool B ≃ₗᵢ[ℂ]
    EuclideanSpace ℂ (Basis B) := NativeDilationLayout.layout

/-- Literal original native queries with untouched spectator registers. -/
abbrev flatOracle (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B) :=
  NativeDilationLayout.oracle F

abbrev cleanBasis (a : B) : Basis B := NativeDilationLayout.cleanBasis a
abbrev imageBasis (a b : B) : Basis B := NativeDilationLayout.imageBasis a b

omit [DecidableEq B] in
theorem flatOracle_unitary
    (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (hF : ∀ l x, IsUnitary (F l x)) (l : L) (x : X) :
    IsUnitary (flatOracle F l x) :=
  NativeDilationLayout.oracle_unitary F hF l x

/-- A common computational input remains valid after the spectator extension. -/
theorem valid
    (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (a : B) (image : L → X → B)
    (hvalid : ∀ l x, F l x (EuclideanSpace.single a 1) =
      EuclideanSpace.single (image l x) 1) (l : L) (x : X) :
    flatOracle F l x (EuclideanSpace.single (cleanBasis a) 1) =
      EuclideanSpace.single (imageBasis a (image l x)) 1 :=
  NativeDilationLayout.valid F a image hvalid l x

/-- Flatten any already compiled native program, preserving every call. -/
def flatten (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (p : MultiOracleCircuit.Program (NativeMaskedProgram.oracle (ι := Bool) F)) :
    MultiOracleCircuit.Program (flatOracle F) := by
  let q := MultiOracleCircuit.Program.transport
    (H := NativeMaskedOracle.Physical Bool B) (K := EuclideanSpace ℂ (Basis B))
    (O := NativeMaskedProgram.oracle (ι := Bool) F) layout p
  with_reducible exact q

omit [DecidableEq B] in
@[simp] theorem flatten_count
    (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (p : MultiOracleCircuit.Program (NativeMaskedProgram.oracle (ι := Bool) F)) :
    (flatten F p).count = p.count := by simp [flatten]

omit [DecidableEq B] in
@[simp] theorem flatten_cost
    (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (p : MultiOracleCircuit.Program (NativeMaskedProgram.oracle (ι := Bool) F))
    (w : L → ℕ) : (flatten F p).cost w = p.cost w := by simp [flatten]

omit [DecidableEq B] in
@[simp] theorem flatten_labelCount [DecidableEq L]
    (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (p : MultiOracleCircuit.Program (NativeMaskedProgram.oracle (ι := Bool) F))
    (l : L) : (flatten F p).labelCount l = p.labelCount l := flatten_cost F p _

omit [DecidableEq B] in
@[simp] theorem flatten_eval
    (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (p : MultiOracleCircuit.Program (NativeMaskedProgram.oracle (ι := Bool) F))
    (x : X) : (flatten F p).eval x = layout.conjStarAlgEquiv (p.eval x) := by
  simp only [flatten, MultiOracleCircuit.Program.eval_transport]

omit [DecidableEq B] in
theorem flatten_unitary
    (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (hF : ∀ l x, IsUnitary (F l x))
    (p : MultiOracleCircuit.Program (NativeMaskedProgram.oracle (ι := Bool) F))
    (x : X) : IsUnitary ((flatten F p).eval x) :=
  (flatten F p).eval_unitary (flatOracle_unitary F hF) x

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- Transport an arbitrary clean encoding through the fixed layout. -/
def embedding (e : V →ₗᵢ[ℂ] NativeMaskedOracle.Physical Bool B) :
    V →ₗᵢ[ℂ] EuclideanSpace ℂ (Basis B) := layout.toLinearIsometry.comp e

omit [CompleteSpace V] [DecidableEq B] in
/-- Exact clean action is preserved by flattening, without any query cost. -/
theorem flatten_intertwines
    (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (p : MultiOracleCircuit.Program (NativeMaskedProgram.oracle (ι := Bool) F))
    (e : V →ₗᵢ[ℂ] NativeMaskedOracle.Physical Bool B)
    (U : V →L[ℂ] V) (x : X)
    (h : p.eval x ∘L e.toContinuousLinearMap = e.toContinuousLinearMap ∘L U) :
    (flatten F p).eval x ∘L (embedding e).toContinuousLinearMap =
      (embedding e).toContinuousLinearMap ∘L U := by
  rw [flatten_eval]
  apply ContinuousLinearMap.ext
  intro v
  change layout (p.eval x (layout.symm (layout (e v)))) = layout (e (U v))
  rw [LinearIsometryEquiv.symm_apply_apply]
  exact congrArg layout (congrArg
    (fun A : V →L[ℂ] NativeMaskedOracle.Physical Bool B => A v) h)

/-- The same clean Boolean preparation in the flattened computational basis. -/
def input (a : B) : NativeMaskedOracle.Logical Bool B →ₗᵢ[ℂ]
    EuclideanSpace ℂ (Basis B) := embedding (NativeMaskedOracle.input (ι := Bool) a)

/-- Compile a masked program and flatten its workspace in a single definition. -/
def program (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (a : B) (label : M → L) (active : M → Bool → Bool)
    (p : MultiOracleCircuit.Program (NativeMaskedProgram.logicalOracle F label active)) :
    MultiOracleCircuit.Program (flatOracle F) :=
  flatten F (NativeMaskedProgram.compile F a label active p)

@[simp] theorem program_count
    (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (a : B) (label : M → L) (active : M → Bool → Bool)
    (p : MultiOracleCircuit.Program (NativeMaskedProgram.logicalOracle F label active)) :
    (program F a label active p).count = p.count * 3 := by simp [program]

@[simp] theorem program_cost
    (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (a : B) (label : M → L) (active : M → Bool → Bool)
    (p : MultiOracleCircuit.Program (NativeMaskedProgram.logicalOracle F label active))
    (w : L → ℕ) :
    (program F a label active p).cost w = p.cost (fun m => 3 * w (label m)) := by
  simp [program]

theorem program_intertwines
    (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (hF : ∀ l x, IsUnitary (F l x)) (a : B) (image : L → X → B)
    (hvalid : ∀ l x, F l x (EuclideanSpace.single a 1) =
      EuclideanSpace.single (image l x) 1)
    (label : M → L) (active : M → Bool → Bool)
    (p : MultiOracleCircuit.Program (NativeMaskedProgram.logicalOracle F label active))
    (x : X) :
    (program F a label active p).eval x ∘L (input a).toContinuousLinearMap =
      (input a).toContinuousLinearMap ∘L p.eval x :=
  flatten_intertwines F (NativeMaskedProgram.compile F a label active p)
    (NativeMaskedOracle.input (ι := Bool) a) (p.eval x) x
    (NativeMaskedProgram.compile_eval F hF a image hvalid label active p x)

end
end SparseHamiltonian.FlatMaskedAccess
