import SparseODE.ODENativeValue

/-!
# Flat native access with arbitrary finite branch registers

This extends the verified Boolean layout to all finite coherent branch labels.
Flattening is a fixed coordinate permutation, preserves every primitive query,
and inherits the common basis-image witness required for native masking.
-/

namespace SparseHamiltonian.FlatBranchNativeAccess

noncomputable section
open ContinuousLinearMap OracleCircuit
open scoped InnerProduct
set_option maxRecDepth 2000
set_option maxHeartbeats 1000000

variable {ι B X L M : Type*} [Fintype ι] [Fintype B] [DecidableEq B]

/-- The branch and three native control registers precede the payload. -/
abbrev Basis (ι B : Type*) := ι × NativeControlledOracle.Workspace B

/-- Fixed flattening for any finite coherent branch register. -/
def layout : NativeMaskedOracle.Physical ι B ≃ₗᵢ[ℂ]
    EuclideanSpace ℂ (Basis ι B) :=
  RegisterEquivalences.productFlatten ι (NativeControlledOracle.Workspace B)

/-- The original native query, with every branch and scratch register a spectator. -/
abbrev flatOracle
    (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B) (l : L) (x : X) :
    EuclideanSpace ℂ (Basis ι B) →L[ℂ] EuclideanSpace ℂ (Basis ι B) :=
  (layout (ι := ι) (B := B)).conjStarAlgEquiv
    (NativeMaskedProgram.oracle (ι := ι) F l x)

/-- The witness uses any chosen branch, rather than a Boolean-specific one. -/
def cleanBasis (i0 : ι) (a : B) : Basis ι B := (i0, (((false, a), a), a))

/-- The witness output changes only the queried payload. -/
def imageBasis (i0 : ι) (a b : B) : Basis ι B := (i0, (((false, a), a), b))

omit [DecidableEq B] in
/-- Flattening preserves both unitary identities on the entire workspace. -/
theorem flatOracle_unitary
    (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (hF : ∀ l x, IsUnitary (F l x)) (l : L) (x : X) :
    IsUnitary (flatOracle (ι := ι) F l x) :=
  (NativeMaskedOracle.oracle_unitary (ι := ι) (F l) (hF l) x).transport layout

/-- A common computational-basis witness survives all spectator registers.
The output witness is used only in the correctness proof, never as a gate. -/
theorem valid [DecidableEq ι]
    (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (i0 : ι) (a : B) (image : L → X → B)
    (hvalid : ∀ l x, F l x (EuclideanSpace.single a 1) =
      EuclideanSpace.single (image l x) 1) (l : L) (x : X) :
    flatOracle F l x (EuclideanSpace.single (cleanBasis i0 a) 1) =
      EuclideanSpace.single (imageBasis i0 a (image l x)) 1 := by
  classical
  have hi : NativeControlledOracle.oracle (F l) x
      (EuclideanSpace.single (((false, a), a), a) 1) =
      EuclideanSpace.single (((false, a), a), image l x) 1 :=
    LookupFromBasisOracle.spectator_single (F l x) a (image l x) 1
      (hvalid l x) ((false, a), a)
  apply PiLp.ext
  intro iw
  rcases iw with ⟨i, w⟩
  change NativeControlledOracle.oracle (F l) x
    (WithLp.toLp 2 (fun q =>
      (EuclideanSpace.single (cleanBasis i0 a) (1 : ℂ)) (i, q))) w = _
  have hs : WithLp.toLp 2 (fun q : NativeControlledOracle.Workspace B =>
      (EuclideanSpace.single (cleanBasis i0 a) (1 : ℂ)) (i, q)) =
      if i = i0 then EuclideanSpace.single (((false, a), a), a) 1 else 0 := by
    ext q
    by_cases h : i = i0 <;> simp [cleanBasis, Prod.ext_iff, h]
  rw [hs]
  by_cases h : i = i0 <;> simp [imageBasis, hi, Prod.ext_iff, h]

/-- Flatten any already compiled native program, preserving every call. -/
def flatten (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (p : MultiOracleCircuit.Program (NativeMaskedProgram.oracle (ι := ι) F)) :
    MultiOracleCircuit.Program (flatOracle (ι := ι) F) := by
  let q := MultiOracleCircuit.Program.transport
    (H := NativeMaskedOracle.Physical ι B) (K := EuclideanSpace ℂ (Basis ι B))
    (O := NativeMaskedProgram.oracle (ι := ι) F) layout p
  with_reducible exact q

omit [DecidableEq B] in
@[simp] theorem flatten_count
    (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (p : MultiOracleCircuit.Program (NativeMaskedProgram.oracle (ι := ι) F)) :
    (flatten F p).count = p.count := by simp [flatten]

omit [DecidableEq B] in
@[simp] theorem flatten_cost
    (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (p : MultiOracleCircuit.Program (NativeMaskedProgram.oracle (ι := ι) F))
    (w : L → ℕ) : (flatten F p).cost w = p.cost w := by simp [flatten]

omit [DecidableEq B] in
@[simp] theorem flatten_labelCount [DecidableEq L]
    (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (p : MultiOracleCircuit.Program (NativeMaskedProgram.oracle (ι := ι) F))
    (l : L) : (flatten F p).labelCount l = p.labelCount l := flatten_cost F p _

omit [DecidableEq B] in
@[simp] theorem flatten_eval
    (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (p : MultiOracleCircuit.Program (NativeMaskedProgram.oracle (ι := ι) F))
    (x : X) : (flatten F p).eval x = layout.conjStarAlgEquiv (p.eval x) := by
  simp only [flatten, MultiOracleCircuit.Program.eval_transport]

omit [DecidableEq B] in
theorem flatten_unitary
    (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (hF : ∀ l x, IsUnitary (F l x))
    (p : MultiOracleCircuit.Program (NativeMaskedProgram.oracle (ι := ι) F))
    (x : X) : IsUnitary ((flatten F p).eval x) :=
  (flatten F p).eval_unitary (flatOracle_unitary (ι := ι) F hF) x

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- Transport an arbitrary clean encoding through the fixed layout. -/
def embedding (e : V →ₗᵢ[ℂ] NativeMaskedOracle.Physical ι B) :
    V →ₗᵢ[ℂ] EuclideanSpace ℂ (Basis ι B) := layout.toLinearIsometry.comp e

omit [DecidableEq B] in
/-- The transported clean preparation is an isometry as a bounded operator. -/
theorem embedding_isometry (e : V →ₗᵢ[ℂ] NativeMaskedOracle.Physical ι B) :
    (embedding e).toContinuousLinearMap† ∘L (embedding e).toContinuousLinearMap = 1 :=
  (embedding e).toContinuousLinearMap.norm_map_iff_adjoint_comp_self.mp
    (embedding e).norm_map

omit [CompleteSpace V] [DecidableEq B] in
/-- Exact clean action is preserved by flattening, without any query cost. -/
theorem flatten_intertwines
    (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (p : MultiOracleCircuit.Program (NativeMaskedProgram.oracle (ι := ι) F))
    (e : V →ₗᵢ[ℂ] NativeMaskedOracle.Physical ι B)
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
    (fun A : V →L[ℂ] NativeMaskedOracle.Physical ι B => A v) h)

/-- The same clean branch preparation in the flattened computational basis. -/
def input (a : B) : NativeMaskedOracle.Logical ι B →ₗᵢ[ℂ]
    EuclideanSpace ℂ (Basis ι B) := embedding (NativeMaskedOracle.input (ι := ι) a)

/-- Compile a masked program and flatten its workspace in a single definition. -/
def program (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (a : B) (label : M → L) (active : M → ι → Bool)
    (p : MultiOracleCircuit.Program (NativeMaskedProgram.logicalOracle F label active)) :
    MultiOracleCircuit.Program (flatOracle (ι := ι) F) :=
  flatten F (NativeMaskedProgram.compile F a label active p)

@[simp] theorem program_count
    (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (a : B) (label : M → L) (active : M → ι → Bool)
    (p : MultiOracleCircuit.Program (NativeMaskedProgram.logicalOracle F label active)) :
    (program F a label active p).count = p.count * 3 := by simp [program]

@[simp] theorem program_cost
    (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (a : B) (label : M → L) (active : M → ι → Bool)
    (p : MultiOracleCircuit.Program (NativeMaskedProgram.logicalOracle F label active))
    (w : L → ℕ) :
    (program F a label active p).cost w = p.cost (fun m => 3 * w (label m)) := by
  simp [program]

theorem program_intertwines
    (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (hF : ∀ l x, IsUnitary (F l x)) (a : B) (image : L → X → B)
    (hvalid : ∀ l x, F l x (EuclideanSpace.single a 1) =
      EuclideanSpace.single (image l x) 1)
    (label : M → L) (active : M → ι → Bool)
    (p : MultiOracleCircuit.Program (NativeMaskedProgram.logicalOracle F label active))
    (x : X) :
    (program F a label active p).eval x ∘L (input a).toContinuousLinearMap =
      (input a).toContinuousLinearMap ∘L p.eval x :=
  flatten_intertwines F (NativeMaskedProgram.compile F a label active p)
    (NativeMaskedOracle.input (ι := ι) a) (p.eval x) x
    (NativeMaskedProgram.compile_eval F hF a image hvalid label active p x)

end
end SparseHamiltonian.FlatBranchNativeAccess
