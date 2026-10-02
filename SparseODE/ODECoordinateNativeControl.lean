import SparseODE.ODEFinalNativeBasis

/-!
# Primitive control on the original source-loading workspace

Fixed Euclidean coordinates and the tensor-sector encoding compose into one
clean input isometry. Each original matrix-sector letter is implemented by
three ordinary matrix queries, whereas each supplied controlled source call
retains one query. The basis-image hypothesis is a primitive-access property,
derived for the native ODE matrix family in `ODEFinalNativeBasis.valid`.
-/

namespace SparseHamiltonian.ODECoordinateNativeControl

noncomputable section
open ContinuousLinearMap OracleCircuit
open scoped InnerProduct BigOperators
set_option maxRecDepth 4096
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 2000000

variable {A B H K X L : Type*}
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (eA : H ≃ₗᵢ[ℂ] EuclideanSpace ℂ A) (eB : K ≃ₗᵢ[ℂ] EuclideanSpace ℂ B)

/-- Fixed coordinates followed by the common clean control encoding. -/
def input (a0 : A) (b0 : B) :
    ODESourceTransport.Space H K →L[ℂ] ODESectorTensor.Physical A B :=
  ODESectorTensor.input a0 b0 ∘L (ODESectorCoordinates.layout eA eB).toLinearIsometry.toContinuousLinearMap

theorem input_isometry (a0 : A) (b0 : B) :
    (input eA eB a0 b0)† ∘L input eA eB a0 b0 = 1 :=
  NativeSparseAttenuation.isometry_comp
    (A := ODESourceTransport.Space H K) (B := ODESectorTensor.Logical A B)
    (C := ODESectorTensor.Physical A B)
    (ODESectorCoordinates.layout eA eB).toLinearIsometry.toContinuousLinearMap
    (ODESectorTensor.input a0 b0)
    (ODESectorCoordinates.layout eA eB).toLinearIsometry.adjoint_comp_self
    (ODESectorTensor.input_isometry a0 b0)

variable (O : L → X → K →L[ℂ] K) (S : Bool → X → H →L[ℂ] H)

/-- Matrix calls are unconditional native payload calls with spectators.
The supplied source interface retains its supported controls. -/
abbrev physicalOracle :=
  ODESectorNativeControl.physicalOracle (fun l x => eB.conjStarAlgEquiv (O l x))
    (fun b x => eA.conjStarAlgEquiv (S b x))

def letter (b0 : B) (l : L ⊕ Bool) :
    MultiOracleCircuit.Program (physicalOracle eA eB O S) :=
  ODESectorNativeControl.letter (fun l x => eB.conjStarAlgEquiv (O l x))
    (fun b x => eA.conjStarAlgEquiv (S b x)) b0 l

omit [DecidableEq A] [DecidableEq B] in
theorem physicalOracle_unitary
    (hO : ∀ l x, IsUnitary (O l x)) (hS : ∀ b x, IsUnitary (S b x)) :
    ∀ l x, IsUnitary (physicalOracle eA eB O S l x) :=
  ODESectorNativeControl.physicalOracle_unitary _ _
    (fun l x => (hO l x).transport eB) (fun b x => (hS b x).transport eA)

/-- The concrete three-query control implements each original letter on the
same fixed clean subspace, including arbitrary coherent source-sector input. -/
theorem letter_intertwines (hO : ∀ l x, IsUnitary (O l x))
    (a0 : A) (b0 : B) (image : L → X → B)
    (hvalid : ∀ l x, eB.conjStarAlgEquiv (O l x) (EuclideanSpace.single b0 1) =
      EuclideanSpace.single (image l x) 1) (l : L ⊕ Bool) (x : X) :
    (letter eA eB O S b0 l).eval x ∘L input eA eB a0 b0 =
      input eA eB a0 b0 ∘L ODESectorCoordinates.oracle O S l x := by
  let C := (ODESectorCoordinates.layout eA eB).toLinearIsometry.toContinuousLinearMap
  let V := ODESectorTensor.input a0 b0
  let F := ODESectorNativeControl.logicalOracle
    (fun l x => eB.conjStarAlgEquiv (O l x))
    (fun b x => eA.conjStarAlgEquiv (S b x))
  have hFirst : (letter eA eB O S b0 l).eval x ∘L V = V ∘L F l x :=
    ODESectorNativeControl.letter_intertwines _ _
      (fun l x => (hO l x).transport eB) a0 b0 image hvalid l x
  have hCoordinates : F l x ∘L C = C ∘L ODESectorCoordinates.oracle O S l x := by
    cases l with
    | inl l => exact ODESectorCoordinates.matrix_intertwines eA eB (O l x)
    | inr b => exact ODESectorCoordinates.source_intertwines eA eB (S b x)
  change (letter eA eB O S b0 l).eval x ∘L (V ∘L C) =
    (V ∘L C) ∘L ODESectorCoordinates.oracle O S l x
  rw [← comp_assoc, hFirst, comp_assoc, hCoordinates, ← comp_assoc]

/-- Compile the already proved ODE9 circuit directly, keeping its logical
oracle type rather than rebuilding a different algorithm in new coordinates. -/
def compile (a0 : A) (b0 : B)
    (p : MultiOracleCircuit.Program (ODESectorCoordinates.oracle O S)) :
    MultiOracleCircuit.Program (physicalOracle eA eB O S) :=
  ODEPrimitiveControlBudget.compile
    (K := ODESourceTransport.Space H K) (H := ODESectorTensor.Physical A B)
    (O := ODESectorCoordinates.oracle O S) (F := physicalOracle eA eB O S)
    (input eA eB a0 b0) (input_isometry eA eB a0 b0) (letter eA eB O S b0) p

theorem compile_eval
    (hO : ∀ l x, IsUnitary (O l x)) (hS : ∀ b x, IsUnitary (S b x))
    (a0 : A) (b0 : B) (image : L → X → B)
    (hvalid : ∀ l x, eB.conjStarAlgEquiv (O l x) (EuclideanSpace.single b0 1) =
      EuclideanSpace.single (image l x) 1)
    (p : MultiOracleCircuit.Program (ODESectorCoordinates.oracle O S)) (x : X) :
    (compile eA eB O S a0 b0 p).eval x ∘L input eA eB a0 b0 =
      input eA eB a0 b0 ∘L p.eval x :=
  EncodedLabeledProgram.compile_eval
    (P := ODESourceTransport.Space H K) (K := ODESectorTensor.Physical A B)
    (F := physicalOracle eA eB O S) (O := ODESectorCoordinates.oracle O S)
    (input eA eB a0 b0) (input_isometry eA eB a0 b0) (letter eA eB O S b0)
    (physicalOracle_unitary eA eB O S hO hS) (ODESectorCoordinates.oracle_unitary O S hO hS)
    (letter_intertwines eA eB O S hO a0 b0 image hvalid) p x

theorem compile_matrix_cost (a0 : A) (b0 : B)
    (p : MultiOracleCircuit.Program (ODESectorCoordinates.oracle O S)) (w : L → ℕ) :
    (compile eA eB O S a0 b0 p).cost (ODESourceQueryBudget.matrixWeight w) =
      3 * p.cost (ODESourceQueryBudget.matrixWeight w) :=
  ODEPrimitiveControlBudget.matrix_cost
    (input eA eB a0 b0) (input_isometry eA eB a0 b0) (letter eA eB O S b0) p w
    (ODESectorNativeControl.letter_matrix_cost _ _ b0 w)

theorem compile_source_cost (a0 : A) (b0 : B)
    (p : MultiOracleCircuit.Program (ODESectorCoordinates.oracle O S)) (b : Bool) :
    (compile eA eB O S a0 b0 p).cost (ODESourceQueryBudget.sourceWeight b) =
      p.cost (ODESourceQueryBudget.sourceWeight b) :=
  ODEPrimitiveControlBudget.source_cost
    (input eA eB a0 b0) (input_isometry eA eB a0 b0) (letter eA eB O S b0) p b
    (ODESectorNativeControl.letter_source_cost _ _ b0 b)

theorem compile_source_total_cost (a0 : A) (b0 : B)
    (p : MultiOracleCircuit.Program (ODESectorCoordinates.oracle O S)) :
    (compile eA eB O S a0 b0 p).cost ODESourceQueryBudget.sourceTotalWeight =
      p.cost ODESourceQueryBudget.sourceTotalWeight :=
  ODEPrimitiveControlBudget.source_total_cost
    (input eA eB a0 b0) (input_isometry eA eB a0 b0) (letter eA eB O S b0) p
    (ODESectorNativeControl.letter_source_total_cost _ _ b0)

variable {P : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-- Removing the common clean embedding returns the identical public vector. -/
theorem decoded_eq
    (hO : ∀ l x, IsUnitary (O l x)) (hS : ∀ b x, IsUnitary (S b x))
    (a0 : A) (b0 : B) (image : L → X → B)
    (hvalid : ∀ l x, eB.conjStarAlgEquiv (O l x) (EuclideanSpace.single b0 1) =
      EuclideanSpace.single (image l x) 1)
    (p : MultiOracleCircuit.Program (ODESectorCoordinates.oracle O S)) (x : X)
    (ψ : ODESourceTransport.Space H K) (F : P →L[ℂ] ODESourceTransport.Space H K) :
    ((input eA eB a0 b0 ∘L F)†)
      ((compile eA eB O S a0 b0 p).eval x (input eA eB a0 b0 ψ)) =
        (F†) (p.eval x ψ) :=
  ODEPrimitiveControlBudget.decoded_eq
    (input eA eB a0 b0) (input_isometry eA eB a0 b0) (letter eA eB O S b0)
    (physicalOracle_unitary eA eB O S hO hS) (ODESectorCoordinates.oracle_unitary O S hO hS)
    (letter_intertwines eA eB O S hO a0 b0 image hvalid) p x ψ F

/-- In particular each trial preserves its original herald probability. -/
theorem projected_norm_eq
    (hO : ∀ l x, IsUnitary (O l x)) (hS : ∀ b x, IsUnitary (S b x))
    (a0 : A) (b0 : B) (image : L → X → B)
    (hvalid : ∀ l x, eB.conjStarAlgEquiv (O l x) (EuclideanSpace.single b0 1) =
      EuclideanSpace.single (image l x) 1)
    (p : MultiOracleCircuit.Program (ODESectorCoordinates.oracle O S)) (x : X)
    (ψ : ODESourceTransport.Space H K) (F : P →L[ℂ] ODESourceTransport.Space H K) :
    ‖ODEHeraldedSuccess.successProjector (input eA eB a0 b0 ∘L F)
      ((compile eA eB O S a0 b0 p).eval x (input eA eB a0 b0 ψ))‖ =
        ‖ODEHeraldedSuccess.successProjector F (p.eval x ψ)‖ :=
  ODEPrimitiveControlBudget.projected_norm_eq
    (input eA eB a0 b0) (input_isometry eA eB a0 b0) (letter eA eB O S b0)
    (physicalOracle_unitary eA eB O S hO hS) (ODESectorCoordinates.oracle_unitary O S hO hS)
    (letter_intertwines eA eB O S hO a0 b0 image hvalid) p x ψ F


/-- All single-letter implementation premises are discharged by the concrete
coordinate and native-control constructions. Any certified ODE9 trial family
therefore has this primitive-access certificate on one fixed clean workspace. -/
theorem transfer_certificate
    (hO : ∀ l x, IsUnitary (O l x)) (hS : ∀ b x, IsUnitary (S b x))
    (a0 : A) (b0 : B) (image : L → X → B)
    (hvalid : ∀ l x, eB.conjStarAlgEquiv (O l x) (EuclideanSpace.single b0 1) =
      EuclideanSpace.single (image l x) 1)
    (q : ℕ → MultiOracleCircuit.Program (ODESectorCoordinates.oracle O S)) (M : ℕ)
    (ψ : ODESourceTransport.Space H K) (hψ : ‖ψ‖ = 1)
    (F : P →L[ℂ] ODESourceTransport.Space H K) (hF : F† ∘L F = 1)
    (x : X) (target : P) (s Θ ell g η : ℝ)
    (hMatrix : ∀ j, j < M →
      ((q j).cost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) : ℝ) ≤
        106168320 * g * ImprovedODEQueryBudget.queryShape s Θ ell)
    (hSource : ∀ j, j < M → ∀ b : Bool,
      ((q j).cost (ODESourceQueryBudget.sourceWeight b) : ℝ) ≤ 10 * g)
    (hSourceTotal : ∀ j, j < M →
      ((q j).cost ODESourceQueryBudget.sourceTotalWeight : ℝ) ≤ 20 * g)
    (hSuccess : (1 : ℝ) / 4 ≤
      (∑ j ∈ Finset.range M,
        ‖ODEHeraldedSuccess.successProjector F ((q j).eval x ψ)‖ ^ 2) / (M : ℝ))
    (hDirection : ∀ j, j < M → (F†) ((q j).eval x ψ) ≠ 0 →
      ∃ ω : ℂ, ‖ω‖ = 1 ∧
        ‖ω • ODEStateNormalization.unitDirection ((F†) ((q j).eval x ψ)) -
          ODEStateNormalization.unitDirection target‖ ≤ η) :
    let J := input eA eB a0 b0
    ‖J ψ‖ = 1 ∧ (J ∘L F)† ∘L (J ∘L F) = 1 ∧
      (∀ j, j < M →
        ((compile eA eB O S a0 b0 (q j)).cost
          (ODESourceQueryBudget.matrixWeight (fun _ => 1)) : ℝ) ≤
            318504960 * g * ImprovedODEQueryBudget.queryShape s Θ ell) ∧
      (∀ j, j < M → ∀ b : Bool,
        ((compile eA eB O S a0 b0 (q j)).cost (ODESourceQueryBudget.sourceWeight b) : ℝ) ≤
          10 * g) ∧
      (∀ j, j < M →
        ((compile eA eB O S a0 b0 (q j)).cost ODESourceQueryBudget.sourceTotalWeight : ℝ) ≤
          20 * g) ∧
      (1 : ℝ) / 4 ≤
          (∑ j ∈ Finset.range M,
            ‖ODEHeraldedSuccess.successProjector (J ∘L F)
              ((compile eA eB O S a0 b0 (q j)).eval x (J ψ))‖ ^ 2) / (M : ℝ) ∧
        ∀ j, j < M → ((J ∘L F)†)
          ((compile eA eB O S a0 b0 (q j)).eval x (J ψ)) ≠ 0 →
          ∃ ω : ℂ, ‖ω‖ = 1 ∧
            ‖ω • ODEStateNormalization.unitDirection (((J ∘L F)†)
                ((compile eA eB O S a0 b0 (q j)).eval x (J ψ))) -
              ODEStateNormalization.unitDirection target‖ ≤ η :=
  ODEPrimitiveControlBudget.transfer_certificate
    (input eA eB a0 b0) (input_isometry eA eB a0 b0) (letter eA eB O S b0)
    (physicalOracle_unitary eA eB O S hO hS) (ODESectorCoordinates.oracle_unitary O S hO hS)
    (letter_intertwines eA eB O S hO a0 b0 image hvalid)
    (ODESectorNativeControl.letter_matrix_cost _ _ b0 (fun _ => 1))
    (fun b => ODESectorNativeControl.letter_source_cost _ _ b0 b)
    (ODESectorNativeControl.letter_source_total_cost _ _ b0)
    q M ψ hψ F hF x target s Θ ell g η
    hMatrix hSource hSourceTotal hSuccess hDirection

end
end SparseHamiltonian.ODECoordinateNativeControl
