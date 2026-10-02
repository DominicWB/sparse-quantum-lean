import SparseODE.ODESourceHeraldLift

/-!
# Source loading compiled into the counted preparation circuit

The coefficient seed, routing and output encoding are fixed independently of
both unknown source states and the matrix input. Two source queries load the
initial and forcing states in a canonical source sector. The exact state
identity below connects their actual circuit to the source input used in the
ODE correctness proof. Matrix counts are relative to the sector-controlled
native matrix family; implementing that extra control is a separate interface.
-/

namespace SparseHamiltonian.ODECompiledSource

noncomputable section
open ContinuousLinearMap OracleCircuit
open scoped InnerProduct
set_option synthInstance.maxSize 2048

variable {ι P K X L : Type*} [Fintype ι]
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {N : ℕ} {O : L → X → K →L[ℂ] K}

abbrev Branch (ι P : Type*) [Fintype ι] [NormedAddCommGroup P] (N : ℕ) :=
  ODESourceControls.BranchSpace ι P N

abbrev Physical (ι P K : Type*) [Fintype ι] [NormedAddCommGroup P] (N : ℕ) :=
  ODESourceTransport.Space (Branch ι P N) K

/-- Exactly two supplied source interfaces, with their supported controls. -/
def sourceOracle (J₀ Jb : X → P →L[ℂ] P) (N : ℕ) (b : Bool) (x : X) :
    Physical ι P K N →L[ℂ] Physical ι P K N :=
  ODESourceTransport.sourceGate
    (if b then ODESourceControls.forcing (Jb x) N
      else ODESourceControls.initial (J₀ x) N)

/-- The known coefficient state in the matrix sector, before source loading. -/
def seed (E : Branch ι P N →L[ℂ] K)
    (d : Option (Fin N) × ι → ℂ) (v : P) : Physical ι P K N :=
  ODESourceTransport.matrixEmbedding (ODEJointLCU.input E d v)

def output (E : Branch ι P N →L[ℂ] K)
    (d : Option (Fin N) × ι → ℂ) : P →L[ℂ] Physical ι P K N :=
  ODESourceTransport.matrixEmbedding ∘L ODEJointLCU.output E d

set_option maxHeartbeats 1000000 in
/-- Route to the source sector, load both sources, route back, then SELECT. -/
def program (p : MultiOracleCircuit.Program O) (J₀ Jb : X → P →L[ℂ] P)
    (E : Branch ι P N →L[ℂ] K) (hE : E† ∘L E = 1) :
    MultiOracleCircuit.Program
      (ODESourceQueryBudget.oracle
        (ODESourceTransport.matrixOracle (B := Branch ι P N) O)
        (sourceOracle J₀ Jb N)) :=
  ODESourceQueryBudget.preparation
    (K := Physical ι P K N) (X := X) (L := L)
    (O := ODESourceTransport.matrixOracle (B := Branch ι P N) O)
    (ODESourceTransport.matrixProgram (B := Branch ι P N) (K := K) (O := O) p)
    (sourceOracle (ι := ι) (P := P) (K := K) J₀ Jb N)
    (ODESourceTransport.route (B := Branch ι P N) (K := K) E)
    (ODESourceTransport.route_unitary (B := Branch ι P N) (K := K) E hE)

theorem sourceOracle_unitary (J₀ Jb : X → P →L[ℂ] P) (N : ℕ)
    (hJ₀ : ∀ x, IsUnitary (J₀ x)) (hJb : ∀ x, IsUnitary (Jb x)) :
    ∀ b x, IsUnitary (sourceOracle (ι := ι) (K := K) J₀ Jb N b x) := by
  intro b x
  apply ODESourceTransport.sourceGate_unitary
  cases b with
  | false => exact ODESourceControls.initial_unitary (J₀ x) N (hJ₀ x)
  | true => exact ODESourceControls.forcing_unitary (Jb x) N (hJb x)

theorem oracle_unitary (J₀ Jb : X → P →L[ℂ] P) (N : ℕ)
    (hO : ∀ l x, IsUnitary (O l x))
    (hJ₀ : ∀ x, IsUnitary (J₀ x)) (hJb : ∀ x, IsUnitary (Jb x)) :
    ∀ l x, IsUnitary
      (ODESourceQueryBudget.oracle
        (ODESourceTransport.matrixOracle (B := Branch ι P N) O)
        (sourceOracle J₀ Jb N) l x) := by
  apply ODESourceQueryBudget.oracle_unitary
  · intro l x
    exact ODESourceTransport.matrixGate_unitary (O l x) (hO l x)
  · exact sourceOracle_unitary J₀ Jb N hJ₀ hJb

theorem program_unitary (p : MultiOracleCircuit.Program O)
    (J₀ Jb : X → P →L[ℂ] P) (E : Branch ι P N →L[ℂ] K)
    (hE : E† ∘L E = 1) (hO : ∀ l x, IsUnitary (O l x))
    (hJ₀ : ∀ x, IsUnitary (J₀ x)) (hJb : ∀ x, IsUnitary (Jb x)) (x : X) :
    IsUnitary ((program p J₀ Jb E hE).eval x) :=
  (program p J₀ Jb E hE).eval_unitary
    (oracle_unitary J₀ Jb N hO hJ₀ hJb) x

/-- Exact preparation action, derived from the routing and the two controlled
source calls. There is no assumption about the action of the compiled circuit. -/
theorem program_state (p : MultiOracleCircuit.Program O)
    (hO : ∀ l x, IsUnitary (O l x)) (J₀ Jb : X → P →L[ℂ] P)
    (E : Branch ι P N →L[ℂ] K) (hE : E† ∘L E = 1)
    (d : Option (Fin N) × ι → ℂ) (v : P) (x : X) :
    (program p J₀ Jb E hE).eval x (seed E d v) =
      ODESourceTransport.matrixEmbedding
        (p.eval x (ODEJointSourceLCU.input E d
          (fun a => ODESourcePreparations.branch (J₀ x) (Jb x) N a.1) v)) := by
  have hIn (b : Branch ι P N) :
      ODESourceTransport.route E
        (ODESourceTransport.matrixEmbedding (E b)) =
          ODESourceTransport.sourceEmbedding b :=
    congrArg (fun A : Branch ι P N →L[ℂ] Physical ι P K N => A b)
      (ODESourceTransport.route_encoded E hE)
  have hOut (b : Branch ι P N) :
      ODESourceTransport.route E (ODESourceTransport.sourceEmbedding b) =
        ODESourceTransport.matrixEmbedding (E b) :=
    congrArg (fun A : Branch ι P N →L[ℂ] Physical ι P K N => A b)
      (ODESourceTransport.route_source E)
  have hSource (S : Branch ι P N →L[ℂ] Branch ι P N) (b : Branch ι P N) :
      ODESourceTransport.sourceGate S (ODESourceTransport.sourceEmbedding b) =
        (ODESourceTransport.sourceEmbedding : Branch ι P N →L[ℂ] Physical ι P K N)
          (S b) :=
    congrArg (fun A : Branch ι P N →L[ℂ] Physical ι P K N => A b)
      (ODESourceTransport.sourceGate_source S)
  have hMatrix (k : K) :
      (ODESourceTransport.matrixProgram (B := Branch ι P N) p).eval x
          (ODESourceTransport.matrixEmbedding k) =
        ODESourceTransport.matrixEmbedding (p.eval x k) :=
    congrArg (fun A : K →L[ℂ] Physical ι P K N => A k)
      (ODESourceTransport.matrixProgram_eval p hO x)
  have hLoad : ODESourceControls.combined (J₀ x) (Jb x) N
        (ODEJointLCU.coefficientInput d v) =
      ODECoherentLCU.inputEmbedding d
        (fun a => ODESourcePreparations.branch (J₀ x) (Jb x) N a.1) v :=
    congrArg (fun A : P →L[ℂ] Branch ι P N => A v)
      (ODESourceControls.combined_inputEmbedding (J₀ x) (Jb x) N d)
  rw [program, ODESourceQueryBudget.preparation_eval]
  simp only [star_eq_adjoint, ODESourceTransport.route_selfAdjoint,
    mul_apply_eq_comp]
  change (ODESourceTransport.matrixProgram (B := Branch ι P N) p).eval x
    (ODESourceTransport.route E
      (ODESourceTransport.sourceGate (ODESourceControls.initial (J₀ x) N)
        (ODESourceTransport.sourceGate (ODESourceControls.forcing (Jb x) N)
          (ODESourceTransport.route E
            (ODESourceTransport.matrixEmbedding
              (E (ODEJointLCU.coefficientInput d v))))))) = _
  rw [hIn, hSource, hSource, hOut, hMatrix]
  change ODESourceTransport.matrixEmbedding
      (p.eval x (E (ODESourceControls.combined (J₀ x) (Jb x) N
        (ODEJointLCU.coefficientInput d v)))) = _
  exact congrArg (fun b : Branch ι P N =>
    ODESourceTransport.matrixEmbedding (p.eval x (E b))) hLoad

theorem seed_unit (E : Branch ι P N →L[ℂ] K)
    (d : Option (Fin N) × ι → ℂ) (hE : E† ∘L E = 1)
    (hd : 0 < ODECoherentLCU.coefficientMass d) (v : P) (hv : ‖v‖ = 1) :
    ‖seed E d v‖ = 1 := by
  unfold seed
  rw [(ODESourceTransport.matrixEmbedding : K →L[ℂ] Physical ι P K N).norm_map_iff_adjoint_comp_self.mpr
    ODESourceTransport.matrixEmbedding_isometry]
  rw [(ODEJointLCU.input E d).norm_map_iff_adjoint_comp_self.mpr
    (ODEJointLCU.input_isometry E d hE hd), hv]

set_option maxHeartbeats 1000000 in
theorem output_isometry (E : Branch ι P N →L[ℂ] K)
    (d : Option (Fin N) × ι → ℂ) (hE : E† ∘L E = 1)
    (hd : 0 < ODECoherentLCU.coefficientMass d) :
    (output E d)† ∘L output E d = 1 :=
  NativeSparseAttenuation.isometry_comp
    (A := P) (B := K) (C := Physical ι P K N)
    (ODEJointLCU.output E d)
    (ODESourceTransport.matrixEmbedding (B := Branch ι P N) (K := K))
    (ODEJointLCU.output_isometry E d hE hd)
    (ODESourceTransport.matrixEmbedding_isometry (B := Branch ι P N) (K := K))

/-- Reading the compiled output gives the original source-correctness vector. -/
theorem decoded_eq (p : MultiOracleCircuit.Program O)
    (hO : ∀ l x, IsUnitary (O l x)) (J₀ Jb : X → P →L[ℂ] P)
    (E : Branch ι P N →L[ℂ] K) (hE : E† ∘L E = 1)
    (d : Option (Fin N) × ι → ℂ) (v : P) (x : X) :
    ((output E d)†) ((program p J₀ Jb E hE).eval x (seed E d v)) =
      ODEJointSourceLCU.decoded E d
        (fun a => ODESourcePreparations.branch (J₀ x) (Jb x) N a.1)
        (p.eval x) v := by
  have hM (k : K) :
      ((ODESourceTransport.matrixEmbedding : K →L[ℂ] Physical ι P K N)†)
        (ODESourceTransport.matrixEmbedding k) = k :=
    congrArg (fun A : K →L[ℂ] K => A k)
      (ODESourceTransport.matrixEmbedding_isometry (B := Branch ι P N) (K := K))
  rw [program_state p hO J₀ Jb E hE d v x]
  simp only [output, adjoint_comp, comp_apply, hM,
    ODEJointSourceLCU.decoded, ODEHeraldedSuccess.decoded]

/-- Matrix calls are unchanged by the source compiler. -/
theorem program_matrix_cost (p : MultiOracleCircuit.Program O)
    (J₀ Jb : X → P →L[ℂ] P) (E : Branch ι P N →L[ℂ] K)
    (hE : E† ∘L E = 1) (w : L → ℕ) :
    (program p J₀ Jb E hE).cost (ODESourceQueryBudget.matrixWeight w) = p.cost w := by
  rw [program, ODESourceQueryBudget.preparation_matrix_cost,
    ODESourceTransport.matrixProgram_cost]

/-- Each source interface is called once, independently of both node counts. -/
theorem program_source_cost (p : MultiOracleCircuit.Program O)
    (J₀ Jb : X → P →L[ℂ] P) (E : Branch ι P N →L[ℂ] K)
    (hE : E† ∘L E = 1) (b : Bool) :
    (program p J₀ Jb E hE).cost (ODESourceQueryBudget.sourceWeight b) = 1 := by
  rw [program, ODESourceQueryBudget.preparation_source_cost]

/-- Both supplied source calls together cost exactly two queries. -/
theorem program_source_total_cost (p : MultiOracleCircuit.Program O)
    (J₀ Jb : X → P →L[ℂ] P) (E : Branch ι P N →L[ℂ] K)
    (hE : E† ∘L E = 1) :
    (program p J₀ Jb E hE).cost ODESourceQueryBudget.sourceTotalWeight = 2 := by
  rw [program, ODESourceQueryBudget.preparation_source_total_cost]

end
end SparseHamiltonian.ODECompiledSource
