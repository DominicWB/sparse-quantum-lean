import TimeDependentODE.Source.Controls

/-!
# Time-dependent source loading compiled into the counted preparation circuit

Time-dependent counterpart of `SparseHamiltonian.ODECompiledSource`. The
coefficient seed, routing and output encoding are the released
`ODECompiledSource.seed`, `ODECompiledSource.output` and
`ODESourceTransport.route`; they are fixed independently of both unknown
source families and the matrix input. Two source queries load the initial
state and the label-dependent forcing states in the canonical source sector:
the single forcing query applies `Jb x q` on every forcing label `some q`.
The exact state identity below connects the actual circuit to the source input
used in the ODE correctness proof, with branch map `branchTD`. Matrix counts
are relative to the sector-controlled native matrix family; implementing that
extra control is a separate interface.
-/

namespace SparseHamiltonian.TimeDependentODE.SourceTD

noncomputable section
open ContinuousLinearMap OracleCircuit
open scoped InnerProduct
set_option synthInstance.maxSize 2048

variable {ι P K X L : Type*} [Fintype ι]
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {N : ℕ} {O : L → X → K →L[ℂ] K}

/-- Exactly two supplied source interfaces, with their supported controls:
`false` is the released initial call and `true` the label-dependent forcing
call. -/
def sourceOracle (J₀ : X → P →L[ℂ] P) (Jb : X → Fin N → P →L[ℂ] P)
    (b : Bool) (x : X) :
    ODECompiledSource.Physical ι P K N →L[ℂ] ODECompiledSource.Physical ι P K N :=
  ODESourceTransport.sourceGate
    (if b then forcing (Jb x)
      else ODESourceControls.initial (J₀ x) N)

set_option maxHeartbeats 1000000 in
/-- Route to the source sector, load both sources, route back, then SELECT. -/
def program (p : MultiOracleCircuit.Program O) (J₀ : X → P →L[ℂ] P)
    (Jb : X → Fin N → P →L[ℂ] P)
    (E : ODECompiledSource.Branch ι P N →L[ℂ] K) (hE : E† ∘L E = 1) :
    MultiOracleCircuit.Program
      (ODESourceQueryBudget.oracle
        (ODESourceTransport.matrixOracle (B := ODECompiledSource.Branch ι P N) O)
        (sourceOracle J₀ Jb)) :=
  ODESourceQueryBudget.preparation
    (K := ODECompiledSource.Physical ι P K N) (X := X) (L := L)
    (O := ODESourceTransport.matrixOracle (B := ODECompiledSource.Branch ι P N) O)
    (ODESourceTransport.matrixProgram (B := ODECompiledSource.Branch ι P N)
      (K := K) (O := O) p)
    (sourceOracle (ι := ι) (P := P) (K := K) J₀ Jb)
    (ODESourceTransport.route (B := ODECompiledSource.Branch ι P N) (K := K) E)
    (ODESourceTransport.route_unitary (B := ODECompiledSource.Branch ι P N)
      (K := K) E hE)

theorem sourceOracle_unitary (J₀ : X → P →L[ℂ] P) (Jb : X → Fin N → P →L[ℂ] P)
    (hJ₀ : ∀ x, IsUnitary (J₀ x)) (hJb : ∀ x q, IsUnitary (Jb x q)) :
    ∀ b x, IsUnitary (sourceOracle (ι := ι) (K := K) J₀ Jb b x) := by
  intro b x
  apply ODESourceTransport.sourceGate_unitary
  cases b with
  | false => exact ODESourceControls.initial_unitary (J₀ x) N (hJ₀ x)
  | true => exact forcing_unitary (Jb x) (hJb x)

theorem oracle_unitary (J₀ : X → P →L[ℂ] P) (Jb : X → Fin N → P →L[ℂ] P)
    (hO : ∀ l x, IsUnitary (O l x))
    (hJ₀ : ∀ x, IsUnitary (J₀ x)) (hJb : ∀ x q, IsUnitary (Jb x q)) :
    ∀ l x, IsUnitary
      (ODESourceQueryBudget.oracle
        (ODESourceTransport.matrixOracle (B := ODECompiledSource.Branch ι P N) O)
        (sourceOracle J₀ Jb) l x) := by
  apply ODESourceQueryBudget.oracle_unitary
  · intro l x
    exact ODESourceTransport.matrixGate_unitary (O l x) (hO l x)
  · exact sourceOracle_unitary J₀ Jb hJ₀ hJb

theorem program_unitary (p : MultiOracleCircuit.Program O)
    (J₀ : X → P →L[ℂ] P) (Jb : X → Fin N → P →L[ℂ] P)
    (E : ODECompiledSource.Branch ι P N →L[ℂ] K)
    (hE : E† ∘L E = 1) (hO : ∀ l x, IsUnitary (O l x))
    (hJ₀ : ∀ x, IsUnitary (J₀ x)) (hJb : ∀ x q, IsUnitary (Jb x q)) (x : X) :
    IsUnitary ((program p J₀ Jb E hE).eval x) :=
  (program p J₀ Jb E hE).eval_unitary
    (oracle_unitary J₀ Jb hO hJ₀ hJb) x

/-- Exact preparation action, derived from the routing and the two controlled
source calls. There is no assumption about the action of the compiled circuit. -/
theorem program_state (p : MultiOracleCircuit.Program O)
    (hO : ∀ l x, IsUnitary (O l x)) (J₀ : X → P →L[ℂ] P)
    (Jb : X → Fin N → P →L[ℂ] P)
    (E : ODECompiledSource.Branch ι P N →L[ℂ] K) (hE : E† ∘L E = 1)
    (d : Option (Fin N) × ι → ℂ) (v : P) (x : X) :
    (program p J₀ Jb E hE).eval x (ODECompiledSource.seed E d v) =
      ODESourceTransport.matrixEmbedding
        (p.eval x (ODEJointSourceLCU.input E d
          (fun a => branchTD (J₀ x) (Jb x) a.1) v)) := by
  have hIn (b : ODECompiledSource.Branch ι P N) :
      ODESourceTransport.route E
        (ODESourceTransport.matrixEmbedding (E b)) =
          ODESourceTransport.sourceEmbedding b :=
    congrArg (fun A : ODECompiledSource.Branch ι P N →L[ℂ]
        ODECompiledSource.Physical ι P K N => A b)
      (ODESourceTransport.route_encoded E hE)
  have hOut (b : ODECompiledSource.Branch ι P N) :
      ODESourceTransport.route E (ODESourceTransport.sourceEmbedding b) =
        ODESourceTransport.matrixEmbedding (E b) :=
    congrArg (fun A : ODECompiledSource.Branch ι P N →L[ℂ]
        ODECompiledSource.Physical ι P K N => A b)
      (ODESourceTransport.route_source E)
  have hSource (S : ODECompiledSource.Branch ι P N →L[ℂ] ODECompiledSource.Branch ι P N)
      (b : ODECompiledSource.Branch ι P N) :
      ODESourceTransport.sourceGate S (ODESourceTransport.sourceEmbedding b) =
        (ODESourceTransport.sourceEmbedding : ODECompiledSource.Branch ι P N →L[ℂ]
          ODECompiledSource.Physical ι P K N) (S b) :=
    congrArg (fun A : ODECompiledSource.Branch ι P N →L[ℂ]
        ODECompiledSource.Physical ι P K N => A b)
      (ODESourceTransport.sourceGate_source S)
  have hMatrix (k : K) :
      (ODESourceTransport.matrixProgram (B := ODECompiledSource.Branch ι P N) p).eval x
          (ODESourceTransport.matrixEmbedding k) =
        ODESourceTransport.matrixEmbedding (p.eval x k) :=
    congrArg (fun A : K →L[ℂ] ODECompiledSource.Physical ι P K N => A k)
      (ODESourceTransport.matrixProgram_eval p hO x)
  have hLoad : combined (J₀ x) (Jb x)
        (ODEJointLCU.coefficientInput d v) =
      ODECoherentLCU.inputEmbedding d
        (fun a => branchTD (J₀ x) (Jb x) a.1) v :=
    congrArg (fun A : P →L[ℂ] ODECompiledSource.Branch ι P N => A v)
      (combined_inputEmbedding (J₀ x) (Jb x) d)
  rw [program, ODESourceQueryBudget.preparation_eval]
  simp only [star_eq_adjoint, ODESourceTransport.route_selfAdjoint,
    mul_apply_eq_comp]
  change (ODESourceTransport.matrixProgram (B := ODECompiledSource.Branch ι P N) p).eval x
    (ODESourceTransport.route E
      (ODESourceTransport.sourceGate (ODESourceControls.initial (J₀ x) N)
        (ODESourceTransport.sourceGate (forcing (Jb x))
          (ODESourceTransport.route E
            (ODESourceTransport.matrixEmbedding
              (E (ODEJointLCU.coefficientInput d v))))))) = _
  rw [hIn, hSource, hSource, hOut, hMatrix]
  change ODESourceTransport.matrixEmbedding
      (p.eval x (E (combined (J₀ x) (Jb x)
        (ODEJointLCU.coefficientInput d v)))) = _
  exact congrArg (fun b : ODECompiledSource.Branch ι P N =>
    ODESourceTransport.matrixEmbedding (p.eval x (E b))) hLoad

/-- Reading the compiled output gives the original source-correctness vector. -/
theorem decoded_eq (p : MultiOracleCircuit.Program O)
    (hO : ∀ l x, IsUnitary (O l x)) (J₀ : X → P →L[ℂ] P)
    (Jb : X → Fin N → P →L[ℂ] P)
    (E : ODECompiledSource.Branch ι P N →L[ℂ] K) (hE : E† ∘L E = 1)
    (d : Option (Fin N) × ι → ℂ) (v : P) (x : X) :
    ((ODECompiledSource.output E d)†)
        ((program p J₀ Jb E hE).eval x (ODECompiledSource.seed E d v)) =
      ODEJointSourceLCU.decoded E d
        (fun a => branchTD (J₀ x) (Jb x) a.1)
        (p.eval x) v := by
  have hM (k : K) :
      ((ODESourceTransport.matrixEmbedding : K →L[ℂ] ODECompiledSource.Physical ι P K N)†)
        (ODESourceTransport.matrixEmbedding k) = k :=
    congrArg (fun A : K →L[ℂ] K => A k)
      (ODESourceTransport.matrixEmbedding_isometry
        (B := ODECompiledSource.Branch ι P N) (K := K))
  rw [program_state p hO J₀ Jb E hE d v x]
  simp only [ODECompiledSource.output, adjoint_comp, comp_apply, hM,
    ODEJointSourceLCU.decoded, ODEHeraldedSuccess.decoded]

/-- Matrix calls are unchanged by the source compiler. -/
theorem program_matrix_cost (p : MultiOracleCircuit.Program O)
    (J₀ : X → P →L[ℂ] P) (Jb : X → Fin N → P →L[ℂ] P)
    (E : ODECompiledSource.Branch ι P N →L[ℂ] K)
    (hE : E† ∘L E = 1) (w : L → ℕ) :
    (program p J₀ Jb E hE).cost (ODESourceQueryBudget.matrixWeight w) = p.cost w := by
  rw [program, ODESourceQueryBudget.preparation_matrix_cost,
    ODESourceTransport.matrixProgram_cost]

/-- Each source interface is called once, independently of both node counts.
In particular the label-dependent forcing interface is one query. -/
theorem program_source_cost (p : MultiOracleCircuit.Program O)
    (J₀ : X → P →L[ℂ] P) (Jb : X → Fin N → P →L[ℂ] P)
    (E : ODECompiledSource.Branch ι P N →L[ℂ] K)
    (hE : E† ∘L E = 1) (b : Bool) :
    (program p J₀ Jb E hE).cost (ODESourceQueryBudget.sourceWeight b) = 1 := by
  rw [program, ODESourceQueryBudget.preparation_source_cost]

/-- Both supplied source calls together cost exactly two queries. -/
theorem program_source_total_cost (p : MultiOracleCircuit.Program O)
    (J₀ : X → P →L[ℂ] P) (Jb : X → Fin N → P →L[ℂ] P)
    (E : ODECompiledSource.Branch ι P N →L[ℂ] K)
    (hE : E† ∘L E = 1) :
    (program p J₀ Jb E hE).cost ODESourceQueryBudget.sourceTotalWeight = 2 := by
  rw [program, ODESourceQueryBudget.preparation_source_total_cost]

end
end SparseHamiltonian.TimeDependentODE.SourceTD
