import GeneralSourceODE.Weights
import SparseODE.ODESectorCoordinates
import SparseODE.ODECountedAmplification

/-!
# The source-loaded preparation with a supplied weight preparation

The circuit of the general source interface (the paragraph after
Eq. `ode:eq:source-interface-preparation`) prepares the weights with the
supplied `P_w`, loads the states with the supplied label-controlled `U_load`,
applies the public coefficient phases, applies the selected propagator block,
and then unprepares only the label register with `P_w†`, retaining the data
output.

Here these steps form two counted source interfaces in the canonical source
sector of the released transport (`ODESourceTransport`):

* `false`, the preparation `phase ∘ U_load ∘ (P_w ⊗ 1)` (`prep`), and
* `true`, the label unpreparation `P_w† ⊗ 1`,

each conjugated by the released routing gate. The matrix program runs in the
matrix sector between them (`program`). The seed and the output encoding are
the released public ones with all source weight on the initial label
(`seed`, `output`); unlike the released source compiler, they do not depend
on the source norms. Decoding the actual circuit gives exactly the decoded
vector of the source-correctness analysis with the actual coefficients and
phased preparations (`decoded_eq`). A preparation makes one call of each
interface (`program_source_cost`).
-/

namespace SparseHamiltonian.GeneralSourceODE

noncomputable section
open ContinuousLinearMap OracleCircuit
open scoped InnerProduct BigOperators

namespace Compiled

variable {ι P K X L : Type*} [Fintype ι]
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {N : ℕ} {O : L → X → K →L[ℂ] K}

abbrev Branch (ι P : Type*) [Fintype ι] [NormedAddCommGroup P] (N : ℕ) :=
  ODECompiledSource.Branch ι P N

abbrev Physical (ι P K : Type*) [Fintype ι] [NormedAddCommGroup P] (N : ℕ) :=
  ODECompiledSource.Physical ι P K N

/-- The public coefficient table of the seed: all source weight on the
initial label. -/
def seedCoefficients (c : ι → ℂ) : Option (Fin N) × ι → ℂ :=
  ODESourceCoefficients.productCoeff (Weights.pointWeight none) c

/-- The preparation call: weights, loading and public phases. -/
def prep (Pw : Weights.LabelOp (Option (Fin N))) (J : Option (Fin N) → P →L[ℂ] P)
    (φ : Option (Fin N) → ℂ) : Branch ι P N →L[ℂ] Branch ι P N :=
  Weights.phaseGate φ ∘L Weights.loader J ∘L Weights.act Pw

/-- The two counted source interfaces: `false` the preparation, `true` the
label unpreparation `P_w†`. -/
def sourceFamily (Pw : X → Weights.LabelOp (Option (Fin N)))
    (J : X → Option (Fin N) → P →L[ℂ] P) (φ : Option (Fin N) → ℂ) :
    Bool → X → Branch ι P N →L[ℂ] Branch ι P N :=
  fun b x => if b then Weights.act ((Pw x)†) else prep (Pw x) (J x) φ

theorem prep_unitary {Pw : Weights.LabelOp (Option (Fin N))} (hPw : IsUnitary Pw)
    {J : Option (Fin N) → P →L[ℂ] P} (hJ : ∀ a, IsUnitary (J a))
    {φ : Option (Fin N) → ℂ} (hφ : ∀ a, ‖φ a‖ = 1) :
    IsUnitary (prep (ι := ι) Pw J φ) := by
  unfold prep
  exact ((Weights.phaseGate_unitary φ hφ).mul (Weights.loader_unitary J hJ)).mul
    (Weights.act_unitary hPw)

theorem adjoint_unitary {U : Weights.LabelOp (Option (Fin N))} (hU : IsUnitary U) :
    IsUnitary (U†) := by
  rw [← star_eq_adjoint]
  exact ⟨by rw [star_star]; exact hU.2, by rw [star_star]; exact hU.1⟩

theorem sourceFamily_unitary {Pw : X → Weights.LabelOp (Option (Fin N))}
    (hPw : ∀ x, IsUnitary (Pw x)) {J : X → Option (Fin N) → P →L[ℂ] P}
    (hJ : ∀ x a, IsUnitary (J x a)) {φ : Option (Fin N) → ℂ} (hφ : ∀ a, ‖φ a‖ = 1) :
    ∀ b x, IsUnitary (sourceFamily (ι := ι) Pw J φ b x) := by
  intro b x
  cases b with
  | false => exact prep_unitary (hPw x) (hJ x) hφ
  | true => exact Weights.act_unitary (adjoint_unitary (hPw x))

/-- Route to the source sector, prepare, route back, run the matrix program,
route again, unprepare the label, and route back. The rightmost factor
executes first. -/
def program (p : MultiOracleCircuit.Program O) (S : Bool → X → Branch ι P N →L[ℂ] Branch ι P N)
    (E : Branch ι P N →L[ℂ] K) (hE : E† ∘L E = 1) :
    MultiOracleCircuit.Program (ODESectorCoordinates.oracle O S) :=
  .seq (.fixed (ODESourceTransport.route E) (ODESourceTransport.route_unitary E hE))
    (.seq (.query (Sum.inr true))
      (.seq (.fixed (ODESourceTransport.route E) (ODESourceTransport.route_unitary E hE))
        (.seq (MultiOracleCircuit.Program.relabel (F := ODESectorCoordinates.oracle O S)
            Sum.inl (ODESourceTransport.matrixProgram (B := Branch ι P N) p))
          (.seq (.fixed (ODESourceTransport.route E) (ODESourceTransport.route_unitary E hE))
            (.seq (.query (Sum.inr false))
              (.fixed (ODESourceTransport.route E) (ODESourceTransport.route_unitary E hE)))))))

theorem program_eval (p : MultiOracleCircuit.Program O)
    (S : Bool → X → Branch ι P N →L[ℂ] Branch ι P N)
    (E : Branch ι P N →L[ℂ] K) (hE : E† ∘L E = 1) (x : X) :
    (program p S E hE).eval x =
      ODESourceTransport.route E * ODESourceTransport.sourceGate (S true x) *
        ODESourceTransport.route E *
        (ODESourceTransport.matrixProgram (B := Branch ι P N) p).eval x *
        ODESourceTransport.route E * ODESourceTransport.sourceGate (S false x) *
        ODESourceTransport.route E := by
  simp only [program, MultiOracleCircuit.Program.eval_seq, MultiOracleCircuit.Program.eval_fixed,
    MultiOracleCircuit.Program.eval_query, MultiOracleCircuit.Program.eval_relabel, mul_assoc]
  rfl

theorem program_unitary (p : MultiOracleCircuit.Program O) (hO : ∀ l x, IsUnitary (O l x))
    (S : Bool → X → Branch ι P N →L[ℂ] Branch ι P N) (hS : ∀ b x, IsUnitary (S b x))
    (E : Branch ι P N →L[ℂ] K) (hE : E† ∘L E = 1) (x : X) :
    IsUnitary ((program p S E hE).eval x) :=
  (program p S E hE).eval_unitary (ODESectorCoordinates.oracle_unitary O S hO hS) x

/-- Matrix calls are unchanged by the source compiler. -/
theorem program_matrix_cost (p : MultiOracleCircuit.Program O)
    (S : Bool → X → Branch ι P N →L[ℂ] Branch ι P N)
    (E : Branch ι P N →L[ℂ] K) (hE : E† ∘L E = 1) (w : L → ℕ) :
    (program p S E hE).cost (ODESourceQueryBudget.matrixWeight w) = p.cost w := by
  simp only [program, MultiOracleCircuit.Program.cost_seq, MultiOracleCircuit.Program.cost_fixed,
    MultiOracleCircuit.Program.cost_query, MultiOracleCircuit.Program.cost_relabel,
    ODESourceQueryBudget.matrixWeight, Sum.elim_inr, Sum.elim_inl, zero_add, add_zero]
  change (ODESourceTransport.matrixProgram (B := Branch ι P N) p).cost w = p.cost w
  exact ODESourceTransport.matrixProgram_cost p w

/-- Each counted source interface is called once per preparation. -/
theorem program_source_cost (p : MultiOracleCircuit.Program O)
    (S : Bool → X → Branch ι P N →L[ℂ] Branch ι P N)
    (E : Branch ι P N →L[ℂ] K) (hE : E† ∘L E = 1) (b : Bool) :
    (program p S E hE).cost (ODESourceQueryBudget.sourceWeight b) = 1 := by
  cases b <;> simp [program, ODESourceQueryBudget.sourceWeight]

theorem program_source_total_cost (p : MultiOracleCircuit.Program O)
    (S : Bool → X → Branch ι P N →L[ℂ] Branch ι P N)
    (E : Branch ι P N →L[ℂ] K) (hE : E† ∘L E = 1) :
    (program p S E hE).cost ODESourceQueryBudget.sourceTotalWeight = 2 := by
  simp [program, ODESourceQueryBudget.sourceTotalWeight]

set_option maxRecDepth 8192 in
/-- **Decoding the compiled circuit.** With a weight preparation of the
actual source probabilities `π`, the public output encoding applied to the
actual circuit on the public seed gives the source-correctness decoded vector
for the actual coefficients and the phased preparations. -/
theorem decoded_eq (p : MultiOracleCircuit.Program O)
    (Pw : X → Weights.LabelOp (Option (Fin N))) (J : X → Option (Fin N) → P →L[ℂ] P)
    (φ : Option (Fin N) → ℂ) (E : Branch ι P N →L[ℂ] K) (hE : E† ∘L E = 1)
    (c : ι → ℂ) (v : P) (x : X) (π : Option (Fin N) → ℝ) (hπ : ∀ a, 0 ≤ π a)
    (hπsum : ∑ a, π a = 1) (hPw : ∀ a, Weights.amp (Pw x) a none = (Real.sqrt (π a) : ℂ)) :
    ((ODECompiledSource.output E (seedCoefficients c))†)
        ((program p (sourceFamily Pw J φ) E hE).eval x
          (ODECompiledSource.seed E (seedCoefficients c) v)) =
      ODEJointSourceLCU.decoded E (ODESourceCoefficients.productCoeff π c)
        (fun b => φ b.1 • J x b.1) (p.eval x) v := by
  set R := ODESourceTransport.route (K := K) E with hRdef
  have hEncoded (b : Branch ι P N) :
      R (ODESourceTransport.matrixEmbedding (E b)) = ODESourceTransport.sourceEmbedding b :=
    congrArg (fun A : Branch ι P N →L[ℂ] Physical ι P K N => A b)
      (ODESourceTransport.route_encoded E hE)
  have hSourceRoute (b : Branch ι P N) :
      R (ODESourceTransport.sourceEmbedding b) = ODESourceTransport.matrixEmbedding (E b) :=
    congrArg (fun A : Branch ι P N →L[ℂ] Physical ι P K N => A b)
      (ODESourceTransport.route_source E)
  have hSource (S' : Branch ι P N →L[ℂ] Branch ι P N) (b : Branch ι P N) :
      ODESourceTransport.sourceGate (K := K) S' (ODESourceTransport.sourceEmbedding b) =
        ODESourceTransport.sourceEmbedding (S' b) :=
    congrArg (fun A : Branch ι P N →L[ℂ] Physical ι P K N => A b)
      (ODESourceTransport.sourceGate_source S')
  have hMatrix (k : K) :
      ODESourceTransport.matrixGate (B := Branch ι P N) (p.eval x)
          (ODESourceTransport.matrixEmbedding k) =
        ODESourceTransport.matrixEmbedding (p.eval x k) :=
    congrArg (fun A : K →L[ℂ] Physical ι P K N => A k)
      (ODESourceTransport.matrixGate_matrix (p.eval x))
  have hM (k : K) :
      ((ODESourceTransport.matrixEmbedding : K →L[ℂ] Physical ι P K N)†)
        (ODESourceTransport.matrixEmbedding k) = k :=
    congrArg (fun A : K →L[ℂ] K => A k)
      (ODESourceTransport.matrixEmbedding_isometry (B := Branch ι P N) (K := K))
  have hR : R† = R := ODESourceTransport.route_selfAdjoint E
  -- the preparation half
  have hIn : Weights.act (Pw x) (ODEJointLCU.coefficientInput (seedCoefficients c) v) =
      ODEJointLCU.coefficientInput (ODESourceCoefficients.productCoeff π c) v :=
    Weights.act_coefficientInput (Pw x) none π hπ hπsum hPw c v
  have hPrep : prep (Pw x) (J x) φ (ODEJointLCU.coefficientInput (seedCoefficients c) v) =
      ODECoherentLCU.inputEmbedding (ODESourceCoefficients.productCoeff π c)
        (fun b => φ b.1 • J x b.1) v := by
    unfold prep
    rw [comp_apply, comp_apply, hIn]
    exact Weights.phase_loader_coefficientInput φ (J x) _ v
  -- the unpreparation half, as an adjoint identity
  have hOut : R ∘L ODESourceTransport.sourceGate (Weights.act (Pw x)) ∘L R ∘L
      ODECompiledSource.output E (seedCoefficients c) =
        ODECompiledSource.output E (ODESourceCoefficients.productCoeff π c) := by
    have h := ODESourceTransport.routed_source E hE (Weights.act (Pw x))
    unfold ODECompiledSource.output ODEJointLCU.output
    calc R ∘L ODESourceTransport.sourceGate (Weights.act (Pw x)) ∘L R ∘L
          (ODESourceTransport.matrixEmbedding ∘L E ∘L
            ODEJointLCU.coefficientOutput (seedCoefficients c))
        = (R ∘L ODESourceTransport.sourceGate (Weights.act (Pw x)) ∘L R ∘L
            ODESourceTransport.matrixEmbedding ∘L E) ∘L
            ODEJointLCU.coefficientOutput (seedCoefficients c) := by
          simp only [comp_assoc]
      _ = ODESourceTransport.matrixEmbedding ∘L E ∘L Weights.act (Pw x) ∘L
            ODEJointLCU.coefficientOutput (seedCoefficients c) := by
          rw [h]
          simp only [comp_assoc]
      _ = ODESourceTransport.matrixEmbedding ∘L E ∘L
            ODEJointLCU.coefficientOutput (ODESourceCoefficients.productCoeff π c) := by
          rw [show Weights.act (Pw x) ∘L ODEJointLCU.coefficientOutput (seedCoefficients c) =
              ODEJointLCU.coefficientOutput (ODESourceCoefficients.productCoeff π c) from
            Weights.act_comp_coefficientOutput (Pw x) none π hπ hπsum hPw c]
  have hOutAdj : (ODECompiledSource.output E (seedCoefficients c))† ∘L R ∘L
      ODESourceTransport.sourceGate (Weights.act ((Pw x)†)) ∘L R =
        (ODECompiledSource.output E (ODESourceCoefficients.productCoeff π c))† := by
    rw [← hOut, adjoint_comp, adjoint_comp, adjoint_comp, hR,
      ODESourceTransport.sourceGate_adjoint, Weights.act_adjoint]
    simp only [comp_assoc]
  rw [program_eval, ODESourceTransport.matrixProgram_eval_eq]
  simp only [sourceFamily, if_true, Bool.false_eq_true, if_false, mul_apply_eq_comp, comp_apply,
    ODECompiledSource.seed, ODEJointLCU.input]
  rw [← hRdef, hEncoded, hSource, hSourceRoute, hMatrix, hPrep]
  have hApply := congrArg (fun A : Physical ι P K N →L[ℂ] P =>
    A (ODESourceTransport.matrixEmbedding (p.eval x
      (E (ODECoherentLCU.inputEmbedding (ODESourceCoefficients.productCoeff π c)
        (fun b => φ b.1 • J x b.1) v))))) hOutAdj
  simp only [comp_apply] at hApply
  rw [hApply]
  unfold ODECompiledSource.output
  rw [adjoint_comp, comp_apply, hM]
  rfl

end Compiled

end

end SparseHamiltonian.GeneralSourceODE
