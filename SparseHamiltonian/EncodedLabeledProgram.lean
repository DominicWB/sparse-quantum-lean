import SparseHamiltonian.ActualSparseAmplifier

/-!
# Encoded compilation preserving physical native oracle labels

Logical and physical programs may have different explicit query-label types and
different Hilbert workspaces. Each logical query is replaced by an actual
physical program; fixed gates use one common clean encoding. Exact weighted
counts are preserved without combining the native labels into SELECT access.
-/
namespace SparseHamiltonian.EncodedLabeledProgram

noncomputable section
open ContinuousLinearMap OracleCircuit
open scoped InnerProduct
set_option maxHeartbeats 800000

variable {P K : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {X L M : Type*}

/-- Compile every labeled logical instruction to an explicitly labeled physical
program. One fixed encoding is used throughout, including between different masks. -/
def compile {F : M → X → K →L[ℂ] K} {O : L → X → P →L[ℂ] P}
    (E : P →L[ℂ] K) (hE : E† ∘L E = 1)
    (circuits : L → MultiOracleCircuit.Program F) :
    MultiOracleCircuit.Program O → MultiOracleCircuit.Program F
  | .fixed U hU => .fixed _ (SubspaceOracle.lift_unitary E hE U hU)
  | .query l => circuits l
  | .queryAdjoint l => (circuits l).adjoint
  | .seq p q => .seq (compile E hE circuits p) (compile E hE circuits q)

/-- Exact total query cost after encoded substitution. -/
@[simp] theorem compile_count
    {F : M → X → K →L[ℂ] K} {O : L → X → P →L[ℂ] P}
    (E : P →L[ℂ] K) (hE : E† ∘L E = 1)
    (circuits : L → MultiOracleCircuit.Program F) (p : MultiOracleCircuit.Program O) :
    (compile E hE circuits p).count = p.cost (fun l => (circuits l).count) := by
  induction p with
  | fixed U hU => rfl
  | query l => rfl
  | queryAdjoint l => exact MultiOracleCircuit.Program.count_adjoint _
  | seq p q hp hq =>
    simp only [compile, MultiOracleCircuit.Program.count_seq,
      MultiOracleCircuit.Program.cost_seq, hp, hq]

/-- All primitive implementation costs remain visible in the final bound. -/
@[simp] theorem compile_cost
    {F : M → X → K →L[ℂ] K} {O : L → X → P →L[ℂ] P}
    (E : P →L[ℂ] K) (hE : E† ∘L E = 1)
    (circuits : L → MultiOracleCircuit.Program F) (p : MultiOracleCircuit.Program O)
    (w : M → ℕ) :
    (compile E hE circuits p).cost w = p.cost (fun l => (circuits l).cost w) := by
  induction p with
  | fixed U hU => rfl
  | query l => rfl
  | queryAdjoint l => exact MultiOracleCircuit.Program.cost_adjoint _ _
  | seq p q hp hq =>
    simp only [compile, MultiOracleCircuit.Program.cost_seq, hp, hq]

/-- Exact per-label counts follow by choosing indicator costs. -/
@[simp] theorem compile_labelCount [DecidableEq M]
    {F : M → X → K →L[ℂ] K} {O : L → X → P →L[ℂ] P}
    (E : P →L[ℂ] K) (hE : E† ∘L E = 1)
    (circuits : L → MultiOracleCircuit.Program F) (p : MultiOracleCircuit.Program O)
    (m : M) :
    (compile E hE circuits p).labelCount m =
      p.cost (fun l => (circuits l).labelCount m) :=
  compile_cost E hE circuits p _

/-- Correctness for an arbitrary coherent input, including every clean ancilla.
Adjoint queries use full physical and logical unitarity. -/
theorem compile_eval
    {F : M → X → K →L[ℂ] K} {O : L → X → P →L[ℂ] P}
    (E : P →L[ℂ] K) (hE : E† ∘L E = 1)
    (circuits : L → MultiOracleCircuit.Program F)
    (hF : ∀ m x, IsUnitary (F m x)) (hO : ∀ l x, IsUnitary (O l x))
    (hcircuits : ∀ l x, (circuits l).eval x ∘L E = E ∘L O l x)
    (p : MultiOracleCircuit.Program O) (x : X) :
    (compile E hE circuits p).eval x ∘L E = E ∘L p.eval x := by
  induction p with
  | fixed U hU => exact EncodedOracle.lift_comp E hE U
  | query l => exact hcircuits l x
  | queryAdjoint l =>
    change (circuits l).adjoint.eval x ∘L E = E ∘L star (O l x)
    rw [MultiOracleCircuit.Program.eval_adjoint]
    exact EncodedOracle.adjoint_intertwines _ _ E
      ((circuits l).eval_unitary hF x) (hO l x) (hcircuits l x)
  | seq p q hp hq =>
    change ((compile E hE circuits p).eval x ∘L
      (compile E hE circuits q).eval x) ∘L E = E ∘L (p.eval x ∘L q.eval x)
    rw [comp_assoc, hq, ← comp_assoc, hp, comp_assoc]

/-- Compressed physical evaluation is exactly the logical program. -/
theorem compile_compression
    {F : M → X → K →L[ℂ] K} {O : L → X → P →L[ℂ] P}
    (E : P →L[ℂ] K) (hE : E† ∘L E = 1)
    (circuits : L → MultiOracleCircuit.Program F)
    (hF : ∀ m x, IsUnitary (F m x)) (hO : ∀ l x, IsUnitary (O l x))
    (hcircuits : ∀ l x, (circuits l).eval x ∘L E = E ∘L O l x)
    (p : MultiOracleCircuit.Program O) (x : X) :
    E† ∘L (compile E hE circuits p).eval x ∘L E = p.eval x := by
  rw [compile_eval E hE circuits hF hO hcircuits,
    ← comp_assoc, hE]
  rfl

/-- Uniform clean-subspace substitution does not increase an output error. -/
theorem compile_error
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {F : M → X → K →L[ℂ] K} {O : L → X → P →L[ℂ] P}
    (E : P →L[ℂ] K) (hE : E† ∘L E = 1)
    (circuits : L → MultiOracleCircuit.Program F)
    (hF : ∀ m x, IsUnitary (F m x)) (hO : ∀ l x, IsUnitary (O l x))
    (hcircuits : ∀ l x, (circuits l).eval x ∘L E = E ∘L O l x)
    (p : MultiOracleCircuit.Program O) (J T : H →L[ℂ] P) (x : X) :
    ‖(compile E hE circuits p).eval x ∘L (E ∘L J) - E ∘L T‖ =
      ‖p.eval x ∘L J - T‖ := by
  rw [← comp_assoc, compile_eval E hE circuits hF hO hcircuits,
    comp_assoc, ← comp_sub]
  exact EncodedOracle.norm_comp_eq E hE _

end
end SparseHamiltonian.EncodedLabeledProgram
