import SparseHamiltonian.MultiOracleCircuit

/-!
# Compilation of several named oracles on one encoded subspace

Each logical oracle label has its own physical implementation certificate on
the same fixed isometric encoding. A logical multi-oracle program compiles to
an ordinary single-oracle physical program by inserting those implementations.
Fixed logical gates are extended by the identity on the orthogonal complement;
the queried physical programs need only be correct on the encoded subspace.
No coherently selected oracle or controlled query is assumed.
-/

namespace SparseHamiltonian.EncodedMultiOracle

noncomputable section

open ContinuousLinearMap OracleCircuit
open scoped InnerProduct

variable {P K : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {X L : Type*}

/-- Move a labeled program to a larger workspace while retaining exactly the
same labeled query instructions. Only its fixed gates are extended. -/
def liftProgram {F : L → X → K →L[ℂ] K} {O : L → X → P →L[ℂ] P}
    (E : P →L[ℂ] K) (hE : E† ∘L E = 1) :
    MultiOracleCircuit.Program O → MultiOracleCircuit.Program F
  | .fixed U hU => .fixed _ (SubspaceOracle.lift_unitary E hE U hU)
  | .query l => .query l
  | .queryAdjoint l => .queryAdjoint l
  | .seq p q => .seq (liftProgram E hE p) (liftProgram E hE q)

@[simp] theorem liftProgram_count {F : L → X → K →L[ℂ] K}
    {O : L → X → P →L[ℂ] P} (E : P →L[ℂ] K) (hE : E† ∘L E = 1)
    (p : MultiOracleCircuit.Program O) :
    (liftProgram (F := F) E hE p).count = p.count := by
  induction p with
  | fixed U hU => rfl
  | query l => rfl
  | queryAdjoint l => rfl
  | seq p q hp hq =>
      simp only [liftProgram, MultiOracleCircuit.Program.count_seq, hp, hq]

@[simp] theorem liftProgram_cost {F : L → X → K →L[ℂ] K}
    {O : L → X → P →L[ℂ] P} (E : P →L[ℂ] K) (hE : E† ∘L E = 1)
    (p : MultiOracleCircuit.Program O) (w : L → ℕ) :
    (liftProgram (F := F) E hE p).cost w = p.cost w := by
  induction p with
  | fixed U hU => rfl
  | query l => rfl
  | queryAdjoint l => rfl
  | seq p q hp hq =>
      simp only [liftProgram, MultiOracleCircuit.Program.cost_seq, hp, hq]

@[simp] theorem liftProgram_labelCount [DecidableEq L] {F : L → X → K →L[ℂ] K}
    {O : L → X → P →L[ℂ] P} (E : P →L[ℂ] K) (hE : E† ∘L E = 1)
    (p : MultiOracleCircuit.Program O) (l : L) :
    (liftProgram (F := F) E hE p).labelCount l = p.labelCount l :=
  liftProgram_cost E hE p _

/-- A label-preserving workspace change is correct on the encoded subspace
when each actual physical oracle intertwines with its logical counterpart. -/
theorem liftProgram_eval {F : L → X → K →L[ℂ] K}
    {O : L → X → P →L[ℂ] P} (E : P →L[ℂ] K) (hE : E† ∘L E = 1)
    (hF : ∀ l x, IsUnitary (F l x)) (hO : ∀ l x, IsUnitary (O l x))
    (h : ∀ l x, F l x ∘L E = E ∘L O l x)
    (p : MultiOracleCircuit.Program O) (x : X) :
    (liftProgram (F := F) E hE p).eval x ∘L E = E ∘L p.eval x := by
  induction p with
  | fixed U hU => exact EncodedOracle.lift_comp E hE U
  | query l => exact h l x
  | queryAdjoint l => exact EncodedOracle.adjoint_intertwines _ _ E (hF l x) (hO l x) (h l x)
  | seq p q hp hq =>
      change ((liftProgram E hE p).eval x ∘L
        (liftProgram E hE q).eval x) ∘L E = E ∘L (p.eval x ∘L q.eval x)
      rw [comp_assoc, hq, ← comp_assoc, hp, comp_assoc]

/-- Compile the named logical calls into ordinary physical oracle programs.
All fixed gates use the same input-independent encoding. -/
def compile {Q : X → K →L[ℂ] K} {O : L → X → P →L[ℂ] P}
    (E : P →L[ℂ] K) (hE : E† ∘L E = 1)
    (circuits : L → OracleCircuit.Program Q) :
    MultiOracleCircuit.Program O → OracleCircuit.Program Q
  | .fixed U hU => .fixed _ (SubspaceOracle.lift_unitary E hE U hU)
  | .query l => circuits l
  | .queryAdjoint l => (circuits l).adjoint
  | .seq p q => .seq (compile E hE circuits p) (compile E hE circuits q)

/-- The physical count is exactly the additive cost of all inserted circuits. -/
@[simp] theorem compile_count {Q : X → K →L[ℂ] K} {O : L → X → P →L[ℂ] P}
    (E : P →L[ℂ] K) (hE : E† ∘L E = 1)
    (circuits : L → OracleCircuit.Program Q) (p : MultiOracleCircuit.Program O) :
    (compile E hE circuits p).count = p.cost (fun l => (circuits l).count) := by
  induction p with
  | fixed U hU => rfl
  | query l => rfl
  | queryAdjoint l => exact OracleCircuit.Program.count_adjoint _
  | seq p q hp hq =>
      simp only [compile, OracleCircuit.Program.count_seq,
        MultiOracleCircuit.Program.cost_seq, hp, hq]

/-- Correctness on the encoded subspace is preserved throughout compilation.
Physical and logical unitarity justify replacing inverse calls by adjoints. -/
theorem compile_eval {Q : X → K →L[ℂ] K} {O : L → X → P →L[ℂ] P}
    (E : P →L[ℂ] K) (hE : E† ∘L E = 1)
    (circuits : L → OracleCircuit.Program Q)
    (hQ : ∀ x, IsUnitary (Q x)) (hO : ∀ l x, IsUnitary (O l x))
    (hcircuits : ∀ l x, (circuits l).eval x ∘L E = E ∘L O l x)
    (p : MultiOracleCircuit.Program O) (x : X) :
    (compile E hE circuits p).eval x ∘L E = E ∘L p.eval x := by
  induction p with
  | fixed U hU => exact EncodedOracle.lift_comp E hE U
  | query l => exact hcircuits l x
  | queryAdjoint l =>
      change (circuits l).adjoint.eval x ∘L E = E ∘L star (O l x)
      rw [OracleCircuit.Program.eval_adjoint]
      exact EncodedOracle.adjoint_intertwines _ _ E
        ((circuits l).eval_unitary hQ x) (hO l x) (hcircuits l x)
  | seq p q hp hq =>
      change ((compile E hE circuits p).eval x ∘L
        (compile E hE circuits q).eval x) ∘L E = E ∘L (p.eval x ∘L q.eval x)
      rw [comp_assoc, hq, ← comp_assoc, hp, comp_assoc]

/-- Separate encoded implementations suffice to compile the whole logical
program, with every oracle label charged its stated implementation budget. -/
theorem implements_compile {Q : X → K →L[ℂ] K} {O : L → X → P →L[ℂ] P}
    (E : P →L[ℂ] K) (hE : E† ∘L E = 1)
    (hQ : ∀ x, IsUnitary (Q x)) (hO : ∀ l x, IsUnitary (O l x))
    (p : MultiOracleCircuit.Program O) (w : L → ℕ)
    (h : ∀ l, EncodedOracle.ImplementsOn Q (O l) E (w l)) :
    EncodedOracle.ImplementsOn Q p.eval E (p.cost w) := by
  classical
  choose circuits heval hcount using h
  refine ⟨compile E hE circuits p, compile_eval E hE circuits hQ hO heval p, ?_⟩
  rw [compile_count]
  exact p.cost_mono hcount

/-- If every named oracle has the same physical query budget, compilation
costs at most the logical query count times that budget. -/
theorem implements_compile_uniform {Q : X → K →L[ℂ] K} {O : L → X → P →L[ℂ] P}
    (E : P →L[ℂ] K) (hE : E† ∘L E = 1)
    (hQ : ∀ x, IsUnitary (Q x)) (hO : ∀ l x, IsUnitary (O l x))
    (p : MultiOracleCircuit.Program O) (q : ℕ)
    (h : ∀ l, EncodedOracle.ImplementsOn Q (O l) E q) :
    EncodedOracle.ImplementsOn Q p.eval E (p.count * q) := by
  simpa using implements_compile E hE hQ hO p (fun _ => q) h

/-- A multi-oracle implementation can be transported into one physical oracle
model using independently supplied subspace implementations of its labels. -/
theorem trans {Q : X → K →L[ℂ] K} {O : L → X → P →L[ℂ] P}
    {F : X → P →L[ℂ] P} {q r : ℕ}
    (E : P →L[ℂ] K) (hE : E† ∘L E = 1)
    (hQ : ∀ x, IsUnitary (Q x)) (hO : ∀ l x, IsUnitary (O l x))
    (hF : MultiOracleCircuit.Implements O F r)
    (h : ∀ l, EncodedOracle.ImplementsOn Q (O l) E q) :
    EncodedOracle.ImplementsOn Q F E (r * q) := by
  obtain ⟨p, hp, hr⟩ := hF
  exact ((implements_compile_uniform E hE hQ hO p q h).congr hp).mono
    (Nat.mul_le_mul_right q hr)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Any logical full-output error estimate transfers to the compiled physical
program on the encoded inputs, with the exact weighted query allowance. -/
theorem output_error_certificate {Q : X → K →L[ℂ] K}
    {O : L → X → P →L[ℂ] P}
    (E : P →L[ℂ] K) (hE : E† ∘L E = 1)
    (hQ : ∀ x, IsUnitary (Q x)) (hO : ∀ l x, IsUnitary (O l x))
    (p : MultiOracleCircuit.Program O) (w : L → ℕ)
    (h : ∀ l, EncodedOracle.ImplementsOn Q (O l) E (w l))
    (J T : X → H →L[ℂ] P) (ε : ℝ)
    (hError : ∀ x, ‖p.eval x ∘L J x - T x‖ ≤ ε) :
    ∃ c : OracleCircuit.Program Q, c.count ≤ p.cost w ∧
      ∀ x, ‖c.eval x ∘L (E ∘L J x) - E ∘L T x‖ ≤ ε :=
  (implements_compile E hE hQ hO p w h).error_certificate hE J T ε hError

end

end SparseHamiltonian.EncodedMultiOracle
