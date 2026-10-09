import DysonSingleProgram.Shape
import SparseHamiltonian.EncodedLabeledProgram

set_option autoImplicit false

/-!
# The compiled amplified trials have the amplification shape

Manuscript lines 4687-4689 (proof of Lemma `odel:lem:dyson`). The released Dyson trials are the
counted amplification programs `ODEGroverProgram.amplified p P Q j` of the logical preparation
`p`, compiled to the physical oracle by the encoded substitution
`EncodedLabeledProgram.compile E hE circuits` (fixed unitaries `U ↦ lift E U`, calls replaced by
their physical circuits). The compiler is a homomorphism of program syntax, so the compiled
family keeps the shape of `GroverShape`:

* `eval_compile_adjoint`: compiling the inverse program gives the adjoint operator
  (`SubspaceOracle.lift_adjoint`, `MultiOracleCircuit.Program.eval_adjoint`);
* `groverShape_compile`: the compiled trials have preparation `compile p`, fixed unitaries
  `lift E (-1)`, `lift E (phase P (-1))`, `lift E (phase Q (-1))` and every weighted cost
  `2j + 1` times that of `compile p`.
-/

namespace DysonSingleProgram.Explicit

noncomputable section
open SparseHamiltonian OracleCircuit PhaseSubspaceGates ContinuousLinearMap
open scoped InnerProduct

variable {P K X L M : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {F : M → X → K →L[ℂ] K} {O : L → X → P →L[ℂ] P}

/-- **The compiled inverse is the adjoint**: `compile (p†)` evaluates to `(compile p)†`. -/
theorem eval_compile_adjoint (E : P →L[ℂ] K) (hE : E† ∘L E = 1)
    (circuits : L → MultiOracleCircuit.Program F) (p : MultiOracleCircuit.Program O) (x : X) :
    (EncodedLabeledProgram.compile E hE circuits p.adjoint).eval x =
      star ((EncodedLabeledProgram.compile E hE circuits p).eval x) := by
  induction p with
  | fixed U hU =>
    change SubspaceOracle.lift E (star U) = star (SubspaceOracle.lift E U)
    rw [star_eq_adjoint, star_eq_adjoint, SubspaceOracle.lift_adjoint]
  | query l =>
    change ((circuits l).adjoint).eval x = star ((circuits l).eval x)
    exact MultiOracleCircuit.Program.eval_adjoint _ _
  | queryAdjoint l =>
    change (circuits l).eval x = star (((circuits l).adjoint).eval x)
    rw [MultiOracleCircuit.Program.eval_adjoint, star_star]
  | seq p q hp hq =>
    simp only [MultiOracleCircuit.Program.adjoint, EncodedLabeledProgram.compile,
      MultiOracleCircuit.Program.eval_seq, hp, hq, star_mul]

/-- **The compiled amplified trials have the amplification shape** (lines 4687-4689). -/
theorem groverShape_compile (E : P →L[ℂ] K) (hE : E† ∘L E = 1)
    (circuits : L → MultiOracleCircuit.Program F) (p : MultiOracleCircuit.Program O)
    (Pr Q : P →L[ℂ] P) (hP : IsOrthogonalProjection Pr) (hQ : IsOrthogonalProjection Q)
    (w : M → ℕ) :
    GroverShape
      (fun j => EncodedLabeledProgram.compile E hE circuits
        (ODEGroverProgram.amplified p Pr Q hP hQ j)) w
      (EncodedLabeledProgram.compile E hE circuits p) w
      (SubspaceOracle.lift E (-1)) (SubspaceOracle.lift E (phase Pr (-1)))
      (SubspaceOracle.lift E (phase Q (-1))) := by
  have hrep : ∀ (s : MultiOracleCircuit.Program O) (j : ℕ) (x : X),
      (EncodedLabeledProgram.compile E hE circuits (ODEGroverProgram.repeatProgram s j)).eval x =
        ((EncodedLabeledProgram.compile E hE circuits s).eval x) ^ j := by
    intro s j x
    induction j with
    | zero =>
      change SubspaceOracle.lift E 1 = _
      rw [SubspaceOracle.lift_one, pow_zero]
    | succ j ih =>
      simp only [ODEGroverProgram.repeatProgram, EncodedLabeledProgram.compile,
        MultiOracleCircuit.Program.eval_seq, ih, pow_succ]
  refine ⟨SubspaceOracle.lift_unitary E hE _ ODEGroverProgram.negative_identity_unitary,
    SubspaceOracle.lift_unitary E hE _ (phase_unitary Pr hP (-1) (by simp)),
    SubspaceOracle.lift_unitary E hE _ (phase_unitary Q hQ (-1) (by simp)), ?_, ?_⟩
  · intro j x
    simp only [ODEGroverProgram.amplified, EncodedLabeledProgram.compile,
      MultiOracleCircuit.Program.eval_seq, hrep]
    simp only [ODEGroverProgram.step, EncodedLabeledProgram.compile,
      MultiOracleCircuit.Program.eval_seq, MultiOracleCircuit.Program.eval_fixed,
      eval_compile_adjoint, mul_assoc]
  · intro j
    simp only [EncodedLabeledProgram.compile_cost, ODEGroverProgram.amplified_cost]

end

end DysonSingleProgram.Explicit
