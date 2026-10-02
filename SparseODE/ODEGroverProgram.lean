import SparseODE.ODEGroverDirection

/-!
# Counted Grover programs over the original oracle vocabulary

All appearances of the input-dependent preparation and its inverse remain
explicit program calls. Only the two fixed subspace phases and a global sign
are free gates. The exact cost identity applies to arbitrary label weights,
so it also counts source-preparation oracles when included in the vocabulary.
-/

namespace SparseHamiltonian.ODEGroverProgram

noncomputable section

open OracleCircuit PhaseSubspaceGates
open scoped InnerProduct

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [CompleteSpace K]
variable {X L : Type*} {O : L → X → K →L[ℂ] K}

/-- The signed Grover step, with the preparation-conjugated input reflection. -/
def operator (U P Q : K →L[ℂ] K) : K →L[ℂ] K :=
  -(U * phase P (-1) * star U * phase Q (-1))

omit [CompleteSpace K] in
theorem phase_neg_one (P : K →L[ℂ] K) :
    phase P (-1) = 1 - (2 : ℂ) • P := by
  unfold phase
  module

/-- This identifies the actual circuit convention with the output-plane
reflection convention. It is only an operator identity, not a free-gate rule. -/
theorem operator_eq_conjugated (U P Q : K →L[ℂ] K) (hU : IsUnitary U) :
    operator U P Q =
      ((2 : ℂ) • (U * P * star U) - 1) * (1 - (2 : ℂ) • Q) := by
  unfold operator
  rw [← phase_conjugate P U hU, phase_neg_one, phase_neg_one]
  calc
    -((1 - (2 : ℂ) • (U * P * star U)) * (1 - (2 : ℂ) • Q)) =
        (-(1 - (2 : ℂ) • (U * P * star U))) * (1 - (2 : ℂ) • Q) :=
      (neg_mul _ _).symm
    _ = _ := by congr 1; module

theorem operator_eq_grover (U P Q : K →L[ℂ] K) (hU : IsUnitary U) :
    operator U P Q = ODEGroverPlane.grover (U * P * star U) Q :=
  operator_eq_conjugated U P Q hU

theorem negative_identity_unitary : IsUnitary (- (1 : K →L[ℂ] K)) := by
  constructor <;> simp

/-- One signed step contains one forward and one inverse preparation. -/
def step (p : MultiOracleCircuit.Program O) (P Q : K →L[ℂ] K)
    (hP : IsOrthogonalProjection P) (hQ : IsOrthogonalProjection Q) :
    MultiOracleCircuit.Program O :=
  .seq (.fixed (-1) negative_identity_unitary)
    (.seq (.seq (.seq p (.fixed (phase P (-1))
      (phase_unitary P hP (-1) (by simp)))) p.adjoint)
      (.fixed (phase Q (-1)) (phase_unitary Q hQ (-1) (by simp))))

@[simp] theorem step_eval (p : MultiOracleCircuit.Program O)
    (P Q : K →L[ℂ] K) (hP : IsOrthogonalProjection P)
    (hQ : IsOrthogonalProjection Q) (x : X) :
    (step p P Q hP hQ).eval x = operator (p.eval x) P Q := by
  simp only [step, MultiOracleCircuit.Program.eval_seq,
    MultiOracleCircuit.Program.eval_fixed, MultiOracleCircuit.Program.eval_adjoint,
    neg_one_mul, operator]

theorem step_eq_grover (p : MultiOracleCircuit.Program O)
    (P Q : K →L[ℂ] K) (hP : IsOrthogonalProjection P)
    (hQ : IsOrthogonalProjection Q) (x : X) (hU : IsUnitary (p.eval x)) :
    (step p P Q hP hQ).eval x =
      ODEGroverPlane.grover (p.eval x * P * star (p.eval x)) Q := by
  rw [step_eval]
  exact operator_eq_grover (p.eval x) P Q hU

@[simp] theorem step_cost (p : MultiOracleCircuit.Program O)
    (P Q : K →L[ℂ] K) (hP : IsOrthogonalProjection P)
    (hQ : IsOrthogonalProjection Q) (w : L → ℕ) :
    (step p P Q hP hQ).cost w = 2 * p.cost w := by
  simp [step, two_mul]

/-- Repetition is a syntax tree, rather than a power assigned a cost afterwards. -/
def repeatProgram (p : MultiOracleCircuit.Program O) : ℕ → MultiOracleCircuit.Program O
  | 0 => MultiOracleCircuit.Program.identity
  | n + 1 => .seq (repeatProgram p n) p

@[simp] theorem repeat_eval (p : MultiOracleCircuit.Program O) (j : ℕ) (x : X) :
    (repeatProgram p j).eval x = (p.eval x) ^ j := by
  induction j with
  | zero => simp [repeatProgram]
  | succ j ih => simp only [repeatProgram, MultiOracleCircuit.Program.eval_seq, ih, pow_succ]

@[simp] theorem repeat_cost (p : MultiOracleCircuit.Program O) (j : ℕ) (w : L → ℕ) :
    (repeatProgram p j).cost w = j * p.cost w := by
  induction j with
  | zero => simp [repeatProgram]
  | succ j ih =>
      simp only [repeatProgram, MultiOracleCircuit.Program.cost_seq, ih, Nat.succ_mul]

/-- The initial preparation is counted as well as the subsequent Grover steps. -/
def amplified (p : MultiOracleCircuit.Program O) (P Q : K →L[ℂ] K)
    (hP : IsOrthogonalProjection P) (hQ : IsOrthogonalProjection Q) (j : ℕ) :
    MultiOracleCircuit.Program O :=
  .seq (repeatProgram (step p P Q hP hQ) j) p

@[simp] theorem amplified_eval (p : MultiOracleCircuit.Program O)
    (P Q : K →L[ℂ] K) (hP : IsOrthogonalProjection P)
    (hQ : IsOrthogonalProjection Q) (j : ℕ) (x : X) :
    (amplified p P Q hP hQ j).eval x = operator (p.eval x) P Q ^ j * p.eval x := by
  simp only [amplified, MultiOracleCircuit.Program.eval_seq, repeat_eval, step_eval]

theorem amplified_eval_grover (p : MultiOracleCircuit.Program O)
    (P Q : K →L[ℂ] K) (hP : IsOrthogonalProjection P)
    (hQ : IsOrthogonalProjection Q) (j : ℕ) (x : X)
    (hU : IsUnitary (p.eval x)) :
    (amplified p P Q hP hQ j).eval x =
      ODEGroverPlane.grover (p.eval x * P * star (p.eval x)) Q ^ j * p.eval x := by
  rw [amplified_eval, operator_eq_grover (p.eval x) P Q hU]

/-- Arbitrary weighted query costs acquire exactly the same odd factor. -/
@[simp] theorem amplified_cost (p : MultiOracleCircuit.Program O)
    (P Q : K →L[ℂ] K) (hP : IsOrthogonalProjection P)
    (hQ : IsOrthogonalProjection Q) (j : ℕ) (w : L → ℕ) :
    (amplified p P Q hP hQ j).cost w = (2 * j + 1) * p.cost w := by
  simp only [amplified, MultiOracleCircuit.Program.cost_seq, repeat_cost, step_cost]
  ring

@[simp] theorem amplified_count (p : MultiOracleCircuit.Program O)
    (P Q : K →L[ℂ] K) (hP : IsOrthogonalProjection P)
    (hQ : IsOrthogonalProjection Q) (j : ℕ) :
    (amplified p P Q hP hQ j).count = (2 * j + 1) * p.count := by
  simpa using amplified_cost p P Q hP hQ j (fun _ => 1)

@[simp] theorem amplified_labelCount [DecidableEq L]
    (p : MultiOracleCircuit.Program O) (P Q : K →L[ℂ] K)
    (hP : IsOrthogonalProjection P) (hQ : IsOrthogonalProjection Q)
    (j : ℕ) (l : L) :
    (amplified p P Q hP hQ j).labelCount l = (2 * j + 1) * p.labelCount l :=
  amplified_cost p P Q hP hQ j _

/-- Full physical unitarity follows from the native oracle semantics. -/
theorem amplified_unitary (p : MultiOracleCircuit.Program O)
    (P Q : K →L[ℂ] K) (hP : IsOrthogonalProjection P)
    (hQ : IsOrthogonalProjection Q) (j : ℕ)
    (hO : ∀ l x, IsUnitary (O l x)) (x : X) :
    IsUnitary ((amplified p P Q hP hQ j).eval x) :=
  (amplified p P Q hP hQ j).eval_unitary hO x

/-- Every possible randomized iteration count satisfies the same worst-case
bound, including source-oracle costs assigned by the weight function. -/
theorem amplified_cost_le (p : MultiOracleCircuit.Program O)
    (P Q : K →L[ℂ] K) (hP : IsOrthogonalProjection P)
    (hQ : IsOrthogonalProjection Q) (j M : ℕ) (g : ℝ)
    (hj : j < M) (hM : (M : ℝ) ≤ 5 * g) (w : L → ℕ) :
    ((amplified p P Q hP hQ j).cost w : ℝ) ≤ 10 * g * (p.cost w : ℝ) := by
  have hnat : 2 * j + 1 ≤ 2 * M := by omega
  have hreal : ((2 * j + 1 : ℕ) : ℝ) ≤ 2 * (M : ℝ) := by
    exact_mod_cast hnat
  have hfactor : ((2 * j + 1 : ℕ) : ℝ) ≤ 10 * g := by linarith
  rw [amplified_cost, Nat.cast_mul]
  exact mul_le_mul_of_nonneg_right hfactor (Nat.cast_nonneg _)

theorem amplified_count_le (p : MultiOracleCircuit.Program O)
    (P Q : K →L[ℂ] K) (hP : IsOrthogonalProjection P)
    (hQ : IsOrthogonalProjection Q) (j M : ℕ) (g : ℝ)
    (hj : j < M) (hM : (M : ℝ) ≤ 5 * g) :
    ((amplified p P Q hP hQ j).count : ℝ) ≤ 10 * g * (p.count : ℝ) := by
  simpa using amplified_cost_le p P Q hP hQ j M g hj hM (fun _ => 1)

end
end SparseHamiltonian.ODEGroverProgram
