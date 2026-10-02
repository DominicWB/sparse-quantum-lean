import SparseHamiltonian.LabeledSimulationTransfer

/-!
# Adjoint simulation at negative time with complete output control

Adjointing a unitary implementation swaps its fixed input and output
encodings. The full-output operator error is preserved exactly, as are all
native primitive query counts. No projection onto a successful block is used.
-/
namespace SparseHamiltonian.LabeledAdjointSimulation
noncomputable section
open ContinuousLinearMap OracleCircuit
open scoped InnerProduct
set_option maxHeartbeats 800000

variable {P K : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {X Label : Type*}

/-- Right multiplication by a unitary preserves rectangular operator norms. -/
theorem norm_comp_unitary_right (A : P →L[ℂ] K) (V : P →L[ℂ] P) (hV : IsUnitary V) :
    ‖A ∘L V‖ = ‖A‖ := by
  calc
    ‖A ∘L V‖ = ‖(A ∘L V)†‖ := (LinearIsometryEquiv.norm_map _ _).symm
    _ = ‖V† ∘L A†‖ := by rw [adjoint_comp]
    _ = ‖A†‖ := EncodedOracle.norm_comp_eq (V†) (by simpa only [← star_eq_adjoint, ← mul_def, star_star] using hV.2) (A†)
    _ = ‖A‖ := LinearIsometryEquiv.norm_map _ _

/-- Unitary reversal preserves the entire input-to-output error, with encodings swapped. -/
theorem adjoint_error_eq (U : K →L[ℂ] K) (V : P →L[ℂ] P)
    (hU : IsUnitary U) (hV : IsUnitary V) (input output : P →L[ℂ] K) :
    ‖U† ∘L output - input ∘L V†‖ = ‖U ∘L input - output ∘L V‖ := by
  have hUf (v : K) : (U†) (U v) = v := congrArg (fun T : K →L[ℂ] K => T v) hU.1
  have hVf (v : P) : V ((V†) v) = v := congrArg (fun T : P →L[ℂ] P => T v) hV.2
  have heq : U† ∘L output - input ∘L V† =
      (U† ∘L (output ∘L V - U ∘L input)) ∘L V† := by
    ext v
    simp only [comp_apply, sub_apply, map_sub, hVf, hUf]
  rw [heq, norm_comp_unitary_right _ (V†) hV.adjoint,
    EncodedOracle.norm_comp_eq (U†) (by simpa only [← star_eq_adjoint, ← mul_def, star_star] using hU.2), norm_sub_rev]

/-- Syntactic adjoint reversal has the exact full-output error for every oracle input. -/
theorem program_adjoint_error_eq {F : Label → X → K →L[ℂ] K}
    (p : MultiOracleCircuit.Program F) (hF : ∀ l x, IsUnitary (F l x))
    (input output : P →L[ℂ] K) (V : X → P →L[ℂ] P)
    (hV : ∀ x, IsUnitary (V x)) (x : X) :
    ‖p.adjoint.eval x ∘L output - input ∘L (V x)†‖ =
      ‖p.eval x ∘L input - output ∘L V x‖ := by
  rw [MultiOracleCircuit.Program.eval_adjoint]
  exact adjoint_error_eq (p.eval x) (V x) (p.eval_unitary hF x) (hV x) input output

/-- A self-adjoint Hamiltonian generates a genuine two-sided unitary. -/
theorem evolution_unitary (H : P →L[ℂ] P) (hH : star H = H) (t : ℝ) :
    IsUnitary (NormedSpace.exp ((-Complex.I * (t : ℂ)) • H)) := by
  letI : NormedAlgebra ℚ (P →L[ℂ] P) := .restrictScalars ℚ ℂ _
  apply Unitary.mem_iff.mp
  apply NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
  apply skewAdjoint.mem_iff.mpr
  simp [star_smul, hH]

/-- Adjointing the evolution changes exactly the sign of its time. -/
theorem evolution_adjoint (H : P →L[ℂ] P) (hH : star H = H) (t : ℝ) :
    (NormedSpace.exp ((-Complex.I * (t : ℂ)) • H))† =
      NormedSpace.exp ((-Complex.I * ((-t : ℝ) : ℂ)) • H) := by
  rw [← star_eq_adjoint, NormedSpace.star_exp]
  simp [star_smul, hH]

/-- The same actual native circuit, reversed, simulates the opposite time. -/
theorem program_negative_time_error {F : Label → X → K →L[ℂ] K}
    (p : MultiOracleCircuit.Program F) (hF : ∀ l x, IsUnitary (F l x))
    (input output : P →L[ℂ] K) (H : X → P →L[ℂ] P)
    (hH : ∀ x, star (H x) = H x) (t ε : ℝ)
    (hSim : ∀ x, ‖p.eval x ∘L input - output ∘L
      NormedSpace.exp ((-Complex.I * (t : ℂ)) • H x)‖ ≤ ε) :
    ∀ x, ‖p.adjoint.eval x ∘L output - input ∘L
      NormedSpace.exp ((-Complex.I * ((-t : ℝ) : ℂ)) • H x)‖ ≤ ε := by
  intro x
  rw [← evolution_adjoint (H x) (hH x) t,
    program_adjoint_error_eq p hF input output _ (fun x => evolution_unitary (H x) (hH x) t) x]
  exact hSim x

/-- Time's sign chooses a whole circuit, never an input-dependent gate. -/
def signedProgram {F : Label → X → K →L[ℂ] K}
    (p : MultiOracleCircuit.Program F) (t : ℝ) : MultiOracleCircuit.Program F :=
  if 0 ≤ t then p else p.adjoint

/-- Reverse time swaps the two fixed preparations. -/
def signedInput (input output : P →L[ℂ] K) (t : ℝ) : P →L[ℂ] K :=
  if 0 ≤ t then input else output

def signedOutput (input output : P →L[ℂ] K) (t : ℝ) : P →L[ℂ] K :=
  if 0 ≤ t then output else input

@[simp] theorem signedProgram_count {F : Label → X → K →L[ℂ] K}
    (p : MultiOracleCircuit.Program F) (t : ℝ) : (signedProgram p t).count = p.count := by
  unfold signedProgram
  split_ifs <;> simp

@[simp] theorem signedProgram_cost {F : Label → X → K →L[ℂ] K}
    (p : MultiOracleCircuit.Program F) (t : ℝ) (w : Label → ℕ) :
    (signedProgram p t).cost w = p.cost w := by
  unfold signedProgram
  split_ifs <;> simp

/-- A nonnegative-time certificate at `|t|` gives arbitrary real time at identical native cost. -/
theorem signed_program_error {F : Label → X → K →L[ℂ] K}
    (p : MultiOracleCircuit.Program F) (hF : ∀ l x, IsUnitary (F l x))
    (input output : P →L[ℂ] K) (H : X → P →L[ℂ] P)
    (hH : ∀ x, star (H x) = H x) (t ε : ℝ)
    (hSim : ∀ x, ‖p.eval x ∘L input - output ∘L
      NormedSpace.exp ((-Complex.I * ((|t| : ℝ) : ℂ)) • H x)‖ ≤ ε) :
    ∀ x, ‖(signedProgram p t).eval x ∘L signedInput input output t -
      signedOutput input output t ∘L
        NormedSpace.exp ((-Complex.I * (t : ℂ)) • H x)‖ ≤ ε := by
  by_cases ht : 0 ≤ t
  · simpa only [signedProgram, signedInput, signedOutput, if_pos ht, abs_of_nonneg ht] using hSim
  · have hn : -|t| = t := by rw [abs_of_neg (lt_of_not_ge ht)]; ring
    have h := program_negative_time_error p hF input output H hH |t| ε hSim
    simpa only [signedProgram, signedInput, signedOutput, if_neg ht, hn] using h

/-- Sign selection preserves isometric input and output preparations. -/
theorem signed_isometries (input output : P →L[ℂ] K)
    (hI : input† ∘L input = 1) (hO : output† ∘L output = 1) (t : ℝ) :
    (signedInput input output t)† ∘L signedInput input output t = 1 ∧
      (signedOutput input output t)† ∘L signedOutput input output t = 1 := by
  by_cases ht : 0 ≤ t <;> simp [signedInput, signedOutput, ht, hI, hO]

end
end SparseHamiltonian.LabeledAdjointSimulation
