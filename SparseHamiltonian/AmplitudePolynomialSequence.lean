import SparseHamiltonian.PhaseSubspaceGates

/-!
# Forward amplitude polynomials of phase sequences

A real signal rotation is alternated with fixed phases on the clean and good
coordinates. Each two-query step is `R D(a) R† D(c)`. Starting with `R |0⟩`,
the first column has the exact form `(P(λ), sqrt(1-λ²) Q(λ))`. The recurrence
below constructs these polynomials, proves their odd/even parity and degree
bounds, and bounds the good amplitude by one using the actual unitary circuit.

These are forward statements for given phase sequences. They do not assert
phase synthesis, approximation to a target function, or amplitude gain.
-/

namespace SparseHamiltonian.AmplitudePolynomialSequence

noncomputable section
open Polynomial ContinuousLinearMap OracleCircuit ComplexAmplitudeRotation
open scoped InnerProduct ComplexConjugate

/-- A phase is fixed independently of the unknown signal. -/
abbrev UnitPhase := {z : ℂ // ‖z‖ = 1}

/-- The two phases applied during one Grover-type iteration. -/
abbrev Phases := UnitPhase × UnitPhase

/-- Phase on the false (clean/good) coordinate. -/
def phase (a : ℂ) : Qubit →L[ℂ] Qubit := matrix a 0 0 1

@[simp] theorem phase_false (a : ℂ) (v : Qubit) : phase a v false = a * v false := by
  simp [phase]

@[simp] theorem phase_true (a : ℂ) (v : Qubit) : phase a v true = v true := by
  simp [phase]

/-- A modulus-one phase gives a full-space unitary gate. -/
theorem phase_unitary (a : UnitPhase) : IsUnitary (phase a) := by
  have ha : (a : ℂ) * conj (a : ℂ) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, a.property]
    norm_num
  have ha' : conj (a : ℂ) * (a : ℂ) = 1 := by simpa only [mul_comm] using ha
  constructor
  · ext v b
    cases b <;> simp [phase, ContinuousLinearMap.star_eq_adjoint, matrix_adjoint, ← mul_assoc, ha']
  · ext v b
    cases b <;> simp [phase, ContinuousLinearMap.star_eq_adjoint, matrix_adjoint, ← mul_assoc, ha]

/-- Polynomial recurrence for the good coordinate. -/
def nextGood (a c : ℂ) (P Q : ℂ[X]) : ℂ[X] :=
  C c * (1 + C (a - 1) * X ^ 2) * P + C (a - 1) * X * (1 - X ^ 2) * Q

/-- Polynomial recurrence for the bad coordinate after factoring out the square root. -/
def nextBad (a c : ℂ) (P Q : ℂ[X]) : ℂ[X] :=
  C c * C (a - 1) * X * P + (C a + C (1 - a) * X ^ 2) * Q

/-- Starting with `(X,1)`, each list entry adds one two-query iteration.
The list head is the last iteration executed. -/
def polynomials : List Phases → ℂ[X] × ℂ[X]
  | [] => (X, 1)
  | s :: ss =>
      (nextGood s.1 s.2 (polynomials ss).1 (polynomials ss).2,
       nextBad s.1 s.2 (polynomials ss).1 (polynomials ss).2)

/-- Each good-coordinate update increases the allowed odd degree by two. -/
theorem nextGood_degree (a c : ℂ) (P Q : ℂ[X]) (n : ℕ)
    (hP : P.natDegree ≤ 2 * n + 1) (hQ : Q.natDegree ≤ 2 * n) :
    (nextGood a c P Q).natDegree ≤ 2 * (n + 1) + 1 := by
  have hX2 : (X ^ 2 : ℂ[X]).natDegree ≤ 2 := natDegree_X_pow_le 2
  have hA : (1 + C (a - 1) * X ^ 2 : ℂ[X]).natDegree ≤ 2 := by
    apply (natDegree_add_le _ _).trans
    apply max_le
    · simp
    · exact natDegree_mul_le.trans (by simpa only [natDegree_C, zero_add] using hX2)
  have hB : (C (a - 1) * X * (1 - X ^ 2) : ℂ[X]).natDegree ≤ 3 := by
    have hD : (1 - X ^ 2 : ℂ[X]).natDegree ≤ 2 :=
      (natDegree_sub_le _ _).trans (max_le (by simp) hX2)
    have hC : (C (a - 1) * X : ℂ[X]).natDegree ≤ 1 :=
      natDegree_mul_le.trans (by simp only [natDegree_C, natDegree_X, zero_add, le_refl])
    exact natDegree_mul_le.trans (by omega)
  unfold nextGood
  apply (natDegree_add_le _ _).trans
  apply max_le
  · have hCA : (C c * (1 + C (a - 1) * X ^ 2) : ℂ[X]).natDegree ≤ 2 :=
      natDegree_mul_le.trans (by simpa only [natDegree_C, zero_add] using hA)
    exact natDegree_mul_le.trans (by omega)
  · exact natDegree_mul_le.trans (by omega)

/-- The factored bad coordinate has even degree at most twice the step count. -/
theorem nextBad_degree (a c : ℂ) (P Q : ℂ[X]) (n : ℕ)
    (hP : P.natDegree ≤ 2 * n + 1) (hQ : Q.natDegree ≤ 2 * n) :
    (nextBad a c P Q).natDegree ≤ 2 * (n + 1) := by
  have hA : (C c * C (a - 1) * X : ℂ[X]).natDegree ≤ 1 := by
    rw [← C_mul]
    exact natDegree_mul_le.trans (by simp only [natDegree_C, natDegree_X, zero_add, le_refl])
  have hB : (C a + C (1 - a) * X ^ 2 : ℂ[X]).natDegree ≤ 2 := by
    apply (natDegree_add_le _ _).trans
    apply max_le
    · simp
    · exact natDegree_mul_le.trans (by simp only [natDegree_C, natDegree_X_pow, zero_add, le_refl])
  unfold nextBad
  apply (natDegree_add_le _ _).trans
  apply max_le
  · exact natDegree_mul_le.trans (by omega)
  · exact natDegree_mul_le.trans (by omega)

/-- Sharp forward degree budgets: at most `2m+1` and `2m`. -/
theorem degree_bounds (ss : List Phases) :
    (polynomials ss).1.natDegree ≤ 2 * ss.length + 1 ∧
    (polynomials ss).2.natDegree ≤ 2 * ss.length := by
  induction ss with
  | nil => simp [polynomials]
  | cons s ss ih =>
      exact ⟨nextGood_degree _ _ _ _ _ ih.1 ih.2,
        nextBad_degree _ _ _ _ _ ih.1 ih.2⟩

/-- Algebraic parity, expressed directly by substitution `X ↦ -X`. -/
theorem parity (ss : List Phases) :
    (polynomials ss).1.comp (-X) = -(polynomials ss).1 ∧
    (polynomials ss).2.comp (-X) = (polynomials ss).2 := by
  induction ss with
  | nil => simp [polynomials]
  | cons s ss ih =>
      simp only [polynomials, nextGood, nextBad, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.sub_comp,
        pow_comp, one_comp, C_comp, X_comp, ih.1, ih.2]
      constructor <;> ring

/-- The good polynomial is odd as a function of the complex signal variable. -/
theorem good_odd (ss : List Phases) :
    Function.Odd (fun z : ℂ => (polynomials ss).1.eval z) := by
  intro z
  have h := congrArg (Polynomial.eval z) (parity ss).1
  simpa using h

/-- The factored bad polynomial is even as a function of the complex signal variable. -/
theorem bad_even (ss : List Phases) :
    Function.Even (fun z : ℂ => (polynomials ss).2.eval z) := by
  intro z
  have h := congrArg (Polynomial.eval z) (parity ss).2
  simpa using h

/-- The actual two-query step in output coordinates. -/
def step (x : ℝ) (s : Phases) : Qubit →L[ℂ] Qubit :=
  rotation (x : ℂ) * phase s.1 * (rotation (x : ℂ))† * phase s.2

/-- The actual product, including the initial preparation rotation. -/
def sequence (x : ℝ) : List Phases → Qubit →L[ℂ] Qubit
  | [] => rotation (x : ℂ)
  | s :: ss => step x s * sequence x ss

/-- The square root is eliminated by the real signal normalization identity. -/
theorem badAmplitude_square (x : ℝ) (hx : |x| ≤ 1) :
    (badAmplitude (x : ℂ) : ℂ) ^ 2 = 1 - (x : ℂ) ^ 2 := by
  have h := coefficient_sum (x : ℂ) (by simpa using hx)
  simp only [Complex.conj_ofReal] at h
  linear_combination h

/-- A polynomial pair describes the complete first column, including the bad flag. -/
def column (x : ℝ) (P Q : ℂ[X]) : Qubit :=
  WithLp.toLp 2 (fun b : Bool =>
    if b then (badAmplitude (x : ℂ) : ℂ) * Q.eval (x : ℂ) else P.eval (x : ℂ))

@[simp] theorem column_false (x : ℝ) (P Q : ℂ[X]) :
    column x P Q false = P.eval (x : ℂ) := rfl

@[simp] theorem column_true (x : ℝ) (P Q : ℂ[X]) :
    column x P Q true = (badAmplitude (x : ℂ) : ℂ) * Q.eval (x : ℂ) := rfl

/-- One physical iteration realizes exactly one polynomial recurrence. -/
theorem step_column (x : ℝ) (hx : |x| ≤ 1) (s : Phases) (P Q : ℂ[X]) :
    step x s (column x P Q) = column x (nextGood s.1 s.2 P Q) (nextBad s.1 s.2 P Q) := by
  have hμ := badAmplitude_square x hx
  have hμ3 : (badAmplitude (x : ℂ) : ℂ) ^ 3 =
      (badAmplitude (x : ℂ) : ℂ) * (1 - (x : ℂ) ^ 2) := by
    rw [pow_succ, hμ]
    ring
  apply PiLp.ext
  intro b
  cases b <;>
    simp only [step, mul_apply_eq_comp, rotation_false, rotation_true,
      rotation_adjoint, phase_false, phase_true, matrix_false, matrix_true,
      Complex.conj_ofReal, column_false, column_true, nextGood, nextBad,
      eval_add, eval_mul, eval_C, eval_sub, eval_one, eval_pow, eval_X] <;>
    ring_nf <;> simp only [hμ, hμ3] <;> ring

/-- Exact evaluation of the complete phase circuit on its clean input. -/
theorem sequence_column (x : ℝ) (hx : |x| ≤ 1) (ss : List Phases) :
    sequence x ss clean = column x (polynomials ss).1 (polynomials ss).2 := by
  induction ss with
  | nil =>
      apply PiLp.ext
      intro b
      cases b <;> simp [sequence, polynomials]
  | cons s ss ih =>
      simpa only [sequence, mul_apply_eq_comp, ih, polynomials] using
        step_column x hx s (polynomials ss).1 (polynomials ss).2

/-- In particular the good amplitude is the constructed polynomial. -/
theorem good_amplitude (x : ℝ) (hx : |x| ≤ 1) (ss : List Phases) :
    sequence x ss clean false = (polynomials ss).1.eval (x : ℂ) := by
  rw [sequence_column x hx ss, column_false]

/-- The complementary coordinate retains exactly one square-root factor. -/
theorem bad_amplitude (x : ℝ) (hx : |x| ≤ 1) (ss : List Phases) :
    sequence x ss clean true =
      (badAmplitude (x : ℂ) : ℂ) * (polynomials ss).2.eval (x : ℂ) := by
  rw [sequence_column x hx ss, column_true]

/-- Every step is unitary throughout the real signal interval. -/
theorem step_unitary (x : ℝ) (hx : |x| ≤ 1) (s : Phases) : IsUnitary (step x s) := by
  have hR := rotation_unitary (x : ℂ) (by simpa using hx)
  exact ((hR.mul (phase_unitary s.1)).mul hR.adjoint).mul (phase_unitary s.2)

/-- Unitarity is proved for the actual product, with no synthesized-polynomial assumption. -/
theorem sequence_unitary (x : ℝ) (hx : |x| ≤ 1) (ss : List Phases) :
    IsUnitary (sequence x ss) := by
  induction ss with
  | nil => exact rotation_unitary (x : ℂ) (by simpa using hx)
  | cons s ss ih => exact (step_unitary x hx s).mul ih

@[simp] theorem clean_norm : ‖clean‖ = 1 := by
  simp [PiLp.norm_eq_of_L2]

/-- Every forward polynomial is bounded by one on the signal interval. -/
theorem good_norm_le_one (x : ℝ) (hx : |x| ≤ 1) (ss : List Phases) :
    ‖(polynomials ss).1.eval (x : ℂ)‖ ≤ 1 := by
  calc
    ‖(polynomials ss).1.eval (x : ℂ)‖ = ‖sequence x ss clean false‖ := by
      rw [good_amplitude x hx ss]
    _ ≤ ‖sequence x ss clean‖ := PiLp.norm_apply_le _ false
    _ = 1 := by
      rw [(norm_map_iff_adjoint_comp_self _).mpr (sequence_unitary x hx ss).1, clean_norm]

/-- The exact complementary-polynomial identity forced by circuit unitarity. -/
theorem probability_identity (x : ℝ) (hx : |x| ≤ 1) (ss : List Phases) :
    ‖(polynomials ss).1.eval (x : ℂ)‖ ^ 2 +
      (1 - x ^ 2) * ‖(polynomials ss).2.eval (x : ℂ)‖ ^ 2 = 1 := by
  have hnorm : ‖sequence x ss clean‖ = 1 := by
    rw [(norm_map_iff_adjoint_comp_self _).mpr (sequence_unitary x hx ss).1, clean_norm]
  have hμ : badAmplitude (x : ℂ) ^ 2 = 1 - x ^ 2 := by
    exact_mod_cast badAmplitude_square x hx
  have h := PiLp.norm_sq_eq_of_L2 (fun _ : Bool => ℂ) (sequence x ss clean)
  rw [hnorm] at h
  simp only [Fintype.sum_bool, good_amplitude x hx ss, bad_amplitude x hx ss,
    norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (badAmplitude_nonneg _), mul_pow, hμ, one_pow] at h
  linarith

/-- Fixed rank-one projection onto the clean/good coordinate. -/
def cleanProjection : Qubit →L[ℂ] Qubit := matrix 1 0 0 0

/-- The projection required by the abstract phase program is certified explicitly. -/
theorem cleanProjection_orthogonal :
    PhaseSubspaceGates.IsOrthogonalProjection cleanProjection := by
  constructor
  · simp [cleanProjection, ContinuousLinearMap.star_eq_adjoint, matrix_adjoint]
  · ext v b
    cases b <;> simp [cleanProjection]

/-- The concrete diagonal gate is exactly the abstract fixed-subspace phase. -/
theorem phase_eq_subspace (a : ℂ) :
    phase a = PhaseSubspaceGates.phase cleanProjection a := by
  ext v b
  cases b <;> simp [phase, PhaseSubspaceGates.phase, cleanProjection]
  ring

/-- Agreement with the abstract two-query Grover-type step. -/
theorem step_eq_subspace (x : ℝ) (s : Phases) :
    step x s = PhaseSubspaceGates.step (rotation (x : ℂ)) cleanProjection cleanProjection s := by
  simp only [step, PhaseSubspaceGates.step, phase_eq_subspace,
    ContinuousLinearMap.star_eq_adjoint]

/-- Agreement with the counted abstract sequence, including its initial preparation. -/
theorem sequence_eq_subspace (x : ℝ) (ss : List Phases) :
    sequence x ss = PhaseSubspaceGates.sequence (rotation (x : ℂ))
      cleanProjection cleanProjection ss * rotation (x : ℂ) := by
  induction ss with
  | nil => simp [sequence, PhaseSubspaceGates.sequence]
  | cons s ss ih =>
      simp only [sequence, PhaseSubspaceGates.sequence, step_eq_subspace, ih, mul_assoc]

/-- A uniform oracle syntax tree: only the rotation depends on the real signal. -/
def program (ss : List Phases) : Program (fun x : ℝ => rotation (x : ℂ)) :=
  PhaseSubspaceGates.preparedProgram (fun x : ℝ => rotation (x : ℂ))
    cleanProjection cleanProjection cleanProjection_orthogonal cleanProjection_orthogonal ss

/-- The syntax tree denotes exactly the product used in polynomial evaluation. -/
@[simp] theorem program_eval (ss : List Phases) (x : ℝ) :
    (program ss).eval x = sequence x ss := by
  rw [program, PhaseSubspaceGates.preparedProgram_eval, sequence_eq_subspace]

/-- An odd polynomial sequence has exactly `2m+1` counted rotation or inverse calls. -/
@[simp] theorem program_count (ss : List Phases) :
    (program ss).count = 2 * ss.length + 1 := by
  exact PhaseSubspaceGates.preparedProgram_count _ _ _ _ _ ss

/-- The counted program has the claimed polynomial as its clean-to-good amplitude. -/
theorem program_good_amplitude (ss : List Phases) (x : ℝ) (hx : |x| ≤ 1) :
    (program ss).eval x clean false = (polynomials ss).1.eval (x : ℂ) := by
  rw [program_eval, good_amplitude x hx ss]

/-- Replacing each signal rotation by a `q`-query implementation multiplies the odd budget. -/
theorem compiled_program_count {O : ℝ → Qubit →L[ℂ] Qubit}
    (ss : List Phases) (p : Program O) :
    ((program ss).substitute p).count = (2 * ss.length + 1) * p.count := by
  simp

end
end SparseHamiltonian.AmplitudePolynomialSequence
