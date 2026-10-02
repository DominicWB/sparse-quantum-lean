import SparseHamiltonian.NativeBandEncoding

/-!
# Fixed subspace phase gates and counted phase sequences

A phase gate acts by a prescribed unit complex number on the range of an
orthogonal projection and by the identity on its kernel. The projections in
the circuits below are fixed operators: dependence on the unknown input is
introduced only through explicitly counted calls to the preparation oracle.
-/

namespace SparseHamiltonian.PhaseSubspaceGates

noncomputable section

open OracleCircuit

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {X : Type*}

/-- Both algebraic conditions for an orthogonal projection. -/
def IsOrthogonalProjection (P : K →L[ℂ] K) : Prop :=
  star P = P ∧ P * P = P

/-- Apply `ζ` to the projected subspace and leave its orthogonal complement alone. -/
def phase (P : K →L[ℂ] K) (ζ : ℂ) : K →L[ℂ] K :=
  1 + (ζ - 1) • P

omit [CompleteSpace K] in
@[simp] theorem phase_one (P : K →L[ℂ] K) : phase P 1 = 1 := by
  simp [phase]

omit [CompleteSpace K] in
@[simp] theorem phase_apply (P : K →L[ℂ] K) (ζ : ℂ) (v : K) :
    phase P ζ v = v + (ζ - 1) • P v := by
  simp [phase]

omit [CompleteSpace K] in
/-- Multiplication of phase gates is multiplication of their phases. -/
theorem phase_mul (P : K →L[ℂ] K) (hP : P * P = P) (ζ η : ℂ) :
    phase P ζ * phase P η = phase P (ζ * η) := by
  simp only [phase, mul_add, add_mul, one_mul, mul_one,
    smul_mul_assoc, mul_smul_comm, hP]
  module

/-- The adjoint conjugates the phase on the same fixed subspace. -/
theorem phase_adjoint (P : K →L[ℂ] K) (hP : star P = P) (ζ : ℂ) :
    star (phase P ζ) = phase P (star ζ) := by
  simp only [phase, star_add, star_one, star_smul, star_sub, hP]

/-- A unit-modulus scalar gives a two-sided unitary gate. -/
theorem phase_unitary (P : K →L[ℂ] K) (hP : IsOrthogonalProjection P)
    (ζ : ℂ) (hζ : ‖ζ‖ = 1) : IsUnitary (phase P ζ) := by
  have hleft : star ζ * ζ = 1 := by
    simpa [hζ] using RCLike.conj_mul ζ
  have hright : ζ * star ζ = 1 := by
    simpa [hζ] using RCLike.mul_conj ζ
  constructor
  · rw [phase_adjoint P hP.1, phase_mul P hP.2, hleft, phase_one]
  · rw [phase_adjoint P hP.1, phase_mul P hP.2, hright, phase_one]

omit [CompleteSpace K] in
/-- Every vector fixed by the projection acquires the prescribed phase. -/
theorem phase_apply_of_fixed (P : K →L[ℂ] K) (ζ : ℂ) (v : K) (hv : P v = v) :
    phase P ζ v = ζ • v := by
  rw [phase_apply, hv, sub_smul, one_smul]
  abel

omit [CompleteSpace K] in
/-- Every vector in the kernel is unchanged. -/
theorem phase_apply_of_kernel (P : K →L[ℂ] K) (ζ : ℂ) (v : K) (hv : P v = 0) :
    phase P ζ v = v := by
  simp only [phase_apply, hv, smul_zero, add_zero]

omit [CompleteSpace K] in
/-- In particular the gate multiplies every vector in the range by its phase. -/
theorem phase_apply_range (P : K →L[ℂ] K) (hP : P * P = P) (ζ : ℂ) (v : K) :
    phase P ζ (P v) = ζ • P v := by
  apply phase_apply_of_fixed
  exact congrArg (fun A : K →L[ℂ] K => A v) hP

/-- Unitary transport preserves the two projection identities. -/
theorem IsOrthogonalProjection.conjugate {P U : K →L[ℂ] K}
    (hP : IsOrthogonalProjection P) (hU : IsUnitary U) :
    IsOrthogonalProjection (U * P * star U) := by
  constructor
  · simp only [star_mul, star_star, hP.1, mul_assoc]
  · calc
      (U * P * star U) * (U * P * star U) =
          U * P * (star U * U) * P * star U := by simp only [mul_assoc]
      _ = U * (P * P) * star U := by rw [hU.1]; simp only [mul_one, mul_assoc]
      _ = U * P * star U := by rw [hP.2]

/-- A phase about a transported subspace requires conjugation by its preparation.
This identity does not turn the transported projector into a free circuit gate. -/
theorem phase_conjugate (P U : K →L[ℂ] K) (hU : IsUnitary U) (ζ : ℂ) :
    phase (U * P * star U) ζ = U * phase P ζ * star U := by
  simp only [phase, mul_add, add_mul, mul_one, mul_smul_comm,
    smul_mul_assoc, hU.2]

/-- A phase is a fixed classical choice, independent of the oracle input. -/
abbrev Phase := {ζ : ℂ // ‖ζ‖ = 1}

/-- The pair consists of the input-subspace phase and the good-subspace phase. -/
abbrev PhasePair := Phase × Phase

/-- One amplitude-manipulation step in the output workspace. -/
def step (U P Q : K →L[ℂ] K) (ζη : PhasePair) : K →L[ℂ] K :=
  U * phase P ζη.1.val * star U * phase Q ζη.2.val

/-- A genuine syntax tree with fixed phase gates and two oracle letters. -/
def stepProgram (O : X → K →L[ℂ] K) (P Q : K →L[ℂ] K)
    (hP : IsOrthogonalProjection P) (hQ : IsOrthogonalProjection Q)
    (ζη : PhasePair) : Program O :=
  .seq (.seq (.seq .query (.fixed (phase P ζη.1.val)
    (phase_unitary P hP ζη.1.val ζη.1.property))) .queryAdjoint)
    (.fixed (phase Q ζη.2.val) (phase_unitary Q hQ ζη.2.val ζη.2.property))

@[simp] theorem stepProgram_eval (O : X → K →L[ℂ] K) (P Q : K →L[ℂ] K)
    (hP : IsOrthogonalProjection P) (hQ : IsOrthogonalProjection Q)
    (ζη : PhasePair) (x : X) :
    (stepProgram O P Q hP hQ ζη).eval x = step (O x) P Q ζη := rfl

@[simp] theorem stepProgram_count (O : X → K →L[ℂ] K) (P Q : K →L[ℂ] K)
    (hP : IsOrthogonalProjection P) (hQ : IsOrthogonalProjection Q)
    (ζη : PhasePair) : (stepProgram O P Q hP hQ ζη).count = 2 := rfl

/-- The head of the list acts last, so the operator list is in multiplication order. -/
def sequence (U P Q : K →L[ℂ] K) : List PhasePair → K →L[ℂ] K
  | [] => 1
  | ζη :: phases => step U P Q ζη * sequence U P Q phases

/-- Finite sequences use only syntactic composition of the two-query steps. -/
def sequenceProgram (O : X → K →L[ℂ] K) (P Q : K →L[ℂ] K)
    (hP : IsOrthogonalProjection P) (hQ : IsOrthogonalProjection Q) :
    List PhasePair → Program O
  | [] => Program.identity
  | ζη :: phases => .seq (stepProgram O P Q hP hQ ζη)
      (sequenceProgram O P Q hP hQ phases)

@[simp] theorem sequenceProgram_eval (O : X → K →L[ℂ] K) (P Q : K →L[ℂ] K)
    (hP : IsOrthogonalProjection P) (hQ : IsOrthogonalProjection Q)
    (phases : List PhasePair) (x : X) :
    (sequenceProgram O P Q hP hQ phases).eval x = sequence (O x) P Q phases := by
  induction phases with
  | nil => rfl
  | cons ζη phases ih => simp only [sequenceProgram, Program.eval_seq,
      stepProgram_eval, ih, sequence]

@[simp] theorem sequenceProgram_count (O : X → K →L[ℂ] K) (P Q : K →L[ℂ] K)
    (hP : IsOrthogonalProjection P) (hQ : IsOrthogonalProjection Q)
    (phases : List PhasePair) :
    (sequenceProgram O P Q hP hQ phases).count = 2 * phases.length := by
  induction phases with
  | nil => rfl
  | cons ζη phases ih => simp [sequenceProgram, ih, Nat.mul_add, Nat.add_comm]

/-- The complete phase sequence is unitary in the full workspace. -/
theorem sequence_unitary (U P Q : K →L[ℂ] K) (hU : IsUnitary U)
    (hP : IsOrthogonalProjection P) (hQ : IsOrthogonalProjection Q)
    (phases : List PhasePair) : IsUnitary (sequence U P Q phases) := by
  have h := (sequenceProgram (fun _ : Unit => U) P Q hP hQ phases).eval_unitary
    (fun _ => hU) ()
  simpa only [sequenceProgram_eval] using h

/-- Initial preparation followed by a sequence preserves the full output norm. -/
theorem prepared_unitary (U P Q : K →L[ℂ] K) (hU : IsUnitary U)
    (hP : IsOrthogonalProjection P) (hQ : IsOrthogonalProjection Q)
    (phases : List PhasePair) : IsUnitary (sequence U P Q phases * U) :=
  (sequence_unitary U P Q hU hP hQ phases).mul hU

/-- Initial preparation followed by the phase sequence is the odd-query circuit. -/
def preparedProgram (O : X → K →L[ℂ] K) (P Q : K →L[ℂ] K)
    (hP : IsOrthogonalProjection P) (hQ : IsOrthogonalProjection Q)
    (phases : List PhasePair) : Program O :=
  .seq (sequenceProgram O P Q hP hQ phases) .query

@[simp] theorem preparedProgram_eval (O : X → K →L[ℂ] K) (P Q : K →L[ℂ] K)
    (hP : IsOrthogonalProjection P) (hQ : IsOrthogonalProjection Q)
    (phases : List PhasePair) (x : X) :
    (preparedProgram O P Q hP hQ phases).eval x =
      sequence (O x) P Q phases * O x := by
  simp [preparedProgram]

@[simp] theorem preparedProgram_count (O : X → K →L[ℂ] K) (P Q : K →L[ℂ] K)
    (hP : IsOrthogonalProjection P) (hQ : IsOrthogonalProjection Q)
    (phases : List PhasePair) :
    (preparedProgram O P Q hP hQ phases).count = 2 * phases.length + 1 := by
  simp [preparedProgram]

/-- Compiling a sequence into a preparation implementation exposes its full cost. -/
theorem compiled_sequence_count {O F : X → K →L[ℂ] K}
    (P Q : K →L[ℂ] K) (hP : IsOrthogonalProjection P) (hQ : IsOrthogonalProjection Q)
    (phases : List PhasePair) (p : Program O) {q : ℕ} (hp : p.count = q) :
    ((sequenceProgram F P Q hP hQ phases).substitute p).count =
      2 * phases.length * q := by
  simp [hp]

/-- Initial preparation contributes one further preparation-oracle implementation. -/
theorem compiled_prepared_count {O F : X → K →L[ℂ] K}
    (P Q : K →L[ℂ] K) (hP : IsOrthogonalProjection P) (hQ : IsOrthogonalProjection Q)
    (phases : List PhasePair) (p : Program O) {q : ℕ} (hp : p.count = q) :
    ((preparedProgram F P Q hP hQ phases).substitute p).count =
      (2 * phases.length + 1) * q := by
  simp [hp]

/-- Compiling the even-query sequence preserves its operator semantics. -/
theorem compiled_sequence_eval {O F : X → K →L[ℂ] K}
    (P Q : K →L[ℂ] K) (hP : IsOrthogonalProjection P) (hQ : IsOrthogonalProjection Q)
    (phases : List PhasePair) (p : Program O) (hp : ∀ x, p.eval x = F x) (x : X) :
    ((sequenceProgram F P Q hP hQ phases).substitute p).eval x =
      sequence (F x) P Q phases := by
  rw [Program.eval_substitute _ _ hp, sequenceProgram_eval]

/-- Substitution preserves the actual operator, with no input-dependent free gate. -/
theorem compiled_prepared_eval {O F : X → K →L[ℂ] K}
    (P Q : K →L[ℂ] K) (hP : IsOrthogonalProjection P) (hQ : IsOrthogonalProjection Q)
    (phases : List PhasePair) (p : Program O) (hp : ∀ x, p.eval x = F x) (x : X) :
    ((preparedProgram F P Q hP hQ phases).substitute p).eval x =
      sequence (F x) P Q phases * F x := by
  rw [Program.eval_substitute _ _ hp, preparedProgram_eval]

end

end SparseHamiltonian.PhaseSubspaceGates
