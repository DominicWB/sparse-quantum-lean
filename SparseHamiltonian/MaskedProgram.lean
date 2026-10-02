import SparseHamiltonian.LookupClockStep

/-!
# Controlled uniform programs with explicitly implemented masked queries

A fixed Boolean predicate selects which direct-sum branches execute a program.
The compiler preserves exact syntax counts relative to the masked oracle.
A separate implementation of that masked query is then substituted, so no
controlled-oracle primitive is granted by the query model.
-/

namespace SparseHamiltonian.MaskedProgram

noncomputable section
open ContinuousLinearMap OracleCircuit
open scoped InnerProduct

variable {ι K : Type*} [Fintype ι]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Execute an operator in active branches and identity in inactive branches. -/
def masked (active : ι → Bool) (U : K →L[ℂ] K) :
    PiLp 2 (fun _ : ι => K) →L[ℂ] PiLp 2 (fun _ : ι => K) :=
  WeightedClock.diagonal (fun i => if active i then U else 1)

omit [Fintype ι] [CompleteSpace K] in
@[simp] theorem masked_apply (active : ι → Bool) (U : K →L[ℂ] K)
    (v : PiLp 2 (fun _ : ι => K)) (i : ι) :
    masked active U v i = if active i then U (v i) else v i := by
  cases h : active i <;> simp [masked, h]

omit [Fintype ι] [CompleteSpace K] in
theorem masked_one (active : ι → Bool) : masked active (1 : K →L[ℂ] K) = 1 := by
  simp [masked, WeightedClock.diagonal_one]

omit [Fintype ι] [CompleteSpace K] in
/-- A fixed mask preserves chronological composition. -/
theorem masked_mul (active : ι → Bool) (U V : K →L[ℂ] K) :
    masked active (U * V) = masked active U * masked active V := by
  ext v i
  cases h : active i <;> simp [masked_apply, h]

/-- Masking respects adjoints, including on bypass branches. -/
theorem masked_adjoint (active : ι → Bool) (U : K →L[ℂ] K) :
    (masked active U)† = masked active (U†) := by
  simp only [masked, WeightedClock.diagonal_adjoint]
  congr 1
  funext i
  cases active i <;> simp

/-- Controlled fixed gates remain fixed unitary gates. -/
theorem masked_unitary (active : ι → Bool) (U : K →L[ℂ] K)
    (hU : IsUnitary U) : IsUnitary (masked active U) := by
  have hLeft : U† * U = 1 := hU.1
  have hRight : U * U† = 1 := hU.2
  constructor
  · change (masked active U)† * masked active U = 1
    rw [masked_adjoint, ← masked_mul, hLeft, masked_one]
  · change masked active U * (masked active U)† = 1
    rw [masked_adjoint, ← masked_mul, hRight, masked_one]

variable {X : Type*} {O : X → K →L[ℂ] K}

/-- Compile with fixed branch controls, relative to the explicitly masked oracle. -/
def compile (active : ι → Bool) :
    Program O → Program (fun x => masked active (O x))
  | .fixed U hU => .fixed _ (masked_unitary active U hU)
  | .query => .query
  | .queryAdjoint => .queryAdjoint
  | .seq p q => .seq (compile active p) (compile active q)

/-- Mask compilation does not insert oracle calls. -/
theorem compile_count (active : ι → Bool) (p : Program O) :
    (compile active p).count = p.count := by
  induction p with
  | fixed U hU => rfl
  | query => rfl
  | queryAdjoint => rfl
  | seq p q hp hq => simp only [compile, Program.count_seq, hp, hq]

/-- Inactive branches execute identity even when the program contains many
fixed gates; the whole controlled program is evaluated, not only its queries. -/
theorem compile_eval (active : ι → Bool) (p : Program O) (x : X) :
    (compile active p).eval x = masked active (p.eval x) := by
  induction p with
  | fixed U hU => rfl
  | query => rfl
  | queryAdjoint => exact masked_adjoint active _
  | seq p q hp hq =>
      simp only [compile, Program.eval_seq, hp, hq]
      exact (masked_mul active _ _).symm

/-- A uniform implementation lifts through a fixed control mask. -/
theorem implements_masked {F : X → K →L[ℂ] K} {q : ℕ}
    (h : Implements O F q) (active : ι → Bool) :
    Implements (fun x => masked active (O x)) (fun x => masked active (F x)) q := by
  obtain ⟨p, hp, hq⟩ := h
  refine ⟨compile active p, fun x => ?_, ?_⟩
  · rw [compile_eval, hp]
  · simpa only [compile_count] using hq

/-- Substituting an actual implementation of the masked query incurs its
proved cost. All masks and all free gates stay independent of the unknown input. -/
theorem implements_of_masked_query {F : X → K →L[ℂ] K} {q c : ℕ}
    (h : Implements O F q) (active : ι → Bool)
    (Q : X → PiLp 2 (fun _ : ι => K) →L[ℂ] PiLp 2 (fun _ : ι => K))
    (hQuery : Implements Q (fun x => masked active (O x)) c) :
    Implements Q (fun x => masked active (F x)) (q * c) :=
  hQuery.trans (implements_masked h active)

end
end SparseHamiltonian.MaskedProgram
