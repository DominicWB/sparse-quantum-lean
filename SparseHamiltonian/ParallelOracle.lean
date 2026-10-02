import SparseHamiltonian.ControlledLookup

/-!
# Uniform oracle programs on parallel clock registers

The parallel clock is an explicit extension of an oracle by an identity
public register and finite Hilbert direct-sum multiplicity. The algebra below
does not identify this interface with a primitive sparse matrix oracle.
The coupling network is independent of the oracle and is genuinely unitary.
-/

namespace SparseHamiltonian.ParallelOracle

noncomputable section
open ContinuousLinearMap GlobalColligation ChronologicalClockFactorization
open scoped InnerProduct

variable {P V : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

omit [CompleteSpace P] [CompleteSpace V] in
/-- The public-bypass extension preserves identity. -/
theorem parallelClock_one (T : ℕ) :
    parallelClock (P := P) (1 : V →L[ℂ] V) T = 1 := by
  ext x
  simp [parallelClock, WeightedClock.diagonal_one, blockMap_apply]
  rfl

omit [CompleteSpace P] [CompleteSpace V] in
/-- The extension preserves composition, with no factor depending on the
number of parallel slots. -/
theorem parallelClock_comp (A B : V →L[ℂ] V) (T : ℕ) :
    parallelClock (P := P) (A ∘L B) T =
      parallelClock (P := P) A T ∘L parallelClock (P := P) B T := by
  ext x
  simp only [comp_apply, parallelClock_apply, WithLp.fst, WithLp.snd]
  rfl

/-- Adjoint oracle calls extend to adjoint parallel oracle calls. -/
theorem parallelClock_adjoint (A : V →L[ℂ] V) (T : ℕ) :
    (parallelClock (P := P) A T)† = parallelClock (P := P) (A†) T := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℂ
  intro y
  simp only [adjoint_inner_left, parallelClock_apply, WithLp.prod_inner_apply,
    WithLp.fst, WithLp.snd]
  rw [← WeightedClock.diagonal_adjoint, adjoint_inner_left]

/-- A two-sided unitary oracle remains unitary under the parallel extension. -/
theorem parallelClock_unitary (A : V →L[ℂ] V) (T : ℕ)
    (hAl : A† ∘L A = 1) (hAr : A ∘L A† = 1) :
    (parallelClock (P := P) A T)† ∘L parallelClock (P := P) A T = 1 ∧
      parallelClock (P := P) A T ∘L (parallelClock (P := P) A T)† = 1 := by
  rw [parallelClock_adjoint, ← parallelClock_comp, ← parallelClock_comp,
    hAl, hAr, parallelClock_one]
  exact ⟨rfl, rfl⟩

/-- The chronological coupling is unitary by the actual local rotation law.
It depends on the fixed boundary and rotation parameters, not the oracle. -/
theorem couplingNetwork_unitary [FiniteDimensional ℂ P] [FiniteDimensional ℂ V]
    (J : P →L[ℂ] V) (c κ σ : ℝ) (T : ℕ)
    (hJ : J† ∘L J = 1) (hκ : κ = 1 - c) (hσ : σ ^ 2 = 1 - c ^ 2) :
    (couplingNetwork J c κ σ T)† ∘L couplingNetwork J c κ σ T = 1 ∧
      couplingNetwork J c κ σ T ∘L (couplingNetwork J c κ σ T)† = 1 := by
  have hStep := LocalRotation.local_step_energy (1 : V →L[ℂ] V) J c κ σ hκ hσ
    (by simp only [one_def, adjoint_id, id_comp]) hJ
  simp only [GlobalResolvent.localPrivateBlock, one_def, comp_id] at hStep
  exact chronological_blockMap_unitary _ _ _ _ hStep T

open OracleCircuit

omit [CompleteSpace P] in
/-- Finite multiplicity preserves both unitary identities. -/
theorem diagonal_unitary (U : V →L[ℂ] V) (T : ℕ) (hU : IsUnitary U) :
    IsUnitary (WeightedClock.diagonal (fun _ : Fin T => U)) := by
  constructor
  · exact WeightedClock.diagonal_isometry _ (fun _ => hU.1)
  · change WeightedClock.diagonal (fun _ : Fin T => U) ∘L
      (WeightedClock.diagonal (fun _ : Fin T => U))† = 1
    rw [WeightedClock.diagonal_adjoint, WeightedClock.diagonal_comp]
    have hRight : U ∘L U† = 1 := hU.2
    simp only [hRight, WeightedClock.diagonal_one]

variable {X : Type*} {O : X → V →L[ℂ] V}

omit [CompleteSpace P] in
/-- Syntactically lift each query to the direct-sum oracle interface. Fixed
gates remain independent of the unknown input. -/
def diagonalProgram (T : ℕ) : Program O →
    Program (fun x => WeightedClock.diagonal (fun _ : Fin T => O x))
  | .fixed U hU => .fixed _ (diagonal_unitary U T hU)
  | .query => .query
  | .queryAdjoint => .queryAdjoint
  | .seq p q => .seq (diagonalProgram T p) (diagonalProgram T q)

omit [CompleteSpace P] in
/-- Parallel multiplicity does not change the number of calls to the extended
oracle interface. -/
theorem diagonalProgram_count (T : ℕ) (p : Program O) :
    (diagonalProgram T p).count = p.count := by
  induction p with
  | fixed U hU => rfl
  | query => rfl
  | queryAdjoint => rfl
  | seq p q hp hq => simp only [diagonalProgram, Program.count_seq, hp, hq]

omit [CompleteSpace P] in
/-- The lifted program acts independently and identically on each slot. -/
theorem diagonalProgram_eval (T : ℕ) (p : Program O) (x : X) :
    (diagonalProgram T p).eval x =
      WeightedClock.diagonal (fun _ : Fin T => p.eval x) := by
  induction p with
  | fixed U hU => rfl
  | query => rfl
  | queryAdjoint => exact WeightedClock.diagonal_adjoint _
  | seq p q hp hq =>
      simp only [diagonalProgram, Program.eval_seq, hp, hq]
      exact WeightedClock.diagonal_comp _ _

/-- Lift an entire program through the public-bypass oracle extension. -/
def parallelProgram (T : ℕ) : Program O →
    Program (fun x => parallelClock (P := P) (O x) T)
  | .fixed U hU => .fixed _ (parallelClock_unitary U T hU.1 hU.2)
  | .query => .query
  | .queryAdjoint => .queryAdjoint
  | .seq p q => .seq (parallelProgram T p) (parallelProgram T q)

/-- The bypass construction preserves the exact syntactic query count. -/
theorem parallelProgram_count (T : ℕ) (p : Program O) :
    (parallelProgram (P := P) T p).count = p.count := by
  induction p with
  | fixed U hU => rfl
  | query => rfl
  | queryAdjoint => rfl
  | seq p q hp hq => simp only [parallelProgram, Program.count_seq, hp, hq]

/-- The bypass lift implements the parallel extension of the original
program's evaluation. -/
theorem parallelProgram_eval (T : ℕ) (p : Program O) (x : X) :
    (parallelProgram (P := P) T p).eval x =
      parallelClock (P := P) (p.eval x) T := by
  induction p with
  | fixed U hU => rfl
  | query => rfl
  | queryAdjoint => exact parallelClock_adjoint _ _
  | seq p q hp hq =>
      simp only [parallelProgram, Program.eval_seq, hp, hq]
      exact (parallelClock_comp _ _ _).symm

omit [CompleteSpace P] in
/-- An implementation certificate lifts to the finite direct-sum interface
with the same query bound. -/
theorem diagonal_implements {F : X → V →L[ℂ] V} {q : ℕ}
    (h : Implements O F q) (T : ℕ) :
    Implements (fun x => WeightedClock.diagonal (fun _ : Fin T => O x))
      (fun x => WeightedClock.diagonal (fun _ : Fin T => F x)) q := by
  obtain ⟨p, hp, hq⟩ := h
  refine ⟨diagonalProgram T p, ?_, ?_⟩
  · intro x
    rw [diagonalProgram_eval, hp]
  · simpa only [diagonalProgram_count] using hq

/-- An implementation certificate lifts through the public bypass with the
same query bound, relative to the explicitly extended oracle. -/
theorem parallel_implements {F : X → V →L[ℂ] V} {q : ℕ}
    (h : Implements O F q) (T : ℕ) :
    Implements (fun x => parallelClock (P := P) (O x) T)
      (fun x => parallelClock (P := P) (F x) T) q := by
  obtain ⟨p, hp, hq⟩ := h
  refine ⟨parallelProgram T p, ?_, ?_⟩
  · intro x
    rw [parallelProgram_eval, hp]
  · simpa only [parallelProgram_count] using hq

/-- The full chronology uses one query to its explicitly extended clock
oracle, followed by a fixed unitary coupling network. -/
theorem clockColligation_implements [FiniteDimensional ℂ P] [FiniteDimensional ℂ V]
    (O : X → V →L[ℂ] V) (J : P →L[ℂ] V) (c κ σ : ℝ) (T : ℕ)
    (hJ : J† ∘L J = 1) (hκ : κ = 1 - c) (hσ : σ ^ 2 = 1 - c ^ 2) :
    Implements (fun x => parallelClock (P := P) (O x) T)
      (fun x => clockColligation (O x) J c κ σ T) 1 := by
  have hFixed := Implements.fixed (O := fun x => parallelClock (P := P) (O x) T)
    (couplingNetwork J c κ σ T) (couplingNetwork_unitary J c κ σ T hJ hκ hσ)
  exact (hFixed.mul Implements.query).congr
    (fun x => (clockColligation_factor (O x) J c κ σ T).symm)

/-- A uniform implementation of the clock compiles into the whole chronology
at the same cost in the extended oracle interface. In particular the number
of chronological steps does not multiply this query bound. -/
theorem clockColligation_implements_of_clock
    [FiniteDimensional ℂ P] [FiniteDimensional ℂ V]
    {D : X → V →L[ℂ] V} {q : ℕ} (hD : Implements O D q)
    (J : P →L[ℂ] V) (c κ σ : ℝ) (T : ℕ)
    (hJ : J† ∘L J = 1) (hκ : κ = 1 - c) (hσ : σ ^ 2 = 1 - c ^ 2) :
    Implements (fun x => parallelClock (P := P) (O x) T)
      (fun x => clockColligation (D x) J c κ σ T) q := by
  have hFixed := Implements.fixed (O := fun x => parallelClock (P := P) (O x) T)
    (couplingNetwork J c κ σ T) (couplingNetwork_unitary J c κ σ T hJ hκ hσ)
  have hProduct := (hFixed.mul (parallel_implements hD T)).congr
    (fun x => (clockColligation_factor (D x) J c κ σ T).symm)
  simpa only [Nat.zero_add] using hProduct

end
end SparseHamiltonian.ParallelOracle
