import SparseHamiltonian.EncodedAmplification

/-!
# Algebra of active shared-register clock operations

The public bypass, finished-branch bypass, and finite clock multiplicity all
preserve identity, composition, adjoints, and two-sided unitarity. Consequently
fixed unitary factors of a clock remain legal fixed gates after all these
controls are added. These algebraic facts do not grant a new query primitive.
-/

namespace SparseHamiltonian.ActiveClockAlgebra

noncomputable section
open ContinuousLinearMap OracleCircuit ReuseLayerFactorization ReuseSchedule
open scoped InnerProduct

variable {P V : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

omit [CompleteSpace P] [CompleteSpace V] in
/-- The shared-register extension preserves identity. -/
theorem sharedAction_one (n : ℕ) : sharedAction (P := P) (1 : V →L[ℂ] V) n = 1 := by
  ext x
  simp only [sharedAction_apply, one_def, id_apply]
  rfl

omit [CompleteSpace P] [CompleteSpace V] in
/-- Acting only on the common private register preserves composition. -/
theorem sharedAction_comp (A B : V →L[ℂ] V) (n : ℕ) :
    sharedAction (P := P) (A ∘L B) n =
      sharedAction (P := P) A n ∘L sharedAction (P := P) B n := by
  ext x
  simp only [comp_apply, sharedAction_apply, WithLp.fst, WithLp.snd]

/-- The public bypass commutes with Hilbert adjoints. -/
theorem sharedAction_adjoint (A : V →L[ℂ] V) (n : ℕ) :
    (sharedAction (P := P) A n)† = sharedAction (P := P) (A†) n := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℂ
  intro y
  simp only [adjoint_inner_left, sharedAction_apply, WithLp.prod_inner_apply,
    WithLp.fst, WithLp.snd, adjoint_inner_left]

/-- Both unitary identities survive the public bypass. -/
theorem sharedAction_unitary (A : V →L[ℂ] V) (hA : IsUnitary A) (n : ℕ) :
    IsUnitary (sharedAction (P := P) A n) := by
  have hAl : A† ∘L A = 1 := hA.1
  have hAr : A ∘L A† = 1 := hA.2
  constructor
  · change (sharedAction (P := P) A n)† ∘L sharedAction (P := P) A n = 1
    rw [sharedAction_adjoint, ← sharedAction_comp, hAl, sharedAction_one]
  · change sharedAction (P := P) A n ∘L (sharedAction (P := P) A n)† = 1
    rw [sharedAction_adjoint, ← sharedAction_comp, hAr, sharedAction_one]

omit [CompleteSpace P] [CompleteSpace V] in
/-- Applying identity is independent of branch activity. -/
theorem activeBranch_one (n r : ℕ) :
    activeBranch (P := P) (1 : V →L[ℂ] V) n r = 1 := by
  unfold activeBranch
  split
  · exact sharedAction_one n
  · rfl

omit [CompleteSpace P] [CompleteSpace V] in
/-- A common branch-activity condition preserves composition. -/
theorem activeBranch_comp (A B : V →L[ℂ] V) (n r : ℕ) :
    activeBranch (P := P) (A ∘L B) n r =
      activeBranch (P := P) A n r ∘L activeBranch (P := P) B n r := by
  unfold activeBranch
  split
  · exact sharedAction_comp A B n
  · rfl

/-- Finished-branch bypass also commutes with adjoints. -/
theorem activeBranch_adjoint (A : V →L[ℂ] V) (n r : ℕ) :
    (activeBranch (P := P) A n r)† = activeBranch (P := P) (A†) n r := by
  unfold activeBranch
  split
  · exact sharedAction_adjoint A n
  · exact adjoint_one

/-- An active or bypassed unitary branch remains unitary. -/
theorem activeBranch_unitary (A : V →L[ℂ] V) (hA : IsUnitary A) (n r : ℕ) :
    IsUnitary (activeBranch (P := P) A n r) := by
  unfold activeBranch
  split
  · exact sharedAction_unitary A hA n
  · exact isUnitary_one

omit [CompleteSpace P] [CompleteSpace V] in
/-- The simultaneous active-branch extension preserves identity. -/
theorem activeQuery_one (d r : ℕ) :
    activeQuery (P := P) (1 : V →L[ℂ] V) d r = 1 := by
  unfold activeQuery
  simp only [activeBranch_one, WeightedClock.diagonal_one]

omit [CompleteSpace P] [CompleteSpace V] in
/-- All active branches preserve operator composition simultaneously. -/
theorem activeQuery_comp (A B : V →L[ℂ] V) (d r : ℕ) :
    activeQuery (P := P) (A ∘L B) d r =
      activeQuery (P := P) A d r ∘L activeQuery (P := P) B d r := by
  unfold activeQuery
  rw [WeightedClock.diagonal_comp]
  simp only [activeBranch_comp]

/-- The active direct-sum action preserves adjoints. -/
theorem activeQuery_adjoint (A : V →L[ℂ] V) (d r : ℕ) :
    (activeQuery (P := P) A d r)† = activeQuery (P := P) (A†) d r := by
  unfold activeQuery
  rw [WeightedClock.diagonal_adjoint]
  simp only [activeBranch_adjoint]

/-- The active query is two-sided unitary on its entire workspace. -/
theorem activeQuery_unitary (A : V →L[ℂ] V) (hA : IsUnitary A) (d r : ℕ) :
    IsUnitary (activeQuery (P := P) A d r) := by
  have hAl : A† ∘L A = 1 := hA.1
  have hAr : A ∘L A† = 1 := hA.2
  constructor
  · change (activeQuery (P := P) A d r)† ∘L activeQuery (P := P) A d r = 1
    rw [activeQuery_adjoint, ← activeQuery_comp, hAl, activeQuery_one]
  · change activeQuery (P := P) A d r ∘L (activeQuery (P := P) A d r)† = 1
    rw [activeQuery_adjoint, ← activeQuery_comp, hAr, activeQuery_one]

omit [CompleteSpace P] [CompleteSpace V] in
/-- Identity on each time slot induces identity on the full controlled workspace. -/
theorem activeClock_one (T d r : ℕ) :
    activeClock (P := P) (1 : V →L[ℂ] V) T d r = 1 := by
  unfold activeClock
  rw [WeightedClock.diagonal_one, activeQuery_one]

omit [CompleteSpace P] [CompleteSpace V] in
/-- Active clock operations preserve composition despite all bypass controls. -/
theorem activeClock_comp (A B : V →L[ℂ] V) (T d r : ℕ) :
    activeClock (P := P) (A ∘L B) T d r =
      activeClock (P := P) A T d r ∘L activeClock (P := P) B T d r := by
  unfold activeClock
  rw [← WeightedClock.diagonal_comp, activeQuery_comp]

omit [CompleteSpace P] [CompleteSpace V] in
/-- Multiplicative notation for the active-clock factorization. -/
theorem activeClock_mul (A B : V →L[ℂ] V) (T d r : ℕ) :
    activeClock (P := P) (A * B) T d r =
      activeClock (P := P) A T d r * activeClock (P := P) B T d r :=
  activeClock_comp A B T d r

/-- Inverse oracle calls remain adjoints after clock extension and controls. -/
theorem activeClock_adjoint (A : V →L[ℂ] V) (T d r : ℕ) :
    (activeClock (P := P) A T d r)† = activeClock (P := P) (A†) T d r := by
  unfold activeClock
  rw [activeQuery_adjoint, WeightedClock.diagonal_adjoint]

/-- A general two-sided unitary clock gives a two-sided unitary active action. -/
theorem activeClock_unitary (A : V →L[ℂ] V) (hA : IsUnitary A) (T d r : ℕ) :
    IsUnitary (activeClock (P := P) A T d r) := by
  have hAl : A† ∘L A = 1 := hA.1
  have hAr : A ∘L A† = 1 := hA.2
  constructor
  · change (activeClock (P := P) A T d r)† ∘L activeClock (P := P) A T d r = 1
    rw [activeClock_adjoint, ← activeClock_comp, hAl, activeClock_one]
  · change activeClock (P := P) A T d r ∘L (activeClock (P := P) A T d r)† = 1
    rw [activeClock_adjoint, ← activeClock_comp, hAr, activeClock_one]

end
end SparseHamiltonian.ActiveClockAlgebra
