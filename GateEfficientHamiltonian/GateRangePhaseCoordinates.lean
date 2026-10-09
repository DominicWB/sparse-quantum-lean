import GateEfficientHamiltonian.GateControlledCompare
/-!
The numerical predicate proved for the bit circuit is the same predicate
used by the Hilbert-space amplitude-amplification reflection.  This is a
coordinate identification, not yet the complete workspace transport of the
normalised phase-kickback circuit.
-/

namespace SparseHamiltonian.GateUniformRange

noncomputable section
open ContinuousLinearMap ComplexAmplitudeRotation

/-- The successful-subspace reflection flips precisely the valid words
whose attenuation flag is false. -/
theorem goodPhase_apply (n N : ℕ) (v : Space N) (j : Fin N) (flag : Bool) :
    PhaseSubspaceGates.phase (goodProjection n N) (-1) v j flag =
      (if flag = false ∧ j.val < n then (-1 : ℂ) else 1) * v j flag := by
  cases flag <;> by_cases hj : j.val < n <;>
    simp [PhaseSubspaceGates.phase_apply, goodProjection,
      WeightedClock.diagonal_apply, cleanProjection, hj]; ring

/-- The established binary encoding carries the physical comparator
predicate to the exact phase used in `rangeProgram`. -/
theorem goodPhase_word (n r : ℕ) (v : Space (2 ^ r))
    (x : GatePointerEncoding.Word r) (flag : Bool) :
    PhaseSubspaceGates.phase (goodProjection n (2 ^ r)) (-1) v
        (GatePointerEncoding.wordEquivFin r x) flag =
      (if flag = false ∧ GatePointerEncoding.wordValue x < n
        then (-1 : ℂ) else 1) *
        v (GatePointerEncoding.wordEquivFin r x) flag := by
  rw [goodPhase_apply]
  rfl

end
end SparseHamiltonian.GateUniformRange

namespace SparseHamiltonian.GateWalshHilbert

noncomputable section
open ContinuousLinearMap ComplexAmplitudeRotation
open scoped InnerProduct BigOperators

theorem inner_cleanInput (r : ℕ) (v : GateUniformRange.Space (2 ^ r)) :
    inner ℂ (cleanInput r) v =
      v (GatePointerEncoding.wordEquivFin r (GateWalshWords.zeroWord r)) false := by
  have he : ∀ j : Fin (2 ^ r), inner ℂ (cleanInput r j) (v j) =
      if j = GatePointerEncoding.wordEquivFin r (GateWalshWords.zeroWord r)
        then v j false else 0 := by
    intro j
    change inner ℂ
        (if j = GatePointerEncoding.wordEquivFin r (GateWalshWords.zeroWord r)
          then clean else 0) (v j) = _
    by_cases hj : j = GatePointerEncoding.wordEquivFin r (GateWalshWords.zeroWord r)
    · simp only [if_pos hj]
      simp [PiLp.inner_apply, clean, RCLike.inner_apply]
    · simp only [if_neg hj, inner_zero_left]
  rw [PiLp.inner_apply]
  simp only [he]
  refine (Finset.sum_eq_single
    (GatePointerEncoding.wordEquivFin r (GateWalshWords.zeroWord r)) ?_ ?_).trans ?_
  · intro j _ hj
    exact if_neg hj
  · intro h
    exact (h (Finset.mem_univ _)).elim
  · exact if_pos rfl

/-- This is the reflection with the exact global sign used by the
amplification identity: it fixes the initial state and negates all other
computational-basis states. -/
theorem zeroReflection_apply (r : ℕ) (v : GateUniformRange.Space (2 ^ r))
    (j : Fin (2 ^ r)) (flag : Bool) :
    GateUniformRange.stateReflection (cleanInput r) v j flag =
      (if flag = false ∧
          j = GatePointerEncoding.wordEquivFin r (GateWalshWords.zeroWord r)
        then (1 : ℂ) else -1) * v j flag := by
  rw [GateUniformRange.stateReflection_apply, inner_cleanInput]
  by_cases hj : j = GatePointerEncoding.wordEquivFin r (GateWalshWords.zeroWord r)
  · subst j
    cases flag <;> simp [cleanInput]; ring
  · change j ≠ GatePointerEncoding.wordFin (GateWalshWords.zeroWord r) at hj
    cases flag <;> simp [cleanInput, hj]

theorem wordValue_eq_zero_iff (x : GatePointerEncoding.Word r) :
    GatePointerEncoding.wordValue x = 0 ↔ x = GateWalshWords.zeroWord r := by
  constructor
  · intro hx
    apply GatePointerEncoding.wordValue_injective
    simpa only [show GateWalshWords.zeroWord r = GatePointerEncoding.zeroWord r
      from rfl, GatePointerEncoding.wordValue_zero] using hx
  · rintro rfl
    exact GatePointerEncoding.wordValue_zero r

theorem zeroReflection_word (r : ℕ) (v : GateUniformRange.Space (2 ^ r))
    (x : GatePointerEncoding.Word r) (flag : Bool) :
    GateUniformRange.stateReflection (cleanInput r) v
        (GatePointerEncoding.wordEquivFin r x) flag =
      (if flag = false ∧ GatePointerEncoding.wordValue x = 0
        then (1 : ℂ) else -1) *
        v (GatePointerEncoding.wordEquivFin r x) flag := by
  rw [zeroReflection_apply]
  have he : GatePointerEncoding.wordEquivFin r x =
      GatePointerEncoding.wordEquivFin r (GateWalshWords.zeroWord r) ↔
      x = GateWalshWords.zeroWord r :=
    ⟨fun h => (GatePointerEncoding.wordEquivFin r).injective h,
      fun h => congrArg (GatePointerEncoding.wordEquivFin r) h⟩
  simp only [he, wordValue_eq_zero_iff]

end
end SparseHamiltonian.GateWalshHilbert
