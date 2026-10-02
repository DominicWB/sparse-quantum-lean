import SparseHamiltonian.LocalRotation

/-!
# Contractivity of the actual chronological private block

Local conservation of private plus public energy telescopes over time. The
private output therefore contracts the genuine finite Hilbert direct sum,
without any normality assumption on the chronological operator.
-/

namespace SparseHamiltonian.ChronologicalContraction

noncomputable section

open ContinuousLinearMap
open SparseHamiltonian.ChronologicalResolvent
open SparseHamiltonian.FiniteChronologicalInverse
open scoped BigOperators

variable {P V : Type*}
  [NormedAddCommGroup P] [NormedSpace ℂ P]
  [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- Exact conservation along the forced chronology, with the final public
state retained as the only boundary term. -/
theorem chronological_energy_sum (R : V →L[ℂ] V) (A : P →L[ℂ] V)
    (u : P →L[ℂ] P) (B : V →L[ℂ] P)
    (hStep : ∀ x p, ‖R x + A p‖ ^ 2 + ‖u p + B x‖ ^ 2 =
      ‖x‖ ^ 2 + ‖p‖ ^ 2) (y : ℕ → V) (T : ℕ) :
    (∑ k ∈ Finset.range T, ‖chronologicalPrivateState R A u B y k‖ ^ 2) +
      ‖forcedPublicState u B y T‖ ^ 2 = ∑ k ∈ Finset.range T, ‖y k‖ ^ 2 := by
  induction T with
  | zero => simp
  | succ T hT =>
      have h := hStep (y T) (forcedPublicState u B y T)
      change ‖chronologicalPrivateState R A u B y T‖ ^ 2 +
        ‖forcedPublicState u B y (T + 1)‖ ^ 2 =
        ‖y T‖ ^ 2 + ‖forcedPublicState u B y T‖ ^ 2 at h
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      linarith

/-- Energy conservation for the actual finite block operator on the ℓ² sum. -/
theorem chronologicalOperator_energy (R : V →L[ℂ] V) (A : P →L[ℂ] V)
    (u : P →L[ℂ] P) (B : V →L[ℂ] P)
    (hStep : ∀ x p, ‖R x + A p‖ ^ 2 + ‖u p + B x‖ ^ 2 =
      ‖x‖ ^ 2 + ‖p‖ ^ 2) (T : ℕ) (x : BlockOperator.H T V) :
    ‖chronologicalOperator R A u B T x‖ ^ 2 +
      ‖forcedPublicState u B (extendSequence x) T‖ ^ 2 = ‖x‖ ^ 2 := by
  have h := chronological_energy_sum R A u B hStep (extendSequence x) T
  have hout : chronologicalOperator R A u B T x =
      restrictSequence T (chronologicalPrivateState R A u B (extendSequence x)) := by
    have hh : chronologicalOperator R A u B T
        (restrictSequence T (extendSequence x)) =
        restrictSequence T (chronologicalPrivateState R A u B (extendSequence x)) := by
      ext k
      exact chronologicalOperator_apply R A u B (extendSequence x) k
    simpa only [restrict_extend] using hh
  rw [hout, PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  simp only [restrictSequence_apply]
  rw [Fin.sum_univ_eq_sum_range
    (fun k => ‖chronologicalPrivateState R A u B (extendSequence x) k‖ ^ 2) T]
  have hin : (∑ k : Fin T, ‖x k‖ ^ 2) =
      ∑ k ∈ Finset.range T, ‖extendSequence x k‖ ^ 2 := by
    simpa only [extendSequence_apply] using
      (Fin.sum_univ_eq_sum_range (fun k => ‖extendSequence x k‖ ^ 2) T)
  rw [hin]
  exact h

/-- An energy-preserving one-step colligation gives a contractive finite
chronological private operator. -/
theorem chronologicalOperator_norm_le_one (R : V →L[ℂ] V) (A : P →L[ℂ] V)
    (u : P →L[ℂ] P) (B : V →L[ℂ] P)
    (hStep : ∀ x p, ‖R x + A p‖ ^ 2 + ‖u p + B x‖ ^ 2 =
      ‖x‖ ^ 2 + ‖p‖ ^ 2) (T : ℕ) :
    ‖chronologicalOperator R A u B T‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  have h := chronologicalOperator_energy R A u B hStep T x
  have hsq : ‖chronologicalOperator R A u B T x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    nlinarith [sq_nonneg ‖forcedPublicState u B (extendSequence x) T‖]
  simpa only [one_mul] using
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

end

end SparseHamiltonian.ChronologicalContraction
