import SparseHamiltonian.PolynomialPhaseReduction

/-!
# Realizing synthesized polynomial pairs with paired phase circuits

An odd list of signal reflections is regrouped into the two-query iterations
already transported to the native sparse preparation circuit. The only extra
operations are a fixed good-coordinate phase and a fixed global phase. This
module connects algebraic converse synthesis to the existing physical circuit,
without introducing additional oracle calls.
-/

namespace SparseHamiltonian.PhysicalPhaseSynthesis

noncomputable section
open Polynomial AmplitudePolynomialSequence PolynomialPhaseReduction
open ComplexAmplitudeRotation ContinuousLinearMap

/-- Flatten each two-query phase pair in execution-list order. -/
def flatten : List Phases → List UnitPhase
  | [] => []
  | s :: ss => s.1 :: s.2 :: flatten ss

/-- Flattening preserves the exact number of single-query steps. -/
theorem flatten_length (ss : List Phases) : (flatten ss).length = 2 * ss.length := by
  induction ss with
  | nil => rfl
  | cons s ss ih => simp only [flatten, List.length_cons, ih]; omega

/-- An initial phase and an odd number of reflections regroup exactly into
paired iterations, with one free final coordinate phase. -/
theorem synthesized_flatten (v u : UnitPhase) (ss : List Phases) :
    synthesized v (u :: flatten ss) =
      (C ((v : ℂ) * (u : ℂ)) * (polynomials ss).1, C (v : ℂ) * (polynomials ss).2) := by
  induction ss generalizing u with
  | nil =>
      simp only [flatten, synthesized, polynomials, forwardGood, reverseGood, reverseBad, map_one,
        map_mul, mul_zero, sub_zero, add_zero, mul_one]
      apply Prod.ext <;> dsimp <;> ring
  | cons s ss ih =>
      change
        (forwardGood u
          (forwardGood s.1 (synthesized v (s.2 :: flatten ss)).1
            (synthesized v (s.2 :: flatten ss)).2)
          (reverseBad 1 (synthesized v (s.2 :: flatten ss)).1
            (synthesized v (s.2 :: flatten ss)).2),
        reverseBad 1
          (forwardGood s.1 (synthesized v (s.2 :: flatten ss)).1
            (synthesized v (s.2 :: flatten ss)).2)
          (reverseBad 1 (synthesized v (s.2 :: flatten ss)).1
            (synthesized v (s.2 :: flatten ss)).2)) =
        (C ((v : ℂ) * (u : ℂ)) * nextGood s.1 s.2 (polynomials ss).1 (polynomials ss).2,
          C (v : ℂ) * nextBad s.1 s.2 (polynomials ss).1 (polynomials ss).2)
      rw [ih]
      apply Prod.ext <;>
        simp only [forwardGood, reverseGood, reverseBad, nextGood, nextBad, map_mul, map_sub, map_one] <;> ring

/-- Every odd phase list admits the paired grouping with its exact pair count. -/
theorem odd_list_grouping (m : ℕ) (us : List UnitPhase) (h : us.length = 2 * m + 1) :
    ∃ u : UnitPhase, ∃ ss : List Phases,
      ss.length = m ∧ us = u :: flatten ss := by
  induction m generalizing us with
  | zero =>
      cases us with
      | nil => simp at h
      | cons u us =>
          have hu : us = [] := by simpa using h
          exact ⟨u, [], rfl, by simp [hu, flatten]⟩
  | succ m ih =>
      cases us with
      | nil => simp at h
      | cons u us =>
          cases us with
          | nil => simp at h
          | cons a us =>
              obtain ⟨c, ss, hlen, heq⟩ := ih us (by simp only [List.length_cons] at h; omega)
              refine ⟨u, (a, c) :: ss, by simp [hlen], ?_⟩
              simp [heq, flatten]

/-- Converse synthesis in the exact phase-pair convention of the native circuit. -/
theorem paired_synthesis (m : ℕ) (P Q : ℂ[X])
    (hP : P.natDegree ≤ 2 * m + 1) (hQ : Q.natDegree ≤ 2 * m)
    (hp : P.comp (-X) = -P) (hq : Q.comp (-X) = Q)
    (h : PolynomialUnitarity.IsNormalized P Q) :
    ∃ v u : UnitPhase, ∃ ss : List Phases, ss.length = m ∧
      P = C ((v : ℂ) * (u : ℂ)) * (polynomials ss).1 ∧
      Q = C (v : ℂ) * (polynomials ss).2 := by
  obtain ⟨v, us, hlen, heq⟩ := synthesis_odd m P Q hP hQ hp hq h
  obtain ⟨u, ss, hss, hus⟩ := odd_list_grouping m us hlen
  rw [hus, synthesized_flatten] at heq
  exact ⟨v, u, ss, hss, (congrArg Prod.fst heq).symm, (congrArg Prod.snd heq).symm⟩

/-- The two fixed output phases give exactly the synthesized first column. -/
theorem phased_column (x : ℝ) (v u : UnitPhase) (P Q : ℂ[X]) :
    ((v : ℂ) • (phase u (column x P Q))) =
      column x (C ((v : ℂ) * (u : ℂ)) * P) (C (v : ℂ) * Q) := by
  apply PiLp.ext
  intro b
  cases b <;>
    simp only [PiLp.smul_apply, smul_eq_mul, phase_false, phase_true, column_false, column_true,
      eval_mul, eval_C] <;> ring

/-- Algebraically admissible odd polynomial pairs are realized by the existing
physical phase circuit with exactly `m` two-query iterations. -/
theorem circuit_synthesis (m : ℕ) (P Q : ℂ[X])
    (hP : P.natDegree ≤ 2 * m + 1) (hQ : Q.natDegree ≤ 2 * m)
    (hp : P.comp (-X) = -P) (hq : Q.comp (-X) = Q)
    (h : PolynomialUnitarity.IsNormalized P Q) :
    ∃ v u : UnitPhase, ∃ ss : List Phases, ss.length = m ∧
      ∀ (x : ℝ), |x| ≤ 1 →
        ((v : ℂ) • (phase u * sequence x ss)) clean = column x P Q := by
  obtain ⟨v, u, ss, hss, hgood, hbad⟩ := paired_synthesis m P Q hP hQ hp hq h
  refine ⟨v, u, ss, hss, ?_⟩
  intro x hx
  simp only [smul_apply, mul_apply_eq_comp, sequence_column x hx, phased_column, hgood, hbad]

end
end SparseHamiltonian.PhysicalPhaseSynthesis
