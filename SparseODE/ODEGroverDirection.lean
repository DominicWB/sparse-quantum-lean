import SparseODE.ODEGroverAverage

/-!
# Successful directions under exact amplification of the actual circuit

The Grover coefficients can change sign. Such a sign is one irrelevant
global phase of the heralded state. The alignment below is mathematical;
no estimate of the unknown amplitude or phase-correction oracle is needed.

-/

namespace SparseHamiltonian.ODEGroverDirection

noncomputable section
open ContinuousLinearMap ODEStateNormalization
open scoped InnerProduct

variable {P K : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [CompleteSpace P] in
theorem unitDirection_neg (v : P) : unitDirection (-v) = -unitDirection v := by
  simp only [unitDirection, norm_neg, smul_neg]

omit [CompleteSpace P] in
/-- A nonzero real multiple has precisely the same direction up to a sign. -/
theorem real_multiple_phase (r : ℝ) (hr : r ≠ 0) (v : P) :
    ∃ ω : ℂ, ‖ω‖ = 1 ∧
      ω • unitDirection ((r : ℂ) • v) = unitDirection v := by
  by_cases hpos : 0 < r
  · refine ⟨1, norm_one, ?_⟩
    rw [one_smul, Complex.coe_smul,
      ODEHeraldedSuccess.unitDirection_pos_smul r hpos]
  · have hneg : 0 < -r := by
      have hrneg : r < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hr
      linarith
    have hscalar : (r : ℂ) • v = -(((-r : ℝ) : ℂ) • v) := by
      rw [Complex.ofReal_neg, neg_smul, neg_neg]
    refine ⟨-1, by simp only [norm_neg, norm_one], ?_⟩
    rw [hscalar, unitDirection_neg]
    simp only [Complex.coe_smul]
    rw [ODEHeraldedSuccess.unitDirection_pos_smul (-r) hneg,
      neg_one_smul, neg_neg]

/-- Decoding an output projection does not alter its public coordinates. -/
theorem decode_projected (F : P →L[ℂ] K) (hF : F† ∘L F = 1) (v : K) :
    (F†) (ODEHeraldedSuccess.successProjector F v) = (F†) v := by
  have hId (w : P) : (F†) (F w) = w :=
    congrArg (fun A : P →L[ℂ] P => A w) hF
  exact hId ((F†) v)

/-- A proportional physical good component gives exactly proportional
public decoded vectors, even when the failed components differ. -/
theorem decode_real_multiple (F : P →L[ℂ] K) (hF : F† ∘L F = 1)
    (v w : K) (r : ℝ)
    (hGood : ODEHeraldedSuccess.successProjector F w =
      (r : ℂ) • ODEHeraldedSuccess.successProjector F v) :
    (F†) w = (r : ℂ) • (F†) v := by
  have h := congrArg (fun z : K => (F†) z) hGood
  simpa only [map_smul, decode_projected F hF] using h

omit [CompleteSpace P] in
/-- Every successful trial inherits the original direction error without
an iteration-count multiplier or a tighter simulation tolerance. -/
theorem direction_error_of_real_multiple (d z target : P) (r η : ℝ)
    (hMultiple : z = (r : ℂ) • d) (hz : z ≠ 0)
    (hError : ‖unitDirection d - unitDirection target‖ ≤ η) :
    ∃ ω : ℂ, ‖ω‖ = 1 ∧
      ‖ω • unitDirection z - unitDirection target‖ ≤ η := by
  have hr : r ≠ 0 := by
    intro hr
    apply hz
    simpa only [hr, Complex.ofReal_zero, zero_smul] using hMultiple
  obtain ⟨ω, hω, hAlign⟩ := real_multiple_phase r hr d
  refine ⟨ω, hω, ?_⟩
  rw [hMultiple, hAlign]
  exact hError

end
end SparseHamiltonian.ODEGroverDirection
