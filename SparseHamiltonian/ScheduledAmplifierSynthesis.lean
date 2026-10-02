import SparseHamiltonian.FractionalAngleSeriesIdentity

/-!
# A fully constructed and scheduled amplitude multiplier

Both the approximating polynomial and its complementary polynomial are
constructed. The only inputs are the public amplitude bound and error target.
The relative approximation, gain bounds, exact phase budget and polynomial
normalization are conclusions, not supplied circuit or approximation premises.
-/
namespace SparseHamiltonian.ScheduledAmplifierSynthesis

noncomputable section
open Polynomial PolynomialCompletion
open ScheduledFractionalAmplifier (index inverseOrder phaseBudget)

/-- Finite coefficient normalization, independent of the oracle input. -/
def mass (A δ : ℝ) : ℝ := NormalizedAmplifierCompletion.mass (inverseOrder A)
  (AmplifierPolynomialConstruction.precisionCutoff δ)

theorem mass_bounds (A δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    1 ≤ mass A δ ∧ mass A δ ≤ 2 :=
  NormalizedAmplifierCompletion.mass_bounds _
    (ScheduledFractionalAmplifier.abs_inverseOrder_le_one A) _
    (ScheduledFractionalAmplifier.precisionCutoff_pos δ hδ hδ1)

theorem mass_pos (A δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) : 0 < mass A δ :=
  lt_of_lt_of_le zero_lt_one (mass_bounds A δ hδ hδ1).1

/-- Explicit endpoint-saturating real odd amplifier. -/
def polynomial (A δ : ℝ) : ℝ[X] :=
  NormalizedAmplifierCompletion.polynomial (inverseOrder A) (index A)
    (AmplifierPolynomialConstruction.precisionCutoff δ)

/-- The linear target gain uses the same finite normalization. -/
def gain (A δ : ℝ) : ℝ := (AmplifierSignalGeometry.order A : ℝ) / mass A δ

theorem gain_pos (A δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) : 0 < gain A δ :=
  div_pos (Nat.cast_pos.mpr (AmplifierSignalGeometry.order_pos A)) (mass_pos A δ hδ hδ1)

theorem gain_bounds (A δ : ℝ) (hA : 0 < A) (hA1 : A ≤ 1)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    1 / 8 ≤ gain A δ * A ∧ gain A δ * A ≤ 3 / 2 := by
  have hm := mass_bounds A δ hδ hδ1
  have hmp := mass_pos A δ hδ hδ1
  have hn := AmplifierSignalGeometry.order_mul_bounds A hA hA1
  unfold gain
  rw [div_mul_eq_mul_div]
  constructor
  · apply (le_div_iff₀ hmp).mpr
    nlinarith [hm.2, hn.1]
  · apply (div_le_iff₀ hmp).mpr
    nlinarith [hm.1, hn.2]

/-- Algebraic relation to the initially quarter-scaled approximation. -/
theorem eval_rescale (A δ x : ℝ) :
    (polynomial A δ).eval x =
      (4 / mass A δ) * (ScheduledFractionalAmplifier.polynomial A δ).eval x := by
  simp only [polynomial, NormalizedAmplifierCompletion.polynomial_eval,
    ScheduledFractionalAmplifier.polynomial, AmplifierPolynomialConstruction.amplifier_eval, mass]
  ring

theorem gain_rescale (A δ : ℝ) :
    gain A δ = (4 / mass A δ) * ScheduledFractionalAmplifier.gain A := by
  unfold gain ScheduledFractionalAmplifier.gain
  ring

/-- The coefficient series identity is discharged by the proved ODE uniqueness theorem. -/
theorem series_target (A y : ℝ) (hy : |y| ≤ 3 / 8) :
    FractionalAngleCoefficients.series (inverseOrder A) y =
      AmplifierSignalGeometry.correction (AmplifierSignalGeometry.order A) y := by
  rw [FractionalAngleSeriesIdentity.series_eq_target (inverseOrder A)
    (ScheduledFractionalAmplifier.abs_inverseOrder_le_one A)
    (ScheduledFractionalAmplifier.inverseOrder_pos A).ne' y (by linarith)]
  simp [inverseOrder, AmplifierSignalGeometry.correction, div_eq_mul_inv, mul_comm]

/-- Uniform relative approximation holds for the actual finite polynomial, including zero. -/
theorem real_relative_error (A δ : ℝ) (hA : 0 < A) (hA1 : A ≤ 1)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (x : ℝ) (hx : |x| ≤ A / 4) :
    |(polynomial A δ).eval x - gain A δ * x| ≤ δ * gain A δ * |x| := by
  have h := ScheduledFractionalAmplifier.relative_error_of_series A δ hA hA1 hδ
    (series_target A) x hx
  have hf : 0 < 4 / mass A δ := div_pos (by norm_num) (mass_pos A δ hδ hδ1)
  calc
    |(polynomial A δ).eval x - gain A δ * x| =
        (4 / mass A δ) * |(ScheduledFractionalAmplifier.polynomial A δ).eval x -
          ScheduledFractionalAmplifier.gain A * x| := by
      rw [eval_rescale, gain_rescale, mul_assoc, ← mul_sub, abs_mul, abs_of_pos hf]
    _ ≤ (4 / mass A δ) * (δ * ScheduledFractionalAmplifier.gain A * |x|) :=
      mul_le_mul_of_nonneg_left h hf.le
    _ = δ * gain A δ * |x| := by rw [gain_rescale]; ring

/-- Complex-amplitude form required by the native sparse-circuit theorem. -/
theorem relative_error (A δ : ℝ) (hA : 0 < A) (hA1 : A ≤ 1)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (x : ℝ) (hx : |x| ≤ A / 4) :
    ‖(complexify (polynomial A δ)).eval (x : ℂ) - (gain A δ : ℂ) * (x : ℂ)‖ ≤
      (δ * gain A δ) * |x| := by
  rw [complexify_eval_real, ← Complex.ofReal_mul, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs]
  exact real_relative_error A δ hA hA1 hδ hδ1 x hx

theorem complex_parity (A δ : ℝ) :
    (complexify (polynomial A δ)).comp (-X) = -(complexify (polynomial A δ)) := by
  have h := NormalizedAmplifierCompletion.polynomial_parity (inverseOrder A) (index A)
    (AmplifierPolynomialConstruction.precisionCutoff δ)
  simpa [complexify, polynomial, Polynomial.map_comp] using
    congrArg (fun p : ℝ[X] => p.map (algebraMap ℝ ℂ)) h

theorem complex_degree (A δ : ℝ) :
    (complexify (polynomial A δ)).natDegree ≤ 2 * phaseBudget A δ + 1 := by
  have hd := NormalizedAmplifierCompletion.polynomial_degree (inverseOrder A) (index A)
    (AmplifierPolynomialConstruction.precisionCutoff δ)
  have hm : (complexify (polynomial A δ)).natDegree ≤ (polynomial A δ).natDegree :=
    Polynomial.natDegree_map_le
  have he : 2 * AmplifierPolynomialConstruction.precisionCutoff δ * (2 * index A + 1) =
      2 * phaseBudget A δ := by
    simp only [phaseBudget, AmplifierSignalGeometry.order, index]
    ring
  rw [he] at hd
  exact hm.trans (hd.trans (Nat.le_succ _))

/-- Complement existence with all degree and parity requirements discharged. -/
theorem completion (A δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ B : ℂ[X], PolynomialUnitarity.IsNormalized (complexify (polynomial A δ)) B ∧
      B.comp (-X) = B ∧ B.natDegree ≤ 2 * phaseBudget A δ := by
  simpa only [polynomial, phaseBudget, AmplifierSignalGeometry.order, index] using
    NormalizedAmplifierCompletion.completion (inverseOrder A)
      (ScheduledFractionalAmplifier.abs_inverseOrder_le_one A) (index A)
      (AmplifierPolynomialConstruction.precisionCutoff δ)
      (ScheduledFractionalAmplifier.precisionCutoff_pos δ hδ hδ1)

/-- The phase list is constructed with the public schedule's exact length. -/
theorem phase_list (A δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ v u : AmplitudePolynomialSequence.UnitPhase,
      ∃ ss : List AmplitudePolynomialSequence.Phases,
      ss.length = phaseBudget A δ ∧ complexify (polynomial A δ) =
        C ((v : ℂ) * (u : ℂ)) * (AmplitudePolynomialSequence.polynomials ss).1 := by
  simpa only [polynomial, phaseBudget, AmplifierSignalGeometry.order, index] using
    NormalizedAmplifierCompletion.phase_list (inverseOrder A)
      (ScheduledFractionalAmplifier.abs_inverseOrder_le_one A) (index A)
      (AmplifierPolynomialConstruction.precisionCutoff δ)
      (ScheduledFractionalAmplifier.precisionCutoff_pos δ hδ hδ1)

end
end SparseHamiltonian.ScheduledAmplifierSynthesis
