import SparseODE.ODEGaussianComplex

/-!
# Holomorphy of the complex-frequency operator evolution

The exponential is analytic on the Banach algebra of bounded operators.
Composing it with the affine complex-frequency generator therefore gives an
entire operator-valued function, even when the two input operators do not
commute. This is a regularity prerequisite for the Gaussian contour argument;
it does not assume or assert an integral representation.

Requires Mathlib.Analysis.Analytic.Constructions.
-/

namespace SparseHamiltonian.ODEComplexFrequency

noncomputable section
open ContinuousLinearMap NormedSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [CompleteSpace V]

omit [CompleteSpace V] in
/-- The affine operator generator is complex analytic everywhere. -/
theorem generator_analyticAt (D H : V →L[ℂ] V) (z : ℂ) :
    AnalyticAt ℂ (generator D H) z := by
  have hFrequency : AnalyticAt ℂ (fun ζ : ℂ => H + ζ • D) z :=
    (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => H) z).add
      ((analyticAt_id : AnalyticAt ℂ (fun ζ : ℂ => ζ) z).smul
        (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => D) z))
  exact hFrequency.const_smul (c := -Complex.I)

/-- The full operator exponential is entire without a commutativity promise. -/
theorem evolution_analyticAt (D H : V →L[ℂ] V) (u : ℝ) (z : ℂ) :
    AnalyticAt ℂ (evolution D H u) z := by
  have hScaled : AnalyticAt ℂ (fun ζ : ℂ => u • generator D H ζ) z :=
    (generator_analyticAt D H z).const_smul (c := u)
  convert! (AnalyticAt.comp (f := fun ζ : ℂ => u • generator D H ζ) (x := z)
    (NormedSpace.exp_analytic (𝕂 := ℂ) (u • generator D H z)) hScaled) using 1

/-- Every complex frequency has a complex Fréchet derivative. -/
theorem evolution_differentiable (D H : V →L[ℂ] V) (u : ℝ) :
    Differentiable ℂ (evolution D H u) := by
  intro z
  exact (evolution_analyticAt D H u z).differentiableAt

/-- The same entire function is analytic in a neighborhood of every point
of any prescribed contour domain. -/
theorem evolution_analyticOnNhd (D H : V →L[ℂ] V) (u : ℝ) (S : Set ℂ) :
    AnalyticOnNhd ℂ (evolution D H u) S := by
  intro z _
  exact evolution_analyticAt D H u z

/-- In particular no boundary regularity premise is required when applying
a complex contour theorem on a closed rectangle. -/
theorem evolution_differentiableOn (D H : V →L[ℂ] V) (u : ℝ) (S : Set ℂ) :
    DifferentiableOn ℂ (evolution D H u) S :=
  (evolution_differentiable D H u).differentiableOn

end
end SparseHamiltonian.ODEComplexFrequency
