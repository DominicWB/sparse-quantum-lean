import SparseODE.ODEActualSourceError

/-!
# Public source coefficients for sampled time-dependent forcing

The source register carries the initial state and the `M` left-endpoint
forcing terms `(T / M) • b_q`. The normalized joint source/LCHS coefficients
depend on these vectors only through their norms (`actual_coefficients_eq`).
With public norms `r₀` and `rb q`, the coefficient table, hence the seed, the
output flag and both amplification reflections, is fixed before the unknown
source directions (`coefficients`). Its absolute mass is exactly three
(`coefficients_mass`); the source mass is `r₀ + (T / M) ∑ rb q` (`mass`).
-/

namespace SparseHamiltonian.TimeDependentODE.PublicSource

noncomputable section
open scoped BigOperators

variable {M : ℕ}

/-- Public source norms: the initial norm and the weighted forcing norms. -/
def norms (r₀ T : ℝ) (rb : Fin M → ℝ) : Option (Fin M) → ℝ
  | none => r₀
  | some q => T / M * rb q

/-- Public source mass, the left-endpoint quadrature of `‖x₀‖ + ∫ ‖b‖`. -/
def mass (r₀ T : ℝ) (rb : Fin M → ℝ) : ℝ := r₀ + T / M * ∑ q, rb q

theorem sum_norms (r₀ T : ℝ) (rb : Fin M → ℝ) :
    ∑ a, norms r₀ T rb a = mass r₀ T rb := by
  rw [Fintype.sum_option]
  simp only [norms, mass, Finset.mul_sum]

theorem norms_nonneg (r₀ T : ℝ) (rb : Fin M → ℝ) (h₀ : 0 ≤ r₀) (hT : 0 ≤ T)
    (hb : ∀ q, 0 ≤ rb q) (a : Option (Fin M)) : 0 ≤ norms r₀ T rb a := by
  cases a with
  | none => exact h₀
  | some q => exact mul_nonneg (div_nonneg hT (Nat.cast_nonneg M)) (hb q)

/-- Source-loading probabilities from public norms only. -/
def probability (r₀ T : ℝ) (rb : Fin M → ℝ) (a : Option (Fin M)) : ℝ :=
  norms r₀ T rb a / mass r₀ T rb

/-- The public joint source/LCHS coefficient table. -/
def coefficients {ι : Type*} (r₀ T : ℝ) (rb : Fin M → ℝ) (c : ι → ℂ) :
    Option (Fin M) × ι → ℂ :=
  ODESourceCoefficients.productCoeff (probability r₀ T rb) c

/-- The public coefficient mass is exactly that of the LCHS table. -/
theorem coefficients_mass {ι : Type*} [Fintype ι] (r₀ T : ℝ) (rb : Fin M → ℝ)
    (h₀ : 0 ≤ r₀) (hT : 0 ≤ T) (hb : ∀ q, 0 ≤ rb q) (hB : 0 < mass r₀ T rb)
    (c : ι → ℂ) (hc : ODECoherentLCU.coefficientMass c = 3) :
    ODECoherentLCU.coefficientMass (coefficients r₀ T rb c) = 3 := by
  unfold coefficients
  rw [ODESourceCoefficients.coefficientMass_product (probability r₀ T rb) c
    (fun a => div_nonneg (norms_nonneg r₀ T rb h₀ hT hb a) hB.le)]
  unfold probability
  rw [← Finset.sum_div, sum_norms, div_self hB.ne', one_mul, hc]

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

omit [InnerProductSpace ℂ P] [CompleteSpace P] in
/-- Source vectors with the public norms have the public mass. -/
theorem mass_eq (z : Option (Fin M) → P) (r₀ T : ℝ) (rb : Fin M → ℝ)
    (hz : ∀ a, ‖z a‖ = norms r₀ T rb a) :
    ODESourceBranches.mass z = mass r₀ T rb := by
  unfold ODESourceBranches.mass
  rw [← sum_norms]
  exact Finset.sum_congr rfl (fun a _ => hz a)

omit [InnerProductSpace ℂ P] [CompleteSpace P] in
/-- Source vectors with the public norms have the public coefficients. -/
theorem actual_coefficients_eq {ι : Type*} [Fintype ι] (z : Option (Fin M) → P)
    (r₀ T : ℝ) (rb : Fin M → ℝ) (hz : ∀ a, ‖z a‖ = norms r₀ T rb a) (c : ι → ℂ) :
    ODEActualSourceError.coefficients z c = coefficients r₀ T rb c := by
  have hmass := mass_eq z r₀ T rb hz
  unfold ODEActualSourceError.coefficients coefficients
  congr 1
  funext a
  unfold ODESourceBranches.probability probability
  rw [hz a, hmass]

end

end SparseHamiltonian.TimeDependentODE.PublicSource
