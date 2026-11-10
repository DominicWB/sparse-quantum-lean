import MeasuredUnitaryLowerBound.OperatorNorm.Bound
import MeasuredUnitaryLowerBound.Endpoint.Calls

set_option autoImplicit false
set_option synthInstance.maxSize 8192

/-!
# The operator-norm `Ω(√N)` bound over controlled and controlled-inverse entry calls

Corollary `hs:cor:unitary` of the manuscript (operator-norm error `0 < ε ≤ 1/2`, inverse calls
counted, `Θ(√N)`), with the access of the lower-bound setting (with inverses and the controls of
Lemma `access:lem:control`, Section `hsl:sec:main`) and measured algorithms by purification and
deferred measurement (proof of Lemma `hsl:lem:precision`). Measured algorithms over the call family
`AdaptiveODELowerBound.Access.callFamily` of the released entry oracle (forward, inverse, controlled
and controlled-inverse calls, each counted once) that implement every `U_m` within operator-norm
error `ε₀ ≤ 1/2` (`NormImplements`) meet the hypotheses of
`MeasuredUnitaryLowerBound.Calls.implementation_count_ge_measured_calls_endpoint` with success
probability one and trace distance `ε₀ √(1 - ε₀²/4)`:

* `implementation_count_ge_measured_calls_norm`:
  `(N (1 - ε₀ √(1 - ε₀²/4)) - 1)² ≤ 32 (N - 1) √(N - 1) Q`;
* `implementation_count_ge_measured_calls_norm_half`: at `ε₀ = 1/2`,
  `(N (1 - √15/8) - 1)² ≤ 32 (N - 1) √(N - 1) Q`;
* `implementation_count_ge_measured_calls_norm_sqrt`: `√(N - 1) ≤ 512 Q` for `N ≥ 3`.
-/

namespace MeasuredUnitaryLowerBound.OperatorNorm

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.Readout ContinuousLinearMap
open UnitaryImplementationExtensions.SearchFamily
open DeferredMeasurementLowerBounds.Model
open AdaptiveODELowerBound.Access (callFamily)
open scoped InnerProduct InnerProductSpace

variable {E G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

/-- **`Ω(√N)` for measured implementations over the call forms, in operator norm** (Corollary
`hs:cor:unitary`, last sentence). A measured algorithm over the four call forms of the released
entry oracle of the search family, on an isometric encoding `J` into `Joint Bool` of the oracle
space and read through an isometry `e`, that implements every `U_m` within operator-norm error
`ε₀ ≤ 1/2` makes, over its worst transcript, `Q` calls with
`(N (1 - ε₀ √(1 - ε₀²/4)) - 1)² ≤ 32 (N - 1) √(N - 1) Q`. -/
theorem implementation_count_ge_measured_calls_norm {N : ℕ} [NeZero N] (hN : 2 ≤ N)
    (γ η t ε : ℝ)
    (M : Measured (callFamily (AdaptiveUnitaryLowerBound.Entry.entryOracles N γ η t ε)) E)
    (J : EuclideanSpace ℂ (Fin N) →L[ℂ]
      Joint Bool (UnitaryEntryOracle.Physical (Fin N) (ZMod 2) γ η t ε))
    (hJ : J† ∘L J = 1) (e : E →L[ℂ] SysGarb (Fin N) G) (he : e† ∘L e = 1) {ε₀ : ℝ}
    (hε₀ : ε₀ ≤ 1 / 2)
    (himpl : ∀ m, NormImplements M J e m (SparseStateOverlap.matrixOperator (searchMatrix N m))
      ε₀) :
    ((N : ℝ) * (1 - ε₀ * Real.sqrt (1 - ε₀ ^ 2 / 4)) - 1) ^ 2 ≤
      32 * ((N : ℝ) - 1) * Real.sqrt ((N : ℝ) - 1) * M.worstCost (fun _ => 1) := by
  obtain ⟨hs, key⟩ := search_accurate_of_normImplements M J e he hε₀ himpl
  simpa only [one_mul] using
    MeasuredUnitaryLowerBound.Calls.implementation_count_ge_measured_calls_endpoint hN γ η t ε M
      J hJ e he (p₀ := 1) one_pos hs key

/-- **The operator-norm endpoint `ε = 1/2` over the call forms**: under the hypotheses of
`implementation_count_ge_measured_calls_norm` with `ε₀ = 1/2`,
`(N (1 - √15/8) - 1)² ≤ 32 (N - 1) √(N - 1) Q`. -/
theorem implementation_count_ge_measured_calls_norm_half {N : ℕ} [NeZero N] (hN : 2 ≤ N)
    (γ η t ε : ℝ)
    (M : Measured (callFamily (AdaptiveUnitaryLowerBound.Entry.entryOracles N γ η t ε)) E)
    (J : EuclideanSpace ℂ (Fin N) →L[ℂ]
      Joint Bool (UnitaryEntryOracle.Physical (Fin N) (ZMod 2) γ η t ε))
    (hJ : J† ∘L J = 1) (e : E →L[ℂ] SysGarb (Fin N) G) (he : e† ∘L e = 1)
    (himpl : ∀ m, NormImplements M J e m (SparseStateOverlap.matrixOperator (searchMatrix N m))
      (1 / 2)) :
    ((N : ℝ) * (1 - Real.sqrt 15 / 8) - 1) ^ 2 ≤
      32 * ((N : ℝ) - 1) * Real.sqrt ((N : ℝ) - 1) * M.worstCost (fun _ => 1) := by
  have h := implementation_count_ge_measured_calls_norm hN γ η t ε M J hJ e he (ε₀ := 1 / 2)
    le_rfl himpl
  rwa [sharp_half] at h

/-- **`Ω(√N)` at fixed operator-norm error over the call forms**: under the hypotheses of
`implementation_count_ge_measured_calls_norm` with `N ≥ 3`, `√(N - 1) ≤ 512 Q`. -/
theorem implementation_count_ge_measured_calls_norm_sqrt {N : ℕ} [NeZero N] (hN : 3 ≤ N)
    (γ η t ε : ℝ)
    (M : Measured (callFamily (AdaptiveUnitaryLowerBound.Entry.entryOracles N γ η t ε)) E)
    (J : EuclideanSpace ℂ (Fin N) →L[ℂ]
      Joint Bool (UnitaryEntryOracle.Physical (Fin N) (ZMod 2) γ η t ε))
    (hJ : J† ∘L J = 1) (e : E →L[ℂ] SysGarb (Fin N) G) (he : e† ∘L e = 1) {ε₀ : ℝ}
    (hε₀ : ε₀ ≤ 1 / 2)
    (himpl : ∀ m, NormImplements M J e m (SparseStateOverlap.matrixOperator (searchMatrix N m))
      ε₀) :
    Real.sqrt ((N : ℝ) - 1) ≤ 512 * M.worstCost (fun _ => 1) := by
  have hε0 : 0 ≤ ε₀ := (himpl 0).nonneg
  have hs : ε₀ * Real.sqrt (1 - ε₀ ^ 2 / 4) ≤ 1 / 2 := (sharp_le_self hε0).trans hε₀
  have h1 := implementation_count_ge_measured_calls_norm (by omega) γ η t ε M J hJ e he hε₀ himpl
  have h2 := sub_two_sq_le (N := N) (by omega) hs
  have h3 : ((N : ℝ) - 2) ^ 2 ≤
      (128 : ℝ) * ((N : ℝ) - 1) * Real.sqrt ((N : ℝ) - 1) * M.worstCost (fun _ => 1) := by
    linarith
  have h4 := MeasuredUnitaryLowerBound.Adaptive.sqrt_le_of_half hN h3
  linarith

end
end MeasuredUnitaryLowerBound.OperatorNorm
