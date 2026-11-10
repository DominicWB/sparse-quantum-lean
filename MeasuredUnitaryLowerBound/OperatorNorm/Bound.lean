import MeasuredUnitaryLowerBound.OperatorNorm.Accuracy
import MeasuredUnitaryLowerBound.Endpoint.Measured

set_option autoImplicit false
set_option synthInstance.maxSize 8192

/-!
# The operator-norm `Ω(√N)` bound for measured algorithms

Corollary `hs:cor:unitary` of the manuscript: error `‖A_U - U‖ ≤ ε` in operator norm (eq.
`hs:eq:unitaryerror`) for `0 < ε ≤ 1/2`, inverse calls counted, "the constant-error worst-case
complexity is `Θ(√N)`", lower half by the reduction to unstructured search (`U_m |0⟩ = |m⟩`), for
measured algorithms by purification and deferred measurement (proof of Lemma `hsl:lem:precision`).

A measured algorithm over the released entry oracle of the search family that implements every
`U_m` within operator-norm error `ε₀ ≤ 1/2` (`NormImplements`) succeeds with probability one and
outputs `U_m |0⟩` within trace distance `ε₀ √(1 - ε₀²/4) < 1/2`
(`densityAccurate_of_normImplements`, `sharp_lt_half`; on the search inputs
`search_accurate_of_normImplements`), so the trace-distance endpoint bounds
`MeasuredUnitaryLowerBound.Deferred.implementation_count_ge_measured_endpoint` and
`entry_count_ge_measured_endpoint` apply with `p₀ = 1`. With `Q` the worst-case number of calls
over all transcripts, inverse calls included:

* `implementation_count_ge_measured_norm`:
  `(N (1 - ε₀ √(1 - ε₀²/4)) - 1)² ≤ 4 (N - 1) √(N - 1) Q`;
* `entry_count_ge_measured_norm`: the same for the ordinary entry lookup with any payload;
* `implementation_count_ge_measured_norm_half`: at `ε₀ = 1/2`,
  `(N (1 - √15/8) - 1)² ≤ 4 (N - 1) √(N - 1) Q`;
* `implementation_count_ge_measured_norm_sqrt`: `√(N - 1) ≤ 64 Q` for `N ≥ 3` and every
  `ε₀ ≤ 1/2`.

Unlike the trace-distance endpoint, the operator-norm bound is not empty at `N = 2`: since
`ε₀ √(1 - ε₀²/4) ≤ √15/8 < 1/2` (`sharp_le_of_le_half`, `sqrt_fifteen_div_eight_lt_half`),
`N (1 - ε₀ √(1 - ε₀²/4)) - 1 > 0` there, and the bound forces at least one call, as it must
(`U_0 = 1` and `U_1 = X` are at operator-norm distance `2`).

The bounds quantify over measured algorithms `Measured`, which act on an input slot. Adaptive
protocols (`Protocol.Tree`) reach the measured model only through
`DeferredMeasurementLowerBounds.Model.ofTree`, on finite-dimensional workspaces and from a fixed
seed; no operator-norm form is stated for them.
-/

namespace MeasuredUnitaryLowerBound.OperatorNorm

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.Readout ContinuousLinearMap
open UnitaryImplementationExtensions.SearchFamily
open DeferredMeasurementLowerBounds.Model
open AdaptiveHamiltonianLowerBound (DensityAccurate)
open scoped InnerProduct InnerProductSpace

variable {E G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

/-- **The search inputs**: if `M` implements every search unitary `U_m` within operator-norm
error `ε₀ ≤ 1/2`, then `ε₀ √(1 - ε₀²/4) ≤ 1/2` and, on the encoded input `J |0⟩` and every
instance `m`, `M` succeeds with probability one and its conditional output is within trace
distance `ε₀ √(1 - ε₀²/4)` of `U_m |0⟩`: the hypotheses of the trace-distance endpoint bounds
with `p₀ = 1`. -/
theorem search_accurate_of_normImplements {N : ℕ} [NeZero N] {K L : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] {O : L → Fin N → K →L[ℂ] K}
    (M : Measured O E) (J : EuclideanSpace ℂ (Fin N) →L[ℂ] K) (e : E →L[ℂ] SysGarb (Fin N) G)
    (he : e† ∘L e = 1) {ε₀ : ℝ} (hε₀ : ε₀ ≤ 1 / 2)
    (himpl : ∀ m, NormImplements M J e m
      (SparseStateOverlap.matrixOperator (searchMatrix N m)) ε₀) :
    ε₀ * Real.sqrt (1 - ε₀ ^ 2 / 4) ≤ 1 / 2 ∧
      ∀ m, 1 ≤ M.successMass m (J (EuclideanSpace.single 0 1)) ∧
        DensityAccurate e (M.conditionalDensity m (J (EuclideanSpace.single 0 1)))
          (SparseStateOverlap.matrixOperator (searchMatrix N m) (EuclideanSpace.single 0 1))
          (ε₀ * Real.sqrt (1 - ε₀ ^ 2 / 4)) := by
  have hε0 : 0 ≤ ε₀ := (himpl 0).nonneg
  have hε2 : ε₀ ^ 2 ≤ 2 := by nlinarith
  refine ⟨(sharp_le_self hε0).trans hε₀, fun m => ?_⟩
  have hψ : ‖(EuclideanSpace.single 0 1 : EuclideanSpace ℂ (Fin N))‖ = 1 := by
    rw [PiLp.norm_single, norm_one]
  have hUψ : ‖SparseStateOverlap.matrixOperator (searchMatrix N m)
      (EuclideanSpace.single 0 1)‖ ≤ 1 := by
    rw [searchMatrix_single_zero, PiLp.norm_single, norm_one]
  have key := densityAccurate_of_normImplements M J e he m _ hε2 (himpl m) hψ hUψ
  exact ⟨key.1.ge, key.2⟩

/-- **`Ω(√N)` for measured implementations in operator norm** (Corollary `hs:cor:unitary`, last
sentence). A measured algorithm over the released entry oracle of the search family, run on an
isometric encoding `J` and read through an isometry `e`, that implements every search unitary
`U_m` within operator-norm error `ε₀ ≤ 1/2` makes, over its worst transcript, `Q` calls with
`(N (1 - ε₀ √(1 - ε₀²/4)) - 1)² ≤ 4 (N - 1) √(N - 1) Q`. -/
theorem implementation_count_ge_measured_norm {N : ℕ} [NeZero N] (hN : 2 ≤ N) (γ η t ε : ℝ)
    (M : Measured (fun (_ : Unit) (m : Fin N) =>
      UnitaryEntryOracle.oracle (searchData N) γ η t ε m) E)
    (J : EuclideanSpace ℂ (Fin N) →L[ℂ] UnitaryEntryOracle.Physical (Fin N) (ZMod 2) γ η t ε)
    (hJ : J† ∘L J = 1) (e : E →L[ℂ] SysGarb (Fin N) G) (he : e† ∘L e = 1) {ε₀ : ℝ}
    (hε₀ : ε₀ ≤ 1 / 2)
    (himpl : ∀ m, NormImplements M J e m (SparseStateOverlap.matrixOperator (searchMatrix N m))
      ε₀) :
    ((N : ℝ) * (1 - ε₀ * Real.sqrt (1 - ε₀ ^ 2 / 4)) - 1) ^ 2 ≤
      4 * ((N : ℝ) - 1) * Real.sqrt ((N : ℝ) - 1) * M.worstCost (fun _ => 1) := by
  obtain ⟨hs, key⟩ := search_accurate_of_normImplements M J e he hε₀ himpl
  simpa only [one_mul] using
    MeasuredUnitaryLowerBound.Deferred.implementation_count_ge_measured_endpoint hN γ η t ε M J
      hJ e he (p₀ := 1) one_pos hs key

/-- **Entry-lookup calls in operator norm** (Corollary `hs:cor:unitary`, last sentence). The
bound of `implementation_count_ge_measured_norm` for measured algorithms over the ordinary entry
lookup of the search family with any payload `W`. -/
theorem entry_count_ge_measured_norm {W : Type*} [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] [CompleteSpace W] {N : ℕ} [NeZero N] (hN : 2 ≤ N)
    (M : Measured (fun (_ : Unit) (m : Fin N) =>
      LookupControlledGate.oracle (K := W) (searchTable N) m) E)
    (J : EuclideanSpace ℂ (Fin N) →L[ℂ] PiLp 2 (fun _ : (Fin N × Fin N) × ZMod 2 => W))
    (hJ : J† ∘L J = 1) (e : E →L[ℂ] SysGarb (Fin N) G) (he : e† ∘L e = 1) {ε₀ : ℝ}
    (hε₀ : ε₀ ≤ 1 / 2)
    (himpl : ∀ m, NormImplements M J e m (SparseStateOverlap.matrixOperator (searchMatrix N m))
      ε₀) :
    ((N : ℝ) * (1 - ε₀ * Real.sqrt (1 - ε₀ ^ 2 / 4)) - 1) ^ 2 ≤
      4 * ((N : ℝ) - 1) * Real.sqrt ((N : ℝ) - 1) * M.worstCost (fun _ => 1) := by
  obtain ⟨hs, key⟩ := search_accurate_of_normImplements M J e he hε₀ himpl
  simpa only [one_mul] using
    MeasuredUnitaryLowerBound.Deferred.entry_count_ge_measured_endpoint hN M J hJ e he (p₀ := 1)
      one_pos hs key

/-- **The operator-norm endpoint `ε = 1/2`** for measured implementations: under the hypotheses
of `implementation_count_ge_measured_norm` with `ε₀ = 1/2`,
`(N (1 - √15/8) - 1)² ≤ 4 (N - 1) √(N - 1) Q`. -/
theorem implementation_count_ge_measured_norm_half {N : ℕ} [NeZero N] (hN : 2 ≤ N)
    (γ η t ε : ℝ)
    (M : Measured (fun (_ : Unit) (m : Fin N) =>
      UnitaryEntryOracle.oracle (searchData N) γ η t ε m) E)
    (J : EuclideanSpace ℂ (Fin N) →L[ℂ] UnitaryEntryOracle.Physical (Fin N) (ZMod 2) γ η t ε)
    (hJ : J† ∘L J = 1) (e : E →L[ℂ] SysGarb (Fin N) G) (he : e† ∘L e = 1)
    (himpl : ∀ m, NormImplements M J e m (SparseStateOverlap.matrixOperator (searchMatrix N m))
      (1 / 2)) :
    ((N : ℝ) * (1 - Real.sqrt 15 / 8) - 1) ^ 2 ≤
      4 * ((N : ℝ) - 1) * Real.sqrt ((N : ℝ) - 1) * M.worstCost (fun _ => 1) := by
  have h := implementation_count_ge_measured_norm hN γ η t ε M J hJ e he (ε₀ := 1 / 2) le_rfl
    himpl
  rwa [sharp_half] at h

/-- **`Ω(√N)` at fixed operator-norm error** for measured implementations: under the hypotheses
of `implementation_count_ge_measured_norm` with `N ≥ 3`, `√(N - 1) ≤ 64 Q`. -/
theorem implementation_count_ge_measured_norm_sqrt {N : ℕ} [NeZero N] (hN : 3 ≤ N)
    (γ η t ε : ℝ)
    (M : Measured (fun (_ : Unit) (m : Fin N) =>
      UnitaryEntryOracle.oracle (searchData N) γ η t ε m) E)
    (J : EuclideanSpace ℂ (Fin N) →L[ℂ] UnitaryEntryOracle.Physical (Fin N) (ZMod 2) γ η t ε)
    (hJ : J† ∘L J = 1) (e : E →L[ℂ] SysGarb (Fin N) G) (he : e† ∘L e = 1) {ε₀ : ℝ}
    (hε₀ : ε₀ ≤ 1 / 2)
    (himpl : ∀ m, NormImplements M J e m (SparseStateOverlap.matrixOperator (searchMatrix N m))
      ε₀) :
    Real.sqrt ((N : ℝ) - 1) ≤ 64 * M.worstCost (fun _ => 1) := by
  have hε0 : 0 ≤ ε₀ := (himpl 0).nonneg
  have hs : ε₀ * Real.sqrt (1 - ε₀ ^ 2 / 4) ≤ 1 / 2 := (sharp_le_self hε0).trans hε₀
  have h1 := implementation_count_ge_measured_norm (by omega) γ η t ε M J hJ e he hε₀ himpl
  have h2 := sub_two_sq_le (N := N) (by omega) hs
  have h3 : ((N : ℝ) - 2) ^ 2 ≤
      (16 : ℝ) * ((N : ℝ) - 1) * Real.sqrt ((N : ℝ) - 1) * M.worstCost (fun _ => 1) := by
    linarith
  have h4 := MeasuredUnitaryLowerBound.Adaptive.sqrt_le_of_half hN h3
  linarith

end
end MeasuredUnitaryLowerBound.OperatorNorm
