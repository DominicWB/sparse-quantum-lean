import MeasuredUnitaryLowerBound.OperatorNorm.ProgramBound
import AdaptiveUnitaryLowerBound.NonVacuity
import MeasuredUnitaryLowerBound.OperatorNorm.Deferred

set_option autoImplicit false
set_option synthInstance.maxSize 8192

/-!
# Non-vacuity of the measured operator-norm bounds

Corollary `hs:cor:unitary` of the manuscript: both halves of `Θ(√N)` in one
oracle model. The released constant-error circuit
(`AdaptiveUnitaryLowerBound.NonVacuity.released`, `released_calls`: operator-norm error `1/4`,
at most `queryConstant · √N` entry calls), run and output in full (`runAll`) and read through the
endpoint readout, is a measured algorithm that implements every `U_m` within operator-norm error
`1/4` (`normImplements_runAll`), so the hypotheses of
`implementation_count_ge_measured_norm` and `implementation_count_ge_measured_calls_norm` are
met:

* `released_measured_norm`: over the released entry oracle;
* `released_measured_calls_norm`: over its four call forms.
-/

namespace MeasuredUnitaryLowerBound.OperatorNorm

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.Readout ContinuousLinearMap
open UnitaryImplementationExtensions.SearchFamily
open DeferredMeasurementLowerBounds.Model
open AdaptiveODELowerBound.Access (callFamily)
open AdaptiveUnitaryLowerBound.NonVacuity (Phys)
open scoped InnerProduct InnerProductSpace

/-- **The released circuit meets the measured operator-norm hypotheses.** For `N ≥ 2` there is a
measured algorithm over the released entry oracle of the search family (the released
constant-error circuit, output in full) with an isometric encoding and an isometric readout that
implements every `U_m` within operator-norm error `1/4`, for which the bound of
`implementation_count_ge_measured_norm` holds, and which makes at most `queryConstant · √N`
entry calls. -/
theorem released_measured_norm {N : ℕ} [NeZero N] (hN : 2 ≤ N) :
    ∃ (γ : ℝ) (M : Measured (fun (_ : Unit) (m : Fin N) =>
        UnitaryEntryOracle.oracle (searchData N) γ 1 (Real.pi / 2) (1 / 4) m) (Phys N γ))
      (J : EuclideanSpace ℂ (Fin N) →L[ℂ] Phys N γ)
      (e : Phys N γ →L[ℂ] SysGarb (Fin N) (Phys N γ)),
      J† ∘L J = 1 ∧ e† ∘L e = 1 ∧
      (∀ m, NormImplements M J e m (SparseStateOverlap.matrixOperator (searchMatrix N m))
        (1 / 4)) ∧
      ((N : ℝ) * (1 - 1 / 4 * Real.sqrt (1 - (1 / 4 : ℝ) ^ 2 / 4)) - 1) ^ 2 ≤
        4 * ((N : ℝ) - 1) * Real.sqrt ((N : ℝ) - 1) * M.worstCost (fun _ => 1) ∧
      ((M.worstCost (fun _ => 1) : ℕ) : ℝ) ≤
        UnitaryImplementation.queryConstant * Real.sqrt (N : ℝ) := by
  obtain ⟨γ, q, J, hJ, hErr, hcount⟩ := AdaptiveUnitaryLowerBound.NonVacuity.released (N := N)
  have himpl : ∀ m, NormImplements (runAll q) J (Hamiltonian.endpointReadout J 0) m
      (SparseStateOverlap.matrixOperator (searchMatrix N m)) (1 / 4) := fun m =>
    normImplements_runAll
      (AdaptiveUnitaryLowerBound.Entry.entryOracles_unitary N γ 1 (Real.pi / 2) (1 / 4))
      q J hJ 0 m _ (hErr m)
  refine ⟨γ, runAll q, J, Hamiltonian.endpointReadout J 0, hJ,
    Hamiltonian.endpointReadout_isometry J hJ 0, himpl,
    implementation_count_ge_measured_norm hN γ 1 (Real.pi / 2) (1 / 4) (runAll q) J hJ
      (Hamiltonian.endpointReadout J 0) (Hamiltonian.endpointReadout_isometry J hJ 0)
      (by norm_num) himpl, ?_⟩
  rw [worstCost_runAll, MultiOracleCircuit.Program.cost_const, mul_one]
  exact hcount

/-- **The released circuit meets the measured operator-norm hypotheses over the call forms.**
For `N ≥ 2` there is a measured algorithm over the four call forms of the released entry oracle
(the released circuit with plain calls, output in full) with an isometric encoding into
`Joint Bool` of the oracle space and an isometric readout that implements every `U_m` within
operator-norm error `1/4`, for which the bound of `implementation_count_ge_measured_calls_norm`
holds, and which makes at most `queryConstant · √N` calls. -/
theorem released_measured_calls_norm {N : ℕ} [NeZero N] (hN : 2 ≤ N) :
    ∃ (γ : ℝ) (M : Measured (callFamily
        (AdaptiveUnitaryLowerBound.Entry.entryOracles N γ 1 (Real.pi / 2) (1 / 4)))
        (Joint Bool (Phys N γ)))
      (J : EuclideanSpace ℂ (Fin N) →L[ℂ] Joint Bool (Phys N γ))
      (e : Joint Bool (Phys N γ) →L[ℂ] SysGarb (Fin N) (Joint Bool (Phys N γ))),
      J† ∘L J = 1 ∧ e† ∘L e = 1 ∧
      (∀ m, NormImplements M J e m (SparseStateOverlap.matrixOperator (searchMatrix N m))
        (1 / 4)) ∧
      ((N : ℝ) * (1 - 1 / 4 * Real.sqrt (1 - (1 / 4 : ℝ) ^ 2 / 4)) - 1) ^ 2 ≤
        32 * ((N : ℝ) - 1) * Real.sqrt ((N : ℝ) - 1) * M.worstCost (fun _ => 1) ∧
      ((M.worstCost (fun _ => 1) : ℕ) : ℝ) ≤
        UnitaryImplementation.queryConstant * Real.sqrt (N : ℝ) := by
  obtain ⟨γ, p, J, hJ, hErr, hcount⟩ :=
    AdaptiveUnitaryLowerBound.NonVacuity.released_calls (N := N)
  have hU := AdaptiveODELowerBound.Access.callFamily_unitary
    (AdaptiveUnitaryLowerBound.Entry.entryOracles_unitary N γ 1 (Real.pi / 2) (1 / 4))
  have he := Hamiltonian.endpointReadout_isometry J hJ 0
  have himpl : ∀ m, NormImplements (runAll p) J (Hamiltonian.endpointReadout J 0) m
      (SparseStateOverlap.matrixOperator (searchMatrix N m)) (1 / 4) := fun m =>
    normImplements_runAll hU p J hJ 0 m _ (hErr m)
  have hb := implementation_count_ge_measured_calls_norm hN γ 1 (Real.pi / 2) (1 / 4)
    (runAll p) J hJ _ he (by norm_num) himpl
  have hc : (((runAll p).worstCost (fun _ => 1) : ℕ) : ℝ) ≤
      UnitaryImplementation.queryConstant * Real.sqrt (N : ℝ) := by
    rw [worstCost_runAll]
    exact hcount
  exact ⟨γ, runAll p, J, _, hJ, he, himpl, hb, hc⟩

end
end MeasuredUnitaryLowerBound.OperatorNorm
