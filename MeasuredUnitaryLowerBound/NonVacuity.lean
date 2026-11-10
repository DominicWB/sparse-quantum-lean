import MeasuredUnitaryLowerBound.Endpoint.Calls
import AdaptiveUnitaryLowerBound.NonVacuity

set_option autoImplicit false

/-!
# Non-vacuity of the endpoint bounds

The released constant-error circuit of `SparseHamiltonian.UnitaryImplementation.implementation`
(the upper half of Corollary `hs:cor:unitary` of the manuscript) has
operator-norm error `1/4`, hence output within trace distance `1/4`, and so `1/2`, of the
target: the endpoint of the error range `0 < ε ≤ 1/2`. It meets every hypothesis of the
endpoint bounds in each algorithm class of this library and makes at most
`queryConstant · √N` entry calls, so the endpoint bounds hold in one oracle model together with
the matching upper bound.

* `densityAccurate_mono`: trace-distance accuracy is monotone in the error.
* `released_tree_half`: the released circuit, run once as an adaptive protocol
  (`AdaptiveUnitaryLowerBound.NonVacuity.released_tree`), for `Adaptive.unheralded_tree_half`
  and `Adaptive.heralded_tree_half`.
* `released_calls_tree_half`: the same over the four call forms on a clean control qubit
  (`AdaptiveUnitaryLowerBound.NonVacuity.released_calls`), for
  `Adaptive.unheralded_calls_tree_half` and `Adaptive.heralded_calls_tree_half`.
* `released_measured_half`: the released circuit followed by the trivial output as a measured
  algorithm, for `Deferred.implementation_count_ge_measured_half`.
* `released_measured_calls_half`: the same over the four call forms, for
  `Calls.implementation_count_ge_measured_calls_half`.
-/

namespace MeasuredUnitaryLowerBound.NonVacuity

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.Readout
open SparseLinearSystems.Protocol ContinuousLinearMap
open AdaptiveHamiltonianLowerBound (DensityAccurate)
open UnitaryImplementationExtensions.SearchFamily
open AdaptiveUnitaryLowerBound.NonVacuity (Phys)
open DeferredMeasurementLowerBounds.Model
open scoped InnerProduct InnerProductSpace
set_option synthInstance.maxSize 8192

/-- **Accuracy is monotone in the error**: an output within trace distance `ε` of a target is
within any larger trace distance `ε'`. -/
theorem densityAccurate_mono {S E G : Type*} [Fintype S] [DecidableEq S]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {e : E →L[ℂ] SysGarb S G} {ρ : E →L[ℂ] E} {ψ : EuclideanSpace ℂ S} {ε ε' : ℝ}
    (h : DensityAccurate e ρ ψ ε) (hε : ε ≤ ε') : DensityAccurate e ρ ψ ε' := by
  intro M hM hM1
  exact (h M hM hM1).trans (by linarith)

/-- **The released circuit meets the endpoint hypotheses.** For `N ≥ 2` there is an adaptive
protocol over the released entry oracle of the search family (one run of the released
constant-error circuit), with an isometric readout, success probability one and output within
trace distance `1/2` of `U_m |0⟩` on every instance, for which both endpoint bounds hold and
which makes at most `queryConstant · √N` entry calls. -/
theorem released_tree_half {N : ℕ} [NeZero N] (hN : 2 ≤ N) :
    ∃ (γ : ℝ) (T : Tree (AdaptiveUnitaryLowerBound.Entry.entryOracles N γ 1 (Real.pi / 2) (1 / 4))
      ℂ (Phys N γ)) (e : Phys N γ →L[ℂ] SysGarb (Fin N) (Phys N γ)),
      e† ∘L e = 1 ∧ (∀ m, T.successMass m = 1) ∧
      (∀ m, DensityAccurate e (T.conditionalDensity m)
        (SparseStateOverlap.matrixOperator (searchMatrix N m) (EuclideanSpace.single 0 1))
          (1 / 2)) ∧
      ((N : ℝ) - 2) ^ 2 ≤
        16 * ((N : ℝ) - 1) * Real.sqrt ((N : ℝ) - 1) * T.worstCost (fun _ => 1) ∧
      ((N : ℝ) - 2) ^ 2 ≤
        36 * ((N : ℝ) - 1) * Real.sqrt ((N : ℝ) - 1) * T.worstCost (fun _ => 1) ∧
      ((T.worstCost (fun _ => 1) : ℕ) : ℝ) ≤
        UnitaryImplementation.queryConstant * Real.sqrt (N : ℝ) := by
  obtain ⟨γ, T, e, he, hs, hacc, -, -, hcount⟩ :=
    AdaptiveUnitaryLowerBound.NonVacuity.released_tree hN
  have hacc' : ∀ m, DensityAccurate e (T.conditionalDensity m)
      (SparseStateOverlap.matrixOperator (searchMatrix N m) (EuclideanSpace.single 0 1))
        (1 / 2) := fun m => densityAccurate_mono (hacc m) (by norm_num)
  exact ⟨γ, T, e, he, hs, hacc',
    Adaptive.unheralded_tree_half hN γ 1 (Real.pi / 2) (1 / 4) T e he hs hacc',
    Adaptive.heralded_tree_half hN γ 1 (Real.pi / 2) (1 / 4) T e he
      (fun m => by rw [hs m]; norm_num) hacc', hcount⟩

set_option maxHeartbeats 1600000 in
/-- **The released circuit over the call forms meets the endpoint hypotheses.** For `N ≥ 2`
there is an adaptive protocol over the four call forms of the released entry oracle of the
search family (one run of the released constant-error circuit on a clean control qubit), with an
isometric readout, success probability one and output within trace distance `1/2` of
`U_m |0⟩` on every instance, for which both endpoint bounds over the call forms hold and which
makes at most `queryConstant · √N` calls. -/
theorem released_calls_tree_half {N : ℕ} [NeZero N] (hN : 2 ≤ N) :
    ∃ (γ : ℝ) (T : Tree (AdaptiveODELowerBound.Access.callFamily
        (AdaptiveUnitaryLowerBound.Entry.entryOracles N γ 1 (Real.pi / 2) (1 / 4)))
        ℂ (Joint Bool (Phys N γ)))
      (e : Joint Bool (Phys N γ) →L[ℂ] SysGarb (Fin N) (Joint Bool (Phys N γ))),
      e† ∘L e = 1 ∧ (∀ m, T.successMass m = 1) ∧
      (∀ m, DensityAccurate e (T.conditionalDensity m)
        (SparseStateOverlap.matrixOperator (searchMatrix N m) (EuclideanSpace.single 0 1))
          (1 / 2)) ∧
      ((N : ℝ) - 2) ^ 2 ≤
        16 * ((N : ℝ) - 1) * Real.sqrt ((N : ℝ) - 1) * T.worstCost (fun _ => 1) ∧
      ((N : ℝ) - 2) ^ 2 ≤
        36 * ((N : ℝ) - 1) * Real.sqrt ((N : ℝ) - 1) * T.worstCost (fun _ => 1) ∧
      ((T.worstCost (fun _ => 1) : ℕ) : ℝ) ≤
        UnitaryImplementation.queryConstant * Real.sqrt (N : ℝ) := by
  obtain ⟨γ, p, J, hJ, hErr, hcost⟩ :=
    AdaptiveUnitaryLowerBound.NonVacuity.released_calls (N := N)
  have hU := AdaptiveODELowerBound.Access.callFamily_unitary
    (AdaptiveUnitaryLowerBound.Entry.entryOracles_unitary N γ 1 (Real.pi / 2) (1 / 4))
  obtain ⟨hφ, he, hs, hacc, hT⟩ :=
    AdaptiveUnitaryLowerBound.NonVacuity.single_hyps hU p J hJ hErr
  have hacc' : ∀ m, DensityAccurate (Hamiltonian.endpointReadout J 0)
      ((AdaptiveHamiltonianLowerBound.Single.tree ℂ p _ hφ).conditionalDensity m)
      (SparseStateOverlap.matrixOperator (searchMatrix N m) (EuclideanSpace.single 0 1))
        (1 / 2) := fun m => densityAccurate_mono (hacc m) (by norm_num)
  have hc : p.cost (fun _ => 1) = p.count := by
    rw [MultiOracleCircuit.Program.cost_const, mul_one]
  refine ⟨γ, AdaptiveHamiltonianLowerBound.Single.tree ℂ p _ hφ, Hamiltonian.endpointReadout J 0,
    he, hs, hacc',
    Adaptive.unheralded_calls_tree_half hN γ 1 (Real.pi / 2) (1 / 4) _ _ he hs hacc',
    Adaptive.heralded_calls_tree_half hN γ 1 (Real.pi / 2) (1 / 4) _ _ he
      (fun m => by rw [hs m]; norm_num) hacc', ?_⟩
  rw [hT, ← hc]
  exact hcost

/-- **The released circuit as a measured algorithm meets the endpoint hypotheses.** For
`N ≥ 2` the released constant-error circuit followed by the trivial output is a measured
algorithm over the released entry oracle of the search family that, on an isometric encoding
`J` and with an isometric readout `e`, succeeds with probability one and has output within
trace distance `1/2` of `U_m ψ` for every instance `m` and unit input `ψ`; it obeys the bound
of `Deferred.implementation_count_ge_measured_half` and makes at most `queryConstant · √N`
entry calls. -/
theorem released_measured_half {N : ℕ} [NeZero N] (hN : 2 ≤ N) :
    ∃ (γ : ℝ) (M : DeferredMeasurementLowerBounds.Model.Measured (fun (_ : Unit) (m : Fin N) =>
        UnitaryEntryOracle.oracle (searchData N) γ 1 (Real.pi / 2) (1 / 4) m) (Phys N γ))
      (J : EuclideanSpace ℂ (Fin N) →L[ℂ] Phys N γ)
      (e : Phys N γ →L[ℂ] SysGarb (Fin N) (Phys N γ)),
      J† ∘L J = 1 ∧ e† ∘L e = 1 ∧
      (∀ m (ψ : EuclideanSpace ℂ (Fin N)), ‖ψ‖ = 1 → M.successMass m (J ψ) = 1 ∧
        DensityAccurate e (M.conditionalDensity m (J ψ))
          (SparseStateOverlap.matrixOperator (searchMatrix N m) ψ) (1 / 2)) ∧
      ((N : ℝ) - 2) ^ 2 ≤
        16 * ((N : ℝ) - 1) * Real.sqrt ((N : ℝ) - 1) * M.worstCost (fun _ => 1) ∧
      ((M.worstCost (fun _ => 1) : ℕ) : ℝ) ≤
        UnitaryImplementation.queryConstant * Real.sqrt (N : ℝ) := by
  obtain ⟨γ, q, J, hJ, hErr, hcount⟩ := AdaptiveUnitaryLowerBound.NonVacuity.released (N := N)
  have hO := AdaptiveUnitaryLowerBound.Entry.entryOracles_unitary N γ 1 (Real.pi / 2) (1 / 4)
  have h1 : (1 : Phys N γ →L[ℂ] Phys N γ)† = 1 := by
    rw [← ContinuousLinearMap.star_eq_adjoint, star_one]
  have hout : (1 : Phys N γ →L[ℂ] Phys N γ)† ∘L (1 : Phys N γ →L[ℂ] Phys N γ) = 1 := by
    rw [h1]
    rfl
  let M : DeferredMeasurementLowerBounds.Model.Measured (fun (_ : Unit) (m : Fin N) =>
      UnitaryEntryOracle.oracle (searchData N) γ 1 (Real.pi / 2) (1 / 4) m) (Phys N γ) :=
    ofProgram q (.output 1 hout)
  have hcost : M.worstCost (fun _ => 1) = q.count := by
    simp only [M, worstCost_ofProgram, worstCost_output, MultiOracleCircuit.Program.cost_const,
      mul_one, add_zero]
  have he := Hamiltonian.endpointReadout_isometry J hJ 0
  have himpl : ∀ m (ψ : EuclideanSpace ℂ (Fin N)), ‖ψ‖ = 1 → M.successMass m (J ψ) = 1 ∧
      DensityAccurate (Hamiltonian.endpointReadout J 0) (M.conditionalDensity m (J ψ))
        (SparseStateOverlap.matrixOperator (searchMatrix N m) ψ) (1 / 2) := by
    intro m ψ hψ
    have hU := q.eval_unitary hO m
    have hΦ : ‖q.eval m (J ψ)‖ = 1 := by
      rw [PositiveAdversary.norm_map_of_isUnitary hU,
        (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).mpr hJ, hψ]
    have hmass : M.successMass m (J ψ) = 1 := by
      simp only [M, successMass_ofProgram, successMass_output, h1, one_apply_eq_self, hΦ, one_pow]
    refine ⟨hmass, densityAccurate_mono ?_ (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2)⟩
    have hdens : M.conditionalDensity m (J ψ) =
        ODEMixedOutput.pureOperator (q.eval m (J ψ)) := by
      rw [Measured.conditionalDensity, hmass]
      simp only [M, successDensity_ofProgram, successDensity_output, h1, one_apply_eq_self,
        inv_one, Complex.ofReal_one, one_smul]
    rw [hdens, AdaptiveHamiltonianLowerBound.densityAccurate_pure_iff]
    exact Hamiltonian.accurate_of_endpoint J hJ 0 (q.eval m) hU.norm_le_one _ hψ.le
      (by rw [PositiveAdversary.norm_map_of_isUnitary (searchMatrix_unitary N m), hψ]) (hErr m)
  refine ⟨γ, M, J, Hamiltonian.endpointReadout J 0, hJ, he, himpl,
    Deferred.implementation_count_ge_measured_half hN γ 1 (Real.pi / 2) (1 / 4) M J hJ _ he himpl,
    ?_⟩
  rw [hcost]
  exact hcount

set_option maxHeartbeats 1600000 in
/-- **The released circuit over the call forms as a measured algorithm meets the endpoint
hypotheses.** For `N ≥ 2` the released constant-error circuit over the four call forms of the
released entry oracle (on a clean control qubit), followed by the trivial output, is a measured
algorithm that, on an isometric encoding `J` into the controlled workspace and with an isometric
readout `e`, succeeds with probability one and has output within trace distance `1/2` of
`U_m ψ` for every instance `m` and unit input `ψ`; it obeys the bound of
`Calls.implementation_count_ge_measured_calls_half` and makes at most `queryConstant · √N`
calls. -/
theorem released_measured_calls_half {N : ℕ} [NeZero N] (hN : 2 ≤ N) :
    ∃ (γ : ℝ) (M : DeferredMeasurementLowerBounds.Model.Measured
        (AdaptiveODELowerBound.Access.callFamily
          (AdaptiveUnitaryLowerBound.Entry.entryOracles N γ 1 (Real.pi / 2) (1 / 4)))
        (Joint Bool (Phys N γ)))
      (J : EuclideanSpace ℂ (Fin N) →L[ℂ] Joint Bool (Phys N γ))
      (e : Joint Bool (Phys N γ) →L[ℂ] SysGarb (Fin N) (Joint Bool (Phys N γ))),
      J† ∘L J = 1 ∧ e† ∘L e = 1 ∧
      (∀ m (ψ : EuclideanSpace ℂ (Fin N)), ‖ψ‖ = 1 → M.successMass m (J ψ) = 1 ∧
        DensityAccurate e (M.conditionalDensity m (J ψ))
          (SparseStateOverlap.matrixOperator (searchMatrix N m) ψ) (1 / 2)) ∧
      ((N : ℝ) - 2) ^ 2 ≤
        128 * ((N : ℝ) - 1) * Real.sqrt ((N : ℝ) - 1) * M.worstCost (fun _ => 1) ∧
      ((M.worstCost (fun _ => 1) : ℕ) : ℝ) ≤
        UnitaryImplementation.queryConstant * Real.sqrt (N : ℝ) := by
  obtain ⟨γ, q, J, hJ, hErr, hcount⟩ :=
    AdaptiveUnitaryLowerBound.NonVacuity.released_calls (N := N)
  have hO := AdaptiveODELowerBound.Access.callFamily_unitary
    (AdaptiveUnitaryLowerBound.Entry.entryOracles_unitary N γ 1 (Real.pi / 2) (1 / 4))
  have h1 : (1 : Joint Bool (Phys N γ) →L[ℂ] Joint Bool (Phys N γ))† = 1 := by
    rw [← ContinuousLinearMap.star_eq_adjoint, star_one]
  have hout : (1 : Joint Bool (Phys N γ) →L[ℂ] Joint Bool (Phys N γ))† ∘L
      (1 : Joint Bool (Phys N γ) →L[ℂ] Joint Bool (Phys N γ)) = 1 := by
    rw [h1]
    rfl
  let M : DeferredMeasurementLowerBounds.Model.Measured
      (AdaptiveODELowerBound.Access.callFamily
        (AdaptiveUnitaryLowerBound.Entry.entryOracles N γ 1 (Real.pi / 2) (1 / 4)))
      (Joint Bool (Phys N γ)) :=
    ofProgram q (.output 1 hout)
  have hcost : M.worstCost (fun _ => 1) = q.cost (fun _ => 1) := by
    simp only [M, worstCost_ofProgram, worstCost_output, add_zero]
  have he := Hamiltonian.endpointReadout_isometry J hJ 0
  have himpl : ∀ m (ψ : EuclideanSpace ℂ (Fin N)), ‖ψ‖ = 1 → M.successMass m (J ψ) = 1 ∧
      DensityAccurate (Hamiltonian.endpointReadout J 0) (M.conditionalDensity m (J ψ))
        (SparseStateOverlap.matrixOperator (searchMatrix N m) ψ) (1 / 2) := by
    intro m ψ hψ
    have hU := q.eval_unitary hO m
    have hΦ : ‖q.eval m (J ψ)‖ = 1 := by
      rw [PositiveAdversary.norm_map_of_isUnitary hU,
        (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).mpr hJ, hψ]
    have hmass : M.successMass m (J ψ) = 1 := by
      simp only [M, successMass_ofProgram, successMass_output, h1, one_apply_eq_self, hΦ, one_pow]
    refine ⟨hmass, densityAccurate_mono ?_ (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2)⟩
    have hdens : M.conditionalDensity m (J ψ) =
        ODEMixedOutput.pureOperator (q.eval m (J ψ)) := by
      rw [Measured.conditionalDensity, hmass]
      simp only [M, successDensity_ofProgram, successDensity_output, h1, one_apply_eq_self,
        inv_one, Complex.ofReal_one, one_smul]
    rw [hdens, AdaptiveHamiltonianLowerBound.densityAccurate_pure_iff]
    exact Hamiltonian.accurate_of_endpoint J hJ 0 (q.eval m) hU.norm_le_one _ hψ.le
      (by rw [PositiveAdversary.norm_map_of_isUnitary (searchMatrix_unitary N m), hψ]) (hErr m)
  refine ⟨γ, M, J, Hamiltonian.endpointReadout J 0, hJ, he, himpl,
    Calls.implementation_count_ge_measured_calls_half hN γ 1 (Real.pi / 2) (1 / 4) M J hJ _ he
      himpl, ?_⟩
  rw [hcost]
  exact hcount

end
end MeasuredUnitaryLowerBound.NonVacuity
