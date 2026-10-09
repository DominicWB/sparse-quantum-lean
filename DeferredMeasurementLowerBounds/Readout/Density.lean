import AdaptiveHamiltonianLowerBound.Readout
import SparseLowerBounds.Adaptive.Access
import ODELowerBoundExtensions.Release.Registers

set_option autoImplicit false

/-!
# Readouts with a classical record register

The deferred program of a measured algorithm outputs the vector `a : Joint J E` of decoded
branch outputs indexed by the output records `J`; the records are part of the garbage. A readout
`e : E → SysGarb S G` of the measured algorithm becomes the readout
`liftReadout J e : Joint J E → SysGarb S (Joint J G)` of the deferred program: system `S`,
garbage `G ⊗ ℂ^J` (system and record registers in `Type`, as for the package's register
exchange). It is an isometry when `e` is (`liftReadout_isometry`).

Every system observable has the same expectation on the pure output `|a⟩⟨a|` read through
`liftReadout J e` as on the mixture `Σ_j |a_j⟩⟨a_j|` read through `e`
(`trace_outObs_liftReadout`): discarding the record register is the partial trace. Hence the
observable form of trace distance transfers (`densityAccurate_liftReadout`), with any common
normalisation.
-/

namespace DeferredMeasurementLowerBounds.Readout

noncomputable section
open scoped BigOperators InnerProductSpace InnerProduct
open SparseHamiltonian ContinuousLinearMap SparseLowerBounds SparseLowerBounds.Readout
open AdaptiveHamiltonianLowerBound (DensityAccurate)

variable {S J : Type} {G E : Type*} [Fintype S] [DecidableEq S] [Fintype J]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- **The readout of the deferred output**: the record register joins the garbage (the register
exchange `ODELowerBoundExtensions.Release.jointSwap` after the record-wise readout). -/
def liftReadout (J : Type) [Fintype J] (e : E →L[ℂ] SysGarb S G) :
    Joint J E →L[ℂ] SysGarb S (Joint J G) :=
  (ODELowerBoundExtensions.Release.jointSwap J S G).toContinuousLinearEquiv.toContinuousLinearMap
    ∘L Adaptive.Access.jointMap J e

omit [DecidableEq S] [CompleteSpace G] [CompleteSpace E] in
/-- Coordinates of the lifted readout. -/
theorem liftReadout_apply (e : E →L[ℂ] SysGarb S G) (a : Joint J E) (s : S) (j : J) :
    liftReadout J e a s j = e (a j) s := rfl

omit [DecidableEq S] [CompleteSpace E] in
/-- The register exchange is an isometry: `U† U = 1`. -/
theorem adjoint_comp_jointSwap :
    ((ODELowerBoundExtensions.Release.jointSwap J S
        G).toContinuousLinearEquiv.toContinuousLinearMap)†
        ∘L (ODELowerBoundExtensions.Release.jointSwap J S
          G).toContinuousLinearEquiv.toContinuousLinearMap =
      1 :=
  (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).mp fun x =>
    LinearIsometryEquiv.norm_map _ x

omit [DecidableEq S] in
/-- The lifted readout of an isometry is an isometry. -/
theorem liftReadout_isometry {e : E →L[ℂ] SysGarb S G} (he : e† ∘L e = 1) :
    (liftReadout J e)† ∘L liftReadout J e = 1 := by
  rw [liftReadout, adjoint_comp]
  refine ContinuousLinearMap.ext fun x => ?_
  simp only [ContinuousLinearMap.comp_apply]
  rw [← ContinuousLinearMap.comp_apply _
      (ODELowerBoundExtensions.Release.jointSwap J S
        G).toContinuousLinearEquiv.toContinuousLinearMap,
    adjoint_comp_jointSwap, one_apply_eq_self, ← ContinuousLinearMap.comp_apply,
    Adaptive.Access.jointMap_isometry J e he]

omit [Fintype J] [CompleteSpace E] in
/-- The expectation of an output observable on a pure output. -/
theorem trace_outObs_pure {K G' : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] [FiniteDimensional ℂ K] [NormedAddCommGroup G'] [InnerProductSpace ℂ G']
    [CompleteSpace G'] (f : K →L[ℂ] SysGarb S G')
    (M : EuclideanSpace ℂ S →L[ℂ] EuclideanSpace ℂ S) (v : K) :
    LinearMap.trace ℂ K ((outObs f M ∘L ODEMixedOutput.pureOperator v : K →L[ℂ] K) : K →ₗ[ℂ] K) =
      ⟪f v, liftObs M (f v)⟫_ℂ := by
  rw [ODEMixedOutput.pureOperator, InnerProductSpace.comp_rankOne,
    InnerProductSpace.trace_rankOne, outObs, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]

omit [DecidableEq S] [CompleteSpace G] [CompleteSpace E] in
/-- The reduced density of the lifted readout is the sum of the record-wise reduced densities. -/
theorem reducedDensity_liftReadout (e : E →L[ℂ] SysGarb S G) (a : Joint J E) :
    reducedDensity (liftReadout J e a) = ∑ j, reducedDensity (e (a j)) := by
  ext s s'
  rw [reducedDensity, Matrix.of_apply, Matrix.sum_apply, PiLp.inner_apply]
  exact Finset.sum_congr rfl fun j _ => rfl

/-- **Discarding the records**: the expectation of `M ⊗ 1` on `|a⟩⟨a|` read through the lifted
readout is the sum of the expectations on the record-wise outputs. -/
theorem trace_outObs_liftReadout [FiniteDimensional ℂ E] (e : E →L[ℂ] SysGarb S G)
    (M : EuclideanSpace ℂ S →L[ℂ] EuclideanSpace ℂ S) (a : Joint J E) :
    LinearMap.trace ℂ (Joint J E)
        ((outObs (liftReadout J e) M ∘L ODEMixedOutput.pureOperator a :
          Joint J E →L[ℂ] Joint J E) : Joint J E →ₗ[ℂ] Joint J E) =
      ∑ j, LinearMap.trace ℂ E
        ((outObs e M ∘L ODEMixedOutput.pureOperator (a j) : E →L[ℂ] E) : E →ₗ[ℂ] E) := by
  simp_rw [trace_outObs_pure, inner_liftObs, reducedDensity_liftReadout, Matrix.mul_sum,
    Matrix.trace_sum]

/-- **Accuracy transfers to the deferred output**: if the record-discarded output, with any
normalisation `c`, is `ε`-accurate through `e`, then the pure deferred output with the same
normalisation is `ε`-accurate through the lifted readout. -/
theorem densityAccurate_liftReadout [FiniteDimensional ℂ E] (e : E →L[ℂ] SysGarb S G)
    (a : Joint J E) (c : ℂ) (ψ : EuclideanSpace ℂ S) (ε : ℝ)
    (h : DensityAccurate e (c • ∑ j, ODEMixedOutput.pureOperator (a j)) ψ ε) :
    DensityAccurate (liftReadout J e) (c • ODEMixedOutput.pureOperator a) ψ ε := by
  intro M hM hM1
  have hcorr : LinearSystemLowerBound.corr (outObs (liftReadout J e) M)
      (c • ODEMixedOutput.pureOperator a) =
      LinearSystemLowerBound.corr (outObs e M) (c • ∑ j, ODEMixedOutput.pureOperator (a j)) := by
    rw [LinearSystemLowerBound.corr, LinearSystemLowerBound.corr, comp_smul, comp_smul,
      toLinearMap_smul, toLinearMap_smul, map_smul, map_smul, trace_outObs_liftReadout,
      comp_finsetSum, toLinearMap_sum, map_sum]
  rw [hcorr]
  exact h M hM hM1

end

end DeferredMeasurementLowerBounds.Readout
