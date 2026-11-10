import MeasuredUnitaryLowerBound.OperatorNorm.Notion
import AdaptiveHamiltonianLowerBound.Readout
import DeferredMeasurementLowerBounds.Corollaries.UnitaryReadout
import LinearSystemLowerBound.Weight.PartialTrace

set_option autoImplicit false

/-!
# Operator-norm implementations are sharply trace-distance accurate

Eq. `hs:eq:unitaryerror` of the manuscript for measured algorithms (purification and deferred
measurement, proof of Lemma `hsl:lem:precision`). A measured algorithm that implements `U` within
operator-norm error `ε` (`NormImplements`, `ε² ≤ 2`) succeeds with probability one on every encoded
unit input `J ψ`, and its output, records discarded and read through the isometry `e`, is within
trace distance `ε √(1 - ε²/4)` of `U ψ` whenever `‖U ψ‖ ≤ 1` (`densityAccurate_of_normImplements`).
The output correlation of a readout effect is the expectation of the record-wise lifted effect in
the read dilation (`corr_outObs_sum_pure`), the target's is that of `U ⊗ γ`
(`inner_garbageTensor_lift`, through the product-vector expectation
`⟪Φ, (Mo ⊗ 1) Φ⟫ = ‖g‖² ⟪v, Mo v⟫` of `inner_tensor_liftObs`), and `abs_re_inner_sub_le_sharp`
compares the two vectors; the read dilation is a unit vector because the trace of the output is the
success probability (`DeferredMeasurementLowerBounds.Corollaries.corr_one_successDensity`).
-/

namespace MeasuredUnitaryLowerBound.OperatorNorm

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.Readout ContinuousLinearMap
open DeferredMeasurementLowerBounds.Model
open AdaptiveHamiltonianLowerBound (DensityAccurate)
open scoped InnerProduct InnerProductSpace

variable {S G E : Type*} [Fintype S] [DecidableEq S]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace G] in
/-- On a product vector `Φ_i = v_i g`, `⟪Φ, (Mo ⊗ 1) Φ⟫ = ‖g‖² ⟪v, Mo v⟫` (the coordinates of
`Mo` from `LinearSystemLowerBound.apply_eq_sum_entry`). -/
theorem inner_tensor_liftObs (Mo : EuclideanSpace ℂ S →L[ℂ] EuclideanSpace ℂ S)
    (v : EuclideanSpace ℂ S) (g : G) (Φ : SysGarb S G) (hΦ : ∀ i, Φ i = v i • g) :
    ⟪Φ, liftObs Mo Φ⟫_ℂ = ((‖g‖ ^ 2 : ℝ) : ℂ) * ⟪v, Mo v⟫_ℂ := by
  have h1 : ⟪Φ, liftObs Mo Φ⟫_ℂ = ∑ i, ⟪Φ i, liftObs Mo Φ i⟫_ℂ := PiLp.inner_apply _ _
  have h2 : ⟪v, Mo v⟫_ℂ = ∑ i, ⟪v i, Mo v i⟫_ℂ := PiLp.inner_apply _ _
  rw [h1, h2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hg : ⟪g, g⟫_ℂ = ((‖g‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_pow]
    exact inner_self_eq_norm_sq_to_K g
  rw [liftObs_apply, LinearSystemLowerBound.apply_eq_sum_entry Mo v i]
  simp only [LinearSystemLowerBound.entry]
  simp only [hΦ, smul_smul, inner_smul_left, inner_sum, inner_smul_right, RCLike.inner_apply, hg]
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i' _ => ?_
  ring

/-- **The output correlation in the read dilation**: for a finite Kraus family `A`, the
correlation of the readout effect `outObs e Mo` with `∑_r |A_r ψ⟩⟨A_r ψ|` is the expectation of
the record-wise lift `Joint.fiber (fun _ => liftObs Mo)` in the read dilation. -/
theorem corr_outObs_sum_pure [FiniteDimensional ℂ E] {R : Type*} [Fintype R]
    (e : E →L[ℂ] SysGarb S G) (A : R → EuclideanSpace ℂ S →L[ℂ] E)
    (Mo : EuclideanSpace ℂ S →L[ℂ] EuclideanSpace ℂ S) (ψ : EuclideanSpace ℂ S) :
    LinearSystemLowerBound.corr (outObs e Mo) (∑ r, ODEMixedOutput.pureOperator (A r ψ)) =
      (⟪readKraus e A ψ,
        Joint.fiber (fun _ : R => liftObs Mo) (readKraus e A ψ)⟫_ℂ).re := by
  rw [LinearSystemLowerBound.corr_sum, PiLp.inner_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [LinearSystemLowerBound.corr_pure, Joint.fiber_apply, readKraus_apply, outObs,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    ContinuousLinearMap.comp_apply]

omit [CompleteSpace G] in
/-- **The expectation in the target**: `⟪(U ⊗ γ) ψ, (Mo ⊗ 1) (U ⊗ γ) ψ⟫ = ‖γ‖² ⟪U ψ, Mo U ψ⟫`. -/
theorem inner_garbageTensor_lift {R : Type*} [Fintype R]
    (U : EuclideanSpace ℂ S →L[ℂ] EuclideanSpace ℂ S) (γ : Joint R G)
    (Mo : EuclideanSpace ℂ S →L[ℂ] EuclideanSpace ℂ S) (ψ : EuclideanSpace ℂ S) :
    ⟪garbageTensor U γ ψ, Joint.fiber (fun _ : R => liftObs Mo) (garbageTensor U γ ψ)⟫_ℂ =
      ((‖γ‖ ^ 2 : ℝ) : ℂ) * ⟪U ψ, Mo (U ψ)⟫_ℂ := by
  rw [PiLp.inner_apply, PiLp.norm_sq_eq_of_L2, Complex.ofReal_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Joint.fiber_apply]
  exact inner_tensor_liftObs Mo (U ψ) (γ r) _ fun i => garbageTensor_apply U γ ψ r i

/-- The record-wise lift of a self-adjoint contraction is a self-adjoint contraction. -/
theorem fiber_liftObs_selfAdjoint {R : Type*} [Fintype R]
    {Mo : EuclideanSpace ℂ S →L[ℂ] EuclideanSpace ℂ S} (hM : IsSelfAdjoint Mo) (hM1 : ‖Mo‖ ≤ 1) :
    IsSelfAdjoint (Joint.fiber (fun _ : R => (liftObs Mo : SysGarb S G →L[ℂ] SysGarb S G))) ∧
      ‖Joint.fiber (fun _ : R => (liftObs Mo : SysGarb S G →L[ℂ] SysGarb S G))‖ ≤ 1 := by
  refine ⟨?_, Joint.norm_fiber_le _ zero_le_one fun _ => (norm_liftObs_le Mo).trans hM1⟩
  rw [IsSelfAdjoint, Joint.star_fiber]
  congr 1
  funext _
  exact (isSelfAdjoint_liftObs hM).star_eq

variable {K X L : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- **Operator-norm error gives sharp per-input trace distance** for measured algorithms. If
`M` implements `U` on the instance `x` within operator-norm error `ε` (`ε² ≤ 2`), then on every
encoded unit input `J ψ` with `‖U ψ‖ ≤ 1` it succeeds with probability one and its conditional
output, read through the isometry `e`, is within trace distance `ε √(1 - ε²/4)` of `U ψ`. -/
theorem densityAccurate_of_normImplements [FiniteDimensional ℂ E] {O : L → X → K →L[ℂ] K}
    (M : Measured O E) (J : EuclideanSpace ℂ S →L[ℂ] K) (e : E →L[ℂ] SysGarb S G)
    (he : e† ∘L e = 1) (x : X) (U : EuclideanSpace ℂ S →L[ℂ] EuclideanSpace ℂ S) {ε : ℝ}
    (hε : ε ^ 2 ≤ 2) (h : NormImplements M J e x U ε) {ψ : EuclideanSpace ℂ S} (hψ : ‖ψ‖ = 1)
    (hUψ : ‖U ψ‖ ≤ 1) :
    M.successMass x (J ψ) = 1 ∧
      DensityAccurate e (M.conditionalDensity x (J ψ)) (U ψ) (ε * Real.sqrt (1 - ε ^ 2 / 4)) := by
  obtain ⟨R, hR, A, γ, hγ, hdens, hmass, hnorm⟩ := h
  have hm : M.successMass x (J ψ) = 1 := by rw [hmass, hψ, one_pow]
  refine ⟨hm, ?_⟩
  have hcond : M.conditionalDensity x (J ψ) = ∑ r, ODEMixedOutput.pureOperator (A r ψ) := by
    rw [Measured.conditionalDensity, hm, hdens]
    simp
  have hb : ‖garbageTensor U γ ψ‖ ≤ 1 := by
    rw [norm_garbageTensor_apply, hγ, mul_one]
    exact hUψ
  have ha : ‖readKraus e A ψ‖ = 1 := by
    have h1 := DeferredMeasurementLowerBounds.Corollaries.corr_one_successDensity M x (J ψ)
    rw [hdens, hm, LinearSystemLowerBound.corr_sum] at h1
    have h3 : ∀ r, LinearSystemLowerBound.corr 1 (ODEMixedOutput.pureOperator (A r ψ)) =
        ‖A r ψ‖ ^ 2 := fun r => by
      rw [LinearSystemLowerBound.corr_pure]
      exact inner_self_eq_norm_sq (𝕜 := ℂ) (A r ψ)
    simp only [h3] at h1
    have h2 := norm_readKraus_apply_sq e he A ψ
    rw [h1] at h2
    have h0 := norm_nonneg (readKraus e A ψ)
    nlinarith
  have hab : ‖readKraus e A ψ - garbageTensor U γ ψ‖ ≤ ε := by
    calc ‖readKraus e A ψ - garbageTensor U γ ψ‖
        = ‖(readKraus e A - garbageTensor U γ) ψ‖ := by rw [sub_apply]
      _ ≤ ‖readKraus e A - garbageTensor U γ‖ * ‖ψ‖ := le_opNorm _ _
      _ ≤ ε := by rw [hψ, mul_one]; exact hnorm
  intro Mo hM hM1
  obtain ⟨hF, hF1⟩ := fiber_liftObs_selfAdjoint (R := R) (G := G) hM hM1
  rw [hcond, corr_outObs_sum_pure]
  have hb' : (⟪U ψ, Mo (U ψ)⟫_ℂ).re = (⟪garbageTensor U γ ψ,
      Joint.fiber (fun _ : R => liftObs Mo) (garbageTensor U γ ψ)⟫_ℂ).re := by
    rw [inner_garbageTensor_lift, hγ]
    simp
  rw [hb']
  exact abs_re_inner_sub_le_sharp _ hF hF1 ha.le hb hab hε

end
end MeasuredUnitaryLowerBound.OperatorNorm
