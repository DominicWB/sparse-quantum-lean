import SparseODE.ODEJointNative

/-!
# One analytic Cayley system for all coherent LCHS branches

The branch register is included in both public and private Hilbert spaces.
All durations use one global horizon and one moment/filter schedule. The
only circuit premise in the final certificate is a counted implementation
of the joint active clock; every analytic obligation is discharged here.

-/

namespace SparseHamiltonian.ODEJointCayley

noncomputable section
open ContinuousLinearMap OracleCircuit ImprovedCayleyMoments CayleyClockInterface
open scoped BigOperators InnerProduct
set_option maxRecDepth 4096
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 2000000

variable {ι X n Z : Type*} [Fintype ι] [Fintype n] [DecidableEq n] {s : ℕ}

abbrev Public (ι n : Type*) [Fintype ι] [Fintype n] :=
  PiLp 2 (fun _ : ι => EuclideanSpace ℂ n)

abbrev Private (ι n : Type*) [Fintype ι] [Fintype n] :=
  PiLp 2 (fun _ : ι => ODETaggedMoments.PrivateSpace n)

/-- The fixed public/private interface includes the spectator branch. -/
def boundary (D : NativeSparseBlockEncoding.Data X n Z s) :
    Public ι n →L[ℂ] Private ι n :=
  CoherentQuerySchedule.rectangular (fun _ : ι => ODEFixedTaggedMoments.boundary D)

def generator (D : NativeSparseBlockEncoding.Data X n Z s) (x : X)
    (k u : ι → ℝ) (ρ T : ℝ) : Private ι n →L[ℂ] Private ι n :=
  WeightedClock.diagonal (fun i => ODECommonDuration.generator D x
    (ODEMatrixEnergy.lchsHamiltonian (D.matrix x) (k i)) ρ (u i / T))

/-- Full inverse, including zero-duration branches. -/
def inverse (D : NativeSparseBlockEncoding.Data X n Z s) (x : X)
    (k u : ι → ℝ) (ρ T γ : ℝ) : Private ι n →L[ℂ] Private ι n :=
  WeightedClock.diagonal (fun i => ODECommonDuration.inverse D x
    (ODEMatrixEnergy.lchsHamiltonian (D.matrix x) (k i)) ρ γ (u i / T))

/-- The diagonal action is exactly the native SELECT target. -/
def action (D : NativeSparseBlockEncoding.Data X n Z s) (x : X)
    (k u : ι → ℝ) (ρ T γ : ℝ) : Private ι n →L[ℂ] Private ι n :=
  WeightedClock.diagonal (fun i => ODECommonDuration.action D x
    (ODEMatrixEnergy.lchsHamiltonian (D.matrix x) (k i)) ρ γ (u i / T))

theorem action_eq_diagonal (D : NativeSparseBlockEncoding.Data X n Z s) (x : X)
    (k u : ι → ℝ) (ρ T γ : ℝ) :
    action D x k u ρ T γ = WeightedClock.diagonal (fun i =>
      ODEFixedTaggedMoments.action D x
        (ODEMatrixEnergy.lchsHamiltonian (D.matrix x) (k i)) ρ (γ * (u i / T))) := rfl

theorem boundary_isometry (D : NativeSparseBlockEncoding.Data X n Z s) :
    (boundary (ι := ι) D)† ∘L boundary D = 1 :=
  CoherentQuerySchedule.rectangular_isometry _
    (fun _ : ι => ODEFixedTaggedMoments.boundary_isometry D)

theorem generator_adjoint (D : NativeSparseBlockEncoding.Data X n Z s) (x : X)
    (k u : ι → ℝ) (ρ T : ℝ) :
    (generator D x k u ρ T)† = generator D x k u ρ T := by
  rw [generator, WeightedClock.diagonal_adjoint]
  congr 1
  funext i
  exact ODECommonDuration.generator_adjoint D x _ ρ (u i / T)

/-- Scalar rescaling is performed independently on each direct-sum block. -/
theorem scaled_generator (D : NativeSparseBlockEncoding.Data X n Z s) (x : X)
    (k u : ι → ℝ) (ρ T γ : ℝ) :
    scaled (generator D x k u ρ T) γ = WeightedClock.diagonal
      (fun i => scaled (ODECommonDuration.generator D x
        (ODEMatrixEnergy.lchsHamiltonian (D.matrix x) (k i)) ρ (u i / T)) γ) := by
  apply ContinuousLinearMap.ext
  intro v
  apply PiLp.ext
  intro i
  rfl

theorem shifted_generator (D : NativeSparseBlockEncoding.Data X n Z s) (x : X)
    (k u : ι → ℝ) (ρ T γ : ℝ) :
    scaled (generator D x k u ρ T) γ - Complex.I • (1 : Private ι n →L[ℂ] _) =
      WeightedClock.diagonal (fun i => scaled (ODECommonDuration.generator D x
        (ODEMatrixEnergy.lchsHamiltonian (D.matrix x) (k i)) ρ (u i / T)) γ -
          Complex.I • (1 : ODETaggedMoments.PrivateSpace n →L[ℂ] _)) := by
  apply ContinuousLinearMap.ext
  intro v
  apply PiLp.ext
  intro i
  rfl

theorem inverse_right (D : NativeSparseBlockEncoding.Data X n Z s) (x : X)
    (k u : ι → ℝ) (ρ T γ : ℝ) :
    (scaled (generator D x k u ρ T) γ - Complex.I • (1 : Private ι n →L[ℂ] _)) *
      inverse D x k u ρ T γ = 1 := by
  apply ContinuousLinearMap.ext
  intro v
  apply PiLp.ext
  intro i
  exact congrArg (fun f : ODETaggedMoments.PrivateSpace n →L[ℂ]
    ODETaggedMoments.PrivateSpace n => f (v i))
      (ODECommonDuration.inverse_right D x
        (ODEMatrixEnergy.lchsHamiltonian (D.matrix x) (k i)) ρ γ (u i / T))

theorem inverse_left (D : NativeSparseBlockEncoding.Data X n Z s) (x : X)
    (k u : ι → ℝ) (ρ T γ : ℝ) :
    inverse D x k u ρ T γ *
      (scaled (generator D x k u ρ T) γ - Complex.I • (1 : Private ι n →L[ℂ] _)) = 1 := by
  apply ContinuousLinearMap.ext
  intro v
  apply PiLp.ext
  intro i
  exact congrArg (fun f : ODETaggedMoments.PrivateSpace n →L[ℂ]
    ODETaggedMoments.PrivateSpace n => f (v i))
      (ODECommonDuration.inverse_left D x
        (ODEMatrixEnergy.lchsHamiltonian (D.matrix x) (k i)) ρ γ (u i / T))

theorem action_unitary (D : NativeSparseBlockEncoding.Data X n Z s) (x : X)
    (k u : ι → ℝ) (ρ T γ : ℝ) : IsUnitary (action D x k u ρ T γ) :=
  CoherentQuerySchedule.diagonal_unitary _
    (fun i => ODECommonDuration.action_unitary D x _ ρ γ (u i / T))

theorem action_eq_cayley (D : NativeSparseBlockEncoding.Data X n Z s) (x : X)
    (k u : ι → ℝ) (ρ T γ : ℝ) :
    action D x k u ρ T γ = cayleyAction
      (scaled (generator D x k u ρ T) γ) (inverse D x k u ρ T γ) := by
  apply ContinuousLinearMap.ext
  intro v
  apply PiLp.ext
  intro i
  exact congrArg (fun f : ODETaggedMoments.PrivateSpace n →L[ℂ]
    ODETaggedMoments.PrivateSpace n => f (v i))
      (ODECommonDuration.action_eq_cayley D x
        (ODEMatrixEnergy.lchsHamiltonian (D.matrix x) (k i)) ρ γ (u i / T))

/-- Both branch moment bounds hold with no factor for the number of nodes. -/
theorem moment_certificate (D : NativeSparseBlockEncoding.Data X n Z s) (x : X)
    (etaH etaD R T : ℝ) (k u : ι → ℝ)
    (hH : 0 ≤ etaH) (hD : 0 ≤ etaD) (hρ : 0 < etaH + R * etaD)
    (hT : 0 < T) (hk : ∀ i, |k i| ≤ R)
    (hu : ∀ i, 0 ≤ u i) (huT : ∀ i, u i ≤ T)
    (hrH : ∀ i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ etaH ^ 2)
    (hcH : ∀ j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ etaH ^ 2)
    (hrD : ∀ i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ etaD ^ 2)
    (hcD : ∀ j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ etaD ^ 2) :
    ‖generator D x k u (etaH + R * etaD) T‖ ≤ Real.sqrt (2 * (s : ℝ)) ∧
    ‖generator D x k u (etaH + R * etaD) T ∘L boundary D‖ ≤ 1 := by
  have h := ODECoherentMoments.lchs_duration_certificate D x etaH etaD R T k u
    hH hD hρ hT hk hu huT hrH hcH hrD hcD
  exact ⟨h.2.2.1, h.2.2.2.1⟩

/-- The common transducer exponent retains every branch's physical duration. -/
theorem physical_exponent (D : NativeSparseBlockEncoding.Data X n Z s) (x : X)
    (k u : ι → ℝ) (ρ T γ : ℝ) (hρ : ρ ≠ 0) (hT : 0 < T) (hγ : γ ≠ 0) :
    (-Complex.I * (time (2 * (s : ℝ)) (ρ * T) γ : ℂ)) •
      compressed (generator D x k u ρ T) (boundary D) γ =
        WeightedClock.diagonal (fun i => (-Complex.I * (u i : ℂ)) •
          SparseStateOverlap.matrixOperator
            (ODEMatrixEnergy.lchsHamiltonian (D.matrix x) (k i))) :=
  ODECoherentMoments.physical_exponent D x k u ρ T γ hρ hT hγ

variable {Label K : Type*}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- One coherent sharp simulation program, with all analytic promises proved
from the original matrix energies. The remaining active-circuit premise is
explicit and is discharged by the native joint construction. -/
theorem query_certificate
    (D : NativeSparseBlockEncoding.Data X n Z s)
    (etaH etaD R T : ℝ) (k u : ι → ℝ)
    (hH : 0 ≤ etaH) (hDiss : 0 ≤ etaD) (hρ : 0 < etaH + R * etaD)
    (hT : 0 < T) (hk : ∀ i, |k i| ≤ R)
    (hu : ∀ i, 0 ≤ u i) (huT : ∀ i, u i ≤ T)
    (hrH : ∀ x i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ etaH ^ 2)
    (hcH : ∀ x j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ etaH ^ 2)
    (hrD : ∀ x i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ etaD ^ 2)
    (hcD : ∀ x j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ etaD ^ 2)
    (γ ε : ℝ) (hγ : 0 < γ) (hγOne : γ ≤ 1)
    (hε : 0 < ε) (hεOne : ε ≤ 1)
    (hBudget : time (2 * (s : ℝ)) ((etaH + R * etaD) * T) γ * moment γ +
      width (2 * (s : ℝ)) γ * ImprovedPrecisionBudget.circuitLog ε ≤
        12 * ImprovedPrecisionBudget.shape (2 * (s : ℝ)) ((etaH + R * etaD) * T) (ImprovedPrecisionBudget.targetLog ε))
    (O : Label → X → K →L[ℂ] K) (hO : ∀ l x, IsUnitary (O l x))
    (E : SharpClockQuery.EvolutionSpace (P := Public ι n)
      (V := Private ι n)
      (time (2 * (s : ℝ)) ((etaH + R * etaD) * T) γ) (width (2 * (s : ℝ)) γ) (moment γ) ε →L[ℂ] K)
    (hE : E† ∘L E = 1) (q : ℕ)
    (hQuery : ∀ r < 2 * SharpFilterSchedule.degree (width (2 * (s : ℝ)) γ)
      (time (2 * (s : ℝ)) ((etaH + R * etaD) * T) γ * moment γ) (ε / 3),
      LabeledEncodedOracle.ImplementsOn O
        (fun x => SharpLabeledActiveClockQuery.evolutionActiveClock
          (P := Public ι n) (action D x k u (etaH + R * etaD) T γ)
          (time (2 * (s : ℝ)) ((etaH + R * etaD) * T) γ) (width (2 * (s : ℝ)) γ) (moment γ) ε r) E q) :
    ∃ p : MultiOracleCircuit.Program O,
      (p.count : ℝ) ≤ 9216 * (q : ℝ) *
        ImprovedPrecisionBudget.shape (2 * (s : ℝ)) ((etaH + R * etaD) * T) (ImprovedPrecisionBudget.targetLog ε) ∧
      (E ∘L SharpClockQuery.evolutionInput (P := Public ι n)
        (V := Private ι n)
        (time (2 * (s : ℝ)) ((etaH + R * etaD) * T) γ) (width (2 * (s : ℝ)) γ) (moment γ) ε)† ∘L
        (E ∘L SharpClockQuery.evolutionInput
          (time (2 * (s : ℝ)) ((etaH + R * etaD) * T) γ) (width (2 * (s : ℝ)) γ) (moment γ) ε) = 1 ∧
      (E ∘L SharpClockSimulation.evolutionOutput (P := Public ι n)
        (V := Private ι n)
        (time (2 * (s : ℝ)) ((etaH + R * etaD) * T) γ) (width (2 * (s : ℝ)) γ) (moment γ) ε)† ∘L
        (E ∘L SharpClockSimulation.evolutionOutput (P := Public ι n)
        (V := Private ι n)
        (time (2 * (s : ℝ)) ((etaH + R * etaD) * T) γ) (width (2 * (s : ℝ)) γ) (moment γ) ε) = 1 ∧
      ∀ x, IsUnitary (p.eval x) ∧
        ‖p.eval x ∘L (E ∘L SharpClockQuery.evolutionInput (P := Public ι n)
            (V := Private ι n)
            (time (2 * (s : ℝ)) ((etaH + R * etaD) * T) γ) (width (2 * (s : ℝ)) γ) (moment γ) ε) -
          (E ∘L SharpClockSimulation.evolutionOutput (P := Public ι n)
        (V := Private ι n)
        (time (2 * (s : ℝ)) ((etaH + R * etaD) * T) γ) (width (2 * (s : ℝ)) γ) (moment γ) ε) ∘L
            NormedSpace.exp (WeightedClock.diagonal (fun i =>
              (-Complex.I * (u i : ℂ)) • SparseStateOverlap.matrixOperator
                (ODEMatrixEnergy.lchsHamiltonian (D.matrix x) (k i))))‖ ≤ ε := by
  have ht : 0 ≤ time (2 * (s : ℝ)) ((etaH + R * etaD) * T) γ :=
    div_nonneg (mul_nonneg (mul_nonneg hρ.le hT.le) (Real.sqrt_nonneg _)) hγ.le
  have hJ := boundary_isometry (ι := ι) D
  have hMoments := fun x => moment_certificate D x etaH etaD R T k u
    hH hDiss hρ hT hk hu huT (hrH x) (hcH x) (hrD x) (hcD x)
  have hSelf : ∀ x, star (generator D x k u (etaH + R * etaD) T) =
      generator D x k u (etaH + R * etaD) T :=
    fun x => generator_adjoint D x k u (etaH + R * etaD) T
  have hD : ∀ x, (action D x k u (etaH + R * etaD) T γ)† ∘L
      action D x k u (etaH + R * etaD) T γ = 1 :=
    fun x => (action_unitary D x k u (etaH + R * etaD) T γ).1
  have hRight : ∀ x, (1 - action D x k u (etaH + R * etaD) T γ) ∘L
      resolventAtOne (scaled (generator D x k u (etaH + R * etaD) T) γ) = 1 := by
    intro x
    change (1 - action D x k u (etaH + R * etaD) T γ) * resolventAtOne (scaled (generator D x k u (etaH + R * etaD) T) γ) = 1
    rw [action_eq_cayley D x k u (etaH + R * etaD) T γ]
    exact ImprovedCayleyMoments.one_sub_cayleyAction_mul_resolventAtOne
      (A := Private ι n →L[ℂ] Private ι n)
      (scaled (generator D x k u (etaH + R * etaD) T) γ) (inverse D x k u (etaH + R * etaD) T γ)
      (inverse_right D x k u (etaH + R * etaD) T γ)
      (inverse_left D x k u (etaH + R * etaD) T γ)
  have hLeft : ∀ x, resolventAtOne (scaled (generator D x k u (etaH + R * etaD) T) γ) ∘L
      (1 - action D x k u (etaH + R * etaD) T γ) = 1 := by
    intro x
    change resolventAtOne (scaled (generator D x k u (etaH + R * etaD) T) γ) * (1 - action D x k u (etaH + R * etaD) T γ) = 1
    rw [action_eq_cayley D x k u (etaH + R * etaD) T γ]
    exact ImprovedCayleyMoments.resolventAtOne_mul_one_sub_cayleyAction
      (A := Private ι n →L[ℂ] Private ι n)
      (scaled (generator D x k u (etaH + R * etaD) T) γ) (inverse D x k u (etaH + R * etaD) T γ)
      (inverse_right D x k u (etaH + R * etaD) T γ)
  obtain ⟨p, _hNat, hCount, hIn, hOut, hAction⟩ :=
    SharpLabeledActiveClockQuery.evolution_query_certificate
      (fun x => action D x k u (etaH + R * etaD) T γ) (fun x => resolventAtOne (scaled (generator D x k u (etaH + R * etaD) T) γ))
      (boundary D) (fun x => compressed (generator D x k u (etaH + R * etaD) T) (boundary D) γ)
      (time (2 * (s : ℝ)) ((etaH + R * etaD) * T) γ) (width (2 * (s : ℝ)) γ) (endpoint γ) (moment γ) ε
      ht (width_ge_one (2 * (s : ℝ)) γ) hD hJ hRight hLeft
      (fun x => resolvent_norm (generator D x k u (etaH + R * etaD) T) (2 * (s : ℝ)) γ hγ.le
        (hMoments x).1)
      (fun x => resolventAtOne_compression (scaled (generator D x k u (etaH + R * etaD) T) γ) (boundary D) hJ)
      (fun x => compressed_self_adjoint (generator D x k u (etaH + R * etaD) T) (boundary D) γ (hSelf x))
      (fun x => (compressed_norm (generator D x k u (etaH + R * etaD) T) (boundary D) γ hγ.le hJ
        (hMoments x).2).trans hγOne)
      (fun x => endpoint_norm (generator D x k u (etaH + R * etaD) T) (boundary D) γ (hSelf x) hJ hγ.le
        (hMoments x).2)
      (endpoint_sq γ).le (moment_le_width (2 * (s : ℝ)) γ hγ.le hγOne)
      hε hεOne O hO E hE q hQuery
  refine ⟨p, ?_, hIn, hOut, fun x => ?_⟩
  · change time (2 * (s : ℝ)) ((etaH + R * etaD) * T) γ * moment γ + width (2 * (s : ℝ)) γ *
      (1 + Real.log (3 / ε)) ≤
        12 * ImprovedPrecisionBudget.shape (2 * (s : ℝ)) ((etaH + R * etaD) * T) (ImprovedPrecisionBudget.targetLog ε)
      at hBudget
    have hMul := mul_le_mul_of_nonneg_left hBudget
      (show (0 : ℝ) ≤ 768 * (q : ℝ) by positivity)
    calc
      (p.count : ℝ) ≤ 768 * (q : ℝ) * (time (2 * (s : ℝ)) ((etaH + R * etaD) * T) γ * moment γ +
          width (2 * (s : ℝ)) γ * (1 + Real.log (3 / ε))) := hCount
      _ ≤ (768 * (q : ℝ)) * (12 * ImprovedPrecisionBudget.shape (2 * (s : ℝ)) ((etaH + R * etaD) * T)
          (ImprovedPrecisionBudget.targetLog ε)) := hMul
      _ = _ := by ring
  · obtain ⟨hUnitary, hError⟩ := hAction x
    rw [physical_exponent D x k u (etaH + R * etaD) T γ hρ.ne' hT hγ.ne'] at hError
    exact ⟨hUnitary, hError⟩


end
end SparseHamiltonian.ODEJointCayley
