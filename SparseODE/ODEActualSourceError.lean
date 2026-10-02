import SparseODE.ODENativeSourceLCU

/-!
# Error and herald for the actual source-aware joint circuit

Normalized source weights and LCHS coefficients are combined in a single
branch register. The implementation error is bounded once on that joint
space. Restoring the source mass and adding the certified quadrature error
then proves the actual decoded-vector premise needed by the herald theorem.
Gaussian LCHS approximation and the supplied source preparation interface
remain explicit; this is not yet a source-oracle or amplification compiler.

-/

namespace SparseHamiltonian.ODEActualSourceError

noncomputable section
open ContinuousLinearMap OracleCircuit
open scoped BigOperators InnerProduct
set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 2048

variable {σ ι P K : Type*} [Fintype σ] [Fintype ι]
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The source probability and the complex LCHS coefficient share one label. -/
def coefficients (z : σ → P) (c : ι → ℂ) : σ × ι → ℂ :=
  ODESourceCoefficients.productCoeff (ODESourceBranches.probability z) c

/-- Actual source preparation followed by the simulator's common embedding. -/
def input (E : ODEJointLCU.BranchSpace (σ × ι) P →L[ℂ] K)
    (z : σ → P) (c : ι → ℂ) (J : σ → P →L[ℂ] P) : P →L[ℂ] K :=
  ODEJointSourceLCU.input E (coefficients z c) (fun a => J a.1)

/-- The output phases erase both the source and LCHS labels. -/
def output (E : ODEJointLCU.BranchSpace (σ × ι) P →L[ℂ] K)
    (z : σ → P) (c : ι → ℂ) : P →L[ℂ] K :=
  ODEJointLCU.output E (coefficients z c)

/-- The decoded successful vector of the implemented circuit. -/
def decoded (E : ODEJointLCU.BranchSpace (σ × ι) P →L[ℂ] K)
    (z : σ → P) (c : ι → ℂ) (J : σ → P →L[ℂ] P)
    (W : K →L[ℂ] K) (v : P) : P :=
  ODEHeraldedSuccess.decoded (output E z c) W (input E z c J v)

omit [CompleteSpace P] [InnerProductSpace ℂ P] in
/-- The joint coefficient mass stays exactly three, independent of the
number of source nodes or the source norm budget. -/
theorem coefficientMass_eq (z : σ → P) (c : ι → ℂ)
    (hz : 0 < ODESourceBranches.mass z)
    (hc : ODECoherentLCU.coefficientMass c = 3) :
    ODECoherentLCU.coefficientMass (coefficients z c) = 3 := by
  unfold coefficients
  rw [ODESourceCoefficients.coefficientMass_product
    (ODESourceBranches.probability z) c (ODESourceBranches.probability_nonneg z),
    ODESourceBranches.sum_probability z hz, one_mul, hc]

/-- Joint simulation, finite LCHS and source quadrature errors add as
3nu*B + 2nu*B + nu*B for the actual decoded physical output. -/
theorem six_tolerance_error
    (E : ODEJointLCU.BranchSpace (σ × ι) P →L[ℂ] K)
    (hE : E† ∘L E = 1) (z : σ → P) (c : ι → ℂ)
    (hz : 0 < ODESourceBranches.mass z)
    (hc : ODECoherentLCU.coefficientMass c = 3)
    (J : σ → P →L[ℂ] P) (hJ : ∀ a, (J a)† ∘L J a = 1)
    (v : P) (hv : ‖v‖ = 1)
    (hPrep : ∀ a, z a ≠ 0 → J a v = ODEStateNormalization.unitDirection (z a))
    (W : K →L[ℂ] K) (U : σ → ι → P →L[ℂ] P)
    (S : σ → P →L[ℂ] P) (x : P) (ν : ℝ)
    (hSimulation : ‖W ∘L E - E ∘L
      WeightedClock.diagonal (fun a : σ × ι => U a.1 a.2)‖ ≤ ν)
    (hLCHS : ∀ a, ‖(∑ i, c i • U a i) - S a‖ ≤ 2 * ν)
    (hQuadrature : ‖(∑ a, S a (z a)) - x‖ ≤ ν * ODESourceBranches.mass z) :
    ‖(3 * ODESourceBranches.mass z) • decoded E z c J W v - x‖ ≤
      6 * ν * ODESourceBranches.mass z := by
  let B := ODESourceBranches.mass z
  let F := ∑ a : σ × ι, coefficients z c a • U a.1 a.2 (J a.1 v)
  let y := ∑ a, (ODESourceBranches.probability z a : ℂ) • S a (J a v)
  have hm : ODECoherentLCU.coefficientMass (coefficients z c) = 3 :=
    coefficientMass_eq z c hz hc
  have hpos : 0 < ODECoherentLCU.coefficientMass (coefficients z c) := by
    rw [hm]
    norm_num
  have hSimulationVector : ‖(3 : ℂ) • decoded E z c J W v - F‖ ≤ 3 * ν := by
    have h := ODEJointSourceLCU.actual_vector_error E (coefficients z c)
      (fun a : σ × ι => J a.1) hE hpos (fun a => hJ a.1)
      W (fun a : σ × ι => U a.1 a.2) ν hSimulation v
    simpa only [hm, hv, mul_one, Complex.ofReal_ofNat, decoded, ODEHeraldedSuccess.decoded,
      ODEJointSourceLCU.decoded, input, output, F] using h
  have hPrepared : ∀ a, ‖J a v‖ = 1 := by
    intro a
    rw [(J a).norm_map_iff_adjoint_comp_self.mpr (hJ a), hv]
  have hAnalytic : ‖F - y‖ ≤ 2 * ν := by
    exact ODESourceCoefficients.uniform_error
      (ODESourceBranches.probability z) c U S (fun a => J a v) (2 * ν)
      (ODESourceBranches.probability_nonneg z)
      (ODESourceBranches.sum_probability z hz) hPrepared hLCHS
  have hFive : ‖(3 : ℂ) • decoded E z c J W v - y‖ ≤ 5 * ν := by
    calc
      _ ≤ ‖(3 : ℂ) • decoded E z c J W v - F‖ + ‖F - y‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ 3 * ν + 2 * ν := add_le_add hSimulationVector hAnalytic
      _ = 5 * ν := by ring
  have hRestore : (B : ℂ) • y = ∑ a, S a (z a) :=
    ODESourceBranches.rescaled_preparedSum z S J v hz hPrep
  have hScalar : ((3 * B : ℝ) : ℂ) = (B : ℂ) * 3 := by
    push_cast
    ring
  have hScaled : ‖((3 * B : ℝ) : ℂ) • decoded E z c J W v - ∑ a, S a (z a)‖ ≤
      5 * ν * B := by
    calc
      _ = ‖(B : ℂ) • ((3 : ℂ) • decoded E z c J W v - y)‖ := by
        rw [smul_sub, hRestore, smul_smul, hScalar]
      _ = B * ‖(3 : ℂ) • decoded E z c J W v - y‖ := by
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hz]
      _ ≤ B * (5 * ν) := mul_le_mul_of_nonneg_left hFive hz.le
      _ = 5 * ν * B := by ring
  have hFinal : ‖((3 * B : ℝ) : ℂ) • decoded E z c J W v - x‖ ≤ 6 * ν * B := by
    calc
      _ ≤ ‖((3 * B : ℝ) : ℂ) • decoded E z c J W v - ∑ a, S a (z a)‖ +
          ‖(∑ a, S a (z a)) - x‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ 5 * ν * B + ν * B := add_le_add hScaled hQuadrature
      _ = 6 * ν * B := by ring
  simpa only [Complex.coe_smul] using hFinal


/-- Accuracy and the herald concern the actual unitary output. This records
an unamplified preparation; the lower probability is quadratic in `1/g`. -/
structure Certificate
    (E : ODEJointLCU.BranchSpace (σ × ι) P →L[ℂ] K)
    (z : σ → P) (c : ι → ℂ) (J : σ → P →L[ℂ] P)
    (W : K →L[ℂ] K) (v x : P) (g ε : ℝ) : Prop where
  input_unit : ‖input E z c J v‖ = 1
  output_isometry : (output E z c)† ∘L output E z c = 1
  evolved_unit : ‖W (input E z c J v)‖ = 1
  success_projection : PhaseSubspaceGates.IsOrthogonalProjection
    (ODEHeraldedSuccess.successProjector (output E z c))
  vector_error : ‖(3 * ODESourceBranches.mass z) • decoded E z c J W v - x‖ ≤
    6 * ImprovedODEQueryBudget.precision g ε * ODESourceBranches.mass z
  decoded_nonzero : decoded E z c J W v ≠ 0
  direction_unit : ‖ODEStateNormalization.unitDirection (decoded E z c J W v)‖ = 1
  direction_error :
    ‖ODEStateNormalization.unitDirection (decoded E z c J W v) -
      ODEStateNormalization.unitDirection x‖ ≤ ε / 500
  amplitude_lower : 1 / (4 * g) ≤
    ‖ODEHeraldedSuccess.successfulComponent (output E z c) W (input E z c J v)‖
  amplitude_upper :
    ‖ODEHeraldedSuccess.successfulComponent (output E z c) W (input E z c J v)‖ < 1 / 2
  probability_lower : 1 / (16 * g ^ 2) ≤
    ODEHeraldedSuccess.successProbability (output E z c) W (input E z c J v)
  probability_upper :
    ODEHeraldedSuccess.successProbability (output E z c) W (input E z c J v) < 1 / 4

/-- The actual-vector error is derived from joint simulation, finite LCHS
and quadrature. It is no longer assumed as a premise of the herald theorem.
The Gaussian and source-access constructions are still separate obligations. -/
theorem actual_source_certificate
    (E : ODEJointLCU.BranchSpace (σ × ι) P →L[ℂ] K)
    (hE : E† ∘L E = 1) (z : σ → P) (c : ι → ℂ)
    (hc : ODECoherentLCU.coefficientMass c = 3)
    (J : σ → P →L[ℂ] P) (hJ : ∀ a, (J a)† ∘L J a = 1)
    (v : P) (hv : ‖v‖ = 1)
    (hPrep : ∀ a, z a ≠ 0 → J a v = ODEStateNormalization.unitDirection (z a))
    (W : K →L[ℂ] K) (hW : IsUnitary W)
    (U : σ → ι → P →L[ℂ] P) (S : σ → P →L[ℂ] P)
    (x : P) (g ε : ℝ) (hx : x ≠ 0) (hg : 1 ≤ g)
    (hε : 0 < ε) (hεHalf : ε ≤ 1 / 2)
    (hNorm : ‖x‖ ≤ ODESourceBranches.mass z)
    (hBudget : ODESourceBranches.mass z ≤ g * ‖x‖)
    (hSimulation : ‖W ∘L E - E ∘L
      WeightedClock.diagonal (fun a : σ × ι => U a.1 a.2)‖ ≤
        ImprovedODEQueryBudget.precision g ε)
    (hLCHS : ∀ a, ‖(∑ i, c i • U a i) - S a‖ ≤
      2 * ImprovedODEQueryBudget.precision g ε)
    (hQuadrature : ‖(∑ a, S a (z a)) - x‖ ≤
      ImprovedODEQueryBudget.precision g ε * ODESourceBranches.mass z) :
    Certificate E z c J W v x g ε := by
  have hz := ODESourceBranches.mass_pos_of_solution z x hx hNorm
  have hm := coefficientMass_eq z c hz hc
  have hpos : 0 < ODECoherentLCU.coefficientMass (coefficients z c) := by
    rw [hm]
    norm_num
  have hOut : (output E z c)† ∘L output E z c = 1 :=
    ODEJointLCU.output_isometry E (coefficients z c) hE hpos
  have hIn : (input E z c J)† ∘L input E z c J = 1 :=
    ODEJointSourceLCU.input_isometry E (coefficients z c)
      (fun a : σ × ι => J a.1) hE hpos (fun a => hJ a.1)
  have hUnit : ‖input E z c J v‖ = 1 := by
    rw [(input E z c J).norm_map_iff_adjoint_comp_self.mpr hIn, hv]
  have hError := six_tolerance_error E hE z c hz hc J hJ v hv hPrep W U S x
    (ImprovedODEQueryBudget.precision g ε) hSimulation hLCHS hQuadrature
  obtain ⟨hEvolved, hProjection, hNonzero, hDirectionUnit, hDirection,
      hLower, hUpper, hLowerSq, hUpperSq⟩ :=
    ODEHeraldedSuccess.actual_preparation_certificate
      (output E z c) hOut W hW (input E z c J v) hUnit
      x (ODESourceBranches.mass z) g ε hx hg hε hεHalf hNorm hBudget hError
  exact ⟨hUnit, hOut, hEvolved, hProjection, hError, hNonzero,
    hDirectionUnit, hDirection, hLower, hUpper, hLowerSq, hUpperSq⟩

end
end SparseHamiltonian.ODEActualSourceError
