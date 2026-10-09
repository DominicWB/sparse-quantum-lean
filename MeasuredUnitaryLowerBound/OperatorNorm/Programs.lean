import MeasuredUnitaryLowerBound.OperatorNorm.Notion
import DeferredMeasurementLowerBounds.Model.Embed

set_option autoImplicit false

/-!
# Unitary programs implement within operator norm

Containment of the operator-norm notion of the manuscript for unitary circuits
(`‖A_U - U‖ ≤ ε`, eq. `hs:eq:unitaryerror`, lines 1652-1654; the package's form
`‖p.eval x ∘L J - J ∘L U‖ ≤ ε` on an isometric encoding `J`, as in
`AdaptiveUnitaryLowerBound.Theorem.implementation_count_ge_program_of_error`) in the measured
notion `NormImplements`. A unitary program `p` followed by the output of the whole workspace is
the measured algorithm `runAll p` (its known unitaries as one-outcome instruments, no
measurement, no rejection, `p.cost w` calls); read through
the endpoint readout `SparseLowerBounds.Hamiltonian.endpointReadout J i₀`, its one-element Kraus
family `p.eval x ∘L J` is within operator norm `ε` of `U ⊗ J |i₀⟩`
(`normImplements_runAll`).
-/

namespace MeasuredUnitaryLowerBound.OperatorNorm

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.Readout ContinuousLinearMap
open DeferredMeasurementLowerBounds.Model
open scoped InnerProduct InnerProductSpace

variable {K X L : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The identity of the workspace is an isometry (from Mathlib's
`ContinuousLinearMap.adjoint_one`). -/
theorem adjoint_one_comp_one : (1 : K →L[ℂ] K)† ∘L (1 : K →L[ℂ] K) = 1 := by
  rw [ContinuousLinearMap.adjoint_one]
  ext
  rfl

/-- **A unitary program as a measured algorithm**: run `p`, then output the whole workspace.
The library `TimeDependentLowerBoundExtensions` restates the same construction as
`TimeDependentLowerBoundExtensions.Measured.programRun`, so that it does not depend on this
library. -/
def runAll {O : L → X → K →L[ℂ] K} (p : MultiOracleCircuit.Program O) : Measured O K :=
  ofProgram p (.output 1 adjoint_one_comp_one)

/-- The output of `runAll p` is the pure final state. -/
theorem successDensity_runAll {O : L → X → K →L[ℂ] K} (p : MultiOracleCircuit.Program O)
    (x : X) (φ : K) :
    (runAll p).successDensity x φ = ODEMixedOutput.pureOperator (p.eval x φ) := by
  rw [runAll, successDensity_ofProgram]
  change ODEMixedOutput.pureOperator (((1 : K →L[ℂ] K)†) (p.eval x φ)) = _
  rw [ContinuousLinearMap.adjoint_one, one_apply_eq_self]

/-- The success probability of `runAll p` is the squared norm of the final state. -/
theorem successMass_runAll {O : L → X → K →L[ℂ] K} (p : MultiOracleCircuit.Program O)
    (x : X) (φ : K) : (runAll p).successMass x φ = ‖p.eval x φ‖ ^ 2 := by
  rw [runAll, successMass_ofProgram]
  change ‖((1 : K →L[ℂ] K)†) (p.eval x φ)‖ ^ 2 = _
  rw [ContinuousLinearMap.adjoint_one, one_apply_eq_self]

/-- `runAll p` makes the calls of `p`. -/
theorem worstCost_runAll {O : L → X → K →L[ℂ] K} (p : MultiOracleCircuit.Program O)
    (w : L → ℕ) : (runAll p).worstCost w = p.cost w := by
  rw [runAll, worstCost_ofProgram]
  exact add_zero _

/-- **Containment**: a unitary program that implements `U` on the isometric encoding `J` with
operator-norm error `ε`, `‖p.eval x ∘L J - J ∘L U‖ ≤ ε`, implements `U` within operator-norm
error `ε` as a measured algorithm (`runAll p`), read through the endpoint readout
`endpointReadout J i₀`, with one Kraus map and garbage `J |i₀⟩`. -/
theorem normImplements_runAll {S : Type*} [Fintype S] [DecidableEq S] {O : L → X → K →L[ℂ] K}
    (hO : ∀ l x, OracleCircuit.IsUnitary (O l x)) (p : MultiOracleCircuit.Program O)
    (J : EuclideanSpace ℂ S →L[ℂ] K) (hJ : J† ∘L J = 1) (i₀ : S) (x : X)
    (U : EuclideanSpace ℂ S →L[ℂ] EuclideanSpace ℂ S) {ε : ℝ}
    (hErr : ‖p.eval x ∘L J - J ∘L U‖ ≤ ε) :
    NormImplements (runAll p) J (Hamiltonian.endpointReadout J i₀) x U ε := by
  have hJn : ∀ v, ‖J v‖ = ‖v‖ := fun v =>
    (ContinuousLinearMap.norm_map_iff_adjoint_comp_self J).mpr hJ v
  have hε : 0 ≤ ε := (norm_nonneg _).trans hErr
  have hen : ∀ v, ‖Hamiltonian.endpointReadout J i₀ v‖ = ‖v‖ := fun v =>
    (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).mpr
      (Hamiltonian.endpointReadout_isometry J hJ i₀) v
  refine ⟨Unit, inferInstance, fun _ => p.eval x ∘L J,
    Joint.const (J (EuclideanSpace.single i₀ 1)), ?_, ?_, ?_, ?_⟩
  · have hsq := Joint.norm_const_sq (J := Unit) (J (EuclideanSpace.single i₀ 1))
    rw [Fintype.card_unit, Nat.cast_one, one_mul, hJn, PiLp.norm_single, norm_one,
      one_pow] at hsq
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp hsq
  · intro ψ
    rw [successDensity_runAll, Fintype.sum_unique]
    rfl
  · intro ψ
    rw [successMass_runAll, PositiveAdversary.norm_map_of_isUnitary (p.eval_unitary hO x), hJn]
  · refine opNorm_le_bound _ hε fun ψ => ?_
    have hg : garbageTensor U (Joint.const (J (EuclideanSpace.single i₀ 1)) : Joint Unit K) ψ () =
        Hamiltonian.endpointReadout J i₀ (J (U ψ)) := by
      ext i
      rw [garbageTensor_apply, Hamiltonian.endpointReadout_apply_iota J hJ]
      rfl
    have hcomp : ((readKraus (Hamiltonian.endpointReadout J i₀) (fun _ => p.eval x ∘L J) -
        garbageTensor U (Joint.const (J (EuclideanSpace.single i₀ 1)) : Joint Unit K) :
        EuclideanSpace ℂ S →L[ℂ] Joint Unit (SysGarb S K)) ψ) () =
        Hamiltonian.endpointReadout J i₀ ((p.eval x ∘L J - J ∘L U) ψ) := by
      rw [sub_apply, PiLp.sub_apply, readKraus_apply, hg,
        sub_apply, map_sub]
      rfl
    rw [PiLp.norm_eq_of_L2, Fintype.sum_unique, Real.sqrt_sq (norm_nonneg _)]
    change ‖((readKraus (Hamiltonian.endpointReadout J i₀) (fun _ => p.eval x ∘L J) -
        garbageTensor U (Joint.const (J (EuclideanSpace.single i₀ 1)) : Joint Unit K) :
        EuclideanSpace ℂ S →L[ℂ] Joint Unit (SysGarb S K)) ψ) ()‖ ≤ _
    rw [hcomp, hen]
    exact ((p.eval x ∘L J - J ∘L U).le_opNorm ψ).trans
      (mul_le_mul_of_nonneg_right hErr (norm_nonneg _))

end
end MeasuredUnitaryLowerBound.OperatorNorm
