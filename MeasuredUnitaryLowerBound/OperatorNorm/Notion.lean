import MeasuredUnitaryLowerBound.OperatorNorm.Sharp
import DeferredMeasurementLowerBounds.Model.Measured

set_option autoImplicit false

/-!
# Operator-norm implementation of a unitary by a measured algorithm

Corollary `hs:cor:unitary` of the manuscript (lines 1647-1666) asks for a unitary circuit
`A_U` with `‖A_U - U‖ ≤ ε` (eq. `hs:eq:unitaryerror`, lines 1652-1654), a guarantee that
"includes inputs entangled with an untouched reference" (lines 1663-1664; "The operator-norm
bound is unchanged by an untouched reference", line 1709). Randomised and adaptive algorithms
are covered "by purification and deferred measurement" (proof of `hsl:lem:precision`, lines
2363-2364).

A measured algorithm `DeferredMeasurementLowerBounds.Model.Measured O E` implements a quantum
instrument, not an operator. Its output on an input `φ`, records discarded, is
`successDensity x φ = ∑_r |A_r φ⟩⟨A_r φ|` for linear Kraus maps `A_r` (the decoded transcripts;
the deferral `DeferredMeasurementLowerBounds.Deferral.amplitude` is one such family). The
operator-norm notion used here is the one of a purification (Stinespring dilation): on the
encoded inputs `J ψ` the output has a Kraus family `A_r`, success (the herald) with probability
`‖ψ‖²`, i.e. with certainty on unit inputs, as for a unitary circuit, and the read dilation
`ψ ↦ (e (A_r ψ))_r` into records ⊗ system ⊗ garbage is within operator norm `ε` of `U ⊗ γ`,
`ψ ↦ (U ψ ⊗ γ_r)_r`, for a unit garbage vector `γ` over the records (`NormImplements`). The
Kraus family and the garbage are existential: any purification will do, and the garbage may
depend on the instance but not on the input. The notion is stated for measured algorithms, which
act on an input slot; adaptive protocols (`Protocol.Tree`) start from a fixed seed and are not
given an operator-norm form here.

* `readKraus e A`, `garbageTensor U γ`: the two maps, with their values (`readKraus_apply`,
  `garbageTensor_apply`) and norms (`norm_readKraus_apply_sq`, `norm_garbageTensor_apply`);
* `NormImplements M J e x U ε`: the notion;
* the guarantee "includes inputs entangled with an untouched reference" (lines 1663-1664, 1709)
  is, for a linear map `T` between possibly different spaces (such as
  `readKraus e A - garbageTensor U γ`), the package's
  `SparseHamiltonian.FiniteReferenceLift.norm_lift_le` (`‖T ⊗ 1‖ ≤ ‖T‖` for a finite reference,
  with entangled inputs in `FiniteReferenceLift.norm_error_le` and `normalized_error_le`). Running
  a measured algorithm next to a reference register is not modelled.
-/

namespace MeasuredUnitaryLowerBound.OperatorNorm

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.Readout ContinuousLinearMap
open DeferredMeasurementLowerBounds.Model
open scoped InnerProduct InnerProductSpace

variable {S G E : Type*} [Fintype S] [DecidableEq S]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- **The read dilation** of a finite Kraus family `A` read through `e`:
`ψ ↦ (e (A r ψ))_r`, from the system into records ⊗ system ⊗ garbage. -/
def readKraus {R : Type*} [Fintype R] (e : E →L[ℂ] SysGarb S G)
    (A : R → EuclideanSpace ℂ S →L[ℂ] E) : EuclideanSpace ℂ S →L[ℂ] Joint R (SysGarb S G) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : R => SysGarb S G)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi fun r => e ∘L A r

/-- **The target `U ⊗ γ`** for a garbage vector `γ` over the records:
`ψ ↦ (U ψ ⊗ γ_r)_r`, with `(U ψ ⊗ g)_i = (U ψ)_i g`. -/
def garbageTensor {R : Type*} [Fintype R] (U : EuclideanSpace ℂ S →L[ℂ] EuclideanSpace ℂ S)
    (γ : Joint R G) : EuclideanSpace ℂ S →L[ℂ] Joint R (SysGarb S G) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : R => SysGarb S G)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi fun r =>
      (PiLp.continuousLinearEquiv 2 ℂ (fun _ : S => G)).symm.toContinuousLinearMap ∘L
        ContinuousLinearMap.pi (fun i => (EuclideanSpace.proj i).smulRight (γ r)) ∘L U

omit [DecidableEq S] [CompleteSpace G] [CompleteSpace E] in
/-- Components of the read dilation. -/
theorem readKraus_apply {R : Type*} [Fintype R] (e : E →L[ℂ] SysGarb S G)
    (A : R → EuclideanSpace ℂ S →L[ℂ] E) (ψ : EuclideanSpace ℂ S) (r : R) :
    readKraus e A ψ r = e (A r ψ) := by
  rfl

omit [DecidableEq S] [CompleteSpace G] in
/-- Components of the target: `(U ⊗ γ) ψ` has component `(U ψ)_i γ_r` at `(r, i)`. -/
theorem garbageTensor_apply {R : Type*} [Fintype R]
    (U : EuclideanSpace ℂ S →L[ℂ] EuclideanSpace ℂ S) (γ : Joint R G) (ψ : EuclideanSpace ℂ S)
    (r : R) (i : S) : garbageTensor U γ ψ r i = U ψ i • γ r := by
  change ((EuclideanSpace.proj i).smulRight (γ r)) (U ψ) = _
  simp [ContinuousLinearMap.smulRight_apply]

omit [DecidableEq S] in
/-- For an isometric readout, the read dilation has squared norm `∑_r ‖A_r ψ‖²`. -/
theorem norm_readKraus_apply_sq {R : Type*} [Fintype R] (e : E →L[ℂ] SysGarb S G)
    (he : e† ∘L e = 1) (A : R → EuclideanSpace ℂ S →L[ℂ] E) (ψ : EuclideanSpace ℂ S) :
    ‖readKraus e A ψ‖ ^ 2 = ∑ r, ‖A r ψ‖ ^ 2 := by
  have hn : ∀ v : E, ‖e v‖ = ‖v‖ := (ContinuousLinearMap.norm_map_iff_adjoint_comp_self e).mpr he
  rw [PiLp.norm_sq_eq_of_L2]
  exact Finset.sum_congr rfl fun r _ => by rw [readKraus_apply, hn]

omit [DecidableEq S] [CompleteSpace G] in
/-- The target has norm `‖U ψ‖ ‖γ‖`. -/
theorem norm_garbageTensor_apply {R : Type*} [Fintype R]
    (U : EuclideanSpace ℂ S →L[ℂ] EuclideanSpace ℂ S) (γ : Joint R G) (ψ : EuclideanSpace ℂ S) :
    ‖garbageTensor U γ ψ‖ = ‖U ψ‖ * ‖γ‖ := by
  have h : ‖garbageTensor U γ ψ‖ ^ 2 = (‖U ψ‖ * ‖γ‖) ^ 2 := by
    rw [mul_pow, PiLp.norm_sq_eq_of_L2 _ (garbageTensor U γ ψ), PiLp.norm_sq_eq_of_L2 _ (U ψ),
      PiLp.norm_sq_eq_of_L2 _ γ, Finset.sum_mul_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [PiLp.norm_sq_eq_of_L2]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [garbageTensor_apply, norm_smul, mul_pow]
  exact (pow_left_inj₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    two_ne_zero).1 h

variable {K X L : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- **Operator-norm implementation by a measured algorithm** (eq. `hs:eq:unitaryerror`, lines
1652-1654, for measured algorithms by purification, lines 2363-2364). On the instance `x`, the
measured algorithm `M`, run on the encoded inputs `J ψ` and read through `e`, implements `U`
within operator-norm error `ε`: its output has a finite Kraus family `A`
(`successDensity x (J ψ) = ∑_r |A_r ψ⟩⟨A_r ψ|`), it succeeds (the herald fires) with probability
`‖ψ‖²`, i.e. with certainty on unit inputs, as for a unitary circuit, and its
read dilation `ψ ↦ (e (A_r ψ))_r` is within operator norm `ε` of `U ⊗ γ` for a unit garbage
vector `γ` over the records. Algorithms that reject (success probability below one on some unit
input) are outside `NormImplements`; for them the heralded trace-distance bounds
(`MeasuredUnitaryLowerBound.Deferred.implementation_count_ge_measured_endpoint` with `p₀ > 0`)
apply. -/
def NormImplements {O : L → X → K →L[ℂ] K} (M : Measured O E) (J : EuclideanSpace ℂ S →L[ℂ] K)
    (e : E →L[ℂ] SysGarb S G) (x : X) (U : EuclideanSpace ℂ S →L[ℂ] EuclideanSpace ℂ S)
    (ε : ℝ) : Prop :=
  ∃ (R : Type) (_ : Fintype R) (A : R → EuclideanSpace ℂ S →L[ℂ] E) (γ : Joint R G),
    ‖γ‖ = 1 ∧
    (∀ ψ, M.successDensity x (J ψ) = ∑ r, ODEMixedOutput.pureOperator (A r ψ)) ∧
    (∀ ψ, M.successMass x (J ψ) = ‖ψ‖ ^ 2) ∧
    ‖readKraus e A - garbageTensor U γ‖ ≤ ε

omit [DecidableEq S] [CompleteSpace G] in
/-- The error of an operator-norm implementation is nonnegative. -/
theorem NormImplements.nonneg {O : L → X → K →L[ℂ] K} {M : Measured O E}
    {J : EuclideanSpace ℂ S →L[ℂ] K} {e : E →L[ℂ] SysGarb S G} {x : X}
    {U : EuclideanSpace ℂ S →L[ℂ] EuclideanSpace ℂ S} {ε : ℝ} (h : NormImplements M J e x U ε) :
    0 ≤ ε := by
  obtain ⟨R, _, A, γ, -, -, -, h⟩ := h
  exact le_trans (norm_nonneg (readKraus e A - garbageTensor U γ)) h

end
end MeasuredUnitaryLowerBound.OperatorNorm
