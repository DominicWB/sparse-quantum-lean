import SparseLowerBounds.Query.Readout
import LinearSystemLowerBound.Weight.Bias

/-!
# Mixed outputs, heralds and trace distance

The output conventions of the manuscript's lower bounds, stated with the spectral trace
distance, and their bridge to the observable forms used by the package's proofs.

* `TraceDistanceLE ρ ψ ε`: `½‖ρ - |ψ⟩⟨ψ|‖₁ ≤ ε`, with the trace norm defined spectrally (the sum
  of the absolute eigenvalues of the Hermitian difference, so that the trace distance is half that
  sum, `ODEMixedOutput.hermitianTraceDistance`). This is the accuracy notion of eqs.
  `hsl:eq:accuracy` and `qlsl:eq:target` and of Section `odel:sec:main`.
* `systemState e Φ`: the possibly mixed system state of a workspace vector `Φ` read through
  `e : K → ℂ^S ⊗ G` (system and garbage registers): the reduced density operator
  `Tr_G |eΦ⟩⟨eΦ|` on `ℂ^S`, characterised by `tr(M ρ) = ⟪eΦ, (M ⊗ 1_G) eΦ⟫` for every `M`
  (`trace_comp_systemState`).
* `heraldedState e P Φ`: the conditional system state after the input-independent herald
  projection `P`, `Tr_G |e PΦ⟩⟨e PΦ| / ‖PΦ‖²`; its success probability is `‖PΦ‖²`.

`accurate_of_traceDistanceLE` and `heraldedAccurate_of_traceDistanceLE` derive the observable
forms `Readout.Accurate` and `Readout.HeraldedAccurate` of the package's lower-bound proofs
(every Hermitian contraction has expectation within `2ε` of its ideal value) from these
trace-distance guarantees, by trace-distance contractivity
(`LinearSystemLowerBound.abs_corr_sub_le`).
-/

set_option autoImplicit false

namespace ManuscriptConformance

noncomputable section
open scoped InnerProductSpace InnerProduct
open ContinuousLinearMap SparseHamiltonian SparseLowerBounds SparseLowerBounds.Readout

section TraceDistance

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-- **Trace distance at most `ε` from a pure state**: `½‖ρ - |ψ⟩⟨ψ|‖₁ ≤ ε`, the trace norm being
the sum of the absolute eigenvalues of the Hermitian difference, so that the trace distance is half
that sum (eqs. `hsl:eq:accuracy`,
`qlsl:eq:target`). The Hermitian-difference proof is part of the statement; it holds for every
density operator (`systemState_isSelfAdjoint`). -/
def TraceDistanceLE (ρ : E →L[ℂ] E) (ψ : E) (ε : ℝ) : Prop :=
  ∃ h : (ρ - ODEMixedOutput.pureOperator ψ).toLinearMap.IsSymmetric,
    ODEMixedOutput.hermitianTraceDistance ρ (ODEMixedOutput.pureOperator ψ) h ≤ ε

/-- Trace-distance contractivity: an operator within trace distance `ε` of `|ψ⟩⟨ψ|` gives every
contraction `M` an expectation within `2ε` of `⟪ψ, M ψ⟫`. -/
theorem abs_corr_sub_le_of_traceDistanceLE {ρ : E →L[ℂ] E} {ψ : E} {ε : ℝ}
    (h : TraceDistanceLE ρ ψ ε) (M : E →L[ℂ] E) (hM : ‖M‖ ≤ 1) :
    |LinearSystemLowerBound.corr M ρ - (⟪ψ, M ψ⟫_ℂ).re| ≤ 2 * ε := by
  obtain ⟨hs, hd⟩ := h
  have hMv : ∀ v, ‖M v‖ ≤ ‖v‖ := fun v =>
    (M.le_opNorm v).trans (mul_le_of_le_one_left (norm_nonneg v) hM)
  have hc := LinearSystemLowerBound.abs_corr_sub_le M hMv ρ (ODEMixedOutput.pureOperator ψ) hs
  rw [LinearSystemLowerBound.corr_pure] at hc
  linarith

end TraceDistance

section SystemState

variable {S G K : Type*} [Fintype S] [DecidableEq S]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- **The system state** of a workspace vector `Φ` read through `e` into system ⊗ garbage: the
reduced density operator `Tr_G |eΦ⟩⟨eΦ|` on `ℂ^S` (entries `⟪(eΦ)_j, (eΦ)_i⟫_G`). Its trace is
`‖eΦ‖²`, so it is a density operator for a unit vector and an isometry `e`. -/
def systemState (e : K →L[ℂ] SysGarb S G) (Φ : K) :
    EuclideanSpace ℂ S →L[ℂ] EuclideanSpace ℂ S :=
  Matrix.toEuclideanCLM (𝕜 := ℂ) (n := S) (reducedDensity (e Φ))

omit [Fintype S] [DecidableEq S] [CompleteSpace G] in
/-- The reduced density matrix is Hermitian. -/
theorem reducedDensity_isHermitian (Φ : SysGarb S G) : (reducedDensity Φ).IsHermitian := by
  ext i j
  simp only [reducedDensity, Matrix.conjTranspose_apply, Matrix.of_apply]
  exact inner_conj_symm (Φ j) (Φ i)

omit [CompleteSpace G] [CompleteSpace K] in
/-- The system state is self-adjoint. -/
theorem systemState_isSelfAdjoint (e : K →L[ℂ] SysGarb S G) (Φ : K) :
    IsSelfAdjoint (systemState e Φ) := by
  rw [IsSelfAdjoint, systemState, ← map_star, Matrix.star_eq_conjTranspose,
    (reducedDensity_isHermitian (e Φ)).eq]

omit [CompleteSpace G] [CompleteSpace K] in
/-- The Hermitian-difference proof of `TraceDistanceLE` always exists for the system state. -/
theorem systemState_sub_pure_isSymmetric (e : K →L[ℂ] SysGarb S G) (Φ : K)
    (ψ : EuclideanSpace ℂ S) :
    (systemState e Φ - ODEMixedOutput.pureOperator ψ).toLinearMap.IsSymmetric :=
  (systemState_isSelfAdjoint e Φ).isSymmetric.sub
    (ODEMixedOutput.pureOperator_positive ψ).isSymmetric

omit [CompleteSpace G] [CompleteSpace K] in
/-- The trace of a matrix operator is the matrix trace. -/
theorem trace_toEuclideanCLM (A : Matrix S S ℂ) :
    LinearMap.trace ℂ (EuclideanSpace ℂ S)
        ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := S) A : EuclideanSpace ℂ S →L[ℂ] _) :
          EuclideanSpace ℂ S →ₗ[ℂ] EuclideanSpace ℂ S) = A.trace := by
  rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin, Matrix.toEuclideanLin_eq_toLin_orthonormal,
    LinearMap.trace_eq_matrix_trace ℂ (EuclideanSpace.basisFun S ℂ).toBasis,
    LinearMap.toMatrix_toLin]

/-- **The system state is the partial trace**: `tr(M ρ) = ⟪eΦ, (M ⊗ 1_G) eΦ⟫ = ⟪Φ, e†(M ⊗ 1)e Φ⟫`
for every system operator `M`. -/
theorem trace_comp_systemState (e : K →L[ℂ] SysGarb S G) (Φ : K)
    (M : EuclideanSpace ℂ S →L[ℂ] EuclideanSpace ℂ S) :
    LinearMap.trace ℂ (EuclideanSpace ℂ S)
        ((M ∘L systemState e Φ : EuclideanSpace ℂ S →L[ℂ] _) :
          EuclideanSpace ℂ S →ₗ[ℂ] EuclideanSpace ℂ S) = ⟪Φ, outObs e M Φ⟫_ℂ := by
  rw [inner_outObs, ← trace_toEuclideanCLM, map_mul, StarAlgEquiv.apply_symm_apply]
  rfl

/-- The correlation of a system observable with the system state. -/
theorem corr_systemState (e : K →L[ℂ] SysGarb S G) (Φ : K)
    (M : EuclideanSpace ℂ S →L[ℂ] EuclideanSpace ℂ S) :
    LinearSystemLowerBound.corr M (systemState e Φ) = (⟪Φ, outObs e M Φ⟫_ℂ).re := by
  rw [LinearSystemLowerBound.corr, trace_comp_systemState]

/-- **Trace-distance accuracy gives the observable form** `Readout.Accurate`: if the system state
of the output is within trace distance `ε` of `|ψ⟩⟨ψ|`, every Hermitian contraction has
expectation within `2ε` of `⟪ψ, M ψ⟫`. -/
theorem accurate_of_traceDistanceLE {e : K →L[ℂ] SysGarb S G} {Φ : K}
    {ψ : EuclideanSpace ℂ S} {ε : ℝ} (h : TraceDistanceLE (systemState e Φ) ψ ε) :
    Accurate e Φ ψ ε := by
  intro M _ hM
  have := abs_corr_sub_le_of_traceDistanceLE h M hM
  rwa [corr_systemState] at this

/-- **The conditional system state after a herald** `P`: `Tr_G |e PΦ⟩⟨e PΦ| / ‖PΦ‖²`, the state
conditional on success, whose probability is `‖PΦ‖²`. -/
def heraldedState (e : K →L[ℂ] SysGarb S G) (P : K →L[ℂ] K) (Φ : K) :
    EuclideanSpace ℂ S →L[ℂ] EuclideanSpace ℂ S :=
  (((‖P Φ‖ ^ 2)⁻¹ : ℝ) : ℂ) • systemState e (P Φ)

/-- **Conditional trace-distance accuracy gives the heralded observable form**
`Readout.HeraldedAccurate`, for an orthogonal herald projection with nonzero success
probability. -/
theorem heraldedAccurate_of_traceDistanceLE {e : K →L[ℂ] SysGarb S G} {P : K →L[ℂ] K}
    (hP : IsStarProjection P) {Φ : K} (hpos : 0 < ‖P Φ‖) {ψ : EuclideanSpace ℂ S} {ε : ℝ}
    (h : TraceDistanceLE (heraldedState e P Φ) ψ ε) : HeraldedAccurate e P Φ ψ ε := by
  intro M _ hM
  have hc := abs_corr_sub_le_of_traceDistanceLE h M hM
  rw [heraldedState, LinearSystemLowerBound.corr_smul_real, corr_systemState] at hc
  have hPsa : P† = P := hP.isSelfAdjoint.star_eq
  have hinner : ⟪Φ, (P ∘L outObs e M ∘L P) Φ⟫_ℂ = ⟪P Φ, outObs e M (P Φ)⟫_ℂ := by
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      ← ContinuousLinearMap.adjoint_inner_left, hPsa]
  rw [hinner]
  set w := ‖P Φ‖ ^ 2 with hw
  have hw0 : 0 < w := by positivity
  set a := (⟪P Φ, outObs e M (P Φ)⟫_ℂ).re
  set b := (⟪ψ, M ψ⟫_ℂ).re
  have hab : |a - w * b| = w * |w⁻¹ * a - b| := by
    rw [← abs_of_pos hw0, ← abs_mul, abs_of_pos hw0]
    congr 1
    field_simp
  rw [hab]
  calc w * |w⁻¹ * a - b| ≤ w * (2 * ε) := mul_le_mul_of_nonneg_left hc hw0.le
    _ = 2 * ε * w := by ring

end SystemState

end

end ManuscriptConformance
