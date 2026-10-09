import DysonSingleProgram.Parallel.Four
import ODELowerBoundExtensions.Release.Strip

set_option autoImplicit false

/-!
# Heralded accuracy of the single program

Manuscript lines 4111-4113 (Section `odel:sec:main`): "The solver produces a success flag of
probability at least `2/3` on
every input. Conditional on success, its output density operator is within trace distance `ε` of
the normalised solution." The single-program class `SparseLowerBounds.ODE.Solver` states this as
`Readout.HeraldedAccurate` (observable form, multiplied through by the success probability).

* `outObs_endpointReadout_one`: the clean endpoint readout `endpointReadout 1 i₀` measures a
  system operator as itself;
* `certificate_observable`: the released complete certificate (`ODECompleteTrial.Certificate`,
  conditional trace distance at most `ε`) bounds the conditional expectation of every
  self-adjoint contraction `A` of the four-attempt wrapper within `2ε` of the ideal one: the
  corollary of `Release.certificate_densityAccurate` with the system read directly
  (`outObs_endpointReadout_one`; for an empty system index both sides vanish).
* `heraldedAccurate_of_corr`: a pure state whose heralded readout correlations are those of a
  retry protocol with positive success mass and `2ε`-accurate conditional expectations is
  heralded-accurate.
-/

namespace DysonSingleProgram

noncomputable section
open SparseHamiltonian SparseLowerBounds OracleCircuit
open scoped InnerProduct InnerProductSpace

/-- **The clean endpoint readout measures a system operator as itself**:
`e† (A ⊗ 1) e = A` for `e = endpointReadout 1 i₀`. -/
theorem outObs_endpointReadout_one {N : Type*} [Fintype N] [DecidableEq N] (i₀ : N)
    (A : EuclideanSpace ℂ N →L[ℂ] EuclideanSpace ℂ N) :
    Readout.outObs (SparseLowerBounds.Hamiltonian.endpointReadout
      (1 : EuclideanSpace ℂ N →L[ℂ] EuclideanSpace ℂ N) i₀) A = A := by
  have h : ∀ φ : EuclideanSpace ℂ N,
      ⟪φ, Readout.outObs (SparseLowerBounds.Hamiltonian.endpointReadout
        (1 : EuclideanSpace ℂ N →L[ℂ] EuclideanSpace ℂ N) i₀) A φ⟫_ℂ = ⟪φ, A φ⟫_ℂ := fun φ => by
    have h1 := SparseLowerBounds.Hamiltonian.inner_outObs_endpointReadout
      (1 : EuclideanSpace ℂ N →L[ℂ] EuclideanSpace ℂ N) (by ext; simp) i₀ A φ
    simp only [one_apply_eq_self] at h1
    exact h1
  refine ContinuousLinearMap.coe_injective ((ext_inner_map _ _).1 fun φ => ?_)
  simp only [ContinuousLinearMap.coe_coe]
  rw [← inner_conj_symm _ φ, h, inner_conj_symm]

/-- **The released certificate in observable form**: the conditional output of the four-attempt
wrapper reproduces every self-adjoint contraction's ideal expectation within `2ε`; the corollary
of `ODELowerBoundExtensions.Release.certificate_densityAccurate` with the system read directly
(`outObs_endpointReadout_one`). -/
theorem certificate_observable {N R X L : Type*} [Fintype N] [DecidableEq N]
    [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
    {O : (L ⊕ Bool) → X → R →L[ℂ] R} {q : ℕ → MultiOracleCircuit.Program O} {M : ℕ} {ψ : R}
    {F : EuclideanSpace ℂ N →L[ℂ] R} {x : X} {target : EuclideanSpace ℂ N}
    {s Θ ell g ε : ℝ} (h : ODECompleteTrial.Certificate q M ψ F x target s Θ ell g ε)
    (A : EuclideanSpace ℂ N →L[ℂ] EuclideanSpace ℂ N) (hA : IsSelfAdjoint A) (hA1 : ‖A‖ ≤ 1) :
    |LinearSystemLowerBound.corr A ((ODECompleteTrial.algorithm h.trial).conditionalDensity x) -
        (⟪ODEStateNormalization.unitDirection target,
          A (ODEStateNormalization.unitDirection target)⟫_ℂ).re| ≤ 2 * ε := by
  rcases isEmpty_or_nonempty N with hN | ⟨⟨i₀⟩⟩
  · have hz : ∀ v : EuclideanSpace ℂ N, v = 0 := fun v => by
      ext i
      exact isEmptyElim i
    have hρ : (ODECompleteTrial.algorithm h.trial).conditionalDensity x = 0 :=
      ContinuousLinearMap.ext fun v => hz _
    obtain ⟨hsym, hdist⟩ := h.conditional_error
    have hε : 0 ≤ ε := (ODEMixedOutput.hermitianTraceDistance_nonneg _ _ hsym).trans hdist
    rw [hρ, LinearSystemLowerBound.corr_zero, hz (ODEStateNormalization.unitDirection target)]
    simp only [map_zero, inner_zero_left, Complex.zero_re, sub_zero, abs_zero]
    linarith
  · have h' := ODELowerBoundExtensions.Release.certificate_densityAccurate h i₀ A hA hA1
    rwa [outObs_endpointReadout_one] at h'

/-- **Heralded accuracy from the protocol's correlations**: if a state `Φ` with herald `P` and
readout `e` has heralded success `p.successMass x > 0` and heralded readout correlations
`corr A (p.successDensity x)`, and the protocol's conditional expectations are within `2ε` of the
target's, then `Φ` is heralded-accurate for the target. -/
theorem heraldedAccurate_of_corr {N K X L G : Type*} [Fintype N] [DecidableEq N]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
    {O : L → X → R →L[ℂ] R} (p : ODERepeatProtocol.Protocol O (EuclideanSpace ℂ N)) (x : X)
    (e : K →L[ℂ] SysGarb N G) (P : K →L[ℂ] K) (Φ : K) (ψ : EuclideanSpace ℂ N) (ε : ℝ)
    (hpos : 0 < p.successMass x) (hsucc : ‖P Φ‖ ^ 2 = p.successMass x)
    (hcorr : ∀ A : EuclideanSpace ℂ N →L[ℂ] EuclideanSpace ℂ N,
      (⟪Φ, (P ∘L Readout.outObs e A ∘L P) Φ⟫_ℂ).re =
        LinearSystemLowerBound.corr A (p.successDensity x))
    (hacc : ∀ A : EuclideanSpace ℂ N →L[ℂ] EuclideanSpace ℂ N, IsSelfAdjoint A → ‖A‖ ≤ 1 →
      |LinearSystemLowerBound.corr A (p.conditionalDensity x) - (⟪ψ, A ψ⟫_ℂ).re| ≤ 2 * ε) :
    Readout.HeraldedAccurate e P Φ ψ ε := by
  intro A hA hA1
  rw [hcorr A, hsucc]
  have hm : ((p.successMass x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hpos.ne'
  have hd : p.successDensity x = ((p.successMass x : ℝ) : ℂ) • p.conditionalDensity x := by
    rw [ODERepeatProtocol.Protocol.conditionalDensity, smul_smul, mul_inv_cancel₀ hm, one_smul]
  rw [hd, LinearSystemLowerBound.corr_smul_real, ← mul_sub, abs_mul, abs_of_pos hpos]
  calc p.successMass x * |LinearSystemLowerBound.corr A (p.conditionalDensity x) -
        (⟪ψ, A ψ⟫_ℂ).re| ≤ p.successMass x * (2 * ε) :=
        mul_le_mul_of_nonneg_left (hacc A hA hA1) hpos.le
    _ = 2 * ε * p.successMass x := by ring

end

end DysonSingleProgram
