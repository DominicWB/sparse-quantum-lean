import DeferredMeasurementLowerBounds.Helpers.SearchReadout.Overlap
import DeferredMeasurementLowerBounds.Model.Measured

set_option autoImplicit false

/-!
# Read probabilities of measured algorithms

The search and unitary-implementation lower bounds for measured algorithms (manuscript Corollary
`hs:cor:unitary`, lines 1647-1666, and line 2364) measure success by the probability of reading
the instance `m` from the heralded output through an isometric readout onto `ℂ^N ⊗ G`
(`readProb`).

* `norm_sq_sel_liftReadout`: in the deferred program the weight of the value `m` in the lifted
  readout of the decoded vector is the read probability of the record-discarded output.
* `one_sub_le_readProb`: an output of unit trace within trace distance `ε₀` of `|m⟩`
  (`DensityAccurate`) reads `m` with probability at least `1 - ε₀`;
  `one_sub_le_readProb_of_accurate` is the case of success probability one.
* `readProb_successDensity`: the heralded read probability is the success probability times the
  conditional read probability, so success probability at least `p₀` and conditional trace
  distance `ε₀ ≤ 1` give a read probability at least `p₀ (1 - ε₀)` (`le_readProb_of_heralded`).
-/

namespace DeferredMeasurementLowerBounds.Corollaries

noncomputable section
open SparseHamiltonian SparseLowerBounds ContinuousLinearMap OracleCircuit
open SparseLowerBounds.Readout
open DeferredMeasurementLowerBounds.Model DeferredMeasurementLowerBounds.Readout
open AdaptiveHamiltonianLowerBound (DensityAccurate)
open scoped InnerProduct InnerProductSpace
open DeferredMeasurementLowerBounds.SearchReadout

/-- The probability of reading `m` from a heralded output. -/
def readProb {N : ℕ} {E G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (e : E →L[ℂ] SysGarb (Fin N) G) (m : Fin N) (ρ : E →L[ℂ] E) : ℝ :=
  LinearSystemLowerBound.corr
    (outObs e (ODEMixedOutput.pureOperator (EuclideanSpace.single m (1 : ℂ)))) ρ

/-- **Reading the deferred output**: the weight of the value `m` in the lifted readout of the
decoded vector `a` is the probability of reading `m` from the record-discarded output. -/
theorem norm_sq_sel_liftReadout {N : ℕ} {E G : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E] [NormedAddCommGroup G]
    [InnerProductSpace ℂ G] [CompleteSpace G] {J : Type} [Fintype J]
    (e : E →L[ℂ] SysGarb (Fin N) G) (m : Fin N) (a : Joint J E) :
    ‖sel m (liftReadout J e a)‖ ^ 2 =
      readProb e m (∑ j, ODEMixedOutput.pureOperator (a j)) := by
  have h1 := trace_outObs_liftReadout e
    (ODEMixedOutput.pureOperator (EuclideanSpace.single m (1 : ℂ))) a
  have h2 : readProb e m (∑ j, ODEMixedOutput.pureOperator (a j)) =
      LinearSystemLowerBound.corr
        (outObs (liftReadout J e)
          (ODEMixedOutput.pureOperator (EuclideanSpace.single m (1 : ℂ))))
        (ODEMixedOutput.pureOperator a) := by
    rw [readProb, LinearSystemLowerBound.corr_sum, LinearSystemLowerBound.corr, h1,
      Complex.re_sum]
    rfl
  rw [h2, LinearSystemLowerBound.corr_pure, outObs, comp_apply, comp_apply,
    adjoint_inner_right, liftObs_pure_single, re_inner_proj (sel_isStarProjection m)]

/-- The correlation of a reflection `2 A - 1`. -/
theorem corr_reflect {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (A ρ : E →L[ℂ] E) :
    LinearSystemLowerBound.corr ((2 : ℂ) • A - 1) ρ =
      2 * LinearSystemLowerBound.corr A ρ - LinearSystemLowerBound.corr 1 ρ := by
  simp only [LinearSystemLowerBound.corr, sub_comp, smul_comp, ContinuousLinearMap.toLinearMap_sub,
    ContinuousLinearMap.toLinearMap_smul, map_sub, map_smul, smul_eq_mul, Complex.sub_re,
    Complex.mul_re]
  norm_num

/-- The trace of the heralded output is the success probability. -/
theorem corr_one_successDensity {K E X L : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] [FiniteDimensional ℂ E] {O : L → X → K →L[ℂ] K} (M : Measured O E)
    (x : X) (φ : K) :
    LinearSystemLowerBound.corr 1 (M.successDensity x φ) = M.successMass x φ := by
  induction M generalizing φ with
  | output out _ =>
      rw [Measured.successDensity, Measured.successMass, LinearSystemLowerBound.corr_pure,
        one_apply_eq_self]
      simpa using inner_self_eq_norm_sq (𝕜 := ℂ) ((out†) φ)
  | reject => exact LinearSystemLowerBound.corr_zero _
  | call l b next ih => exact ih _
  | instrument n A _ next ih =>
      rw [Measured.successDensity, Measured.successMass, LinearSystemLowerBound.corr_sum]
      exact Finset.sum_congr rfl fun j _ => ih j _

/-- An output within trace distance `ε₀` of `|m⟩` reads `m` with probability at least
`1 - ε₀`. -/
theorem one_sub_le_readProb {N : ℕ} {E G : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E] [NormedAddCommGroup G]
    [InnerProductSpace ℂ G] [CompleteSpace G] (e : E →L[ℂ] SysGarb (Fin N) G)
    (he : e† ∘L e = 1) (m : Fin N) (ρ : E →L[ℂ] E) {ε₀ : ℝ}
    (hρ : LinearSystemLowerBound.corr 1 ρ = 1)
    (h : DensityAccurate e ρ (EuclideanSpace.single m (1 : ℂ)) ε₀) :
    1 - ε₀ ≤ readProb e m ρ := by
  unfold readProb
  set u : EuclideanSpace ℂ (Fin N) := EuclideanSpace.single m (1 : ℂ) with hu
  have hu1 : ⟪u, u⟫_ℂ = 1 := by simp [hu]
  set Pm := ODEMixedOutput.pureOperator u with hPm
  have hPv : ∀ v, Pm (Pm v) = Pm v := fun v => by
    simp only [hPm, ODEMixedOutput.pureOperator, InnerProductSpace.rankOne_apply,
      inner_smul_right, hu1, mul_one]
  have hPsa : IsSelfAdjoint Pm := (ODEMixedOutput.pureOperator_positive u).isSelfAdjoint
  set Mo : EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N) := (2 : ℂ) • Pm - 1 with hMo
  have hMsa : IsSelfAdjoint Mo := by
    rw [hMo]
    exact (IsSelfAdjoint.smul (by simp) hPsa).sub (IsSelfAdjoint.one _)
  have hMM : star Mo * Mo = 1 := by
    rw [hMsa.star_eq]
    refine ContinuousLinearMap.ext fun v => ?_
    show Mo (Mo v) = v
    simp only [hMo, sub_apply, smul_apply, one_apply_eq_self, map_sub, map_smul, hPv]
    module
  have hMnorm : ‖Mo‖ ≤ 1 := by
    have h2 := CStarRing.norm_star_mul_self (x := Mo)
    rw [hMM] at h2
    have h1 : ‖(1 : EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N))‖ ≤ 1 :=
      ContinuousLinearMap.norm_id_le
    nlinarith [norm_nonneg Mo]
  have hval : (⟪u, Mo u⟫_ℂ).re = 1 := by
    simp only [hMo, hPm, sub_apply, smul_apply, one_apply_eq_self, ODEMixedOutput.pureOperator,
      InnerProductSpace.rankOne_apply, hu1, one_smul, inner_sub_right, inner_smul_right]
    norm_num
  have hobs : outObs e Mo = (2 : ℂ) • outObs e Pm - 1 := by
    have he' : ∀ v, (e†) (e v) = v := fun v => by rw [← comp_apply, he, one_apply_eq_self]
    ext v
    simp only [hMo, outObs, liftObs_reflect, comp_apply, sub_apply, smul_apply, one_apply_eq_self,
      map_sub, map_smul, he']
  have hb := h Mo hMsa hMnorm
  rw [hobs, corr_reflect, hρ, hval] at hb
  have := (abs_le.mp hb).1
  linarith

/-- A measured algorithm that succeeds with probability one on the input `φ` and whose output is
within trace distance `ε₀` of `|m⟩` reads `m` jointly with the herald with probability at least
`1 - ε₀`. -/
theorem one_sub_le_readProb_of_accurate {N : ℕ} {K E G X L : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] [FiniteDimensional ℂ E] [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [CompleteSpace G] {O : L → X → K →L[ℂ] K} (M : Measured O E) (x : X) (φ : K)
    (e : E →L[ℂ] SysGarb (Fin N) G) (he : e† ∘L e = 1) (m : Fin N) {ε₀ : ℝ}
    (hmass : M.successMass x φ = 1)
    (hacc : DensityAccurate e (M.conditionalDensity x φ) (EuclideanSpace.single m (1 : ℂ)) ε₀) :
    1 - ε₀ ≤ readProb e m (M.successDensity x φ) := by
  have hcd : M.conditionalDensity x φ = M.successDensity x φ := by
    rw [Measured.conditionalDensity, hmass]
    simp
  rw [hcd] at hacc
  exact one_sub_le_readProb e he m _ (by rw [corr_one_successDensity, hmass]) hacc

/-- **The heralded read probability** is the success probability times the conditional read
probability. -/
theorem readProb_successDensity {N : ℕ} {K E G X L : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {O : L → X → K →L[ℂ] K} (M : Measured O E) (x : X) (φ : K)
    (e : E →L[ℂ] SysGarb (Fin N) G) (m : Fin N) (hpos : M.successMass x φ ≠ 0) :
    readProb e m (M.successDensity x φ) =
      M.successMass x φ * readProb e m (M.conditionalDensity x φ) := by
  rw [readProb, readProb, Measured.conditionalDensity, ← Complex.ofReal_inv,
    LinearSystemLowerBound.corr_smul_real, ← mul_assoc, mul_inv_cancel₀ hpos, one_mul]

/-- The conditional output of a measured algorithm with positive success mass has unit trace. -/
theorem corr_one_conditionalDensity {K E X L : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] [FiniteDimensional ℂ E] {O : L → X → K →L[ℂ] K} (M : Measured O E)
    (x : X) (φ : K) (hpos : M.successMass x φ ≠ 0) :
    LinearSystemLowerBound.corr 1 (M.conditionalDensity x φ) = 1 := by
  rw [Measured.conditionalDensity, ← Complex.ofReal_inv, LinearSystemLowerBound.corr_smul_real,
    corr_one_successDensity, inv_mul_cancel₀ hpos]

/-- **Heralded accuracy gives a read probability**: a measured algorithm that succeeds with
probability at least `p₀` on the input `φ` and whose conditional output is within trace distance
`ε₀ ≤ 1` of `|m⟩`, with `p₀ (1 - ε₀) > 0`, reads `m` jointly with the herald with probability at
least `p₀ (1 - ε₀)`. -/
theorem le_readProb_of_heralded {N : ℕ} {K E G X L : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] [FiniteDimensional ℂ E] [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [CompleteSpace G] {O : L → X → K →L[ℂ] K} (M : Measured O E) (x : X) (φ : K)
    (e : E →L[ℂ] SysGarb (Fin N) G) (he : e† ∘L e = 1) (m : Fin N) {p₀ ε₀ : ℝ}
    (hε₀1 : ε₀ ≤ 1) (hp : 0 < p₀ * (1 - ε₀)) (hmass : p₀ ≤ M.successMass x φ)
    (hacc : DensityAccurate e (M.conditionalDensity x φ) (EuclideanSpace.single m (1 : ℂ)) ε₀) :
    p₀ * (1 - ε₀) ≤ readProb e m (M.successDensity x φ) := by
  have h1 : 0 ≤ 1 - ε₀ := by linarith
  have hp0 : 0 < p₀ := by
    by_contra h
    push Not at h
    nlinarith
  have hpos : M.successMass x φ ≠ 0 := (hp0.trans_le hmass).ne'
  have hr := one_sub_le_readProb e he m _ (corr_one_conditionalDensity M x φ hpos) hacc
  rw [readProb_successDensity M x φ e m hpos]
  exact mul_le_mul hmass hr h1 (hp0.le.trans hmass)

end

end DeferredMeasurementLowerBounds.Corollaries
