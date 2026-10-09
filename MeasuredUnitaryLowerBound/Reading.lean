import MeasuredUnitaryLowerBound.Global.Reads
import AdaptiveUnitaryLowerBound.Correlation
import DeferredMeasurementLowerBounds.Corollaries.UnitaryReadout
import DeferredMeasurementLowerBounds.Model.Embed

set_option autoImplicit false

/-!
# Read values of accurate outputs

The read values of the endpoint search bound (`Global.tree_count_ge_of_reads`) for the
reduction of Corollary `hs:cor:unitary` of the manuscript (lines 1711-1718: `U_m |0⟩ = |m⟩`):
the effect `R_y` reads the value `y` of the system register through an isometry
`e : E → ℂ^N ⊗ G`, so `r(x, y)` is the probability
`DeferredMeasurementLowerBounds.Corollaries.readProb e y` of reading `y` jointly with the success
herald on instance `x`.

* `sum_outObs_pure`, `sum_readProb`: the effects sum to the identity, so the read values of an
  output sum to its trace `corr 1 ρ`.
* `norm_outObs_pure_sub_le`: `‖R_x - R_{x'}‖ ≤ 1` (the readout of the pair observable
  `AdaptiveUnitaryLowerBound.Observable.pairObs`).
* `corr_one_successDensity_tree`: the heralded output of an adaptive protocol of unitary runs
  has trace its success probability (through `DeferredMeasurementLowerBounds.Model.ofTree`).
* `tree_read_bound`, `measured_read_bound`: success probability at least `s₀ > 0` and
  conditional output within trace distance `ε₀ ≤ 1/2` of `|x⟩` give
  `N r(x, x) - ∑_y r(x, y) ≥ s₀ (N (1 - ε₀) - 1) ≥ 0`.

At `ε₀ = 1/2` the right side is `s₀ (N/2 - 1)`, positive for `N ≥ 3`.
-/

namespace MeasuredUnitaryLowerBound.Reading

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.Readout
open SparseLinearSystems.Protocol ContinuousLinearMap
open AdaptiveHamiltonianLowerBound (DensityAccurate)
open LinearSystemLowerBound (corr)
open DeferredMeasurementLowerBounds.Corollaries (readProb)
open DeferredMeasurementLowerBounds.Model (Measured)
open scoped InnerProduct InnerProductSpace

variable {E W Fl L G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
  [NormedAddCommGroup Fl] [InnerProductSpace ℂ Fl] [CompleteSpace Fl]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

omit [CompleteSpace G] in
/-- The lift `M ⊗ 1_G` is additive in the system observable. -/
theorem liftObs_add {N : ℕ} (A B : EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N)) :
    (liftObs (A + B) : SysGarb (Fin N) G →L[ℂ] SysGarb (Fin N) G) = liftObs A + liftObs B := by
  ext Φ i
  simp [liftObs_apply, add_smul, Finset.sum_add_distrib]

omit [CompleteSpace G] in
/-- The lift of the identity is the identity. -/
theorem liftObs_one {N : ℕ} :
    (liftObs (1 : EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N)) :
      SysGarb (Fin N) G →L[ℂ] SysGarb (Fin N) G) = 1 := by
  ext Φ i
  rw [liftObs_apply]
  simp

/-- The workspace readout `outObs e` is additive. -/
theorem outObs_add {N : ℕ} (e : E →L[ℂ] SysGarb (Fin N) G)
    (A B : EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N)) :
    outObs e (A + B) = outObs e A + outObs e B := by
  simp only [outObs, liftObs_add, add_comp, comp_add]

/-- The workspace readout `outObs e` as an additive map. -/
def outObsHom {N : ℕ} (e : E →L[ℂ] SysGarb (Fin N) G) :
    (EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N)) →+ (E →L[ℂ] E) :=
  AddMonoidHom.mk' (outObs e) (outObs_add e)

/-- The workspace readout commutes with finite sums. -/
theorem outObs_sum {N : ℕ} (e : E →L[ℂ] SysGarb (Fin N) G) {ι : Type*} (s : Finset ι)
    (A : ι → EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N)) :
    outObs e (∑ i ∈ s, A i) = ∑ i ∈ s, outObs e (A i) :=
  map_sum (outObsHom e) A s

/-- The workspace readout commutes with differences. -/
theorem outObs_sub {N : ℕ} (e : E →L[ℂ] SysGarb (Fin N) G)
    (A B : EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N)) :
    outObs e (A - B) = outObs e A - outObs e B :=
  map_sub (outObsHom e) A B

/-- For an isometry `e`, the readout of the identity is the identity. -/
theorem outObs_one {N : ℕ} (e : E →L[ℂ] SysGarb (Fin N) G) (he : e† ∘L e = 1) :
    outObs e 1 = 1 := by
  rw [outObs, liftObs_one, one_def, id_comp, he]

/-- The rank-one projections onto the basis vectors sum to the identity:
`∑_y |y⟩⟨y| = 1`. -/
theorem sum_pure_single (N : ℕ) :
    ∑ y : Fin N, ODEMixedOutput.pureOperator (EuclideanSpace.single y (1 : ℂ)) = 1 := by
  refine ContinuousLinearMap.ext fun v => ?_
  rw [_root_.sum_apply, one_apply_eq_self]
  conv_rhs => rw [← (EuclideanSpace.basisFun (Fin N) ℂ).sum_repr' v]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp [ODEMixedOutput.pureOperator, InnerProductSpace.rankOne_apply]

omit [CompleteSpace E] in
/-- The correlation is additive in its first argument. -/
theorem corr_add_left (A B ρ : E →L[ℂ] E) : corr (A + B) ρ = corr A ρ + corr B ρ := by
  simp only [corr, add_comp, ContinuousLinearMap.toLinearMap_add, map_add, Complex.add_re]

omit [CompleteSpace E] in
/-- The correlation commutes with finite sums in its first argument. -/
theorem corr_sum_left {ι : Type*} (s : Finset ι) (A : ι → E →L[ℂ] E) (ρ : E →L[ℂ] E) :
    corr (∑ i ∈ s, A i) ρ = ∑ i ∈ s, corr (A i) ρ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [corr]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, corr_add_left, ih]

/-- **The read effects sum to the identity**: for an isometry `e` into system ⊗ garbage,
`∑_y outObs e |y⟩⟨y| = 1`. -/
theorem sum_outObs_pure {N : ℕ} (e : E →L[ℂ] SysGarb (Fin N) G) (he : e† ∘L e = 1) :
    ∑ y : Fin N, outObs e (ODEMixedOutput.pureOperator (EuclideanSpace.single y (1 : ℂ))) = 1 := by
  rw [← outObs_sum, sum_pure_single, outObs_one e he]

/-- **The read values sum to the trace**: `∑_y readProb e y ρ = corr 1 ρ`. -/
theorem sum_readProb {N : ℕ} (e : E →L[ℂ] SysGarb (Fin N) G) (he : e† ∘L e = 1)
    (ρ : E →L[ℂ] E) : ∑ y : Fin N, readProb e y ρ = corr 1 ρ := by
  have h := corr_sum_left Finset.univ
    (fun y : Fin N => outObs e (ODEMixedOutput.pureOperator (EuclideanSpace.single y (1 : ℂ)))) ρ
  rw [sum_outObs_pure e he] at h
  exact h.symm

/-- **Two read effects differ by a contraction**: for an isometry `e`,
`‖outObs e |x⟩⟨x| - outObs e |x'⟩⟨x'|‖ ≤ 1`; this is
`AdaptiveUnitaryLowerBound.Correlation.norm_outObs_pairObs_le` restated for read effects. -/
theorem norm_outObs_pure_sub_le {N : ℕ} (e : E →L[ℂ] SysGarb (Fin N) G) (he : e† ∘L e = 1)
    (x x' : Fin N) :
    ‖outObs e (ODEMixedOutput.pureOperator (EuclideanSpace.single x (1 : ℂ))) -
      outObs e (ODEMixedOutput.pureOperator (EuclideanSpace.single x' (1 : ℂ)))‖ ≤ 1 := by
  rw [← outObs_sub]
  exact AdaptiveUnitaryLowerBound.Correlation.norm_outObs_pairObs_le e he x x'

/-- **The trace of the heralded output of an adaptive protocol** is its success probability,
for unitary runs on finite-dimensional spaces. -/
theorem corr_one_successDensity_tree [FiniteDimensional ℂ W] [FiniteDimensional ℂ E] {X : Type*}
    {O : L → X → W →L[ℂ] W} (hO : ∀ l x, OracleCircuit.IsUnitary (O l x)) (T : Tree O Fl E)
    (x : X) : corr 1 (T.successDensity x) = T.successMass x := by
  have key : ∀ φ : W, ‖φ‖ = 1 → corr 1 (T.successDensity x) = T.successMass x :=
    fun φ hφ => by
      rw [← DeferredMeasurementLowerBounds.Model.successDensity_ofTree hO T x hφ,
        DeferredMeasurementLowerBounds.Corollaries.corr_one_successDensity,
        DeferredMeasurementLowerBounds.Model.successMass_ofTree hO T x hφ]
  cases T with
  | test t s f => exact key t.seed t.seed_unit
  | final p =>
    cases p with
    | abort =>
      simp [Tree.successDensity, Tree.successMass, Tree.expect,
        ODERepeatProtocol.Protocol.successMass, ODERepeatProtocol.Protocol.failureMass,
        ODERepeatProtocol.Protocol.successDensity, LinearSystemLowerBound.corr_zero]
    | freshTrial t k => exact key t.seed t.seed_unit

/-- **Read values of an accurate adaptive output.** For unitary runs on finite-dimensional
spaces, if the protocol succeeds on instance `x` with probability at least `s₀ > 0` and its
conditional output, read through the isometry `e`, is within trace distance `ε₀ ≤ 1/2` of `|x⟩`,
then `s₀ (N (1 - ε₀) - 1) ≤ N r(x, x) - ∑_y r(x, y)` with `r(x, y) = readProb e y ρ_x`. -/
theorem tree_read_bound [FiniteDimensional ℂ W] [FiniteDimensional ℂ E] {N : ℕ} (hN : 2 ≤ N)
    {O : L → Fin N → W →L[ℂ] W} (hO : ∀ l x, OracleCircuit.IsUnitary (O l x)) (T : Tree O Fl E)
    (e : E →L[ℂ] SysGarb (Fin N) G) (he : e† ∘L e = 1) {s₀ ε₀ : ℝ} (hs₀ : 0 < s₀)
    (hε₀ : ε₀ ≤ 1 / 2) (x : Fin N) (hsucc : s₀ ≤ T.successMass x)
    (hacc : DensityAccurate e (T.conditionalDensity x) (EuclideanSpace.single x 1) ε₀) :
    s₀ * ((N : ℝ) * (1 - ε₀) - 1) ≤
      (N : ℝ) * readProb e x (T.successDensity x) - ∑ y, readProb e y (T.successDensity x) := by
  have ht0 : 0 < T.successMass x := lt_of_lt_of_le hs₀ hsucc
  have hsd : T.successDensity x = ((T.successMass x : ℝ) : ℂ) • T.conditionalDensity x := by
    rw [Tree.conditionalDensity, smul_smul]
    have : ((T.successMass x : ℝ) : ℂ) * ((T.successMass x : ℂ))⁻¹ = 1 := by
      have : (T.successMass x : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
      field_simp
    rw [this, one_smul]
  have hc1 : corr 1 (T.conditionalDensity x) = 1 := by
    rw [Tree.conditionalDensity, ← Complex.ofReal_inv, LinearSystemLowerBound.corr_smul_real,
      corr_one_successDensity_tree hO T x, inv_mul_cancel₀ ht0.ne']
  have h1 := DeferredMeasurementLowerBounds.Corollaries.one_sub_le_readProb e he x _ hc1 hacc
  have hread : readProb e x (T.successDensity x) =
      T.successMass x * readProb e x (T.conditionalDensity x) := by
    rw [hsd]
    exact LinearSystemLowerBound.corr_smul_real _ _ _
  have hsum : ∑ y, readProb e y (T.successDensity x) = T.successMass x := by
    rw [sum_readProb e he, corr_one_successDensity_tree hO T x]
  rw [hsum, hread]
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hP : 0 ≤ (N : ℝ) * (1 - ε₀) - 1 := by nlinarith
  have h2 := mul_le_mul_of_nonneg_left h1 ht0.le
  have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ N)
  nlinarith [mul_le_mul_of_nonneg_right hsucc hP]

/-- **Read values of an accurate measured output**: the bound of `tree_read_bound` for a
measured algorithm (`DeferredMeasurementLowerBounds.Model.Measured`) on the initial vector `φ`. -/
theorem measured_read_bound {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] [FiniteDimensional ℂ E] {N : ℕ} (hN : 2 ≤ N) {O : L → Fin N → K →L[ℂ] K}
    (M : Measured O E) (φ : K) (e : E →L[ℂ] SysGarb (Fin N) G) (he : e† ∘L e = 1)
    {s₀ ε₀ : ℝ} (hs₀ : 0 < s₀) (hε₀ : ε₀ ≤ 1 / 2) (x : Fin N) (hsucc : s₀ ≤ M.successMass x φ)
    (hacc : DensityAccurate e (M.conditionalDensity x φ) (EuclideanSpace.single x 1) ε₀) :
    s₀ * ((N : ℝ) * (1 - ε₀) - 1) ≤
      (N : ℝ) * readProb e x (M.successDensity x φ) -
        ∑ y, readProb e y (M.successDensity x φ) := by
  have ht0 : 0 < M.successMass x φ := lt_of_lt_of_le hs₀ hsucc
  have hc1 :=
    DeferredMeasurementLowerBounds.Corollaries.corr_one_conditionalDensity M x φ ht0.ne'
  have h1 := DeferredMeasurementLowerBounds.Corollaries.one_sub_le_readProb e he x _ hc1 hacc
  have hread :=
    DeferredMeasurementLowerBounds.Corollaries.readProb_successDensity M x φ e x ht0.ne'
  have hsum : ∑ y, readProb e y (M.successDensity x φ) = M.successMass x φ := by
    rw [sum_readProb e he, DeferredMeasurementLowerBounds.Corollaries.corr_one_successDensity]
  rw [hsum, hread]
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hP : 0 ≤ (N : ℝ) * (1 - ε₀) - 1 := by nlinarith
  have h2 := mul_le_mul_of_nonneg_left h1 ht0.le
  have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ N)
  nlinarith [mul_le_mul_of_nonneg_right hsucc hP]

end
end MeasuredUnitaryLowerBound.Reading
