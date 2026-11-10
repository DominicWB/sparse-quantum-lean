import ManuscriptConformance.ActualRuns
import ManuscriptConformance.ODETime

/-!
# Conformance: the successful runs for approximate source preparations

`ode_thm_time_approx` gives only the heralded mixed-output form for approximate source preparations
on clean work registers: a rare successful branch can be inaccurate although the aggregate state is
close, so `TrialsClose` (every trial with a nonzero success branch accurate) cannot hold in general.
This module gives the history-resolved statement that does hold for the actual implemented trials:

* `norm_unitDirection_sub_le`, `direction_close_of_near`: the direction of a vector within `η` of
  an accurate vector `u` is accurate up to `2 η / ‖u'‖`;
* `lowWeight_le`: in the four-attempt protocol with success at least `2/3`, the successful histories
  whose trial has success probability below `p₀` carry conditional weight at most `6 p₀`;
* `ApproxRuns`, `work_certificate_runs`, `work_approx_build_runs`,
  `work_approx_solver_nonneg_runs`, `work_approx_solver_nonneg_regular_runs`: the released
  construction of `CleanWorkODE` with, in addition, `ApproxRuns`: every actual trial whose selected
  output has norm above `η = 30 g' δ` (the per-trial perturbation of the released proof) has
  direction error at most `ε/500 + 2 η / ‖u'‖`;
* `ode_thm_time_approx_runs`: Theorem `ode:thm:time` for approximate source preparations with, for
  the same protocol, the ensemble of successful histories, the accuracy of every history whose trial
  has success probability at least `p₀ > η²` (direction error `ε/500 + 2 η/√p₀`), and conditional
  weight at most `6 p₀` for the other histories.
-/

set_option autoImplicit false

namespace ManuscriptConformance

noncomputable section
open ContinuousLinearMap SparseHamiltonian NativeSparseBlockEncoding OracleCircuit Set
open ODEStateNormalization (unitDirection)
open scoped InnerProduct InnerProductSpace

set_option maxRecDepth 4096
set_option synthInstance.maxSize 8192

/-! ### Directions of nearby vectors -/

section Directions

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The directions of two vectors differ by at most twice their distance over the norm of the
first. -/
theorem norm_unitDirection_sub_le (a b : E) (ha : a ≠ 0) :
    ‖unitDirection a - unitDirection b‖ ≤ 2 * ‖a - b‖ / ‖a‖ := by
  have hr : 0 < ‖a‖ := norm_pos_iff.mpr ha
  unfold unitDirection
  have e : ‖a‖⁻¹ • a - ‖b‖⁻¹ • b = ‖a‖⁻¹ • (a - b) + (‖a‖⁻¹ - ‖b‖⁻¹) • b := by
    rw [smul_sub, sub_smul]
    abel
  rw [e]
  have h1 : ‖‖a‖⁻¹ • (a - b)‖ = ‖a - b‖ / ‖a‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr), div_eq_inv_mul]
  have h2 : ‖(‖a‖⁻¹ - ‖b‖⁻¹) • b‖ ≤ ‖a - b‖ / ‖a‖ := by
    by_cases hb : b = 0
    · subst hb
      simp only [norm_zero, inv_zero, sub_zero, smul_zero]
      positivity
    · have hs : 0 < ‖b‖ := norm_pos_iff.mpr hb
      rw [norm_smul, Real.norm_eq_abs]
      have e2 : (‖a‖⁻¹ - ‖b‖⁻¹) = (‖b‖ - ‖a‖) / (‖a‖ * ‖b‖) := by
        field_simp
      have hab : |‖b‖ - ‖a‖| ≤ ‖a - b‖ :=
        (abs_norm_sub_norm_le b a).trans (le_of_eq (norm_sub_rev b a))
      rw [e2, abs_div, abs_of_pos (mul_pos hr hs)]
      calc |‖b‖ - ‖a‖| / (‖a‖ * ‖b‖) * ‖b‖ = |‖b‖ - ‖a‖| / ‖a‖ := by
            field_simp
        _ ≤ ‖a - b‖ / ‖a‖ := div_le_div_of_nonneg_right hab hr.le
  calc ‖‖a‖⁻¹ • (a - b) + (‖a‖⁻¹ - ‖b‖⁻¹) • b‖
      ≤ ‖‖a‖⁻¹ • (a - b)‖ + ‖(‖a‖⁻¹ - ‖b‖⁻¹) • b‖ := norm_add_le _ _
    _ ≤ ‖a - b‖ / ‖a‖ + ‖a - b‖ / ‖a‖ := by rw [h1]; linarith [h2]
    _ = 2 * ‖a - b‖ / ‖a‖ := by ring

/-- **A vector near an accurate vector is accurate**: if `‖u' - u‖ ≤ η < ‖u'‖` and the direction
of `u` (when `u ≠ 0`) is within `δ` of `v` up to a phase, the direction of `u'` is within
`δ + 2 η / ‖u'‖`. -/
theorem direction_close_of_near {u u' v : E} {δ η : ℝ} (hη : ‖u' - u‖ ≤ η)
    (hdir : u ≠ 0 → ∃ ω : ℂ, ‖ω‖ = 1 ∧ ‖ω • unitDirection u - v‖ ≤ δ) (hu' : η < ‖u'‖) :
    ∃ ω : ℂ, ‖ω‖ = 1 ∧ ‖ω • unitDirection u' - v‖ ≤ δ + 2 * η / ‖u'‖ := by
  have hη0 : 0 ≤ η := (norm_nonneg _).trans hη
  have hu'0 : u' ≠ 0 := by
    intro h
    rw [h, norm_zero] at hu'
    linarith
  have hpos : 0 < ‖u'‖ := norm_pos_iff.mpr hu'0
  have hu0 : u ≠ 0 := by
    intro h
    rw [h, sub_zero] at hη
    linarith
  obtain ⟨ω, hω, hle⟩ := hdir hu0
  refine ⟨ω, hω, ?_⟩
  have hd := norm_unitDirection_sub_le u' u hu'0
  have e : ω • unitDirection u' - v =
      ω • (unitDirection u' - unitDirection u) + (ω • unitDirection u - v) := by
    rw [smul_sub]
    abel
  calc ‖ω • unitDirection u' - v‖
      = ‖ω • (unitDirection u' - unitDirection u) + (ω • unitDirection u - v)‖ := by rw [e]
    _ ≤ ‖ω • (unitDirection u' - unitDirection u)‖ + ‖ω • unitDirection u - v‖ :=
        norm_add_le _ _
    _ = ‖unitDirection u' - unitDirection u‖ + ‖ω • unitDirection u - v‖ := by
        rw [norm_smul, hω, one_mul]
    _ ≤ 2 * ‖u' - u‖ / ‖u'‖ + δ := add_le_add hd hle
    _ ≤ 2 * η / ‖u'‖ + δ := by
        gcongr
    _ = δ + 2 * η / ‖u'‖ := by ring

end Directions

/-! ### The weight of the low-probability histories -/

section Threshold

/-- **The low-probability trials carry little conditional weight**: in the four-attempt protocol
with success probability at least `2/3`, the successful histories `(i, j)` whose trial `j` has
success probability below `p₀` have total conditional weight at most `6 p₀`. -/
theorem lowWeight_le {M : ℕ} (p : Fin M → ℝ) (hp : ∀ j, 0 ≤ p j) (hp1 : ∀ j, p j ≤ 1)
    (hS : 2 / 3 ≤ ODERepeatProbability.successProbability p) {p₀ : ℝ} (hp₀ : 0 ≤ p₀) :
    ∑ b ∈ Finset.univ.filter (fun b : Fin 4 × Fin M => p b.2 < p₀),
      ODERepeatProbability.conditionalWeight p b ≤ 6 * p₀ := by
  classical
  have hMpos : 0 < M := by
    rcases Nat.eq_zero_or_pos M with h | h
    · subst h
      have : ODERepeatProbability.successProbability p = 0 := by
        simp [ODERepeatProbability.successProbability]
      linarith
    · exact h
  have hMr : (0 : ℝ) < M := by exact_mod_cast hMpos
  have hm0 : 0 ≤ ODERepeatProbability.mean p := ODERepeatProbability.mean_nonneg p hp
  have hm1 : ODERepeatProbability.mean p ≤ 1 := ODERepeatProbability.mean_le_one p hMpos hp1
  set c := 1 - ODERepeatProbability.mean p with hc
  have hc0 : 0 ≤ c := by rw [hc]; linarith
  have hc1 : c ≤ 1 := by rw [hc]; linarith
  have hSeq : ODERepeatProbability.successProbability p =
      ODERepeatProbability.mean p * (1 + c + c ^ 2 + c ^ 3) := by
    unfold ODERepeatProbability.successProbability
    simp only [ODERepeatProbability.firstSuccessWeight_sum, Fin.sum_univ_four]
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one]
    have h3 : ((3 : Fin 4) : ℕ) = 3 := rfl
    rw [h3]
    ring
  have hSpos : 0 < ODERepeatProbability.successProbability p := by linarith
  have hgeo : 1 + c + c ^ 2 + c ^ 3 ≤ 4 := by
    have := pow_le_one₀ hc0 hc1 (n := 2)
    have := pow_le_one₀ hc0 hc1 (n := 3)
    linarith
  have hgeo0 : 0 < 1 + c + c ^ 2 + c ^ 3 := by positivity
  have hmean : (1 : ℝ) / 6 ≤ ODERepeatProbability.mean p := by
    have : ODERepeatProbability.successProbability p ≤ 4 * ODERepeatProbability.mean p := by
      rw [hSeq]
      nlinarith
    linarith
  have hmpos : 0 < ODERepeatProbability.mean p := by linarith
  -- each low-probability history is bounded by its weight at probability `p₀`
  have hterm : ∀ b ∈ Finset.univ.filter (fun b : Fin 4 × Fin M => p b.2 < p₀),
      ODERepeatProbability.conditionalWeight p b ≤
        c ^ (b.1 : ℕ) * p₀ / M / ODERepeatProbability.successProbability p := by
    intro b hb
    have hlt : p b.2 < p₀ := (Finset.mem_filter.mp hb).2
    unfold ODERepeatProbability.conditionalWeight
    rw [ODERepeatProbability.firstSuccessWeight_eq]
    have hcr : 0 ≤ c ^ (b.1 : ℕ) := pow_nonneg hc0 _
    gcongr
  have hnonneg : ∀ b ∈ (Finset.univ : Finset (Fin 4 × Fin M)),
      0 ≤ c ^ (b.1 : ℕ) * p₀ / M / ODERepeatProbability.successProbability p := by
    intro b _
    have : 0 ≤ c ^ (b.1 : ℕ) := pow_nonneg hc0 _
    positivity
  have hall : ∑ b : Fin 4 × Fin M,
      c ^ (b.1 : ℕ) * p₀ / M / ODERepeatProbability.successProbability p =
        p₀ * (1 + c + c ^ 2 + c ^ 3) / ODERepeatProbability.successProbability p := by
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Fin.sum_univ_four]
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one]
    have h3 : ((3 : Fin 4) : ℕ) = 3 := rfl
    rw [h3]
    field_simp
  calc ∑ b ∈ Finset.univ.filter (fun b : Fin 4 × Fin M => p b.2 < p₀),
        ODERepeatProbability.conditionalWeight p b
      ≤ ∑ b ∈ Finset.univ.filter (fun b : Fin 4 × Fin M => p b.2 < p₀),
          c ^ (b.1 : ℕ) * p₀ / M / ODERepeatProbability.successProbability p :=
        Finset.sum_le_sum hterm
    _ ≤ ∑ b : Fin 4 × Fin M,
          c ^ (b.1 : ℕ) * p₀ / M / ODERepeatProbability.successProbability p :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun b hb _ => hnonneg b hb)
    _ = p₀ * (1 + c + c ^ 2 + c ^ 3) / ODERepeatProbability.successProbability p := hall
    _ = p₀ / ODERepeatProbability.mean p := by
        rw [hSeq]
        field_simp
    _ ≤ 6 * p₀ := by
        rw [div_le_iff₀ hmpos]
        nlinarith

end Threshold

end

end ManuscriptConformance

/-! ### The released construction with the accuracy of the runs -/

namespace SparseHamiltonian.CleanWorkODE

noncomputable section
open ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding Set MeasureTheory
open TimeDependentExtensions SparseHamiltonian.GeneralSourceExtensions
open SparseHamiltonian.RepresentedSampleODE
open SparseHamiltonian.TimeDependentODE (Accretive SolvesODE ratio accuracy radius precision
  lipschitz Index lchsCoefficients)
open SparseHamiltonian.GeneralSourceODE (SourceCall sources phases phases_norm)
open SparseHamiltonian.GeneralSourceExtensions.Mesh (meshScale sampleError refinementError
  IsMeshPropagator lchsCoefficients_mass)
open scoped BigOperators InnerProduct
set_option maxRecDepth 4096
set_option synthInstance.maxSize 8192

variable {X n Z W : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] [Fintype W] [DecidableEq W] {s M : ℕ}


open SparseHamiltonian.GeneralSourceExtensions (ApproxCertificate norm_adjoint_apply_le)
open ODEStateNormalization (unitDirection unitDirection_norm)

/-- **Every actual trial above the perturbation is accurate**: every trial whose selected output has
norm above `η` has direction error at most `ε₀ + 2 η / ‖u'‖`, `u'` its selected output. -/
def ApproxRuns {K E L X' : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] {O : L → X' → K →L[ℂ] K}
    (t : ODERepeatProtocol.TrialFamily O E) (x : X') (target : E) (η ε₀ : ℝ) : Prop :=
  ∀ j : Fin t.choices, η < ‖t.amplitude x j‖ →
    ∃ ω : ℂ, ‖ω‖ = 1 ∧ ‖ω • t.outputDirection x j - unitDirection target‖ ≤
      ε₀ + 2 * η / ‖t.amplitude x j‖

section CertificateRuns

variable {P R RW : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [FiniteDimensional ℂ P]
  [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
  [NormedAddCommGroup RW] [InnerProductSpace ℂ RW] [CompleteSpace RW]

set_option maxHeartbeats 1000000 in
/-- **The per-trial accuracy of `work_certificate`**: under its hypotheses, every actual trial over
the oracles with temporary work registers whose selected output has norm above `30 g δ` has
direction error at most `ε/500 + 2 (30 g δ)/‖u'‖` (the per-trial perturbation of the released
proof and the direction error of the exact trial). -/
theorem work_certificate_runs (e : WorkEmbedding R RW) {L X₁ X₂ : Type*}
    {O : (L ⊕ Bool) → X₁ → R →L[ℂ] R}
    {O₁ : NativeSparseBlockEncoding.Query ⊕ SourceCall → X₁ → R →L[ℂ] R}
    {O₂ : NativeSparseBlockEncoding.Query ⊕ SourceCall → X₂ → RW →L[ℂ] RW}
    {q : ℕ → MultiOracleCircuit.Program O} {M : ℕ} {ψ : R} {F : P →L[ℂ] R} {x₁ : X₁}
    {target : P} {s Θ ell g ε : ℝ}
    (hCert : ODECompleteTrial.Certificate q M ψ F x₁ target s Θ ell g ε)
    (q₁ : ℕ → MultiOracleCircuit.Program O₁) (hM : 0 < M) (hψ : ‖ψ‖ = 1) (hF : F† ∘L F = 1)
    (hEval : ∀ j, (q₁ j).eval x₁ = (q j).eval x₁)
    (_hMatrix : ∀ j, (q₁ j).cost GeneralSourceODE.Oracles.matrixCalls =
      (q j).cost (ODESourceQueryBudget.matrixWeight (fun _ => 1)))
    (_hWeight : ∀ j, (q₁ j).cost (GeneralSourceODE.Oracles.calls .weight) =
      (q j).cost (ODESourceQueryBudget.sourceWeight false))
    (_hLoad : ∀ j, (q₁ j).cost (GeneralSourceODE.Oracles.calls .load) =
      (q j).cost (ODESourceQueryBudget.sourceWeight false))
    (_hUnweight : ∀ j, (q₁ j).cost (GeneralSourceODE.Oracles.calls .unweight) =
      (q j).cost (ODESourceQueryBudget.sourceWeight true))
    (hSource : ∀ j, (q₁ j).cost GeneralSourceODE.Oracles.sourceCalls =
      2 * (q j).cost (ODESourceQueryBudget.sourceWeight false) +
        (q j).cost (ODESourceQueryBudget.sourceWeight true))
    (hO₁ : ∀ l y, IsUnitary (O₁ l y)) (hO₂ : ∀ l y, IsUnitary (O₂ l y))
    (x₂ : X₂) {δ : ℝ} (hδ : 0 ≤ δ)
    (hclean : ∀ l, CleanErr e.clean (O₂ l x₂) (O₁ l x₁)
      (δ * GeneralSourceODE.Oracles.sourceCalls l))
    (_hδ1 : 30 * g * δ ≤ 1 / 400) (_hδε : 30 * g * δ ≤ ε / 20) (_hTarget : target ≠ 0) :
    ApproxRuns
      (ODERepeatProtocol.ofCircuits (fun j => workRecast (O' := O₂) e (q₁ j)) M hM
        (e.clean ψ) (e.clean_unit hψ) (e.clean ∘L F) (e.output_isometry hF)) x₂
      target (30 * g * δ) (ε / 500) := by
  have hTrial := hCert.trial
  let q₂ : ℕ → MultiOracleCircuit.Program O₂ := fun j => workRecast (O' := O₂) e (q₁ j)
  have hcost₂ : ∀ (w : NativeSparseBlockEncoding.Query ⊕ SourceCall → ℕ) j,
      (q₂ j).cost w = (q₁ j).cost w := fun w j => cost_workRecast e (q₁ j) w
  -- Per-trial perturbation on clean work registers.
  have hclose : ∀ j, j < M →
      ‖(q₂ j).eval x₂ (e.clean ψ) - e.clean ((q₁ j).eval x₁ ψ)‖ ≤ 30 * g * δ := by
    intro j hj
    have h := eval_workRecast_clean (O' := O₂) e (q₁ j) hO₁ hO₂ x₁ x₂ hδ
      GeneralSourceODE.Oracles.sourceCalls hclean ψ
    rw [hψ, mul_one] at h
    refine h.trans ?_
    have hc : ((q₁ j).cost GeneralSourceODE.Oracles.sourceCalls : ℝ) ≤ 30 * g := by
      rw [hSource j]
      push_cast
      have h1 := hTrial.source_queries j hj false
      have h2 := hTrial.source_queries j hj true
      linarith
    calc δ * ((q₁ j).cost GeneralSourceODE.Oracles.sourceCalls : ℝ) ≤ δ * (30 * g) :=
          mul_le_mul_of_nonneg_left hc hδ
      _ = 30 * g * δ := by ring
  have hU₁ : ∀ j, IsUnitary ((q₁ j).eval x₁) := fun j => (q₁ j).eval_unitary hO₁ x₁
  have hU₂ : ∀ j, IsUnitary ((q₂ j).eval x₂) := fun j => (q₂ j).eval_unitary hO₂ x₂
  have hmean : (1 : ℝ) / 4 ≤ (∑ j ∈ Finset.range M,
      ‖ODEHeraldedSuccess.successProjector F ((q₁ j).eval x₁ ψ)‖ ^ 2) / (M : ℝ) := by
    simp only [hEval]
    exact hTrial.mean_success
  have hdir : ∀ j, j < M → (F†) ((q₁ j).eval x₁ ψ) ≠ 0 →
      ∃ ω : ℂ, ‖ω‖ = 1 ∧ ‖ω • unitDirection ((F†) ((q₁ j).eval x₁ ψ)) -
        unitDirection target‖ ≤ ε / 500 := by
    intro j hj hz
    rw [hEval j] at hz ⊢
    exact hTrial.direction_error j hj hz
  intro j hj
  have hamp : ‖((e.clean ∘L F)†) ((q₂ j.val).eval x₂ (e.clean ψ)) -
      (F†) ((q₁ j.val).eval x₁ ψ)‖ ≤ 30 * g * δ := by
    have h1 : (F†) ((q₁ j.val).eval x₁ ψ) =
        ((e.clean ∘L F)†) (e.clean ((q₁ j.val).eval x₁ ψ)) := by
      rw [adjoint_comp, comp_apply, e.adjoint_clean]
    rw [h1, ← map_sub]
    exact (norm_adjoint_apply_le _ (e.output_isometry hF) _).trans (hclose j.val j.isLt)
  exact ManuscriptConformance.direction_close_of_near hamp (hdir j.val j.isLt) hj

end CertificateRuns

set_option maxHeartbeats 8000000 in
/-- `WorkApproxBudgetOutcome` with `ApproxRuns` for the trial family. -/
def WorkApproxRunsOutcome (D : Data (X × Fin M) n Z s) (t : ℕ → ℝ) (N : ℕ)
    (etaH etaD T gbar cq ε : ℝ) {m : ℕ} (v : Fin m → ℝ) (ω : Fin m → ℂ) (w₀ : W)
    (Pw : X → LabelW m W →L[ℂ] LabelW m W) (J : X → LoadW m n W →L[ℂ] LoadW m n W)
    (seed : EuclideanSpace ℂ n) (Q : ℝ) : Prop :=
  ∃ (d : ℕ) (tf : ODERepeatProtocol.TrialFamily
      (actualOracleW (ι := Index D T (cq * gbar) ε) D m N d Pw J) (EuclideanSpace ℂ n)),
    tf.choices = ODEGroverAverage.chosenIterations (ratio (cq * gbar)) ∧
    (∀ j y, IsUnitary ((tf.circuit j).eval y)) ∧
    ∀ (x : X) (P : GeneralSourceODE.Weights.LabelOp (Option (Fin m)))
      (L : Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) (δ : ℝ)
      (G : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
      (b : Fin M → ℝ → EuclideanSpace ℂ n) (sol : ℝ → EuclideanSpace ℂ n)
      (bv : Fin m → EuclideanSpace ℂ n)
      (U : ℝ → EuclideanSpace ℂ n → ℝ → EuclideanSpace ℂ n) (ζ : ℝ),
      IsUnitary P → (∀ a, IsUnitary (L a)) → 0 ≤ δ →
      CleanErr (cleanPi (V := ℂ) w₀) (Pw x) P δ →
      CleanErr (cleanPi (V := ℂ) w₀) (J x) (ctrlL L) δ →
      30 * ratio (cq * gbar) * δ ≤ 1 / 400 → 30 * ratio (cq * gbar) * δ ≤ ε / 20 →
      (∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), Accretive (G r u)) →
      (∀ r : Fin M, IntervalIntegrable (G r) volume (t r) (t ((r : ℕ) + 1))) →
      IsMeshPropagator G t T U →
      GeneralSourceODE.Compiled.WeightPrep P (sources (sol 0) bv ω) →
      (sol 0 ≠ 0 → L none seed = ODEStateNormalization.unitDirection (sol 0)) →
      (∀ i, ω i ≠ 0 → bv i ≠ 0 → L (some i) seed =
        ODEStateNormalization.unitDirection (bv i)) →
      ODESourceBranches.mass (sources (sol 0) bv ω) ≤ cq * meshScale sol b t →
      ‖sol T - U 0 (sol 0) T - ∑ i, ω i • U (v i) (bv i) T‖ ≤ ζ * meshScale sol b t →
      sol T ≠ 0 →
      meshScale sol b t ≤ gbar * ‖sol T‖ →
      RobustBudget D x t G T N cq gbar ε ζ →
      ApproxCertificate (ODERepeatProtocol.Protocol.repeatTrials tf 4) x (sol T) (s : ℝ)
        (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) (ratio (cq * gbar)) (accuracy ε))
        (ImprovedODEQueryBudget.logBudget (ratio (cq * gbar)) (accuracy ε))
        (ratio (cq * gbar)) ε ∧
      ((ODERepeatProtocol.Protocol.repeatTrials tf 4).worstCost
        GeneralSourceODE.Oracles.matrixCalls : ℝ) ≤ Q ∧
      ApproxRuns tf x (sol T) (30 * ratio (cq * gbar) * δ) (ε / 500)

set_option maxHeartbeats 8000000 in
/-- **`work_approx_build` with the accuracy of the runs** (`ApproxRuns` at `η = 30 g' δ`). -/
theorem work_approx_build_runs (D : Data (X × Fin M) n Z s) (hM : 0 < M) (t : ℕ → ℝ) (N : ℕ)
    (etaH etaD T gbar cq ε : ℝ) {m : ℕ} (v : Fin m → ℝ) (ω : Fin m → ℂ)
    (hT : 0 ≤ T) (hg : 1 ≤ gbar) (hcq : 1 ≤ cq) (hε : 0 < ε) (hεOne : ε ≤ 1) (w₀ : W)
    (Pw : X → LabelW m W →L[ℂ] LabelW m W) (hPw : ∀ x, IsUnitary (Pw x))
    (J : X → LoadW m n W →L[ℂ] LoadW m n W) (hJ : ∀ x, IsUnitary (J x))
    (seed : EuclideanSpace ℂ n) (hSeed : ‖seed‖ = 1) (d : ℕ)
    (E : GeneralSourceODE.Native.SourceSpace
        (Index (pullback D (Inst.input (X := X) (n := n) (m := m))) T (cq * gbar) ε) n m →L[ℂ]
      MeshNative.MatrixSpace
        (Index (pullback D (Inst.input (X := X) (n := n) (m := m))) T (cq * gbar) ε) n Z m M N d)
    (hE : E† ∘L E = 1)
    (q : ℕ → MultiOracleCircuit.Program
      (MeshNative.physicalOracle
        (ι := Index (pullback D (Inst.input (X := X) (n := n) (m := m))) T (cq * gbar) ε)
        (pullback D (Inst.input (X := X) (n := n) (m := m))) m N d Inst.weight Inst.loader
        (phases ω)))
    (hCert : ∀ (p : Inst X n m) (G : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
      (b : Fin M → ℝ → EuclideanSpace ℂ n) (sol : ℝ → EuclideanSpace ℂ n)
      (bv : Fin m → EuclideanSpace ℂ n)
      (U : ℝ → EuclideanSpace ℂ n → ℝ → EuclideanSpace ℂ n) (ζ : ℝ),
      (∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), Accretive (G r u)) →
      (∀ r : Fin M, IntervalIntegrable (G r) volume (t r) (t ((r : ℕ) + 1))) →
      IsMeshPropagator G t T U →
      GeneralSourceODE.Compiled.WeightPrep (Inst.weight p) (sources (sol 0) bv ω) →
      (sol 0 ≠ 0 → Inst.loader p none seed = ODEStateNormalization.unitDirection (sol 0)) →
      (∀ i, ω i ≠ 0 → bv i ≠ 0 → Inst.loader p (some i) seed =
        ODEStateNormalization.unitDirection (bv i)) →
      ODESourceBranches.mass (sources (sol 0) bv ω) ≤ cq * meshScale sol b t →
      ‖sol T - U 0 (sol 0) T - ∑ i, ω i • U (v i) (bv i) T‖ ≤ ζ * meshScale sol b t →
      sol T ≠ 0 →
      meshScale sol b t ≤ gbar * ‖sol T‖ →
      RobustBudget (pullback D (Inst.input (X := X) (n := n) (m := m))) p t G T N cq gbar ε ζ →
      ODECompleteTrial.Certificate q
        (ODEGroverAverage.chosenIterations (ratio (cq * gbar)))
        (MeshNative.input (pullback D (Inst.input (X := X) (n := n) (m := m))) hM (Sum.inr false)
          m N d (ODECompiledSource.seed E
            (GeneralSourceODE.Compiled.seedCoefficients
              (lchsCoefficients (pullback D (Inst.input (X := X) (n := n) (m := m))) T
                (cq * gbar) ε)) seed))
        (MeshNative.input (pullback D (Inst.input (X := X) (n := n) (m := m))) hM (Sum.inr false)
            m N d ∘L
          ODECompiledSource.output E
            (GeneralSourceODE.Compiled.seedCoefficients
              (lchsCoefficients (pullback D (Inst.input (X := X) (n := n) (m := m))) T
                (cq * gbar) ε)))
        p (sol T) (s : ℝ)
        (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) (ratio (cq * gbar)) (accuracy ε))
        (ImprovedODEQueryBudget.logBudget (ratio (cq * gbar)) (accuracy ε))
        (ratio (cq * gbar)) ε) :
    ∃ tf : ODERepeatProtocol.TrialFamily
        (actualOracleW (ι := Index D T (cq * gbar) ε) D m N d Pw J) (EuclideanSpace ℂ n),
      tf.choices = ODEGroverAverage.chosenIterations (ratio (cq * gbar)) ∧
      (∀ j y, IsUnitary ((tf.circuit j).eval y)) ∧
      (∀ j : Fin tf.choices, (tf.circuit j).cost GeneralSourceODE.Oracles.matrixCalls =
        (q j.val).cost (ODESourceQueryBudget.matrixWeight (fun _ => 1))) ∧
    ∀ (x : X) (P : GeneralSourceODE.Weights.LabelOp (Option (Fin m)))
      (L : Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) (δ : ℝ)
      (G : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
      (b : Fin M → ℝ → EuclideanSpace ℂ n) (sol : ℝ → EuclideanSpace ℂ n)
      (bv : Fin m → EuclideanSpace ℂ n)
      (U : ℝ → EuclideanSpace ℂ n → ℝ → EuclideanSpace ℂ n) (ζ : ℝ),
      IsUnitary P → (∀ a, IsUnitary (L a)) → 0 ≤ δ →
      CleanErr (cleanPi (V := ℂ) w₀) (Pw x) P δ →
      CleanErr (cleanPi (V := ℂ) w₀) (J x) (ctrlL L) δ →
      30 * ratio (cq * gbar) * δ ≤ 1 / 400 → 30 * ratio (cq * gbar) * δ ≤ ε / 20 →
      (∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), Accretive (G r u)) →
      (∀ r : Fin M, IntervalIntegrable (G r) volume (t r) (t ((r : ℕ) + 1))) →
      IsMeshPropagator G t T U →
      GeneralSourceODE.Compiled.WeightPrep P (sources (sol 0) bv ω) →
      (sol 0 ≠ 0 → L none seed = ODEStateNormalization.unitDirection (sol 0)) →
      (∀ i, ω i ≠ 0 → bv i ≠ 0 → L (some i) seed =
        ODEStateNormalization.unitDirection (bv i)) →
      ODESourceBranches.mass (sources (sol 0) bv ω) ≤ cq * meshScale sol b t →
      ‖sol T - U 0 (sol 0) T - ∑ i, ω i • U (v i) (bv i) T‖ ≤ ζ * meshScale sol b t →
      sol T ≠ 0 →
      meshScale sol b t ≤ gbar * ‖sol T‖ →
      RobustBudget D x t G T N cq gbar ε ζ →
      ApproxCertificate (ODERepeatProtocol.Protocol.repeatTrials tf 4) x (sol T) (s : ℝ)
        (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) (ratio (cq * gbar)) (accuracy ε))
        (ImprovedODEQueryBudget.logBudget (ratio (cq * gbar)) (accuracy ε))
        (ratio (cq * gbar)) ε ∧
      ApproxRuns tf x (sol T) (30 * ratio (cq * gbar) * δ) (ε / 500) := by
  let D' := (pullback D (Inst.input (X := X) (n := n) (m := m)))
  have hg1 : 1 ≤ ratio (cq * gbar) := by
    unfold ratio
    nlinarith
  obtain ⟨hMpos, -, -⟩ := ODEGroverAverage.chosenIterations_bounds (ratio (cq * gbar)) hg1
  have hcpos : 0 < ODECoherentLCU.coefficientMass (lchsCoefficients D' T (cq * gbar) ε) := by
    rw [lchsCoefficients_mass D' hT (cq * gbar) ε hg1 hε hεOne]
    norm_num
  have hψ := MeshNative.seed_unit D' hM (Sum.inr false) m N d E hE
    (lchsCoefficients D' T (cq * gbar) ε) hcpos seed hSeed
  have hF := MeshNative.output_isometry D' hM (Sum.inr false) m N d E hE
    (lchsCoefficients D' T (cq * gbar) ε) hcpos
  -- The family over the exact actual oracles of the instances.
  let q₁ := MeshOracles.actualTrials D' m N d Inst.weight Inst.loader (phases ω)
    (phases_norm ω) q
  have hEval : ∀ j y, (q₁ j).eval y = (q j).eval y := fun j y =>
    MultiOracleCircuit.Program.eval_substitute (q j) _
      (MeshOracles.implementation_eval D' m N d Inst.weight Inst.loader (phases ω)
        (phases_norm ω)) y
  have hO₁ := MeshOracles.actualOracle_unitary (ι := Index D' T (cq * gbar) ε) D' m N d
    (Inst.weight_unitary (X := X) (n := n) (m := m))
    (Inst.loader_unitary (X := X) (n := n) (m := m))
  have hO₂ := actualOracleW_unitary (ι := Index D T (cq * gbar) ε) D m N d hPw hJ
  have hCost : ∀ (w : Query ⊕ SourceCall → ℕ) (j : ℕ),
      (q₁ j).cost w = (q j).cost (fun l =>
        (MeshOracles.implementation D' m N d Inst.weight Inst.loader (phases ω)
          (phases_norm ω) l).cost w) :=
    fun w j => MultiOracleCircuit.Program.cost_substitute (q j) _ w
  have hMatrix : ∀ j, (q₁ j).cost GeneralSourceODE.Oracles.matrixCalls =
      (q j).cost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) := fun j => by
    rw [hCost]
    exact congrArg (q j).cost (funext (MeshOracles.implementation_matrix D' m N d _ _ _ _))
  -- The same syntax, with every fixed gate lifted to the work register, on the actual oracles
  -- with a work register.
  let q₂ : ℕ → MultiOracleCircuit.Program
      (actualOracleW (ι := Index D T (cq * gbar) ε) D m N d Pw J) :=
    fun j => workRecast (piWork w₀) (q₁ j)
  refine ⟨ODERepeatProtocol.ofCircuits q₂
    (ODEGroverAverage.chosenIterations (ratio (cq * gbar))) hMpos _
    ((piWork w₀).clean_unit hψ) _ ((piWork w₀).output_isometry hF), rfl,
    fun j y => (q₂ j.val).eval_unitary hO₂ y,
    fun j => (cost_workRecast _ _ _).trans (hMatrix j.val), ?_⟩
  intro x P L δ G b sol bv U ζ hP hL hδ hPc hJc hδ1 hδε hG hGint hU hW hLoad₀ hLoad hMassB
    hCertP hTarget hB hBudget
  let p : Inst X n m := Inst.mk x P L hP hL
  have hC := hCert p G b sol bv U ζ hG hGint hU hW hLoad₀ hLoad hMassB hCertP hTarget hB
    hBudget
  have hclean := actualOracleW_clean (ι := Index D T (cq * gbar) ε) D D' m N d w₀ Pw J
    Inst.weight Inst.loader x p
    (fun l => MeshOracles.actualOracle_pullback_matrix D (Inst.input (X := X) (n := n) (m := m))
      m N d (fun _ => 1) (fun _ _ => 1) Inst.weight Inst.loader l p) (hPw x) hP hδ hPc hJc
  have hc := work_certificate (piWork w₀) hC q₁ hMpos hψ hF (fun j => hEval j p) hMatrix
    (fun j => by
      rw [hCost]
      exact congrArg (q j).cost (funext (MeshOracles.implementation_weight D' m N d _ _ _ _)))
    (fun j => by
      rw [hCost]
      exact congrArg (q j).cost (funext (MeshOracles.implementation_load D' m N d _ _ _ _)))
    (fun j => by
      rw [hCost]
      exact congrArg (q j).cost (funext (MeshOracles.implementation_unweight D' m N d _ _ _ _)))
    (fun j => by
      rw [hCost, funext (MeshOracles.implementation_source D' m N d _ _ _ _),
        GeneralSourceODE.Oracles.cost_add, NativeHermitianDilation.cost_scale])
    hO₁ hO₂ x hδ hclean hδ1 hδε hTarget
  have hr := work_certificate_runs (piWork w₀) hC q₁ hMpos hψ hF (fun j => hEval j p) hMatrix
    (fun j => by
      rw [hCost]
      exact congrArg (q j).cost (funext (MeshOracles.implementation_weight D' m N d _ _ _ _)))
    (fun j => by
      rw [hCost]
      exact congrArg (q j).cost (funext (MeshOracles.implementation_load D' m N d _ _ _ _)))
    (fun j => by
      rw [hCost]
      exact congrArg (q j).cost (funext (MeshOracles.implementation_unweight D' m N d _ _ _ _)))
    (fun j => by
      rw [hCost, funext (MeshOracles.implementation_source D' m N d _ _ _ _),
        GeneralSourceODE.Oracles.cost_add, NativeHermitianDilation.cost_scale])
    hO₁ hO₂ x hδ hclean hδ1 hδε hTarget
  exact ⟨hc, hr⟩

set_option maxHeartbeats 8000000 in
/-- **`work_approx_solver_nonneg` with the accuracy of the runs.** -/
theorem work_approx_solver_nonneg_runs (D : Data (X × Fin M) n Z s) (hM : 0 < M) (t : ℕ → ℝ)
    {N : ℕ} (hN : 0 < N) (etaH etaD T gbar cq ε : ℝ) {m : ℕ} (v : Fin m → ℝ) (ω : Fin m → ℂ)
    (hH : 0 ≤ etaH) (hDiss : 0 ≤ etaD) (hT : 0 ≤ T) (hg : 1 ≤ gbar) (hcq : 1 ≤ cq)
    (hε : 0 < ε) (hεOne : ε ≤ 1) (hmesh : IsMesh t M T)
    (hClock : 8 * s * ((etaH + radius (cq * gbar) ε * etaD) * T) ≤ N)
    (hCayley : 3 * (Real.sqrt (2 * (s : ℝ)) *
      ((etaH + radius (cq * gbar) ε * etaD) * T)) ^ 3 ≤
        precision (cq * gbar) ε * (N : ℝ) ^ 2)
    (hv : ∀ i, v i ∈ Icc 0 T)
    (hrH : ∀ y i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix y) i j‖ ^ 2 ≤ etaH ^ 2)
    (hcH : ∀ y j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix y) i j‖ ^ 2 ≤ etaH ^ 2)
    (hrD : ∀ y i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix y) i j‖ ^ 2 ≤ etaD ^ 2)
    (hcD : ∀ y j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix y) i j‖ ^ 2 ≤ etaD ^ 2)
    (w₀ : W) (Pw : X → LabelW m W →L[ℂ] LabelW m W) (hPw : ∀ x, IsUnitary (Pw x))
    (J : X → LoadW m n W →L[ℂ] LoadW m n W) (hJ : ∀ x, IsUnitary (J x))
    (seed : EuclideanSpace ℂ n) (hSeed : ‖seed‖ = 1) :
    WorkApproxRunsOutcome D t N etaH etaD T gbar cq ε v ω w₀ Pw J seed
      (if T = 0 ∨ etaH + radius (cq * gbar) ε * etaD = 0 then 0 else
        1274019840 * ratio (cq * gbar) * ImprovedODEQueryBudget.queryShape (s : ℝ)
          (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) (ratio (cq * gbar)) (accuracy ε))
          (ImprovedODEQueryBudget.logBudget (ratio (cq * gbar)) (accuracy ε))) := by
  by_cases hZero : T = 0 ∨ etaH + radius (cq * gbar) ε * etaD = 0
  · rw [if_pos hZero]
    obtain ⟨d, E, hE, q, _hU, hCost, hCert⟩ := robust_zero_core
      (pullback D (Inst.input (X := X) (n := n) (m := m))) hM t hN etaH etaD T gbar cq ε v ω
      hH hDiss hT hZero hg hcq hε hεOne hmesh hv
      (fun y i => hrH (Inst.input y.1, y.2) i) (fun y i => hrD (Inst.input y.1, y.2) i)
      Inst.weight (Inst.weight_unitary (X := X) (n := n) (m := m))
      Inst.loader (Inst.loader_unitary (X := X) (n := n) (m := m)) seed hSeed
    obtain ⟨tf, hch, hU, hcost, hC⟩ := work_approx_build_runs D hM t N etaH etaD T gbar cq ε v ω hT
      hg hcq hε hεOne w₀ Pw hPw J hJ seed hSeed d E hE q hCert
    have h := ODERepeatProtocol.Protocol.repeat_worstCost_le tf 4
      GeneralSourceODE.Oracles.matrixCalls 0 (fun j => by rw [hcost j]; exact hCost j.val)
    rw [mul_zero] at h
    exact ⟨d, tf, hch, hU, fun x P L δ G b sol bv U ζ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
      h14 h15 h16 h17 h18 =>
        let hc := hC x P L δ G b sol bv U ζ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
          h16 h17 h18
        ⟨hc.1, h, hc.2⟩⟩
  · rw [if_neg hZero]
    have hg' : 1 ≤ ratio (cq * gbar) := by unfold ratio; nlinarith
    have hε' : 0 < accuracy ε := by unfold accuracy; linarith
    have hε'One : accuracy ε ≤ 1 := by unfold accuracy; linarith
    have hR : 0 ≤ radius (cq * gbar) ε :=
      ImprovedODEQueryBudget.radius_nonneg _ _ hg' hε' hε'One
    have hTpos : 0 < T := lt_of_le_of_ne hT (fun h => hZero (Or.inl h.symm))
    have hρ : 0 < etaH + radius (cq * gbar) ε * etaD :=
      lt_of_le_of_ne (add_nonneg hH (mul_nonneg hR hDiss)) (fun h => hZero (Or.inr h.symm))
    obtain ⟨d, E, hE, q, _hU, hCert⟩ := robust_propagated_solver
      (pullback D (Inst.input (X := X) (n := n) (m := m))) hM t hN etaH etaD T gbar cq ε v ω
      hH hDiss hTpos hg hcq hε hεOne hmesh hρ hClock hCayley hv
      (fun y i => hrH (Inst.input y.1, y.2) i) (fun y j => hcH (Inst.input y.1, y.2) j)
      (fun y i => hrD (Inst.input y.1, y.2) i) (fun y j => hcD (Inst.input y.1, y.2) j)
      Inst.weight (Inst.weight_unitary (X := X) (n := n) (m := m))
      Inst.loader (Inst.loader_unitary (X := X) (n := n) (m := m)) seed hSeed
    obtain ⟨tf, hch, hU, -, hC⟩ := work_approx_build_runs D hM t N etaH etaD T gbar cq ε v ω hT
      hg hcq hε hεOne w₀ Pw hPw J hJ seed hSeed d E hE q hCert
    exact ⟨d, tf, hch, hU, fun x P L δ G b sol bv U ζ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
      h14 h15 h16 h17 h18 =>
      let hc := hC x P L δ G b sol bv U ζ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
        h17 h18
      ⟨hc.1, hc.1.matrix_queries, hc.2⟩⟩

/-- `WorkRegularOutcome` with `ApproxRuns` for the trial family. -/
def WorkRegularRunsOutcome (D : Data (X × Fin M) n Z s) (t : ℕ → ℝ) (N : ℕ)
    (etaH etaD T gbar cq ε : ℝ) {m : ℕ} (v : Fin m → ℝ) (ω : Fin m → ℂ) (w₀ : W)
    (Pw : X → LabelW m W →L[ℂ] LabelW m W) (J : X → LoadW m n W →L[ℂ] LoadW m n W)
    (seed : EuclideanSpace ℂ n) (Q : ℝ) : Prop :=
  ∃ (d : ℕ) (tf : ODERepeatProtocol.TrialFamily
      (actualOracleW (ι := Index D T (cq * gbar) ε) D m N d Pw J) (EuclideanSpace ℂ n)),
    tf.choices = ODEGroverAverage.chosenIterations (ratio (cq * gbar)) ∧
    (∀ j y, IsUnitary ((tf.circuit j).eval y)) ∧
    ∀ (x : X) (P : GeneralSourceODE.Weights.LabelOp (Option (Fin m)))
      (L : Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) (δ : ℝ)
      (G : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
      (b : Fin M → ℝ → EuclideanSpace ℂ n) (sol : ℝ → EuclideanSpace ℂ n)
      (bv : Fin m → EuclideanSpace ℂ n)
      (U : ℝ → EuclideanSpace ℂ n → ℝ → EuclideanSpace ℂ n) (ζ : ℝ),
      IsUnitary P → (∀ a, IsUnitary (L a)) → 0 ≤ δ →
      CleanErr (cleanPi (V := ℂ) w₀) (Pw x) P δ →
      CleanErr (cleanPi (V := ℂ) w₀) (J x) (ctrlL L) δ →
      30 * ratio (cq * gbar) * δ ≤ 1 / 400 → 30 * ratio (cq * gbar) * δ ≤ ε / 20 →
      (∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), Accretive (G r u)) →
      RegularPieces t G →
      MildSolution t T b sol U →
      IsMeshPropagator G t T U →
      GeneralSourceODE.Compiled.WeightPrep P (sources (sol 0) bv ω) →
      (sol 0 ≠ 0 → L none seed = ODEStateNormalization.unitDirection (sol 0)) →
      (∀ i, ω i ≠ 0 → bv i ≠ 0 → L (some i) seed =
        ODEStateNormalization.unitDirection (bv i)) →
      ODESourceBranches.mass (sources (sol 0) bv ω) ≤ cq * meshScale sol b t →
      ‖(∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1), U u (b r u) T) -
          ∑ i, ω i • U (v i) (bv i) T‖ ≤ ζ * meshScale sol b t →
      sol T ≠ 0 →
      meshScale sol b t ≤ gbar * ‖sol T‖ →
      ζ + cq * (sampleError D x t G + 2 * dissipativeError D x t G +
        2 * refinementError D t T N) ≤ ε / (2000 * gbar) →
      6 * radius (cq * gbar) ε * (dissipativeError D x t G + refinementError D t T N) ≤
        precision (cq * gbar) ε →
      ApproxCertificate (ODERepeatProtocol.Protocol.repeatTrials tf 4) x (sol T) (s : ℝ)
        (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) (ratio (cq * gbar)) (accuracy ε))
        (ImprovedODEQueryBudget.logBudget (ratio (cq * gbar)) (accuracy ε))
        (ratio (cq * gbar)) ε ∧
      ((ODERepeatProtocol.Protocol.repeatTrials tf 4).worstCost
        GeneralSourceODE.Oracles.matrixCalls : ℝ) ≤ Q ∧
      ApproxRuns tf x (sol T) (30 * ratio (cq * gbar) * δ) (ε / 500)

/-- **`work_approx_solver_nonneg_regular` with the accuracy of the runs.** -/
theorem work_approx_solver_nonneg_regular_runs (D : Data (X × Fin M) n Z s) (hM : 0 < M)
    (t : ℕ → ℝ) {N : ℕ} (hN : 0 < N) (etaH etaD T gbar cq ε : ℝ) {m : ℕ} (v : Fin m → ℝ)
    (ω : Fin m → ℂ)
    (hH : 0 ≤ etaH) (hDiss : 0 ≤ etaD) (hT : 0 ≤ T) (hg : 1 ≤ gbar) (hcq : 1 ≤ cq)
    (hε : 0 < ε) (hεOne : ε ≤ 1) (hmesh : IsMesh t M T)
    (hClock : 8 * s * ((etaH + radius (cq * gbar) ε * etaD) * T) ≤ N)
    (hCayley : 3 * (Real.sqrt (2 * (s : ℝ)) *
      ((etaH + radius (cq * gbar) ε * etaD) * T)) ^ 3 ≤
        precision (cq * gbar) ε * (N : ℝ) ^ 2)
    (hv : ∀ i, v i ∈ Icc 0 T)
    (hrH : ∀ y i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix y) i j‖ ^ 2 ≤ etaH ^ 2)
    (hcH : ∀ y j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix y) i j‖ ^ 2 ≤ etaH ^ 2)
    (hrD : ∀ y i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix y) i j‖ ^ 2 ≤ etaD ^ 2)
    (hcD : ∀ y j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix y) i j‖ ^ 2 ≤ etaD ^ 2)
    (w₀ : W) (Pw : X → LabelW m W →L[ℂ] LabelW m W) (hPw : ∀ x, IsUnitary (Pw x))
    (J : X → LoadW m n W →L[ℂ] LoadW m n W) (hJ : ∀ x, IsUnitary (J x))
    (seed : EuclideanSpace ℂ n) (hSeed : ‖seed‖ = 1) :
    WorkRegularRunsOutcome D t N etaH etaD T gbar cq ε v ω w₀ Pw J seed
      (if T = 0 ∨ etaH + radius (cq * gbar) ε * etaD = 0 then 0 else
        1274019840 * ratio (cq * gbar) * ImprovedODEQueryBudget.queryShape (s : ℝ)
          (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) (ratio (cq * gbar)) (accuracy ε))
          (ImprovedODEQueryBudget.logBudget (ratio (cq * gbar)) (accuracy ε))) := by
  obtain ⟨d, tf, hch, hU, hC⟩ := work_approx_solver_nonneg_runs D hM t hN etaH etaD T gbar cq ε v ω
    hH hDiss hT hg hcq hε hεOne hmesh hClock hCayley hv hrH hcH hrD hcD w₀ Pw hPw J hJ seed
    hSeed
  refine ⟨d, tf, hch, hU, fun x P L δ G b sol bv U ζ hP hL hδ hPc hJc hδ1 hδε hG hreg hsol hUm
    hW hL0 hL' hMass hInt hTarget hB hB1 hB2 => ?_⟩
  have hD : sol T - U 0 (sol 0) T =
      ∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1), U u (b r u) T := by
    rw [hsol.2]
    abel
  have hCertP : ‖sol T - U 0 (sol 0) T - ∑ i, ω i • U (v i) (bv i) T‖ ≤
      ζ * meshScale sol b t := by
    rw [hD]
    exact hInt
  exact hC x P L δ G b sol bv U ζ hP hL hδ hPc hJc hδ1 hδε hG hreg hUm hW hL0 hL' hMass
    hCertP hTarget hB (robustBudget_of_path_int D x hmesh G hG hreg hB1 hB2)

end

end SparseHamiltonian.CleanWorkODE


namespace ManuscriptConformance

noncomputable section
open ContinuousLinearMap SparseHamiltonian NativeSparseBlockEncoding OracleCircuit Set
open SparseHamiltonian.GeneralSourceExtensions
open scoped InnerProduct InnerProductSpace

set_option maxRecDepth 4096
set_option synthInstance.maxSize 8192

universe u v w

set_option maxHeartbeats 8000000 in
/-- **Theorem `ode:thm:time` for approximate source preparations, with the accuracy of the
successful runs.** The hypotheses of `ode_thm_time_approx`; for the same protocol (four fresh trials
of one public trial family `tf`, fixed before the instance) and every instance satisfying its
conditions (the supplied preparations within `δ` of exact ones on a clean work register): the
heralded output; the conditional output is the ensemble of the successful histories (first success
at attempt `i` with trial `j`, their actual conditional weights and output directions); every trial
whose success probability is at least `p₀ > η²`, `η = 60 c_q ḡ δ`, has direction error at most
`ε/500 + 2 η/√p₀` up to a phase; the histories whose trial has success probability below `p₀`
carry conditional weight at most `6 p₀`; and the counts of `ode_thm_time_approx`. A rare successful
branch can be inaccurate only within that weight. -/
theorem ode_thm_time_approx_runs :
    ∃ C : ℝ, 0 < C ∧
      ∀ {X : Type u} {n : Type v} {Z : Type w} [Fintype n] [DecidableEq n] [Fintype Z]
        [AddCommGroup Z] [DecidableEq Z] {s M : ℕ} (D : Data (X × Fin M) n Z s), 0 < M →
        ∀ (t : ℕ → ℝ) (N : ℕ), 0 < N →
        ∀ (etaH etaD T gbar cq ε : ℝ) {m : ℕ} (v : Fin m → ℝ) (ω : Fin m → ℂ),
        0 ≤ etaH → 0 ≤ etaD → 0 ≤ T → 1 ≤ gbar → 1 ≤ cq → 0 < ε → ε ≤ 1 →
        TimeDependentExtensions.IsMesh t M T →
        8 * s * ((etaH + TimeDependentODE.radius (cq * gbar) ε * etaD) * T) ≤ N →
        3 * (Real.sqrt (2 * (s : ℝ)) *
          ((etaH + TimeDependentODE.radius (cq * gbar) ε * etaD) * T)) ^ 3 ≤
          TimeDependentODE.precision (cq * gbar) ε * (N : ℝ) ^ 2 →
        (∀ i, v i ∈ Icc 0 T) →
        (∀ y i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix y) i j‖ ^ 2 ≤ etaH ^ 2) →
        (∀ y j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix y) i j‖ ^ 2 ≤ etaH ^ 2) →
        (∀ y i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix y) i j‖ ^ 2 ≤ etaD ^ 2) →
        (∀ y j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix y) i j‖ ^ 2 ≤ etaD ^ 2) →
        ∀ {W : Type} [Fintype W] [DecidableEq W] (w₀ : W)
          (Pw : X → CleanWorkODE.LabelW m W →L[ℂ] CleanWorkODE.LabelW m W),
        (∀ x, IsUnitary (Pw x)) →
        ∀ (J : X → CleanWorkODE.LoadW m n W →L[ℂ] CleanWorkODE.LoadW m n W),
        (∀ x, IsUnitary (J x)) →
        ∀ seed : EuclideanSpace ℂ n, ‖seed‖ = 1 →
        ∃ (d : ℕ) (tf : ODERepeatProtocol.TrialFamily
            (CleanWorkODE.actualOracleW (ι := TimeDependentODE.Index D T (cq * gbar) ε) D m N d
              Pw J)
            (EuclideanSpace ℂ n)),
          ∀ (x : X) (P : GeneralSourceODE.Weights.LabelOp (Option (Fin m)))
            (L : Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) (δ : ℝ)
            (G : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
            (b : Fin M → ℝ → EuclideanSpace ℂ n) (sol : ℝ → EuclideanSpace ℂ n)
            (bv : Fin m → EuclideanSpace ℂ n)
            (U : ℝ → EuclideanSpace ℂ n → ℝ → EuclideanSpace ℂ n) (ζ : ℝ),
            IsUnitary P → (∀ a, IsUnitary (L a)) → 0 ≤ δ →
            cleanInputError w₀ (Pw x) P δ →
            cleanInputError w₀ (J x) (CleanWorkODE.ctrlL L) δ →
            60 * (cq * gbar) * δ ≤ 1 / 400 → 60 * (cq * gbar) * δ ≤ ε / 20 →
            (∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), TimeDependentODE.Accretive (G r u)) →
            RepresentedSampleODE.RegularPieces t G →
            RepresentedSampleODE.MildSolution t T b sol U →
            formal_classicalPropagator G t T U →
            GeneralSourceODE.Compiled.WeightPrep P (GeneralSourceODE.sources (sol 0) bv ω) →
            (sol 0 ≠ 0 → L none seed = ODEStateNormalization.unitDirection (sol 0)) →
            (∀ i, ω i ≠ 0 → bv i ≠ 0 →
              L (some i) seed = ODEStateNormalization.unitDirection (bv i)) →
            ODESourceBranches.mass (GeneralSourceODE.sources (sol 0) bv ω) ≤
              cq * Mesh.meshScale sol b t →
            ‖(∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1), U u (b r u) T) -
                ∑ i, ω i • U (v i) (bv i) T‖ ≤ ζ * Mesh.meshScale sol b t →
            sol T ≠ 0 →
            Mesh.meshScale sol b t ≤ gbar * ‖sol T‖ →
            ζ + cq * (Mesh.sampleError D x t G + 2 * RepresentedSampleODE.dissipativeError D x t G +
                2 * Mesh.refinementError D t T N) ≤ ε / (2000 * gbar) →
            6 * TimeDependentODE.radius (cq * gbar) ε *
                (RepresentedSampleODE.dissipativeError D x t G + Mesh.refinementError D t T N) ≤
              TimeDependentODE.precision (cq * gbar) ε →
            HeraldedOutput (ODERepeatProtocol.Protocol.repeatTrials tf 4) x
              (ODEStateNormalization.unitDirection (sol T)) ε ∧
            (ODERepeatProtocol.Protocol.repeatTrials tf 4).conditionalDensity x =
              ODEMixedOutput.ensemble (ODERepeatProbability.conditionalWeight (tf.probability x))
                (fun a : Fin 4 × Fin tf.choices => tf.outputDirection x a.2) ∧
            (∀ p₀ : ℝ, (60 * (cq * gbar) * δ) ^ 2 < p₀ → ∀ j : Fin tf.choices,
              p₀ ≤ tf.probability x j →
              ∃ ω : ℂ, ‖ω‖ = 1 ∧ ‖ω • tf.outputDirection x j -
                ODEStateNormalization.unitDirection (sol T)‖ ≤
                  ε / 500 + 2 * (60 * (cq * gbar) * δ) / Real.sqrt p₀) ∧
            (∀ p₀ : ℝ, 0 ≤ p₀ →
              ∑ b ∈ Finset.univ.filter
                  (fun b : Fin 4 × Fin tf.choices => tf.probability x b.2 < p₀),
                ODERepeatProbability.conditionalWeight (tf.probability x) b ≤ 6 * p₀) ∧
            ((ODERepeatProtocol.Protocol.repeatTrials tf 4).worstCost
              GeneralSourceODE.Oracles.matrixCalls : ℝ) ≤
              C * (cq * gbar) * (Real.sqrt s * (T * etaH + T * etaD *
                  Real.log (40000 * cq * gbar / ε)) +
                Real.sqrt (s * (T * etaH + T * etaD * Real.log (40000 * cq * gbar / ε)) *
                  Real.log (40000 * cq * gbar / ε)) + Real.log (40000 * cq * gbar / ε)) ∧
            ((ODERepeatProtocol.Protocol.repeatTrials tf 4).worstCost
              GeneralSourceODE.Oracles.sourceCalls : ℝ) ≤ C * (cq * gbar) := by
  refine ⟨2548039680, by norm_num, ?_⟩
  intro X n Z _ _ _ _ _ s M D hM t N hN etaH etaD T gbar cq ε m v ω hH hDiss hT hg hcq hε hεOne
    hmesh hClock hCayley hv hrH hcH hrD hcD W _ _ w₀ Pw hPw J hJ seed hSeed
  obtain ⟨d, tf, -, hUt, hC⟩ := CleanWorkODE.work_approx_solver_nonneg_regular_runs D hM t hN
    etaH etaD T gbar cq ε v ω hH hDiss hT hg hcq hε hεOne hmesh hClock hCayley hv hrH hcH hrD hcD w₀
    Pw hPw J hJ seed hSeed
  refine ⟨d, tf, fun x P L δ G b sol bv U ζ hP hL hδ hPc hJc hδ1 hδε hG hreg hsol hUm hW hL0 hL'
    hMass hInt hTarget hB hB1 hB2 => ?_⟩
  have hratio : 30 * TimeDependentODE.ratio (cq * gbar) * δ = 60 * (cq * gbar) * δ := by
    unfold TimeDependentODE.ratio; ring
  obtain ⟨hcert, -, hruns⟩ := hC x P L δ G b sol bv U ζ hP hL hδ (cleanErr_of_fullOutputError hPc)
    (cleanErr_of_fullOutputError hJc) (hratio ▸ hδ1)
    (hratio ▸ hδε) hG hreg hsol hUm hW hL0 hL' hMass hInt hTarget hB hB1 hB2
  rw [hratio] at hruns
  have hS : 2 / 3 ≤ ODERepeatProbability.successProbability (tf.probability x) := by
    rw [← ODERepeatProtocol.Protocol.four_successMass_eq]
    exact hcert.success_two_thirds
  have hpb := tf.probability_bounds x (fun j => hUt j x)
  have hη0 : 0 ≤ 60 * (cq * gbar) * δ := by
    have : 0 ≤ cq * gbar := by positivity
    positivity
  refine ⟨⟨hcert.success_two_thirds, hcert.output_density, hcert.conditional_error⟩,
    ODERepeatProtocol.Protocol.four_conditionalDensity_eq tf x, ?_, ?_, ?_, ?_⟩
  · intro p₀ hp₀ j hj
    have hp₀pos : 0 < p₀ := lt_of_le_of_lt (sq_nonneg _) hp₀
    have hsq : 60 * (cq * gbar) * δ < Real.sqrt p₀ := by
      rw [← Real.sqrt_sq hη0]
      exact Real.sqrt_lt_sqrt (sq_nonneg _) hp₀
    have hamp : Real.sqrt p₀ ≤ ‖tf.amplitude x j‖ := by
      have e : tf.probability x j = ‖tf.amplitude x j‖ ^ 2 := rfl
      rw [← Real.sqrt_sq (norm_nonneg (tf.amplitude x j)), ← e]
      exact Real.sqrt_le_sqrt hj
    obtain ⟨ω', hω', hle⟩ := hruns j (lt_of_lt_of_le hsq hamp)
    refine ⟨ω', hω', hle.trans ?_⟩
    have hden : 0 < Real.sqrt p₀ := Real.sqrt_pos.mpr hp₀pos
    gcongr
  · intro p₀ hp₀
    exact lowWeight_le (tf.probability x) (fun j => (hpb j).1) (fun j => (hpb j).2) hS hp₀
  · refine hcert.matrix_queries.trans (le_of_eq ?_)
    rw [ImprovedODEQueryBudget.queryShape, ImprovedODEQueryBudget.theta, time_log_eq]
    unfold TimeDependentODE.ratio
    ring
  · refine hcert.source_calls.trans ?_
    unfold TimeDependentODE.ratio
    have : 0 ≤ cq * gbar := by positivity
    nlinarith

end

end ManuscriptConformance
