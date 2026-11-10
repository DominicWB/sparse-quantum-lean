import ManuscriptConformance.ODETime

/-!
# Conformance: accuracy of the actual successful runs

`RunsClose` (in `ODEUpper`) asserts that the conditional output has **some** finite ensemble
decomposition whose vectors are close to the target; it does not identify those vectors with the
actual trial outputs. This module states the per-run property for the actual circuits:

* `TrialsClose t x target ε`: for every trial `j` of the public trial family `t` (circuit
  `t.circuit j`, seed `t.seed`, selected-output isometry `t.output`), the selected output
  `v_j = t.output† (t.circuit j · t.seed)` is either zero or satisfies
  `‖ω · v_j/‖v_j‖ - target/‖target‖‖ ≤ ε` for some phase `|ω| = 1`;
* `HistoriesClose`: the same for every positive-probability successful history of the
  four-attempt protocol `repeatTrials t 4`, through its actual history-to-trial map (history
  `(i, j)`: first success at attempt `i` with trial circuit `t.circuit j`); the conditional density
  of the protocol **is** the ensemble of these histories
  (`ODERepeatProtocol.Protocol.four_conditionalDensity_eq`, the first clause of `HistoriesClose`);
* `trialsClose_of_certificate`, `historiesClose_of_trialsClose`: both follow from the released
  complete certificate `ODECompleteTrial.Certificate` (whose trial certificate bounds the
  direction error of every actual trial by `ε/500`); `trialsClose_congr`: the property depends only
  on the evaluations, so it transfers through the substitution of the separate source primitives;
* `runsClose_diagnostic`: the density `diag(0.99, 0.01)` satisfies `RunsClose` with target `|0⟩`
  and `ε = 1/5` (through the decomposition `√0.99 |0⟩ ± 0.1 |1⟩`), although it is the mixture of a
  physical `|1⟩` branch of positive weight, at distance `√2` from every phase of `|0⟩` (stated as
  `> 1/5`);
* `ode_thm_main_actual`: Theorem `ode:thm:main` with `TrialsClose` and `HistoriesClose` for its
  protocol, in addition to all the conclusions of `ode_thm_main`;
* `ode_thm_time_actual`: Theorem `ode:thm:time` for exact source preparations (the instance class
  of `ode_thm_time`, represented samples of either sign, arbitrary public complex source weights
  and nodes, every `T ≥ 0` including the zero-time and zero-generator cases) with `HeraldedOutput`,
  `TrialsClose`, `HistoriesClose` and the worst-history counts of `ode_thm_time`, for one protocol
  over the separate source primitives, fixed before the instance. The certificate is taken from
  the exact-source solvers (`RepresentedSampleODE.robust_propagated_solver`, `robust_zero_core`)
  directly, not recovered from the mixed-output form.

Not claimed: per-run accuracy for approximate source preparations (`ode_thm_time_approx`). A rare
successful branch can be inaccurate although the aggregate state is close; that needs a separate
proof about the actual implemented preparation.
-/

set_option autoImplicit false

namespace ManuscriptConformance

noncomputable section
open ContinuousLinearMap SparseHamiltonian NativeSparseBlockEncoding OracleCircuit Set
open SparseHamiltonian.GeneralSourceExtensions
open scoped InnerProduct InnerProductSpace

set_option maxRecDepth 4096
set_option synthInstance.maxSize 8192

universe u v w

section Generic

variable {E K X L L' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- **Every actual trial is accurate**: for every trial `j` of the trial family `t` (circuit
`t.circuit j`, seed `t.seed`, selected-output isometry `t.output`), the actual selected output
`v_j = t.output† (t.circuit j · t.seed)` (`TrialFamily.amplitude`) is zero (the trial never
succeeds) or its direction `v_j/‖v_j‖` is within `ε` of `target/‖target‖` up to a phase. -/
def TrialsClose {O : L → X → K →L[ℂ] K} (t : ODERepeatProtocol.TrialFamily O E) (x : X)
    (target : E) (ε : ℝ) : Prop :=
  ∀ j : Fin t.choices, t.amplitude x j ≠ 0 →
    ∃ ω : ℂ, ‖ω‖ = 1 ∧
      ‖ω • t.outputDirection x j - ODEStateNormalization.unitDirection target‖ ≤ ε

/-- **Every positive-probability successful history is accurate**: the conditional density of
the four-attempt protocol `repeatTrials t 4` is the ensemble of its successful histories
`(i, j)` (first success at attempt `i` with trial `j`) with their actual conditional weights and
actual output directions, and every history of positive weight has a nonzero selected output
whose direction is within `ε` of `target/‖target‖` up to a phase. -/
def HistoriesClose {O : L → X → K →L[ℂ] K} (t : ODERepeatProtocol.TrialFamily O E) (x : X)
    (target : E) (ε : ℝ) : Prop :=
  (ODERepeatProtocol.Protocol.repeatTrials t 4).conditionalDensity x =
      ODEMixedOutput.ensemble (ODERepeatProbability.conditionalWeight (t.probability x))
        (fun a : Fin 4 × Fin t.choices => t.outputDirection x a.2) ∧
    ∀ a : Fin 4 × Fin t.choices, ODERepeatProbability.conditionalWeight (t.probability x) a ≠ 0 →
      t.amplitude x a.2 ≠ 0 ∧
        ∃ ω : ℂ, ‖ω‖ = 1 ∧
          ‖ω • t.outputDirection x a.2 - ODEStateNormalization.unitDirection target‖ ≤ ε

/-- **The released trial certificate gives `TrialsClose`** for the family of its circuits. -/
theorem trialsClose_of_trialCertificate {O : (L ⊕ Bool) → X → K →L[ℂ] K}
    {q : ℕ → MultiOracleCircuit.Program O} {M : ℕ} (hM : 0 < M) {ψ : K} (hψ : ‖ψ‖ = 1)
    {F : E →L[ℂ] K} (hF : F† ∘L F = 1) {x : X} {target : E} {s Θ ell g η ε : ℝ}
    (h : ODEPrimitiveSourceJoin.TrialCertificate q M ψ F x target s Θ ell g η) (hη : η ≤ ε) :
    TrialsClose (ODERepeatProtocol.ofCircuits q M hM ψ hψ F hF) x target ε := by
  intro j hne
  obtain ⟨ω, hω, hd⟩ := h.direction_error j.val j.isLt hne
  exact ⟨ω, hω, hd.trans hη⟩

/-- **The released complete certificate gives `TrialsClose`** (with `ε/500 ≤ ε`). -/
theorem trialsClose_of_certificate [FiniteDimensional ℂ E] {O : (L ⊕ Bool) → X → K →L[ℂ] K}
    {q : ℕ → MultiOracleCircuit.Program O} {M : ℕ} (hM : 0 < M) {ψ : K} (hψ : ‖ψ‖ = 1)
    {F : E →L[ℂ] K} (hF : F† ∘L F = 1) {x : X} {target : E} {s Θ ell g ε : ℝ}
    (h : ODECompleteTrial.Certificate q M ψ F x target s Θ ell g ε) (hε : 0 ≤ ε) :
    TrialsClose (ODERepeatProtocol.ofCircuits q M hM ψ hψ F hF) x target ε :=
  trialsClose_of_trialCertificate hM hψ hF h.trial (by linarith)

/-- **`TrialsClose` depends only on the evaluations**: two program families with the same
evaluations at `x` (for instance a family and its substitution by implementations of the counted
interfaces) have the same selected outputs. -/
theorem trialsClose_congr {O : L → X → K →L[ℂ] K} {O' : L' → X → K →L[ℂ] K}
    {q : ℕ → MultiOracleCircuit.Program O} {q' : ℕ → MultiOracleCircuit.Program O'} {M : ℕ}
    (hM : 0 < M) {ψ : K} (hψ : ‖ψ‖ = 1) {F : E →L[ℂ] K} (hF : F† ∘L F = 1) {x : X}
    {target : E} {ε : ℝ} (hEval : ∀ j, (q' j).eval x = (q j).eval x)
    (h : TrialsClose (ODERepeatProtocol.ofCircuits q M hM ψ hψ F hF) x target ε) :
    TrialsClose (ODERepeatProtocol.ofCircuits q' M hM ψ hψ F hF) x target ε := by
  intro j hne
  have e : (ODERepeatProtocol.ofCircuits q' M hM ψ hψ F hF).amplitude x j =
      (ODERepeatProtocol.ofCircuits q M hM ψ hψ F hF).amplitude x j := by
    change (F†) ((q' j.val).eval x ψ) = (F†) ((q j.val).eval x ψ)
    rw [hEval j.val]
  have e' : (ODERepeatProtocol.ofCircuits q' M hM ψ hψ F hF).outputDirection x j =
      (ODERepeatProtocol.ofCircuits q M hM ψ hψ F hF).outputDirection x j := by
    unfold ODERepeatProtocol.TrialFamily.outputDirection
    rw [e]
  rw [e] at hne
  rw [e']
  exact h j hne

/-- **`TrialsClose` gives `HistoriesClose`**: the conditional density of the four-attempt protocol
is the ensemble of its successful histories (`four_conditionalDensity_eq`), and a history of
positive conditional weight runs a trial of positive success probability. -/
theorem historiesClose_of_trialsClose {O : L → X → K →L[ℂ] K}
    {t : ODERepeatProtocol.TrialFamily O E} {x : X} {target : E} {ε : ℝ}
    (h : TrialsClose t x target ε) : HistoriesClose t x target ε := by
  refine ⟨ODERepeatProtocol.Protocol.four_conditionalDensity_eq t x, fun a ha => ?_⟩
  have hp := ODERepeatProbability.conditionalWeight_ne_zero_implies (t.probability x) a ha
  have hne : t.amplitude x a.2 ≠ 0 := by
    intro hz
    apply hp
    simp [ODERepeatProtocol.TrialFamily.probability, hz]
  exact ⟨hne, h a.2 hne⟩

/-- `HistoriesClose` gives `RunsClose`, with the actual histories as the decomposition. -/
theorem runsClose_of_historiesClose [FiniteDimensional ℂ E] {O : L → X → K →L[ℂ] K}
    {t : ODERepeatProtocol.TrialFamily O E} {x : X} {target : E} {ε : ℝ}
    (hw : ∀ a, 0 ≤ ODERepeatProbability.conditionalWeight (t.probability x) a)
    (hsum : ∑ a, ODERepeatProbability.conditionalWeight (t.probability x) a = 1)
    (h : HistoriesClose t x target ε) :
    RunsClose ((ODERepeatProtocol.Protocol.repeatTrials t 4).conditionalDensity x)
      (ODEStateNormalization.unitDirection target) ε := by
  refine ⟨Fin 4 × Fin t.choices, inferInstance,
    ODERepeatProbability.conditionalWeight (t.probability x),
    fun a => t.outputDirection x a.2, h.1, hw, hsum, fun a ha => ⟨?_, (h.2 a ha).2⟩⟩
  exact ODEStateNormalization.unitDirection_norm _ (h.2 a ha).1

end Generic

/-! ### The diagnostic example -/

/-- `|0⟩` in `ℂ²`. -/
def diagE₀ : EuclideanSpace ℂ (Fin 2) := EuclideanSpace.single 0 (1 : ℂ)

/-- `|1⟩` in `ℂ²`. -/
def diagE₁ : EuclideanSpace ℂ (Fin 2) := EuclideanSpace.single 1 (1 : ℂ)

/-- The physical weights `0.99`, `0.01`. -/
def diagWeights : Fin 2 → ℝ := ![99 / 100, 1 / 100]

/-- The physical branches `|0⟩`, `|1⟩`. -/
def diagBranches : Fin 2 → EuclideanSpace ℂ (Fin 2) := ![diagE₀, diagE₁]

/-- The density `diag(0.99, 0.01)` as the ensemble of its physical branches. -/
def diagDensity : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  ODEMixedOutput.ensemble diagWeights diagBranches

/-- The alternative branches `a |0⟩ + (σ/10) |1⟩`. -/
def diagAlt (a : ℝ) (σ : ℂ) : EuclideanSpace ℂ (Fin 2) :=
  (a : ℂ) • diagE₀ + (σ / 10) • diagE₁

theorem diagE₀_apply (i : Fin 2) : diagE₀ i = if i = 0 then 1 else 0 := by
  fin_cases i <;> simp [diagE₀]

theorem diagE₁_apply (i : Fin 2) : diagE₁ i = if i = 0 then 0 else 1 := by
  fin_cases i <;> simp [diagE₁]

theorem diagAlt_apply (a : ℝ) (σ : ℂ) (i : Fin 2) :
    diagAlt a σ i = if i = 0 then (a : ℂ) else σ / 10 := by
  fin_cases i <;> simp [diagAlt, diagE₀_apply, diagE₁_apply]

/-- The two decompositions give the same density when `a² = 0.99`. -/
theorem diagDensity_eq_alt (a : ℝ) (ha : a ^ 2 = 99 / 100) :
    diagDensity =
      ODEMixedOutput.ensemble (![1 / 2, 1 / 2] : Fin 2 → ℝ) ![diagAlt a 1, diagAlt a (-1)] := by
  have hs : (a : ℂ) ^ 2 = 99 / 100 := by
    rw [← Complex.ofReal_pow, ha]
    push_cast
    ring
  ext z i
  simp only [diagDensity, ODEMixedOutput.ensemble, ODEMixedOutput.pureOperator, Fin.sum_univ_two,
    _root_.add_apply, _root_.smul_apply, InnerProductSpace.rankOne_apply,
    PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, diagWeights, diagBranches, Matrix.cons_val_zero,
    Matrix.cons_val_one, EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, Fin.sum_univ_two, Pi.star_apply, RCLike.star_def, diagAlt_apply,
    diagE₀_apply, diagE₁_apply]
  fin_cases i
  · simp [Complex.conj_ofReal, map_ofNat]
    ring_nf
    first | ring | linear_combination (z.ofLp 0) * hs | linear_combination -(z.ofLp 0) * hs
  · simp [Complex.conj_ofReal, map_ofNat]
    ring_nf

/-- `‖ω |1⟩ - |0⟩‖ ≥ 1` for every `ω`. -/
theorem diag_branch_far (ω : ℂ) : 1 ≤ ‖ω • diagE₁ - diagE₀‖ := by
  have h := norm_inner_le_norm (𝕜 := ℂ) diagE₀ (ω • diagE₁ - diagE₀)
  have hin : inner ℂ diagE₀ (ω • diagE₁ - diagE₀) = -1 := by
    simp [diagE₀, diagE₁, EuclideanSpace.inner_single_left]
  have hn : ‖diagE₀‖ = 1 := by simp [diagE₀]
  rw [hin, norm_neg, norm_one, hn, one_mul] at h
  exact h

/-- `‖a |0⟩ ± 0.1 |1⟩ - |0⟩‖ ≤ 1/5` for `0.99 ≤ a ≤ 1`. -/
theorem diagAlt_close (a : ℝ) (ha : 99 / 100 ≤ a) (ha1 : a ≤ 1) (σ : ℂ) (hσ : ‖σ‖ = 1) :
    ‖diagAlt a σ - diagE₀‖ ≤ 1 / 5 := by
  have e : diagAlt a σ - diagE₀ = ((a - 1 : ℝ) : ℂ) • diagE₀ + (σ / 10) • diagE₁ := by
    rw [diagAlt, Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul]
    abel
  rw [e]
  have h1 : ‖diagE₀‖ = 1 := by simp [diagE₀]
  have h2 : ‖diagE₁‖ = 1 := by simp [diagE₁]
  calc ‖((a - 1 : ℝ) : ℂ) • diagE₀ + (σ / 10) • diagE₁‖
      ≤ ‖((a - 1 : ℝ) : ℂ) • diagE₀‖ + ‖(σ / 10) • diagE₁‖ := norm_add_le _ _
    _ = |a - 1| + 1 / 10 := by
        rw [norm_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs, norm_div, hσ, h1, h2]
        norm_num
    _ ≤ 1 / 5 := by
        rw [abs_of_nonpos (by linarith)]
        linarith

/-- `‖a |0⟩ ± 0.1 |1⟩‖ = 1` when `a² = 0.99`. -/
theorem diagAlt_norm (a : ℝ) (ha : a ^ 2 = 99 / 100) (σ : ℂ) (hσ : ‖σ‖ = 1) :
    ‖diagAlt a σ‖ = 1 := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, diagAlt_apply, diagAlt_apply]
  have h10 : ((1 : Fin 2) = 0) = False := by decide
  simp only [if_true, h10, if_false, Complex.norm_real, Real.norm_eq_abs, sq_abs, norm_div, hσ, ha]
  norm_num

/-- **`RunsClose` does not control the physical branches.** The density `diag(0.99, 0.01)`, the
mixture of the physical branches `|0⟩` (weight `0.99`) and `|1⟩` (weight `0.01`), satisfies
`RunsClose` with target `|0⟩` and `ε = 1/5` through the alternative decomposition
`√0.99 |0⟩ ± 0.1 |1⟩`; but the physical branch `|1⟩` has positive weight and is at distance at
least `1 > 1/5` from every phase of `|0⟩`, so the per-history property fails for this physical
decomposition. -/
theorem runsClose_diagnostic :
    RunsClose diagDensity diagE₀ (1 / 5) ∧ diagWeights 1 ≠ 0 ∧
      ∀ ω : ℂ, ‖ω‖ = 1 → 1 / 5 < ‖ω • diagBranches 1 - diagE₀‖ := by
  set a := Real.sqrt (99 / 100) with hadef
  have ha : a ^ 2 = 99 / 100 := Real.sq_sqrt (by norm_num)
  have ha0 : 99 / 100 ≤ a := by
    rw [hadef, Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  have ha1 : a ≤ 1 := by
    rw [hadef, Real.sqrt_le_one]
    norm_num
  refine ⟨⟨Fin 2, inferInstance, ![1 / 2, 1 / 2], ![diagAlt a 1, diagAlt a (-1)],
    diagDensity_eq_alt a ha, ?_, ?_, ?_⟩, by simp [diagWeights], fun ω _ => ?_⟩
  · intro i
    fin_cases i <;> norm_num
  · simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num
  · intro i _
    fin_cases i
    · exact ⟨diagAlt_norm a ha 1 (by simp), 1, by simp,
        by simpa using diagAlt_close a ha0 ha1 1 (by simp)⟩
    · exact ⟨diagAlt_norm a ha (-1) (by simp), 1, by simp,
        by simpa using diagAlt_close a ha0 ha1 (-1) (by simp)⟩
  · have h := diag_branch_far ω
    show 1 / 5 < ‖ω • diagE₁ - diagE₀‖
    linarith

/-! ### The conformance theorems with the actual-run property -/

set_option maxHeartbeats 8000000 in
/-- **Theorem `ode:thm:main` with the accuracy of the actual successful runs.** The protocol,
circuits, seed, selected-output isometry, success, trace-distance and worst-history counts are
those of `ode_thm_main`; in addition `TrialsClose`: every actual trial circuit `q_j` with a
nonzero selected output `F†(q_j ψ)` prepares `x(T)/‖x(T)‖` to Euclidean error at most `ε` up to a
global phase, and `HistoriesClose`: the same for every positive-probability successful history of
the four-attempt protocol, whose conditional density is the ensemble of those histories. -/
theorem ode_thm_main_actual :
    ∃ C : ℝ, 0 < C ∧
      ∀ {X : Type u} {n : Type v} {Z : Type w} [Fintype n] [DecidableEq n] [Fintype Z]
        [AddCommGroup Z] [DecidableEq Z] {s : ℕ} (D : Data X n Z s)
        (etaH etaD T gbar ε r₀ rb : ℝ),
        0 ≤ etaH → 0 ≤ etaD → 0 ≤ T → 0 < ε → ε ≤ 1 / 2 →
        (∀ x i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ etaH ^ 2) →
        (∀ x j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ etaH ^ 2) →
        (∀ x i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ etaD ^ 2) →
        (∀ x j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ etaD ^ 2) →
        (∀ (x : X) (z : EuclideanSpace ℂ n), 0 ≤ (inner ℂ z (SparseStateOverlap.matrixOperator
          (ODEMatrixEnergy.dissipativePart (D.matrix x)) z)).re) →
        ∀ (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n),
        (∀ y, IsUnitary (J₀ y)) → (∀ y, IsUnitary (Jb y)) →
        ∀ seed : EuclideanSpace ℂ n, ‖seed‖ = 1 →
        ∃ (Tslots d : ℕ)
          (q : ℕ → MultiOracleCircuit.Program
            (ODEFinalNativeSource.physicalOracle
              (ι := Fin (ODEPublicGaussianEndpoint.gridSize D T gbar ε) ⊕ Bool) D
              (ODEPublicSourceMesh.meshSize D T (ImprovedODEQueryBudget.precision gbar ε))
              Tslots d J₀ Jb))
          (M : ℕ)
          (ψ : ODEFinalNativeSource.Physical (Fin (ODEPublicGaussianEndpoint.gridSize D T gbar ε) ⊕
            Bool) n Z (ODEPublicSourceMesh.meshSize D T (ImprovedODEQueryBudget.precision gbar ε))
            Tslots d)
          (F : EuclideanSpace ℂ n →L[ℂ] ODEFinalNativeSource.Physical
            (Fin (ODEPublicGaussianEndpoint.gridSize D T gbar ε) ⊕ Bool) n Z
            (ODEPublicSourceMesh.meshSize D T (ImprovedODEQueryBudget.precision gbar ε)) Tslots d),
          ∀ (x : X) (v b : EuclideanSpace ℂ n), ‖v‖ = r₀ → ‖b‖ = rb →
            (v ≠ 0 → J₀ x seed = ODEStateNormalization.unitDirection v) →
            (b ≠ 0 → Jb x seed = ODEStateNormalization.unitDirection b) →
            ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T ≠ 0 →
            r₀ + T * rb ≤
              gbar * ‖ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T‖ →
            ∃ (hM : 0 < M) (hψ : ‖ψ‖ = 1) (hF : F† ∘L F = 1),
              HeraldedOutput (ODERepeatProtocol.fourTrials q M hM ψ hψ F hF) x
                (ODEStateNormalization.unitDirection
                  (ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T)) ε ∧
              RunsClose ((ODERepeatProtocol.fourTrials q M hM ψ hψ F hF).conditionalDensity x)
                (ODEStateNormalization.unitDirection
                  (ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T)) ε ∧
              TrialsClose (ODERepeatProtocol.ofCircuits q M hM ψ hψ F hF) x
                (ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T) ε ∧
              HistoriesClose (ODERepeatProtocol.ofCircuits q M hM ψ hψ F hF) x
                (ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T) ε ∧
              ((ODERepeatProtocol.fourTrials q M hM ψ hψ F hF).worstCost
                  (ODESourceQueryBudget.matrixWeight fun _ => 1) : ℝ) ≤
                C * gbar * (Real.sqrt s * (T * etaH + T * etaD * Real.log (10000 * gbar / ε)) +
                  Real.sqrt (s * (T * etaH + T * etaD * Real.log (10000 * gbar / ε)) *
                    Real.log (10000 * gbar / ε)) + Real.log (10000 * gbar / ε)) ∧
              ∀ c : Bool, ((ODERepeatProtocol.fourTrials q M hM ψ hψ F hF).worstCost
                (ODESourceQueryBudget.sourceWeight c) : ℝ) ≤ C * gbar := by
  refine ⟨1274019840, by norm_num, ?_⟩
  intro X n Z _ _ _ _ _ s D etaH etaD T gbar ε r₀ rb hH hDiss hT hε hεHalf hrH hcH hrD hcD hPSD
    J₀ Jb hJ₀ hJb seed hSeed
  by_cases hex : ∃ (x : X) (v b : EuclideanSpace ℂ n), ‖v‖ = r₀ ∧ ‖b‖ = rb ∧
      ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T ≠ 0 ∧
      (r₀ + T * rb) /
        ‖ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T‖ ≤ gbar
  · obtain ⟨x₁, v₁, b₁, hv₁, hb₁, hsol₁, hg₁⟩ := hex
    have hg : 1 ≤ gbar := by
      have hRatio := ODEConstantForcing.normalization_ratio_ge_one
        (ODEPublicSourceMesh.generator D x₁)
        (ODEPublicSourceMesh.generator_dissipative D x₁ (hPSD x₁)) v₁ b₁ T hT hsol₁
      rw [hv₁, hb₁] at hRatio
      exact hRatio.trans hg₁
    obtain ⟨Tslots, d, E, q, -, hC⟩ := ZeroTimeRemarks.ODEConstant.solver_nonneg D etaH etaD T
      gbar ε r₀ rb hH hDiss hT hε hεHalf hrH hcH hrD hcD hPSD J₀ Jb hJ₀ hJb seed hSeed x₁ v₁ b₁
      hv₁ hb₁ hsol₁ hg₁
    have hℓ : 0 ≤ Real.log (10000 * gbar / ε) :=
      Real.log_nonneg (by rw [le_div_iff₀ hε]; nlinarith)
    have hshape : 0 ≤ ImprovedODEQueryBudget.queryShape (s : ℝ)
        (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) gbar ε)
        (ImprovedODEQueryBudget.logBudget gbar ε) := by
      unfold ImprovedODEQueryBudget.queryShape ImprovedODEQueryBudget.theta
        ImprovedODEQueryBudget.logBudget
      have : 0 ≤ T * etaH + T * etaD * Real.log (10000 * gbar / ε) := by positivity
      positivity
    refine ⟨Tslots, d, q, ODEGroverAverage.chosenIterations gbar,
      ODEFinalNativeSource.input D (Sum.inr false)
        (ODEPublicSourceMesh.meshSize D T (ImprovedODEQueryBudget.precision gbar ε)) Tslots d
        (ODECompiledSource.seed E
          (ODESourcePublicNorms.publicCoefficients r₀ rb T
            (ODEPublicSourceMesh.meshSize D T (ImprovedODEQueryBudget.precision gbar ε))
            (ODECoefficientPadding.paddedCoefficient
              (ODEPublicGaussianEndpoint.coefficients D T gbar ε) 3)) seed),
      ODEFinalNativeSource.input D (Sum.inr false)
        (ODEPublicSourceMesh.meshSize D T (ImprovedODEQueryBudget.precision gbar ε)) Tslots d ∘L
          ODECompiledSource.output E
            (ODESourcePublicNorms.publicCoefficients r₀ rb T
              (ODEPublicSourceMesh.meshSize D T (ImprovedODEQueryBudget.precision gbar ε))
              (ODECoefficientPadding.paddedCoefficient
                (ODEPublicGaussianEndpoint.coefficients D T gbar ε) 3)),
      fun x v b hv hb hJv hJbv hsol hB => ?_⟩
    obtain ⟨h, hQ⟩ := hC v b x hv hb hJv hJbv hsol hB
    refine ⟨h.trial.cutoff_pos, h.trial.seed_unit, h.trial.output_isometry,
      ⟨h.success_two_thirds, h.output_density, h.conditional_error⟩,
      runsClose_of_certificate h hε.le,
      trialsClose_of_certificate h.trial.cutoff_pos h.trial.seed_unit h.trial.output_isometry h hε.le,
      historiesClose_of_trialsClose (trialsClose_of_certificate h.trial.cutoff_pos h.trial.seed_unit
        h.trial.output_isometry h hε.le), hQ.trans ?_, fun c => (h.source_queries c).trans ?_⟩
    · split_ifs
      · have : (0 : ℝ) ≤ 1274019840 * gbar := by positivity
        exact mul_nonneg this hshape
      · exact le_rfl
    · nlinarith
  · refine ⟨0, 0, fun _ => .fixed 1 OracleCircuit.isUnitary_one, 1, 0, 0,
      fun x v b hv hb _ _ hsol hB => ?_⟩
    exfalso
    refine hex ⟨x, v, b, hv, hb, hsol, ?_⟩
    rw [div_le_iff₀ (norm_pos_iff.mpr hsol)]
    linarith


set_option maxHeartbeats 16000000 in
/-- **Theorem `ode:thm:time` with the accuracy of the actual successful runs, exact source
preparations.** The instance class, the protocol's oracle (the coherent sampled-time matrix
oracle and the separate supplied `P_w`, `U_load`, `P_w†`), the success, trace-distance and
worst-history counts are those of `ode_thm_time`, for one public trial family `tf` fixed before
the instance; in addition `TrialsClose`: every actual trial circuit with a nonzero selected
output prepares `x(T)/‖x(T)‖` to Euclidean error at most `ε` up to a global phase, and
`HistoriesClose`: the same for every positive-probability successful history of
`repeatTrials tf 4`. The certificate is the exact-source one (`robust_propagated_solver` for
`T > 0` and `η_H + R η_D > 0`, `robust_zero_core` otherwise), with the input budgets converted by
`robustBudget_of_path_int`. -/
theorem ode_thm_time_actual :
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
        ∀ (Pw : X → GeneralSourceODE.Weights.LabelOp (Option (Fin m))), (∀ x, IsUnitary (Pw x)) →
        ∀ (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n),
        (∀ x a, IsUnitary (J x a)) →
        ∀ seed : EuclideanSpace ℂ n, ‖seed‖ = 1 →
        ∃ (d : ℕ) (tf : ODERepeatProtocol.TrialFamily
            (MeshOracles.actualOracle (ι := TimeDependentODE.Index D T (cq * gbar) ε) D m N d Pw J)
            (EuclideanSpace ℂ n)),
          ∀ (x : X) (G : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
            (b : Fin M → ℝ → EuclideanSpace ℂ n) (sol : ℝ → EuclideanSpace ℂ n)
            (bv : Fin m → EuclideanSpace ℂ n)
            (U : ℝ → EuclideanSpace ℂ n → ℝ → EuclideanSpace ℂ n) (ζ : ℝ),
            (∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), TimeDependentODE.Accretive (G r u)) →
            RepresentedSampleODE.RegularPieces t G →
            RepresentedSampleODE.MildSolution t T b sol U →
            formal_classicalPropagator G t T U →
            GeneralSourceODE.Compiled.WeightPrep (Pw x) (GeneralSourceODE.sources (sol 0) bv ω) →
            (sol 0 ≠ 0 → J x none seed = ODEStateNormalization.unitDirection (sol 0)) →
            (∀ i, ω i ≠ 0 → bv i ≠ 0 →
              J x (some i) seed = ODEStateNormalization.unitDirection (bv i)) →
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
            TrialsClose tf x (sol T) ε ∧ HistoriesClose tf x (sol T) ε ∧
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
    hmesh hClock hCayley hv hrH hcH hrD hcD Pw hPw J hJ seed hSeed
  have hg1 : 1 ≤ TimeDependentODE.ratio (cq * gbar) := by
    unfold TimeDependentODE.ratio
    nlinarith
  -- The exact-source certificate, for every `T ≥ 0`.
  have hOut : RepresentedSampleODE.RobustPropagatedOutcome D hM t N etaH etaD T gbar cq ε v ω Pw J
      seed := by
    by_cases hZero : T = 0 ∨ etaH + TimeDependentODE.radius (cq * gbar) ε * etaD = 0
    · obtain ⟨d, E, hE, q, hU, -, hC⟩ := RepresentedSampleODE.robust_zero_core D hM t hN etaH etaD
        T gbar cq ε v ω hH hDiss hT hZero hg hcq hε hεOne hmesh hv hrH hrD Pw hPw J hJ seed hSeed
      exact ⟨d, E, hE, q, hU, hC⟩
    · push Not at hZero
      have hε' : 0 < TimeDependentODE.accuracy ε := by
        unfold TimeDependentODE.accuracy
        linarith
      have hε'One : TimeDependentODE.accuracy ε ≤ 1 := by
        unfold TimeDependentODE.accuracy
        linarith
      have hR : 0 ≤ TimeDependentODE.radius (cq * gbar) ε :=
        le_trans (by norm_num : (0 : ℝ) ≤ 4)
          (ODEGaussianParameters.radius_ge_four _ _ hg1 hε' hε'One)
      have hT' : 0 < T := lt_of_le_of_ne hT (Ne.symm hZero.1)
      have hρ : 0 < etaH + TimeDependentODE.radius (cq * gbar) ε * etaD :=
        lt_of_le_of_ne (by positivity) (Ne.symm hZero.2)
      exact RepresentedSampleODE.robust_propagated_solver D hM t hN etaH etaD T gbar cq ε v ω hH
        hDiss hT' hg hcq hε hεOne hmesh hρ hClock hCayley hv hrH hcH hrD hcD Pw hPw J hJ seed hSeed
  obtain ⟨d, E, hE, q, -, hCert⟩ := hOut
  -- The public seed and output, and the substitution of the separate source primitives.
  obtain ⟨hMpos, -, -⟩ := ODEGroverAverage.chosenIterations_bounds
    (TimeDependentODE.ratio (cq * gbar)) hg1
  have hcpos : 0 < ODECoherentLCU.coefficientMass
      (TimeDependentODE.lchsCoefficients D T (cq * gbar) ε) := by
    rw [Mesh.lchsCoefficients_mass D hT (cq * gbar) ε hg1 hε hεOne]
    norm_num
  have hψ := MeshNative.seed_unit D hM (Sum.inr false) m N d E hE
    (TimeDependentODE.lchsCoefficients D T (cq * gbar) ε) hcpos seed hSeed
  have hF := MeshNative.output_isometry D hM (Sum.inr false) m N d E hE
    (TimeDependentODE.lchsCoefficients D T (cq * gbar) ε) hcpos
  let q' := MeshOracles.actualTrials D m N d Pw J (GeneralSourceODE.phases ω)
    (GeneralSourceODE.phases_norm ω) q
  have hEval : ∀ j x, (q' j).eval x = (q j).eval x := fun j x =>
    MultiOracleCircuit.Program.eval_substitute (q j) _
      (MeshOracles.implementation_eval D m N d Pw J (GeneralSourceODE.phases ω)
        (GeneralSourceODE.phases_norm ω)) x
  have hCost : ∀ (w : Query ⊕ GeneralSourceODE.SourceCall → ℕ) (j : ℕ),
      (q' j).cost w = (q j).cost (fun l =>
        (MeshOracles.implementation D m N d Pw J (GeneralSourceODE.phases ω)
          (GeneralSourceODE.phases_norm ω) l).cost w) :=
    fun w j => MultiOracleCircuit.Program.cost_substitute (q j) _ w
  have hMatrix : ∀ j, (q' j).cost GeneralSourceODE.Oracles.matrixCalls =
      (q j).cost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) := fun j => by
    rw [hCost]
    exact congrArg (q j).cost (funext (MeshOracles.implementation_matrix D m N d Pw J _ _))
  refine ⟨d, ODERepeatProtocol.ofCircuits q'
    (ODEGroverAverage.chosenIterations (TimeDependentODE.ratio (cq * gbar))) hMpos _ hψ _ hF,
    fun x G b sol bv U ζ hG hreg hsol hUm hW hL0 hL hMass hInt hTarget hB hB1 hB2 => ?_⟩
  have hD : sol T - U 0 (sol 0) T =
      ∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1), U u (b r u) T := by
    rw [hsol.2]
    abel
  have hCertP : ‖sol T - U 0 (sol 0) T - ∑ i, ω i • U (v i) (bv i) T‖ ≤
      ζ * Mesh.meshScale sol b t := by
    rw [hD]
    exact hInt
  have hC := hCert x G b sol bv U ζ hG hreg hUm hW hL0 hL hMass hCertP hTarget hB
    (RepresentedSampleODE.robustBudget_of_path_int D x hmesh G hG hreg hB1 hB2)
  have hA := GeneralSourceODE.Oracles.actual_certificate hC q' hMpos hψ hF (fun j => hEval j x)
    hMatrix
    (fun j => by
      rw [hCost]
      exact congrArg (q j).cost (funext (MeshOracles.implementation_weight D m N d Pw J _ _)))
    (fun j => by
      rw [hCost]
      exact congrArg (q j).cost (funext (MeshOracles.implementation_load D m N d Pw J _ _)))
    (fun j => by
      rw [hCost]
      exact congrArg (q j).cost (funext (MeshOracles.implementation_unweight D m N d Pw J _ _)))
    (fun j => by
      rw [hCost, funext (MeshOracles.implementation_source D m N d Pw J _ _),
        GeneralSourceODE.Oracles.cost_add, NativeHermitianDilation.cost_scale])
  have hTC : TrialsClose (ODERepeatProtocol.ofCircuits q'
      (ODEGroverAverage.chosenIterations (TimeDependentODE.ratio (cq * gbar))) hMpos _ hψ _ hF)
      x (sol T) ε :=
    trialsClose_congr hMpos hψ hF (fun j => hEval j x)
      (trialsClose_of_certificate hMpos hψ hF hC hε.le)
  refine ⟨⟨hA.success_two_thirds, hA.output_density, hA.conditional_error⟩, hTC,
    historiesClose_of_trialsClose hTC, ?_, ?_⟩
  · refine hA.matrix_queries.trans (le_of_eq ?_)
    rw [ImprovedODEQueryBudget.queryShape, ImprovedODEQueryBudget.theta, time_log_eq]
    unfold TimeDependentODE.ratio
    ring
  · refine hA.source_calls.trans ?_
    unfold TimeDependentODE.ratio
    have : 0 ≤ cq * gbar := by positivity
    nlinarith

end

end ManuscriptConformance
