import GateEfficientODE.Time.Certificate
import SparseODE.ODECompleteSuccess

/-!
# The complete time-dependent gate-level protocol

The trial circuits are read as released multi-oracle programs whose labels
are the instructions (`program`), so weighted costs count elementary gates,
slot-selected private calls, `U_J` calls, loading calls, weight-preparation
calls and seed reflections exactly.  The complete protocol is the released
bounded four-attempt wrapper `ODERepeatProtocol.fourTrials` with the uniform
trial count `j < chosenIterations (2 g)`.

* `protocol_worst`: over every history, including four failures, at most
  `80 g · prepGates + 40 g · reflGates` elementary gates, `480 g d` private
  calls, `960 g d` calls of `U_J` or `U_J†`, `80 g` loading calls, `160 g`
  weight-preparation calls and `40 g` seed reflections.
* `outcome`: for every valid instance, success at least `175/256 > 2/3`, and
  the conditional output is a density operator within trace distance `ε` of
  `x(T) / ‖x(T)‖`.
-/

namespace SparseHamiltonian.GateODE.Time

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit
open GateCircuit.Sim (Wire)
open scoped InnerProduct BigOperators

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

namespace TParams

variable (p : TParams)

/-! ### Weights and programs -/

/-- Counts elementary gates. -/
def wGate : p.Ins → ℕ := fun g => if g.isGate then 1 else 0
/-- Counts slot-selected private Cayley calls (forward or inverse). -/
def wPriv : p.Ins → ℕ := fun g => if g.isPriv then 1 else 0
/-- Counts calls of `U_J` or `U_J†`. -/
def wUJ : p.Ins → ℕ := fun g => if g.isUJ then 1 else 0
/-- Counts calls of the source loading (forward or inverse). -/
def wLoad : p.Ins → ℕ := fun g => if g.isSrc false then 1 else 0
/-- Counts calls of the weight preparation (forward or inverse). -/
def wPrep : p.Ins → ℕ := fun g => if g.isSrc true then 1 else 0
/-- Counts seed reflections. -/
def wSeed : p.Ins → ℕ := fun g => if g.isSeed then 1 else 0

/-- The trial with `j` steps as a released multi-oracle program. -/
def program (v : P) (j : ℕ) :
    MultiOracleCircuit.Program (tfamily (a := p.a) (m := p.m) (r := p.r) (K := p.K) (k := p.m)
      (l := p.l) (f := p.f) v) :=
  ttoProgram v (p.trialC j)

theorem program_eval (v : P) (σ : TOracles p.a p.m p.l P) (j : ℕ) :
    (p.program v j).eval σ = trun v σ (p.trialC j) :=
  ttoProgram_eval _ _ _

theorem program_cost (v : P) (j : ℕ) :
    (p.program v j).cost p.wGate = nGates (p.trialC j) ∧
    (p.program v j).cost p.wPriv = nPriv (p.trialC j) ∧
    (p.program v j).cost p.wUJ = nUJ (p.trialC j) ∧
    (p.program v j).cost p.wLoad = nSrc false (p.trialC j) ∧
    (p.program v j).cost p.wPrep = nSrc true (p.trialC j) ∧
    (p.program v j).cost p.wSeed = nSeed (p.trialC j) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · rw [program, ttoProgram_cost]
    exact sum_map_indicator _ _

/-- The complete bounded four-attempt protocol. -/
def protocol (v : P) (hv : ‖v‖ = 1) (hg : 1 ≤ p.g) :
    ODERepeatProtocol.Protocol (tfamily (a := p.a) (m := p.m) (r := p.r) (K := p.K) (k := p.m)
      (l := p.l) (f := p.f) v) P :=
  ODERepeatProtocol.fourTrials (p.program v) (ODEGroverAverage.chosenIterations p.ratio)
    (ODEGroverAverage.chosenIterations_bounds p.ratio (p.ratio_ge hg)).1 (seedState v)
    (seedState_norm v hv) goodF goodF_isometry

/-! ### Worst-case counts -/

theorem trial_cost_bound (hp : p.PublicOK) (v : P) (j : ℕ)
    (hj : j < ODEGroverAverage.chosenIterations p.ratio) :
    ((p.program v j).cost p.wGate : ℝ) ≤ 20 * p.g * p.prepGates + 10 * p.g * p.reflGates ∧
    ((p.program v j).cost p.wPriv : ℝ) ≤ 120 * p.g * p.d ∧
    ((p.program v j).cost p.wUJ : ℝ) ≤ 240 * p.g * p.d ∧
    ((p.program v j).cost p.wLoad : ℝ) ≤ 20 * p.g ∧
    ((p.program v j).cost p.wPrep : ℝ) ≤ 40 * p.g ∧
    ((p.program v j).cost p.wSeed : ℝ) ≤ 10 * p.g := by
  obtain ⟨cG, cP, cU, cL, cW, cE⟩ := p.program_cost v j
  obtain ⟨tP, tU, tL, tW, tE, tG⟩ := p.trialC_counts hp.tau_pos.le hp.nu_pos hp.mesh j
  have hM := (ODEGroverAverage.chosenIterations_bounds p.ratio (p.ratio_ge hp.g_ge)).2.2
  have hjM : (j : ℝ) + 1 ≤ ODEGroverAverage.chosenIterations p.ratio := by exact_mod_cast hj
  have hr : p.ratio = 2 * p.g := rfl
  have hj1 : (2 * (j : ℝ) + 1) ≤ 20 * p.g := by
    have := hp.g_ge
    rw [hr] at hM
    linarith
  have hj2 : (j : ℝ) ≤ 10 * p.g := by
    rw [hr] at hM
    linarith
  rw [cG, cP, cU, cL, cW, cE]
  clear cG cP cU cL cW cE
  generalize nGates (p.trialC j) = nG at tG ⊢
  generalize nPriv (p.trialC j) = nP at tP ⊢
  generalize nUJ (p.trialC j) = nU at tU ⊢
  generalize nSrc false (p.trialC j) = nL at tL ⊢
  generalize nSrc true (p.trialC j) = nW at tW ⊢
  generalize nSeed (p.trialC j) = nE at tE ⊢
  generalize p.prepGates = Gp at tG ⊢
  generalize p.reflGates = Rg at tG ⊢
  generalize p.d = D at tP tU ⊢
  have hD : (0 : ℝ) ≤ D := Nat.cast_nonneg _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h : (nG : ℝ) ≤ (2 * j + 1) * Gp + j * Rg := by exact_mod_cast tG
    have h1 : (2 * (j : ℝ) + 1) * Gp ≤ 20 * p.g * Gp :=
      mul_le_mul_of_nonneg_right hj1 (Nat.cast_nonneg _)
    have h2 : (j : ℝ) * Rg ≤ 10 * p.g * Rg :=
      mul_le_mul_of_nonneg_right hj2 (Nat.cast_nonneg _)
    linarith
  · have h1 : (2 * (j : ℝ) + 1) * (6 * D) ≤ 20 * p.g * (6 * D) :=
      mul_le_mul_of_nonneg_right hj1 (mul_nonneg (by norm_num) hD)
    rw [tP]
    push_cast
    linarith
  · have h1 : (2 * (j : ℝ) + 1) * (12 * D) ≤ 20 * p.g * (12 * D) :=
      mul_le_mul_of_nonneg_right hj1 (mul_nonneg (by norm_num) hD)
    rw [tU]
    push_cast
    linarith
  · rw [tL]
    push_cast
    linarith
  · rw [tW]
    push_cast
    linarith
  · rw [tE]
    exact hj2

/-- **Worst-case counts of the complete protocol**, over every history. -/
theorem protocol_worst (hp : p.PublicOK) (v : P) (hv : ‖v‖ = 1) :
    ((p.protocol v hv hp.g_ge).worstCost p.wGate : ℝ) ≤
      80 * p.g * p.prepGates + 40 * p.g * p.reflGates ∧
    ((p.protocol v hv hp.g_ge).worstCost p.wPriv : ℝ) ≤ 480 * p.g * p.d ∧
    ((p.protocol v hv hp.g_ge).worstCost p.wUJ : ℝ) ≤ 960 * p.g * p.d ∧
    ((p.protocol v hv hp.g_ge).worstCost p.wLoad : ℝ) ≤ 80 * p.g ∧
    ((p.protocol v hv hp.g_ge).worstCost p.wPrep : ℝ) ≤ 160 * p.g ∧
    ((p.protocol v hv hp.g_ge).worstCost p.wSeed : ℝ) ≤ 40 * p.g := by
  have hW := fun w B (h : ∀ j, j < ODEGroverAverage.chosenIterations p.ratio →
      ((p.program v j).cost w : ℝ) ≤ B) =>
    ODERepeatProtocol.fourTrials_worstCost_le (p.program v)
      (ODEGroverAverage.chosenIterations p.ratio)
      (ODEGroverAverage.chosenIterations_bounds p.ratio (p.ratio_ge hp.g_ge)).1 (seedState v)
      (seedState_norm v hv) goodF goodF_isometry w B h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h := hW p.wGate _ (fun j hj => (p.trial_cost_bound hp v j hj).1)
    unfold protocol
    linarith
  · have h := hW p.wPriv _ (fun j hj => (p.trial_cost_bound hp v j hj).2.1)
    unfold protocol
    linarith
  · have h := hW p.wUJ _ (fun j hj => (p.trial_cost_bound hp v j hj).2.2.1)
    unfold protocol
    linarith
  · have h := hW p.wLoad _ (fun j hj => (p.trial_cost_bound hp v j hj).2.2.2.1)
    unfold protocol
    linarith
  · have h := hW p.wPrep _ (fun j hj => (p.trial_cost_bound hp v j hj).2.2.2.2.1)
    unfold protocol
    linarith
  · have h := hW p.wSeed _ (fun j hj => (p.trial_cost_bound hp v j hj).2.2.2.2.2)
    unfold protocol
    linarith

/-! ### Success and the conditional output -/

/-- The public trial family: a uniform trial count `j < chosenIterations (2g)`. -/
def trials (v : P) (hv : ‖v‖ = 1) (hg : 1 ≤ p.g) :
    ODERepeatProtocol.TrialFamily (tfamily (a := p.a) (m := p.m) (r := p.r) (K := p.K)
      (k := p.m) (l := p.l) (f := p.f) v) P :=
  ODERepeatProtocol.ofCircuits (p.program v) (ODEGroverAverage.chosenIterations p.ratio)
    (ODEGroverAverage.chosenIterations_bounds p.ratio (p.ratio_ge hg)).1 (seedState v)
    (seedState_norm v hv) goodF goodF_isometry

theorem protocol_eq (v : P) (hv : ‖v‖ = 1) (hg : 1 ≤ p.g) :
    p.protocol v hv hg = ODERepeatProtocol.Protocol.repeatTrials (p.trials v hv hg) 4 := rfl

theorem trials_choices (v : P) (hv : ‖v‖ = 1) (hg : 1 ≤ p.g) :
    (p.trials v hv hg).choices = ODEGroverAverage.chosenIterations p.ratio := rfl

theorem trials_eval (v : P) (hv : ‖v‖ = 1) (hg : 1 ≤ p.g) (σ : TOracles p.a p.m p.l P)
    (j : Fin (p.trials v hv hg).choices) :
    ((p.trials v hv hg).circuit j).eval σ = trun v σ (p.trialC j.val) :=
  p.program_eval v σ j.val

theorem trials_output (v : P) (hv : ‖v‖ = 1) (hg : 1 ≤ p.g) :
    (p.trials v hv hg).output = goodF := rfl

theorem trials_seed (v : P) (hv : ‖v‖ = 1) (hg : 1 ≤ p.g) :
    (p.trials v hv hg).seed = seedState v := rfl

theorem trials_amplitude (v : P) (hv : ‖v‖ = 1) (hg : 1 ≤ p.g)
    (σ : TOracles p.a p.m p.l P) (j : Fin (p.trials v hv hg).choices) :
    (p.trials v hv hg).amplitude σ j =
      (goodF†) (trun v σ (p.trialC j.val) (seedState v)) := by
  rw [ODERepeatProtocol.TrialFamily.amplitude, p.trials_eval, p.trials_output, p.trials_seed]

variable [FiniteDimensional ℂ P]

/-- The guarantees of the complete protocol for one instance with final
state `x`. -/
structure Outcome (v : P) (hv : ‖v‖ = 1) (hg : 1 ≤ p.g) (σ : TOracles p.a p.m p.l P)
    (x : P) : Prop where
  unitary_trials : ∀ j, IsUnitary (trun v σ (p.trialC j))
  mean_success : (1 : ℝ) / 4 ≤
    (∑ j ∈ Finset.range (ODEGroverAverage.chosenIterations p.ratio),
      ‖ODEHeraldedSuccess.successProjector goodF
        (trun v σ (p.trialC j) (seedState v))‖ ^ 2) /
      (ODEGroverAverage.chosenIterations p.ratio : ℝ)
  trial_direction : ∀ j : ℕ, (goodF†) (trun v σ (p.trialC j) (seedState v)) ≠ 0 →
    ∃ ω : ℂ, ‖ω‖ = 1 ∧
      ‖ω • ODEStateNormalization.unitDirection
          ((goodF†) (trun v σ (p.trialC j) (seedState v))) -
        ODEStateNormalization.unitDirection x‖ ≤ p.ε / 500
  success_lower : (175 : ℝ) / 256 ≤ (p.protocol v hv hg).successMass σ
  success_two_thirds : (2 : ℝ) / 3 ≤ (p.protocol v hv hg).successMass σ
  output_density : ODEMixedOutput.IsDensity ((p.protocol v hv hg).conditionalDensity σ)
  conditional_error :
    ∃ h : ((p.protocol v hv hg).conditionalDensity σ -
        ODEMixedOutput.pureOperator (ODEStateNormalization.unitDirection x)).toLinearMap.IsSymmetric,
      ODEMixedOutput.hermitianTraceDistance ((p.protocol v hv hg).conditionalDensity σ)
        (ODEMixedOutput.pureOperator (ODEStateNormalization.unitDirection x)) h ≤ p.ε

/-- **The complete time-dependent protocol is correct for every valid
instance.** -/
theorem outcome (hp : p.PublicOK) (v : P) (hv : ‖v‖ = 1) (σ : TOracles p.a p.m p.l P)
    (Hs Ls : ℕ → P →L[ℂ] P) (G : ℝ → P →L[ℂ] P) (b x : ℝ → P) (bs : ℕ → P)
    (βG δG βb δb bmax : ℝ) (hI : p.InstanceOK v σ Hs Ls G b x bs βG δG βb δb bmax) :
    p.Outcome v hv hp.g_ge σ (x p.T) := by
  have hU := p.unitary_of hI
  have hunit : ∀ j, IsUnitary (trun v σ (p.trialC j)) := fun j =>
    trun_isUnitary v σ hU hv _ (p.trialC_valid hp.tau_pos.le hp.nu_pos hp.mesh j)
  obtain ⟨hM, _, hmean, hdir⟩ := p.trial_bounds hp v hv σ Hs Ls G b x bs βG δG βb δb bmax hI
  have hunitT : ∀ j, IsUnitary (((p.trials v hv hp.g_ge).circuit j).eval σ) := by
    intro j
    rw [p.trials_eval]
    exact hunit _
  have hprob : ∀ j, (p.trials v hv hp.g_ge).probability σ j =
      ‖ODEHeraldedSuccess.successProjector goodF
        (trun v σ (p.trialC j.val) (seedState v))‖ ^ 2 := by
    intro j
    rw [(p.trials v hv hp.g_ge).probability_eq_projected σ j, p.trials_eval, p.trials_output,
      p.trials_seed]
  have hsumP : ∑ j : Fin (p.trials v hv hp.g_ge).choices, (p.trials v hv hp.g_ge).probability σ j =
      ∑ j ∈ Finset.range (ODEGroverAverage.chosenIterations p.ratio),
        ‖ODEHeraldedSuccess.successProjector goodF
          (trun v σ (p.trialC j) (seedState v))‖ ^ 2 := by
    rw [Finset.sum_congr rfl (fun j _ => hprob j)]
    exact Fin.sum_univ_eq_sum_range (fun j => ‖ODEHeraldedSuccess.successProjector goodF
      (trun v σ (p.trialC j) (seedState v))‖ ^ 2) _
  have hmeanT : (1 : ℝ) / 4 ≤
      ODERepeatProbability.mean ((p.trials v hv hp.g_ge).probability σ) := by
    unfold ODERepeatProbability.mean
    rw [hsumP]
    exact hmean
  have hupper : ODERepeatProbability.mean ((p.trials v hv hp.g_ge).probability σ) ≤ 1 :=
    ODERepeatProbability.mean_le_one _ (p.trials v hv hp.g_ge).choices_pos
      (fun j => ((p.trials v hv hp.g_ge).probability_bounds σ hunitT j).2)
  have hnonneg : ∀ j, 0 ≤ (p.trials v hv hp.g_ge).probability σ j :=
    fun j => ((p.trials v hv hp.g_ge).probability_bounds σ hunitT j).1
  have hsucc : (p.protocol v hv hp.g_ge).successMass σ =
      ODERepeatProbability.successProbability ((p.trials v hv hp.g_ge).probability σ) :=
    ODERepeatProtocol.Protocol.four_successMass_eq (p.trials v hv hp.g_ge) σ
  have hdens : (p.protocol v hv hp.g_ge).conditionalDensity σ =
      ODEMixedOutput.ensemble
        (ODERepeatProbability.conditionalWeight ((p.trials v hv hp.g_ge).probability σ))
        (fun a => (p.trials v hv hp.g_ge).outputDirection σ a.2) :=
    ODERepeatProtocol.Protocol.four_conditionalDensity_eq (p.trials v hv hp.g_ge) σ
  have hw := ODERepeatProbability.conditionalWeight_nonneg _ hnonneg hmeanT hupper
  have hsum := ODERepeatProbability.conditionalWeight_sum _ hmeanT hupper
  have hne : ∀ a : Fin 4 × Fin (p.trials v hv hp.g_ge).choices,
      ODERepeatProbability.conditionalWeight ((p.trials v hv hp.g_ge).probability σ) a ≠ 0 →
      (p.trials v hv hp.g_ge).amplitude σ a.2 ≠ 0 := by
    intro a ha hz
    apply ODERepeatProbability.conditionalWeight_ne_zero_implies _ a ha
    rw [ODERepeatProtocol.TrialFamily.probability, hz, norm_zero]
    norm_num
  have hclose : ∀ a : Fin 4 × Fin (p.trials v hv hp.g_ge).choices,
      ODERepeatProbability.conditionalWeight ((p.trials v hv hp.g_ge).probability σ) a ≠ 0 →
      ∃ ω : ℂ, ‖ω‖ = 1 ∧ ‖ω • (p.trials v hv hp.g_ge).outputDirection σ a.2 -
        ODEStateNormalization.unitDirection (x p.T)‖ ≤ p.ε / 500 := by
    intro a ha
    have hz := hne a ha
    rw [p.trials_amplitude] at hz
    have h := hdir a.2.val hz
    rw [ODERepeatProtocol.TrialFamily.outputDirection, p.trials_amplitude]
    exact h
  have hunitDir : ∀ a : Fin 4 × Fin (p.trials v hv hp.g_ge).choices,
      ODERepeatProbability.conditionalWeight ((p.trials v hv hp.g_ge).probability σ) a ≠ 0 →
      ‖(p.trials v hv hp.g_ge).outputDirection σ a.2‖ = 1 :=
    fun a ha => ODEStateNormalization.unitDirection_norm _ (hne a ha)
  obtain ⟨hDensity, hSymm, hDistance⟩ := ODEMixedOutput.ensemble_trace_distance_le
    (ODERepeatProbability.conditionalWeight ((p.trials v hv hp.g_ge).probability σ))
    (fun a => (p.trials v hv hp.g_ge).outputDirection σ a.2)
    (ODEStateNormalization.unitDirection (x p.T)) (p.ε / 500) hw hsum
    hunitDir (ODEStateNormalization.unitDirection_norm _ hI.target_ne) hclose
  have hlow : (175 : ℝ) / 256 ≤ (p.protocol v hv hp.g_ge).successMass σ := by
    rw [hsucc]
    exact ODERepeatProbability.successProbability_lower _ hmeanT hupper
  have htwo : (2 : ℝ) / 3 ≤ (p.protocol v hv hp.g_ge).successMass σ := by
    rw [hsucc]
    exact ODERepeatProbability.successProbability_two_thirds _ hmeanT hupper
  have hden : ODEMixedOutput.IsDensity ((p.protocol v hv hp.g_ge).conditionalDensity σ) := by
    rw [hdens]
    exact hDensity
  have herr : ∃ h : ((p.protocol v hv hp.g_ge).conditionalDensity σ -
        ODEMixedOutput.pureOperator
          (ODEStateNormalization.unitDirection (x p.T))).toLinearMap.IsSymmetric,
      ODEMixedOutput.hermitianTraceDistance ((p.protocol v hv hp.g_ge).conditionalDensity σ)
        (ODEMixedOutput.pureOperator
          (ODEStateNormalization.unitDirection (x p.T))) h ≤ p.ε := by
    rw [hdens]
    refine ⟨hSymm, hDistance.trans ?_⟩
    have := hp.ε_pos
    linarith
  exact ⟨hunit, hmean, hdir, hlow, htwo, hden, herr⟩

end TParams

end

end SparseHamiltonian.GateODE.Time
