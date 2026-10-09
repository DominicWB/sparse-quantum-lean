import ZeroTimeGateODE.ExactCircuit
import ZeroTimeGateODE.Combined

/-!
# Zero time or a known zero generator with exact gates: the protocol and the solver

The exact-gate form of the remark of Theorem `ode:thm:gates` (constant coefficients).  The
zero-case trials `ztrialE p j` are read as released multi-oracle programs (`zprogram`), and the
protocol is the released bounded four-attempt wrapper `ODERepeatProtocol.fourTrials` with the
released public cutoff `ODEGroverAverage.chosenIterations g` (`zprotocol`), as for the released
`GateODE.Params.protocol`.

* `zprotocol_worst`: in every history at most `40 g · 2 + 20 g · reflGates` elementary gates,
  no private call, no `U_J` call, at most `40 g` calls of each source interface and `20 g` seed
  reflections.
* `ztrial_bounds`: the amplitude of the zero-case preparation is `‖x₀ + T b‖ / B ≥ 1/g`, its
  decoded vector has the direction of `x₀ + T b`, and `randomized_certificate_full` gives the
  mean success and the direction of every successful trial.
* `zoutcome`: the guarantees `ZOutcome` (the fields of the released
  `GateODE.Params.Outcome` for the zero-case trials and protocol).
* `exact_ode_solver_zero`: the exact-gate solver in the zero case.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.ZeroTimeGateODE

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit
open GateCircuit.Sim (Wire)
open GateODE (Params OInstr OWire AW Label Oracles wiring run seedState seedState_norm goodF
  goodF_isometry nGates nPriv nUJ nSrc nSeed)
open ODEStateNormalization (unitDirection)
open scoped InnerProduct BigOperators

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-! ### The protocol -/

section Protocol

variable (p : Params)

/-- The zero-case trial with `j` steps as a released multi-oracle program. -/
def zprogram (v : P) (j : ℕ) :
    MultiOracleCircuit.Program (GateODE.family (wiring (a := p.a) (m := p.m) (r := p.r)
      (K := p.K) (k := p.k) (l := p.l) (f := p.f) v)) :=
  GateODE.toProgram (wiring v) (ztrialE p j)

theorem zprogram_eval (v : P) (σ : Oracles p.a (Label p.k p.l) P) (j : ℕ) :
    (zprogram p v j).eval σ = run (wiring v) σ (ztrialE p j) :=
  GateODE.toProgram_eval _ _ _

theorem zprogram_cost (v : P) (j : ℕ) :
    (zprogram p v j).cost p.wGate = nGates (ztrialE p j) ∧
    (zprogram p v j).cost p.wPriv = nPriv (ztrialE p j) ∧
    (zprogram p v j).cost p.wUJ = nUJ (ztrialE p j) ∧
    (∀ c, (zprogram p v j).cost (p.wSrc c) = nSrc c (ztrialE p j)) ∧
    (zprogram p v j).cost p.wSeed = nSeed (ztrialE p j) := by
  refine ⟨?_, ?_, ?_, fun c => ?_, ?_⟩ <;>
  · rw [zprogram, GateODE.toProgram_cost]
    exact GateODE.sum_map_indicator _ _

/-- **The zero-case protocol**: the released bounded four-attempt wrapper around the zero-case
trials, with the released public cutoff. -/
def zprotocol (v : P) (hv : ‖v‖ = 1) (hg : 1 ≤ p.g) :
    ODERepeatProtocol.Protocol (GateODE.family (wiring (a := p.a) (m := p.m) (r := p.r)
      (K := p.K) (k := p.k) (l := p.l) (f := p.f) v)) P :=
  ODERepeatProtocol.fourTrials (zprogram p v) (ODEGroverAverage.chosenIterations p.g)
    (ODEGroverAverage.chosenIterations_bounds p.g hg).1 (seedState v) (seedState_norm v hv)
    goodF goodF_isometry

/-- The public trial family of the zero case. -/
def ztrials (v : P) (hv : ‖v‖ = 1) (hg : 1 ≤ p.g) :
    ODERepeatProtocol.TrialFamily (GateODE.family (wiring (a := p.a) (m := p.m) (r := p.r)
      (K := p.K) (k := p.k) (l := p.l) (f := p.f) v)) P :=
  ODERepeatProtocol.ofCircuits (zprogram p v) (ODEGroverAverage.chosenIterations p.g)
    (ODEGroverAverage.chosenIterations_bounds p.g hg).1 (seedState v) (seedState_norm v hv)
    goodF goodF_isometry

theorem zprotocol_eq (v : P) (hv : ‖v‖ = 1) (hg : 1 ≤ p.g) :
    zprotocol p v hv hg = ODERepeatProtocol.Protocol.repeatTrials (ztrials p v hv hg) 4 := rfl

theorem ztrials_eval (v : P) (hv : ‖v‖ = 1) (hg : 1 ≤ p.g) (σ : Oracles p.a (Label p.k p.l) P)
    (j : Fin (ztrials p v hv hg).choices) :
    ((ztrials p v hv hg).circuit j).eval σ = run (wiring v) σ (ztrialE p j.val) :=
  zprogram_eval p v σ j.val

theorem ztrials_output (v : P) (hv : ‖v‖ = 1) (hg : 1 ≤ p.g) :
    (ztrials p v hv hg).output = goodF := rfl

theorem ztrials_seed (v : P) (hv : ‖v‖ = 1) (hg : 1 ≤ p.g) :
    (ztrials p v hv hg).seed = seedState v := rfl

theorem ztrials_amplitude (v : P) (hv : ‖v‖ = 1) (hg : 1 ≤ p.g)
    (σ : Oracles p.a (Label p.k p.l) P) (j : Fin (ztrials p v hv hg).choices) :
    (ztrials p v hv hg).amplitude σ j =
      (goodF†) (run (wiring v) σ (ztrialE p j.val) (seedState v)) := by
  rw [ODERepeatProtocol.TrialFamily.amplitude, ztrials_eval p v hv hg σ j,
    ztrials_output p v hv hg, ztrials_seed p v hv hg]

end Protocol

/-! ### Worst-case counts -/

section Worst

variable (p : Params)

theorem ztrial_cost_bound (hg : 1 ≤ p.g) (v : P) (j : ℕ)
    (hj : j < ODEGroverAverage.chosenIterations p.g) :
    ((zprogram p v j).cost p.wGate : ℝ) ≤ 10 * p.g * 2 + 5 * p.g * p.reflGates ∧
    (zprogram p v j).cost p.wPriv = 0 ∧
    (zprogram p v j).cost p.wUJ = 0 ∧
    (∀ c, ((zprogram p v j).cost (p.wSrc c) : ℝ) ≤ 10 * p.g) ∧
    ((zprogram p v j).cost p.wSeed : ℝ) ≤ 5 * p.g := by
  obtain ⟨cG, cP, cU, cS, cE⟩ := zprogram_cost p v j
  obtain ⟨tP, tU, tS, tE, tG⟩ := ztrialE_counts p j
  have hM := (ODEGroverAverage.chosenIterations_bounds p.g hg).2.2
  have hjM : (j : ℝ) + 1 ≤ ODEGroverAverage.chosenIterations p.g := by exact_mod_cast hj
  have hj1 : (2 * (j : ℝ) + 1) ≤ 10 * p.g := by linarith
  have hj2 : (j : ℝ) ≤ 5 * p.g := by linarith
  rw [cG, cP, cU, cE, tP, tU, tE]
  simp only [cS, tS]
  refine ⟨?_, trivial, trivial, fun c => ?_, hj2⟩
  · generalize p.reflGates = Rg at tG ⊢
    have h : (nGates (ztrialE p j) : ℝ) ≤ (2 * j + 1) * 2 + j * Rg := by exact_mod_cast tG
    have h1 : (2 * (j : ℝ) + 1) * 2 ≤ 10 * p.g * 2 := by linarith
    have h2 : (j : ℝ) * Rg ≤ 5 * p.g * Rg := mul_le_mul_of_nonneg_right hj2 (Nat.cast_nonneg _)
    linarith
  · push_cast
    linarith

/-- **Worst-case counts of the zero-case protocol**, over every history: at most
`40 g · 2 + 20 g · reflGates` elementary gates, no private call and no `U_J` call, at most
`40 g` calls of each source interface and `20 g` seed reflections. -/
theorem zprotocol_worst (hg : 1 ≤ p.g) (v : P) (hv : ‖v‖ = 1) :
    ((zprotocol p v hv hg).worstCost p.wGate : ℝ) ≤ 40 * p.g * 2 + 20 * p.g * p.reflGates ∧
    (zprotocol p v hv hg).worstCost p.wPriv = 0 ∧
    (zprotocol p v hv hg).worstCost p.wUJ = 0 ∧
    (∀ c, ((zprotocol p v hv hg).worstCost (p.wSrc c) : ℝ) ≤ 40 * p.g) ∧
    ((zprotocol p v hv hg).worstCost p.wSeed : ℝ) ≤ 20 * p.g := by
  have hW := fun w B (h : ∀ j, j < ODEGroverAverage.chosenIterations p.g →
      ((zprogram p v j).cost w : ℝ) ≤ B) =>
    ODERepeatProtocol.fourTrials_worstCost_le (zprogram p v)
      (ODEGroverAverage.chosenIterations p.g) (ODEGroverAverage.chosenIterations_bounds p.g hg).1
      (seedState v) (seedState_norm v hv) goodF goodF_isometry w B h
  refine ⟨?_, ?_, ?_, fun c => ?_, ?_⟩
  · have h := hW p.wGate _ (fun j hj => (ztrial_cost_bound p hg v j hj).1)
    unfold zprotocol
    linarith
  · have h := hW p.wPriv 0 (fun j hj => by
      rw [(ztrial_cost_bound p hg v j hj).2.1]
      norm_num)
    have h0 : ((zprotocol p v hv hg).worstCost p.wPriv : ℝ) ≤ 0 := by
      unfold zprotocol
      linarith
    exact_mod_cast le_antisymm h0 (Nat.cast_nonneg _)
  · have h := hW p.wUJ 0 (fun j hj => by
      rw [(ztrial_cost_bound p hg v j hj).2.2.1]
      norm_num)
    have h0 : ((zprotocol p v hv hg).worstCost p.wUJ : ℝ) ≤ 0 := by
      unfold zprotocol
      linarith
    exact_mod_cast le_antisymm h0 (Nat.cast_nonneg _)
  · have h := hW (p.wSrc c) _ (fun j hj => (ztrial_cost_bound p hg v j hj).2.2.2.1 c)
    unfold zprotocol
    linarith
  · have h := hW p.wSeed _ (fun j hj => (ztrial_cost_bound p hg v j hj).2.2.2.2)
    unfold zprotocol
    linarith

end Worst

/-! ### Success and the conditional output -/

section Outcome

variable (p : Params)

/-- **Mean success and direction error of the zero-case trials**: the amplitude of the
zero-case preparation is `‖x₀ + T b‖ / B ≥ 1/g`, its decoded vector has the direction of
`x₀ + T b`, and the amplification for amplitudes up to one (`randomized_certificate_full`)
applies. -/
theorem ztrial_bounds (hp : PublicOK0 p) (hz : ZeroCase p) (v : P) (hv : ‖v‖ = 1)
    (σ : Oracles p.a (Label p.k p.l) P) (H L : P →L[ℂ] P) (x0 b : P)
    (hI : ZInstanceOK p v σ.J H L x0 b) :
    0 < ODEGroverAverage.chosenIterations p.g ∧
    (ODEGroverAverage.chosenIterations p.g : ℝ) ≤ 5 * p.g ∧
    (1 : ℝ) / 4 ≤ (∑ j ∈ Finset.range (ODEGroverAverage.chosenIterations p.g),
      ‖ODEHeraldedSuccess.successProjector goodF
        (run (wiring v) σ (ztrialE p j) (seedState v))‖ ^ 2) /
        (ODEGroverAverage.chosenIterations p.g : ℝ) ∧
    ∀ j : ℕ, (goodF†) (run (wiring v) σ (ztrialE p j) (seedState v)) ≠ 0 →
      ∃ ω : ℂ, ‖ω‖ = 1 ∧
        ‖ω • unitDirection ((goodF†) (run (wiring v) σ (ztrialE p j) (seedState v))) -
          unitDirection (p.target H L x0 b)‖ ≤ p.ε / 500 := by
  have hW := zprepE_isUnitary p hp.r₀_nonneg hp.rb_nonneg hp.T_nonneg hp.B_pos v hv σ
    hI.src_unitary
  have ht := target_zero hp hz H L x0 b hI.normH hI.normL
  have hne := hI.target_ne
  have hbud := hI.budget
  rw [ht] at hne hbud
  rw [ht]
  have hdec := zprepE_decoded p hp.r₀_nonneg hp.rb_nonneg hp.T_nonneg hp.B_pos v σ x0 b
    hI.init_norm hI.forcing_norm hI.init_prep hI.forcing_prep
  have hB := hp.B_pos
  generalize hy : (goodF†) (run (wiring v) σ (zprepE p) (seedState v)) = y at hdec
  have hyx : y = p.B⁻¹ • (x0 + p.T • b) := by
    rw [← hdec, smul_smul, inv_mul_cancel₀ hB.ne', one_smul]
  have hamp : ODEGroverActual.amplitude goodF (run (wiring v) σ (zprepE p)) (seedState v) =
      ‖y‖ := by
    rw [ODEGroverActual.amplitude, ← ODEHeraldedSuccess.successfulComponent,
      ODEHeraldedSuccess.successfulComponent_norm _ goodF_isometry, ← hy]
    rfl
  have hnorm : ‖y‖ = ‖x0 + p.T • b‖ / p.B := by
    rw [hyx, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hB), inv_mul_eq_div]
  have hxpos : 0 < ‖x0 + p.T • b‖ := norm_pos_iff.mpr hne
  have hg := hp.g_ge
  have hlow : 1 / (4 * p.g) ≤
      ODEGroverActual.amplitude goodF (run (wiring v) σ (zprepE p)) (seedState v) := by
    rw [hamp, hnorm, div_le_div_iff₀ (by positivity) hB]
    nlinarith
  have herr : ‖unitDirection ((goodF†) (run (wiring v) σ (zprepE p) (seedState v))) -
      unitDirection (x0 + p.T • b)‖ ≤ p.ε / 500 := by
    rw [hy, hyx, ODEHeraldedSuccess.unitDirection_pos_smul _ (inv_pos.mpr hB), sub_self,
      norm_zero]
    have := hp.ε_pos
    positivity
  have hR := randomized_certificate_full (P := P) (K := Reg p.W P) goodF goodF_isometry
    (run (wiring v) σ (zprepE p)) hW (seedState v) (seedState_norm v hv) p.g hg hlow
    (x0 + p.T • b) (p.ε / 500) herr
  have htrial : ∀ j, run (wiring v) σ (ztrialE p j) (seedState v) =
      ODEGroverActual.trial goodF (run (wiring v) σ (zprepE p)) (seedState v) j :=
    fun j => ztrialE_seed p hp.r₀_nonneg hp.rb_nonneg hp.T_nonneg hp.B_pos v hv σ
      hI.src_unitary j
  obtain ⟨hM, hM5, hmean, hdir⟩ := hR
  refine ⟨hM, hM5, ?_, ?_⟩
  · simp only [htrial]
    exact hmean
  · intro j hj
    rw [htrial] at hj ⊢
    exact hdir j hj

variable [FiniteDimensional ℂ P]

/-- The guarantees of the zero-case protocol for one instance: the fields of the released
`GateODE.Params.Outcome` for the zero-case trials `ztrialE` and protocol `zprotocol`. -/
structure ZOutcome (v : P) (hv : ‖v‖ = 1) (hg : 1 ≤ p.g) (σ : Oracles p.a (Label p.k p.l) P)
    (x : P) : Prop where
  unitary_trials : ∀ j, IsUnitary (run (wiring v) σ (ztrialE p j))
  mean_success : (1 : ℝ) / 4 ≤
    (∑ j ∈ Finset.range (ODEGroverAverage.chosenIterations p.g),
      ‖ODEHeraldedSuccess.successProjector goodF
        (run (wiring v) σ (ztrialE p j) (seedState v))‖ ^ 2) /
      (ODEGroverAverage.chosenIterations p.g : ℝ)
  trial_direction : ∀ j : ℕ, (goodF†) (run (wiring v) σ (ztrialE p j) (seedState v)) ≠ 0 →
    ∃ ω : ℂ, ‖ω‖ = 1 ∧
      ‖ω • unitDirection ((goodF†) (run (wiring v) σ (ztrialE p j) (seedState v))) -
        unitDirection x‖ ≤ p.ε / 500
  success_lower : (175 : ℝ) / 256 ≤ (zprotocol p v hv hg).successMass σ
  success_two_thirds : (2 : ℝ) / 3 ≤ (zprotocol p v hv hg).successMass σ
  output_density : ODEMixedOutput.IsDensity ((zprotocol p v hv hg).conditionalDensity σ)
  conditional_error :
    ∃ h : ((zprotocol p v hv hg).conditionalDensity σ -
        ODEMixedOutput.pureOperator (unitDirection x)).toLinearMap.IsSymmetric,
      ODEMixedOutput.hermitianTraceDistance ((zprotocol p v hv hg).conditionalDensity σ)
        (ODEMixedOutput.pureOperator (unitDirection x)) h ≤ p.ε

/-- **The zero-case protocol is correct for every instance of the zero case.** -/
theorem zoutcome (hp : PublicOK0 p) (hz : ZeroCase p) (v : P) (hv : ‖v‖ = 1)
    (σ : Oracles p.a (Label p.k p.l) P) (H L : P →L[ℂ] P) (x0 b : P)
    (hI : ZInstanceOK p v σ.J H L x0 b) :
    ZOutcome p v hv hp.g_ge σ (p.target H L x0 b) := by
  have hunit : ∀ j, IsUnitary (run (wiring v) σ (ztrialE p j)) := fun j =>
    ztrialE_isUnitary p hp.r₀_nonneg hp.rb_nonneg hp.T_nonneg hp.B_pos v hv σ hI.src_unitary j
  obtain ⟨hM, _, hmean, hdir⟩ := ztrial_bounds p hp hz v hv σ H L x0 b hI
  have hunitT : ∀ j, IsUnitary (((ztrials p v hv hp.g_ge).circuit j).eval σ) := by
    intro j
    rw [ztrials_eval p v hv hp.g_ge σ j]
    exact hunit _
  have hprob : ∀ j, (ztrials p v hv hp.g_ge).probability σ j =
      ‖ODEHeraldedSuccess.successProjector goodF
        (run (wiring v) σ (ztrialE p j.val) (seedState v))‖ ^ 2 := by
    intro j
    rw [(ztrials p v hv hp.g_ge).probability_eq_projected σ j, ztrials_eval p v hv hp.g_ge σ j,
      ztrials_output p v hv hp.g_ge, ztrials_seed p v hv hp.g_ge]
  have hsumP : ∑ j : Fin (ztrials p v hv hp.g_ge).choices,
      (ztrials p v hv hp.g_ge).probability σ j =
      ∑ j ∈ Finset.range (ODEGroverAverage.chosenIterations p.g),
        ‖ODEHeraldedSuccess.successProjector goodF
          (run (wiring v) σ (ztrialE p j) (seedState v))‖ ^ 2 := by
    rw [Finset.sum_congr rfl (fun j _ => hprob j)]
    exact Fin.sum_univ_eq_sum_range (fun j => ‖ODEHeraldedSuccess.successProjector goodF
      (run (wiring v) σ (ztrialE p j) (seedState v))‖ ^ 2) _
  have hmeanT : (1 : ℝ) / 4 ≤
      ODERepeatProbability.mean ((ztrials p v hv hp.g_ge).probability σ) := by
    unfold ODERepeatProbability.mean
    rw [hsumP]
    exact hmean
  have hupper : ODERepeatProbability.mean ((ztrials p v hv hp.g_ge).probability σ) ≤ 1 :=
    ODERepeatProbability.mean_le_one _ (ztrials p v hv hp.g_ge).choices_pos
      (fun j => ((ztrials p v hv hp.g_ge).probability_bounds σ hunitT j).2)
  have hnonneg : ∀ j, 0 ≤ (ztrials p v hv hp.g_ge).probability σ j :=
    fun j => ((ztrials p v hv hp.g_ge).probability_bounds σ hunitT j).1
  have hsucc : (zprotocol p v hv hp.g_ge).successMass σ =
      ODERepeatProbability.successProbability ((ztrials p v hv hp.g_ge).probability σ) :=
    ODERepeatProtocol.Protocol.four_successMass_eq (ztrials p v hv hp.g_ge) σ
  have hdens : (zprotocol p v hv hp.g_ge).conditionalDensity σ =
      ODEMixedOutput.ensemble
        (ODERepeatProbability.conditionalWeight ((ztrials p v hv hp.g_ge).probability σ))
        (fun a => (ztrials p v hv hp.g_ge).outputDirection σ a.2) :=
    ODERepeatProtocol.Protocol.four_conditionalDensity_eq (ztrials p v hv hp.g_ge) σ
  have hw := ODERepeatProbability.conditionalWeight_nonneg _ hnonneg hmeanT hupper
  have hsum := ODERepeatProbability.conditionalWeight_sum _ hmeanT hupper
  have hne : ∀ a : Fin 4 × Fin (ztrials p v hv hp.g_ge).choices,
      ODERepeatProbability.conditionalWeight ((ztrials p v hv hp.g_ge).probability σ) a ≠ 0 →
      (ztrials p v hv hp.g_ge).amplitude σ a.2 ≠ 0 := by
    intro a ha hz0
    apply ODERepeatProbability.conditionalWeight_ne_zero_implies _ a ha
    rw [ODERepeatProtocol.TrialFamily.probability, hz0, norm_zero]
    norm_num
  have hclose : ∀ a : Fin 4 × Fin (ztrials p v hv hp.g_ge).choices,
      ODERepeatProbability.conditionalWeight ((ztrials p v hv hp.g_ge).probability σ) a ≠ 0 →
      ∃ ω : ℂ, ‖ω‖ = 1 ∧ ‖ω • (ztrials p v hv hp.g_ge).outputDirection σ a.2 -
        unitDirection (p.target H L x0 b)‖ ≤ p.ε / 500 := by
    intro a ha
    have hz0 := hne a ha
    rw [ztrials_amplitude] at hz0
    have h := hdir a.2.val hz0
    rw [ODERepeatProtocol.TrialFamily.outputDirection, ztrials_amplitude]
    exact h
  have hunitDir : ∀ a : Fin 4 × Fin (ztrials p v hv hp.g_ge).choices,
      ODERepeatProbability.conditionalWeight ((ztrials p v hv hp.g_ge).probability σ) a ≠ 0 →
      ‖(ztrials p v hv hp.g_ge).outputDirection σ a.2‖ = 1 :=
    fun a ha => ODEStateNormalization.unitDirection_norm _ (hne a ha)
  obtain ⟨hDensity, hSymm, hDistance⟩ := ODEMixedOutput.ensemble_trace_distance_le
    (ODERepeatProbability.conditionalWeight ((ztrials p v hv hp.g_ge).probability σ))
    (fun a => (ztrials p v hv hp.g_ge).outputDirection σ a.2)
    (unitDirection (p.target H L x0 b)) (p.ε / 500) hw hsum
    hunitDir (ODEStateNormalization.unitDirection_norm _ hI.target_ne) hclose
  have hlow : (175 : ℝ) / 256 ≤ (zprotocol p v hv hp.g_ge).successMass σ := by
    rw [hsucc]
    exact ODERepeatProbability.successProbability_lower _ hmeanT hupper
  have htwo : (2 : ℝ) / 3 ≤ (zprotocol p v hv hp.g_ge).successMass σ := by
    rw [hsucc]
    exact ODERepeatProbability.successProbability_two_thirds _ hmeanT hupper
  have hden : ODEMixedOutput.IsDensity ((zprotocol p v hv hp.g_ge).conditionalDensity σ) := by
    rw [hdens]
    exact hDensity
  have herr : ∃ h : ((zprotocol p v hv hp.g_ge).conditionalDensity σ -
        ODEMixedOutput.pureOperator (unitDirection (p.target H L x0 b))).toLinearMap.IsSymmetric,
      ODEMixedOutput.hermitianTraceDistance ((zprotocol p v hv hp.g_ge).conditionalDensity σ)
        (ODEMixedOutput.pureOperator (unitDirection (p.target H L x0 b))) h ≤ p.ε := by
    rw [hdens]
    refine ⟨hSymm, hDistance.trans ?_⟩
    have := hp.ε_pos
    linarith
  exact ⟨hunit, hmean, hdir, hlow, htwo, hden, herr⟩

/-- **Zero time or a known zero generator with exact gates, constant coefficients** (remark of
Theorem `ode:thm:gates`: direct source assembly, no matrix calls).

For public data `p` with `PublicOK0 p` in the zero case (`T = 0 ∨ λ_H + R λ_D = 0`) and a unit
seed `v`, the zero-case protocol `zprotocol p v` on the released wires: every instruction of
every trial is a valid elementary instruction; in every history (including four failures) it
uses at most `40 g · 2 + 20 g · reflGates` elementary gates, makes no private Cayley call and no
call of `U_J` or `U_J†`, at most `40 g` calls of each source interface and `20 g` seed
reflections; `reflGates` and the number of wires are the released ones.  For all supplied
unitaries `σ` (no condition on `U_J` and the private operations) and all `H, L, x₀, b`
satisfying the zero-case conditions `ZInstanceOK` (unitary source interfaces, `‖H‖ ≤ λ_H`,
`‖L‖ ≤ λ_D`, public norms, seed promises, nonzero target and `B ≤ g ‖x(T)‖`), the protocol has
the guarantees `ZOutcome` against the released target `x(T)` (which is `x₀ + T b`,
`target_zero`): unitary trials, mean success at least `1/4`, every successful trial within
`ε/500` of `x(T)/‖x(T)‖` up to a global phase, success probability at least `175/256 > 2/3`, and
a conditional output density operator within trace distance `ε` of `x(T)/‖x(T)‖`. -/
theorem exact_ode_solver_zero (p : Params) (hp : PublicOK0 p) (hz : ZeroCase p) (v : P)
    (hv : ‖v‖ = 1) :
    (∀ j, ∀ g ∈ ztrialE p j, g.Valid Wire.anc) ∧
    ((zprotocol p v hv hp.g_ge).worstCost p.wGate : ℝ) ≤
      40 * p.g * 2 + 20 * p.g * p.reflGates ∧
    (zprotocol p v hv hp.g_ge).worstCost p.wPriv = 0 ∧
    (zprotocol p v hv hp.g_ge).worstCost p.wUJ = 0 ∧
    (∀ c, ((zprotocol p v hv hp.g_ge).worstCost (p.wSrc c) : ℝ) ≤ 40 * p.g) ∧
    ((zprotocol p v hv hp.g_ge).worstCost p.wSeed : ℝ) ≤ 20 * p.g ∧
    p.reflGates = 6 * (2 * p.a + 3 * p.m + 6 * p.r + 4 + p.k + p.l) + 4 ∧
    Fintype.card p.W = 4 * p.a + 6 * p.m + 12 * p.r + 2 * p.k + 2 * p.l + 8 ∧
    ∀ (σ : Oracles p.a (Label p.k p.l) P) (H L : P →L[ℂ] P) (x0 b : P),
      ZInstanceOK p v σ.J H L x0 b → ZOutcome p v hv hp.g_ge σ (p.target H L x0 b) := by
  obtain ⟨wG, wP, wU, wS, wE⟩ := zprotocol_worst p hp.g_ge v hv
  exact ⟨ztrialE_valid p hp.r₀_nonneg hp.rb_nonneg hp.T_nonneg hp.B_pos, wG, wP, wU, wS, wE,
    p.reflGates_eq, p.card_W, fun σ H L x0 b hI => zoutcome p hp hz v hv σ H L x0 b hI⟩

end Outcome

end

end SparseHamiltonian.ZeroTimeGateODE
