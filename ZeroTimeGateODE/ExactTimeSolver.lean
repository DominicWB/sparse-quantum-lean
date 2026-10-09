import ZeroTimeGateODE.ExactTime

/-!
# Zero time or a known zero generator with exact gates, time-dependent coefficients: the solver

The guarantees of the time-dependent zero-case protocol `tzprotocol` of `ExactTime`.

* `tztrial_bounds`: the decoded prepared vector is `(x₀ + (T/M) ∑ b_r) / B`, `B` the released
  source mass; the released discretisation budget (`GateODE.Time.TParams.discretisation_error`,
  `TimeDependentODE.Sampling.target_budget`) gives amplitude at least `1/(2g)` and direction
  within `ε/1000` of `x(T)`, and `randomized_certificate_full` gives the mean success and the
  direction of every successful trial;
* `tzoutcome`: the guarantees `TZOutcome` (the fields of the released
  `GateODE.Time.TParams.Outcome` for the zero-case trials and protocol);
* `exact_ode_time_solver_zero`: the exact-gate time-dependent solver in the zero case.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.ZeroTimeGateODE

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit
open GateCircuit.Sim (Wire)
open GateODE (seedState seedState_norm goodF goodF_isometry)
open GateODE.Time (TParams TOracles trun)
open ODEStateNormalization (unitDirection)
open scoped InnerProduct BigOperators

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

section Outcome

variable (p : TParams)

/-- **Mean success and direction error of the time-dependent zero-case trials.** -/
theorem tztrial_bounds (hp : TPublicOK0 p) (hz : TZeroCase p) (v : P) (hv : ‖v‖ = 1)
    (σ : TOracles p.a p.m p.l P) (Hs Ls : ℕ → P →L[ℂ] P) (G : ℝ → P →L[ℂ] P) (b x : ℝ → P)
    (bs : ℕ → P) (βG δG βb δb bmax : ℝ)
    (hI : TZInstanceOK p v σ.J σ.Wp Hs Ls G b x bs βG δG βb δb bmax) :
    0 < ODEGroverAverage.chosenIterations p.ratio ∧
    (ODEGroverAverage.chosenIterations p.ratio : ℝ) ≤ 5 * p.ratio ∧
    (1 : ℝ) / 4 ≤ (∑ j ∈ Finset.range (ODEGroverAverage.chosenIterations p.ratio),
      ‖ODEHeraldedSuccess.successProjector goodF (trun v σ (tztrialE p j) (seedState v))‖ ^ 2) /
        (ODEGroverAverage.chosenIterations p.ratio : ℝ) ∧
    ∀ j : ℕ, (goodF†) (trun v σ (tztrialE p j) (seedState v)) ≠ 0 →
      ∃ ω : ℂ, ‖ω‖ = 1 ∧
        ‖ω • unitDirection ((goodF†) (trun v σ (tztrialE p j) (seedState v))) -
          unitDirection (x p.T)‖ ≤ p.ε / 500 := by
  have hεOne : p.ε ≤ 1 := hp.ε_half.trans (by norm_num)
  have hW := tzprepE_isUnitary p v hv σ hI.load_unitary hI.prep_left hI.prep_right
  have hzero := tzero_samples p hp.g_ge hp.ε_pos hεOne hp.lamH_nonneg hp.lamD_nonneg hz Hs Ls
    hI.normH hI.normL
  have hy : p.target Hs Ls (x 0) bs = ∑ s, p.zsrc (x 0) bs s := by
    rw [ttarget_zero p Hs Ls (x 0) bs hzero, zsrc_sum]
  have hErr := p.discretisation_error hp.T_nonneg G b x Hs Ls bs βG δG βb δb bmax hI.βG_nonneg
    hI.βb_nonneg hI.solves hI.accretive hI.lipG hI.sampleG hI.lipb hI.sampleb hI.boundb hI.selfH
    hI.psd hI.normH hI.normL
  obtain ⟨hy0, hbud, hdirY⟩ := TimeDependentODE.Sampling.target_budget (x p.T)
    (p.target Hs Ls (x 0) bs) (p.mass (x 0) bs) p.g p.ε _ hp.g_ge hp.ε_pos hεOne hI.target_ne
    hI.budget hErr hI.disc
  have hNorm := p.target_norm_le hp.T_nonneg Hs Ls hI.selfH hI.psd (x 0) bs
  have hB : 0 < p.mass (x 0) bs := (norm_pos_iff.mpr hy0).trans_le hNorm
  have hrel := tz_decoded p (a := p.a) (m := p.m) (r := p.r) (K := p.K) (l := p.l) (f := p.f)
    hp.T_nonneg v σ (x 0) bs hB hI.prep hI.init_load hI.forcing_load
  rw [← hy] at hrel
  have hrel' : p.mass (x 0) bs • (goodF†) (trun v σ (tzprepE p) (seedState v)) =
      p.target Hs Ls (x 0) bs := hrel
  generalize hY : (goodF†) (trun v σ (tzprepE p) (seedState v)) = Y at hrel'
  have hYx : Y = (p.mass (x 0) bs)⁻¹ • p.target Hs Ls (x 0) bs := by
    rw [← hrel', smul_smul, inv_mul_cancel₀ hB.ne', one_smul]
  have hamp : ODEGroverActual.amplitude goodF (trun v σ (tzprepE p)) (seedState v) = ‖Y‖ := by
    rw [ODEGroverActual.amplitude, ← ODEHeraldedSuccess.successfulComponent,
      ODEHeraldedSuccess.successfulComponent_norm _ goodF_isometry, ← hY]
    rfl
  have hnorm : ‖Y‖ = ‖p.target Hs Ls (x 0) bs‖ / p.mass (x 0) bs := by
    rw [hYx, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hB), inv_mul_eq_div]
  have hpos : 0 < ‖p.target Hs Ls (x 0) bs‖ := norm_pos_iff.mpr hy0
  have hratio := p.ratio_ge hp.g_ge
  have hbud' : p.mass (x 0) bs ≤ p.ratio * ‖p.target Hs Ls (x 0) bs‖ := hbud
  have hlow : 1 / (4 * p.ratio) ≤
      ODEGroverActual.amplitude goodF (trun v σ (tzprepE p)) (seedState v) := by
    rw [hamp, hnorm, div_le_div_iff₀ (by positivity) hB]
    nlinarith
  have herr : ‖unitDirection ((goodF†) (trun v σ (tzprepE p) (seedState v))) -
      unitDirection (x p.T)‖ ≤ p.ε / 500 := by
    rw [hY, hYx, ODEHeraldedSuccess.unitDirection_pos_smul _ (inv_pos.mpr hB)]
    have := hp.ε_pos
    linarith
  have hR := randomized_certificate_full (P := P) (K := Reg p.W P) goodF goodF_isometry
    (trun v σ (tzprepE p)) hW (seedState v) (seedState_norm v hv) p.ratio hratio hlow
    (x p.T) (p.ε / 500) herr
  have htrial : ∀ j, trun v σ (tztrialE p j) (seedState v) =
      ODEGroverActual.trial goodF (trun v σ (tzprepE p)) (seedState v) j :=
    fun j => tztrialE_seed p v hv σ hI.load_unitary hI.prep_left hI.prep_right j
  obtain ⟨hM, hM5, hmean, hdir⟩ := hR
  refine ⟨hM, hM5, ?_, ?_⟩
  · simp only [htrial]
    exact hmean
  · intro j hj
    rw [htrial] at hj ⊢
    exact hdir j hj

variable [FiniteDimensional ℂ P]

/-- The guarantees of the time-dependent zero-case protocol for one instance with final state
`x`: the fields of the released `GateODE.Time.TParams.Outcome` for the zero-case trials
`tztrialE` and protocol `tzprotocol`. -/
structure TZOutcome (v : P) (hv : ‖v‖ = 1) (hg : 1 ≤ p.g) (σ : TOracles p.a p.m p.l P)
    (x : P) : Prop where
  unitary_trials : ∀ j, IsUnitary (trun v σ (tztrialE p j))
  mean_success : (1 : ℝ) / 4 ≤
    (∑ j ∈ Finset.range (ODEGroverAverage.chosenIterations p.ratio),
      ‖ODEHeraldedSuccess.successProjector goodF (trun v σ (tztrialE p j) (seedState v))‖ ^ 2) /
      (ODEGroverAverage.chosenIterations p.ratio : ℝ)
  trial_direction : ∀ j : ℕ, (goodF†) (trun v σ (tztrialE p j) (seedState v)) ≠ 0 →
    ∃ ω : ℂ, ‖ω‖ = 1 ∧
      ‖ω • unitDirection ((goodF†) (trun v σ (tztrialE p j) (seedState v))) -
        unitDirection x‖ ≤ p.ε / 500
  success_lower : (175 : ℝ) / 256 ≤ (tzprotocol p v hv hg).successMass σ
  success_two_thirds : (2 : ℝ) / 3 ≤ (tzprotocol p v hv hg).successMass σ
  output_density : ODEMixedOutput.IsDensity ((tzprotocol p v hv hg).conditionalDensity σ)
  conditional_error :
    ∃ h : ((tzprotocol p v hv hg).conditionalDensity σ -
        ODEMixedOutput.pureOperator (unitDirection x)).toLinearMap.IsSymmetric,
      ODEMixedOutput.hermitianTraceDistance ((tzprotocol p v hv hg).conditionalDensity σ)
        (ODEMixedOutput.pureOperator (unitDirection x)) h ≤ p.ε

/-- **The time-dependent zero-case protocol is correct for every instance of the zero
case.** -/
theorem tzoutcome (hp : TPublicOK0 p) (hz : TZeroCase p) (v : P) (hv : ‖v‖ = 1)
    (σ : TOracles p.a p.m p.l P) (Hs Ls : ℕ → P →L[ℂ] P) (G : ℝ → P →L[ℂ] P) (b x : ℝ → P)
    (bs : ℕ → P) (βG δG βb δb bmax : ℝ)
    (hI : TZInstanceOK p v σ.J σ.Wp Hs Ls G b x bs βG δG βb δb bmax) :
    TZOutcome p v hv hp.g_ge σ (x p.T) := by
  have hunit : ∀ j, IsUnitary (trun v σ (tztrialE p j)) := fun j =>
    tztrialE_isUnitary p v hv σ hI.load_unitary hI.prep_left hI.prep_right j
  obtain ⟨hM, _, hmean, hdir⟩ :=
    tztrial_bounds p hp hz v hv σ Hs Ls G b x bs βG δG βb δb bmax hI
  have hunitT : ∀ j, IsUnitary (((tztrials p v hv hp.g_ge).circuit j).eval σ) := by
    intro j
    rw [tztrials_eval p v hv hp.g_ge σ j]
    exact hunit _
  have hprob : ∀ j, (tztrials p v hv hp.g_ge).probability σ j =
      ‖ODEHeraldedSuccess.successProjector goodF
        (trun v σ (tztrialE p j.val) (seedState v))‖ ^ 2 := by
    intro j
    rw [(tztrials p v hv hp.g_ge).probability_eq_projected σ j,
      tztrials_eval p v hv hp.g_ge σ j, tztrials_output p v hv hp.g_ge,
      tztrials_seed p v hv hp.g_ge]
  have hsumP : ∑ j : Fin (tztrials p v hv hp.g_ge).choices,
      (tztrials p v hv hp.g_ge).probability σ j =
      ∑ j ∈ Finset.range (ODEGroverAverage.chosenIterations p.ratio),
        ‖ODEHeraldedSuccess.successProjector goodF
          (trun v σ (tztrialE p j) (seedState v))‖ ^ 2 := by
    rw [Finset.sum_congr rfl (fun j _ => hprob j)]
    exact Fin.sum_univ_eq_sum_range (fun j => ‖ODEHeraldedSuccess.successProjector goodF
      (trun v σ (tztrialE p j) (seedState v))‖ ^ 2) _
  have hmeanT : (1 : ℝ) / 4 ≤
      ODERepeatProbability.mean ((tztrials p v hv hp.g_ge).probability σ) := by
    unfold ODERepeatProbability.mean
    rw [hsumP]
    exact hmean
  have hupper : ODERepeatProbability.mean ((tztrials p v hv hp.g_ge).probability σ) ≤ 1 :=
    ODERepeatProbability.mean_le_one _ (tztrials p v hv hp.g_ge).choices_pos
      (fun j => ((tztrials p v hv hp.g_ge).probability_bounds σ hunitT j).2)
  have hnonneg : ∀ j, 0 ≤ (tztrials p v hv hp.g_ge).probability σ j :=
    fun j => ((tztrials p v hv hp.g_ge).probability_bounds σ hunitT j).1
  have hsucc : (tzprotocol p v hv hp.g_ge).successMass σ =
      ODERepeatProbability.successProbability ((tztrials p v hv hp.g_ge).probability σ) :=
    ODERepeatProtocol.Protocol.four_successMass_eq (tztrials p v hv hp.g_ge) σ
  have hdens : (tzprotocol p v hv hp.g_ge).conditionalDensity σ =
      ODEMixedOutput.ensemble
        (ODERepeatProbability.conditionalWeight ((tztrials p v hv hp.g_ge).probability σ))
        (fun a => (tztrials p v hv hp.g_ge).outputDirection σ a.2) :=
    ODERepeatProtocol.Protocol.four_conditionalDensity_eq (tztrials p v hv hp.g_ge) σ
  have hw := ODERepeatProbability.conditionalWeight_nonneg _ hnonneg hmeanT hupper
  have hsum := ODERepeatProbability.conditionalWeight_sum _ hmeanT hupper
  have hne : ∀ a : Fin 4 × Fin (tztrials p v hv hp.g_ge).choices,
      ODERepeatProbability.conditionalWeight ((tztrials p v hv hp.g_ge).probability σ) a ≠ 0 →
      (tztrials p v hv hp.g_ge).amplitude σ a.2 ≠ 0 := by
    intro a ha hz0
    apply ODERepeatProbability.conditionalWeight_ne_zero_implies _ a ha
    rw [ODERepeatProtocol.TrialFamily.probability, hz0, norm_zero]
    norm_num
  have hclose : ∀ a : Fin 4 × Fin (tztrials p v hv hp.g_ge).choices,
      ODERepeatProbability.conditionalWeight ((tztrials p v hv hp.g_ge).probability σ) a ≠ 0 →
      ∃ ω : ℂ, ‖ω‖ = 1 ∧ ‖ω • (tztrials p v hv hp.g_ge).outputDirection σ a.2 -
        unitDirection (x p.T)‖ ≤ p.ε / 500 := by
    intro a ha
    have hz0 := hne a ha
    rw [tztrials_amplitude] at hz0
    have h := hdir a.2.val hz0
    rw [ODERepeatProtocol.TrialFamily.outputDirection, tztrials_amplitude]
    exact h
  have hunitDir : ∀ a : Fin 4 × Fin (tztrials p v hv hp.g_ge).choices,
      ODERepeatProbability.conditionalWeight ((tztrials p v hv hp.g_ge).probability σ) a ≠ 0 →
      ‖(tztrials p v hv hp.g_ge).outputDirection σ a.2‖ = 1 :=
    fun a ha => ODEStateNormalization.unitDirection_norm _ (hne a ha)
  obtain ⟨hDensity, hSymm, hDistance⟩ := ODEMixedOutput.ensemble_trace_distance_le
    (ODERepeatProbability.conditionalWeight ((tztrials p v hv hp.g_ge).probability σ))
    (fun a => (tztrials p v hv hp.g_ge).outputDirection σ a.2)
    (unitDirection (x p.T)) (p.ε / 500) hw hsum
    hunitDir (ODEStateNormalization.unitDirection_norm _ hI.target_ne) hclose
  have hlow : (175 : ℝ) / 256 ≤ (tzprotocol p v hv hp.g_ge).successMass σ := by
    rw [hsucc]
    exact ODERepeatProbability.successProbability_lower _ hmeanT hupper
  have htwo : (2 : ℝ) / 3 ≤ (tzprotocol p v hv hp.g_ge).successMass σ := by
    rw [hsucc]
    exact ODERepeatProbability.successProbability_two_thirds _ hmeanT hupper
  have hden : ODEMixedOutput.IsDensity ((tzprotocol p v hv hp.g_ge).conditionalDensity σ) := by
    rw [hdens]
    exact hDensity
  have herr : ∃ h : ((tzprotocol p v hv hp.g_ge).conditionalDensity σ -
        ODEMixedOutput.pureOperator (unitDirection (x p.T))).toLinearMap.IsSymmetric,
      ODEMixedOutput.hermitianTraceDistance ((tzprotocol p v hv hp.g_ge).conditionalDensity σ)
        (ODEMixedOutput.pureOperator (unitDirection (x p.T))) h ≤ p.ε := by
    rw [hdens]
    refine ⟨hSymm, hDistance.trans ?_⟩
    have := hp.ε_pos
    linarith
  exact ⟨hunit, hmean, hdir, hlow, htwo, hden, herr⟩

/-- **Zero time or a known zero generator with exact gates, time-dependent coefficients**
(remark of Theorem `ode:thm:gates`, time-dependent part: direct source assembly, no matrix
calls).

For public data `p` with `TPublicOK0 p` in the zero case (`T = 0 ∨ λ_H + R λ_D = 0`) and a unit
seed `v`, the zero-case protocol `tzprotocol p v` (ratio `2g`) on the released wires: every
instruction of every trial is a valid elementary instruction; in every history it uses at most
`40 g · reflGates` elementary gates, makes no private call and no call of `U_J` or `U_J†`, at
most `80 g` loading calls, `160 g` weight-preparation calls and `40 g` seed reflections;
`reflGates` and the number of wires are the released ones.  For all supplied operations `σ`
(no condition on `U_J` and the private operations) and every instance satisfying the zero-case
conditions `TZInstanceOK` for the loading `σ.J` and the weights `σ.Wp`, the protocol has the
guarantees `TZOutcome` against `x(T)`. -/
theorem exact_ode_time_solver_zero (p : TParams) (hp : TPublicOK0 p) (hz : TZeroCase p) (v : P)
    (hv : ‖v‖ = 1) :
    (∀ j, ∀ g ∈ tztrialE p j, g.Valid Wire.anc) ∧
    ((tzprotocol p v hv hp.g_ge).worstCost p.wGate : ℝ) ≤ 40 * p.g * p.reflGates ∧
    (tzprotocol p v hv hp.g_ge).worstCost p.wPriv = 0 ∧
    (tzprotocol p v hv hp.g_ge).worstCost p.wUJ = 0 ∧
    ((tzprotocol p v hv hp.g_ge).worstCost p.wLoad : ℝ) ≤ 80 * p.g ∧
    ((tzprotocol p v hv hp.g_ge).worstCost p.wPrep : ℝ) ≤ 160 * p.g ∧
    ((tzprotocol p v hv hp.g_ge).worstCost p.wSeed : ℝ) ≤ 40 * p.g ∧
    p.reflGates = 6 * (2 * p.a + 4 * p.m + 6 * p.r + 4 + p.l) + 4 ∧
    Fintype.card p.W = 4 * p.a + 8 * p.m + 12 * p.r + 2 * p.l + 8 ∧
    ∀ (σ : TOracles p.a p.m p.l P) (Hs Ls : ℕ → P →L[ℂ] P) (G : ℝ → P →L[ℂ] P)
      (b x : ℝ → P) (bs : ℕ → P) (βG δG βb δb bmax : ℝ),
      TZInstanceOK p v σ.J σ.Wp Hs Ls G b x bs βG δG βb δb bmax →
        TZOutcome p v hv hp.g_ge σ (x p.T) := by
  obtain ⟨wG, wP, wU, wL, wW, wE⟩ := tzprotocol_worst p hp.g_ge v hv
  exact ⟨tztrialE_valid p, wG, wP, wU, wL, wW, wE, p.reflGates_eq, p.card_W,
    fun σ Hs Ls G b x bs βG δG βb δb bmax hI =>
      tzoutcome p hp hz v hv σ Hs Ls G b x bs βG δG βb δb bmax hI⟩

end Outcome

end

end SparseHamiltonian.ZeroTimeGateODE
