import GateEfficientODE.Time.Theorem

/-!
# The time-dependent gate-level ODE solver from target facts

The released time-dependent gate-level solver `GateODE.Time.solver` (Theorem `ode:thm:gates`,
time-dependent part, exact gates) states its guarantee `GateODE.Time.TParams.Outcome` for every
instance satisfying `GateODE.Time.TParams.InstanceOK`, which bundles the supplied unitaries and
their promises with a Lipschitz generator and forcing path and the discretisation budget. The
path enters the released proof only through `target_facts`: the discretised target `y` (the
exponential left-endpoint recurrence of the represented samples, `TParams.target`) is nonzero,
`B ≤ 2 g ‖y‖` for the source mass `B`, and `y` has the direction of `x(T)` up to `ε/1000`.

This module splits the instance conditions accordingly: `CoreOK` collects the conditions on the
supplied unitaries and samples (`InstanceOK` without the path), and `TargetOK` the conditions
on the final state: `x(T) ≠ 0`, `B ≤ g ‖x(T)‖` and `‖x(T) - y‖ ≤ ε B/(2000 g)`. The released
proof chain is reassembled from the public lemmas it uses (`select_error`, `lchs_error`,
`source_sum`, `coeffW_mass`, `target_norm_le`, `decoded_eq`, `trialC_seed`, the released
actual-source certificate and randomized amplification), with the target facts from
`TimeDependentODE.Sampling.target_budget`:

* `target_facts_of`: the target facts from `TargetOK`;
* `prep_certificate_of`: the released actual-source certificate for the discretised target;
* `trial_bounds_of`: mean success and the direction error of every successful trial;
* `outcome_of`: the released `Outcome` (success at least `2/3`, conditional output within trace
  distance `ε`) for every instance with `CoreOK` and `TargetOK`.

Every certificate on the path then only has to bound `‖x(T) - y‖` (modules `ODE/Target` and
`ODE/Mesh`).
-/

set_option autoImplicit false

namespace SparseHamiltonian.GateMesh.ODE

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit
open GateCircuit.Sim (Wire)
open GatePointerEncoding (wordValue)
open GateODE (goodF goodF_isometry seedState seedState_norm)
open GateODE.Time (TParams TOracles trun trun_isUnitary)
open scoped InnerProduct BigOperators

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-- **The conditions on the supplied source unitaries**: those of the released
`GateODE.Time.TParams.InstanceOK` for the loading `J s` and the weight preparation `Wp`, for
the initial state `x₀` and the forcing samples `b_r` (the weight promise
`Wp |0⟩ = ∑_s √(‖z_s‖ / B) |s⟩` and the loaded directions). -/
structure SourceOK (p : TParams) (v : P) (Jl : Bool × (Fin p.m → Bool) → P →L[ℂ] P)
    (Wp : Matrix (Cfg (Fin (p.m + 1))) (Cfg (Fin (p.m + 1))) ℂ) (x0 : P) (bs : ℕ → P) :
    Prop where
  load_unitary : ∀ s, IsUnitary (Jl s)
  prep_left : Wp.conjTranspose * Wp = 1
  prep_right : Wp * Wp.conjTranspose = 1
  prep : ∀ w : Cfg (Fin (p.m + 1)),
    Wp w (fun _ => false) = ((p.srcAmp x0 bs (w 0, Fin.tail w) : ℝ) : ℂ)
  init_load : x0 ≠ 0 →
    Jl (false, fun _ => false) v = ODEStateNormalization.unitDirection x0
  forcing_load : ∀ w : Fin p.m → Bool, bs (wordValue w) ≠ 0 →
    Jl (true, w) v = ODEStateNormalization.unitDirection (bs (wordValue w))

/-- **The conditions on an instance that do not involve the path**: those of the released
`GateODE.Time.TParams.InstanceOK` for the supplied unitaries (`SelectHypT`: unitarity and the
clock promises at every label and slot), the represented samples `H_r, L_r` (`r < 2^m`, `L_r`
positive semidefinite), the source unitaries, the forcing samples `b_r` and the initial state
`x₀`. -/
structure CoreOK (p : TParams) (v : P) (σ : TOracles p.a p.m p.l P) (Hs Ls : ℕ → P →L[ℂ] P)
    (x0 : P) (bs : ℕ → P) : Prop where
  select : p.SelectHypT σ Hs Ls
  psd : ∀ r < p.M, ∀ w : P, 0 ≤ (inner ℂ w (Ls r w)).re
  sources : SourceOK p v σ.J σ.Wp x0 bs

/-- **The conditions on the final state**: `x(T) ≠ 0`, the normalisation budget
`B ≤ g ‖x(T)‖` for the source mass `B`, and the certified distance
`‖x(T) - y‖ ≤ ε B/(2000 g)` of the discretised target `y`. -/
structure TargetOK (p : TParams) (Hs Ls : ℕ → P →L[ℂ] P) (x0 : P) (bs : ℕ → P) (xT : P) :
    Prop where
  ne : xT ≠ 0
  budget : p.mass x0 bs ≤ p.g * ‖xT‖
  error : ‖xT - p.target Hs Ls x0 bs‖ ≤ p.ε * p.mass x0 bs / (2000 * p.g)

namespace CoreOK

variable {p : TParams} {v : P} {σ : TOracles p.a p.m p.l P} {Hs Ls : ℕ → P →L[ℂ] P} {x0 : P}
  {bs : ℕ → P}

/-- The supplied unitaries of a `CoreOK` instance satisfy the released unitarity conditions
`GateODE.Time.TOracles.Unitary` (from the selection hypotheses and the source conditions). -/
theorem unitary (hC : CoreOK p v σ Hs Ls x0 bs) : σ.Unitary p.m :=
  ⟨hC.select.uj, hC.select.priv, hC.sources.load_unitary, hC.sources.prep_left,
    hC.sources.prep_right⟩

end CoreOK

omit [CompleteSpace P] in
/-- **The target facts** from the conditions on the final state. -/
theorem target_facts_of (p : TParams) (hp : p.PublicOK) {Hs Ls : ℕ → P →L[ℂ] P} {x0 : P}
    {bs : ℕ → P} {xT : P} (hT : TargetOK p Hs Ls x0 bs xT) :
    p.target Hs Ls x0 bs ≠ 0 ∧ p.mass x0 bs ≤ 2 * p.g * ‖p.target Hs Ls x0 bs‖ ∧
      ‖ODEStateNormalization.unitDirection (p.target Hs Ls x0 bs) -
        ODEStateNormalization.unitDirection xT‖ ≤ p.ε / 1000 :=
  TimeDependentODE.Sampling.target_budget xT (p.target Hs Ls x0 bs) (p.mass x0 bs) p.g p.ε _
    hp.g_ge hp.ε_pos hp.eps_le_one hT.ne hT.budget hT.error le_rfl

/-- **The actual preparation satisfies the released actual-source certificate for the
discretised target**, from the conditions on the supplied unitaries and the target facts. -/
theorem prep_certificate_of (p : TParams) (hp : p.PublicOK) (v : P) (hv : ‖v‖ = 1)
    (σ : TOracles p.a p.m p.l P) (Hs Ls : ℕ → P →L[ℂ] P) (x0 : P) (bs : ℕ → P)
    (hC : CoreOK p v σ Hs Ls x0 bs) (hy : p.target Hs Ls x0 bs ≠ 0)
    (hbud : p.mass x0 bs ≤ 2 * p.g * ‖p.target Hs Ls x0 bs‖) :
    ODEActualSourceError.Certificate p.branchE (p.zsrc x0 bs) p.coeffW σ.J
      (trun v σ p.select) v (p.target Hs Ls x0 bs) p.ratio p.acc := by
  have hT := hp.T_pos.le
  have hS := hC.select
  have hU := hC.unitary
  have hsel : IsUnitary (trun v σ p.select) :=
    trun_isUnitary v σ hU hv _ (fun g hg =>
      p.prepC_valid hp.tau_pos.le hp.nu_pos hp.mesh g (by simp [TParams.prepC, hg]))
  have hJ : ∀ s, (σ.J s)† ∘L σ.J s = 1 := by
    intro s
    have h := (hC.sources.load_unitary s).1
    rwa [star_eq_adjoint, mul_def] at h
  have hM : 0 < p.T / p.M := div_pos hp.T_pos (by exact_mod_cast p.M_pos)
  have hPrep : ∀ s, p.zsrc x0 bs s ≠ 0 →
      σ.J s v = ODEStateNormalization.unitDirection (p.zsrc x0 bs s) := by
    intro s hs
    obtain ⟨c, w⟩ := s
    cases c
    · by_cases hw : w = (fun _ => false)
      · subst hw
        have hx : x0 ≠ 0 := by
          intro h0
          apply hs
          simp [TParams.zsrc, h0]
        simp only [TParams.zsrc, Bool.false_eq_true, if_false, if_true]
        exact hC.sources.init_load hx
      · exfalso
        apply hs
        simp [TParams.zsrc, hw]
    · have hb : bs (wordValue w) ≠ 0 := by
        intro h0
        apply hs
        simp [TParams.zsrc, h0]
      simp only [TParams.zsrc, if_true]
      rw [hC.sources.forcing_load w hb, Complex.coe_smul,
        ODEHeraldedSuccess.unitDirection_pos_smul _ hM]
  have hNorm := p.target_norm_le hT Hs Ls hS.selfH hC.psd x0 bs
  have hSim := p.select_error hT hp.tau_pos hp.g_ge hp.ε_pos hp.eps_le_one hp.TD_nonneg hp.Q_ge
    hp.qbar_nonneg hp.qbar_le hp.mesh v σ Hs Ls hS
  have hLCHS := fun s => p.lchs_error hT hp.g_ge hp.ε_pos hp.eps_le_one hp.lamD_nonneg Hs Ls
    hS.selfH hS.selfL hS.normL hC.psd s
  have hQuad : ‖(∑ s, p.propS Hs Ls s (p.zsrc x0 bs s)) - p.target Hs Ls x0 bs‖ ≤
      ImprovedODEQueryBudget.precision p.ratio p.acc *
        ODESourceBranches.mass (p.zsrc x0 bs) := by
    rw [p.source_sum, sub_self, norm_zero]
    exact mul_nonneg (p.nu_pos hp.g_ge hp.ε_pos).le (ODESourceBranches.mass_nonneg _)
  have hmass := p.coeffW_mass hp.g_ge hp.ε_pos hp.eps_le_one hp.TD_nonneg
  have hacc : p.acc ≤ 1 / 2 := by
    have := hp.ε_half
    unfold TParams.acc
    linarith
  exact ODEActualSourceError.actual_source_certificate (σ := Bool × (Fin p.m → Bool))
    (ι := Fin p.l → Bool) (P := P) (K := Reg p.W P) p.branchE p.branchE_isometry
    (p.zsrc x0 bs) p.coeffW hmass σ.J hJ v hv hPrep (trun v σ p.select) hsel
    (p.branchU Hs Ls) (p.propS Hs Ls) (p.target Hs Ls x0 bs) p.ratio p.acc hy
    (p.ratio_ge hp.g_ge) (p.acc_pos hp.ε_pos) hacc hNorm hbud (by convert hSim using 4) hLCHS
    hQuad

/-- **Mean success and direction error of the actual trial circuits**, from the conditions on
the supplied unitaries and on the final state. -/
theorem trial_bounds_of (p : TParams) (hp : p.PublicOK) (v : P) (hv : ‖v‖ = 1)
    (σ : TOracles p.a p.m p.l P) (Hs Ls : ℕ → P →L[ℂ] P) (x0 : P) (bs : ℕ → P) (xT : P)
    (hC : CoreOK p v σ Hs Ls x0 bs) (hT : TargetOK p Hs Ls x0 bs xT) :
    0 < ODEGroverAverage.chosenIterations p.ratio ∧
    (ODEGroverAverage.chosenIterations p.ratio : ℝ) ≤ 5 * p.ratio ∧
    (1 : ℝ) / 4 ≤ (∑ j ∈ Finset.range (ODEGroverAverage.chosenIterations p.ratio),
      ‖ODEHeraldedSuccess.successProjector goodF
        (trun v σ (p.trialC j) (seedState v))‖ ^ 2) /
        (ODEGroverAverage.chosenIterations p.ratio : ℝ) ∧
    ∀ j : ℕ, (goodF†) (trun v σ (p.trialC j) (seedState v)) ≠ 0 →
      ∃ ω : ℂ, ‖ω‖ = 1 ∧
        ‖ω • ODEStateNormalization.unitDirection
            ((goodF†) (trun v σ (p.trialC j) (seedState v))) -
          ODEStateNormalization.unitDirection xT‖ ≤ p.ε / 500 := by
  have hU := hC.unitary
  have hW := p.prepC_isUnitary hp.tau_pos.le hp.nu_pos hp.mesh v hv σ hU
  obtain ⟨hy, hbud, hdirY⟩ := target_facts_of p hp hT
  have hCert := prep_certificate_of p hp v hv σ Hs Ls x0 bs hC hy hbud
  have hB : 0 < p.mass x0 bs := by
    have hNorm := p.target_norm_le hp.T_pos.le Hs Ls hC.select.selfH hC.psd x0 bs
    have := norm_pos_iff.mpr hy
    linarith
  have hdec := p.decoded_eq hp v σ x0 bs hB hC.sources.prep
  have hamp : ODEGroverActual.amplitude goodF (trun v σ p.prepC) (seedState v) =
      ‖ODEActualSourceError.decoded p.branchE (p.zsrc x0 bs) p.coeffW σ.J
        (trun v σ p.select) v‖ := by
    rw [ODEGroverActual.amplitude, ← ODEHeraldedSuccess.successfulComponent,
      ODEHeraldedSuccess.successfulComponent_norm _ goodF_isometry, hdec]
  have hampC : ‖ODEHeraldedSuccess.successfulComponent (ODEActualSourceError.output p.branchE
      (p.zsrc x0 bs) p.coeffW) (trun v σ p.select)
        (ODEActualSourceError.input p.branchE (p.zsrc x0 bs) p.coeffW σ.J v)‖ =
      ‖ODEActualSourceError.decoded p.branchE (p.zsrc x0 bs) p.coeffW σ.J
        (trun v σ p.select) v‖ :=
    ODEHeraldedSuccess.successfulComponent_norm _ hCert.output_isometry _ _
  have hlow : 1 / (4 * p.ratio) ≤ ODEGroverActual.amplitude goodF (trun v σ p.prepC)
      (seedState v) := by
    rw [hamp, ← hampC]
    exact hCert.amplitude_lower
  have hup : ODEGroverActual.amplitude goodF (trun v σ p.prepC) (seedState v) ≤ 1 / 2 := by
    rw [hamp, ← hampC]
    exact hCert.amplitude_upper.le
  have herr : ‖ODEStateNormalization.unitDirection ((goodF†) (trun v σ p.prepC
      (seedState v))) - ODEStateNormalization.unitDirection (p.target Hs Ls x0 bs)‖ ≤
        p.acc / 500 := by
    have h := hCert.direction_error
    rw [← ODEHeraldedSuccess.decoded, hdec]
    exact h
  have hR := ODEGroverActual.randomized_certificate (P := P) (K := Reg p.W P) goodF goodF_isometry
    (trun v σ p.prepC) hW (seedState v) (seedState_norm v hv) p.ratio (p.ratio_ge hp.g_ge) hlow
    hup (p.target Hs Ls x0 bs) (p.acc / 500) herr
  have htrial : ∀ j, trun v σ (p.trialC j) (seedState v) =
      ODEGroverActual.trial goodF (trun v σ p.prepC) (seedState v) j :=
    fun j => p.trialC_seed hp.tau_pos.le hp.nu_pos hp.mesh v hv σ hU j
  obtain ⟨hM, hM5, hmean, hdir⟩ := hR
  refine ⟨hM, hM5, ?_, ?_⟩
  · simp only [htrial]
    exact hmean
  · intro j hj
    rw [htrial] at hj ⊢
    obtain ⟨ω, hω, hd⟩ := hdir j hj
    refine ⟨ω, hω, ?_⟩
    calc _ ≤ ‖ω • ODEStateNormalization.unitDirection (ODEGroverActual.decoded goodF
            (trun v σ p.prepC) (seedState v) j) -
            ODEStateNormalization.unitDirection (p.target Hs Ls x0 bs)‖ +
          ‖ODEStateNormalization.unitDirection (p.target Hs Ls x0 bs) -
            ODEStateNormalization.unitDirection xT‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ p.acc / 500 + p.ε / 1000 := add_le_add hd hdirY
      _ = p.ε / 500 := by unfold TParams.acc; ring

variable [FiniteDimensional ℂ P]

/-- **The complete time-dependent protocol is correct for every instance with the conditions on
the supplied unitaries (`CoreOK`) and on the final state (`TargetOK`)**: the released
`GateODE.Time.TParams.Outcome` (success at least `175/256 > 2/3`, every successful trial within
`ε/500` of `x(T)/‖x(T)‖` up to a phase, conditional output within trace distance `ε`). -/
theorem outcome_of (p : TParams) (hp : p.PublicOK) (v : P) (hv : ‖v‖ = 1)
    (σ : TOracles p.a p.m p.l P) (Hs Ls : ℕ → P →L[ℂ] P) (x0 : P) (bs : ℕ → P) (xT : P)
    (hC : CoreOK p v σ Hs Ls x0 bs) (hT : TargetOK p Hs Ls x0 bs xT) :
    p.Outcome v hv hp.g_ge σ xT := by
  have hU := hC.unitary
  have hunit : ∀ j, IsUnitary (trun v σ (p.trialC j)) := fun j =>
    trun_isUnitary v σ hU hv _ (p.trialC_valid hp.tau_pos.le hp.nu_pos hp.mesh j)
  obtain ⟨hM, _, hmean, hdir⟩ := trial_bounds_of p hp v hv σ Hs Ls x0 bs xT hC hT
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
  have hsumP : ∑ j : Fin (p.trials v hv hp.g_ge).choices,
      (p.trials v hv hp.g_ge).probability σ j =
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
        ODEStateNormalization.unitDirection xT‖ ≤ p.ε / 500 := by
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
    (ODEStateNormalization.unitDirection xT) (p.ε / 500) hw hsum
    hunitDir (ODEStateNormalization.unitDirection_norm _ hT.ne) hclose
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
          (ODEStateNormalization.unitDirection xT)).toLinearMap.IsSymmetric,
      ODEMixedOutput.hermitianTraceDistance ((p.protocol v hv hp.g_ge).conditionalDensity σ)
        (ODEMixedOutput.pureOperator
          (ODEStateNormalization.unitDirection xT)) h ≤ p.ε := by
    rw [hdens]
    refine ⟨hSymm, hDistance.trans ?_⟩
    have := hp.ε_pos
    linarith
  exact ⟨hunit, hmean, hdir, hlow, htwo, hden, herr⟩

end

end SparseHamiltonian.GateMesh.ODE
