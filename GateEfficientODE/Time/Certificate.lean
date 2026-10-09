import GateEfficientODE.Time.Table
import GateEfficientODE.Analysis.Certificate
import TimeDependentODE.Solver.Target

/-!
# The certificate of the time-dependent preparation and its trials

`PublicOK` collects the public conditions, including the mesh condition
`steps tau (nu/3) ≤ 2^m` of the slot-selected simulator.  `InstanceOK`
collects the conditions on an instance: the supplied unitaries with the clock
promises at every label and slot and the promises of the weight
preparation and the source loading; the represented samples `H_r, L_r`
(`‖H_r‖ ≤ λH`, `‖L_r‖ ≤ λD`, `L_r ≥ 0`) and forcing samples `b_r`; a solution
`x` of `x' = -G(u) x + b(u)` on `[0, T]` for an accretive `βG`-Lipschitz
generator path `G` with `‖G(rT/2^m) - (L_r + i H_r)‖ ≤ δG` and a
`βb`-Lipschitz forcing with `‖b‖ ≤ bmax` and `‖b(rT/2^m) - b_r‖ ≤ δb`; a nonzero
final state with `B ≤ g ‖x(T)‖` for the source mass `B`; and the
discretisation budget `discretisation ≤ ε B / (2000 g)`.

Under them the discretised target `y` retains half of the solution norm and
has its direction up to `ε / 1000` (`TimeDependentODE.Sampling.target_budget`),
and the actual preparation satisfies the released actual-source certificate
for `y` with ratio `2g` and accuracy `ε/2` (`prep_certificate`).  The
released randomized amplification theorem then gives mean success at least
`1/4` over the public cutoff `chosenIterations (2g) ≤ 10 g`, and direction
error at most `ε / 500` against `x(T)` for every successful trial
(`trial_bounds`).
-/

namespace SparseHamiltonian.GateODE.Time

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit
open GateCircuit.Sim (Wire)
open GatePointerEncoding (wordValue)
open scoped InnerProduct BigOperators

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

namespace TParams

variable (p : TParams)

/-- The public conditions of the time-dependent solver. -/
structure PublicOK : Prop where
  T_pos : 0 < p.T
  g_ge : 1 ≤ p.g
  ε_pos : 0 < p.ε
  ε_half : p.ε ≤ 1 / 2
  lamH_nonneg : 0 ≤ p.lamH
  lamD_nonneg : 0 ≤ p.lamD
  energy_pos : 0 < p.lamH + p.R * p.lamD
  Q_ge : 1 ≤ p.Q
  qbar_nonneg : 0 ≤ p.qbar
  qbar_le : p.qbar ≤ p.Q
  mesh : TimeSchedule.steps p.tau (p.nu / 3) ≤ 2 ^ p.m

/-- The conditions on an instance. -/
structure InstanceOK (v : P) (σ : TOracles p.a p.m p.l P) (Hs Ls : ℕ → P →L[ℂ] P)
    (G : ℝ → P →L[ℂ] P) (b x : ℝ → P) (bs : ℕ → P) (βG δG βb δb bmax : ℝ) : Prop where
  select : p.SelectHypT σ Hs Ls
  psd : ∀ r < p.M, ∀ w : P, 0 ≤ (inner ℂ w (Ls r w)).re
  load_unitary : ∀ s, IsUnitary (σ.J s)
  prep_left : σ.Wp.conjTranspose * σ.Wp = 1
  prep_right : σ.Wp * σ.Wp.conjTranspose = 1
  prep : p.WpPromise σ (x 0) bs
  init_load : x 0 ≠ 0 →
    σ.J (false, fun _ => false) v = ODEStateNormalization.unitDirection (x 0)
  forcing_load : ∀ w : Fin p.m → Bool, bs (wordValue w) ≠ 0 →
    σ.J (true, w) v = ODEStateNormalization.unitDirection (bs (wordValue w))
  solves : TimeDependentODE.SolvesODE G b x 0 p.T
  accretive : ∀ u ∈ Set.Icc 0 p.T, TimeDependentODE.Accretive (G u)
  lipG : ∀ u ∈ Set.Icc 0 p.T, ∀ u' ∈ Set.Icc 0 p.T, ‖G u - G u'‖ ≤ βG * |u - u'|
  sampleG : ∀ r < p.M, ‖G (r * p.T / p.M) - gens Hs Ls r‖ ≤ δG
  lipb : ∀ u ∈ Set.Icc 0 p.T, ∀ u' ∈ Set.Icc 0 p.T, ‖b u - b u'‖ ≤ βb * |u - u'|
  sampleb : ∀ r < p.M, ‖b (r * p.T / p.M) - bs r‖ ≤ δb
  boundb : ∀ u ∈ Set.Icc 0 p.T, ‖b u‖ ≤ bmax
  βG_nonneg : 0 ≤ βG
  βb_nonneg : 0 ≤ βb
  target_ne : x p.T ≠ 0
  budget : p.mass (x 0) bs ≤ p.g * ‖x p.T‖
  disc : p.discretisation βG δG βb δb bmax ‖x 0‖ ≤ p.ε * p.mass (x 0) bs / (2000 * p.g)

theorem PublicOK.eps_le_one {p : TParams} (h : p.PublicOK) : p.ε ≤ 1 :=
  h.ε_half.trans (by norm_num)

theorem PublicOK.tau_pos {p : TParams} (h : p.PublicOK) : 0 < p.tau :=
  mul_pos h.T_pos h.energy_pos

theorem PublicOK.nu_pos {p : TParams} (h : p.PublicOK) : 0 < p.nu :=
  p.nu_pos h.g_ge h.ε_pos

theorem PublicOK.TD_nonneg {p : TParams} (h : p.PublicOK) : 0 ≤ p.T * p.lamD :=
  mul_nonneg h.T_pos.le h.lamD_nonneg

theorem unitary_of {v : P} {σ : TOracles p.a p.m p.l P} {Hs Ls : ℕ → P →L[ℂ] P}
    {G : ℝ → P →L[ℂ] P} {b x : ℝ → P} {bs : ℕ → P} {βG δG βb δb bmax : ℝ}
    (hI : p.InstanceOK v σ Hs Ls G b x bs βG δG βb δb bmax) : σ.Unitary p.m :=
  ⟨hI.select.uj, hI.select.priv, hI.load_unitary, hI.prep_left, hI.prep_right⟩

/-- The discretised target retains half of the solution norm and has the
solution's direction up to `ε / 1000`. -/
theorem target_facts (hp : p.PublicOK) {v : P} {σ : TOracles p.a p.m p.l P}
    {Hs Ls : ℕ → P →L[ℂ] P} {G : ℝ → P →L[ℂ] P} {b x : ℝ → P} {bs : ℕ → P}
    {βG δG βb δb bmax : ℝ} (hI : p.InstanceOK v σ Hs Ls G b x bs βG δG βb δb bmax) :
    p.target Hs Ls (x 0) bs ≠ 0 ∧ p.mass (x 0) bs ≤ 2 * p.g * ‖p.target Hs Ls (x 0) bs‖ ∧
      ‖ODEStateNormalization.unitDirection (p.target Hs Ls (x 0) bs) -
        ODEStateNormalization.unitDirection (x p.T)‖ ≤ p.ε / 1000 := by
  have hS := hI.select
  have hErr := p.discretisation_error hp.T_pos.le G b x Hs Ls bs βG δG βb δb bmax hI.βG_nonneg
    hI.βb_nonneg hI.solves hI.accretive hI.lipG hI.sampleG hI.lipb hI.sampleb hI.boundb hS.selfH
    hI.psd hS.normH hS.normL
  exact TimeDependentODE.Sampling.target_budget (x p.T) (p.target Hs Ls (x 0) bs)
    (p.mass (x 0) bs) p.g p.ε _ hp.g_ge hp.ε_pos hp.eps_le_one hI.target_ne hI.budget hErr hI.disc

/-- **The actual preparation satisfies the released actual-source
certificate for the discretised target.** -/
theorem prep_certificate (hp : p.PublicOK) (v : P) (hv : ‖v‖ = 1)
    (σ : TOracles p.a p.m p.l P) (Hs Ls : ℕ → P →L[ℂ] P) (G : ℝ → P →L[ℂ] P) (b x : ℝ → P)
    (bs : ℕ → P) (βG δG βb δb bmax : ℝ)
    (hI : p.InstanceOK v σ Hs Ls G b x bs βG δG βb δb bmax) :
    ODEActualSourceError.Certificate p.branchE (p.zsrc (x 0) bs) p.coeffW σ.J
      (trun v σ p.select) v (p.target Hs Ls (x 0) bs) p.ratio p.acc := by
  have hT := hp.T_pos.le
  have hS := hI.select
  have hU := p.unitary_of hI
  have hsel : IsUnitary (trun v σ p.select) :=
    trun_isUnitary v σ hU hv _ (fun g hg =>
      p.prepC_valid hp.tau_pos.le hp.nu_pos hp.mesh g (by simp [prepC, hg]))
  have hJ : ∀ s, (σ.J s)† ∘L σ.J s = 1 := by
    intro s
    have h := (hI.load_unitary s).1
    rwa [star_eq_adjoint, mul_def] at h
  have hM : 0 < p.T / p.M := div_pos hp.T_pos (by exact_mod_cast p.M_pos)
  have hPrep : ∀ s, p.zsrc (x 0) bs s ≠ 0 →
      σ.J s v = ODEStateNormalization.unitDirection (p.zsrc (x 0) bs s) := by
    intro s hs
    obtain ⟨c, w⟩ := s
    cases c
    · by_cases hw : w = (fun _ => false)
      · subst hw
        have hx : x 0 ≠ 0 := by
          intro h0
          apply hs
          simp [zsrc, h0]
        simp only [zsrc, Bool.false_eq_true, if_false, if_true]
        exact hI.init_load hx
      · exfalso
        apply hs
        simp [zsrc, hw]
    · have hb : bs (wordValue w) ≠ 0 := by
        intro h0
        apply hs
        simp [zsrc, h0]
      simp only [zsrc, if_true]
      rw [hI.forcing_load w hb, Complex.coe_smul, ODEHeraldedSuccess.unitDirection_pos_smul _ hM]
  obtain ⟨hy, hbud, _⟩ := p.target_facts hp hI
  have hNorm := p.target_norm_le hT Hs Ls hS.selfH hI.psd (x 0) bs
  have hSim := p.select_error hT hp.tau_pos hp.g_ge hp.ε_pos hp.eps_le_one hp.TD_nonneg hp.Q_ge
    hp.qbar_nonneg hp.qbar_le hp.mesh v σ Hs Ls hS
  have hLCHS := fun s => p.lchs_error hT hp.g_ge hp.ε_pos hp.eps_le_one hp.lamD_nonneg Hs Ls
    hS.selfH hS.selfL hS.normL hI.psd s
  have hQuad : ‖(∑ s, p.propS Hs Ls s (p.zsrc (x 0) bs s)) - p.target Hs Ls (x 0) bs‖ ≤
      ImprovedODEQueryBudget.precision p.ratio p.acc * ODESourceBranches.mass (p.zsrc (x 0) bs) := by
    rw [p.source_sum, sub_self, norm_zero]
    exact mul_nonneg (p.nu_pos hp.g_ge hp.ε_pos).le (ODESourceBranches.mass_nonneg _)
  have hmass := p.coeffW_mass hp.g_ge hp.ε_pos hp.eps_le_one hp.TD_nonneg
  have hacc : p.acc ≤ 1 / 2 := by
    have := hp.ε_half
    unfold acc
    linarith
  exact ODEActualSourceError.actual_source_certificate (σ := Bool × (Fin p.m → Bool))
    (ι := Fin p.l → Bool) (P := P) (K := Reg p.W P) p.branchE p.branchE_isometry
    (p.zsrc (x 0) bs) p.coeffW hmass σ.J hJ v hv hPrep (trun v σ p.select) hsel
    (p.branchU Hs Ls) (p.propS Hs Ls) (p.target Hs Ls (x 0) bs) p.ratio p.acc hy
    (p.ratio_ge hp.g_ge) (p.acc_pos hp.ε_pos) hacc hNorm hbud (by convert hSim using 4) hLCHS hQuad

/-- The clean decoded vector of the actual preparation is the released
actual-source decoded vector. -/
theorem decoded_eq (hp : p.PublicOK) (v : P) (σ : TOracles p.a p.m p.l P) (x0 : P) (bs : ℕ → P)
    (hB : 0 < p.mass x0 bs) (hW : p.WpPromise σ x0 bs) :
    ODEHeraldedSuccess.decoded goodF (trun v σ p.prepC) (seedState v) =
      ODEActualSourceError.decoded p.branchE (p.zsrc x0 bs) p.coeffW σ.J (trun v σ p.select) v := by
  rw [p.decoded_prepC v σ]
  have hin := p.inMap_eq_input hp.g_ge hp.ε_pos hp.eps_le_one hp.TD_nonneg v σ x0 bs hB hW
  have hout := p.outMap_eq_output hp.g_ge hp.ε_pos hp.eps_le_one hp.TD_nonneg σ x0 bs hB hW
  rw [hin, hout]
  simp only [ODEActualSourceError.decoded, ODEHeraldedSuccess.decoded]

/-- **Mean success and direction error of the actual trial circuits.** -/
theorem trial_bounds (hp : p.PublicOK) (v : P) (hv : ‖v‖ = 1)
    (σ : TOracles p.a p.m p.l P) (Hs Ls : ℕ → P →L[ℂ] P) (G : ℝ → P →L[ℂ] P) (b x : ℝ → P)
    (bs : ℕ → P) (βG δG βb δb bmax : ℝ)
    (hI : p.InstanceOK v σ Hs Ls G b x bs βG δG βb δb bmax) :
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
          ODEStateNormalization.unitDirection (x p.T)‖ ≤ p.ε / 500 := by
  have hU := p.unitary_of hI
  have hW := p.prepC_isUnitary hp.tau_pos.le hp.nu_pos hp.mesh v hv σ hU
  have hC := p.prep_certificate hp v hv σ Hs Ls G b x bs βG δG βb δb bmax hI
  obtain ⟨hy, _, hdirY⟩ := p.target_facts hp hI
  have hB : 0 < p.mass (x 0) bs := by
    have hNorm := p.target_norm_le hp.T_pos.le Hs Ls hI.select.selfH hI.psd (x 0) bs
    have := norm_pos_iff.mpr hy
    linarith
  have hdec := p.decoded_eq hp v σ (x 0) bs hB hI.prep
  have hamp : ODEGroverActual.amplitude goodF (trun v σ p.prepC) (seedState v) =
      ‖ODEActualSourceError.decoded p.branchE (p.zsrc (x 0) bs) p.coeffW σ.J
        (trun v σ p.select) v‖ := by
    rw [ODEGroverActual.amplitude, ← ODEHeraldedSuccess.successfulComponent,
      ODEHeraldedSuccess.successfulComponent_norm _ goodF_isometry, hdec]
  have hampC : ‖ODEHeraldedSuccess.successfulComponent (ODEActualSourceError.output p.branchE
      (p.zsrc (x 0) bs) p.coeffW) (trun v σ p.select)
        (ODEActualSourceError.input p.branchE (p.zsrc (x 0) bs) p.coeffW σ.J v)‖ =
      ‖ODEActualSourceError.decoded p.branchE (p.zsrc (x 0) bs) p.coeffW σ.J
        (trun v σ p.select) v‖ :=
    ODEHeraldedSuccess.successfulComponent_norm _ hC.output_isometry _ _
  have hlow : 1 / (4 * p.ratio) ≤ ODEGroverActual.amplitude goodF (trun v σ p.prepC)
      (seedState v) := by
    rw [hamp, ← hampC]
    exact hC.amplitude_lower
  have hup : ODEGroverActual.amplitude goodF (trun v σ p.prepC) (seedState v) ≤ 1 / 2 := by
    rw [hamp, ← hampC]
    exact hC.amplitude_upper.le
  have herr : ‖ODEStateNormalization.unitDirection ((goodF†) (trun v σ p.prepC
      (seedState v))) - ODEStateNormalization.unitDirection (p.target Hs Ls (x 0) bs)‖ ≤
        p.acc / 500 := by
    have h := hC.direction_error
    rw [← ODEHeraldedSuccess.decoded, hdec]
    exact h
  have hR := ODEGroverActual.randomized_certificate (P := P) (K := Reg p.W P) goodF goodF_isometry
    (trun v σ p.prepC) hW (seedState v) (seedState_norm v hv) p.ratio (p.ratio_ge hp.g_ge) hlow
    hup (p.target Hs Ls (x 0) bs) (p.acc / 500) herr
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
            ODEStateNormalization.unitDirection (p.target Hs Ls (x 0) bs)‖ +
          ‖ODEStateNormalization.unitDirection (p.target Hs Ls (x 0) bs) -
            ODEStateNormalization.unitDirection (x p.T)‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ p.acc / 500 + p.ε / 1000 := add_le_add hd hdirY
      _ = p.ε / 500 := by unfold acc; ring

end TParams

end

end SparseHamiltonian.GateODE.Time
