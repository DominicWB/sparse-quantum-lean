import GateEfficientODE.Analysis.Table

/-!
# The certificate of the actual gate-level preparation and its trials

`PublicOK` collects the public conditions and `InstanceOK` the conditions on
an instance: the supplied unitaries, the Hermitian parts `H, L` of `-A`
(`L ≥ 0`, `‖H‖ ≤ λH`, `‖L‖ ≤ λD`), the clock promises of every label, the
source vectors `x₀, b` with the public norms and their preparation from the
seed, a nonzero solution, and the normalisation `B ≤ g ‖x(T)‖`.

Under them the actual preparation circuit satisfies the released
actual-source certificate (`prep_certificate`): its clean decoded vector has
direction within `ε / 500` of the solution and amplitude in
`[1/(4g), 1/2)`.  The released randomized amplification theorem then gives,
for the actual trial circuits, mean success at least `1/4` over the public
cutoff `chosenIterations g ≤ 5g` and the same direction error for every
successful trial (`trial_bounds`).
-/

namespace SparseHamiltonian.GateODE

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit
open GateCircuit.Sim (Wire)
open scoped InnerProduct BigOperators

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

namespace Params

variable (p : Params)

/-- The public conditions of the solver. -/
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
  r₀_nonneg : 0 ≤ p.r₀
  rb_nonneg : 0 ≤ p.rb
  B_pos : 0 < p.B

/-- The solution of `x' = A x + b`, `A = -(L + iH)`, at time `T`. -/
def target (H L : P →L[ℂ] P) (x0 b : P) : P :=
  ODEConstantForcing.solution (gen H L) x0 b p.T

/-- The conditions on an instance. -/
structure InstanceOK (v : P) (σ : Oracles p.a (Label p.k p.l) P) (H L : P →L[ℂ] P)
    (x0 b : P) : Prop where
  select : p.SelectHyp σ H L
  src_unitary : ∀ c, IsUnitary (σ.J c)
  psd : ∀ w : P, 0 ≤ (inner ℂ w (L w)).re
  init_norm : ‖x0‖ = p.r₀
  forcing_norm : ‖b‖ = p.rb
  init_prep : x0 ≠ 0 → σ.J false v = ODEStateNormalization.unitDirection x0
  forcing_prep : b ≠ 0 → σ.J true v = ODEStateNormalization.unitDirection b
  target_ne : p.target H L x0 b ≠ 0
  budget : p.B ≤ p.g * ‖p.target H L x0 b‖

theorem PublicOK.eps_le_one {p : Params} (h : p.PublicOK) : p.ε ≤ 1 :=
  h.ε_half.trans (by norm_num)

theorem PublicOK.tau_pos {p : Params} (h : p.PublicOK) : 0 < p.tau :=
  mul_pos h.T_pos h.energy_pos

theorem PublicOK.nu_pos {p : Params} (h : p.PublicOK) : 0 < p.nu :=
  ImprovedODEQueryBudget.precision_pos p.g p.ε h.g_ge h.ε_pos

theorem PublicOK.TD_nonneg {p : Params} (h : p.PublicOK) : 0 ≤ p.T * p.lamD :=
  mul_nonneg h.T_pos.le h.lamD_nonneg

theorem unitaries_of {v : P} (hv : ‖v‖ = 1) {σ : Oracles p.a (Label p.k p.l) P}
    {H L : P →L[ℂ] P} {x0 b : P} (hI : p.InstanceOK v σ H L x0 b) : p.Unitaries v σ :=
  ⟨hv, hI.select.uj, hI.select.priv, hI.src_unitary⟩

/-- **The actual preparation satisfies the released actual-source
certificate.** -/
theorem prep_certificate (hp : p.PublicOK) (v : P) (hv : ‖v‖ = 1)
    (σ : Oracles p.a (Label p.k p.l) P) (H L : P →L[ℂ] P) (x0 b : P)
    (hI : p.InstanceOK v σ H L x0 b) :
    ODEActualSourceError.Certificate p.branchE (p.zsrc x0 b) p.coeffW (p.srcJ σ)
      (run (wiring v) σ p.select) v (p.target H L x0 b) p.g p.ε := by
  have hT := hp.T_pos.le
  have hS := hI.select
  have hU := p.unitaries_of hv hI
  have hsel : IsUnitary (run (wiring v) σ p.select) :=
    run_isUnitary _ _ hU.uj hU.priv hU.src hU.seed _ (fun g hg =>
      p.prepC_valid hp.tau_pos.le hp.nu_pos hp.r₀_nonneg hp.rb_nonneg hT hp.B_pos g
        (by simp [prepC, hg]))
  have hJ : ∀ s, (p.srcJ σ s)† ∘L p.srcJ σ s = 1 := by
    intro s
    have h := (hI.src_unitary s.1).1
    rwa [star_eq_adjoint, mul_def] at h
  have hPrep : ∀ s, p.zsrc x0 b s ≠ 0 →
      p.srcJ σ s v = ODEStateNormalization.unitDirection (p.zsrc x0 b s) := by
    intro s hs
    obtain ⟨c, w⟩ := s
    cases c
    · have hx : x0 ≠ 0 := by
        intro h0
        apply hs
        simp [zsrc, h0]
      simp only [srcJ, zsrc, Bool.false_eq_true, if_false]
      rw [hI.init_prep hx, smul_ofReal, ODEHeraldedSuccess.unitDirection_pos_smul _ (by positivity)]
    · have hb : b ≠ 0 := by
        intro h0
        apply hs
        simp [zsrc, h0]
      simp only [srcJ, zsrc, if_true]
      rw [hI.forcing_prep hb, smul_ofReal,
        ODEHeraldedSuccess.unitDirection_pos_smul _ (div_pos hp.T_pos (by positivity))]
  have hNorm := p.solution_le_mass hT H L hS.selfH hS.selfL hI.psd x0 b hI.init_norm
    hI.forcing_norm
  have hBudget : ODESourceBranches.mass (p.zsrc x0 b) ≤ p.g * ‖p.target H L x0 b‖ := by
    rw [p.mass_zsrc x0 b hT hI.init_norm hI.forcing_norm]
    exact hI.budget
  have hSim := p.select_error hT hp.tau_pos hp.g_ge hp.ε_pos hp.eps_le_one hp.TD_nonneg hp.Q_ge
    hp.qbar_le v σ H L hS
  have hLCHS := fun s => p.lchs_error hT hp.g_ge hp.ε_pos hp.eps_le_one hp.TD_nonneg H L
    hS.selfH hS.selfL hS.normL hI.psd s
  have hQuad := p.quadrature_error hT hp.g_ge hp.ε_pos H L hS.selfH hS.selfL hS.normH hS.normL
    hI.psd x0 b hI.init_norm hI.forcing_norm
  have hmass := p.coeffW_mass hp.g_ge hp.ε_pos hp.eps_le_one hp.TD_nonneg
  have h1 := ODEActualSourceError.actual_source_certificate (σ := Bool × (Fin p.k → Bool))
    (ι := Fin p.l → Bool) (P := P) (K := Reg p.W P) p.branchE p.branchE_isometry
    (p.zsrc x0 b) p.coeffW hmass (p.srcJ σ) hJ v hv hPrep (run (wiring v) σ p.select) hsel
    (p.branchU H L) (p.propS H L) (p.target H L x0 b) p.g p.ε hI.target_ne hp.g_ge hp.ε_pos
    hp.ε_half hNorm hBudget (by convert hSim using 4) hLCHS hQuad
  exact h1

/-- The clean decoded vector of the actual preparation is the released
actual-source decoded vector. -/
theorem decoded_eq (hp : p.PublicOK) (v : P) (σ : Oracles p.a (Label p.k p.l) P) (x0 b : P)
    (h₀ : ‖x0‖ = p.r₀) (hb : ‖b‖ = p.rb) :
    ODEHeraldedSuccess.decoded goodF (run (wiring v) σ p.prepC) (seedState v) =
      ODEActualSourceError.decoded p.branchE (p.zsrc x0 b) p.coeffW (p.srcJ σ)
        (run (wiring v) σ p.select) v := by
  rw [p.decoded_prepC v σ]
  have hin := p.inMap_eq_input hp.g_ge hp.ε_pos hp.eps_le_one hp.TD_nonneg
    hp.r₀_nonneg hp.rb_nonneg hp.T_pos.le hp.B_pos x0 b h₀ hb v σ
  have hout := p.outMap_eq_output (P := P) hp.g_ge hp.ε_pos hp.eps_le_one hp.TD_nonneg hp.r₀_nonneg
    hp.rb_nonneg hp.T_pos.le hp.B_pos x0 b h₀ hb
  rw [hin, hout]
  simp only [ODEActualSourceError.decoded, ODEHeraldedSuccess.decoded]

/-- **Mean success and direction error of the actual trial circuits.** -/
theorem trial_bounds (hp : p.PublicOK) (v : P) (hv : ‖v‖ = 1)
    (σ : Oracles p.a (Label p.k p.l) P) (H L : P →L[ℂ] P) (x0 b : P)
    (hI : p.InstanceOK v σ H L x0 b) :
    0 < ODEGroverAverage.chosenIterations p.g ∧
    (ODEGroverAverage.chosenIterations p.g : ℝ) ≤ 5 * p.g ∧
    (1 : ℝ) / 4 ≤ (∑ j ∈ Finset.range (ODEGroverAverage.chosenIterations p.g),
      ‖ODEHeraldedSuccess.successProjector goodF
        (run (wiring v) σ (p.trialC j) (seedState v))‖ ^ 2) /
        (ODEGroverAverage.chosenIterations p.g : ℝ) ∧
    ∀ j : ℕ, (goodF†) (run (wiring v) σ (p.trialC j) (seedState v)) ≠ 0 →
      ∃ ω : ℂ, ‖ω‖ = 1 ∧
        ‖ω • ODEStateNormalization.unitDirection
            ((goodF†) (run (wiring v) σ (p.trialC j) (seedState v))) -
          ODEStateNormalization.unitDirection (p.target H L x0 b)‖ ≤ p.ε / 500 := by
  have hT := hp.T_pos.le
  have hU := p.unitaries_of hv hI
  have hW := p.prepC_isUnitary hp.tau_pos.le hp.nu_pos hp.r₀_nonneg hp.rb_nonneg hT hp.B_pos v σ hU
  have hC := p.prep_certificate hp v hv σ H L x0 b hI
  have hdec := p.decoded_eq hp v σ x0 b hI.init_norm hI.forcing_norm
  have hamp : ODEGroverActual.amplitude goodF (run (wiring v) σ p.prepC) (seedState v) =
      ‖ODEActualSourceError.decoded p.branchE (p.zsrc x0 b) p.coeffW (p.srcJ σ)
        (run (wiring v) σ p.select) v‖ := by
    rw [ODEGroverActual.amplitude, ← ODEHeraldedSuccess.successfulComponent,
      ODEHeraldedSuccess.successfulComponent_norm _ goodF_isometry, hdec]
  have hampC : ‖ODEHeraldedSuccess.successfulComponent (ODEActualSourceError.output p.branchE
      (p.zsrc x0 b) p.coeffW) (run (wiring v) σ p.select)
        (ODEActualSourceError.input p.branchE (p.zsrc x0 b) p.coeffW (p.srcJ σ) v)‖ =
      ‖ODEActualSourceError.decoded p.branchE (p.zsrc x0 b) p.coeffW (p.srcJ σ)
        (run (wiring v) σ p.select) v‖ :=
    ODEHeraldedSuccess.successfulComponent_norm _ hC.output_isometry _ _
  have hlow : 1 / (4 * p.g) ≤ ODEGroverActual.amplitude goodF (run (wiring v) σ p.prepC)
      (seedState v) := by
    rw [hamp, ← hampC]
    exact hC.amplitude_lower
  have hup : ODEGroverActual.amplitude goodF (run (wiring v) σ p.prepC) (seedState v) ≤ 1 / 2 := by
    rw [hamp, ← hampC]
    exact hC.amplitude_upper.le
  have herr : ‖ODEStateNormalization.unitDirection ((goodF†) (run (wiring v) σ p.prepC
      (seedState v))) - ODEStateNormalization.unitDirection (p.target H L x0 b)‖ ≤ p.ε / 500 := by
    have h := hC.direction_error
    rw [← ODEHeraldedSuccess.decoded, hdec]
    exact h
  have hR := ODEGroverActual.randomized_certificate (P := P) (K := Reg p.W P) goodF goodF_isometry
    (run (wiring v) σ p.prepC) hW (seedState v) (seedState_norm v hv) p.g hp.g_ge hlow hup
    (p.target H L x0 b) (p.ε / 500) herr
  have htrial : ∀ j, run (wiring v) σ (p.trialC j) (seedState v) =
      ODEGroverActual.trial goodF (run (wiring v) σ p.prepC) (seedState v) j :=
    fun j => p.trialC_seed hp.tau_pos.le hp.nu_pos hp.r₀_nonneg hp.rb_nonneg hT hp.B_pos v σ hU j
  obtain ⟨hM, hM5, hmean, hdir⟩ := hR
  refine ⟨hM, hM5, ?_, ?_⟩
  · simp only [htrial]
    exact hmean
  · intro j hj
    rw [htrial] at hj ⊢
    exact hdir j hj

end Params

end

end SparseHamiltonian.GateODE
