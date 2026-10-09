import GateEfficientSelect.ODE.Disc

/-!
# The certificate of the released preparation on branch-dependent meshes

`BInstanceOK` collects the conditions on an instance of the released time-dependent protocol
read with the branch-dependent meshes of Lemma `ode:lem:gate-select`:

* unitary supplied operations, and the clock promises of the released simulator at every joint
  label `z = (s, w)` and slot `r` for the normalised slot Hamiltonian
  `branchHB = (durB s / τ)(Hb s r + k_w Lb s r)` of the branch of `s` on its own mesh;
* represented branch samples `Hb s r`, `Lb s r` (self-adjoint, `‖Hb‖ ≤ λH`, `‖Lb‖ ≤ λD`,
  `Lb ≥ 0`) with `‖G(addrB s r) - (Lb s r + i Hb s r)‖ ≤ δG` at the branch addresses
  `addrB s r = startB s + r (T - startB s) / 2^m`, for an accretive `βG`-Lipschitz generator
  path `G`;
* a positive source quadrature: nodes `v q ∈ [0, T]` (`q < 2^m`), weights `w q ≥ 0` and
  forcing vectors `f q`; the source vector of the forcing label `(true, q)` is `w_q f_q` and the
  source mass is `B = ‖x(0)‖ + ∑_q w_q ‖f_q‖` (`mass_bsW`); the weight preparation has the
  amplitudes `sqrt (‖z_s‖ / B)` (the released `WpPromise`), and the loading places the
  directions of `x(0)` and of every `f_q` with `w_q ≠ 0`;
* a solution `x` of `x' = -G(u) x + b(u)` on `[0, T]` with `x(T) ≠ 0` and `B ≤ g ‖x(T)‖`, and
  the source certificate: solutions `y_s` of `y' = -G(u) y` on `[startB s, T]` with
  `y_s(startB s) = z_s` (informally `y_s(T) = U(T, v_s) z_s` for the propagator `U` of the
  paper) and `‖x(T) - ∑_s y_s(T)‖ ≤ κ`; with `f_q = b(v_q)` this is the first certificate of
  `ode:eq:gate-source-certificates`, and the proofs use the solution only through `x(0)`, `x(T)`
  and the certificate;
* the budget `κ + T (βG T / 2^m + δG) B ≤ ε B / (2000 g)`.

Under them the exact target retains half of the solution norm and has its direction up to
`ε / 1000` (`target_factsB`), and the actual preparation of the released protocol satisfies the
released actual-source certificate for the exact target (`prep_certificateB`); the released
randomized amplification then gives the trial bounds (`trial_boundsB`).
-/

set_option autoImplicit false

namespace SparseHamiltonian.GateSelect.ODE

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit
open GateCircuit.Sim (Wire)
open GateODE (Label ClockPromise goodF goodF_isometry seedState seedState_norm)
open GateODE.Time (TParams TOracles trun gens)
open GatePointerEncoding (wordValue)
open TimeDependentODE (SolvesODE Accretive)
open ODEStateNormalization (unitDirection)
open scoped InnerProduct BigOperators

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

variable (p : TParams)

/-- The conditions on an instance of the released time-dependent protocol on branch-dependent
meshes. -/
structure BInstanceOK (v₀ : P) (σ : TOracles p.a p.m p.l P) (v wq : ℕ → ℝ) (fv : ℕ → P)
    (Hb Lb : Bool × (Fin p.m → Bool) → ℕ → P →L[ℂ] P) (G : ℝ → P →L[ℂ] P) (b x : ℝ → P)
    (ys : Bool × (Fin p.m → Bool) → ℝ → P) (βG δG κ : ℝ) : Prop where
  uj : IsUnitary σ.UJ
  priv : ∀ z, ∀ r < p.M, IsUnitary (σ.D z r)
  clock : ∀ z, ∀ r < p.M, ClockPromise σ.UJ (σ.D z r) (branchHB p v Hb Lb z r) p.Q p.qbar
  selfH : ∀ s, ∀ r < p.M, star (Hb s r) = Hb s r
  selfL : ∀ s, ∀ r < p.M, star (Lb s r) = Lb s r
  normH : ∀ s, ∀ r < p.M, ‖Hb s r‖ ≤ p.lamH
  normL : ∀ s, ∀ r < p.M, ‖Lb s r‖ ≤ p.lamD
  psd : ∀ s, ∀ r < p.M, ∀ w : P, 0 ≤ (inner ℂ w (Lb s r w)).re
  nodes : ∀ q < p.M, 0 ≤ v q ∧ v q ≤ p.T
  weights : ∀ q < p.M, 0 ≤ wq q
  load_unitary : ∀ s, IsUnitary (σ.J s)
  prep_left : σ.Wp.conjTranspose * σ.Wp = 1
  prep_right : σ.Wp * σ.Wp.conjTranspose = 1
  prep : p.WpPromise σ (x 0) (bsW p wq fv)
  init_load : x 0 ≠ 0 → σ.J (false, fun _ => false) v₀ = unitDirection (x 0)
  forcing_load : ∀ w : Fin p.m → Bool, wq (wordValue w) ≠ 0 → fv (wordValue w) ≠ 0 →
    σ.J (true, w) v₀ = unitDirection (fv (wordValue w))
  solves : SolvesODE G b x 0 p.T
  accretive : ∀ u ∈ Set.Icc 0 p.T, Accretive (G u)
  lipG : ∀ u ∈ Set.Icc 0 p.T, ∀ u' ∈ Set.Icc 0 p.T, ‖G u - G u'‖ ≤ βG * |u - u'|
  βG_nonneg : 0 ≤ βG
  sampleG : ∀ s, ∀ r < p.M, ‖G (addrB p v s r) - gens (Hb s) (Lb s) r‖ ≤ δG
  branch_sol : ∀ s, SolvesODE G (fun _ => 0) (ys s) (startB p v s) p.T
  branch_init : ∀ s, ys s (startB p v s) = p.zsrc (x 0) (bsW p wq fv) s
  quad : ‖x p.T - ∑ s, ys s p.T‖ ≤ κ
  target_ne : x p.T ≠ 0
  budget : p.mass (x 0) (bsW p wq fv) ≤ p.g * ‖x p.T‖
  disc : κ + p.T * (βG * (p.T / p.M) + δG) * p.mass (x 0) (bsW p wq fv) ≤
    p.ε * p.mass (x 0) (bsW p wq fv) / (2000 * p.g)

section Facts

variable {p}
variable {v₀ : P} {σ : TOracles p.a p.m p.l P} {v wq : ℕ → ℝ} {fv : ℕ → P}
  {Hb Lb : Bool × (Fin p.m → Bool) → ℕ → P →L[ℂ] P} {G : ℝ → P →L[ℂ] P} {b x : ℝ → P}
  {ys : Bool × (Fin p.m → Bool) → ℝ → P} {βG δG κ : ℝ}

theorem BInstanceOK.unitary (hI : BInstanceOK p v₀ σ v wq fv Hb Lb G b x ys βG δG κ) :
    σ.Unitary p.m :=
  ⟨hI.uj, hI.priv, hI.load_unitary, hI.prep_left, hI.prep_right⟩

/-- The exact target retains half of the solution norm and has the solution's direction up to
`ε / 1000`. -/
theorem target_factsB (hp : p.PublicOK) (hI : BInstanceOK p v₀ σ v wq fv Hb Lb G b x ys βG δG κ) :
    targetB p v Hb Lb (x 0) wq fv ≠ 0 ∧
      p.mass (x 0) (bsW p wq fv) ≤ 2 * p.g * ‖targetB p v Hb Lb (x 0) wq fv‖ ∧
      ‖unitDirection (targetB p v Hb Lb (x 0) wq fv) - unitDirection (x p.T)‖ ≤ p.ε / 1000 := by
  have hErr := target_errorB p hp.T_pos v hI.nodes Hb Lb G x ys wq fv βG δG κ hI.βG_nonneg
    hI.branch_sol hI.branch_init hI.quad hI.accretive hI.lipG hI.sampleG hI.selfH hI.psd
  exact TimeDependentODE.Sampling.target_budget (x p.T) (targetB p v Hb Lb (x 0) wq fv)
    (p.mass (x 0) (bsW p wq fv)) p.g p.ε _ hp.g_ge hp.ε_pos hp.eps_le_one hI.target_ne
    hI.budget hErr hI.disc

end Facts

/-- **The actual preparation of the released protocol satisfies the released actual-source
certificate for the exact target on branch-dependent meshes.** -/
theorem prep_certificateB (hp : p.PublicOK) (v₀ : P) (hv : ‖v₀‖ = 1)
    (σ : TOracles p.a p.m p.l P) (v wq : ℕ → ℝ) (fv : ℕ → P)
    (Hb Lb : Bool × (Fin p.m → Bool) → ℕ → P →L[ℂ] P) (G : ℝ → P →L[ℂ] P) (b x : ℝ → P)
    (ys : Bool × (Fin p.m → Bool) → ℝ → P) (βG δG κ : ℝ)
    (hI : BInstanceOK p v₀ σ v wq fv Hb Lb G b x ys βG δG κ) :
    ODEActualSourceError.Certificate p.branchE (p.zsrc (x 0) (bsW p wq fv)) p.coeffW σ.J
      (trun v₀ σ p.select) v₀ (targetB p v Hb Lb (x 0) wq fv) p.ratio p.acc := by
  have hT := hp.T_pos.le
  have hU := hI.unitary
  have hsel : IsUnitary (trun v₀ σ p.select) :=
    GateODE.Time.trun_isUnitary v₀ σ hU hv _ (fun g hg =>
      p.prepC_valid hp.tau_pos.le hp.nu_pos hp.mesh g (by simp [GateODE.Time.TParams.prepC, hg]))
  have hJ : ∀ s, (σ.J s)† ∘L σ.J s = 1 := by
    intro s
    have h := (hI.load_unitary s).1
    rwa [star_eq_adjoint, mul_def] at h
  have hPrep : ∀ s, p.zsrc (x 0) (bsW p wq fv) s ≠ 0 →
      σ.J s v₀ = unitDirection (p.zsrc (x 0) (bsW p wq fv) s) := by
    intro s hs
    obtain ⟨c, w⟩ := s
    cases c
    · by_cases hw : w = (fun _ => false)
      · subst hw
        have hx : x 0 ≠ 0 := by
          intro h0
          apply hs
          simp [GateODE.Time.TParams.zsrc, h0]
        simp only [GateODE.Time.TParams.zsrc, Bool.false_eq_true, if_false, if_true]
        exact hI.init_load hx
      · exfalso
        apply hs
        simp [GateODE.Time.TParams.zsrc, hw]
    · rw [zsrc_bsW p hp.T_pos] at hs ⊢
      have hwq : wq (wordValue w) ≠ 0 := by
        intro h0
        apply hs
        simp [h0]
      have hfv : fv (wordValue w) ≠ 0 := by
        intro h0
        apply hs
        simp [h0]
      have hpos : 0 < wq (wordValue w) :=
        lt_of_le_of_ne (hI.weights _ (GatePointerEncoding.wordValue_lt_pow w)) (Ne.symm hwq)
      rw [hI.forcing_load w hwq hfv, Complex.coe_smul,
        ODEHeraldedSuccess.unitDirection_pos_smul _ hpos]
  obtain ⟨hy, hbud, _⟩ := target_factsB hp hI
  have hNorm := targetB_norm_le p hT v hI.nodes Hb Lb hI.selfH hI.selfL hI.psd (x 0) wq fv
  have hSim := select_errorB p hp v₀ σ v hI.nodes Hb Lb hI.uj hI.priv hI.selfH hI.selfL
    hI.normH hI.normL hI.clock
  have hLCHS := fun s => lchs_errorB p hT hp.g_ge hp.ε_pos hp.eps_le_one hp.lamD_nonneg v
    hI.nodes Hb Lb hI.selfH hI.selfL hI.normL hI.psd s
  have hQuad : ‖(∑ s, propB p v Hb Lb s (p.zsrc (x 0) (bsW p wq fv) s)) -
      targetB p v Hb Lb (x 0) wq fv‖ ≤
      ImprovedODEQueryBudget.precision p.ratio p.acc *
        ODESourceBranches.mass (p.zsrc (x 0) (bsW p wq fv)) := by
    unfold targetB
    rw [sub_self, norm_zero]
    exact mul_nonneg hp.nu_pos.le (ODESourceBranches.mass_nonneg _)
  have hmass := p.coeffW_mass hp.g_ge hp.ε_pos hp.eps_le_one hp.TD_nonneg
  have hacc : p.acc ≤ 1 / 2 := by
    have := hp.ε_half
    unfold GateODE.Time.TParams.acc
    linarith
  exact ODEActualSourceError.actual_source_certificate (σ := Bool × (Fin p.m → Bool))
    (ι := Fin p.l → Bool) (P := P) (K := Reg p.W P) p.branchE p.branchE_isometry
    (p.zsrc (x 0) (bsW p wq fv)) p.coeffW hmass σ.J hJ v₀ hv hPrep (trun v₀ σ p.select) hsel
    (branchUB p v Hb Lb) (propB p v Hb Lb) (targetB p v Hb Lb (x 0) wq fv) p.ratio p.acc hy
    (p.ratio_ge hp.g_ge) (p.acc_pos hp.ε_pos) hacc hNorm hbud (by convert hSim using 4) hLCHS
    hQuad

/-- **Mean success and direction error of the actual trial circuits on branch-dependent
meshes.** -/
theorem trial_boundsB (hp : p.PublicOK) (v₀ : P) (hv : ‖v₀‖ = 1)
    (σ : TOracles p.a p.m p.l P) (v wq : ℕ → ℝ) (fv : ℕ → P)
    (Hb Lb : Bool × (Fin p.m → Bool) → ℕ → P →L[ℂ] P) (G : ℝ → P →L[ℂ] P) (b x : ℝ → P)
    (ys : Bool × (Fin p.m → Bool) → ℝ → P) (βG δG κ : ℝ)
    (hI : BInstanceOK p v₀ σ v wq fv Hb Lb G b x ys βG δG κ) :
    0 < ODEGroverAverage.chosenIterations p.ratio ∧
    (ODEGroverAverage.chosenIterations p.ratio : ℝ) ≤ 5 * p.ratio ∧
    (1 : ℝ) / 4 ≤ (∑ j ∈ Finset.range (ODEGroverAverage.chosenIterations p.ratio),
      ‖ODEHeraldedSuccess.successProjector goodF
        (trun v₀ σ (p.trialC j) (seedState v₀))‖ ^ 2) /
        (ODEGroverAverage.chosenIterations p.ratio : ℝ) ∧
    ∀ j : ℕ, (goodF†) (trun v₀ σ (p.trialC j) (seedState v₀)) ≠ 0 →
      ∃ ω : ℂ, ‖ω‖ = 1 ∧
        ‖ω • unitDirection ((goodF†) (trun v₀ σ (p.trialC j) (seedState v₀))) -
          unitDirection (x p.T)‖ ≤ p.ε / 500 := by
  have hU := hI.unitary
  have hW := p.prepC_isUnitary hp.tau_pos.le hp.nu_pos hp.mesh v₀ hv σ hU
  have hC := prep_certificateB p hp v₀ hv σ v wq fv Hb Lb G b x ys βG δG κ hI
  obtain ⟨hy, _, hdirY⟩ := target_factsB hp hI
  have hB : 0 < p.mass (x 0) (bsW p wq fv) := by
    have hNorm := targetB_norm_le p hp.T_pos.le v hI.nodes Hb Lb hI.selfH hI.selfL hI.psd (x 0)
      wq fv
    have := norm_pos_iff.mpr hy
    linarith
  have hdec := p.decoded_eq hp v₀ σ (x 0) (bsW p wq fv) hB hI.prep
  have hamp : ODEGroverActual.amplitude goodF (trun v₀ σ p.prepC) (seedState v₀) =
      ‖ODEActualSourceError.decoded p.branchE (p.zsrc (x 0) (bsW p wq fv)) p.coeffW σ.J
        (trun v₀ σ p.select) v₀‖ := by
    rw [ODEGroverActual.amplitude, ← ODEHeraldedSuccess.successfulComponent,
      ODEHeraldedSuccess.successfulComponent_norm _ goodF_isometry, hdec]
  have hampC : ‖ODEHeraldedSuccess.successfulComponent (ODEActualSourceError.output p.branchE
      (p.zsrc (x 0) (bsW p wq fv)) p.coeffW) (trun v₀ σ p.select)
        (ODEActualSourceError.input p.branchE (p.zsrc (x 0) (bsW p wq fv)) p.coeffW σ.J v₀)‖ =
      ‖ODEActualSourceError.decoded p.branchE (p.zsrc (x 0) (bsW p wq fv)) p.coeffW σ.J
        (trun v₀ σ p.select) v₀‖ :=
    ODEHeraldedSuccess.successfulComponent_norm _ hC.output_isometry _ _
  have hlow : 1 / (4 * p.ratio) ≤ ODEGroverActual.amplitude goodF (trun v₀ σ p.prepC)
      (seedState v₀) := by
    rw [hamp, ← hampC]
    exact hC.amplitude_lower
  have hup : ODEGroverActual.amplitude goodF (trun v₀ σ p.prepC) (seedState v₀) ≤ 1 / 2 := by
    rw [hamp, ← hampC]
    exact hC.amplitude_upper.le
  have herr : ‖unitDirection ((goodF†) (trun v₀ σ p.prepC (seedState v₀))) -
      unitDirection (targetB p v Hb Lb (x 0) wq fv)‖ ≤ p.acc / 500 := by
    have h := hC.direction_error
    rw [← ODEHeraldedSuccess.decoded, hdec]
    exact h
  have hR := ODEGroverActual.randomized_certificate (P := P) (K := Reg p.W P) goodF
    goodF_isometry (trun v₀ σ p.prepC) hW (seedState v₀) (seedState_norm v₀ hv) p.ratio
    (p.ratio_ge hp.g_ge) hlow hup (targetB p v Hb Lb (x 0) wq fv) (p.acc / 500) herr
  have htrial : ∀ j, trun v₀ σ (p.trialC j) (seedState v₀) =
      ODEGroverActual.trial goodF (trun v₀ σ p.prepC) (seedState v₀) j :=
    fun j => p.trialC_seed hp.tau_pos.le hp.nu_pos hp.mesh v₀ hv σ hU j
  obtain ⟨hM, hM5, hmean, hdir⟩ := hR
  refine ⟨hM, hM5, ?_, ?_⟩
  · simp only [htrial]
    exact hmean
  · intro j hj
    rw [htrial] at hj ⊢
    obtain ⟨ω, hω, hd⟩ := hdir j hj
    refine ⟨ω, hω, ?_⟩
    calc _ ≤ ‖ω • unitDirection (ODEGroverActual.decoded goodF
            (trun v₀ σ p.prepC) (seedState v₀) j) -
            unitDirection (targetB p v Hb Lb (x 0) wq fv)‖ +
          ‖unitDirection (targetB p v Hb Lb (x 0) wq fv) - unitDirection (x p.T)‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ p.acc / 500 + p.ε / 1000 := add_le_add hd hdirY
      _ = p.ε / 500 := by unfold GateODE.Time.TParams.acc; ring

end

end SparseHamiltonian.GateSelect.ODE
