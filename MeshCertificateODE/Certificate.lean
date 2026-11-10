import MeshCertificateODE.Target

/-!
# The time-dependent gate solver under the manuscript's certificates: the instance conditions

`CertInstanceOK` collects the instance conditions of the time-dependent gate solver
(`GateODE.Time`) in the form of Theorem `ode:thm:gates` for the
time-dependent problem of Theorem `ode:thm:time`:

* the selection hypotheses of the represented samples `G̃_r = L_r + i H_r` (`SelectHypT`: the
  uniform moment and norm promises; no positivity of the represented dissipative parts) and the
  supplied loading and weight preparation with their promises (the initial state and the source
  vectors `b_r` of the slot nodes `t_r = r T / M`, weighted by `T / M`);
* the generator pieces `G_r` on the uniform mesh, accretive (the true path dissipative) and
  integrable, with their propagator `U` (`IsMeshPropagator`), and a nonzero final vector
  `x(T)` with `B ≤ ḡ ‖x(T)‖`, `B = ‖x₀‖ + ∫ ‖b‖` (`meshScale`);
* the source certificate of eq. `ode:eq:gate-source-certificates`:
  `‖x(T) - U(T, 0) x₀ - ∑_r (T/M) U(T, t_r) b_r‖ ≤ ζ B` and `B_m ≤ c_q B` (`c_q = 2` in the
  manuscript), with `c_q ḡ ≤ g` for the public amplification bound `g` of the solver;
* the sample certificate for the same uniform mesh: the integrated sample error
  `ΔG = ∑_r ∫ ‖G_r - G̃_r‖` and its dissipative part `ΔD` with `ζ + c_q (ΔG + 2 ΔD) ≤ ε / (2000 ḡ)`
  and the branch budget `6 R ΔD ≤ ν'` (`ν'` the precision `TParams.nu` of the solver's private
  simulation; `R ΔD` bounds the dissipative part of the integrated branch sample error in the
  manuscript's branch certificate, after eq. `ode:eq:timedisc` in the proof of `ode:thm:time`).

The analysis runs on the positive repairs `repair L_r κ_r` of the dissipative samples with the
path negativity bounds `κ_r = pathκ` (whose negativity mass is `ΔD`); the circuits keep the
represented samples.

* `branchU_sub_le'`: the represented and repaired branch evolutions differ by at most
  `R ∑_r (T/M) c_r` for slot-dependent differences `c_r`;
* `cert_target_facts'`: the repaired target is nonzero, `B_m ≤ 2 g ‖y'‖` and its direction is
  within `ε / 1000` of that of `x(T)`;
* `cert_prep_certificate`: the actual preparation satisfies the released actual-source certificate
  for the repaired target.
-/

set_option autoImplicit false

namespace SparseHamiltonian.MeshCertificateODE

noncomputable section
open ContinuousLinearMap Set MeasureTheory OracleCircuit GateCircuit
open TimeDependentExtensions
open SparseHamiltonian.TimeDependentODE (Accretive)
open SparseHamiltonian.GeneralSourceExtensions.Mesh (IsMeshPropagator meshScale meshScale_nonneg)
open SparseHamiltonian.GateODE.Time (TParams TOracles gens trun trun_isUnitary)
open SparseHamiltonian.TimeDependentODE.GaussianLCHS (productFamily)
open GatePointerEncoding (wordValue)
open ODEStateNormalization (unitDirection)
open scoped InnerProduct BigOperators

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-! ### The instance conditions -/

/-- **The instance conditions of the time-dependent gate solver under the manuscript's
certificates.** See the module docstring. -/
structure CertInstanceOK (p : TParams) (v : P) (σ : TOracles p.a p.m p.l P)
    (Hs Ls : ℕ → P →L[ℂ] P) (G : Fin p.M → ℝ → P →L[ℂ] P) (bf : Fin p.M → ℝ → P)
    (sol : ℝ → P) (U : ℝ → P → ℝ → P) (bs : ℕ → P) (gb cq ζ : ℝ) : Prop where
  select : p.SelectHypT σ Hs Ls
  load_unitary : ∀ s, IsUnitary (σ.J s)
  prep_left : σ.Wp.conjTranspose * σ.Wp = 1
  prep_right : σ.Wp * σ.Wp.conjTranspose = 1
  prep : p.WpPromise σ (sol 0) bs
  init_load : sol 0 ≠ 0 → σ.J (false, fun _ => false) v = unitDirection (sol 0)
  forcing_load : ∀ w : Fin p.m → Bool, bs (wordValue w) ≠ 0 →
    σ.J (true, w) v = unitDirection (bs (wordValue w))
  accretive : ∀ r : Fin p.M, ∀ u ∈ Icc (umesh p.T p.M r) (umesh p.T p.M ((r : ℕ) + 1)),
    Accretive (G r u)
  regular : RepresentedSampleODE.RegularPieces (umesh p.T p.M) G
  propagator : IsMeshPropagator G (umesh p.T p.M) p.T U
  target_ne : sol p.T ≠ 0
  gb_pos : 0 < gb
  cq_nonneg : 0 ≤ cq
  scale : meshScale sol bf (umesh p.T p.M) ≤ gb * ‖sol p.T‖
  mass : p.mass (sol 0) bs ≤ cq * meshScale sol bf (umesh p.T p.M)
  ratio : cq * gb ≤ p.g
  source : ‖sol p.T - quadSum p.T p.M U (sol 0) bs‖ ≤ ζ * meshScale sol bf (umesh p.T p.M)
  budget : ζ + cq * (sampleErr (umesh p.T p.M) G (fun r => gens Hs Ls r) +
    2 * dissErr (umesh p.T p.M) G (fun r => gens Hs Ls r)) ≤ p.ε / (2000 * gb)
  branch : 6 * p.R * dissErr (umesh p.T p.M) G (fun r => gens Hs Ls r) ≤ p.nu

theorem CertInstanceOK.unitary {p : TParams} {v : P} {σ : TOracles p.a p.m p.l P}
    {Hs Ls : ℕ → P →L[ℂ] P} {G : Fin p.M → ℝ → P →L[ℂ] P} {bf : Fin p.M → ℝ → P}
    {sol : ℝ → P} {U : ℝ → P → ℝ → P} {bs : ℕ → P} {gb cq ζ : ℝ}
    (hI : CertInstanceOK p v σ Hs Ls G bf sol U bs gb cq ζ) : σ.Unitary p.m :=
  ⟨hI.select.uj, hI.select.priv, hI.load_unitary, hI.prep_left, hI.prep_right⟩

/-! ### The repaired samples of an instance -/

/-- The negativity bounds of the represented dissipative samples of an instance. -/
theorem CertInstanceOK.neg {p : TParams} {v : P} {σ : TOracles p.a p.m p.l P}
    {Hs Ls : ℕ → P →L[ℂ] P} {G : Fin p.M → ℝ → P →L[ℂ] P} {bf : Fin p.M → ℝ → P}
    {sol : ℝ → P} {U : ℝ → P → ℝ → P} {bs : ℕ → P} {gb cq ζ : ℝ}
    (hI : CertInstanceOK p v σ Hs Ls G bf sol U bs gb cq ζ) :
    ∀ r < p.M, ∀ w : P, -pathκ p.T G Hs Ls r * ‖w‖ ^ 2 ≤ (inner ℂ w (Ls r w)).re :=
  fun _ hr w => pathκ_bound G Hs Ls hI.select.selfH hI.accretive hI.regular hr w

/-- **The facts on the repaired samples of an instance**: self-adjoint, positive semidefinite, no
larger than `λ_D`, within `2 κ_r` of the samples. -/
theorem CertInstanceOK.repaired {p : TParams} {v : P} {σ : TOracles p.a p.m p.l P}
    {Hs Ls : ℕ → P →L[ℂ] P} {G : Fin p.M → ℝ → P →L[ℂ] P} {bf : Fin p.M → ℝ → P}
    {sol : ℝ → P} {U : ℝ → P → ℝ → P} {bs : ℕ → P} {gb cq ζ : ℝ}
    (hI : CertInstanceOK p v σ Hs Ls G bf sol U bs gb cq ζ) (hT : 0 ≤ p.T) :
    (∀ r < p.M, star (repLs Ls (pathκ p.T G Hs Ls) r) = repLs Ls (pathκ p.T G Hs Ls) r) ∧
    (∀ r < p.M, ∀ w : P, 0 ≤ (inner ℂ w (repLs Ls (pathκ p.T G Hs Ls) r w)).re) ∧
    (∀ r < p.M, ‖repLs Ls (pathκ p.T G Hs Ls) r‖ ≤ p.lamD) ∧
    (∀ r < p.M, ‖Ls r - repLs Ls (pathκ p.T G Hs Ls) r‖ ≤ 2 * pathκ p.T G Hs Ls r) :=
  repLs_facts p Ls _ (pathκ_nonneg hT p.M_pos G Hs Ls) hI.select.selfL hI.select.normL hI.neg

/-! ### The repaired target -/

/-- **The repaired target** retains half of the solution norm (`B_m ≤ 2 g ‖y'‖`) and has the
solution's direction up to `ε / 1000`. -/
theorem cert_target_facts' {p : TParams} (hp : p.PublicOK) {v : P} {σ : TOracles p.a p.m p.l P}
    {Hs Ls : ℕ → P →L[ℂ] P} {G : Fin p.M → ℝ → P →L[ℂ] P} {bf : Fin p.M → ℝ → P}
    {sol : ℝ → P} {U : ℝ → P → ℝ → P} {bs : ℕ → P} {gb cq ζ : ℝ}
    (hI : CertInstanceOK p v σ Hs Ls G bf sol U bs gb cq ζ) :
    p.target Hs (repLs Ls (pathκ p.T G Hs Ls)) (sol 0) bs ≠ 0 ∧
      p.mass (sol 0) bs ≤ 2 * p.g * ‖p.target Hs (repLs Ls (pathκ p.T G Hs Ls)) (sol 0) bs‖ ∧
      ‖unitDirection (p.target Hs (repLs Ls (pathκ p.T G Hs Ls)) (sol 0) bs) -
        unitDirection (sol p.T)‖ ≤ p.ε / 1000 := by
  have hT := hp.T_pos.le
  have hmesh := isMesh_umesh hT p.M_pos
  obtain ⟨-, hpsd', -, hdiff⟩ := hI.repaired hT
  set Ls' := repLs Ls (pathκ p.T G Hs Ls) with hLs'
  have hacc' : ∀ r < p.M, Accretive (gens Hs Ls' r) := fun r hr =>
    GateODE.Time.slot_accretive _ _ (hI.select.selfH r hr) (hpsd' r hr)
  have herr := quad_target_error p hT Hs Ls' hacc' G hI.accretive hI.regular U hI.propagator
    (sol 0) bs
  have hrep := sampleErr_repLs_le hT p.M_pos Hs Ls (pathκ p.T G Hs Ls) hdiff G hI.regular
  rw [negativity_pathκ hT p.M_pos G Hs Ls] at hrep
  have hK0 : 0 ≤ sampleErr (umesh p.T p.M) G (fun r => gens Hs Ls' r) :=
    sampleErr_nonneg hmesh G _
  have hbud : ζ + cq * sampleErr (umesh p.T p.M) G (fun r => gens Hs Ls' r) ≤
      p.ε / (2000 * gb) := by
    have := mul_le_mul_of_nonneg_left hrep hI.cq_nonneg
    linarith [hI.budget]
  exact cert_target_facts (sol p.T) (quadSum p.T p.M U (sol 0) bs) _ hp.g_ge hp.ε_pos
    hp.eps_le_one hI.target_ne (meshScale_nonneg hmesh sol bf) hI.gb_pos hI.cq_nonneg hK0
    hI.source herr hI.mass hI.scale hI.ratio hbud

/-! ### The branch comparison -/

/-- **The represented and repaired branch evolutions** differ by at most `R ∑_r (T/M) c_r` at every
public node if the dissipative samples differ by at most `c_r` on slot `r`. -/
theorem branchU_sub_le' {p : TParams} (hT : 0 ≤ p.T) (hg : 1 ≤ p.g) (hε : 0 < p.ε)
    (hεOne : p.ε ≤ 1) (hTD : 0 ≤ p.T * p.lamD) (Hs Ls Ls' : ℕ → P →L[ℂ] P)
    (hH : ∀ r < p.M, star (Hs r) = Hs r) (hL : ∀ r < p.M, star (Ls r) = Ls r)
    (hL' : ∀ r < p.M, star (Ls' r) = Ls' r) (c : ℕ → ℝ)
    (hc : ∀ r < p.M, ‖Ls r - Ls' r‖ ≤ c r) (s : Bool × (Fin p.m → Bool)) (w : Fin p.l → Bool) :
    ‖p.branchU Hs Ls s w - p.branchU Hs Ls' s w‖ ≤
      p.R * ∑ r ∈ Finset.range p.M, p.T / p.M * c r := by
  have hcl := GateCircuit.SlotSim.min_pred_lt p.M_pos
  rw [← p.family_ofReal Hs Ls s w, ← p.family_ofReal Hs Ls' s w]
  show ‖productFamily (GateCircuit.SlotSim.clampAt p.M Hs) (GateCircuit.SlotSim.clampAt p.M Ls)
      (p.dur s) p.M (p.nodeW w : ℂ) - productFamily (GateCircuit.SlotSim.clampAt p.M Hs)
      (GateCircuit.SlotSim.clampAt p.M Ls') (p.dur s) p.M (p.nodeW w : ℂ)‖ ≤ _
  have h := RepresentedSampleODE.productFamily_sub_le (GateCircuit.SlotSim.clampAt p.M Hs)
    (GateCircuit.SlotSim.clampAt p.M Ls) (GateCircuit.SlotSim.clampAt p.M Ls') (p.dur s) p.M
    (fun r => hH _ (hcl r)) (fun r => hL _ (hcl r)) (fun r => hL' _ (hcl r))
    (fun r => p.dur_nonneg hT s r) (p.nodeW w)
  refine h.trans ?_
  have hR : 0 ≤ p.R := ImprovedODEQueryBudget.radius_nonneg p.ratio p.acc (p.ratio_ge hg)
    (p.acc_pos hε) (p.acc_le_one hεOne)
  have hk := p.nodeW_abs_le hg hε hεOne hTD w
  have hsum : ∑ r ∈ Finset.range p.M, p.dur s r *
      ‖GateCircuit.SlotSim.clampAt p.M Ls r - GateCircuit.SlotSim.clampAt p.M Ls' r‖ ≤
      ∑ r ∈ Finset.range p.M, p.T / p.M * c r := by
    refine Finset.sum_le_sum fun r hr => ?_
    have hr' := Finset.mem_range.mp hr
    rw [GateCircuit.SlotSim.clampAt_of_lt p.M Ls hr', GateCircuit.SlotSim.clampAt_of_lt p.M Ls' hr']
    exact mul_le_mul (p.dur_le hT s r) (hc r hr') (norm_nonneg _)
      (div_nonneg hT (Nat.cast_nonneg _))
  have hs0 : 0 ≤ ∑ r ∈ Finset.range p.M, p.dur s r *
      ‖GateCircuit.SlotSim.clampAt p.M Ls r - GateCircuit.SlotSim.clampAt p.M Ls' r‖ :=
    Finset.sum_nonneg fun r _ => mul_nonneg (p.dur_nonneg hT s r) (norm_nonneg _)
  exact mul_le_mul hk hsum hs0 hR

/-- The slot sum of `(T/M) κ_r` is the negativity mass on the uniform mesh. -/
theorem sum_range_negativity (p : TParams) (κ : ℕ → ℝ) :
    ∑ r ∈ Finset.range p.M, p.T / p.M * κ r =
      RepresentedSampleODE.negativity (umesh p.T p.M) (fun r : Fin p.M => κ r) := by
  unfold RepresentedSampleODE.negativity
  rw [← Fin.sum_univ_eq_sum_range (fun r => p.T / p.M * κ r) p.M]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [umesh_succ_sub]

/-! ### The certificate -/

/-- **The actual preparation satisfies the released actual-source certificate for the repaired
target** under the manuscript's certificates (represented samples of any sign). -/
theorem cert_prep_certificate {p : TParams} (hp : p.PublicOK) (v : P) (hv : ‖v‖ = 1)
    (σ : TOracles p.a p.m p.l P) (Hs Ls : ℕ → P →L[ℂ] P) (G : Fin p.M → ℝ → P →L[ℂ] P)
    (bf : Fin p.M → ℝ → P) (sol : ℝ → P) (U : ℝ → P → ℝ → P) (bs : ℕ → P) (gb cq ζ : ℝ)
    (hI : CertInstanceOK p v σ Hs Ls G bf sol U bs gb cq ζ) :
    ODEActualSourceError.Certificate p.branchE (p.zsrc (sol 0) bs) p.coeffW σ.J
      (trun v σ p.select) v (p.target Hs (repLs Ls (pathκ p.T G Hs Ls)) (sol 0) bs) p.ratio
      p.acc := by
  have hT := hp.T_pos.le
  have hS := hI.select
  have hU := hI.unitary
  obtain ⟨hself', hpsd', hnorm', hdiff⟩ := hI.repaired hT
  set κ := pathκ p.T G Hs Ls with hκ
  set Ls' : ℕ → P →L[ℂ] P := repLs Ls κ with hLs'
  have hsel : IsUnitary (trun v σ p.select) :=
    trun_isUnitary v σ hU hv _ (fun g hg =>
      p.prepC_valid hp.tau_pos.le hp.nu_pos hp.mesh g (by simp [TParams.prepC, hg]))
  have hJ : ∀ s, (σ.J s)† ∘L σ.J s = 1 := by
    intro s
    have h := (hI.load_unitary s).1
    rwa [star_eq_adjoint, mul_def] at h
  have hM : 0 < p.T / p.M := div_pos hp.T_pos (by exact_mod_cast p.M_pos)
  have hPrep : ∀ s, p.zsrc (sol 0) bs s ≠ 0 →
      σ.J s v = unitDirection (p.zsrc (sol 0) bs s) := by
    intro s hs
    obtain ⟨c, w⟩ := s
    cases c
    · by_cases hw : w = (fun _ => false)
      · subst hw
        have hx : sol 0 ≠ 0 := by
          intro h0
          apply hs
          simp [TParams.zsrc, h0]
        simp only [TParams.zsrc, Bool.false_eq_true, if_false, if_true]
        exact hI.init_load hx
      · exfalso
        apply hs
        simp [TParams.zsrc, hw]
    · have hb : bs (wordValue w) ≠ 0 := by
        intro h0
        apply hs
        simp [TParams.zsrc, h0]
      simp only [TParams.zsrc, if_true]
      rw [hI.forcing_load w hb, Complex.coe_smul, ODEHeraldedSuccess.unitDirection_pos_smul _ hM]
  obtain ⟨hy, hbud, _⟩ := cert_target_facts' hp hI
  have hNorm := p.target_norm_le hT Hs Ls' hS.selfH hpsd' (sol 0) bs
  have hSim := p.select_error hT hp.tau_pos hp.g_ge hp.ε_pos hp.eps_le_one hp.TD_nonneg hp.Q_ge
    hp.qbar_nonneg hp.qbar_le hp.mesh v σ Hs Ls hS
  let Bsum : Bool × (Fin p.m → Bool) → P →L[ℂ] P := fun s =>
    ∑ w, p.coeffW w • p.branchU Hs Ls s w
  let Rsum : Bool × (Fin p.m → Bool) → P →L[ℂ] P := fun s =>
    ∑ w, p.coeffW w • p.branchU Hs Ls' s w
  let Sx : Bool × (Fin p.m → Bool) → P →L[ℂ] P := fun s =>
    Bsum s - (Rsum s - p.propS Hs Ls' s)
  have hLCHS : ∀ s, ‖(∑ w, p.coeffW w • p.branchU Hs Ls s w) - Sx s‖ ≤ 2 * p.nu := by
    intro s
    have e : (∑ w, p.coeffW w • p.branchU Hs Ls s w) - Sx s = Rsum s - p.propS Hs Ls' s := by
      simp only [Sx, Bsum]
      abel
    rw [e]
    exact p.lchs_error hT hp.g_ge hp.ε_pos hp.eps_le_one hp.lamD_nonneg Hs Ls' hS.selfH hself'
      hnorm' hpsd' s
  have hBR : ∀ s, ‖Bsum s - Rsum s‖ ≤ p.nu := by
    intro s
    have hbr := branchU_sub_le' hT hp.g_ge hp.ε_pos hp.eps_le_one hp.TD_nonneg Hs Ls Ls' hS.selfH
      hS.selfL hself' (fun r => 2 * κ r) hdiff s
    have h3 := RepresentedSampleODE.GateTime.branch_sum_sub_le hp.g_ge hp.ε_pos hp.eps_le_one
      hp.TD_nonneg Hs Ls Ls' s hbr
    have hmass : ∑ r ∈ Finset.range p.M, p.T / p.M * (2 * κ r) =
        2 * dissErr (umesh p.T p.M) G (fun r => gens Hs Ls r) := by
      have e : ∑ r ∈ Finset.range p.M, p.T / p.M * (2 * κ r) =
          2 * ∑ r ∈ Finset.range p.M, p.T / p.M * κ r := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun r _ => ?_
        ring
      rw [e, sum_range_negativity, hκ, negativity_pathκ hT p.M_pos G Hs Ls]
    rw [hmass] at h3
    have hB := hI.branch
    calc ‖Bsum s - Rsum s‖ ≤ 3 * (p.R * (2 * dissErr (umesh p.T p.M) G
          (fun r => gens Hs Ls r))) := h3
      _ = 6 * p.R * dissErr (umesh p.T p.M) G (fun r => gens Hs Ls r) := by ring
      _ ≤ p.nu := hB
  have hQuad : ‖(∑ s, Sx s (p.zsrc (sol 0) bs s)) - p.target Hs Ls' (sol 0) bs‖ ≤
      ImprovedODEQueryBudget.precision p.ratio p.acc *
        ODESourceBranches.mass (p.zsrc (sol 0) bs) := by
    have e : (∑ s, Sx s (p.zsrc (sol 0) bs s)) - p.target Hs Ls' (sol 0) bs =
        ∑ s, (Bsum s - Rsum s) (p.zsrc (sol 0) bs s) := by
      rw [← p.source_sum Hs Ls' (sol 0) bs, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun s _ => ?_
      simp only [Sx, sub_apply]
      abel
    rw [e, ODESourceBranches.mass, Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun s _ => ?_)
    exact (le_opNorm _ _).trans (mul_le_mul_of_nonneg_right (hBR s) (norm_nonneg _))
  have hmass := p.coeffW_mass hp.g_ge hp.ε_pos hp.eps_le_one hp.TD_nonneg
  have hacc : p.acc ≤ 1 / 2 := by
    have := hp.ε_half
    unfold TParams.acc
    linarith
  exact ODEActualSourceError.actual_source_certificate (σ := Bool × (Fin p.m → Bool))
    (ι := Fin p.l → Bool) (P := P) (K := Reg p.W P) p.branchE p.branchE_isometry
    (p.zsrc (sol 0) bs) p.coeffW hmass σ.J hJ v hv hPrep (trun v σ p.select) hsel
    (p.branchU Hs Ls) Sx (p.target Hs Ls' (sol 0) bs) p.ratio p.acc hy
    (p.ratio_ge hp.g_ge) (p.acc_pos hp.ε_pos) hacc hNorm hbud (by convert hSim using 4) hLCHS hQuad

end

end SparseHamiltonian.MeshCertificateODE
