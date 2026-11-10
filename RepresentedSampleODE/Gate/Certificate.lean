import GateEfficientODE.Time.Certificate
import RepresentedSampleODE.Repair

/-!
# The time-dependent gate solver with represented samples of any sign: the certificate

The released time-dependent gate solver (`GateODE.Time`) asks of the represented slot samples
`G̃_r = L_r + i H_r` that `L_r ⪰ 0` (`InstanceOK.psd`). On the uniform mesh the generator path is
accretive and within `δ_G` of the samples at the slot times (`sampleG`), so the samples satisfy
the negativity bound `Re ⟨w, L_r w⟩ ≥ -δ_G ‖w‖²` (`negativity_of_sample`). The analysis then runs
on the positive repairs `L'_r = repair L_r δ_G` (`RepresentedSampleODE.repair`), and the circuits
keep the represented samples:

* the repaired samples are self-adjoint, positive semidefinite, no larger in norm than `L_r` and
  within `2 δ_G` of `L_r`, so the repaired generators are within `3 δ_G` of the path at the slot
  times (`repaired_facts`, `RobustInstanceOK.repaired`);
* the discretised target `y'` of the repaired generators retains half of the solution norm and
  has its direction up to `ε / 1000` under the discretisation budget at `3 δ_G`
  (`robust_target_facts`);
* at every public node `|k| ≤ R` the represented and repaired branch evolutions differ by at
  most `2 R T δ_G` (`branchU_sub_le`), so their coefficient-weighted sums differ by at most
  `6 R T δ_G ≤ ν` (`branch_sum_sub_le`; the coefficient mass is three);
* the actual preparation satisfies the released actual-source certificate for `y'`
  (`robust_prep_certificate`): the per-label targets are the represented branch sums corrected by
  the error of the Gaussian table on the repaired family, and the quadrature step absorbs the
  branch difference.

`RobustInstanceOK` collects the conditions: those of the released `InstanceOK` without `psd`,
with the discretisation budget at `3 δ_G` and the branch budget `6 R T δ_G ≤ ν`. The branch budget
bounds the dissipative part `|k| ∑_r h_r ‖L_r - D(t_r)‖ ≤ R T δ_G` of the represented-sample
contribution `∑_r h_r ‖K̃_{k,r} - K_k(t_r)‖`, `|k| ≤ R`, to the manuscript's branch certificate
(proof of `ode:thm:time`: the definition of `K_k` and the sentence after eq. `ode:eq:timedisc`).
-/

set_option autoImplicit false

namespace SparseHamiltonian.RepresentedSampleODE.GateTime

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit
open GatePointerEncoding (wordValue)
open SparseHamiltonian.GateODE.Time (TParams TOracles gens trun trun_isUnitary)
open SparseHamiltonian.TimeDependentODE.GaussianLCHS (productFamily)
open ODEStateNormalization (unitDirection)
open scoped InnerProduct BigOperators

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-! ### The instance conditions -/

/-- **The instance conditions with represented samples of any sign**: those of the released
`GateODE.Time.TParams.InstanceOK` without the positivity `psd` of the represented dissipative
samples, with the discretisation budget at the sample error `3 δ_G` and the branch budget
`6 R T δ_G ≤ ν`. -/
structure RobustInstanceOK (p : TParams) (v : P) (σ : TOracles p.a p.m p.l P)
    (Hs Ls : ℕ → P →L[ℂ] P) (G : ℝ → P →L[ℂ] P) (b x : ℝ → P) (bs : ℕ → P)
    (βG δG βb δb bmax : ℝ) : Prop where
  select : p.SelectHypT σ Hs Ls
  load_unitary : ∀ s, IsUnitary (σ.J s)
  prep_left : σ.Wp.conjTranspose * σ.Wp = 1
  prep_right : σ.Wp * σ.Wp.conjTranspose = 1
  prep : p.WpPromise σ (x 0) bs
  init_load : x 0 ≠ 0 → σ.J (false, fun _ => false) v = unitDirection (x 0)
  forcing_load : ∀ w : Fin p.m → Bool, bs (wordValue w) ≠ 0 →
    σ.J (true, w) v = unitDirection (bs (wordValue w))
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
  disc : p.discretisation βG (3 * δG) βb δb bmax ‖x 0‖ ≤ p.ε * p.mass (x 0) bs / (2000 * p.g)
  branch : 6 * p.R * p.T * δG ≤ p.nu

/-- The released instance conditions with the two budgets give the robust ones. -/
theorem RobustInstanceOK.of_released {p : TParams} {v : P} {σ : TOracles p.a p.m p.l P}
    {Hs Ls : ℕ → P →L[ℂ] P} {G : ℝ → P →L[ℂ] P} {b x : ℝ → P} {bs : ℕ → P}
    {βG δG βb δb bmax : ℝ} (hI : p.InstanceOK v σ Hs Ls G b x bs βG δG βb δb bmax)
    (hdisc : p.discretisation βG (3 * δG) βb δb bmax ‖x 0‖ ≤
      p.ε * p.mass (x 0) bs / (2000 * p.g))
    (hbranch : 6 * p.R * p.T * δG ≤ p.nu) :
    RobustInstanceOK p v σ Hs Ls G b x bs βG δG βb δb bmax :=
  ⟨hI.select, hI.load_unitary, hI.prep_left, hI.prep_right, hI.prep, hI.init_load,
    hI.forcing_load, hI.solves, hI.accretive, hI.lipG, hI.sampleG, hI.lipb, hI.sampleb, hI.boundb,
    hI.βG_nonneg, hI.βb_nonneg, hI.target_ne, hI.budget, hdisc, hbranch⟩

theorem RobustInstanceOK.unitary {p : TParams} {v : P} {σ : TOracles p.a p.m p.l P}
    {Hs Ls : ℕ → P →L[ℂ] P} {G : ℝ → P →L[ℂ] P} {b x : ℝ → P} {bs : ℕ → P}
    {βG δG βb δb bmax : ℝ} (hI : RobustInstanceOK p v σ Hs Ls G b x bs βG δG βb δb bmax) :
    σ.Unitary p.m :=
  ⟨hI.select.uj, hI.select.priv, hI.load_unitary, hI.prep_left, hI.prep_right⟩

/-! ### The negativity bound and the repaired samples -/

/-- The slot times lie in `[0, T]`. -/
theorem slot_mem {p : TParams} (hT : 0 ≤ p.T) {r : ℕ} (hr : r < p.M) :
    ((r : ℝ) * p.T / p.M) ∈ Set.Icc 0 p.T := by
  have hMR : (0 : ℝ) < p.M := by exact_mod_cast p.M_pos
  have hrM : (r : ℝ) ≤ p.M := by exact_mod_cast hr.le
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ hMR]
  nlinarith

/-- The quadratic form of a slot generator `L + i H` is that of `L`. -/
theorem re_inner_gens (Hs Ls : ℕ → P →L[ℂ] P) (r : ℕ) (hH : star (Hs r) = Hs r) (w : P) :
    (inner ℂ w (gens Hs Ls r w)).re = (inner ℂ w (Ls r w)).re := by
  have him := ODEComplexFrequency.inner_im_eq_zero (Hs r) hH w
  show (inner ℂ w ((Ls r + Complex.I • Hs r) w)).re = _
  rw [add_apply, smul_apply, inner_add_right, inner_smul_right, Complex.add_re,
    Complex.mul_re, Complex.I_re, Complex.I_im, him]
  simp

/-- **The negativity bound of the represented samples**: a sample within `δ_G` of an accretive
generator has `Re ⟨w, L_r w⟩ ≥ -δ_G ‖w‖²`. -/
theorem negativity_of_sample {p : TParams} (hT : 0 ≤ p.T) (Hs Ls : ℕ → P →L[ℂ] P)
    (G : ℝ → P →L[ℂ] P) (δG : ℝ) (hH : ∀ r < p.M, star (Hs r) = Hs r)
    (hacc : ∀ u ∈ Set.Icc 0 p.T, TimeDependentODE.Accretive (G u))
    (hs : ∀ r < p.M, ‖G (r * p.T / p.M) - gens Hs Ls r‖ ≤ δG) {r : ℕ} (hr : r < p.M) (w : P) :
    -δG * ‖w‖ ^ 2 ≤ (inner ℂ w (Ls r w)).re := by
  have h0 := hacc _ (slot_mem hT hr) w
  rw [← re_inner_gens Hs Ls r (hH r hr) w]
  set A := G (r * p.T / p.M) - gens Hs Ls r with hA
  have e : (inner ℂ w (gens Hs Ls r w)).re =
      (inner ℂ w (G (r * p.T / p.M) w)).re - (inner ℂ w (A w)).re := by
    rw [hA, sub_apply, inner_sub_right, Complex.sub_re]
    ring
  have hb : (inner ℂ w (A w)).re ≤ δG * ‖w‖ ^ 2 := by
    calc (inner ℂ w (A w)).re ≤ ‖inner ℂ w (A w)‖ := Complex.re_le_norm _
      _ ≤ ‖w‖ * ‖A w‖ := norm_inner_le_norm _ _
      _ ≤ ‖w‖ * (‖A‖ * ‖w‖) := mul_le_mul_of_nonneg_left (le_opNorm _ _) (norm_nonneg _)
      _ ≤ ‖w‖ * (δG * ‖w‖) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hs r hr) (norm_nonneg _))
            (norm_nonneg _)
      _ = δG * ‖w‖ ^ 2 := by ring
  rw [e]
  linarith

/-- The repaired dissipative samples `repair L_r κ`. -/
def repairedLs (Ls : ℕ → P →L[ℂ] P) (κ : ℝ) (r : ℕ) : P →L[ℂ] P := repair (Ls r) κ

/-- The facts on the repaired samples used by the analysis: on every slot they are self-adjoint,
positive semidefinite and no larger than `λ_D`, and the repaired generators are within `3 δ_G` of
the path at the slot times. -/
theorem repaired_facts {p : TParams} (hT : 0 ≤ p.T) (Hs Ls : ℕ → P →L[ℂ] P)
    (G : ℝ → P →L[ℂ] P) (δG : ℝ) (hδ : 0 ≤ δG) (hH : ∀ r < p.M, star (Hs r) = Hs r)
    (hL : ∀ r < p.M, star (Ls r) = Ls r) (hLn : ∀ r < p.M, ‖Ls r‖ ≤ p.lamD)
    (hacc : ∀ u ∈ Set.Icc 0 p.T, TimeDependentODE.Accretive (G u))
    (hs : ∀ r < p.M, ‖G (r * p.T / p.M) - gens Hs Ls r‖ ≤ δG) :
    (∀ r < p.M, star (repairedLs Ls δG r) = repairedLs Ls δG r) ∧
    (∀ r < p.M, ∀ w : P, 0 ≤ (inner ℂ w (repairedLs Ls δG r w)).re) ∧
    (∀ r < p.M, ‖repairedLs Ls δG r‖ ≤ p.lamD) ∧
    (∀ r < p.M, ‖Ls r - repairedLs Ls δG r‖ ≤ 2 * δG) ∧
    (∀ r < p.M, ‖G (r * p.T / p.M) - gens Hs (repairedLs Ls δG) r‖ ≤ 3 * δG) := by
  have hdiff : ∀ r < p.M, ‖Ls r - repairedLs Ls δG r‖ ≤ 2 * δG := fun r _ => by
    rw [norm_sub_rev]
    exact norm_repair_sub_le (Ls r) hδ
  refine ⟨fun r hr => repair_selfAdjoint (Ls r) (hL r hr) δG,
    fun r hr w => repair_nonneg (Ls r) hδ
      (negativity_of_sample hT Hs Ls G δG hH hacc hs hr) w,
    fun r hr => (norm_repair_le (Ls r) hδ).trans (hLn r hr), hdiff, fun r hr => ?_⟩
  have e : G (r * p.T / p.M) - gens Hs (repairedLs Ls δG) r =
      (G (r * p.T / p.M) - gens Hs Ls r) + (Ls r - repairedLs Ls δG r) := by
    simp only [gens]
    abel
  rw [e]
  calc _ ≤ ‖G (r * p.T / p.M) - gens Hs Ls r‖ + ‖Ls r - repairedLs Ls δG r‖ := norm_add_le _ _
    _ ≤ δG + 2 * δG := add_le_add (hs r hr) (hdiff r hr)
    _ = 3 * δG := by ring

theorem RobustInstanceOK.δG_nonneg {p : TParams} {v : P} {σ : TOracles p.a p.m p.l P}
    {Hs Ls : ℕ → P →L[ℂ] P} {G : ℝ → P →L[ℂ] P} {b x : ℝ → P} {bs : ℕ → P}
    {βG δG βb δb bmax : ℝ} (hI : RobustInstanceOK p v σ Hs Ls G b x bs βG δG βb δb bmax) :
    0 ≤ δG :=
  (norm_nonneg _).trans (hI.sampleG 0 p.M_pos)

/-- The facts on the repaired samples of an instance. -/
theorem RobustInstanceOK.repaired {p : TParams} {v : P} {σ : TOracles p.a p.m p.l P}
    {Hs Ls : ℕ → P →L[ℂ] P} {G : ℝ → P →L[ℂ] P} {b x : ℝ → P} {bs : ℕ → P}
    {βG δG βb δb bmax : ℝ} (hI : RobustInstanceOK p v σ Hs Ls G b x bs βG δG βb δb bmax)
    (hT : 0 ≤ p.T) :
    (∀ r < p.M, star (repairedLs Ls δG r) = repairedLs Ls δG r) ∧
    (∀ r < p.M, ∀ w : P, 0 ≤ (inner ℂ w (repairedLs Ls δG r w)).re) ∧
    (∀ r < p.M, ‖repairedLs Ls δG r‖ ≤ p.lamD) ∧
    (∀ r < p.M, ‖Ls r - repairedLs Ls δG r‖ ≤ 2 * δG) ∧
    (∀ r < p.M, ‖G (r * p.T / p.M) - gens Hs (repairedLs Ls δG) r‖ ≤ 3 * δG) :=
  repaired_facts hT Hs Ls G δG hI.δG_nonneg hI.select.selfH hI.select.selfL hI.select.normL
    hI.accretive hI.sampleG

/-! ### The repaired target -/

/-- **The repaired discretised target** retains half of the solution norm and has the solution's
direction up to `ε / 1000`. -/
theorem robust_target_facts {p : TParams} (hp : p.PublicOK) {v : P} {σ : TOracles p.a p.m p.l P}
    {Hs Ls : ℕ → P →L[ℂ] P} {G : ℝ → P →L[ℂ] P} {b x : ℝ → P} {bs : ℕ → P}
    {βG δG βb δb bmax : ℝ} (hI : RobustInstanceOK p v σ Hs Ls G b x bs βG δG βb δb bmax) :
    p.target Hs (repairedLs Ls δG) (x 0) bs ≠ 0 ∧
      p.mass (x 0) bs ≤ 2 * p.g * ‖p.target Hs (repairedLs Ls δG) (x 0) bs‖ ∧
      ‖unitDirection (p.target Hs (repairedLs Ls δG) (x 0) bs) - unitDirection (x p.T)‖ ≤
        p.ε / 1000 := by
  obtain ⟨-, hpsd, hnorm, -, hsample⟩ := hI.repaired hp.T_pos.le
  have hErr := p.discretisation_error hp.T_pos.le G b x Hs (repairedLs Ls δG) bs βG (3 * δG) βb
    δb bmax hI.βG_nonneg hI.βb_nonneg hI.solves hI.accretive hI.lipG hsample hI.lipb hI.sampleb
    hI.boundb hI.select.selfH hpsd hI.select.normH hnorm
  exact TimeDependentODE.Sampling.target_budget (x p.T) (p.target Hs (repairedLs Ls δG) (x 0) bs)
    (p.mass (x 0) bs) p.g p.ε _ hp.g_ge hp.ε_pos hp.eps_le_one hI.target_ne hI.budget hErr hI.disc

/-! ### The branch comparison -/

/-- **The represented and repaired branch evolutions** differ by at most `R T c` at every public
node if the dissipative samples differ by at most `c` on every slot. -/
theorem branchU_sub_le {p : TParams} (hT : 0 ≤ p.T) (hg : 1 ≤ p.g) (hε : 0 < p.ε)
    (hεOne : p.ε ≤ 1) (hTD : 0 ≤ p.T * p.lamD) (Hs Ls Ls' : ℕ → P →L[ℂ] P)
    (hH : ∀ r < p.M, star (Hs r) = Hs r) (hL : ∀ r < p.M, star (Ls r) = Ls r)
    (hL' : ∀ r < p.M, star (Ls' r) = Ls' r) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ r < p.M, ‖Ls r - Ls' r‖ ≤ c) (s : Bool × (Fin p.m → Bool)) (w : Fin p.l → Bool) :
    ‖p.branchU Hs Ls s w - p.branchU Hs Ls' s w‖ ≤ p.R * (p.T * c) := by
  have hcl := SlotSim.min_pred_lt p.M_pos
  rw [← p.family_ofReal Hs Ls s w, ← p.family_ofReal Hs Ls' s w]
  show ‖productFamily (SlotSim.clampAt p.M Hs) (SlotSim.clampAt p.M Ls) (p.dur s) p.M
      (p.nodeW w : ℂ) - productFamily (SlotSim.clampAt p.M Hs) (SlotSim.clampAt p.M Ls')
      (p.dur s) p.M (p.nodeW w : ℂ)‖ ≤ _
  have h := productFamily_sub_le (SlotSim.clampAt p.M Hs) (SlotSim.clampAt p.M Ls)
    (SlotSim.clampAt p.M Ls') (p.dur s) p.M (fun r => hH _ (hcl r)) (fun r => hL _ (hcl r))
    (fun r => hL' _ (hcl r)) (fun r => p.dur_nonneg hT s r) (p.nodeW w)
  refine h.trans ?_
  have hR : 0 ≤ p.R := ImprovedODEQueryBudget.radius_nonneg p.ratio p.acc (p.ratio_ge hg)
    (p.acc_pos hε) (p.acc_le_one hεOne)
  have hk := p.nodeW_abs_le hg hε hεOne hTD w
  have hsum : ∑ r ∈ Finset.range p.M,
      p.dur s r * ‖SlotSim.clampAt p.M Ls r - SlotSim.clampAt p.M Ls' r‖ ≤ p.T * c := by
    calc ∑ r ∈ Finset.range p.M,
          p.dur s r * ‖SlotSim.clampAt p.M Ls r - SlotSim.clampAt p.M Ls' r‖ ≤
        ∑ r ∈ Finset.range p.M, p.dur s r * c := by
          refine Finset.sum_le_sum fun r hr => ?_
          have hr' := Finset.mem_range.mp hr
          rw [SlotSim.clampAt_of_lt p.M Ls hr', SlotSim.clampAt_of_lt p.M Ls' hr']
          exact mul_le_mul_of_nonneg_left (hc r hr') (p.dur_nonneg hT s r)
      _ = (∑ r ∈ Finset.range p.M, p.dur s r) * c := by rw [Finset.sum_mul]
      _ ≤ p.T * c := mul_le_mul_of_nonneg_right (p.sum_dur_le hT s) hc0
  have hs0 : 0 ≤ ∑ r ∈ Finset.range p.M,
      p.dur s r * ‖SlotSim.clampAt p.M Ls r - SlotSim.clampAt p.M Ls' r‖ :=
    Finset.sum_nonneg fun r _ => mul_nonneg (p.dur_nonneg hT s r) (norm_nonneg _)
  exact mul_le_mul hk hsum hs0 hR

omit [CompleteSpace P] in
/-- The coefficient-weighted branch sums differ by at most three times the branch difference
(the coefficient mass is three). -/
theorem branch_sum_sub_le {p : TParams} (hg : 1 ≤ p.g) (hε : 0 < p.ε) (hεOne : p.ε ≤ 1)
    (hTD : 0 ≤ p.T * p.lamD) (Hs Ls Ls' : ℕ → P →L[ℂ] P) (s : Bool × (Fin p.m → Bool)) {W : ℝ}
    (hW : ∀ w, ‖p.branchU Hs Ls s w - p.branchU Hs Ls' s w‖ ≤ W) :
    ‖(∑ w, p.coeffW w • p.branchU Hs Ls s w) - ∑ w, p.coeffW w • p.branchU Hs Ls' s w‖ ≤
      3 * W := by
  rw [← Finset.sum_sub_distrib]
  calc ‖∑ w, (p.coeffW w • p.branchU Hs Ls s w - p.coeffW w • p.branchU Hs Ls' s w)‖ ≤
        ∑ w, ‖p.coeffW w • p.branchU Hs Ls s w - p.coeffW w • p.branchU Hs Ls' s w‖ :=
      norm_sum_le _ _
    _ ≤ ∑ w, ‖p.coeffW w‖ * W := by
      refine Finset.sum_le_sum fun w _ => ?_
      rw [← smul_sub, norm_smul]
      exact mul_le_mul_of_nonneg_left (hW w) (norm_nonneg _)
    _ = ODECoherentLCU.coefficientMass p.coeffW * W := by
      rw [ODECoherentLCU.coefficientMass, Finset.sum_mul]
    _ = 3 * W := by rw [p.coeffW_mass hg hε hεOne hTD]

/-! ### The certificate -/

/-- **The actual preparation satisfies the released actual-source certificate for the repaired
target**, represented samples of any sign. -/
theorem robust_prep_certificate {p : TParams} (hp : p.PublicOK) (v : P) (hv : ‖v‖ = 1)
    (σ : TOracles p.a p.m p.l P) (Hs Ls : ℕ → P →L[ℂ] P) (G : ℝ → P →L[ℂ] P) (b x : ℝ → P)
    (bs : ℕ → P) (βG δG βb δb bmax : ℝ)
    (hI : RobustInstanceOK p v σ Hs Ls G b x bs βG δG βb δb bmax) :
    ODEActualSourceError.Certificate p.branchE (p.zsrc (x 0) bs) p.coeffW σ.J
      (trun v σ p.select) v (p.target Hs (repairedLs Ls δG) (x 0) bs) p.ratio p.acc := by
  have hT := hp.T_pos.le
  have hS := hI.select
  have hU := hI.unitary
  have hδ := hI.δG_nonneg
  obtain ⟨hself', hpsd', hnorm', hdiff, -⟩ := hI.repaired hT
  set Ls' : ℕ → P →L[ℂ] P := repairedLs Ls δG with hLs'
  have hsel : IsUnitary (trun v σ p.select) :=
    trun_isUnitary v σ hU hv _ (fun g hg =>
      p.prepC_valid hp.tau_pos.le hp.nu_pos hp.mesh g (by simp [TParams.prepC, hg]))
  have hJ : ∀ s, (σ.J s)† ∘L σ.J s = 1 := by
    intro s
    have h := (hI.load_unitary s).1
    rwa [star_eq_adjoint, mul_def] at h
  have hM : 0 < p.T / p.M := div_pos hp.T_pos (by exact_mod_cast p.M_pos)
  have hPrep : ∀ s, p.zsrc (x 0) bs s ≠ 0 →
      σ.J s v = unitDirection (p.zsrc (x 0) bs s) := by
    intro s hs
    obtain ⟨c, w⟩ := s
    cases c
    · by_cases hw : w = (fun _ => false)
      · subst hw
        have hx : x 0 ≠ 0 := by
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
  obtain ⟨hy, hbud, _⟩ := robust_target_facts hp hI
  have hNorm := p.target_norm_le hT Hs Ls' hS.selfH hpsd' (x 0) bs
  have hSim := p.select_error hT hp.tau_pos hp.g_ge hp.ε_pos hp.eps_le_one hp.TD_nonneg hp.Q_ge
    hp.qbar_nonneg hp.qbar_le hp.mesh v σ Hs Ls hS
  -- The per-label targets: the represented branch sums corrected by the table error of the
  -- repaired family.
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
    have hbr := branchU_sub_le hT hp.g_ge hp.ε_pos hp.eps_le_one hp.TD_nonneg Hs Ls Ls' hS.selfH
      hS.selfL hself' (by linarith : (0 : ℝ) ≤ 2 * δG) hdiff s
    have h3 := branch_sum_sub_le hp.g_ge hp.ε_pos hp.eps_le_one hp.TD_nonneg Hs Ls Ls' s hbr
    have hB := hI.branch
    calc ‖Bsum s - Rsum s‖ ≤ 3 * (p.R * (p.T * (2 * δG))) := h3
      _ = 6 * p.R * p.T * δG := by ring
      _ ≤ p.nu := hB
  have hQuad : ‖(∑ s, Sx s (p.zsrc (x 0) bs s)) - p.target Hs Ls' (x 0) bs‖ ≤
      ImprovedODEQueryBudget.precision p.ratio p.acc *
        ODESourceBranches.mass (p.zsrc (x 0) bs) := by
    have e : (∑ s, Sx s (p.zsrc (x 0) bs s)) - p.target Hs Ls' (x 0) bs =
        ∑ s, (Bsum s - Rsum s) (p.zsrc (x 0) bs s) := by
      rw [← p.source_sum Hs Ls' (x 0) bs, ← Finset.sum_sub_distrib]
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
    (p.zsrc (x 0) bs) p.coeffW hmass σ.J hJ v hv hPrep (trun v σ p.select) hsel
    (p.branchU Hs Ls) Sx (p.target Hs Ls' (x 0) bs) p.ratio p.acc hy
    (p.ratio_ge hp.g_ge) (p.acc_pos hp.ε_pos) hacc hNorm hbud (by convert hSim using 4) hLCHS hQuad

end

end SparseHamiltonian.RepresentedSampleODE.GateTime
