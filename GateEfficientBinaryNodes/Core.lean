import GateEfficientBinarySelect.Synth

/-!
# The outcome of the released protocol from the target facts

The released chain on branch-dependent meshes (`GateSelect.ODE.prep_certificateB`,
`native_time_outcomeB`, `GateBinarySelect.native_time_trials_outcomeB`) uses its instance
conditions `GateSelect.ODE.BInstanceOK` in two ways: the selection and source conditions
directly, and the generator path, the branch solutions, the sample bound and the budget only
through the three *target facts* of `GateSelect.ODE.target_factsB` (the exact target `y` is
nonzero, `B ≤ 2 g ‖y‖`, and `y` has the direction of `x(T)` up to `ε/1000`). This module states
the chain with the facts as hypotheses, so that other certificates of the target error (the
integrated sample-error certificate of `Integrated`) give the released guarantees.

* `BCore`: the selection and source conditions of `BInstanceOK` (no path, solution or budget),
  for an initial vector `x₀`; `BInstanceOK.core`.
* `TFacts`: the three target facts for `x₀` and a target vector `x_T`;
  `target_facts_of_error`: they follow from `‖x_T - y‖ ≤ E` with `E ≤ ε B/(2000 g)`, `x_T ≠ 0` and
  `B ≤ g ‖x_T‖` (the released `TimeDependentODE.Sampling.target_budget`).
* `prep_certificateC`: the released actual-source certificate of the preparation;
* `native_time_outcomeC`: the guarantees `NOutcome` of the native protocol;
* `native_time_trials_outcomeC`: the guarantees `NOutcome` of the native protocol on the
  synthesised preparation `GateSynthTrials.synthPrep`.

The proofs are those of the released theorems, with `target_factsB` replaced by the facts.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateBinaryNodes

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit GateNative
open GateCircuit.Sim (Wire)
open GateODE (Label ClockPromise goodF goodF_isometry seedState seedState_norm)
open GateODE.Time (TParams TOracles trun gens teval)
open GateSelect.ODE (startB durB addrB branchHB branchUB propB bsW targetB BInstanceOK
  zsrc_bsW targetB_norm_le select_errorB lchs_errorB)
open GatePointerEncoding (wordValue)
open TimeDependentODE (SolvesODE Accretive)
open ODEStateNormalization (unitDirection)
open scoped InnerProduct BigOperators

/-! ### The core conditions and the target facts -/

section Defs

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
variable (p : TParams)

/-- **The core conditions** of an instance of the released time-dependent protocol on
branch-dependent meshes: the selection conditions (unitary supplied operations, the clock
promises for the branch Hamiltonians, represented samples with their norm bounds) and the source
conditions (nodes, nonnegative weights, the loading and the weight preparation for the initial
vector `x₀`) of `GateSelect.ODE.BInstanceOK`. -/
structure BCore (v₀ : P) (σ : TOracles p.a p.m p.l P) (v wq : ℕ → ℝ) (fv : ℕ → P)
    (Hb Lb : Bool × (Fin p.m → Bool) → ℕ → P →L[ℂ] P) (x0 : P) : Prop where
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
  prep : p.WpPromise σ x0 (bsW p wq fv)
  init_load : x0 ≠ 0 → σ.J (false, fun _ => false) v₀ = unitDirection x0
  forcing_load : ∀ w : Fin p.m → Bool, wq (wordValue w) ≠ 0 → fv (wordValue w) ≠ 0 →
    σ.J (true, w) v₀ = unitDirection (fv (wordValue w))

/-- **The target facts**: the exact target `y = targetB` of the circuit for the initial vector
`x₀` is nonzero, the source mass satisfies `B ≤ 2 g ‖y‖`, and `y` has the direction of `x_T` up
to `ε/1000`. -/
def TFacts (v : ℕ → ℝ) (Hb Lb : Bool × (Fin p.m → Bool) → ℕ → P →L[ℂ] P) (x0 : P)
    (wq : ℕ → ℝ) (fv : ℕ → P) (xT : P) : Prop :=
  targetB p v Hb Lb x0 wq fv ≠ 0 ∧
    p.mass x0 (bsW p wq fv) ≤ 2 * p.g * ‖targetB p v Hb Lb x0 wq fv‖ ∧
    ‖unitDirection (targetB p v Hb Lb x0 wq fv) - unitDirection xT‖ ≤ p.ε / 1000

variable {p}

theorem BCore.unitary {v₀ : P} {σ : TOracles p.a p.m p.l P} {v wq : ℕ → ℝ} {fv : ℕ → P}
    {Hb Lb : Bool × (Fin p.m → Bool) → ℕ → P →L[ℂ] P} {x0 : P}
    (hI : BCore p v₀ σ v wq fv Hb Lb x0) : σ.Unitary p.m :=
  ⟨hI.uj, hI.priv, hI.load_unitary, hI.prep_left, hI.prep_right⟩

/-- The core conditions of a released instance. -/
theorem BInstanceOK.core {v₀ : P} {σ : TOracles p.a p.m p.l P} {v wq : ℕ → ℝ} {fv : ℕ → P}
    {Hb Lb : Bool × (Fin p.m → Bool) → ℕ → P →L[ℂ] P} {G : ℝ → P →L[ℂ] P} {b x : ℝ → P}
    {ys : Bool × (Fin p.m → Bool) → ℝ → P} {βG δG κ : ℝ}
    (hI : BInstanceOK p v₀ σ v wq fv Hb Lb G b x ys βG δG κ) :
    BCore p v₀ σ v wq fv Hb Lb (x 0) :=
  ⟨hI.uj, hI.priv, hI.clock, hI.selfH, hI.selfL, hI.normH, hI.normL, hI.psd, hI.nodes,
    hI.weights, hI.load_unitary, hI.prep_left, hI.prep_right, hI.prep, hI.init_load,
    hI.forcing_load⟩

/-- **The target facts from a target error.** If `‖x_T - y‖ ≤ E` for the exact target `y`, with
`x_T ≠ 0`, `B ≤ g ‖x_T‖` and `E ≤ ε B / (2000 g)`, the target facts hold. -/
theorem target_facts_of_error (hp : p.PublicOK) (v : ℕ → ℝ)
    (Hb Lb : Bool × (Fin p.m → Bool) → ℕ → P →L[ℂ] P) (x0 : P) (wq : ℕ → ℝ) (fv : ℕ → P)
    (xT : P) (E : ℝ) (hne : xT ≠ 0) (hbud : p.mass x0 (bsW p wq fv) ≤ p.g * ‖xT‖)
    (herr : ‖xT - targetB p v Hb Lb x0 wq fv‖ ≤ E)
    (hdisc : E ≤ p.ε * p.mass x0 (bsW p wq fv) / (2000 * p.g)) :
    TFacts p v Hb Lb x0 wq fv xT :=
  TimeDependentODE.Sampling.target_budget xT (targetB p v Hb Lb x0 wq fv)
    (p.mass x0 (bsW p wq fv)) p.g p.ε E hp.g_ge hp.ε_pos hp.eps_le_one hne hbud herr hdisc

/-- The released instance conditions give the target facts. -/
theorem BInstanceOK.facts (hp : p.PublicOK) {v₀ : P} {σ : TOracles p.a p.m p.l P}
    {v wq : ℕ → ℝ} {fv : ℕ → P} {Hb Lb : Bool × (Fin p.m → Bool) → ℕ → P →L[ℂ] P}
    {G : ℝ → P →L[ℂ] P} {b x : ℝ → P} {ys : Bool × (Fin p.m → Bool) → ℝ → P} {βG δG κ : ℝ}
    (hI : BInstanceOK p v₀ σ v wq fv Hb Lb G b x ys βG δG κ) :
    TFacts p v Hb Lb (x 0) wq fv (x p.T) :=
  GateSelect.ODE.target_factsB hp hI

end Defs

/-! ### The actual-source certificate -/

section Certificate

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
variable (p : TParams)

/-- **The actual preparation of the released protocol satisfies the released actual-source
certificate for the exact target**, under the core conditions and the first two target facts
(the proof of `GateSelect.ODE.prep_certificateB`). -/
theorem prep_certificateC (hp : p.PublicOK) (v₀ : P) (hv : ‖v₀‖ = 1)
    (σ : TOracles p.a p.m p.l P) (v wq : ℕ → ℝ) (fv : ℕ → P)
    (Hb Lb : Bool × (Fin p.m → Bool) → ℕ → P →L[ℂ] P) (x0 : P)
    (hI : BCore p v₀ σ v wq fv Hb Lb x0) (hy : targetB p v Hb Lb x0 wq fv ≠ 0)
    (hbud : p.mass x0 (bsW p wq fv) ≤ 2 * p.g * ‖targetB p v Hb Lb x0 wq fv‖) :
    ODEActualSourceError.Certificate p.branchE (p.zsrc x0 (bsW p wq fv)) p.coeffW σ.J
      (trun v₀ σ p.select) v₀ (targetB p v Hb Lb x0 wq fv) p.ratio p.acc := by
  have hT := hp.T_pos.le
  have hU := hI.unitary
  have hsel : IsUnitary (trun v₀ σ p.select) :=
    GateODE.Time.trun_isUnitary v₀ σ hU hv _ (fun g hg =>
      p.prepC_valid hp.tau_pos.le hp.nu_pos hp.mesh g (by simp [GateODE.Time.TParams.prepC, hg]))
  have hJ : ∀ s, (σ.J s)† ∘L σ.J s = 1 := by
    intro s
    have h := (hI.load_unitary s).1
    rwa [star_eq_adjoint, mul_def] at h
  have hPrep : ∀ s, p.zsrc x0 (bsW p wq fv) s ≠ 0 →
      σ.J s v₀ = unitDirection (p.zsrc x0 (bsW p wq fv) s) := by
    intro s hs
    obtain ⟨c, w⟩ := s
    cases c
    · by_cases hw : w = (fun _ => false)
      · subst hw
        have hx : x0 ≠ 0 := by
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
  have hNorm := targetB_norm_le p hT v hI.nodes Hb Lb hI.selfH hI.selfL hI.psd x0 wq fv
  have hSim := select_errorB p hp v₀ σ v hI.nodes Hb Lb hI.uj hI.priv hI.selfH hI.selfL
    hI.normH hI.normL hI.clock
  have hLCHS := fun s => lchs_errorB p hT hp.g_ge hp.ε_pos hp.eps_le_one hp.lamD_nonneg v
    hI.nodes Hb Lb hI.selfH hI.selfL hI.normL hI.psd s
  have hQuad : ‖(∑ s, propB p v Hb Lb s (p.zsrc x0 (bsW p wq fv) s)) -
      targetB p v Hb Lb x0 wq fv‖ ≤
      ImprovedODEQueryBudget.precision p.ratio p.acc *
        ODESourceBranches.mass (p.zsrc x0 (bsW p wq fv)) := by
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
    (p.zsrc x0 (bsW p wq fv)) p.coeffW hmass σ.J hJ v₀ hv hPrep (trun v₀ σ p.select) hsel
    (branchUB p v Hb Lb) (propB p v Hb Lb) (targetB p v Hb Lb x0 wq fv) p.ratio p.acc hy
    (p.ratio_ge hp.g_ge) (p.acc_pos hp.ε_pos) hacc hNorm hbud (by convert hSim using 4) hLCHS
    hQuad

end Certificate

/-! ### The native outcomes -/

section Native

variable {S Zs Z Y J Xa : Type*} [Fintype S] [DecidableEq S] [Fintype Zs] [DecidableEq Zs]
  [Fintype Z] [DecidableEq Z] [Fintype Y] [DecidableEq Y] [Fintype Xa] [DecidableEq Xa]
variable {𝒢 : Set GateSynth.Kind} {len : ℝ → ℕ}

/-- **The guarantees of the native protocol from the core conditions and the target facts** (the
proof of `GateSelect.ODE.native_time_outcomeB`). For the native data of the released native
time-dependent solver (the native identity of the label- and slot-selected private family, the
loading and the weight preparation within `ζs`, the budget `24 d ζ + 3 ζs ≤ ν`), an instance
with the core conditions for the initial vector `x₀` and the target facts for `x_T ≠ 0`, the
native protocol has the guarantees `NOutcome` for `x_T`. -/
theorem native_time_outcomeC (p : TParams) (hp : p.PublicOK)
    (UJg : List (Gate (Fin p.a ⊕ S))) (hUJg : ∀ g ∈ UJg, GateOK 3 g)
    (nd : NativeOp (TSel p.m p.l p.m) (Fin p.a ⊕ S) Z Y J) (hnd : nd.Public)
    (ar : Arith (NB (TSel p.m p.l p.m) (Fin p.a ⊕ S) Z)) (ζ : ℝ) (hζ : 0 ≤ ζ)
    (har : ArithOK ar (Sum.inl (Sum.inr nd.o)) nd.dec ζ)
    (loadC : List (NInstr ((Fin (p.m + 1) ⊕ S) ⊕ Zs) Y J)) (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (p.m + 1) ⊕ Zs) Y J)) (hwpV : ∀ i ∈ wpC, i.Valid)
    (prim : J → Reg Y ℂ →L[ℂ] Reg Y ℂ) (hprim : ∀ j, IsUnitary (prim j))
    (σ : TOracles p.a p.m p.l (Reg S ℂ)) (hUJ : σ.UJ = UJop (R := ℂ) UJg)
    (hN : NativeOK prim nd (selOp (tlabFam (P := Reg S ℂ) σ.D false)))
    (ζs : ℝ) (hζs : 0 ≤ ζs)
    (hload : ApproxOn CleanX (nrun prim loadC) (liftB (loadIdeal σ.J)) ζs)
    (hwp : ApproxOn CleanX (nrun prim wpC) (liftB (matOp σ.Wp)) ζs)
    (hbudget : 24 * (p.d : ℝ) * ζ + 3 * ζs ≤ p.nu)
    (v wq : ℕ → ℝ) (fv : ℕ → Reg S ℂ)
    (Hb Lb : Bool × (Fin p.m → Bool) → ℕ → Reg S ℂ →L[ℂ] Reg S ℂ) (x0 xT : Reg S ℂ)
    (hI : BCore p (seedV (S := S)) σ v wq fv Hb Lb x0)
    (hF : TFacts p v Hb Lb x0 wq fv xT) (hne : xT ≠ 0) :
    NOutcome (tnprepC p UJg nd ar loadC wpC) p.ratio p.ε (p.ratio_ge hp.g_ge) prim xT := by
  obtain ⟨cP, -, cSF, cST, -, -⟩ := p.prepC_counts hp.tau_pos.le hp.nu_pos hp.mesh
  have hvalid := p.prepC_valid hp.tau_pos.le hp.nu_pos hp.mesh
  have hprepV := tnprepC_valid p hp UJg hUJg nd hnd ar har loadC hloadV wpC hwpV
  have hU := hI.unitary
  have hDu : ∀ w, IsUnitary (tlabFam (m := p.m) (P := Reg S ℂ) σ.D false w) := fun w =>
    hU.priv _ _ (GatePointerEncoding.wordEquivFin p.m (fun i => w (Sum.inr i))).isLt
  have hDadj : ∀ w, tlabFam (m := p.m) (P := Reg S ℂ) σ.D true w =
      (tlabFam (m := p.m) (P := Reg S ℂ) σ.D false w)† := fun _ => rfl
  have hA := oprep_approx prim hprim tlabSel UJg hUJg nd hnd ar hζ har
    (tlabFam (P := Reg S ℂ) σ.D) hDu hDadj hN (teval (seedV (S := S)) σ) (fun _ => rfl)
    (fun adj => tode_eval_uj (seedV (S := S)) σ UJg hUJ tlabSel (tlabFam (P := Reg S ℂ) σ.D) adj)
    (fun adj => tode_eval_priv (seedV (S := S)) σ UJg adj)
    (tsrcMacro p loadC wpC) hζs
    (fun c adj => tsrcMacro_approx p prim hprim loadC hloadV wpC hwpV (seedV (S := S)) σ hU hζs
      hload hwp c adj)
    (tsrcMacro_valid p loadC hloadV wpC hwpV) p.prepC (osec_tprepC p) (noseed_tprepC p hp) hvalid
    (fun i hi => GateODE.Time.teval_isUnitary (seedV (S := S)) σ hU norm_seedV i (hvalid i hi))
  rw [prodOps_teval, nSrcAny_eq, cP, cSF, cST] at hA
  have hδ : ((6 * p.d : ℕ) : ℝ) * (4 * ζ) + ((1 + 2 : ℕ) : ℝ) * ζs ≤ p.nu := by
    have e2 : ((6 * p.d : ℕ) : ℝ) = 6 * (p.d : ℝ) := by rw [Nat.cast_mul, Nat.cast_ofNat]
    have e3 : ((1 + 2 : ℕ) : ℝ) = 3 := by norm_num
    rw [e2, e3]
    linarith only [hbudget]
  have hA' := hA.mono hδ
  obtain ⟨hy, hbud, hdirY⟩ := hF
  have hC := prep_certificateC p hp (seedV (S := S)) norm_seedV σ v wq fv Hb Lb x0 hI hy hbud
  have hNorm := targetB_norm_le p hp.T_pos.le v hI.nodes Hb Lb hI.selfH hI.selfL hI.psd x0 wq fv
  have hB : 0 < p.mass x0 (bsW p wq fv) := (norm_pos_iff.mpr hy).trans_le hNorm
  have hdec := p.decoded_eq hp (seedV (S := S)) σ x0 (bsW p wq fv) hB hI.prep
  have h := hC.vector_error
  have hm : p.mass x0 (bsW p wq fv) = ODESourceBranches.mass (p.zsrc x0 (bsW p wq fv)) := rfl
  rw [← hdec, ← hm] at h
  have hacc : p.acc ≤ 1 / 2 := by
    have := hp.ε_half
    simp only [TParams.acc]
    linarith
  have hUN : IsUnitary (nrun prim (tnprepC p UJg nd ar loadC wpC)) :=
    nrun_isUnitary prim hprim _ hprepV
  have hnP : Fintype.card (GateODE.AW p.a p.m p.r p.K p.m p.l p.f) +
      Fintype.card (XW Z ar.bT ar.bP ar.A) + Fintype.card Zs + Fintype.card S ≤
      tnPool p S Zs Z ar.bT ar.bP ar.A + 1 := Nat.le_succ _
  generalize trun (seedV (S := S)) σ p.prepC = Urel at h hA'
  generalize targetB p v Hb Lb x0 wq fv = y at h hy hbud hdirY hNorm
  have hbud' : p.mass x0 (bsW p wq fv) ≤ p.ratio * ‖y‖ := hbud
  have hdirY' : ‖unitDirection y - unitDirection xT‖ ≤ p.ε / 1000 := hdirY
  obtain ⟨-, -, hmean, hdir⟩ := native_trial_bounds prim hnP (tnprepC p UJg nd ar loadC wpC) hUN
    (tnprepC_pres p UJg nd ar loadC wpC prim) Urel hA' y (p.mass x0 (bsW p wq fv)) p.ratio p.acc
    hy (p.ratio_ge hp.g_ge) (p.acc_pos hp.ε_pos) hacc hNorm hbud' h le_rfl
  refine noutcome_of_bounds (tnprepC p UJg nd ar loadC wpC) prim hprim hprepV xT
    hne p.ratio p.ε (p.ratio_ge hp.g_ge) hp.ε_pos hmean ?_
  intro j hj
  obtain ⟨ω, hω, hd⟩ := hdir j hj
  refine ⟨ω, hω, ?_⟩
  refine (norm_sub_le_norm_sub_add_norm_sub _ (unitDirection y) _).trans ?_
  have e : p.acc / 500 + p.ε / 1000 = p.ε / 500 := by
    simp only [TParams.acc]
    ring
  linarith only [hd, hdirY', e]

/-- **The guarantees of the synthesised preparation from the core conditions and the target
facts** (the proof of `GateBinarySelect.native_time_trials_outcomeB`): under the hypotheses of
`native_time_outcomeC`, the released native protocol on the synthesised preparation
`synthPrep hS (ν/3) (tnprepC …)` has the guarantees `NOutcome` for `x_T`. -/
theorem native_time_trials_outcomeC (hS : GateSynth.Synthesis 𝒢 Xa len) (p : TParams)
    (hp : p.PublicOK) (UJg : List (Gate (Fin p.a ⊕ S))) (hUJg : ∀ g ∈ UJg, GateOK 3 g)
    (nd : NativeOp (TSel p.m p.l p.m) (Fin p.a ⊕ S) Z Y J) (hnd : nd.Public)
    (ar : Arith (NB (TSel p.m p.l p.m) (Fin p.a ⊕ S) Z)) (ζ : ℝ) (hζ : 0 ≤ ζ)
    (har : ArithOK ar (Sum.inl (Sum.inr nd.o)) nd.dec ζ)
    (loadC : List (NInstr ((Fin (p.m + 1) ⊕ S) ⊕ Zs) Y J)) (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (p.m + 1) ⊕ Zs) Y J)) (hwpV : ∀ i ∈ wpC, i.Valid)
    (prim : J → Reg Y ℂ →L[ℂ] Reg Y ℂ) (hprim : ∀ j, IsUnitary (prim j))
    (σ : TOracles p.a p.m p.l (Reg S ℂ)) (hUJ : σ.UJ = UJop (R := ℂ) UJg)
    (hN : NativeOK prim nd (selOp (tlabFam (P := Reg S ℂ) σ.D false)))
    (ζs : ℝ) (hζs : 0 ≤ ζs)
    (hload : ApproxOn CleanX (nrun prim loadC) (liftB (loadIdeal σ.J)) ζs)
    (hwp : ApproxOn CleanX (nrun prim wpC) (liftB (matOp σ.Wp)) ζs)
    (hbudget : 24 * (p.d : ℝ) * ζ + 3 * ζs ≤ p.nu)
    (v wq : ℕ → ℝ) (fv : ℕ → Reg S ℂ)
    (Hb Lb : Bool × (Fin p.m → Bool) → ℕ → Reg S ℂ →L[ℂ] Reg S ℂ) (x0 xT : Reg S ℂ)
    (hI : BCore p (seedV (S := S)) σ v wq fv Hb Lb x0)
    (hF : TFacts p v Hb Lb x0 wq fv xT) (hne : xT ≠ 0) :
    NOutcome (GateSynthTrials.synthPrep hS (p.nu / 3) (tnprepC p UJg nd ar loadC wpC)) p.ratio
      p.ε (p.ratio_ge hp.g_ge) prim xT := by
  have hprepV := tnprepC_valid p hp UJg hUJg nd hnd ar har loadC hloadV wpC hwpV
  have hν := hp.nu_pos
  have hη : 0 < p.nu / 3 := by positivity
  obtain ⟨cP, -, cSF, cST, -, -⟩ := p.prepC_counts hp.tau_pos.le hp.nu_pos hp.mesh
  have hvalid := p.prepC_valid hp.tau_pos.le hp.nu_pos hp.mesh
  have hU := hI.unitary
  have hDu : ∀ w, IsUnitary (tlabFam (m := p.m) (P := Reg S ℂ) σ.D false w) := fun w =>
    hU.priv _ _ (GatePointerEncoding.wordEquivFin p.m (fun i => w (Sum.inr i))).isLt
  have hDadj : ∀ w, tlabFam (m := p.m) (P := Reg S ℂ) σ.D true w =
      (tlabFam (m := p.m) (P := Reg S ℂ) σ.D false w)† := fun _ => rfl
  have hA := oprep_approx prim hprim tlabSel UJg hUJg nd hnd ar hζ har
    (tlabFam (P := Reg S ℂ) σ.D) hDu hDadj hN (teval (seedV (S := S)) σ) (fun _ => rfl)
    (fun adj => tode_eval_uj (seedV (S := S)) σ UJg hUJ tlabSel (tlabFam (P := Reg S ℂ) σ.D) adj)
    (fun adj => tode_eval_priv (seedV (S := S)) σ UJg adj)
    (tsrcMacro p loadC wpC) hζs
    (fun c adj => tsrcMacro_approx p prim hprim loadC hloadV wpC hwpV (seedV (S := S)) σ hU hζs
      hload hwp c adj)
    (tsrcMacro_valid p loadC hloadV wpC hwpV) p.prepC (osec_tprepC p) (noseed_tprepC p hp) hvalid
    (fun i hi => GateODE.Time.teval_isUnitary (seedV (S := S)) σ hU norm_seedV i (hvalid i hi))
  rw [prodOps_teval, nSrcAny_eq, cP, cSF, cST] at hA
  have hδ : ((6 * p.d : ℕ) : ℝ) * (4 * ζ) + ((1 + 2 : ℕ) : ℝ) * ζs ≤ p.nu := by
    have e2 : ((6 * p.d : ℕ) : ℝ) = 6 * (p.d : ℝ) := by rw [Nat.cast_mul, Nat.cast_ofNat]
    have e3 : ((1 + 2 : ℕ) : ℝ) = 3 := by norm_num
    rw [e2, e3]
    linarith only [hbudget]
  have hA' := hA.mono hδ
  obtain ⟨hy, hbud, hdirY⟩ := hF
  have hC := prep_certificateC p hp (seedV (S := S)) norm_seedV σ v wq fv Hb Lb x0 hI hy hbud
  have hNorm := targetB_norm_le p hp.T_pos.le v hI.nodes Hb Lb hI.selfH hI.selfL hI.psd x0 wq fv
  have hB : 0 < p.mass x0 (bsW p wq fv) := (norm_pos_iff.mpr hy).trans_le hNorm
  have hdec := p.decoded_eq hp (seedV (S := S)) σ x0 (bsW p wq fv) hB hI.prep
  have h := hC.vector_error
  have hm : p.mass x0 (bsW p wq fv) = ODESourceBranches.mass (p.zsrc x0 (bsW p wq fv)) := rfl
  rw [← hdec, ← hm] at h
  have hacc : p.acc ≤ 1 / 2 := by
    have := hp.ε_half
    simp only [TParams.acc]
    linarith
  have hUS : IsUnitary (nrun prim (GateSynthTrials.synthPrep hS (p.nu / 3)
      (tnprepC p UJg nd ar loadC wpC))) :=
    nrun_isUnitary prim hprim _ (GateSynthTrials.synthPrep_valid hS hη _ hprepV)
  have hηδ : p.nu / 3 + p.nu ≤ 4 / 3 * ImprovedODEQueryBudget.precision p.ratio p.acc := by
    have e : p.nu = ImprovedODEQueryBudget.precision p.ratio p.acc := rfl
    linarith only [e]
  generalize trun (seedV (S := S)) σ p.prepC = Urel at h hA'
  generalize targetB p v Hb Lb x0 wq fv = y at h hy hbud hdirY hNorm
  have hbud' : p.mass x0 (bsW p wq fv) ≤ p.ratio * ‖y‖ := hbud
  have hdirY' : ‖unitDirection y - unitDirection xT‖ ≤ p.ε / 1000 := hdirY
  have hAT := GateSynthTrials.synthPrep_approx hS hη (tnprepC p UJg nd ar loadC wpC) hprepV prim
    hprim Urel hν.le hA'
  obtain ⟨-, -, hmean, hdir⟩ := GateSynthTrials.native_trial_bounds10 prim
    GateSynthTrials.hnP_SWO (GateSynthTrials.synthPrep hS (p.nu / 3)
      (tnprepC p UJg nd ar loadC wpC)) hUS
    (GateSynthTrials.synthPrep_pres hS (p.nu / 3) (tnprepC p UJg nd ar loadC wpC) prim) Urel hAT
    y (p.mass x0 (bsW p wq fv)) p.ratio p.acc hy (p.ratio_ge hp.g_ge) (p.acc_pos hp.ε_pos) hacc
    hNorm hbud' h hηδ
  refine noutcome_of_bounds (GateSynthTrials.synthPrep hS (p.nu / 3)
    (tnprepC p UJg nd ar loadC wpC)) prim hprim
    (GateSynthTrials.synthPrep_valid hS hη _ hprepV) xT hne p.ratio p.ε
    (p.ratio_ge hp.g_ge) hp.ε_pos hmean ?_
  intro j hj
  obtain ⟨ω, hω, hd⟩ := hdir j hj
  refine ⟨ω, hω, ?_⟩
  refine (norm_sub_le_norm_sub_add_norm_sub _ (unitDirection y) _).trans ?_
  have e : p.acc / 500 + p.ε / 1000 = p.ε / 500 := by
    simp only [TParams.acc]
    ring
  linarith only [hd, hdirY', e]

end Native

end

end SparseHamiltonian.GateBinaryNodes
