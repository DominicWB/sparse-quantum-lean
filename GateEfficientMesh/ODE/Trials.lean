import GateEfficientMesh.ODE.BinaryMesh
import GateEfficientODEBudget.Synth

/-!
# The ODE endpoints over a finite gate set with exact reflections

The finite-gate-set forms of Theorem `ode:thm:gates` in this module are a partial formalisation of
its finite-set statement, under this package's format hypotheses: the manuscript states Theorem
`ode:thm:gates` over a finite gate set; the conformance endpoints count native gates.

The released per-trial finite-set forms of Theorem `ode:thm:gates`, time-dependent part
(`GateSynthTrials.native_ode_time_solver_trials`,
`GateSynthTrials.binary_ode_time_solver_trials`, `GateODEBudget.binary_ode_time_budget_trials`),
synthesise one native preparation over `𝒢` with the synthesis budget `ν/3`
(`GateSynthTrials.synthPrep`) and keep the zero tests, the sign and the inverse preparation
exact; their guarantee is the native `NOutcome` of the protocol on the synthesised preparation,
every successful trial included. Their proofs use the instance only through the released
actual-source certificate and the target facts; `trials_outcome_of` reassembles the instance
part from the public lemmas (`oprep_approx`, `tsrcMacro_approx`, `synthPrep_approx`,
`native_trial_bounds10`, `noutcome_of_bounds`) with the certificate of `prep_certificate_of` and
the target facts of `target_facts_of`. The counts are those of the released theorems.

* `native_ode_time_solver_certified_trials`, `native_ode_time_solver_mesh_trials`;
* `binary_ode_time_solver_certified_trials`, `binary_ode_time_solver_mesh_trials`;
* `binary_ode_time_budget_certified_trials`, `binary_ode_time_budget_mesh_trials`: the budget
  form (equations `ode:eq:gate-main` and `ode:eq:gate-space` over a finite gate set) with the
  public rescaling `γ = gammaOf …`.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateMesh.ODE

noncomputable section
open ContinuousLinearMap MeasureTheory Set OracleCircuit GateCircuit GateNative GateSynth
open SparseHamiltonian.GateSynthTrials SparseHamiltonian.GateODEBudget
open SparseHamiltonian.GateBinary SparseHamiltonian.GateBinaryODE
open SparseHamiltonian.GateBinaryODETime
open NativeSparseBlockEncoding (Data Query)
open GateCircuit.Sim (Wire)
open GateODE (Label)
open GateODE.Time (TParams TOracles teval trun)
open GatePointerEncoding (wordEquivFin)
open ODEStateNormalization (unitDirection)
open ImprovedODEQueryBudget (logBudget)
open TimeDependentODE (SolvesODE Accretive)
open TimeDependentExtensions (IsMesh slotPiece)
open scoped InnerProduct BigOperators

section Native

variable {S Zs Z Y J X : Type*} [Fintype S] [DecidableEq S] [Fintype Zs] [DecidableEq Zs]
  [Fintype Z] [DecidableEq Z] [Fintype Y] [DecidableEq Y] [Fintype X] [DecidableEq X]
variable {𝒢 : Set Kind} {len : ℝ → ℕ}

/-- **The per-trial guarantees of the protocol on the synthesised preparation for one
instance**, from the conditions on the supplied unitaries (`CoreOK`) and on the final state
(`TargetOK`), with native implementations of the private operation (`NativeOK`, `ArithOK`), of
the loading and of the weight preparation (within `ζs`) and the budget `24 d ζ + 3 ζs ≤ ν`: the
protocol `nprotocol (synthPrep hS (ν/3) (tnprepC …)) (2g)` has the guarantees `NOutcome`. -/
theorem trials_outcome_of (hS : Synthesis 𝒢 X len) (p : TParams) (hp : p.PublicOK)
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
    (Hs Ls : ℕ → Reg S ℂ →L[ℂ] Reg S ℂ) (x0 : Reg S ℂ) (bs : ℕ → Reg S ℂ) (xT : Reg S ℂ)
    (hC : CoreOK p (seedV (S := S)) σ Hs Ls x0 bs) (hT : TargetOK p Hs Ls x0 bs xT) :
    NOutcome (synthPrep hS (p.nu / 3) (tnprepC p UJg nd ar loadC wpC)) p.ratio p.ε
      (p.ratio_ge hp.g_ge) prim xT := by
  have hprepV := tnprepC_valid p hp UJg hUJg nd hnd ar har loadC hloadV wpC hwpV
  have hν := hp.nu_pos
  have hη : 0 < p.nu / 3 := by positivity
  obtain ⟨cP, -, cSF, cST, -, -⟩ := p.prepC_counts hp.tau_pos.le hp.nu_pos hp.mesh
  have hvalid := p.prepC_valid hp.tau_pos.le hp.nu_pos hp.mesh
  have hU := hC.unitary
  have hDu : ∀ w, IsUnitary (tlabFam (m := p.m) (P := Reg S ℂ) σ.D false w) := fun w =>
    hU.priv _ _ (wordEquivFin p.m (fun i => w (Sum.inr i))).isLt
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
  -- the released certificate of the discretised target, from the target facts
  obtain ⟨hy, hbud, hdirY⟩ := target_facts_of p hp hT
  have hCert := prep_certificate_of p hp (seedV (S := S)) norm_seedV σ Hs Ls x0 bs hC hy hbud
  have hNorm := p.target_norm_le hp.T_pos.le Hs Ls hC.select.selfH hC.psd x0 bs
  have hB : 0 < p.mass x0 bs := (norm_pos_iff.mpr hy).trans_le hNorm
  have hdec := p.decoded_eq hp (seedV (S := S)) σ x0 bs hB hC.sources.prep
  have h := hCert.vector_error
  have hm : p.mass x0 bs = ODESourceBranches.mass (p.zsrc x0 bs) := rfl
  rw [← hdec, ← hm] at h
  have hacc : p.acc ≤ 1 / 2 := by
    have := hp.ε_half
    simp only [TParams.acc]
    linarith
  have hUS : IsUnitary (nrun prim (synthPrep hS (p.nu / 3) (tnprepC p UJg nd ar loadC wpC))) :=
    nrun_isUnitary prim hprim _ (synthPrep_valid hS hη _ hprepV)
  have hne := hT.ne
  have hηδ : p.nu / 3 + p.nu ≤ 4 / 3 * ImprovedODEQueryBudget.precision p.ratio p.acc := by
    have e : p.nu = ImprovedODEQueryBudget.precision p.ratio p.acc := rfl
    linarith only [e]
  generalize trun (seedV (S := S)) σ p.prepC = Urel at h hA'
  generalize p.target Hs Ls x0 bs = y at h hy hbud hdirY hNorm
  have hbud' : p.mass x0 bs ≤ p.ratio * ‖y‖ := hbud
  have hdirY' : ‖unitDirection y - unitDirection xT‖ ≤ p.ε / 1000 := hdirY
  have hAT := synthPrep_approx hS hη (tnprepC p UJg nd ar loadC wpC) hprepV prim hprim Urel
    hν.le hA'
  obtain ⟨-, -, hmean, hdir⟩ := native_trial_bounds10 prim hnP_SWO
    (synthPrep hS (p.nu / 3) (tnprepC p UJg nd ar loadC wpC)) hUS
    (synthPrep_pres hS (p.nu / 3) (tnprepC p UJg nd ar loadC wpC) prim) Urel hAT y
    (p.mass x0 bs) p.ratio p.acc hy (p.ratio_ge hp.g_ge) (p.acc_pos hp.ε_pos) hacc hNorm hbud' h
    hηδ
  refine noutcome_of_bounds (synthPrep hS (p.nu / 3) (tnprepC p UJg nd ar loadC wpC)) prim hprim
    (synthPrep_valid hS hη _ hprepV) xT hne p.ratio p.ε (p.ratio_ge hp.g_ge) hp.ε_pos hmean ?_
  intro j hj
  obtain ⟨ω, hω, hd⟩ := hdir j hj
  refine ⟨ω, hω, ?_⟩
  refine (norm_sub_le_norm_sub_add_norm_sub _ (unitDirection y) _).trans ?_
  have e : p.acc / 500 + p.ε / 1000 = p.ε / 500 := by
    simp only [TParams.acc]
    ring
  linarith only [hd, hdirY', e]

/-- **Native dissipative ODE solver under the integrated certificate on the uniform slots over a
finite gate set with exact reflections** (partial formalisation, under this package's format
hypotheses, of the finite-set statement of Theorem `ode:thm:gates`,
time-dependent part, with finite-set synthesis as a hypothesis, including the per-trial claim). The
protocol `nprotocol (synthPrep hS (ν/3) (tnprepC p UJg nd ar loadC wpC)) (2g)` has the released
counts of `GateSynthTrials.native_ode_time_solver_trials`; for every instance as in
`native_ode_time_solver_certified` it has the guarantees `NOutcome`: every successful trial
within `ε/500` of `x(T)/‖x(T)‖` up to a phase, success probability at least `2/3`, conditional
output within trace distance `ε`. -/
theorem native_ode_time_solver_certified_trials (hS : Synthesis 𝒢 X len) (hadj : AdjClosed 𝒢)
    (hzt : zeroTestKinds ⊆ 𝒢) (p : TParams) (hp : p.PublicOK)
    (UJg : List (Gate (Fin p.a ⊕ S))) (hUJg : ∀ g ∈ UJg, GateOK 3 g)
    (nd : NativeOp (TSel p.m p.l p.m) (Fin p.a ⊕ S) Z Y J) (hnd : nd.Public)
    (ar : Arith (NB (TSel p.m p.l p.m) (Fin p.a ⊕ S) Z)) (ζ : ℝ) (hζ : 0 ≤ ζ)
    (har : ArithOK ar (Sum.inl (Sum.inr nd.o)) nd.dec ζ)
    (loadC : List (NInstr ((Fin (p.m + 1) ⊕ S) ⊕ Zs) Y J)) (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (p.m + 1) ⊕ Zs) Y J)) (hwpV : ∀ i ∈ wpC, i.Valid) :
    (∀ j, (∀ i ∈ trialN (synthPrep hS (p.nu / 3) (tnprepC p UJg nd ar loadC wpC)) j,
        i.Valid) ∧
      ∀ g, NInstr.gate g ∈ trialN (synthPrep hS (p.nu / 3) (tnprepC p UJg nd ar loadC wpC)) j →
        GateOf 𝒢 g) ∧
    nGatesN (tnprepC p UJg nd ar loadC wpC) ≤ p.prepGates + 84 * p.d * UJg.length +
      6 * p.d * privGates nd ar + nGatesN loadC + 2 * nGatesN wpC ∧
    (∀ q : J → Bool, nCallsN q (tnprepC p UJg nd ar loadC wpC) ≤
      12 * p.d * nCallsN q nd.V + nCallsN q loadC + 2 * nCallsN q wpC) ∧
    nGatesN (synthPrep hS (p.nu / 3) (tnprepC p UJg nd ar loadC wpC)) ≤
      nGatesN (tnprepC p UJg nd ar loadC wpC) *
        len (p.nu / 3 / (nGatesN (tnprepC p UJg nd ar loadC wpC) + 1)) ∧
    (∀ q : J → Bool, nCallsN q (synthPrep hS (p.nu / 3) (tnprepC p UJg nd ar loadC wpC)) =
      nCallsN q (tnprepC p UJg nd ar loadC wpC)) ∧
    (∀ q : J → Bool,
      ((nprotocol (synthPrep hS (p.nu / 3) (tnprepC p UJg nd ar loadC wpC)) p.ratio
        (p.ratio_ge hp.g_ge)).worstCost (wCallN q) : ℝ) ≤
        40 * p.ratio * nCallsN q (tnprepC p UJg nd ar loadC wpC)) ∧
    ((nprotocol (synthPrep hS (p.nu / 3) (tnprepC p UJg nd ar loadC wpC)) p.ratio
        (p.ratio_ge hp.g_ge)).worstCost wGateN : ℝ) ≤
      40 * p.ratio * nGatesN (synthPrep hS (p.nu / 3) (tnprepC p UJg nd ar loadC wpC)) +
        20 * p.ratio * (4 * (Fintype.card p.W + Fintype.card (XW Z ar.bT ar.bP ar.A) +
          Fintype.card (SX Zs (tnPool p S Zs Z ar.bT ar.bP ar.A) X) + Fintype.card S) + 3) ∧
    (∀ c₀ c₁ : ℝ, 0 ≤ c₀ → 0 ≤ c₁ →
      (∀ ζ' : ℝ, 0 < ζ' → ζ' ≤ 1 → (len ζ' : ℝ) ≤ c₁ * Real.log (1 / ζ') + c₀) →
      ((nprotocol (synthPrep hS (p.nu / 3) (tnprepC p UJg nd ar loadC wpC)) p.ratio
          (p.ratio_ge hp.g_ge)).worstCost wGateN : ℝ) ≤
        40 * p.ratio * (nGatesN (tnprepC p UJg nd ar loadC wpC) *
          (c₁ * Real.log ((nGatesN (tnprepC p UJg nd ar loadC wpC) + 1) / (p.nu / 3)) + c₀)) +
        20 * p.ratio * (4 * (Fintype.card p.W + Fintype.card (XW Z ar.bT ar.bP ar.A) +
          Fintype.card (SX Zs (tnPool p S Zs Z ar.bT ar.bP ar.A) X) + Fintype.card S) + 3)) ∧
    Fintype.card (STW p S Zs Z ar.bT ar.bP ar.A X) =
      Fintype.card S + 2 * (Fintype.card p.W + (Fintype.card Z + ar.bT + ar.bP + ar.A + 3) +
        (Fintype.card Zs + 1 + tnPool p S Zs Z ar.bT ar.bP ar.A + Fintype.card X)) +
        Fintype.card S + 1 ∧
    ∀ (prim : J → Reg Y ℂ →L[ℂ] Reg Y ℂ)
      (D : Label p.m p.l → ℕ → Anc p.a (Reg S ℂ) →L[ℂ] Anc p.a (Reg S ℂ))
      (Jl : Bool × (Fin p.m → Bool) → Reg S ℂ →L[ℂ] Reg S ℂ)
      (Wp : Matrix (Cfg (Fin (p.m + 1))) (Cfg (Fin (p.m + 1))) ℂ)
      (Hs Ls : ℕ → Reg S ℂ →L[ℂ] Reg S ℂ) (G : ℕ → ℝ → Reg S ℂ →L[ℂ] Reg S ℂ)
      (b : ℕ → ℝ → Reg S ℂ) (x : ℝ → Reg S ℂ) (bs : ℕ → Reg S ℂ) (bmax ζs : ℝ),
      (∀ j, IsUnitary (prim j)) →
      NativeOK prim nd (selOp (tlabFam (P := Reg S ℂ) D false)) →
      0 ≤ ζs →
      ApproxOn CleanX (nrun prim loadC) (liftB (loadIdeal Jl)) ζs →
      ApproxOn CleanX (nrun prim wpC) (liftB (matOp Wp)) ζs →
      24 * (p.d : ℝ) * ζ + 3 * ζs ≤ p.nu →
      CoreOK p (seedV (S := S))
        (⟨UJop (R := ℂ) UJg, D, Jl, Wp⟩ : TOracles p.a p.m p.l (Reg S ℂ)) Hs Ls (x 0) bs →
      (∀ k < p.M, SolvesODE (G k) (b k) x (slotMesh p.T p.m k) (slotMesh p.T p.m (k + 1))) →
      (∀ k < p.M, ∀ u ∈ Icc (slotMesh p.T p.m k) (slotMesh p.T p.m (k + 1)),
        Accretive (G k u)) →
      (∀ k < p.M, IntervalIntegrable (G k) volume (slotMesh p.T p.m k)
        (slotMesh p.T p.m (k + 1))) →
      (∀ k < p.M, IntervalIntegrable (b k) volume (slotMesh p.T p.m k)
        (slotMesh p.T p.m (k + 1))) →
      0 ≤ bmax →
      (∀ k < p.M, ∀ u ∈ Icc (slotMesh p.T p.m k) (slotMesh p.T p.m (k + 1)), ‖b k u‖ ≤ bmax) →
      x p.T ≠ 0 → p.mass (x 0) bs ≤ p.g * ‖x p.T‖ →
      slotCertificate p Hs Ls bs G b ‖x 0‖ bmax ≤ p.ε * p.mass (x 0) bs / (2000 * p.g) →
      NOutcome (synthPrep hS (p.nu / 3) (tnprepC p UJg nd ar loadC wpC)) p.ratio p.ε
        (p.ratio_ge hp.g_ge) prim (x p.T) := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, -⟩ :=
    native_ode_time_solver_trials hS hadj hzt p hp UJg hUJg nd hnd ar ζ hζ har loadC hloadV wpC
      hwpV
  refine ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, ?_⟩
  intro prim D Jl Wp Hs Ls G b x bs bmax ζs hprim hN hζs hload hwp hbudget hCore hx hGa hGint
    hbint hbmax hb hne hbud hcert
  have herr := slot_target_error p hp.T_pos Hs Ls bs G b x bmax hbmax hx hGa hGint hbint hb
    hCore.select.selfH hCore.psd hCore.select.normH hCore.select.normL
  exact trials_outcome_of hS p hp UJg hUJg nd hnd ar ζ hζ har loadC hloadV wpC hwpV prim hprim
    ⟨UJop (R := ℂ) UJg, D, Jl, Wp⟩ rfl hN ζs hζs hload hwp hbudget Hs Ls (x 0) bs (x p.T) hCore
    ⟨hne, hbud, herr.trans hcert⟩

/-- **Native dissipative ODE solver on a nonuniform mesh over a finite gate set with exact
reflections** (partial formalisation, under this package's format hypotheses, of the finite-set
statement of Theorem `ode:thm:gates`, time-dependent part, extended by
uniform refinement to nonuniform meshes with breakpoints, with finite-set synthesis as a hypothesis,
including the per-trial claim). The protocol has the counts of
`native_ode_time_solver_certified_trials`; for every mesh and instance as in
`native_ode_time_solver_mesh` it has the guarantees `NOutcome`. -/
theorem native_ode_time_solver_mesh_trials (hS : Synthesis 𝒢 X len) (hadj : AdjClosed 𝒢)
    (hzt : zeroTestKinds ⊆ 𝒢) (p : TParams) (hp : p.PublicOK)
    (UJg : List (Gate (Fin p.a ⊕ S))) (hUJg : ∀ g ∈ UJg, GateOK 3 g)
    (nd : NativeOp (TSel p.m p.l p.m) (Fin p.a ⊕ S) Z Y J) (hnd : nd.Public)
    (ar : Arith (NB (TSel p.m p.l p.m) (Fin p.a ⊕ S) Z)) (ζ : ℝ) (hζ : 0 ≤ ζ)
    (har : ArithOK ar (Sum.inl (Sum.inr nd.o)) nd.dec ζ)
    (loadC : List (NInstr ((Fin (p.m + 1) ⊕ S) ⊕ Zs) Y J)) (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (p.m + 1) ⊕ Zs) Y J)) (hwpV : ∀ i ∈ wpC, i.Valid) :
    (∀ j, (∀ i ∈ trialN (synthPrep hS (p.nu / 3) (tnprepC p UJg nd ar loadC wpC)) j,
        i.Valid) ∧
      ∀ g, NInstr.gate g ∈ trialN (synthPrep hS (p.nu / 3) (tnprepC p UJg nd ar loadC wpC)) j →
        GateOf 𝒢 g) ∧
    nGatesN (tnprepC p UJg nd ar loadC wpC) ≤ p.prepGates + 84 * p.d * UJg.length +
      6 * p.d * privGates nd ar + nGatesN loadC + 2 * nGatesN wpC ∧
    (∀ q : J → Bool, nCallsN q (tnprepC p UJg nd ar loadC wpC) ≤
      12 * p.d * nCallsN q nd.V + nCallsN q loadC + 2 * nCallsN q wpC) ∧
    nGatesN (synthPrep hS (p.nu / 3) (tnprepC p UJg nd ar loadC wpC)) ≤
      nGatesN (tnprepC p UJg nd ar loadC wpC) *
        len (p.nu / 3 / (nGatesN (tnprepC p UJg nd ar loadC wpC) + 1)) ∧
    (∀ q : J → Bool, nCallsN q (synthPrep hS (p.nu / 3) (tnprepC p UJg nd ar loadC wpC)) =
      nCallsN q (tnprepC p UJg nd ar loadC wpC)) ∧
    (∀ q : J → Bool,
      ((nprotocol (synthPrep hS (p.nu / 3) (tnprepC p UJg nd ar loadC wpC)) p.ratio
        (p.ratio_ge hp.g_ge)).worstCost (wCallN q) : ℝ) ≤
        40 * p.ratio * nCallsN q (tnprepC p UJg nd ar loadC wpC)) ∧
    ((nprotocol (synthPrep hS (p.nu / 3) (tnprepC p UJg nd ar loadC wpC)) p.ratio
        (p.ratio_ge hp.g_ge)).worstCost wGateN : ℝ) ≤
      40 * p.ratio * nGatesN (synthPrep hS (p.nu / 3) (tnprepC p UJg nd ar loadC wpC)) +
        20 * p.ratio * (4 * (Fintype.card p.W + Fintype.card (XW Z ar.bT ar.bP ar.A) +
          Fintype.card (SX Zs (tnPool p S Zs Z ar.bT ar.bP ar.A) X) + Fintype.card S) + 3) ∧
    (∀ c₀ c₁ : ℝ, 0 ≤ c₀ → 0 ≤ c₁ →
      (∀ ζ' : ℝ, 0 < ζ' → ζ' ≤ 1 → (len ζ' : ℝ) ≤ c₁ * Real.log (1 / ζ') + c₀) →
      ((nprotocol (synthPrep hS (p.nu / 3) (tnprepC p UJg nd ar loadC wpC)) p.ratio
          (p.ratio_ge hp.g_ge)).worstCost wGateN : ℝ) ≤
        40 * p.ratio * (nGatesN (tnprepC p UJg nd ar loadC wpC) *
          (c₁ * Real.log ((nGatesN (tnprepC p UJg nd ar loadC wpC) + 1) / (p.nu / 3)) + c₀)) +
        20 * p.ratio * (4 * (Fintype.card p.W + Fintype.card (XW Z ar.bT ar.bP ar.A) +
          Fintype.card (SX Zs (tnPool p S Zs Z ar.bT ar.bP ar.A) X) + Fintype.card S) + 3)) ∧
    Fintype.card (STW p S Zs Z ar.bT ar.bP ar.A X) =
      Fintype.card S + 2 * (Fintype.card p.W + (Fintype.card Z + ar.bT + ar.bP + ar.A + 3) +
        (Fintype.card Zs + 1 + tnPool p S Zs Z ar.bT ar.bP ar.A + Fintype.card X)) +
        Fintype.card S + 1 ∧
    ∀ (tm : ℕ → ℝ) (Mm : ℕ), 0 < Mm → IsMesh tm Mm p.T →
    ∀ (prim : J → Reg Y ℂ →L[ℂ] Reg Y ℂ)
      (D : Label p.m p.l → ℕ → Anc p.a (Reg S ℂ) →L[ℂ] Anc p.a (Reg S ℂ))
      (Jl : Bool × (Fin p.m → Bool) → Reg S ℂ →L[ℂ] Reg S ℂ)
      (Wp : Matrix (Cfg (Fin (p.m + 1))) (Cfg (Fin (p.m + 1))) ℂ)
      (Hm Lm : ℕ → Reg S ℂ →L[ℂ] Reg S ℂ) (bm : ℕ → Reg S ℂ)
      (G : ℕ → ℝ → Reg S ℂ →L[ℂ] Reg S ℂ) (b : ℕ → ℝ → Reg S ℂ) (x : ℝ → Reg S ℂ)
      (bmax ζs : ℝ),
      (∀ j, IsUnitary (prim j)) →
      NativeOK prim nd (selOp (tlabFam (P := Reg S ℂ) D false)) →
      0 ≤ ζs →
      ApproxOn CleanX (nrun prim loadC) (liftB (loadIdeal Jl)) ζs →
      ApproxOn CleanX (nrun prim wpC) (liftB (matOp Wp)) ζs →
      24 * (p.d : ℝ) * ζ + 3 * ζs ≤ p.nu →
      CoreOK p (seedV (S := S))
        (⟨UJop (R := ℂ) UJg, D, Jl, Wp⟩ : TOracles p.a p.m p.l (Reg S ℂ))
        (fun k => Hm (slotPiece tm p.T p.M Mm k)) (fun k => Lm (slotPiece tm p.T p.M Mm k))
        (x 0) (fun k => bm (slotPiece tm p.T p.M Mm k)) →
      (∀ q < Mm, star (Hm q) = Hm q) →
      (∀ q < Mm, ∀ w : Reg S ℂ, 0 ≤ (inner ℂ w (Lm q w)).re) →
      (∀ q < Mm, ‖Hm q‖ ≤ p.lamH) → (∀ q < Mm, ‖Lm q‖ ≤ p.lamD) →
      (∀ q < Mm, SolvesODE (G q) (b q) x (tm q) (tm (q + 1))) →
      (∀ q < Mm, ∀ u ∈ Icc (tm q) (tm (q + 1)), Accretive (G q u)) →
      (∀ q < Mm, IntervalIntegrable (G q) volume (tm q) (tm (q + 1))) →
      (∀ q < Mm, IntervalIntegrable (b q) volume (tm q) (tm (q + 1))) →
      0 ≤ bmax →
      (∀ q < Mm, ∀ u ∈ Icc (tm q) (tm (q + 1)), ‖b q u‖ ≤ bmax) →
      x p.T ≠ 0 →
      p.mass (x 0) (fun k => bm (slotPiece tm p.T p.M Mm k)) ≤ p.g * ‖x p.T‖ →
      meshCertificate p tm Mm Hm Lm bm G b ‖x 0‖ bmax ≤
        p.ε * p.mass (x 0) (fun k => bm (slotPiece tm p.T p.M Mm k)) / (2000 * p.g) →
      NOutcome (synthPrep hS (p.nu / 3) (tnprepC p UJg nd ar loadC wpC)) p.ratio p.ε
        (p.ratio_ge hp.g_ge) prim (x p.T) := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, -⟩ :=
    native_ode_time_solver_trials hS hadj hzt p hp UJg hUJg nd hnd ar ζ hζ har loadC hloadV wpC
      hwpV
  refine ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, ?_⟩
  intro tm Mm hMm hmesh prim D Jl Wp Hm Lm bm G b x bmax ζs hprim hN hζs hload hwp hbudget hCore
    hH hPSD hHn hLn hx hGa hGint hbint hbmax hb hne hbud hcert
  have herr := mesh_target_error p hp.T_pos (add_nonneg hp.lamH_nonneg hp.lamD_nonneg) tm Mm hMm
    hmesh Hm Lm bm hH hPSD hHn hLn G b x bmax hbmax hx hGa hGint hbint hb
  exact trials_outcome_of hS p hp UJg hUJg nd hnd ar ζ hζ har loadC hloadV wpC hwpV prim hprim
    ⟨UJop (R := ℂ) UJg, D, Jl, Wp⟩ rfl hN ζs hζs hload hwp hbudget _ _ (x 0) _ (x p.T) hCore
    ⟨hne, hbud, herr.trans hcert⟩

end Native

section Binary

variable {X n : Type*} [Fintype n] [DecidableEq n] {Zs : Type*} [Fintype Zs] [DecidableEq Zs]
variable {Xa : Type*} [Fintype Xa] [DecidableEq Xa] {𝒢 : Set Kind} {len : ℝ → ℕ}

/-- **Dissipative ODE solver from time-indexed binary sparse data under the integrated
certificate on the uniform slots over a finite gate set with exact reflections** (partial
formalisation, under this package's format hypotheses, of the finite-set statement of Theorem
`ode:thm:gates`, time-dependent part, with finite-set synthesis as a hypothesis,
including the per-trial claim). The protocol
`nprotocol (synthPrep hS (ν/3) (q.prep loadC wpC)) (2g)` has the released counts of
`GateSynthTrials.binary_ode_time_solver_trials`; for every input and instance as in
`binary_ode_time_solver_certified` it has the guarantees `NOutcome`. -/
theorem binary_ode_time_solver_certified_trials (hS : Synthesis 𝒢 Xa len) (hadj : AdjClosed 𝒢)
    (hzt : zeroTestKinds ⊆ 𝒢) (q : PubT) (hq : q.OK)
    (D : Data (X × Fin (2 ^ q.m)) n (Cfg (VW q.b)) q.s) (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (hdec : ∀ e z, D.decode e z = (q.c0 : ℂ) * gauss z)
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b)
      Query)) (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b) Query))
    (hwpV : ∀ i ∈ wpC, i.Valid) :
    (∀ j, (∀ i ∈ trialN (synthPrep hS (q.params.nu / 3) (q.prep loadC wpC)) j, i.Valid) ∧
      ∀ g, NInstr.gate g ∈ trialN (synthPrep hS (q.params.nu / 3) (q.prep loadC wpC)) j →
        GateOf 𝒢 g) ∧
    nGatesN (q.prep loadC wpC) ≤ q.params.prepGates + 84 * q.params.d * (q.σ + 3) +
      6 * q.params.d * (2 * (28 * q.kx + 2) + 2 * q.ar.circ.length +
        (2 * q.ar.bP + q.ar.bT + 1)) + nGatesN loadC + 2 * nGatesN wpC ∧
    (∀ c : Query → Bool, nCallsN c (q.prep loadC wpC) ≤
      12 * q.params.d * (2 * (if c Query.rowLocation then 1 else 0) +
        2 * (if c Query.columnLocation then 1 else 0) + 2 * (if c Query.value then 1 else 0)) +
        nCallsN c loadC + 2 * nCallsN c wpC) ∧
    nGatesN (synthPrep hS (q.params.nu / 3) (q.prep loadC wpC)) ≤
      nGatesN (q.prep loadC wpC) * len (q.params.nu / 3 / (nGatesN (q.prep loadC wpC) + 1)) ∧
    (∀ c : Query → Bool, nCallsN c (synthPrep hS (q.params.nu / 3) (q.prep loadC wpC)) =
      nCallsN c (q.prep loadC wpC)) ∧
    (∀ c : Query → Bool,
      ((nprotocol (synthPrep hS (q.params.nu / 3) (q.prep loadC wpC)) q.params.ratio
        (q.params.ratio_ge hq.g_ge)).worstCost (wCallN c) : ℝ) ≤
        40 * q.params.ratio * nCallsN c (q.prep loadC wpC)) ∧
    ((nprotocol (synthPrep hS (q.params.nu / 3) (q.prep loadC wpC)) q.params.ratio
        (q.params.ratio_ge hq.g_ge)).worstCost wGateN : ℝ) ≤
      40 * q.params.ratio * nGatesN (synthPrep hS (q.params.nu / 3) (q.prep loadC wpC)) +
        20 * q.params.ratio * (4 * (Fintype.card q.params.W +
          Fintype.card (XW (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) +
          Fintype.card (SX Zs (tnPool q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP
            q.ar.A) Xa) + q.kx) + 3) ∧
    (∀ c₀ c₁ : ℝ, 0 ≤ c₀ → 0 ≤ c₁ →
      (∀ ζ' : ℝ, 0 < ζ' → ζ' ≤ 1 → (len ζ' : ℝ) ≤ c₁ * Real.log (1 / ζ') + c₀) →
      ((nprotocol (synthPrep hS (q.params.nu / 3) (q.prep loadC wpC)) q.params.ratio
          (q.params.ratio_ge hq.g_ge)).worstCost wGateN : ℝ) ≤
        40 * q.params.ratio * (nGatesN (q.prep loadC wpC) *
          (c₁ * Real.log ((nGatesN (q.prep loadC wpC) + 1) / (q.params.nu / 3)) + c₀)) +
        20 * q.params.ratio * (4 * (Fintype.card q.params.W +
          Fintype.card (XW (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) +
          Fintype.card (SX Zs (tnPool q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP
            q.ar.A) Xa) + q.kx) + 3)) ∧
    Fintype.card (STW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A Xa) =
      q.kx + 2 * (Fintype.card q.params.W +
        (6 * q.kx + 4 * q.b + q.ar.bT + q.ar.bP + q.ar.A + 3) +
        (Fintype.card Zs + 1 + tnPool q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A +
          Fintype.card Xa)) + q.kx + 1 ∧
    ∀ x : X,
      (∀ r i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaH ^ 2) →
      (∀ r j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaH ^ 2) →
      (∀ r i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaD ^ 2) →
      (∀ r j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaD ^ 2) →
      (∀ r, ∀ w : EuclideanSpace ℂ n, 0 ≤ (inner ℂ w (SparseStateOverlap.matrixOperator
        (ODEMatrixEnergy.dissipativePart (D.matrix (x, r))) w)).re) →
      ∀ (Jl : Bool × (Fin q.m → Bool) → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
        (Wp : Matrix (Cfg (Fin (q.m + 1))) (Cfg (Fin (q.m + 1))) ℂ)
        (G : ℕ → ℝ → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ) (bf : ℕ → ℝ → Reg (Fin q.kx) ℂ)
        (xs : ℝ → Reg (Fin q.kx) ℂ) (bs : ℕ → Reg (Fin q.kx) ℂ) (bmax ζs : ℝ),
      0 ≤ ζs →
      ApproxOn CleanX (nrun (primsT (R := ℂ) D en x) loadC) (liftB (loadIdeal Jl)) ζs →
      ApproxOn CleanX (nrun (primsT (R := ℂ) D en x) wpC) (liftB (matOp Wp)) ζs →
      24 * (q.params.d : ℝ) * q.ζ + 3 * ζs ≤ q.params.nu →
      SourceOK q.params (seedV (S := Fin q.kx)) Jl Wp (xs 0) bs →
      (∀ k < q.params.M, SolvesODE (G k) (bf k) xs (slotMesh q.T q.m k)
        (slotMesh q.T q.m (k + 1))) →
      (∀ k < q.params.M, ∀ u ∈ Icc (slotMesh q.T q.m k) (slotMesh q.T q.m (k + 1)),
        Accretive (G k u)) →
      (∀ k < q.params.M, IntervalIntegrable (G k) volume (slotMesh q.T q.m k)
        (slotMesh q.T q.m (k + 1))) →
      (∀ k < q.params.M, IntervalIntegrable (bf k) volume (slotMesh q.T q.m k)
        (slotMesh q.T q.m (k + 1))) →
      0 ≤ bmax →
      (∀ k < q.params.M, ∀ u ∈ Icc (slotMesh q.T q.m k) (slotMesh q.T q.m (k + 1)),
        ‖bf k u‖ ≤ bmax) →
      xs q.T ≠ 0 → q.params.mass (xs 0) bs ≤ q.g * ‖xs q.T‖ →
      slotCertificate q.params (GateBinaryODETime.HsT D en x) (GateBinaryODETime.LsT D en x) bs G
        bf ‖xs 0‖ bmax ≤
        q.ε * q.params.mass (xs 0) bs / (2000 * q.g) →
      NOutcome (synthPrep hS (q.params.nu / 3) (q.prep loadC wpC)) q.params.ratio q.ε
        (q.params.ratio_ge hq.g_ge) (primsT (R := ℂ) D en x) (xs q.T) := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, -⟩ :=
    binary_ode_time_solver_trials hS hadj hzt q hq D en hrange hdec loadC hloadV wpC hwpV
  refine ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, ?_⟩
  intro x hrH hcH hrD hcD hPSD Jl Wp G bf xs bs bmax ζs hζs hload hwp hbud hS' hx hGa hGint
    hbint hbmax hb hne hB hcert
  have hp := q.params_ok hq
  have hCore := binary_coreOK q hq D en hrange x hrH hcH hrD hcD hPSD Jl Wp (xs 0) bs hS'
  have herr := slot_target_error q.params hp.T_pos (GateBinaryODETime.HsT D en x)
    (GateBinaryODETime.LsT D en x) bs G bf xs bmax
    hbmax hx hGa hGint hbint hb hCore.select.selfH hCore.psd hCore.select.normH
    hCore.select.normL
  exact trials_outcome_of hS q.params hp q.UJg (hadUJ4_ok q.σ q.hσ) q.nd q.nd_public q.ar q.ζ
    hq.ζ_pos.le (q.ar_ok hq) loadC hloadV wpC hwpV (primsT (R := ℂ) D en x)
    (primsT_isUnitary D en x) ⟨UJop (R := ℂ) q.UJg, privFamT q.params D en x q.rho q.γ, Jl, Wp⟩
    rfl (q.nativeOK hq D en hrange hdec x) ζs hζs hload hwp hbud _ _ (xs 0) bs (xs q.T) hCore
    ⟨hne, hB, herr.trans hcert⟩

/-- **Dissipative ODE solver from binary sparse data on a nonuniform mesh over a finite gate set
with exact reflections** (partial formalisation, under this package's format hypotheses, of the
finite-set statement of Theorem `ode:thm:gates`, time-dependent part,
extended by uniform refinement to nonuniform meshes with breakpoints, with finite-set synthesis as a
hypothesis, including the per-trial claim). The protocol has the counts of
`binary_ode_time_solver_certified_trials`; it runs on the clock data `clockData D_m`,
and for every input and instance as in `binary_ode_time_solver_mesh` it has the guarantees
`NOutcome`. -/
theorem binary_ode_time_solver_mesh_trials (hS : Synthesis 𝒢 Xa len) (hadj : AdjClosed 𝒢)
    (hzt : zeroTestKinds ⊆ 𝒢) (q : PubT) (hq : q.OK) {Mm : ℕ} (hMm : 0 < Mm) (tm : ℕ → ℝ)
    (hmesh : IsMesh tm Mm q.T)
    (D : Data (X × Fin Mm) n (Cfg (VW q.b)) q.s) (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (hdec : ∀ e z, D.decode e z = (q.c0 : ℂ) * gauss z)
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b)
      Query)) (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b) Query))
    (hwpV : ∀ i ∈ wpC, i.Valid) :
    (∀ j, (∀ i ∈ trialN (synthPrep hS (q.params.nu / 3) (q.prep loadC wpC)) j, i.Valid) ∧
      ∀ g, NInstr.gate g ∈ trialN (synthPrep hS (q.params.nu / 3) (q.prep loadC wpC)) j →
        GateOf 𝒢 g) ∧
    nGatesN (q.prep loadC wpC) ≤ q.params.prepGates + 84 * q.params.d * (q.σ + 3) +
      6 * q.params.d * (2 * (28 * q.kx + 2) + 2 * q.ar.circ.length +
        (2 * q.ar.bP + q.ar.bT + 1)) + nGatesN loadC + 2 * nGatesN wpC ∧
    (∀ c : Query → Bool, nCallsN c (q.prep loadC wpC) ≤
      12 * q.params.d * (2 * (if c Query.rowLocation then 1 else 0) +
        2 * (if c Query.columnLocation then 1 else 0) + 2 * (if c Query.value then 1 else 0)) +
        nCallsN c loadC + 2 * nCallsN c wpC) ∧
    nGatesN (synthPrep hS (q.params.nu / 3) (q.prep loadC wpC)) ≤
      nGatesN (q.prep loadC wpC) * len (q.params.nu / 3 / (nGatesN (q.prep loadC wpC) + 1)) ∧
    (∀ c : Query → Bool, nCallsN c (synthPrep hS (q.params.nu / 3) (q.prep loadC wpC)) =
      nCallsN c (q.prep loadC wpC)) ∧
    (∀ c : Query → Bool,
      ((nprotocol (synthPrep hS (q.params.nu / 3) (q.prep loadC wpC)) q.params.ratio
        (q.params.ratio_ge hq.g_ge)).worstCost (wCallN c) : ℝ) ≤
        40 * q.params.ratio * nCallsN c (q.prep loadC wpC)) ∧
    ((nprotocol (synthPrep hS (q.params.nu / 3) (q.prep loadC wpC)) q.params.ratio
        (q.params.ratio_ge hq.g_ge)).worstCost wGateN : ℝ) ≤
      40 * q.params.ratio * nGatesN (synthPrep hS (q.params.nu / 3) (q.prep loadC wpC)) +
        20 * q.params.ratio * (4 * (Fintype.card q.params.W +
          Fintype.card (XW (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) +
          Fintype.card (SX Zs (tnPool q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP
            q.ar.A) Xa) + q.kx) + 3) ∧
    (∀ c₀ c₁ : ℝ, 0 ≤ c₀ → 0 ≤ c₁ →
      (∀ ζ' : ℝ, 0 < ζ' → ζ' ≤ 1 → (len ζ' : ℝ) ≤ c₁ * Real.log (1 / ζ') + c₀) →
      ((nprotocol (synthPrep hS (q.params.nu / 3) (q.prep loadC wpC)) q.params.ratio
          (q.params.ratio_ge hq.g_ge)).worstCost wGateN : ℝ) ≤
        40 * q.params.ratio * (nGatesN (q.prep loadC wpC) *
          (c₁ * Real.log ((nGatesN (q.prep loadC wpC) + 1) / (q.params.nu / 3)) + c₀)) +
        20 * q.params.ratio * (4 * (Fintype.card q.params.W +
          Fintype.card (XW (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) +
          Fintype.card (SX Zs (tnPool q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP
            q.ar.A) Xa) + q.kx) + 3)) ∧
    Fintype.card (STW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A Xa) =
      q.kx + 2 * (Fintype.card q.params.W +
        (6 * q.kx + 4 * q.b + q.ar.bT + q.ar.bP + q.ar.A + 3) +
        (Fintype.card Zs + 1 + tnPool q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A +
          Fintype.card Xa)) + q.kx + 1 ∧
    ∀ x : X,
      (∀ r i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaH ^ 2) →
      (∀ r j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaH ^ 2) →
      (∀ r i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaD ^ 2) →
      (∀ r j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaD ^ 2) →
      (∀ r, ∀ w : EuclideanSpace ℂ n, 0 ≤ (inner ℂ w (SparseStateOverlap.matrixOperator
        (ODEMatrixEnergy.dissipativePart (D.matrix (x, r))) w)).re) →
      ∀ (Jl : Bool × (Fin q.m → Bool) → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
        (Wp : Matrix (Cfg (Fin (q.m + 1))) (Cfg (Fin (q.m + 1))) ℂ)
        (G : ℕ → ℝ → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ) (bf : ℕ → ℝ → Reg (Fin q.kx) ℂ)
        (xs : ℝ → Reg (Fin q.kx) ℂ) (bm : ℕ → Reg (Fin q.kx) ℂ) (bmax ζs : ℝ),
      0 ≤ ζs →
      ApproxOn CleanX (nrun (primsT (R := ℂ) (clockData D hMm tm q.T q.m) en x) loadC)
        (liftB (loadIdeal Jl)) ζs →
      ApproxOn CleanX (nrun (primsT (R := ℂ) (clockData D hMm tm q.T q.m) en x) wpC)
        (liftB (matOp Wp)) ζs →
      24 * (q.params.d : ℝ) * q.ζ + 3 * ζs ≤ q.params.nu →
      SourceOK q.params (seedV (S := Fin q.kx)) Jl Wp (xs 0)
        (fun k => bm (slotPiece tm q.T (2 ^ q.m) Mm k)) →
      (∀ r < Mm, SolvesODE (G r) (bf r) xs (tm r) (tm (r + 1))) →
      (∀ r < Mm, ∀ u ∈ Icc (tm r) (tm (r + 1)), Accretive (G r u)) →
      (∀ r < Mm, IntervalIntegrable (G r) volume (tm r) (tm (r + 1))) →
      (∀ r < Mm, IntervalIntegrable (bf r) volume (tm r) (tm (r + 1))) →
      0 ≤ bmax →
      (∀ r < Mm, ∀ u ∈ Icc (tm r) (tm (r + 1)), ‖bf r u‖ ≤ bmax) →
      xs q.T ≠ 0 →
      q.params.mass (xs 0) (fun k => bm (slotPiece tm q.T (2 ^ q.m) Mm k)) ≤ q.g * ‖xs q.T‖ →
      meshCertificate q.params tm Mm (meshH D en x) (meshL D en x) bm G bf ‖xs 0‖ bmax ≤
        q.ε * q.params.mass (xs 0) (fun k => bm (slotPiece tm q.T (2 ^ q.m) Mm k)) /
          (2000 * q.g) →
      NOutcome (synthPrep hS (q.params.nu / 3) (q.prep loadC wpC)) q.params.ratio q.ε
        (q.params.ratio_ge hq.g_ge) (primsT (R := ℂ) (clockData D hMm tm q.T q.m) en x)
        (xs q.T) := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, -⟩ :=
    binary_ode_time_solver_trials hS hadj hzt q hq (clockData D hMm tm q.T q.m) en hrange hdec
      loadC hloadV wpC hwpV
  refine ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, ?_⟩
  intro x hrH hcH hrD hcD hPSD Jl Wp G bf xs bm bmax ζs hζs hload hwp hbud hS' hx hGa hGint
    hbint hbmax hb hne hB hcert
  have hp := q.params_ok hq
  set Dc : Data (X × Fin (2 ^ q.m)) n (Cfg (VW q.b)) q.s := clockData D hMm tm q.T q.m with hDc
  have hrangeC : ∀ j : n, (∃ m, Dc.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u) :=
    hrange
  have hdecC : ∀ e z, Dc.decode e z = (q.c0 : ℂ) * gauss z := hdec
  have hCore := binary_coreOK q hq Dc en hrangeC x (fun _ => hrH _) (fun _ => hcH _)
    (fun _ => hrD _) (fun _ => hcD _) (fun _ => hPSD _) Jl Wp (xs 0)
    (fun k => bm (slotPiece tm q.T (2 ^ q.m) Mm k)) hS'
  have hTarget := binary_mesh_targetOK q hq hMm tm hmesh D en hrange x hrH hcH hrD hcD hPSD G bf
    xs bm bmax hx hGa hGint hbint hbmax hb hne hB hcert
  exact trials_outcome_of hS q.params hp q.UJg (hadUJ4_ok q.σ q.hσ) q.nd q.nd_public q.ar q.ζ
    hq.ζ_pos.le (q.ar_ok hq) loadC hloadV wpC hwpV (primsT (R := ℂ) Dc en x)
    (primsT_isUnitary Dc en x) ⟨UJop (R := ℂ) q.UJg, privFamT q.params Dc en x q.rho q.γ, Jl, Wp⟩
    rfl (q.nativeOK hq Dc en hrangeC hdecC x) ζs hζs hload hwp hbud _ _ (xs 0) _ (xs q.T) hCore
    hTarget

/-- **The gate, call and qubit budget over a finite gate set under the integrated certificate on
the uniform slots** (partial formalisation, under this package's format hypotheses, of the
finite-set statement of Theorem `ode:thm:gates`, time-dependent part, equations
`ode:eq:gate-main` and `ode:eq:gate-space` over a finite gate set). Under `Synthesis 𝒢 Xa len` with
`len ζ ≤ c₁ log(1/ζ) + c₀` on `(0, 1]`, `AdjClosed 𝒢` and `zeroTestKinds ⊆ 𝒢`, for the public
data `q` with `γ = gammaOf T η_H η_D (2g) (ε/2)` and `q* = qOf s T η_H η_D (2g) (ε/2)`, the
protocol `nprotocol (synthPrep hS (ν/3) (q.prep loadC wpC)) (2g)` has the released budget of
`GateODEBudget.binary_ode_time_budget_trials` (one native preparation at most
`B = prepBoundT q loadC wpC` gates; in every history at most
`80 g B (c₁ log((B+1)/(ν/3)) + c₀) + 40 g (4 n + 3)` gates of `𝒢` and at most `7864320 g q*`
calls of each coherent sampled-time oracle besides the source calls; the stated qubits), and for
every input and instance as in `binary_ode_time_solver_certified` with
`98304 q* ζ + 3 ζs ≤ ν` it has the guarantees `NOutcome`. -/
theorem binary_ode_time_budget_certified_trials (hS : Synthesis 𝒢 Xa len) (hadj : AdjClosed 𝒢)
    (hzt : zeroTestKinds ⊆ 𝒢) {c₀ c₁ : ℝ} (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁)
    (hlen : ∀ ζ' : ℝ, 0 < ζ' → ζ' ≤ 1 → (len ζ' : ℝ) ≤ c₁ * Real.log (1 / ζ') + c₀)
    (q : PubT) (hq : q.OK) (hγ : q.γ = gammaOf q.T q.etaH q.etaD (2 * q.g) (q.ε / 2))
    (D : Data (X × Fin (2 ^ q.m)) n (Cfg (VW q.b)) q.s) (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (hdec : ∀ e z, D.decode e z = (q.c0 : ℂ) * gauss z)
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b)
      Query)) (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b) Query))
    (hwpV : ∀ i ∈ wpC, i.Valid) :
    (∀ j, (∀ i ∈ trialN (synthPrep hS (q.params.nu / 3) (q.prep loadC wpC)) j, i.Valid) ∧
      ∀ g, NInstr.gate g ∈ trialN (synthPrep hS (q.params.nu / 3) (q.prep loadC wpC)) j →
        GateOf 𝒢 g) ∧
    (nGatesN (q.prep loadC wpC) : ℝ) ≤ prepBoundT q loadC wpC ∧
    ((nprotocol (synthPrep hS (q.params.nu / 3) (q.prep loadC wpC)) q.params.ratio
        (q.params.ratio_ge hq.g_ge)).worstCost wGateN : ℝ) ≤
      80 * q.g * (prepBoundT q loadC wpC *
        (c₁ * Real.log ((prepBoundT q loadC wpC + 1) / (q.params.nu / 3)) + c₀)) +
      40 * q.g * (4 * ((22 * q.kx + 16 * q.params.m + 24 * q.params.r + 4 * q.params.l +
        8 * q.b + 2 * (q.ar.bT + q.ar.bP + q.ar.A) + 2 * Fintype.card Zs +
        Fintype.card Xa + 47 : ℕ) : ℝ) + 3) ∧
    (∀ c : Query → Bool,
      ((nprotocol (synthPrep hS (q.params.nu / 3) (q.prep loadC wpC)) q.params.ratio
        (q.params.ratio_ge hq.g_ge)).worstCost (wCallN c) : ℝ) ≤
      7864320 * q.g * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
          ((if c Query.rowLocation then 1 else 0) + (if c Query.columnLocation then 1 else 0) +
            (if c Query.value then 1 else 0)) +
        80 * q.g * ((nCallsN c loadC : ℝ) + 2 * nCallsN c wpC)) ∧
    Fintype.card (STW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A Xa) =
      44 * q.kx + 32 * q.params.m + 48 * q.params.r + 8 * q.params.l + 16 * q.b +
        4 * (q.ar.bT + q.ar.bP + q.ar.A) + 4 * Fintype.card Zs + 2 * Fintype.card Xa + 95 ∧
    ∀ x : X,
      (∀ r i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaH ^ 2) →
      (∀ r j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaH ^ 2) →
      (∀ r i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaD ^ 2) →
      (∀ r j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaD ^ 2) →
      (∀ r, ∀ w : EuclideanSpace ℂ n, 0 ≤ (inner ℂ w (SparseStateOverlap.matrixOperator
        (ODEMatrixEnergy.dissipativePart (D.matrix (x, r))) w)).re) →
      ∀ (Jl : Bool × (Fin q.m → Bool) → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
        (Wp : Matrix (Cfg (Fin (q.m + 1))) (Cfg (Fin (q.m + 1))) ℂ)
        (G : ℕ → ℝ → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ) (bf : ℕ → ℝ → Reg (Fin q.kx) ℂ)
        (xs : ℝ → Reg (Fin q.kx) ℂ) (bs : ℕ → Reg (Fin q.kx) ℂ) (bmax ζs : ℝ),
      0 ≤ ζs →
      ApproxOn CleanX (nrun (primsT (R := ℂ) D en x) loadC) (liftB (loadIdeal Jl)) ζs →
      ApproxOn CleanX (nrun (primsT (R := ℂ) D en x) wpC) (liftB (matOp Wp)) ζs →
      98304 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * q.ζ + 3 * ζs ≤ q.params.nu →
      SourceOK q.params (seedV (S := Fin q.kx)) Jl Wp (xs 0) bs →
      (∀ k < q.params.M, SolvesODE (G k) (bf k) xs (slotMesh q.T q.m k)
        (slotMesh q.T q.m (k + 1))) →
      (∀ k < q.params.M, ∀ u ∈ Icc (slotMesh q.T q.m k) (slotMesh q.T q.m (k + 1)),
        Accretive (G k u)) →
      (∀ k < q.params.M, IntervalIntegrable (G k) volume (slotMesh q.T q.m k)
        (slotMesh q.T q.m (k + 1))) →
      (∀ k < q.params.M, IntervalIntegrable (bf k) volume (slotMesh q.T q.m k)
        (slotMesh q.T q.m (k + 1))) →
      0 ≤ bmax →
      (∀ k < q.params.M, ∀ u ∈ Icc (slotMesh q.T q.m k) (slotMesh q.T q.m (k + 1)),
        ‖bf k u‖ ≤ bmax) →
      xs q.T ≠ 0 → q.params.mass (xs 0) bs ≤ q.g * ‖xs q.T‖ →
      slotCertificate q.params (GateBinaryODETime.HsT D en x) (GateBinaryODETime.LsT D en x) bs
        G bf ‖xs 0‖ bmax ≤ q.ε * q.params.mass (xs 0) bs / (2000 * q.g) →
      NOutcome (synthPrep hS (q.params.nu / 3) (q.prep loadC wpC)) q.params.ratio q.ε
        (q.params.ratio_ge hq.g_ge) (primsT (R := ℂ) D en x) (xs q.T) := by
  obtain ⟨c1, c2, c3, c4, c5, -⟩ := binary_ode_time_budget_trials hS hadj hzt hc₀ hc₁ hlen q hq
    hγ D en hrange hdec loadC hloadV wpC hwpV
  obtain ⟨-, hd, -, -, -, -⟩ := binary_ode_time_sizes q hq hγ
  obtain ⟨-, -, -, -, -, -, -, -, -, hout⟩ := binary_ode_time_solver_certified_trials hS hadj hzt
    q hq D en hrange hdec loadC hloadV wpC hwpV
  refine ⟨c1, c2, c3, c4, c5, ?_⟩
  intro x hrH hcH hrD hcD hPSD Jl Wp G bf xs bs bmax ζs hζs hload hwp hbud hS' hx hGa hGint
    hbint hbmax hb hne hB hcert
  refine hout x hrH hcH hrD hcD hPSD Jl Wp G bf xs bs bmax ζs hζs hload hwp ?_ hS' hx hGa hGint
    hbint hbmax hb hne hB hcert
  have hζ := hq.ζ_pos.le
  have := mul_le_mul_of_nonneg_right hd hζ
  linarith

/-- **The gate, call and qubit budget over a finite gate set on a nonuniform mesh** (partial
formalisation, under this package's format hypotheses, of the finite-set statement of Theorem
`ode:thm:gates`, time-dependent part, equations `ode:eq:gate-main` and
`ode:eq:gate-space` over a finite gate set, extended by uniform refinement to nonuniform meshes with
breakpoints). The protocol has the budget of
`binary_ode_time_budget_certified_trials` (the mesh enters only through `m`); it runs on the
clock data `clockData D_m`, and for every input and instance as in
`binary_ode_time_solver_mesh` with `98304 q* ζ + 3 ζs ≤ ν` it has the guarantees `NOutcome`. -/
theorem binary_ode_time_budget_mesh_trials (hS : Synthesis 𝒢 Xa len) (hadj : AdjClosed 𝒢)
    (hzt : zeroTestKinds ⊆ 𝒢) {c₀ c₁ : ℝ} (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁)
    (hlen : ∀ ζ' : ℝ, 0 < ζ' → ζ' ≤ 1 → (len ζ' : ℝ) ≤ c₁ * Real.log (1 / ζ') + c₀)
    (q : PubT) (hq : q.OK) (hγ : q.γ = gammaOf q.T q.etaH q.etaD (2 * q.g) (q.ε / 2))
    {Mm : ℕ} (hMm : 0 < Mm) (tm : ℕ → ℝ) (hmesh : IsMesh tm Mm q.T)
    (D : Data (X × Fin Mm) n (Cfg (VW q.b)) q.s) (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (hdec : ∀ e z, D.decode e z = (q.c0 : ℂ) * gauss z)
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b)
      Query)) (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b) Query))
    (hwpV : ∀ i ∈ wpC, i.Valid) :
    (∀ j, (∀ i ∈ trialN (synthPrep hS (q.params.nu / 3) (q.prep loadC wpC)) j, i.Valid) ∧
      ∀ g, NInstr.gate g ∈ trialN (synthPrep hS (q.params.nu / 3) (q.prep loadC wpC)) j →
        GateOf 𝒢 g) ∧
    (nGatesN (q.prep loadC wpC) : ℝ) ≤ prepBoundT q loadC wpC ∧
    ((nprotocol (synthPrep hS (q.params.nu / 3) (q.prep loadC wpC)) q.params.ratio
        (q.params.ratio_ge hq.g_ge)).worstCost wGateN : ℝ) ≤
      80 * q.g * (prepBoundT q loadC wpC *
        (c₁ * Real.log ((prepBoundT q loadC wpC + 1) / (q.params.nu / 3)) + c₀)) +
      40 * q.g * (4 * ((22 * q.kx + 16 * q.params.m + 24 * q.params.r + 4 * q.params.l +
        8 * q.b + 2 * (q.ar.bT + q.ar.bP + q.ar.A) + 2 * Fintype.card Zs +
        Fintype.card Xa + 47 : ℕ) : ℝ) + 3) ∧
    (∀ c : Query → Bool,
      ((nprotocol (synthPrep hS (q.params.nu / 3) (q.prep loadC wpC)) q.params.ratio
        (q.params.ratio_ge hq.g_ge)).worstCost (wCallN c) : ℝ) ≤
      7864320 * q.g * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
          ((if c Query.rowLocation then 1 else 0) + (if c Query.columnLocation then 1 else 0) +
            (if c Query.value then 1 else 0)) +
        80 * q.g * ((nCallsN c loadC : ℝ) + 2 * nCallsN c wpC)) ∧
    Fintype.card (STW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A Xa) =
      44 * q.kx + 32 * q.params.m + 48 * q.params.r + 8 * q.params.l + 16 * q.b +
        4 * (q.ar.bT + q.ar.bP + q.ar.A) + 4 * Fintype.card Zs + 2 * Fintype.card Xa + 95 ∧
    ∀ x : X,
      (∀ r i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaH ^ 2) →
      (∀ r j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaH ^ 2) →
      (∀ r i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaD ^ 2) →
      (∀ r j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaD ^ 2) →
      (∀ r, ∀ w : EuclideanSpace ℂ n, 0 ≤ (inner ℂ w (SparseStateOverlap.matrixOperator
        (ODEMatrixEnergy.dissipativePart (D.matrix (x, r))) w)).re) →
      ∀ (Jl : Bool × (Fin q.m → Bool) → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
        (Wp : Matrix (Cfg (Fin (q.m + 1))) (Cfg (Fin (q.m + 1))) ℂ)
        (G : ℕ → ℝ → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ) (bf : ℕ → ℝ → Reg (Fin q.kx) ℂ)
        (xs : ℝ → Reg (Fin q.kx) ℂ) (bm : ℕ → Reg (Fin q.kx) ℂ) (bmax ζs : ℝ),
      0 ≤ ζs →
      ApproxOn CleanX (nrun (primsT (R := ℂ) (clockData D hMm tm q.T q.m) en x) loadC)
        (liftB (loadIdeal Jl)) ζs →
      ApproxOn CleanX (nrun (primsT (R := ℂ) (clockData D hMm tm q.T q.m) en x) wpC)
        (liftB (matOp Wp)) ζs →
      98304 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * q.ζ + 3 * ζs ≤ q.params.nu →
      SourceOK q.params (seedV (S := Fin q.kx)) Jl Wp (xs 0)
        (fun k => bm (slotPiece tm q.T (2 ^ q.m) Mm k)) →
      (∀ r < Mm, SolvesODE (G r) (bf r) xs (tm r) (tm (r + 1))) →
      (∀ r < Mm, ∀ u ∈ Icc (tm r) (tm (r + 1)), Accretive (G r u)) →
      (∀ r < Mm, IntervalIntegrable (G r) volume (tm r) (tm (r + 1))) →
      (∀ r < Mm, IntervalIntegrable (bf r) volume (tm r) (tm (r + 1))) →
      0 ≤ bmax →
      (∀ r < Mm, ∀ u ∈ Icc (tm r) (tm (r + 1)), ‖bf r u‖ ≤ bmax) →
      xs q.T ≠ 0 →
      q.params.mass (xs 0) (fun k => bm (slotPiece tm q.T (2 ^ q.m) Mm k)) ≤ q.g * ‖xs q.T‖ →
      meshCertificate q.params tm Mm (meshH D en x) (meshL D en x) bm G bf ‖xs 0‖ bmax ≤
        q.ε * q.params.mass (xs 0) (fun k => bm (slotPiece tm q.T (2 ^ q.m) Mm k)) /
          (2000 * q.g) →
      NOutcome (synthPrep hS (q.params.nu / 3) (q.prep loadC wpC)) q.params.ratio q.ε
        (q.params.ratio_ge hq.g_ge) (primsT (R := ℂ) (clockData D hMm tm q.T q.m) en x)
        (xs q.T) := by
  obtain ⟨c1, c2, c3, c4, c5, -⟩ := binary_ode_time_budget_trials hS hadj hzt hc₀ hc₁ hlen q hq
    hγ (clockData D hMm tm q.T q.m) en hrange hdec loadC hloadV wpC hwpV
  obtain ⟨-, hd, -, -, -, -⟩ := binary_ode_time_sizes q hq hγ
  obtain ⟨-, -, -, -, -, -, -, -, -, hout⟩ := binary_ode_time_solver_mesh_trials hS hadj hzt q hq
    hMm tm hmesh D en hrange hdec loadC hloadV wpC hwpV
  refine ⟨c1, c2, c3, c4, c5, ?_⟩
  intro x hrH hcH hrD hcD hPSD Jl Wp G bf xs bm bmax ζs hζs hload hwp hbud hS' hx hGa hGint
    hbint hbmax hb hne hB hcert
  refine hout x hrH hcH hrD hcD hPSD Jl Wp G bf xs bm bmax ζs hζs hload hwp ?_ hS' hx hGa hGint
    hbint hbmax hb hne hB hcert
  have hζ := hq.ζ_pos.le
  have := mul_le_mul_of_nonneg_right hd hζ
  linarith

end Binary

end

end SparseHamiltonian.GateMesh.ODE
