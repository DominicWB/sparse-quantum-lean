import GateEfficientMesh.ODE.Exact
import GateEfficientMesh.Native
import GateEfficientNative.ODE.Time

/-!
# The native time-dependent ODE solver under integrated certificates

The released native solver `GateNative.native_ode_time_solver` (Theorem `ode:thm:gates`,
time-dependent part, before finite-set synthesis) has its counts from the public data alone and
its guarantee `GateNative.NOutcome` for every instance satisfying the released
`GateODE.Time.TParams.InstanceOK` (Lipschitz path and released budget). Its proof
(`GateNative.native_time_outcome`) uses the instance only through the released certificate
(`prep_certificate`) and the target facts; it is reassembled here from the public lemmas
(`oprep_approx`, `tsrcMacro_approx`, `native_trial_bounds`, `noutcome_of_bounds`) with the
certificate of `prep_certificate_of`:

* `native_outcome_of`: `NOutcome` for every instance with `CoreOK` and `TargetOK`;
* `native_ode_time_solver_certified`: the released native protocol and counts, correct under the
  integrated certificate on the uniform slots (`slotCertificate ≤ ε B/(2000 g)`) for classical
  piecewise solutions with one generator and forcing piece per slot.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateMesh.ODE

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit GateNative
open MeasureTheory Set
open GateCircuit.Sim (Wire anc_injective)
open GateODE (OInstr OWire AW goodF Label labOf)
open GateODE.Time (TParams TOracles teval trun)
open GatePointerEncoding (wordEquivFin)
open ODEStateNormalization (unitDirection)
open TimeDependentODE (SolvesODE Accretive)
open scoped InnerProduct BigOperators

section Main

variable {S Zs Z Y J : Type*} [Fintype S] [DecidableEq S] [Fintype Zs] [DecidableEq Zs]
  [Fintype Z] [DecidableEq Z] [Fintype Y] [DecidableEq Y]

/-- **The guarantees of the native time-dependent solver for one instance**, from the conditions
on the supplied unitaries (`CoreOK`) and on the final state (`TargetOK`), with native
implementations of the private operation (`NativeOK`, `ArithOK`), of the loading and of the
weight preparation (within `ζs`) and the budget `24 d ζ + 3 ζs ≤ ν`. -/
theorem native_outcome_of (p : TParams) (hp : p.PublicOK)
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
    NOutcome (tnprepC p UJg nd ar loadC wpC) p.ratio p.ε (p.ratio_ge hp.g_ge) prim xT := by
  obtain ⟨cP, -, cSF, cST, -, -⟩ := p.prepC_counts hp.tau_pos.le hp.nu_pos hp.mesh
  have hvalid := p.prepC_valid hp.tau_pos.le hp.nu_pos hp.mesh
  have hprepV := tnprepC_valid p hp UJg hUJg nd hnd ar har loadC hloadV wpC hwpV
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
  have hUN : IsUnitary (nrun prim (tnprepC p UJg nd ar loadC wpC)) :=
    nrun_isUnitary prim hprim _ hprepV
  have hnP : Fintype.card (AW p.a p.m p.r p.K p.m p.l p.f) +
      Fintype.card (XW Z ar.bT ar.bP ar.A) + Fintype.card Zs + Fintype.card S ≤
      tnPool p S Zs Z ar.bT ar.bP ar.A + 1 := Nat.le_succ _
  have hne := hT.ne
  generalize trun (seedV (S := S)) σ p.prepC = Urel at h hA'
  generalize p.target Hs Ls x0 bs = y at h hy hbud hdirY hNorm
  have hbud' : p.mass x0 bs ≤ p.ratio * ‖y‖ := hbud
  have hdirY' : ‖unitDirection y - unitDirection xT‖ ≤ p.ε / 1000 := hdirY
  obtain ⟨-, -, hmean, hdir⟩ := native_trial_bounds prim hnP (tnprepC p UJg nd ar loadC wpC) hUN
    (tnprepC_pres p UJg nd ar loadC wpC prim) Urel hA' y (p.mass x0 bs) p.ratio p.acc hy
    (p.ratio_ge hp.g_ge) (p.acc_pos hp.ε_pos) hacc hNorm hbud' h le_rfl
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

/-- **Native gate-efficient dissipative ODE solver under the integrated certificate on the
uniform slots** (Theorem `ode:thm:gates`, time-dependent part, before finite-set synthesis:
"more generally, a certificate for the same uniform meshes suffices").

The native protocol `nprotocol (tnprepC p UJg nd ar loadC wpC) (2g)` depends only on the public
data and has the released validity, gate, call and qubit counts of
`GateNative.native_ode_time_solver`. For every instance with unitary primitive oracles, the
label- and slot-selected private operations `D z r` given natively by `V` (`NativeOK`), a loading
`J s` and a weight preparation `Wp` approximated by the supplied circuits within `ζs`, the budget
`24 d ζ + 3 ζs ≤ ν`, the conditions `CoreOK` on the supplied unitaries and samples, and every
classical piecewise solution on the uniform slots with accretive, interval-integrable generator
pieces and interval-integrable forcing pieces bounded by `b_max ≥ 0`, with `x(T) ≠ 0`,
`B ≤ g ‖x(T)‖` and `slotCertificate ≤ ε B/(2000 g)`, the protocol has the released guarantees
`NOutcome`: success probability at least `2/3`, every successful trial within `ε/500` of
`x(T)/‖x(T)‖` up to a phase, and conditional output within trace distance `ε`. -/
theorem native_ode_time_solver_certified (p : TParams) (hp : p.PublicOK)
    (UJg : List (Gate (Fin p.a ⊕ S))) (hUJg : ∀ g ∈ UJg, GateOK 3 g)
    (nd : NativeOp (TSel p.m p.l p.m) (Fin p.a ⊕ S) Z Y J) (hnd : nd.Public)
    (ar : Arith (NB (TSel p.m p.l p.m) (Fin p.a ⊕ S) Z)) (ζ : ℝ) (hζ : 0 ≤ ζ)
    (har : ArithOK ar (Sum.inl (Sum.inr nd.o)) nd.dec ζ)
    (loadC : List (NInstr ((Fin (p.m + 1) ⊕ S) ⊕ Zs) Y J)) (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (p.m + 1) ⊕ Zs) Y J)) (hwpV : ∀ i ∈ wpC, i.Valid) :
    (∀ j, ∀ i ∈ trialN (tnprepC p UJg nd ar loadC wpC) j, i.Valid) ∧
    nGatesN (tnprepC p UJg nd ar loadC wpC) ≤ p.prepGates + 84 * p.d * UJg.length +
      6 * p.d * privGates nd ar + nGatesN loadC + 2 * nGatesN wpC ∧
    (∀ q : J → Bool, nCallsN q (tnprepC p UJg nd ar loadC wpC) ≤
      12 * p.d * nCallsN q nd.V + nCallsN q loadC + 2 * nCallsN q wpC) ∧
    ((nprotocol (tnprepC p UJg nd ar loadC wpC) p.ratio (p.ratio_ge hp.g_ge)).worstCost
        wGateN : ℝ) ≤
      40 * p.ratio * nGatesN (tnprepC p UJg nd ar loadC wpC) +
        20 * p.ratio * (4 * (Fintype.card p.W + Fintype.card (XW Z ar.bT ar.bP ar.A) +
          Fintype.card Zs + Fintype.card S) + 3) ∧
    (∀ q : J → Bool,
      ((nprotocol (tnprepC p UJg nd ar loadC wpC) p.ratio (p.ratio_ge hp.g_ge)).worstCost
        (wCallN q) : ℝ) ≤ 40 * p.ratio * nCallsN q (tnprepC p UJg nd ar loadC wpC)) ∧
    Fintype.card (TNW p S Zs Z ar.bT ar.bP ar.A) =
      Fintype.card S + 2 * (Fintype.card p.W + (Fintype.card Z + ar.bT + ar.bP + ar.A + 3) +
        Fintype.card Zs) + Fintype.card S + 1 ∧
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
      NOutcome (tnprepC p UJg nd ar loadC wpC) p.ratio p.ε (p.ratio_ge hp.g_ge) prim (x p.T) := by
  obtain ⟨hV, hG, hC, hW, hWC, hcard, -⟩ :=
    native_ode_time_solver p hp UJg hUJg nd hnd ar ζ hζ har loadC hloadV wpC hwpV
  refine ⟨hV, hG, hC, hW, hWC, hcard, ?_⟩
  intro prim D Jl Wp Hs Ls G b x bs bmax ζs hprim hN hζs hload hwp hbudget hCore hx hGa hGint
    hbint hbmax hb hne hbud hcert
  have herr := slot_target_error p hp.T_pos Hs Ls bs G b x bmax hbmax hx hGa hGint hbint hb
    hCore.select.selfH hCore.psd hCore.select.normH hCore.select.normL
  exact native_outcome_of p hp UJg hUJg nd hnd ar ζ hζ har loadC hloadV wpC hwpV prim hprim
    ⟨UJop (R := ℂ) UJg, D, Jl, Wp⟩ rfl hN ζs hζs hload hwp hbudget Hs Ls (x 0) bs (x p.T) hCore
    ⟨hne, hbud, herr.trans hcert⟩

end Main

end

end SparseHamiltonian.GateMesh.ODE
