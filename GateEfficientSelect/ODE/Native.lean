import GateEfficientSelect.ODE.Theorem
import GateEfficientNative.ODE.Time

/-!
# The native solver on branch-dependent meshes

The released native time-dependent solver `GateNative.native_ode_time_solver` replaces every
oracle call of the released time-dependent protocol by a native implementation: `U_J` by its
gates, the label- and slot-selected private Cayley operation by one native compute circuit with
reversible angle arithmetic (`NativeOK`, `ArithOK`), and the loading and weight preparation by
supplied native circuits within `ζs`. Its circuits depend only on the public data and the
supplied native circuits, so its validity and its counts of gates and primitive calls are those
of the released theorem; the branch-dependent meshes enter only through the ideal private family
`D` that the compute circuit implements.

`native_time_outcomeB`, `native_ode_time_solverB`: for every instance whose ideal oracles
`(U_J, D, J, Wp)` satisfy `BInstanceOK` (the branch-dependent meshes of Lemma
`ode:lem:gate-select` with a positive source quadrature and the source certificate) and the
released error budget `24 d ζ + 3 ζs ≤ ν`, the native protocol succeeds with probability at
least `2/3` and its conditional output is within trace distance `ε` of `x(T)/‖x(T)‖` (the
released `NOutcome`).
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000

namespace SparseHamiltonian.GateSelect.ODE

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit GateNative
open GateCircuit.Sim (Wire anc_injective)
open GateODE (OInstr OWire AW goodF Label labOf adjIf srcTS srcTS_injective)
open GateODE.Time (TParams TOracles teval trun psel labAt)
open GatePointerEncoding (wordEquivFin)
open ODEStateNormalization (unitDirection)
open scoped InnerProduct BigOperators

variable {S Zs Z Y J : Type*} [Fintype S] [DecidableEq S] [Fintype Zs] [DecidableEq Zs]
  [Fintype Z] [DecidableEq Z] [Fintype Y] [DecidableEq Y]

/-- **The guarantees for one instance** of the native time-dependent solver on
branch-dependent meshes. -/
theorem native_time_outcomeB (p : TParams) (hp : p.PublicOK)
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
    (Hb Lb : Bool × (Fin p.m → Bool) → ℕ → Reg S ℂ →L[ℂ] Reg S ℂ)
    (G : ℝ → Reg S ℂ →L[ℂ] Reg S ℂ) (b x : ℝ → Reg S ℂ)
    (ys : Bool × (Fin p.m → Bool) → ℝ → Reg S ℂ) (βG δG κ : ℝ)
    (hI : BInstanceOK p (seedV (S := S)) σ v wq fv Hb Lb G b x ys βG δG κ) :
    NOutcome (tnprepC p UJg nd ar loadC wpC) p.ratio p.ε (p.ratio_ge hp.g_ge) prim (x p.T) := by
  obtain ⟨cP, -, cSF, cST, -, -⟩ := p.prepC_counts hp.tau_pos.le hp.nu_pos hp.mesh
  have hvalid := p.prepC_valid hp.tau_pos.le hp.nu_pos hp.mesh
  have hprepV := tnprepC_valid p hp UJg hUJg nd hnd ar har loadC hloadV wpC hwpV
  have hU := hI.unitary
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
  -- the released certificate of the exact target on branch-dependent meshes
  have hC := prep_certificateB p hp (seedV (S := S)) norm_seedV σ v wq fv Hb Lb G b x ys βG δG κ
    hI
  obtain ⟨hy, hbud, hdirY⟩ := target_factsB hp hI
  have hNorm := targetB_norm_le p hp.T_pos.le v hI.nodes Hb Lb hI.selfH hI.selfL hI.psd (x 0) wq
    fv
  have hB : 0 < p.mass (x 0) (bsW p wq fv) := (norm_pos_iff.mpr hy).trans_le hNorm
  have hdec := p.decoded_eq hp (seedV (S := S)) σ (x 0) (bsW p wq fv) hB hI.prep
  have h := hC.vector_error
  have hm : p.mass (x 0) (bsW p wq fv) = ODESourceBranches.mass (p.zsrc (x 0) (bsW p wq fv)) :=
    rfl
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
  have hne := hI.target_ne
  generalize trun (seedV (S := S)) σ p.prepC = Urel at h hA'
  generalize targetB p v Hb Lb (x 0) wq fv = y at h hy hbud hdirY hNorm
  have hbud' : p.mass (x 0) (bsW p wq fv) ≤ p.ratio * ‖y‖ := hbud
  have hdirY' : ‖unitDirection y - unitDirection (x p.T)‖ ≤ p.ε / 1000 := hdirY
  obtain ⟨-, -, hmean, hdir⟩ := native_trial_bounds prim hnP (tnprepC p UJg nd ar loadC wpC) hUN
    (tnprepC_pres p UJg nd ar loadC wpC prim) Urel hA' y (p.mass (x 0) (bsW p wq fv)) p.ratio p.acc
    hy (p.ratio_ge hp.g_ge) (p.acc_pos hp.ε_pos) hacc hNorm hbud' h le_rfl
  refine noutcome_of_bounds (tnprepC p UJg nd ar loadC wpC) prim hprim hprepV (x p.T)
    hne p.ratio p.ε (p.ratio_ge hp.g_ge) hp.ε_pos hmean ?_
  intro j hj
  obtain ⟨ω, hω, hd⟩ := hdir j hj
  refine ⟨ω, hω, ?_⟩
  refine (norm_sub_le_norm_sub_add_norm_sub _ (unitDirection y) _).trans ?_
  have e : p.acc / 500 + p.ε / 1000 = p.ε / 500 := by
    simp only [TParams.acc]
    ring
  linarith only [hd, hdirY', e]

/-- **Native gate-efficient dissipative ODE solver on branch-dependent meshes** (Theorem
`ode:thm:gates`, time-dependent part, with the branch-dependent meshes of Lemma
`ode:lem:gate-select`, before finite-set synthesis). The native protocol of the released
`GateNative.native_ode_time_solver` keeps its validity and its counts of gates, primitive calls
and wires; for every instance with primitive oracles `prim`, label- and slot-selected private
Cayley operations `D z r` given natively by `V` (`NativeOK`), a loading `J s` and a weight
preparation `Wp` approximated by the supplied circuits within `ζs`, the conditions
`BInstanceOK` for `(U_J, D, J, Wp)` and the error budget `24 d ζ + 3 ζs ≤ ν`, the protocol
succeeds with probability at least `2/3`, and its conditional output is within trace distance
`ε` of `x(T)/‖x(T)‖`. -/
theorem native_ode_time_solverB (p : TParams) (hp : p.PublicOK)
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
      (v wq : ℕ → ℝ) (fv : ℕ → Reg S ℂ)
      (Hb Lb : Bool × (Fin p.m → Bool) → ℕ → Reg S ℂ →L[ℂ] Reg S ℂ)
      (G : ℝ → Reg S ℂ →L[ℂ] Reg S ℂ) (b x : ℝ → Reg S ℂ)
      (ys : Bool × (Fin p.m → Bool) → ℝ → Reg S ℂ) (βG δG κ ζs : ℝ),
      (∀ j, IsUnitary (prim j)) →
      NativeOK prim nd (selOp (tlabFam (P := Reg S ℂ) D false)) →
      0 ≤ ζs →
      ApproxOn CleanX (nrun prim loadC) (liftB (loadIdeal Jl)) ζs →
      ApproxOn CleanX (nrun prim wpC) (liftB (matOp Wp)) ζs →
      24 * (p.d : ℝ) * ζ + 3 * ζs ≤ p.nu →
      BInstanceOK p (seedV (S := S))
        (⟨UJop (R := ℂ) UJg, D, Jl, Wp⟩ : TOracles p.a p.m p.l (Reg S ℂ))
        v wq fv Hb Lb G b x ys βG δG κ →
      NOutcome (tnprepC p UJg nd ar loadC wpC) p.ratio p.ε (p.ratio_ge hp.g_ge) prim (x p.T) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := native_ode_time_solver p hp UJg hUJg nd hnd ar ζ hζ har
    loadC hloadV wpC hwpV
  refine ⟨h1, h2, h3, h4, h5, h6, ?_⟩
  intro prim D Jl Wp v wq fv Hb Lb G b x ys βG δG κ ζs hprim hN hζs hload hwp hbudget hI
  exact native_time_outcomeB p hp UJg hUJg nd hnd ar ζ hζ har loadC hloadV wpC hwpV prim hprim
    ⟨UJop (R := ℂ) UJg, D, Jl, Wp⟩ rfl hN ζs hζs hload hwp hbudget v wq fv Hb Lb G b x ys βG δG κ
    hI

end

end SparseHamiltonian.GateSelect.ODE
