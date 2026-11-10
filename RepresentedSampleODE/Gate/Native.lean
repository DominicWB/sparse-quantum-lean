import GateEfficientNative.ODE.Time
import RepresentedSampleODE.Gate.Certificate

/-!
# The native time-dependent gate solver with represented samples of any sign

The guarantees for one instance of the released native time-dependent solver
(`GateNative.native_time_outcome`) under the robust instance conditions `RobustInstanceOK`: the
same native protocol, fixed before the instance, succeeds with probability at least `2/3`, its
conditional output is within trace distance `ε` of `x(T)/‖x(T)‖`, and every successful trial is
within `ε / 500` of it up to a global phase, without the positivity of the represented
dissipative samples. The proof is that of the released outcome with the certificate and the
target facts of the repaired target (`robust_prep_certificate`, `robust_target_facts`).
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.RepresentedSampleODE.GateTime

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit SparseHamiltonian.GateNative
open GateCircuit.Sim (Wire anc_injective)
open GateODE (OInstr OWire AW goodF Label labOf adjIf srcTS srcTS_injective)
open GateODE.Time (TParams TOracles teval trun psel labAt)
open GatePointerEncoding (wordEquivFin)
open ODEStateNormalization (unitDirection)
open scoped InnerProduct BigOperators

variable {S Zs Z Y J : Type*} [Fintype S] [DecidableEq S] [Fintype Zs] [DecidableEq Zs]
  [Fintype Z] [DecidableEq Z] [Fintype Y] [DecidableEq Y]

/-- **The guarantees for one instance** of the native time-dependent solver, represented samples
of any sign. -/
theorem robust_native_time_outcome (p : TParams) (hp : p.PublicOK)
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
    (Hs Ls : ℕ → Reg S ℂ →L[ℂ] Reg S ℂ) (G : ℝ → Reg S ℂ →L[ℂ] Reg S ℂ) (b x : ℝ → Reg S ℂ)
    (bs : ℕ → Reg S ℂ) (βG δG βb δb bmax : ℝ)
    (hI : RobustInstanceOK p (seedV (S := S)) σ Hs Ls G b x bs βG δG βb δb bmax) :
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
  -- the certificate of the repaired discretised target
  have hC := robust_prep_certificate hp (seedV (S := S)) norm_seedV σ Hs Ls G b x bs βG δG βb δb
    bmax hI
  obtain ⟨hy, hbud, hdirY⟩ := robust_target_facts hp hI
  obtain ⟨-, hpsd', -, -, -⟩ := hI.repaired hp.T_pos.le
  have hNorm := p.target_norm_le hp.T_pos.le Hs (repairedLs Ls δG) hI.select.selfH hpsd' (x 0) bs
  have hB : 0 < p.mass (x 0) bs := (norm_pos_iff.mpr hy).trans_le hNorm
  have hdec := p.decoded_eq hp (seedV (S := S)) σ (x 0) bs hB hI.prep
  have h := hC.vector_error
  have hm : p.mass (x 0) bs = ODESourceBranches.mass (p.zsrc (x 0) bs) := rfl
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
  generalize p.target Hs (repairedLs Ls δG) (x 0) bs = y at h hy hbud hdirY hNorm
  have hbud' : p.mass (x 0) bs ≤ p.ratio * ‖y‖ := hbud
  have hdirY' : ‖unitDirection y - unitDirection (x p.T)‖ ≤ p.ε / 1000 := hdirY
  obtain ⟨-, -, hmean, hdir⟩ := native_trial_bounds prim hnP (tnprepC p UJg nd ar loadC wpC) hUN
    (tnprepC_pres p UJg nd ar loadC wpC prim) Urel hA' y (p.mass (x 0) bs) p.ratio p.acc hy
    (p.ratio_ge hp.g_ge) (p.acc_pos hp.ε_pos) hacc hNorm hbud' h le_rfl
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

end

end SparseHamiltonian.RepresentedSampleODE.GateTime
