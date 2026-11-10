import SourceAccuracyODE.Outcome
import RepresentedSampleODE.Gate.Binary

/-!
# Source circuits within `ν`: the time-dependent gate solver

The time-dependent native gate solver with represented samples of any sign
(`RepresentedSampleODE.GateTime.robust_native_time_outcome`, from binary data
`robust_binary_time_outcome_nonneg`) runs at the internal ratio `2ḡ` and accuracy `ε/2`, with
precision `ν' = ε/(4·10⁴ ḡ) = ν/4`, `ν = ε/(10⁴ ḡ)`, and certifies its protocol under
`24 d ζ + 3 ζ_s ≤ ν'` for loading and weight-preparation circuits within `ζ_s`; with the released
arithmetic accuracy `98304 q* ζ ≤ ν'/2` (the internal `q* = qOf s T η_H η_D (2ḡ) (ε/2)`) this asks
each circuit to be within `ν'/6 = ν/24`.
Theorem `ode:thm:gates` asks of `P_w`, the loading and `P_w†` only a combined implementation error
`ν` (`G_src(ν)`, defined in the paragraph before the theorem). Here the same protocol is certified
under `24 d ζ + 3 ζ_s ≤ 13 ν'`, so loading and weight-preparation circuits within `ν = 4 ν'` each
suffice, with every successful trial within `ε / 100` of the solution direction and the conditional
output within trace distance `ε / 100` (`WOutcome`):

* `native_time_outcome` (native data, `T > 0`), `native_time_zero_outcome` (direct source
  assembly, `3 ζ_s ≤ 13 ν'`);
* `binary_time_outcome` (binary data, `T > 0`, `24 d ζ + 3 ζ_s ≤ 13 ν'`) and
  `binary_time_outcome_nonneg` (every `T ≥ 0`, the released protocol `btprepC q loadC wpC`, the
  public rescaling outside the zero case and `98304 q* ζ + 3 ζ_s ≤ 13 ν'`).

The protocols, their counts and the robust instance conditions are those of
`RepresentedSampleODE.GateTime`; only the source budget and the per-trial bound change.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.SourceAccuracyODE

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit GateNative
open GateCircuit.Sim (Wire anc_injective)
open GateODE (OInstr OWire AW goodF Label labOf adjIf srcTS srcTS_injective cfgOf)
open GateODE.Time (TParams TOracles teval trun psel labAt gens)
open GatePointerEncoding (wordValue wordEquivFin)
open ODEStateNormalization (unitDirection)
open RepresentedSampleODE.GateTime (RobustInstanceOK RobustRest robust_prep_certificate
  robust_target_facts repairedLs robust_instanceOK robust_tzInstanceOK)
open scoped InnerProduct BigOperators

/-! ### The native solver -/

section Native

variable {S Zs Z Y J : Type*} [Fintype S] [DecidableEq S] [Fintype Zs] [DecidableEq Zs]
  [Fintype Z] [DecidableEq Z] [Fintype Y] [DecidableEq Y]

set_option maxHeartbeats 1600000 in
/-- **The native time-dependent protocol with represented samples of any sign and circuits within
`4 ν'`**: for every instance of `RepresentedSampleODE.GateTime.robust_native_time_outcome` under
`24 d ζ + 3 ζ_s ≤ 13 ν'` in place of `24 d ζ + 3 ζ_s ≤ ν'`, the protocol has the guarantees
`WOutcome … (ε / 100)`. -/
theorem native_time_outcome (p : TParams) (hp : p.PublicOK)
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
    (hbudget : 24 * (p.d : ℝ) * ζ + 3 * ζs ≤ 13 * p.nu)
    (Hs Ls : ℕ → Reg S ℂ →L[ℂ] Reg S ℂ) (G : ℝ → Reg S ℂ →L[ℂ] Reg S ℂ) (b x : ℝ → Reg S ℂ)
    (bs : ℕ → Reg S ℂ) (βG δG βb δb bmax : ℝ)
    (hI : RobustInstanceOK p (seedV (S := S)) σ Hs Ls G b x bs βG δG βb δb bmax) :
    WOutcome (tnprepC p UJg nd ar loadC wpC) p.ratio (p.ε / 100) (p.ratio_ge hp.g_ge) prim
      (x p.T) := by
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
  have hδ : ((6 * p.d : ℕ) : ℝ) * (4 * ζ) + ((1 + 2 : ℕ) : ℝ) * ζs ≤ 13 * p.nu := by
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
  have hnP : Fintype.card (AW p.a p.m p.r p.K p.m p.l p.f) +
      Fintype.card (XW Z ar.bT ar.bP ar.A) + Fintype.card Zs + Fintype.card S ≤
      tnPool p S Zs Z ar.bT ar.bP ar.A + 1 := Nat.le_succ _
  have hne := hI.target_ne
  generalize trun (seedV (S := S)) σ p.prepC = Urel at h hA'
  generalize p.target Hs (repairedLs Ls δG) (x 0) bs = y at h hy hbud hdirY hNorm
  have hbud' : p.mass (x 0) bs ≤ p.ratio * ‖y‖ := hbud
  have hdirY' : ‖unitDirection y - unitDirection (x p.T)‖ ≤ p.ε / 1000 := hdirY
  have hg1 : 1 ≤ p.ratio := p.ratio_ge hp.g_ge
  have hg0 : 0 < p.ratio := by linarith
  have hνg : p.nu * p.ratio = p.acc / 10000 := precision_mul p.ratio p.acc hg0
  have hρ : (3 * (13 * p.nu) + 6 * p.nu) * p.ratio ≤ 9 * p.acc / 2000 := by
    have e : (3 * (13 * p.nu) + 6 * p.nu) * p.ratio = 45 * (p.nu * p.ratio) := by ring
    rw [e, hνg]
    linarith
  have hw := woutcome_lifted hnP (tnprepC p UJg nd ar loadC wpC) prim hprim hprepV
    (tnprepC_pres p UJg nd ar loadC wpC prim) Urel hA' y (x p.T) (p.mass (x 0) bs) p.ratio p.nu
    (9 * p.acc / 2000) (p.ε / 1000) hy hne hg1 hB hbud' h (by linarith [hp.nu_pos]) hρ
    (by linarith) hdirY'
  refine hw.mono ?_
  have e : p.acc = p.ε / 2 := by simp only [TParams.acc]
  rw [e]
  linarith [hp.ε_pos]

end Native

/-! ### The zero case -/

section Zero

variable {S Zs Z Y J : Type*} [Fintype S] [DecidableEq S] [Fintype Zs] [DecidableEq Zs]
  [Fintype Z] [DecidableEq Z] [Fintype Y] [DecidableEq Y]

open ZeroTimeGateODE (ZNW zPool tzprepC tzprepC_valid tzprepC_approx tzprepC_pres tzrelC
  TZInstanceOK tzero_samples ttarget_zero zsrc_sum tz_decoded)

/-- **The time-dependent zero case with circuits within `4 ν'`** (direct source assembly of
`ZeroTimeGateODE.native_time_zero_outcome`): under `3 ζ_s ≤ 13 ν'` the protocol has the
guarantees `WOutcome … (ε / 100)` against `x(T)`. -/
theorem native_time_zero_outcome (p : TParams) (a m r K l f bT bP A : ℕ) (hT : 0 ≤ p.T)
    (hg : 1 ≤ p.g) (hε : 0 < p.ε) (hεHalf : p.ε ≤ 1 / 2) (hlamH : 0 ≤ p.lamH)
    (hlamD : 0 ≤ p.lamD) (hz : p.T = 0 ∨ p.lamH + p.R * p.lamD = 0)
    (loadC : List (NInstr ((Fin (p.m + 1) ⊕ S) ⊕ Zs) Y J)) (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (p.m + 1) ⊕ Zs) Y J)) (hwpV : ∀ i ∈ wpC, i.Valid)
    (prim : J → Reg Y ℂ →L[ℂ] Reg Y ℂ) (Jl : Bool × (Fin p.m → Bool) → Reg S ℂ →L[ℂ] Reg S ℂ)
    (Wp : Matrix (Cfg (Fin (p.m + 1))) (Cfg (Fin (p.m + 1))) ℂ)
    (Hs Ls : ℕ → Reg S ℂ →L[ℂ] Reg S ℂ) (G : ℝ → Reg S ℂ →L[ℂ] Reg S ℂ) (b x : ℝ → Reg S ℂ)
    (bs : ℕ → Reg S ℂ) (βG δG βb δb bmax ζs : ℝ) (hprim : ∀ j, IsUnitary (prim j))
    (hζs : 0 ≤ ζs) (hload : ApproxOn CleanX (nrun prim loadC) (liftB (loadIdeal Jl)) ζs)
    (hwp : ApproxOn CleanX (nrun prim wpC) (liftB (matOp Wp)) ζs)
    (hbudget : 3 * ζs ≤ 13 * p.nu)
    (hI : TZInstanceOK p (seedV (S := S)) Jl Wp Hs Ls G b x bs βG δG βb δb bmax) :
    WOutcome (tzprepC loadC wpC : List (NInstr (ZNW a m r K p.m l f S Zs Z bT bP A) Y J))
      p.ratio (p.ε / 100) (p.ratio_ge hg) prim (x p.T) := by
  have hεOne : p.ε ≤ 1 := hεHalf.trans (by norm_num)
  have hprepV := tzprepC_valid (a := a) (m := m) (r := r) (K := K) (k := p.m) (l := l) (f := f)
    (nP := zPool a m r K p.m l f S Zs Z bT bP A) (Z := Z) (bT := bT) (bP := bP) (A := A)
    loadC hloadV wpC hwpV
  let σ : TOracles a p.m l (Reg S ℂ) := ⟨1, fun _ _ => 1, Jl, Wp⟩
  have hσ : σ.Unitary m := ⟨isUnitary_one, fun _ _ _ => isUnitary_one, hI.load_unitary,
    hI.prep_left, hI.prep_right⟩
  have hA := tzprepC_approx (a := a) (m := m) (r := r) (K := K) (k := p.m) (l := l) (f := f)
    (nP := zPool a m r K p.m l f S Zs Z bT bP A) (Z := Z) (bT := bT) (bP := bP) (A := A) prim hprim
    loadC hloadV wpC hwpV seedV σ hσ hζs hload hwp
  -- the target
  have hzero := tzero_samples p hg hε hεOne hlamH hlamD hz Hs Ls hI.normH hI.normL
  have hy : p.target Hs Ls (x 0) bs = ∑ s, p.zsrc (x 0) bs s := by
    rw [ttarget_zero p Hs Ls (x 0) bs hzero, zsrc_sum]
  have hErr := p.discretisation_error hT G b x Hs Ls bs βG δG βb δb bmax hI.βG_nonneg
    hI.βb_nonneg hI.solves hI.accretive hI.lipG hI.sampleG hI.lipb hI.sampleb hI.boundb hI.selfH
    hI.psd hI.normH hI.normL
  obtain ⟨hy0, hbud, hdirY⟩ := TimeDependentODE.Sampling.target_budget (x p.T)
    (p.target Hs Ls (x 0) bs) (p.mass (x 0) bs) p.g p.ε _ hg hε hεOne hI.target_ne hI.budget hErr
    hI.disc
  have hNorm := p.target_norm_le hT Hs Ls hI.selfH hI.psd (x 0) bs
  have hB : 0 < p.mass (x 0) bs := (norm_pos_iff.mpr hy0).trans_le hNorm
  -- the decoded vector
  have hrel := tz_decoded p (a := a) (m := m) (r := r) (K := K) (l := l) (f := f) hT seedV σ
    (x 0) bs hB hI.prep hI.init_load hI.forcing_load
  rw [← hy] at hrel
  generalize trun (a := a) (m := m) (r := r) (K := K) (l := l) (f := f) seedV σ tzrelC = Urel
    at hA hrel
  have hbud' : p.mass (x 0) bs ≤ p.ratio * ‖p.target Hs Ls (x 0) bs‖ := hbud
  have hg1 : 1 ≤ p.ratio := p.ratio_ge hg
  have hg0 : 0 < p.ratio := by linarith
  have hνg : p.nu * p.ratio = p.acc / 10000 := precision_mul p.ratio p.acc hg0
  have hρ : 3 * ζs * p.ratio ≤ 13 * p.acc / 10000 := by
    have h1 := mul_le_mul_of_nonneg_right hbudget hg0.le
    rw [show 13 * p.nu * p.ratio = 13 * (p.nu * p.ratio) by ring, hνg] at h1
    linarith
  have hρ4 : 13 * p.acc / 10000 ≤ 1 / 4 := by
    have e : p.acc = p.ε / 2 := by simp only [GateODE.Time.TParams.acc]
    rw [e]
    linarith
  have hw := woutcome_direct (Nat.le_succ _)
    (tzprepC loadC wpC : List (NInstr (ZNW a m r K p.m l f S Zs Z bT bP A) Y J)) prim hprim
    hprepV (tzprepC_pres loadC wpC prim) Urel hA (p.target Hs Ls (x 0) bs) (x p.T)
    (p.mass (x 0) bs) p.ratio (13 * p.acc / 10000) (p.ε / 1000) hy0 hI.target_ne hg1 hB hbud' hrel
    (by linarith) hρ hρ4 hdirY
  refine hw.mono ?_
  have e : p.acc = p.ε / 2 := by simp only [GateODE.Time.TParams.acc]
  rw [e]
  linarith

end Zero

/-! ### Binary data -/

section Binary

variable {X n : Type*} [Fintype n] [DecidableEq n] {Zs : Type*} [Fintype Zs] [DecidableEq Zs]

open GateBinary GateBinaryODE
open GateBinaryODETime (PubT HsT LsT privFamT)
open ZeroTimeGateODE (btprepC BTPublicOK0 BTZeroCase tzprepC btparams_ok0 btzeroCase_params
  btpublicOK_of)
open NativeSparseBlockEncoding (Data Query)

set_option maxHeartbeats 1600000 in
/-- **Binary data, `T > 0`, circuits within `4 ν'`**: the guarantees
`WOutcome … (ε / 100)` of the protocol of `RepresentedSampleODE.GateTime.robust_binary_time_outcome`
under `24 d ζ + 3 ζ_s ≤ 13 ν'`. -/
theorem binary_time_outcome (q : PubT) (hq : q.OK)
    (D : Data (X × Fin (2 ^ q.m)) n (Cfg (VW q.b)) q.s) (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (hdec : ∀ e z, D.decode e z = (q.c0 : ℂ) * gauss z)
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b)
      Query)) (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b) Query))
    (hwpV : ∀ i ∈ wpC, i.Valid) (x : X)
    (hrH : ∀ r i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaH ^ 2)
    (hcH : ∀ r j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaH ^ 2)
    (hrD : ∀ r i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaD ^ 2)
    (hcD : ∀ r j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaD ^ 2)
    (Jl : Bool × (Fin q.m → Bool) → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
    (Wp : Matrix (Cfg (Fin (q.m + 1))) (Cfg (Fin (q.m + 1))) ℂ)
    (G : ℝ → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ) (bf xs : ℝ → Reg (Fin q.kx) ℂ)
    (bs : ℕ → Reg (Fin q.kx) ℂ) (βG δG βb δb bmax ζs : ℝ) (hζs : 0 ≤ ζs)
    (hload : ApproxOn CleanX (nrun (primsT (R := ℂ) D en x) loadC) (liftB (loadIdeal Jl)) ζs)
    (hwp : ApproxOn CleanX (nrun (primsT (R := ℂ) D en x) wpC) (liftB (matOp Wp)) ζs)
    (hbud : 24 * (q.params.d : ℝ) * q.ζ + 3 * ζs ≤ 13 * q.params.nu)
    (hR : RobustRest q D en x Jl Wp G bf xs bs βG δG βb δb bmax) :
    WOutcome (q.prep loadC wpC) q.params.ratio (q.ε / 100) (q.params.ratio_ge hq.g_ge)
      (primsT (R := ℂ) D en x) (xs q.T) :=
  native_time_outcome q.params (q.params_ok hq) q.UJg (hadUJ4_ok q.σ q.hσ) q.nd q.nd_public
    q.ar q.ζ hq.ζ_pos.le (q.ar_ok hq) loadC hloadV wpC hwpV (primsT (R := ℂ) D en x)
    (primsT_isUnitary D en x) ⟨UJop (R := ℂ) q.UJg, privFamT q.params D en x q.rho q.γ, Jl, Wp⟩
    rfl (q.nativeOK hq D en hrange hdec x) ζs hζs hload hwp hbud (HsT D en x) (LsT D en x) G bf xs
    bs βG δG βb δb bmax
    (robust_instanceOK q hq D en hrange x hrH hcH hrD hcD Jl Wp G bf xs bs βG δG βb δb bmax hR)

set_option maxHeartbeats 1600000 in
/-- **Binary data, every `T ≥ 0`, circuits within `4 ν'`**: for time-indexed binary public data
with `BTPublicOK0 q` and the public rescaling outside the zero case, every input whose samples have
the released energy bounds, circuits within `ζ_s` with `98304 q* ζ + 3 ζ_s ≤ 13 ν'` and the robust
remaining conditions, the protocol `nprotocol (btprepC q loadC wpC) (2g)` has the guarantees
`WOutcome … (ε / 100)` against `x(T)`. -/
theorem binary_time_outcome_nonneg (q : PubT) (hq : BTPublicOK0 q)
    (hγ : ¬ BTZeroCase q →
      q.γ = GateODEBudget.gammaOf q.T q.etaH q.etaD (2 * q.g) (q.ε / 2))
    (D : Data (X × Fin (2 ^ q.m)) n (Cfg (VW q.b)) q.s) (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (hdec : ∀ e z, D.decode e z = (q.c0 : ℂ) * gauss z)
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b)
      Query)) (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b) Query))
    (hwpV : ∀ i ∈ wpC, i.Valid) (x : X)
    (hrH : ∀ r i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaH ^ 2)
    (hcH : ∀ r j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaH ^ 2)
    (hrD : ∀ r i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaD ^ 2)
    (hcD : ∀ r j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaD ^ 2)
    (Jl : Bool × (Fin q.m → Bool) → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
    (Wp : Matrix (Cfg (Fin (q.m + 1))) (Cfg (Fin (q.m + 1))) ℂ)
    (G : ℝ → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ) (bf xs : ℝ → Reg (Fin q.kx) ℂ)
    (bs : ℕ → Reg (Fin q.kx) ℂ) (βG δG βb δb bmax ζs : ℝ) (hζs : 0 ≤ ζs)
    (hload : ApproxOn CleanX (nrun (primsT (R := ℂ) D en x) loadC) (liftB (loadIdeal Jl)) ζs)
    (hwp : ApproxOn CleanX (nrun (primsT (R := ℂ) D en x) wpC) (liftB (matOp Wp)) ζs)
    (hbud : 98304 * GateODEBudget.qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * q.ζ + 3 * ζs ≤
      13 * q.params.nu)
    (hR : RobustRest q D en x Jl Wp G bf xs bs βG δG βb δb bmax) :
    WOutcome (btprepC q loadC wpC) q.params.ratio (q.ε / 100) (q.params.ratio_ge hq.g_ge)
      (primsT (R := ℂ) D en x) (xs q.T) := by
  have hε2 : (0 : ℝ) < q.ε / 2 := by linarith [hq.ε_pos]
  have hQ1 : 1 ≤ GateODEBudget.qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) :=
    GateRemarks.ODE.one_le_qOf hq.T_nonneg hq.etaH_nonneg hq.etaD_nonneg (by linarith [hq.g_ge])
      hε2 (by linarith [hq.ε_half])
  by_cases hz : BTZeroCase q
  · have hp := btparams_ok0 hq
    have hpr : btprepC q loadC wpC = tzprepC loadC wpC := by
      rw [btprepC, if_pos hz]
    have h0 : 0 ≤ 98304 * GateODEBudget.qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * q.ζ :=
      mul_nonneg (mul_nonneg (by norm_num) (by linarith)) hq.ζ_pos.le
    have hI := robust_tzInstanceOK q hq D en x hrH hcH hrD hcD Jl Wp G bf xs bs βG δG βb δb bmax hR
    rw [hpr]
    exact native_time_zero_outcome (S := Fin q.kx) (Zs := Zs) (Z := SZ4 q.kx q.b)
      (Y := Fin q.m ⊕ PY q.kx q.b) (J := Query) q.params q.params.a q.params.m q.params.r
      q.params.K q.params.l q.params.f q.ar.bT q.ar.bP q.ar.A hq.T_nonneg hq.g_ge hq.ε_pos
      hq.ε_half hp.lamH_nonneg hp.lamD_nonneg (btzeroCase_params hq hz) loadC hloadV wpC hwpV
      (primsT (R := ℂ) D en x) Jl Wp (HsT D en x) (repairedLs (LsT D en x) δG) G bf xs bs βG
      (3 * δG) βb δb bmax ζs (primsT_isUnitary D en x) hζs hload hwp (by linarith) hI
  · have hP := btpublicOK_of hq hz
    obtain ⟨-, hd, -, -, -, -⟩ := GateODEBudget.binary_ode_time_sizes q hP (hγ hz)
    have hpr : btprepC q loadC wpC = q.prep loadC wpC := by
      rw [btprepC, if_neg hz]
    have hbud' : 24 * (q.params.d : ℝ) * q.ζ + 3 * ζs ≤ 13 * q.params.nu := by
      have := mul_le_mul_of_nonneg_right hd hP.ζ_pos.le
      linarith
    rw [hpr]
    exact binary_time_outcome q hP D en hrange hdec loadC hloadV wpC hwpV x hrH hcH hrD hcD
      Jl Wp G bf xs bs βG δG βb δb bmax ζs hζs hload hwp hbud' hR

end Binary

end

end SparseHamiltonian.SourceAccuracyODE
