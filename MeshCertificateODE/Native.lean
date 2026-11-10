import MeshCertificateODE.Certificate
import SourceAccuracyODE.Time

/-!
# The native time-dependent protocol under the manuscript's certificates

The released native time-dependent protocol (`GateNative.tnprepC`; direct source assembly
`ZeroTimeGateODE.tzprepC` in the zero case), with loading and weight-preparation circuits within
`8 ν'` (`ν'` the precision of the private simulation; twice the tolerance `4 ν'` of
`SourceAccuracyODE`, with the source budget `24 d ζ + 3 ζ_s ≤ 25 ν'` in place of its `13 ν'`), has
the guarantees `SourceAccuracyODE.WOutcome … (ε / 100)` against `x(T)` under the certificate-form
instance conditions (the vector error at most `81 ν' B_m`):

* `cert_native_time_outcome`: native data, `T > 0`, under `CertInstanceOK`;
* `cert_target_facts_of`: the target facts of the repaired target from the certificates (the
  conditions of `CertInstanceOK` that concern the target);
* `CertTZInstanceOK`, `cert_native_time_zero_outcome`: the zero case
  `T = 0 ∨ λ_H + R λ_D = 0`, without the selection hypotheses of the private operations.

The protocols and their counts are those of the released solvers; only the instance conditions
change.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.MeshCertificateODE

noncomputable section
open ContinuousLinearMap Set MeasureTheory OracleCircuit GateCircuit GateNative
open GateCircuit.Sim (Wire anc_injective)
open GateODE (OInstr OWire AW goodF Label labOf adjIf srcTS srcTS_injective cfgOf)
open GateODE.Time (TParams TOracles teval trun psel labAt gens)
open GatePointerEncoding (wordValue wordEquivFin)
open ODEStateNormalization (unitDirection)
open SparseHamiltonian.TimeDependentODE (Accretive)
open SparseHamiltonian.GeneralSourceExtensions.Mesh (IsMeshPropagator meshScale meshScale_nonneg)
open SparseHamiltonian.SourceAccuracyODE (WOutcome woutcome_lifted woutcome_direct precision_mul)
open scoped InnerProduct BigOperators

/-! ### The native solver -/

section Native

variable {S Zs Z Y J : Type*} [Fintype S] [DecidableEq S] [Fintype Zs] [DecidableEq Zs]
  [Fintype Z] [DecidableEq Z] [Fintype Y] [DecidableEq Y]

set_option maxHeartbeats 1600000 in
/-- **The native time-dependent protocol under the manuscript's certificates, circuits within
`8 ν'`**: for public data with `PublicOK`, the released native data, loading and weight-preparation
circuits within `ζ_s` with `24 d ζ + 3 ζ_s ≤ 25 ν'`, and the instance conditions
`CertInstanceOK`, the protocol `tnprepC p UJg nd ar loadC wpC` has the guarantees
`WOutcome … (ε / 100)` against `x(T)`. -/
theorem cert_native_time_outcome (p : TParams) (hp : p.PublicOK)
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
    (hbudget : 24 * (p.d : ℝ) * ζ + 3 * ζs ≤ 25 * p.nu)
    (Hs Ls : ℕ → Reg S ℂ →L[ℂ] Reg S ℂ) (G : Fin p.M → ℝ → Reg S ℂ →L[ℂ] Reg S ℂ)
    (bf : Fin p.M → ℝ → Reg S ℂ) (sol : ℝ → Reg S ℂ) (U : ℝ → Reg S ℂ → ℝ → Reg S ℂ)
    (bs : ℕ → Reg S ℂ) (gb cq ζc : ℝ)
    (hI : CertInstanceOK p (seedV (S := S)) σ Hs Ls G bf sol U bs gb cq ζc) :
    WOutcome (tnprepC p UJg nd ar loadC wpC) p.ratio (p.ε / 100) (p.ratio_ge hp.g_ge) prim
      (sol p.T) := by
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
  have hδ : ((6 * p.d : ℕ) : ℝ) * (4 * ζ) + ((1 + 2 : ℕ) : ℝ) * ζs ≤ 25 * p.nu := by
    have e2 : ((6 * p.d : ℕ) : ℝ) = 6 * (p.d : ℝ) := by rw [Nat.cast_mul, Nat.cast_ofNat]
    have e3 : ((1 + 2 : ℕ) : ℝ) = 3 := by norm_num
    rw [e2, e3]
    linarith only [hbudget]
  have hA' := hA.mono hδ
  -- the certificate of the repaired discretised target
  have hC := cert_prep_certificate hp (seedV (S := S)) norm_seedV σ Hs Ls G bf sol U bs gb cq ζc
    hI
  obtain ⟨hy, hbud, hdirY⟩ := cert_target_facts' hp hI
  obtain ⟨-, hpsd', -, -⟩ := hI.repaired hp.T_pos.le
  have hNorm := p.target_norm_le hp.T_pos.le Hs (repLs Ls (pathκ p.T G Hs Ls)) hI.select.selfH
    hpsd' (sol 0) bs
  have hB : 0 < p.mass (sol 0) bs := (norm_pos_iff.mpr hy).trans_le hNorm
  have hdec := p.decoded_eq hp (seedV (S := S)) σ (sol 0) bs hB hI.prep
  have h := hC.vector_error
  have hm : p.mass (sol 0) bs = ODESourceBranches.mass (p.zsrc (sol 0) bs) := rfl
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
  generalize p.target Hs (repLs Ls (pathκ p.T G Hs Ls)) (sol 0) bs = y at h hy hbud hdirY hNorm
  have hbud' : p.mass (sol 0) bs ≤ p.ratio * ‖y‖ := hbud
  have hdirY' : ‖unitDirection y - unitDirection (sol p.T)‖ ≤ p.ε / 1000 := hdirY
  have hg1 : 1 ≤ p.ratio := p.ratio_ge hp.g_ge
  have hg0 : 0 < p.ratio := by linarith
  have hνg : p.nu * p.ratio = p.acc / 10000 := precision_mul p.ratio p.acc hg0
  have hρ : (3 * (25 * p.nu) + 6 * p.nu) * p.ratio ≤ 81 * p.acc / 10000 := by
    have e : (3 * (25 * p.nu) + 6 * p.nu) * p.ratio = 81 * (p.nu * p.ratio) := by ring
    rw [e, hνg]
    linarith
  have hw := woutcome_lifted hnP (tnprepC p UJg nd ar loadC wpC) prim hprim hprepV
    (tnprepC_pres p UJg nd ar loadC wpC prim) Urel hA' y (sol p.T) (p.mass (sol 0) bs) p.ratio
    p.nu (81 * p.acc / 10000) (p.ε / 1000) hy hne hg1 hB hbud' h (by linarith [hp.nu_pos]) hρ
    (by linarith) hdirY'
  refine hw.mono ?_
  have e : p.acc = p.ε / 2 := by simp only [TParams.acc]
  rw [e]
  linarith [hp.ε_pos]

end Native

/-! ### The target facts from the certificates -/

section Facts

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-- **The target facts of the repaired target from the certificates**, from the conditions of
`CertInstanceOK` that concern the target (self-adjoint Hamiltonian samples, the generator pieces
and their propagator, the source certificate, the mass and amplification conditions and the
budget). -/
theorem cert_target_facts_of (p : TParams) (hT : 0 ≤ p.T) (hg : 1 ≤ p.g) (hε : 0 < p.ε)
    (hεOne : p.ε ≤ 1) (Hs Ls : ℕ → P →L[ℂ] P) (hH : ∀ r < p.M, star (Hs r) = Hs r)
    (G : Fin p.M → ℝ → P →L[ℂ] P)
    (hG : ∀ r : Fin p.M, ∀ u ∈ Icc (umesh p.T p.M r) (umesh p.T p.M ((r : ℕ) + 1)),
      Accretive (G r u))
    (hGi : RepresentedSampleODE.RegularPieces (umesh p.T p.M) G) (bf : Fin p.M → ℝ → P)
    (sol : ℝ → P) (U : ℝ → P → ℝ → P) (hU : IsMeshPropagator G (umesh p.T p.M) p.T U)
    (bs : ℕ → P) {gb cq ζ : ℝ} (hx : sol p.T ≠ 0) (hgb : 0 < gb) (hcq : 0 ≤ cq)
    (hscale : meshScale sol bf (umesh p.T p.M) ≤ gb * ‖sol p.T‖)
    (hmass : p.mass (sol 0) bs ≤ cq * meshScale sol bf (umesh p.T p.M))
    (hratio : cq * gb ≤ p.g)
    (hsrc : ‖sol p.T - quadSum p.T p.M U (sol 0) bs‖ ≤ ζ * meshScale sol bf (umesh p.T p.M))
    (hbudget : ζ + cq * (sampleErr (umesh p.T p.M) G (fun r => gens Hs Ls r) +
      2 * dissErr (umesh p.T p.M) G (fun r => gens Hs Ls r)) ≤ p.ε / (2000 * gb)) :
    (∀ r < p.M, ∀ w : P, 0 ≤ (inner ℂ w (repLs Ls (pathκ p.T G Hs Ls) r w)).re) ∧
    (∀ r < p.M, ‖repLs Ls (pathκ p.T G Hs Ls) r‖ ≤ ‖Ls r‖) ∧
    p.target Hs (repLs Ls (pathκ p.T G Hs Ls)) (sol 0) bs ≠ 0 ∧
      p.mass (sol 0) bs ≤ 2 * p.g * ‖p.target Hs (repLs Ls (pathκ p.T G Hs Ls)) (sol 0) bs‖ ∧
      ‖unitDirection (p.target Hs (repLs Ls (pathκ p.T G Hs Ls)) (sol 0) bs) -
        unitDirection (sol p.T)‖ ≤ p.ε / 1000 := by
  have hmesh := isMesh_umesh hT p.M_pos
  have hκ0 := pathκ_nonneg hT p.M_pos G Hs Ls
  have hneg : ∀ r < p.M, ∀ w : P, -pathκ p.T G Hs Ls r * ‖w‖ ^ 2 ≤ (inner ℂ w (Ls r w)).re :=
    fun _ hr w => pathκ_bound G Hs Ls hH hG hGi hr w
  have hpsd' : ∀ r < p.M, ∀ w : P, 0 ≤ (inner ℂ w (repLs Ls (pathκ p.T G Hs Ls) r w)).re :=
    fun r hr w => RepresentedSampleODE.repair_nonneg (Ls r) (hκ0 r) (hneg r hr) w
  have hdiff : ∀ r < p.M, ‖Ls r - repLs Ls (pathκ p.T G Hs Ls) r‖ ≤ 2 * pathκ p.T G Hs Ls r :=
    fun r _ => by
      rw [norm_sub_rev]
      exact RepresentedSampleODE.norm_repair_sub_le (Ls r) (hκ0 r)
  refine ⟨hpsd', fun r _ => RepresentedSampleODE.norm_repair_le (Ls r) (hκ0 r), ?_⟩
  set Ls' := repLs Ls (pathκ p.T G Hs Ls) with hLs'
  have hacc' : ∀ r < p.M, Accretive (gens Hs Ls' r) := fun r hr =>
    GateODE.Time.slot_accretive _ _ (hH r hr) (hpsd' r hr)
  have herr := quad_target_error p hT Hs Ls' hacc' G hG hGi U hU (sol 0) bs
  have hrep := sampleErr_repLs_le hT p.M_pos Hs Ls (pathκ p.T G Hs Ls) hdiff G hGi
  rw [negativity_pathκ hT p.M_pos G Hs Ls] at hrep
  have hK0 : 0 ≤ sampleErr (umesh p.T p.M) G (fun r => gens Hs Ls' r) :=
    sampleErr_nonneg hmesh G _
  have hbud : ζ + cq * sampleErr (umesh p.T p.M) G (fun r => gens Hs Ls' r) ≤
      p.ε / (2000 * gb) := by
    have := mul_le_mul_of_nonneg_left hrep hcq
    linarith
  exact cert_target_facts (sol p.T) (quadSum p.T p.M U (sol 0) bs) _ hg hε hεOne hx
    (meshScale_nonneg hmesh sol bf) hgb hcq hK0 hsrc herr hmass hscale hratio hbud

end Facts

/-! ### The zero case -/

section Zero

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-- **The zero-case instance conditions under the certificates**: those of `CertInstanceOK`
without the conditions on `U_J`, on the private operations and on the branch budget (the zero
case has no LCHS branches): the represented samples (self-adjoint `H_r`, `‖H_r‖ ≤ λ_H`,
`‖L_r‖ ≤ λ_D`; no positivity), the supplied loading `Jl` and weight preparation `Wp` with their
promises, the generator pieces with their propagator, and the source and sample certificates. -/
structure CertTZInstanceOK (p : TParams) (v : P) (Jl : Bool × (Fin p.m → Bool) → P →L[ℂ] P)
    (Wp : Matrix (Cfg (Fin (p.m + 1))) (Cfg (Fin (p.m + 1))) ℂ) (Hs Ls : ℕ → P →L[ℂ] P)
    (G : Fin p.M → ℝ → P →L[ℂ] P) (bf : Fin p.M → ℝ → P) (sol : ℝ → P) (U : ℝ → P → ℝ → P)
    (bs : ℕ → P) (gb cq ζ : ℝ) : Prop where
  selfH : ∀ r < p.M, star (Hs r) = Hs r
  normH : ∀ r < p.M, ‖Hs r‖ ≤ p.lamH
  normL : ∀ r < p.M, ‖Ls r‖ ≤ p.lamD
  load_unitary : ∀ s, IsUnitary (Jl s)
  prep_left : Wp.conjTranspose * Wp = 1
  prep_right : Wp * Wp.conjTranspose = 1
  prep : ∀ w : Cfg (Fin (p.m + 1)),
    Wp w (fun _ => false) = ((p.srcAmp (sol 0) bs (w 0, Fin.tail w) : ℝ) : ℂ)
  init_load : sol 0 ≠ 0 → Jl (false, fun _ => false) v = unitDirection (sol 0)
  forcing_load : ∀ w : Fin p.m → Bool, bs (wordValue w) ≠ 0 →
    Jl (true, w) v = unitDirection (bs (wordValue w))
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

variable {S Zs Z Y J : Type*} [Fintype S] [DecidableEq S] [Fintype Zs] [DecidableEq Zs]
  [Fintype Z] [DecidableEq Z] [Fintype Y] [DecidableEq Y]

open ZeroTimeGateODE (ZNW zPool tzprepC tzprepC_valid tzprepC_approx tzprepC_pres tzrelC
  tzero_samples ttarget_zero zsrc_sum tz_decoded)

/-- **The time-dependent zero case under the certificates, circuits within `8 ν'`** (direct
source assembly): under `3 ζ_s ≤ 25 ν'` the protocol `tzprepC loadC wpC` has the guarantees
`WOutcome … (ε / 100)` against `x(T)`. -/
theorem cert_native_time_zero_outcome (p : TParams) (a m r K l f bT bP A : ℕ) (hT : 0 ≤ p.T)
    (hg : 1 ≤ p.g) (hε : 0 < p.ε) (hεHalf : p.ε ≤ 1 / 2) (hlamH : 0 ≤ p.lamH)
    (hlamD : 0 ≤ p.lamD) (hz : p.T = 0 ∨ p.lamH + p.R * p.lamD = 0)
    (loadC : List (NInstr ((Fin (p.m + 1) ⊕ S) ⊕ Zs) Y J)) (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (p.m + 1) ⊕ Zs) Y J)) (hwpV : ∀ i ∈ wpC, i.Valid)
    (prim : J → Reg Y ℂ →L[ℂ] Reg Y ℂ) (Jl : Bool × (Fin p.m → Bool) → Reg S ℂ →L[ℂ] Reg S ℂ)
    (Wp : Matrix (Cfg (Fin (p.m + 1))) (Cfg (Fin (p.m + 1))) ℂ)
    (Hs Ls : ℕ → Reg S ℂ →L[ℂ] Reg S ℂ) (G : Fin p.M → ℝ → Reg S ℂ →L[ℂ] Reg S ℂ)
    (bf : Fin p.M → ℝ → Reg S ℂ) (sol : ℝ → Reg S ℂ) (U : ℝ → Reg S ℂ → ℝ → Reg S ℂ)
    (bs : ℕ → Reg S ℂ) (gb cq ζc ζs : ℝ) (hprim : ∀ j, IsUnitary (prim j))
    (hζs : 0 ≤ ζs) (hload : ApproxOn CleanX (nrun prim loadC) (liftB (loadIdeal Jl)) ζs)
    (hwp : ApproxOn CleanX (nrun prim wpC) (liftB (matOp Wp)) ζs)
    (hbudget : 3 * ζs ≤ 25 * p.nu)
    (hI : CertTZInstanceOK p (seedV (S := S)) Jl Wp Hs Ls G bf sol U bs gb cq ζc) :
    WOutcome (tzprepC loadC wpC : List (NInstr (ZNW a m r K p.m l f S Zs Z bT bP A) Y J))
      p.ratio (p.ε / 100) (p.ratio_ge hg) prim (sol p.T) := by
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
  -- the repaired target and its facts
  obtain ⟨hpsd', hnorm', hy0, hbud, hdirY⟩ := cert_target_facts_of p hT hg hε hεOne Hs Ls
    hI.selfH G hI.accretive hI.regular bf sol U hI.propagator bs hI.target_ne hI.gb_pos
    hI.cq_nonneg hI.scale hI.mass hI.ratio hI.source hI.budget
  set Ls' := repLs Ls (pathκ p.T G Hs Ls) with hLs'
  have hzero := tzero_samples p hg hε hεOne hlamH hlamD hz Hs Ls' hI.normH
    (fun r hr => (hnorm' r hr).trans (hI.normL r hr))
  have hy : p.target Hs Ls' (sol 0) bs = ∑ s, p.zsrc (sol 0) bs s := by
    rw [ttarget_zero p Hs Ls' (sol 0) bs hzero, zsrc_sum]
  have hNorm := p.target_norm_le hT Hs Ls' hI.selfH hpsd' (sol 0) bs
  have hB : 0 < p.mass (sol 0) bs := (norm_pos_iff.mpr hy0).trans_le hNorm
  -- the decoded vector
  have hrel := tz_decoded p (a := a) (m := m) (r := r) (K := K) (l := l) (f := f) hT seedV σ
    (sol 0) bs hB hI.prep hI.init_load hI.forcing_load
  rw [← hy] at hrel
  generalize trun (a := a) (m := m) (r := r) (K := K) (l := l) (f := f) seedV σ tzrelC = Urel
    at hA hrel
  have hbud' : p.mass (sol 0) bs ≤ p.ratio * ‖p.target Hs Ls' (sol 0) bs‖ := hbud
  have hg1 : 1 ≤ p.ratio := p.ratio_ge hg
  have hg0 : 0 < p.ratio := by linarith
  have hνg : p.nu * p.ratio = p.acc / 10000 := precision_mul p.ratio p.acc hg0
  have hρ : 3 * ζs * p.ratio ≤ 25 * p.acc / 10000 := by
    have h1 := mul_le_mul_of_nonneg_right hbudget hg0.le
    rw [show 25 * p.nu * p.ratio = 25 * (p.nu * p.ratio) by ring, hνg] at h1
    linarith
  have hρ4 : 25 * p.acc / 10000 ≤ 1 / 4 := by
    have e : p.acc = p.ε / 2 := by simp only [GateODE.Time.TParams.acc]
    rw [e]
    linarith
  have hw := woutcome_direct (Nat.le_succ _)
    (tzprepC loadC wpC : List (NInstr (ZNW a m r K p.m l f S Zs Z bT bP A) Y J)) prim hprim
    hprepV (tzprepC_pres loadC wpC prim) Urel hA (p.target Hs Ls' (sol 0) bs) (sol p.T)
    (p.mass (sol 0) bs) p.ratio (25 * p.acc / 10000) (p.ε / 1000) hy0 hI.target_ne hg1 hB hbud'
    hrel (by linarith) hρ hρ4 hdirY
  refine hw.mono ?_
  have e : p.acc = p.ε / 2 := by simp only [GateODE.Time.TParams.acc]
  rw [e]
  linarith

end Zero

end

end SparseHamiltonian.MeshCertificateODE
