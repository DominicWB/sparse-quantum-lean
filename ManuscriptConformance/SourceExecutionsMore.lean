import ManuscriptConformance.SourceExecutions
import ManuscriptConformance.GateODETime
import ManuscriptConformance.GateODEGeneral
import ManuscriptConformance.GateODETimeGeneral
import ManuscriptConformance.GateODEDecoder

/-!
# Conformance: source executions of the remaining gate endpoints

`ManuscriptConformance.SourceExecutions` counts the executions of the supplied source circuits
after native macro expansion for `ode_thm_gates`, `ode_thm_gates_decoder`,
`ode_thm_gates_time_cert` and `ode_thm_gates_time_decoder_cert`. This module does the same for the
four other native gate endpoints of Theorem `ode:thm:gates`, with the same generic lemmas:

* `ode_thm_gates_general_sources` (`ode_thm_gates_general`, general sizes, constant
  coefficients): the preparation `GPub.prep N 0 srcC` is `prepI` at the general-size
  implementation `implP N s 0`, annotated by `constAnnotI`; at most `40 ḡ` executions of each
  source circuit;
* `ode_thm_gates_time_sources` (`ode_thm_gates_time`, uniform mesh): the preparation `btprepC`,
  annotated by `btimeAnnot` (the released zero-case assembly `tzrelC` or the released preparation
  `q.params.prepC`, each instruction with its native macro);
* `ode_thm_gates_time_general_sources` (`ode_thm_gates_time_general`): `GPubT.prep N 0 loadC wpC`,
  which is `prepTI` at `implP N s 0`, annotated by `timeAnnot`;
* `ode_thm_gates_time_decoder_sources` (`ode_thm_gates_time_decoder`): `prepTD`, annotated by
  `timeAnnot` at the decoder implementation `implDP`.

The three time-dependent protocols have the parameter `2ḡ`, so along every history there are at
most `80 ḡ` executions of the loading circuit and `160 ḡ` of the weight-preparation circuit (one
loading and two weight preparations per preparation, `40 · 2ḡ` preparations per history). In
each statement, along every history: the calls of every oracle kind are the propagation calls
(the same trials with empty source circuits) plus the executions times the calls inside each
source circuit, the propagation calls are at most `C ḡ q` per selected kind (none if `T = 0` or
`η_H + η_D = 0`), the total is at most that plus the execution bounds times the source calls, and
the gates are the propagation gates plus the executions times the source gates. `C` is the
constant of the original endpoint, and the propagation bounds are that endpoint applied to the
same protocol with empty source circuits.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4096

namespace ManuscriptConformance

noncomputable section

open SparseHamiltonian SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
open SparseHamiltonian.GateODE (OInstr)
open scoped InnerProduct

universe u v

/-! ### The annotated preparation of the uniform-mesh solver -/

section Preparations

open SparseHamiltonian.GateBinary
open SparseHamiltonian.GateBinaryODE (SZ4)
open SparseHamiltonian.GateBinaryODETime (PubT)
open SparseHamiltonian.ZeroTimeGateODE (btprepC BTPublicOK0 BTZeroCase tzrelC tzmacro)
open NativeSparseBlockEncoding (Query)

variable {Zs : Type*} [Fintype Zs]

/-- **The annotated preparation of the uniform-mesh time-dependent solver** (`btprepC`): the
released zero-case assembly `tzrelC` or the released preparation `q.params.prepC`, each
instruction with its native macro. -/
def btimeAnnot (q : PubT)
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b) Query))
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b) Query)) :
    List (ABlock (TNW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A)
      (Fin q.m ⊕ PY q.kx q.b) Query) :=
  if BTZeroCase q then annotOf (tzmacro loadC wpC) tzrelC
  else annotOf (omacro tlabSel q.UJg q.nd q.ar (tsrcMacro q.params loadC wpC)) q.params.prepC

theorem aflat_btimeAnnot [DecidableEq Zs] (q : PubT)
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b) Query))
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b) Query)) :
    aflat (btimeAnnot q loadC wpC) = btprepC q loadC wpC := by
  unfold btimeAnnot btprepC
  split_ifs
  · rw [aflat_annotOf, ZeroTimeGateODE.tzprepC_eq_flatMap]
  · rw [aflat_annotOf]
    rfl

theorem annotOK_btimeAnnot (q : PubT)
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b) Query))
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b) Query)) :
    AnnotOK (tsrcMacro q.params loadC wpC) (btimeAnnot q loadC wpC) := by
  unfold btimeAnnot
  split_ifs
  · exact annotOK_annotOf _ _ (fun b adj => by cases b <;> cases adj <;> rfl) _
  · exact annotOK_annotOf _ _ (fun _ _ => rfl) _

theorem aerase_btimeAnnot (q : PubT)
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b) Query))
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b) Query)) :
    aerase (btimeAnnot q loadC wpC) = btimeAnnot q [] [] := by
  unfold btimeAnnot
  split_ifs
  · refine aerase_annotOf _ _ (fun i hi => ?_) (fun b adj => by cases b <;> cases adj <;> rfl) _
    cases i <;> first | rfl | cases hi
  · refine aerase_annotOf _ _ (fun i hi => ?_) (fun b adj => by cases b <;> cases adj <;> rfl) _
    cases i <;> first | rfl | cases hi

/-- One execution of the loading circuit and two of the weight-preparation circuit per
preparation (both orientations counted). -/
theorem nexec_btimeAnnot (q : PubT) (hq : BTPublicOK0 q)
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b) Query))
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b) Query)) :
    nexec false false (btimeAnnot q loadC wpC) + nexec false true (btimeAnnot q loadC wpC) = 1 ∧
      nexec true false (btimeAnnot q loadC wpC) + nexec true true (btimeAnnot q loadC wpC) = 2 := by
  unfold btimeAnnot
  split_ifs with hz
  · rw [nexec_annotOf, nexec_annotOf]
    exact ⟨rfl, rfl⟩
  · rw [nexec_annotOf, nexec_annotOf]
    have hp := q.params_ok (ZeroTimeGateODE.btpublicOK_of hq hz)
    obtain ⟨-, -, h0, h1, -⟩ := q.params.prepC_counts hp.tau_pos.le hp.nu_pos hp.mesh
    exact ⟨h0, h1⟩

end Preparations

/-! ### The endpoints -/

section Endpoints

open ContinuousLinearMap SparseHamiltonian.GateBinary SparseHamiltonian.GateBitBudget
  SparseHamiltonian.GeneralSparseAccess
open SparseHamiltonian.GateBinaryODE (Pub mLift SZ4)
open SparseHamiltonian.ZeroTimeGateODE (bprepC btprepC BPublicOK0 BZeroCase BTPublicOK0
  BTZeroCase)
open SparseHamiltonian.GeneralSparseODE (GPubT liftC nCallsN_liftC nGatesN_liftC)
open SparseHamiltonian.GeneralDecoderODE (BinDecode DW prepTD prepTI implDP prepD)
open NativeSparseBlockEncoding (Data Query)

set_option maxHeartbeats 8000000 in
/-- **Source executions of Theorem `ode:thm:gates` for sparse access of general size, constant
coefficients** (`ode_thm_gates_general`). For the protocol `nprotocol ((odePubG …).prep N 0 srcC) ḡ`
of that endpoint (fixed before the instance): the annotation `constAnnotI` at the general-size
implementation `implP N s 0` evaluates to its preparation and to each of its trials, every
annotated execution is the placed supplied circuit or its literal inverse, and along every
history: at most `40 ḡ` executions of each source circuit; the calls are the propagation calls
(at most `C ḡ q` per selected kind, none if `T = 0` or `η_H + η_D = 0`) plus the executions times
the calls inside each source circuit, in total at most that plus `40 ḡ` times those calls; the
gates are the propagation gates (at most `C ḡ (q (𝔟 + 1)³ + A_src)`) plus the executions times the
source gates. `C` is the constant of `ode_thm_gates_general`. -/
theorem ode_thm_gates_general_sources :
    ∃ C : ℝ, 0 < C ∧
      ∀ {X : Type u} {N s k b : ℕ} (D : GeneralSparseAccess.QData X N s k b) (bd : ℕ)
        (c0 etaH etaD T gbar ε r₀ rb : ℝ),
        2 ^ k < 2 * N → formal_binaryDecoder D c0 → comp_bits b bd [c0, T, etaH, etaD] →
        ∀ (hnd : formal_nondegenerate gbar (r₀ + T * rb))
        {Zs : Type} [Fintype Zs] [DecidableEq Zs]
        (srcC : Bool → List (NInstr ((Unit ⊕ Fin k) ⊕ Zs) (PY k b) Query)),
        (∀ c, ∀ i ∈ srcC c, i.Valid) →
        0 ≤ etaH → 0 ≤ etaD → 0 ≤ T → 0 < ε → ε ≤ 1 / 2 → 0 ≤ r₀ → 0 ≤ rb →
        aflat (constAnnotI (odePubG k s D.s_le_pow b c0 etaH etaD T gbar ε r₀ rb) (implP (k := k)
            (b := b) N s (fun _ => false)) srcC) = ((odePubG k s D.s_le_pow b c0 etaH etaD T gbar ε
            r₀ rb).prep N (fun _ => false) srcC) ∧
          AnnotOK (srcMacro (odePubG k s D.s_le_pow b c0 etaH etaD T gbar ε r₀ rb).pub.params (fun
              c => liftC (srcC c))) (constAnnotI (odePubG k s D.s_le_pow b c0 etaH etaD T gbar ε r₀
              rb) (implP (k := k) (b := b) N s (fun _ => false)) srcC) ∧
          (∀ j, aflat (atrial (constAnnotI (odePubG k s D.s_le_pow b c0 etaH etaD T gbar ε r₀ rb)
              (implP (k := k) (b := b) N s (fun _ => false)) srcC) j) = trialN ((odePubG k s
              D.s_le_pow b c0 etaH etaD T gbar ε r₀ rb).prep N (fun _ => false) srcC) j) ∧
          ∀ h : ODERepeatProtocol.Protocol.History (nprotocol ((odePubG k s D.s_le_pow b c0 etaH
              etaD T gbar ε r₀ rb).prep N (fun _ => false) srcC) gbar hnd.1),
            (∀ c : Bool, (srcExecs (constAnnotI (odePubG k s D.s_le_pow b c0 etaH etaD T gbar ε r₀
                rb) (implP (k := k) (b := b) N s (fun _ => false)) srcC) c h : ℝ) ≤ 40 * gbar) ∧
            (∀ c : Query → Bool, h.cost (wCallN c) =
              propCount ((odePubG k s D.s_le_pow b c0 etaH etaD T gbar ε r₀ rb).prep N (fun _ =>
                  false) (fun _ => ([] : List (NInstr ((Unit ⊕ Fin k) ⊕ Zs) (PY k b) Query))))
                  (wCallN c) h +
              ∑ c' : Bool, srcExecs (constAnnotI (odePubG k s D.s_le_pow b c0 etaH etaD T gbar ε r₀
                  rb) (implP (k := k) (b := b) N s (fun _ => false)) srcC) c' h * nCallsN c (srcC
                  c')) ∧
            (∀ c : Query → Bool, (propCount ((odePubG k s D.s_le_pow b c0 etaH etaD T gbar ε r₀
                rb).prep N (fun _ => false) (fun _ => ([] : List (NInstr ((Unit ⊕ Fin k) ⊕ Zs) (PY
                k b) Query)))) (wCallN c) h : ℝ) ≤
                if T = 0 ∨ etaH + etaD = 0 then 0 else
                  C * gbar * odeShape s T etaH etaD gbar ε *
                    ((if c Query.rowLocation then 1 else 0) +
                      (if c Query.columnLocation then 1 else 0) + (if c Query.value then 1 else
                          0))) ∧
            (∀ c : Query → Bool, (h.cost (wCallN c) : ℝ) ≤
              (if T = 0 ∨ etaH + etaD = 0 then 0 else
                  C * gbar * odeShape s T etaH etaD gbar ε *
                    ((if c Query.rowLocation then 1 else 0) +
                      (if c Query.columnLocation then 1 else 0) + (if c Query.value then 1 else
                          0))) +
                (40 * gbar * nCallsN c (srcC false) + 40 * gbar * nCallsN c (srcC true))) ∧
            h.cost wGateN =
              propCount ((odePubG k s D.s_le_pow b c0 etaH etaD T gbar ε r₀ rb).prep N (fun _ =>
                  false) (fun _ => ([] : List (NInstr ((Unit ⊕ Fin k) ⊕ Zs) (PY k b) Query))))
                  wGateN h +
              ∑ c' : Bool, srcExecs (constAnnotI (odePubG k s D.s_le_pow b c0 etaH etaD T gbar ε r₀
                  rb) (implP (k := k) (b := b) N s (fun _ => false)) srcC) c' h * nGatesN (srcC c')
                  ∧
            (propCount ((odePubG k s D.s_le_pow b c0 etaH etaD T gbar ε r₀ rb).prep N (fun _ =>
                false) (fun _ => ([] : List (NInstr ((Unit ⊕ Fin k) ⊕ Zs) (PY k b) Query)))) wGateN
                h : ℝ) ≤
              C * gbar * (odeShape s T etaH etaD gbar ε *
                (bitB bd N 0 0 (odeShape s T etaH etaD gbar ε) gbar ε + 1) ^ 3 + Fintype.card Zs)
                    := by
  obtain ⟨C₀, hC₀, H⟩ := ode_thm_gates_general.{u}
  refine ⟨C₀, hC₀, ?_⟩
  intro X N s k b D bd c0 etaH etaD T gbar ε r₀ rb hk hF hbits hnd Zs _ _ srcC hsrcV hH hD hT hε
    hε2 hr0 hrb
  obtain ⟨-, hG', -, hC', -⟩ := H D bd c0 etaH etaD T gbar ε r₀ rb hk hF hbits hnd
    (fun _ => ([] : List (NInstr ((Unit ⊕ Fin k) ⊕ Zs) (PY k b) Query))) (by simp) hH hD hT hε hε2
      hr0 hrb
  have hq : BPublicOK0 (odePubG k s D.s_le_pow b c0 etaH etaD T gbar ε r₀ rb).pub := by
    rw [show (odePubG k s D.s_le_pow b c0 etaH etaD T gbar ε r₀ rb).pub = odePub (k + 1) (sbP s)
        ((sbP_le D.s_le_pow).trans (Nat.le_succ k)) b c0 etaH etaD T gbar ε r₀ rb from rfl]
    exact odePub_ok _ hF.hb hF.hc0 hH hD hT hnd.1 hε hε2 hr0 hrb hnd.2
  have hflat : aflat (constAnnotI (odePubG k s D.s_le_pow b c0 etaH etaD T gbar ε r₀ rb) (implP (k
      := k) (b := b) N s (fun _ => false)) srcC) = ((odePubG k s D.s_le_pow b c0 etaH etaD T gbar ε
      r₀ rb).prep N (fun _ => false) srcC) := by
    rw [aflat_constAnnotI]
    rfl
  have hok := annotOK_constAnnotI (odePubG k s D.s_le_pow b c0 etaH etaD T gbar ε r₀ rb) (implP (k
      := k) (b := b) N s (fun _ => false)) srcC
  have herase : aflat (aerase (constAnnotI (odePubG k s D.s_le_pow b c0 etaH etaD T gbar ε r₀ rb)
      (implP (k := k) (b := b) N s (fun _ => false)) srcC)) = ((odePubG k s D.s_le_pow b c0 etaH
      etaD T gbar ε r₀ rb).prep N (fun _ => false) (fun _ => ([] : List (NInstr ((Unit ⊕ Fin k) ⊕
      Zs) (PY k b) Query)))) := by
    rw [aerase_constAnnotI, aflat_constAnnotI]
    rfl
  refine ⟨hflat, hok, fun j => (aflat_atrial _ j).trans (congrArg (fun P => trialN P j) hflat),
    fun h => ?_⟩
  have hexec : ∀ c : Bool, (srcExecs (constAnnotI (odePubG k s D.s_le_pow b c0 etaH etaD T gbar ε
      r₀ rb) (implP (k := k) (b := b) N s (fun _ => false)) srcC) c h : ℝ) ≤ 40 * gbar := by
    intro c
    have h1 := nhistory_exec_le _ hflat gbar hnd.1 c h
    have h2 : ((nexec c false (constAnnotI (odePubG k s D.s_le_pow b c0 etaH etaD T gbar ε r₀ rb)
        (implP (k := k) (b := b) N s (fun _ => false)) srcC) : ℝ) + nexec c true (constAnnotI
        (odePubG k s D.s_le_pow b c0 etaH etaD T gbar ε r₀ rb) (implP (k := k) (b := b) N s (fun _
        => false)) srcC)) = 1 := by
      exact_mod_cast nexec_constAnnotI _ hq (implP (k := k) (b := b) N s (fun _ => false)) srcC c
    rw [h2, mul_one] at h1
    exact h1
  have hprop : ∀ c : Query → Bool, (propCount ((odePubG k s D.s_le_pow b c0 etaH etaD T gbar ε r₀
      rb).prep N (fun _ => false) (fun _ => ([] : List (NInstr ((Unit ⊕ Fin k) ⊕ Zs) (PY k b)
      Query)))) (wCallN c) h : ℝ) ≤
        if T = 0 ∨ etaH + etaD = 0 then 0 else
          C₀ * gbar * odeShape s T etaH etaD gbar ε *
                    ((if c Query.rowLocation then 1 else 0) +
                      (if c Query.columnLocation then 1 else 0) + (if c Query.value then 1 else 0))
                          := by
    intro c
    have h1 := propCount_le ((odePubG k s D.s_le_pow b c0 etaH etaD T gbar ε r₀ rb).prep N (fun _
        => false) srcC) ((odePubG k s D.s_le_pow b c0 etaH etaD T gbar ε r₀ rb).prep N (fun _ =>
        false) (fun _ => ([] : List (NInstr ((Unit ⊕ Fin k) ⊕ Zs) (PY k b) Query)))) gbar hnd.1
        (wCallN c) h
    have h2 := hC' c
    simp only [nCallsN, List.countP_nil, Nat.cast_zero, add_zero, mul_zero] at h2
    exact h1.trans h2
  refine ⟨hexec, fun c => ?_, hprop, fun c => ?_, ?_, ?_⟩
  · have e := nhistory_calls_src _ _ hflat hok (fun b adj => ninv_srcMacro _ _ b adj) gbar hnd.1 c
      (fun b => nCallsN c (srcC b))
      (fun b adj => by rw [nCallsN_srcMacro, nCallsN_liftC]; try rfl) h
    rw [herase] at e
    exact e
  · exact nhistory_calls_le _ _ hflat herase hok (fun b adj => ninv_srcMacro _ _ b adj) gbar hnd.1 c
      (fun b => nCallsN c (srcC b))
      (fun b adj => by rw [nCallsN_srcMacro, nCallsN_liftC]; try rfl)
      (fun _ => 40 * gbar) _ h hexec (hprop c)
  · have e := nhistory_gates_src _ _ hflat hok (fun b adj => ninv_srcMacro _ _ b adj) gbar hnd.1
      (fun b => nGatesN (srcC b))
      (fun b adj => by rw [nGatesN_srcMacro, nGatesN_liftC]; try rfl) h
    rw [herase] at e
    exact e
  · have h1 := propCount_le ((odePubG k s D.s_le_pow b c0 etaH etaD T gbar ε r₀ rb).prep N (fun _
      => false) srcC) ((odePubG k s D.s_le_pow b c0 etaH etaD T gbar ε r₀ rb).prep N (fun _ =>
      false) (fun _ => ([] : List (NInstr ((Unit ⊕ Fin k) ⊕ Zs) (PY k b) Query)))) gbar hnd.1
      wGateN h
    simp only [nGatesN, List.countP_nil, Nat.cast_zero, add_zero] at hG'
    exact h1.trans hG'

set_option maxHeartbeats 8000000 in
/-- **Source executions of the time-dependent Theorem `ode:thm:gates`, uniform mesh**
(`ode_thm_gates_time`). For the protocol `nprotocol (btprepC (odePubT …) loadC wpC) (2ḡ)` of that
endpoint (fixed before the instance): the annotation `btimeAnnot` evaluates to its preparation and
to each of its trials, every annotated execution is the placed loading circuit (`b = false`) or
weight-preparation circuit (`b = true`), or its literal inverse, and along every history: at most
`80 ḡ` executions of the loading circuit and `160 ḡ` of the weight-preparation circuit; the calls
and gates are the propagation part (at most `C ḡ q` calls per selected kind, none if `T = 0` or
`η_H + η_D = 0`, and `C ḡ (q (𝔟 + 1)³ + A_src)` gates) plus the executions times the calls and
gates of the two circuits; in total at most the propagation bound plus
`80 ḡ Q_load + 160 ḡ Q_wp` calls. `C` is the constant of `ode_thm_gates_time`. -/
theorem ode_thm_gates_time_sources :
    ∃ C : ℝ, 0 < C ∧
      ∀ {X : Type u} {n : Type v} [Fintype n] [DecidableEq n] {k b : ℕ} (sb bd : ℕ)
        (hsb : sb ≤ k) (c0 etaH etaD T gbar ε : ℝ),
        ∀ m : ℕ, odeMesh k sb hsb b c0 etaH etaD T gbar ε ≤ m →
        ∀ (D : Data (X × Fin (2 ^ m)) n (Cfg (VW b)) (2 ^ sb)) (en : Cfg (Fin k) ≃ n)
          (_ : formal_binaryInput D en sb c0) (_ : comp_bits b bd [c0, T, etaH, etaD])
          (hg : formal_gbarOne gbar)
          {Zs : Type} [Fintype Zs] [DecidableEq Zs]
          (loadC : List (NInstr ((Fin (m + 1) ⊕ Fin k) ⊕ Zs) (Fin m ⊕ PY k b) Query))
          (wpC : List (NInstr (Fin (m + 1) ⊕ Zs) (Fin m ⊕ PY k b) Query)),
          (∀ i ∈ loadC, i.Valid) → (∀ i ∈ wpC, i.Valid) →
          0 ≤ etaH → 0 ≤ etaD → 0 ≤ T → 0 < ε → ε ≤ 1 / 2 →
          aflat (btimeAnnot (odePubT k sb hsb b c0 etaH etaD T gbar ε m) loadC wpC) = (btprepC
              (odePubT k sb hsb b c0 etaH etaD T gbar ε m) loadC wpC) ∧
          AnnotOK (tsrcMacro (odePubT k sb hsb b c0 etaH etaD T gbar ε m).params loadC wpC)
              (btimeAnnot (odePubT k sb hsb b c0 etaH etaD T gbar ε m) loadC wpC) ∧
          (∀ j, aflat (atrial (btimeAnnot (odePubT k sb hsb b c0 etaH etaD T gbar ε m) loadC wpC)
              j) = trialN (btprepC (odePubT k sb hsb b c0 etaH etaD T gbar ε m) loadC wpC) j) ∧
          ∀ h : ODERepeatProtocol.Protocol.History (nprotocol (btprepC (odePubT k sb hsb b c0 etaH
              etaD T gbar ε m) loadC wpC) (2 * gbar)
              (one_le_two_mul hg)),
            (srcExecs (btimeAnnot (odePubT k sb hsb b c0 etaH etaD T gbar ε m) loadC wpC) false h :
                ℝ) ≤ 80 * gbar ∧
            (srcExecs (btimeAnnot (odePubT k sb hsb b c0 etaH etaD T gbar ε m) loadC wpC) true h :
                ℝ) ≤ 160 * gbar ∧
            (∀ c : Query → Bool, h.cost (wCallN c) =
              propCount (btprepC (odePubT k sb hsb b c0 etaH etaD T gbar ε m) ([] : List (NInstr
                  ((Fin (m + 1) ⊕ Fin k) ⊕ Zs) (Fin m ⊕ PY k b) Query))
                ([] : List (NInstr (Fin (m + 1) ⊕ Zs) (Fin m ⊕ PY k b) Query))) (wCallN c) h +
              ∑ b'' : Bool, srcExecs (btimeAnnot (odePubT k sb hsb b c0 etaH etaD T gbar ε m) loadC
                  wpC) b'' h *
                (if b'' then nCallsN c wpC else nCallsN c loadC)) ∧
            (∀ c : Query → Bool, (propCount (btprepC (odePubT k sb hsb b c0 etaH etaD T gbar ε m)
                ([] : List (NInstr ((Fin (m + 1) ⊕ Fin k) ⊕ Zs) (Fin m ⊕ PY k b) Query))
                ([] : List (NInstr (Fin (m + 1) ⊕ Zs) (Fin m ⊕ PY k b) Query))) (wCallN c) h : ℝ) ≤
                if T = 0 ∨ etaH + etaD = 0 then 0 else
                  C * gbar * odeShape ((2 ^ sb : ℕ) : ℝ) T etaH etaD gbar ε *
                    ((if c Query.rowLocation then 1 else 0) +
                      (if c Query.columnLocation then 1 else 0) + (if c Query.value then 1 else
                          0))) ∧
            (∀ c : Query → Bool, (h.cost (wCallN c) : ℝ) ≤
              (if T = 0 ∨ etaH + etaD = 0 then 0 else
                  C * gbar * odeShape ((2 ^ sb : ℕ) : ℝ) T etaH etaD gbar ε *
                    ((if c Query.rowLocation then 1 else 0) +
                      (if c Query.columnLocation then 1 else 0) + (if c Query.value then 1 else
                          0))) +
                (80 * gbar * nCallsN c loadC + 160 * gbar * nCallsN c wpC)) ∧
            h.cost wGateN =
              propCount (btprepC (odePubT k sb hsb b c0 etaH etaD T gbar ε m) ([] : List (NInstr
                  ((Fin (m + 1) ⊕ Fin k) ⊕ Zs) (Fin m ⊕ PY k b) Query))
                ([] : List (NInstr (Fin (m + 1) ⊕ Zs) (Fin m ⊕ PY k b) Query))) wGateN h +
              ∑ b'' : Bool, srcExecs (btimeAnnot (odePubT k sb hsb b c0 etaH etaD T gbar ε m) loadC
                  wpC) b'' h * (if b'' then nGatesN wpC else nGatesN loadC) ∧
            (propCount (btprepC (odePubT k sb hsb b c0 etaH etaD T gbar ε m) ([] : List (NInstr
                ((Fin (m + 1) ⊕ Fin k) ⊕ Zs) (Fin m ⊕ PY k b) Query))
                ([] : List (NInstr (Fin (m + 1) ⊕ Zs) (Fin m ⊕ PY k b) Query))) wGateN h : ℝ) ≤
              C * gbar * (odeShape ((2 ^ sb : ℕ) : ℝ) T etaH etaD gbar ε *
                (bitB bd (Fintype.card n) (2 ^ m) (2 ^ m)
                  (odeShape ((2 ^ sb : ℕ) : ℝ) T etaH etaD gbar ε) gbar ε + 1) ^ 3 + Fintype.card
                      Zs) := by
  obtain ⟨C₀, hC₀, H⟩ := ode_thm_gates_time.{u, v}
  refine ⟨C₀, hC₀, ?_⟩
  intro X n _ _ k b sb bd hsb c0 etaH etaD T gbar ε m hm D en hF hbits hg Zs _ _ loadC wpC hloadV
    hwpV hH hD hT hε hε2
  obtain ⟨-, hG', -, hC', -⟩ := H sb bd hsb c0 etaH etaD T gbar ε m hm D en hF hbits hg ([] : List
      (NInstr ((Fin (m + 1) ⊕ Fin k) ⊕ Zs) (Fin m ⊕ PY k b) Query))
    ([] : List (NInstr (Fin (m + 1) ⊕ Zs) (Fin m ⊕ PY k b) Query)) (by simp) (by simp) hH hD hT hε
        hε2
  have hq : BTPublicOK0 (odePubT k sb hsb b c0 etaH etaD T gbar ε m) := odePubT_ok hsb hF.hb hF.hc0
      hH hD hT hg hε hε2 hm
  have hflat : aflat (btimeAnnot (odePubT k sb hsb b c0 etaH etaD T gbar ε m) loadC wpC) = (btprepC
      (odePubT k sb hsb b c0 etaH etaD T gbar ε m) loadC wpC) := aflat_btimeAnnot (odePubT k sb hsb
      b c0 etaH etaD T gbar ε m) loadC wpC
  have hok := annotOK_btimeAnnot (odePubT k sb hsb b c0 etaH etaD T gbar ε m) loadC wpC
  have herase : aflat (aerase (btimeAnnot (odePubT k sb hsb b c0 etaH etaD T gbar ε m) loadC wpC))
      = (btprepC (odePubT k sb hsb b c0 etaH etaD T gbar ε m) ([] : List (NInstr ((Fin (m + 1) ⊕
      Fin k) ⊕ Zs) (Fin m ⊕ PY k b) Query))
                ([] : List (NInstr (Fin (m + 1) ⊕ Zs) (Fin m ⊕ PY k b) Query))) := by
    rw [aerase_btimeAnnot, aflat_btimeAnnot]
    rfl
  obtain ⟨hn0, hn1⟩ := nexec_btimeAnnot (odePubT k sb hsb b c0 etaH etaD T gbar ε m) hq loadC wpC
  refine ⟨hflat, hok, fun j => (aflat_atrial _ j).trans (congrArg (fun P => trialN P j) hflat),
    fun h => ?_⟩
  have hexec0 : (srcExecs (btimeAnnot (odePubT k sb hsb b c0 etaH etaD T gbar ε m) loadC wpC) false
      h : ℝ) ≤ 80 * gbar := by
    have h1 := nhistory_exec_le _ hflat _ (one_le_two_mul hg) false h
    have h2 : ((nexec false false (btimeAnnot (odePubT k sb hsb b c0 etaH etaD T gbar ε m) loadC
        wpC) : ℝ) + nexec false true (btimeAnnot (odePubT k sb hsb b c0 etaH etaD T gbar ε m) loadC
        wpC)) = 1 := by
      exact_mod_cast hn0
    rw [h2] at h1
    exact h1.trans (le_of_eq (by ring))
  have hexec1 : (srcExecs (btimeAnnot (odePubT k sb hsb b c0 etaH etaD T gbar ε m) loadC wpC) true
      h : ℝ) ≤ 160 * gbar := by
    have h1 := nhistory_exec_le _ hflat _ (one_le_two_mul hg) true h
    have h2 : ((nexec true false (btimeAnnot (odePubT k sb hsb b c0 etaH etaD T gbar ε m) loadC
        wpC) : ℝ) + nexec true true (btimeAnnot (odePubT k sb hsb b c0 etaH etaD T gbar ε m) loadC
        wpC)) = 2 := by
      exact_mod_cast hn1
    rw [h2] at h1
    exact h1.trans (le_of_eq (by ring))
  have hprop : ∀ c : Query → Bool, (propCount (btprepC (odePubT k sb hsb b c0 etaH etaD T gbar ε m)
      ([] : List (NInstr ((Fin (m + 1) ⊕ Fin k) ⊕ Zs) (Fin m ⊕ PY k b) Query))
                ([] : List (NInstr (Fin (m + 1) ⊕ Zs) (Fin m ⊕ PY k b) Query))) (wCallN c) h : ℝ) ≤
        if T = 0 ∨ etaH + etaD = 0 then 0 else
          C₀ * gbar * odeShape ((2 ^ sb : ℕ) : ℝ) T etaH etaD gbar ε *
                    ((if c Query.rowLocation then 1 else 0) +
                      (if c Query.columnLocation then 1 else 0) + (if c Query.value then 1 else 0))
                          := by
    intro c
    have h1 := propCount_le (btprepC (odePubT k sb hsb b c0 etaH etaD T gbar ε m) loadC wpC)
        (btprepC (odePubT k sb hsb b c0 etaH etaD T gbar ε m) ([] : List (NInstr ((Fin (m + 1) ⊕
        Fin k) ⊕ Zs) (Fin m ⊕ PY k b) Query))
                ([] : List (NInstr (Fin (m + 1) ⊕ Zs) (Fin m ⊕ PY k b) Query))) _ (one_le_two_mul
                    hg) (wCallN c) h
    have h2 := hC' c
    simp only [nCallsN, List.countP_nil, Nat.cast_zero, add_zero, mul_zero] at h2
    exact h1.trans h2
  refine ⟨hexec0, hexec1, fun c => ?_, hprop, fun c => ?_, ?_, ?_⟩
  · have e := nhistory_calls_src _ _ hflat hok (fun b adj => ninv_tsrcMacro _ _ _ b adj) _ _ c
      (fun b'' => if b'' then nCallsN c wpC else nCallsN c loadC)
      (fun b adj => by rw [nCallsN_tsrcMacro]; try rfl) h
    rw [herase] at e
    exact e
  · exact nhistory_calls_le _ _ hflat herase hok (fun b adj => ninv_tsrcMacro _ _ _ b adj) _ _ c
      (fun b'' => if b'' then nCallsN c wpC else nCallsN c loadC)
      (fun b adj => by rw [nCallsN_tsrcMacro]; try rfl)
      (fun b'' => if b'' then 160 * gbar else 80 * gbar) _ h
      (fun b'' => by cases b'' <;> simpa using (by assumption)) (hprop c)
  · have e := nhistory_gates_src _ _ hflat hok (fun b adj => ninv_tsrcMacro _ _ _ b adj) _ _
      (fun b'' => if b'' then nGatesN wpC else nGatesN loadC)
      (fun b adj => by rw [nGatesN_tsrcMacro]; try rfl) h
    rw [herase] at e
    exact e
  · have h1 := propCount_le (btprepC (odePubT k sb hsb b c0 etaH etaD T gbar ε m) loadC wpC)
      (btprepC (odePubT k sb hsb b c0 etaH etaD T gbar ε m) ([] : List (NInstr ((Fin (m + 1) ⊕ Fin
      k) ⊕ Zs) (Fin m ⊕ PY k b) Query))
                ([] : List (NInstr (Fin (m + 1) ⊕ Zs) (Fin m ⊕ PY k b) Query))) _ (one_le_two_mul
                    hg) wGateN h
    simp only [nGatesN, List.countP_nil, Nat.cast_zero, add_zero, mul_zero] at hG'
    exact h1.trans hG'

set_option maxHeartbeats 8000000 in
/-- **Source executions of the time-dependent Theorem `ode:thm:gates` for sparse access of
general size** (`ode_thm_gates_time_general`): as `ode_thm_gates_time_sources` for the protocol
`nprotocol ((odePubTG …).prep N 0 loadC wpC) (2ḡ)` of that endpoint (annotation `timeAnnot` at the
general-size implementation `implP N s 0`). `C` is the constant of
`ode_thm_gates_time_general`. -/
theorem ode_thm_gates_time_general_sources :
    ∃ C : ℝ, 0 < C ∧
      ∀ {X : Type u} {N s k b : ℕ} (bd : ℕ) (c0 etaH etaD T gbar ε : ℝ) (m : ℕ)
        (D : GeneralSparseAccess.QData (X × Fin (2 ^ m)) N s k b),
        odeMeshG k s D.s_le_pow b c0 etaH etaD T gbar ε ≤ m →
        2 ^ k < 2 * N → formal_binaryDecoder D c0 → comp_bits b bd [c0, T, etaH, etaD] →
        ∀ (hg : formal_gbarOne gbar) {Zs : Type} [Fintype Zs] [DecidableEq Zs]
          (loadC : List (NInstr ((Fin (m + 1) ⊕ Fin k) ⊕ Zs) (Fin m ⊕ PY k b) Query))
          (wpC : List (NInstr (Fin (m + 1) ⊕ Zs) (Fin m ⊕ PY k b) Query)),
          (∀ i ∈ loadC, i.Valid) → (∀ i ∈ wpC, i.Valid) →
          0 ≤ etaH → 0 ≤ etaD → 0 ≤ T → 0 < ε → ε ≤ 1 / 2 →
          aflat (timeAnnot (odePubTG k s D.s_le_pow b c0 etaH etaD T gbar ε m) (implP (k := k) (b
              := b) N s (fun _ => false)) loadC wpC) = ((odePubTG k s D.s_le_pow b c0 etaH etaD T
              gbar ε m).prep N (fun _ => false) loadC wpC) ∧
          AnnotOK (tsrcMacro (odePubTG k s D.s_le_pow b c0 etaH etaD T gbar ε m).pub.params (liftC
              loadC) wpC) (timeAnnot (odePubTG k s D.s_le_pow b c0 etaH etaD T gbar ε m) (implP (k
              := k) (b := b) N s (fun _ => false)) loadC wpC) ∧
          (∀ j, aflat (atrial (timeAnnot (odePubTG k s D.s_le_pow b c0 etaH etaD T gbar ε m) (implP
              (k := k) (b := b) N s (fun _ => false)) loadC wpC) j) = trialN ((odePubTG k s
              D.s_le_pow b c0 etaH etaD T gbar ε m).prep N (fun _ => false) loadC wpC) j) ∧
          ∀ h : ODERepeatProtocol.Protocol.History (nprotocol ((odePubTG k s D.s_le_pow b c0 etaH
              etaD T gbar ε m).prep N (fun _ => false) loadC wpC) (2 * gbar)
              (one_le_two_mul hg)),
            (srcExecs (timeAnnot (odePubTG k s D.s_le_pow b c0 etaH etaD T gbar ε m) (implP (k :=
                k) (b := b) N s (fun _ => false)) loadC wpC) false h : ℝ) ≤ 80 * gbar ∧
            (srcExecs (timeAnnot (odePubTG k s D.s_le_pow b c0 etaH etaD T gbar ε m) (implP (k :=
                k) (b := b) N s (fun _ => false)) loadC wpC) true h : ℝ) ≤ 160 * gbar ∧
            (∀ c : Query → Bool, h.cost (wCallN c) =
              propCount ((odePubTG k s D.s_le_pow b c0 etaH etaD T gbar ε m).prep N (fun _ =>
                  false) ([] : List (NInstr ((Fin (m + 1) ⊕ Fin k) ⊕ Zs) (Fin m ⊕ PY k b) Query))
                ([] : List (NInstr (Fin (m + 1) ⊕ Zs) (Fin m ⊕ PY k b) Query))) (wCallN c) h +
              ∑ b'' : Bool, srcExecs (timeAnnot (odePubTG k s D.s_le_pow b c0 etaH etaD T gbar ε m)
                  (implP (k := k) (b := b) N s (fun _ => false)) loadC wpC) b'' h *
                (if b'' then nCallsN c wpC else nCallsN c loadC)) ∧
            (∀ c : Query → Bool, (propCount ((odePubTG k s D.s_le_pow b c0 etaH etaD T gbar ε
                m).prep N (fun _ => false) ([] : List (NInstr ((Fin (m + 1) ⊕ Fin k) ⊕ Zs) (Fin m ⊕
                PY k b) Query))
                ([] : List (NInstr (Fin (m + 1) ⊕ Zs) (Fin m ⊕ PY k b) Query))) (wCallN c) h : ℝ) ≤
                if T = 0 ∨ etaH + etaD = 0 then 0 else
                  C * gbar * odeShape s T etaH etaD gbar ε *
                    ((if c Query.rowLocation then 1 else 0) +
                      (if c Query.columnLocation then 1 else 0) + (if c Query.value then 1 else
                          0))) ∧
            (∀ c : Query → Bool, (h.cost (wCallN c) : ℝ) ≤
              (if T = 0 ∨ etaH + etaD = 0 then 0 else
                  C * gbar * odeShape s T etaH etaD gbar ε *
                    ((if c Query.rowLocation then 1 else 0) +
                      (if c Query.columnLocation then 1 else 0) + (if c Query.value then 1 else
                          0))) +
                (80 * gbar * nCallsN c loadC + 160 * gbar * nCallsN c wpC)) ∧
            h.cost wGateN =
              propCount ((odePubTG k s D.s_le_pow b c0 etaH etaD T gbar ε m).prep N (fun _ =>
                  false) ([] : List (NInstr ((Fin (m + 1) ⊕ Fin k) ⊕ Zs) (Fin m ⊕ PY k b) Query))
                ([] : List (NInstr (Fin (m + 1) ⊕ Zs) (Fin m ⊕ PY k b) Query))) wGateN h +
              ∑ b'' : Bool, srcExecs (timeAnnot (odePubTG k s D.s_le_pow b c0 etaH etaD T gbar ε m)
                  (implP (k := k) (b := b) N s (fun _ => false)) loadC wpC) b'' h * (if b'' then
                  nGatesN wpC else nGatesN loadC) ∧
            (propCount ((odePubTG k s D.s_le_pow b c0 etaH etaD T gbar ε m).prep N (fun _ => false)
                ([] : List (NInstr ((Fin (m + 1) ⊕ Fin k) ⊕ Zs) (Fin m ⊕ PY k b) Query))
                ([] : List (NInstr (Fin (m + 1) ⊕ Zs) (Fin m ⊕ PY k b) Query))) wGateN h : ℝ) ≤
              C * gbar * (odeShape s T etaH etaD gbar ε *
                (bitB bd N (2 ^ m) (2 ^ m) (odeShape s T etaH etaD gbar ε) gbar ε + 1) ^ 3 +
                Fintype.card Zs) := by
  obtain ⟨C₀, hC₀, H⟩ := ode_thm_gates_time_general.{u}
  refine ⟨C₀, hC₀, ?_⟩
  intro X N s k b bd c0 etaH etaD T gbar ε m D hm hk hF hbits hg Zs _ _ loadC wpC hloadV hwpV hH
    hD hT hε hε2
  obtain ⟨-, hG', -, hC', -⟩ := H bd c0 etaH etaD T gbar ε m D hm hk hF hbits hg ([] : List (NInstr
      ((Fin (m + 1) ⊕ Fin k) ⊕ Zs) (Fin m ⊕ PY k b) Query))
    ([] : List (NInstr (Fin (m + 1) ⊕ Zs) (Fin m ⊕ PY k b) Query)) (by simp) (by simp) hH hD hT hε
        hε2
  have hq : BTPublicOK0 (odePubTG k s D.s_le_pow b c0 etaH etaD T gbar ε m).pub := by
    rw [odePubTG_pub]
    exact odePubT_ok _ hF.hb hF.hc0 hH hD hT hg hε hε2 hm
  have hflat : aflat (timeAnnot (odePubTG k s D.s_le_pow b c0 etaH etaD T gbar ε m) (implP (k := k)
      (b := b) N s (fun _ => false)) loadC wpC) = ((odePubTG k s D.s_le_pow b c0 etaH etaD T gbar ε
      m).prep N (fun _ => false) loadC wpC) := by
    rw [aflat_timeAnnot]
    rfl
  have hok := annotOK_timeAnnot (odePubTG k s D.s_le_pow b c0 etaH etaD T gbar ε m) (implP (k := k)
      (b := b) N s (fun _ => false)) loadC wpC
  have herase : aflat (aerase (timeAnnot (odePubTG k s D.s_le_pow b c0 etaH etaD T gbar ε m) (implP
      (k := k) (b := b) N s (fun _ => false)) loadC wpC)) = ((odePubTG k s D.s_le_pow b c0 etaH
      etaD T gbar ε m).prep N (fun _ => false) ([] : List (NInstr ((Fin (m + 1) ⊕ Fin k) ⊕ Zs) (Fin
      m ⊕ PY k b) Query))
                ([] : List (NInstr (Fin (m + 1) ⊕ Zs) (Fin m ⊕ PY k b) Query))) := by
    rw [aerase_timeAnnot, aflat_timeAnnot]
    rfl
  obtain ⟨hn0, hn1⟩ := nexec_timeAnnot (odePubTG k s D.s_le_pow b c0 etaH etaD T gbar ε m) hq
      (implP (k := k) (b := b) N s (fun _ => false)) loadC wpC
  refine ⟨hflat, hok, fun j => (aflat_atrial _ j).trans (congrArg (fun P => trialN P j) hflat),
    fun h => ?_⟩
  have hexec0 : (srcExecs (timeAnnot (odePubTG k s D.s_le_pow b c0 etaH etaD T gbar ε m) (implP (k
      := k) (b := b) N s (fun _ => false)) loadC wpC) false h : ℝ) ≤ 80 * gbar := by
    have h1 := nhistory_exec_le _ hflat _ (one_le_two_mul hg) false h
    have h2 : ((nexec false false (timeAnnot (odePubTG k s D.s_le_pow b c0 etaH etaD T gbar ε m)
        (implP (k := k) (b := b) N s (fun _ => false)) loadC wpC) : ℝ) + nexec false true
        (timeAnnot (odePubTG k s D.s_le_pow b c0 etaH etaD T gbar ε m) (implP (k := k) (b := b) N s
        (fun _ => false)) loadC wpC)) = 1 := by
      exact_mod_cast hn0
    rw [h2] at h1
    exact h1.trans (le_of_eq (by ring))
  have hexec1 : (srcExecs (timeAnnot (odePubTG k s D.s_le_pow b c0 etaH etaD T gbar ε m) (implP (k
      := k) (b := b) N s (fun _ => false)) loadC wpC) true h : ℝ) ≤ 160 * gbar := by
    have h1 := nhistory_exec_le _ hflat _ (one_le_two_mul hg) true h
    have h2 : ((nexec true false (timeAnnot (odePubTG k s D.s_le_pow b c0 etaH etaD T gbar ε m)
        (implP (k := k) (b := b) N s (fun _ => false)) loadC wpC) : ℝ) + nexec true true (timeAnnot
        (odePubTG k s D.s_le_pow b c0 etaH etaD T gbar ε m) (implP (k := k) (b := b) N s (fun _ =>
        false)) loadC wpC)) = 2 := by
      exact_mod_cast hn1
    rw [h2] at h1
    exact h1.trans (le_of_eq (by ring))
  have hprop : ∀ c : Query → Bool, (propCount ((odePubTG k s D.s_le_pow b c0 etaH etaD T gbar ε
      m).prep N (fun _ => false) ([] : List (NInstr ((Fin (m + 1) ⊕ Fin k) ⊕ Zs) (Fin m ⊕ PY k b)
      Query))
                ([] : List (NInstr (Fin (m + 1) ⊕ Zs) (Fin m ⊕ PY k b) Query))) (wCallN c) h : ℝ) ≤
        if T = 0 ∨ etaH + etaD = 0 then 0 else
          C₀ * gbar * odeShape s T etaH etaD gbar ε *
                    ((if c Query.rowLocation then 1 else 0) +
                      (if c Query.columnLocation then 1 else 0) + (if c Query.value then 1 else 0))
                          := by
    intro c
    have h1 := propCount_le ((odePubTG k s D.s_le_pow b c0 etaH etaD T gbar ε m).prep N (fun _ =>
        false) loadC wpC) ((odePubTG k s D.s_le_pow b c0 etaH etaD T gbar ε m).prep N (fun _ =>
        false) ([] : List (NInstr ((Fin (m + 1) ⊕ Fin k) ⊕ Zs) (Fin m ⊕ PY k b) Query))
                ([] : List (NInstr (Fin (m + 1) ⊕ Zs) (Fin m ⊕ PY k b) Query))) _ (one_le_two_mul
                    hg) (wCallN c) h
    have h2 := hC' c
    simp only [nCallsN, List.countP_nil, Nat.cast_zero, add_zero, mul_zero] at h2
    exact h1.trans h2
  refine ⟨hexec0, hexec1, fun c => ?_, hprop, fun c => ?_, ?_, ?_⟩
  · have e := nhistory_calls_src _ _ hflat hok (fun b adj => ninv_tsrcMacro _ _ _ b adj) _ _ c
      (fun b'' => if b'' then nCallsN c wpC else nCallsN c loadC)
      (fun b adj => by rw [nCallsN_tsrcMacro, nCallsN_liftC]; try rfl) h
    rw [herase] at e
    exact e
  · exact nhistory_calls_le _ _ hflat herase hok (fun b adj => ninv_tsrcMacro _ _ _ b adj) _ _ c
      (fun b'' => if b'' then nCallsN c wpC else nCallsN c loadC)
      (fun b adj => by rw [nCallsN_tsrcMacro, nCallsN_liftC]; try rfl)
      (fun b'' => if b'' then 160 * gbar else 80 * gbar) _ h
      (fun b'' => by cases b'' <;> simpa using (by assumption)) (hprop c)
  · have e := nhistory_gates_src _ _ hflat hok (fun b adj => ninv_tsrcMacro _ _ _ b adj) _ _
      (fun b'' => if b'' then nGatesN wpC else nGatesN loadC)
      (fun b adj => by rw [nGatesN_tsrcMacro, nGatesN_liftC]; try rfl) h
    rw [herase] at e
    exact e
  · have h1 := propCount_le ((odePubTG k s D.s_le_pow b c0 etaH etaD T gbar ε m).prep N (fun _ =>
      false) loadC wpC) ((odePubTG k s D.s_le_pow b c0 etaH etaD T gbar ε m).prep N (fun _ =>
      false) ([] : List (NInstr ((Fin (m + 1) ⊕ Fin k) ⊕ Zs) (Fin m ⊕ PY k b) Query))
                ([] : List (NInstr (Fin (m + 1) ⊕ Zs) (Fin m ⊕ PY k b) Query))) _ (one_le_two_mul
                    hg) wGateN h
    simp only [nGatesN, List.countP_nil, Nat.cast_zero, add_zero, mul_zero] at hG'
    exact h1.trans hG'

set_option maxHeartbeats 8000000 in
/-- **Source executions of the time-dependent Theorem `ode:thm:gates` with a binary entry
decoder** (`ode_thm_gates_time_decoder`): as `ode_thm_gates_time_sources` for the protocol
`nprotocol (prepTD (odePubTG …) N dc loadC wpC) (2ḡ)` of that endpoint (annotation `timeAnnot` at
the decoder implementation `implDP`; the propagation gates include the decoder cost `dc.cost`).
`C` is the constant of `ode_thm_gates_time_decoder`. -/
theorem ode_thm_gates_time_decoder_sources :
    ∃ C : ℝ, 0 < C ∧
      ∀ {X : Type u} {N s k b b' A : ℕ} (bd : ℕ) (c0 etaH etaD T gbar ε : ℝ) (m : ℕ)
        (D : GeneralSparseAccess.QData (X × Fin (2 ^ m)) N s k b) (dc : BinDecode b b' A),
        odeMeshG k s D.s_le_pow b' c0 etaH etaD T gbar ε ≤ m →
        2 ^ k < 2 * N → BinaryEntryDecoding D dc c0 → comp_bits b' bd [c0, T, etaH, etaD] →
        ∀ (hg : formal_gbarOne gbar) {Zs : Type} [Fintype Zs] [DecidableEq Zs]
          (loadC : List (NInstr ((Fin (m + 1) ⊕ Fin k) ⊕ Zs) (Fin m ⊕ PY k b) Query))
          (wpC : List (NInstr (Fin (m + 1) ⊕ Zs) (Fin m ⊕ PY k b) Query)),
          (∀ i ∈ loadC, i.Valid) → (∀ i ∈ wpC, i.Valid) →
          0 ≤ etaH → 0 ≤ etaD → 0 ≤ T → 0 < ε → ε ≤ 1 / 2 →
          aflat (timeAnnot (odePubTG k s D.s_le_pow b' c0 etaH etaD T gbar ε m) (implDP (k := k) N
              s (fun _ => false) dc) loadC wpC) = (prepTD (odePubTG k s D.s_le_pow b' c0 etaH etaD
              T gbar ε m) N dc loadC wpC) ∧
          AnnotOK (tsrcMacro (odePubTG k s D.s_le_pow b' c0 etaH etaD T gbar ε m).pub.params (liftC
              loadC) wpC) (timeAnnot (odePubTG k s D.s_le_pow b' c0 etaH etaD T gbar ε m) (implDP
              (k := k) N s (fun _ => false) dc) loadC wpC) ∧
          (∀ j, aflat (atrial (timeAnnot (odePubTG k s D.s_le_pow b' c0 etaH etaD T gbar ε m)
              (implDP (k := k) N s (fun _ => false) dc) loadC wpC) j) = trialN (prepTD (odePubTG k
              s D.s_le_pow b' c0 etaH etaD T gbar ε m) N dc loadC wpC) j) ∧
          ∀ h : ODERepeatProtocol.Protocol.History (nprotocol (prepTD (odePubTG k s D.s_le_pow b'
              c0 etaH etaD T gbar ε m) N dc loadC wpC) (2 * gbar)
              (one_le_two_mul hg)),
            (srcExecs (timeAnnot (odePubTG k s D.s_le_pow b' c0 etaH etaD T gbar ε m) (implDP (k :=
                k) N s (fun _ => false) dc) loadC wpC) false h : ℝ) ≤ 80 * gbar ∧
            (srcExecs (timeAnnot (odePubTG k s D.s_le_pow b' c0 etaH etaD T gbar ε m) (implDP (k :=
                k) N s (fun _ => false) dc) loadC wpC) true h : ℝ) ≤ 160 * gbar ∧
            (∀ c : Query → Bool, h.cost (wCallN c) =
              propCount (prepTD (odePubTG k s D.s_le_pow b' c0 etaH etaD T gbar ε m) N dc ([] :
                  List (NInstr ((Fin (m + 1) ⊕ Fin k) ⊕ Zs) (Fin m ⊕ PY k b) Query))
                ([] : List (NInstr (Fin (m + 1) ⊕ Zs) (Fin m ⊕ PY k b) Query))) (wCallN c) h +
              ∑ b'' : Bool, srcExecs (timeAnnot (odePubTG k s D.s_le_pow b' c0 etaH etaD T gbar ε
                  m) (implDP (k := k) N s (fun _ => false) dc) loadC wpC) b'' h *
                (if b'' then nCallsN c wpC else nCallsN c loadC)) ∧
            (∀ c : Query → Bool, (propCount (prepTD (odePubTG k s D.s_le_pow b' c0 etaH etaD T gbar
                ε m) N dc ([] : List (NInstr ((Fin (m + 1) ⊕ Fin k) ⊕ Zs) (Fin m ⊕ PY k b) Query))
                ([] : List (NInstr (Fin (m + 1) ⊕ Zs) (Fin m ⊕ PY k b) Query))) (wCallN c) h : ℝ) ≤
                if T = 0 ∨ etaH + etaD = 0 then 0 else
                  C * gbar * odeShape s T etaH etaD gbar ε *
                    ((if c Query.rowLocation then 1 else 0) +
                      (if c Query.columnLocation then 1 else 0) + (if c Query.value then 1 else
                          0))) ∧
            (∀ c : Query → Bool, (h.cost (wCallN c) : ℝ) ≤
              (if T = 0 ∨ etaH + etaD = 0 then 0 else
                  C * gbar * odeShape s T etaH etaD gbar ε *
                    ((if c Query.rowLocation then 1 else 0) +
                      (if c Query.columnLocation then 1 else 0) + (if c Query.value then 1 else
                          0))) +
                (80 * gbar * nCallsN c loadC + 160 * gbar * nCallsN c wpC)) ∧
            h.cost wGateN =
              propCount (prepTD (odePubTG k s D.s_le_pow b' c0 etaH etaD T gbar ε m) N dc ([] :
                  List (NInstr ((Fin (m + 1) ⊕ Fin k) ⊕ Zs) (Fin m ⊕ PY k b) Query))
                ([] : List (NInstr (Fin (m + 1) ⊕ Zs) (Fin m ⊕ PY k b) Query))) wGateN h +
              ∑ b'' : Bool, srcExecs (timeAnnot (odePubTG k s D.s_le_pow b' c0 etaH etaD T gbar ε
                  m) (implDP (k := k) N s (fun _ => false) dc) loadC wpC) b'' h * (if b'' then
                  nGatesN wpC else nGatesN loadC) ∧
            (propCount (prepTD (odePubTG k s D.s_le_pow b' c0 etaH etaD T gbar ε m) N dc ([] : List
                (NInstr ((Fin (m + 1) ⊕ Fin k) ⊕ Zs) (Fin m ⊕ PY k b) Query))
                ([] : List (NInstr (Fin (m + 1) ⊕ Zs) (Fin m ⊕ PY k b) Query))) wGateN h : ℝ) ≤
              C * gbar * (odeShape s T etaH etaD gbar ε *
                ((bitB bd N (2 ^ m) (2 ^ m) (odeShape s T etaH etaD gbar ε) gbar ε + 1) ^ 3 +
                    dc.cost) +
                Fintype.card Zs) := by
  obtain ⟨C₀, hC₀, H⟩ := ode_thm_gates_time_decoder.{u}
  refine ⟨C₀, hC₀, ?_⟩
  intro X N s k b b' A bd c0 etaH etaD T gbar ε m D dc hm hk hF hbits hg Zs _ _ loadC wpC hloadV
    hwpV hH hD hT hε hε2
  obtain ⟨-, hG', -, hC', -⟩ := H bd c0 etaH etaD T gbar ε m D dc hm hk hF hbits hg ([] : List
      (NInstr ((Fin (m + 1) ⊕ Fin k) ⊕ Zs) (Fin m ⊕ PY k b) Query))
    ([] : List (NInstr (Fin (m + 1) ⊕ Zs) (Fin m ⊕ PY k b) Query)) (by simp) (by simp) hH hD hT hε
        hε2
  have hq : BTPublicOK0 (odePubTG k s D.s_le_pow b' c0 etaH etaD T gbar ε m).pub := by
    rw [odePubTG_pub]
    exact odePubT_ok _ hF.hb hF.hc0 hH hD hT hg hε hε2 hm
  have hflat : aflat (timeAnnot (odePubTG k s D.s_le_pow b' c0 etaH etaD T gbar ε m) (implDP (k :=
      k) N s (fun _ => false) dc) loadC wpC) = (prepTD (odePubTG k s D.s_le_pow b' c0 etaH etaD T
      gbar ε m) N dc loadC wpC) := by
    rw [aflat_timeAnnot]
    rfl
  have hok := annotOK_timeAnnot (odePubTG k s D.s_le_pow b' c0 etaH etaD T gbar ε m) (implDP (k :=
      k) N s (fun _ => false) dc) loadC wpC
  have herase : aflat (aerase (timeAnnot (odePubTG k s D.s_le_pow b' c0 etaH etaD T gbar ε m)
      (implDP (k := k) N s (fun _ => false) dc) loadC wpC)) = (prepTD (odePubTG k s D.s_le_pow b'
      c0 etaH etaD T gbar ε m) N dc ([] : List (NInstr ((Fin (m + 1) ⊕ Fin k) ⊕ Zs) (Fin m ⊕ PY k
      b) Query))
                ([] : List (NInstr (Fin (m + 1) ⊕ Zs) (Fin m ⊕ PY k b) Query))) := by
    rw [aerase_timeAnnot, aflat_timeAnnot]
    rfl
  obtain ⟨hn0, hn1⟩ := nexec_timeAnnot (odePubTG k s D.s_le_pow b' c0 etaH etaD T gbar ε m) hq
      (implDP (k := k) N s (fun _ => false) dc) loadC wpC
  refine ⟨hflat, hok, fun j => (aflat_atrial _ j).trans (congrArg (fun P => trialN P j) hflat),
    fun h => ?_⟩
  have hexec0 : (srcExecs (timeAnnot (odePubTG k s D.s_le_pow b' c0 etaH etaD T gbar ε m) (implDP
      (k := k) N s (fun _ => false) dc) loadC wpC) false h : ℝ) ≤ 80 * gbar := by
    have h1 := nhistory_exec_le _ hflat _ (one_le_two_mul hg) false h
    have h2 : ((nexec false false (timeAnnot (odePubTG k s D.s_le_pow b' c0 etaH etaD T gbar ε m)
        (implDP (k := k) N s (fun _ => false) dc) loadC wpC) : ℝ) + nexec false true (timeAnnot
        (odePubTG k s D.s_le_pow b' c0 etaH etaD T gbar ε m) (implDP (k := k) N s (fun _ => false)
        dc) loadC wpC)) = 1 := by
      exact_mod_cast hn0
    rw [h2] at h1
    exact h1.trans (le_of_eq (by ring))
  have hexec1 : (srcExecs (timeAnnot (odePubTG k s D.s_le_pow b' c0 etaH etaD T gbar ε m) (implDP
      (k := k) N s (fun _ => false) dc) loadC wpC) true h : ℝ) ≤ 160 * gbar := by
    have h1 := nhistory_exec_le _ hflat _ (one_le_two_mul hg) true h
    have h2 : ((nexec true false (timeAnnot (odePubTG k s D.s_le_pow b' c0 etaH etaD T gbar ε m)
        (implDP (k := k) N s (fun _ => false) dc) loadC wpC) : ℝ) + nexec true true (timeAnnot
        (odePubTG k s D.s_le_pow b' c0 etaH etaD T gbar ε m) (implDP (k := k) N s (fun _ => false)
        dc) loadC wpC)) = 2 := by
      exact_mod_cast hn1
    rw [h2] at h1
    exact h1.trans (le_of_eq (by ring))
  have hprop : ∀ c : Query → Bool, (propCount (prepTD (odePubTG k s D.s_le_pow b' c0 etaH etaD T
      gbar ε m) N dc ([] : List (NInstr ((Fin (m + 1) ⊕ Fin k) ⊕ Zs) (Fin m ⊕ PY k b) Query))
                ([] : List (NInstr (Fin (m + 1) ⊕ Zs) (Fin m ⊕ PY k b) Query))) (wCallN c) h : ℝ) ≤
        if T = 0 ∨ etaH + etaD = 0 then 0 else
          C₀ * gbar * odeShape s T etaH etaD gbar ε *
                    ((if c Query.rowLocation then 1 else 0) +
                      (if c Query.columnLocation then 1 else 0) + (if c Query.value then 1 else 0))
                          := by
    intro c
    have h1 := propCount_le (prepTD (odePubTG k s D.s_le_pow b' c0 etaH etaD T gbar ε m) N dc loadC
        wpC) (prepTD (odePubTG k s D.s_le_pow b' c0 etaH etaD T gbar ε m) N dc ([] : List (NInstr
        ((Fin (m + 1) ⊕ Fin k) ⊕ Zs) (Fin m ⊕ PY k b) Query))
                ([] : List (NInstr (Fin (m + 1) ⊕ Zs) (Fin m ⊕ PY k b) Query))) _ (one_le_two_mul
                    hg) (wCallN c) h
    have h2 := hC' c
    simp only [nCallsN, List.countP_nil, Nat.cast_zero, add_zero, mul_zero] at h2
    exact h1.trans h2
  refine ⟨hexec0, hexec1, fun c => ?_, hprop, fun c => ?_, ?_, ?_⟩
  · have e := nhistory_calls_src _ _ hflat hok (fun b adj => ninv_tsrcMacro _ _ _ b adj) _ _ c
      (fun b'' => if b'' then nCallsN c wpC else nCallsN c loadC)
      (fun b adj => by rw [nCallsN_tsrcMacro, nCallsN_liftC]; try rfl) h
    rw [herase] at e
    exact e
  · exact nhistory_calls_le _ _ hflat herase hok (fun b adj => ninv_tsrcMacro _ _ _ b adj) _ _ c
      (fun b'' => if b'' then nCallsN c wpC else nCallsN c loadC)
      (fun b adj => by rw [nCallsN_tsrcMacro, nCallsN_liftC]; try rfl)
      (fun b'' => if b'' then 160 * gbar else 80 * gbar) _ h
      (fun b'' => by cases b'' <;> simpa using (by assumption)) (hprop c)
  · have e := nhistory_gates_src _ _ hflat hok (fun b adj => ninv_tsrcMacro _ _ _ b adj) _ _
      (fun b'' => if b'' then nGatesN wpC else nGatesN loadC)
      (fun b adj => by rw [nGatesN_tsrcMacro, nGatesN_liftC]; try rfl) h
    rw [herase] at e
    exact e
  · have h1 := propCount_le (prepTD (odePubTG k s D.s_le_pow b' c0 etaH etaD T gbar ε m) N dc loadC
      wpC) (prepTD (odePubTG k s D.s_le_pow b' c0 etaH etaD T gbar ε m) N dc ([] : List (NInstr
      ((Fin (m + 1) ⊕ Fin k) ⊕ Zs) (Fin m ⊕ PY k b) Query))
                ([] : List (NInstr (Fin (m + 1) ⊕ Zs) (Fin m ⊕ PY k b) Query))) _ (one_le_two_mul
                    hg) wGateN h
    simp only [nGatesN, List.countP_nil, Nat.cast_zero, add_zero, mul_zero] at hG'
    exact h1.trans hG'

end Endpoints

end

end ManuscriptConformance
