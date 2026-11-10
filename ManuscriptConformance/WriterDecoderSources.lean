import ManuscriptConformance.WriterDecoderCert
import ManuscriptConformance.WriterODESources
import ManuscriptConformance.WriterODECert

/-!
# Conformance: source executions of the ODE gate theorems with binary entry decoding and a writer

The source-execution forms `ode_thm_gates_decoder_sources`, `ode_thm_gates_time_decoder_sources`,
`ode_thm_gates_time_decoder_cert_sources` (`SourceExecutions`, `SourceExecutionsMore`) for the
protocols of the writer forms `ode_thm_gates_decoder_writer`, `ode_thm_gates_time_decoder_writer`,
`ode_thm_gates_time_decoder_cert_writer` (handover item B4), and `ode_thm_gates_time_cert_sources`
for the protocol of `ode_thm_gates_time_cert_writer`: the annotations `constAnnotI`, `timeAnnot` at
the implementations `GeneralDecoderODE.implDPW`, `GeneralSparseAccess.implPW` evaluate to the
preparations `prepDW`, `prepTDW`, `GPubT.prepW` and to each of their trials, and along every
history the executions of each source circuit, the calls and the gates are bounded as in the
released forms, with the constants of the writer endpoints. The proofs are those of the released
forms at `implDPW`, `implPW`.
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

section Endpoints

open ContinuousLinearMap SparseHamiltonian.GateBinary SparseHamiltonian.GateBitBudget
  SparseHamiltonian.GeneralSparseAccess
open SparseHamiltonian.GateBinaryODE (Pub mLift SZ4)
open SparseHamiltonian.ZeroTimeGateODE (bprepC btprepC BPublicOK0 BZeroCase BTPublicOK0
  BTZeroCase)
open SparseHamiltonian.GeneralSparseODE (GPubT liftC nCallsN_liftC nGatesN_liftC)
open SparseHamiltonian.GeneralDecoderODE (BinDecode DW prepTDW prepTI implDPW prepDW)
open NativeSparseBlockEncoding (Data Query)

set_option maxHeartbeats 8000000 in
/-- **Source executions of Theorem `ode:thm:gates` with binary entry decoding and a writer,
constant coefficients** (`ode_thm_gates_decoder_writer`): as `ode_thm_gates_decoder_sources`, for
the protocol `nprotocol (prepDW (odePubG …) N dc srcC) ḡ` (annotation `constAnnotI` at
`implDPW N s 0 dc`). `C` is the constant of `ode_thm_gates_decoder_writer`. -/
theorem ode_thm_gates_decoder_sources_writer :
    ∃ C : ℝ, 0 < C ∧
      ∀ {X : Type u} {N s k b b' A : ℕ} (D : GeneralSparseAccess.QData X N s k b)
        (dc : BinDecode b b' A) (bd : ℕ) (c0 etaH etaD T gbar ε r₀ rb : ℝ),
        2 ^ k < 2 * N → BinaryEntryDecoding D dc c0 → comp_bits b' bd [c0, T, etaH, etaD] →
        ∀ (hnd : formal_nondegenerate gbar (r₀ + T * rb))
        {Zs : Type} [Fintype Zs] [DecidableEq Zs]
        (srcC : Bool → List (NInstr ((Unit ⊕ Fin k) ⊕ Zs) (PY k b) Query)),
        (∀ c, ∀ i ∈ srcC c, i.Valid) →
        0 ≤ etaH → 0 ≤ etaD → 0 ≤ T → 0 < ε → ε ≤ 1 / 2 → 0 ≤ r₀ → 0 ≤ rb →
        aflat (constAnnotI (odePubG k s D.s_le_pow b' c0 etaH etaD T gbar ε r₀ rb) (implDPW (k := k)
            N s (fun _ => false) dc) srcC) = prepDW (odePubG k s D.s_le_pow b' c0 etaH etaD T gbar ε
            r₀ rb) N dc srcC ∧
          AnnotOK (srcMacro (odePubG k s D.s_le_pow b' c0 etaH etaD T gbar ε r₀ rb).pub.params (fun
              c => liftC (srcC c))) (constAnnotI (odePubG k s D.s_le_pow b' c0 etaH etaD T gbar ε
              r₀ rb) (implDPW (k := k) N s (fun _ => false) dc) srcC) ∧
          (∀ j, aflat (atrial (constAnnotI (odePubG k s D.s_le_pow b' c0 etaH etaD T gbar ε r₀ rb)
              (implDPW (k := k) N s (fun _ => false) dc) srcC) j) = trialN (prepDW (odePubG k s
              D.s_le_pow b' c0 etaH etaD T gbar ε r₀ rb) N dc srcC) j) ∧
          ∀ h : ODERepeatProtocol.Protocol.History (nprotocol (prepDW (odePubG k s D.s_le_pow b' c0
              etaH etaD T gbar ε r₀ rb) N dc srcC) gbar hnd.1),
            (∀ c : Bool, (srcExecs (constAnnotI (odePubG k s D.s_le_pow b' c0 etaH etaD T gbar ε r₀
                rb) (implDPW (k := k) N s (fun _ => false) dc) srcC) c h : ℝ) ≤ 40 * gbar) ∧
            (∀ c : Query → Bool, h.cost (wCallN c) =
              propCount (prepDW (odePubG k s D.s_le_pow b' c0 etaH etaD T gbar ε r₀ rb) N dc (fun _
                  => ([] : List (NInstr ((Unit ⊕ Fin k) ⊕ Zs) (PY k b) Query)))) (wCallN c) h +
              ∑ c' : Bool, srcExecs (constAnnotI (odePubG k s D.s_le_pow b' c0 etaH etaD T gbar ε
                  r₀ rb) (implDPW (k := k) N s (fun _ => false) dc) srcC) c' h * nCallsN c (srcC
                  c')) ∧
            (∀ c : Query → Bool,
              (propCount (prepDW (odePubG k s D.s_le_pow b' c0 etaH etaD T gbar ε r₀ rb) N dc (fun _
                  => ([] : List (NInstr ((Unit ⊕ Fin k) ⊕ Zs) (PY k b) Query)))) (wCallN c) h : ℝ) ≤
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
              propCount (prepDW (odePubG k s D.s_le_pow b' c0 etaH etaD T gbar ε r₀ rb) N dc (fun _
                  => ([] : List (NInstr ((Unit ⊕ Fin k) ⊕ Zs) (PY k b) Query)))) wGateN h +
              ∑ c' : Bool, srcExecs (constAnnotI (odePubG k s D.s_le_pow b' c0 etaH etaD T gbar ε
                  r₀ rb) (implDPW (k := k) N s (fun _ => false) dc) srcC) c' h * nGatesN (srcC c') ∧
            (propCount (prepDW (odePubG k s D.s_le_pow b' c0 etaH etaD T gbar ε r₀ rb) N dc (fun _
                => ([] : List (NInstr ((Unit ⊕ Fin k) ⊕ Zs) (PY k b) Query)))) wGateN h : ℝ) ≤
              C * gbar * (odeShape s T etaH etaD gbar ε *
                ((bitB bd N 0 0 (odeShape s T etaH etaD gbar ε) gbar ε + 1) ^ 3 + dc.cost) +
                Fintype.card Zs) := by
  obtain ⟨C₀, hC₀, H⟩ := ode_thm_gates_decoder_writer.{u}
  refine ⟨C₀, hC₀, ?_⟩
  intro X N s k b b' A D dc bd c0 etaH etaD T gbar ε r₀ rb hk hF hbits hnd Zs _ _ srcC hsrcV hH hD
    hT hε hε2 hr0 hrb
  obtain ⟨-, hG', -, hC', -⟩ := H D dc bd c0 etaH etaD T gbar ε r₀ rb hk hF hbits hnd
    (fun _ => ([] : List (NInstr ((Unit ⊕ Fin k) ⊕ Zs) (PY k b) Query))) (by simp) hH hD hT hε hε2
        hr0 hrb
  have hq : BPublicOK0 (odePubG k s D.s_le_pow b' c0 etaH etaD T gbar ε r₀ rb).pub := by
    rw [show (odePubG k s D.s_le_pow b' c0 etaH etaD T gbar ε r₀ rb).pub = odePub (k + 1) (sbP s)
        ((sbP_le D.s_le_pow).trans (Nat.le_succ k)) b' c0
      etaH etaD T gbar ε r₀ rb from rfl]
    exact odePub_ok _ hF.hb hF.hc0 hH hD hT hnd.1 hε hε2 hr0 hrb hnd.2
  have hflat : aflat (constAnnotI (odePubG k s D.s_le_pow b' c0 etaH etaD T gbar ε r₀ rb) (implDPW
      (k := k) N s (fun _ => false) dc) srcC) = prepDW (odePubG k s D.s_le_pow b' c0 etaH etaD T
      gbar ε r₀ rb) N dc srcC := by
    rw [aflat_constAnnotI]
    rfl
  have hok := annotOK_constAnnotI (odePubG k s D.s_le_pow b' c0 etaH etaD T gbar ε r₀ rb) (implDPW
      (k := k) N s (fun _ => false) dc) srcC
  have herase : aflat (aerase (constAnnotI (odePubG k s D.s_le_pow b' c0 etaH etaD T gbar ε r₀ rb)
      (implDPW (k := k) N s (fun _ => false) dc) srcC)) = prepDW (odePubG k s D.s_le_pow b' c0 etaH
      etaD T gbar ε r₀ rb) N dc (fun _ => ([] : List (NInstr ((Unit ⊕ Fin k) ⊕ Zs) (PY k b)
      Query))) := by
    rw [aerase_constAnnotI, aflat_constAnnotI]
    rfl
  refine ⟨hflat, hok, fun j => (aflat_atrial _ j).trans (congrArg (fun P => trialN P j) hflat),
    fun h => ?_⟩
  have hexec : ∀ c : Bool, (srcExecs (constAnnotI (odePubG k s D.s_le_pow b' c0 etaH etaD T gbar ε
      r₀ rb) (implDPW (k := k) N s (fun _ => false) dc) srcC) c h : ℝ) ≤ 40 * gbar := by
    intro c
    have h1 := nhistory_exec_le _ hflat gbar hnd.1 c h
    have h2 : ((nexec c false (constAnnotI (odePubG k s D.s_le_pow b' c0 etaH etaD T gbar ε r₀ rb)
        (implDPW (k := k) N s (fun _ => false) dc) srcC) : ℝ) + nexec c true (constAnnotI (odePubG k
        s D.s_le_pow b' c0 etaH etaD T gbar ε r₀ rb) (implDPW (k := k) N s (fun _ => false) dc)
        srcC)) = 1 := by
      exact_mod_cast nexec_constAnnotI _ hq (implDPW (k := k) N s (fun _ => false) dc) srcC c
    rw [h2, mul_one] at h1
    exact h1
  have hprop : ∀ c : Query → Bool,
      (propCount (prepDW (odePubG k s D.s_le_pow b' c0 etaH etaD T gbar ε r₀ rb) N dc (fun _ => ([]
          : List (NInstr ((Unit ⊕ Fin k) ⊕ Zs) (PY k b) Query)))) (wCallN c) h : ℝ) ≤
        if T = 0 ∨ etaH + etaD = 0 then 0 else
                  C₀ * gbar * odeShape s T etaH etaD gbar ε *
                    ((if c Query.rowLocation then 1 else 0) +
                      (if c Query.columnLocation then 1 else 0) + (if c Query.value then 1 else 0))
                          := by
    intro c
    have h1 := propCount_le (prepDW (odePubG k s D.s_le_pow b' c0 etaH etaD T gbar ε r₀ rb) N dc
        srcC) (prepDW (odePubG k s D.s_le_pow b' c0 etaH etaD T gbar ε r₀ rb) N dc (fun _ => ([] :
        List (NInstr ((Unit ⊕ Fin k) ⊕ Zs) (PY k b) Query)))) gbar hnd.1 (wCallN c) h
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
  · have h1 := propCount_le (prepDW (odePubG k s D.s_le_pow b' c0 etaH etaD T gbar ε r₀ rb) N dc
      srcC) (prepDW (odePubG k s D.s_le_pow b' c0 etaH etaD T gbar ε r₀ rb) N dc (fun _ => ([] :
      List (NInstr ((Unit ⊕ Fin k) ⊕ Zs) (PY k b) Query)))) gbar hnd.1 wGateN h
    simp only [nGatesN, List.countP_nil, Nat.cast_zero, add_zero] at hG'
    exact h1.trans hG'

set_option maxHeartbeats 8000000 in
/-- **Source executions of the time-dependent Theorem `ode:thm:gates` with binary entry decoding
and a writer** (`ode_thm_gates_time_decoder_writer`): as `ode_thm_gates_time_decoder_sources`,
for the protocol `nprotocol (prepTDW (odePubTG …) N dc loadC wpC) (2ḡ)` (annotation `timeAnnot`
at `implDPW N s 0 dc`). `C` is the constant of `ode_thm_gates_time_decoder_writer`. -/
theorem ode_thm_gates_time_decoder_sources_writer :
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
          aflat (timeAnnot (odePubTG k s D.s_le_pow b' c0 etaH etaD T gbar ε m) (implDPW (k := k) N
              s (fun _ => false) dc) loadC wpC) = (prepTDW (odePubTG k s D.s_le_pow b' c0 etaH etaD
              T gbar ε m) N dc loadC wpC) ∧
          AnnotOK (tsrcMacro (odePubTG k s D.s_le_pow b' c0 etaH etaD T gbar ε m).pub.params (liftC
              loadC) wpC) (timeAnnot (odePubTG k s D.s_le_pow b' c0 etaH etaD T gbar ε m) (implDPW
              (k := k) N s (fun _ => false) dc) loadC wpC) ∧
          (∀ j, aflat (atrial (timeAnnot (odePubTG k s D.s_le_pow b' c0 etaH etaD T gbar ε m)
              (implDPW (k := k) N s (fun _ => false) dc) loadC wpC) j) = trialN (prepTDW (odePubTG k
              s D.s_le_pow b' c0 etaH etaD T gbar ε m) N dc loadC wpC) j) ∧
          ∀ h : ODERepeatProtocol.Protocol.History (nprotocol (prepTDW (odePubTG k s D.s_le_pow b'
              c0 etaH etaD T gbar ε m) N dc loadC wpC) (2 * gbar)
              (one_le_two_mul hg)),
            (srcExecs (timeAnnot (odePubTG k s D.s_le_pow b' c0 etaH etaD T gbar ε m) (implDPW (k :=
                k) N s (fun _ => false) dc) loadC wpC) false h : ℝ) ≤ 80 * gbar ∧
            (srcExecs (timeAnnot (odePubTG k s D.s_le_pow b' c0 etaH etaD T gbar ε m) (implDPW (k :=
                k) N s (fun _ => false) dc) loadC wpC) true h : ℝ) ≤ 160 * gbar ∧
            (∀ c : Query → Bool, h.cost (wCallN c) =
              propCount (prepTDW (odePubTG k s D.s_le_pow b' c0 etaH etaD T gbar ε m) N dc ([] :
                  List (NInstr ((Fin (m + 1) ⊕ Fin k) ⊕ Zs) (Fin m ⊕ PY k b) Query))
                ([] : List (NInstr (Fin (m + 1) ⊕ Zs) (Fin m ⊕ PY k b) Query))) (wCallN c) h +
              ∑ b'' : Bool, srcExecs (timeAnnot (odePubTG k s D.s_le_pow b' c0 etaH etaD T gbar ε
                  m) (implDPW (k := k) N s (fun _ => false) dc) loadC wpC) b'' h *
                (if b'' then nCallsN c wpC else nCallsN c loadC)) ∧
            (∀ c : Query → Bool, (propCount (prepTDW (odePubTG k s D.s_le_pow b' c0 etaH etaD T gbar
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
              propCount (prepTDW (odePubTG k s D.s_le_pow b' c0 etaH etaD T gbar ε m) N dc ([] :
                  List (NInstr ((Fin (m + 1) ⊕ Fin k) ⊕ Zs) (Fin m ⊕ PY k b) Query))
                ([] : List (NInstr (Fin (m + 1) ⊕ Zs) (Fin m ⊕ PY k b) Query))) wGateN h +
              ∑ b'' : Bool, srcExecs (timeAnnot (odePubTG k s D.s_le_pow b' c0 etaH etaD T gbar ε
                  m) (implDPW (k := k) N s (fun _ => false) dc) loadC wpC) b'' h * (if b'' then
                  nGatesN wpC else nGatesN loadC) ∧
            (propCount (prepTDW (odePubTG k s D.s_le_pow b' c0 etaH etaD T gbar ε m) N dc ([] : List
                (NInstr ((Fin (m + 1) ⊕ Fin k) ⊕ Zs) (Fin m ⊕ PY k b) Query))
                ([] : List (NInstr (Fin (m + 1) ⊕ Zs) (Fin m ⊕ PY k b) Query))) wGateN h : ℝ) ≤
              C * gbar * (odeShape s T etaH etaD gbar ε *
                ((bitB bd N (2 ^ m) (2 ^ m) (odeShape s T etaH etaD gbar ε) gbar ε + 1) ^ 3 +
                    dc.cost) +
                Fintype.card Zs) := by
  obtain ⟨C₀, hC₀, H⟩ := ode_thm_gates_time_decoder_writer.{u}
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
  have hflat : aflat (timeAnnot (odePubTG k s D.s_le_pow b' c0 etaH etaD T gbar ε m) (implDPW (k :=
      k) N s (fun _ => false) dc) loadC wpC) = (prepTDW (odePubTG k s D.s_le_pow b' c0 etaH etaD T
      gbar ε m) N dc loadC wpC) := by
    rw [aflat_timeAnnot]
    rfl
  have hok := annotOK_timeAnnot (odePubTG k s D.s_le_pow b' c0 etaH etaD T gbar ε m) (implDPW (k :=
      k) N s (fun _ => false) dc) loadC wpC
  have herase : aflat (aerase (timeAnnot (odePubTG k s D.s_le_pow b' c0 etaH etaD T gbar ε m)
      (implDPW (k := k) N s (fun _ => false) dc) loadC wpC)) = (prepTDW (odePubTG k s D.s_le_pow b'
      c0 etaH etaD T gbar ε m) N dc ([] : List (NInstr ((Fin (m + 1) ⊕ Fin k) ⊕ Zs) (Fin m ⊕ PY k
      b) Query))
                ([] : List (NInstr (Fin (m + 1) ⊕ Zs) (Fin m ⊕ PY k b) Query))) := by
    rw [aerase_timeAnnot, aflat_timeAnnot]
    rfl
  obtain ⟨hn0, hn1⟩ := nexec_timeAnnot (odePubTG k s D.s_le_pow b' c0 etaH etaD T gbar ε m) hq
      (implDPW (k := k) N s (fun _ => false) dc) loadC wpC
  refine ⟨hflat, hok, fun j => (aflat_atrial _ j).trans (congrArg (fun P => trialN P j) hflat),
    fun h => ?_⟩
  have hexec0 : (srcExecs (timeAnnot (odePubTG k s D.s_le_pow b' c0 etaH etaD T gbar ε m) (implDPW
      (k := k) N s (fun _ => false) dc) loadC wpC) false h : ℝ) ≤ 80 * gbar := by
    have h1 := nhistory_exec_le _ hflat _ (one_le_two_mul hg) false h
    have h2 : ((nexec false false (timeAnnot (odePubTG k s D.s_le_pow b' c0 etaH etaD T gbar ε m)
        (implDPW (k := k) N s (fun _ => false) dc) loadC wpC) : ℝ) + nexec false true (timeAnnot
        (odePubTG k s D.s_le_pow b' c0 etaH etaD T gbar ε m) (implDPW (k := k) N s (fun _ => false)
        dc) loadC wpC)) = 1 := by
      exact_mod_cast hn0
    rw [h2] at h1
    exact h1.trans (le_of_eq (by ring))
  have hexec1 : (srcExecs (timeAnnot (odePubTG k s D.s_le_pow b' c0 etaH etaD T gbar ε m) (implDPW
      (k := k) N s (fun _ => false) dc) loadC wpC) true h : ℝ) ≤ 160 * gbar := by
    have h1 := nhistory_exec_le _ hflat _ (one_le_two_mul hg) true h
    have h2 : ((nexec true false (timeAnnot (odePubTG k s D.s_le_pow b' c0 etaH etaD T gbar ε m)
        (implDPW (k := k) N s (fun _ => false) dc) loadC wpC) : ℝ) + nexec true true (timeAnnot
        (odePubTG k s D.s_le_pow b' c0 etaH etaD T gbar ε m) (implDPW (k := k) N s (fun _ => false)
        dc) loadC wpC)) = 2 := by
      exact_mod_cast hn1
    rw [h2] at h1
    exact h1.trans (le_of_eq (by ring))
  have hprop : ∀ c : Query → Bool, (propCount (prepTDW (odePubTG k s D.s_le_pow b' c0 etaH etaD T
      gbar ε m) N dc ([] : List (NInstr ((Fin (m + 1) ⊕ Fin k) ⊕ Zs) (Fin m ⊕ PY k b) Query))
                ([] : List (NInstr (Fin (m + 1) ⊕ Zs) (Fin m ⊕ PY k b) Query))) (wCallN c) h : ℝ) ≤
        if T = 0 ∨ etaH + etaD = 0 then 0 else
          C₀ * gbar * odeShape s T etaH etaD gbar ε *
                    ((if c Query.rowLocation then 1 else 0) +
                      (if c Query.columnLocation then 1 else 0) + (if c Query.value then 1 else 0))
                          := by
    intro c
    have h1 := propCount_le (prepTDW (odePubTG k s D.s_le_pow b' c0 etaH etaD T gbar ε m) N dc loadC
        wpC) (prepTDW (odePubTG k s D.s_le_pow b' c0 etaH etaD T gbar ε m) N dc ([] : List (NInstr
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
  · have h1 := propCount_le (prepTDW (odePubTG k s D.s_le_pow b' c0 etaH etaD T gbar ε m) N dc loadC
      wpC) (prepTDW (odePubTG k s D.s_le_pow b' c0 etaH etaD T gbar ε m) N dc ([] : List (NInstr
      ((Fin (m + 1) ⊕ Fin k) ⊕ Zs) (Fin m ⊕ PY k b) Query))
                ([] : List (NInstr (Fin (m + 1) ⊕ Zs) (Fin m ⊕ PY k b) Query))) _ (one_le_two_mul
                    hg) wGateN h
    simp only [nGatesN, List.countP_nil, Nat.cast_zero, add_zero, mul_zero] at hG'
    exact h1.trans hG'
set_option maxHeartbeats 8000000 in
/-- **Source executions of the time-dependent Theorem `ode:thm:gates` with binary entry decoding,
a writer and the manuscript's certificates** (`ode_thm_gates_time_decoder_cert_writer`): as
`ode_thm_gates_time_decoder_cert_sources`, for the preparation `prepTDW` of that endpoint
(annotation `timeAnnot` at `implDPW N s 0 dc`). -/
theorem ode_thm_gates_time_decoder_cert_sources_writer :
    ∃ C : ℝ, 0 < C ∧
      ∀ {X : Type u} {N s k b b' A : ℕ} (bd : ℕ) (c0 etaH etaD T gbar ε : ℝ) (m : ℕ)
        (D : GeneralSparseAccess.QData (X × Fin (2 ^ m)) N s k b) (dc : BinDecode b b' A),
        odeMeshG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar) ε ≤ m →
        2 ^ k < 2 * N → BinaryEntryDecoding D dc c0 → comp_bits b' bd [c0, T, etaH, etaD] →
        ∀ (hg : formal_gbarOne gbar) {Zs : Type} [Fintype Zs] [DecidableEq Zs]
          (loadC : List (NInstr ((Fin (m + 1) ⊕ Fin k) ⊕ Zs) (Fin m ⊕ PY k b) Query))
          (wpC : List (NInstr (Fin (m + 1) ⊕ Zs) (Fin m ⊕ PY k b) Query)),
          (∀ i ∈ loadC, i.Valid) → (∀ i ∈ wpC, i.Valid) →
          0 ≤ etaH → 0 ≤ etaD → 0 ≤ T → 0 < ε → ε ≤ 1 / 2 →
          aflat (timeAnnot (odePubTG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar) ε m) (implDPW (k :=
              k) N s (fun _ => false) dc) loadC wpC) = prepTDW (odePubTG k s D.s_le_pow b' c0 etaH
              etaD T (2 * gbar) ε m) N dc loadC wpC ∧
          AnnotOK (tsrcMacro (odePubTG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar) ε m).pub.params
              (liftC loadC) wpC) (timeAnnot (odePubTG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar) ε
              m) (implDPW (k := k) N s (fun _ => false) dc) loadC wpC) ∧
          (∀ j, aflat (atrial (timeAnnot (odePubTG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar) ε m)
              (implDPW (k := k) N s (fun _ => false) dc) loadC wpC) j) = trialN (prepTDW (odePubTG k
              s D.s_le_pow b' c0 etaH etaD T (2 * gbar) ε m) N dc loadC wpC) j) ∧
          ∀ h : ODERepeatProtocol.Protocol.History (nprotocol (prepTDW (odePubTG k s D.s_le_pow b'
              c0 etaH etaD T (2 * gbar) ε m) N dc loadC wpC) (2 * (2 * gbar))
                (one_le_two_mul (one_le_two_mul hg))),
            (srcExecs (timeAnnot (odePubTG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar) ε m) (implDPW
                (k := k) N s (fun _ => false) dc) loadC wpC) false h : ℝ) ≤ 160 * gbar ∧
            (srcExecs (timeAnnot (odePubTG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar) ε m) (implDPW
                (k := k) N s (fun _ => false) dc) loadC wpC) true h : ℝ) ≤ 320 * gbar ∧
            (∀ c : Query → Bool, h.cost (wCallN c) =
              propCount (prepTDW (odePubTG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar) ε m) N dc ([]
                  : List (NInstr ((Fin (m + 1) ⊕ Fin k) ⊕ Zs) (Fin m ⊕ PY k b) Query)) ([] : List
                  (NInstr (Fin (m + 1) ⊕ Zs) (Fin m ⊕ PY k b) Query))) (wCallN c) h +
              ∑ b'' : Bool, srcExecs (timeAnnot (odePubTG k s D.s_le_pow b' c0 etaH etaD T (2 *
                  gbar) ε m) (implDPW (k := k) N s (fun _ => false) dc) loadC wpC) b'' h *
                (if b'' then nCallsN c wpC else nCallsN c loadC)) ∧
            (∀ c : Query → Bool,
              (propCount (prepTDW (odePubTG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar) ε m) N dc
                  ([] : List (NInstr ((Fin (m + 1) ⊕ Fin k) ⊕ Zs) (Fin m ⊕ PY k b) Query)) ([] :
                  List (NInstr (Fin (m + 1) ⊕ Zs) (Fin m ⊕ PY k b) Query))) (wCallN c) h : ℝ) ≤
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
                (160 * gbar * nCallsN c loadC + 320 * gbar * nCallsN c wpC)) ∧
            h.cost wGateN =
              propCount (prepTDW (odePubTG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar) ε m) N dc ([]
                  : List (NInstr ((Fin (m + 1) ⊕ Fin k) ⊕ Zs) (Fin m ⊕ PY k b) Query)) ([] : List
                  (NInstr (Fin (m + 1) ⊕ Zs) (Fin m ⊕ PY k b) Query))) wGateN h +
              ∑ b'' : Bool, srcExecs (timeAnnot (odePubTG k s D.s_le_pow b' c0 etaH etaD T (2 *
                  gbar) ε m) (implDPW (k := k) N s (fun _ => false) dc) loadC wpC) b'' h * (if b''
                  then nGatesN wpC else nGatesN loadC) ∧
            (propCount (prepTDW (odePubTG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar) ε m) N dc ([]
                : List (NInstr ((Fin (m + 1) ⊕ Fin k) ⊕ Zs) (Fin m ⊕ PY k b) Query)) ([] : List
                (NInstr (Fin (m + 1) ⊕ Zs) (Fin m ⊕ PY k b) Query))) wGateN h : ℝ) ≤
              C * gbar * (odeShape s T etaH etaD gbar ε *
                ((bitB bd N (2 ^ m) (2 ^ m) (odeShape s T etaH etaD gbar ε) gbar ε + 1) ^ 3 +
                  dc.cost) + Fintype.card Zs) := by
  obtain ⟨C₀, hC₀, H⟩ := ode_thm_gates_time_decoder_cert_writer.{u}
  refine ⟨C₀, hC₀, ?_⟩
  intro X N s k b b' A bd c0 etaH etaD T gbar ε m D dc hm hk hF hbits hg Zs _ _ loadC wpC hloadV
    hwpV hH hD hT hε hε2
  obtain ⟨-, hG', -, hC', -⟩ := H bd c0 etaH etaD T gbar ε m D dc hm hk hF hbits hg ([] : List
      (NInstr ((Fin (m + 1) ⊕ Fin k) ⊕ Zs) (Fin m ⊕ PY k b) Query))
    ([] : List (NInstr (Fin (m + 1) ⊕ Zs) (Fin m ⊕ PY k b) Query)) (by simp) (by simp) hH hD hT hε
        hε2
  have hg2 : 1 ≤ 2 * gbar := one_le_two_mul hg
  have hq : BTPublicOK0 (odePubTG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar) ε m).pub := by
    rw [odePubTG_pub]
    exact odePubT_ok _ hF.hb hF.hc0 hH hD hT hg2 hε hε2 hm
  have hflat : aflat (timeAnnot (odePubTG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar) ε m) (implDPW
      (k := k) N s (fun _ => false) dc) loadC wpC) = prepTDW (odePubTG k s D.s_le_pow b' c0 etaH
      etaD T (2 * gbar) ε m) N dc loadC wpC := by
    rw [aflat_timeAnnot]
    rfl
  have hok := annotOK_timeAnnot (odePubTG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar) ε m) (implDPW
      (k := k) N s (fun _ => false) dc) loadC wpC
  have herase : aflat (aerase (timeAnnot (odePubTG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar) ε m)
      (implDPW (k := k) N s (fun _ => false) dc) loadC wpC)) = (prepTDW (odePubTG k s D.s_le_pow b'
      c0 etaH etaD T (2 * gbar) ε m) N dc ([] : List (NInstr ((Fin (m + 1) ⊕ Fin k) ⊕ Zs) (Fin m ⊕
      PY k b) Query)) ([] : List (NInstr (Fin (m + 1) ⊕ Zs) (Fin m ⊕ PY k b) Query))) := by
    rw [aerase_timeAnnot, aflat_timeAnnot]
    rfl
  obtain ⟨hn0, hn1⟩ := nexec_timeAnnot (odePubTG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar) ε m)
      hq (implDPW (k := k) N s (fun _ => false) dc) loadC wpC
  refine ⟨hflat, hok, fun j => (aflat_atrial _ j).trans (congrArg (fun P => trialN P j) hflat),
    fun h => ?_⟩
  have hexec0 : (srcExecs (timeAnnot (odePubTG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar) ε m)
      (implDPW (k := k) N s (fun _ => false) dc) loadC wpC) false h : ℝ) ≤ 160 * gbar := by
    have h1 := nhistory_exec_le _ hflat _ (one_le_two_mul (one_le_two_mul hg)) false h
    have h2 : ((nexec false false (timeAnnot (odePubTG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar)
        ε m) (implDPW (k := k) N s (fun _ => false) dc) loadC wpC) : ℝ) + nexec false true
        (timeAnnot (odePubTG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar) ε m) (implDPW (k := k) N s
        (fun _ => false) dc) loadC wpC)) = 1 := by
      exact_mod_cast hn0
    rw [h2] at h1
    exact h1.trans (le_of_eq (by ring))
  have hexec1 : (srcExecs (timeAnnot (odePubTG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar) ε m)
      (implDPW (k := k) N s (fun _ => false) dc) loadC wpC) true h : ℝ) ≤ 320 * gbar := by
    have h1 := nhistory_exec_le _ hflat _ (one_le_two_mul (one_le_two_mul hg)) true h
    have h2 : ((nexec true false (timeAnnot (odePubTG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar) ε
        m) (implDPW (k := k) N s (fun _ => false) dc) loadC wpC) : ℝ) + nexec true true (timeAnnot
        (odePubTG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar) ε m) (implDPW (k := k) N s (fun _ =>
        false) dc) loadC wpC)) = 2 := by
      exact_mod_cast hn1
    rw [h2] at h1
    exact h1.trans (le_of_eq (by ring))
  have hprop : ∀ c : Query → Bool,
      (propCount (prepTDW (odePubTG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar) ε m) N dc ([] : List
          (NInstr ((Fin (m + 1) ⊕ Fin k) ⊕ Zs) (Fin m ⊕ PY k b) Query)) ([] : List (NInstr (Fin (m
          + 1) ⊕ Zs) (Fin m ⊕ PY k b) Query))) (wCallN c) h : ℝ) ≤
        if T = 0 ∨ etaH + etaD = 0 then 0 else
                  C₀ * gbar * odeShape s T etaH etaD gbar ε *
                    ((if c Query.rowLocation then 1 else 0) +
                      (if c Query.columnLocation then 1 else 0) + (if c Query.value then 1 else 0))
                          := by
    intro c
    have h1 := propCount_le (prepTDW (odePubTG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar) ε m) N dc
        loadC wpC) (prepTDW (odePubTG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar) ε m) N dc ([] :
        List (NInstr ((Fin (m + 1) ⊕ Fin k) ⊕ Zs) (Fin m ⊕ PY k b) Query)) ([] : List (NInstr (Fin
        (m + 1) ⊕ Zs) (Fin m ⊕ PY k b) Query))) _ (one_le_two_mul (one_le_two_mul hg)) (wCallN c) h
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
      (fun b'' => if b'' then 320 * gbar else 160 * gbar) _ h
      (fun b'' => by cases b'' <;> simpa using (by assumption)) (hprop c)
  · have e := nhistory_gates_src _ _ hflat hok (fun b adj => ninv_tsrcMacro _ _ _ b adj) _ _
      (fun b'' => if b'' then nGatesN wpC else nGatesN loadC)
      (fun b adj => by rw [nGatesN_tsrcMacro, nGatesN_liftC]; try rfl) h
    rw [herase] at e
    exact e
  · have h1 := propCount_le (prepTDW (odePubTG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar) ε m) N dc
      loadC wpC) (prepTDW (odePubTG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar) ε m) N dc ([] : List
      (NInstr ((Fin (m + 1) ⊕ Fin k) ⊕ Zs) (Fin m ⊕ PY k b) Query)) ([] : List (NInstr (Fin (m + 1)
      ⊕ Zs) (Fin m ⊕ PY k b) Query))) _ (one_le_two_mul (one_le_two_mul hg)) wGateN h
    simp only [nGatesN, List.countP_nil, Nat.cast_zero, add_zero, mul_zero] at hG'
    exact h1.trans hG'
set_option maxHeartbeats 8000000 in
/-- **Source executions of the time-dependent Theorem `ode:thm:gates` with a writer and the
manuscript's certificates** (`ode_thm_gates_time_cert_writer`): as
`ode_thm_gates_time_cert_sources`, for the protocol
`nprotocol ((odePubTG … (2ḡ) …).prepW N 0 loadC wpC) (4ḡ)` (annotation `timeAnnot` at
`implPW N s 0`). `C` is the constant of `ode_thm_gates_time_cert_writer`. -/
theorem ode_thm_gates_time_cert_sources_writer :
    ∃ C : ℝ, 0 < C ∧
      ∀ {X : Type u} {N s k b : ℕ} (bd : ℕ) (c0 etaH etaD T gbar ε : ℝ) (m : ℕ)
        (D : GeneralSparseAccess.QData (X × Fin (2 ^ m)) N s k b),
        odeMeshG k s D.s_le_pow b c0 etaH etaD T (2 * gbar) ε ≤ m →
        2 ^ k < 2 * N → formal_binaryDecoder D c0 → comp_bits b bd [c0, T, etaH, etaD] →
        ∀ (hg : formal_gbarOne gbar) {Zs : Type} [Fintype Zs] [DecidableEq Zs]
          (loadC : List (NInstr ((Fin (m + 1) ⊕ Fin k) ⊕ Zs) (Fin m ⊕ PY k b) Query))
          (wpC : List (NInstr (Fin (m + 1) ⊕ Zs) (Fin m ⊕ PY k b) Query)),
          (∀ i ∈ loadC, i.Valid) → (∀ i ∈ wpC, i.Valid) →
          0 ≤ etaH → 0 ≤ etaD → 0 ≤ T → 0 < ε → ε ≤ 1 / 2 →
          aflat (timeAnnot (odePubTG k s D.s_le_pow b c0 etaH etaD T (2 * gbar) ε m) (implPW (k :=
              k) (b := b) N s (fun _ => false)) loadC wpC) = (odePubTG k s D.s_le_pow b c0 etaH
              etaD T (2 * gbar) ε m).prepW N (fun _ => false) loadC wpC ∧
          AnnotOK (tsrcMacro (odePubTG k s D.s_le_pow b c0 etaH etaD T (2 * gbar) ε m).pub.params
              (liftC loadC) wpC) (timeAnnot (odePubTG k s D.s_le_pow b c0 etaH etaD T (2 * gbar) ε
              m) (implPW (k := k) (b := b) N s (fun _ => false)) loadC wpC) ∧
          (∀ j, aflat (atrial (timeAnnot (odePubTG k s D.s_le_pow b c0 etaH etaD T (2 * gbar) ε m)
              (implPW (k := k) (b := b) N s (fun _ => false)) loadC wpC) j) = trialN ((odePubTG k s
              D.s_le_pow b c0 etaH etaD T (2 * gbar) ε m).prepW N (fun _ => false) loadC wpC) j) ∧
          ∀ h : ODERepeatProtocol.Protocol.History (nprotocol ((odePubTG k s D.s_le_pow b c0 etaH
              etaD T (2 * gbar) ε m).prepW N (fun _ => false) loadC wpC) (2 * (2 * gbar))
                (one_le_two_mul (one_le_two_mul hg))),
            (srcExecs (timeAnnot (odePubTG k s D.s_le_pow b c0 etaH etaD T (2 * gbar) ε m) (implPW
                (k := k) (b := b) N s (fun _ => false)) loadC wpC) false h : ℝ) ≤ 160 * gbar ∧
            (srcExecs (timeAnnot (odePubTG k s D.s_le_pow b c0 etaH etaD T (2 * gbar) ε m) (implPW
                (k := k) (b := b) N s (fun _ => false)) loadC wpC) true h : ℝ) ≤ 320 * gbar ∧
            (∀ c : Query → Bool, h.cost (wCallN c) =
              propCount ((odePubTG k s D.s_le_pow b c0 etaH etaD T (2 * gbar) ε m).prepW N (fun _ =>
                  false) ([] : List (NInstr ((Fin (m + 1) ⊕ Fin k) ⊕ Zs) (Fin m ⊕ PY k b) Query))
                  ([] : List (NInstr (Fin (m + 1) ⊕ Zs) (Fin m ⊕ PY k b) Query))) (wCallN c) h +
              ∑ b'' : Bool, srcExecs (timeAnnot (odePubTG k s D.s_le_pow b c0 etaH etaD T (2 *
                  gbar) ε m) (implPW (k := k) (b := b) N s (fun _ => false)) loadC wpC) b'' h *
                (if b'' then nCallsN c wpC else nCallsN c loadC)) ∧
            (∀ c : Query → Bool,
              (propCount ((odePubTG k s D.s_le_pow b c0 etaH etaD T (2 * gbar) ε m).prepW N (fun _
                  => false) ([] : List (NInstr ((Fin (m + 1) ⊕ Fin k) ⊕ Zs) (Fin m ⊕ PY k b)
                  Query)) ([] : List (NInstr (Fin (m + 1) ⊕ Zs) (Fin m ⊕ PY k b) Query))) (wCallN
                  c) h : ℝ) ≤
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
                (160 * gbar * nCallsN c loadC + 320 * gbar * nCallsN c wpC)) ∧
            h.cost wGateN =
              propCount ((odePubTG k s D.s_le_pow b c0 etaH etaD T (2 * gbar) ε m).prepW N (fun _ =>
                  false) ([] : List (NInstr ((Fin (m + 1) ⊕ Fin k) ⊕ Zs) (Fin m ⊕ PY k b) Query))
                  ([] : List (NInstr (Fin (m + 1) ⊕ Zs) (Fin m ⊕ PY k b) Query))) wGateN h +
              ∑ b'' : Bool, srcExecs (timeAnnot (odePubTG k s D.s_le_pow b c0 etaH etaD T (2 *
                  gbar) ε m) (implPW (k := k) (b := b) N s (fun _ => false)) loadC wpC) b'' h * (if
                  b'' then nGatesN wpC else nGatesN loadC) ∧
            (propCount ((odePubTG k s D.s_le_pow b c0 etaH etaD T (2 * gbar) ε m).prepW N (fun _ =>
                false) ([] : List (NInstr ((Fin (m + 1) ⊕ Fin k) ⊕ Zs) (Fin m ⊕ PY k b) Query)) ([]
                : List (NInstr (Fin (m + 1) ⊕ Zs) (Fin m ⊕ PY k b) Query))) wGateN h : ℝ) ≤
              C * gbar * (odeShape s T etaH etaD gbar ε *
                (bitB bd N (2 ^ m) (2 ^ m) (odeShape s T etaH etaD gbar ε) gbar ε + 1) ^ 3 +
                Fintype.card Zs) := by
  obtain ⟨C₀, hC₀, H⟩ := ode_thm_gates_time_cert_writer.{u}
  refine ⟨C₀, hC₀, ?_⟩
  intro X N s k b bd c0 etaH etaD T gbar ε m D hm hk hF hbits hg Zs _ _ loadC wpC hloadV hwpV hH
    hD hT hε hε2
  obtain ⟨-, hG', -, hC', -⟩ := H bd c0 etaH etaD T gbar ε m D hm hk hF hbits hg ([] : List (NInstr
      ((Fin (m + 1) ⊕ Fin k) ⊕ Zs) (Fin m ⊕ PY k b) Query))
    ([] : List (NInstr (Fin (m + 1) ⊕ Zs) (Fin m ⊕ PY k b) Query)) (by simp) (by simp) hH hD hT hε
        hε2
  have hg2 : 1 ≤ 2 * gbar := one_le_two_mul hg
  have hq : BTPublicOK0 (odePubTG k s D.s_le_pow b c0 etaH etaD T (2 * gbar) ε m).pub := by
    rw [odePubTG_pub]
    exact odePubT_ok _ hF.hb hF.hc0 hH hD hT hg2 hε hε2 hm
  have hflat : aflat (timeAnnot (odePubTG k s D.s_le_pow b c0 etaH etaD T (2 * gbar) ε m) (implPW (k
      := k) (b := b) N s (fun _ => false)) loadC wpC) = (odePubTG k s D.s_le_pow b c0 etaH etaD T
      (2 * gbar) ε m).prepW N (fun _ => false) loadC wpC := by
    rw [aflat_timeAnnot]
    rfl
  have hok := annotOK_timeAnnot (odePubTG k s D.s_le_pow b c0 etaH etaD T (2 * gbar) ε m) (implPW (k
      := k) (b := b) N s (fun _ => false)) loadC wpC
  have herase : aflat (aerase (timeAnnot (odePubTG k s D.s_le_pow b c0 etaH etaD T (2 * gbar) ε m)
      (implPW (k := k) (b := b) N s (fun _ => false)) loadC wpC)) = ((odePubTG k s D.s_le_pow b c0
      etaH etaD T (2 * gbar) ε m).prepW N (fun _ => false) ([] : List (NInstr ((Fin (m + 1) ⊕ Fin k)
      ⊕ Zs) (Fin m ⊕ PY k b) Query)) ([] : List (NInstr (Fin (m + 1) ⊕ Zs) (Fin m ⊕ PY k b)
      Query))) := by
    rw [aerase_timeAnnot, aflat_timeAnnot]
    rfl
  obtain ⟨hn0, hn1⟩ := nexec_timeAnnot (odePubTG k s D.s_le_pow b c0 etaH etaD T (2 * gbar) ε m) hq
      (implPW (k := k) (b := b) N s (fun _ => false)) loadC wpC
  refine ⟨hflat, hok, fun j => (aflat_atrial _ j).trans (congrArg (fun P => trialN P j) hflat),
    fun h => ?_⟩
  have hexec0 : (srcExecs (timeAnnot (odePubTG k s D.s_le_pow b c0 etaH etaD T (2 * gbar) ε m)
      (implPW (k := k) (b := b) N s (fun _ => false)) loadC wpC) false h : ℝ) ≤ 160 * gbar := by
    have h1 := nhistory_exec_le _ hflat _ (one_le_two_mul (one_le_two_mul hg)) false h
    have h2 : ((nexec false false (timeAnnot (odePubTG k s D.s_le_pow b c0 etaH etaD T (2 * gbar) ε
        m) (implPW (k := k) (b := b) N s (fun _ => false)) loadC wpC) : ℝ) + nexec false true
        (timeAnnot (odePubTG k s D.s_le_pow b c0 etaH etaD T (2 * gbar) ε m) (implPW (k := k) (b :=
        b) N s (fun _ => false)) loadC wpC)) = 1 := by
      exact_mod_cast hn0
    rw [h2] at h1
    exact h1.trans (le_of_eq (by ring))
  have hexec1 : (srcExecs (timeAnnot (odePubTG k s D.s_le_pow b c0 etaH etaD T (2 * gbar) ε m)
      (implPW (k := k) (b := b) N s (fun _ => false)) loadC wpC) true h : ℝ) ≤ 320 * gbar := by
    have h1 := nhistory_exec_le _ hflat _ (one_le_two_mul (one_le_two_mul hg)) true h
    have h2 : ((nexec true false (timeAnnot (odePubTG k s D.s_le_pow b c0 etaH etaD T (2 * gbar) ε
        m) (implPW (k := k) (b := b) N s (fun _ => false)) loadC wpC) : ℝ) + nexec true true
        (timeAnnot (odePubTG k s D.s_le_pow b c0 etaH etaD T (2 * gbar) ε m) (implPW (k := k) (b :=
        b) N s (fun _ => false)) loadC wpC)) = 2 := by
      exact_mod_cast hn1
    rw [h2] at h1
    exact h1.trans (le_of_eq (by ring))
  have hprop : ∀ c : Query → Bool,
      (propCount ((odePubTG k s D.s_le_pow b c0 etaH etaD T (2 * gbar) ε m).prepW N (fun _ => false)
          ([] : List (NInstr ((Fin (m + 1) ⊕ Fin k) ⊕ Zs) (Fin m ⊕ PY k b) Query)) ([] : List
          (NInstr (Fin (m + 1) ⊕ Zs) (Fin m ⊕ PY k b) Query))) (wCallN c) h : ℝ) ≤
        if T = 0 ∨ etaH + etaD = 0 then 0 else
                  C₀ * gbar * odeShape s T etaH etaD gbar ε *
                    ((if c Query.rowLocation then 1 else 0) +
                      (if c Query.columnLocation then 1 else 0) + (if c Query.value then 1 else 0))
                          := by
    intro c
    have h1 := propCount_le ((odePubTG k s D.s_le_pow b c0 etaH etaD T (2 * gbar) ε m).prepW N (fun
        _ => false) loadC wpC) ((odePubTG k s D.s_le_pow b c0 etaH etaD T (2 * gbar) ε m).prepW N
        (fun _ => false) ([] : List (NInstr ((Fin (m + 1) ⊕ Fin k) ⊕ Zs) (Fin m ⊕ PY k b) Query))
        ([] : List (NInstr (Fin (m + 1) ⊕ Zs) (Fin m ⊕ PY k b) Query))) _ (one_le_two_mul
        (one_le_two_mul hg)) (wCallN c) h
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
      (fun b'' => if b'' then 320 * gbar else 160 * gbar) _ h
      (fun b'' => by cases b'' <;> simpa using (by assumption)) (hprop c)
  · have e := nhistory_gates_src _ _ hflat hok (fun b adj => ninv_tsrcMacro _ _ _ b adj) _ _
      (fun b'' => if b'' then nGatesN wpC else nGatesN loadC)
      (fun b adj => by rw [nGatesN_tsrcMacro, nGatesN_liftC]; try rfl) h
    rw [herase] at e
    exact e
  · have h1 := propCount_le ((odePubTG k s D.s_le_pow b c0 etaH etaD T (2 * gbar) ε m).prepW N (fun
      _ => false) loadC wpC) ((odePubTG k s D.s_le_pow b c0 etaH etaD T (2 * gbar) ε m).prepW N (fun
      _ => false) ([] : List (NInstr ((Fin (m + 1) ⊕ Fin k) ⊕ Zs) (Fin m ⊕ PY k b) Query)) ([] :
      List (NInstr (Fin (m + 1) ⊕ Zs) (Fin m ⊕ PY k b) Query))) _ (one_le_two_mul (one_le_two_mul
      hg)) wGateN h
    simp only [nGatesN, List.countP_nil, Nat.cast_zero, add_zero, mul_zero] at hG'
    exact h1.trans hG'

end Endpoints

end

end ManuscriptConformance
