import ManuscriptConformance.SourceExecutionsMore
import MeshCertificateODE.Selective

/-!
# Conformance: the certificate-form time-dependent solver over a finite gate set

Theorem `ode:thm:gates` (time-dependent coefficients) over a finite gate set, under the
manuscript's certificates (represented samples of either sign), for time-indexed binary data on
the uniform mesh with the slot-time sources. The protocol is the released finite-set protocol of
`GateSelective.binary_ode_time_budget_sel`: the native preparation compiled selectively
(`GateSelective.selPrep`: the gates of `𝒢` and every call kept, the supplied loading and
weight-preparation circuits over `𝒢` retained verbatim, the other gates synthesised with the
budget `ν/3`), the exact zero tests (gate kinds `zeroTestKinds ⊆ 𝒢`, an explicit hypothesis) and
the literal reverse-adjoint of the compiled preparation as its inverse. Its guarantees under the
certificates are `MeshCertificateODE.binary_ode_time_cert_sel`.

**Source executions in the compiled protocol.** The annotation of the native preparation
(`binAnnot`) is carried through the selective compiler and the placement on the trial register
(`selAnnot`: every block compiled with the accuracy of the whole preparation and placed, its tag
kept): `aflat_selAnnot`, `annotOK_selAnnot`, `nexec_selAnnot`, `aerase_selAnnot`. Source circuits
over `𝒢` contribute no synthesised gate (`nSynN_aflat_aerase`), so the compiled preparation with
the source blocks emptied is the compiled preparation with empty source circuits, at the same
accuracy (`aerase_sbAnnot`). `binary_time_sel_sources`: the annotation flattens to the compiled
preparation and to each of its trials, every tagged block is the supplied circuit (or its literal
inverse) retained verbatim and placed (`sbSrc_facts`), and along every history: at most `80 ḡ`
executions of the loading circuit and `160 ḡ` of the weight-preparation circuit (`ḡ` the public
bound `q.g`, protocol parameter `2ḡ`); the calls of every oracle kind are the propagation calls of
the compiled protocol with empty source circuits (at most `7864320 ḡ q*` per selected kind) plus
the executions times the calls inside the circuits, and the gates are the propagation gates (at
most the separated bound with `G_src = 0`) plus the executions times the gates of the circuits.

**The endpoint.** `ode_thm_gates_time_cert_finite` states the conclusions of
`MeshCertificateODE.binary_ode_time_cert_sel` (valid trials over `𝒢`, synthesised occurrences,
gates, matrix calls, qubits, and the guarantees `NOutcome` under `CertRest`) together with those
of `binary_time_sel_sources`, for one protocol fixed before the instance.

Scope: the case `T > 0`, `η_H + η_D > 0` (`PubT.OK`), stated for the public record `q : PubT`
(no wrapper in the manuscript's parameters); time-indexed binary data with exact binary entries
(`hdec`) on the uniform mesh `M = 2^m`, sources at the slot times; no general sizes, no
approximate decoding, no off-mesh source nodes.
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

/-! ### Annotations through the selective compiler -/

section Transport

open SparseHamiltonian.GateSynth SparseHamiltonian.GateSelective

variable {V Y J X W : Type*} [Fintype V] [DecidableEq V] [Fintype Y] [DecidableEq Y]
  [Fintype X] [DecidableEq X] {𝒢 : Set Kind} {L : ℝ → ℕ}

/-- **The annotation of a selectively compiled and placed circuit**: every block compiled with the
accuracy `ζ` and placed by `e`, its tag kept. -/
def selAnnot (hS : Synthesis 𝒢 X L) (ζ : ℝ) (e : V ⊕ X ↪ W) (bs : List (ABlock V Y J)) :
    List (ABlock W Y J) :=
  bs.map fun x => (x.1, (selC hS ζ x.2).map (NInstr.map e))

/-- The compiled and placed source circuits. -/
def selSrc (hS : Synthesis 𝒢 X L) (ζ : ℝ) (src : Bool → Bool → List (NInstr V Y J))
    (e : V ⊕ X ↪ W) : Bool → Bool → List (NInstr W Y J) :=
  fun b adj => (selC hS ζ (src b adj)).map (NInstr.map e)

omit [Fintype Y] [DecidableEq Y] in
theorem aflat_selAnnot (hS : Synthesis 𝒢 X L) (ζ : ℝ) (e : V ⊕ X ↪ W)
    (bs : List (ABlock V Y J)) :
    aflat (selAnnot hS ζ e bs) = (selC hS ζ (aflat bs)).map (NInstr.map e) := by
  induction bs with
  | nil => rfl
  | cons x bs ih =>
      rw [selAnnot, List.map_cons, aflat_cons, ← selAnnot, ih, aflat_cons, selC_append,
        List.map_append]

omit [Fintype Y] [DecidableEq Y] in
theorem nexec_selAnnot (hS : Synthesis 𝒢 X L) (ζ : ℝ) (e : V ⊕ X ↪ W) (b adj : Bool)
    (bs : List (ABlock V Y J)) : nexec b adj (selAnnot hS ζ e bs) = nexec b adj bs := by
  unfold nexec selAnnot
  rw [List.countP_map]
  rfl

omit [Fintype Y] [DecidableEq Y] in
theorem aerase_selAnnot (hS : Synthesis 𝒢 X L) (ζ : ℝ) (e : V ⊕ X ↪ W)
    (bs : List (ABlock V Y J)) : aerase (selAnnot hS ζ e bs) = selAnnot hS ζ e (aerase bs) := by
  unfold aerase selAnnot
  rw [List.map_map, List.map_map]
  apply List.map_congr_left
  intro x _
  simp only [Function.comp_apply]
  split_ifs <;> rfl

omit [Fintype Y] [DecidableEq Y] in
theorem annotOK_selAnnot (hS : Synthesis 𝒢 X L) (ζ : ℝ) (e : V ⊕ X ↪ W)
    {src : Bool → Bool → List (NInstr V Y J)} {bs : List (ABlock V Y J)} (hok : AnnotOK src bs) :
    AnnotOK (selSrc hS ζ src e) (selAnnot hS ζ e bs) := by
  intro x hx b adj hxt
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  exact congrArg (fun C => (selC hS ζ C).map (NInstr.map e)) (hok y hy b adj hxt)

omit [Fintype V] [DecidableEq V] [Fintype Y] [DecidableEq Y] [Fintype X] [DecidableEq X] in
/-- **Source circuits without synthesised gates**: the synthesised occurrences of an annotated
program are those of the program with the source blocks emptied. -/
theorem nSynN_aflat_aerase {src : Bool → Bool → List (NInstr V Y J)}
    (hsrc : ∀ b adj, nSynN 𝒢 (src b adj) = 0) {bs : List (ABlock V Y J)} (hok : AnnotOK src bs) :
    nSynN 𝒢 (aflat bs) = nSynN 𝒢 (aflat (aerase bs)) := by
  induction bs with
  | nil => rfl
  | cons x bs ih =>
      have hok' : AnnotOK src bs := fun y hy => hok y (List.mem_cons_of_mem _ hy)
      have e1 : aerase (x :: bs) = (x.1, if x.1.isSome then [] else x.2) :: aerase bs := rfl
      rw [e1, aflat_cons, aflat_cons, nSynN_append, nSynN_append, ih hok']
      rcases hx1 : x.1 with _ | ⟨b, adj⟩
      · simp
      · have hx2 := hok x List.mem_cons_self b adj hx1
        rw [hx2, hsrc b adj]
        simp [nSynN_nil]

omit [Fintype Y] [DecidableEq Y] in
/-- **Supplied circuits over `𝒢` are retained verbatim**, placed. -/
theorem selSrc_retained (hS : Synthesis 𝒢 X L) (ζ : ℝ) (src : Bool → Bool → List (NInstr V Y J))
    (e : V ⊕ X ↪ W) (b adj : Bool) (h : ∀ g, NInstr.gate g ∈ src b adj → GateOf 𝒢 g) :
    selSrc hS ζ src e b adj = ((src b adj).map (NInstr.map inlE)).map (NInstr.map e) := by
  rw [selSrc, selC_retained hS ζ _ h]

end Transport

/-! ### The annotated preparation of the binary-data solver -/

section Binary

open SparseHamiltonian.GateSynth SparseHamiltonian.GateSynthTrials SparseHamiltonian.GateSelective
open SparseHamiltonian.GateBinary
open SparseHamiltonian.GateBinaryODE (SZ4 hadUJ4_ok)
open SparseHamiltonian.GateBinaryODETime (PubT)
open SparseHamiltonian.GateODE.Time (TParams)
open NativeSparseBlockEncoding (Query)

variable {Zs : Type*} [Fintype Zs]

/-- **The annotated native preparation of the binary-data time-dependent solver** (the case
`PubT.OK`): the released preparation `q.params.prepC`, each instruction with its native macro. -/
def binAnnot (q : PubT)
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b) Query))
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b) Query)) :
    List (ABlock (TNW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A)
      (Fin q.m ⊕ PY q.kx q.b) Query) :=
  annotOf (omacro tlabSel q.UJg q.nd q.ar (tsrcMacro q.params loadC wpC)) q.params.prepC

theorem aflat_binAnnot [DecidableEq Zs] (q : PubT)
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b) Query))
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b) Query)) :
    aflat (binAnnot q loadC wpC) = q.prep loadC wpC := by
  rw [binAnnot, aflat_annotOf]
  rfl

theorem annotOK_binAnnot (q : PubT)
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b) Query))
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b) Query)) :
    AnnotOK (tsrcMacro q.params loadC wpC) (binAnnot q loadC wpC) :=
  annotOK_annotOf _ _ (fun _ _ => rfl) _

theorem aerase_binAnnot (q : PubT)
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b) Query))
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b) Query)) :
    aerase (binAnnot q loadC wpC) = binAnnot q [] [] := by
  refine aerase_annotOf _ _ (fun i hi => ?_) (fun b adj => by cases b <;> cases adj <;> rfl) _
  cases i <;> first | rfl | cases hi

/-- One execution of the loading circuit and two of the weight-preparation circuit per
preparation (both orientations counted). -/
theorem nexec_binAnnot (q : PubT) (hq : q.OK)
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b) Query))
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b) Query)) :
    nexec false false (binAnnot q loadC wpC) + nexec false true (binAnnot q loadC wpC) = 1 ∧
      nexec true false (binAnnot q loadC wpC) + nexec true true (binAnnot q loadC wpC) = 2 := by
  rw [binAnnot, nexec_annotOf, nexec_annotOf]
  have hp := q.params_ok hq
  obtain ⟨-, -, h0, h1, -⟩ := q.params.prepC_counts hp.tau_pos.le hp.nu_pos hp.mesh
  exact ⟨h0, h1⟩

omit [Fintype Zs] in
/-- The placed loading and weight-preparation circuits, and their literal inverses, are circuits
over an adjoint-closed `𝒢` when the supplied circuits are. -/
theorem tsrcMacro_gateOf {𝒢 : Set Kind} (hadj : AdjClosed 𝒢) (p : TParams) {S Z Y J : Type*}
    [Fintype S] [Fintype Zs] [Fintype Z] {bT bP A : ℕ}
    (loadC : List (NInstr ((Fin (p.m + 1) ⊕ S) ⊕ Zs) Y J))
    (hloadG : ∀ g, NInstr.gate g ∈ loadC → GateOf 𝒢 g)
    (wpC : List (NInstr (Fin (p.m + 1) ⊕ Zs) Y J)) (hwpG : ∀ g, NInstr.gate g ∈ wpC → GateOf 𝒢 g)
    (b adj : Bool) :
    ∀ g, NInstr.gate g ∈ tsrcMacro (Z := Z) (bT := bT) (bP := bP) (A := A) p loadC wpC b adj →
      GateOf 𝒢 g := by
  intro g hg
  cases b <;> cases adj
  · obtain ⟨g', hg', rfl⟩ := mem_map_gate _ _ g hg
    exact (hloadG g' hg').map _
  · obtain ⟨g', hg', rfl⟩ := mem_map_gate _ _ g hg
    exact (ninv_gateOf hadj _ hloadG g' hg').map _
  · obtain ⟨g', hg', rfl⟩ := mem_map_gate _ _ g hg
    exact (hwpG g' hg').map _
  · obtain ⟨g', hg', rfl⟩ := mem_map_gate _ _ g hg
    exact (ninv_gateOf hadj _ hwpG g' hg').map _

variable [DecidableEq Zs]

/-- The synthesis accuracy of the selective preparation of the binary-data solver (budget `ν/3`
shared over its synthesised occurrences). -/
def sbZeta (𝒢 : Set Kind) (q : PubT)
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b) Query))
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b) Query)) : ℝ :=
  q.params.nu / 3 / (nSynN 𝒢 (q.prep loadC wpC) + 1)

variable {Xa : Type*} [Fintype Xa] [DecidableEq Xa] {𝒢 : Set Kind} {len : ℝ → ℕ}

/-- **The annotated selective preparation** of the binary-data solver on the trial register. -/
def sbAnnot (hS : Synthesis 𝒢 Xa len) (q : PubT)
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b) Query))
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b) Query)) :
    List (ABlock (STW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A Xa)
      (Fin q.m ⊕ PY q.kx q.b) Query) :=
  selAnnot hS (sbZeta 𝒢 q loadC wpC) embS (binAnnot q loadC wpC)

/-- **The compiled source circuits** of the selective preparation, on the trial register. -/
def sbSrc (hS : Synthesis 𝒢 Xa len) (q : PubT)
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b) Query))
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b) Query)) :
    Bool → Bool → List (NInstr (STW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A Xa)
      (Fin q.m ⊕ PY q.kx q.b) Query) :=
  selSrc hS (sbZeta 𝒢 q loadC wpC) (tsrcMacro q.params loadC wpC) embS

theorem aflat_sbAnnot (hS : Synthesis 𝒢 Xa len) (q : PubT)
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b) Query))
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b) Query)) :
    aflat (sbAnnot hS q loadC wpC) = selPrep hS (q.params.nu / 3) (q.prep loadC wpC) := by
  rw [sbAnnot, aflat_selAnnot, aflat_binAnnot]
  rfl

theorem annotOK_sbAnnot (hS : Synthesis 𝒢 Xa len) (q : PubT)
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b) Query))
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b) Query)) :
    AnnotOK (sbSrc hS q loadC wpC) (sbAnnot hS q loadC wpC) :=
  annotOK_selAnnot hS _ embS (annotOK_binAnnot q loadC wpC)

/-- With source circuits over the adjoint-closed `𝒢`, the compiled preparation with the source
blocks emptied is the compiled preparation with empty source circuits. -/
theorem aerase_sbAnnot (hS : Synthesis 𝒢 Xa len) (hadj : AdjClosed 𝒢) (q : PubT)
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b) Query))
    (hloadG : ∀ g, NInstr.gate g ∈ loadC → GateOf 𝒢 g)
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b) Query))
    (hwpG : ∀ g, NInstr.gate g ∈ wpC → GateOf 𝒢 g) :
    aflat (aerase (sbAnnot hS q loadC wpC)) =
      selPrep hS (q.params.nu / 3) (q.prep (Zs := Zs) [] []) := by
  have hsyn : nSynN 𝒢 (q.prep loadC wpC) = nSynN 𝒢 (q.prep (Zs := Zs) [] []) := by
    have h := nSynN_aflat_aerase (𝒢 := 𝒢) (src := tsrcMacro q.params loadC wpC)
      (fun b adj => nSynN_eq_zero 𝒢 _ (tsrcMacro_gateOf hadj q.params loadC hloadG wpC hwpG b adj))
      (annotOK_binAnnot q loadC wpC)
    rwa [aflat_binAnnot, aerase_binAnnot, aflat_binAnnot] at h
  rw [sbAnnot, aerase_selAnnot, aerase_binAnnot, aflat_selAnnot, aflat_binAnnot, sbZeta, hsyn]
  rfl

/-- The compiled source circuits are the supplied circuits retained and placed; their literal
inverses are the opposite orientation, with the same calls and gates. -/
theorem sbSrc_facts (hS : Synthesis 𝒢 Xa len) (hadj : AdjClosed 𝒢) (q : PubT)
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b) Query))
    (hloadG : ∀ g, NInstr.gate g ∈ loadC → GateOf 𝒢 g)
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b) Query))
    (hwpG : ∀ g, NInstr.gate g ∈ wpC → GateOf 𝒢 g) :
    (∀ b adj, sbSrc hS q loadC wpC b adj =
      ((tsrcMacro q.params loadC wpC b adj).map (NInstr.map inlE)).map (NInstr.map embS)) ∧
    (∀ b adj, ninv (sbSrc hS q loadC wpC b adj) = sbSrc hS q loadC wpC b (!adj)) ∧
    (∀ (c : Query → Bool) b adj,
      nCallsN c (sbSrc hS q loadC wpC b adj) = if b then nCallsN c wpC else nCallsN c loadC) ∧
    (∀ b adj, nGatesN (sbSrc hS q loadC wpC b adj) = if b then nGatesN wpC else nGatesN loadC) := by
  have hret : ∀ b adj, sbSrc hS q loadC wpC b adj =
      ((tsrcMacro q.params loadC wpC b adj).map (NInstr.map inlE)).map (NInstr.map embS) :=
    fun b adj => selSrc_retained hS _ _ embS b adj
      (tsrcMacro_gateOf hadj q.params loadC hloadG wpC hwpG b adj)
  refine ⟨hret, fun b adj => ?_, fun c b adj => ?_, fun b adj => ?_⟩
  · rw [hret, hret, ninv_map, ninv_map, ninv_tsrcMacro]
  · rw [hret, nCallsN_map, nCallsN_map, nCallsN_tsrcMacro]
  · rw [hret, nGatesN_map, nGatesN_map, nGatesN_tsrcMacro]

end Binary

/-! ### Source executions and the endpoint -/

section Endpoint

open SparseHamiltonian.GateSynth SparseHamiltonian.GateSynthTrials SparseHamiltonian.GateSelective
open SparseHamiltonian.GateBinary SparseHamiltonian.GateBinaryODE
    SparseHamiltonian.GateBinaryODETime
open SparseHamiltonian.GateODEBudget (gammaOf qOf prepBoundT)
open SparseHamiltonian.GateBitBudget (bitB HasBits)
open SparseHamiltonian.MeshCertificateODE (CertRest binary_ode_time_cert_sel)
open NativeSparseBlockEncoding (Data Query)

variable {X n : Type*} [Fintype n] [DecidableEq n] {Zs : Type*} [Fintype Zs] [DecidableEq Zs]
variable {Xa : Type*} [Fintype Xa] [DecidableEq Xa] {𝒢 : Set Kind} {len : ℝ → ℕ}

set_option maxHeartbeats 8000000 in
/-- **Source executions of the finite-set binary-data solver** (the protocol of
`GateSelective.binary_ode_time_budget_sel` and `MeshCertificateODE.binary_ode_time_cert_sel`).
The annotation `sbAnnot` flattens to the compiled preparation and to each of its trials, its
tagged blocks are the supplied loading (`b = false`) and weight-preparation (`b = true`) circuits,
or their literal inverses, retained verbatim and placed, and along every history: at most `80 ḡ`
executions of the loading circuit and `160 ḡ` of the weight-preparation circuit; the calls and
gates are the propagation part (the compiled protocol with empty source circuits: at most
`7864320 ḡ q*` calls of each selected kind and the separated gate bound with `G_src = 0`) plus the
executions times the calls and gates of the two circuits; in total at most the propagation bound
plus `80 ḡ Q_load + 160 ḡ Q_wp` calls. -/
theorem binary_time_sel_sources (hS : Synthesis 𝒢 Xa len) (hadj : AdjClosed 𝒢)
    (hzt : zeroTestKinds ⊆ 𝒢) {c₀ c₁ : ℝ} (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁)
    (hlen : ∀ ζ' : ℝ, 0 < ζ' → ζ' ≤ 1 → (len ζ' : ℝ) ≤ c₁ * Real.log (1 / ζ') + c₀)
    (bd : ℕ) (q : PubT) (hq : q.OK) (hγ : q.γ = gammaOf q.T q.etaH q.etaD (2 * q.g) (q.ε / 2))
    (hζ : q.params.nu ≤ 196608 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * q.ζ)
    (hb : q.b ≤ bd) (hc0 : HasBits bd q.c0) (hT : HasBits bd q.T) (hH : HasBits bd q.etaH)
    (hD : HasBits bd q.etaD)
    (D : Data (X × Fin (2 ^ q.m)) n (Cfg (VW q.b)) q.s) (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (hdec : ∀ e z, D.decode e z = (q.c0 : ℂ) * gauss z)
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b)
      Query)) (hloadG : ∀ g, NInstr.gate g ∈ loadC → GateOf 𝒢 g)
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b) Query))
    (hwpG : ∀ g, NInstr.gate g ∈ wpC → GateOf 𝒢 g) :
    aflat (sbAnnot hS q loadC wpC) = (selPrep hS (q.params.nu / 3) (q.prep loadC wpC)) ∧
    AnnotOK (sbSrc hS q loadC wpC) (sbAnnot hS q loadC wpC) ∧
    (∀ b adj, sbSrc hS q loadC wpC b adj =
      ((tsrcMacro q.params loadC wpC b adj).map (NInstr.map inlE)).map (NInstr.map embS)) ∧
    (∀ j, aflat (atrial (sbAnnot hS q loadC wpC) j) = trialN (selPrep hS (q.params.nu / 3) (q.prep
        loadC wpC)) j) ∧
    ∀ h : ODERepeatProtocol.Protocol.History (nprotocol (selPrep hS (q.params.nu / 3) (q.prep loadC
        wpC)) q.params.ratio
        (q.params.ratio_ge hq.g_ge)),
      (srcExecs (sbAnnot hS q loadC wpC) false h : ℝ) ≤ 80 * q.g ∧
      (srcExecs (sbAnnot hS q loadC wpC) true h : ℝ) ≤ 160 * q.g ∧
      (∀ c : Query → Bool, h.cost (wCallN c) =
        propCount (selPrep hS (q.params.nu / 3) (q.prep (Zs := Zs) [] [])) (wCallN c) h +
        ∑ b'' : Bool, srcExecs (sbAnnot hS q loadC wpC) b'' h *
          (if b'' then nCallsN c wpC else nCallsN c loadC)) ∧
      (∀ c : Query → Bool, (propCount (selPrep hS (q.params.nu / 3) (q.prep (Zs := Zs) [] []))
          (wCallN c) h : ℝ) ≤
        7864320 * q.g * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
          ((if c Query.rowLocation then 1 else 0) +
            (if c Query.columnLocation then 1 else 0) + (if c Query.value then 1 else 0))) ∧
      (∀ c : Query → Bool, (h.cost (wCallN c) : ℝ) ≤
        7864320 * q.g * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
          ((if c Query.rowLocation then 1 else 0) +
            (if c Query.columnLocation then 1 else 0) + (if c Query.value then 1 else 0)) +
          (80 * q.g * nCallsN c loadC + 160 * q.g * nCallsN c wpC)) ∧
      h.cost wGateN = propCount (selPrep hS (q.params.nu / 3) (q.prep (Zs := Zs) [] [])) wGateN h +
        ∑ b'' : Bool, srcExecs (sbAnnot hS q loadC wpC) b'' h * (if b'' then nGatesN wpC else
            nGatesN loadC) ∧
      (propCount (selPrep hS (q.params.nu / 3) (q.prep (Zs := Zs) [] [])) wGateN h : ℝ) ≤
        80 * q.g * (2 * 10 ^ 18 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
          (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
            (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ 3 *
          (c₁ * (64 * (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
            (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1)) + c₀ + 1)) +
        40 * q.g * (4 * (3 * 10 ^ 11 * (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
            (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ 3 +
          2 * Fintype.card Zs + Fintype.card Xa) + 3) := by
  have hg := q.params.ratio_ge hq.g_ge
  have hr2 : q.params.ratio = 2 * q.g := rfl
  have hflat := aflat_sbAnnot hS q loadC wpC
  have hok := annotOK_sbAnnot hS q loadC wpC
  have herase := aerase_sbAnnot hS hadj q loadC hloadG wpC hwpG
  obtain ⟨hret, hinv, hcalls, hgates⟩ := sbSrc_facts hS hadj q loadC hloadG wpC hwpG
  obtain ⟨hn0, hn1⟩ := nexec_binAnnot q hq loadC wpC
  obtain ⟨-, -, -, hW0, hC0, -, -⟩ := binary_ode_time_budget_sel hS hadj hzt hc₀ hc₁ hlen bd q hq
    hγ hζ hb hc0 hT hH hD D en hrange hdec (Zs := Zs) [] (by simp) (by simp) [] (by simp)
    (by simp)
  refine ⟨hflat, hok, hret, fun j => (aflat_atrial _ j).trans (congrArg (fun P => trialN P j)
    hflat), fun h => ?_⟩
  have hexec0 : (srcExecs (sbAnnot hS q loadC wpC) false h : ℝ) ≤ 80 * q.g := by
    have h1 := nhistory_exec_le _ hflat _ hg false h
    have h2 : ((nexec false false (sbAnnot hS q loadC wpC) : ℝ) +
        nexec false true (sbAnnot hS q loadC wpC)) = 1 := by
      rw [sbAnnot, nexec_selAnnot, nexec_selAnnot]
      exact_mod_cast hn0
    rw [h2] at h1
    linarith [h1, hr2]
  have hexec1 : (srcExecs (sbAnnot hS q loadC wpC) true h : ℝ) ≤ 160 * q.g := by
    have h1 := nhistory_exec_le _ hflat _ hg true h
    have h2 : ((nexec true false (sbAnnot hS q loadC wpC) : ℝ) +
        nexec true true (sbAnnot hS q loadC wpC)) = 2 := by
      rw [sbAnnot, nexec_selAnnot, nexec_selAnnot]
      exact_mod_cast hn1
    rw [h2] at h1
    linarith [h1, hr2]
  have hprop : ∀ c : Query → Bool,
      (propCount (selPrep hS (q.params.nu / 3) (q.prep (Zs := Zs) [] [])) (wCallN c) h : ℝ) ≤
        7864320 * q.g * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
          ((if c Query.rowLocation then 1 else 0) +
            (if c Query.columnLocation then 1 else 0) + (if c Query.value then 1 else 0)) := by
    intro c
    have h1 := propCount_le (selPrep hS (q.params.nu / 3) (q.prep loadC wpC))
      (selPrep hS (q.params.nu / 3) (q.prep (Zs := Zs) [] [])) _ hg (wCallN c) h
    have h2 := hC0 c
    simp only [nCallsN, List.countP_nil, Nat.cast_zero, mul_zero, add_zero] at h2
    exact h1.trans h2
  refine ⟨hexec0, hexec1, fun c => ?_, hprop, fun c => ?_, ?_, ?_⟩
  · have e := nhistory_calls_src _ _ hflat hok hinv _ hg c
      (fun b'' => if b'' then nCallsN c wpC else nCallsN c loadC) (fun b adj => hcalls c b adj) h
    rw [herase] at e
    exact e
  · exact nhistory_calls_le _ _ hflat herase hok hinv _ hg c
      (fun b'' => if b'' then nCallsN c wpC else nCallsN c loadC) (fun b adj => hcalls c b adj)
      (fun b'' => if b'' then 160 * q.g else 80 * q.g) _ h
      (fun b'' => match b'' with
        | false => hexec0
        | true => hexec1) (hprop c)
  · have e := nhistory_gates_src _ _ hflat hok hinv _ hg
      (fun b'' => if b'' then nGatesN wpC else nGatesN loadC) hgates h
    rw [herase] at e
    exact e
  · have h1 := propCount_le (selPrep hS (q.params.nu / 3) (q.prep loadC wpC))
      (selPrep hS (q.params.nu / 3) (q.prep (Zs := Zs) [] [])) _ hg wGateN h
    simp only [nGatesN, List.countP_nil, Nat.cast_zero, mul_zero, add_zero, zero_add] at hW0
    exact h1.trans hW0

set_option maxHeartbeats 8000000 in
/-- **The time-dependent Theorem `ode:thm:gates` over a finite gate set under the manuscript's
certificates, with the source executions** (time-indexed binary data, uniform mesh, slot-time
sources, exact binary entries; the case `PubT.OK`). For one protocol fixed before the instance
(the selective preparation of `GateSelective.binary_ode_time_budget_sel`, the exact zero tests
with `zeroTestKinds ⊆ 𝒢`, the literal inverse): the conclusions of
`MeshCertificateODE.binary_ode_time_cert_sel` (valid trials over `𝒢`; synthesised occurrences;
gates, with the supplied circuits charged linearly and outside the synthesis logarithm; matrix
calls; qubits; success at least `2/3`, conditional trace distance `ε` and every successful trial
within `ε/500` of `x(T)/‖x(T)‖` up to a global phase, for every instance under `CertRest`, with
represented samples of either sign) and those of `binary_time_sel_sources` (at most `80 ḡ`
loadings and `160 ḡ` weight preparations in every history, the calls and gates split into the
propagation part and the executions times the supplied costs). -/
theorem ode_thm_gates_time_cert_finite (hS : Synthesis 𝒢 Xa len) (hadj : AdjClosed 𝒢)
    (hzt : zeroTestKinds ⊆ 𝒢) {c₀ c₁ : ℝ} (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁)
    (hlen : ∀ ζ' : ℝ, 0 < ζ' → ζ' ≤ 1 → (len ζ' : ℝ) ≤ c₁ * Real.log (1 / ζ') + c₀)
    (bd : ℕ) (q : PubT) (hq : q.OK) (hγ : q.γ = gammaOf q.T q.etaH q.etaD (2 * q.g) (q.ε / 2))
    (hζ : q.params.nu ≤ 196608 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * q.ζ)
    (hb : q.b ≤ bd) (hc0 : HasBits bd q.c0) (hT : HasBits bd q.T) (hH : HasBits bd q.etaH)
    (hD : HasBits bd q.etaD)
    (D : Data (X × Fin (2 ^ q.m)) n (Cfg (VW q.b)) q.s) (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (hdec : ∀ e z, D.decode e z = (q.c0 : ℂ) * gauss z)
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b)
      Query)) (hloadV : ∀ i ∈ loadC, i.Valid) (hloadG : ∀ g, NInstr.gate g ∈ loadC → GateOf 𝒢 g)
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b) Query))
    (hwpV : ∀ i ∈ wpC, i.Valid) (hwpG : ∀ g, NInstr.gate g ∈ wpC → GateOf 𝒢 g) :
    ((∀ j, (∀ i ∈ trialN (selPrep hS (q.params.nu / 3) (q.prep loadC wpC)) j, i.Valid) ∧
      ∀ g, NInstr.gate g ∈ trialN (selPrep hS (q.params.nu / 3) (q.prep loadC wpC)) j →
        GateOf 𝒢 g) ∧
    (nSynN 𝒢 (q.prep loadC wpC) : ℝ) ≤ prepBoundT (Zs := Zs) q [] [] ∧
    prepBoundT (Zs := Zs) q [] [] ≤
      2 * 10 ^ 18 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
        (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
          (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ 3 ∧
    ((nprotocol (selPrep hS (q.params.nu / 3) (q.prep loadC wpC)) q.params.ratio
        (q.params.ratio_ge hq.g_ge)).worstCost wGateN : ℝ) ≤
      80 * q.g * (((nGatesN loadC : ℝ) + 2 * nGatesN wpC) +
        2 * 10 ^ 18 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
          (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
            (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ 3 *
          (c₁ * (64 * (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
            (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1)) + c₀ + 1)) +
      40 * q.g * (4 * (3 * 10 ^ 11 * (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
          (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ 3 +
        2 * Fintype.card Zs + Fintype.card Xa) + 3) ∧
    (∀ c : Query → Bool,
      ((nprotocol (selPrep hS (q.params.nu / 3) (q.prep loadC wpC)) q.params.ratio
        (q.params.ratio_ge hq.g_ge)).worstCost (wCallN c) : ℝ) ≤
      7864320 * q.g * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
          ((if c Query.rowLocation then 1 else 0) + (if c Query.columnLocation then 1 else 0) +
            (if c Query.value then 1 else 0)) +
        80 * q.g * ((nCallsN c loadC : ℝ) + 2 * nCallsN c wpC)) ∧
    (Fintype.card (STW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A Xa) : ℝ) ≤
      7 * 10 ^ 11 * (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
          (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ 3 +
        4 * Fintype.card Zs + 2 * Fintype.card Xa ∧
    ∀ x : X,
      (∀ r i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaH ^ 2) →
      (∀ r j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaH ^ 2) →
      (∀ r i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaD ^ 2) →
      (∀ r j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaD ^ 2) →
      ∀ (Jl : Bool × (Fin q.m → Bool) → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
        (Wp : Matrix (Cfg (Fin (q.m + 1))) (Cfg (Fin (q.m + 1))) ℂ)
        (G : Fin (2 ^ q.m) → ℝ → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
        (bf : Fin (2 ^ q.m) → ℝ → Reg (Fin q.kx) ℂ) (sol : ℝ → Reg (Fin q.kx) ℂ)
        (U : ℝ → Reg (Fin q.kx) ℂ → ℝ → Reg (Fin q.kx) ℂ) (bs : ℕ → Reg (Fin q.kx) ℂ)
        (gb cq ζc ζs : ℝ),
      0 ≤ ζs →
      ApproxOn CleanX (nrun (primsT (R := ℂ) D en x) loadC) (liftB (loadIdeal Jl)) ζs →
      ApproxOn CleanX (nrun (primsT (R := ℂ) D en x) wpC) (liftB (matOp Wp)) ζs →
      98304 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * q.ζ + 3 * ζs ≤ q.params.nu →
      CertRest q D en x Jl Wp G bf sol U bs gb cq ζc →
      NOutcome (selPrep hS (q.params.nu / 3) (q.prep loadC wpC)) q.params.ratio q.ε
        (q.params.ratio_ge hq.g_ge) (primsT (R := ℂ) D en x) (sol q.T)) ∧
    (aflat (sbAnnot hS q loadC wpC) = (selPrep hS (q.params.nu / 3) (q.prep loadC wpC)) ∧
    AnnotOK (sbSrc hS q loadC wpC) (sbAnnot hS q loadC wpC) ∧
    (∀ b adj, sbSrc hS q loadC wpC b adj =
      ((tsrcMacro q.params loadC wpC b adj).map (NInstr.map inlE)).map (NInstr.map embS)) ∧
    (∀ j, aflat (atrial (sbAnnot hS q loadC wpC) j) = trialN (selPrep hS (q.params.nu / 3) (q.prep
        loadC wpC)) j) ∧
    ∀ h : ODERepeatProtocol.Protocol.History (nprotocol (selPrep hS (q.params.nu / 3) (q.prep loadC
        wpC)) q.params.ratio
        (q.params.ratio_ge hq.g_ge)),
      (srcExecs (sbAnnot hS q loadC wpC) false h : ℝ) ≤ 80 * q.g ∧
      (srcExecs (sbAnnot hS q loadC wpC) true h : ℝ) ≤ 160 * q.g ∧
      (∀ c : Query → Bool, h.cost (wCallN c) =
        propCount (selPrep hS (q.params.nu / 3) (q.prep (Zs := Zs) [] [])) (wCallN c) h +
        ∑ b'' : Bool, srcExecs (sbAnnot hS q loadC wpC) b'' h *
          (if b'' then nCallsN c wpC else nCallsN c loadC)) ∧
      (∀ c : Query → Bool, (propCount (selPrep hS (q.params.nu / 3) (q.prep (Zs := Zs) [] []))
          (wCallN c) h : ℝ) ≤
        7864320 * q.g * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
          ((if c Query.rowLocation then 1 else 0) +
            (if c Query.columnLocation then 1 else 0) + (if c Query.value then 1 else 0))) ∧
      (∀ c : Query → Bool, (h.cost (wCallN c) : ℝ) ≤
        7864320 * q.g * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
          ((if c Query.rowLocation then 1 else 0) +
            (if c Query.columnLocation then 1 else 0) + (if c Query.value then 1 else 0)) +
          (80 * q.g * nCallsN c loadC + 160 * q.g * nCallsN c wpC)) ∧
      h.cost wGateN = propCount (selPrep hS (q.params.nu / 3) (q.prep (Zs := Zs) [] [])) wGateN h +
        ∑ b'' : Bool, srcExecs (sbAnnot hS q loadC wpC) b'' h * (if b'' then nGatesN wpC else
            nGatesN loadC) ∧
      (propCount (selPrep hS (q.params.nu / 3) (q.prep (Zs := Zs) [] [])) wGateN h : ℝ) ≤
        80 * q.g * (2 * 10 ^ 18 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
          (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
            (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ 3 *
          (c₁ * (64 * (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
            (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1)) + c₀ + 1)) +
        40 * q.g * (4 * (3 * 10 ^ 11 * (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
            (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ 3 +
          2 * Fintype.card Zs + Fintype.card Xa) + 3)) :=
  ⟨binary_ode_time_cert_sel hS hadj hzt hc₀ hc₁ hlen bd q hq hγ hζ hb hc0 hT hH hD D en hrange hdec
      loadC hloadV hloadG wpC hwpV hwpG,
    binary_time_sel_sources hS hadj hzt hc₀ hc₁ hlen bd q hq hγ hζ hb hc0 hT hH hD D en hrange hdec
        loadC hloadG wpC hwpG⟩

end Endpoint

end

end ManuscriptConformance
