import ManuscriptConformance.PrepColumn
import GateEfficientNative.ODE.Time
import ZeroTimeGateODE.TimeAssembly
import GeneralSparseODE.Time
import GeneralDecoderODE.SolverTime

/-!
# The time-dependent native preparations depend only on the loader's label columns (item D1, part)

The native preparation of the time-dependent solver, `GateNative.tnprepC p UJg nd ar loadC wpC`, is
the macro expansion of the logical preparation
`Wp · LCHS · LOAD · SELECT · PHASE · LCHS⁻¹ · Wp⁻¹` (`GateODE.Time.TParams.prepC`). The zero-case
preparation `ZeroTimeGateODE.tzprepC` is `Wp · LOAD · Wp⁻¹`. In both, the supplied loading circuit
`loadC` appears exactly once, forward. On the seed it acts after the weight preparation (and the
LCHS rotation tree), which change neither the system nor the source scratch when the weight
preparation leaves its scratch clean on the clean input. So the loading circuit then acts only on
its label columns `|c⟩|0⟩_S|0⟩_{Zs}`, and two loading circuits with the same label columns give
preparations with the same column on the seed. With `PrepColumn`, the native protocols then have
the same law and the same released guarantees.

* `tnprepC_eq`, `omacro_tsrc_congr`, `flatMap_omacro_congr`, `prepPre_noLoad`, `prepPost_noLoad`:
  the decomposition of the preparation around the loading call. The macro expansion of the other
  instructions does not depend on the loading circuit.
* `load_agrees`: two loading circuits with the same label columns agree, placed on the native
  register, on the states with clean system and source scratch.
* `supp_wprep`: the placed weight preparation keeps the seed's system and source scratch clean when
  the weight-preparation circuit leaves its scratch clean on the clean input (`hwp`).
  `wpScratch_of_exact`: this holds in the exact case `ζ_s = 0` of the released source hypothesis.
* `tnprepC_column_congr`, `tzprepC_column_congr`: the columns of the two preparations depend on the
  loading circuit only through its label columns.
* For the general-size solvers, in both branches:
  * `GeneralSparseODE.liftC_cols`;
  * `GPubT.prep_column_congr`, `GPubT.wOutcome_of_loader_columns`;
  * `GeneralDecoderODE.prepTI_column_congr`, `prepTI_wOutcome_of_loader_columns` (any
    implementation of the padded oracles, so also the decoder solvers and the writer forms).

  The released guarantee `WOutcome` for one loading circuit gives it for every valid loading
  circuit with the same label columns.
* `SourceAccuracyODE.WOutcome.of_loader_columns`: the same for `tnprepC` directly.

Scope: the exact case of item D1 for the time-dependent native preparations.
* An approximate weight preparation, which may leave the scratch dirty, and approximate
  completions are not treated.
* The constant-coefficient preparation is not restated.
* The loading hypotheses of the endpoints are unchanged. They are stated for a label-controlled
  ideal loader on all clean inputs. The theorems here transfer the guarantees of a loading circuit
  meeting them to every loading circuit with the same label columns.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateNative

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit
open GateODE (OInstr OWire AW srcTS)
open GateODE.Time (TParams)
open scoped InnerProduct BigOperators

/-! ### The system and source-scratch wires -/

section Wires

variable {a m r K k l f : ℕ} {S Zs Z : Type*} {nP bT bP A : ℕ}

/-- The system wires and the source-scratch wires of the native register. -/
def sysScratch : HWO a m r K k l f S Zs nP Z bT bP A → Prop
  | Sum.inl (Sum.inr _) => True
  | Sum.inr (Sum.inr (Sum.inl _)) => True
  | _ => False

/-- The source-scratch wires of a weight-preparation circuit. -/
def wpScratch : Fin (k + 1) ⊕ Zs → Prop
  | Sum.inl _ => False
  | Sum.inr _ => True

end Wires

/-! ### The loading circuit on its label columns -/

section Load

variable {a m r K k l f : ℕ} {S Zs Z Y J : Type*} {nP bT bP A : ℕ}
  [Fintype S] [DecidableEq S] [Fintype Zs] [DecidableEq Zs] [Fintype Z] [DecidableEq Z]
  [Fintype Y] [DecidableEq Y]

/-- **Two loading circuits with the same label columns agree on the native register** on the
states with clean system and source scratch. -/
theorem load_agrees (P : J → Reg Y ℂ →L[ℂ] Reg Y ℂ)
    (loadC loadC' : List (NInstr ((Fin (k + 1) ⊕ S) ⊕ Zs) Y J))
    (hcol : ∀ (c : Cfg (Fin (k + 1))) (q : ℂ),
      nrun P loadC (bas (Sum.elim (Sum.elim c (fun _ => false)) (fun _ => false)) q) =
        nrun P loadC' (bas (Sum.elim (Sum.elim c (fun _ => false)) (fun _ => false)) q)) :
    Agrees (ZeroOn (sysScratch (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f)
        (S := S) (Zs := Zs) (nP := nP) (Z := Z) (bT := bT) (bP := bP) (A := A)))
      (nrun P (loadC.map (NInstr.map loadPl)))
      (nrun P (loadC'.map (NInstr.map loadPl))) := by
  rw [nrun_map, nrun_map]
  apply agrees_of_bas
  intro z hz q
  simp only [localOp_bas]
  have hloc : (fun x => z (loadPl (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f)
      (S := S) (Zs := Zs) (nP := nP) (Z := Z) (bT := bT) (bP := bP) (A := A) x)) =
      Sum.elim (Sum.elim (fun i => z (Sum.inl (Sum.inl (srcTS i)))) (fun _ => false))
        (fun _ => false) := by
    funext x
    rcases x with (i | s) | w
    · rfl
    · exact hz (Sum.inl (Sum.inr s)) trivial
    · exact hz (Sum.inr (Sum.inr (Sum.inl w))) trivial
  rw [hloc, hcol]

/-- **The placed weight preparation keeps the seed's system and source scratch clean**, when the
weight-preparation circuit leaves its scratch clean on the clean input. -/
theorem supp_wprep (P : J → Reg Y ℂ →L[ℂ] Reg Y ℂ) (wpC : List (NInstr (Fin (k + 1) ⊕ Zs) Y J))
    (hwp : Supp (ZeroOn wpScratch) (nrun P wpC (bas (fun _ => false) 1))) :
    Supp (ZeroOn (sysScratch (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f)
        (S := S) (Zs := Zs) (nP := nP) (Z := Z) (bT := bT) (bP := bP) (A := A)))
      (nrun P (wpC.map (NInstr.map wpPl)) sN) := by
  change Supp _ (nrun P (wpC.map (NInstr.map wpPl)) (bas (fun _ => false) 1))
  rw [nrun_map]
  simp only [localOp_bas]
  intro y hy
  rw [GateODE.put_apply]
  split_ifs with h
  · apply hwp
    intro hz
    apply hy
    intro w hw
    rcases w with (v | s) | (x | (zs | u))
    · exact False.elim hw
    · -- a system wire: outside the placement, so clean as in the seed
      have hout : ∀ c, wpPl (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f)
          (S := S) (Zs := Zs) (nP := nP) (Z := Z) (bT := bT) (bP := bP) (A := A) c ≠
          Sum.inl (Sum.inr s) := by
        rintro (c | c) hc <;> cases hc
      exact congrFun h ⟨Sum.inl (Sum.inr s), hout⟩
    · exact False.elim hw
    · exact hz (Sum.inr zs) trivial
    · exact False.elim hw
  · rfl

omit [Fintype S] [DecidableEq S] [Fintype Z] [DecidableEq Z] in
/-- **An exact weight preparation leaves its scratch clean on the clean input**: the exact case
(`ζ_s = 0`) of the released source hypothesis `ApproxOn CleanX (nrun P wpC) (liftB (matOp Wp))`. -/
theorem wpScratch_of_exact (P : J → Reg Y ℂ →L[ℂ] Reg Y ℂ)
    (wpC : List (NInstr (Fin (k + 1) ⊕ Zs) Y J)) (Wp : Matrix (Cfg (Fin (k + 1)))
      (Cfg (Fin (k + 1))) ℂ)
    (h : ApproxOn CleanX (nrun P wpC) (liftB (X := Zs) (matOp Wp)) 0) :
    Supp (ZeroOn wpScratch) (nrun P wpC (bas (fun _ => false) 1)) := by
  have hb : Supp CleanX (bas (fun _ => false : Cfg (Fin (k + 1) ⊕ Zs)) (1 : ℂ)) :=
    supp_bas _ (fun _ => rfl) _
  have he : nrun P wpC (bas (fun _ => false) 1) = liftB (X := Zs) (matOp Wp)
      (bas (fun _ => false) 1) := by
    have h0 := h _ hb
    rw [zero_mul, norm_le_zero_iff, sub_eq_zero] at h0
    exact h0
  rw [he]
  intro y hy
  apply (pres2_liftB (X := Zs) (matOp Wp)).1 _ hb
  intro hc
  apply hy
  intro w hw
  rcases w with w | w
  · exact False.elim hw
  · exact hc w

/-- **The zero-case preparation depends only on the loader's label columns**: the weight
preparation, the placed loading circuit and the inverse weight preparation
(`ZeroTimeGateODE.tzprepC`) act in the same way on the seed for two loading circuits with the same
label columns, when the weight-preparation circuit leaves its scratch clean on the clean input. -/
theorem tzprepC_column_congr (P : J → Reg Y ℂ →L[ℂ] Reg Y ℂ)
    (loadC loadC' : List (NInstr ((Fin (k + 1) ⊕ S) ⊕ Zs) Y J))
    (wpC : List (NInstr (Fin (k + 1) ⊕ Zs) Y J))
    (hwp : Supp (ZeroOn wpScratch) (nrun P wpC (bas (fun _ => false) 1)))
    (hcol : ∀ (c : Cfg (Fin (k + 1))) (q : ℂ),
      nrun P loadC (bas (Sum.elim (Sum.elim c (fun _ => false)) (fun _ => false)) q) =
        nrun P loadC' (bas (Sum.elim (Sum.elim c (fun _ => false)) (fun _ => false)) q)) :
    nrun P (ZeroTimeGateODE.tzprepC loadC wpC :
        List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J)) sN =
      nrun P (ZeroTimeGateODE.tzprepC loadC' wpC :
        List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J)) sN := by
  have hL := load_agrees (a := a) (m := m) (r := r) (K := K) (l := l) (f := f) (nP := nP) (Z := Z)
    (bT := bT) (bP := bP) (A := A) P loadC loadC' hcol _ (supp_wprep P wpC hwp)
  unfold ZeroTimeGateODE.tzprepC
  simp only [nrun_append, comp_apply]
  rw [hL]

end Load

/-! ### The preparation around the loading call -/

section Prep

variable {S Zs Z Y J : Type*} [Fintype S] [DecidableEq S] [Fintype Zs] [DecidableEq Zs]
  [Fintype Z] [DecidableEq Z] [Fintype Y] [DecidableEq Y]

omit [DecidableEq S] [DecidableEq Zs] [DecidableEq Z] [Fintype Y] [DecidableEq Y] in
/-- The macro expansion of an instruction other than the loading call does not depend on the
loading circuit. -/
theorem omacro_tsrc_congr (p : TParams) {Sel : Type*} [Fintype Sel] [DecidableEq Sel]
    (sw : SelWires (odeRel p.a p.m p.r p.K p.m p.l p.f) Sel) (UJg : List (Gate (Fin p.a ⊕ S)))
    (nd : NativeOp Sel (Fin p.a ⊕ S) Z Y J) (ar : Arith (NB Sel (Fin p.a ⊕ S) Z))
    (loadC loadC' : List (NInstr ((Fin (p.m + 1) ⊕ S) ⊕ Zs) Y J))
    (wpC : List (NInstr (Fin (p.m + 1) ⊕ Zs) Y J))
    (i : OInstr (GateCircuit.Sim.Wire p.a p.m p.r p.K) (OWire p.m p.l p.f))
    (hi : ∀ adj, i ≠ OInstr.src false adj) :
    omacro (nP := tnPool p S Zs Z ar.bT ar.bP ar.A) sw UJg nd ar (tsrcMacro p loadC wpC) i =
      omacro sw UJg nd ar (tsrcMacro p loadC' wpC) i := by
  cases i with
  | gate g => rfl
  | uj cs adj => rfl
  | priv cs adj => rfl
  | src b adj =>
      cases b with
      | false => exact absurd rfl (hi adj)
      | true => cases adj <;> rfl
  | seed cs => rfl

omit [DecidableEq S] [DecidableEq Zs] [DecidableEq Z] [Fintype Y] [DecidableEq Y] in
theorem flatMap_omacro_congr (p : TParams) {Sel : Type*} [Fintype Sel] [DecidableEq Sel]
    (sw : SelWires (odeRel p.a p.m p.r p.K p.m p.l p.f) Sel) (UJg : List (Gate (Fin p.a ⊕ S)))
    (nd : NativeOp Sel (Fin p.a ⊕ S) Z Y J) (ar : Arith (NB Sel (Fin p.a ⊕ S) Z))
    (loadC loadC' : List (NInstr ((Fin (p.m + 1) ⊕ S) ⊕ Zs) Y J))
    (wpC : List (NInstr (Fin (p.m + 1) ⊕ Zs) Y J))
    (L : List (OInstr (GateCircuit.Sim.Wire p.a p.m p.r p.K) (OWire p.m p.l p.f)))
    (hL : ∀ i ∈ L, ∀ adj, i ≠ OInstr.src false adj) :
    L.flatMap (omacro (nP := tnPool p S Zs Z ar.bT ar.bP ar.A) sw UJg nd ar
        (tsrcMacro p loadC wpC)) =
      L.flatMap (omacro sw UJg nd ar (tsrcMacro p loadC' wpC)) := by
  induction L with
  | nil => rfl
  | cons i L ih =>
      rw [List.flatMap_cons, List.flatMap_cons,
        omacro_tsrc_congr p sw UJg nd ar loadC loadC' wpC i (hL i (List.mem_cons.mpr (Or.inl rfl))),
        ih (fun j hj => hL j (List.mem_cons_of_mem _ hj))]

/-- The instructions of the preparation before the loading call. -/
def prepPre (p : TParams) : List (OInstr (GateCircuit.Sim.Wire p.a p.m p.r p.K)
    (OWire p.m p.l p.f)) :=
  p.wprepC ++ GateODE.ofGates p.lchPrep

/-- The instructions of the preparation after the loading call. -/
def prepPost (p : TParams) : List (OInstr (GateCircuit.Sim.Wire p.a p.m p.r p.K)
    (OWire p.m p.l p.f)) :=
  p.select ++ (GateODE.ofGates p.lchPhase ++ GateODE.invList (GateODE.ofGates p.lchPrep) ++
    GateODE.invList p.wprepC)

theorem prepPre_noLoad (p : TParams) : ∀ i ∈ prepPre p, ∀ adj, i ≠ OInstr.src false adj := by
  intro i hi adj he
  subst he
  simp [prepPre, GateODE.Time.TParams.wprepC, GateODE.ofGates] at hi

theorem prepPost_noLoad (p : TParams) : ∀ i ∈ prepPost p, ∀ adj, i ≠ OInstr.src false adj := by
  intro i hi adj he
  subst he
  simp only [prepPost, List.mem_append] at hi
  rcases hi with h | ((h | h) | h)
  · simp only [GateODE.Time.TParams.select, List.mem_map] at h
    obtain ⟨j, _, hj⟩ := h
    cases j <;> cases hj
  · simp [GateODE.ofGates] at h
  · simp [GateODE.invList, GateODE.ofGates, GateODE.OInstr.inv] at h
  · simp [GateODE.invList, GateODE.Time.TParams.wprepC, GateODE.OInstr.inv] at h

omit [DecidableEq S] [DecidableEq Zs] [DecidableEq Z] [Fintype Y] [DecidableEq Y] in
/-- **The preparation around the loading call**: the macro expansion of the instructions before
the loading call, the placed loading circuit, and the macro expansion of the instructions after
it. -/
theorem tnprepC_eq (p : TParams) (UJg : List (Gate (Fin p.a ⊕ S)))
    (nd : NativeOp (TSel p.m p.l p.m) (Fin p.a ⊕ S) Z Y J)
    (ar : Arith (NB (TSel p.m p.l p.m) (Fin p.a ⊕ S) Z))
    (loadC : List (NInstr ((Fin (p.m + 1) ⊕ S) ⊕ Zs) Y J))
    (wpC : List (NInstr (Fin (p.m + 1) ⊕ Zs) Y J)) :
    tnprepC p UJg nd ar loadC wpC =
      (prepPre p).flatMap (omacro tlabSel UJg nd ar (tsrcMacro p loadC wpC)) ++
        (loadC.map (NInstr.map loadPl) ++
          (prepPost p).flatMap (omacro tlabSel UJg nd ar (tsrcMacro p loadC wpC))) := by
  have hload : p.load.flatMap (omacro (nP := tnPool p S Zs Z ar.bT ar.bP ar.A) tlabSel UJg nd ar
      (tsrcMacro p loadC wpC)) = loadC.map (NInstr.map loadPl) := by
    rw [show p.load = [OInstr.src false false] from rfl, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
    rfl
  unfold tnprepC
  rw [show p.prepC = prepPre p ++ p.load ++ prepPost p from by
    simp only [prepPre, prepPost, GateODE.Time.TParams.prepC, List.append_assoc]]
  rw [List.flatMap_append, List.flatMap_append, hload, List.append_assoc]

/-- **The column of the time-dependent native preparation depends only on the loader's label
columns**: for two loading circuits with the same label columns `|c⟩|0⟩_S|0⟩_{Zs}` and a
weight-preparation circuit leaving its scratch clean on the clean input, the two preparations act
in the same way on the seed. -/
theorem tnprepC_column_congr (p : TParams) (UJg : List (Gate (Fin p.a ⊕ S)))
    (nd : NativeOp (TSel p.m p.l p.m) (Fin p.a ⊕ S) Z Y J)
    (ar : Arith (NB (TSel p.m p.l p.m) (Fin p.a ⊕ S) Z)) (P : J → Reg Y ℂ →L[ℂ] Reg Y ℂ)
    (loadC loadC' : List (NInstr ((Fin (p.m + 1) ⊕ S) ⊕ Zs) Y J))
    (wpC : List (NInstr (Fin (p.m + 1) ⊕ Zs) Y J))
    (hwp : Supp (ZeroOn wpScratch) (nrun P wpC (bas (fun _ => false) 1)))
    (hcol : ∀ (c : Cfg (Fin (p.m + 1))) (q : ℂ),
      nrun P loadC (bas (Sum.elim (Sum.elim c (fun _ => false)) (fun _ => false)) q) =
        nrun P loadC' (bas (Sum.elim (Sum.elim c (fun _ => false)) (fun _ => false)) q)) :
    nrun P (tnprepC p UJg nd ar loadC wpC) sN = nrun P (tnprepC p UJg nd ar loadC' wpC) sN := by
  -- the state after the weight preparation and the LCHS rotation tree
  have hpre : (prepPre p).flatMap (omacro (nP := tnPool p S Zs Z ar.bT ar.bP ar.A) tlabSel UJg nd
      ar (tsrcMacro p loadC' wpC)) = wpC.map (NInstr.map wpPl) ++
        (GateODE.ofGates p.lchPrep).flatMap
          (omacro tlabSel UJg nd ar (tsrcMacro p loadC' wpC)) := by
    rw [prepPre, List.flatMap_append,
      show p.wprepC = [OInstr.src true false] from rfl, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
    rfl
  have hsupp : Supp (ZeroOn sysScratch) (nrun P ((prepPre p).flatMap
      (omacro (nP := tnPool p S Zs Z ar.bT ar.bP ar.A) tlabSel UJg nd ar
        (tsrcMacro p loadC' wpC))) sN) := by
    rw [hpre, nrun_append, comp_apply]
    apply preserves_nrun_zeroOn P sysScratch
    · intro i hi
      simp only [GateODE.ofGates, List.mem_flatMap, List.mem_map] at hi
      obtain ⟨_, ⟨g, _, rfl⟩, hg⟩ := hi
      change i ∈ [NInstr.gate (GateODE.Gate.map wEmb g)] at hg
      rw [List.mem_singleton] at hg
      subst hg
      intro h
      exact h
    · exact supp_wprep P wpC hwp
  have hL := load_agrees P loadC loadC' hcol _ hsupp
  rw [tnprepC_eq, tnprepC_eq,
    flatMap_omacro_congr p tlabSel UJg nd ar loadC loadC' wpC _ (prepPre_noLoad p),
    flatMap_omacro_congr p tlabSel UJg nd ar loadC loadC' wpC (prepPost p) (prepPost_noLoad p)]
  simp only [nrun_append, comp_apply]
  rw [hL]

end Prep

end

end SparseHamiltonian.GateNative

namespace SparseHamiltonian.GeneralSparseODE

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit GateNative GateBinary
open SparseHamiltonian.GeneralSparseAccess
open ZeroTimeGateODE (BTZeroCase tzprepC)
open SourceAccuracyODE (WOutcome)
open NativeSparseBlockEncoding (Query)
open scoped InnerProduct

/-- **Label columns of the lifted loading circuit**: two loading circuits with the same label
columns, lifted to the low wires of the padded system register (`liftC`), have the same label
columns. -/
theorem liftC_cols {C Zs Y J : Type*} [Fintype C] [DecidableEq C] [Fintype Zs] [DecidableEq Zs]
    [Fintype Y] [DecidableEq Y] {k : ℕ} (P : J → Reg Y ℂ →L[ℂ] Reg Y ℂ)
    (loadC loadC' : List (NInstr ((C ⊕ Fin k) ⊕ Zs) Y J))
    (hcol : ∀ (c : Cfg C) (q : ℂ),
      nrun P loadC (bas (Sum.elim (Sum.elim c (fun _ => false)) (fun _ => false)) q) =
        nrun P loadC' (bas (Sum.elim (Sum.elim c (fun _ => false)) (fun _ => false)) q))
    (c : Cfg C) (q : ℂ) :
    nrun P (liftC loadC) (bas (Sum.elim (Sum.elim c (fun _ => false)) (fun _ => false)) q) =
      nrun P (liftC loadC') (bas (Sum.elim (Sum.elim c (fun _ => false)) (fun _ => false)) q) := by
  unfold liftC
  rw [nrun_map, nrun_map]
  simp only [localOp_bas]
  have hloc : (fun x => (Sum.elim (Sum.elim c (fun _ => false)) (fun _ => false) :
      Cfg ((C ⊕ Fin (k + 1)) ⊕ Zs)) (liftE C Zs k x)) =
      Sum.elim (Sum.elim c (fun _ => false)) (fun _ => false) := by
    funext x
    rcases x with (i | i) | w <;> rfl
  rw [hloc, hcol]

namespace GPubT

variable (q : GPubT) {Zs : Type*} [Fintype Zs] [DecidableEq Zs]

/-- **The preparation of the general-size time-dependent solver depends only on the loader's
label columns**, in both branches, when the weight-preparation circuit leaves its scratch clean on
the clean input. -/
theorem prep_column_congr (N : ℕ) (z₀ : Cfg (VW q.b))
    (P : Query → Reg (Fin q.m ⊕ PY q.k q.b) ℂ →L[ℂ] Reg (Fin q.m ⊕ PY q.k q.b) ℂ)
    (loadC loadC' : List (NInstr ((Fin (q.m + 1) ⊕ Fin q.k) ⊕ Zs) (Fin q.m ⊕ PY q.k q.b) Query))
    (wpC : List (NInstr (Fin (q.m + 1) ⊕ Zs) (Fin q.m ⊕ PY q.k q.b) Query))
    (hwp : Supp (ZeroOn wpScratch) (nrun P wpC (bas (fun _ => false) 1)))
    (hcol : ∀ (c : Cfg (Fin (q.m + 1))) (q' : ℂ),
      nrun P loadC (bas (Sum.elim (Sum.elim c (fun _ => false)) (fun _ => false)) q') =
        nrun P loadC' (bas (Sum.elim (Sum.elim c (fun _ => false)) (fun _ => false)) q')) :
    nrun P (q.prep N z₀ loadC wpC) sN = nrun P (q.prep N z₀ loadC' wpC) sN := by
  have hcol' := liftC_cols P loadC loadC' hcol
  unfold GPubT.prep
  split_ifs
  · exact tzprepC_column_congr P _ _ wpC hwp hcol'
  · exact tnprepC_column_congr q.pub.params q.pub.UJg (q.nd N z₀) q.ar P _ _ wpC hwp hcol'

theorem prep_pres (N : ℕ) (z₀ : Cfg (VW q.b))
    (P : Query → Reg (Fin q.m ⊕ PY q.k q.b) ℂ →L[ℂ] Reg (Fin q.m ⊕ PY q.k q.b) ℂ)
    (loadC : List (NInstr ((Fin (q.m + 1) ⊕ Fin q.k) ⊕ Zs) (Fin q.m ⊕ PY q.k q.b) Query))
    (wpC : List (NInstr (Fin (q.m + 1) ⊕ Zs) (Fin q.m ⊕ PY q.k q.b) Query)) :
    Pres2 (ZeroOn reflWire) (nrun P (q.prep N z₀ loadC wpC)) := by
  unfold GPubT.prep
  split_ifs
  · exact ZeroTimeGateODE.tzprepC_pres _ wpC P
  · exact tnprepC_pres q.pub.params q.pub.UJg (q.nd N z₀) q.ar _ wpC P

/-- **The guarantee of the general-size time-dependent solver depends on the loading circuit only
through its label columns**: if the protocol with the loading circuit `loadC` has the guarantee
`WOutcome … β` against `x` (for instance from `general_time_outcome`), then so has that with every
loading circuit `loadC'` with the same label columns whose preparation is valid, for unitary
primitives and a weight-preparation circuit leaving its scratch clean on the clean input. -/
theorem wOutcome_of_loader_columns (N : ℕ) (z₀ : Cfg (VW q.b))
    (P : Query → Reg (Fin q.m ⊕ PY q.k q.b) ℂ →L[ℂ] Reg (Fin q.m ⊕ PY q.k q.b) ℂ)
    (hP : ∀ j, IsUnitary (P j))
    (loadC loadC' : List (NInstr ((Fin (q.m + 1) ⊕ Fin q.k) ⊕ Zs) (Fin q.m ⊕ PY q.k q.b) Query))
    (wpC : List (NInstr (Fin (q.m + 1) ⊕ Zs) (Fin q.m ⊕ PY q.k q.b) Query))
    (hv' : ∀ i ∈ q.prep N z₀ loadC' wpC, i.Valid)
    (hwp : Supp (ZeroOn wpScratch) (nrun P wpC (bas (fun _ => false) 1)))
    (hcol : ∀ (c : Cfg (Fin (q.m + 1))) (q' : ℂ),
      nrun P loadC (bas (Sum.elim (Sum.elim c (fun _ => false)) (fun _ => false)) q') =
        nrun P loadC' (bas (Sum.elim (Sum.elim c (fun _ => false)) (fun _ => false)) q'))
    {g β : ℝ} {hg : 1 ≤ g} {x : Reg (Fin (q.k + 1)) ℂ}
    (h : WOutcome (q.prep N z₀ loadC wpC) g β hg P x) :
    WOutcome (q.prep N z₀ loadC' wpC) g β hg P x :=
  h.of_column (Nat.le_succ _) (q.prep_pres N z₀ P loadC wpC) hv' hP
    (q.prep_pres N z₀ P loadC' wpC) (q.prep_column_congr N z₀ P loadC loadC' wpC hwp hcol)

end GPubT

end

end SparseHamiltonian.GeneralSparseODE

namespace SparseHamiltonian.GeneralDecoderODE

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit GateNative GateBinary
open SparseHamiltonian.GeneralSparseAccess
open SparseHamiltonian.GeneralSparseODE (GPubT liftC liftC_cols)
open ZeroTimeGateODE (BTZeroCase tzprepC)
open SourceAccuracyODE (WOutcome)
open NativeSparseBlockEncoding (Query)
open scoped InnerProduct

variable (q : GPubT) {Y Xa Zs : Type*} [Fintype Y] [DecidableEq Y] [Fintype Xa] [DecidableEq Xa]
  [Fintype Zs] [DecidableEq Zs]

/-- **The preparation through any implementation depends only on the loader's label columns**
(`prepTI`, the time-dependent preparation of the decoder solvers and of the writer forms), in both
branches, when the weight-preparation circuit leaves its scratch clean on the clean input. -/
theorem prepTI_column_congr (impl : Query → List (NInstr (PY (q.k + 1) q.b ⊕ Xa) Y Query))
    (P : Query → Reg (Fin q.m ⊕ Y) ℂ →L[ℂ] Reg (Fin q.m ⊕ Y) ℂ)
    (loadC loadC' : List (NInstr ((Fin (q.m + 1) ⊕ Fin q.k) ⊕ Zs) (Fin q.m ⊕ Y) Query))
    (wpC : List (NInstr (Fin (q.m + 1) ⊕ Zs) (Fin q.m ⊕ Y) Query))
    (hwp : Supp (ZeroOn wpScratch) (nrun P wpC (bas (fun _ => false) 1)))
    (hcol : ∀ (c : Cfg (Fin (q.m + 1))) (q' : ℂ),
      nrun P loadC (bas (Sum.elim (Sum.elim c (fun _ => false)) (fun _ => false)) q') =
        nrun P loadC' (bas (Sum.elim (Sum.elim c (fun _ => false)) (fun _ => false)) q')) :
    nrun P (prepTI q impl loadC wpC) sN = nrun P (prepTI q impl loadC' wpC) sN := by
  have hcol' := liftC_cols P loadC loadC' hcol
  unfold prepTI
  split_ifs
  · exact tzprepC_column_congr P _ _ wpC hwp hcol'
  · exact tnprepC_column_congr q.pub.params q.pub.UJg (ndTI q impl) (arTI q Xa) P _ _ wpC hwp
      hcol'

theorem prepTI_pres (impl : Query → List (NInstr (PY (q.k + 1) q.b ⊕ Xa) Y Query))
    (P : Query → Reg (Fin q.m ⊕ Y) ℂ →L[ℂ] Reg (Fin q.m ⊕ Y) ℂ)
    (loadC : List (NInstr ((Fin (q.m + 1) ⊕ Fin q.k) ⊕ Zs) (Fin q.m ⊕ Y) Query))
    (wpC : List (NInstr (Fin (q.m + 1) ⊕ Zs) (Fin q.m ⊕ Y) Query)) :
    Pres2 (ZeroOn reflWire) (nrun P (prepTI q impl loadC wpC)) := by
  unfold prepTI
  split_ifs
  · exact ZeroTimeGateODE.tzprepC_pres _ wpC P
  · exact tnprepC_pres q.pub.params q.pub.UJg (ndTI q impl) (arTI q Xa) _ wpC P

/-- **The guarantee of the time-dependent solver through any implementation depends on the loading
circuit only through its label columns**: `WOutcome` for the loading circuit `loadC` (for instance
from `general_time_outcomeI`, `decoder_time_outcome` or its writer form) gives `WOutcome` for every
loading circuit `loadC'` with the same label columns whose preparation is valid, for unitary
primitives and a weight-preparation circuit leaving its scratch clean on the clean input. -/
theorem prepTI_wOutcome_of_loader_columns
    (impl : Query → List (NInstr (PY (q.k + 1) q.b ⊕ Xa) Y Query))
    (P : Query → Reg (Fin q.m ⊕ Y) ℂ →L[ℂ] Reg (Fin q.m ⊕ Y) ℂ) (hP : ∀ j, IsUnitary (P j))
    (loadC loadC' : List (NInstr ((Fin (q.m + 1) ⊕ Fin q.k) ⊕ Zs) (Fin q.m ⊕ Y) Query))
    (wpC : List (NInstr (Fin (q.m + 1) ⊕ Zs) (Fin q.m ⊕ Y) Query))
    (hv' : ∀ i ∈ prepTI q impl loadC' wpC, i.Valid)
    (hwp : Supp (ZeroOn wpScratch) (nrun P wpC (bas (fun _ => false) 1)))
    (hcol : ∀ (c : Cfg (Fin (q.m + 1))) (q' : ℂ),
      nrun P loadC (bas (Sum.elim (Sum.elim c (fun _ => false)) (fun _ => false)) q') =
        nrun P loadC' (bas (Sum.elim (Sum.elim c (fun _ => false)) (fun _ => false)) q'))
    {g β : ℝ} {hg : 1 ≤ g} {x : Reg (Fin (q.k + 1)) ℂ}
    (h : WOutcome (prepTI q impl loadC wpC) g β hg P x) :
    WOutcome (prepTI q impl loadC' wpC) g β hg P x :=
  h.of_column (Nat.le_succ _) (prepTI_pres q impl P loadC wpC) hv' hP
    (prepTI_pres q impl P loadC' wpC) (prepTI_column_congr q impl P loadC loadC' wpC hwp hcol)

end

end SparseHamiltonian.GeneralDecoderODE

namespace SparseHamiltonian.SourceAccuracyODE

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit GateNative
open GateODE (AW)
open GateODE.Time (TParams)
open scoped InnerProduct BigOperators

variable {S Zs Z Y J : Type*} [Fintype S] [DecidableEq S] [Fintype Zs] [DecidableEq Zs]
  [Fintype Z] [DecidableEq Z] [Fintype Y] [DecidableEq Y]

/-- **The released guarantee depends on the loading circuit only through its label columns**: if
the native protocol of the time-dependent preparation with the loading circuit `loadC` has the
guarantee `WOutcome … β` against `x`, then so has that with every valid loading circuit `loadC'`
with the same label columns, for unitary primitives and a weight-preparation circuit leaving its
scratch clean on the clean input. -/
theorem WOutcome.of_loader_columns (p : TParams)
    (UJg : List (Gate (Fin p.a ⊕ S))) (nd : NativeOp (TSel p.m p.l p.m) (Fin p.a ⊕ S) Z Y J)
    (ar : Arith (NB (TSel p.m p.l p.m) (Fin p.a ⊕ S) Z))
    (hnP : Fintype.card (AW p.a p.m p.r p.K p.m p.l p.f) + Fintype.card (XW Z ar.bT ar.bP ar.A) +
      Fintype.card Zs + Fintype.card S ≤ tnPool p S Zs Z ar.bT ar.bP ar.A + 1)
    (P : J → Reg Y ℂ →L[ℂ] Reg Y ℂ)
    (hP : ∀ j, IsUnitary (P j)) (loadC loadC' : List (NInstr ((Fin (p.m + 1) ⊕ S) ⊕ Zs) Y J))
    (wpC : List (NInstr (Fin (p.m + 1) ⊕ Zs) Y J))
    (hv' : ∀ i ∈ tnprepC p UJg nd ar loadC' wpC, i.Valid)
    (hwp : Supp (ZeroOn wpScratch) (nrun P wpC (bas (fun _ => false) 1)))
    (hcol : ∀ (c : Cfg (Fin (p.m + 1))) (q : ℂ),
      nrun P loadC (bas (Sum.elim (Sum.elim c (fun _ => false)) (fun _ => false)) q) =
        nrun P loadC' (bas (Sum.elim (Sum.elim c (fun _ => false)) (fun _ => false)) q))
    {g β : ℝ} {hg : 1 ≤ g} {x : Reg S ℂ}
    (h : WOutcome (tnprepC p UJg nd ar loadC wpC) g β hg P x) :
    WOutcome (tnprepC p UJg nd ar loadC' wpC) g β hg P x :=
  h.of_column hnP (tnprepC_pres p UJg nd ar loadC wpC P) hv' hP
    (tnprepC_pres p UJg nd ar loadC' wpC P)
    (tnprepC_column_congr p UJg nd ar P loadC loadC' wpC hwp hcol)

end

end SparseHamiltonian.SourceAccuracyODE
