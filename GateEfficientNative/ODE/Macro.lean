import GateEfficientNative.Hamiltonian.Circuit
import GateEfficientNative.Model.Touch
import GateEfficientODE.Circuit.Reflect

/-!
# Native macros for the released gate-level ODE solvers

The released solvers act on the wires `AW a m r K k l f` (simulator wires and
solver wires) with the system as payload.  Their simulator instructions call
`U_J` and the private Cayley operation under the sector wire of the
simulator (`odeRel`); the private operation is selected by solver wires (the
joint label, and in the time-dependent case also the slot wires).

The native register adds the system qubits, the work wires of the private
implementation, the scratch `Zs` of the source circuits, one flag and a pool
`Fin nP` for the native zero tests (`HWO`).  `omacro` replaces

* gates, `U_J` calls and private calls by the macros of `hmacro`;
* source calls by supplied native source circuits `srcN b adj`;
* seed reflections by nothing (they do not occur in the preparations).

`omacro_approx`: in the full-output convention on clean work wires every
macro implements its released instruction, a private call within `4ζ` and a
source call within the accuracy `ζs` of the source circuits; along a list
the errors add (`oprep_approx`).
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateNative

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit
open GateCircuit.Sim (Wire anc_injective)
open GateODE (OInstr OWire AW localOp_localOp localOp_localOp' overwrite_apply_ι
  overwrite_apply_out)
open scoped InnerProduct BigOperators

/-! ### The released ODE register -/

/-- The released ODE register: the ancillas and the sector wire of the
embedded simulator. -/
def odeRel (a m r K k l f : ℕ) : RelW (AW a m r K k l f) a :=
  ⟨fun i => Sum.inl (Wire.anc i), fun _ _ h => anc_injective (Sum.inl_injective h),
    Sum.inl Wire.sec, fun _ h => by cases h⟩

/-- Extra work wires of the native ODE register: source scratch, the native
flag and the native pool. -/
abbrev OX (Zs : Type*) (nP : ℕ) := Zs ⊕ (Unit ⊕ Fin nP)

/-- The native ODE register. -/
abbrev HWO (a m r K k l f : ℕ) (S Zs : Type*) (nP : ℕ) (Z : Type*) (bT bP A : ℕ) :=
  HW (AW a m r K k l f) S (OX Zs nP) Z bT bP A

section Instr

variable {a m r K k l f : ℕ}

/-- A literal control on a simulator wire, on the ODE register. -/
def liftLit (c : Wire a m r K × Bool) : AW a m r K k l f × Bool := (Sum.inl c.1, c.2)

/-- The oracle calls of an instruction are controlled by the sector wire. -/
def OSecOK : OInstr (Wire a m r K) (OWire k l f) → Prop
  | .uj cs _ => cs = [(Wire.sec, true)]
  | .priv cs _ => cs = [(Wire.sec, true)]
  | _ => True

/-- Is a source call. -/
def isSrcAny : OInstr (Wire a m r K) (OWire k l f) → Bool
  | .src _ _ => true
  | _ => false

/-- The number of source calls. -/
def nSrcAny (gs : List (OInstr (Wire a m r K) (OWire k l f))) : ℕ := gs.countP isSrcAny

theorem nSrcAny_eq (gs : List (OInstr (Wire a m r K) (OWire k l f))) :
    nSrcAny gs = GateODE.nSrc false gs + GateODE.nSrc true gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
      simp only [nSrcAny, GateODE.nSrc, List.countP_cons] at ih ⊢
      rw [ih]
      cases g with
      | src b adj => cases b <;> simp [isSrcAny, OInstr.isSrc] <;> ring
      | _ => simp [isSrcAny, OInstr.isSrc]

end Instr

/-! ### The macros -/

section Macro

variable {a m r K k l f : ℕ} {S Zs Z Sel Y J : Type*} {nP : ℕ}

/-- **The native macro of a released ODE instruction.** -/
def omacro (sw : SelWires (odeRel a m r K k l f) Sel) (UJg : List (Gate (Fin a ⊕ S)))
    (nd : NativeOp Sel (Fin a ⊕ S) Z Y J) (ar : Arith (NB Sel (Fin a ⊕ S) Z))
    (srcN : Bool → Bool → List (NInstr (HWO a m r K k l f S Zs nP Z ar.bT ar.bP ar.A) Y J)) :
    OInstr (Wire a m r K) (OWire k l f) →
      List (NInstr (HWO a m r K k l f S Zs nP Z ar.bT ar.bP ar.A) Y J)
  | .gate g => hmacro (odeRel a m r K k l f) sw UJg nd ar (.gate g)
  | .uj cs adj => hmacro (odeRel a m r K k l f) sw UJg nd ar (.uj (cs.map liftLit) adj)
  | .priv cs adj => hmacro (odeRel a m r K k l f) sw UJg nd ar (.priv (cs.map liftLit) adj)
  | .src b adj => srcN b adj
  | .seed _ => []

variable [Fintype S] [DecidableEq S] [Fintype Zs] [DecidableEq Zs] [Fintype Z] [DecidableEq Z]
  [Fintype Sel] [DecidableEq Sel] [Fintype Y] [DecidableEq Y]
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- The error weight of a released instruction. -/
def oweight (ζ ζs : ℝ) (i : OInstr (Wire a m r K) (OWire k l f)) : ℝ :=
  (if i.isPriv then 4 * ζ else 0) + (if isSrcAny i then ζs else 0)

omit [Fintype S] [DecidableEq S] [Fintype Zs] [DecidableEq Zs] [Fintype Z] [DecidableEq Z]
  [Fintype Sel] [DecidableEq Sel] [Fintype Y] [DecidableEq Y] in
theorem sum_oweight (ζ ζs : ℝ) (gs : List (OInstr (Wire a m r K) (OWire k l f))) :
    (gs.map (oweight ζ ζs)).sum = (GateODE.nPriv gs : ℝ) * (4 * ζ) + (nSrcAny gs : ℝ) * ζs := by
  induction gs with
  | nil => simp [GateODE.nPriv, nSrcAny]
  | cons i gs ih =>
      rw [List.map_cons, List.sum_cons, ih]
      simp only [GateODE.nPriv, nSrcAny, List.countP_cons, oweight]
      cases i <;> simp [OInstr.isPriv, isSrcAny] <;> ring

/-- **Every native ODE macro implements its released instruction.** -/
theorem omacro_approx (prim : J → Reg Y R →L[ℂ] Reg Y R) (hprim : ∀ j, IsUnitary (prim j))
    (sw : SelWires (odeRel a m r K k l f) Sel) (UJg : List (Gate (Fin a ⊕ S)))
    (hUJ : ∀ g ∈ UJg, GateOK 3 g)
    (nd : NativeOp Sel (Fin a ⊕ S) Z Y J) (hnd : nd.Public) (ar : Arith (NB Sel (Fin a ⊕ S) Z))
    {ζ : ℝ} (hζ : 0 ≤ ζ) (har : ArithOK ar (Sum.inl (Sum.inr nd.o)) nd.dec ζ)
    (Dfam : Bool → Cfg Sel → (Reg (Fin a) (Reg S R) →L[ℂ] Reg (Fin a) (Reg S R)))
    (hDu : ∀ w, IsUnitary (Dfam false w)) (hDadj : ∀ w, Dfam true w = (Dfam false w)†)
    (hN : NativeOK prim nd (selOp (Dfam false)))
    (ev : OInstr (Wire a m r K) (OWire k l f) →
      Reg (AW a m r K k l f) (Reg S R) →L[ℂ] Reg (AW a m r K k l f) (Reg S R))
    (hev_gate : ∀ g, ev (.gate g) = gateOp g.cs g.t g.u)
    (hev_uj : ∀ adj, ev (.uj [(Wire.sec, true)] adj) =
      evalSel (odeRel a m r K k l f) UJg sw Dfam (.uj [(Sum.inl Wire.sec, true)] adj))
    (hev_priv : ∀ adj, ev (.priv [(Wire.sec, true)] adj) =
      evalSel (odeRel a m r K k l f) UJg sw Dfam (.priv [(Sum.inl Wire.sec, true)] adj))
    (srcN : Bool → Bool → List (NInstr (HWO a m r K k l f S Zs nP Z ar.bT ar.bP ar.A) Y J))
    {ζs : ℝ}
    (hsrc : ∀ b adj, ApproxOn CleanX (nrun prim (srcN b adj)) (liftB (conj (ev (.src b adj)))) ζs)
    (i : OInstr (Wire a m r K) (OWire k l f)) (hi : OSecOK i) (hseed : i.isSeed = false) :
    ApproxOn CleanX (nrun prim (omacro sw UJg nd ar srcN i)) (liftB (conj (ev i)))
      (oweight ζ ζs i) := by
  cases i with
  | gate g =>
      have h := hmacro_approx (X' := OX Zs nP) prim hprim (odeRel a m r K k l f) sw UJg hUJ nd hnd
        ar hζ har Dfam hDu hDadj hN (.gate g)
      have e1 : (if (Instr.gate g : Instr (AW a m r K k l f)).isPriv then 4 * ζ else 0) =
          oweight ζ ζs (OInstr.gate g : OInstr (Wire a m r K) (OWire k l f)) := by
        simp [oweight, OInstr.isPriv, isSrcAny, Instr.isPriv]
      have e2 : evalSel (odeRel a m r K k l f) UJg sw Dfam (.gate g) = ev (.gate g) := by
        rw [hev_gate]; rfl
      rw [e1, e2] at h
      exact h
  | uj cs adj =>
      simp only [OSecOK] at hi
      subst hi
      have h := hmacro_approx (X' := OX Zs nP) prim hprim (odeRel a m r K k l f) sw UJg hUJ nd hnd
        ar hζ har Dfam hDu hDadj hN (.uj [(Sum.inl Wire.sec, true)] adj)
      have e1 : (if (Instr.uj [(Sum.inl Wire.sec, true)] adj : Instr (AW a m r K k l f)).isPriv
          then 4 * ζ else 0) =
          oweight ζ ζs
            (OInstr.uj [(Wire.sec, true)] adj : OInstr (Wire a m r K) (OWire k l f)) := by
        simp [oweight, OInstr.isPriv, isSrcAny, Instr.isPriv]
      rw [e1, ← hev_uj] at h
      exact h
  | priv cs adj =>
      simp only [OSecOK] at hi
      subst hi
      have h := hmacro_approx (X' := OX Zs nP) prim hprim (odeRel a m r K k l f) sw UJg hUJ nd hnd
        ar hζ har Dfam hDu hDadj hN (.priv [(Sum.inl Wire.sec, true)] adj)
      have e1 : (if (Instr.priv [(Sum.inl Wire.sec, true)] adj : Instr (AW a m r K k l f)).isPriv
          then 4 * ζ else 0) =
          oweight ζ ζs
            (OInstr.priv [(Wire.sec, true)] adj : OInstr (Wire a m r K) (OWire k l f)) := by
        simp [oweight, OInstr.isPriv, isSrcAny, Instr.isPriv]
      rw [e1, ← hev_priv] at h
      exact h
  | src b adj =>
      have e1 : oweight ζ ζs (OInstr.src b adj : OInstr (Wire a m r K) (OWire k l f)) = ζs := by
        simp [oweight, OInstr.isPriv, isSrcAny]
      rw [e1]
      exact hsrc b adj
  | seed cs => simp [OInstr.isSeed] at hseed

/-! ### Validity -/

omit [Fintype S] [Fintype Zs] [DecidableEq Zs] [Fintype Z] [Fintype Sel] [Fintype Y]
  [DecidableEq Y] in
theorem omacro_valid (sw : SelWires (odeRel a m r K k l f) Sel) (UJg : List (Gate (Fin a ⊕ S)))
    (hUJ : ∀ g ∈ UJg, GateOK 3 g) (nd : NativeOp Sel (Fin a ⊕ S) Z Y J) (hnd : nd.Public)
    (ar : Arith (NB Sel (Fin a ⊕ S) Z)) (helem : ∀ g ∈ ar.circ, g.cs.length ≤ 3)
    (hcl : Classical ar.circ)
    (srcN : Bool → Bool → List (NInstr (HWO a m r K k l f S Zs nP Z ar.bT ar.bP ar.A) Y J))
    (hsrcV : ∀ b adj, ∀ j ∈ srcN b adj, j.Valid)
    (i : OInstr (Wire a m r K) (OWire k l f)) (hi : OSecOK i) (hv : i.Valid Wire.anc) :
    ∀ j ∈ omacro sw UJg nd ar srcN i, j.Valid := by
  cases i with
  | gate g =>
      exact hmacro_valid (odeRel a m r K k l f) sw UJg hUJ nd hnd ar helem hcl (.gate g) hv
  | uj cs adj =>
      simp only [OSecOK] at hi
      subst hi
      simp only [omacro]
      refine hmacro_valid (odeRel a m r K k l f) sw UJg hUJ nd hnd ar helem hcl _ ?_
      refine ⟨by simp, ?_⟩
      intro c hc i h
      simp only [List.map_cons, List.map_nil, liftLit, List.mem_cons, List.not_mem_nil,
        or_false] at hc
      subst hc
      cases h
  | priv cs adj =>
      simp only [OSecOK] at hi
      subst hi
      simp only [omacro]
      refine hmacro_valid (odeRel a m r K k l f) sw UJg hUJ nd hnd ar helem hcl _ ?_
      refine ⟨by simp, ?_⟩
      intro c hc i h
      simp only [List.map_cons, List.map_nil, liftLit, List.mem_cons, List.not_mem_nil,
        or_false] at hc
      subst hc
      cases h
  | src b adj => exact hsrcV b adj
  | seed cs => intro j hj; simp [omacro] at hj

/-! ### Along a list -/

/-- **The native preparation approximates the released one**: the errors of the
private calls and of the source calls add. -/
theorem oprep_approx (prim : J → Reg Y R →L[ℂ] Reg Y R) (hprim : ∀ j, IsUnitary (prim j))
    (sw : SelWires (odeRel a m r K k l f) Sel) (UJg : List (Gate (Fin a ⊕ S)))
    (hUJ : ∀ g ∈ UJg, GateOK 3 g)
    (nd : NativeOp Sel (Fin a ⊕ S) Z Y J) (hnd : nd.Public) (ar : Arith (NB Sel (Fin a ⊕ S) Z))
    {ζ : ℝ} (hζ : 0 ≤ ζ) (har : ArithOK ar (Sum.inl (Sum.inr nd.o)) nd.dec ζ)
    (Dfam : Bool → Cfg Sel → (Reg (Fin a) (Reg S R) →L[ℂ] Reg (Fin a) (Reg S R)))
    (hDu : ∀ w, IsUnitary (Dfam false w)) (hDadj : ∀ w, Dfam true w = (Dfam false w)†)
    (hN : NativeOK prim nd (selOp (Dfam false)))
    (ev : OInstr (Wire a m r K) (OWire k l f) →
      Reg (AW a m r K k l f) (Reg S R) →L[ℂ] Reg (AW a m r K k l f) (Reg S R))
    (hev_gate : ∀ g, ev (.gate g) = gateOp g.cs g.t g.u)
    (hev_uj : ∀ adj, ev (.uj [(Wire.sec, true)] adj) =
      evalSel (odeRel a m r K k l f) UJg sw Dfam (.uj [(Sum.inl Wire.sec, true)] adj))
    (hev_priv : ∀ adj, ev (.priv [(Wire.sec, true)] adj) =
      evalSel (odeRel a m r K k l f) UJg sw Dfam (.priv [(Sum.inl Wire.sec, true)] adj))
    (srcN : Bool → Bool → List (NInstr (HWO a m r K k l f S Zs nP Z ar.bT ar.bP ar.A) Y J))
    {ζs : ℝ} (hζs : 0 ≤ ζs)
    (hsrc : ∀ b adj, ApproxOn CleanX (nrun prim (srcN b adj)) (liftB (conj (ev (.src b adj)))) ζs)
    (hsrcV : ∀ b adj, ∀ j ∈ srcN b adj, j.Valid)
    (gs : List (OInstr (Wire a m r K) (OWire k l f))) (hl : ∀ i ∈ gs, OSecOK i)
    (hseed : ∀ i ∈ gs, i.isSeed = false) (hv : ∀ i ∈ gs, i.Valid Wire.anc)
    (hevU : ∀ i ∈ gs, IsUnitary (ev i)) :
    ApproxOn CleanX (nrun prim (gs.flatMap (omacro sw UJg nd ar srcN)))
      (liftB (conj (prodOps ev gs)))
      ((GateODE.nPriv gs : ℝ) * (4 * ζ) + (nSrcAny gs : ℝ) * ζs) := by
  have h := approxOn_flatMap prim CleanX (omacro sw UJg nd ar srcN)
    (fun i => liftB (X := XW Z ar.bT ar.bP ar.A ⊕ OX Zs nP) (conj (ev i)))
    (oweight ζ ζs) gs
    (fun i hi => omacro_approx prim hprim sw UJg hUJ nd hnd ar hζ har Dfam hDu hDadj hN ev hev_gate
      hev_uj hev_priv srcN hsrc i (hl i hi) (hseed i hi))
    (fun i _ => preserves_liftB _)
    (fun i hi ψ => IsUnitary.norm_apply_le (liftB_isUnitary (conj_isUnitary (hevU i hi))) ψ)
    (fun i hi ψ => IsUnitary.norm_apply_le (nrun_isUnitary prim hprim _
      (omacro_valid sw UJg hUJ nd hnd ar har.elem har.classical srcN hsrcV i (hl i hi)
        (hv i hi))) ψ)
    (fun i _ => by
      unfold oweight
      split_ifs <;> linarith)
  rw [sum_oweight, prodOps_liftB_conj] at h
  exact h

end Macro

/-! ### Counts -/

section Count

variable {a m r K k l f : ℕ} {S Zs Z Sel Y J : Type*} {nP : ℕ}

/-- The four kinds of counted released instructions. -/
theorem sum_le_ocounts (gs : List (OInstr (Wire a m r K) (OWire k l f)))
    (w : OInstr (Wire a m r K) (OWire k l f) → ℕ) (cg cu cp : ℕ) (cs : Bool → ℕ)
    (hw : ∀ i ∈ gs, w i ≤ (if i.isGate then cg else 0) + (if i.isUJ then cu else 0) +
      (if i.isPriv then cp else 0) + (if i.isSrc false then cs false else 0) +
      (if i.isSrc true then cs true else 0)) :
    (gs.map w).sum ≤ GateODE.nGates gs * cg + GateODE.nUJ gs * cu + GateODE.nPriv gs * cp +
      GateODE.nSrc false gs * cs false + GateODE.nSrc true gs * cs true := by
  induction gs with
  | nil => simp
  | cons i gs ih =>
      have h1 := hw i List.mem_cons_self
      have h2 := ih (fun j hj => hw j (List.mem_cons_of_mem i hj))
      rw [List.map_cons, List.sum_cons]
      simp only [GateODE.nGates, GateODE.nUJ, GateODE.nPriv, GateODE.nSrc, List.countP_cons]
        at h2 ⊢
      cases i with
      | src b adj =>
          cases b <;>
            simp only [OInstr.isGate, OInstr.isUJ, OInstr.isPriv, OInstr.isSrc, beq_self_eq_true,
              beq_true, beq_false, Bool.not_true, Bool.false_eq_true, if_false, if_true, add_zero,
              zero_add, add_mul, one_mul] at h1 h2 ⊢ <;> omega
      | _ =>
          simp only [OInstr.isGate, OInstr.isUJ, OInstr.isPriv, OInstr.isSrc, if_true,
            Bool.false_eq_true, if_false, add_zero, zero_add, add_mul, one_mul] at h1 h2 ⊢
          omega

theorem omacro_nGates (sw : SelWires (odeRel a m r K k l f) Sel) (UJg : List (Gate (Fin a ⊕ S)))
    (hUJ : ∀ g ∈ UJg, GateOK 3 g) (nd : NativeOp Sel (Fin a ⊕ S) Z Y J)
    (ar : Arith (NB Sel (Fin a ⊕ S) Z))
    (srcN : Bool → Bool → List (NInstr (HWO a m r K k l f S Zs nP Z ar.bT ar.bP ar.A) Y J))
    (cs : Bool → ℕ) (hcs : ∀ b adj, nGatesN (srcN b adj) ≤ cs b)
    (i : OInstr (Wire a m r K) (OWire k l f)) :
    nGatesN (omacro sw UJg nd ar srcN i) ≤ (if i.isGate then 1 else 0) +
      (if i.isUJ then 7 * UJg.length else 0) +
      (if i.isPriv then 2 * nGatesN nd.V + 2 * ar.circ.length + (2 * ar.bP + ar.bT + 1) else 0) +
      (if i.isSrc false then cs false else 0) + (if i.isSrc true then cs true else 0) := by
  cases i with
  | gate g =>
      have h := hmacro_nGates (X' := OX Zs nP) (odeRel a m r K k l f) sw UJg hUJ nd ar (.gate g)
      simp only [Instr.isGate, Instr.isUJ, Instr.isPriv] at h
      simp only [omacro, OInstr.isGate, OInstr.isUJ, OInstr.isPriv, OInstr.isSrc]
      simpa using h
  | uj c adj =>
      have h := hmacro_nGates (X' := OX Zs nP) (odeRel a m r K k l f) sw UJg hUJ nd ar
        (.uj (c.map liftLit) adj)
      simp only [Instr.isGate, Instr.isUJ, Instr.isPriv] at h
      simp only [omacro, OInstr.isGate, OInstr.isUJ, OInstr.isPriv, OInstr.isSrc]
      simpa using h
  | priv c adj =>
      have h := hmacro_nGates (X' := OX Zs nP) (odeRel a m r K k l f) sw UJg hUJ nd ar
        (.priv (c.map liftLit) adj)
      simp only [Instr.isGate, Instr.isUJ, Instr.isPriv] at h
      simp only [omacro, OInstr.isGate, OInstr.isUJ, OInstr.isPriv, OInstr.isSrc]
      simpa using h
  | src b adj =>
      have h := hcs b adj
      cases b <;> simpa [omacro, OInstr.isGate, OInstr.isUJ, OInstr.isPriv, OInstr.isSrc] using h
  | seed c => simp [omacro, nGatesN]

theorem omacro_nCalls (p : J → Bool) (sw : SelWires (odeRel a m r K k l f) Sel)
    (UJg : List (Gate (Fin a ⊕ S))) (nd : NativeOp Sel (Fin a ⊕ S) Z Y J)
    (ar : Arith (NB Sel (Fin a ⊕ S) Z))
    (srcN : Bool → Bool → List (NInstr (HWO a m r K k l f S Zs nP Z ar.bT ar.bP ar.A) Y J))
    (cs : Bool → ℕ) (hcs : ∀ b adj, nCallsN p (srcN b adj) = cs b)
    (i : OInstr (Wire a m r K) (OWire k l f)) :
    nCallsN p (omacro sw UJg nd ar srcN i) ≤
      (if i.isGate then 0 else 0) + (if i.isUJ then 0 else 0) +
      (if i.isPriv then 2 * nCallsN p nd.V else 0) +
      (if i.isSrc false then cs false else 0) + (if i.isSrc true then cs true else 0) := by
  cases i with
  | gate g =>
      have h := hmacro_nCalls (X' := OX Zs nP) p (odeRel a m r K k l f) sw UJg nd ar (.gate g)
      simp only [omacro, OInstr.isGate, OInstr.isUJ, OInstr.isPriv, OInstr.isSrc, h]
      simp [Instr.isPriv]
  | uj c adj =>
      have h := hmacro_nCalls (X' := OX Zs nP) p (odeRel a m r K k l f) sw UJg nd ar
        (.uj (c.map liftLit) adj)
      simp only [omacro, OInstr.isGate, OInstr.isUJ, OInstr.isPriv, OInstr.isSrc, h]
      simp [Instr.isPriv]
  | priv c adj =>
      have h := hmacro_nCalls (X' := OX Zs nP) p (odeRel a m r K k l f) sw UJg nd ar
        (.priv (c.map liftLit) adj)
      simp only [omacro, OInstr.isGate, OInstr.isUJ, OInstr.isPriv, OInstr.isSrc, h]
      simp [Instr.isPriv]
  | src b adj =>
      have h := hcs b adj
      cases b <;> simp [omacro, OInstr.isGate, OInstr.isUJ, OInstr.isPriv, OInstr.isSrc, h]
  | seed c => simp [omacro, nCallsN]

end Count

/-! ### Wires touched by the macros -/

section Targets

variable {W : Type*}

theorem andChain_target (p : W × Bool) (ls : List (W × Bool)) (fl : List W) :
    ∀ g ∈ andChain p ls fl, g.t ∈ fl := by
  induction ls generalizing p fl with
  | nil => intro g hg; simp [andChain] at hg
  | cons l ls ih =>
      cases fl with
      | nil => intro g hg; simp [andChain] at hg
      | cons f fs =>
          intro g hg
          simp only [andChain, List.mem_cons] at hg
          rcases hg with rfl | hg
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem f (ih (f, true) fs g hg)

theorem mcGate_target (ls : List (W × Bool)) (fl : List W) (t : W) (u : Matrix Bool Bool ℂ) :
    ∀ g ∈ mcGate ls fl t u, g.t = t ∨ g.t ∈ fl := by
  cases ls with
  | nil =>
      intro g hg
      simp only [mcGate, List.mem_cons, List.not_mem_nil, or_false] at hg
      subst hg
      exact Or.inl rfl
  | cons l ls =>
      intro g hg
      simp only [mcGate, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with (hg | rfl) | hg
      · exact Or.inr (andChain_target l ls fl g hg)
      · exact Or.inl rfl
      · obtain ⟨g', hg', rfl⟩ := mem_gInv _ g hg
        exact Or.inr (andChain_target l ls fl g' hg')

theorem ctrlGate_target (w₀ : W) (fl : List W) (h : Gate W) :
    ∀ g ∈ ctrlGate w₀ fl h, g.t = h.t ∨ g.t ∈ fl := by
  unfold ctrlGate
  split_ifs
  · intro g hg
    simp only [List.mem_singleton] at hg
    subst hg
    exact Or.inl rfl
  · exact mcGate_target _ fl h.t h.u

end Targets

section Touch

variable {a m r K k l f : ℕ} {S Zs Z Sel Y J : Type*} {nP : ℕ}

/-- The native flag and pool wires of the zero tests. -/
def reflWire {bT bP A : ℕ} : HWO a m r K k l f S Zs nP Z bT bP A → Prop
  | Sum.inr (Sum.inr (Sum.inr _)) => True
  | _ => False

theorem not_reflWire_inl {bT bP A : ℕ} (v : AW a m r K k l f ⊕ S) :
    ¬ reflWire (Sum.inl v : HWO a m r K k l f S Zs nP Z bT bP A) := fun h => h

theorem not_reflWire_xw {bT bP A : ℕ} (x : XW Z bT bP A) :
    ¬ reflWire (Sum.inr (Sum.inl x) : HWO a m r K k l f S Zs nP Z bT bP A) := fun h => h

theorem not_reflWire_zs {bT bP A : ℕ} (z : Zs) :
    ¬ reflWire (Sum.inr (Sum.inr (Sum.inl z)) : HWO a m r K k l f S Zs nP Z bT bP A) :=
  fun h => h

/-- **The macros never change the native flag and pool.** -/
theorem omacro_not_touches (sw : SelWires (odeRel a m r K k l f) Sel)
    (UJg : List (Gate (Fin a ⊕ S))) (nd : NativeOp Sel (Fin a ⊕ S) Z Y J)
    (ar : Arith (NB Sel (Fin a ⊕ S) Z))
    (srcN : Bool → Bool → List (NInstr (HWO a m r K k l f S Zs nP Z ar.bT ar.bP ar.A) Y J))
    (hsrcT : ∀ b adj, ∀ j ∈ srcN b adj, ¬ j.Touches reflWire)
    (i : OInstr (Wire a m r K) (OWire k l f)) :
    ∀ j ∈ omacro sw UJg nd ar srcN i, ¬ j.Touches reflWire := by
  have hgate : ∀ (cs : List ((AW a m r K k l f) × Bool)) (adj : Bool),
      ∀ j ∈ hmacro (X' := OX Zs nP) (odeRel a m r K k l f) sw UJg nd ar (.uj cs adj),
        ¬ j.Touches reflWire := by
    intro cs adj j hj
    simp only [hmacro, nGatesOf, List.mem_map] at hj
    obtain ⟨g, hg, rfl⟩ := hj
    simp only [ujGates, List.mem_flatMap] at hg
    obtain ⟨g', _, hg⟩ := hg
    change ¬ reflWire g.t
    rcases ctrlGate_target _ _ _ g hg with h | h
    · rw [h]
      exact not_reflWire_inl _
    · simp only [flagList, flagW, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h | h <;> rw [h] <;> exact not_reflWire_xw _
  have hpriv : ∀ (cs : List ((AW a m r K k l f) × Bool)) (adj : Bool),
      ∀ j ∈ hmacro (X' := OX Zs nP) (odeRel a m r K k l f) sw UJg nd ar (.priv cs adj),
        ¬ j.Touches reflWire := by
    intro cs adj j hj
    simp only [hmacro, List.mem_map] at hj
    obtain ⟨j', _, rfl⟩ := hj
    apply NInstr.not_touches_map
    intro v
    rcases v with ⟨⟩ | (((s | (i | x)) | z) | w) <;> exact fun h => h
  cases i with
  | gate g =>
      intro j hj
      simp only [omacro, hmacro, List.mem_singleton] at hj
      subst hj
      exact fun h => h
  | uj cs adj =>
      simp only [omacro]
      exact hgate _ adj
  | priv cs adj =>
      simp only [omacro]
      exact hpriv _ adj
  | src b adj =>
      simp only [omacro]
      exact hsrcT b adj
  | seed cs => intro j hj; simp [omacro] at hj

end Touch

end

end SparseHamiltonian.GateNative
