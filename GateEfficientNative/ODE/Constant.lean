import GateEfficientNative.ODE.Protocol
import GateEfficientODE.Theorem

/-!
# Native gate-efficient dissipative ODE solver, constant coefficients

The released solver `GateEfficientODE` with every oracle call replaced by a
native implementation, on a qubit system `S` (payload `ℂ`, seed the all-zero
state):

* `U_J` by its `C_J` gates, controlled by the sector wire;
* the label-selected private Cayley operation by one native compute circuit
  `V` on the label wires, the private register and scratch, with reversible
  angle arithmetic and bit-controlled rotations (`NativeOK`, `ArithOK`);
* the controlled source interfaces `J₀` (on `ini = 0`) and `J_b` (on
  `ini = 1`) by supplied native circuits `srcC b` on the control, the system
  and source scratch `Zs`, each within `ζs` of the controlled interface
  (`srcIdeal`) in the full-output convention: the hypothesis `G_src, A_src`;
* the reflections by exact zero tests on the native register.

`native_ode_solver`: the native protocol depends only on the public data;
its trial circuits are valid, its worst-case counts of elementary gates and
of primitive calls are explicit, and for every instance satisfying the
released instance conditions with `24 d ζ + 2 ζs ≤ ν` it succeeds with
probability at least `2/3` and outputs a state within trace distance `ε` of
the normalised solution.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateNative

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit
open GateCircuit.Sim (Wire anc_injective simCircuit)
open GateODE (OInstr OWire AW goodF Params Label labOf adjIf wiring Oracles)
open ODEStateNormalization (unitDirection)
open scoped InnerProduct BigOperators

/-! ### Label selection -/

section Label

variable {a m r K k l f : ℕ}

/-- The label wires of the solver: the source sector, the node word and the
LCHS word. -/
abbrev LabW (k l : ℕ) := (Unit ⊕ Fin k) ⊕ Fin l

/-- The label wires in the solver register. -/
def labEmbFun : LabW k l → AW a m r K k l f
  | Sum.inl (Sum.inl _) => Sum.inr OWire.ini
  | Sum.inl (Sum.inr i) => Sum.inr (OWire.src i)
  | Sum.inr j => Sum.inr (OWire.lch j)

theorem labEmbFun_injective :
    Function.Injective
      (labEmbFun (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f)) := by
  intro x y h
  rcases x with (u | i) | j <;> rcases y with (u' | i') | j' <;>
    simp_all [labEmbFun]

/-- The label wires as selection wires of the private calls. -/
def labSel : SelWires (odeRel a m r K k l f) (LabW k l) :=
  ⟨⟨labEmbFun, labEmbFun_injective⟩,
    fun s => by rcases s with (u | i) | j <;> simp [labEmbFun, odeRel],
    fun s i => by rcases s with (u | i') | j <;> simp [labEmbFun, odeRel]⟩

/-- The joint label read from the label wires. -/
def labOfW (y : Cfg (LabW k l)) : Label k l :=
  ((y (Sum.inl (Sum.inl ())), fun i => y (Sum.inl (Sum.inr i))), fun j => y (Sum.inr j))

/-- The label-selected private family. -/
def labFam {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
    (D : Label k l → Anc a P →L[ℂ] Anc a P) :
    Bool → Cfg (LabW k l) → (Anc a P →L[ℂ] Anc a P) :=
  fun adj y => adjIf adj (D (labOfW y))

end Label

/-! ### The released oracle calls in selected form -/

section Eval

variable {a m r K k l f : ℕ} {S : Type*} [Fintype S] [DecidableEq S]

theorem ctrlOK_secW (x : Cfg (Wire a m r K)) : ctrlOK [(Wire.sec, true)] x = x Wire.sec := by
  simp [ctrlOK]

/-- A sector-controlled oracle call of the embedded simulator, selected by the
solver wires, in selected form. -/
theorem ode_oracle_eq (F : Cfg (AW a m r K k l f) → (Anc a (Reg S ℂ) →L[ℂ] Anc a (Reg S ℂ)))
    (hF : ∀ x x', (∀ o, x (Sum.inr o) = x' (Sum.inr o)) → F x = F x') :
    localOp (Sum.inl : Wire a m r K → AW a m r K k l f) Sum.inl_injective
        (fun x => oracleOp Wire.anc anc_injective [(Wire.sec, true)] (F x)) =
      localOp (odeRel a m r K k l f).anc (odeRel a m r K k l f).anc_inj
        (fun y => if y (Sum.inl Wire.sec) then F y else 1) := by
  unfold oracleOp
  rw [GateODE.localOp_localOp' Sum.inl_injective anc_injective (odeRel a m r K k l f).anc
    (odeRel a m r K k l f).anc_inj (fun _ => rfl)]
  apply localOp_congr
  intro z
  set z' := clearCfg (odeRel a m r K k l f).anc z
  have h1 : clearCfg Wire.anc (fun w => z' (Sum.inl w)) Wire.sec = z' (Sum.inl Wire.sec) :=
    clearCfg_apply_out _ _ Wire.sec (fun i h => by cases h)
  have h2 : F (clearCfg Sum.inl z') = F z' :=
    hF _ _ (fun o => clearCfg_apply_out _ _ _ (fun w h => by cases h))
  simp only [ctrlOK_secW, h1, h2]

variable {Zs Z : Type*} [Fintype Zs] [DecidableEq Zs] [Fintype Z] [DecidableEq Z] {nP bT bP A : ℕ}

/-- `U_J` from its gates in the released solver, in selected form. -/
theorem ode_eval_uj (v : Reg S ℂ) (σ : Oracles a (Label k l) (Reg S ℂ))
    (UJg : List (Gate (Fin a ⊕ S))) (hσ : σ.UJ = UJop (R := ℂ) UJg) {Sel : Type*} [Fintype Sel]
    [DecidableEq Sel] (sw : SelWires (odeRel a m r K k l f) Sel)
    (Dfam : Bool → Cfg Sel → (Anc a (Reg S ℂ) →L[ℂ] Anc a (Reg S ℂ))) (adj : Bool) :
    OInstr.eval (wiring (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f) v) σ
        (.uj [(Wire.sec, true)] adj) =
      evalSel (odeRel a m r K k l f) UJg sw Dfam (.uj [(Sum.inl Wire.sec, true)] adj) := by
  rw [OInstr.eval_uj]
  change localOp Sum.inl Sum.inl_injective (fun _ => oracleOp Wire.anc anc_injective
    [(Wire.sec, true)] (adjIf adj σ.UJ)) = _
  rw [ode_oracle_eq (fun _ => adjIf adj σ.UJ) (fun _ _ _ => rfl), hσ]
  rfl

/-- The label-selected private call in selected form. -/
theorem ode_eval_priv (v : Reg S ℂ) (σ : Oracles a (Label k l) (Reg S ℂ))
    (UJg : List (Gate (Fin a ⊕ S))) (adj : Bool) :
    OInstr.eval (wiring (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f) v) σ
        (.priv [(Wire.sec, true)] adj) =
      evalSel (odeRel a m r K k l f) UJg labSel (labFam (P := Reg S ℂ) σ.D)
        (.priv [(Sum.inl Wire.sec, true)] adj) := by
  rw [OInstr.eval_priv]
  change localOp Sum.inl Sum.inl_injective (fun x => oracleOp Wire.anc anc_injective
    [(Wire.sec, true)] (adjIf adj (σ.D (labOf (fun o => x (Sum.inr o)))))) = _
  rw [ode_oracle_eq (fun x => adjIf adj (σ.D (labOf (fun o => x (Sum.inr o)))))
    (fun x x' h => by simp only [h])]
  rfl

/-- A payload-controlled operator, flattened. -/
theorem conj_pctl {V : Type*} [Fintype V] [DecidableEq V] (cs : List (V × Bool))
    (O : Reg S ℂ →L[ℂ] Reg S ℂ) :
    conj (GateODE.pctl cs O : Reg V (Reg S ℂ) →L[ℂ] Reg V (Reg S ℂ)) =
      localOp (Sum.inr : S → V ⊕ S) Sum.inr_injective
        (fun y => if ctrlOK cs (fun w => y (Sum.inl w)) then O else 1) := by
  ext φ y
  rw [conj_apply, GateODE.pctl_apply, localOp_apply]
  have hc : (fun w => clearCfg (Sum.inr : S → V ⊕ S) y (Sum.inl w)) = (fun w => y (Sum.inl w)) :=
    funext (fun w => GateODE.overwrite_apply_out _ _ _ _ (fun s h => by cases h))
  have hs : slice (Sum.inr : S → V ⊕ S) φ y = (flat V S ℂ).symm φ (fun w => y (Sum.inl w)) := by
    apply PiLp.ext
    intro s
    have hov : overwrite (Sum.inr : S → V ⊕ S) y s = Sum.elim (fun w => y (Sum.inl w)) s := by
      funext u
      rcases u with w | s'
      · exact GateODE.overwrite_apply_out _ _ _ _ (fun s h => by cases h)
      · exact GateODE.overwrite_apply_ι Sum.inr_injective _ _ s'
    rw [slice_apply, flat_symm_apply, hov]
  rw [hc, hs]
  split_ifs <;> rfl

/-- The ideal of a source circuit: `O` on the system when the control wire
carries `b`. -/
def srcIdeal (b : Bool) (O : Reg S ℂ →L[ℂ] Reg S ℂ) : Reg (Unit ⊕ S) ℂ →L[ℂ] Reg (Unit ⊕ S) ℂ :=
  localOp (Sum.inr : S → Unit ⊕ S) Sum.inr_injective (fun y => if y (Sum.inl ()) = b then O else 1)

theorem srcIdeal_isUnitary (b : Bool) (O : Reg S ℂ →L[ℂ] Reg S ℂ) (hO : IsUnitary O) :
    IsUnitary (srcIdeal b O) :=
  localOp_isUnitary _ _ (fun y => by split_ifs; exacts [hO, isUnitary_one])

theorem srcIdeal_adjoint (b : Bool) (O : Reg S ℂ →L[ℂ] Reg S ℂ) :
    (srcIdeal b O)† = srcIdeal b (O†) := by
  unfold srcIdeal
  rw [localOp_adjoint]
  congr 1
  funext y
  split_ifs <;> simp

/-- The placement of the source circuit wires. -/
def srcPlFun : (Unit ⊕ S) ⊕ Zs → HWO a m r K k l f S Zs nP Z bT bP A
  | Sum.inl (Sum.inl _) => Sum.inl (Sum.inl (Sum.inr OWire.ini))
  | Sum.inl (Sum.inr s) => Sum.inl (Sum.inr s)
  | Sum.inr z => Sum.inr (Sum.inr (Sum.inl z))

omit [Fintype S] [DecidableEq S] [Fintype Zs] [DecidableEq Zs] [Fintype Z] [DecidableEq Z] in
theorem srcPlFun_injective : Function.Injective (srcPlFun (a := a) (m := m) (r := r) (K := K)
    (k := k) (l := l) (f := f) (S := S) (Zs := Zs) (nP := nP) (Z := Z) (bT := bT) (bP := bP)
    (A := A)) := by
  intro x y h
  rcases x with (u | s) | z <;> rcases y with (u' | s') | z' <;> simp_all [srcPlFun]

/-- The placement of the source circuit wires. -/
def srcPl : (Unit ⊕ S) ⊕ Zs ↪ HWO a m r K k l f S Zs nP Z bT bP A :=
  ⟨srcPlFun, srcPlFun_injective⟩

/-- The released controlled source call, flattened and lifted, is the placed
ideal of the source circuit. -/
theorem liftB_conj_src (b : Bool) (O : Reg S ℂ →L[ℂ] Reg S ℂ) :
    liftB (X := XW Z bT bP A ⊕ OX Zs nP)
      (conj (GateODE.pctl [(Sum.inr OWire.ini, b)] O :
        Reg (AW a m r K k l f) (Reg S ℂ) →L[ℂ] Reg (AW a m r K k l f) (Reg S ℂ))) =
      localOp (srcPl (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f) (S := S)
        (Zs := Zs) (nP := nP) (Z := Z) (bT := bT) (bP := bP) (A := A)) (srcPl).injective
        (fun _ => liftB (srcIdeal b O)) := by
  rw [conj_pctl]
  unfold liftB srcIdeal
  rw [GateODE.localOp_localOp' Sum.inl_injective Sum.inr_injective
      (fun s => (Sum.inl (Sum.inr s) : HWO a m r K k l f S Zs nP Z bT bP A))
      (fun _ _ h => Sum.inr_injective (Sum.inl_injective h)) (fun _ => rfl),
    GateODE.localOp_localOp (srcPl).injective Sum.inl_injective,
    GateODE.localOp_localOp' ((srcPl).injective.comp Sum.inl_injective) Sum.inr_injective
      (fun s => (Sum.inl (Sum.inr s) : HWO a m r K k l f S Zs nP Z bT bP A))
      (fun _ _ h => Sum.inr_injective (Sum.inl_injective h)) (fun _ => rfl)]
  apply localOp_congr
  intro z
  set z' := clearCfg (fun s => (Sum.inl (Sum.inr s) : HWO a m r K k l f S Zs nP Z bT bP A)) z
  have h1 : clearCfg (Sum.inr : S → AW a m r K k l f ⊕ S) (fun v => z' (Sum.inl v))
      (Sum.inl (Sum.inr OWire.ini)) = z' (Sum.inl (Sum.inl (Sum.inr OWire.ini))) :=
    clearCfg_apply_out _ _ _ (fun s h => by cases h)
  have h2 : clearCfg (Sum.inr : S → Unit ⊕ S) (fun t => z' (srcPl (Sum.inl t))) (Sum.inl ()) =
      z' (Sum.inl (Sum.inl (Sum.inr OWire.ini))) :=
    clearCfg_apply_out _ _ _ (fun s h => by cases h)
  simp only [ctrlOK, List.all_cons, List.all_nil, Bool.and_true, Function.comp_apply, h1, h2,
    beq_iff_eq]

/-- The lifted released source call is the placed ideal of the source circuit. -/
theorem liftB_conj_eval_src (v : Reg S ℂ) (σ : Oracles a (Label k l) (Reg S ℂ)) (b adj : Bool) :
    liftB (X := XW Z bT bP A ⊕ OX Zs nP)
      (conj (W := AW a m r K k l f) (S := S) (R := ℂ)
        (OInstr.eval (wiring (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f) v)
          σ (.src b adj))) =
      localOp (srcPl (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f) (S := S)
        (Zs := Zs) (nP := nP) (Z := Z) (bT := bT) (bP := bP) (A := A)) (srcPl).injective
        (fun _ => liftB (srcIdeal b (adjIf adj (σ.J b)))) := by
  rw [OInstr.eval_src]
  exact liftB_conj_src b (adjIf adj (σ.J b))

end Eval

/-! ### The native preparation -/

section Prep

variable {S Zs Z Y J : Type*} [Fintype S] [DecidableEq S] [Fintype Zs] [DecidableEq Zs]
  [Fintype Z] [DecidableEq Z] [Fintype Y] [DecidableEq Y]

/-- The size of the native pool. -/
abbrev nPool (p : Params) (S Zs Z : Type*) [Fintype S] [Fintype Zs] [Fintype Z] (bT bP A : ℕ) : ℕ :=
  Fintype.card p.W + Fintype.card (XW Z bT bP A) + Fintype.card Zs + Fintype.card S

/-- The native register of the constant-coefficient solver. -/
abbrev NW (p : Params) (S Zs Z : Type*) [Fintype S] [Fintype Zs] [Fintype Z] (bT bP A : ℕ) :=
  HWO p.a p.m p.r p.K p.k p.l p.f S Zs (nPool p S Zs Z bT bP A) Z bT bP A

/-- The native source macros: the source circuit or its literal inverse,
placed on the control, the system and the source scratch. -/
def srcMacro (p : Params) {bT bP A : ℕ} (srcC : Bool → List (NInstr ((Unit ⊕ S) ⊕ Zs) Y J))
    (b adj : Bool) : List (NInstr (NW p S Zs Z bT bP A) Y J) :=
  (if adj then ninv (srcC b) else srcC b).map (NInstr.map srcPl)

/-- **The native preparation circuit.**  It depends only on the public data:
`p`, the gates of `U_J`, the compute circuit, orientation wire and decoder of
the private operation, the arithmetic and the source circuits. -/
def nprepC (p : Params) (UJg : List (Gate (Fin p.a ⊕ S)))
    (nd : NativeOp (LabW p.k p.l) (Fin p.a ⊕ S) Z Y J)
    (ar : Arith (NB (LabW p.k p.l) (Fin p.a ⊕ S) Z))
    (srcC : Bool → List (NInstr ((Unit ⊕ S) ⊕ Zs) Y J)) :
    List (NInstr (NW p S Zs Z ar.bT ar.bP ar.A) Y J) :=
  p.prepC.flatMap (omacro labSel UJg nd ar (srcMacro p srcC))

theorem osec_prepC (p : Params) : ∀ i ∈ p.prepC, OSecOK i := by
  have hg : ∀ (gs : List (Gate p.W)), ∀ i ∈ GateODE.ofGates (S := Wire p.a p.m p.r p.K) gs,
      OSecOK i := by
    intro gs i hi
    simp only [GateODE.ofGates, List.mem_map] at hi
    obtain ⟨g, _, rfl⟩ := hi
    trivial
  have hgi : ∀ (gs : List (Gate p.W)),
      ∀ i ∈ GateODE.invList (GateODE.ofGates (S := Wire p.a p.m p.r p.K) gs), OSecOK i := by
    intro gs i hi
    simp only [GateODE.invList, GateODE.ofGates, List.mem_reverse, List.mem_map] at hi
    obtain ⟨_, ⟨g, _, rfl⟩, rfl⟩ := hi
    trivial
  have hsel : ∀ i ∈ p.select, OSecOK i := by
    intro i hi
    simp only [Params.select, List.mem_map] at hi
    obtain ⟨j, hj, rfl⟩ := hi
    have h := secOK_ampI (a := p.a) (m := p.m) (K := p.K) _ _ _ _ _ _ j hj
    cases j with
    | gate g => trivial
    | uj cs adj => exact h
    | priv cs adj => exact h
  intro i hi
  simp only [Params.prepC, List.mem_append] at hi
  rcases hi with ((((h | h) | h) | h) | ((h | h) | h))
  · exact hg _ i h
  · exact hg _ i h
  · simp only [Params.load, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> trivial
  · exact hsel i h
  · exact hg _ i h
  · exact hgi _ i h
  · exact hgi _ i h

theorem noseed_prepC (p : Params) (hτ : 0 ≤ p.tau) (hν : 0 < p.nu) :
    ∀ i ∈ p.prepC, i.isSeed = false := by
  have h := (p.prepC_counts hτ hν).2.2.2.1
  intro i hi
  by_contra hs
  have hs' : i.isSeed = true := by simpa using hs
  have : 0 < GateODE.nSeed p.prepC := List.countP_pos_iff.mpr ⟨i, hi, hs'⟩
  omega

theorem prodOps_oeval {a m r K k l f : ℕ} {Λ P : Type*} [NormedAddCommGroup P]
    [InnerProductSpace ℂ P] [CompleteSpace P]
    (ω : GateODE.Wiring (Wire a m r K) (OWire k l f) a Λ P) (σ : Oracles a Λ P)
    (gs : List (OInstr (Wire a m r K) (OWire k l f))) :
    prodOps (OInstr.eval ω σ) gs = GateODE.run ω σ gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih => rw [prodOps, GateODE.run_cons, ih]

/-- The source macros approximate the released controlled source calls. -/
theorem srcMacro_approx (p : Params) {bT bP A : ℕ} (prim : J → Reg Y ℂ →L[ℂ] Reg Y ℂ)
    (hprim : ∀ j, IsUnitary (prim j)) (srcC : Bool → List (NInstr ((Unit ⊕ S) ⊕ Zs) Y J))
    (hsrcV : ∀ b, ∀ i ∈ srcC b, i.Valid) (Jsrc : Bool → Reg S ℂ →L[ℂ] Reg S ℂ)
    (hJ : ∀ b, IsUnitary (Jsrc b)) {ζs : ℝ} (hζs : 0 ≤ ζs)
    (hsrc : ∀ b, ApproxOn CleanX (nrun prim (srcC b)) (liftB (srcIdeal b (Jsrc b))) ζs)
    (v : Reg S ℂ) (D : Label p.k p.l → Anc p.a (Reg S ℂ) →L[ℂ] Anc p.a (Reg S ℂ))
    (UJ : Anc p.a (Reg S ℂ) →L[ℂ] Anc p.a (Reg S ℂ)) (b adj : Bool) :
    ApproxOn CleanX (nrun prim (srcMacro (Z := Z) (bT := bT) (bP := bP) (A := A) p srcC b adj))
      (liftB (conj (OInstr.eval (wiring (a := p.a) (m := p.m) (r := p.r) (K := p.K) (k := p.k)
        (l := p.l) (f := p.f) v) ⟨UJ, D, Jsrc⟩ (.src b adj)))) ζs := by
  have hidealU : IsUnitary (liftB (X := Zs) (srcIdeal b (Jsrc b))) :=
    liftB_isUnitary (srcIdeal_isUnitary b _ (hJ b))
  have hCU : IsUnitary (nrun prim (srcC b)) := nrun_isUnitary prim hprim _ (hsrcV b)
  have hS : ∀ y : Cfg (NW p S Zs Z bT bP A), CleanX y →
      CleanX (fun c => y ((srcPl (a := p.a) (m := p.m) (r := p.r) (K := p.K) (k := p.k)
        (l := p.l) (f := p.f) (S := S) (Zs := Zs) (nP := nPool p S Zs Z bT bP A) (Z := Z)
        (bT := bT) (bP := bP) (A := A)) c)) := by
    intro y hy z
    exact hy (Sum.inr (Sum.inl z))
  rw [liftB_conj_eval_src, srcMacro, nrun_map]
  apply approxOn_localOp _ _ _ hζs hS
  intro _
  cases adj
  · show ApproxOn CleanX (nrun prim (srcC b)) (liftB (srcIdeal b (Jsrc b))) ζs
    exact hsrc b
  · show ApproxOn CleanX (nrun prim (ninv (srcC b))) (liftB (srcIdeal b ((Jsrc b)†))) ζs
    rw [nrun_ninv, ← srcIdeal_adjoint, liftB_adjoint]
    exact (hsrc b).adjoint hCU hidealU (by rw [← liftB_adjoint]; exact preserves_liftB _)

omit [Fintype Y] [DecidableEq Y] [DecidableEq S] [DecidableEq Zs] [DecidableEq Z] in
theorem srcMacro_not_touches (p : Params) {bT bP A : ℕ}
    (srcC : Bool → List (NInstr ((Unit ⊕ S) ⊕ Zs) Y J)) (b adj : Bool) :
    ∀ i ∈ srcMacro (Z := Z) (bT := bT) (bP := bP) (A := A) p srcC b adj, ¬ i.Touches reflWire := by
  intro i hi
  simp only [srcMacro, List.mem_map] at hi
  obtain ⟨i', _, rfl⟩ := hi
  apply NInstr.not_touches_map
  intro v
  rcases v with (u | s) | z <;> exact fun h => h

omit [Fintype Y] [DecidableEq Y] [DecidableEq S] [DecidableEq Zs] [DecidableEq Z] in
theorem srcMacro_valid (p : Params) {bT bP A : ℕ}
    (srcC : Bool → List (NInstr ((Unit ⊕ S) ⊕ Zs) Y J)) (hsrcV : ∀ b, ∀ i ∈ srcC b, i.Valid)
    (b adj : Bool) :
    ∀ i ∈ srcMacro (Z := Z) (bT := bT) (bP := bP) (A := A) p srcC b adj, i.Valid := by
  unfold srcMacro
  apply valid_map_list
  split_ifs
  · exact valid_ninv _ (hsrcV b)
  · exact hsrcV b

omit [Fintype Y] [DecidableEq Y] [DecidableEq S] [DecidableEq Zs] [DecidableEq Z] in
theorem srcMacro_counts (p : Params) {bT bP A : ℕ}
    (srcC : Bool → List (NInstr ((Unit ⊕ S) ⊕ Zs) Y J)) (b adj : Bool) (q : J → Bool) :
    nGatesN (srcMacro (Z := Z) (bT := bT) (bP := bP) (A := A) p srcC b adj) = nGatesN (srcC b) ∧
    nCallsN q (srcMacro (Z := Z) (bT := bT) (bP := bP) (A := A) p srcC b adj) =
      nCallsN q (srcC b) := by
  unfold srcMacro
  split_ifs
  · exact ⟨by rw [nGatesN_map, nGatesN_ninv], by rw [nCallsN_map, nCallsN_ninv]⟩
  · exact ⟨nGatesN_map _ _, nCallsN_map _ _ _⟩

end Prep

/-! ### The main theorem -/

section Main

variable {S Zs Z Y J : Type*} [Fintype S] [DecidableEq S] [Fintype Zs] [DecidableEq Zs]
  [Fintype Z] [DecidableEq Z] [Fintype Y] [DecidableEq Y]

/-- The gate count of one private call of the native implementation. -/
abbrev privGates {Sel PR Z' Y' J' : Type*} (nd : NativeOp Sel PR Z' Y' J')
    (ar : Arith (NB Sel PR Z')) : ℕ :=
  2 * nGatesN nd.V + 2 * ar.circ.length + (2 * ar.bP + ar.bT + 1)

/-- **Native gate-efficient dissipative ODE solver, constant coefficients**
(Theorem `ode:thm:gates`, before finite-set synthesis).

The native protocol `nprotocol (nprepC p UJg nd ar srcC) g` depends only on
the public data.  Its trial circuits consist of valid elementary gates and
primitive calls; one preparation uses at most
`prepGates + 84 d C_J + 6 d G_C + |srcC 0| + |srcC 1|` elementary gates (with
`G_C` the gates of one native private call) and at most
`12 d · calls(V) + calls(srcC 0) + calls(srcC 1)` primitive calls of every kind;
in every history the protocol uses at most `40 g` times these per preparation,
plus `20 g (4 n + 3)` gates for the zero tests, where `n` counts every wire
except the native flag and pool (the system qubits included, since the seed
reflection tests them).  For every instance with primitive oracles `prim`, private
Cayley operations `D z` given natively by `V` (`NativeOK`), source interfaces
`J b` approximated by the source circuits within `ζs`, the released instance
conditions for `(U_J, D, J)` and the error budget `24 d ζ + 2 ζs ≤ ν`, the
protocol succeeds with probability at least `2/3`, and its conditional output
is within trace distance `ε` of the normalised solution. -/
theorem native_ode_solver (p : Params) (hp : p.PublicOK)
    (UJg : List (Gate (Fin p.a ⊕ S))) (hUJg : ∀ g ∈ UJg, GateOK 3 g)
    (nd : NativeOp (LabW p.k p.l) (Fin p.a ⊕ S) Z Y J) (hnd : nd.Public)
    (ar : Arith (NB (LabW p.k p.l) (Fin p.a ⊕ S) Z)) (ζ : ℝ) (hζ : 0 ≤ ζ)
    (har : ArithOK ar (Sum.inl (Sum.inr nd.o)) nd.dec ζ)
    (srcC : Bool → List (NInstr ((Unit ⊕ S) ⊕ Zs) Y J)) (hsrcV : ∀ b, ∀ i ∈ srcC b, i.Valid) :
    (∀ j, ∀ i ∈ trialN (nprepC p UJg nd ar srcC) j, i.Valid) ∧
    nGatesN (nprepC p UJg nd ar srcC) ≤ p.prepGates + 84 * p.d * UJg.length +
      6 * p.d * privGates nd ar + nGatesN (srcC false) + nGatesN (srcC true) ∧
    (∀ q : J → Bool, nCallsN q (nprepC p UJg nd ar srcC) ≤
      12 * p.d * nCallsN q nd.V + nCallsN q (srcC false) + nCallsN q (srcC true)) ∧
    ((nprotocol (nprepC p UJg nd ar srcC) p.g hp.g_ge).worstCost wGateN : ℝ) ≤
      40 * p.g * nGatesN (nprepC p UJg nd ar srcC) +
        20 * p.g * (4 * (Fintype.card p.W + Fintype.card (XW Z ar.bT ar.bP ar.A) +
          Fintype.card Zs + Fintype.card S) + 3) ∧
    (∀ q : J → Bool, ((nprotocol (nprepC p UJg nd ar srcC) p.g hp.g_ge).worstCost (wCallN q) : ℝ) ≤
      40 * p.g * nCallsN q (nprepC p UJg nd ar srcC)) ∧
    Fintype.card (NW p S Zs Z ar.bT ar.bP ar.A) =
      Fintype.card S + 2 * (Fintype.card p.W + (Fintype.card Z + ar.bT + ar.bP + ar.A + 3) +
        Fintype.card Zs) + Fintype.card S + 1 ∧
    ∀ (prim : J → Reg Y ℂ →L[ℂ] Reg Y ℂ)
      (D : Label p.k p.l → Anc p.a (Reg S ℂ) →L[ℂ] Anc p.a (Reg S ℂ))
      (Jsrc : Bool → Reg S ℂ →L[ℂ] Reg S ℂ) (H L : Reg S ℂ →L[ℂ] Reg S ℂ) (x0 b : Reg S ℂ)
      (ζs : ℝ),
      (∀ j, IsUnitary (prim j)) →
      NativeOK prim nd (selOp (labFam D false)) →
      0 ≤ ζs →
      (∀ c, ApproxOn CleanX (nrun prim (srcC c)) (liftB (srcIdeal c (Jsrc c))) ζs) →
      24 * (p.d : ℝ) * ζ + 2 * ζs ≤ p.nu →
      p.InstanceOK (seedV (S := S))
        (⟨UJop (R := ℂ) UJg, D, Jsrc⟩ : Oracles p.a (Label p.k p.l) (Reg S ℂ)) H L x0 b →
      NOutcome (nprepC p UJg nd ar srcC) p.g p.ε hp.g_ge prim (p.target H L x0 b) := by
  have hτ := hp.tau_pos.le
  have hν := hp.nu_pos
  obtain ⟨cP, cU, cS, cE, cG⟩ := p.prepC_counts hτ hν
  have hvalid := p.prepC_valid hτ hν hp.r₀_nonneg hp.rb_nonneg hp.T_pos.le hp.B_pos
  have hsec := osec_prepC p
  have hnoseed := noseed_prepC p hτ hν
  have hprepV : ∀ i ∈ nprepC p UJg nd ar srcC, i.Valid := by
    intro i hi
    simp only [nprepC, List.mem_flatMap] at hi
    obtain ⟨o, ho, hi⟩ := hi
    exact omacro_valid labSel UJg hUJg nd hnd ar har.elem har.classical (srcMacro p srcC)
      (srcMacro_valid p srcC hsrcV) o (hsec o ho) (hvalid o ho) i hi
  have hnP : Fintype.card (AW p.a p.m p.r p.K p.k p.l p.f) +
      Fintype.card (XW Z ar.bT ar.bP ar.A) + Fintype.card Zs + Fintype.card S ≤
      nPool p S Zs Z ar.bT ar.bP ar.A + 1 := by
    have e : Fintype.card p.W = Fintype.card (AW p.a p.m p.r p.K p.k p.l p.f) := rfl
    unfold nPool
    omega
  refine ⟨fun j => trialN_valid _ hprepV j, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- gates of one preparation
    rw [nprepC, nGatesN_flatMap]
    refine (sum_le_ocounts _ _ 1 (7 * UJg.length) (privGates nd ar)
      (fun c => nGatesN (srcC c))
      (fun i _ => omacro_nGates labSel UJg hUJg nd ar (srcMacro p srcC)
        (fun c => nGatesN (srcC c))
        (fun c adj => (srcMacro_counts p srcC c adj (fun _ => true)).1.le)
        i)).trans ?_
    rw [cP, cU, cS false, cS true]
    have := cG
    nlinarith
  · -- calls of one preparation
    intro q
    rw [nprepC, nCallsN_flatMap]
    refine (sum_le_ocounts _ _ 0 0 (2 * nCallsN q nd.V) (fun c => nCallsN q (srcC c))
      (fun i _ => omacro_nCalls q labSel UJg nd ar (srcMacro p srcC) (fun c => nCallsN q (srcC c))
        (fun c adj => (srcMacro_counts p srcC c adj q).2) i)).trans ?_
    rw [cP, cS false, cS true]
    nlinarith
  · exact (nprotocol_worst _ p.g hp.g_ge (fun _ => true)).1
  · intro q
    exact (nprotocol_worst _ p.g hp.g_ge q).2
  · rw [card_HW]
    simp only [OX, Fintype.card_sum, Fintype.card_unit, Fintype.card_fin, nPool, XW, AWr]
    ring
  · intro prim D Jsrc H L x0 b ζs hprim hN hζs hsrc hbudget hI
    let σ : Oracles p.a (Label p.k p.l) (Reg S ℂ) := ⟨UJop (R := ℂ) UJg, D, Jsrc⟩
    have hU := p.unitaries_of (norm_seedV (S := S)) hI
    have hJ : ∀ c, IsUnitary (Jsrc c) := hU.src
    have hDu : ∀ w, IsUnitary (labFam D false w) := fun w => hU.priv _
    have hDadj : ∀ w, labFam D true w = (labFam D false w)† := fun _ => rfl
    have hP : Pres2 (ZeroOn reflWire) (nrun prim (nprepC p UJg nd ar srcC)) := by
      apply pres2_nrun_zeroOn
      intro i hi
      simp only [nprepC, List.mem_flatMap] at hi
      obtain ⟨o, _, hi⟩ := hi
      exact omacro_not_touches labSel UJg nd ar (srcMacro p srcC)
        (srcMacro_not_touches p srcC) o i hi
    have hA := oprep_approx prim hprim labSel UJg hUJg nd hnd ar hζ har (labFam D) hDu hDadj hN
      (OInstr.eval (wiring (seedV (S := S))) σ) (fun _ => rfl)
      (fun adj => ode_eval_uj (seedV (S := S)) σ UJg rfl labSel (labFam D) adj)
      (fun adj => ode_eval_priv (seedV (S := S)) σ UJg adj)
      (srcMacro p srcC) hζs
      (fun c adj => srcMacro_approx p prim hprim srcC hsrcV Jsrc hJ hζs hsrc (seedV (S := S)) D
        (UJop (R := ℂ) UJg) c adj)
      (srcMacro_valid p srcC hsrcV) p.prepC hsec hnoseed hvalid
      (fun i hi => OInstr.eval_isUnitary (wiring (seedV (S := S))) σ hU.uj hU.priv hU.src hU.seed i
        (hvalid i hi))
    rw [prodOps_oeval, nSrcAny_eq, cP, cS false, cS true] at hA
    -- the released certificate
    have hT := hp.T_pos.le
    have hS := hI.select
    have hC := p.prep_certificate hp (seedV (S := S)) norm_seedV σ H L x0 b hI
    have hdec := p.decoded_eq hp (seedV (S := S)) σ x0 b hI.init_norm hI.forcing_norm
    have hmass := p.mass_zsrc x0 b hT hI.init_norm hI.forcing_norm
    have hNorm : ‖p.target H L x0 b‖ ≤ p.B := by
      rw [← hmass]
      exact p.solution_le_mass hT H L hS.selfH hS.selfL hI.psd x0 b hI.init_norm hI.forcing_norm
    have h := hC.vector_error
    rw [hmass, ← hdec] at h
    have hδ : ((6 * p.d : ℕ) : ℝ) * (4 * ζ) + ((1 + 1 : ℕ) : ℝ) * ζs ≤
        ImprovedODEQueryBudget.precision p.g p.ε := by
      have e : p.nu = ImprovedODEQueryBudget.precision p.g p.ε := rfl
      have e2 : ((6 * p.d : ℕ) : ℝ) = 6 * (p.d : ℝ) := by rw [Nat.cast_mul, Nat.cast_ofNat]
      have e3 : ((1 + 1 : ℕ) : ℝ) = 2 := by norm_num
      rw [e2, e3]
      linarith only [hbudget, e]
    have hne := hI.target_ne
    have hbud := hI.budget
    generalize GateODE.run (wiring (seedV (S := S))) σ p.prepC = Urel at h hA
    generalize p.target H L x0 b = x at h hNorm hne hbud ⊢
    exact noutcome hnP (nprepC p UJg nd ar srcC) prim hprim hprepV hP Urel hA x p.B p.g p.ε hne
      hp.g_ge hp.ε_pos hp.ε_half hNorm hbud h hδ

end Main

end

end SparseHamiltonian.GateNative
