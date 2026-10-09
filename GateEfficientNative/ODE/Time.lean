import GateEfficientNative.ODE.Constant
import GateEfficientODE.Time.Theorem

/-!
# Native gate-efficient dissipative ODE solver, time-dependent coefficients

The released time-dependent solver `GateEfficientODE.Time` with every oracle
call replaced by a native implementation, on a qubit system `S` (payload `ℂ`,
seed the all-zero state):

* `U_J` by its `C_J` gates, controlled by the sector wire;
* the label- and slot-selected private Cayley operation by one native
  compute circuit `V` on the label wires, the slot wires, the private
  register and scratch, with reversible angle arithmetic and bit-controlled
  rotations (`NativeOK`, `ArithOK`);
* the coherent source loading `J s` by a supplied native circuit `loadC` on
  the source-label wires, the system and source scratch `Zs`, within `ζs` of
  the selected loading (`loadIdeal`), and the weight preparation `Wp` by a
  supplied native circuit `wpC` on the source-label wires and the scratch,
  within `ζs` of `Wp` (both in the full-output convention): the hypothesis
  `G_src, A_src`;
* the reflections by exact zero tests on the native register.

`native_ode_time_solver`: the native protocol depends only on the public
data; its trial circuits are valid, its worst-case counts of elementary gates
and of primitive calls are explicit, and for every instance satisfying the
released instance conditions with `24 d ζ + 3 ζs ≤ ν` it succeeds with
probability at least `2/3` and outputs a state within trace distance `ε` of
the normalised solution `x(T)`.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateNative

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit
open GateCircuit.Sim (Wire anc_injective)
open GateODE (OInstr OWire AW goodF Label labOf adjIf srcTS srcTS_injective)
open GateODE.Time (TParams TOracles teval trun psel labAt)
open GatePointerEncoding (wordEquivFin)
open ODEStateNormalization (unitDirection)
open scoped InnerProduct BigOperators

/-! ### Label and slot selection -/

section Select

variable {a m r K k l f : ℕ}

/-- The selection wires of the time-dependent private calls: the label wires
of the solver and the slot wires of the simulator. -/
abbrev TSel (k l m : ℕ) := LabW k l ⊕ Fin m

/-- The selection wires in the solver register. -/
def tselFun : TSel k l m → AW a m r K k l f
  | Sum.inl s => labEmbFun s
  | Sum.inr i => Sum.inl (Wire.slot i)

theorem tselFun_injective :
    Function.Injective
      (tselFun (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f)) := by
  intro x y h
  rcases x with ((u | i) | j) | i <;> rcases y with ((u' | i') | j') | i' <;>
    simp_all [tselFun, labEmbFun]

/-- The label and slot wires as selection wires of the private calls. -/
def tlabSel : SelWires (odeRel a m r K k l f) (TSel k l m) :=
  ⟨⟨tselFun, tselFun_injective⟩,
    fun s => by rcases s with ((u | i) | j) | i <;> simp [tselFun, labEmbFun, odeRel],
    fun s i => by rcases s with ((u | i') | j) | i' <;> simp [tselFun, labEmbFun, odeRel]⟩

/-- The label- and slot-selected private family: at the joint label `z` and
the slot word `w`, the private operation `D z w` (or its adjoint). -/
def tlabFam {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
    (D : Label k l → ℕ → Anc a P →L[ℂ] Anc a P) :
    Bool → Cfg (TSel k l m) → (Anc a P →L[ℂ] Anc a P) :=
  fun adj y => SlotSim.adjT adj
    (D (labOfW (fun s => y (Sum.inl s))) (wordEquivFin m (fun i => y (Sum.inr i))))

end Select

/-! ### The released oracle calls in selected form -/

section Eval

variable {a m r K k l f : ℕ} {S : Type*} [Fintype S] [DecidableEq S]

/-- A sector-controlled slot-selected oracle call of the embedded simulator,
selected by the solver wires, in selected form. -/
theorem ode_slot_oracle_eq
    (F : Cfg (AW a m r K k l f) → ℕ → (Anc a (Reg S ℂ) →L[ℂ] Anc a (Reg S ℂ)))
    (hF : ∀ x x', (∀ o, x (Sum.inr o) = x' (Sum.inr o)) → F x = F x') :
    localOp (Sum.inl : Wire a m r K → AW a m r K k l f) Sum.inl_injective
        (fun x => SlotSim.slotOracle [(Wire.sec, true)] (F x)) =
      localOp (odeRel a m r K k l f).anc (odeRel a m r K k l f).anc_inj
        (fun y => if y (Sum.inl Wire.sec) then
          F y (wordEquivFin m (fun i => y (Sum.inl (Wire.slot i)))) else 1) := by
  unfold SlotSim.slotOracle
  rw [GateODE.localOp_localOp' Sum.inl_injective anc_injective (odeRel a m r K k l f).anc
    (odeRel a m r K k l f).anc_inj (fun _ => rfl)]
  apply localOp_congr
  intro z
  set z' := clearCfg (odeRel a m r K k l f).anc z
  have h1 : clearCfg Wire.anc (fun w => z' (Sum.inl w)) Wire.sec = z' (Sum.inl Wire.sec) :=
    clearCfg_apply_out _ _ Wire.sec (fun i h => by cases h)
  have h2 : ∀ n, F (clearCfg Sum.inl z') n = F z' n := fun n =>
    congrFun (hF _ _ (fun o => clearCfg_apply_out _ _ _ (fun w h => by cases h))) n
  have h3 : GateCircuit.Sim.slotIdx (clearCfg Wire.anc (fun w => z' (Sum.inl w))) =
      wordEquivFin m (fun i => z' (Sum.inl (Wire.slot i))) := by
    unfold GateCircuit.Sim.slotIdx GateCircuit.Sim.slotOf
    congr 1
    funext i
    exact clearCfg_apply_out _ _ _ (fun j h => by cases h)
  simp only [ctrlOK_secW, h1, h2, h3]

/-- `U_J` from its gates in the time-dependent solver, in selected form. -/
theorem tode_eval_uj (v : Reg S ℂ) (σ : TOracles a k l (Reg S ℂ))
    (UJg : List (Gate (Fin a ⊕ S))) (hσ : σ.UJ = UJop (R := ℂ) UJg) {Sel : Type*} [Fintype Sel]
    [DecidableEq Sel] (sw : SelWires (odeRel a m r K k l f) Sel)
    (Dfam : Bool → Cfg Sel → (Anc a (Reg S ℂ) →L[ℂ] Anc a (Reg S ℂ))) (adj : Bool) :
    teval (m := m) (r := r) (K := K) (f := f) v σ (.uj [(Wire.sec, true)] adj) =
      evalSel (odeRel a m r K k l f) UJg sw Dfam (.uj [(Sum.inl Wire.sec, true)] adj) := by
  rw [GateODE.Time.teval_uj, ode_oracle_eq (fun _ => adjIf adj σ.UJ) (fun _ _ _ => rfl), hσ]
  rfl

/-- The label- and slot-selected private call in selected form. -/
theorem tode_eval_priv (v : Reg S ℂ) (σ : TOracles a k l (Reg S ℂ))
    (UJg : List (Gate (Fin a ⊕ S))) (adj : Bool) :
    teval (m := m) (r := r) (K := K) (f := f) v σ (.priv [(Wire.sec, true)] adj) =
      evalSel (odeRel a m r K k l f) UJg tlabSel (tlabFam (P := Reg S ℂ) σ.D)
        (.priv [(Sum.inl Wire.sec, true)] adj) := by
  have hF : ∀ x x' : Cfg (AW a m r K k l f), (∀ o, x (Sum.inr o) = x' (Sum.inr o)) →
      (fun j => SlotSim.adjT adj (σ.D (labAt x) j)) =
        (fun j => SlotSim.adjT adj (σ.D (labAt x') j)) := by
    intro x x' h
    have e : labAt x = labAt x' := congrArg GateODE.labOf (funext h)
    rw [e]
  rw [GateODE.Time.teval_priv]
  refine (ode_slot_oracle_eq (S := S) (fun x j => SlotSim.adjT adj (σ.D (labAt x) j)) hF).trans ?_
  rfl

/-- A configuration-selected payload operator, flattened. -/
theorem conj_psel {V : Type*} [Fintype V] [DecidableEq V] (F : Cfg V → Reg S ℂ →L[ℂ] Reg S ℂ) :
    conj (psel F : Reg V (Reg S ℂ) →L[ℂ] Reg V (Reg S ℂ)) =
      localOp (Sum.inr : S → V ⊕ S) Sum.inr_injective (fun y => F (fun w => y (Sum.inl w))) := by
  ext φ y
  rw [conj_apply, GateODE.Time.psel_apply, localOp_apply]
  have hc : (fun w => clearCfg (Sum.inr : S → V ⊕ S) y (Sum.inl w)) = (fun w => y (Sum.inl w)) :=
    funext (fun w => clearCfg_apply_out _ _ _ (fun s h => by cases h))
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

/-- A matrix on exposed wires with a register payload, flattened: the same
matrix, the identity on the payload wires. -/
theorem conj_matOp {T : Type*} [Fintype T] [DecidableEq T] (M : Matrix (Cfg T) (Cfg T) ℂ) :
    conj (matOp M : Reg T (Reg S ℂ) →L[ℂ] Reg T (Reg S ℂ)) = liftB (X := S) (matOp M) := by
  ext φ y
  rw [conj_apply, matOp_apply, liftB, localOp_apply, matOp_apply]
  simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, slice_apply,
    flat_symm_apply]
  apply Finset.sum_congr rfl
  intro c _
  have hcfg : Sum.elim c (fun s => y (Sum.inr s)) = overwrite (Sum.inl : T → T ⊕ S) y c := by
    funext v
    cases v with
    | inl t => exact (GateODE.overwrite_apply_ι Sum.inl_injective y c t).symm
    | inr s => exact (GateODE.overwrite_apply_out _ y c _ (fun b h => by cases h)).symm
  rw [hcfg]

end Eval

/-! ### The native source circuits -/

section SourceWires

variable {a m r K k l f : ℕ} {S Zs Z : Type*} {nP bT bP A : ℕ}

/-- The placement of the loading circuit wires: the source-label wires, the
system and the source scratch. -/
def loadPlFun : (Fin (k + 1) ⊕ S) ⊕ Zs → HWO a m r K k l f S Zs nP Z bT bP A
  | Sum.inl (Sum.inl i) => Sum.inl (Sum.inl (srcTS i))
  | Sum.inl (Sum.inr s) => Sum.inl (Sum.inr s)
  | Sum.inr z => Sum.inr (Sum.inr (Sum.inl z))

theorem loadPlFun_injective : Function.Injective (loadPlFun (a := a) (m := m) (r := r) (K := K)
    (k := k) (l := l) (f := f) (S := S) (Zs := Zs) (nP := nP) (Z := Z) (bT := bT) (bP := bP)
    (A := A)) := by
  intro x y h
  rcases x with (i | s) | z <;> rcases y with (i' | s') | z' <;>
    simp only [loadPlFun, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq] at h <;>
    first
      | rw [srcTS_injective h]
      | rw [h]

/-- The placement of the loading circuit wires. -/
def loadPl : (Fin (k + 1) ⊕ S) ⊕ Zs ↪ HWO a m r K k l f S Zs nP Z bT bP A :=
  ⟨loadPlFun, loadPlFun_injective⟩

/-- The placement of the weight-preparation circuit wires: the source-label
wires and the source scratch. -/
def wpPlFun : Fin (k + 1) ⊕ Zs → HWO a m r K k l f S Zs nP Z bT bP A
  | Sum.inl i => Sum.inl (Sum.inl (srcTS i))
  | Sum.inr z => Sum.inr (Sum.inr (Sum.inl z))

theorem wpPlFun_injective : Function.Injective (wpPlFun (a := a) (m := m) (r := r) (K := K)
    (k := k) (l := l) (f := f) (S := S) (Zs := Zs) (nP := nP) (Z := Z) (bT := bT) (bP := bP)
    (A := A)) := by
  intro x y h
  rcases x with i | z <;> rcases y with i' | z' <;>
    simp only [wpPlFun, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq] at h <;>
    first
      | rw [srcTS_injective h]
      | rw [h]

/-- The placement of the weight-preparation circuit wires. -/
def wpPl : Fin (k + 1) ⊕ Zs ↪ HWO a m r K k l f S Zs nP Z bT bP A :=
  ⟨wpPlFun, wpPlFun_injective⟩

end SourceWires

section Source

variable {a m r K k l f : ℕ} {S Zs Z : Type*} [Fintype S] [DecidableEq S] [Fintype Zs]
  [DecidableEq Zs] [Fintype Z] [DecidableEq Z] {nP bT bP A : ℕ}

/-- The source label carried by the source-label wires. -/
def srcLab (y : Cfg (Fin (k + 1))) : Bool × (Fin k → Bool) := (y 0, fun i => y i.succ)

/-- The ideal of a loading circuit: `J s` on the system for the source label
`s` on the source-label wires. -/
def loadIdeal (Jl : Bool × (Fin k → Bool) → Reg S ℂ →L[ℂ] Reg S ℂ) :
    Reg (Fin (k + 1) ⊕ S) ℂ →L[ℂ] Reg (Fin (k + 1) ⊕ S) ℂ :=
  localOp (Sum.inr : S → Fin (k + 1) ⊕ S) Sum.inr_injective
    (fun y => Jl (srcLab (fun i => y (Sum.inl i))))

theorem loadIdeal_isUnitary (Jl : Bool × (Fin k → Bool) → Reg S ℂ →L[ℂ] Reg S ℂ)
    (hJ : ∀ s, IsUnitary (Jl s)) : IsUnitary (loadIdeal Jl) :=
  localOp_isUnitary _ _ (fun _ => hJ _)

theorem loadIdeal_adjoint (Jl : Bool × (Fin k → Bool) → Reg S ℂ →L[ℂ] Reg S ℂ) :
    (loadIdeal Jl)† = loadIdeal (fun s => (Jl s)†) := by
  unfold loadIdeal
  rw [localOp_adjoint]

/-- The released coherent loading, flattened and lifted, is the placed ideal
of a loading circuit. -/
theorem liftB_conj_load (e : (Fin (k + 1) ⊕ S) ⊕ Zs ↪ HWO a m r K k l f S Zs nP Z bT bP A)
    (he1 : ∀ i, e (Sum.inl (Sum.inl i)) = Sum.inl (Sum.inl (srcTS i)))
    (he2 : ∀ s, e (Sum.inl (Sum.inr s)) = Sum.inl (Sum.inr s))
    (Jl : Bool × (Fin k → Bool) → Reg S ℂ →L[ℂ] Reg S ℂ) :
    liftB (X := XW Z bT bP A ⊕ OX Zs nP)
      (conj (psel (fun x => Jl (labAt x).1) :
        Reg (AW a m r K k l f) (Reg S ℂ) →L[ℂ] Reg (AW a m r K k l f) (Reg S ℂ))) =
      localOp e e.injective (fun _ => liftB (loadIdeal Jl)) := by
  rw [conj_psel]
  unfold liftB loadIdeal
  rw [GateODE.localOp_localOp' Sum.inl_injective Sum.inr_injective
      (fun s => (Sum.inl (Sum.inr s) : HWO a m r K k l f S Zs nP Z bT bP A))
      (fun _ _ h => Sum.inr_injective (Sum.inl_injective h)) (fun _ => rfl),
    GateODE.localOp_localOp e.injective Sum.inl_injective,
    GateODE.localOp_localOp' (e.injective.comp Sum.inl_injective) Sum.inr_injective
      (fun s => (Sum.inl (Sum.inr s) : HWO a m r K k l f S Zs nP Z bT bP A))
      (fun _ _ h => Sum.inr_injective (Sum.inl_injective h)) (fun s => (he2 s).symm)]
  apply localOp_congr
  intro z
  set z' := clearCfg (fun s => (Sum.inl (Sum.inr s) : HWO a m r K k l f S Zs nP Z bT bP A)) z
  have h1 : ∀ w : AW a m r K k l f, clearCfg (Sum.inr : S → AW a m r K k l f ⊕ S)
      (fun v => z' (Sum.inl v)) (Sum.inl w) = z' (Sum.inl (Sum.inl w)) :=
    fun w => clearCfg_apply_out _ _ _ (fun s h => by cases h)
  have h2 : ∀ i : Fin (k + 1), clearCfg (Sum.inr : S → Fin (k + 1) ⊕ S)
      (fun t => z' (e (Sum.inl t))) (Sum.inl i) = z' (Sum.inl (Sum.inl (srcTS i))) := by
    intro i
    rw [clearCfg_apply_out _ _ _ (fun s h => by cases h)]
    exact congrArg z' (he1 i)
  simp only [Function.comp_apply, h1, h2]
  rfl

/-- The released weight preparation, flattened and lifted, is the placed
matrix of a weight-preparation circuit. -/
theorem liftB_conj_wprep (e : Fin (k + 1) ⊕ Zs ↪ HWO a m r K k l f S Zs nP Z bT bP A)
    (he : ∀ i, e (Sum.inl i) = Sum.inl (Sum.inl (srcTS i)))
    (M : Matrix (Cfg (Fin (k + 1))) (Cfg (Fin (k + 1))) ℂ) :
    liftB (X := XW Z bT bP A ⊕ OX Zs nP)
      (conj (localOp srcTS srcTS_injective (fun _ => matOp M) :
        Reg (AW a m r K k l f) (Reg S ℂ) →L[ℂ] Reg (AW a m r K k l f) (Reg S ℂ))) =
      localOp e e.injective (fun _ => liftB (matOp M)) := by
  have hinj1 : Function.Injective
      (fun i : Fin (k + 1) => (Sum.inl (srcTS i) : AW a m r K k l f ⊕ S)) :=
    fun _ _ h => srcTS_injective (Sum.inl_injective h)
  have hinj2 : Function.Injective
      (fun i : Fin (k + 1) =>
        (Sum.inl (Sum.inl (srcTS i)) : HWO a m r K k l f S Zs nP Z bT bP A)) :=
    fun _ _ h => srcTS_injective (Sum.inl_injective (Sum.inl_injective h))
  rw [conj_localOp srcTS_injective, conj_matOp]
  unfold liftB
  rw [GateODE.localOp_localOp' (mapId_injective srcTS_injective) Sum.inl_injective _ hinj1
      (fun _ => rfl),
    GateODE.localOp_localOp' Sum.inl_injective hinj1 _ hinj2 (fun _ => rfl),
    GateODE.localOp_localOp' e.injective Sum.inl_injective _ hinj2 (fun i => (he i).symm)]

end Source

/-! ### The native preparation -/

section Prep

variable {S Zs Z Y J : Type*} [Fintype S] [DecidableEq S] [Fintype Zs] [DecidableEq Zs]
  [Fintype Z] [DecidableEq Z] [Fintype Y] [DecidableEq Y]

/-- The size of the native pool of the time-dependent solver. -/
abbrev tnPool (p : TParams) (S Zs Z : Type*) [Fintype S] [Fintype Zs] [Fintype Z]
    (bT bP A : ℕ) : ℕ :=
  Fintype.card p.W + Fintype.card (XW Z bT bP A) + Fintype.card Zs + Fintype.card S

/-- The native register of the time-dependent solver. -/
abbrev TNW (p : TParams) (S Zs Z : Type*) [Fintype S] [Fintype Zs] [Fintype Z] (bT bP A : ℕ) :=
  HWO p.a p.m p.r p.K p.m p.l p.f S Zs (tnPool p S Zs Z bT bP A) Z bT bP A

/-- The native source macros of the time-dependent solver: the loading
circuit (`src false`) and the weight-preparation circuit (`src true`), or
their literal inverses, placed on the source-label wires, the system and the
source scratch. -/
def tsrcMacro (p : TParams) {bT bP A : ℕ} (loadC : List (NInstr ((Fin (p.m + 1) ⊕ S) ⊕ Zs) Y J))
    (wpC : List (NInstr (Fin (p.m + 1) ⊕ Zs) Y J)) :
    Bool → Bool → List (NInstr (TNW p S Zs Z bT bP A) Y J)
  | false, false => loadC.map (NInstr.map loadPl)
  | false, true => (ninv loadC).map (NInstr.map loadPl)
  | true, false => wpC.map (NInstr.map wpPl)
  | true, true => (ninv wpC).map (NInstr.map wpPl)

/-- **The native preparation circuit** of the time-dependent solver.  It
depends only on the public data: `p`, the gates of `U_J`, the compute circuit,
orientation wire and decoder of the private operation, the arithmetic, the
loading circuit and the weight-preparation circuit. -/
def tnprepC (p : TParams) (UJg : List (Gate (Fin p.a ⊕ S)))
    (nd : NativeOp (TSel p.m p.l p.m) (Fin p.a ⊕ S) Z Y J)
    (ar : Arith (NB (TSel p.m p.l p.m) (Fin p.a ⊕ S) Z))
    (loadC : List (NInstr ((Fin (p.m + 1) ⊕ S) ⊕ Zs) Y J))
    (wpC : List (NInstr (Fin (p.m + 1) ⊕ Zs) Y J)) :
    List (NInstr (TNW p S Zs Z ar.bT ar.bP ar.A) Y J) :=
  p.prepC.flatMap (omacro tlabSel UJg nd ar (tsrcMacro p loadC wpC))

theorem osec_tprepC (p : TParams) : ∀ i ∈ p.prepC, OSecOK i := by
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
    simp only [TParams.select, List.mem_map] at hi
    obtain ⟨j, hj, rfl⟩ := hi
    have h : SecOK (wireRel p.a p.m p.r p.K) j := by
      unfold SlotSim.simCircuitT at hj
      exact secOK_ampI _ _ _ _ _ _ j hj
    cases j with
    | gate g => trivial
    | uj cs adj => exact h
    | priv cs adj => exact h
  intro i hi
  simp only [TParams.prepC, List.mem_append] at hi
  rcases hi with ((((h | h) | h) | h) | ((h | h) | h))
  · simp only [TParams.wprepC, List.mem_singleton] at h
    subst h
    trivial
  · exact hg _ i h
  · simp only [TParams.load, List.mem_singleton] at h
    subst h
    trivial
  · exact hsel i h
  · exact hg _ i h
  · exact hgi _ i h
  · simp only [GateODE.invList, TParams.wprepC, List.mem_reverse, List.mem_map,
      List.mem_singleton] at h
    obtain ⟨_, rfl, rfl⟩ := h
    trivial

theorem noseed_tprepC (p : TParams) (hp : p.PublicOK) : ∀ i ∈ p.prepC, i.isSeed = false := by
  have h := (p.prepC_counts hp.tau_pos.le hp.nu_pos hp.mesh).2.2.2.2.1
  intro i hi
  by_contra hs
  have hs' : i.isSeed = true := by simpa using hs
  have : 0 < GateODE.nSeed p.prepC := List.countP_pos_iff.mpr ⟨i, hi, hs'⟩
  omega

theorem prodOps_teval {a m r K k l f : ℕ} {P : Type*} [NormedAddCommGroup P]
    [InnerProductSpace ℂ P] [CompleteSpace P] (v : P) (σ : TOracles a k l P)
    (gs : List (OInstr (Wire a m r K) (OWire k l f))) :
    prodOps (teval v σ) gs = trun v σ gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih => rw [prodOps, GateODE.Time.trun_cons, ih]

/-- The native source macros approximate the released loading and weight
preparation. -/
theorem tsrcMacro_approx (p : TParams) {bT bP A : ℕ} (prim : J → Reg Y ℂ →L[ℂ] Reg Y ℂ)
    (hprim : ∀ j, IsUnitary (prim j))
    (loadC : List (NInstr ((Fin (p.m + 1) ⊕ S) ⊕ Zs) Y J)) (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (p.m + 1) ⊕ Zs) Y J)) (hwpV : ∀ i ∈ wpC, i.Valid)
    (v : Reg S ℂ) (σ : TOracles p.a p.m p.l (Reg S ℂ)) (hσ : σ.Unitary p.m) {ζs : ℝ}
    (hζs : 0 ≤ ζs)
    (hload : ApproxOn CleanX (nrun prim loadC) (liftB (loadIdeal σ.J)) ζs)
    (hwp : ApproxOn CleanX (nrun prim wpC) (liftB (matOp σ.Wp)) ζs) (c adj : Bool) :
    ApproxOn CleanX
      (nrun prim (tsrcMacro (Z := Z) (bT := bT) (bP := bP) (A := A) p loadC wpC c adj))
      (liftB (conj (teval (m := p.m) (r := p.r) (K := p.K) (f := p.f) v σ (.src c adj)))) ζs := by
  cases c
  · -- the coherent loading
    have hS : ∀ y : Cfg (TNW p S Zs Z bT bP A), CleanX y →
        CleanX (fun c => y ((loadPl (a := p.a) (m := p.m) (r := p.r) (K := p.K) (k := p.m)
          (l := p.l) (f := p.f) (S := S) (Zs := Zs) (nP := tnPool p S Zs Z bT bP A) (Z := Z)
          (bT := bT) (bP := bP) (A := A)) c)) :=
      fun y hy z => hy (Sum.inr (Sum.inl z))
    have hCU : IsUnitary (nrun prim loadC) := nrun_isUnitary prim hprim _ hloadV
    have hIU : IsUnitary (liftB (X := Zs) (loadIdeal σ.J)) :=
      liftB_isUnitary (loadIdeal_isUnitary _ hσ.load)
    rw [GateODE.Time.teval_load, liftB_conj_load loadPl (fun _ => rfl) (fun _ => rfl)
      (fun s => adjIf adj (σ.J s))]
    cases adj
    · simp only [tsrcMacro]
      rw [nrun_map]
      apply approxOn_localOp _ _ _ hζs hS
      intro _
      exact hload
    · simp only [tsrcMacro]
      rw [nrun_map]
      apply approxOn_localOp _ _ _ hζs hS
      intro _
      show ApproxOn CleanX (nrun prim (ninv loadC)) (liftB (loadIdeal (fun s => (σ.J s)†))) ζs
      rw [nrun_ninv, ← loadIdeal_adjoint, liftB_adjoint]
      exact hload.adjoint hCU hIU (by rw [← liftB_adjoint]; exact preserves_liftB _)
  · -- the weight preparation
    have hS : ∀ y : Cfg (TNW p S Zs Z bT bP A), CleanX y →
        CleanX (fun c => y ((wpPl (a := p.a) (m := p.m) (r := p.r) (K := p.K) (k := p.m)
          (l := p.l) (f := p.f) (S := S) (Zs := Zs) (nP := tnPool p S Zs Z bT bP A) (Z := Z)
          (bT := bT) (bP := bP) (A := A)) c)) :=
      fun y hy z => hy (Sum.inr (Sum.inl z))
    have hCU : IsUnitary (nrun prim wpC) := nrun_isUnitary prim hprim _ hwpV
    have hIU : IsUnitary (liftB (X := Zs) (matOp (Q := ℂ) σ.Wp)) :=
      liftB_isUnitary (matOp_isUnitary _ hσ.prep_left hσ.prep_right)
    rw [GateODE.Time.teval_wprep, GateODE.Time.wprep, liftB_conj_wprep wpPl (fun _ => rfl)]
    cases adj
    · simp only [tsrcMacro]
      rw [nrun_map]
      apply approxOn_localOp _ _ _ hζs hS
      intro _
      exact hwp
    · simp only [tsrcMacro]
      rw [nrun_map]
      apply approxOn_localOp _ _ _ hζs hS
      intro _
      show ApproxOn CleanX (nrun prim (ninv wpC)) (liftB (matOp σ.Wp.conjTranspose)) ζs
      rw [nrun_ninv, ← matOp_adjoint, liftB_adjoint]
      exact hwp.adjoint hCU hIU (by rw [← liftB_adjoint]; exact preserves_liftB _)

omit [DecidableEq S] [DecidableEq Zs] [DecidableEq Z] [Fintype Y] [DecidableEq Y] in
theorem tsrcMacro_not_touches (p : TParams) {bT bP A : ℕ}
    (loadC : List (NInstr ((Fin (p.m + 1) ⊕ S) ⊕ Zs) Y J))
    (wpC : List (NInstr (Fin (p.m + 1) ⊕ Zs) Y J)) (c adj : Bool) :
    ∀ i ∈ tsrcMacro (Z := Z) (bT := bT) (bP := bP) (A := A) p loadC wpC c adj,
      ¬ i.Touches reflWire := by
  have hl : ∀ v, ¬ reflWire ((loadPl : (Fin (p.m + 1) ⊕ S) ⊕ Zs ↪ TNW p S Zs Z bT bP A) v) := by
    intro v
    rcases v with (j | s) | z <;> exact fun h => h
  have hw : ∀ v, ¬ reflWire ((wpPl : Fin (p.m + 1) ⊕ Zs ↪ TNW p S Zs Z bT bP A) v) := by
    intro v
    rcases v with j | z <;> exact fun h => h
  intro i hi
  cases c <;> cases adj <;> simp only [tsrcMacro, List.mem_map] at hi <;>
    obtain ⟨i', _, rfl⟩ := hi
  · exact NInstr.not_touches_map _ _ hl i'
  · exact NInstr.not_touches_map _ _ hl i'
  · exact NInstr.not_touches_map _ _ hw i'
  · exact NInstr.not_touches_map _ _ hw i'

omit [DecidableEq S] [DecidableEq Zs] [DecidableEq Z] [Fintype Y] [DecidableEq Y] in
theorem tsrcMacro_valid (p : TParams) {bT bP A : ℕ}
    (loadC : List (NInstr ((Fin (p.m + 1) ⊕ S) ⊕ Zs) Y J)) (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (p.m + 1) ⊕ Zs) Y J)) (hwpV : ∀ i ∈ wpC, i.Valid) (c adj : Bool) :
    ∀ i ∈ tsrcMacro (Z := Z) (bT := bT) (bP := bP) (A := A) p loadC wpC c adj, i.Valid := by
  cases c <;> cases adj <;> simp only [tsrcMacro] <;> apply valid_map_list
  · exact hloadV
  · exact valid_ninv _ hloadV
  · exact hwpV
  · exact valid_ninv _ hwpV

omit [DecidableEq S] [DecidableEq Zs] [DecidableEq Z] [Fintype Y] [DecidableEq Y] in
theorem tsrcMacro_counts (p : TParams) {bT bP A : ℕ}
    (loadC : List (NInstr ((Fin (p.m + 1) ⊕ S) ⊕ Zs) Y J))
    (wpC : List (NInstr (Fin (p.m + 1) ⊕ Zs) Y J)) (c adj : Bool) (q : J → Bool) :
    nGatesN (tsrcMacro (Z := Z) (bT := bT) (bP := bP) (A := A) p loadC wpC c adj) =
      cond c (nGatesN wpC) (nGatesN loadC) ∧
    nCallsN q (tsrcMacro (Z := Z) (bT := bT) (bP := bP) (A := A) p loadC wpC c adj) =
      cond c (nCallsN q wpC) (nCallsN q loadC) := by
  cases c <;> cases adj <;>
    simp only [tsrcMacro, cond_false, cond_true, nGatesN_map, nCallsN_map, nGatesN_ninv,
      nCallsN_ninv, and_self]

omit [DecidableEq Zs] [Fintype Y] [DecidableEq Y] in
/-- Every instruction of the native time-dependent preparation is valid. -/
theorem tnprepC_valid (p : TParams) (hp : p.PublicOK) (UJg : List (Gate (Fin p.a ⊕ S)))
    (hUJg : ∀ g ∈ UJg, GateOK 3 g) (nd : NativeOp (TSel p.m p.l p.m) (Fin p.a ⊕ S) Z Y J)
    (hnd : nd.Public) (ar : Arith (NB (TSel p.m p.l p.m) (Fin p.a ⊕ S) Z)) {ζ : ℝ}
    (har : ArithOK ar (Sum.inl (Sum.inr nd.o)) nd.dec ζ)
    (loadC : List (NInstr ((Fin (p.m + 1) ⊕ S) ⊕ Zs) Y J)) (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (p.m + 1) ⊕ Zs) Y J)) (hwpV : ∀ i ∈ wpC, i.Valid) :
    ∀ i ∈ tnprepC p UJg nd ar loadC wpC, i.Valid := by
  have hvalid := p.prepC_valid hp.tau_pos.le hp.nu_pos hp.mesh
  have hsec := osec_tprepC p
  intro i hi
  simp only [tnprepC, List.mem_flatMap] at hi
  obtain ⟨o, ho, hi⟩ := hi
  exact omacro_valid tlabSel UJg hUJg nd hnd ar har.elem har.classical (tsrcMacro p loadC wpC)
    (tsrcMacro_valid p loadC hloadV wpC hwpV) o (hsec o ho) (hvalid o ho) i hi

/-- The native time-dependent preparation never changes the native flag and
pool. -/
theorem tnprepC_pres (p : TParams) (UJg : List (Gate (Fin p.a ⊕ S)))
    (nd : NativeOp (TSel p.m p.l p.m) (Fin p.a ⊕ S) Z Y J)
    (ar : Arith (NB (TSel p.m p.l p.m) (Fin p.a ⊕ S) Z))
    (loadC : List (NInstr ((Fin (p.m + 1) ⊕ S) ⊕ Zs) Y J))
    (wpC : List (NInstr (Fin (p.m + 1) ⊕ Zs) Y J)) (prim : J → Reg Y ℂ →L[ℂ] Reg Y ℂ) :
    Pres2 (ZeroOn reflWire) (nrun prim (tnprepC p UJg nd ar loadC wpC)) := by
  apply pres2_nrun_zeroOn
  intro i hi
  simp only [tnprepC, List.mem_flatMap] at hi
  obtain ⟨o, _, hi⟩ := hi
  exact omacro_not_touches tlabSel UJg nd ar (tsrcMacro p loadC wpC)
    (tsrcMacro_not_touches p loadC wpC) o i hi

end Prep

/-! ### The main theorem -/

section Main

variable {S Zs Z Y J : Type*} [Fintype S] [DecidableEq S] [Fintype Zs] [DecidableEq Zs]
  [Fintype Z] [DecidableEq Z] [Fintype Y] [DecidableEq Y]

/-- **The guarantees for one instance** of the native time-dependent solver. -/
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
    (hbudget : 24 * (p.d : ℝ) * ζ + 3 * ζs ≤ p.nu)
    (Hs Ls : ℕ → Reg S ℂ →L[ℂ] Reg S ℂ) (G : ℝ → Reg S ℂ →L[ℂ] Reg S ℂ) (b x : ℝ → Reg S ℂ)
    (bs : ℕ → Reg S ℂ) (βG δG βb δb bmax : ℝ)
    (hI : p.InstanceOK (seedV (S := S)) σ Hs Ls G b x bs βG δG βb δb bmax) :
    NOutcome (tnprepC p UJg nd ar loadC wpC) p.ratio p.ε (p.ratio_ge hp.g_ge) prim (x p.T) := by
  obtain ⟨cP, -, cSF, cST, -, -⟩ := p.prepC_counts hp.tau_pos.le hp.nu_pos hp.mesh
  have hvalid := p.prepC_valid hp.tau_pos.le hp.nu_pos hp.mesh
  have hprepV := tnprepC_valid p hp UJg hUJg nd hnd ar har loadC hloadV wpC hwpV
  have hU := p.unitary_of hI
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
  -- the released certificate of the discretised target
  have hC := p.prep_certificate hp (seedV (S := S)) norm_seedV σ Hs Ls G b x bs βG δG βb δb bmax hI
  obtain ⟨hy, hbud, hdirY⟩ := p.target_facts hp hI
  have hNorm := p.target_norm_le hp.T_pos.le Hs Ls hI.select.selfH hI.psd (x 0) bs
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
  generalize p.target Hs Ls (x 0) bs = y at h hy hbud hdirY hNorm
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

/-- **Native gate-efficient dissipative ODE solver, time-dependent
coefficients** (Theorem `ode:thm:gates`, time-dependent part, before
finite-set synthesis).

The native protocol `nprotocol (tnprepC p UJg nd ar loadC wpC) (2g)` depends
only on the public data.  Its trial circuits consist of valid elementary
gates and primitive calls; one preparation uses at most
`prepGates + 84 d C_J + 6 d G_C + |loadC| + 2 |wpC|` elementary gates (with
`G_C` the gates of one native private call) and at most
`12 d · calls(V) + calls(loadC) + 2 calls(wpC)` primitive calls of every
kind; in every history the protocol uses at most `80 g` times these per
preparation, plus `40 g (4 n + 3)` gates for the zero tests, where `n`
counts every wire except the native flag and pool (the system qubits
included).  For every instance with primitive
oracles `prim`, label- and slot-selected private Cayley operations `D z r`
given natively by `V` (`NativeOK`), a loading `J s` and a weight preparation
`Wp` approximated by the supplied circuits within `ζs`, the released
instance conditions for `(U_J, D, J, Wp)` and the error budget
`24 d ζ + 3 ζs ≤ ν`, the protocol succeeds with probability at least `2/3`,
and its conditional output is within trace distance `ε` of `x(T)/‖x(T)‖`. -/
theorem native_ode_time_solver (p : TParams) (hp : p.PublicOK)
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
      (Hs Ls : ℕ → Reg S ℂ →L[ℂ] Reg S ℂ) (G : ℝ → Reg S ℂ →L[ℂ] Reg S ℂ) (b x : ℝ → Reg S ℂ)
      (bs : ℕ → Reg S ℂ) (βG δG βb δb bmax ζs : ℝ),
      (∀ j, IsUnitary (prim j)) →
      NativeOK prim nd (selOp (tlabFam (P := Reg S ℂ) D false)) →
      0 ≤ ζs →
      ApproxOn CleanX (nrun prim loadC) (liftB (loadIdeal Jl)) ζs →
      ApproxOn CleanX (nrun prim wpC) (liftB (matOp Wp)) ζs →
      24 * (p.d : ℝ) * ζ + 3 * ζs ≤ p.nu →
      p.InstanceOK (seedV (S := S))
        (⟨UJop (R := ℂ) UJg, D, Jl, Wp⟩ : TOracles p.a p.m p.l (Reg S ℂ))
        Hs Ls G b x bs βG δG βb δb bmax →
      NOutcome (tnprepC p UJg nd ar loadC wpC) p.ratio p.ε (p.ratio_ge hp.g_ge) prim (x p.T) := by
  obtain ⟨cP, cU, cSF, cST, -, cG⟩ := p.prepC_counts hp.tau_pos.le hp.nu_pos hp.mesh
  have hprepV := tnprepC_valid p hp UJg hUJg nd hnd ar har loadC hloadV wpC hwpV
  refine ⟨fun j => trialN_valid _ hprepV j, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- gates of one preparation
    rw [tnprepC, nGatesN_flatMap]
    refine (sum_le_ocounts _ _ 1 (7 * UJg.length) (privGates nd ar)
      (fun c => cond c (nGatesN wpC) (nGatesN loadC))
      (fun i _ => omacro_nGates tlabSel UJg hUJg nd ar (tsrcMacro p loadC wpC)
        (fun c => cond c (nGatesN wpC) (nGatesN loadC))
        (fun c adj => (tsrcMacro_counts p loadC wpC c adj (fun _ => true)).1.le) i)).trans ?_
    rw [cP, cU, cSF, cST]
    simp only [cond_false, cond_true]
    have := cG
    nlinarith
  · -- calls of one preparation
    intro q
    rw [tnprepC, nCallsN_flatMap]
    refine (sum_le_ocounts _ _ 0 0 (2 * nCallsN q nd.V)
      (fun c => cond c (nCallsN q wpC) (nCallsN q loadC))
      (fun i _ => omacro_nCalls q tlabSel UJg nd ar (tsrcMacro p loadC wpC)
        (fun c => cond c (nCallsN q wpC) (nCallsN q loadC))
        (fun c adj => (tsrcMacro_counts p loadC wpC c adj q).2) i)).trans ?_
    rw [cP, cSF, cST]
    simp only [cond_false, cond_true]
    calc _ = 12 * p.d * nCallsN q nd.V + nCallsN q loadC + 2 * nCallsN q wpC := by ring
      _ ≤ _ := le_rfl
  · exact (nprotocol_worst _ p.ratio (p.ratio_ge hp.g_ge) (fun _ => true)).1
  · intro q
    exact (nprotocol_worst _ p.ratio (p.ratio_ge hp.g_ge) q).2
  · rw [card_HW]
    simp only [OX, Fintype.card_sum, Fintype.card_unit, Fintype.card_fin, tnPool, XW, AWr]
    ring
  · intro prim D Jl Wp Hs Ls G b x bs βG δG βb δb bmax ζs hprim hN hζs hload hwp hbudget hI
    exact native_time_outcome p hp UJg hUJg nd hnd ar ζ hζ har loadC hloadV wpC hwpV prim hprim
      ⟨UJop (R := ℂ) UJg, D, Jl, Wp⟩ rfl hN ζs hζs hload hwp hbudget Hs Ls G b x bs βG δG βb δb
      bmax hI

end Main

end

end SparseHamiltonian.GateNative
