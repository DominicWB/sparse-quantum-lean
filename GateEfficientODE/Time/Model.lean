import GateEfficientTimeDependent.SlotError
import GateEfficientODE.Circuit.Reflect

/-!
# The instruction model of the time-dependent gate-level solver

The register and the instruction syntax are those of the constant-coefficient
solver (`OInstr` on the simulator wires `Wire a m r K` and the solver wires
`OWire k l f`).  The time-dependent semantics `teval` reads the supplied
unitaries `TOracles` as follows.

* `gate`, `uj` and `seed` act as before.
* `priv cs adj` is the label- and slot-selected private Cayley call: on every
  configuration whose solver wires carry the joint label `z` and whose slot
  wires carry slot `j`, it applies `D z j` (or its adjoint) to the ancilla
  slice under the literal controls.  One call is counted once.
* `src false adj` is the coherent source loading: on every configuration
  whose source wires carry the source label `s`, it applies `J s` (or its
  inverse) to the payload.  One call is counted once.
* `src true adj` is the supplied weight preparation: the unitary matrix `Wp`
  (or its adjoint) on the source-label wires `ini, src 0, …, src (k-1)`.

The embedded simulator acts, on every configuration of the solver wires, as
the slot-selected simulator of the selected label (`trun_map_embI`).  Lists of
gates and seed reflections run exactly as in the constant-coefficient model
(`trun_eq_run`), so the zero-test and seed reflections are inherited.
`ttoProgram` reads a circuit as a released multi-oracle program whose labels
are its instructions.
-/

namespace SparseHamiltonian.GateODE.Time

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit
open GateCircuit.Sim (Wire anc_injective Vsp)
open scoped InnerProduct BigOperators

/-! ### Configuration-selected payload operators -/

section Payload

variable {W : Type*} [Fintype W] [DecidableEq W]
variable {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] [CompleteSpace Q]

/-- The payload operator `F x` on every configuration `x`. -/
def psel (F : Cfg W → Q →L[ℂ] Q) : Reg W Q →L[ℂ] Reg W Q :=
  ofCoords (fun x => F x ∘L coord x)

omit [Fintype W] [DecidableEq W] [CompleteSpace Q] in
theorem psel_apply (F : Cfg W → Q →L[ℂ] Q) (ψ : Reg W Q) (x : Cfg W) :
    psel F ψ x = F x (ψ x) := rfl

omit [DecidableEq W] [CompleteSpace Q] in
theorem psel_bas (F : Cfg W → Q →L[ℂ] Q) (x : Cfg W) (q : Q) :
    psel F (bas x q) = bas x (F x q) := by
  apply PiLp.ext
  intro y
  rw [psel_apply]
  by_cases hy : y = x
  · subst hy; simp
  · simp [hy]

omit [Fintype W] [DecidableEq W] [CompleteSpace Q] in
theorem psel_comp (F G : Cfg W → Q →L[ℂ] Q) :
    psel F ∘L psel G = psel (fun x => F x ∘L G x) := by
  ext ψ x
  rfl

omit [Fintype W] [DecidableEq W] [CompleteSpace Q] in
theorem psel_one : psel (W := W) (fun _ => (1 : Q →L[ℂ] Q)) = 1 := by
  ext ψ x
  rfl

theorem psel_adjoint (F : Cfg W → Q →L[ℂ] Q) : (psel F)† = psel (fun x => (F x)†) := by
  apply ContinuousLinearMap.ext
  intro ψ
  apply ext_inner_right ℂ
  intro φ
  rw [adjoint_inner_left, PiLp.inner_apply, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro x _
  rw [psel_apply, psel_apply, adjoint_inner_left]

theorem psel_isUnitary (F : Cfg W → Q →L[ℂ] Q) (hF : ∀ x, IsUnitary (F x)) :
    IsUnitary (psel F) := by
  constructor
  · rw [star_eq_adjoint, psel_adjoint, mul_def, psel_comp]
    have h : (fun x => (F x)† ∘L F x) = fun _ => (1 : Q →L[ℂ] Q) := by
      funext x
      have := (hF x).1
      rwa [star_eq_adjoint, mul_def] at this
    rw [h, psel_one]
  · rw [star_eq_adjoint, psel_adjoint, mul_def, psel_comp]
    have h : (fun x => F x ∘L (F x)†) = fun _ => (1 : Q →L[ℂ] Q) := by
      funext x
      have := (hF x).2
      rwa [star_eq_adjoint, mul_def] at this
    rw [h, psel_one]

/-- A configuration-selected payload operator never changes a configuration. -/
theorem pres2_psel (S : Cfg W → Prop) (F : Cfg W → Q →L[ℂ] Q) : Pres2 S (psel F) := by
  constructor
  · intro ψ hψ x hx
    rw [psel_apply, hψ x hx, map_zero]
  · rw [psel_adjoint]
    intro ψ hψ x hx
    rw [psel_apply, hψ x hx, map_zero]

end Payload

/-! ### The supplied unitaries -/

/-- The supplied unitaries of the time-dependent solver: `U_J`, the private
Cayley operation `D z j` of every joint label `z` and slot `j`, the source
loading `J s` of every source label `s`, and the weight preparation `Wp` of
the source-label register. -/
structure TOracles (a k l : ℕ) (P : Type*) [NormedAddCommGroup P] [InnerProductSpace ℂ P] where
  UJ : Anc a P →L[ℂ] Anc a P
  D : Label k l → ℕ → Anc a P →L[ℂ] Anc a P
  J : Bool × (Fin k → Bool) → P →L[ℂ] P
  Wp : Matrix (Cfg (Fin (k + 1))) (Cfg (Fin (k + 1))) ℂ

variable {a m r K k l f : ℕ}
variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-- The joint label carried by the solver wires of a configuration. -/
abbrev labAt (x : Cfg (AW a m r K k l f)) : Label k l := labOf (fun o => x (Sum.inr o))

/-- The weight preparation (or its adjoint) on the source-label wires. -/
def wprep (σ : TOracles a k l P) (adj : Bool) :
    Reg (AW a m r K k l f) P →L[ℂ] Reg (AW a m r K k l f) P :=
  localOp srcTS srcTS_injective (fun _ => matOp (if adj then σ.Wp.conjTranspose else σ.Wp))

/-- The operator of one instruction in the time-dependent semantics. -/
def teval (v : P) (σ : TOracles a k l P) :
    OInstr (Wire a m r K) (OWire k l f) → Reg (AW a m r K k l f) P →L[ℂ] Reg (AW a m r K k l f) P
  | .gate g => gateOp g.cs g.t g.u
  | .uj cs adj => localOp Sum.inl Sum.inl_injective
      (fun _ => oracleOp Wire.anc anc_injective cs (adjIf adj σ.UJ))
  | .priv cs adj => localOp Sum.inl Sum.inl_injective
      (fun x => SlotSim.slotOracle cs (fun j => SlotSim.adjT adj (σ.D (labAt x) j)))
  | .src b adj => if b then wprep σ adj else psel (fun x => adjIf adj (σ.J (labAt x).1))
  | .seed cs => pctl cs (seedRefl v)

section EvalLemmas

variable (v : P) (σ : TOracles a k l P)

@[simp] theorem teval_gate (g : Gate (AW a m r K k l f)) :
    teval v σ (.gate g) = gateOp g.cs g.t g.u := rfl

@[simp] theorem teval_uj (cs : List (Wire a m r K × Bool)) (adj : Bool) :
    teval (f := f) v σ (.uj cs adj) = localOp Sum.inl Sum.inl_injective
      (fun _ => oracleOp Wire.anc anc_injective cs (adjIf adj σ.UJ)) := rfl

@[simp] theorem teval_priv (cs : List (Wire a m r K × Bool)) (adj : Bool) :
    teval (f := f) v σ (.priv cs adj) = localOp Sum.inl Sum.inl_injective
      (fun x => SlotSim.slotOracle cs (fun j => SlotSim.adjT adj (σ.D (labAt x) j))) := rfl

@[simp] theorem teval_load (adj : Bool) :
    teval (m := m) (r := r) (K := K) (f := f) v σ (.src false adj) =
      psel (fun x => adjIf adj (σ.J (labAt x).1)) := rfl

@[simp] theorem teval_wprep (adj : Bool) :
    teval (m := m) (r := r) (K := K) (f := f) v σ (.src true adj) = wprep σ adj := rfl

@[simp] theorem teval_seed (cs : List (AW a m r K k l f × Bool)) :
    teval v σ (.seed cs) = pctl cs (seedRefl v) := rfl

end EvalLemmas

theorem wprep_adjoint (σ : TOracles a k l P) (adj : Bool) :
    (wprep (m := m) (r := r) (K := K) (f := f) σ adj)† = wprep σ (!adj) := by
  unfold wprep
  rw [localOp_adjoint]
  congr 1
  funext x
  rw [matOp_adjoint]
  cases adj <;> simp

theorem teval_inv (v : P) (σ : TOracles a k l P) (g : OInstr (Wire a m r K) (OWire k l f)) :
    teval v σ g.inv = (teval v σ g)† := by
  cases g with
  | gate g => exact (gateOp_adjoint g.cs g.t g.u).symm
  | uj cs adj =>
      have e : (OInstr.uj cs adj : OInstr (Wire a m r K) (OWire k l f)).inv = .uj cs (!adj) := rfl
      rw [e, teval_uj, teval_uj, localOp_adjoint]
      congr 1
      funext x
      rw [oracleOp_adjoint, adjIf_adjoint]
  | priv cs adj =>
      have e : (OInstr.priv cs adj : OInstr (Wire a m r K) (OWire k l f)).inv =
          .priv cs (!adj) := rfl
      rw [e, teval_priv, teval_priv, localOp_adjoint]
      congr 1
      funext x
      rw [SlotSim.slotOracle_adjoint]
      congr 1
      funext j
      rw [SlotSim.adjT_adjoint]
  | src b adj =>
      have e : (OInstr.src b adj : OInstr (Wire a m r K) (OWire k l f)).inv = .src b (!adj) := rfl
      rw [e]
      cases b
      · rw [teval_load, teval_load, psel_adjoint]
        congr 1
        funext x
        rw [adjIf_adjoint]
      · rw [teval_wprep, teval_wprep, wprep_adjoint]
  | seed cs =>
      have e : (OInstr.seed cs : OInstr (Wire a m r K) (OWire k l f)).inv = .seed cs := rfl
      rw [e, teval_seed, pctl_adjoint, seedRefl_adjoint]

/-- The hypotheses making every supplied operation unitary. -/
structure TOracles.Unitary (σ : TOracles a k l P) (m : ℕ) : Prop where
  uj : IsUnitary σ.UJ
  priv : ∀ z, ∀ j < 2 ^ m, IsUnitary (σ.D z j)
  load : ∀ s, IsUnitary (σ.J s)
  prep_left : σ.Wp.conjTranspose * σ.Wp = 1
  prep_right : σ.Wp * σ.Wp.conjTranspose = 1

theorem wprep_isUnitary (σ : TOracles a k l P) (hσ : σ.Unitary m) (adj : Bool) :
    IsUnitary (wprep (m := m) (r := r) (K := K) (f := f) σ adj) := by
  apply localOp_isUnitary
  intro _
  cases adj
  · exact matOp_isUnitary _ hσ.prep_left hσ.prep_right
  · simp only [if_true]
    apply matOp_isUnitary
    · rw [Matrix.conjTranspose_conjTranspose]; exact hσ.prep_right
    · rw [Matrix.conjTranspose_conjTranspose]; exact hσ.prep_left

theorem teval_isUnitary (v : P) (σ : TOracles a k l P) (hσ : σ.Unitary m) (hv : ‖v‖ = 1)
    (g : OInstr (Wire a m r K) (OWire k l f)) (hg : g.Valid Wire.anc) :
    IsUnitary (teval v σ g) := by
  cases g with
  | gate g => exact gateOp_isUnitary g.cs g.t g.u hg.2.2
  | uj cs adj =>
      rw [teval_uj]
      exact localOp_isUnitary Sum.inl_injective _
        (fun _ => oracleOp_isUnitary Wire.anc anc_injective cs _ (adjIf_isUnitary adj σ.UJ hσ.uj))
  | priv cs adj =>
      rw [teval_priv]
      exact localOp_isUnitary Sum.inl_injective _ (fun x => SlotSim.slotOracle_isUnitary cs _
        (fun j hj => SlotSim.adjT_isUnitary adj _ (hσ.priv _ j hj)))
  | src b adj =>
      cases b
      · rw [teval_load]
        exact psel_isUnitary _ (fun x => adjIf_isUnitary adj _ (hσ.load _))
      · rw [teval_wprep]
        exact wprep_isUnitary σ hσ adj
  | seed cs =>
      rw [teval_seed]
      exact pctl_isUnitary _ _ (seedRefl_isUnitary _ hv)

/-! ### Circuits -/

/-- Run a circuit in the time-dependent semantics: the head instruction acts
first. -/
def trun (v : P) (σ : TOracles a k l P) :
    List (OInstr (Wire a m r K) (OWire k l f)) → Reg (AW a m r K k l f) P →L[ℂ] Reg (AW a m r K k l f) P
  | [] => 1
  | g :: gs => trun v σ gs ∘L teval v σ g

section Run

variable (v : P) (σ : TOracles a k l P)

@[simp] theorem trun_nil : trun v σ ([] : List (OInstr (Wire a m r K) (OWire k l f))) = 1 := rfl

theorem trun_cons (g : OInstr (Wire a m r K) (OWire k l f))
    (gs : List (OInstr (Wire a m r K) (OWire k l f))) :
    trun v σ (g :: gs) = trun v σ gs ∘L teval v σ g := rfl

theorem trun_append (gs hs : List (OInstr (Wire a m r K) (OWire k l f))) :
    trun v σ (gs ++ hs) = trun v σ hs ∘L trun v σ gs := by
  induction gs with
  | nil => ext ψ; rfl
  | cons g gs ih => simp only [List.cons_append, trun_cons, ih, comp_assoc]

theorem trun_singleton (g : OInstr (Wire a m r K) (OWire k l f)) :
    trun v σ [g] = teval v σ g := by
  ext ψ; rfl

theorem trun_invList (gs : List (OInstr (Wire a m r K) (OWire k l f))) :
    trun v σ (invList gs) = (trun v σ gs)† := by
  induction gs with
  | nil => simp [invList, trun]
  | cons g gs ih =>
      have h1 : invList (g :: gs) = invList gs ++ [g.inv] := by simp [invList]
      rw [h1, trun_append, ih, trun_singleton, teval_inv, trun_cons, adjoint_comp]

theorem trun_isUnitary (hσ : σ.Unitary m) (hv : ‖v‖ = 1)
    (gs : List (OInstr (Wire a m r K) (OWire k l f))) (hgs : ∀ g ∈ gs, g.Valid Wire.anc) :
    IsUnitary (trun v σ gs) := by
  induction gs with
  | nil => exact isUnitary_one
  | cons g gs ih =>
      rw [trun_cons, ← mul_def]
      exact (ih (fun h hh => hgs h (List.mem_cons_of_mem g hh))).mul
        (teval_isUnitary v σ hσ hv g (hgs g List.mem_cons_self))

theorem trun_ofGates (gs : List (Gate (AW a m r K k l f))) : trun v σ (ofGates gs) = gRun gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
      simp only [ofGates, List.map_cons] at ih ⊢
      rw [trun_cons, ih]
      rfl

/-- Lists of gates and seed reflections run as in the constant-coefficient
semantics. -/
theorem trun_eq_run (σ₁ : Oracles a (Label k l) P)
    (gs : List (OInstr (Wire a m r K) (OWire k l f)))
    (h : ∀ g ∈ gs, g.isGate = true ∨ g.isSeed = true) :
    trun v σ gs = run (wiring v) σ₁ gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
      rw [trun_cons, run_cons, ih (fun h' hh => h h' (List.mem_cons_of_mem g hh))]
      have hg := h g List.mem_cons_self
      cases g with
      | gate g => rfl
      | uj cs adj => simp [OInstr.isGate, OInstr.isSeed] at hg
      | priv cs adj => simp [OInstr.isGate, OInstr.isSeed] at hg
      | src b adj => simp [OInstr.isGate, OInstr.isSeed] at hg
      | seed cs => rfl

end Run

/-! ### The embedded slot-selected simulator -/

theorem teval_embI (v : P) (σ : TOracles a k l P) (i : Instr (Wire a m r K)) :
    teval (f := f) v σ (embI i) =
      localOp Sum.inl Sum.inl_injective (fun x => SlotSim.evalT σ.UJ (σ.D (labAt x)) i) := by
  cases i with
  | gate g => exact (Gate.map_op Sum.inl_injective g).symm
  | uj cs adj =>
      have e : embI (O := OWire k l f) (Instr.uj cs adj) = .uj cs adj := rfl
      rw [e, teval_uj]
      rfl
  | priv cs adj =>
      have e : embI (O := OWire k l f) (Instr.priv cs adj) = .priv cs adj := rfl
      rw [e, teval_priv]
      rfl

/-- The embedded simulator acts on every configuration of the solver wires as
the slot-selected simulator of the selected label. -/
theorem trun_map_embI (v : P) (σ : TOracles a k l P) (gs : List (Instr (Wire a m r K))) :
    trun v σ (gs.map (embI (O := OWire k l f))) =
      localOp Sum.inl Sum.inl_injective (fun x => SlotSim.runT σ.UJ (σ.D (labAt x)) gs) := by
  induction gs with
  | nil => exact (localOp_one Sum.inl_injective).symm
  | cons g gs ih =>
      rw [List.map_cons, trun_cons, ih, teval_embI, localOp_comp]
      rfl

/-! ### Circuits as released multi-oracle programs -/

/-- Every instruction is a named oracle of the released program model. -/
def tfamily (v : P) :
    OInstr (Wire a m r K) (OWire k l f) → TOracles a k l P →
      Reg (AW a m r K k l f) P →L[ℂ] Reg (AW a m r K k l f) P :=
  fun g σ => teval v σ g

/-- A circuit as a released multi-oracle program. -/
def ttoProgram (v : P) :
    List (OInstr (Wire a m r K) (OWire k l f)) →
      MultiOracleCircuit.Program (tfamily (a := a) (m := m) (r := r) (K := K) (k := k) (l := l)
        (f := f) v)
  | [] => .identity
  | g :: gs => .seq (ttoProgram v gs) (.query g)

theorem ttoProgram_eval (v : P) (σ : TOracles a k l P)
    (gs : List (OInstr (Wire a m r K) (OWire k l f))) :
    (ttoProgram v gs).eval σ = trun v σ gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
      rw [ttoProgram, MultiOracleCircuit.Program.eval_seq, ih,
        MultiOracleCircuit.Program.eval_query, trun_cons, mul_def]
      rfl

theorem ttoProgram_cost (v : P) (gs : List (OInstr (Wire a m r K) (OWire k l f)))
    (w : OInstr (Wire a m r K) (OWire k l f) → ℕ) :
    (ttoProgram v gs).cost w = (gs.map w).sum := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
      rw [ttoProgram, MultiOracleCircuit.Program.cost_seq, ih,
        MultiOracleCircuit.Program.cost_query, List.map_cons, List.sum_cons, add_comm]

end

end SparseHamiltonian.GateODE.Time
