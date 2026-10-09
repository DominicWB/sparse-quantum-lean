import GateEfficientODE.Model.Exposure
import SparseODE.ODEGroverActual

/-!
# The instruction model of the gate-level ODE solver

The register has the simulator wires `S` of the released gate-level
Hamiltonian simulator, the solver wires `O`, and the system payload `P`.
An instruction is one of

* an elementary gate on any wires (`gate`): a one-qubit unitary with at most
  three literal controls;
* a call of `U_J` or `U_J†` (`uj`), or of the label-selected private Cayley
  operation `D` or `D†` (`priv`), on the ancilla wires of the simulator and
  the payload, under literal controls on the simulator wires.  The private
  call applies `D z` on every configuration whose solver wires carry the
  label `z`; one such call is counted once (coherent selection);
* a controlled call of a supplied source interface or its inverse (`src`):
  `J false = J₀` on the initial sector `ini = 0`, `J true = J_b` on the
  forcing sector `ini = 1`;
* the public payload reflection about the seed vector (`seed`) under literal
  controls; it is counted separately.

A circuit is a list of instructions, executed left to right.  The released
simulator embeds via `embI` (`run_map_embI`): its operator is the direct sum,
over the configurations of the solver wires, of the released circuit
operators for the selected private operations.

`toProgram` reads a circuit as a released multi-oracle program whose labels
are the instructions, so weighted costs count gates and calls exactly.
-/

namespace SparseHamiltonian.GateODE

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit
open scoped InnerProduct BigOperators

/-- Instructions on simulator wires `S` and solver wires `O`. -/
inductive OInstr (S O : Type*)
  | gate (g : Gate (S ⊕ O))
  | uj (cs : List (S × Bool)) (adj : Bool)
  | priv (cs : List (S × Bool)) (adj : Bool)
  | src (b adj : Bool)
  | seed (cs : List ((S ⊕ O) × Bool))

/-- The public wiring: ancillas of the simulator, the source-sector wire,
the label read from the solver wires, and the public seed vector. -/
structure Wiring (S O : Type*) (a : ℕ) (Λ : Type*) (P : Type*) where
  anc : Fin a → S
  hanc : Function.Injective anc
  ini : O
  lab : Cfg O → Λ
  seedVec : P

/-- The supplied unitaries: `U_J`, the private Cayley operation of every
label, and the two source interfaces. -/
structure Oracles (a : ℕ) (Λ : Type*) (P : Type*) [NormedAddCommGroup P]
    [InnerProductSpace ℂ P] where
  UJ : Anc a P →L[ℂ] Anc a P
  D : Λ → Anc a P →L[ℂ] Anc a P
  J : Bool → P →L[ℂ] P

/-- `A` or its adjoint. -/
def adjIf {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (adj : Bool) (A : E →L[ℂ] E) : E →L[ℂ] E :=
  if adj then A† else A

theorem adjIf_adjoint {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (adj : Bool) (A : E →L[ℂ] E) : (adjIf adj A)† = adjIf (!adj) A := by
  cases adj <;> simp [adjIf]

theorem adjIf_isUnitary {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (adj : Bool) (A : E →L[ℂ] E) (hA : IsUnitary A) :
    IsUnitary (adjIf adj A) := by
  cases adj
  · exact hA
  · simpa [adjIf, star_eq_adjoint] using hA.adjoint

/-- The public reflection about the seed vector, `1 - 2 |v⟩⟨v|`. -/
def seedRefl {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
    (v : P) : P →L[ℂ] P :=
  PhaseSubspaceGates.phase (ODEGroverRay.projector v) (-1)

theorem projector_star {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P]
    [CompleteSpace P] (v : P) : star (ODEGroverRay.projector v) = ODEGroverRay.projector v := by
  rw [ODEGroverRay.projector, star_eq_adjoint, adjoint_comp, adjoint_adjoint]

theorem seedRefl_adjoint {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P]
    [CompleteSpace P] (v : P) : (seedRefl v)† = seedRefl v := by
  rw [← star_eq_adjoint, seedRefl, PhaseSubspaceGates.phase_adjoint _ (projector_star v)]
  simp

theorem seedRefl_isUnitary {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P]
    [CompleteSpace P] (v : P) (hv : ‖v‖ = 1) : IsUnitary (seedRefl v) :=
  PhaseSubspaceGates.phase_unitary _ (ODEGroverRay.projector_isOrthogonalProjection v hv) _
    (by simp)

variable {S O : Type*} [Fintype S] [DecidableEq S] [Fintype O] [DecidableEq O]
variable {a : ℕ} {Λ : Type*}
variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

namespace OInstr

/-- The simulator semantics selected by the solver-wire configuration of `x`. -/
def semAt (ω : Wiring S O a Λ P) (σ : Oracles a Λ P) (x : Cfg (S ⊕ O)) : Sem S a P :=
  ⟨ω.anc, ω.hanc, σ.UJ, σ.D (ω.lab (fun o => x (Sum.inr o)))⟩

/-- The operator of one instruction. -/
def eval (ω : Wiring S O a Λ P) (σ : Oracles a Λ P) :
    OInstr S O → Reg (S ⊕ O) P →L[ℂ] Reg (S ⊕ O) P
  | .gate g => gateOp g.cs g.t g.u
  | .uj cs adj => localOp Sum.inl Sum.inl_injective
      (fun _ => oracleOp ω.anc ω.hanc cs (adjIf adj σ.UJ))
  | .priv cs adj => localOp Sum.inl Sum.inl_injective
      (fun x => oracleOp ω.anc ω.hanc cs
        (adjIf adj (σ.D (ω.lab (fun o => x (Sum.inr o))))))
  | .src b adj => pctl [(Sum.inr ω.ini, b)] (adjIf adj (σ.J b))
  | .seed cs => pctl cs (seedRefl ω.seedVec)

section EvalLemmas

variable (ω : Wiring S O a Λ P) (σ : Oracles a Λ P)

@[simp] theorem eval_gate (g : Gate (S ⊕ O)) :
    (OInstr.gate g).eval ω σ = gateOp g.cs g.t g.u := rfl

@[simp] theorem eval_uj (cs : List (S × Bool)) (adj : Bool) :
    (OInstr.uj cs adj : OInstr S O).eval ω σ = localOp Sum.inl Sum.inl_injective
      (fun _ => oracleOp ω.anc ω.hanc cs (adjIf adj σ.UJ)) := rfl

@[simp] theorem eval_priv (cs : List (S × Bool)) (adj : Bool) :
    (OInstr.priv cs adj : OInstr S O).eval ω σ = localOp Sum.inl Sum.inl_injective
      (fun x => oracleOp ω.anc ω.hanc cs
        (adjIf adj (σ.D (ω.lab (fun o => x (Sum.inr o)))))) := rfl

@[simp] theorem eval_src (b adj : Bool) :
    (OInstr.src b adj : OInstr S O).eval ω σ =
      pctl [(Sum.inr ω.ini, b)] (adjIf adj (σ.J b)) := rfl

@[simp] theorem eval_seed (cs : List ((S ⊕ O) × Bool)) :
    (OInstr.seed cs : OInstr S O).eval ω σ = pctl cs (seedRefl ω.seedVec) := rfl

end EvalLemmas

/-- The inverse instruction. -/
def inv : OInstr S O → OInstr S O
  | .gate g => .gate ⟨g.cs, g.t, g.u.conjTranspose⟩
  | .uj cs adj => .uj cs (!adj)
  | .priv cs adj => .priv cs (!adj)
  | .src b adj => .src b (!adj)
  | .seed cs => .seed cs

def isGate : OInstr S O → Bool
  | .gate _ => true
  | _ => false

def isUJ : OInstr S O → Bool
  | .uj _ _ => true
  | _ => false

def isPriv : OInstr S O → Bool
  | .priv _ _ => true
  | _ => false

def isSrc (b : Bool) : OInstr S O → Bool
  | .src b' _ => b' == b
  | _ => false

def isSeed : OInstr S O → Bool
  | .seed _ => true
  | _ => false

omit [Fintype S] [DecidableEq S] [Fintype O] [DecidableEq O] in
@[simp] theorem isGate_inv (g : OInstr S O) : g.inv.isGate = g.isGate := by cases g <;> rfl
omit [Fintype S] [DecidableEq S] [Fintype O] [DecidableEq O] in
@[simp] theorem isUJ_inv (g : OInstr S O) : g.inv.isUJ = g.isUJ := by cases g <;> rfl
omit [Fintype S] [DecidableEq S] [Fintype O] [DecidableEq O] in
@[simp] theorem isPriv_inv (g : OInstr S O) : g.inv.isPriv = g.isPriv := by cases g <;> rfl
omit [Fintype S] [DecidableEq S] [Fintype O] [DecidableEq O] in
@[simp] theorem isSrc_inv (b : Bool) (g : OInstr S O) : g.inv.isSrc b = g.isSrc b := by
  cases g <;> rfl
omit [Fintype S] [DecidableEq S] [Fintype O] [DecidableEq O] in
@[simp] theorem isSeed_inv (g : OInstr S O) : g.inv.isSeed = g.isSeed := by cases g <;> rfl

/-- Elementary validity: gates have at most three controls off the target and
a unitary matrix; oracle calls have at most one control, off the ancillas;
seed reflections have at most one control. -/
def Valid (anc : Fin a → S) : OInstr S O → Prop
  | .gate g => g.cs.length ≤ 3 ∧ (∀ c ∈ g.cs, c.1 ≠ g.t) ∧ UnitaryMat g.u
  | .uj cs _ => cs.length ≤ 1 ∧ ∀ c ∈ cs, ∀ i, anc i ≠ c.1
  | .priv cs _ => cs.length ≤ 1 ∧ ∀ c ∈ cs, ∀ i, anc i ≠ c.1
  | .src _ _ => True
  | .seed cs => cs.length ≤ 1

omit [Fintype S] [DecidableEq S] [Fintype O] [DecidableEq O] in
theorem valid_inv (anc : Fin a → S) (g : OInstr S O) (h : g.Valid anc) : g.inv.Valid anc := by
  cases g with
  | gate g =>
      obtain ⟨h1, h2, h3, h4⟩ := h
      refine ⟨h1, h2, ?_⟩
      constructor
      · rw [Matrix.conjTranspose_conjTranspose]; exact h4
      · rw [Matrix.conjTranspose_conjTranspose]; exact h3
  | uj cs adj => exact h
  | priv cs adj => exact h
  | src b adj => exact h
  | seed cs => exact h

theorem eval_inv (ω : Wiring S O a Λ P) (σ : Oracles a Λ P) (g : OInstr S O) :
    g.inv.eval ω σ = (g.eval ω σ)† := by
  cases g with
  | gate g => exact (gateOp_adjoint g.cs g.t g.u).symm
  | uj cs adj =>
      have e : (OInstr.uj cs adj : OInstr S O).inv = .uj cs (!adj) := rfl
      rw [e, eval_uj, eval_uj, localOp_adjoint]
      congr 1
      funext x
      rw [oracleOp_adjoint, adjIf_adjoint]
  | priv cs adj =>
      have e : (OInstr.priv cs adj : OInstr S O).inv = .priv cs (!adj) := rfl
      rw [e, eval_priv, eval_priv, localOp_adjoint]
      congr 1
      funext x
      rw [oracleOp_adjoint, adjIf_adjoint]
  | src b adj =>
      have e : (OInstr.src b adj : OInstr S O).inv = .src b (!adj) := rfl
      rw [e, eval_src, eval_src, pctl_adjoint, adjIf_adjoint]
  | seed cs =>
      have e : (OInstr.seed cs : OInstr S O).inv = .seed cs := rfl
      rw [e, eval_seed, pctl_adjoint, seedRefl_adjoint]

/-- Unitary oracles, a unit seed and validity make every instruction unitary. -/
theorem eval_isUnitary (ω : Wiring S O a Λ P) (σ : Oracles a Λ P)
    (hUJ : IsUnitary σ.UJ) (hD : ∀ z, IsUnitary (σ.D z)) (hJ : ∀ b, IsUnitary (σ.J b))
    (hv : ‖ω.seedVec‖ = 1) (g : OInstr S O) (hg : g.Valid ω.anc) :
    IsUnitary (g.eval ω σ) := by
  cases g with
  | gate g => exact gateOp_isUnitary g.cs g.t g.u hg.2.2
  | uj cs adj =>
      rw [eval_uj]
      exact localOp_isUnitary Sum.inl_injective _
        (fun _ => oracleOp_isUnitary ω.anc ω.hanc cs _ (adjIf_isUnitary adj σ.UJ hUJ))
  | priv cs adj =>
      rw [eval_priv]
      exact localOp_isUnitary Sum.inl_injective _
        (fun _ => oracleOp_isUnitary ω.anc ω.hanc cs _ (adjIf_isUnitary adj _ (hD _)))
  | src b adj =>
      rw [eval_src]
      exact pctl_isUnitary _ _ (adjIf_isUnitary _ _ (hJ b))
  | seed cs =>
      rw [eval_seed]
      exact pctl_isUnitary _ _ (seedRefl_isUnitary _ hv)

end OInstr

/-! ### Circuits -/

/-- Run a circuit: the head instruction acts first. -/
def run (ω : Wiring S O a Λ P) (σ : Oracles a Λ P) :
    List (OInstr S O) → Reg (S ⊕ O) P →L[ℂ] Reg (S ⊕ O) P
  | [] => 1
  | g :: gs => run ω σ gs ∘L g.eval ω σ

section Run

variable (ω : Wiring S O a Λ P) (σ : Oracles a Λ P)

@[simp] theorem run_nil : run ω σ ([] : List (OInstr S O)) = 1 := rfl

theorem run_cons (g : OInstr S O) (gs : List (OInstr S O)) :
    run ω σ (g :: gs) = run ω σ gs ∘L g.eval ω σ := rfl

theorem run_append (gs hs : List (OInstr S O)) :
    run ω σ (gs ++ hs) = run ω σ hs ∘L run ω σ gs := by
  induction gs with
  | nil => ext ψ; rfl
  | cons g gs ih => simp only [List.cons_append, run_cons, ih, comp_assoc]

theorem run_singleton (g : OInstr S O) : run ω σ [g] = g.eval ω σ := by
  ext ψ; rfl

/-- The literal inverse circuit. -/
def invList (gs : List (OInstr S O)) : List (OInstr S O) := (gs.map OInstr.inv).reverse

theorem run_invList (gs : List (OInstr S O)) : run ω σ (invList gs) = (run ω σ gs)† := by
  induction gs with
  | nil => simp [invList, run]
  | cons g gs ih =>
      have h1 : invList (g :: gs) = invList gs ++ [g.inv] := by simp [invList]
      rw [h1, run_append, ih, run_singleton, OInstr.eval_inv, run_cons, adjoint_comp]

theorem run_isUnitary (hUJ : IsUnitary σ.UJ) (hD : ∀ z, IsUnitary (σ.D z))
    (hJ : ∀ b, IsUnitary (σ.J b)) (hv : ‖ω.seedVec‖ = 1) (gs : List (OInstr S O))
    (hgs : ∀ g ∈ gs, g.Valid ω.anc) : IsUnitary (run ω σ gs) := by
  induction gs with
  | nil => exact isUnitary_one
  | cons g gs ih =>
      rw [run_cons, ← mul_def]
      exact (ih (fun h hh => hgs h (List.mem_cons_of_mem g hh))).mul
        (OInstr.eval_isUnitary ω σ hUJ hD hJ hv g (hgs g List.mem_cons_self))

end Run

omit [Fintype S] [DecidableEq S] [Fintype O] [DecidableEq O] in
theorem valid_invList (anc : Fin a → S) (gs : List (OInstr S O))
    (h : ∀ g ∈ gs, g.Valid anc) : ∀ g ∈ invList gs, g.Valid anc := by
  intro g hg
  simp only [invList, List.mem_reverse, List.mem_map] at hg
  obtain ⟨g', hg', rfl⟩ := hg
  exact OInstr.valid_inv anc g' (h g' hg')

/-! ### Counting -/

section Count

def nGates (gs : List (OInstr S O)) : ℕ := gs.countP OInstr.isGate
def nUJ (gs : List (OInstr S O)) : ℕ := gs.countP OInstr.isUJ
def nPriv (gs : List (OInstr S O)) : ℕ := gs.countP OInstr.isPriv
def nSrc (b : Bool) (gs : List (OInstr S O)) : ℕ := gs.countP (OInstr.isSrc b)
def nSeed (gs : List (OInstr S O)) : ℕ := gs.countP OInstr.isSeed

omit [Fintype S] [DecidableEq S] [Fintype O] [DecidableEq O]

theorem nGates_append (gs hs : List (OInstr S O)) :
    nGates (gs ++ hs) = nGates gs + nGates hs := List.countP_append ..
theorem nUJ_append (gs hs : List (OInstr S O)) : nUJ (gs ++ hs) = nUJ gs + nUJ hs :=
  List.countP_append ..
theorem nPriv_append (gs hs : List (OInstr S O)) : nPriv (gs ++ hs) = nPriv gs + nPriv hs :=
  List.countP_append ..
theorem nSrc_append (b : Bool) (gs hs : List (OInstr S O)) :
    nSrc b (gs ++ hs) = nSrc b gs + nSrc b hs := List.countP_append ..
theorem nSeed_append (gs hs : List (OInstr S O)) : nSeed (gs ++ hs) = nSeed gs + nSeed hs :=
  List.countP_append ..

theorem nGates_invList (gs : List (OInstr S O)) : nGates (invList gs) = nGates gs := by
  simp [nGates, invList, List.countP_reverse, List.countP_map, Function.comp_def]
theorem nUJ_invList (gs : List (OInstr S O)) : nUJ (invList gs) = nUJ gs := by
  simp [nUJ, invList, List.countP_reverse, List.countP_map, Function.comp_def]
theorem nPriv_invList (gs : List (OInstr S O)) : nPriv (invList gs) = nPriv gs := by
  simp [nPriv, invList, List.countP_reverse, List.countP_map, Function.comp_def]
theorem nSrc_invList (b : Bool) (gs : List (OInstr S O)) : nSrc b (invList gs) = nSrc b gs := by
  simp [nSrc, invList, List.countP_reverse, List.countP_map, Function.comp_def]
theorem nSeed_invList (gs : List (OInstr S O)) : nSeed (invList gs) = nSeed gs := by
  simp [nSeed, invList, List.countP_reverse, List.countP_map, Function.comp_def]

end Count

/-! ### Elementary gate lists -/

/-- Elementary gates as instructions. -/
def ofGates (gs : List (Gate (S ⊕ O))) : List (OInstr S O) := gs.map OInstr.gate

theorem run_ofGates (ω : Wiring S O a Λ P) (σ : Oracles a Λ P) (gs : List (Gate (S ⊕ O))) :
    run ω σ (ofGates gs) = gRun gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
      simp only [ofGates, List.map_cons] at ih ⊢
      rw [run_cons, ih]
      rfl

omit [Fintype S] [DecidableEq S] [Fintype O] [DecidableEq O] in
theorem ofGates_append (gs hs : List (Gate (S ⊕ O))) :
    ofGates (gs ++ hs) = ofGates gs ++ ofGates hs := by
  simp [ofGates]

omit [Fintype S] [DecidableEq S] [Fintype O] [DecidableEq O] in
theorem nGates_ofGates (gs : List (Gate (S ⊕ O))) : nGates (ofGates gs) = gs.length := by
  simp [nGates, ofGates, List.countP_map, Function.comp_def, OInstr.isGate]

omit [Fintype S] [DecidableEq S] [Fintype O] [DecidableEq O] in
theorem ofGates_counts (gs : List (Gate (S ⊕ O))) :
    nUJ (ofGates gs) = 0 ∧ nPriv (ofGates gs) = 0 ∧ (∀ b, nSrc b (ofGates gs) = 0) ∧
      nSeed (ofGates gs) = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [nUJ, ofGates, List.countP_map, Function.comp_def, OInstr.isUJ]
  · simp [nPriv, ofGates, List.countP_map, Function.comp_def, OInstr.isPriv]
  · intro b; simp [nSrc, ofGates, List.countP_map, Function.comp_def, OInstr.isSrc]
  · simp [nSeed, ofGates, List.countP_map, Function.comp_def, OInstr.isSeed]

omit [Fintype S] [DecidableEq S] [Fintype O] [DecidableEq O] in
theorem valid_ofGates (anc : Fin a → S) (gs : List (Gate (S ⊕ O)))
    (h : ∀ g ∈ gs, GateOK 3 g) : ∀ g ∈ ofGates gs, g.Valid anc := by
  intro g hg
  simp only [ofGates, List.mem_map] at hg
  obtain ⟨g', hg', rfl⟩ := hg
  exact h g' hg'

/-! ### The embedded simulator -/

/-- The released simulator instruction on the simulator wires. -/
def embI : Instr S → OInstr S O
  | .gate g => .gate (Gate.map Sum.inl g)
  | .uj cs adj => .uj cs adj
  | .priv cs adj => .priv cs adj

theorem eval_embI (ω : Wiring S O a Λ P) (σ : Oracles a Λ P) (i : Instr S) :
    (embI (O := O) i).eval ω σ =
      localOp Sum.inl Sum.inl_injective (fun x => i.eval (OInstr.semAt ω σ x)) := by
  cases i with
  | gate g => exact (Gate.map_op Sum.inl_injective g).symm
  | uj cs adj =>
      have e : embI (O := O) (Instr.uj cs adj) = .uj cs adj := rfl
      rw [e, OInstr.eval_uj]
      congr 1
  | priv cs adj =>
      have e : embI (O := O) (Instr.priv cs adj) = .priv cs adj := rfl
      rw [e, OInstr.eval_priv]
      congr 1

/-- The embedded simulator acts as the released circuit selected by every
configuration of the solver wires. -/
theorem run_map_embI (ω : Wiring S O a Λ P) (σ : Oracles a Λ P) (gs : List (Instr S)) :
    run ω σ (gs.map (embI (O := O))) =
      localOp Sum.inl Sum.inl_injective (fun x => GateCircuit.run (OInstr.semAt ω σ x) gs) := by
  induction gs with
  | nil => exact (localOp_one Sum.inl_injective).symm
  | cons g gs ih =>
      rw [List.map_cons, run_cons, ih, eval_embI, localOp_comp]
      rfl

omit [Fintype S] [DecidableEq S] [Fintype O] [DecidableEq O] in
theorem embI_valid (anc : Fin a → S) (i : Instr S) (h : i.Valid anc) :
    (embI (O := O) i).Valid anc := by
  cases i with
  | gate g =>
      obtain ⟨h1, h2, h3⟩ := h
      refine ⟨by simpa [Gate.map] using h1, ?_, h3⟩
      intro c hc
      simp only [Gate.map, List.mem_map] at hc
      obtain ⟨c', hc', rfl⟩ := hc
      intro e
      exact h2 c' hc' (Sum.inl_injective e)
  | uj cs adj => exact h
  | priv cs adj => exact h

omit [Fintype S] [DecidableEq S] [Fintype O] [DecidableEq O] in
theorem embI_counts (gs : List (Instr S)) :
    nGates (gs.map (embI (O := O))) = GateCircuit.nGates gs ∧
      nUJ (gs.map (embI (O := O))) = GateCircuit.nUJ gs ∧
      nPriv (gs.map (embI (O := O))) = GateCircuit.nPriv gs ∧
      (∀ b, nSrc b (gs.map (embI (O := O))) = 0) ∧ nSeed (gs.map (embI (O := O))) = 0 := by
  have hG : ∀ i : Instr S, (embI (O := O) i).isGate = i.isGate := by intro i; cases i <;> rfl
  have hU : ∀ i : Instr S, (embI (O := O) i).isUJ = i.isUJ := by intro i; cases i <;> rfl
  have hP : ∀ i : Instr S, (embI (O := O) i).isPriv = i.isPriv := by intro i; cases i <;> rfl
  have hS : ∀ b (i : Instr S), (embI (O := O) i).isSrc b = false := by
    intro b i; cases i <;> rfl
  have hE : ∀ i : Instr S, (embI (O := O) i).isSeed = false := by intro i; cases i <;> rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [nGates, GateCircuit.nGates, List.countP_map, Function.comp_def, hG]
  · simp [nUJ, GateCircuit.nUJ, List.countP_map, Function.comp_def, hU]
  · simp [nPriv, GateCircuit.nPriv, List.countP_map, Function.comp_def, hP]
  · intro b; simp [nSrc, List.countP_map, Function.comp_def, hS]
  · simp [nSeed, List.countP_map, Function.comp_def, hE]

/-! ### Circuits as released multi-oracle programs -/

/-- Every instruction is a named oracle of the released program model. -/
def family (ω : Wiring S O a Λ P) :
    OInstr S O → Oracles a Λ P → Reg (S ⊕ O) P →L[ℂ] Reg (S ⊕ O) P :=
  fun g σ => g.eval ω σ

/-- A circuit as a released multi-oracle program. -/
def toProgram (ω : Wiring S O a Λ P) :
    List (OInstr S O) → MultiOracleCircuit.Program (family ω)
  | [] => .identity
  | g :: gs => .seq (toProgram ω gs) (.query g)

theorem toProgram_eval (ω : Wiring S O a Λ P) (σ : Oracles a Λ P) (gs : List (OInstr S O)) :
    (toProgram ω gs).eval σ = run ω σ gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
      rw [toProgram, MultiOracleCircuit.Program.eval_seq, ih,
        MultiOracleCircuit.Program.eval_query, run_cons, mul_def]
      rfl

theorem toProgram_cost (ω : Wiring S O a Λ P) (gs : List (OInstr S O)) (w : OInstr S O → ℕ) :
    (toProgram ω gs).cost w = (gs.map w).sum := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
      rw [toProgram, MultiOracleCircuit.Program.cost_seq, ih,
        MultiOracleCircuit.Program.cost_query, List.map_cons, List.sum_cons, add_comm]

omit [Fintype S] [DecidableEq S] [Fintype O] [DecidableEq O] in
theorem sum_map_indicator (p : OInstr S O → Bool) (gs : List (OInstr S O)) :
    (gs.map (fun g => if p g then 1 else 0)).sum = gs.countP p := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
      rw [List.map_cons, List.sum_cons, ih, List.countP_cons]
      by_cases h : p g = true
      · simp [h, add_comm]
      · simp [h]

end

end SparseHamiltonian.GateODE
