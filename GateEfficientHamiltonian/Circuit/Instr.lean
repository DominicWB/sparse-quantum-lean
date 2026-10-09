import GateEfficientHamiltonian.Circuit.Register

/-!
# Elementary gates, oracle calls and circuits

An elementary gate is a one-qubit matrix on a target wire, controlled by at
most three literals (so it touches at most four wires).  The two oracle
instructions apply the supplied unitary `U_J` or the private Cayley operation
`D` (or their adjoints) to the ancilla wires and the system payload, under
literal controls.  A circuit is a list of instructions executed from left to
right; its inverse is the reversed list of inverse instructions.

`Agrees S C O` states that the circuit operator `C` equals the ideal operator
`O` on every vector supported on the clean configurations `S`.  The calculus
below composes such statements and transfers them to adjoints.
-/

namespace SparseHamiltonian.GateCircuit

noncomputable section
open ContinuousLinearMap OracleCircuit
open scoped InnerProduct BigOperators

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- Literal controls: wire `c.1` holds the value `c.2`. -/
def ctrlOK (cs : List (W × Bool)) (x : Cfg W) : Bool := cs.all (fun c => x c.1 == c.2)

omit [Fintype W] [DecidableEq W] in
theorem ctrlOK_iff (cs : List (W × Bool)) (x : Cfg W) :
    ctrlOK cs x = true ↔ ∀ c ∈ cs, x c.1 = c.2 := by
  simp [ctrlOK, List.all_eq_true]

omit [Fintype W] [DecidableEq W] in
theorem ctrlOK_nil (x : Cfg W) : ctrlOK [] x = true := rfl

omit [Fintype W] [DecidableEq W] in
theorem ctrlOK_cons (c : W × Bool) (cs : List (W × Bool)) (x : Cfg W) :
    ctrlOK (c :: cs) x = ((x c.1 == c.2) && ctrlOK cs x) := rfl

omit [Fintype W] in
theorem ctrlOK_update (cs : List (W × Bool)) (t : W) (ht : ∀ c ∈ cs, c.1 ≠ t)
    (x : Cfg W) (b : Bool) : ctrlOK cs (Function.update x t b) = ctrlOK cs x := by
  apply Bool.eq_iff_iff.mpr
  rw [ctrlOK_iff, ctrlOK_iff]
  constructor
  · intro h c hc
    have := h c hc
    rwa [Function.update_of_ne (ht c hc)] at this
  · intro h c hc
    rw [Function.update_of_ne (ht c hc)]
    exact h c hc

/-- An elementary gate. -/
structure Gate (W : Type*) where
  cs : List (W × Bool)
  t : W
  u : Matrix Bool Bool ℂ

/-- The Pauli `X` matrix, used by reversible classical gates. -/
def pauliX : Matrix Bool Bool ℂ := fun b c => if b = c then 0 else 1

theorem pauliX_apply (b c : Bool) : pauliX b c = if b = !c then 1 else 0 := by
  cases b <;> cases c <;> rfl

theorem pauliX_conjTranspose : pauliX.conjTranspose = pauliX := by
  funext b c; cases b <;> cases c <;> simp [pauliX, Matrix.conjTranspose_apply]

theorem pauliX_mul_self : pauliX * pauliX = 1 := by
  funext b c
  simp only [Matrix.mul_apply, Fintype.sum_bool, pauliX, Matrix.one_apply]
  cases b <;> cases c <;> simp

/-- A unitary one-qubit matrix. -/
def UnitaryMat (u : Matrix Bool Bool ℂ) : Prop :=
  u.conjTranspose * u = 1 ∧ u * u.conjTranspose = 1

theorem pauliX_unitary : UnitaryMat pauliX := by
  constructor <;> rw [pauliX_conjTranspose, pauliX_mul_self]

theorem one_unitaryMat : UnitaryMat (1 : Matrix Bool Bool ℂ) := by
  constructor <;> simp

variable {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] [CompleteSpace Q]

/-- Semantics of a controlled one-qubit matrix. -/
def gateOp (cs : List (W × Bool)) (t : W) (u : Matrix Bool Bool ℂ) : Reg W Q →L[ℂ] Reg W Q :=
  condOp t (fun x => if ctrlOK cs x then u else 1)

omit [Fintype W] [CompleteSpace Q] in
theorem sum_update_one (ψ : Reg W Q) (x : Cfg W) (t : W) :
    (∑ b : Bool, (1 : Matrix Bool Bool ℂ) (x t) b • ψ (Function.update x t b)) = ψ x := by
  rw [Finset.sum_eq_single (x t)]
  · simp
  · intro b _ hb; simp [Ne.symm hb]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem gateOp_apply (cs : List (W × Bool)) (t : W) (u : Matrix Bool Bool ℂ)
    (ht : ∀ c ∈ cs, c.1 ≠ t) (ψ : Reg W Q) (x : Cfg W) :
    gateOp cs t u ψ x = if ctrlOK cs x then
      ∑ b : Bool, u (x t) b • ψ (Function.update x t b) else ψ x := by
  rw [gateOp, condOp_apply, ctrlOK_update cs t ht]
  split_ifs
  · rfl
  · exact sum_update_one ψ x t

theorem gateOp_adjoint (cs : List (W × Bool)) (t : W) (u : Matrix Bool Bool ℂ) :
    (gateOp (Q := Q) cs t u)† = gateOp cs t u.conjTranspose := by
  rw [gateOp, condOp_adjoint]
  congr 1
  funext x
  split_ifs <;> simp

theorem gateOp_isUnitary (cs : List (W × Bool)) (t : W) (u : Matrix Bool Bool ℂ)
    (hu : UnitaryMat u) : IsUnitary (gateOp (Q := Q) cs t u) := by
  apply condOp_isUnitary
  intro x
  split_ifs
  · exact hu
  · simp

/-- Flipping the target of a classical gate. -/
def flipCfg (cs : List (W × Bool)) (t : W) (x : Cfg W) : Cfg W :=
  if ctrlOK cs x then Function.update x t (!x t) else x

omit [Fintype W] in
theorem flipCfg_flipCfg (cs : List (W × Bool)) (t : W) (ht : ∀ c ∈ cs, c.1 ≠ t)
    (x : Cfg W) : flipCfg cs t (flipCfg cs t x) = x := by
  unfold flipCfg
  by_cases h : ctrlOK cs x = true
  · rw [if_pos h, ctrlOK_update cs t ht, if_pos h]
    funext w
    by_cases hw : w = t
    · subst hw; simp
    · simp [Function.update_of_ne hw]
  · rw [if_neg h, if_neg h]

/-- A controlled NOT as a permutation of configurations. -/
def flipEquiv (cs : List (W × Bool)) (t : W) (ht : ∀ c ∈ cs, c.1 ≠ t) : Cfg W ≃ Cfg W where
  toFun := flipCfg cs t
  invFun := flipCfg cs t
  left_inv := flipCfg_flipCfg cs t ht
  right_inv := flipCfg_flipCfg cs t ht

theorem gateOp_pauliX (cs : List (W × Bool)) (t : W) (ht : ∀ c ∈ cs, c.1 ≠ t) :
    gateOp (Q := Q) cs t pauliX = permOp (flipEquiv cs t ht) := by
  ext ψ x
  rw [gateOp_apply cs t pauliX ht, permOp_apply]
  change _ = ψ (flipCfg cs t x)
  unfold flipCfg
  by_cases h : ctrlOK cs x = true
  · simp only [h, if_true]
    rw [Fintype.sum_bool]
    cases hx : x t <;> simp [pauliX]
  · simp only [h]
    rfl

/-! ### Instructions -/

/-- The instructions of the gate-level simulator. -/
inductive Instr (W : Type*)
  | gate (g : Gate W)
  | uj (cs : List (W × Bool)) (adj : Bool)
  | priv (cs : List (W × Bool)) (adj : Bool)

namespace Instr

def isGate : Instr W → Bool
  | .gate _ => true
  | _ => false

def isUJ : Instr W → Bool
  | .uj _ _ => true
  | _ => false

def isPriv : Instr W → Bool
  | .priv _ _ => true
  | _ => false

/-- Inverse instruction. -/
def inv : Instr W → Instr W
  | .gate g => .gate ⟨g.cs, g.t, g.u.conjTranspose⟩
  | .uj cs adj => .uj cs (!adj)
  | .priv cs adj => .priv cs (!adj)

omit [Fintype W] [DecidableEq W] in
@[simp] theorem isGate_inv (g : Instr W) : g.inv.isGate = g.isGate := by cases g <;> rfl
omit [Fintype W] [DecidableEq W] in
@[simp] theorem isUJ_inv (g : Instr W) : g.inv.isUJ = g.isUJ := by cases g <;> rfl
omit [Fintype W] [DecidableEq W] in
@[simp] theorem isPriv_inv (g : Instr W) : g.inv.isPriv = g.isPriv := by cases g <;> rfl

/-- Elementary validity: at most three controls distinct from the target and a
unitary matrix for gates; at most one control off the ancilla wires for oracle
calls. -/
def Valid {a : ℕ} (anc : Fin a → W) : Instr W → Prop
  | .gate g => g.cs.length ≤ 3 ∧ (∀ c ∈ g.cs, c.1 ≠ g.t) ∧ UnitaryMat g.u
  | .uj cs _ => cs.length ≤ 1 ∧ ∀ c ∈ cs, ∀ i, anc i ≠ c.1
  | .priv cs _ => cs.length ≤ 1 ∧ ∀ c ∈ cs, ∀ i, anc i ≠ c.1

omit [Fintype W] [DecidableEq W] in
theorem valid_inv {a : ℕ} (anc : Fin a → W) (g : Instr W) (h : g.Valid anc) :
    g.inv.Valid anc := by
  cases g with
  | gate g =>
      obtain ⟨h1, h2, h3, h4⟩ := h
      refine ⟨h1, h2, ?_⟩
      constructor
      · rw [Matrix.conjTranspose_conjTranspose]; exact h4
      · rw [Matrix.conjTranspose_conjTranspose]; exact h3
  | uj cs adj => exact h
  | priv cs adj => exact h

end Instr

section Semantics

variable {a : ℕ} {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-- The ancilla-and-system space on which `U_J` and `D` act. -/
abbrev Anc (a : ℕ) (P : Type*) := Reg (Fin a) P

/-- An oracle call on the ancilla wires, under literal controls. -/
def oracleOp (anc : Fin a → W) (hanc : Function.Injective anc) (cs : List (W × Bool))
    (O : Anc a P →L[ℂ] Anc a P) : Reg W P →L[ℂ] Reg W P :=
  localOp anc hanc (fun x => if ctrlOK cs x then O else 1)

theorem oracleOp_adjoint (anc : Fin a → W) (hanc : Function.Injective anc)
    (cs : List (W × Bool)) (O : Anc a P →L[ℂ] Anc a P) :
    (oracleOp anc hanc cs O)† = oracleOp anc hanc cs (O†) := by
  have h : (fun x => (if ctrlOK cs x then O else 1)†) =
      (fun x => if ctrlOK cs x then O† else 1) := by
    funext x; split_ifs <;> simp
  simp only [oracleOp, localOp_adjoint, h]

theorem oracleOp_isUnitary (anc : Fin a → W) (hanc : Function.Injective anc)
    (cs : List (W × Bool)) (O : Anc a P →L[ℂ] Anc a P) (hO : IsUnitary O) :
    IsUnitary (oracleOp anc hanc cs O) := by
  apply localOp_isUnitary
  intro x
  split_ifs
  · exact hO
  · exact isUnitary_one

/-- The fixed data of a semantics: ancilla wires and the two oracles. -/
structure Sem (W : Type*) (a : ℕ) (P : Type*) [NormedAddCommGroup P]
    [InnerProductSpace ℂ P] where
  anc : Fin a → W
  hanc : Function.Injective anc
  UJ : Anc a P →L[ℂ] Anc a P
  D : Anc a P →L[ℂ] Anc a P

variable (σ : Sem W a P)

def Instr.eval : Instr W → Reg W P →L[ℂ] Reg W P
  | .gate g => gateOp g.cs g.t g.u
  | .uj cs adj => oracleOp σ.anc σ.hanc cs (if adj then (σ.UJ)† else σ.UJ)
  | .priv cs adj => oracleOp σ.anc σ.hanc cs (if adj then (σ.D)† else σ.D)

theorem Instr.eval_inv (g : Instr W) : (g.inv).eval σ = (g.eval σ)† := by
  cases g with
  | gate g => exact (gateOp_adjoint g.cs g.t g.u).symm
  | uj cs adj =>
      cases adj
      · have e1 : (Instr.uj cs false).inv.eval σ = oracleOp σ.anc σ.hanc cs ((σ.UJ)†) := rfl
        have e2 : (Instr.uj cs false).eval σ = oracleOp σ.anc σ.hanc cs σ.UJ := rfl
        rw [e1, e2, oracleOp_adjoint]
      · have e1 : (Instr.uj cs true).inv.eval σ = oracleOp σ.anc σ.hanc cs σ.UJ := rfl
        have e2 : (Instr.uj cs true).eval σ = oracleOp σ.anc σ.hanc cs ((σ.UJ)†) := rfl
        rw [e1, e2, oracleOp_adjoint, adjoint_adjoint]
  | priv cs adj =>
      cases adj
      · have e1 : (Instr.priv cs false).inv.eval σ = oracleOp σ.anc σ.hanc cs ((σ.D)†) := rfl
        have e2 : (Instr.priv cs false).eval σ = oracleOp σ.anc σ.hanc cs σ.D := rfl
        rw [e1, e2, oracleOp_adjoint]
      · have e1 : (Instr.priv cs true).inv.eval σ = oracleOp σ.anc σ.hanc cs σ.D := rfl
        have e2 : (Instr.priv cs true).eval σ = oracleOp σ.anc σ.hanc cs ((σ.D)†) := rfl
        rw [e1, e2, oracleOp_adjoint, adjoint_adjoint]

theorem Instr.eval_isUnitary (hUJ : IsUnitary σ.UJ) (hD : IsUnitary σ.D)
    (g : Instr W) (hg : g.Valid σ.anc) : IsUnitary (g.eval σ) := by
  cases g with
  | gate g => exact gateOp_isUnitary g.cs g.t g.u hg.2.2
  | uj cs adj =>
      apply oracleOp_isUnitary
      cases adj
      · exact hUJ
      · simpa [star_eq_adjoint] using hUJ.adjoint
  | priv cs adj =>
      apply oracleOp_isUnitary
      cases adj
      · exact hD
      · simpa [star_eq_adjoint] using hD.adjoint

/-- Run a circuit: the head instruction acts first. -/
def run : List (Instr W) → Reg W P →L[ℂ] Reg W P
  | [] => 1
  | g :: gs => run gs ∘L g.eval σ

@[simp] theorem run_nil : run σ ([] : List (Instr W)) = 1 := rfl

theorem run_cons (g : Instr W) (gs : List (Instr W)) :
    run σ (g :: gs) = run σ gs ∘L g.eval σ := rfl

theorem run_append (gs hs : List (Instr W)) :
    run σ (gs ++ hs) = run σ hs ∘L run σ gs := by
  induction gs with
  | nil => ext ψ; rfl
  | cons g gs ih => simp only [List.cons_append, run_cons, ih, comp_assoc]

theorem run_singleton (g : Instr W) : run σ [g] = g.eval σ := by
  ext ψ; rfl

/-- The literal inverse circuit. -/
def invList (gs : List (Instr W)) : List (Instr W) := (gs.map Instr.inv).reverse

theorem run_invList (gs : List (Instr W)) : run σ (invList gs) = (run σ gs)† := by
  induction gs with
  | nil => simp [invList, run]
  | cons g gs ih =>
      have h1 : invList (g :: gs) = invList gs ++ [g.inv] := by simp [invList]
      rw [h1, run_append, ih, run_singleton, Instr.eval_inv, run_cons, adjoint_comp]

theorem run_isUnitary (hUJ : IsUnitary σ.UJ) (hD : IsUnitary σ.D) (gs : List (Instr W))
    (hgs : ∀ g ∈ gs, g.Valid σ.anc) : IsUnitary (run σ gs) := by
  induction gs with
  | nil => exact isUnitary_one
  | cons g gs ih =>
      rw [run_cons, ← mul_def]
      exact (ih (fun h hh => hgs h (List.mem_cons_of_mem g hh))).mul
        (Instr.eval_isUnitary σ hUJ hD g (hgs g (List.mem_cons_self)))

end Semantics

/-! ### Gate lists over an arbitrary payload -/

section GateLists

variable {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] [CompleteSpace Q]

def Gate.op (g : Gate W) : Reg W Q →L[ℂ] Reg W Q := gateOp g.cs g.t g.u

/-- Run a list of elementary gates. -/
def gRun : List (Gate W) → Reg W Q →L[ℂ] Reg W Q
  | [] => 1
  | g :: gs => gRun gs ∘L g.op

@[simp] theorem gRun_nil : gRun (Q := Q) ([] : List (Gate W)) = 1 := rfl

theorem gRun_cons (g : Gate W) (gs : List (Gate W)) :
    gRun (Q := Q) (g :: gs) = gRun gs ∘L g.op := rfl

theorem gRun_append (gs hs : List (Gate W)) :
    gRun (Q := Q) (gs ++ hs) = gRun hs ∘L gRun gs := by
  induction gs with
  | nil => ext ψ; rfl
  | cons g gs ih => simp only [List.cons_append, gRun_cons, ih, comp_assoc]

theorem gRun_singleton (g : Gate W) : gRun (Q := Q) [g] = g.op := by
  ext ψ; rfl

/-- The literal inverse gate list. -/
def gInv (gs : List (Gate W)) : List (Gate W) :=
  (gs.map (fun g => ⟨g.cs, g.t, g.u.conjTranspose⟩)).reverse

theorem gRun_gInv (gs : List (Gate W)) : gRun (Q := Q) (gInv gs) = (gRun gs)† := by
  induction gs with
  | nil => simp [gInv, gRun]
  | cons g gs ih =>
      have h1 : gInv (g :: gs) = gInv gs ++ [⟨g.cs, g.t, g.u.conjTranspose⟩] := by
        simp [gInv]
      rw [h1, gRun_append, ih, gRun_singleton, gRun_cons, adjoint_comp]
      simp only [Gate.op, gateOp_adjoint]

omit [Fintype W] [DecidableEq W] in
theorem gInv_length (gs : List (Gate W)) : (gInv gs).length = gs.length := by
  simp [gInv]

omit [Fintype W] [DecidableEq W] in
theorem mem_gInv (gs : List (Gate W)) (g : Gate W) (hg : g ∈ gInv gs) :
    ∃ h ∈ gs, g = ⟨h.cs, h.t, h.u.conjTranspose⟩ := by
  simp only [gInv, List.mem_reverse, List.mem_map] at hg
  obtain ⟨h, hh, rfl⟩ := hg
  exact ⟨h, hh, rfl⟩

/-- The elementary gates as instructions. -/
def ofGates (gs : List (Gate W)) : List (Instr W) := gs.map Instr.gate

theorem run_ofGates {a : ℕ} {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P]
    [CompleteSpace P] (σ : Sem W a P) (gs : List (Gate W)) :
    run σ (ofGates gs) = gRun gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih => simp only [ofGates, List.map_cons] at ih ⊢; rw [run_cons, ih]; rfl

omit [Fintype W] [DecidableEq W] in
theorem ofGates_append (gs hs : List (Gate W)) :
    ofGates (gs ++ hs) = ofGates gs ++ ofGates hs := by
  simp [ofGates]

end GateLists

/-! ### Counting -/

def nGates (gs : List (Instr W)) : ℕ := gs.countP Instr.isGate
def nUJ (gs : List (Instr W)) : ℕ := gs.countP Instr.isUJ
def nPriv (gs : List (Instr W)) : ℕ := gs.countP Instr.isPriv

omit [Fintype W] [DecidableEq W] in
theorem nGates_append (gs hs : List (Instr W)) :
    nGates (gs ++ hs) = nGates gs + nGates hs := List.countP_append ..
omit [Fintype W] [DecidableEq W] in
theorem nUJ_append (gs hs : List (Instr W)) : nUJ (gs ++ hs) = nUJ gs + nUJ hs :=
  List.countP_append ..
omit [Fintype W] [DecidableEq W] in
theorem nPriv_append (gs hs : List (Instr W)) : nPriv (gs ++ hs) = nPriv gs + nPriv hs :=
  List.countP_append ..

omit [Fintype W] [DecidableEq W] in
theorem nGates_invList (gs : List (Instr W)) : nGates (invList gs) = nGates gs := by
  simp [nGates, invList, List.countP_reverse, List.countP_map, Function.comp_def]
omit [Fintype W] [DecidableEq W] in
theorem nUJ_invList (gs : List (Instr W)) : nUJ (invList gs) = nUJ gs := by
  simp [nUJ, invList, List.countP_reverse, List.countP_map, Function.comp_def]
omit [Fintype W] [DecidableEq W] in
theorem nPriv_invList (gs : List (Instr W)) : nPriv (invList gs) = nPriv gs := by
  simp [nPriv, invList, List.countP_reverse, List.countP_map, Function.comp_def]

omit [Fintype W] [DecidableEq W] in
theorem nGates_ofGates (gs : List (Gate W)) : nGates (ofGates gs) = gs.length := by
  simp [nGates, ofGates, List.countP_map, Function.comp_def, Instr.isGate]
omit [Fintype W] [DecidableEq W] in
theorem nUJ_ofGates (gs : List (Gate W)) : nUJ (ofGates gs) = 0 := by
  simp [nUJ, ofGates, List.countP_map, Function.comp_def, Instr.isUJ]
omit [Fintype W] [DecidableEq W] in
theorem nPriv_ofGates (gs : List (Gate W)) : nPriv (ofGates gs) = 0 := by
  simp [nPriv, ofGates, List.countP_map, Function.comp_def, Instr.isPriv]

/-! ### Agreement on clean configurations -/

section Agree

variable {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] [CompleteSpace Q]

/-- `ψ` is supported on configurations satisfying `S`. -/
def Supp (S : Cfg W → Prop) (ψ : Reg W Q) : Prop := ∀ x, ¬ S x → ψ x = 0

/-- `O` maps `S`-supported vectors to `S`-supported vectors. -/
def Preserves (S : Cfg W → Prop) (O : Reg W Q →L[ℂ] Reg W Q) : Prop :=
  ∀ ψ, Supp S ψ → Supp S (O ψ)

/-- The circuit operator agrees with the ideal one on `S`-supported vectors. -/
def Agrees (S : Cfg W → Prop) (C O : Reg W Q →L[ℂ] Reg W Q) : Prop :=
  ∀ ψ, Supp S ψ → C ψ = O ψ

omit [Fintype W] [DecidableEq W] [CompleteSpace Q] in
theorem Agrees.refl (S : Cfg W → Prop) (C : Reg W Q →L[ℂ] Reg W Q) : Agrees S C C :=
  fun _ _ => rfl

omit [Fintype W] [DecidableEq W] [CompleteSpace Q] in
theorem Agrees.comp {S : Cfg W → Prop} {C₁ C₂ O₁ O₂ : Reg W Q →L[ℂ] Reg W Q}
    (h₁ : Agrees S C₁ O₁) (hO₁ : Preserves S O₁) (h₂ : Agrees S C₂ O₂) :
    Agrees S (C₂ ∘L C₁) (O₂ ∘L O₁) := by
  intro ψ hψ
  rw [comp_apply, comp_apply, h₁ ψ hψ, h₂ _ (hO₁ ψ hψ)]

omit [Fintype W] [DecidableEq W] [CompleteSpace Q] in
theorem Preserves.comp {S : Cfg W → Prop} {O₁ O₂ : Reg W Q →L[ℂ] Reg W Q}
    (h₁ : Preserves S O₁) (h₂ : Preserves S O₂) : Preserves S (O₂ ∘L O₁) :=
  fun ψ hψ => h₂ _ (h₁ ψ hψ)

omit [Fintype W] [DecidableEq W] [CompleteSpace Q] in
theorem Preserves.one (S : Cfg W → Prop) : Preserves S (1 : Reg W Q →L[ℂ] Reg W Q) :=
  fun _ hψ => hψ

theorem Agrees.adjoint {S : Cfg W → Prop} {C O : Reg W Q →L[ℂ] Reg W Q}
    (h : Agrees S C O) (hC : IsUnitary C) (hO : IsUnitary O)
    (hOs : Preserves S (O†)) : Agrees S (C†) (O†) := by
  intro ψ hψ
  have h1 : C ((O†) ψ) = ψ := by
    rw [h _ (hOs ψ hψ)]
    have := congrArg (fun F : Reg W Q →L[ℂ] Reg W Q => F ψ) hO.2
    simpa [star_eq_adjoint, mul_def] using this
  have h2 : (C†) (C ((O†) ψ)) = (O†) ψ := by
    have := congrArg (fun F : Reg W Q →L[ℂ] Reg W Q => F ((O†) ψ)) hC.1
    simpa [star_eq_adjoint, mul_def] using this
  rw [← h2, h1]

omit [Fintype W] [DecidableEq W] [InnerProductSpace ℂ Q] [CompleteSpace Q] in
theorem supp_add {S : Cfg W → Prop} {ψ φ : Reg W Q} (h₁ : Supp S ψ) (h₂ : Supp S φ) :
    Supp S (ψ + φ) := by
  intro x hx
  simp [h₁ x hx, h₂ x hx]

omit [Fintype W] [DecidableEq W] [CompleteSpace Q] in
theorem supp_smul {S : Cfg W → Prop} {ψ : Reg W Q} (c : ℂ) (h : Supp S ψ) :
    Supp S (c • ψ) := by
  intro x hx
  simp [h x hx]

omit [DecidableEq W] [InnerProductSpace ℂ Q] [CompleteSpace Q] in
theorem supp_bas {S : Cfg W → Prop} (x : Cfg W) (hx : S x) (q : Q) : Supp S (bas x q) := by
  intro y hy
  have : y ≠ x := fun h => hy (h ▸ hx)
  simp [this]

omit [CompleteSpace Q] in
/-- Agreement can be checked on basis vectors of `S`. -/
theorem agrees_of_bas {S : Cfg W → Prop} {C O : Reg W Q →L[ℂ] Reg W Q}
    (h : ∀ x, S x → ∀ q, C (bas x q) = O (bas x q)) : Agrees S C O := by
  intro ψ hψ
  rw [← sum_bas ψ, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : S x
  · exact h x hx (ψ x)
  · have : bas x (ψ x) = (0 : Reg W Q) := by
      rw [hψ x hx]
      apply PiLp.ext; intro y; simp
    rw [this, map_zero, map_zero]

end Agree

end

end SparseHamiltonian.GateCircuit
