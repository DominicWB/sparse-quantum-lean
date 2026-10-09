import GateEfficientODE.Model.Block

/-!
# The native instruction model

The native gate-level circuits act on qubit wires `V` carrying a payload
Hilbert space `R`.  An instruction is

* an elementary gate (`gate`): a one-qubit unitary with at most three literal
  controls, all off the target, exactly as in the released gate-level
  libraries; every elementary gate counts as one gate;
* a call of a supplied primitive oracle or of its inverse (`call j adj pos`):
  the unitary `prim j` on a fixed register `Reg Y R`, placed on the wires of
  the embedding `pos : Y ↪ V`.  Primitive calls are never controlled, and
  every call counts as one call.

A circuit is a list of instructions; the head acts first.  The literal
inverse circuit reverses the list and inverts every instruction
(`run_invList`).  Renaming the wires along an embedding acts as the
corresponding exposed operator (`run_map`).
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateNative

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit
open GateODE (adjIf adjIf_adjoint adjIf_isUnitary localOp_localOp localOp_gateOp)
open scoped InnerProduct BigOperators

/-- Native instructions on wires `V`: elementary gates, and calls of the
primitive oracle `j` (or its inverse) placed on the wires `pos`. -/
inductive NInstr (V : Type*) (Y : Type*) (J : Type*)
  | gate (g : Gate V)
  | call (j : J) (adj : Bool) (pos : Y ↪ V)

namespace NInstr

variable {V V' Y J : Type*}

/-- Is an elementary gate. -/
def isGate : NInstr V Y J → Bool
  | .gate _ => true
  | _ => false

/-- Is a primitive call whose oracle satisfies `p`. -/
def isCall (p : J → Bool) : NInstr V Y J → Bool
  | .call j _ _ => p j
  | _ => false

/-- The inverse instruction. -/
def inv : NInstr V Y J → NInstr V Y J
  | .gate g => .gate ⟨g.cs, g.t, g.u.conjTranspose⟩
  | .call j adj pos => .call j (!adj) pos

/-- Renaming the wires along an embedding. -/
def map (f : V ↪ V') : NInstr V Y J → NInstr V' Y J
  | .gate g => .gate (GateODE.Gate.map f g)
  | .call j adj pos => .call j adj (pos.trans f)

/-- Elementary validity: a gate has at most three controls, all off the
target, and a unitary matrix; a call is always valid. -/
def Valid : NInstr V Y J → Prop
  | .gate g => GateOK 3 g
  | .call _ _ _ => True

@[simp] theorem isGate_inv (i : NInstr V Y J) : i.inv.isGate = i.isGate := by cases i <;> rfl
@[simp] theorem isCall_inv (p : J → Bool) (i : NInstr V Y J) : i.inv.isCall p = i.isCall p := by
  cases i <;> rfl
@[simp] theorem isGate_map (f : V ↪ V') (i : NInstr V Y J) : (i.map f).isGate = i.isGate := by
  cases i <;> rfl
@[simp] theorem isCall_map (p : J → Bool) (f : V ↪ V') (i : NInstr V Y J) :
    (i.map f).isCall p = i.isCall p := by
  cases i <;> rfl

theorem valid_inv (i : NInstr V Y J) (h : i.Valid) : i.inv.Valid := by
  cases i with
  | gate g => exact gateOK_conj h
  | call j adj pos => trivial

theorem valid_map (f : V ↪ V') (i : NInstr V Y J) (h : i.Valid) : (i.map f).Valid := by
  cases i with
  | gate g =>
      obtain ⟨h1, h2, h3⟩ := h
      refine ⟨by simpa [GateODE.Gate.map] using h1, ?_, h3⟩
      intro c hc
      simp only [GateODE.Gate.map, List.mem_map] at hc
      obtain ⟨c', hc', rfl⟩ := hc
      intro e
      exact h2 c' hc' (f.injective e)
  | call j adj pos => trivial

end NInstr

/-! ### Semantics -/

section Semantics

variable {V Y J : Type*} [Fintype V] [DecidableEq V] [Fintype Y] [DecidableEq Y]
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- The operator of one instruction, for the primitive oracles `prim`. -/
def NInstr.eval (prim : J → Reg Y R →L[ℂ] Reg Y R) : NInstr V Y J → Reg V R →L[ℂ] Reg V R
  | .gate g => gateOp g.cs g.t g.u
  | .call j adj pos => localOp pos pos.injective (fun _ => adjIf adj (prim j))

variable (prim : J → Reg Y R →L[ℂ] Reg Y R)

@[simp] theorem NInstr.eval_gate (g : Gate V) :
    (NInstr.gate g : NInstr V Y J).eval prim = gateOp g.cs g.t g.u := rfl

@[simp] theorem NInstr.eval_call (j : J) (adj : Bool) (pos : Y ↪ V) :
    (NInstr.call j adj pos : NInstr V Y J).eval prim =
      localOp pos pos.injective (fun _ => adjIf adj (prim j)) := rfl

theorem NInstr.eval_inv (i : NInstr V Y J) : i.inv.eval prim = (i.eval prim)† := by
  cases i with
  | gate g => exact (gateOp_adjoint g.cs g.t g.u).symm
  | call j adj pos =>
      change localOp pos pos.injective (fun _ => adjIf (!adj) (prim j)) =
        (localOp pos pos.injective (fun _ => adjIf adj (prim j)))†
      rw [localOp_adjoint, adjIf_adjoint]

theorem NInstr.eval_isUnitary (hprim : ∀ j, IsUnitary (prim j)) (i : NInstr V Y J)
    (hi : i.Valid) : IsUnitary (i.eval prim) := by
  cases i with
  | gate g => exact gateOp_isUnitary g.cs g.t g.u hi.2.2
  | call j adj pos =>
      rw [NInstr.eval_call]
      exact localOp_isUnitary _ _ (fun _ => adjIf_isUnitary adj _ (hprim j))

/-- Run a circuit: the head instruction acts first. -/
def nrun : List (NInstr V Y J) → Reg V R →L[ℂ] Reg V R
  | [] => 1
  | i :: is => nrun is ∘L i.eval prim

@[simp] theorem nrun_nil : nrun prim ([] : List (NInstr V Y J)) = 1 := rfl

theorem nrun_cons (i : NInstr V Y J) (is : List (NInstr V Y J)) :
    nrun prim (i :: is) = nrun prim is ∘L i.eval prim := rfl

theorem nrun_append (is js : List (NInstr V Y J)) :
    nrun prim (is ++ js) = nrun prim js ∘L nrun prim is := by
  induction is with
  | nil => ext ψ; rfl
  | cons i is ih => simp only [List.cons_append, nrun_cons, ih, comp_assoc]

theorem nrun_singleton (i : NInstr V Y J) : nrun prim [i] = i.eval prim := by
  ext ψ; rfl

/-- The literal inverse circuit. -/
def ninv (is : List (NInstr V Y J)) : List (NInstr V Y J) := (is.map NInstr.inv).reverse

theorem nrun_ninv (is : List (NInstr V Y J)) : nrun prim (ninv is) = (nrun prim is)† := by
  induction is with
  | nil => simp [ninv, nrun]
  | cons i is ih =>
      have h1 : ninv (i :: is) = ninv is ++ [i.inv] := by simp [ninv]
      rw [h1, nrun_append, ih, nrun_singleton, NInstr.eval_inv, nrun_cons, adjoint_comp]

omit [Fintype V] [DecidableEq V] [Fintype Y] [DecidableEq Y] in
theorem ninv_append (is js : List (NInstr V Y J)) : ninv (is ++ js) = ninv js ++ ninv is := by
  simp [ninv]

omit [Fintype V] [DecidableEq V] [Fintype Y] [DecidableEq Y] in
theorem ninv_ninv (is : List (NInstr V Y J)) : ninv (ninv is) = is := by
  have hinv : ∀ i : NInstr V Y J, i.inv.inv = i := by
    intro i
    cases i with
    | gate g => simp [NInstr.inv, Matrix.conjTranspose_conjTranspose]
    | call j adj pos => simp [NInstr.inv]
  simp [ninv, List.map_reverse, List.map_map, Function.comp_def, hinv]

theorem nrun_isUnitary (hprim : ∀ j, IsUnitary (prim j)) (is : List (NInstr V Y J))
    (his : ∀ i ∈ is, i.Valid) : IsUnitary (nrun prim is) := by
  induction is with
  | nil => exact isUnitary_one
  | cons i is ih =>
      rw [nrun_cons, ← mul_def]
      exact (ih (fun h hh => his h (List.mem_cons_of_mem i hh))).mul
        (NInstr.eval_isUnitary prim hprim i (his i List.mem_cons_self))

omit [Fintype V] [DecidableEq V] [Fintype Y] [DecidableEq Y] in
theorem valid_ninv (is : List (NInstr V Y J)) (h : ∀ i ∈ is, i.Valid) :
    ∀ i ∈ ninv is, i.Valid := by
  intro i hi
  simp only [ninv, List.mem_reverse, List.mem_map] at hi
  obtain ⟨i', hi', rfl⟩ := hi
  exact NInstr.valid_inv i' (h i' hi')

/-! ### Elementary gate lists -/

/-- Elementary gates as native instructions. -/
def nGatesOf (gs : List (Gate V)) : List (NInstr V Y J) := gs.map NInstr.gate

theorem nrun_nGatesOf (gs : List (Gate V)) :
    nrun prim (nGatesOf (Y := Y) (J := J) gs) = gRun gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
      simp only [nGatesOf, List.map_cons] at ih ⊢
      rw [nrun_cons, ih]
      rfl

omit [Fintype V] [DecidableEq V] [Fintype Y] [DecidableEq Y] in
theorem nGatesOf_append (gs hs : List (Gate V)) :
    nGatesOf (Y := Y) (J := J) (gs ++ hs) = nGatesOf gs ++ nGatesOf hs := by
  simp [nGatesOf]

omit [Fintype V] [DecidableEq V] [Fintype Y] [DecidableEq Y] in
theorem valid_nGatesOf (gs : List (Gate V)) (h : ∀ g ∈ gs, GateOK 3 g) :
    ∀ i ∈ nGatesOf (Y := Y) (J := J) gs, i.Valid := by
  intro i hi
  simp only [nGatesOf, List.mem_map] at hi
  obtain ⟨g, hg, rfl⟩ := hi
  exact h g hg

omit [Fintype V] [DecidableEq V] [Fintype Y] [DecidableEq Y] in
theorem ninv_nGatesOf (gs : List (Gate V)) :
    ninv (nGatesOf (Y := Y) (J := J) gs) = nGatesOf (gInv gs) := by
  simp [ninv, nGatesOf, gInv, List.map_reverse, List.map_map, Function.comp_def, NInstr.inv]

end Semantics

/-! ### Renaming wires -/

section Map

variable {V V' Y J : Type*} [Fintype V] [DecidableEq V] [Fintype V'] [DecidableEq V']
  [Fintype Y] [DecidableEq Y]
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
variable (prim : J → Reg Y R →L[ℂ] Reg Y R)

/-- A renamed instruction acts as the original one on the exposed wires. -/
theorem NInstr.eval_map (f : V ↪ V') (i : NInstr V Y J) :
    (i.map f).eval prim = localOp f f.injective (fun _ => i.eval prim) := by
  cases i with
  | gate g => exact (GateODE.Gate.map_op f.injective g).symm
  | call j adj pos =>
      change localOp (pos.trans f) (pos.trans f).injective (fun _ => adjIf adj (prim j)) =
        localOp f f.injective (fun _ => localOp pos pos.injective (fun _ => adjIf adj (prim j)))
      rw [localOp_localOp f.injective pos.injective (fun _ _ => adjIf adj (prim j))]
      rfl

/-- A renamed circuit acts as the original one on the exposed wires. -/
theorem nrun_map (f : V ↪ V') (is : List (NInstr V Y J)) :
    nrun prim (is.map (NInstr.map f)) = localOp f f.injective (fun _ => nrun prim is) := by
  induction is with
  | nil => exact (localOp_one f.injective).symm
  | cons i is ih =>
      rw [List.map_cons, nrun_cons, ih, NInstr.eval_map, localOp_comp, nrun_cons]

omit [Fintype V] [DecidableEq V] [Fintype V'] [DecidableEq V'] [Fintype Y] [DecidableEq Y] in
theorem valid_map_list (f : V ↪ V') (is : List (NInstr V Y J)) (h : ∀ i ∈ is, i.Valid) :
    ∀ i ∈ is.map (NInstr.map f), i.Valid := by
  intro i hi
  simp only [List.mem_map] at hi
  obtain ⟨i', hi', rfl⟩ := hi
  exact NInstr.valid_map f i' (h i' hi')

omit [Fintype V] [DecidableEq V] [Fintype V'] [DecidableEq V'] [Fintype Y] [DecidableEq Y] in
theorem ninv_map (f : V ↪ V') (is : List (NInstr V Y J)) :
    ninv (is.map (NInstr.map f)) = (ninv is).map (NInstr.map f) := by
  have h : ∀ i : NInstr V Y J, (i.map f).inv = i.inv.map f := by
    intro i
    cases i with
    | gate g => rfl
    | call j adj pos => rfl
  simp [ninv, List.map_reverse, List.map_map, Function.comp_def, h]

end Map

/-! ### Counting -/

section Count

variable {V V' Y J : Type*}

/-- The number of elementary gates. -/
def nGatesN (is : List (NInstr V Y J)) : ℕ := is.countP NInstr.isGate

/-- The number of primitive calls of the oracles satisfying `p`. -/
def nCallsN (p : J → Bool) (is : List (NInstr V Y J)) : ℕ := is.countP (NInstr.isCall p)

theorem nGatesN_append (is js : List (NInstr V Y J)) :
    nGatesN (is ++ js) = nGatesN is + nGatesN js := List.countP_append ..

theorem nCallsN_append (p : J → Bool) (is js : List (NInstr V Y J)) :
    nCallsN p (is ++ js) = nCallsN p is + nCallsN p js := List.countP_append ..

theorem nGatesN_ninv (is : List (NInstr V Y J)) : nGatesN (ninv is) = nGatesN is := by
  simp [nGatesN, ninv, List.countP_reverse, List.countP_map, Function.comp_def]

theorem nCallsN_ninv (p : J → Bool) (is : List (NInstr V Y J)) :
    nCallsN p (ninv is) = nCallsN p is := by
  simp [nCallsN, ninv, List.countP_reverse, List.countP_map, Function.comp_def]

theorem nGatesN_map (f : V ↪ V') (is : List (NInstr V Y J)) :
    nGatesN (is.map (NInstr.map f)) = nGatesN is := by
  simp [nGatesN, List.countP_map, Function.comp_def]

theorem nCallsN_map (p : J → Bool) (f : V ↪ V') (is : List (NInstr V Y J)) :
    nCallsN p (is.map (NInstr.map f)) = nCallsN p is := by
  simp [nCallsN, List.countP_map, Function.comp_def]

theorem nGatesN_nGatesOf (gs : List (Gate V)) :
    nGatesN (nGatesOf (Y := Y) (J := J) gs) = gs.length := by
  simp [nGatesN, nGatesOf, List.countP_map, Function.comp_def, NInstr.isGate]

theorem nCallsN_nGatesOf (p : J → Bool) (gs : List (Gate V)) :
    nCallsN p (nGatesOf (Y := Y) (J := J) gs) = 0 := by
  simp [nCallsN, nGatesOf, List.countP_map, Function.comp_def, NInstr.isCall]

theorem nGatesN_flatMap {α : Type*} (f : α → List (NInstr V Y J)) (l : List α) :
    nGatesN (l.flatMap f) = (l.map (fun a => nGatesN (f a))).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.flatMap_cons, nGatesN_append, ih, List.map_cons, List.sum_cons]

theorem nCallsN_flatMap {α : Type*} (p : J → Bool) (f : α → List (NInstr V Y J)) (l : List α) :
    nCallsN p (l.flatMap f) = (l.map (fun a => nCallsN p (f a))).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.flatMap_cons, nCallsN_append, ih, List.map_cons, List.sum_cons]

theorem nGatesN_replicate (n : ℕ) (is : List (NInstr V Y J)) :
    nGatesN (List.replicate n is).flatten = n * nGatesN is := by
  induction n with
  | zero => simp [nGatesN]
  | succ n ih =>
      rw [List.replicate_succ, List.flatten_cons, nGatesN_append, ih]
      ring

theorem nCallsN_replicate (p : J → Bool) (n : ℕ) (is : List (NInstr V Y J)) :
    nCallsN p (List.replicate n is).flatten = n * nCallsN p is := by
  induction n with
  | zero => simp [nCallsN]
  | succ n ih =>
      rw [List.replicate_succ, List.flatten_cons, nCallsN_append, ih]
      ring

end Count

end

end SparseHamiltonian.GateNative
