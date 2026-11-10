import ManuscriptConformance.GateODETimeCert

/-!
# Conformance: source executions after native macro expansion

Manuscript: the resource statements of Theorem `ode:thm:gates` (constant and time-dependent
coefficients), which charge `O(ḡ)` executions of the supplied source preparations, `O(ḡ q)`
propagation calls and `O(ḡ (q + Q_src))` matrix calls in total.

The released solvers are labelled programs: a list of released instructions (`GateODE.OInstr`), in
which a source instruction `.src b adj` is one use of source interface `b` (its inverse when
`adj`). The native preparation is the macro expansion of this list (`nprepC`, `tnprepC` and the
zero-case assemblies `zprepC`, `tzprepC` are `List.flatMap` of their macros), and a source
instruction expands to exactly one copy of the supplied native circuit or its literal inverse,
placed on the source wires (`srcMacro`, `tsrcMacro`). A flat gate list does not record where a
source subroutine begins, so this module keeps the expansion as an **annotated program**:

* `ABlock`: a block of native instructions with a tag, `some (b, adj)` for one execution of the
  supplied source circuit `b` (literal inverse when `adj`), `none` for any other block;
  `aflat` flattens, `nexec b adj` counts the tagged executions, `AnnotOK src` says that every
  tagged block is exactly `src b adj`, `aerase` empties the source blocks;
* `ainv`, `astep`, `atrial`: the annotated inverse, amplification step and trial; `aflat_atrial`:
  the annotated trial **is** the actual native trial `trialN (aflat bs) j` (the same list of
  instructions), and `nexec_atrial`: a trial with `j` steps executes every source circuit
  `2j + 1` times (counting both orientations);
* `nCallsN_aflat`, `nGatesN_aflat`: the calls and gates of an annotated program are those of its
  other blocks plus, for every `(b, adj)`, the number of executions times the calls (gates) of
  `src b adj` (exact, not a division of a total);
* `labelCount`: the sum of a per-trial count over the trials of a completed history
  (`ODERepeatProtocol.Protocol.History`), so that counts hold for every history of the four-attempt
  protocol, including early successes and the history of four failures; `nhistory_calls`,
  `nhistory_gates`: along every history of `nprotocol (aflat bs) g`, the calls and gates are the
  propagation part (the same trials with the source blocks emptied) plus the executions times the
  supplied costs; `nhistory_exec_le`: at most `40 g` times the executions per preparation.

## The endpoints

`constAnnot`, `constAnnotI`, `timeAnnot`: the annotations of the constant preparation `bprepC`,
of the constant general-size preparations (`prepI`, hence `prepD`) and of the time-dependent
preparations (`GPubT.prep`, `prepTI`, hence `prepTD`), in the zero case and outside it.
`ode_thm_gates_sources` (constant, `ode_thm_gates`), `ode_thm_gates_decoder_sources` (constant,
binary entry decoder, `ode_thm_gates_decoder`), `ode_thm_gates_time_cert_sources`
(time-dependent certificate endpoint, `ode_thm_gates_time_cert`) and
`ode_thm_gates_time_decoder_cert_sources` (time-dependent, binary entry decoder,
`ode_thm_gates_time_decoder_cert`) state, for the protocols of those endpoints and every completed
history:

* **source executions**: at most `40 ḡ` executions of each source circuit (constant); at most
  `160 ḡ` executions of the loading circuit and `320 ḡ` of the weight-preparation circuit
  (time-dependent, protocol parameter `4ḡ`; one loading and two weight preparations per
  preparation);
* **calls**: the history's calls of every oracle kind are the propagation calls plus the executions
  times the calls inside each supplied circuit; the propagation calls are at most `C ḡ q` (times
  the number of selected kinds), zero when `T = 0` or `η_H + η_D = 0`, while the calls inside the
  supplied circuits are kept: in total at most `C ḡ q + 40 ḡ Q_src`, resp. `C ḡ q + 160 ḡ Q_load +
  320 ḡ Q_wp`;
* **gates**: the history's gates are the propagation gates (at most `C ḡ (q P(𝔟) + A_src)`) plus
  the executions times the gates of each supplied circuit (linear in the supplied gates);
* **workspace**: the source scratch `Zs` is one register of the native register, reused by every
  execution (the qubit bounds `C (𝔟 + 1)³ + C A_src` of the endpoints do not depend on the number
  of executions); every execution returns it clean on the instances of the endpoints (their
  `ApproxOn CleanX` hypotheses).

Here `C` is the constant of the corresponding endpoint (the propagation part is that endpoint's
bound for the same protocol with empty source circuits). The loading and weight-preparation
circuits are separate supplied interfaces and are counted separately; their adjoints are their
literal inverses (`ninv`), counted with them (`nexec b true`), with the same gate and call counts.
The protocols of `ode_thm_gates_time_cert_valid` and `ode_thm_gates_time_decoder_cert_valid` are
those of the certificate endpoints. The uniform-mesh endpoint `ode_thm_gates_time` and the
endpoints `ode_thm_gates_general`, `ode_thm_gates_time_general`, `ode_thm_gates_time_decoder` are
restated in `SourceExecutionsMore` with the same generic lemmas (annotations `btimeAnnot`,
`constAnnotI` and `timeAnnot`).
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

/-! ### Annotated native programs -/

section Annot

variable {V Y J : Type*}

/-- The source tag of a released instruction: `some (b, adj)` for a use of source interface `b`
(its inverse when `adj`), `none` otherwise. -/
def srcTag {S O : Type*} : OInstr S O → Option (Bool × Bool)
  | .src b adj => some (b, adj)
  | _ => none

/-- **An annotated block** of a native program: `some (b, adj)` marks one execution of the supplied
source circuit `b` (its literal inverse when `adj`), `none` any other block. -/
abbrev ABlock (V Y J : Type*) := Option (Bool × Bool) × List (NInstr V Y J)

/-- The native program of an annotated program. -/
def aflat (bs : List (ABlock V Y J)) : List (NInstr V Y J) := bs.flatMap Prod.snd

/-- The number of executions `(b, adj)` recorded by the annotation. -/
def nexec (b adj : Bool) (bs : List (ABlock V Y J)) : ℕ :=
  bs.countP fun x => x.1 == some (b, adj)

/-- The annotated program with every source execution emptied. -/
def aerase (bs : List (ABlock V Y J)) : List (ABlock V Y J) :=
  bs.map fun x => (x.1, if x.1.isSome then [] else x.2)

/-- **A faithful annotation**: every block tagged `(b, adj)` is exactly `src b adj`. -/
def AnnotOK (src : Bool → Bool → List (NInstr V Y J)) (bs : List (ABlock V Y J)) : Prop :=
  ∀ x ∈ bs, ∀ b adj, x.1 = some (b, adj) → x.2 = src b adj

/-- The tag of the inverse block. -/
def flipTag (t : Option (Bool × Bool)) : Option (Bool × Bool) := t.map fun p => (p.1, !p.2)

/-- **The annotated inverse**: the blocks in reverse order, each inverted, source executions
reversed in orientation. -/
def ainv (bs : List (ABlock V Y J)) : List (ABlock V Y J) :=
  (bs.map fun x => (flipTag x.1, ninv x.2)).reverse

@[simp] theorem aflat_nil : aflat ([] : List (ABlock V Y J)) = [] := rfl

@[simp] theorem aflat_cons (x : ABlock V Y J) (bs : List (ABlock V Y J)) :
    aflat (x :: bs) = x.2 ++ aflat bs := List.flatMap_cons ..

@[simp] theorem aflat_append (bs cs : List (ABlock V Y J)) :
    aflat (bs ++ cs) = aflat bs ++ aflat cs := List.flatMap_append ..

theorem aflat_flatten_replicate (n : ℕ) (bs : List (ABlock V Y J)) :
    aflat (List.replicate n bs).flatten = (List.replicate n (aflat bs)).flatten := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.replicate_succ, List.flatten_cons, aflat_append, ih, List.replicate_succ,
        List.flatten_cons]

theorem aflat_ainv (bs : List (ABlock V Y J)) : aflat (ainv bs) = ninv (aflat bs) := by
  induction bs with
  | nil => rfl
  | cons x bs ih =>
      simp only [ainv, List.map_cons, List.reverse_cons] at ih ⊢
      rw [aflat_append, ih, aflat_cons, aflat_nil, List.append_nil, aflat_cons, ninv_append]

theorem flipTag_beq (t : Option (Bool × Bool)) (b adj : Bool) :
    (flipTag t == some (b, adj)) = (t == some (b, !adj)) := by
  rcases t with _ | ⟨b', a'⟩
  · simp [flipTag]
  · cases b' <;> cases a' <;> cases b <;> cases adj <;> simp [flipTag]

theorem nexec_ainv (b adj : Bool) (bs : List (ABlock V Y J)) :
    nexec b adj (ainv bs) = nexec b (!adj) bs := by
  simp only [nexec, ainv, List.countP_reverse, List.countP_map, Function.comp_def, flipTag_beq]

@[simp] theorem nexec_nil (b adj : Bool) : nexec b adj ([] : List (ABlock V Y J)) = 0 := rfl

theorem nexec_cons (b adj : Bool) (x : ABlock V Y J) (bs : List (ABlock V Y J)) :
    nexec b adj (x :: bs) = nexec b adj bs + if x.1 = some (b, adj) then 1 else 0 := by
  simp only [nexec, List.countP_cons, beq_iff_eq]

theorem nexec_append (b adj : Bool) (bs cs : List (ABlock V Y J)) :
    nexec b adj (bs ++ cs) = nexec b adj bs + nexec b adj cs := List.countP_append ..

theorem nexec_flatten_replicate (b adj : Bool) (n : ℕ) (bs : List (ABlock V Y J)) :
    nexec b adj (List.replicate n bs).flatten = n * nexec b adj bs := by
  induction n with
  | zero => simp [nexec]
  | succ n ih =>
      rw [List.replicate_succ, List.flatten_cons, nexec_append, ih]
      ring

@[simp] theorem nexec_none (b adj : Bool) (l : List (NInstr V Y J)) :
    nexec b adj [((none : Option (Bool × Bool)), l)] = 0 := by
  simp [nexec]

theorem aerase_append (bs cs : List (ABlock V Y J)) :
    aerase (bs ++ cs) = aerase bs ++ aerase cs := List.map_append ..

theorem aerase_flatten_replicate (n : ℕ) (bs : List (ABlock V Y J)) :
    aerase (List.replicate n bs).flatten = (List.replicate n (aerase bs)).flatten := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.replicate_succ, List.flatten_cons, aerase_append, ih, List.replicate_succ,
        List.flatten_cons]

@[simp] theorem aerase_none (l : List (NInstr V Y J)) :
    aerase [((none : Option (Bool × Bool)), l)] = [(none, l)] := rfl

theorem aerase_ainv (bs : List (ABlock V Y J)) : aerase (ainv bs) = ainv (aerase bs) := by
  unfold aerase ainv
  rw [List.map_reverse, List.map_map, List.map_map]
  congr 1
  apply List.map_congr_left
  rintro ⟨t, l⟩ -
  rcases t with _ | ⟨b, a⟩ <;> simp [flipTag, ninv]

theorem annotOK_append {src : Bool → Bool → List (NInstr V Y J)} {bs cs : List (ABlock V Y J)}
    (h₁ : AnnotOK src bs) (h₂ : AnnotOK src cs) : AnnotOK src (bs ++ cs) := by
  intro x hx
  rcases List.mem_append.mp hx with h | h
  · exact h₁ x h
  · exact h₂ x h

theorem annotOK_none (src : Bool → Bool → List (NInstr V Y J)) (l : List (NInstr V Y J)) :
    AnnotOK src [((none : Option (Bool × Bool)), l)] := by
  intro x hx b adj ht
  rw [List.mem_singleton] at hx
  subst hx
  cases ht

theorem annotOK_flatten_replicate {src : Bool → Bool → List (NInstr V Y J)}
    {bs : List (ABlock V Y J)} (h : AnnotOK src bs) (n : ℕ) :
    AnnotOK src (List.replicate n bs).flatten := by
  intro x hx
  obtain ⟨l, hl, hxl⟩ := List.mem_flatten.mp hx
  rw [List.eq_of_mem_replicate hl] at hxl
  exact h x hxl

theorem annotOK_ainv {src : Bool → Bool → List (NInstr V Y J)} {bs : List (ABlock V Y J)}
    (h : AnnotOK src bs) (hinv : ∀ b adj, ninv (src b adj) = src b (!adj)) :
    AnnotOK src (ainv bs) := by
  intro x hx b adj hxt
  simp only [ainv, List.mem_reverse, List.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  rcases hyt : y.1 with _ | ⟨b', a'⟩
  · simp [flipTag, hyt] at hxt
  · simp only [flipTag, hyt, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hxt
    obtain ⟨rfl, rfl⟩ := hxt
    simp only
    rw [h y hy b' a' hyt, hinv]

/-- **The calls of an annotated program**: the calls of its other blocks plus, for every
`(b, adj)`, the number of executions times the calls of `src b adj`. -/
theorem nCallsN_aflat (p : J → Bool) (src : Bool → Bool → List (NInstr V Y J))
    (bs : List (ABlock V Y J)) (h : AnnotOK src bs) :
    nCallsN p (aflat bs) = nCallsN p (aflat (aerase bs)) +
      ∑ b : Bool, ∑ adj : Bool, nexec b adj bs * nCallsN p (src b adj) := by
  induction bs with
  | nil => simp [aerase, nCallsN]
  | cons x bs ih =>
      have h' : AnnotOK src bs := fun y hy => h y (List.mem_cons_of_mem x hy)
      rw [aflat_cons, nCallsN_append, ih h']
      rcases x with ⟨t, l⟩
      rcases t with _ | ⟨b₀, a₀⟩
      · simp only [aerase, List.map_cons, aflat_cons, nCallsN_append, nexec_cons,
          reduceCtorEq, if_false, add_zero, Option.isSome_none, Bool.false_eq_true]
        ring
      · have hl : l = src b₀ a₀ := h (some (b₀, a₀), l) List.mem_cons_self b₀ a₀ rfl
        subst hl
        simp only [aerase, List.map_cons, aflat_cons, nCallsN_append, nexec_cons,
          Option.isSome_some, if_true, Option.some.injEq, Prod.mk.injEq]
        simp only [Fintype.sum_bool]
        cases b₀ <;> cases a₀ <;> simp [nCallsN] <;> ring

/-- **The gates of an annotated program**: the gates of its other blocks plus, for every
`(b, adj)`, the number of executions times the gates of `src b adj`. -/
theorem nGatesN_aflat (src : Bool → Bool → List (NInstr V Y J)) (bs : List (ABlock V Y J))
    (h : AnnotOK src bs) :
    nGatesN (aflat bs) = nGatesN (aflat (aerase bs)) +
      ∑ b : Bool, ∑ adj : Bool, nexec b adj bs * nGatesN (src b adj) := by
  induction bs with
  | nil => simp [aerase, nGatesN]
  | cons x bs ih =>
      have h' : AnnotOK src bs := fun y hy => h y (List.mem_cons_of_mem x hy)
      rw [aflat_cons, nGatesN_append, ih h']
      rcases x with ⟨t, l⟩
      rcases t with _ | ⟨b₀, a₀⟩
      · simp only [aerase, List.map_cons, aflat_cons, nGatesN_append, nexec_cons,
          reduceCtorEq, if_false, add_zero, Option.isSome_none, Bool.false_eq_true]
        ring
      · have hl : l = src b₀ a₀ := h (some (b₀, a₀), l) List.mem_cons_self b₀ a₀ rfl
        subst hl
        simp only [aerase, List.map_cons, aflat_cons, nGatesN_append, nexec_cons,
          Option.isSome_some, if_true, Option.some.injEq, Prod.mk.injEq]
        simp only [Fintype.sum_bool]
        cases b₀ <;> cases a₀ <;> simp [nGatesN] <;> ring

/-! #### Annotations of macro expansions -/

/-- The annotated macro expansion of a released program. -/
def annotOf {S O : Type*} (μ : OInstr S O → List (NInstr V Y J)) (rel : List (OInstr S O)) :
    List (ABlock V Y J) :=
  rel.map fun i => (srcTag i, μ i)

/-- **The annotation evaluates to the macro expansion.** -/
theorem aflat_annotOf {S O : Type*} (μ : OInstr S O → List (NInstr V Y J))
    (rel : List (OInstr S O)) : aflat (annotOf μ rel) = rel.flatMap μ := by
  induction rel with
  | nil => rfl
  | cons i rel ih => rw [annotOf, List.map_cons, aflat_cons, ← annotOf, ih, List.flatMap_cons]

theorem annotOK_annotOf {S O : Type*} (μ : OInstr S O → List (NInstr V Y J))
    (src : Bool → Bool → List (NInstr V Y J)) (hμ : ∀ b adj, μ (.src b adj) = src b adj)
    (rel : List (OInstr S O)) : AnnotOK src (annotOf μ rel) := by
  intro x hx b adj hxt
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
  cases i with
  | src b' adj' =>
      simp only [srcTag, Option.some.injEq, Prod.mk.injEq] at hxt
      obtain ⟨rfl, rfl⟩ := hxt
      exact hμ _ _
  | _ => cases hxt

/-- **The executions recorded by the annotation are the released source uses**:
`nexec b false + nexec b true = nSrc b`. -/
theorem nexec_annotOf {S O : Type*} (μ : OInstr S O → List (NInstr V Y J))
    (rel : List (OInstr S O)) (b : Bool) :
    nexec b false (annotOf μ rel) + nexec b true (annotOf μ rel) = GateODE.nSrc b rel := by
  induction rel with
  | nil => rfl
  | cons i rel ih =>
      rw [annotOf, List.map_cons, nexec_cons, nexec_cons, ← annotOf]
      simp only [GateODE.nSrc, List.countP_cons] at ih ⊢
      rw [← ih]
      cases i with
      | src b' adj' =>
          cases b' <;> cases adj' <;> cases b <;> simp [srcTag, OInstr.isSrc] <;> ring
      | _ => simp [srcTag, OInstr.isSrc]

/-- Emptying the source blocks of a macro expansion is the expansion with the empty source
macros, when the other macros do not depend on the source circuits. -/
theorem aerase_annotOf {S O : Type*} (μ μ' : OInstr S O → List (NInstr V Y J))
    (h₁ : ∀ i, srcTag i = none → μ' i = μ i) (h₂ : ∀ b adj, μ' (.src b adj) = [])
    (rel : List (OInstr S O)) : aerase (annotOf μ rel) = annotOf μ' rel := by
  unfold aerase annotOf
  rw [List.map_map]
  apply List.map_congr_left
  intro i _
  cases i with
  | src b adj => simp [srcTag, h₂]
  | gate g => simp [srcTag, h₁ (.gate g) rfl]
  | uj cs adj => simp [srcTag, h₁ (.uj cs adj) rfl]
  | priv cs adj => simp [srcTag, h₁ (.priv cs adj) rfl]
  | seed cs => simp [srcTag, h₁ (.seed cs) rfl]

end Annot

/-! ### Annotated trials -/

section Trials

variable {a m r K k l f : ℕ} {S Zs Z Y J : Type*} {nP bT bP A : ℕ}
variable [Fintype S] [Fintype Zs] [Fintype Z]

/-- **The annotated amplification step**: good reflection, annotated inverse preparation, seed
reflection, annotated preparation, global sign. -/
def astep (bs : List (ABlock (HWO a m r K k l f S Zs nP Z bT bP A) Y J)) :
    List (ABlock (HWO a m r K k l f S Zs nP Z bT bP A) Y J) :=
  [(none, nGatesOf rgoodNG)] ++ ainv bs ++ [(none, nGatesOf rseedNG)] ++ bs ++
    [(none, [NInstr.gate negGateN])]

/-- **The annotated trial** with `j` amplification steps. -/
def atrial (bs : List (ABlock (HWO a m r K k l f S Zs nP Z bT bP A) Y J)) (j : ℕ) :
    List (ABlock (HWO a m r K k l f S Zs nP Z bT bP A) Y J) :=
  bs ++ (List.replicate j (astep bs)).flatten

theorem aflat_astep (bs : List (ABlock (HWO a m r K k l f S Zs nP Z bT bP A) Y J)) :
    aflat (astep bs) = stepN (aflat bs) := by
  simp only [astep, stepN, aflat_append, aflat_ainv, aflat_cons, aflat_nil, List.append_nil]

/-- **The annotated trial is the actual native trial**: the same list of instructions. -/
theorem aflat_atrial (bs : List (ABlock (HWO a m r K k l f S Zs nP Z bT bP A) Y J)) (j : ℕ) :
    aflat (atrial bs j) = trialN (aflat bs) j := by
  rw [atrial, trialN, aflat_append, aflat_flatten_replicate, aflat_astep]

theorem nexec_astep (b adj : Bool) (bs : List (ABlock (HWO a m r K k l f S Zs nP Z bT bP A) Y J)) :
    nexec b adj (astep bs) = nexec b (!adj) bs + nexec b adj bs := by
  simp only [astep, nexec_append, nexec_ainv, nexec_none]
  ring

/-- **A trial with `j` steps** executes `(b, adj)` once per preparation and `(b, !adj)` once per
inverse preparation. -/
theorem nexec_atrial (b adj : Bool) (bs : List (ABlock (HWO a m r K k l f S Zs nP Z bT bP A) Y J))
    (j : ℕ) :
    nexec b adj (atrial bs j) = nexec b adj bs + j * (nexec b (!adj) bs + nexec b adj bs) := by
  rw [atrial, nexec_append, nexec_flatten_replicate, nexec_astep]

/-- Counting both orientations, a trial with `j` steps executes each source circuit `2j + 1` times
per execution in the preparation. -/
theorem nexec_atrial_both (b : Bool) (bs : List (ABlock (HWO a m r K k l f S Zs nP Z bT bP A) Y J))
    (j : ℕ) :
    nexec b false (atrial bs j) + nexec b true (atrial bs j) =
      (2 * j + 1) * (nexec b false bs + nexec b true bs) := by
  rw [nexec_atrial, nexec_atrial]
  simp only [Bool.not_false, Bool.not_true]
  ring

theorem aerase_astep (bs : List (ABlock (HWO a m r K k l f S Zs nP Z bT bP A) Y J)) :
    aerase (astep bs) = astep (aerase bs) := by
  simp only [astep, aerase_append, aerase_ainv, aerase_none]

theorem aerase_atrial (bs : List (ABlock (HWO a m r K k l f S Zs nP Z bT bP A) Y J)) (j : ℕ) :
    aerase (atrial bs j) = atrial (aerase bs) j := by
  rw [atrial, atrial, aerase_append, aerase_flatten_replicate, aerase_astep]

theorem annotOK_atrial {src : Bool → Bool → List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J)}
    {bs : List (ABlock (HWO a m r K k l f S Zs nP Z bT bP A) Y J)} (h : AnnotOK src bs)
    (hinv : ∀ b adj, ninv (src b adj) = src b (!adj)) (j : ℕ) : AnnotOK src (atrial bs j) := by
  refine annotOK_append h (annotOK_flatten_replicate ?_ j)
  exact annotOK_append (annotOK_append (annotOK_append (annotOK_append (annotOK_none _ _)
    (annotOK_ainv h hinv)) (annotOK_none _ _)) h) (annotOK_none _ _)

end Trials

/-! ### Counts along the histories of the four-attempt protocol -/

section History

open SparseHamiltonian.ODERepeatProtocol

variable {E K X L : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {O : L → X → K →L[ℂ] K}

/-- **A per-trial count summed along a completed history**: `f j` for every trial of the history,
`j` its drawn number of steps. -/
def labelCount (f : ℕ → ℕ) : {p : Protocol O E} → Protocol.History p → ℕ
  | _, .abort => 0
  | _, .success _ _ j => f j.val
  | _, .failure _ _ j tail => f j.val + labelCount f tail

theorem labelCount_decomp (F : ℕ → ℕ) (G : Bool → Bool → ℕ → ℕ) (c : Bool → Bool → ℕ)
    {p : Protocol O E} (h : Protocol.History p) :
    labelCount (fun j => F j + ∑ b : Bool, ∑ adj : Bool, G b adj j * c b adj) h =
      labelCount F h + ∑ b : Bool, ∑ adj : Bool, labelCount (G b adj) h * c b adj := by
  induction h with
  | abort => simp [labelCount]
  | success t k j => simp [labelCount]
  | failure t k j tail ih =>
      simp only [labelCount]
      rw [ih]
      simp only [Fintype.sum_bool]
      ring

theorem labelCount_add (f g : ℕ → ℕ) {p : Protocol O E} (h : Protocol.History p) :
    labelCount (fun j => f j + g j) h = labelCount f h + labelCount g h := by
  induction h with
  | abort => rfl
  | success t k j => rfl
  | failure t k j tail ih =>
      simp only [labelCount, ih]
      ring

/-- Along every history of the repeated trials of `ofCircuits q …`, the cost is the sum of the
costs of the drawn trials. -/
theorem cost_eq_labelCount (q : ℕ → MultiOracleCircuit.Program O) (M : ℕ) (hM : 0 < M)
    (ψ : K) (hψ : ‖ψ‖ = 1) (F : E →L[ℂ] K) (hF : F† ∘L F = 1) (w : L → ℕ) :
    ∀ (r : ℕ) (h : Protocol.History (Protocol.repeatTrials (ofCircuits q M hM ψ hψ F hF) r)),
      h.cost w = labelCount (fun j => (q j).cost w) h := by
  intro r
  induction r with
  | zero =>
      intro h
      cases h
      rfl
  | succ r ih =>
      intro h
      cases h with
      | success _ _ j => rfl
      | failure _ _ j tail =>
          simp only [Protocol.History.cost, labelCount, ih tail]
          rfl

/-- **Every history of `r` repeated trials**: a per-trial count bounded by `B` sums to at most
`r B`. -/
theorem labelCount_le (t : TrialFamily O E) (f : ℕ → ℕ) (B : ℝ)
    (hf : ∀ j : Fin t.choices, (f j.val : ℝ) ≤ B) :
    ∀ (r : ℕ) (h : Protocol.History (Protocol.repeatTrials t r)), (labelCount f h : ℝ) ≤ r * B := by
  have hB : 0 ≤ B := (Nat.cast_nonneg _).trans (hf ⟨0, t.choices_pos⟩)
  intro r
  induction r with
  | zero =>
      intro h
      cases h
      simp [labelCount]
  | succ r ih =>
      intro h
      cases h with
      | success _ _ j =>
          have h1 := hf j
          have h2 := mul_nonneg (Nat.cast_nonneg r) hB
          simp only [labelCount]
          push_cast
          linarith
      | failure _ _ j tail =>
          have h1 := hf j
          have h2 := ih tail
          simp only [labelCount]
          push_cast
          linarith

end History

/-! ### Histories of the native protocol -/

section NativeHistory

open SparseHamiltonian.ODERepeatProtocol

variable {a m r K k l f : ℕ} {S Zs Z Y J : Type*} {nP bT bP A : ℕ}
variable [Fintype S] [DecidableEq S] [Fintype Zs] [DecidableEq Zs] [Fintype Z] [DecidableEq Z]
  [Fintype Y] [DecidableEq Y]

/-- **Executions of source circuit `b`** (both orientations) along a history, read from the
annotated trials. -/
def srcExecs (bs : List (ABlock (HWO a m r K k l f S Zs nP Z bT bP A) Y J)) (b : Bool)
    {p : Protocol (nfamily (V := HWO a m r K k l f S Zs nP Z bT bP A) (Y := Y) (J := J))
      (Reg S ℂ)} (h : Protocol.History p) : ℕ :=
  labelCount (fun j => nexec b false (atrial bs j) + nexec b true (atrial bs j)) h

/-- **The propagation part** of a weight along a history: the weight of the same drawn trials of
the native protocol with preparation `prepN'` (the preparation with empty source circuits). -/
def propCount (prepN' : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J))
    (w : NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J → ℕ)
    {p : Protocol (nfamily (V := HWO a m r K k l f S Zs nP Z bT bP A) (Y := Y) (J := J))
      (Reg S ℂ)} (h : Protocol.History p) : ℕ :=
  labelCount (fun j => (nprogram prepN' j).cost w) h

theorem nhistory_cost (prepN : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J)) (g : ℝ)
    (hg : 1 ≤ g) (w : NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J → ℕ)
    (h : Protocol.History (nprotocol prepN g hg)) :
    h.cost w = labelCount (fun j => (nprogram prepN j).cost w) h :=
  cost_eq_labelCount (nprogram prepN) _ _ _ _ _ _ w 4 h

/-- **The calls along every history of the native protocol**: the propagation calls plus, for every
`(b, adj)`, the executions times the calls of `src b adj`. -/
theorem nhistory_calls (bs : List (ABlock (HWO a m r K k l f S Zs nP Z bT bP A) Y J))
    (src : Bool → Bool → List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J))
    {prepN : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J)} (hflat : aflat bs = prepN)
    (hok : AnnotOK src bs) (hinv : ∀ b adj, ninv (src b adj) = src b (!adj)) (g : ℝ)
    (hg : 1 ≤ g) (c : J → Bool) (h : Protocol.History (nprotocol prepN g hg)) :
    h.cost (wCallN c) = propCount (aflat (aerase bs)) (wCallN c) h +
      ∑ b : Bool, ∑ adj : Bool,
        labelCount (fun j => nexec b adj (atrial bs j)) h * nCallsN c (src b adj) := by
  subst hflat
  rw [nhistory_cost]
  have e : ∀ j, (nprogram (aflat bs) j).cost (wCallN c) =
      (nprogram (aflat (aerase bs)) j).cost (wCallN c) +
        ∑ b : Bool, ∑ adj : Bool, nexec b adj (atrial bs j) * nCallsN c (src b adj) := by
    intro j
    rw [nprogram, nprogram, (ntoProgram_counts _ c).2, (ntoProgram_counts _ c).2, ← aflat_atrial,
      nCallsN_aflat c src _ (annotOK_atrial hok hinv j), aerase_atrial, aflat_atrial]
  simp only [e]
  exact labelCount_decomp _ _ _ h

/-- **The gates along every history of the native protocol**: the propagation gates plus, for
every `(b, adj)`, the executions times the gates of `src b adj`. -/
theorem nhistory_gates (bs : List (ABlock (HWO a m r K k l f S Zs nP Z bT bP A) Y J))
    (src : Bool → Bool → List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J))
    {prepN : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J)} (hflat : aflat bs = prepN)
    (hok : AnnotOK src bs) (hinv : ∀ b adj, ninv (src b adj) = src b (!adj)) (g : ℝ)
    (hg : 1 ≤ g) (h : Protocol.History (nprotocol prepN g hg)) :
    h.cost wGateN = propCount (aflat (aerase bs)) wGateN h +
      ∑ b : Bool, ∑ adj : Bool,
        labelCount (fun j => nexec b adj (atrial bs j)) h * nGatesN (src b adj) := by
  subst hflat
  rw [nhistory_cost]
  have e : ∀ j, (nprogram (aflat bs) j).cost wGateN =
      (nprogram (aflat (aerase bs)) j).cost wGateN +
        ∑ b : Bool, ∑ adj : Bool, nexec b adj (atrial bs j) * nGatesN (src b adj) := by
    intro j
    rw [nprogram, nprogram, (ntoProgram_counts _ (fun _ => true)).1,
      (ntoProgram_counts _ (fun _ => true)).1, ← aflat_atrial,
      nGatesN_aflat src _ (annotOK_atrial hok hinv j), aerase_atrial, aflat_atrial]
  simp only [e]
  exact labelCount_decomp _ _ _ h

/-- **The calls along every history, per source circuit**: when the calls of `src b adj` are `κ b`
for both orientations, the calls are the propagation calls plus `∑_b` (executions of `b`) `· κ b`. -/
theorem nhistory_calls_src (bs : List (ABlock (HWO a m r K k l f S Zs nP Z bT bP A) Y J))
    (src : Bool → Bool → List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J))
    {prepN : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J)} (hflat : aflat bs = prepN)
    (hok : AnnotOK src bs) (hinv : ∀ b adj, ninv (src b adj) = src b (!adj)) (g : ℝ)
    (hg : 1 ≤ g) (c : J → Bool) (κ : Bool → ℕ) (hκ : ∀ b adj, nCallsN c (src b adj) = κ b)
    (h : Protocol.History (nprotocol prepN g hg)) :
    h.cost (wCallN c) = propCount (aflat (aerase bs)) (wCallN c) h +
      ∑ b : Bool, srcExecs bs b h * κ b := by
  rw [nhistory_calls bs src hflat hok hinv g hg c h]
  simp only [hκ, Fintype.sum_bool]
  unfold srcExecs
  rw [labelCount_add, labelCount_add]
  ring

/-- **The gates along every history, per source circuit**. -/
theorem nhistory_gates_src (bs : List (ABlock (HWO a m r K k l f S Zs nP Z bT bP A) Y J))
    (src : Bool → Bool → List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J))
    {prepN : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J)} (hflat : aflat bs = prepN)
    (hok : AnnotOK src bs) (hinv : ∀ b adj, ninv (src b adj) = src b (!adj)) (g : ℝ)
    (hg : 1 ≤ g) (κ : Bool → ℕ) (hκ : ∀ b adj, nGatesN (src b adj) = κ b)
    (h : Protocol.History (nprotocol prepN g hg)) :
    h.cost wGateN = propCount (aflat (aerase bs)) wGateN h + ∑ b : Bool, srcExecs bs b h * κ b := by
  rw [nhistory_gates bs src hflat hok hinv g hg h]
  simp only [hκ, Fintype.sum_bool]
  unfold srcExecs
  rw [labelCount_add, labelCount_add]
  ring

/-- **The total calls along a history**: at most the propagation bound `P` plus, per source
circuit, the bound `E b` on its executions times its calls `κ b`. -/
theorem nhistory_calls_le (bs : List (ABlock (HWO a m r K k l f S Zs nP Z bT bP A) Y J))
    (src : Bool → Bool → List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J))
    {prepN prepN' : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J)}
    (hflat : aflat bs = prepN) (herase : aflat (aerase bs) = prepN')
    (hok : AnnotOK src bs) (hinv : ∀ b adj, ninv (src b adj) = src b (!adj)) (g : ℝ)
    (hg : 1 ≤ g) (c : J → Bool) (κ : Bool → ℕ) (hκ : ∀ b adj, nCallsN c (src b adj) = κ b)
    (E : Bool → ℝ) (P : ℝ) (h : Protocol.History (nprotocol prepN g hg))
    (hE : ∀ b, (srcExecs bs b h : ℝ) ≤ E b) (hP : (propCount prepN' (wCallN c) h : ℝ) ≤ P) :
    (h.cost (wCallN c) : ℝ) ≤ P + (E false * κ false + E true * κ true) := by
  rw [nhistory_calls_src bs src hflat hok hinv g hg c κ hκ h, herase, Fintype.sum_bool]
  push_cast
  have h1 := mul_le_mul_of_nonneg_right (hE false) (Nat.cast_nonneg (κ false))
  have h2 := mul_le_mul_of_nonneg_right (hE true) (Nat.cast_nonneg (κ true))
  linarith

/-- **The propagation part is at most the worst-case cost of the protocol with the propagation
preparation**, along every history. -/
theorem propCount_le (prepN prepN' : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J))
    (g : ℝ) (hg : 1 ≤ g) (w : NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J → ℕ)
    (h : Protocol.History (nprotocol prepN g hg)) :
    (propCount prepN' w h : ℝ) ≤ (nprotocol prepN' g hg).worstCost w := by
  set t' := ofCircuits (nprogram prepN') (ODEGroverAverage.chosenIterations g)
    (ODEGroverAverage.chosenIterations_bounds g hg).1 sN norm_sN goodN goodN_isometry
  have key := labelCount_le (ofCircuits (nprogram prepN) (ODEGroverAverage.chosenIterations g)
      (ODEGroverAverage.chosenIterations_bounds g hg).1 sN norm_sN goodN goodN_isometry)
    (fun j => (nprogram prepN' j).cost w) (t'.maxCost w)
    (fun j => Nat.cast_le.mpr (t'.cost_le_maxCost w ⟨j.val, j.isLt⟩)) 4 h
  have hw : (nprotocol prepN' g hg).worstCost w = 4 * t'.maxCost w :=
    Protocol.repeat_worstCost t' 4 w
  unfold propCount
  rw [hw]
  push_cast
  exact key

/-- **The executions along every history**: at most `40 g` times the executions of each source
circuit in the preparation. -/
theorem nhistory_exec_le (bs : List (ABlock (HWO a m r K k l f S Zs nP Z bT bP A) Y J))
    {prepN : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J)} (hflat : aflat bs = prepN)
    (g : ℝ) (hg : 1 ≤ g) (b : Bool) (h : Protocol.History (nprotocol prepN g hg)) :
    (srcExecs bs b h : ℝ) ≤ 40 * g * (nexec b false bs + nexec b true bs) := by
  subst hflat
  have hM := (ODEGroverAverage.chosenIterations_bounds g hg).2.2
  have key : (srcExecs bs b h : ℝ) ≤ 4 * (10 * g * (nexec b false bs + nexec b true bs)) :=
    labelCount_le (ofCircuits (nprogram (aflat bs)) (ODEGroverAverage.chosenIterations g)
      (ODEGroverAverage.chosenIterations_bounds g hg).1 sN norm_sN goodN goodN_isometry)
    (fun j => nexec b false (atrial bs j) + nexec b true (atrial bs j))
    (10 * g * (nexec b false bs + nexec b true bs)) (fun j => by
      have hj : j.val < ODEGroverAverage.chosenIterations g := j.isLt
      have hjM : (j.val : ℝ) + 1 ≤ ODEGroverAverage.chosenIterations g := by exact_mod_cast hj
      have hj1 : 2 * (j.val : ℝ) + 1 ≤ 10 * g := by linarith
      rw [nexec_atrial_both]
      push_cast
      exact mul_le_mul_of_nonneg_right hj1 (by positivity)) 4 h
  linarith

end NativeHistory

/-! ### The source macros -/

section Macros

variable {a m r K k l f : ℕ} {S Zs Z Y J : Type*} {nP bT bP A : ℕ}

theorem ninv_srcMacro (p : GateODE.Params) {bT bP A : ℕ}
    (srcC : Bool → List (NInstr ((Unit ⊕ S) ⊕ Zs) Y J)) [Fintype S] [Fintype Zs] [Fintype Z]
    (b adj : Bool) :
    ninv (srcMacro (Z := Z) (bT := bT) (bP := bP) (A := A) p srcC b adj) =
      srcMacro p srcC b (!adj) := by
  unfold srcMacro
  rw [ninv_map]
  cases adj <;> simp [ninv_ninv]

theorem nCallsN_srcMacro (p : GateODE.Params) {bT bP A : ℕ}
    (srcC : Bool → List (NInstr ((Unit ⊕ S) ⊕ Zs) Y J)) [Fintype S] [Fintype Zs] [Fintype Z]
    (c : J → Bool) (b adj : Bool) :
    nCallsN c (srcMacro (Z := Z) (bT := bT) (bP := bP) (A := A) p srcC b adj) =
      nCallsN c (srcC b) := by
  unfold srcMacro
  rw [nCallsN_map]
  cases adj <;> simp [nCallsN_ninv]

theorem nGatesN_srcMacro (p : GateODE.Params) {bT bP A : ℕ}
    (srcC : Bool → List (NInstr ((Unit ⊕ S) ⊕ Zs) Y J)) [Fintype S] [Fintype Zs] [Fintype Z]
    (b adj : Bool) :
    nGatesN (srcMacro (Z := Z) (bT := bT) (bP := bP) (A := A) p srcC b adj) = nGatesN (srcC b) := by
  unfold srcMacro
  rw [nGatesN_map]
  cases adj <;> simp [nGatesN_ninv]

theorem ninv_tsrcMacro (p : GateODE.Time.TParams) {bT bP A : ℕ}
    (loadC : List (NInstr ((Fin (p.m + 1) ⊕ S) ⊕ Zs) Y J)) (wpC : List (NInstr (Fin (p.m + 1) ⊕ Zs)
        Y J))
    [Fintype S] [Fintype Zs] [Fintype Z] (b adj : Bool) :
    ninv (tsrcMacro (Z := Z) (bT := bT) (bP := bP) (A := A) p loadC wpC b adj) =
      tsrcMacro p loadC wpC b (!adj) := by
  cases b <;> cases adj <;> simp [tsrcMacro, ninv_map, ninv_ninv]

theorem nCallsN_tsrcMacro (p : GateODE.Time.TParams) {bT bP A : ℕ}
    (loadC : List (NInstr ((Fin (p.m + 1) ⊕ S) ⊕ Zs) Y J)) (wpC : List (NInstr (Fin (p.m + 1) ⊕ Zs)
        Y J))
    [Fintype S] [Fintype Zs] [Fintype Z] (c : J → Bool) (b adj : Bool) :
    nCallsN c (tsrcMacro (Z := Z) (bT := bT) (bP := bP) (A := A) p loadC wpC b adj) =
      if b then nCallsN c wpC else nCallsN c loadC := by
  cases b <;> cases adj <;> simp [tsrcMacro, nCallsN_map, nCallsN_ninv]

theorem nGatesN_tsrcMacro (p : GateODE.Time.TParams) {bT bP A : ℕ}
    (loadC : List (NInstr ((Fin (p.m + 1) ⊕ S) ⊕ Zs) Y J)) (wpC : List (NInstr (Fin (p.m + 1) ⊕ Zs)
        Y J))
    [Fintype S] [Fintype Zs] [Fintype Z] (b adj : Bool) :
    nGatesN (tsrcMacro (Z := Z) (bT := bT) (bP := bP) (A := A) p loadC wpC b adj) =
      if b then nGatesN wpC else nGatesN loadC := by
  cases b <;> cases adj <;> simp [tsrcMacro, nGatesN_map, nGatesN_ninv]

end Macros

/-! ### The annotated preparations of the endpoints -/

section Preparations

open SparseHamiltonian.GateBinary
open SparseHamiltonian.GateBinaryODE (Pub SZ4)
open SparseHamiltonian.ZeroTimeGateODE (bprepC BPublicOK0 BZeroCase zrelC zmacro srcRot
  BTPublicOK0 BTZeroCase tzrelC tzmacro)
open SparseHamiltonian.GeneralSparseODE (GPub GPubT liftC)
open SparseHamiltonian.GeneralDecoderODE (prepTI ndTI arTI prepI ndI arI)
open NativeSparseBlockEncoding (Query)

variable {Zs : Type*} [Fintype Zs]

/-- **The annotated preparation of the constant-coefficient solver** (`bprepC`): the released
zero-case assembly `zrelC` or the released preparation `q.params.prepC`, each instruction with its
native macro. -/
def constAnnot (q : Pub) (srcC : Bool → List (NInstr ((Unit ⊕ Fin q.kx) ⊕ Zs) (PY q.kx q.b) Query))
    :
    List (ABlock (NW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A)
      (PY q.kx q.b) Query) :=
  if BZeroCase q then annotOf (zmacro srcC) (zrelC (srcRot q.T q.r₀ q.rb))
  else annotOf (omacro labSel q.UJg q.nd q.ar (srcMacro q.params srcC)) q.params.prepC

theorem aflat_constAnnot [DecidableEq Zs] (q : Pub)
    (srcC : Bool → List (NInstr ((Unit ⊕ Fin q.kx) ⊕ Zs) (PY q.kx q.b) Query)) :
    aflat (constAnnot q srcC) = bprepC q srcC := by
  unfold constAnnot bprepC
  split_ifs
  · rw [aflat_annotOf, ZeroTimeGateODE.zprepC_eq_flatMap]
  · rw [aflat_annotOf]
    rfl

theorem annotOK_constAnnot (q : Pub)
    (srcC : Bool → List (NInstr ((Unit ⊕ Fin q.kx) ⊕ Zs) (PY q.kx q.b) Query)) :
    AnnotOK (srcMacro q.params srcC) (constAnnot q srcC) := by
  unfold constAnnot
  split_ifs
  · exact annotOK_annotOf _ _ (fun _ _ => rfl) _
  · exact annotOK_annotOf _ _ (fun _ _ => rfl) _

theorem aerase_constAnnot (q : Pub)
    (srcC : Bool → List (NInstr ((Unit ⊕ Fin q.kx) ⊕ Zs) (PY q.kx q.b) Query)) :
    aerase (constAnnot q srcC) = constAnnot q (fun _ => []) := by
  unfold constAnnot
  split_ifs
  · refine aerase_annotOf _ _ (fun i hi => ?_) (fun b adj => by cases adj <;> rfl) _
    cases i <;> first | rfl | cases hi
  · refine aerase_annotOf _ _ (fun i hi => ?_) (fun b adj => by cases adj <;> rfl) _
    cases i <;> first | rfl | cases hi

/-- One execution of each source circuit per preparation (both orientations counted). -/
theorem nexec_constAnnot (q : Pub) (hq : BPublicOK0 q)
    (srcC : Bool → List (NInstr ((Unit ⊕ Fin q.kx) ⊕ Zs) (PY q.kx q.b) Query)) (b : Bool) :
    nexec b false (constAnnot q srcC) + nexec b true (constAnnot q srcC) = 1 := by
  unfold constAnnot
  split_ifs with hz
  · rw [nexec_annotOf]
    cases b <;> rfl
  · rw [nexec_annotOf]
    have hp := q.params_ok (ZeroTimeGateODE.bpublicOK_of hq hz)
    exact (q.params.prepC_counts hp.tau_pos.le hp.nu_pos).2.2.1 b

/-- **The annotated preparation of the time-dependent solvers** (`prepTI`, hence `GPubT.prep` and
`prepTD`): the released zero-case assembly `tzrelC` or the released preparation
`q.pub.params.prepC`, each instruction with its native macro. -/
def timeAnnot (q : GPubT) {Y Xa : Type*} [Fintype Xa] [DecidableEq Xa]
    (impl : Query → List (NInstr (PY (q.k + 1) q.b ⊕ Xa) Y Query))
    (loadC : List (NInstr ((Fin (q.m + 1) ⊕ Fin q.k) ⊕ Zs) (Fin q.m ⊕ Y) Query))
    (wpC : List (NInstr (Fin (q.m + 1) ⊕ Zs) (Fin q.m ⊕ Y) Query)) :
    List (ABlock (TNW q.pub.params (Fin (q.k + 1)) Zs (SZ4 (q.k + 1) q.b ⊕ Xa)
      (arTI q Xa).bT (arTI q Xa).bP (arTI q Xa).A) (Fin q.m ⊕ Y) Query) :=
  if BTZeroCase q.pub then annotOf (tzmacro (liftC loadC) wpC) tzrelC
  else annotOf (omacro tlabSel q.pub.UJg (ndTI q impl) (arTI q Xa)
    (tsrcMacro q.pub.params (liftC loadC) wpC)) q.pub.params.prepC

theorem aflat_timeAnnot [DecidableEq Zs] (q : GPubT) {Y Xa : Type*} [Fintype Xa] [DecidableEq Xa]
    (impl : Query → List (NInstr (PY (q.k + 1) q.b ⊕ Xa) Y Query))
    (loadC : List (NInstr ((Fin (q.m + 1) ⊕ Fin q.k) ⊕ Zs) (Fin q.m ⊕ Y) Query))
    (wpC : List (NInstr (Fin (q.m + 1) ⊕ Zs) (Fin q.m ⊕ Y) Query)) :
    aflat (timeAnnot q impl loadC wpC) = prepTI q impl loadC wpC := by
  unfold timeAnnot prepTI
  split_ifs
  · rw [aflat_annotOf, ZeroTimeGateODE.tzprepC_eq_flatMap]
  · rw [aflat_annotOf]
    rfl

theorem annotOK_timeAnnot (q : GPubT) {Y Xa : Type*} [Fintype Xa] [DecidableEq Xa]
    (impl : Query → List (NInstr (PY (q.k + 1) q.b ⊕ Xa) Y Query))
    (loadC : List (NInstr ((Fin (q.m + 1) ⊕ Fin q.k) ⊕ Zs) (Fin q.m ⊕ Y) Query))
    (wpC : List (NInstr (Fin (q.m + 1) ⊕ Zs) (Fin q.m ⊕ Y) Query)) :
    AnnotOK (tsrcMacro q.pub.params (liftC loadC) wpC) (timeAnnot q impl loadC wpC) := by
  unfold timeAnnot
  split_ifs
  · exact annotOK_annotOf _ _ (fun b adj => by cases b <;> cases adj <;> rfl) _
  · exact annotOK_annotOf _ _ (fun _ _ => rfl) _

theorem aerase_timeAnnot (q : GPubT) {Y Xa : Type*} [Fintype Xa] [DecidableEq Xa]
    (impl : Query → List (NInstr (PY (q.k + 1) q.b ⊕ Xa) Y Query))
    (loadC : List (NInstr ((Fin (q.m + 1) ⊕ Fin q.k) ⊕ Zs) (Fin q.m ⊕ Y) Query))
    (wpC : List (NInstr (Fin (q.m + 1) ⊕ Zs) (Fin q.m ⊕ Y) Query)) :
    aerase (timeAnnot q impl loadC wpC) = timeAnnot q impl [] [] := by
  unfold timeAnnot
  split_ifs
  · refine aerase_annotOf _ _ (fun i hi => ?_) (fun b adj => by cases b <;> cases adj <;> rfl) _
    cases i <;> first | rfl | cases hi
  · refine aerase_annotOf _ _ (fun i hi => ?_) (fun b adj => by cases b <;> cases adj <;> rfl) _
    cases i <;> first | rfl | cases hi

/-- One execution of the loading circuit and two of the weight-preparation circuit per
preparation (both orientations counted). -/
theorem nexec_timeAnnot (q : GPubT) (hq : BTPublicOK0 q.pub) {Y Xa : Type*} [Fintype Xa]
    [DecidableEq Xa] (impl : Query → List (NInstr (PY (q.k + 1) q.b ⊕ Xa) Y Query))
    (loadC : List (NInstr ((Fin (q.m + 1) ⊕ Fin q.k) ⊕ Zs) (Fin q.m ⊕ Y) Query))
    (wpC : List (NInstr (Fin (q.m + 1) ⊕ Zs) (Fin q.m ⊕ Y) Query)) :
    nexec false false (timeAnnot q impl loadC wpC) + nexec false true (timeAnnot q impl loadC wpC)
        = 1 ∧
      nexec true false (timeAnnot q impl loadC wpC) +
        nexec true true (timeAnnot q impl loadC wpC) = 2 := by
  unfold timeAnnot
  split_ifs with hz
  · rw [nexec_annotOf, nexec_annotOf]
    exact ⟨rfl, rfl⟩
  · rw [nexec_annotOf, nexec_annotOf]
    have hp := q.pub.params_ok (ZeroTimeGateODE.btpublicOK_of hq hz)
    obtain ⟨-, -, h0, h1, -⟩ := q.pub.params.prepC_counts hp.tau_pos.le hp.nu_pos hp.mesh
    exact ⟨h0, h1⟩

/-- **The annotated preparation of the constant-coefficient general-size solvers** (`prepI`, hence
`GPub.prep` and `prepD` of the decoder solver): `zrelC` or `q.pub.params.prepC`, each instruction
with its native macro, the source circuits on the low wires of the padded system register. -/
def constAnnotI (q : GPub) {Y Xa : Type*} [Fintype Xa] [DecidableEq Xa]
    (impl : Query → List (NInstr (PY (q.k + 1) q.b ⊕ Xa) Y Query))
    (srcC : Bool → List (NInstr ((Unit ⊕ Fin q.k) ⊕ Zs) Y Query)) :
    List (ABlock (NW q.pub.params (Fin (q.k + 1)) Zs (SZ4 (q.k + 1) q.b ⊕ Xa)
      (arI q Xa).bT (arI q Xa).bP (arI q Xa).A) Y Query) :=
  if BZeroCase q.pub then annotOf (zmacro (fun c => liftC (srcC c))) (zrelC (srcRot q.T q.r₀ q.rb))
  else annotOf (omacro labSel q.pub.UJg (ndI q impl) (arI q Xa)
    (srcMacro q.pub.params (fun c => liftC (srcC c)))) q.pub.params.prepC

theorem aflat_constAnnotI [DecidableEq Zs] (q : GPub) {Y Xa : Type*} [Fintype Xa] [DecidableEq Xa]
    (impl : Query → List (NInstr (PY (q.k + 1) q.b ⊕ Xa) Y Query))
    (srcC : Bool → List (NInstr ((Unit ⊕ Fin q.k) ⊕ Zs) Y Query)) :
    aflat (constAnnotI q impl srcC) = prepI q impl srcC := by
  unfold constAnnotI prepI
  split_ifs
  · rw [aflat_annotOf, ZeroTimeGateODE.zprepC_eq_flatMap]
  · rw [aflat_annotOf]
    rfl

theorem annotOK_constAnnotI (q : GPub) {Y Xa : Type*} [Fintype Xa] [DecidableEq Xa]
    (impl : Query → List (NInstr (PY (q.k + 1) q.b ⊕ Xa) Y Query))
    (srcC : Bool → List (NInstr ((Unit ⊕ Fin q.k) ⊕ Zs) Y Query)) :
    AnnotOK (srcMacro q.pub.params (fun c => liftC (srcC c))) (constAnnotI q impl srcC) := by
  unfold constAnnotI
  split_ifs
  · exact annotOK_annotOf _ _ (fun _ _ => rfl) _
  · exact annotOK_annotOf _ _ (fun _ _ => rfl) _

theorem aerase_constAnnotI (q : GPub) {Y Xa : Type*} [Fintype Xa] [DecidableEq Xa]
    (impl : Query → List (NInstr (PY (q.k + 1) q.b ⊕ Xa) Y Query))
    (srcC : Bool → List (NInstr ((Unit ⊕ Fin q.k) ⊕ Zs) Y Query)) :
    aerase (constAnnotI q impl srcC) = constAnnotI q impl (fun _ => []) := by
  unfold constAnnotI
  split_ifs
  · refine aerase_annotOf _ _ (fun i hi => ?_) (fun b adj => by cases adj <;> rfl) _
    cases i <;> first | rfl | cases hi
  · refine aerase_annotOf _ _ (fun i hi => ?_) (fun b adj => by cases adj <;> rfl) _
    cases i <;> first | rfl | cases hi

/-- One execution of each source circuit per preparation (both orientations counted). -/
theorem nexec_constAnnotI (q : GPub) (hq : BPublicOK0 q.pub) {Y Xa : Type*} [Fintype Xa]
    [DecidableEq Xa] (impl : Query → List (NInstr (PY (q.k + 1) q.b ⊕ Xa) Y Query))
    (srcC : Bool → List (NInstr ((Unit ⊕ Fin q.k) ⊕ Zs) Y Query)) (b : Bool) :
    nexec b false (constAnnotI q impl srcC) + nexec b true (constAnnotI q impl srcC) = 1 := by
  unfold constAnnotI
  split_ifs with hz
  · rw [nexec_annotOf]
    cases b <;> rfl
  · rw [nexec_annotOf]
    have hp := q.pub.params_ok (ZeroTimeGateODE.bpublicOK_of hq hz)
    exact (q.pub.params.prepC_counts hp.tau_pos.le hp.nu_pos).2.2.1 b

end Preparations

/-! ### The endpoints -/

section Endpoints

open ContinuousLinearMap SparseHamiltonian.GateBinary SparseHamiltonian.GateBitBudget
  SparseHamiltonian.GeneralSparseAccess
open SparseHamiltonian.GateBinaryODE (Pub mLift SZ4)
open SparseHamiltonian.ZeroTimeGateODE (bprepC BPublicOK0 BZeroCase BTPublicOK0 BTZeroCase)
open SparseHamiltonian.GeneralSparseODE (GPubT liftC nCallsN_liftC nGatesN_liftC)
open SparseHamiltonian.GeneralDecoderODE (BinDecode DW prepTD prepTI implDP prepD)
open NativeSparseBlockEncoding (Data Query)

set_option maxHeartbeats 8000000 in
/-- **Source executions of Theorem `ode:thm:gates`, constant coefficients** (`ode_thm_gates`). For
the protocol `nprotocol (bprepC (odePub …) srcC) ḡ` of `ode_thm_gates` (fixed before the
instance): the annotation `constAnnot` evaluates to its preparation and to each of its trials
(the same instruction lists), every annotated execution is the placed supplied circuit or its
literal inverse, and along **every** history (early success, four failures, zero time or a known
zero generator included):

* at most `40 ḡ` executions of each source circuit `srcC c` (both orientations);
* the calls of every oracle kind are the propagation calls (those of the same trials with empty
  source circuits) plus the executions times the calls inside each source circuit; the
  propagation calls are at most `C ḡ q` per selected kind (none if `T = 0` or `η_H + η_D = 0`),
  and in total at most that plus `40 ḡ` times the calls inside each source circuit (the source
  calls are kept when the propagation calls vanish);
* the gates are the propagation gates (at most `C ḡ (q (𝔟 + 1)³ + A_src)`) plus the executions
  times the gates of each source circuit.

`C` is the constant of `ode_thm_gates`. -/
theorem ode_thm_gates_sources :
    ∃ C : ℝ, 0 < C ∧
      ∀ {X : Type u} {n : Type v} [Fintype n] [DecidableEq n] {s k b : ℕ}
        (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (sb bd : ℕ)
        (c0 etaH etaD T gbar ε r₀ rb : ℝ)
        (hF : formal_binaryInput D en sb c0) (_ : comp_bits b bd [c0, T, etaH, etaD])
        (hnd : formal_nondegenerate gbar (r₀ + T * rb))
        {Zs : Type} [Fintype Zs] [DecidableEq Zs]
        (srcC : Bool → List (NInstr ((Unit ⊕ Fin k) ⊕ Zs) (PY k b) Query)),
        (∀ c, ∀ i ∈ srcC c, i.Valid) →
        0 ≤ etaH → 0 ≤ etaD → 0 ≤ T → 0 < ε → ε ≤ 1 / 2 → 0 ≤ r₀ → 0 ≤ rb →
        aflat (constAnnot (odePub k sb hF.hsb b c0 etaH etaD T gbar ε r₀ rb) srcC) =
            bprepC (odePub k sb hF.hsb b c0 etaH etaD T gbar ε r₀ rb) srcC ∧
          AnnotOK (srcMacro (odePub k sb hF.hsb b c0 etaH etaD T gbar ε r₀ rb).params srcC)
            (constAnnot (odePub k sb hF.hsb b c0 etaH etaD T gbar ε r₀ rb) srcC) ∧
          (∀ j, aflat (atrial (constAnnot (odePub k sb hF.hsb b c0 etaH etaD T gbar ε r₀ rb)
              srcC) j) =
            trialN (bprepC (odePub k sb hF.hsb b c0 etaH etaD T gbar ε r₀ rb) srcC) j) ∧
          ∀ h : ODERepeatProtocol.Protocol.History
              (nprotocol (bprepC (odePub k sb hF.hsb b c0 etaH etaD T gbar ε r₀ rb) srcC) gbar
                hnd.1),
            (∀ c : Bool, (srcExecs (constAnnot (odePub k sb hF.hsb b c0 etaH etaD T gbar ε r₀ rb)
              srcC) c h : ℝ) ≤ 40 * gbar) ∧
            (∀ c : Query → Bool, h.cost (wCallN c) =
              propCount (bprepC (odePub k sb hF.hsb b c0 etaH etaD T gbar ε r₀ rb)
                (fun _ => ([] : List (NInstr ((Unit ⊕ Fin k) ⊕ Zs) (PY k b) Query)))) (wCallN c) h +
              ∑ c' : Bool, srcExecs (constAnnot (odePub k sb hF.hsb b c0 etaH etaD T gbar ε r₀ rb)
                srcC) c' h * nCallsN c (srcC c')) ∧
            (∀ c : Query → Bool,
              (propCount (bprepC (odePub k sb hF.hsb b c0 etaH etaD T gbar ε r₀ rb)
                (fun _ => ([] : List (NInstr ((Unit ⊕ Fin k) ⊕ Zs) (PY k b) Query)))) (wCallN c) h :
                  ℝ) ≤
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
              propCount (bprepC (odePub k sb hF.hsb b c0 etaH etaD T gbar ε r₀ rb)
                (fun _ => ([] : List (NInstr ((Unit ⊕ Fin k) ⊕ Zs) (PY k b) Query)))) wGateN h +
              ∑ c' : Bool, srcExecs (constAnnot (odePub k sb hF.hsb b c0 etaH etaD T gbar ε r₀ rb)
                srcC) c' h * nGatesN (srcC c') ∧
            (propCount (bprepC (odePub k sb hF.hsb b c0 etaH etaD T gbar ε r₀ rb)
                (fun _ => ([] : List (NInstr ((Unit ⊕ Fin k) ⊕ Zs) (PY k b) Query)))) wGateN h : ℝ)
                    ≤
              C * gbar * (odeShape s T etaH etaD gbar ε *
                (bitB bd (Fintype.card n) 0 0 (odeShape s T etaH etaD gbar ε) gbar ε + 1) ^ 3 +
                Fintype.card Zs) := by
  obtain ⟨C₀, hC₀, H⟩ := ode_thm_gates.{u, v}
  refine ⟨C₀, hC₀, ?_⟩
  intro X n _ _ s k b D en sb bd c0 etaH etaD T gbar ε r₀ rb hF hbits hnd Zs _ _ srcC hsrcV
    hH hD hT hε hε2 hr0 hrb
  obtain ⟨-, hG', -, hC', -⟩ := H D en sb bd c0 etaH etaD T gbar ε r₀ rb hF hbits hnd
    (fun _ => ([] : List (NInstr ((Unit ⊕ Fin k) ⊕ Zs) (PY k b) Query))) (by simp) hH hD hT hε
    hε2 hr0 hrb
  have hq : BPublicOK0 (odePub k sb hF.hsb b c0 etaH etaD T gbar ε r₀ rb) :=
    odePub_ok hF.hsb hF.hb hF.hc0 hH hD hT hnd.1 hε hε2 hr0 hrb hnd.2
  have hflat := aflat_constAnnot (odePub k sb hF.hsb b c0 etaH etaD T gbar ε r₀ rb) srcC
  have hok := annotOK_constAnnot (odePub k sb hF.hsb b c0 etaH etaD T gbar ε r₀ rb) srcC
  have herase : aflat (aerase (constAnnot (odePub k sb hF.hsb b c0 etaH etaD T gbar ε r₀ rb)
      srcC)) = bprepC (odePub k sb hF.hsb b c0 etaH etaD T gbar ε r₀ rb)
      (fun _ => ([] : List (NInstr ((Unit ⊕ Fin k) ⊕ Zs) (PY k b) Query))) := by
    rw [aerase_constAnnot, aflat_constAnnot]
    rfl
  refine ⟨hflat, hok, fun j => (aflat_atrial _ j).trans (congrArg (fun P => trialN P j) hflat),
    fun h => ?_⟩
  have hexec : ∀ c : Bool, (srcExecs (constAnnot (odePub k sb hF.hsb b c0 etaH etaD T gbar ε r₀ rb)
      srcC) c h : ℝ) ≤ 40 * gbar := by
    intro c
    have h1 := nhistory_exec_le _ hflat gbar hnd.1 c h
    have h2 : ((nexec c false (constAnnot (odePub k sb hF.hsb b c0 etaH etaD T gbar ε r₀ rb)
        srcC) : ℝ) + nexec c true (constAnnot (odePub k sb hF.hsb b c0 etaH etaD T gbar ε r₀ rb)
        srcC)) = 1 := by
      exact_mod_cast nexec_constAnnot _ hq srcC c
    rw [h2, mul_one] at h1
    exact h1
  have hprop : ∀ c : Query → Bool,
      (propCount (bprepC (odePub k sb hF.hsb b c0 etaH etaD T gbar ε r₀ rb)
        (fun _ => ([] : List (NInstr ((Unit ⊕ Fin k) ⊕ Zs) (PY k b) Query)))) (wCallN c) h : ℝ) ≤
        if T = 0 ∨ etaH + etaD = 0 then 0 else
          C₀ * gbar * odeShape s T etaH etaD gbar ε *
            ((if c Query.rowLocation then 1 else 0) +
                      (if c Query.columnLocation then 1 else 0) + (if c Query.value then 1 else 0))
                          := by
    intro c
    have h1 := propCount_le (bprepC (odePub k sb hF.hsb b c0 etaH etaD T gbar ε r₀ rb) srcC)
      (bprepC (odePub k sb hF.hsb b c0 etaH etaD T gbar ε r₀ rb)
        (fun _ => ([] : List (NInstr ((Unit ⊕ Fin k) ⊕ Zs) (PY k b) Query)))) gbar hnd.1 (wCallN c)
            h
    have h2 := hC' c
    simp only [nCallsN, List.countP_nil, Nat.cast_zero, add_zero, mul_zero] at h2
    exact h1.trans h2
  refine ⟨hexec, fun c => ?_, hprop, fun c => ?_, ?_, ?_⟩
  · have e := nhistory_calls_src _ _ hflat hok (fun b adj => ninv_srcMacro _ _ b adj) gbar hnd.1 c
      (fun b => nCallsN c (srcC b)) (fun b adj => nCallsN_srcMacro _ _ c b adj) h
    rw [herase] at e
    exact e
  · exact nhistory_calls_le _ _ hflat herase hok (fun b adj => ninv_srcMacro _ _ b adj) gbar hnd.1 c
      (fun b => nCallsN c (srcC b)) (fun b adj => nCallsN_srcMacro _ _ c b adj)
      (fun _ => 40 * gbar) _ h hexec (hprop c)
  · have e := nhistory_gates_src _ _ hflat hok (fun b adj => ninv_srcMacro _ _ b adj) gbar hnd.1
      (fun b => nGatesN (srcC b)) (fun b adj => nGatesN_srcMacro _ _ b adj) h
    rw [herase] at e
    exact e
  · have h1 := propCount_le (bprepC (odePub k sb hF.hsb b c0 etaH etaD T gbar ε r₀ rb) srcC)
      (bprepC (odePub k sb hF.hsb b c0 etaH etaD T gbar ε r₀ rb)
        (fun _ => ([] : List (NInstr ((Unit ⊕ Fin k) ⊕ Zs) (PY k b) Query)))) gbar hnd.1 wGateN h
    simp only [nGatesN, List.countP_nil, Nat.cast_zero, add_zero] at hG'
    exact h1.trans hG'

set_option maxHeartbeats 8000000 in
/-- **Source executions of Theorem `ode:thm:gates`, constant coefficients, binary entry decoder**
(`ode_thm_gates_decoder`): as `ode_thm_gates_sources` for the protocol
`nprotocol (prepD (odePubG …) N dc srcC) ḡ` of that endpoint (annotation `constAnnotI`; the
propagation gates include the decoder cost `dc.cost`). `C` is the constant of
`ode_thm_gates_decoder`. -/
theorem ode_thm_gates_decoder_sources :
    ∃ C : ℝ, 0 < C ∧
      ∀ {X : Type u} {N s k b b' A : ℕ} (D : GeneralSparseAccess.QData X N s k b)
        (dc : BinDecode b b' A) (bd : ℕ) (c0 etaH etaD T gbar ε r₀ rb : ℝ),
        2 ^ k < 2 * N → BinaryEntryDecoding D dc c0 → comp_bits b' bd [c0, T, etaH, etaD] →
        ∀ (hnd : formal_nondegenerate gbar (r₀ + T * rb))
        {Zs : Type} [Fintype Zs] [DecidableEq Zs]
        (srcC : Bool → List (NInstr ((Unit ⊕ Fin k) ⊕ Zs) (PY k b) Query)),
        (∀ c, ∀ i ∈ srcC c, i.Valid) →
        0 ≤ etaH → 0 ≤ etaD → 0 ≤ T → 0 < ε → ε ≤ 1 / 2 → 0 ≤ r₀ → 0 ≤ rb →
        aflat (constAnnotI (odePubG k s D.s_le_pow b' c0 etaH etaD T gbar ε r₀ rb) (implDP (k := k)
            N s (fun _ => false) dc) srcC) = prepD (odePubG k s D.s_le_pow b' c0 etaH etaD T gbar ε
            r₀ rb) N dc srcC ∧
          AnnotOK (srcMacro (odePubG k s D.s_le_pow b' c0 etaH etaD T gbar ε r₀ rb).pub.params (fun
              c => liftC (srcC c))) (constAnnotI (odePubG k s D.s_le_pow b' c0 etaH etaD T gbar ε
              r₀ rb) (implDP (k := k) N s (fun _ => false) dc) srcC) ∧
          (∀ j, aflat (atrial (constAnnotI (odePubG k s D.s_le_pow b' c0 etaH etaD T gbar ε r₀ rb)
              (implDP (k := k) N s (fun _ => false) dc) srcC) j) = trialN (prepD (odePubG k s
              D.s_le_pow b' c0 etaH etaD T gbar ε r₀ rb) N dc srcC) j) ∧
          ∀ h : ODERepeatProtocol.Protocol.History (nprotocol (prepD (odePubG k s D.s_le_pow b' c0
              etaH etaD T gbar ε r₀ rb) N dc srcC) gbar hnd.1),
            (∀ c : Bool, (srcExecs (constAnnotI (odePubG k s D.s_le_pow b' c0 etaH etaD T gbar ε r₀
                rb) (implDP (k := k) N s (fun _ => false) dc) srcC) c h : ℝ) ≤ 40 * gbar) ∧
            (∀ c : Query → Bool, h.cost (wCallN c) =
              propCount (prepD (odePubG k s D.s_le_pow b' c0 etaH etaD T gbar ε r₀ rb) N dc (fun _
                  => ([] : List (NInstr ((Unit ⊕ Fin k) ⊕ Zs) (PY k b) Query)))) (wCallN c) h +
              ∑ c' : Bool, srcExecs (constAnnotI (odePubG k s D.s_le_pow b' c0 etaH etaD T gbar ε
                  r₀ rb) (implDP (k := k) N s (fun _ => false) dc) srcC) c' h * nCallsN c (srcC
                  c')) ∧
            (∀ c : Query → Bool,
              (propCount (prepD (odePubG k s D.s_le_pow b' c0 etaH etaD T gbar ε r₀ rb) N dc (fun _
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
              propCount (prepD (odePubG k s D.s_le_pow b' c0 etaH etaD T gbar ε r₀ rb) N dc (fun _
                  => ([] : List (NInstr ((Unit ⊕ Fin k) ⊕ Zs) (PY k b) Query)))) wGateN h +
              ∑ c' : Bool, srcExecs (constAnnotI (odePubG k s D.s_le_pow b' c0 etaH etaD T gbar ε
                  r₀ rb) (implDP (k := k) N s (fun _ => false) dc) srcC) c' h * nGatesN (srcC c') ∧
            (propCount (prepD (odePubG k s D.s_le_pow b' c0 etaH etaD T gbar ε r₀ rb) N dc (fun _
                => ([] : List (NInstr ((Unit ⊕ Fin k) ⊕ Zs) (PY k b) Query)))) wGateN h : ℝ) ≤
              C * gbar * (odeShape s T etaH etaD gbar ε *
                ((bitB bd N 0 0 (odeShape s T etaH etaD gbar ε) gbar ε + 1) ^ 3 + dc.cost) +
                Fintype.card Zs) := by
  obtain ⟨C₀, hC₀, H⟩ := ode_thm_gates_decoder.{u}
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
  have hflat : aflat (constAnnotI (odePubG k s D.s_le_pow b' c0 etaH etaD T gbar ε r₀ rb) (implDP
      (k := k) N s (fun _ => false) dc) srcC) = prepD (odePubG k s D.s_le_pow b' c0 etaH etaD T
      gbar ε r₀ rb) N dc srcC := by
    rw [aflat_constAnnotI]
    rfl
  have hok := annotOK_constAnnotI (odePubG k s D.s_le_pow b' c0 etaH etaD T gbar ε r₀ rb) (implDP
      (k := k) N s (fun _ => false) dc) srcC
  have herase : aflat (aerase (constAnnotI (odePubG k s D.s_le_pow b' c0 etaH etaD T gbar ε r₀ rb)
      (implDP (k := k) N s (fun _ => false) dc) srcC)) = prepD (odePubG k s D.s_le_pow b' c0 etaH
      etaD T gbar ε r₀ rb) N dc (fun _ => ([] : List (NInstr ((Unit ⊕ Fin k) ⊕ Zs) (PY k b)
      Query))) := by
    rw [aerase_constAnnotI, aflat_constAnnotI]
    rfl
  refine ⟨hflat, hok, fun j => (aflat_atrial _ j).trans (congrArg (fun P => trialN P j) hflat),
    fun h => ?_⟩
  have hexec : ∀ c : Bool, (srcExecs (constAnnotI (odePubG k s D.s_le_pow b' c0 etaH etaD T gbar ε
      r₀ rb) (implDP (k := k) N s (fun _ => false) dc) srcC) c h : ℝ) ≤ 40 * gbar := by
    intro c
    have h1 := nhistory_exec_le _ hflat gbar hnd.1 c h
    have h2 : ((nexec c false (constAnnotI (odePubG k s D.s_le_pow b' c0 etaH etaD T gbar ε r₀ rb)
        (implDP (k := k) N s (fun _ => false) dc) srcC) : ℝ) + nexec c true (constAnnotI (odePubG k
        s D.s_le_pow b' c0 etaH etaD T gbar ε r₀ rb) (implDP (k := k) N s (fun _ => false) dc)
        srcC)) = 1 := by
      exact_mod_cast nexec_constAnnotI _ hq (implDP (k := k) N s (fun _ => false) dc) srcC c
    rw [h2, mul_one] at h1
    exact h1
  have hprop : ∀ c : Query → Bool,
      (propCount (prepD (odePubG k s D.s_le_pow b' c0 etaH etaD T gbar ε r₀ rb) N dc (fun _ => ([]
          : List (NInstr ((Unit ⊕ Fin k) ⊕ Zs) (PY k b) Query)))) (wCallN c) h : ℝ) ≤
        if T = 0 ∨ etaH + etaD = 0 then 0 else
                  C₀ * gbar * odeShape s T etaH etaD gbar ε *
                    ((if c Query.rowLocation then 1 else 0) +
                      (if c Query.columnLocation then 1 else 0) + (if c Query.value then 1 else 0))
                          := by
    intro c
    have h1 := propCount_le (prepD (odePubG k s D.s_le_pow b' c0 etaH etaD T gbar ε r₀ rb) N dc
        srcC) (prepD (odePubG k s D.s_le_pow b' c0 etaH etaD T gbar ε r₀ rb) N dc (fun _ => ([] :
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
  · have h1 := propCount_le (prepD (odePubG k s D.s_le_pow b' c0 etaH etaD T gbar ε r₀ rb) N dc
      srcC) (prepD (odePubG k s D.s_le_pow b' c0 etaH etaD T gbar ε r₀ rb) N dc (fun _ => ([] :
      List (NInstr ((Unit ⊕ Fin k) ⊕ Zs) (PY k b) Query)))) gbar hnd.1 wGateN h
    simp only [nGatesN, List.countP_nil, Nat.cast_zero, add_zero] at hG'
    exact h1.trans hG'

set_option maxHeartbeats 8000000 in
/-- **Source executions of the time-dependent Theorem `ode:thm:gates` with the manuscript's
certificates** (`ode_thm_gates_time_cert`). For the protocol of `ode_thm_gates_time_cert` (fixed
before the instance; preparation `GPubT.prep`, parameter `4ḡ`): the annotation `timeAnnot`
evaluates to its preparation and to each of its trials, every annotated execution is the placed
loading circuit (`b = false`) or weight-preparation circuit (`b = true`), or its literal inverse,
and along every history: at most `160 ḡ` executions of the loading circuit and `320 ḡ` of the
weight-preparation circuit; the calls and gates are the propagation part (the same trials with
empty source circuits; at most `C ḡ q` calls per selected kind, none if `T = 0` or
`η_H + η_D = 0`, and `C ḡ (q (𝔟 + 1)³ + A_src)` gates) plus the executions times the calls and
gates of the loading and weight-preparation circuits; in total at most the propagation bound plus
`160 ḡ Q_load + 320 ḡ Q_wp` calls. `C` is the constant of `ode_thm_gates_time_cert`. -/
theorem ode_thm_gates_time_cert_sources :
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
          aflat (timeAnnot (odePubTG k s D.s_le_pow b c0 etaH etaD T (2 * gbar) ε m) (implP (k :=
              k) (b := b) N s (fun _ => false)) loadC wpC) = (odePubTG k s D.s_le_pow b c0 etaH
              etaD T (2 * gbar) ε m).prep N (fun _ => false) loadC wpC ∧
          AnnotOK (tsrcMacro (odePubTG k s D.s_le_pow b c0 etaH etaD T (2 * gbar) ε m).pub.params
              (liftC loadC) wpC) (timeAnnot (odePubTG k s D.s_le_pow b c0 etaH etaD T (2 * gbar) ε
              m) (implP (k := k) (b := b) N s (fun _ => false)) loadC wpC) ∧
          (∀ j, aflat (atrial (timeAnnot (odePubTG k s D.s_le_pow b c0 etaH etaD T (2 * gbar) ε m)
              (implP (k := k) (b := b) N s (fun _ => false)) loadC wpC) j) = trialN ((odePubTG k s
              D.s_le_pow b c0 etaH etaD T (2 * gbar) ε m).prep N (fun _ => false) loadC wpC) j) ∧
          ∀ h : ODERepeatProtocol.Protocol.History (nprotocol ((odePubTG k s D.s_le_pow b c0 etaH
              etaD T (2 * gbar) ε m).prep N (fun _ => false) loadC wpC) (2 * (2 * gbar))
                (one_le_two_mul (one_le_two_mul hg))),
            (srcExecs (timeAnnot (odePubTG k s D.s_le_pow b c0 etaH etaD T (2 * gbar) ε m) (implP
                (k := k) (b := b) N s (fun _ => false)) loadC wpC) false h : ℝ) ≤ 160 * gbar ∧
            (srcExecs (timeAnnot (odePubTG k s D.s_le_pow b c0 etaH etaD T (2 * gbar) ε m) (implP
                (k := k) (b := b) N s (fun _ => false)) loadC wpC) true h : ℝ) ≤ 320 * gbar ∧
            (∀ c : Query → Bool, h.cost (wCallN c) =
              propCount ((odePubTG k s D.s_le_pow b c0 etaH etaD T (2 * gbar) ε m).prep N (fun _ =>
                  false) ([] : List (NInstr ((Fin (m + 1) ⊕ Fin k) ⊕ Zs) (Fin m ⊕ PY k b) Query))
                  ([] : List (NInstr (Fin (m + 1) ⊕ Zs) (Fin m ⊕ PY k b) Query))) (wCallN c) h +
              ∑ b'' : Bool, srcExecs (timeAnnot (odePubTG k s D.s_le_pow b c0 etaH etaD T (2 *
                  gbar) ε m) (implP (k := k) (b := b) N s (fun _ => false)) loadC wpC) b'' h *
                (if b'' then nCallsN c wpC else nCallsN c loadC)) ∧
            (∀ c : Query → Bool,
              (propCount ((odePubTG k s D.s_le_pow b c0 etaH etaD T (2 * gbar) ε m).prep N (fun _
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
              propCount ((odePubTG k s D.s_le_pow b c0 etaH etaD T (2 * gbar) ε m).prep N (fun _ =>
                  false) ([] : List (NInstr ((Fin (m + 1) ⊕ Fin k) ⊕ Zs) (Fin m ⊕ PY k b) Query))
                  ([] : List (NInstr (Fin (m + 1) ⊕ Zs) (Fin m ⊕ PY k b) Query))) wGateN h +
              ∑ b'' : Bool, srcExecs (timeAnnot (odePubTG k s D.s_le_pow b c0 etaH etaD T (2 *
                  gbar) ε m) (implP (k := k) (b := b) N s (fun _ => false)) loadC wpC) b'' h * (if
                  b'' then nGatesN wpC else nGatesN loadC) ∧
            (propCount ((odePubTG k s D.s_le_pow b c0 etaH etaD T (2 * gbar) ε m).prep N (fun _ =>
                false) ([] : List (NInstr ((Fin (m + 1) ⊕ Fin k) ⊕ Zs) (Fin m ⊕ PY k b) Query)) ([]
                : List (NInstr (Fin (m + 1) ⊕ Zs) (Fin m ⊕ PY k b) Query))) wGateN h : ℝ) ≤
              C * gbar * (odeShape s T etaH etaD gbar ε *
                (bitB bd N (2 ^ m) (2 ^ m) (odeShape s T etaH etaD gbar ε) gbar ε + 1) ^ 3 +
                Fintype.card Zs) := by
  obtain ⟨C₀, hC₀, H⟩ := ode_thm_gates_time_cert.{u}
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
  have hflat : aflat (timeAnnot (odePubTG k s D.s_le_pow b c0 etaH etaD T (2 * gbar) ε m) (implP (k
      := k) (b := b) N s (fun _ => false)) loadC wpC) = (odePubTG k s D.s_le_pow b c0 etaH etaD T
      (2 * gbar) ε m).prep N (fun _ => false) loadC wpC := by
    rw [aflat_timeAnnot]
    rfl
  have hok := annotOK_timeAnnot (odePubTG k s D.s_le_pow b c0 etaH etaD T (2 * gbar) ε m) (implP (k
      := k) (b := b) N s (fun _ => false)) loadC wpC
  have herase : aflat (aerase (timeAnnot (odePubTG k s D.s_le_pow b c0 etaH etaD T (2 * gbar) ε m)
      (implP (k := k) (b := b) N s (fun _ => false)) loadC wpC)) = ((odePubTG k s D.s_le_pow b c0
      etaH etaD T (2 * gbar) ε m).prep N (fun _ => false) ([] : List (NInstr ((Fin (m + 1) ⊕ Fin k)
      ⊕ Zs) (Fin m ⊕ PY k b) Query)) ([] : List (NInstr (Fin (m + 1) ⊕ Zs) (Fin m ⊕ PY k b)
      Query))) := by
    rw [aerase_timeAnnot, aflat_timeAnnot]
    rfl
  obtain ⟨hn0, hn1⟩ := nexec_timeAnnot (odePubTG k s D.s_le_pow b c0 etaH etaD T (2 * gbar) ε m) hq
      (implP (k := k) (b := b) N s (fun _ => false)) loadC wpC
  refine ⟨hflat, hok, fun j => (aflat_atrial _ j).trans (congrArg (fun P => trialN P j) hflat),
    fun h => ?_⟩
  have hexec0 : (srcExecs (timeAnnot (odePubTG k s D.s_le_pow b c0 etaH etaD T (2 * gbar) ε m)
      (implP (k := k) (b := b) N s (fun _ => false)) loadC wpC) false h : ℝ) ≤ 160 * gbar := by
    have h1 := nhistory_exec_le _ hflat _ (one_le_two_mul (one_le_two_mul hg)) false h
    have h2 : ((nexec false false (timeAnnot (odePubTG k s D.s_le_pow b c0 etaH etaD T (2 * gbar) ε
        m) (implP (k := k) (b := b) N s (fun _ => false)) loadC wpC) : ℝ) + nexec false true
        (timeAnnot (odePubTG k s D.s_le_pow b c0 etaH etaD T (2 * gbar) ε m) (implP (k := k) (b :=
        b) N s (fun _ => false)) loadC wpC)) = 1 := by
      exact_mod_cast hn0
    rw [h2] at h1
    exact h1.trans (le_of_eq (by ring))
  have hexec1 : (srcExecs (timeAnnot (odePubTG k s D.s_le_pow b c0 etaH etaD T (2 * gbar) ε m)
      (implP (k := k) (b := b) N s (fun _ => false)) loadC wpC) true h : ℝ) ≤ 320 * gbar := by
    have h1 := nhistory_exec_le _ hflat _ (one_le_two_mul (one_le_two_mul hg)) true h
    have h2 : ((nexec true false (timeAnnot (odePubTG k s D.s_le_pow b c0 etaH etaD T (2 * gbar) ε
        m) (implP (k := k) (b := b) N s (fun _ => false)) loadC wpC) : ℝ) + nexec true true
        (timeAnnot (odePubTG k s D.s_le_pow b c0 etaH etaD T (2 * gbar) ε m) (implP (k := k) (b :=
        b) N s (fun _ => false)) loadC wpC)) = 2 := by
      exact_mod_cast hn1
    rw [h2] at h1
    exact h1.trans (le_of_eq (by ring))
  have hprop : ∀ c : Query → Bool,
      (propCount ((odePubTG k s D.s_le_pow b c0 etaH etaD T (2 * gbar) ε m).prep N (fun _ => false)
          ([] : List (NInstr ((Fin (m + 1) ⊕ Fin k) ⊕ Zs) (Fin m ⊕ PY k b) Query)) ([] : List
          (NInstr (Fin (m + 1) ⊕ Zs) (Fin m ⊕ PY k b) Query))) (wCallN c) h : ℝ) ≤
        if T = 0 ∨ etaH + etaD = 0 then 0 else
                  C₀ * gbar * odeShape s T etaH etaD gbar ε *
                    ((if c Query.rowLocation then 1 else 0) +
                      (if c Query.columnLocation then 1 else 0) + (if c Query.value then 1 else 0))
                          := by
    intro c
    have h1 := propCount_le ((odePubTG k s D.s_le_pow b c0 etaH etaD T (2 * gbar) ε m).prep N (fun
        _ => false) loadC wpC) ((odePubTG k s D.s_le_pow b c0 etaH etaD T (2 * gbar) ε m).prep N
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
  · have h1 := propCount_le ((odePubTG k s D.s_le_pow b c0 etaH etaD T (2 * gbar) ε m).prep N (fun
      _ => false) loadC wpC) ((odePubTG k s D.s_le_pow b c0 etaH etaD T (2 * gbar) ε m).prep N (fun
      _ => false) ([] : List (NInstr ((Fin (m + 1) ⊕ Fin k) ⊕ Zs) (Fin m ⊕ PY k b) Query)) ([] :
      List (NInstr (Fin (m + 1) ⊕ Zs) (Fin m ⊕ PY k b) Query))) _ (one_le_two_mul (one_le_two_mul
      hg)) wGateN h
    simp only [nGatesN, List.countP_nil, Nat.cast_zero, add_zero, mul_zero] at hG'
    exact h1.trans hG'

set_option maxHeartbeats 8000000 in
/-- **Source executions of the time-dependent Theorem `ode:thm:gates` with a binary entry
decoder** (`ode_thm_gates_time_decoder_cert`): as `ode_thm_gates_time_cert_sources` for the
preparation `prepTD` of that endpoint (the propagation gates include the decoder cost
`dc.cost`). -/
theorem ode_thm_gates_time_decoder_cert_sources :
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
          aflat (timeAnnot (odePubTG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar) ε m) (implDP (k :=
              k) N s (fun _ => false) dc) loadC wpC) = prepTD (odePubTG k s D.s_le_pow b' c0 etaH
              etaD T (2 * gbar) ε m) N dc loadC wpC ∧
          AnnotOK (tsrcMacro (odePubTG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar) ε m).pub.params
              (liftC loadC) wpC) (timeAnnot (odePubTG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar) ε
              m) (implDP (k := k) N s (fun _ => false) dc) loadC wpC) ∧
          (∀ j, aflat (atrial (timeAnnot (odePubTG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar) ε m)
              (implDP (k := k) N s (fun _ => false) dc) loadC wpC) j) = trialN (prepTD (odePubTG k
              s D.s_le_pow b' c0 etaH etaD T (2 * gbar) ε m) N dc loadC wpC) j) ∧
          ∀ h : ODERepeatProtocol.Protocol.History (nprotocol (prepTD (odePubTG k s D.s_le_pow b'
              c0 etaH etaD T (2 * gbar) ε m) N dc loadC wpC) (2 * (2 * gbar))
                (one_le_two_mul (one_le_two_mul hg))),
            (srcExecs (timeAnnot (odePubTG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar) ε m) (implDP
                (k := k) N s (fun _ => false) dc) loadC wpC) false h : ℝ) ≤ 160 * gbar ∧
            (srcExecs (timeAnnot (odePubTG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar) ε m) (implDP
                (k := k) N s (fun _ => false) dc) loadC wpC) true h : ℝ) ≤ 320 * gbar ∧
            (∀ c : Query → Bool, h.cost (wCallN c) =
              propCount (prepTD (odePubTG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar) ε m) N dc ([]
                  : List (NInstr ((Fin (m + 1) ⊕ Fin k) ⊕ Zs) (Fin m ⊕ PY k b) Query)) ([] : List
                  (NInstr (Fin (m + 1) ⊕ Zs) (Fin m ⊕ PY k b) Query))) (wCallN c) h +
              ∑ b'' : Bool, srcExecs (timeAnnot (odePubTG k s D.s_le_pow b' c0 etaH etaD T (2 *
                  gbar) ε m) (implDP (k := k) N s (fun _ => false) dc) loadC wpC) b'' h *
                (if b'' then nCallsN c wpC else nCallsN c loadC)) ∧
            (∀ c : Query → Bool,
              (propCount (prepTD (odePubTG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar) ε m) N dc
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
              propCount (prepTD (odePubTG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar) ε m) N dc ([]
                  : List (NInstr ((Fin (m + 1) ⊕ Fin k) ⊕ Zs) (Fin m ⊕ PY k b) Query)) ([] : List
                  (NInstr (Fin (m + 1) ⊕ Zs) (Fin m ⊕ PY k b) Query))) wGateN h +
              ∑ b'' : Bool, srcExecs (timeAnnot (odePubTG k s D.s_le_pow b' c0 etaH etaD T (2 *
                  gbar) ε m) (implDP (k := k) N s (fun _ => false) dc) loadC wpC) b'' h * (if b''
                  then nGatesN wpC else nGatesN loadC) ∧
            (propCount (prepTD (odePubTG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar) ε m) N dc ([]
                : List (NInstr ((Fin (m + 1) ⊕ Fin k) ⊕ Zs) (Fin m ⊕ PY k b) Query)) ([] : List
                (NInstr (Fin (m + 1) ⊕ Zs) (Fin m ⊕ PY k b) Query))) wGateN h : ℝ) ≤
              C * gbar * (odeShape s T etaH etaD gbar ε *
                ((bitB bd N (2 ^ m) (2 ^ m) (odeShape s T etaH etaD gbar ε) gbar ε + 1) ^ 3 +
                  dc.cost) + Fintype.card Zs) := by
  obtain ⟨C₀, hC₀, H⟩ := ode_thm_gates_time_decoder_cert.{u}
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
  have hflat : aflat (timeAnnot (odePubTG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar) ε m) (implDP
      (k := k) N s (fun _ => false) dc) loadC wpC) = prepTD (odePubTG k s D.s_le_pow b' c0 etaH
      etaD T (2 * gbar) ε m) N dc loadC wpC := by
    rw [aflat_timeAnnot]
    rfl
  have hok := annotOK_timeAnnot (odePubTG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar) ε m) (implDP
      (k := k) N s (fun _ => false) dc) loadC wpC
  have herase : aflat (aerase (timeAnnot (odePubTG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar) ε m)
      (implDP (k := k) N s (fun _ => false) dc) loadC wpC)) = (prepTD (odePubTG k s D.s_le_pow b'
      c0 etaH etaD T (2 * gbar) ε m) N dc ([] : List (NInstr ((Fin (m + 1) ⊕ Fin k) ⊕ Zs) (Fin m ⊕
      PY k b) Query)) ([] : List (NInstr (Fin (m + 1) ⊕ Zs) (Fin m ⊕ PY k b) Query))) := by
    rw [aerase_timeAnnot, aflat_timeAnnot]
    rfl
  obtain ⟨hn0, hn1⟩ := nexec_timeAnnot (odePubTG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar) ε m)
      hq (implDP (k := k) N s (fun _ => false) dc) loadC wpC
  refine ⟨hflat, hok, fun j => (aflat_atrial _ j).trans (congrArg (fun P => trialN P j) hflat),
    fun h => ?_⟩
  have hexec0 : (srcExecs (timeAnnot (odePubTG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar) ε m)
      (implDP (k := k) N s (fun _ => false) dc) loadC wpC) false h : ℝ) ≤ 160 * gbar := by
    have h1 := nhistory_exec_le _ hflat _ (one_le_two_mul (one_le_two_mul hg)) false h
    have h2 : ((nexec false false (timeAnnot (odePubTG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar)
        ε m) (implDP (k := k) N s (fun _ => false) dc) loadC wpC) : ℝ) + nexec false true
        (timeAnnot (odePubTG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar) ε m) (implDP (k := k) N s
        (fun _ => false) dc) loadC wpC)) = 1 := by
      exact_mod_cast hn0
    rw [h2] at h1
    exact h1.trans (le_of_eq (by ring))
  have hexec1 : (srcExecs (timeAnnot (odePubTG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar) ε m)
      (implDP (k := k) N s (fun _ => false) dc) loadC wpC) true h : ℝ) ≤ 320 * gbar := by
    have h1 := nhistory_exec_le _ hflat _ (one_le_two_mul (one_le_two_mul hg)) true h
    have h2 : ((nexec true false (timeAnnot (odePubTG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar) ε
        m) (implDP (k := k) N s (fun _ => false) dc) loadC wpC) : ℝ) + nexec true true (timeAnnot
        (odePubTG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar) ε m) (implDP (k := k) N s (fun _ =>
        false) dc) loadC wpC)) = 2 := by
      exact_mod_cast hn1
    rw [h2] at h1
    exact h1.trans (le_of_eq (by ring))
  have hprop : ∀ c : Query → Bool,
      (propCount (prepTD (odePubTG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar) ε m) N dc ([] : List
          (NInstr ((Fin (m + 1) ⊕ Fin k) ⊕ Zs) (Fin m ⊕ PY k b) Query)) ([] : List (NInstr (Fin (m
          + 1) ⊕ Zs) (Fin m ⊕ PY k b) Query))) (wCallN c) h : ℝ) ≤
        if T = 0 ∨ etaH + etaD = 0 then 0 else
                  C₀ * gbar * odeShape s T etaH etaD gbar ε *
                    ((if c Query.rowLocation then 1 else 0) +
                      (if c Query.columnLocation then 1 else 0) + (if c Query.value then 1 else 0))
                          := by
    intro c
    have h1 := propCount_le (prepTD (odePubTG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar) ε m) N dc
        loadC wpC) (prepTD (odePubTG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar) ε m) N dc ([] :
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
  · have h1 := propCount_le (prepTD (odePubTG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar) ε m) N dc
      loadC wpC) (prepTD (odePubTG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar) ε m) N dc ([] : List
      (NInstr ((Fin (m + 1) ⊕ Fin k) ⊕ Zs) (Fin m ⊕ PY k b) Query)) ([] : List (NInstr (Fin (m + 1)
      ⊕ Zs) (Fin m ⊕ PY k b) Query))) _ (one_le_two_mul (one_le_two_mul hg)) wGateN h
    simp only [nGatesN, List.countP_nil, Nat.cast_zero, add_zero, mul_zero] at hG'
    exact h1.trans hG'

end Endpoints

end

end ManuscriptConformance
