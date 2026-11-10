import GeneralSparseAccess.MatOp

/-!
# Substituting implementing circuits for primitive calls

A native circuit `C` on the wires `V` calls primitives `prim'` on a register `Y'`. If every
primitive `j` is implemented by a native circuit `impl j` on its register `Y'` and clean ancillas
`A`, calling the primitives `prim` on a register `Y` and acting as `prim' j` on clean ancillas
(`ImplOK`), and both `prim` and `prim'` are unitary, then the circuit `subst impl C` on `V ⊕ A`,
with every elementary gate renamed onto `V` and every call (or inverse call) replaced by `impl j`
(or its literal inverse) on the wires of the call and the ancillas, acts as `C` on clean ancillas
(`nrun_subst_cleanEmb`). The ancillas are shared by all calls, since each implementation returns
them clean.

* `valid_subst`: the substituted circuit is valid when the implementations are;
* `nGatesN_subst_le`: at most `G` more gates per call when every implementation has at most `G`
  gates;
* `nCallsN_subst_le`: at most `c` calls of each primitive per call of the corresponding one when
  every implementation of `j` makes at most `c` calls, all of primitives of the kind of `j`
  (`KindOK`).
-/

set_option autoImplicit false

namespace SparseHamiltonian.GeneralSparseAccess

noncomputable section
open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
open SparseHamiltonian.OracleCircuit
open SparseHamiltonian.GateODE (overwrite_apply_ι overwrite_apply_out adjIf adjIf_adjoint)
open scoped InnerProduct

section Subst

variable {V Y Y' J J' A : Type*} [Fintype V] [DecidableEq V] [Fintype Y] [DecidableEq Y]
  [Fintype Y'] [DecidableEq Y'] [Fintype A] [DecidableEq A]

/-- The wires of a call and the ancillas, inside the wires of the circuit and the ancillas. -/
def callEmb (pos : Y' ↪ V) : Y' ⊕ A ↪ V ⊕ A :=
  Function.Embedding.sumMap pos (Function.Embedding.refl A)

omit [Fintype V] [DecidableEq V] [Fintype Y'] [DecidableEq Y'] [Fintype A] [DecidableEq A] in
@[simp] theorem callEmb_inl (pos : Y' ↪ V) (y : Y') :
    callEmb (A := A) pos (Sum.inl y) = Sum.inl (pos y) := rfl

omit [Fintype V] [DecidableEq V] [Fintype Y'] [DecidableEq Y'] [Fintype A] [DecidableEq A] in
@[simp] theorem callEmb_inr (pos : Y' ↪ V) (a : A) :
    callEmb (A := A) pos (Sum.inr a) = Sum.inr a := rfl

/-- The implementation of a call: `impl j` for a forward call and its literal inverse for an
inverse call. -/
def implAdj (impl : J' → List (NInstr (Y' ⊕ A) Y J)) (j : J') (adj : Bool) :
    List (NInstr (Y' ⊕ A) Y J) :=
  if adj then ninv (impl j) else impl j

/-- Substitution in one instruction. -/
def substI (impl : J' → List (NInstr (Y' ⊕ A) Y J)) : NInstr V Y' J' → List (NInstr (V ⊕ A) Y J)
  | .gate g => [.gate (GateODE.Gate.map Sum.inl g)]
  | .call j adj pos => (implAdj impl j adj).map (NInstr.map (callEmb pos))

/-- **The substituted circuit**: every elementary gate renamed onto `V`, every call replaced by its
implementation on the wires of the call and the shared ancillas `A`. -/
def subst (impl : J' → List (NInstr (Y' ⊕ A) Y J)) (C : List (NInstr V Y' J')) :
    List (NInstr (V ⊕ A) Y J) :=
  C.flatMap (substI impl)

omit [Fintype V] [DecidableEq V] [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']
  [Fintype A] [DecidableEq A] in
@[simp] theorem subst_nil (impl : J' → List (NInstr (Y' ⊕ A) Y J)) :
    subst impl ([] : List (NInstr V Y' J')) = [] := rfl

omit [Fintype V] [DecidableEq V] [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']
  [Fintype A] [DecidableEq A] in
theorem subst_cons (impl : J' → List (NInstr (Y' ⊕ A) Y J)) (i : NInstr V Y' J')
    (C : List (NInstr V Y' J')) : subst impl (i :: C) = substI impl i ++ subst impl C := by
  simp [subst, List.flatMap_cons]

omit [Fintype V] [DecidableEq V] [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']
  [Fintype A] [DecidableEq A] in
theorem subst_append (impl : J' → List (NInstr (Y' ⊕ A) Y J)) (C C' : List (NInstr V Y' J')) :
    subst impl (C ++ C') = subst impl C ++ subst impl C' := by
  simp [subst, List.flatMap_append]

variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- **An implementation of the primitives `prim'`**: every `impl j` is a valid circuit acting as
`prim' j` on clean ancillas. -/
structure ImplOK (prim : J → Reg Y R →L[ℂ] Reg Y R) (prim' : J' → Reg Y' R →L[ℂ] Reg Y' R)
    (impl : J' → List (NInstr (Y' ⊕ A) Y J)) : Prop where
  valid : ∀ j, ∀ i ∈ impl j, i.Valid
  clean : ∀ j, nrun prim (impl j) ∘L cleanEmb (X := A) = cleanEmb ∘L prim' j

omit [Fintype V] [DecidableEq Y'] [CompleteSpace R] in
/-- The slice of a clean vector along the wires of a call and the ancillas. -/
theorem slice_callEmb_cleanEmb (pos : Y' ↪ V) (ψ : Reg V R) (x : Cfg (V ⊕ A)) :
    slice (callEmb (A := A) pos) (cleanEmb (X := A) ψ) x =
      cleanEmb (X := A) (slice pos ψ (fun v => x (Sum.inl v))) := by
  apply PiLp.ext
  intro c
  rw [slice_apply, cleanEmb_apply, cleanEmb_apply, slice_apply]
  have hr : (fun a => overwrite (callEmb (A := A) pos) x c (Sum.inr a)) = fun a => c (Sum.inr a) :=
    funext fun a => by
      rw [← callEmb_inr (A := A) pos a]
      exact overwrite_apply_ι (callEmb (A := A) pos).injective x c (Sum.inr a)
  have hl : (fun v => overwrite (callEmb (A := A) pos) x c (Sum.inl v)) =
      overwrite pos (fun v => x (Sum.inl v)) (fun y => c (Sum.inl y)) := by
    funext v
    by_cases hv : ∃ y, pos y = v
    · obtain ⟨y, rfl⟩ := hv
      rw [← callEmb_inl (A := A) pos y, overwrite_apply_ι (callEmb (A := A) pos).injective,
        overwrite_apply_ι pos.injective]
    · have h1 : ∀ w, callEmb (A := A) pos w ≠ Sum.inl v := by
        rintro (y | a) h
        · exact hv ⟨y, Sum.inl_injective h⟩
        · cases h
      rw [overwrite_apply_out _ x c _ h1,
        overwrite_apply_out pos _ _ v (fun y hy => hv ⟨y, hy⟩)]
  rw [hr, hl]

/-- **A call replaced by its implementation**: on clean ancillas the implementation on the wires of
the call acts as the primitive on those wires. -/
theorem localOp_callEmb_cleanEmb (pos : Y' ↪ V) (U : Reg (Y' ⊕ A) R →L[ℂ] Reg (Y' ⊕ A) R)
    (P : Reg Y' R →L[ℂ] Reg Y' R) (h : U ∘L cleanEmb (X := A) = cleanEmb ∘L P) :
    localOp (callEmb (A := A) pos) (callEmb pos).injective (fun _ => U) ∘L cleanEmb (X := A) =
      cleanEmb (X := A) ∘L localOp pos pos.injective (fun _ => P) := by
  ext ψ x
  rw [comp_apply, comp_apply, localOp_apply, slice_callEmb_cleanEmb]
  have hU := congrArg (fun F => F (slice pos ψ (fun v => x (Sum.inl v)))) h
  simp only [comp_apply] at hU
  rw [hU, cleanEmb_apply, cleanEmb_apply, localOp_apply]
  have hr : (fun a => (fun w => x (callEmb (A := A) pos w)) (Sum.inr a)) = fun a => x (Sum.inr a) :=
    rfl
  have hl : (fun y => (fun w => x (callEmb (A := A) pos w)) (Sum.inl y)) =
      fun y => x (Sum.inl (pos y)) := rfl
  rw [hr, hl]

/-- The adjoint of an intertwining of unitaries intertwines the adjoints. -/
theorem adjoint_intertwine {K P : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
    {U : K →L[ℂ] K} {Q : P →L[ℂ] P} {E : P →L[ℂ] K} (hU : IsUnitary U) (hQ : IsUnitary Q)
    (h : U ∘L E = E ∘L Q) : U† ∘L E = E ∘L Q† := by
  have h1 : U† ∘L U = 1 := by
    have := hU.1
    rwa [star_eq_adjoint, mul_def] at this
  have h2 : Q ∘L Q† = 1 := by
    have := hQ.2
    rwa [star_eq_adjoint, mul_def] at this
  calc U† ∘L E = U† ∘L E ∘L (Q ∘L Q†) := by rw [h2]; exact ContinuousLinearMap.ext fun v => rfl
    _ = U† ∘L (U ∘L E) ∘L Q† := by rw [h]; simp only [comp_assoc]
    _ = E ∘L Q† := by
        rw [← comp_assoc, ← comp_assoc, h1]
        exact ContinuousLinearMap.ext fun v => rfl

variable (prim : J → Reg Y R →L[ℂ] Reg Y R) (prim' : J' → Reg Y' R →L[ℂ] Reg Y' R)

/-- One substituted instruction acts as the instruction on clean ancillas. -/
theorem nrun_substI_cleanEmb (hprim : ∀ j, IsUnitary (prim j)) (hprim' : ∀ j, IsUnitary (prim' j))
    {impl : J' → List (NInstr (Y' ⊕ A) Y J)} (h : ImplOK prim prim' impl) (i : NInstr V Y' J') :
    nrun prim (substI impl i) ∘L cleanEmb (X := A) = cleanEmb ∘L i.eval prim' := by
  cases i with
  | gate g =>
      change nrun prim [NInstr.gate (GateODE.Gate.map Sum.inl g)] ∘L cleanEmb (X := A) = _
      rw [nrun_singleton, NInstr.eval_gate, NInstr.eval_gate]
      have e := GateODE.Gate.map_op (Q := R) (Sum.inl_injective (α := V) (β := A)) g
      change _ = (GateODE.Gate.map Sum.inl g).op at e
      change (GateODE.Gate.map Sum.inl g).op ∘L cleanEmb (X := A) = cleanEmb ∘L g.op
      rw [← e]
      exact liftB_cleanEmb _
  | call j adj pos =>
      change nrun prim ((implAdj impl j adj).map (NInstr.map (callEmb pos))) ∘L cleanEmb (X := A) =
        cleanEmb ∘L localOp pos pos.injective (fun _ => adjIf adj (prim' j))
      rw [nrun_map]
      apply localOp_callEmb_cleanEmb
      cases adj with
      | false =>
          exact h.clean j
      | true =>
          change nrun prim (ninv (impl j)) ∘L cleanEmb (X := A) = cleanEmb ∘L (prim' j)†
          rw [nrun_ninv]
          exact adjoint_intertwine (nrun_isUnitary prim hprim _ (h.valid j)) (hprim' j) (h.clean j)

/-- **The substituted circuit acts as the circuit on clean ancillas.** -/
theorem nrun_subst_cleanEmb (hprim : ∀ j, IsUnitary (prim j)) (hprim' : ∀ j, IsUnitary (prim' j))
    {impl : J' → List (NInstr (Y' ⊕ A) Y J)} (h : ImplOK prim prim' impl)
    (C : List (NInstr V Y' J')) :
    nrun prim (subst impl C) ∘L cleanEmb (X := A) = cleanEmb ∘L nrun prim' C := by
  induction C with
  | nil =>
      rw [subst_nil, nrun_nil, nrun_nil]
      exact ContinuousLinearMap.ext fun v => rfl
  | cons i C ih =>
      rw [subst_cons, nrun_append, nrun_cons, comp_assoc,
        nrun_substI_cleanEmb prim prim' hprim hprim' h i, ← comp_assoc, ih, comp_assoc]

omit [Fintype V] [DecidableEq V] [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']
  [Fintype A] [DecidableEq A] [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R] in
/-- The substituted circuit is valid. -/
theorem valid_subst {impl : J' → List (NInstr (Y' ⊕ A) Y J)} (hv : ∀ j, ∀ i ∈ impl j, i.Valid)
    (C : List (NInstr V Y' J')) (hC : ∀ i ∈ C, i.Valid) : ∀ i ∈ subst impl C, i.Valid := by
  intro i hi
  rcases List.mem_flatMap.mp hi with ⟨i', hi', hi⟩
  cases i' with
  | gate g =>
      simp only [substI, List.mem_singleton] at hi
      subst hi
      exact NInstr.valid_map ⟨Sum.inl, Sum.inl_injective⟩ (NInstr.gate g) (hC _ hi')
  | call j adj pos =>
      simp only [substI, List.mem_map] at hi
      obtain ⟨i'', hi'', rfl⟩ := hi
      apply NInstr.valid_map
      unfold implAdj at hi''
      cases adj with
      | false => exact hv j i'' hi''
      | true => exact valid_ninv _ (hv j) i'' hi''

end Subst

/-! ### Counts -/

section Counts

variable {V Y Y' J J' A : Type*}

/-- The gates of one substituted instruction. -/
theorem nGatesN_substI (impl : J' → List (NInstr (Y' ⊕ A) Y J)) (i : NInstr V Y' J') :
    nGatesN (substI impl i) =
      match i with
      | .gate _ => 1
      | .call j _ _ => nGatesN (impl j) := by
  cases i with
  | gate g => rfl
  | call j adj pos =>
      change nGatesN ((implAdj impl j adj).map (NInstr.map (callEmb pos))) = _
      rw [nGatesN_map]
      unfold implAdj
      cases adj
      · rfl
      · exact nGatesN_ninv _

/-- **The gates of the substituted circuit**: at most `G` more gates for every call when every
implementation has at most `G` gates. -/
theorem nGatesN_subst_le (impl : J' → List (NInstr (Y' ⊕ A) Y J)) (G : ℕ)
    (hG : ∀ j, nGatesN (impl j) ≤ G) (C : List (NInstr V Y' J')) :
    nGatesN (subst impl C) ≤ nGatesN C + G * nCallsN (fun _ => true) C := by
  induction C with
  | nil => simp [nGatesN, nCallsN]
  | cons i C ih =>
      rw [subst_cons, nGatesN_append, nGatesN_substI]
      cases i with
      | gate g =>
          have h1 : nGatesN (NInstr.gate g :: C) = nGatesN C + 1 := by
            simp [nGatesN, NInstr.isGate]
          have h2 : nCallsN (fun _ => true) (NInstr.gate g :: C) = nCallsN (fun _ => true) C := by
            simp [nCallsN, NInstr.isCall]
          simp only at *
          rw [h1, h2]
          omega
      | call j adj pos =>
          have h1 : nGatesN (NInstr.call j adj pos :: C) = nGatesN C := by
            simp [nGatesN, NInstr.isGate]
          have h2 : nCallsN (fun _ => true) (NInstr.call j adj pos :: C) =
              nCallsN (fun _ => true) C + 1 := by
            simp [nCallsN, NInstr.isCall]
          simp only at *
          rw [h1, h2]
          have := hG j
          nlinarith

/-- An implementation of the primitive `j` makes at most `c` calls, all of primitives of the kind
of `j`. -/
structure KindOK (impl : J' → List (NInstr (Y' ⊕ A) Y J)) (kind : J → J') (c : ℕ) : Prop where
  kind_eq : ∀ j, ∀ q ∈ impl j, ∀ j' adj pos, q = .call j' adj pos → kind j' = j
  count : ∀ j, nCallsN (fun _ => true) (impl j) ≤ c

theorem nCallsN_le_of_kind {impl : J' → List (NInstr (Y' ⊕ A) Y J)} {kind : J → J'} {c : ℕ}
    (h : KindOK impl kind c) (j : J') (p : J' → Bool) :
    nCallsN (fun j' => p (kind j')) (impl j) ≤ c * (if p j then 1 else 0) := by
  by_cases hp : p j = true
  · rw [if_pos hp, mul_one]
    refine le_trans ?_ (h.count j)
    unfold nCallsN
    apply List.countP_mono_left
    intro q _ hq'
    cases q with
    | gate g => simp [NInstr.isCall] at hq'
    | call _ _ _ => simp [NInstr.isCall]
  · rw [if_neg hp, mul_zero]
    unfold nCallsN
    rw [Nat.le_zero, List.countP_eq_zero]
    intro q hq
    cases q with
    | gate g => simp [NInstr.isCall]
    | call j' adj pos =>
        have hk := h.kind_eq j _ hq j' adj pos rfl
        simp [NInstr.isCall, hk, hp]

/-- **The calls of the substituted circuit**: at most `c` calls of the kind `p` for every call of the
kind `p`. -/
theorem nCallsN_subst_le {impl : J' → List (NInstr (Y' ⊕ A) Y J)} {kind : J → J'} {c : ℕ}
    (h : KindOK impl kind c) (p : J' → Bool) (C : List (NInstr V Y' J')) :
    nCallsN (fun j' => p (kind j')) (subst impl C) ≤ c * nCallsN p C := by
  induction C with
  | nil => simp [nCallsN]
  | cons i C ih =>
      rw [subst_cons, nCallsN_append]
      cases i with
      | gate g =>
          have h1 : nCallsN (fun j' => p (kind j')) (substI impl (NInstr.gate g : NInstr V Y' J')) = 0 := by
            simp [substI, nCallsN, NInstr.isCall]
          have h2 : nCallsN p (NInstr.gate g :: C) = nCallsN p C := by
            simp [nCallsN, NInstr.isCall]
          rw [h1, h2]
          omega
      | call j adj pos =>
          have h1 : nCallsN (fun j' => p (kind j')) (substI impl (NInstr.call j adj pos : NInstr V Y' J')) =
              nCallsN (fun j' => p (kind j')) (impl j) := by
            change nCallsN _ ((implAdj impl j adj).map (NInstr.map (callEmb pos))) = _
            rw [nCallsN_map]
            unfold implAdj
            cases adj
            · rfl
            · exact nCallsN_ninv _ _
          have h2 : nCallsN p (NInstr.call j adj pos :: C) =
              nCallsN p C + (if p j then 1 else 0) := by
            simp only [nCallsN, List.countP_cons, NInstr.isCall]
            split_ifs <;> simp_all
          rw [h1, h2, mul_add]
          have := nCallsN_le_of_kind h j p
          omega

end Counts

end

end SparseHamiltonian.GeneralSparseAccess
