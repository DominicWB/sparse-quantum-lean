import GeneralSparseAccess.Subst

/-!
# Composing implementations of primitive oracles

If the primitives `P₂` are implemented from the primitives `P₃` by `impl₂` on clean ancillas `A₂`
and the primitives `P₁` from `P₂` by `impl₁` on clean ancillas `A₁`
(`GeneralSparseAccess.ImplOK`), the **composite implementation** `implComp impl₁ impl₂` (every call
of `impl₁ j` replaced by its implementation `impl₂`, `GeneralSparseAccess.subst`, the wires
reassociated to the register of `P₁` and the ancillas `A₁ ⊕ A₂`) implements `P₁` from `P₃` on
clean ancillas (`implOK_comp`), with

* `kindOK_comp`: at most `c₂ c₁` calls per call, all of the kind of the call, when `impl₁` makes at
  most `c₁` and `impl₂` at most `c₂` calls of the kind of the call;
* `nGatesN_implComp_le`: at most `G₁ + G₂ c₁` gates per call for `G₁` and `G₂` gates per call of
  `impl₁` and `impl₂`.
-/

set_option autoImplicit false

namespace SparseHamiltonian.GeneralDecoderODE

noncomputable section
open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
open SparseHamiltonian.GeneralSparseAccess
open SparseHamiltonian.OracleCircuit
open scoped InnerProduct

/-! ### The composite implementation -/

section Def

variable {Y₁ Y₂ Y₃ J₁ J₂ J₃ A₁ A₂ : Type*}

/-- The reassociation of the wires of a substituted implementation. -/
def assocE : (Y₁ ⊕ A₁) ⊕ A₂ ↪ Y₁ ⊕ (A₁ ⊕ A₂) := (Equiv.sumAssoc Y₁ A₁ A₂).toEmbedding

@[simp] theorem assocE_inl_inl (y : Y₁) :
    assocE (A₁ := A₁) (A₂ := A₂) (Sum.inl (Sum.inl y)) = Sum.inl y := rfl

@[simp] theorem assocE_inl_inr (a : A₁) :
    assocE (Y₁ := Y₁) (A₂ := A₂) (Sum.inl (Sum.inr a)) = Sum.inr (Sum.inl a) := rfl

@[simp] theorem assocE_inr (a : A₂) :
    assocE (Y₁ := Y₁) (A₁ := A₁) (Sum.inr a) = Sum.inr (Sum.inr a) := rfl

/-- **The composite implementation**: every call of `impl₁ j` replaced by its implementation
`impl₂` on the shared ancillas `A₂`, the wires reassociated to the register of `impl₁` and the
ancillas `A₁ ⊕ A₂`. -/
def implComp (impl₁ : J₁ → List (NInstr (Y₁ ⊕ A₁) Y₂ J₂))
    (impl₂ : J₂ → List (NInstr (Y₂ ⊕ A₂) Y₃ J₃)) :
    J₁ → List (NInstr (Y₁ ⊕ (A₁ ⊕ A₂)) Y₃ J₃) :=
  fun j => (subst impl₂ (impl₁ j)).map (NInstr.map assocE)

end Def

/-! ### Clean ancillas -/

section Clean

variable {Y₁ A₁ A₂ : Type*} [Fintype Y₁] [DecidableEq Y₁] [Fintype A₁] [DecidableEq A₁]
  [Fintype A₂] [DecidableEq A₂]
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

omit [Fintype Y₁] [DecidableEq Y₁] [Fintype A₁] [DecidableEq A₁] [Fintype A₂] [DecidableEq A₂] in
theorem sum_elim_eq_false {α β : Type*} (f : α → Bool) (g : β → Bool) :
    Sum.elim f g = (fun _ => false) ↔ f = (fun _ => false) ∧ g = (fun _ => false) := by
  constructor
  · intro h
    exact ⟨funext fun a => congrFun h (Sum.inl a), funext fun c => congrFun h (Sum.inr c)⟩
  · rintro ⟨hf, hg⟩
    funext x
    cases x with
    | inl a => exact congrFun hf a
    | inr c => exact congrFun hg c

/-- **The reassociated operator on clean ancillas**: an operator on `(Y₁ ⊕ A₁) ⊕ A₂` acting as `P`
on the two clean embeddings acts, reassociated, as `P` on the clean embedding into
`Y₁ ⊕ (A₁ ⊕ A₂)`. -/
theorem localOp_assocE_clean (U : Reg ((Y₁ ⊕ A₁) ⊕ A₂) R →L[ℂ] Reg ((Y₁ ⊕ A₁) ⊕ A₂) R)
    (P : Reg Y₁ R →L[ℂ] Reg Y₁ R)
    (h : U ∘L (cleanEmb (X := A₂) ∘L cleanEmb (X := A₁)) =
      (cleanEmb (X := A₂) ∘L cleanEmb (X := A₁)) ∘L P) :
    localOp assocE assocE.injective (fun _ => U) ∘L cleanEmb (X := A₁ ⊕ A₂) =
      cleanEmb (X := A₁ ⊕ A₂) ∘L P := by
  ext ψ z
  rw [comp_apply, comp_apply, localOp_apply]
  have ho : ∀ (c : Cfg ((Y₁ ⊕ A₁) ⊕ A₂)) (a : (Y₁ ⊕ A₁) ⊕ A₂),
      overwrite assocE z c (assocE a) = c a := fun c a =>
    GateODE.overwrite_apply_ι assocE.injective z c a
  have hs : slice assocE (cleanEmb (X := A₁ ⊕ A₂) ψ) z =
      cleanEmb (X := A₂) (cleanEmb (X := A₁) ψ) := by
    apply PiLp.ext
    intro c
    have h1 : (fun x => overwrite assocE z c (Sum.inr x)) =
        Sum.elim (fun a => c (Sum.inl (Sum.inr a))) (fun a => c (Sum.inr a)) := by
      funext x
      cases x with
      | inl a => exact ho c (Sum.inl (Sum.inr a))
      | inr a => exact ho c (Sum.inr a)
    have h2 : (fun y => overwrite assocE z c (Sum.inl y)) = fun y => c (Sum.inl (Sum.inl y)) :=
      funext fun y => ho c (Sum.inl (Sum.inl y))
    rw [slice_apply]
    simp only [cleanEmb_apply]
    rw [h1, h2]
    by_cases hg : (fun a => c (Sum.inr a)) = (fun _ => false)
    · by_cases hf : (fun a => c (Sum.inl (Sum.inr a))) = (fun _ => false)
      · rw [if_pos ((sum_elim_eq_false _ _).mpr ⟨hf, hg⟩), if_pos hg, if_pos hf]
      · rw [if_neg (fun h => hf ((sum_elim_eq_false _ _).mp h).1), if_pos hg, if_neg hf]
    · rw [if_neg (fun h => hg ((sum_elim_eq_false _ _).mp h).2), if_neg hg]
  rw [hs]
  have hU := congrArg (fun F => F ψ) h
  simp only [comp_apply] at hU
  rw [hU]
  have h3 : (fun x => z (Sum.inr x)) =
      Sum.elim (fun a => z (Sum.inr (Sum.inl a))) (fun a => z (Sum.inr (Sum.inr a))) := by
    funext x
    cases x <;> rfl
  simp only [cleanEmb_apply, assocE_inl_inl, assocE_inl_inr, assocE_inr]
  rw [h3]
  by_cases hg : (fun a => z (Sum.inr (Sum.inr a))) = (fun _ => false)
  · by_cases hf : (fun a => z (Sum.inr (Sum.inl a))) = (fun _ => false)
    · rw [if_pos hg, if_pos hf, if_pos ((sum_elim_eq_false _ _).mpr ⟨hf, hg⟩)]
    · rw [if_pos hg, if_neg hf, if_neg (fun h => hf ((sum_elim_eq_false _ _).mp h).1)]
  · rw [if_neg hg, if_neg (fun h => hg ((sum_elim_eq_false _ _).mp h).2)]

end Clean

/-! ### The composite implementation on clean ancillas -/

section OK

variable {Y₁ Y₂ Y₃ J₁ J₂ J₃ A₁ A₂ : Type*} [Fintype Y₁] [DecidableEq Y₁] [Fintype Y₂]
  [DecidableEq Y₂] [Fintype Y₃] [DecidableEq Y₃] [Fintype A₁] [DecidableEq A₁] [Fintype A₂]
  [DecidableEq A₂]
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- **The composite implementation implements the composite**: if `impl₂` implements `P₂` from the
unitary primitives `P₃` and `impl₁` implements `P₁` from the unitary primitives `P₂`, then
`implComp impl₁ impl₂` implements `P₁` from `P₃`. -/
theorem implOK_comp (P₃ : J₃ → Reg Y₃ R →L[ℂ] Reg Y₃ R) (P₂ : J₂ → Reg Y₂ R →L[ℂ] Reg Y₂ R)
    (P₁ : J₁ → Reg Y₁ R →L[ℂ] Reg Y₁ R) (hP₃ : ∀ j, IsUnitary (P₃ j))
    (hP₂ : ∀ j, IsUnitary (P₂ j)) {impl₁ : J₁ → List (NInstr (Y₁ ⊕ A₁) Y₂ J₂)}
    {impl₂ : J₂ → List (NInstr (Y₂ ⊕ A₂) Y₃ J₃)} (h₂ : ImplOK P₃ P₂ impl₂)
    (h₁ : ImplOK P₂ P₁ impl₁) : ImplOK P₃ P₁ (implComp impl₁ impl₂) where
  valid j := by
    intro i hi
    obtain ⟨i', hi', rfl⟩ := List.mem_map.mp hi
    exact NInstr.valid_map assocE i' (valid_subst h₂.valid (impl₁ j) (h₁.valid j) i' hi')
  clean j := by
    show nrun P₃ ((subst impl₂ (impl₁ j)).map (NInstr.map assocE)) ∘L cleanEmb = _
    rw [nrun_map]
    apply localOp_assocE_clean
    have hs := nrun_subst_cleanEmb P₃ P₂ hP₃ hP₂ h₂ (impl₁ j)
    have hc := h₁.clean j
    calc nrun P₃ (subst impl₂ (impl₁ j)) ∘L (cleanEmb (X := A₂) ∘L cleanEmb (X := A₁))
        = (nrun P₃ (subst impl₂ (impl₁ j)) ∘L cleanEmb (X := A₂)) ∘L cleanEmb (X := A₁) := by
          rw [comp_assoc]
      _ = (cleanEmb (X := A₂) ∘L nrun P₂ (impl₁ j)) ∘L cleanEmb (X := A₁) := by rw [hs]
      _ = cleanEmb (X := A₂) ∘L (nrun P₂ (impl₁ j) ∘L cleanEmb (X := A₁)) := by rw [comp_assoc]
      _ = cleanEmb (X := A₂) ∘L (cleanEmb (X := A₁) ∘L P₁ j) := by rw [hc]
      _ = (cleanEmb (X := A₂) ∘L cleanEmb (X := A₁)) ∘L P₁ j := by rw [comp_assoc]

end OK

/-! ### Counts -/

section Counts

variable {Y₁ Y₂ Y₃ J₁ J₂ J₃ A₁ A₂ : Type*}

/-- **The calls of the composite implementation**: at most `c₂ c₁` per call, all of the kind of
the call. -/
theorem kindOK_comp {impl₁ : J₁ → List (NInstr (Y₁ ⊕ A₁) Y₂ J₂)}
    {impl₂ : J₂ → List (NInstr (Y₂ ⊕ A₂) Y₃ J₃)} {kind₁ : J₂ → J₁} {kind₂ : J₃ → J₂} {c₁ c₂ : ℕ}
    (h₁ : KindOK impl₁ kind₁ c₁) (h₂ : KindOK impl₂ kind₂ c₂) :
    KindOK (implComp impl₁ impl₂) (fun j₃ => kind₁ (kind₂ j₃)) (c₂ * c₁) where
  kind_eq j q hq j' adj pos he := by
    classical
    have hk : nCallsN (fun j₂ => decide (kind₁ j₂ ≠ j)) (impl₁ j) = 0 := by
      have := nCallsN_le_of_kind h₁ j (fun j₁ => decide (j₁ ≠ j))
      rw [if_neg (by simp)] at this
      omega
    have h0 : nCallsN (fun j₃ => decide (kind₁ (kind₂ j₃) ≠ j)) (implComp impl₁ impl₂ j) = 0 := by
      show nCallsN _ ((subst impl₂ (impl₁ j)).map (NInstr.map assocE)) = 0
      rw [nCallsN_map]
      have hs := nCallsN_subst_le h₂ (fun j₂ => decide (kind₁ j₂ ≠ j)) (impl₁ j)
      rw [hk] at hs
      omega
    unfold nCallsN at h0
    rw [List.countP_eq_zero] at h0
    have h1 := h0 q hq
    subst he
    simpa [NInstr.isCall] using h1
  count j := by
    show nCallsN _ ((subst impl₂ (impl₁ j)).map (NInstr.map assocE)) ≤ _
    rw [nCallsN_map]
    exact (nCallsN_subst_le h₂ (fun _ => true) (impl₁ j)).trans
      (Nat.mul_le_mul_left _ (h₁.count j))

/-- `kindOK_comp` for implementations whose calls are of the kind of the call. -/
theorem kindOK_comp_id {impl₁ : J₁ → List (NInstr (Y₁ ⊕ A₁) Y₂ J₁)}
    {impl₂ : J₁ → List (NInstr (Y₂ ⊕ A₂) Y₃ J₁)} {c₁ c₂ : ℕ} (h₁ : KindOK impl₁ id c₁)
    (h₂ : KindOK impl₂ id c₂) : KindOK (implComp impl₁ impl₂) id (c₂ * c₁) :=
  kindOK_comp h₁ h₂

/-- **The gates of the composite implementation**: at most `G₁ + G₂ c₁` per call. -/
theorem nGatesN_implComp_le (impl₁ : J₁ → List (NInstr (Y₁ ⊕ A₁) Y₂ J₂))
    (impl₂ : J₂ → List (NInstr (Y₂ ⊕ A₂) Y₃ J₃)) (G₁ G₂ c₁ : ℕ)
    (hG₁ : ∀ j, nGatesN (impl₁ j) ≤ G₁) (hG₂ : ∀ j, nGatesN (impl₂ j) ≤ G₂) {kind₁ : J₂ → J₁}
    (h₁ : KindOK impl₁ kind₁ c₁) (j : J₁) :
    nGatesN (implComp impl₁ impl₂ j) ≤ G₁ + G₂ * c₁ := by
  show nGatesN ((subst impl₂ (impl₁ j)).map (NInstr.map assocE)) ≤ _
  rw [nGatesN_map]
  have h := nGatesN_subst_le impl₂ G₂ hG₂ (impl₁ j)
  have hc := Nat.mul_le_mul_left G₂ (h₁.count j)
  have hg := hG₁ j
  omega

end Counts

end

end SparseHamiltonian.GeneralDecoderODE
