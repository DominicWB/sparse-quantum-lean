import GeneralSparseAccess.Subst
import GateEfficientBinaryTime.Slot
import GateOptimalBinary.SignedNative

/-!
# Native private operations calling implemented primitives

The native private operation of a gate-level solver (`GateNative.NativeOp`: a compute circuit `V`
of elementary gates and primitive calls, an orientation wire and a decoder) calls the primitive
oracles `prim'` only inside `V`. If the primitives `prim'` are implemented by circuits `impl` calling
primitives `prim` on clean ancillas `A` (`GeneralSparseAccess.ImplOK`), the **substituted
operation** `substOp nd impl` has the compute circuit `GeneralSparseAccess.subst impl V` on the base
wires with the ancillas added to the scratch (`Z ⊕ A`), the same orientation wire and the decoder
of `nd` read on the base wires:

* `nativeOK_substOp`: if `V† R_val V` acts as the selected private operation `Dsel` on clean
  scratch for the primitives `prim'` (`NativeOK`), the substituted operation does for `prim`;
* `substOp_public`, `nGatesN_substOp_le`, `nCallsN_substOp_le`: the public conditions, at most
  `G` more gates per call and at most `c` calls per call of the same kind;
* `liftA`, `arithOK_liftA`: the reversible arithmetic of `nd` on the base wires with the
  ancillas added, with the same accuracy and counts.

The time-slot-selected form is `GeneralSparseODE.substSlot` (module `SubstSlot`).

`cleanOn e` is the clean embedding along an embedding of wires (every other wire zero); a local
operation along `e` intertwines it (`localOp_cleanOn`).
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GeneralSparseODE

noncomputable section
open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
open SparseHamiltonian.GeneralSparseAccess
open SparseHamiltonian.OracleCircuit
open SparseHamiltonian.GateODE (overwrite_apply_ι overwrite_apply_out update_comp_injective)
open scoped InnerProduct

/-! ### The clean embedding along an embedding of wires -/

section CleanOn

variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R]

/-- **The clean embedding along an embedding of wires**: the vector on the wires `e(S)`, every
other wire zero. -/
def cleanOn {S W : Type*} [Fintype S] [DecidableEq S] [Fintype W] [DecidableEq W]
    (e : S ↪ W) : Reg S R →L[ℂ] Reg W R :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Cfg W => R)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi (fun y =>
      @ite _ (∀ w, (∀ s, e s ≠ w) → y w = false) (Classical.propDecidable _)
        (coord (fun s => y (e s))) 0)

theorem cleanOn_apply {S W : Type*} [Fintype S] [DecidableEq S] [Fintype W] [DecidableEq W]
    (e : S ↪ W) (ψ : Reg S R) (y : Cfg W) :
    cleanOn e ψ y = @ite _ (∀ w, (∀ s, e s ≠ w) → y w = false) (Classical.propDecidable _)
      (ψ (fun s => y (e s))) 0 := by
  change (@ite _ (∀ w, (∀ s, e s ≠ w) → y w = false) (Classical.propDecidable _)
    (coord (fun s => y (e s))) 0) ψ = _
  split_ifs <;> rfl

/-- **The clean embeddings along embeddings compose.** -/
theorem cleanOn_trans {S T W : Type*} [Fintype S] [DecidableEq S] [Fintype T] [DecidableEq T]
    [Fintype W] [DecidableEq W] (e₁ : S ↪ T) (e₂ : T ↪ W) :
    cleanOn (R := R) (e₁.trans e₂) = cleanOn e₂ ∘L cleanOn e₁ := by
  refine ContinuousLinearMap.ext fun ψ => PiLp.ext fun y => ?_
  rw [comp_apply, cleanOn_apply, cleanOn_apply, cleanOn_apply]
  by_cases h1 : ∀ w, (∀ t, e₂ t ≠ w) → y w = false
  · rw [if_pos h1]
    by_cases h2 : ∀ t, (∀ s, e₁ s ≠ t) → y (e₂ t) = false
    · rw [if_pos h2, if_pos]
      · rfl
      · intro w hw
        by_cases hr : ∃ t, e₂ t = w
        · obtain ⟨t, rfl⟩ := hr
          exact h2 t (fun s hs => hw s (congrArg e₂ hs))
        · exact h1 w (fun t ht => hr ⟨t, ht⟩)
    · rw [if_neg h2, if_neg]
      intro h
      apply h2
      intro t ht
      exact h (e₂ t) (fun s hs => ht s (e₂.injective hs))
  · rw [if_neg h1, if_neg]
    intro h
    apply h1
    intro w hw
    exact h w (fun s hs => hw (e₁ s) hs)

/-- **The clean embedding along `Sum.inl` is the package's clean embedding.** -/
theorem cleanOn_inl {B X : Type*} [Fintype B] [DecidableEq B] [Fintype X] [DecidableEq X] :
    cleanOn (R := R) (⟨Sum.inl, Sum.inl_injective⟩ : B ↪ B ⊕ X) = cleanEmb (X := X) := by
  refine ContinuousLinearMap.ext fun ψ => PiLp.ext fun y => ?_
  rw [cleanOn_apply, cleanEmb_apply]
  by_cases h : ∀ x, y (Sum.inr x) = false
  · rw [if_pos, if_pos (funext h)]
    · rfl
    · intro w hw
      rcases w with b | x
      · exact absurd rfl (hw b)
      · exact h x
  · rw [if_neg, if_neg]
    · intro h'
      exact h (fun x => congrFun h' x)
    · intro h'
      exact h (fun x => h' (Sum.inr x) (fun b hb => Sum.inl_ne_inr hb))

/-- **The clean embedding is an isometry.** -/
theorem norm_cleanOn {S W : Type*} [Fintype S] [DecidableEq S] [Fintype W] [DecidableEq W]
    (e : S ↪ W) (ψ : Reg S R) : ‖cleanOn e ψ‖ = ‖ψ‖ := by
  have hsq : ‖cleanOn e ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    have hinj : ∀ d ∈ (Finset.univ : Finset (Cfg S)), ∀ d' ∈ (Finset.univ : Finset (Cfg S)),
        overwrite e (fun _ => false) d = overwrite e (fun _ => false) d' → d = d' := by
      intro d _ d' _ h
      funext s
      have := congrFun h (e s)
      rwa [overwrite_apply_ι e.injective, overwrite_apply_ι e.injective] at this
    have hclean : ∀ d : Cfg S, ∀ w, (∀ s, e s ≠ w) →
        overwrite e (fun _ => false) d w = false := fun d w hw => by
      rw [overwrite_apply_out _ _ _ _ hw]
    have hval : ∀ d : Cfg S, (fun s => overwrite e (fun _ => false) d (e s)) = d :=
      fun d => funext fun s => overwrite_apply_ι e.injective _ d s
    calc ∑ y, ‖cleanOn e ψ y‖ ^ 2
        = ∑ y ∈ Finset.univ.image (fun d : Cfg S => overwrite e (fun _ => false) d),
            ‖cleanOn e ψ y‖ ^ 2 := by
          symm
          apply Finset.sum_subset (Finset.subset_univ _)
          intro y _ hy
          rw [cleanOn_apply, if_neg]
          · simp
          · intro h
            apply hy
            refine Finset.mem_image.mpr ⟨fun s => y (e s), Finset.mem_univ _, ?_⟩
            funext w
            by_cases hw : ∃ s, e s = w
            · obtain ⟨s, rfl⟩ := hw
              exact overwrite_apply_ι e.injective _ _ s
            · rw [overwrite_apply_out _ _ _ _ (fun s hs => hw ⟨s, hs⟩)]
              exact (h w (fun s hs => hw ⟨s, hs⟩)).symm
      _ = ∑ d, ‖cleanOn e ψ (overwrite e (fun _ => false) d)‖ ^ 2 :=
          Finset.sum_image hinj
      _ = ∑ d, ‖ψ d‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro d _
          rw [cleanOn_apply, if_pos (hclean d), hval d]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

variable [CompleteSpace R]

/-- **A local operation along an embedding intertwines the clean embedding along it.** -/
theorem localOp_cleanOn {B W : Type*} [Fintype B] [DecidableEq B] [Fintype W] [DecidableEq W]
    (e : B ↪ W) (U : Reg B R →L[ℂ] Reg B R) :
    localOp e e.injective (fun _ => U) ∘L cleanOn e = cleanOn e ∘L U := by
  refine ContinuousLinearMap.ext fun ψ => PiLp.ext fun y => ?_
  rw [comp_apply, comp_apply, localOp_apply, cleanOn_apply]
  have hs : slice e (cleanOn (R := R) e ψ) y =
      @ite _ (∀ w, (∀ s, e s ≠ w) → y w = false) (Classical.propDecidable _) ψ 0 := by
    apply PiLp.ext
    intro b
    rw [slice_apply, cleanOn_apply]
    have hout : (∀ w, (∀ s, e s ≠ w) → overwrite e y b w = false) ↔
        ∀ w, (∀ s, e s ≠ w) → y w = false := by
      constructor
      · intro h w hw
        rw [← overwrite_apply_out e y b w hw]
        exact h w hw
      · intro h w hw
        rw [overwrite_apply_out e y b w hw]
        exact h w hw
    have hb : (fun s => overwrite e y b (e s)) = b :=
      funext fun s => overwrite_apply_ι e.injective y b s
    by_cases h : ∀ w, (∀ s, e s ≠ w) → y w = false
    · rw [if_pos (hout.mpr h), if_pos h, hb]
    · rw [if_neg (fun h' => h (hout.mp h')), if_neg h]
      rfl
  rw [hs]
  split_ifs
  · rfl
  · rw [map_zero]
    rfl

end CleanOn

/-! ### The substituted native operation -/

section Wires

variable {Sel PR Z Y Y' J J' Xa : Type*}

theorem inclZ_injective : Function.Injective
    (Sum.map id Sum.inl : NB Sel PR Z → NB Sel PR (Z ⊕ Xa)) :=
  Sum.map_injective.2 ⟨Function.injective_id, Sum.inl_injective⟩

/-- **The base wires of a native operation** inside those with the ancillas `Xa` added to the
scratch. -/
def inclZ : NB Sel PR Z ↪ NB Sel PR (Z ⊕ Xa) := ⟨Sum.map id Sum.inl, inclZ_injective⟩

theorem ascE_injective : Function.Injective
    (Sum.elim (Sum.map id Sum.inl) (fun a => Sum.inr (Sum.inr a)) :
      NB Sel PR Z ⊕ Xa → NB Sel PR (Z ⊕ Xa)) := by
  intro u v h
  rcases u with (p | z) | a <;> rcases v with (p' | z') | a' <;> simp_all

/-- **The wires of the substituted compute circuit**: the base wires and the ancillas, inside the
base wires with the ancillas added to the scratch. -/
def ascE : NB Sel PR Z ⊕ Xa ↪ NB Sel PR (Z ⊕ Xa) :=
  ⟨Sum.elim (Sum.map id Sum.inl) (fun a => Sum.inr (Sum.inr a)), ascE_injective⟩

@[simp] theorem ascE_inl (w : NB Sel PR Z) :
    (ascE (Xa := Xa) (Sel := Sel) (PR := PR) (Z := Z) (Sum.inl w)) = inclZ w := rfl

/-- **The substituted native operation**: the compute circuit with every primitive call replaced by
its implementation on the ancillas `Xa` of the scratch, the same orientation wire, and the decoder
of `nd` on the base wires. -/
def substOp (nd : NativeOp Sel PR Z Y' J') (impl : J' → List (NInstr (Y' ⊕ Xa) Y J)) :
    NativeOp Sel PR (Z ⊕ Xa) Y J where
  V := (subst impl nd.V).map (NInstr.map ascE)
  o := nd.o
  dec := fun y => nd.dec (fun w => y (inclZ w))

end Wires

section NativeSubst

variable {Sel PR Z Y Y' J J' Xa : Type*} [Fintype Sel] [DecidableEq Sel] [Fintype PR]
  [DecidableEq PR] [Fintype Z] [DecidableEq Z] [Fintype Y] [DecidableEq Y] [Fintype Y']
  [DecidableEq Y'] [Fintype Xa] [DecidableEq Xa]

omit [Fintype Sel] [Fintype PR] [Fintype Z] [Fintype Y] [DecidableEq Y] [Fintype Y']
  [DecidableEq Y'] [Fintype Xa] in
/-- **The substituted operation satisfies the public conditions.** -/
theorem substOp_public {nd : NativeOp Sel PR Z Y' J'} (hnd : nd.Public)
    {impl : J' → List (NInstr (Y' ⊕ Xa) Y J)} (hv : ∀ j, ∀ i ∈ impl j, i.Valid) :
    (substOp nd impl).Public where
  valid := valid_map_list ascE _ (valid_subst hv nd.V hnd.valid)
  dec_indep x b := by
    show nd.dec (fun w => Function.update x (Sum.inl (Sum.inr nd.o)) b (inclZ w)) =
      nd.dec (fun w => x (inclZ w))
    have e : (fun w => Function.update x (Sum.inl (Sum.inr nd.o)) b (inclZ w)) =
        Function.update (fun w => x (inclZ w)) (Sum.inl (Sum.inr nd.o)) b :=
      update_comp_injective (inclZ (Xa := Xa) (Sel := Sel) (PR := PR) (Z := Z)).injective x
        (Sum.inl (Sum.inr nd.o)) b
    rw [e]
    exact hnd.dec_indep _ b

omit [Fintype Sel] [DecidableEq Sel] [Fintype PR] [DecidableEq PR] [Fintype Z] [DecidableEq Z]
  [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] [Fintype Xa] [DecidableEq Xa] in
/-- **The gates of the substituted compute circuit**: at most `G` more per call. -/
theorem nGatesN_substOp_le (nd : NativeOp Sel PR Z Y' J')
    (impl : J' → List (NInstr (Y' ⊕ Xa) Y J)) (G : ℕ) (hG : ∀ j, nGatesN (impl j) ≤ G) :
    nGatesN (substOp nd impl).V ≤ nGatesN nd.V + G * nCallsN (fun _ => true) nd.V := by
  show nGatesN ((subst impl nd.V).map (NInstr.map ascE)) ≤ _
  rw [nGatesN_map]
  exact nGatesN_subst_le impl G hG nd.V

omit [Fintype Sel] [DecidableEq Sel] [Fintype PR] [DecidableEq PR] [Fintype Z] [DecidableEq Z]
  [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] [Fintype Xa] [DecidableEq Xa] in
/-- **The calls of the substituted compute circuit**: at most `c` of the kind `p` per call of the
kind `p`. -/
theorem nCallsN_substOp_le (nd : NativeOp Sel PR Z Y' J')
    {impl : J' → List (NInstr (Y' ⊕ Xa) Y J)} {kind : J → J'} {c : ℕ} (h : KindOK impl kind c)
    (p : J' → Bool) :
    nCallsN (fun j => p (kind j)) (substOp nd impl).V ≤ c * nCallsN p nd.V := by
  show nCallsN _ ((subst impl nd.V).map (NInstr.map ascE)) ≤ _
  rw [nCallsN_map]
  exact nCallsN_subst_le h p nd.V

variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

omit [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] in
/-- The decoded rotation of the substituted operation is that of `nd` on the base wires. -/
theorem Rdec_substOp (nd : NativeOp Sel PR Z Y' J') (impl : J' → List (NInstr (Y' ⊕ Xa) Y J)) :
    Rdec (R := R) (substOp nd impl) =
      localOp ascE ascE.injective (fun _ => liftB (X := Xa) (Rdec (R := R) nd)) := by
  have h1 : liftB (X := Xa) (Rdec (R := R) nd) =
      condOp (Sum.inl (Sum.inl (Sum.inr nd.o)) : NB Sel PR Z ⊕ Xa)
        (fun z => edgeMat (nd.dec (fun a => z (Sum.inl a)))) := by
    rw [liftB, Rdec]
    exact GateBinary.localOp_condOp (⟨Sum.inl, Sum.inl_injective⟩ : NB Sel PR Z ↪ NB Sel PR Z ⊕ Xa)
      _ _
  rw [h1, GateBinary.localOp_condOp, Rdec]
  rfl

/-- **The native identity of the substituted operation**: for unitary primitives and an
implementation `impl` of the primitives `prim'` by circuits calling `prim`, the native identity of
`nd` for `prim'` gives that of `substOp nd impl` for `prim`, with the same selected private
operation. -/
theorem nativeOK_substOp (prim : J → Reg Y R →L[ℂ] Reg Y R) (prim' : J' → Reg Y' R →L[ℂ] Reg Y' R)
    (hprim : ∀ j, IsUnitary (prim j)) (hprim' : ∀ j, IsUnitary (prim' j))
    {impl : J' → List (NInstr (Y' ⊕ Xa) Y J)} (himpl : ImplOK prim prim' impl)
    (nd : NativeOp Sel PR Z Y' J') (hnd : nd.Public)
    (Dsel : Reg (Sel ⊕ PR) R →L[ℂ] Reg (Sel ⊕ PR) R) (hOK : NativeOK prim' nd Dsel) :
    NativeOK prim (substOp nd impl) Dsel := by
  unfold NativeOK at hOK ⊢
  have hUu : IsUnitary (nrun prim' nd.V) := nrun_isUnitary prim' hprim' _ hnd.valid
  have hUsu : IsUnitary (nrun prim (subst impl nd.V)) :=
    nrun_isUnitary prim hprim _ (valid_subst himpl.valid nd.V hnd.valid)
  have hsub : nrun prim (subst impl nd.V) ∘L cleanEmb (X := Xa) =
      cleanEmb ∘L nrun prim' nd.V :=
    nrun_subst_cleanEmb prim prim' hprim hprim' himpl nd.V
  have hsubA : (nrun prim (subst impl nd.V))† ∘L cleanEmb (X := Xa) =
      cleanEmb ∘L (nrun prim' nd.V)† := adjoint_intertwine hUsu hUu hsub
  have hRl : liftB (X := Xa) (Rdec (R := R) nd) ∘L cleanEmb (X := Xa) =
      cleanEmb ∘L Rdec (R := R) nd := by
    have h := localOp_cleanOn (R := R)
      (⟨Sum.inl, Sum.inl_injective⟩ : NB Sel PR Z ↪ NB Sel PR Z ⊕ Xa) (Rdec (R := R) nd)
    rw [cleanOn_inl] at h
    exact h
  have hV : nrun prim (substOp nd impl).V =
      localOp ascE ascE.injective (fun _ => nrun prim (subst impl nd.V)) := by
    show nrun prim ((subst impl nd.V).map (NInstr.map ascE)) = _
    rw [nrun_map]
  have hE : (cleanEmb (X := Z ⊕ Xa) : Reg (Sel ⊕ PR) R →L[ℂ] Reg (NB Sel PR (Z ⊕ Xa)) R) =
      cleanOn ascE ∘L (cleanEmb (X := Xa) ∘L cleanEmb (X := Z)) := by
    rw [← cleanOn_inl, ← cleanOn_inl, ← cleanOn_inl, ← cleanOn_trans, ← cleanOn_trans]
    rfl
  generalize nrun prim (subst impl nd.V) = Us at hUsu hsub hsubA hV
  generalize nrun prim' nd.V = U at hUu hsub hsubA hOK
  have hc : (localOp ascE ascE.injective (fun _ => Us†) ∘L
      localOp ascE ascE.injective (fun _ => liftB (X := Xa) (Rdec (R := R) nd)) ∘L
        localOp ascE ascE.injective (fun _ => Us)) =
      localOp ascE ascE.injective (fun _ => Us† ∘L liftB (X := Xa) (Rdec (R := R) nd) ∘L Us) := by
    rw [localOp_comp, localOp_comp]
  have hM : (Us† ∘L liftB (X := Xa) (Rdec (R := R) nd) ∘L Us) ∘L cleanEmb (X := Xa) =
      cleanEmb (X := Xa) ∘L (U† ∘L Rdec (R := R) nd ∘L U) := by
    calc (Us† ∘L liftB (X := Xa) (Rdec (R := R) nd) ∘L Us) ∘L cleanEmb (X := Xa)
        = Us† ∘L (liftB (X := Xa) (Rdec (R := R) nd) ∘L (Us ∘L cleanEmb (X := Xa))) := by
          simp only [comp_assoc]
      _ = Us† ∘L ((liftB (X := Xa) (Rdec (R := R) nd) ∘L cleanEmb (X := Xa)) ∘L U) := by
          rw [hsub]
          simp only [comp_assoc]
      _ = (Us† ∘L cleanEmb (X := Xa)) ∘L (Rdec (R := R) nd ∘L U) := by
          rw [hRl]
          simp only [comp_assoc]
      _ = cleanEmb (X := Xa) ∘L (U† ∘L Rdec (R := R) nd ∘L U) := by
          rw [hsubA]
          simp only [comp_assoc]
  rw [hV, Rdec_substOp, localOp_adjoint, hE]
  calc localOp ascE ascE.injective (fun _ => Us†) ∘L
        localOp ascE ascE.injective (fun _ => liftB (X := Xa) (Rdec (R := R) nd)) ∘L
          localOp ascE ascE.injective (fun _ => Us) ∘L
            (cleanOn ascE ∘L (cleanEmb (X := Xa) ∘L cleanEmb (X := Z)))
      = (localOp ascE ascE.injective (fun _ => Us†) ∘L
          localOp ascE ascE.injective (fun _ => liftB (X := Xa) (Rdec (R := R) nd)) ∘L
            localOp ascE ascE.injective (fun _ => Us)) ∘L
              (cleanOn ascE ∘L (cleanEmb (X := Xa) ∘L cleanEmb (X := Z))) := by
        simp only [comp_assoc]
    _ = localOp ascE ascE.injective
          (fun _ => Us† ∘L liftB (X := Xa) (Rdec (R := R) nd) ∘L Us) ∘L
            (cleanOn ascE ∘L (cleanEmb (X := Xa) ∘L cleanEmb (X := Z))) := by
        rw [hc]
    _ = (cleanOn ascE ∘L (Us† ∘L liftB (X := Xa) (Rdec (R := R) nd) ∘L Us)) ∘L
            (cleanEmb (X := Xa) ∘L cleanEmb (X := Z)) := by
        rw [← comp_assoc, localOp_cleanOn]
    _ = cleanOn ascE ∘L (((Us† ∘L liftB (X := Xa) (Rdec (R := R) nd) ∘L Us) ∘L
            cleanEmb (X := Xa)) ∘L cleanEmb (X := Z)) := by
        simp only [comp_assoc]
    _ = cleanOn ascE ∘L (cleanEmb (X := Xa) ∘L (U† ∘L Rdec (R := R) nd ∘L U ∘L
            cleanEmb (X := Z))) := by
        rw [hM]
        simp only [comp_assoc]
    _ = (cleanOn ascE ∘L (cleanEmb (X := Xa) ∘L cleanEmb (X := Z))) ∘L Dsel := by
        rw [hOK]
        simp only [comp_assoc]

end NativeSubst

/-! ### The arithmetic on the base wires -/

section ArithLift

variable {Sel PR Z Xa : Type*}

theorem liftW_injective {bT bP A : ℕ} : Function.Injective
    (Sum.map (inclZ (Xa := Xa) (Sel := Sel) (PR := PR) (Z := Z)) id :
      NB Sel PR Z ⊕ AWr bT bP A → NB Sel PR (Z ⊕ Xa) ⊕ AWr bT bP A) :=
  Sum.map_injective.2 ⟨inclZ.injective, Function.injective_id⟩

/-- **The arithmetic on the base wires with the ancillas added to the scratch**: the same circuit
on the base and arithmetic wires and the same output words of the base configuration. -/
def liftA (ar : Arith (NB Sel PR Z)) : Arith (NB Sel PR (Z ⊕ Xa)) where
  bT := ar.bT
  bP := ar.bP
  A := ar.A
  circ := ar.circ.map (GateODE.Gate.map (Sum.map (inclZ (Xa := Xa)) id))
  tw := fun y => ar.tw (fun w => y (inclZ w))
  pw := fun y => ar.pw (fun w => y (inclZ w))

@[simp] theorem liftA_circ_length (ar : Arith (NB Sel PR Z)) :
    (liftA (Xa := Xa) ar).circ.length = ar.circ.length := by
  simp [liftA]

variable [Fintype Sel] [DecidableEq Sel] [Fintype PR] [DecidableEq PR] [Fintype Z] [DecidableEq Z]
  [Fintype Xa] [DecidableEq Xa]

omit [Fintype Xa] in
/-- **The arithmetic hypothesis on the base wires**: the lifted arithmetic of an `ArithOK`
arithmetic for the decoder `dec` is `ArithOK` for the decoder `dec` on the base wires, with the
same accuracy. -/
theorem arithOK_liftA (ar : Arith (NB Sel PR Z)) (o : PR) (dec : Cfg (NB Sel PR Z) → ℂ) (ζ : ℝ)
    (h : ArithOK ar (Sum.inl (Sum.inr o)) dec ζ) :
    ArithOK (liftA (Xa := Xa) ar) (Sum.inl (Sum.inr o)) (fun y => dec (fun w => y (inclZ w))) ζ where
  elem g hg := by
    have hg' : g ∈ ar.circ.map (GateODE.Gate.map (Sum.map (inclZ (Xa := Xa)) id)) := hg
    obtain ⟨g', hg'', rfl⟩ := List.mem_map.mp hg'
    show (g'.cs.map (fun c => (Sum.map (inclZ (Xa := Xa)) id c.1, c.2))).length ≤ 3
    rw [List.length_map]
    exact h.elem g' hg''
  classical := GateOptimalBinary.classical_map liftW_injective h.classical
  compute x := by
    show cfgRun (ar.circ.map (GateODE.Gate.map (Sum.map (inclZ (Xa := Xa)) id)))
      (Sum.elim x (fun _ => false)) = Sum.elim x (Arith.out ar (fun w => x (inclZ w)))
    rw [GateOptimalBinary.cfgRun_map liftW_injective]
    have e1 : (fun a => (Sum.elim x (fun _ => false) :
        Cfg (NB Sel PR (Z ⊕ Xa) ⊕ AWr ar.bT ar.bP ar.A)) (Sum.map (inclZ (Xa := Xa)) id a)) =
        Sum.elim (fun w => x (inclZ w)) (fun _ => false) := by
      funext a
      rcases a with w | q <;> rfl
    rw [e1, h.compute]
    funext v
    rcases v with w | q
    · by_cases hw : ∃ w', inclZ (Xa := Xa) w' = w
      · obtain ⟨w', rfl⟩ := hw
        exact overwrite_apply_ι liftW_injective _ _ (Sum.inl w')
      · rw [overwrite_apply_out _ _ _ _ (fun a ha => by
          rcases a with w' | q
          · exact hw ⟨w', Sum.inl_injective ha⟩
          · cases ha)]
        rfl
    · exact overwrite_apply_ι liftW_injective _ _ (Sum.inr q)
  tw_indep x b := by
    have e : (fun w => Function.update x (Sum.inl (Sum.inr o)) b (inclZ (Xa := Xa) w)) =
        Function.update (fun w => x (inclZ w)) (Sum.inl (Sum.inr o)) b :=
      update_comp_injective (inclZ (Xa := Xa) (Sel := Sel) (PR := PR) (Z := Z)).injective x
        (Sum.inl (Sum.inr o)) b
    show ar.tw (fun w => Function.update x (Sum.inl (Sum.inr o)) b (inclZ w)) =
      ar.tw (fun w => x (inclZ w))
    rw [e]
    exact h.tw_indep _ b
  pw_indep x b := by
    have e : (fun w => Function.update x (Sum.inl (Sum.inr o)) b (inclZ (Xa := Xa) w)) =
        Function.update (fun w => x (inclZ w)) (Sum.inl (Sum.inr o)) b :=
      update_comp_injective (inclZ (Xa := Xa) (Sel := Sel) (PR := PR) (Z := Z)).injective x
        (Sum.inl (Sum.inr o)) b
    show ar.pw (fun w => Function.update x (Sum.inl (Sum.inr o)) b (inclZ w)) =
      ar.pw (fun w => x (inclZ w))
    rw [e]
    exact h.pw_indep _ b
  theta x := h.theta _
  phi x hx := h.phi _ hx

end ArithLift

end

end SparseHamiltonian.GeneralSparseODE
