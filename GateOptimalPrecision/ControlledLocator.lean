import GateEfficientNative.Native.Private

/-!
# Controls on native locators (Section `gate:sec:native`)

Let `U` be a primitive locator on `w`-bit words with `U|x_*⟩ = |y_*⟩` for a known valid word `x_*`;
the label `y_*` need not be known. The construction of the paragraph "Controls on native locators"
of Section `gate:sec:native` controls `U` with five primitive queries:

1. the two-query reference preparation (`prepL`): `U` on a reference in `x_*`, a copy of its
   basis output `y_*` into a clean register (`copyG`), and `U†` on the reference;
2. the target swapped with a dummy in `x_*` on the inactive branch (`swapG`), the unitary
   `V = W_{y_*}† U` applied unconditionally (one query and the XOR translation
   `W_y : x ↦ x ⊕ x_* ⊕ y`, `xorG`), and the swap undone;
3. the controlled `W_{y_*}`, and the reference preparation reversed.

* `ctrlLoc_agrees`: on clean work wires (`LocClean`: the reference and the dummy in `x_*`, the
  copy register zero) the circuit is exactly the controlled `U` on the target (`ctrlU`), for
  every unitary `U` with the prescribed action at `x_*`. The rest of the oracle extension is
  unrestricted, and `U` may act on the payload. The work wires are restored on both branches.
* `ctrlLoc_inv_agrees`: the reversed circuit is the controlled `U†`.
* `ctrlLoc_nCalls`: five primitive queries; `ctrlLoc_nGates`: at most `12 w` elementary gates;
  `ctrlLoc_valid`: every instruction is valid, the gates being `X` gates with at most three
  controls off their targets (`GateOK 3`; `copyG_classical`, `swapG_classical`,
  `xorG_classical`); `card_LocW`: `4w + 1` wires (the control, the target word and `3w` work
  bits).
* The `12 w` gates assume the reference and the dummy already hold `x_*`. On zero-initialised work
  wires (`LocZero`), `ctrlLoc0` first writes `x_*` into both with at most `2w` uncontrolled `X`
  gates (`setG`) and undoes them at the end: `ctrlLoc0_agrees`, `ctrlLoc0_inv_agrees` (the
  controlled `U` and `U†`), `ctrlLoc0_nCalls` (five queries), `ctrlLoc0_nGates` (at most `16 w`
  gates), `ctrlLoc0_valid`.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace GateOptimalPrecision

noncomputable section

open ContinuousLinearMap SparseHamiltonian SparseHamiltonian.OracleCircuit
  SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
open GateODE (put put_apply localOp_put bas_eq_put overwrite_apply_ι overwrite_apply_out adjIf)
open scoped InnerProduct BigOperators

/-! ### The wires -/

/-- The wires of the controlled locator for `w`-bit words: the control, the target word, the
reference, the copy register and the dummy. -/
inductive LocW (w : ℕ)
  | ctl
  | tgt (i : Fin w)
  | ref (i : Fin w)
  | cpy (i : Fin w)
  | dum (i : Fin w)
  deriving DecidableEq

namespace LocW

variable {w : ℕ}

/-- The decomposition of the wires. -/
def equiv (w : ℕ) : LocW w ≃ Unit ⊕ ((Fin w ⊕ Fin w) ⊕ (Fin w ⊕ Fin w)) where
  toFun
    | ctl => Sum.inl ()
    | tgt i => Sum.inr (Sum.inl (Sum.inl i))
    | ref i => Sum.inr (Sum.inl (Sum.inr i))
    | cpy i => Sum.inr (Sum.inr (Sum.inl i))
    | dum i => Sum.inr (Sum.inr (Sum.inr i))
  invFun
    | Sum.inl () => ctl
    | Sum.inr (Sum.inl (Sum.inl i)) => tgt i
    | Sum.inr (Sum.inl (Sum.inr i)) => ref i
    | Sum.inr (Sum.inr (Sum.inl i)) => cpy i
    | Sum.inr (Sum.inr (Sum.inr i)) => dum i
  left_inv v := by cases v <;> rfl
  right_inv v := by rcases v with ⟨⟩ | ((i | i) | (i | i)) <;> rfl

instance : Fintype (LocW w) := Fintype.ofEquiv _ (equiv w).symm

/-- The index of a word wire. -/
def idx : LocW w → Option (Fin w)
  | ctl => none
  | tgt i => some i
  | ref i => some i
  | cpy i => some i
  | dum i => some i

end LocW

open LocW

/-- `4w + 1` wires: the control, the target word, and `3w` work bits. -/
theorem card_LocW (w : ℕ) : Fintype.card (LocW w) = 4 * w + 1 := by
  rw [Fintype.card_congr (LocW.equiv w)]
  simp only [Fintype.card_sum, Fintype.card_unit, Fintype.card_fin]
  ring

/-- The target word. -/
def tgtE (w : ℕ) : Fin w ↪ LocW w := ⟨LocW.tgt, fun _ _ h => LocW.tgt.inj h⟩

/-- The reference word. -/
def refE (w : ℕ) : Fin w ↪ LocW w := ⟨LocW.ref, fun _ _ h => LocW.ref.inj h⟩

/-- The configuration with control `c`, target `t`, reference `r`, copy `y` and dummy `d`. -/
def mk {w : ℕ} (c : Bool) (t r y d : Cfg (Fin w)) : Cfg (LocW w)
  | .ctl => c
  | .tgt i => t i
  | .ref i => r i
  | .cpy i => y i
  | .dum i => d i

/-! ### The circuit -/

section Circuit

variable {w : ℕ} {J : Type*}

/-- `X` on `t` under the literals `cs`. -/
def cx (cs : List (LocW w × Bool)) (t : LocW w) : Gate (LocW w) := ⟨cs, t, pauliX⟩

/-- Copy the reference into the copy register. -/
def copyG (w : ℕ) : List (Gate (LocW w)) :=
  (List.finRange w).flatMap (fun i => [cx [(.ref i, true)] (.cpy i)])

/-- The XOR translation `W_y : x ↦ x ⊕ x_* ⊕ y` on the target, with `y` read from the copy
register, under the literals `cs`. -/
def xorG (xs : Cfg (Fin w)) (cs : List (LocW w × Bool)) : List (Gate (LocW w)) :=
  (List.finRange w).flatMap (fun i =>
    cx ((.cpy i, true) :: cs) (.tgt i) :: (if xs i then [cx cs (.tgt i)] else []))

/-- Swap the target and the dummy on the inactive branch. -/
def swapG (w : ℕ) : List (Gate (LocW w)) :=
  (List.finRange w).flatMap (fun i =>
    [cx [(.tgt i, true)] (.dum i), cx [(.ctl, false), (.dum i, true)] (.tgt i),
      cx [(.tgt i, true)] (.dum i)])

/-- **The two-query reference preparation.** -/
def prepL (w : ℕ) (j : J) : List (NInstr (LocW w) (Fin w) J) :=
  [NInstr.call j false (refE w)] ++ nGatesOf (copyG w) ++ [NInstr.call j true (refE w)]

/-- **The controlled locator**: the reference preparation, `V = W_{y_*}† U` on the target swapped
with the dummy on the inactive branch, the controlled `W_{y_*}`, and the reversed reference
preparation. -/
def ctrlLoc (j : J) (xs : Cfg (Fin w)) : List (NInstr (LocW w) (Fin w) J) :=
  prepL w j ++ nGatesOf (swapG w) ++ [NInstr.call j false (tgtE w)] ++ nGatesOf (xorG xs []) ++
    nGatesOf (swapG w) ++ nGatesOf (xorG xs [(.ctl, true)]) ++ prepL w j

/-- Clean work wires: the reference and the dummy in `x_*`, the copy register zero. -/
def LocClean (xs : Cfg (Fin w)) (x : Cfg (LocW w)) : Prop :=
  (∀ i, x (.ref i) = xs i) ∧ (∀ i, x (.cpy i) = false) ∧ (∀ i, x (.dum i) = xs i)

end Circuit

/-! ### Counts and validity -/

section Counts

variable {w : ℕ} {J : Type*}

theorem length_flatMap_le {α β : Type*} (l : List α) (f : α → List β) (k : ℕ)
    (h : ∀ a ∈ l, (f a).length ≤ k) : (l.flatMap f).length ≤ k * l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
      rw [List.flatMap_cons, List.length_append, List.length_cons]
      have h1 := h a List.mem_cons_self
      have h2 := ih (fun b hb => h b (List.mem_cons_of_mem a hb))
      nlinarith

theorem length_copyG : (copyG w).length ≤ w := by
  have h := length_flatMap_le (List.finRange w) (fun i => [cx [(LocW.ref i, true)] (LocW.cpy i)]) 1
    (fun _ _ => le_refl _)
  rw [List.length_finRange, one_mul] at h
  exact h

theorem length_swapG : (swapG w).length ≤ 3 * w := by
  have h := length_flatMap_le (List.finRange w) (fun i =>
    [cx [(LocW.tgt i, true)] (LocW.dum i), cx [(LocW.ctl, false), (LocW.dum i, true)] (LocW.tgt i),
      cx [(LocW.tgt i, true)] (LocW.dum i)]) 3 (fun _ _ => le_refl _)
  rw [List.length_finRange] at h
  exact h

theorem length_xorG (xs : Cfg (Fin w)) (cs : List (LocW w × Bool)) :
    (xorG xs cs).length ≤ 2 * w := by
  have h := length_flatMap_le (List.finRange w) (fun i =>
    cx ((LocW.cpy i, true) :: cs) (LocW.tgt i) :: (if xs i then [cx cs (LocW.tgt i)] else [])) 2
    (fun i _ => by split_ifs <;> simp)
  rw [List.length_finRange] at h
  exact h

theorem nCallsN_call (p : J → Bool) (j : J) (adj : Bool) (pos : Fin w ↪ LocW w) :
    nCallsN p [(NInstr.call j adj pos : NInstr (LocW w) (Fin w) J)] = if p j then 1 else 0 := by
  simp [nCallsN, NInstr.isCall]

theorem nGatesN_call (j : J) (adj : Bool) (pos : Fin w ↪ LocW w) :
    nGatesN [(NInstr.call j adj pos : NInstr (LocW w) (Fin w) J)] = 0 := by
  simp [nGatesN, NInstr.isGate]

/-- **Five primitive queries.** -/
theorem ctrlLoc_nCalls (p : J → Bool) (j : J) (xs : Cfg (Fin w)) :
    nCallsN p (ctrlLoc j xs) = if p j then 5 else 0 := by
  simp only [ctrlLoc, prepL, nCallsN_append, nCallsN_nGatesOf, nCallsN_call]
  split_ifs <;> rfl

/-- **At most `12 w` elementary gates.** -/
theorem ctrlLoc_nGates (j : J) (xs : Cfg (Fin w)) : nGatesN (ctrlLoc j xs) ≤ 12 * w := by
  simp only [ctrlLoc, prepL, nGatesN_append, nGatesN_nGatesOf, nGatesN_call]
  have := length_copyG (w := w)
  have := length_swapG (w := w)
  have := length_xorG xs []
  have := length_xorG xs [(LocW.ctl, true)]
  omega

theorem cx_ok (cs : List (LocW w × Bool)) (t : LocW w) (hcs : cs.length ≤ 3)
    (ht : ∀ c ∈ cs, c.1 ≠ t) : GateOK 3 (cx cs t) :=
  ⟨hcs, ht, pauliX_unitary⟩

theorem copyG_ok : ∀ g ∈ copyG w, GateOK 3 g := by
  intro g hg
  simp only [copyG, List.mem_flatMap, List.mem_singleton] at hg
  obtain ⟨i, -, rfl⟩ := hg
  exact cx_ok _ _ (by simp) (by simp)

theorem swapG_ok : ∀ g ∈ swapG w, GateOK 3 g := by
  intro g hg
  simp only [swapG, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hg
  obtain ⟨i, -, rfl | rfl | rfl⟩ := hg <;> exact cx_ok _ _ (by simp) (by simp)

theorem xorG_ok (xs : Cfg (Fin w)) (cs : List (LocW w × Bool)) (hcs : cs.length ≤ 2)
    (ht : ∀ i, ∀ c ∈ cs, c.1 ≠ LocW.tgt i) : ∀ g ∈ xorG xs cs, GateOK 3 g := by
  intro g hg
  simp only [xorG, List.mem_flatMap, List.mem_cons] at hg
  obtain ⟨i, -, hg⟩ := hg
  rcases hg with rfl | hg
  · refine cx_ok _ _ (by simp; omega) ?_
    intro c hc
    simp only [List.mem_cons] at hc
    rcases hc with rfl | hc
    · simp
    · exact ht i c hc
  · split_ifs at hg
    · simp only [List.mem_singleton] at hg
      subst hg
      exact cx_ok _ _ (by omega) (ht i)
    · simp at hg

/-- **Every instruction is valid**: each gate is an `X` gate with at most three controls off its
target (`GateOK 3`). -/
theorem ctrlLoc_valid (j : J) (xs : Cfg (Fin w)) : ∀ i ∈ ctrlLoc j xs, i.Valid := by
  have hP : ∀ i ∈ prepL (J := J) w j, i.Valid := by
    intro i hi
    simp only [prepL, List.mem_append, List.mem_singleton] at hi
    rcases hi with (rfl | hi) | rfl
    · trivial
    · exact valid_nGatesOf _ copyG_ok i hi
    · trivial
  have hx0 := xorG_ok xs [] (by simp) (by simp)
  have hx1 := xorG_ok xs [(LocW.ctl, true)] (by simp) (by simp)
  intro i hi
  simp only [ctrlLoc, List.mem_append, List.mem_singleton] at hi
  rcases hi with (((((hi | hi) | rfl) | hi) | hi) | hi) | hi
  · exact hP i hi
  · exact valid_nGatesOf _ swapG_ok i hi
  · trivial
  · exact valid_nGatesOf _ hx0 i hi
  · exact valid_nGatesOf _ swapG_ok i hi
  · exact valid_nGatesOf _ hx1 i hi
  · exact hP i hi

end Counts

/-! ### Classical gate lists on the word wires -/

section Cfg

variable {w : ℕ}

theorem cfgRun_apply_of_ne {W : Type*} [DecidableEq W] (gs : List (Gate W)) (x : Cfg W) (v : W)
    (hv : ∀ g ∈ gs, g.t ≠ v) : cfgRun gs x v = x v := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
      change cfgRun gs (flipCfg g.cs g.t x) v = x v
      rw [ih _ (fun g' hg' => hv g' (List.mem_cons_of_mem _ hg'))]
      unfold flipCfg
      split_ifs
      · exact Function.update_of_ne (hv g List.mem_cons_self).symm _ _
      · rfl

/-- A gate list on the wires of index `i`, reading at most the control besides. -/
def LocalTo (i : Fin w) (gs : List (Gate (LocW w))) : Prop :=
  ∀ g ∈ gs, g.t.idx = some i ∧ ∀ c ∈ g.cs, c.1 = LocW.ctl ∨ c.1.idx = some i

/-- Agreement on the control and on the wires of index `i`. -/
def AgreeI (i : Fin w) (x x' : Cfg (LocW w)) : Prop :=
  x LocW.ctl = x' LocW.ctl ∧ ∀ v : LocW w, v.idx = some i → x v = x' v

theorem cfgRun_out {i : Fin w} {gs : List (Gate (LocW w))} (h : LocalTo i gs) (x : Cfg (LocW w))
    (v : LocW w) (hv : v.idx ≠ some i) : cfgRun gs x v = x v :=
  cfgRun_apply_of_ne gs x v (fun g hg e => hv (e ▸ (h g hg).1))

theorem cfgRun_agree {i : Fin w} {gs : List (Gate (LocW w))} (h : LocalTo i gs)
    {x x' : Cfg (LocW w)} (hx : AgreeI i x x') : AgreeI i (cfgRun gs x) (cfgRun gs x') := by
  induction gs generalizing x x' with
  | nil => exact hx
  | cons g gs ih =>
      apply ih (fun g' hg' => h g' (List.mem_cons_of_mem _ hg'))
      obtain ⟨ht, hc⟩ := h g List.mem_cons_self
      have hxc : ∀ c ∈ g.cs, x c.1 = x' c.1 := fun c hc' => by
        rcases hc c hc' with e | e
        · rw [e]; exact hx.1
        · exact hx.2 _ e
      have hok : ctrlOK g.cs x = ctrlOK g.cs x' := by
        apply Bool.eq_iff_iff.mpr
        rw [ctrlOK_iff, ctrlOK_iff]
        constructor
        · intro h' c hc'
          rw [← hxc c hc']
          exact h' c hc'
        · intro h' c hc'
          rw [hxc c hc']
          exact h' c hc'
      have hct : LocW.ctl ≠ g.t := by
        intro e
        rw [← e] at ht
        cases ht
      unfold flipCfg
      rw [hok]
      split_ifs
      · refine ⟨?_, ?_⟩
        · rw [Function.update_of_ne hct, Function.update_of_ne hct]
          exact hx.1
        · intro v hv
          by_cases hvt : v = g.t
          · subst hvt
            rw [Function.update_self, Function.update_self, hx.2 _ ht]
          · rw [Function.update_of_ne hvt, Function.update_of_ne hvt]
            exact hx.2 v hv
      · exact hx

theorem cfgRun_flatMap_some (gs : Fin w → List (Gate (LocW w))) (hgs : ∀ i, LocalTo i (gs i))
    (l : List (Fin w)) (hl : l.Nodup) (x : Cfg (LocW w)) (v : LocW w) (i : Fin w)
    (hv : v.idx = some i) :
    cfgRun (l.flatMap gs) x v = if i ∈ l then cfgRun (gs i) x v else x v := by
  induction l generalizing x with
  | nil => simp [cfgRun]
  | cons a l ih =>
      rw [List.flatMap_cons, cfgRun_append, ih (List.nodup_cons.mp hl).2]
      have ha : a ∉ l := (List.nodup_cons.mp hl).1
      by_cases hil : i ∈ l
      · have hia : i ≠ a := fun e => ha (e ▸ hil)
        rw [if_pos hil, if_pos (List.mem_cons_of_mem a hil)]
        have hag : AgreeI i (cfgRun (gs a) x) x := by
          refine ⟨cfgRun_out (hgs a) x _ (by simp [LocW.idx]), ?_⟩
          intro v' hv'
          exact cfgRun_out (hgs a) x v' (by rw [hv']; simpa using hia)
        exact (cfgRun_agree (hgs i) hag).2 v hv
      · rw [if_neg hil]
        by_cases hia : i = a
        · subst hia
          rw [if_pos List.mem_cons_self]
        · rw [if_neg (by simp [hia, hil])]
          exact cfgRun_out (hgs a) x v (by rw [hv]; simpa using hia)

theorem cfgRun_flatMap_ctl (gs : Fin w → List (Gate (LocW w))) (hgs : ∀ i, LocalTo i (gs i))
    (l : List (Fin w)) (x : Cfg (LocW w)) : cfgRun (l.flatMap gs) x LocW.ctl = x LocW.ctl := by
  induction l generalizing x with
  | nil => rfl
  | cons a l ih =>
      rw [List.flatMap_cons, cfgRun_append, ih]
      exact cfgRun_out (hgs a) x _ (by simp [LocW.idx])

theorem localTo_copy (i : Fin w) : LocalTo i [cx [(LocW.ref i, true)] (LocW.cpy i)] := by
  intro g hg
  simp only [List.mem_singleton] at hg
  subst hg
  refine ⟨rfl, ?_⟩
  intro c hc
  simp only [cx, List.mem_singleton] at hc
  subst hc
  exact Or.inr rfl

theorem localTo_xor (xs : Cfg (Fin w)) (cs : List (LocW w × Bool))
    (hcs : ∀ c ∈ cs, c.1 = LocW.ctl) (i : Fin w) :
    LocalTo i (cx ((LocW.cpy i, true) :: cs) (LocW.tgt i) ::
      (if xs i then [cx cs (LocW.tgt i)] else [])) := by
  intro g hg
  simp only [List.mem_cons] at hg
  rcases hg with rfl | hg
  · refine ⟨rfl, ?_⟩
    intro c hc
    simp only [cx, List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact Or.inr rfl
    · exact Or.inl (hcs c hc)
  · split_ifs at hg
    · simp only [List.mem_singleton] at hg
      subst hg
      exact ⟨rfl, fun c hc => Or.inl (hcs c hc)⟩
    · simp at hg

theorem localTo_swap (i : Fin w) :
    LocalTo i [cx [(LocW.tgt i, true)] (LocW.dum i), cx [(LocW.ctl, false), (LocW.dum i, true)]
      (LocW.tgt i), cx [(LocW.tgt i, true)] (LocW.dum i)] := by
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl <;> refine ⟨rfl, ?_⟩ <;> intro c hc <;>
    simp only [cx, List.mem_cons, List.not_mem_nil, or_false] at hc
  · subst hc; exact Or.inr rfl
  · rcases hc with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · subst hc; exact Or.inr rfl

/-- **The copy register XOR the reference.** -/
theorem cfgRun_copyG (c : Bool) (t r y d : Cfg (Fin w)) :
    cfgRun (copyG w) (mk c t r y d) = mk c t r (fun i => y i ^^ r i) d := by
  funext v
  cases v with
  | ctl => exact cfgRun_flatMap_ctl _ localTo_copy _ _
  | tgt i =>
      rw [copyG, cfgRun_flatMap_some _ localTo_copy _ (List.nodup_finRange w) _ _ i rfl]
      simp [cfgRun, flipCfg, cx, mk, ctrlOK, ite_apply]
  | ref i =>
      rw [copyG, cfgRun_flatMap_some _ localTo_copy _ (List.nodup_finRange w) _ _ i rfl]
      simp [cfgRun, flipCfg, cx, mk, ctrlOK, ite_apply]
  | cpy i =>
      rw [copyG, cfgRun_flatMap_some _ localTo_copy _ (List.nodup_finRange w) _ _ i rfl]
      cases hr : r i <;> cases hy : y i <;>
        simp [hr, hy, cfgRun, flipCfg, cx, mk, ctrlOK]
  | dum i =>
      rw [copyG, cfgRun_flatMap_some _ localTo_copy _ (List.nodup_finRange w) _ _ i rfl]
      simp [cfgRun, flipCfg, cx, mk, ctrlOK, ite_apply]

/-- **The XOR translation `W_y`.** -/
theorem cfgRun_xorG_nil (xs : Cfg (Fin w)) (c : Bool) (t r y d : Cfg (Fin w)) :
    cfgRun (xorG xs []) (mk c t r y d) = mk c (fun i => (t i ^^ y i) ^^ xs i) r y d := by
  have hl := localTo_xor xs ([] : List (LocW w × Bool)) (by simp)
  funext v
  cases v with
  | ctl => exact cfgRun_flatMap_ctl _ hl _ _
  | tgt i =>
      rw [xorG, cfgRun_flatMap_some _ hl _ (List.nodup_finRange w) _ _ i rfl]
      cases hx : xs i <;> cases ht : t i <;> cases hy : y i <;>
        simp [hx, ht, hy, cfgRun, flipCfg, cx, mk, ctrlOK, Function.update_apply]
  | ref i =>
      rw [xorG, cfgRun_flatMap_some _ hl _ (List.nodup_finRange w) _ _ i rfl]
      cases hx : xs i <;> simp [cfgRun, flipCfg, cx, mk, ctrlOK, ite_apply, Function.update_apply]
  | cpy i =>
      rw [xorG, cfgRun_flatMap_some _ hl _ (List.nodup_finRange w) _ _ i rfl]
      cases hx : xs i <;> simp [cfgRun, flipCfg, cx, mk, ctrlOK, ite_apply, Function.update_apply]
  | dum i =>
      rw [xorG, cfgRun_flatMap_some _ hl _ (List.nodup_finRange w) _ _ i rfl]
      cases hx : xs i <;> simp [cfgRun, flipCfg, cx, mk, ctrlOK, ite_apply, Function.update_apply]

/-- **The controlled XOR translation.** -/
theorem cfgRun_xorG_ctl (xs : Cfg (Fin w)) (c : Bool) (t r y d : Cfg (Fin w)) :
    cfgRun (xorG xs [(LocW.ctl, true)]) (mk c t r y d) =
      mk c (fun i => if c then (t i ^^ y i) ^^ xs i else t i) r y d := by
  have hl := localTo_xor xs [(LocW.ctl, true)] (by simp)
  funext v
  cases v with
  | ctl => exact cfgRun_flatMap_ctl _ hl _ _
  | tgt i =>
      rw [xorG, cfgRun_flatMap_some _ hl _ (List.nodup_finRange w) _ _ i rfl]
      cases hc : c <;> cases hx : xs i <;> cases ht : t i <;> cases hy : y i <;>
        simp [hx, ht, hy, cfgRun, flipCfg, cx, mk, ctrlOK, Function.update_apply]
  | ref i =>
      rw [xorG, cfgRun_flatMap_some _ hl _ (List.nodup_finRange w) _ _ i rfl]
      cases hx : xs i <;> simp [cfgRun, flipCfg, cx, mk, ctrlOK, ite_apply, Function.update_apply]
  | cpy i =>
      rw [xorG, cfgRun_flatMap_some _ hl _ (List.nodup_finRange w) _ _ i rfl]
      cases hx : xs i <;> simp [cfgRun, flipCfg, cx, mk, ctrlOK, ite_apply, Function.update_apply]
  | dum i =>
      rw [xorG, cfgRun_flatMap_some _ hl _ (List.nodup_finRange w) _ _ i rfl]
      cases hx : xs i <;> simp [cfgRun, flipCfg, cx, mk, ctrlOK, ite_apply, Function.update_apply]

/-- **The swap on the inactive branch**, active. -/
theorem cfgRun_swapG_true (t r y d : Cfg (Fin w)) :
    cfgRun (swapG w) (mk true t r y d) = mk true t r y d := by
  funext v
  cases v with
  | ctl => exact cfgRun_flatMap_ctl _ localTo_swap _ _
  | tgt i =>
      rw [swapG, cfgRun_flatMap_some _ localTo_swap _ (List.nodup_finRange w) _ _ i rfl]
      cases ht : t i <;> cases hd : d i <;>
        simp [ht, hd, cfgRun, flipCfg, cx, mk, ctrlOK, Function.update_apply]
  | ref i =>
      rw [swapG, cfgRun_flatMap_some _ localTo_swap _ (List.nodup_finRange w) _ _ i rfl]
      simp [cfgRun, flipCfg, cx, mk, ctrlOK, ite_apply, Function.update_apply]
  | cpy i =>
      rw [swapG, cfgRun_flatMap_some _ localTo_swap _ (List.nodup_finRange w) _ _ i rfl]
      simp [cfgRun, flipCfg, cx, mk, ctrlOK, ite_apply, Function.update_apply]
  | dum i =>
      rw [swapG, cfgRun_flatMap_some _ localTo_swap _ (List.nodup_finRange w) _ _ i rfl]
      cases ht : t i <;> cases hd : d i <;>
        simp [ht, hd, cfgRun, flipCfg, cx, mk, ctrlOK, Function.update_apply]

/-- **The swap on the inactive branch**, inactive: the target and the dummy are exchanged. -/
theorem cfgRun_swapG_false (t r y d : Cfg (Fin w)) :
    cfgRun (swapG w) (mk false t r y d) = mk false d r y t := by
  funext v
  cases v with
  | ctl => exact cfgRun_flatMap_ctl _ localTo_swap _ _
  | tgt i =>
      rw [swapG, cfgRun_flatMap_some _ localTo_swap _ (List.nodup_finRange w) _ _ i rfl]
      cases ht : t i <;> cases hd : d i <;>
        simp [ht, hd, cfgRun, flipCfg, cx, mk, ctrlOK, Function.update_apply]
  | ref i =>
      rw [swapG, cfgRun_flatMap_some _ localTo_swap _ (List.nodup_finRange w) _ _ i rfl]
      simp [cfgRun, flipCfg, cx, mk, ctrlOK, ite_apply, Function.update_apply]
  | cpy i =>
      rw [swapG, cfgRun_flatMap_some _ localTo_swap _ (List.nodup_finRange w) _ _ i rfl]
      simp [cfgRun, flipCfg, cx, mk, ctrlOK, ite_apply, Function.update_apply]
  | dum i =>
      rw [swapG, cfgRun_flatMap_some _ localTo_swap _ (List.nodup_finRange w) _ _ i rfl]
      cases ht : t i <;> cases hd : d i <;>
        simp [ht, hd, cfgRun, flipCfg, cx, mk, ctrlOK, Function.update_apply]

theorem classical_of_cx (gs : List (Gate (LocW w))) (h : ∀ g ∈ gs, g.u = pauliX)
    (hok : ∀ g ∈ gs, GateOK 3 g) : Classical gs :=
  fun g hg => ⟨h g hg, (hok g hg).2.1⟩

theorem copyG_classical : Classical (copyG w) := by
  refine classical_of_cx _ ?_ copyG_ok
  intro g hg
  simp only [copyG, List.mem_flatMap, List.mem_singleton] at hg
  obtain ⟨i, -, rfl⟩ := hg
  rfl

theorem swapG_classical : Classical (swapG w) := by
  refine classical_of_cx _ ?_ swapG_ok
  intro g hg
  simp only [swapG, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hg
  obtain ⟨i, -, rfl | rfl | rfl⟩ := hg <;> rfl

theorem xorG_classical (xs : Cfg (Fin w)) (cs : List (LocW w × Bool)) (hcs : cs.length ≤ 2)
    (ht : ∀ i, ∀ c ∈ cs, c.1 ≠ LocW.tgt i) : Classical (xorG xs cs) := by
  refine classical_of_cx _ ?_ (xorG_ok xs cs hcs ht)
  intro g hg
  simp only [xorG, List.mem_flatMap, List.mem_cons] at hg
  obtain ⟨i, -, hg⟩ := hg
  rcases hg with rfl | hg
  · rfl
  · split_ifs at hg
    · simp only [List.mem_singleton] at hg
      subst hg
      rfl
    · simp at hg

end Cfg

/-! ### Zero-initialised work wires -/

section Zero

variable {w : ℕ} {J : Type*}

/-- `X` gates writing `x_*` into the reference and the dummy. -/
def setG (xs : Cfg (Fin w)) : List (Gate (LocW w)) :=
  (List.finRange w).flatMap (fun i => if xs i then [cx [] (.ref i), cx [] (.dum i)] else [])

/-- **The controlled locator on zero-initialised work wires**: the reference and the dummy are
prepared in `x_*` by `X` gates, the controlled locator runs, and the `X` gates are undone. -/
def ctrlLoc0 (j : J) (xs : Cfg (Fin w)) : List (NInstr (LocW w) (Fin w) J) :=
  nGatesOf (setG xs) ++ ctrlLoc j xs ++ nGatesOf (setG xs)

/-- Zero work wires: the reference, the copy register and the dummy. -/
def LocZero (x : Cfg (LocW w)) : Prop :=
  (∀ i, x (.ref i) = false) ∧ (∀ i, x (.cpy i) = false) ∧ (∀ i, x (.dum i) = false)

theorem length_setG (xs : Cfg (Fin w)) : (setG xs).length ≤ 2 * w := by
  have h := length_flatMap_le (List.finRange w) (fun i =>
    if xs i then [cx [] (LocW.ref i), cx [] (LocW.dum i)] else []) 2
    (fun i _ => by split_ifs <;> simp)
  rw [List.length_finRange] at h
  exact h

theorem setG_ok (xs : Cfg (Fin w)) : ∀ g ∈ setG xs, GateOK 3 g := by
  intro g hg
  simp only [setG, List.mem_flatMap] at hg
  obtain ⟨i, -, hg⟩ := hg
  split_ifs at hg
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl <;> exact cx_ok _ _ (by simp) (by simp)
  · simp at hg

theorem setG_classical (xs : Cfg (Fin w)) : Classical (setG xs) := by
  refine classical_of_cx _ ?_ (setG_ok xs)
  intro g hg
  simp only [setG, List.mem_flatMap] at hg
  obtain ⟨i, -, hg⟩ := hg
  split_ifs at hg
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl <;> rfl
  · simp at hg

theorem localTo_set (xs : Cfg (Fin w)) (i : Fin w) :
    LocalTo i (if xs i then [cx [] (LocW.ref i), cx [] (LocW.dum i)] else []) := by
  intro g hg
  split_ifs at hg
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl <;> exact ⟨rfl, fun c hc => by simp [cx] at hc⟩
  · simp at hg

/-- **The reference and the dummy XOR `x_*`.** -/
theorem cfgRun_setG (xs : Cfg (Fin w)) (c : Bool) (t r y d : Cfg (Fin w)) :
    cfgRun (setG xs) (mk c t r y d) = mk c t (fun i => r i ^^ xs i) y (fun i => d i ^^ xs i) := by
  have hl := localTo_set xs
  funext v
  cases v with
  | ctl => exact cfgRun_flatMap_ctl _ hl _ _
  | tgt i =>
      rw [setG, cfgRun_flatMap_some _ hl _ (List.nodup_finRange w) _ _ i rfl]
      cases hx : xs i <;> simp [cfgRun, flipCfg, cx, mk, ctrlOK, Function.update_apply]
  | ref i =>
      rw [setG, cfgRun_flatMap_some _ hl _ (List.nodup_finRange w) _ _ i rfl]
      cases hx : xs i <;> cases hr : r i <;>
        simp [hx, hr, cfgRun, flipCfg, cx, mk, ctrlOK, Function.update_apply]
  | cpy i =>
      rw [setG, cfgRun_flatMap_some _ hl _ (List.nodup_finRange w) _ _ i rfl]
      cases hx : xs i <;> simp [cfgRun, flipCfg, cx, mk, ctrlOK, Function.update_apply]
  | dum i =>
      rw [setG, cfgRun_flatMap_some _ hl _ (List.nodup_finRange w) _ _ i rfl]
      cases hx : xs i <;> cases hd : d i <;>
        simp [hx, hd, cfgRun, flipCfg, cx, mk, ctrlOK, Function.update_apply]

theorem cfgRun_setG_zero (xs : Cfg (Fin w)) (c : Bool) (t y : Cfg (Fin w)) :
    cfgRun (setG xs) (mk c t (fun _ => false) y (fun _ => false)) = mk c t xs y xs := by
  rw [cfgRun_setG]
  congr 1 <;> funext i <;> simp

theorem cfgRun_setG_xs (xs : Cfg (Fin w)) (c : Bool) (t y : Cfg (Fin w)) :
    cfgRun (setG xs) (mk c t xs y xs) = mk c t (fun _ => false) y (fun _ => false) := by
  rw [cfgRun_setG]
  congr 1 <;> funext i <;> simp

/-- **Five primitive queries** on zero-initialised work wires. -/
theorem ctrlLoc0_nCalls (p : J → Bool) (j : J) (xs : Cfg (Fin w)) :
    nCallsN p (ctrlLoc0 j xs) = if p j then 5 else 0 := by
  simp only [ctrlLoc0, nCallsN_append, nCallsN_nGatesOf, ctrlLoc_nCalls, zero_add, add_zero]

/-- **At most `16 w` elementary gates** on zero-initialised work wires. -/
theorem ctrlLoc0_nGates (j : J) (xs : Cfg (Fin w)) : nGatesN (ctrlLoc0 j xs) ≤ 16 * w := by
  simp only [ctrlLoc0, nGatesN_append, nGatesN_nGatesOf]
  have := ctrlLoc_nGates j xs
  have := length_setG xs
  omega

theorem ctrlLoc0_valid (j : J) (xs : Cfg (Fin w)) : ∀ i ∈ ctrlLoc0 j xs, i.Valid := by
  intro i hi
  simp only [ctrlLoc0, List.mem_append] at hi
  rcases hi with (hi | hi) | hi
  · exact valid_nGatesOf _ (setG_ok xs) i hi
  · exact ctrlLoc_valid j xs i hi
  · exact valid_nGatesOf _ (setG_ok xs) i hi

end Zero

/-! ### The controlled locator -/

section Sem

variable {w : ℕ} {J : Type*}
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- **The controlled `U`** on the target word. -/
def ctrlU (U : Reg (Fin w) R →L[ℂ] Reg (Fin w) R) : Reg (LocW w) R →L[ℂ] Reg (LocW w) R :=
  localOp (tgtE w) (tgtE w).injective (fun x => if x LocW.ctl then U else 1)

omit [CompleteSpace R] in
theorem put_add' {W A : Type*} [Fintype W] [DecidableEq W] [Fintype A] [DecidableEq A]
    {ι : A → W} (hι : Function.Injective ι) (x : Cfg W) (φ φ' : Reg A R) :
    put ι hι x (φ + φ') = put ι hι x φ + put ι hι x φ' := by
  simp only [put, Pi.single_add, WithLp.toLp_add, map_add]

omit [CompleteSpace R] in
theorem put_zero' {W A : Type*} [Fintype W] [DecidableEq W] [Fintype A] [DecidableEq A]
    {ι : A → W} (hι : Function.Injective ι) (x : Cfg W) : put ι hι x (0 : Reg A R) = 0 := by
  simp only [put, Pi.single_zero, WithLp.toLp_zero, map_zero]

omit [CompleteSpace R] in
theorem put_finset_sum {W A α : Type*} [Fintype W] [DecidableEq W] [Fintype A] [DecidableEq A]
    {ι : A → W} (hι : Function.Injective ι) (x : Cfg W) (s : Finset α) (f : α → Reg A R) :
    put ι hι x (∑ a ∈ s, f a) = ∑ a ∈ s, put ι hι x (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, put_zero']
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, put_add', ih]

omit [CompleteSpace R] in
theorem put_ref (c : Bool) (t r y d r' : Cfg (Fin w)) (q : R) :
    put (refE w) (refE w).injective (mk c t r y d) (bas r' q) = bas (mk c t r' y d) q := by
  rw [put_bas]
  congr 1
  funext v
  cases v with
  | ref i => exact overwrite_apply_ι (refE w).injective _ _ i
  | ctl => exact overwrite_apply_out _ _ _ _ (fun a h => by simp [refE] at h)
  | tgt i => exact overwrite_apply_out _ _ _ _ (fun a h => by simp [refE] at h)
  | cpy i => exact overwrite_apply_out _ _ _ _ (fun a h => by simp [refE] at h)
  | dum i => exact overwrite_apply_out _ _ _ _ (fun a h => by simp [refE] at h)

omit [CompleteSpace R] in
theorem put_tgt (c : Bool) (t r y d t' : Cfg (Fin w)) (q : R) :
    put (tgtE w) (tgtE w).injective (mk c t r y d) (bas t' q) = bas (mk c t' r y d) q := by
  rw [put_bas]
  congr 1
  funext v
  cases v with
  | tgt i => exact overwrite_apply_ι (tgtE w).injective _ _ i
  | ctl => exact overwrite_apply_out _ _ _ _ (fun a h => by simp [tgtE] at h)
  | ref i => exact overwrite_apply_out _ _ _ _ (fun a h => by simp [tgtE] at h)
  | cpy i => exact overwrite_apply_out _ _ _ _ (fun a h => by simp [tgtE] at h)
  | dum i => exact overwrite_apply_out _ _ _ _ (fun a h => by simp [tgtE] at h)

omit [CompleteSpace R] in
theorem put_tgt_sum (c : Bool) (t r y d : Cfg (Fin w)) (φ : Reg (Fin w) R) :
    put (tgtE w) (tgtE w).injective (mk c t r y d) φ = ∑ z, bas (mk c z r y d) (φ z) := by
  conv_lhs => rw [← sum_bas φ]
  rw [put_finset_sum]
  exact Finset.sum_congr rfl (fun z _ => put_tgt c t r y d z (φ z))

theorem eval_call_ref (prim : J → Reg (Fin w) R →L[ℂ] Reg (Fin w) R) (j : J) (adj : Bool)
    (c : Bool) (t r y d : Cfg (Fin w)) (q : R) :
    (NInstr.call j adj (refE w) : NInstr (LocW w) (Fin w) J).eval prim (bas (mk c t r y d) q) =
      put (refE w) (refE w).injective (mk c t r y d) (adjIf adj (prim j) (bas r q)) := by
  rw [NInstr.eval_call, localOp_bas]
  rfl

theorem eval_call_tgt (prim : J → Reg (Fin w) R →L[ℂ] Reg (Fin w) R) (j : J) (adj : Bool)
    (c : Bool) (t r y d : Cfg (Fin w)) (q : R) :
    (NInstr.call j adj (tgtE w) : NInstr (LocW w) (Fin w) J).eval prim (bas (mk c t r y d) q) =
      put (tgtE w) (tgtE w).injective (mk c t r y d) (adjIf adj (prim j) (bas t q)) := by
  rw [NInstr.eval_call, localOp_bas]
  rfl

theorem ctrlU_bas (U : Reg (Fin w) R →L[ℂ] Reg (Fin w) R) (c : Bool) (t r y d : Cfg (Fin w))
    (q : R) : ctrlU U (bas (mk c t r y d) q) =
      put (tgtE w) (tgtE w).injective (mk c t r y d) ((if c then U else 1) (bas t q)) := by
  unfold ctrlU
  rw [localOp_bas]
  have hc : clearCfg (tgtE w) (mk c t r y d) LocW.ctl = c :=
    clearCfg_apply_out _ _ _ (fun a h => by simp [tgtE] at h)
  simp only [hc]
  rfl

variable (prim : J → Reg (Fin w) R →L[ℂ] Reg (Fin w) R) (j : J) (xs ys : Cfg (Fin w))

theorem adj_loc (hU : IsUnitary (prim j)) (hloc : ∀ q, prim j (bas xs q) = bas ys q) (q : R) :
    ((prim j)†) (bas ys q) = bas xs q := by
  rw [← hloc q]
  have := congrArg (fun F : Reg (Fin w) R →L[ℂ] Reg (Fin w) R => F (bas xs q)) hU.1
  simpa [star_eq_adjoint, mul_def] using this

/-- **The two-query reference preparation** XORs `y_* = U x_*` into the copy register and restores
the reference. -/
theorem nrun_prepL (hU : IsUnitary (prim j)) (hloc : ∀ q, prim j (bas xs q) = bas ys q)
    (c : Bool) (t y d : Cfg (Fin w)) (q : R) :
    nrun prim (prepL w j) (bas (mk c t xs y d) q) = bas (mk c t xs (fun i => y i ^^ ys i) d) q := by
  simp only [prepL, nrun_append, nrun_singleton, nrun_nGatesOf, comp_apply]
  rw [eval_call_ref]
  simp only [adjIf, Bool.false_eq_true, if_false]
  rw [hloc, put_ref, gRun_classical_bas _ copyG_classical, cfgRun_copyG, eval_call_ref]
  simp only [adjIf, if_true]
  rw [adj_loc prim j xs ys hU hloc, put_ref]

theorem xor_false_left (y : Cfg (Fin w)) : (fun i => (fun _ : Fin w => false) i ^^ y i) = y := by
  funext i
  simp

theorem xor_self' (y : Cfg (Fin w)) : (fun i => y i ^^ y i) = fun _ : Fin w => false := by
  funext i
  simp

/-- The active branch after the query on the target: `W_{y_*}` and its controlled copy cancel,
and the reference preparation restores the copy register. -/
theorem nrun_tail_true (hU : IsUnitary (prim j)) (hloc : ∀ q, prim j (bas xs q) = bas ys q)
    (t : Cfg (Fin w)) (φ : Reg (Fin w) R) :
    nrun prim (prepL w j) (gRun (xorG xs [(LocW.ctl, true)]) (gRun (swapG w) (gRun (xorG xs [])
      (put (tgtE w) (tgtE w).injective (mk true t xs ys xs) φ)))) =
      put (tgtE w) (tgtE w).injective (mk true t xs (fun _ => false) xs) φ := by
  rw [put_tgt_sum, put_tgt_sum]
  simp only [map_sum]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  rw [gRun_classical_bas _ (xorG_classical xs [] (by simp) (by simp)), cfgRun_xorG_nil,
    gRun_classical_bas _ swapG_classical, cfgRun_swapG_true,
    gRun_classical_bas _ (xorG_classical xs [(LocW.ctl, true)] (by simp) (by simp)),
    cfgRun_xorG_ctl, nrun_prepL prim j xs ys hU hloc, xor_self']
  congr 2
  funext i
  simp only [if_true]
  cases z i <;> cases ys i <;> cases xs i <;> rfl

/-- **The controlled locator on basis vectors with clean work wires.** -/
theorem ctrlLoc_bas (hU : IsUnitary (prim j)) (hloc : ∀ q, prim j (bas xs q) = bas ys q)
    (c : Bool) (t : Cfg (Fin w)) (q : R) :
    nrun prim (ctrlLoc j xs) (bas (mk c t xs (fun _ => false) xs) q) =
      ctrlU (prim j) (bas (mk c t xs (fun _ => false) xs) q) := by
  simp only [ctrlLoc, nrun_append, nrun_singleton, nrun_nGatesOf, comp_apply]
  rw [nrun_prepL prim j xs ys hU hloc, xor_false_left, ctrlU_bas]
  cases c with
  | true =>
      rw [gRun_classical_bas _ swapG_classical, cfgRun_swapG_true, eval_call_tgt]
      simp only [adjIf, Bool.false_eq_true, if_false, if_true]
      exact nrun_tail_true prim j xs ys hU hloc t _
  | false =>
      rw [gRun_classical_bas _ swapG_classical, cfgRun_swapG_false, eval_call_tgt]
      simp only [adjIf, Bool.false_eq_true, if_false]
      rw [hloc, put_tgt, gRun_classical_bas _ (xorG_classical xs [] (by simp) (by simp)),
        cfgRun_xorG_nil, gRun_classical_bas _ swapG_classical, cfgRun_swapG_false,
        gRun_classical_bas _ (xorG_classical xs [(LocW.ctl, true)] (by simp) (by simp)),
        cfgRun_xorG_ctl, nrun_prepL prim j xs ys hU hloc, xor_self', one_apply_eq_self,
        put_tgt]
      simp only [Bool.false_eq_true, if_false, Bool.xor_self, Bool.false_xor]

theorem eq_mk_of_clean {x : Cfg (LocW w)} (hx : LocClean xs x) :
    x = mk (x LocW.ctl) (fun i => x (LocW.tgt i)) xs (fun _ => false) xs := by
  obtain ⟨hr, hy, hd⟩ := hx
  funext v
  cases v with
  | ctl => rfl
  | tgt i => rfl
  | ref i => exact hr i
  | cpy i => exact hy i
  | dum i => exact hd i

/-- **The controlled locator (Section `gate:sec:native`).** On clean work wires the five-query
circuit is exactly the controlled `U` on the target, for every unitary `U` with `U|x_*⟩ = |y_*⟩`. -/
theorem ctrlLoc_agrees (hU : IsUnitary (prim j)) (hloc : ∀ q, prim j (bas xs q) = bas ys q) :
    Agrees (LocClean xs) (nrun prim (ctrlLoc j xs)) (ctrlU (prim j)) := by
  apply agrees_of_bas
  intro x hx q
  rw [eq_mk_of_clean xs hx]
  exact ctrlLoc_bas prim j xs ys hU hloc _ _ q

theorem ctrlU_isUnitary {U : Reg (Fin w) R →L[ℂ] Reg (Fin w) R} (hU : IsUnitary U) :
    IsUnitary (ctrlU U) := by
  refine localOp_isUnitary _ _ (fun x => ?_)
  split_ifs
  · exact hU
  · exact isUnitary_one

theorem ctrlU_adjoint (U : Reg (Fin w) R →L[ℂ] Reg (Fin w) R) : (ctrlU U)† = ctrlU (U†) := by
  unfold ctrlU
  rw [localOp_adjoint]
  congr 1
  funext x
  split_ifs
  · rfl
  · exact adjoint_one

theorem preserves_ctrlU (U : Reg (Fin w) R →L[ℂ] Reg (Fin w) R) :
    Preserves (LocClean xs) (ctrlU U) := by
  apply preserves_localOp
  intro y b ⟨hr, hy, hd⟩
  refine ⟨fun i => ?_, fun i => ?_, fun i => ?_⟩
  · rw [overwrite_apply_out _ _ _ _ (fun a h => by simp [tgtE] at h)]
    exact hr i
  · rw [overwrite_apply_out _ _ _ _ (fun a h => by simp [tgtE] at h)]
    exact hy i
  · rw [overwrite_apply_out _ _ _ _ (fun a h => by simp [tgtE] at h)]
    exact hd i

/-- **The reversed circuit controls `U†`.** -/
theorem ctrlLoc_inv_agrees (hprim : ∀ j, IsUnitary (prim j))
    (hloc : ∀ q, prim j (bas xs q) = bas ys q) :
    Agrees (LocClean xs) (nrun prim (ninv (ctrlLoc j xs))) (ctrlU ((prim j)†)) := by
  rw [nrun_ninv, ← ctrlU_adjoint]
  refine Agrees.adjoint (ctrlLoc_agrees prim j xs ys (hprim j) hloc)
    (nrun_isUnitary prim hprim _ (ctrlLoc_valid j xs)) (ctrlU_isUnitary (hprim j)) ?_
  rw [ctrlU_adjoint]
  exact preserves_ctrlU xs _

theorem eq_mk_of_zero {x : Cfg (LocW w)} (hx : LocZero x) :
    x = mk (x LocW.ctl) (fun i => x (LocW.tgt i)) (fun _ => false) (fun _ => false)
      (fun _ => false) := by
  obtain ⟨hr, hy, hd⟩ := hx
  funext v
  cases v with
  | ctl => rfl
  | tgt i => rfl
  | ref i => exact hr i
  | cpy i => exact hy i
  | dum i => exact hd i

/-- **The controlled locator on zero-initialised work wires** is exactly the controlled `U` on the
target, for every unitary `U` with `U|x_*⟩ = |y_*⟩`. -/
theorem ctrlLoc0_agrees (hU : IsUnitary (prim j)) (hloc : ∀ q, prim j (bas xs q) = bas ys q) :
    Agrees LocZero (nrun prim (ctrlLoc0 j xs)) (ctrlU (prim j)) := by
  apply agrees_of_bas
  intro x hx q
  rw [eq_mk_of_zero hx]
  simp only [ctrlLoc0, nrun_append, nrun_nGatesOf, comp_apply]
  rw [gRun_classical_bas _ (setG_classical xs), cfgRun_setG_zero,
    ctrlLoc_bas prim j xs ys hU hloc, ctrlU_bas, ctrlU_bas, put_tgt_sum, put_tgt_sum, map_sum]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  rw [gRun_classical_bas _ (setG_classical xs), cfgRun_setG_xs]

theorem preserves_ctrlU0 (U : Reg (Fin w) R →L[ℂ] Reg (Fin w) R) :
    Preserves LocZero (ctrlU U) := by
  apply preserves_localOp
  intro y b ⟨hr, hy, hd⟩
  refine ⟨fun i => ?_, fun i => ?_, fun i => ?_⟩
  · rw [overwrite_apply_out _ _ _ _ (fun a h => by simp [tgtE] at h)]
    exact hr i
  · rw [overwrite_apply_out _ _ _ _ (fun a h => by simp [tgtE] at h)]
    exact hy i
  · rw [overwrite_apply_out _ _ _ _ (fun a h => by simp [tgtE] at h)]
    exact hd i

/-- **The reversed circuit on zero-initialised work wires controls `U†`.** -/
theorem ctrlLoc0_inv_agrees (hprim : ∀ j, IsUnitary (prim j))
    (hloc : ∀ q, prim j (bas xs q) = bas ys q) :
    Agrees LocZero (nrun prim (ninv (ctrlLoc0 j xs))) (ctrlU ((prim j)†)) := by
  rw [nrun_ninv, ← ctrlU_adjoint]
  refine Agrees.adjoint (ctrlLoc0_agrees prim j xs ys (hprim j) hloc)
    (nrun_isUnitary prim hprim _ (ctrlLoc0_valid j xs)) (ctrlU_isUnitary (hprim j)) ?_
  rw [ctrlU_adjoint]
  exact preserves_ctrlU0 _

end Sem

end

end GateOptimalPrecision
