import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Fin

/-!
# Classical reversible gates and bit-vector registers

A classical reversible circuit is a list of multiply controlled NOT gates (`CGate`): a gate
flips its target wire when all of its control literals hold. A gate whose controls avoid its
target is an involution, so the reversed list undoes a list (`crun_reverse`). Gates that only
mention wires of a set `S` leave the other wires alone and act on `S` through the values on
`S` (`crun_apply_of_not`, `crun_congr`, `crun_override`).

Registers are read as bit vectors (`readBV`, built from `ofBits`), so that ripple-carry
arithmetic can be compared with `BitVec` arithmetic. A bit source (`BSrc`) is a wire literal
or a constant; `BSrc.gates` XORs it into a target wire.
-/

set_option autoImplicit false

namespace SparseHamiltonian.GateBinary

/-- A classical reversible gate on the wires `W`: the target `t` is flipped when every
control literal `(c, b)` holds, that is `x c = b`. -/
structure CGate (W : Type*) where
  cs : List (W × Bool)
  t : W

section Gates

variable {W : Type*} [DecidableEq W]

/-- Every control literal holds. -/
def lits (cs : List (W × Bool)) (x : W → Bool) : Bool := cs.all (fun c => x c.1 == c.2)

/-- The configuration map of one gate. -/
def CGate.run (g : CGate W) (x : W → Bool) : W → Bool :=
  if lits g.cs x then Function.update x g.t (!x g.t) else x

/-- The configuration map of a gate list; the head acts first. -/
def crun : List (CGate W) → (W → Bool) → W → Bool
  | [], x => x
  | g :: gs, x => crun gs (g.run x)

@[simp] theorem crun_nil (x : W → Bool) : crun ([] : List (CGate W)) x = x := rfl

@[simp] theorem crun_cons (g : CGate W) (gs : List (CGate W)) (x : W → Bool) :
    crun (g :: gs) x = crun gs (g.run x) := rfl

theorem crun_append (gs hs : List (CGate W)) (x : W → Bool) :
    crun (gs ++ hs) x = crun hs (crun gs x) := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih => exact ih _

omit [DecidableEq W] in
/-- The control literals only see the control wires. -/
theorem lits_congr (cs : List (W × Bool)) (x x' : W → Bool) (h : ∀ c ∈ cs, x c.1 = x' c.1) :
    lits cs x = lits cs x' := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      simp only [lits, List.all_cons] at ih ⊢
      rw [h c List.mem_cons_self, ih (fun c' hc' => h c' (List.mem_cons_of_mem c hc'))]

/-- The controls of a gate are off its target. -/
def CGate.Proper (g : CGate W) : Prop := ∀ c ∈ g.cs, c.1 ≠ g.t

/-- A proper gate is an involution. -/
theorem CGate.run_run (g : CGate W) (hg : g.Proper) (x : W → Bool) : g.run (g.run x) = x := by
  have hl : lits g.cs (Function.update x g.t (!x g.t)) = lits g.cs x :=
    lits_congr _ _ _ (fun c hc => Function.update_of_ne (hg c hc) _ _)
  unfold CGate.run
  by_cases h : lits g.cs x = true
  · rw [if_pos h, if_pos (hl.trans h)]
    funext u
    by_cases hu : u = g.t
    · subst hu
      simp
    · simp [Function.update_of_ne hu]
  · rw [if_neg h, if_neg h]

/-- The reversed list of proper gates undoes the list. -/
theorem crun_reverse (gs : List (CGate W)) (h : ∀ g ∈ gs, g.Proper) (x : W → Bool) :
    crun gs.reverse (crun gs x) = x := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
      have h1 : crun (g :: gs).reverse (crun (g :: gs) x) =
          g.run (crun gs.reverse (crun gs (g.run x))) := by
        rw [List.reverse_cons, crun_append]
        rfl
      rw [h1, ih (fun g' hg' => h g' (List.mem_cons_of_mem g hg')) (g.run x),
        CGate.run_run g (h g List.mem_cons_self)]

/-- Every wire mentioned by a gate satisfies `S`. -/
def CGate.Within (S : W → Prop) (g : CGate W) : Prop := S g.t ∧ ∀ c ∈ g.cs, S c.1

/-- A gate does not change a wire other than its target. -/
theorem CGate.run_apply_of_ne (g : CGate W) (x : W → Bool) (u : W) (hu : u ≠ g.t) :
    g.run x u = x u := by
  unfold CGate.run
  split_ifs
  · exact Function.update_of_ne hu _ _
  · rfl

/-- Gates whose targets lie in `S` do not change the wires outside `S`. -/
theorem crun_apply_of_not (gs : List (CGate W)) (S : W → Prop) (h : ∀ g ∈ gs, S g.t)
    (x : W → Bool) (u : W) (hu : ¬ S u) : crun gs x u = x u := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
      rw [crun_cons, ih (fun g' hg' => h g' (List.mem_cons_of_mem g hg'))]
      exact g.run_apply_of_ne x u (fun he => hu (he ▸ h g List.mem_cons_self))

/-- A gate within `S` acts on `S` through the values on `S` only. -/
theorem CGate.run_congr (g : CGate W) (S : W → Prop) (hg : g.Within S) (x x' : W → Bool)
    (hx : ∀ u, S u → x u = x' u) (u : W) (hu : S u) : g.run x u = g.run x' u := by
  have hl : lits g.cs x = lits g.cs x' := lits_congr _ _ _ (fun c hc => hx _ (hg.2 c hc))
  unfold CGate.run
  rw [hl]
  split_ifs
  · by_cases he : u = g.t
    · subst he
      simp [hx _ hg.1]
    · simp [Function.update_of_ne he, hx u hu]
  · exact hx u hu

/-- Gates within `S` act on `S` through the values on `S` only. -/
theorem crun_congr (gs : List (CGate W)) (S : W → Prop) (h : ∀ g ∈ gs, g.Within S)
    (x x' : W → Bool) (hx : ∀ u, S u → x u = x' u) : ∀ u, S u → crun gs x u = crun gs x' u := by
  induction gs generalizing x x' with
  | nil => exact hx
  | cons g gs ih =>
      intro u hu
      exact ih (fun g' hg' => h g' (List.mem_cons_of_mem g hg')) _ _
        (fun v hv => g.run_congr S (h g List.mem_cons_self) x x' hx v hv) u hu

/-- Overriding the values outside `S` commutes with gates within `S`. -/
theorem crun_override (gs : List (CGate W)) (S : W → Prop) [DecidablePred S]
    (h : ∀ g ∈ gs, g.Within S) (x v : W → Bool) :
    crun gs (fun u => if S u then x u else v u) = fun u => if S u then crun gs x u else v u := by
  funext u
  by_cases hu : S u
  · rw [if_pos hu]
    exact crun_congr gs S h _ x (fun u' hu' => if_pos hu') u hu
  · rw [if_neg hu, crun_apply_of_not gs S (fun g hg => (h g hg).1) _ u hu, if_neg hu]

omit [DecidableEq W] in
/-- The gates of a list are proper. -/
theorem proper_append {gs hs : List (CGate W)} (h₁ : ∀ g ∈ gs, g.Proper)
    (h₂ : ∀ g ∈ hs, g.Proper) : ∀ g ∈ gs ++ hs, g.Proper := by
  intro g hg
  rcases List.mem_append.1 hg with hg | hg
  · exact h₁ g hg
  · exact h₂ g hg

end Gates

/-! ### Bit vectors read from wires -/

section Bits

/-- The bit vector of width `w` with bits `f 0, …, f (w - 1)`. -/
def ofBits : (ℕ → Bool) → (w : ℕ) → BitVec w
  | _, 0 => 0#0
  | f, w + 1 => (ofBits (fun i => f (i + 1)) w).concat (f 0)

theorem getLsbD_ofBits (f : ℕ → Bool) (w i : ℕ) :
    (ofBits f w).getLsbD i = (decide (i < w) && f i) := by
  induction w generalizing f i with
  | zero => simp [ofBits]
  | succ w ih =>
      rw [ofBits, BitVec.getLsbD_concat]
      rcases i with _ | i
      · simp
      · simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel, ih]
        congr 1
        simp

theorem ofBits_congr (f f' : ℕ → Bool) (w : ℕ) (h : ∀ i < w, f i = f' i) :
    ofBits f w = ofBits f' w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_ofBits, getLsbD_ofBits, h i hi]

theorem ofBits_getLsbD {w : ℕ} (v : BitVec w) : ofBits v.getLsbD w = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_ofBits]
  simp [hi]

variable {W : Type*}

/-- The bit vector of width `w` read from the wires `r 0, …, r (w - 1)`. -/
def readBV (r : ℕ → W) (w : ℕ) (x : W → Bool) : BitVec w := ofBits (fun i => x (r i)) w

theorem getLsbD_readBV (r : ℕ → W) (w : ℕ) (x : W → Bool) (i : ℕ) :
    (readBV r w x).getLsbD i = (decide (i < w) && x (r i)) :=
  getLsbD_ofBits _ w i

theorem readBV_congr (r : ℕ → W) (w : ℕ) (x x' : W → Bool) (h : ∀ i < w, x (r i) = x' (r i)) :
    readBV r w x = readBV r w x' :=
  ofBits_congr _ _ w h

end Bits

/-! ### Bit sources -/

section Sources

variable {W : Type*} [DecidableEq W]

/-- A bit source: a wire literal (`x u == pol`) or a constant. -/
inductive BSrc (W : Type*) where
  | lit (u : W) (pol : Bool)
  | const (b : Bool)

/-- The value of a bit source. -/
def BSrc.val : BSrc W → (W → Bool) → Bool
  | .lit u pol, x => x u == pol
  | .const b, _ => b

/-- The wire predicate `S` holds for the wire of the source, if any. -/
def BSrc.On (S : W → Prop) : BSrc W → Prop
  | .lit u _ => S u
  | .const _ => True

/-- The gates XOR-ing a bit source into the target `t`. -/
def BSrc.gates : BSrc W → W → List (CGate W)
  | .lit u pol, t => [⟨[(u, pol)], t⟩]
  | .const true, t => [⟨[], t⟩]
  | .const false, _ => []

omit [DecidableEq W] in
theorem BSrc.val_congr (s : BSrc W) (S : W → Prop) (hs : s.On S) (x x' : W → Bool)
    (h : ∀ u, S u → x u = x' u) : s.val x = s.val x' := by
  cases s with
  | lit u pol => simp only [BSrc.val, h u hs]
  | const b => rfl

omit [DecidableEq W] in
theorem BSrc.length_gates_le (s : BSrc W) (t : W) : (s.gates t).length ≤ 1 := by
  cases s with
  | lit u pol => simp [BSrc.gates]
  | const b => cases b <;> simp [BSrc.gates]

/-- XOR-ing a source into a wire it does not read. -/
theorem BSrc.crun_gates (s : BSrc W) (t : W) (hs : s.On (· ≠ t)) (x : W → Bool) :
    crun (s.gates t) x = Function.update x t (x t ^^ s.val x) := by
  cases s with
  | lit u pol =>
      simp only [BSrc.gates, crun_cons, crun_nil, CGate.run, lits, List.all_cons,
        List.all_nil, Bool.and_true, BSrc.val]
      have hu : u ≠ t := hs
      cases h : (x u == pol)
      · simp only [Bool.false_eq_true, if_false, Bool.xor_false]
        funext v
        by_cases hv : v = t
        · subst hv
          simp
        · simp [Function.update_of_ne hv]
      · simp only [if_true, Bool.xor_true]
  | const b =>
      cases b
      · simp only [BSrc.gates, crun_nil, BSrc.val, Bool.xor_false]
        funext v
        by_cases hv : v = t
        · subst hv
          simp
        · simp [Function.update_of_ne hv]
      · simp [BSrc.gates, CGate.run, lits, BSrc.val]

omit [DecidableEq W] in
/-- The gates of a source are proper when it does not read the target. -/
theorem BSrc.proper_gates (s : BSrc W) (t : W) (hs : s.On (· ≠ t)) :
    ∀ g ∈ s.gates t, g.Proper := by
  cases s with
  | lit u pol =>
      intro g hg
      simp only [BSrc.gates, List.mem_singleton] at hg
      subst hg
      intro c hc
      simp only [List.mem_singleton] at hc
      subst hc
      exact hs
  | const b =>
      cases b
      · simp [BSrc.gates]
      · intro g hg
        simp only [BSrc.gates, List.mem_singleton] at hg
        subst hg
        intro c hc
        simp at hc

omit [DecidableEq W] in
/-- The gates of a source only mention its wire and the target. -/
theorem BSrc.within_gates (s : BSrc W) (t : W) (S : W → Prop) (hs : s.On S) (ht : S t) :
    ∀ g ∈ s.gates t, g.Within S := by
  cases s with
  | lit u pol =>
      intro g hg
      simp only [BSrc.gates, List.mem_singleton] at hg
      subst hg
      refine ⟨ht, ?_⟩
      intro c hc
      simp only [List.mem_singleton] at hc
      subst hc
      exact hs
  | const b =>
      cases b
      · simp [BSrc.gates]
      · intro g hg
        simp only [BSrc.gates, List.mem_singleton] at hg
        subst hg
        exact ⟨ht, by simp⟩

omit [DecidableEq W] in
/-- The controls of the gates of a source. -/
theorem BSrc.cs_length_gates (s : BSrc W) (t : W) : ∀ g ∈ s.gates t, g.cs.length ≤ 1 := by
  cases s with
  | lit u pol =>
      intro g hg
      simp only [BSrc.gates, List.mem_singleton] at hg
      subst hg
      simp
  | const b =>
      cases b
      · simp [BSrc.gates]
      · intro g hg
        simp only [BSrc.gates, List.mem_singleton] at hg
        subst hg
        simp

omit [DecidableEq W] in
/-- The target of the gates of a source. -/
theorem BSrc.t_gates (s : BSrc W) (t : W) : ∀ g ∈ s.gates t, g.t = t := by
  cases s with
  | lit u pol =>
      intro g hg
      simp only [BSrc.gates, List.mem_singleton] at hg
      subst hg
      rfl
  | const b =>
      cases b
      · simp [BSrc.gates]
      · intro g hg
        simp only [BSrc.gates, List.mem_singleton] at hg
        subst hg
        rfl

end Sources

end SparseHamiltonian.GateBinary
