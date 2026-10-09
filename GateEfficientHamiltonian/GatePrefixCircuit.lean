import GateEfficientHamiltonian.GateDyadicBoundary
/-!
# A clean linear-size circuit for lower-prefix controlled rotations

Compiles with Lean/Mathlib 4.32.1. The computational basis has
`w` slot bits and `w` clean flags. A prefix gate is a NOT at position zero,
and otherwise a Toffoli with one negative control. A rotation gate has one
flag control and one slot target. Thus no unbounded-control operation is
assigned constant cost. The theorem is an equality of linear maps and hence
applies to arbitrary superpositions, not merely to individual basis words.
-/

noncomputable section
open scoped BigOperators
namespace SparseHamiltonian.GatePrefixCircuit

abbrev Word (w : ℕ) := Fin w → Bool

structure Configuration (w : ℕ) where
  slot : Word w
  flags : Word w

noncomputable instance configurationDecidableEq (w : ℕ) : DecidableEq (Configuration w) :=
  Classical.decEq _

/-- Enumerate configurations through their two finite Boolean registers. -/
instance configurationFintype (w : ℕ) : Fintype (Configuration w) :=
  Fintype.ofEquiv (Word w × Word w)
    { toFun := fun z => ⟨z.1, z.2⟩
      invFun := fun z => (z.slot, z.flags)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

@[ext] theorem Configuration.ext {w : ℕ} {a b : Configuration w}
    (hs : a.slot = b.slot) (hf : a.flags = b.flags) : a = b := by
  cases a; cases b; cases hs; cases hf; rfl

variable {w : ℕ}

def bit (x : Word w) (n : ℕ) : Bool :=
  if h : n < w then x ⟨n, h⟩ else false

@[simp] theorem bit_index (x : Word w) (j : Fin w) : bit x j.val = x j := by
  simp [bit, j.isLt]

def prefixBit (x : Word w) : ℕ → Bool
  | 0 => true
  | n + 1 => prefixBit x n && !(bit x n)

@[simp] theorem prefix_zero (x : Word w) : prefixBit x 0 = true := rfl

/-- Updating bit `j` leaves every lower-prefix predicate unchanged. -/
theorem prefix_update (x : Word w) (j : Fin w) (b : Bool)
    (n : ℕ) (hn : n ≤ j.val) :
    prefixBit (Function.update x j b) n = prefixBit x n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hn' : n ≤ j.val := by omega
      have hnlt : n < w := lt_of_lt_of_le (by omega : n < j.val) (Nat.le_of_lt j.isLt)
      have hne : (⟨n, hnlt⟩ : Fin w) ≠ j := by
        intro he
        have heval : n = j.val := congrArg (fun k : Fin w => k.val) he
        omega
      simp only [prefixBit, ih hn', bit, dif_pos hnlt]
      rw [Function.update_of_ne hne]

/-- Prefix flags below `n`; all other flags are zero. -/
def encoded (n : ℕ) (x : Word w) : Configuration w where
  slot := x
  flags := fun j => if j.val < n then prefixBit x j.val else false

@[simp] theorem encoded_zero (x : Word w) :
    (encoded 0 x).flags = fun _ => false := by
  funext j
  simp [encoded]

def previous (j : Fin w) (_hj : j.val ≠ 0) : Fin w :=
  ⟨j.val - 1, by omega⟩

/-- The control uses at most two wires, independent of the word size. -/
def prefixControl (j : Fin w) (z : Configuration w) : Bool :=
  if hj : j.val = 0 then true
  else z.flags (previous j hj) && !(z.slot (previous j hj))

/-- One NOT or one mixed-polarity Toffoli; target is flag `j`. -/
def togglePrefix (j : Fin w) (z : Configuration w) : Configuration w where
  slot := z.slot
  flags := Function.update z.flags j
    (if prefixControl j z then !(z.flags j) else z.flags j)

theorem previous_ne (j : Fin w) (hj : j.val ≠ 0) : previous j hj ≠ j := by
  intro he
  have := congrArg Fin.val he
  simp only [previous] at this
  omega

theorem prefixControl_toggle (j : Fin w) (z : Configuration w) :
    prefixControl j (togglePrefix j z) = prefixControl j z := by
  by_cases hj : j.val = 0
  · simp [prefixControl, hj]
  · simp [prefixControl, hj, togglePrefix, Function.update_of_ne (previous_ne j hj)]

/-- Every Boolean gate used in the construction is its own inverse. -/
theorem togglePrefix_involutive (j : Fin w) : Function.Involutive (togglePrefix j) := by
  intro z
  apply Configuration.ext
  · rfl
  · funext i
    by_cases hi : i = j
    · subst i
      change Function.update (togglePrefix j z).flags j
        (if prefixControl j (togglePrefix j z) then
          !((togglePrefix j z).flags j) else (togglePrefix j z).flags j) j = z.flags j
      rw [Function.update_self, prefixControl_toggle]
      simp only [togglePrefix, Function.update_self]
      cases h : prefixControl j z <;> simp
    · simp [togglePrefix, Function.update_of_ne hi]

/-- The local two-wire control agrees with the complete predicate already
stored in the previous clean flag. -/
theorem prefixControl_encoded (j : Fin w) (x : Word w) :
    prefixControl j (encoded j.val x) = prefixBit x j.val := by
  by_cases hj : j.val = 0
  · simp [prefixControl, hj]
  · have hp : (previous j hj).val < j.val := by simp [previous]; omega
    have hs : j.val = (j.val - 1) + 1 := by omega
    simp only [prefixControl, dif_neg hj, encoded, if_pos hp]
    conv_rhs => rw [hs]
    simp only [prefixBit]
    have hb : bit x (j.val - 1) = x (previous j hj) := bit_index x (previous j hj)
    rw [hb]
    rfl

/-- Compute one new flag. -/
theorem togglePrefix_encoded (j : Fin w) (x : Word w) :
    togglePrefix j (encoded j.val x) = encoded (j.val + 1) x := by
  apply Configuration.ext
  · rfl
  · funext i
    by_cases hi : i = j
    · subst i
      change Function.update (encoded j.val x).flags j
        (if prefixControl j (encoded j.val x) then
          !((encoded j.val x).flags j) else (encoded j.val x).flags j) j =
            (encoded (j.val + 1) x).flags j
      rw [Function.update_self, prefixControl_encoded]
      simp only [encoded, Nat.lt_irrefl, if_false, Nat.lt_succ_self, if_true]
      cases prefixBit x j.val <;> rfl
    · have hv : i.val ≠ j.val := fun h => hi (Fin.ext h)
      have hr : (i.val < j.val + 1) = (i.val < j.val) := propext (by omega)
      simp only [togglePrefix, Function.update_of_ne hi, encoded, hr]

/-- Erase the flag with the same elementary gate. -/
theorem togglePrefix_encoded_succ (j : Fin w) (x : Word w) :
    togglePrefix j (encoded (j.val + 1) x) = encoded j.val x := by
  rw [← togglePrefix_encoded j x]
  exact togglePrefix_involutive j (encoded j.val x)

/-- A changed target bit does not alter any currently live flag. -/
theorem encoded_update_slot (j : Fin w) (x : Word w) (b : Bool) :
    encoded (j.val + 1) (Function.update x j b) =
      { slot := Function.update x j b, flags := (encoded (j.val + 1) x).flags } := by
  apply Configuration.ext
  · rfl
  · funext i
    by_cases hi : i.val < j.val + 1
    · simpa only [encoded, if_pos hi] using
        prefix_update x j b i.val (by omega)
    · simp only [encoded, if_neg hi]

abbrev State (w : ℕ) := Configuration w →₀ ℂ
abbrev SlotState (w : ℕ) := Word w →₀ ℂ
abbrev Coefficients := Matrix Bool Bool ℂ

/-- Actual elementary syntax. The `rotate` constructor is a known one-control
single-qubit matrix, not a many-controlled black box. -/
inductive Gate (w : ℕ)
  | prefixBit (j : Fin w)
  | rotate (j : Fin w) (a : Coefficients)

/-- Matrix action of one controlled single-qubit rotation on basis states. -/
def rotateBasis (j : Fin w) (a : Coefficients) (z : Configuration w) : State w :=
  if z.flags j then
    ∑ b : Bool, a b (z.slot j) •
      Finsupp.single { slot := Function.update z.slot j b, flags := z.flags } 1
  else Finsupp.single z 1

/-- Each gate is interpreted by linear extension of its computational-basis
matrix columns. The entire semantics is complex linear. -/
def Gate.eval : Gate w → State w →ₗ[ℂ] State w
  | .prefixBit j => Finsupp.linearCombination ℂ
      (fun z => Finsupp.single (togglePrefix j z) 1)
  | .rotate j a => Finsupp.linearCombination ℂ (rotateBasis j a)

def embed (n : ℕ) : SlotState w →ₗ[ℂ] State w :=
  Finsupp.linearCombination ℂ (fun x => Finsupp.single (encoded n x) 1)

/-- Ideal rotation conditioned on all lower slot bits being zero. Its purpose
is to state correctness; only `Gate` constructors contribute actual gates. -/
def idealBasis (j : Fin w) (a : Coefficients) (x : Word w) : SlotState w :=
  if prefixBit x j.val then
    ∑ b : Bool, a b (x j) • Finsupp.single (Function.update x j b) 1
  else Finsupp.single x 1

def idealStep (j : Fin w) (a : Coefficients) : SlotState w →ₗ[ℂ] SlotState w :=
  Finsupp.linearCombination ℂ (idealBasis j a)


/-- Swapping the source and output of a one-bit update. -/
theorem update_exchange (j : Fin w) (x y : Word w) :
    Function.update y j (x j) = x ↔ y = Function.update x j (y j) := by
  constructor <;> intro h <;> funext k <;> by_cases hk : k = j
  · subst k; simp
  · have hh := congrFun h k
    simpa [Function.update_of_ne hk] using hh
  · subst k; simp
  · have hh := congrFun h k
    simpa [Function.update_of_ne hk] using hh

private theorem sum_single_update_input (j : Fin w) (x y : Word w)
    (c : ℂ) (t : Bool → ℂ) :
    (∑ b : Bool, t b * (Finsupp.single y c) (Function.update x j b)) =
      t (y j) * (Finsupp.single y c) (Function.update x j (y j)) := by
  classical
  apply Finset.sum_eq_single (y j)
  · intro b hb hne
    have hword : y ≠ Function.update x j b := by
      intro h
      have hh := congrFun h j
      simp only [Function.update_self] at hh
      exact hne hh.symm
    simp [hword]
  · simp

private theorem sum_single_update_output (j : Fin w) (x y : Word w)
    (c : ℂ) (t : Bool → ℂ) :
    (∑ b : Bool, t b * (Finsupp.single (Function.update y j b) c) x) =
      t (x j) * (Finsupp.single (Function.update y j (x j)) c) x := by
  classical
  apply Finset.sum_eq_single (x j)
  · intro b hb hne
    have hword : Function.update y j b ≠ x := by
      intro h
      have hh := congrFun h j
      simp only [Function.update_self] at hh
      exact hne hh
    simp [hword]
  · simp

/-- Coordinate (row-action) formula for a lower-prefix controlled step. -/
theorem idealStep_apply (j : Fin w) (a : Coefficients) (f : SlotState w) (x : Word w) :
    (idealStep j a f) x =
      if prefixBit x j.val then
        ∑ b : Bool, a (x j) b * f (Function.update x j b)
      else f x := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
      rw [map_add]
      simp only [Finsupp.add_apply, hf, hg]
      cases hp : prefixBit x j.val <;> simp [mul_add, Finset.sum_add_distrib]
  | single y c =>
      simp only [idealStep, Finsupp.linearCombination_single, Finsupp.smul_apply,
        smul_eq_mul, idealBasis]
      by_cases he : Function.update y j (x j) = x
      · have hp : prefixBit y j.val = prefixBit x j.val := by
          calc
            prefixBit y j.val = prefixBit (Function.update y j (x j)) j.val :=
              (prefix_update y j (x j) j.val le_rfl).symm
            _ = prefixBit x j.val := congrArg (fun z => prefixBit z j.val) he
        have he' := (update_exchange j x y).mp he
        cases h : prefixBit x j.val
        · simp [hp, h, Finsupp.single_apply]
        · simp only [hp, h, if_true, Finsupp.finsetSum_apply,
            Finsupp.smul_apply, smul_eq_mul]
          rw [sum_single_update_output, sum_single_update_input]
          simp only [Finsupp.single_apply, if_pos he, if_pos he', mul_one]
          ring
      · have he' : y ≠ Function.update x j (y j) := by
          intro h; exact he ((update_exchange j x y).mpr h)
        have hxy : y ≠ x := by
          intro h; subst y; exact he (Function.update_eq_self j x)
        cases hp : prefixBit y j.val <;> cases hx : prefixBit x j.val
          <;> simp only [Bool.false_eq_true, if_true, if_false,
            Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
          <;> (try simp only [sum_single_update_output, sum_single_update_input])
          <;> simp only [Finsupp.single_apply, if_neg he, if_neg he', if_neg hxy,
            mul_zero]

theorem prefix_gate_embed (j : Fin w) :
    (Gate.eval (.prefixBit j)).comp (embed j.val) = embed (j.val + 1) := by
  apply Finsupp.lhom_ext
  intro x c
  simp [Gate.eval, embed, togglePrefix_encoded]

theorem prefix_gate_unembed (j : Fin w) :
    (Gate.eval (.prefixBit j)).comp (embed (j.val + 1)) = embed j.val := by
  apply Finsupp.lhom_ext
  intro x c
  simp [Gate.eval, embed, togglePrefix_encoded_succ]

/-- The flag-controlled elementary gate agrees exactly with the ideal
many-controlled rotation on the invariant prefix-flag subspace. -/
theorem rotation_gate_embed (j : Fin w) (a : Coefficients) :
    (Gate.eval (.rotate j a)).comp (embed (j.val + 1)) =
      (embed (j.val + 1)).comp (idealStep j a) := by
  apply Finsupp.lhom_ext
  intro x c
  simp only [LinearMap.comp_apply, embed, Gate.eval, idealStep,
    Finsupp.linearCombination_single, map_smul]
  congr 1
  have hf : (encoded (j.val + 1) x).flags j = prefixBit x j.val := by
    simp [encoded]
  simp only [rotateBasis, idealBasis, hf]
  cases hp : prefixBit x j.val
  · simp
  · simp only [if_true, map_sum, map_smul,
      Finsupp.linearCombination_single, one_smul]
    apply Finset.sum_congr rfl
    intro b hb
    rw [encoded_update_slot]
    rfl

/-- Execute lists from left to right. -/
def run : List (Gate w) → State w →ₗ[ℂ] State w
  | [] => LinearMap.id
  | g :: gs => (run gs).comp g.eval

@[simp] theorem run_nil : run ([] : List (Gate w)) = LinearMap.id := rfl

@[simp] theorem run_append (gs hs : List (Gate w)) :
    run (gs ++ hs) = (run hs).comp (run gs) := by
  induction gs with
  | nil => simp [run]
  | cons g gs ih => simp [run, ih, LinearMap.comp_assoc]

/-- Prefix flag computation, with each added gate reading at most two bits. -/
def compute : (n : ℕ) → n ≤ w → List (Gate w)
  | 0, _ => []
  | n + 1, h => compute n (by omega) ++ [.prefixBit ⟨n, by omega⟩]

/-- Descending rotations erase flag `j` before any lower bit can change. -/
def descend (a : Fin w → Coefficients) : (n : ℕ) → n ≤ w → List (Gate w)
  | 0, _ => []
  | n + 1, h => [.rotate ⟨n, by omega⟩ (a ⟨n, by omega⟩),
      .prefixBit ⟨n, by omega⟩] ++ descend a n (by omega)

/-- The intended ordered product of lower-prefix controlled rotations. -/
def ideal (a : Fin w → Coefficients) : (n : ℕ) → n ≤ w → SlotState w →ₗ[ℂ] SlotState w
  | 0, _ => LinearMap.id
  | n + 1, h => (ideal a n (by omega)).comp (idealStep ⟨n, by omega⟩ (a ⟨n, by omega⟩))

theorem compute_correct (n : ℕ) (h : n ≤ w) :
    (run (compute n h)).comp (embed 0) = embed n := by
  induction n with
  | zero => simp [compute]
  | succ n ih =>
      rw [compute, run_append, LinearMap.comp_assoc, ih]
      simpa [run] using prefix_gate_embed (⟨n, by omega⟩ : Fin w)

theorem descend_correct (a : Fin w → Coefficients) (n : ℕ) (h : n ≤ w) :
    (run (descend a n h)).comp (embed n) = (embed 0).comp (ideal a n h) := by
  induction n with
  | zero => simp [descend, ideal]
  | succ n ih =>
      let j : Fin w := ⟨n, by omega⟩
      change (run ([.rotate j (a j), .prefixBit j] ++ descend a n (by omega))).comp
          (embed (j.val + 1)) =
        (embed 0).comp ((ideal a n (by omega)).comp (idealStep j (a j)))
      rw [run_append]
      simp only [run, LinearMap.id_comp, LinearMap.comp_assoc]
      rw [rotation_gate_embed]
      rw [← LinearMap.comp_assoc (idealStep j (a j)) (embed (j.val + 1))
        (Gate.eval (.prefixBit j)), prefix_gate_unembed]
      rw [← LinearMap.comp_assoc, ih, LinearMap.comp_assoc]


/-- The recursively computed Boolean is exactly the lower-zero predicate. -/
theorem prefix_true_iff (x : Word w) (n : ℕ) (hn : n ≤ w) :
    prefixBit x n = true ↔ ∀ j : Fin w, j.val < n → x j = false := by
  induction n with
  | zero => simp [prefixBit]
  | succ n ih =>
      let j : Fin w := ⟨n, by omega⟩
      have hb : bit x n = x j := bit_index x j
      have hnot : (!bit x n) = true ↔ bit x n = false := by
        cases bit x n <;> simp
      rw [prefixBit, Bool.and_eq_true, hnot, ih (by omega), hb]
      constructor
      · rintro ⟨hl, hj⟩ k hk
        by_cases hkn : k.val < n
        · exact hl k hkn
        · have he : k = j := Fin.ext (by dsimp [j]; omega)
          simpa [he] using hj
      · intro h
        exact ⟨fun k hk => h k (by omega), h j (by simp [j])⟩

def withHigh (b : Bool) (x : Word w) : Word (w + 1) := Fin.lastCases b x

theorem prefix_withHigh (x : Word w) (b : Bool) (n : ℕ) (hn : n ≤ w) :
    prefixBit (withHigh b x) n = prefixBit x n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hn' : n < w := by omega
      have hb : bit (withHigh b x) n = bit x n := by
        simp only [bit, dif_pos hn', dif_pos (by omega : n < w + 1)]
        exact Fin.lastCases_castSucc (⟨n, hn'⟩ : Fin w)
      simp only [prefixBit, ih (by omega), hb]

theorem withHigh_update (x : Word w) (b c : Bool) (j : Fin w) :
    withHigh b (Function.update x j c) = Function.update (withHigh b x) j.castSucc c := by
  funext k
  refine Fin.lastCases ?_ (fun i => ?_) k
  · have hne : Fin.last w ≠ j.castSucc := by
      intro h; have hh := congrArg Fin.val h; simp only [Fin.val_last, Fin.val_castSucc] at hh
      omega
    simp [withHigh, Function.update_of_ne hne]
  · by_cases hi : i = j
    · subst i; simp [withHigh]
    · have hne : i.castSucc ≠ j.castSucc := by
        intro h
        exact hi (Fin.ext (congrArg (fun k : Fin (w + 1) => k.val) h))
      simp [withHigh, Function.update_of_ne hi, Function.update_of_ne hne]

/-- Attach a fixed high spectator bit by complex linear extension. -/
def attachHigh (b : Bool) : SlotState w →ₗ[ℂ] SlotState (w + 1) :=
  Finsupp.linearCombination ℂ (fun x => Finsupp.single (withHigh b x) 1)

theorem idealStep_attachHigh (j : Fin w) (a : Coefficients) (b : Bool) :
    (idealStep j.castSucc a).comp (attachHigh b) =
      (attachHigh b).comp (idealStep j a) := by
  apply Finsupp.lhom_ext
  intro x c
  simp only [LinearMap.comp_apply, attachHigh, idealStep,
    Finsupp.linearCombination_single, map_smul]
  congr 1
  have hp : prefixBit (withHigh b x) j.castSucc.val = prefixBit x j.val :=
    prefix_withHigh x b j.val (Nat.le_of_lt j.isLt)
  simp only [idealBasis, hp]
  cases h : prefixBit x j.val
  · simp
  · simp only [if_true, map_sum, map_smul,
      Finsupp.linearCombination_single, one_smul]
    apply Finset.sum_congr rfl
    intro t ht
    rw [withHigh_update]
    simp [withHigh]

theorem ideal_attachHigh (a : Fin (w + 1) → Coefficients) (b : Bool)
    (n : ℕ) (hn : n ≤ w) :
    (ideal a n (by omega)).comp (attachHigh b) =
      (attachHigh b).comp (ideal (fun j : Fin w => a j.castSucc) n hn) := by
  induction n with
  | zero => simp [ideal]
  | succ n ih =>
      let j : Fin w := ⟨n, by omega⟩
      change ((ideal a n (by omega)).comp (idealStep j.castSucc (a j.castSucc))).comp
          (attachHigh b) =
        (attachHigh b).comp ((ideal (fun i : Fin w => a i.castSucc) n (by omega)).comp
          (idealStep j (a j.castSucc)))
      rw [LinearMap.comp_assoc, idealStep_attachHigh, ← LinearMap.comp_assoc,
        ih (by omega), LinearMap.comp_assoc]


/-- Restriction of the high spectator bit, as a linear amplitude slice. -/
def restrictHigh (b : Bool) : SlotState (w + 1) →ₗ[ℂ] SlotState w where
  toFun f := Finsupp.equivFunOnFinite.symm (fun x => f (withHigh b x))
  map_add' f g := by ext x; rfl
  map_smul' c f := by ext x; rfl

@[simp] theorem restrictHigh_apply (b : Bool) (f : SlotState (w + 1)) (x : Word w) :
    restrictHigh b f x = f (withHigh b x) := rfl

theorem restrictHigh_idealStep (j : Fin w) (a : Coefficients) (b : Bool) :
    (restrictHigh b).comp (idealStep j.castSucc a) =
      (idealStep j a).comp (restrictHigh b) := by
  apply LinearMap.ext
  intro f
  apply Finsupp.ext
  intro x
  simp only [LinearMap.comp_apply, restrictHigh_apply, idealStep_apply,
    Fin.val_castSucc, prefix_withHigh x b j.val (Nat.le_of_lt j.isLt)]
  cases h : prefixBit x j.val
  · simp
  · simp only [if_true]
    apply Finset.sum_congr rfl
    intro t ht
    rw [withHigh_update]
    simp [withHigh]

theorem restrictHigh_ideal (a : Fin (w + 1) → Coefficients) (b : Bool)
    (n : ℕ) (hn : n ≤ w) :
    (restrictHigh b).comp (ideal a n (by omega)) =
      (ideal (fun j : Fin w => a j.castSucc) n hn).comp (restrictHigh b) := by
  induction n with
  | zero => simp [ideal]
  | succ n ih =>
      let j : Fin w := ⟨n, by omega⟩
      change (restrictHigh b).comp ((ideal a n (by omega)).comp
          (idealStep j.castSucc (a j.castSucc))) =
        ((ideal (fun i : Fin w => a i.castSucc) n (by omega)).comp
          (idealStep j (a j.castSucc))).comp (restrictHigh b)
      rw [← LinearMap.comp_assoc, ih (by omega), LinearMap.comp_assoc,
        restrictHigh_idealStep, ← LinearMap.comp_assoc]

/-- Pointwise spectator formula, ready to identify the prefix circuit with
recursive dyadic frames defined by splitting off the highest slot bit. -/
theorem ideal_restrictHigh (a : Fin (w + 1) → Coefficients) (b : Bool)
    (n : ℕ) (hn : n ≤ w) (f : SlotState (w + 1)) (x : Word w) :
    (ideal a n (by omega) f) (withHigh b x) =
      (ideal (fun j : Fin w => a j.castSucc) n hn
        (Finsupp.equivFunOnFinite.symm (fun y => f (withHigh b y)))) x := by
  have h := LinearMap.congr_fun (restrictHigh_ideal a b n hn) f
  exact congrArg (fun v : SlotState w => v x) h

/-- The actual clean implementation consists of `w` computation gates,
`w` singly controlled rotations, and `w` uncomputation gates. -/
def circuit (a : Fin w → Coefficients) : List (Gate w) :=
  compute w le_rfl ++ descend a w le_rfl

/-- Exact equality on all input amplitudes; every flag is reset. -/
theorem circuit_correct (a : Fin w → Coefficients) :
    (run (circuit a)).comp (embed 0) = (embed 0).comp (ideal a w le_rfl) := by
  rw [circuit, run_append, LinearMap.comp_assoc, compute_correct, descend_correct]

@[simp] theorem compute_length (n : ℕ) (h : n ≤ w) : (compute n h).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [compute, ih]

@[simp] theorem descend_length (a : Fin w → Coefficients) (n : ℕ) (h : n ≤ w) :
    (descend a n h).length = 2 * n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [descend, ih]; omega

/-- Exact elementary-gate bound with one mixed-polarity Toffoli counted as
one gate. In a positive-control gate basis, replacing each negative control
by NOT--Toffoli--NOT increases this to at most `7*w` gates. -/
theorem circuit_length (a : Fin w → Coefficients) : (circuit a).length = 3 * w := by
  simp [circuit]; omega

/-- Cost in a positive-control Boolean basis. The zero-prefix gate is
actually only a NOT; the uniform bound of three is convenient. -/
def Gate.positiveCost : Gate w → ℕ
  | .prefixBit _ => 3
  | .rotate _ _ => 1

def positiveCost (gs : List (Gate w)) : ℕ :=
  (gs.map Gate.positiveCost).sum

@[simp] theorem positiveCost_append (gs hs : List (Gate w)) :
    positiveCost (gs ++ hs) = positiveCost gs + positiveCost hs := by
  simp [positiveCost]

@[simp] theorem compute_positiveCost (n : ℕ) (h : n ≤ w) :
    positiveCost (compute n h) = 3 * n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [compute, positiveCost_append, ih]
      simp [positiveCost, Gate.positiveCost]; omega

@[simp] theorem descend_positiveCost (a : Fin w → Coefficients)
    (n : ℕ) (h : n ≤ w) : positiveCost (descend a n h) = 4 * n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [descend, positiveCost_append, ih]
      simp [positiveCost, Gate.positiveCost]; omega

/-- Replacing each mixed-polarity Toffoli by NOT--Toffoli--NOT gives this
strict elementary-gate upper bound; the `w` controlled rotations cost one
each and are not unnecessarily expanded into three gates. -/
theorem positive_control_gate_bound (a : Fin w → Coefficients) :
    positiveCost (circuit a) = 7 * w := by
  simp [circuit]; omega

/-- The supplied two-by-two matrix must be unitary if it is to be realised
as a quantum rotation. The exact clean-circuit identity above is stronger:
it is valid even for arbitrary linear coefficient arrays. -/
def Coefficients.IsUnitary (a : Coefficients) : Prop :=
  Matrix.conjTranspose a * a = 1 ∧ a * Matrix.conjTranspose a = 1

def Gate.Valid : Gate w → Prop
  | .prefixBit _ => True
  | .rotate _ a => a.IsUnitary

/-- Every gate in the generated circuit is either one of the explicitly
reversible Boolean gates or a supplied one-control unitary matrix. -/
theorem circuit_valid (a : Fin w → Coefficients) (ha : ∀ j, (a j).IsUnitary) :
    ∀ g ∈ circuit a, g.Valid := by
  have hc : ∀ n (h : n ≤ w), ∀ g ∈ compute n h, g.Valid := by
    intro n h
    induction n with
    | zero => simp [compute]
    | succ n ih =>
        intro g hg
        simp only [compute, List.mem_append, List.mem_singleton] at hg
        rcases hg with hg | rfl
        · exact ih _ g hg
        · trivial
  have hd : ∀ n (h : n ≤ w), ∀ g ∈ descend a n h, g.Valid := by
    intro n h
    induction n with
    | zero => simp [descend]
    | succ n ih =>
        intro g hg
        simp only [descend, List.mem_append, List.mem_cons, List.not_mem_nil,
          or_false] at hg
        rcases hg with (rfl | rfl) | hg
        · exact ha _
        · trivial
        · exact ih _ g hg
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · exact hc w le_rfl g hg
  · exact hd w le_rfl g hg

/-- Number of supplied clean prefix qubits. The types contain exactly `w`
flags, and correctness returns every one to zero. -/
theorem work_qubits : Fintype.card (Fin w) = w := Fintype.card_fin w

end SparseHamiltonian.GatePrefixCircuit

end
