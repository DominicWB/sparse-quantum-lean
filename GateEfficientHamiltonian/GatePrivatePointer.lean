import GateEfficientHamiltonian.GatePhysicalBoundary
/-!
# A clean bounded-arity binary pointer circuit

The abstract reuse calculation above increments only the private-sector
pointer.  Here that routing operation is compiled into NOT, CNOT and Toffoli
type gates.  The circuit first computes the lower-one predicates into clean
carry flags.  It then visits the pointer bits from high to low, flips the bit
selected by its carry, and erases that carry before a lower bit is changed.
Consequently the flags finish clean and the public sector is the identity.

Every gate reads or writes at most three Boolean wires.  The forward circuit
has exactly `3*r` gates on an `r`-bit pointer.  Its literal list reversal is
proved to be its inverse on the entire configuration space, rather than only
on the reachable one-pointer subspace.  This is the finite reversible layer;
the next bridge transports its basis permutation to the amplitude register
used by `GateBinaryReuse`.
-/

namespace SparseHamiltonian.GatePrivatePointer

noncomputable section

abbrev Word (r : ℕ) := Fin r → Bool

/-- The sector bit is `true` on the private component.  Carry flags are
ancillas and are required to enter and leave in the all-zero word. -/
structure Configuration (r : ℕ) where
  privateSector : Bool
  pointer : Word r
  carry : Word r

@[ext] theorem Configuration.ext {r : ℕ} {z z' : Configuration r}
    (hs : z.privateSector = z'.privateSector)
    (hp : z.pointer = z'.pointer) (hc : z.carry = z'.carry) : z = z' := by
  cases z
  cases z'
  cases hs
  cases hp
  cases hc
  rfl

variable {r : ℕ}

def bit (x : Word r) (n : ℕ) : Bool :=
  if h : n < r then x ⟨n, h⟩ else false

@[simp] theorem bit_index (x : Word r) (j : Fin r) : bit x j.val = x j := by
  simp [bit, j.isLt]

/-- All pointer bits strictly below `n` are one. -/
def onePrefix (x : Word r) : ℕ → Bool
  | 0 => true
  | n + 1 => onePrefix x n && bit x n

@[simp] theorem onePrefix_zero (x : Word r) : onePrefix x 0 = true := rfl

/-- A change at bit `j` cannot affect a predicate involving only lower bits. -/
theorem onePrefix_update (x : Word r) (j : Fin r) (b : Bool)
    (n : ℕ) (hn : n ≤ j.val) :
    onePrefix (Function.update x j b) n = onePrefix x n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hn' : n ≤ j.val := by omega
      have hnlt : n < r := lt_of_lt_of_le (by omega : n < j.val)
        (Nat.le_of_lt j.isLt)
      have hne : (⟨n, hnlt⟩ : Fin r) ≠ j := by
        intro h
        have hv := congrArg Fin.val h
        change n = j.val at hv
        omega
      simp only [onePrefix, ih hn', bit, dif_pos hnlt]
      rw [Function.update_of_ne hne]

/-- Clean carries after the first `n` carry-computation gates. -/
def encoded (n : ℕ) (s : Bool) (x : Word r) : Configuration r where
  privateSector := s
  pointer := x
  carry := fun j => if j.val < n then s && onePrefix x j.val else false

@[simp] theorem encoded_zero (s : Bool) (x : Word r) :
    (encoded 0 s x).carry = fun _ => false := by
  funext j
  simp [encoded]

def previous (j : Fin r) (_hj : j.val ≠ 0) : Fin r :=
  ⟨j.val - 1, by omega⟩

theorem previous_ne (j : Fin r) (hj : j.val ≠ 0) : previous j hj ≠ j := by
  intro h
  have hv := congrArg Fin.val h
  simp only [previous] at hv
  omega

/-- The first carry is controlled by the private-sector bit.  Every later
carry is a Toffoli controlled by the preceding carry and pointer bit. -/
def carryControl (j : Fin r) (z : Configuration r) : Bool :=
  if hj : j.val = 0 then z.privateSector
  else z.carry (previous j hj) && z.pointer (previous j hj)

def toggleCarry (j : Fin r) (z : Configuration r) : Configuration r where
  privateSector := z.privateSector
  pointer := z.pointer
  carry := Function.update z.carry j
    (if carryControl j z then !(z.carry j) else z.carry j)

theorem carryControl_toggle (j : Fin r) (z : Configuration r) :
    carryControl j (toggleCarry j z) = carryControl j z := by
  by_cases hj : j.val = 0
  · simp [carryControl, hj, toggleCarry]
  · simp [carryControl, hj, toggleCarry,
      Function.update_of_ne (previous_ne j hj)]

theorem toggleCarry_involutive (j : Fin r) : Function.Involutive (toggleCarry j) := by
  intro z
  apply Configuration.ext
  · rfl
  · rfl
  · funext i
    by_cases hi : i = j
    · subst i
      change (Function.update (toggleCarry j z).carry j
        (if carryControl j (toggleCarry j z) then
          !((toggleCarry j z).carry j) else (toggleCarry j z).carry j)) j = z.carry j
      rw [Function.update_self, carryControl_toggle]
      simp only [toggleCarry, Function.update_self]
      cases h : carryControl j z <;> simp
    · simp [toggleCarry, Function.update_of_ne hi]

theorem carryControl_encoded (j : Fin r) (s : Bool) (x : Word r) :
    carryControl j (encoded j.val s x) = (s && onePrefix x j.val) := by
  by_cases hj : j.val = 0
  · simp [carryControl, hj, encoded]
  · have hp : (previous j hj).val < j.val := by
      change j.val - 1 < j.val
      omega
    have hs : j.val = (j.val - 1) + 1 := by omega
    have hb : bit x (j.val - 1) = x (previous j hj) := by
      exact bit_index x (previous j hj)
    have hprefix : onePrefix x j.val =
        (onePrefix x (j.val - 1) && x (previous j hj)) := by
      calc
        onePrefix x j.val = onePrefix x ((j.val - 1) + 1) :=
          congrArg (onePrefix x) hs
        _ = (onePrefix x (j.val - 1) && x (previous j hj)) := by
          simp only [onePrefix]
          rw [hb]
    simp only [carryControl, dif_neg hj, encoded, if_pos hp]
    change ((s && onePrefix x (j.val - 1)) && x (previous j hj)) =
      (s && onePrefix x j.val)
    rw [hprefix]
    cases s <;> cases onePrefix x (j.val - 1) <;>
      cases x (previous j hj) <;> rfl

theorem toggleCarry_encoded (j : Fin r) (s : Bool) (x : Word r) :
    toggleCarry j (encoded j.val s x) = encoded (j.val + 1) s x := by
  apply Configuration.ext
  · rfl
  · rfl
  · funext i
    by_cases hi : i = j
    · subst i
      change (Function.update (encoded j.val s x).carry j
        (if carryControl j (encoded j.val s x) then
          !((encoded j.val s x).carry j) else (encoded j.val s x).carry j)) j =
            (encoded (j.val + 1) s x).carry j
      rw [Function.update_self, carryControl_encoded]
      simp only [encoded, Nat.lt_irrefl, if_false, Nat.lt_succ_self, if_true]
      cases s && onePrefix x j.val <;> rfl
    · have hv : i.val ≠ j.val := fun h => hi (Fin.ext h)
      have hr : (i.val < j.val + 1) = (i.val < j.val) := propext (by omega)
      simp only [toggleCarry, Function.update_of_ne hi, encoded, hr]

theorem toggleCarry_encoded_succ (j : Fin r) (s : Bool) (x : Word r) :
    toggleCarry j (encoded (j.val + 1) s x) = encoded j.val s x := by
  rw [← toggleCarry_encoded j s x]
  exact toggleCarry_involutive j (encoded j.val s x)

/-- Flip one pointer bit under its already computed carry. -/
def flipPointer (j : Fin r) (z : Configuration r) : Configuration r where
  privateSector := z.privateSector
  pointer := Function.update z.pointer j
    (if z.carry j then !(z.pointer j) else z.pointer j)
  carry := z.carry

theorem flipPointer_involutive (j : Fin r) : Function.Involutive (flipPointer j) := by
  intro z
  apply Configuration.ext
  · rfl
  · funext i
    by_cases hi : i = j
    · subst i
      simp only [flipPointer, Function.update_self]
      cases z.carry j <;> simp
    · simp [flipPointer, Function.update_of_ne hi]
  · rfl

/-- Semantic bit update used to state correctness of the gate list. -/
def advance (s : Bool) (j : Fin r) (x : Word r) : Word r :=
  if s && onePrefix x j.val then Function.update x j (!(x j)) else x

theorem advance_apply_ne (s : Bool) (j : Fin r) (x : Word r)
    (i : Fin r) (hi : i ≠ j) : advance s j x i = x i := by
  unfold advance
  split_ifs <;> simp only [Function.update_of_ne hi]

theorem advance_apply_self (s : Bool) (j : Fin r) (x : Word r) :
    advance s j x j = (if s && onePrefix x j.val then !(x j) else x j) := by
  unfold advance
  split_ifs <;> simp only [Function.update_self]

theorem onePrefix_advance (s : Bool) (j : Fin r) (x : Word r)
    (n : ℕ) (hn : n ≤ j.val) :
    onePrefix (advance s j x) n = onePrefix x n := by
  unfold advance
  split_ifs
  · exact onePrefix_update x j (!(x j)) n hn
  · rfl

theorem flipPointer_encoded (j : Fin r) (s : Bool) (x : Word r) :
    flipPointer j (encoded (j.val + 1) s x) =
      encoded (j.val + 1) s (advance s j x) := by
  apply Configuration.ext
  · rfl
  · funext i
    by_cases hi : i = j
    · subst i
      simp only [flipPointer, encoded, Nat.lt_succ_self, if_true,
        Function.update_self, advance]
      cases h : s && onePrefix x j.val <;> simp
    · simp only [flipPointer, Function.update_of_ne hi, encoded, advance]
      split_ifs <;> simp [Function.update_of_ne hi]
  · funext i
    by_cases hi : i.val < j.val + 1
    · have hil : i.val ≤ j.val := by omega
      simp only [flipPointer, encoded, if_pos hi]
      rw [onePrefix_advance s j x i.val hil]
    · simp only [flipPointer, encoded, if_neg hi]

/-- Every constructor is a bounded-arity reversible Boolean gate. -/
inductive Gate (r : ℕ)
  | carry (j : Fin r)
  | flip (j : Fin r)

def Gate.eval : Gate r → Configuration r → Configuration r
  | .carry j => toggleCarry j
  | .flip j => flipPointer j

theorem Gate.eval_involutive (g : Gate r) : Function.Involutive g.eval := by
  cases g with
  | carry j => exact toggleCarry_involutive j
  | flip j => exact flipPointer_involutive j

/-- Number of Boolean wires touched by the corresponding elementary gate. -/
def Gate.arity : Gate r → ℕ
  | .carry j => if j.val = 0 then 2 else 3
  | .flip _ => 2

theorem Gate.arity_le_three (g : Gate r) : g.arity ≤ 3 := by
  cases g with
  | carry j =>
      simp only [Gate.arity]
      split_ifs <;> omega
  | flip j => simp [Gate.arity]

/-- Execute a gate list from left to right. -/
def exec : List (Gate r) → Configuration r → Configuration r
  | [], z => z
  | g :: gs, z => exec gs (g.eval z)

@[simp] theorem exec_nil (z : Configuration r) : exec [] z = z := rfl

theorem exec_append (gs hs : List (Gate r)) (z : Configuration r) :
    exec (gs ++ hs) z = exec hs (exec gs z) := by
  induction gs generalizing z with
  | nil => rfl
  | cons g gs ih => simp only [List.cons_append, exec, ih]

/-- Computing the carries uses exactly one bounded-arity gate per bit. -/
def compute : (n : ℕ) → n ≤ r → List (Gate r)
  | 0, _ => []
  | n + 1, h => compute n (by omega) ++ [.carry ⟨n, by omega⟩]

theorem compute_correct (n : ℕ) (h : n ≤ r) (s : Bool) (x : Word r) :
    exec (compute n h) (encoded 0 s x) = encoded n s x := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [compute, exec_append, ih]
      simp only [exec]
      exact toggleCarry_encoded (⟨n, by omega⟩ : Fin r) s x

/-- High-to-low updates, erasing each carry immediately after its use. -/
def descend : (n : ℕ) → n ≤ r → List (Gate r)
  | 0, _ => []
  | n + 1, h => [.flip ⟨n, by omega⟩, .carry ⟨n, by omega⟩] ++
      descend n (by omega)

/-- The word transformation computed by `descend`. -/
def incrementWord (s : Bool) : (n : ℕ) → n ≤ r → Word r → Word r
  | 0, _, x => x
  | n + 1, h, x => incrementWord s n (by omega)
      (advance s ⟨n, by omega⟩ x)

theorem descend_correct (n : ℕ) (h : n ≤ r) (s : Bool) (x : Word r) :
    exec (descend n h) (encoded n s x) =
      encoded 0 s (incrementWord s n h x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      let j : Fin r := ⟨n, by omega⟩
      change exec ([.flip j, .carry j] ++ descend n (by omega))
          (encoded (j.val + 1) s x) = _
      rw [exec_append]
      simp only [exec, Gate.eval]
      rw [flipPointer_encoded, toggleCarry_encoded_succ]
      exact ih (by omega) (advance s j x)

def incrementCircuit (r : ℕ) : List (Gate r) :=
  compute r le_rfl ++ descend r le_rfl

/-- Literal reversal supplies decrement; it is not an uncharged arithmetic
permutation. -/
def decrementCircuit (r : ℕ) : List (Gate r) :=
  (incrementCircuit r).reverse

theorem exec_reverse_exec (gs : List (Gate r)) (z : Configuration r) :
    exec gs.reverse (exec gs z) = z := by
  induction gs generalizing z with
  | nil => rfl
  | cons g gs ih =>
      rw [List.reverse_cons, exec_append]
      simp only [exec]
      rw [ih]
      exact Gate.eval_involutive g z

theorem exec_exec_reverse (gs : List (Gate r)) (z : Configuration r) :
    exec gs (exec gs.reverse z) = z := by
  have h := exec_reverse_exec gs.reverse z
  simpa using h

theorem incrementCircuit_correct (s : Bool) (x : Word r) :
    exec (incrementCircuit r) (encoded 0 s x) =
      encoded 0 s (incrementWord s r le_rfl x) := by
  rw [incrementCircuit, exec_append, compute_correct, descend_correct]

theorem decrement_increment (z : Configuration r) :
    exec (decrementCircuit r) (exec (incrementCircuit r) z) = z := by
  exact exec_reverse_exec (incrementCircuit r) z

theorem increment_decrement (z : Configuration r) :
    exec (incrementCircuit r) (exec (decrementCircuit r) z) = z := by
  exact exec_exec_reverse (incrementCircuit r) z

theorem compute_length (n : ℕ) (h : n ≤ r) : (compute n h).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [compute, ih]

theorem descend_length (n : ℕ) (h : n ≤ r) : (descend n h).length = 2 * n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [descend, ih]; omega

theorem incrementCircuit_length (r : ℕ) : (incrementCircuit r).length = 3 * r := by
  simp [incrementCircuit, compute_length, descend_length]
  omega

theorem decrementCircuit_length (r : ℕ) : (decrementCircuit r).length = 3 * r := by
  simp [decrementCircuit, incrementCircuit_length]

theorem incrementWord_false (n : ℕ) (h : n ≤ r) (x : Word r) :
    incrementWord false n h x = x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      simp only [incrementWord, advance, Bool.false_and,
        Bool.false_eq_true, if_false]
      exact ih (by omega) x

/-- The public sector is pointwise fixed, including on dirty pointer words;
only the carry ancillas are required to be initially clean. -/
theorem public_identity (x : Word r) :
    exec (incrementCircuit r) (encoded 0 false x) = encoded 0 false x := by
  rw [incrementCircuit_correct]
  rw [incrementWord_false]

/-- The private sector performs the full ripple update and leaves all carries
clean. -/
theorem private_increment (x : Word r) :
    exec (incrementCircuit r) (encoded 0 true x) =
      encoded 0 true (incrementWord true r le_rfl x) :=
  incrementCircuit_correct true x

/-- Linear extension of the actual basis permutation.  This is the bridge
from reversible Boolean semantics to coherent amplitudes; it is not an
abstract whole-register gate constructor. -/
abbrev Amplitude (r : ℕ) := Configuration r →₀ ℂ

def circuitLinear (gs : List (Gate r)) : Amplitude r →ₗ[ℂ] Amplitude r :=
  Finsupp.linearCombination ℂ
    (fun z => Finsupp.single (exec gs z) 1)

theorem circuitLinear_single (gs : List (Gate r)) (z : Configuration r) (a : ℂ) :
    circuitLinear gs (Finsupp.single z a) =
      Finsupp.single (exec gs z) a := by
  simp [circuitLinear]

/-- The inverse is obtained by reversing the very same elementary gate
list.  The equality is on the full amplitude space. -/
theorem circuitLinear_reverse_comp (gs : List (Gate r)) :
    (circuitLinear gs.reverse).comp (circuitLinear gs) = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro z a
  simp [circuitLinear_single, exec_reverse_exec]

theorem circuitLinear_comp_reverse (gs : List (Gate r)) :
    (circuitLinear gs).comp (circuitLinear gs.reverse) = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro z a
  simp [circuitLinear_single, exec_exec_reverse]

end

end SparseHamiltonian.GatePrivatePointer
