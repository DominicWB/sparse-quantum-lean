import GateEfficientHamiltonian.GatePointerEncoding
/-!
# A clean ripple comparison with a public constant

For a little-endian word `x`, the final borrow compares `x` with the
lowest `r` bits of `threshold`.  This is `x < threshold` when the threshold
is below `2^r`; the later closed-range wrapper separately handles `2^r`.
The circuit computes the borrow one bit at a time, copies only the final
borrow to a mark wire, and reverses the computation.  Its `r` computed
borrow flags and fixed zero input-borrow wire are clean at the output.  The constant bits are public compile-time data and do
not occupy quantum wires.
-/

namespace SparseHamiltonian.GateConstantCompare

noncomputable section

abbrev Word (r : ℕ) := GatePrivatePointer.Word r

structure Configuration (r : ℕ) where
  pointer : Word r
  borrow : Fin (r + 1) → Bool
  marked : Bool

@[ext] theorem Configuration.ext {r : ℕ} {z z' : Configuration r}
    (hp : z.pointer = z'.pointer) (hb : z.borrow = z'.borrow)
    (hm : z.marked = z'.marked) : z = z' := by
  cases z
  cases z'
  cases hp
  cases hb
  cases hm
  rfl

variable {r : ℕ}

def thresholdBit (threshold n : ℕ) : Bool := Nat.testBit threshold n

/-- One full-subtractor borrow update, specialised to the known bit of the
threshold. -/
def nextBorrow (threshold : ℕ) (xbit incoming : Bool) (n : ℕ) : Bool :=
  if thresholdBit threshold n then (!xbit) || incoming
  else (!xbit) && incoming

def borrowValue (threshold : ℕ) (x : Word r) : ℕ → Bool
  | 0 => false
  | n + 1 => nextBorrow threshold (GatePrivatePointer.bit x n)
      (borrowValue threshold x n) n

/-- After `n` ripple gates, precisely the first `n+1` borrow positions have
their semantic values; all higher workspace bits remain zero. -/
def encoded (threshold n : ℕ) (x : Word r) (marked : Bool) : Configuration r where
  pointer := x
  borrow := fun i => if i.val ≤ n then borrowValue threshold x i.val else false
  marked := marked

@[simp] theorem encoded_zero (threshold : ℕ) (x : Word r) (marked : Bool) :
    (encoded threshold 0 x marked).borrow = fun _ => false := by
  funext i
  change (if i.val ≤ 0 then borrowValue threshold x i.val else false) = false
  split_ifs with hi
  · have hv : i.val = 0 := Nat.eq_zero_of_le_zero hi
    rw [hv]
    rfl
  · rfl

def borrowControl (threshold : ℕ) (j : Fin r) (z : Configuration r) : Bool :=
  nextBorrow threshold (z.pointer j) (z.borrow (Fin.castSucc j)) j.val

def toggleBorrow (threshold : ℕ) (j : Fin r)
    (z : Configuration r) : Configuration r where
  pointer := z.pointer
  borrow := Function.update z.borrow (Fin.succ j)
    (if borrowControl threshold j z then !(z.borrow (Fin.succ j))
      else z.borrow (Fin.succ j))
  marked := z.marked

theorem castSucc_ne_succ (j : Fin r) : Fin.castSucc j ≠ Fin.succ j := by
  intro h
  have hv := congrArg Fin.val h
  simp at hv

theorem borrowControl_toggle (threshold : ℕ) (j : Fin r) (z : Configuration r) :
    borrowControl threshold j (toggleBorrow threshold j z) =
      borrowControl threshold j z := by
  simp [borrowControl, toggleBorrow, Function.update_of_ne (castSucc_ne_succ j)]

theorem toggleBorrow_at (threshold : ℕ) (j : Fin r) (z : Configuration r) :
    (toggleBorrow threshold j z).borrow (Fin.succ j) =
      (if borrowControl threshold j z then !(z.borrow (Fin.succ j))
        else z.borrow (Fin.succ j)) := by
  simp only [toggleBorrow, Function.update_self]

theorem toggleBorrow_involutive (threshold : ℕ) (j : Fin r) :
    Function.Involutive (toggleBorrow threshold j) := by
  intro z
  apply Configuration.ext
  · rfl
  · funext i
    by_cases hi : i = Fin.succ j
    · subst i
      rw [toggleBorrow_at, borrowControl_toggle, toggleBorrow_at]
      cases borrowControl threshold j z <;> simp
    · simp [toggleBorrow, Function.update_of_ne hi]
  · rfl

theorem borrowControl_encoded (threshold : ℕ) (j : Fin r)
    (x : Word r) (marked : Bool) :
    borrowControl threshold j (encoded threshold j.val x marked) =
      borrowValue threshold x (j.val + 1) := by
  change nextBorrow threshold (x j)
      (if j.val ≤ j.val then borrowValue threshold x j.val else false) j.val =
    borrowValue threshold x (j.val + 1)
  rw [if_pos le_rfl]
  simp only [borrowValue, GatePrivatePointer.bit_index]

theorem toggleBorrow_encoded (threshold : ℕ) (j : Fin r)
    (x : Word r) (marked : Bool) :
    toggleBorrow threshold j (encoded threshold j.val x marked) =
      encoded threshold (j.val + 1) x marked := by
  apply Configuration.ext
  · rfl
  · funext i
    by_cases hi : i = Fin.succ j
    · subst i
      rw [toggleBorrow_at, borrowControl_encoded]
      simp only [encoded]
      have hnot : ¬ (Fin.succ j).val ≤ j.val := by simp
      have hyes : (Fin.succ j).val ≤ j.val + 1 := by simp
      rw [if_neg hnot, if_pos hyes]
      change (if borrowValue threshold x (j.val + 1) then !false else false) =
        borrowValue threshold x (j.val + 1)
      cases borrowValue threshold x (j.val + 1) <;> rfl
    · have hv : i.val ≠ j.val + 1 := by
        intro h
        apply hi
        exact Fin.ext (by simpa using h)
      have hle : (i.val ≤ j.val + 1) = (i.val ≤ j.val) := propext (by omega)
      simp [toggleBorrow, Function.update_of_ne hi, encoded, hle]
  · rfl

/-- Copy the final borrow to the one persistent mark wire. -/
def toggleMark (z : Configuration r) : Configuration r where
  pointer := z.pointer
  borrow := z.borrow
  marked := if z.borrow (Fin.last r) then !z.marked else z.marked

theorem toggleMark_involutive : Function.Involutive (@toggleMark r) := by
  intro z
  apply Configuration.ext
  · rfl
  · rfl
  · simp only [toggleMark]
    cases z.borrow (Fin.last r) <;> simp

inductive Gate (r : ℕ)
  | borrow (j : Fin r)
  | mark

def Gate.eval (threshold : ℕ) : Gate r → Configuration r → Configuration r
  | .borrow j => toggleBorrow threshold j
  | .mark => toggleMark

theorem Gate.eval_involutive (threshold : ℕ) (g : Gate r) :
    Function.Involutive (Gate.eval threshold g) := by
  cases g with
  | borrow j => exact toggleBorrow_involutive threshold j
  | mark => exact toggleMark_involutive

def Gate.arity : Gate r → ℕ
  | .borrow _ => 3
  | .mark => 2

theorem Gate.arity_le_three (g : Gate r) : g.arity ≤ 3 := by
  cases g <;> simp [Gate.arity]

def exec (threshold : ℕ) : List (Gate r) → Configuration r → Configuration r
  | [], z => z
  | g :: gs, z => exec threshold gs (Gate.eval threshold g z)

theorem exec_append (threshold : ℕ) (gs hs : List (Gate r))
    (z : Configuration r) :
    exec threshold (gs ++ hs) z = exec threshold hs (exec threshold gs z) := by
  induction gs generalizing z with
  | nil => rfl
  | cons g gs ih => simp only [List.cons_append, exec, ih]

theorem exec_reverse_exec (threshold : ℕ) (gs : List (Gate r))
    (z : Configuration r) :
    exec threshold gs.reverse (exec threshold gs z) = z := by
  induction gs generalizing z with
  | nil => rfl
  | cons g gs ih =>
      rw [List.reverse_cons, exec_append]
      simp only [exec]
      rw [ih]
      exact Gate.eval_involutive threshold g z

def compute (threshold : ℕ) : (n : ℕ) → n ≤ r → List (Gate r)
  | 0, _ => []
  | n + 1, h => compute threshold n (by omega) ++ [.borrow ⟨n, by omega⟩]

theorem compute_correct (threshold n : ℕ) (h : n ≤ r)
    (x : Word r) (marked : Bool) :
    exec threshold (compute threshold n h) (encoded threshold 0 x marked) =
      encoded threshold n x marked := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [compute, exec_append, ih]
      simp only [exec]
      exact toggleBorrow_encoded threshold (⟨n, by omega⟩ : Fin r) x marked

theorem uncompute_correct (threshold n : ℕ) (h : n ≤ r)
    (x : Word r) (marked : Bool) :
    exec threshold (compute threshold n h).reverse (encoded threshold n x marked) =
      encoded threshold 0 x marked := by
  rw [← compute_correct threshold n h x marked]
  exact exec_reverse_exec threshold (compute threshold n h)
    (encoded threshold 0 x marked)

def compareCircuit (threshold r : ℕ) : List (Gate r) :=
  compute threshold r le_rfl ++ [.mark] ++ (compute threshold r le_rfl).reverse

def lessThan (threshold : ℕ) (x : Word r) : Bool :=
  borrowValue threshold x r

theorem mark_encoded (threshold : ℕ) (x : Word r) :
    toggleMark (encoded threshold r x false) =
      encoded threshold r x (lessThan threshold x) := by
  apply Configuration.ext
  · rfl
  · rfl
  · simp [toggleMark, encoded, lessThan]

/-- The complete comparator has a clean borrow register and exposes only the
comparison result. -/
theorem compareCircuit_correct (threshold : ℕ) (x : Word r) :
    exec threshold (compareCircuit threshold r) (encoded threshold 0 x false) =
      encoded threshold 0 x (lessThan threshold x) := by
  rw [compareCircuit, exec_append, exec_append, compute_correct]
  simp only [exec, Gate.eval]
  rw [mark_encoded, uncompute_correct]

theorem compute_length (threshold n : ℕ) (h : n ≤ r) :
    (compute threshold n h).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [compute, ih]

theorem compareCircuit_length (threshold r : ℕ) :
    (compareCircuit threshold r).length = 2 * r + 1 := by
  simp [compareCircuit, compute_length]
  omega

/-! ### Coherent phase kickback -/

/-- The marked bit may start in either computational basis state.  The clean
borrow circuit toggles it precisely on the accepted pointer words. -/
theorem mark_encoded_general (threshold : ℕ) (x : Word r) (marked : Bool) :
    toggleMark (encoded threshold r x marked) =
      encoded threshold r x
        (if lessThan threshold x then !marked else marked) := by
  apply Configuration.ext
  · rfl
  · rfl
  · simp [toggleMark, encoded, lessThan]

/-- Full clean comparator action for an arbitrary target-bit basis state. -/
theorem compareCircuit_correct_marked (threshold : ℕ) (x : Word r)
    (marked : Bool) :
    exec threshold (compareCircuit threshold r)
        (encoded threshold 0 x marked) =
      encoded threshold 0 x
        (if lessThan threshold x then !marked else marked) := by
  rw [compareCircuit, exec_append, exec_append, compute_correct]
  simp only [exec, Gate.eval]
  rw [mark_encoded_general, uncompute_correct]

/-- Coherent linear extension of the actual comparator gate list. -/
abbrev Amplitude (r : ℕ) := Configuration r →₀ ℂ

def circuitLinear (threshold : ℕ) (gs : List (Gate r)) :
    Amplitude r →ₗ[ℂ] Amplitude r :=
  Finsupp.linearCombination ℂ
    (fun z => Finsupp.single (exec threshold gs z) 1)

theorem circuitLinear_single (threshold : ℕ) (gs : List (Gate r))
    (z : Configuration r) (a : ℂ) :
    circuitLinear threshold gs (Finsupp.single z a) =
      Finsupp.single (exec threshold gs z) a := by
  simp [circuitLinear]

/-- The unnormalised minus state of the marked wire, with all borrow flags
clean and an arbitrary pointer basis state. -/
def kickback (threshold : ℕ) (x : Word r) (a : ℂ) : Amplitude r :=
  Finsupp.single (encoded threshold 0 x false) a -
    Finsupp.single (encoded threshold 0 x true) a

def phaseSign (b : Bool) : ℂ := if b then -1 else 1

/-- The concrete compute/mark/uncompute circuit leaves the marked wire in
its minus state and applies exactly the comparison phase.  In particular,
all `r+1` borrow wires are returned to zero; no abstract comparison unitary
is used. -/
theorem compareCircuit_kickback (threshold : ℕ) (x : Word r) (a : ℂ) :
    circuitLinear threshold (compareCircuit threshold r)
        (kickback threshold x a) =
      phaseSign (lessThan threshold x) • kickback threshold x a := by
  unfold kickback
  rw [map_sub, circuitLinear_single, circuitLinear_single,
    compareCircuit_correct_marked, compareCircuit_correct_marked]
  cases h : lessThan threshold x <;>
    simp [phaseSign]

/-- Phase kickback therefore costs the comparator list itself: `2*r+1`
bounded-arity gates.  Preparation and final disposal of the reusable minus
ancilla are independent of the threshold. -/
theorem comparisonPhase_gateCount (threshold r : ℕ) :
    (compareCircuit threshold r).length = 2 * r + 1 :=
  compareCircuit_length threshold r

/-- Reversing the concrete list gives the inverse on the entire amplitude
space, including dirty borrow and marked wires. -/
theorem circuitLinear_reverse_comp (threshold : ℕ) (gs : List (Gate r)) :
    (circuitLinear threshold gs.reverse).comp
        (circuitLinear threshold gs) = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro z a
  simp [circuitLinear_single, exec_reverse_exec]

end
end SparseHamiltonian.GateConstantCompare
