import GateEfficientHamiltonian.GateWalshHilbertAdjoint
/-!
# A known control for the concrete comparison phase

The comparison workspace is augmented by one unchanged enable qubit.  Its
borrow computation and its literal reversal run unconditionally; only the
middle target flip gains the enable control.  Thus the extra condition uses
one three-wire controlled flip, rather than controlling an opaque comparison
unitary.  The clean action proved below is valid on both enable basis states
and hence on their coherent superpositions.

The raw circuit first implements `GateConstantCompare.lessThan`.  The
bounded-threshold bridge then gives its numerical interpretation, and an
explicit full-range branch covers `threshold = 2^r`.  Finally, two literal NOT
gates turn the positive enable control into a negative attenuation-flag
control, restoring that physical flag at an additive cost of two gates.
-/

namespace SparseHamiltonian.GateControlledCompare

open scoped BigOperators

abbrev Word (r : ℕ) := GateConstantCompare.Word r

/-- The first factor is an unchanged, known ancilla control. -/
abbrev Configuration (r : ℕ) := Bool × GateConstantCompare.Configuration r

variable {r : ℕ}

def encoded (threshold n : ℕ) (enable : Bool) (x : Word r)
    (marked : Bool) : Configuration r :=
  (enable, GateConstantCompare.encoded threshold n x marked)

/-- A borrow update has two input wires and one target.  The mark gate uses
the enable and final-borrow wires as its two controls. -/
inductive Gate (r : ℕ)
  | borrow (j : Fin r)
  | mark

def Gate.eval (threshold : ℕ) : Gate r → Configuration r → Configuration r
  | .borrow j, z => (z.1, GateConstantCompare.toggleBorrow threshold j z.2)
  | .mark, z =>
      (z.1, if z.1 then GateConstantCompare.toggleMark z.2 else z.2)

theorem Gate.eval_involutive (threshold : ℕ) (g : Gate r) :
    Function.Involutive (Gate.eval threshold g) := by
  intro z
  rcases z with ⟨enable, z⟩
  cases g with
  | borrow j =>
      change (enable, GateConstantCompare.toggleBorrow threshold j
        (GateConstantCompare.toggleBorrow threshold j z)) = (enable, z)
      rw [GateConstantCompare.toggleBorrow_involutive threshold j z]
  | mark =>
      cases enable
      · rfl
      · change (true, GateConstantCompare.toggleMark
          (GateConstantCompare.toggleMark z)) = (true, z)
        rw [GateConstantCompare.toggleMark_involutive z]

def Gate.arity : Gate r → ℕ
  | .borrow _ => 3
  | .mark => 3

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

theorem exec_exec_reverse (threshold : ℕ) (gs : List (Gate r))
    (z : Configuration r) :
    exec threshold gs (exec threshold gs.reverse z) = z := by
  simpa only [List.reverse_reverse] using
    exec_reverse_exec threshold gs.reverse z

/-- Exactly the original unconditional ripple, now on the larger register. -/
def compute (threshold : ℕ) : (n : ℕ) → n ≤ r → List (Gate r)
  | 0, _ => []
  | n + 1, h => compute threshold n (by omega) ++ [.borrow ⟨n, by omega⟩]

theorem borrow_encoded (threshold : ℕ) (j : Fin r) (enable : Bool)
    (x : Word r) (marked : Bool) :
    Gate.eval threshold (.borrow j) (encoded threshold j.val enable x marked) =
      encoded threshold (j.val + 1) enable x marked := by
  change (enable, GateConstantCompare.toggleBorrow threshold j
    (GateConstantCompare.encoded threshold j.val x marked)) =
      (enable, GateConstantCompare.encoded threshold (j.val + 1) x marked)
  rw [GateConstantCompare.toggleBorrow_encoded]

theorem compute_correct (threshold n : ℕ) (h : n ≤ r) (enable : Bool)
    (x : Word r) (marked : Bool) :
    exec threshold (compute threshold n h) (encoded threshold 0 enable x marked) =
      encoded threshold n enable x marked := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [compute, exec_append, ih]
      simp only [exec]
      exact borrow_encoded threshold (⟨n, by omega⟩ : Fin r) enable x marked

theorem uncompute_correct (threshold n : ℕ) (h : n ≤ r) (enable : Bool)
    (x : Word r) (marked : Bool) :
    exec threshold (compute threshold n h).reverse
        (encoded threshold n enable x marked) =
      encoded threshold 0 enable x marked := by
  rw [← compute_correct threshold n h enable x marked]
  exact exec_reverse_exec threshold (compute threshold n h)
    (encoded threshold 0 enable x marked)

theorem mark_encoded (threshold : ℕ) (enable : Bool) (x : Word r)
    (marked : Bool) :
    Gate.eval threshold .mark (encoded threshold r enable x marked) =
      encoded threshold r enable x
        (if enable && GateConstantCompare.lessThan threshold x
          then !marked else marked) := by
  cases enable
  · rfl
  · change (true, GateConstantCompare.toggleMark
        (GateConstantCompare.encoded threshold r x marked)) =
      (true, GateConstantCompare.encoded threshold r x
        (if GateConstantCompare.lessThan threshold x then !marked else marked))
    rw [GateConstantCompare.mark_encoded_general]

def compareCircuit (threshold r : ℕ) : List (Gate r) :=
  compute threshold r le_rfl ++ [.mark] ++ (compute threshold r le_rfl).reverse

/-- The enable and pointer wires are unchanged; every borrow flag is reset.
Only the marked target carries the conjunction of the two conditions. -/
theorem compareCircuit_correct_marked (threshold : ℕ) (enable : Bool)
    (x : Word r) (marked : Bool) :
    exec threshold (compareCircuit threshold r)
        (encoded threshold 0 enable x marked) =
      encoded threshold 0 enable x
        (if enable && GateConstantCompare.lessThan threshold x
          then !marked else marked) := by
  rw [compareCircuit, exec_append, exec_append, compute_correct]
  simp only [exec]
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

noncomputable section

abbrev Amplitude (r : ℕ) := Configuration r →₀ ℂ

/-- Linear extension of the literal reversible gate list. -/
def circuitLinear (threshold : ℕ) (gs : List (Gate r)) :
    Amplitude r →ₗ[ℂ] Amplitude r :=
  Finsupp.linearCombination ℂ
    (fun z => Finsupp.single (exec threshold gs z) 1)

theorem circuitLinear_single (threshold : ℕ) (gs : List (Gate r))
    (z : Configuration r) (a : ℂ) :
    circuitLinear threshold gs (Finsupp.single z a) =
      Finsupp.single (exec threshold gs z) a := by
  simp [circuitLinear]

def kickback (threshold : ℕ) (enable : Bool) (x : Word r)
    (a : ℂ) : Amplitude r :=
  Finsupp.single (encoded threshold 0 enable x false) a -
    Finsupp.single (encoded threshold 0 enable x true) a

/-- Exact conditional phase action, with the minus target and all borrow
ancillas returned to their initial states.  The coefficient `a` is arbitrary,
so the identity includes any normalisation of the minus target. -/
theorem compareCircuit_kickback (threshold : ℕ) (enable : Bool)
    (x : Word r) (a : ℂ) :
    circuitLinear threshold (compareCircuit threshold r)
        (kickback threshold enable x a) =
      GateConstantCompare.phaseSign
        (enable && GateConstantCompare.lessThan threshold x) •
          kickback threshold enable x a := by
  unfold kickback
  rw [map_sub, circuitLinear_single, circuitLinear_single,
    compareCircuit_correct_marked, compareCircuit_correct_marked]
  cases h : enable && GateConstantCompare.lessThan threshold x <;>
    simp [GateConstantCompare.phaseSign]

/-- Coherent superpositions of both pointer words and enable values follow
by linearity of the actual gate-list implementation. -/
theorem compareCircuit_kickback_sum {ι : Type*} (s : Finset ι)
    (threshold : ℕ) (enable : ι → Bool) (x : ι → Word r) (a : ι → ℂ) :
    circuitLinear threshold (compareCircuit threshold r)
        (∑ i ∈ s, kickback threshold (enable i) (x i) (a i)) =
      ∑ i ∈ s, GateConstantCompare.phaseSign
        (enable i && GateConstantCompare.lessThan threshold (x i)) •
          kickback threshold (enable i) (x i) (a i) := by
  simp only [map_sum, compareCircuit_kickback]

/-- Reversing the list is an inverse on the entire register, including
arbitrary dirty borrow flags and arbitrary enable-target correlations. -/
theorem circuitLinear_reverse_comp (threshold : ℕ) (gs : List (Gate r)) :
    (circuitLinear threshold gs.reverse).comp
        (circuitLinear threshold gs) = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro z a
  simp [circuitLinear_single, exec_reverse_exec]

theorem circuitLinear_comp_reverse (threshold : ℕ) (gs : List (Gate r)) :
    (circuitLinear threshold gs).comp
        (circuitLinear threshold gs.reverse) = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro z a
  simp [circuitLinear_single, exec_exec_reverse]

/-- At the full-range endpoint the numerical predicate is always true, so
the phase needs only a controlled NOT with the known enable wire. -/
def enabledFlip (z : Configuration r) : Configuration r :=
  (z.1, if z.1 then GateConstantCompare.flipMarked z.2 else z.2)

theorem enabledFlip_involutive : Function.Involutive (@enabledFlip r) := by
  intro z
  rcases z with ⟨enable, z⟩
  cases enable
  · rfl
  · change (true, GateConstantCompare.flipMarked
      (GateConstantCompare.flipMarked z)) = (true, z)
    rw [GateConstantCompare.flipMarked_involutive z]

inductive RangeGate (r : ℕ)
  | comparator (g : Gate r)
  | enabledFlip
  | notEnable
  | notMarked

def RangeGate.eval (threshold : ℕ) : RangeGate r → Configuration r → Configuration r
  | .comparator g => Gate.eval threshold g
  | .enabledFlip => GateControlledCompare.enabledFlip
  | .notEnable => fun z => (!z.1, z.2)
  | .notMarked => fun z => (z.1, GateConstantCompare.flipMarked z.2)

def RangeGate.arity : RangeGate r → ℕ
  | .comparator g => g.arity
  | .enabledFlip => 2
  | .notEnable => 1
  | .notMarked => 1

theorem RangeGate.arity_le_three (g : RangeGate r) : g.arity ≤ 3 := by
  cases g with
  | comparator g => exact g.arity_le_three
  | enabledFlip => norm_num [RangeGate.arity]
  | notEnable => norm_num [RangeGate.arity]
  | notMarked => norm_num [RangeGate.arity]

theorem RangeGate.eval_involutive (threshold : ℕ) (g : RangeGate r) :
    Function.Involutive (RangeGate.eval threshold g) := by
  cases g with
  | comparator g => exact Gate.eval_involutive threshold g
  | enabledFlip => exact enabledFlip_involutive
  | notEnable =>
      intro z
      rcases z with ⟨enable, z⟩
      cases enable <;> rfl
  | notMarked =>
      intro z
      rcases z with ⟨enable, z⟩
      change (enable, GateConstantCompare.flipMarked
        (GateConstantCompare.flipMarked z)) = (enable, z)
      rw [GateConstantCompare.flipMarked_involutive z]

def rangeExec (threshold : ℕ) : List (RangeGate r) → Configuration r → Configuration r
  | [], z => z
  | g :: gs, z => rangeExec threshold gs (RangeGate.eval threshold g z)

theorem rangeExec_append (threshold : ℕ) (gs hs : List (RangeGate r))
    (z : Configuration r) :
    rangeExec threshold (gs ++ hs) z =
      rangeExec threshold hs (rangeExec threshold gs z) := by
  induction gs generalizing z with
  | nil => rfl
  | cons g gs ih => simp only [List.cons_append, rangeExec, ih]

theorem rangeExec_reverse_exec (threshold : ℕ) (gs : List (RangeGate r))
    (z : Configuration r) :
    rangeExec threshold gs.reverse (rangeExec threshold gs z) = z := by
  induction gs generalizing z with
  | nil => rfl
  | cons g gs ih =>
      rw [List.reverse_cons, rangeExec_append]
      simp only [rangeExec]
      rw [ih]
      exact RangeGate.eval_involutive threshold g z

theorem rangeExec_exec_reverse (threshold : ℕ) (gs : List (RangeGate r))
    (z : Configuration r) :
    rangeExec threshold gs (rangeExec threshold gs.reverse z) = z := by
  simpa only [List.reverse_reverse] using
    rangeExec_reverse_exec threshold gs.reverse z

theorem rangeExec_map (threshold : ℕ) (gs : List (Gate r)) (z : Configuration r) :
    rangeExec threshold (gs.map RangeGate.comparator) z = exec threshold gs z := by
  induction gs generalizing z with
  | nil => rfl
  | cons g gs ih => exact ih (Gate.eval threshold g z)

def rangeCompareCircuit (threshold r : ℕ) : List (RangeGate r) :=
  if threshold = 2 ^ r then [.enabledFlip]
  else (compareCircuit threshold r).map RangeGate.comparator

/-- A clean numerical comparator controlled on the supplied enable wire,
with the closed range `0 ≤ threshold ≤ 2^r` covered exactly. -/
theorem rangeCompareCircuit_correct (threshold : ℕ) (enable : Bool)
    (x : Word r) (marked : Bool) (h : threshold ≤ 2 ^ r) :
    rangeExec threshold (rangeCompareCircuit threshold r)
        (encoded threshold 0 enable x marked) =
      encoded threshold 0 enable x
        (if enable && decide (GatePointerEncoding.wordValue x < threshold)
          then !marked else marked) := by
  by_cases he : threshold = 2 ^ r
  · subst threshold
    have hx := GatePointerEncoding.wordValue_lt_pow x
    cases enable <;>
      simp [rangeCompareCircuit, rangeExec, RangeGate.eval,
        GateControlledCompare.enabledFlip, encoded,
        GateConstantCompare.flipMarked, GateConstantCompare.encoded, hx]
  · rw [rangeCompareCircuit, if_neg he, rangeExec_map,
        compareCircuit_correct_marked,
        GateConstantCompare.lessThan_eq_decide threshold x (by omega)]

theorem rangeCompareCircuit_length (threshold r : ℕ) :
    (rangeCompareCircuit threshold r).length ≤ 2 * r + 1 := by
  by_cases he : threshold = 2 ^ r
  · simp [rangeCompareCircuit, he]
  · simp [rangeCompareCircuit, he, compareCircuit_length]

def rangeCircuitLinear (threshold : ℕ) (gs : List (RangeGate r)) :
    Amplitude r →ₗ[ℂ] Amplitude r :=
  Finsupp.linearCombination ℂ
    (fun z => Finsupp.single (rangeExec threshold gs z) 1)

theorem rangeCircuitLinear_single (threshold : ℕ) (gs : List (RangeGate r))
    (z : Configuration r) (a : ℂ) :
    rangeCircuitLinear threshold gs (Finsupp.single z a) =
      Finsupp.single (rangeExec threshold gs z) a := by
  simp [rangeCircuitLinear]

theorem rangeCircuitLinear_reverse_comp (threshold : ℕ) (gs : List (RangeGate r)) :
    (rangeCircuitLinear threshold gs.reverse).comp
        (rangeCircuitLinear threshold gs) = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro z a
  simp [rangeCircuitLinear_single, rangeExec_reverse_exec]

theorem rangeCircuitLinear_comp_reverse (threshold : ℕ) (gs : List (RangeGate r)) :
    (rangeCircuitLinear threshold gs).comp
        (rangeCircuitLinear threshold gs.reverse) = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro z a
  simp [rangeCircuitLinear_single, rangeExec_exec_reverse]

/-- Exact numerical conjunction phase implemented by at most `2r+1`
three-wire gates, including the full-range threshold. -/
theorem rangeCompareCircuit_kickback (threshold : ℕ) (enable : Bool)
    (x : Word r) (a : ℂ) (h : threshold ≤ 2 ^ r) :
    rangeCircuitLinear threshold (rangeCompareCircuit threshold r)
        (kickback threshold enable x a) =
      GateConstantCompare.phaseSign
        (enable && decide (GatePointerEncoding.wordValue x < threshold)) •
          kickback threshold enable x a := by
  unfold kickback
  rw [map_sub, rangeCircuitLinear_single, rangeCircuitLinear_single,
    rangeCompareCircuit_correct threshold enable x false h,
    rangeCompareCircuit_correct threshold enable x true h]
  cases hp : enable && decide (GatePointerEncoding.wordValue x < threshold) <;>
    simp [GateConstantCompare.phaseSign]

/-- Semantic action on a complemented input flag.  The physical two-NOT
conjugation implementing this change of polarity is constructed below. -/
theorem rangeCompareCircuit_negatedInput (threshold : ℕ) (flag : Bool)
    (x : Word r) (a : ℂ) (h : threshold ≤ 2 ^ r) :
    rangeCircuitLinear threshold (rangeCompareCircuit threshold r)
        (kickback threshold (!flag) x a) =
      (if flag = false ∧ GatePointerEncoding.wordValue x < threshold
        then (-1 : ℂ) else 1) • kickback threshold (!flag) x a := by
  rw [rangeCompareCircuit_kickback threshold (!flag) x a h]
  cases flag <;>
    by_cases hx : GatePointerEncoding.wordValue x < threshold <;>
    simp [GateConstantCompare.phaseSign, hx]

/-- Literal negative-control compilation on the existing physical flag. -/
def acceptedCompareCircuit (threshold r : ℕ) : List (RangeGate r) :=
  [.notEnable] ++ rangeCompareCircuit threshold r ++ [.notEnable]

theorem acceptedCompareCircuit_correct (threshold : ℕ) (flag : Bool)
    (x : Word r) (marked : Bool) (h : threshold ≤ 2 ^ r) :
    rangeExec threshold (acceptedCompareCircuit threshold r)
        (encoded threshold 0 flag x marked) =
      encoded threshold 0 flag x
        (if (!flag) && decide (GatePointerEncoding.wordValue x < threshold)
          then !marked else marked) := by
  rw [acceptedCompareCircuit, rangeExec_append, rangeExec_append]
  change rangeExec threshold [.notEnable]
      (rangeExec threshold (rangeCompareCircuit threshold r)
        (encoded threshold 0 (!flag) x marked)) = _
  rw [rangeCompareCircuit_correct threshold (!flag) x marked h]
  cases flag <;> rfl

/-- Every borrowed comparison flag and the attenuation flag itself are
restored, and the exact conjunction phase is applied on the actual input
flag, without a free-control convention. -/
theorem acceptedCompareCircuit_kickback (threshold : ℕ) (flag : Bool)
    (x : Word r) (a : ℂ) (h : threshold ≤ 2 ^ r) :
    rangeCircuitLinear threshold (acceptedCompareCircuit threshold r)
        (kickback threshold flag x a) =
      (if flag = false ∧ GatePointerEncoding.wordValue x < threshold
        then (-1 : ℂ) else 1) • kickback threshold flag x a := by
  unfold kickback
  rw [map_sub, rangeCircuitLinear_single, rangeCircuitLinear_single,
    acceptedCompareCircuit_correct threshold flag x false h,
    acceptedCompareCircuit_correct threshold flag x true h]
  cases flag <;>
    by_cases hx : GatePointerEncoding.wordValue x < threshold <;>
    simp [hx]

theorem acceptedCompareCircuit_length (threshold r : ℕ) :
    (acceptedCompareCircuit threshold r).length ≤ 2 * r + 3 := by
  have h := rangeCompareCircuit_length threshold r
  simp only [acceptedCompareCircuit, List.length_append, List.length_cons,
    List.length_nil]
  omega

/-- The exact initial-state reflection includes a final unconditional NOT
on the minus target.  This supplies the global minus sign rather than
discarding it: accepted input has phase `+1`, all other words have phase `-1`.
This sign distinction matters when the reflection is subsequently controlled.
-/
def zeroStateReflectionCircuit (r : ℕ) : List (RangeGate r) :=
  acceptedCompareCircuit 1 r ++ [.notMarked]

theorem zeroStateReflectionCircuit_correct (flag : Bool) (x : Word r)
    (marked : Bool) :
    rangeExec 1 (zeroStateReflectionCircuit r)
        (encoded 1 0 flag x marked) =
      encoded 1 0 flag x
        (if flag = false ∧ GatePointerEncoding.wordValue x = 0
          then marked else !marked) := by
  have hcap : 1 ≤ 2 ^ r := by
    have hp : 0 < (2 : ℕ) ^ r := pow_pos (by decide) r
    omega
  rw [zeroStateReflectionCircuit, rangeExec_append,
    acceptedCompareCircuit_correct 1 flag x marked hcap]
  simp only [rangeExec, RangeGate.eval]
  cases flag <;>
    by_cases hx : GatePointerEncoding.wordValue x = 0 <;>
    simp [GateConstantCompare.flipMarked, encoded,
      GateConstantCompare.encoded, hx]

/-- Clean, exact action of `2|zero,false⟩⟨zero,false| - I` in numerical word
coordinates.  The reusable minus target and all borrow flags are restored.
-/
theorem zeroStateReflectionCircuit_kickback (flag : Bool) (x : Word r)
    (a : ℂ) :
    rangeCircuitLinear 1 (zeroStateReflectionCircuit r)
        (kickback 1 flag x a) =
      (if flag = false ∧ GatePointerEncoding.wordValue x = 0
        then (1 : ℂ) else -1) • kickback 1 flag x a := by
  unfold kickback
  rw [map_sub, rangeCircuitLinear_single, rangeCircuitLinear_single,
    zeroStateReflectionCircuit_correct flag x false,
    zeroStateReflectionCircuit_correct flag x true]
  by_cases h : flag = false ∧ GatePointerEncoding.wordValue x = 0 <;>
    simp [h]

theorem zeroStateReflectionCircuit_length (r : ℕ) :
    (zeroStateReflectionCircuit r).length ≤ 2 * r + 4 := by
  have h := acceptedCompareCircuit_length 1 r
  simp only [zeroStateReflectionCircuit, List.length_append, List.length_cons,
    List.length_nil]
  omega

end
end SparseHamiltonian.GateControlledCompare
