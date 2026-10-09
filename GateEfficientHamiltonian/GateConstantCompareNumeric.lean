import GateEfficientHamiltonian.GateWalshInverse
/-!
# Numerical correctness of the clean constant comparator

The borrow circuit uses the lowest `r` threshold bits.  We prove that its
output is the numerical predicate when the threshold is below `2^r`.
The full-range threshold `2^r` requires separate treatment: all pointer
words are accepted.  A wrapper implements that public special case with
one literal NOT gate on the marked wire.
-/

namespace SparseHamiltonian.GateConstantCompare

noncomputable section

open scoped BigOperators
open GatePointerEncoding

variable {r : ℕ}

/-- The numerical value of the first `n` bits of an infinite bit sequence. -/
def prefixValue (bits : ℕ → Bool) (n : ℕ) : ℕ :=
  wordValue (fun j : Fin n => bits j.val)

@[simp] theorem prefixValue_zero (bits : ℕ → Bool) :
    prefixValue bits 0 = 0 := by
  simp [prefixValue, wordValue]

theorem prefixValue_succ (bits : ℕ → Bool) (n : ℕ) :
    prefixValue bits (n + 1) =
      prefixValue bits n + bitValue (bits n) * 2 ^ n := by
  unfold prefixValue wordValue
  rw [Fin.sum_univ_castSucc]
  rfl

theorem prefixValue_lt (bits : ℕ → Bool) (n : ℕ) :
    prefixValue bits n < 2 ^ n :=
  wordValue_lt_pow (fun j : Fin n => bits j.val)

theorem prefixValue_pointer (x : Word r) :
    prefixValue (GatePrivatePointer.bit x) r = wordValue x := by
  unfold prefixValue
  congr 1
  funext j
  exact GatePrivatePointer.bit_index x j

/-- The invariant behind the ripple subtraction is a comparison of its
two numerical prefixes.  No comparator-correctness hypothesis is used. -/
theorem borrowValue_iff_prefix_lt (threshold : ℕ) (x : Word r) (n : ℕ) :
    borrowValue threshold x n = true ↔
      prefixValue (GatePrivatePointer.bit x) n <
        prefixValue (thresholdBit threshold) n := by
  induction n with
  | zero => simp [borrowValue]
  | succ n ih =>
      have hxlt := prefixValue_lt (GatePrivatePointer.bit x) n
      have htlt := prefixValue_lt (thresholdBit threshold) n
      rw [borrowValue, prefixValue_succ, prefixValue_succ]
      cases hx : GatePrivatePointer.bit x n <;>
        cases ht : thresholdBit threshold n <;>
        cases hb : borrowValue threshold x n <;>
        simp_all [nextBorrow, bitValue] <;> omega

/-- Public threshold bits on the physical word register. -/
def thresholdWord (threshold r : ℕ) : Word r :=
  fun j => thresholdBit threshold j.val

theorem bitValue_eq_toNat (b : Bool) : bitValue b = b.toNat := by
  cases b <;> rfl

theorem thresholdWord_head_value (threshold r : ℕ) :
    bitValue (thresholdWord threshold (r + 1) 0) = threshold % 2 := by
  simpa [thresholdWord, thresholdBit, bitValue_eq_toNat] using
    Nat.toNat_testBit threshold 0

theorem thresholdWord_tail (threshold r : ℕ) :
    tail (thresholdWord threshold (r + 1)) = thresholdWord (threshold / 2) r := by
  funext j
  exact Nat.testBit_succ threshold j.val

/-- Reconstruction of a representable threshold from its literal bits. -/
theorem wordValue_thresholdWord (threshold r : ℕ)
    (h : threshold < 2 ^ r) :
    wordValue (thresholdWord threshold r) = threshold := by
  induction r generalizing threshold with
  | zero =>
      have ht : threshold = 0 := by simpa using h
      subst threshold
      simp [wordValue]
  | succ r ih =>
      have ht : threshold / 2 < 2 ^ r := by
        rw [pow_succ] at h
        omega
      rw [wordValue_succ, thresholdWord_head_value, thresholdWord_tail, ih _ ht]
      have hd := Nat.mod_add_div threshold 2
      omega

/-- The precise supported range of the unwrapped borrow comparator. -/
theorem lessThan_iff_wordValue_lt (threshold : ℕ) (x : Word r)
    (h : threshold < 2 ^ r) :
    lessThan threshold x = true ↔ wordValue x < threshold := by
  rw [lessThan, borrowValue_iff_prefix_lt, prefixValue_pointer]
  change wordValue x < wordValue (thresholdWord threshold r) ↔ _
  rw [wordValue_thresholdWord threshold r h]

theorem lessThan_eq_decide (threshold : ℕ) (x : Word r)
    (h : threshold < 2 ^ r) :
    lessThan threshold x = decide (wordValue x < threshold) := by
  have hc := lessThan_iff_wordValue_lt threshold x h
  cases hb : lessThan threshold x <;> simp_all

/-- The complete, clean circuit now has an arithmetic specification. -/
theorem compareCircuit_correct_numeric (threshold : ℕ) (x : Word r)
    (marked : Bool) (h : threshold < 2 ^ r) :
    exec threshold (compareCircuit threshold r)
        (encoded threshold 0 x marked) =
      encoded threshold 0 x
        (if wordValue x < threshold then !marked else marked) := by
  rw [compareCircuit_correct_marked, lessThan_eq_decide threshold x h]
  simp

/-- A literal one-wire NOT is the all-accept branch at threshold `2^r`. -/
def flipMarked (z : Configuration r) : Configuration r :=
  { z with marked := !z.marked }

theorem flipMarked_involutive : Function.Involutive (@flipMarked r) := by
  intro z
  apply Configuration.ext <;> simp [flipMarked]

/-- The wrapper adds only a one-wire gate to the existing elementary set. -/
inductive RangeGate (r : ℕ)
  | comparator (g : Gate r)
  | notMarked

def RangeGate.eval (threshold : ℕ) : RangeGate r → Configuration r → Configuration r
  | .comparator g => Gate.eval threshold g
  | .notMarked => flipMarked

def RangeGate.arity : RangeGate r → ℕ
  | .comparator g => g.arity
  | .notMarked => 1

theorem RangeGate.arity_le_three (g : RangeGate r) : g.arity ≤ 3 := by
  cases g with
  | comparator g => exact g.arity_le_three
  | notMarked =>
      change (1 : ℕ) ≤ 3
      decide

theorem RangeGate.eval_involutive (threshold : ℕ) (g : RangeGate r) :
    Function.Involutive (RangeGate.eval threshold g) := by
  cases g with
  | comparator g => exact Gate.eval_involutive threshold g
  | notMarked => exact flipMarked_involutive

def rangeExec (threshold : ℕ) : List (RangeGate r) → Configuration r → Configuration r
  | [], z => z
  | g :: gs, z => rangeExec threshold gs (RangeGate.eval threshold g z)

theorem rangeExec_map (threshold : ℕ) (gs : List (Gate r)) (z : Configuration r) :
    rangeExec threshold (gs.map RangeGate.comparator) z = exec threshold gs z := by
  induction gs generalizing z with
  | nil => rfl
  | cons g gs ih => exact ih (Gate.eval threshold g z)

/-- A closed-range comparator accepting every threshold from `0` to `2^r`.
The branch is chosen at circuit construction time from public data. -/
def rangeCompareCircuit (threshold r : ℕ) : List (RangeGate r) :=
  if threshold = 2 ^ r then [.notMarked]
  else (compareCircuit threshold r).map RangeGate.comparator

/-- Both endpoint thresholds are covered, with unchanged pointer and clean
borrow flags.  In particular, the all-accept threshold never wraps to zero. -/
theorem rangeCompareCircuit_correct (threshold : ℕ) (x : Word r)
    (marked : Bool) (h : threshold ≤ 2 ^ r) :
    rangeExec threshold (rangeCompareCircuit threshold r)
        (encoded threshold 0 x marked) =
      encoded threshold 0 x
        (if wordValue x < threshold then !marked else marked) := by
  by_cases he : threshold = 2 ^ r
  · have hx : wordValue x < threshold := he.symm ▸ wordValue_lt_pow x
    simp only [rangeCompareCircuit, if_pos he, rangeExec, RangeGate.eval, if_pos hx]
    rfl
  · rw [rangeCompareCircuit, if_neg he, rangeExec_map]
    exact compareCircuit_correct_numeric threshold x marked (by omega)

theorem rangeCompareCircuit_length (threshold r : ℕ) :
    (rangeCompareCircuit threshold r).length ≤ 2 * r + 1 := by
  by_cases he : threshold = 2 ^ r
  · simp [rangeCompareCircuit, he]
  · simp [rangeCompareCircuit, he, compareCircuit_length]

/-- Coherent semantics of the concrete closed-range gate list. -/
def rangeCircuitLinear (threshold : ℕ) (gs : List (RangeGate r)) :
    Amplitude r →ₗ[ℂ] Amplitude r :=
  Finsupp.linearCombination ℂ
    (fun z => Finsupp.single (rangeExec threshold gs z) 1)

theorem rangeCircuitLinear_single (threshold : ℕ) (gs : List (RangeGate r))
    (z : Configuration r) (a : ℂ) :
    rangeCircuitLinear threshold gs (Finsupp.single z a) =
      Finsupp.single (rangeExec threshold gs z) a := by
  simp [rangeCircuitLinear]

/-- Numerical phase kickback, including `threshold = 2^r`, from the actual
bounded-arity comparator circuit.  Borrow flags and the minus-state ancilla
are cleanly restored, rather than supplied as a semantic assumption. -/
theorem rangeCompareCircuit_kickback (threshold : ℕ) (x : Word r) (a : ℂ)
    (h : threshold ≤ 2 ^ r) :
    rangeCircuitLinear threshold (rangeCompareCircuit threshold r)
        (kickback threshold x a) =
      (if wordValue x < threshold then (-1 : ℂ) else 1) •
        kickback threshold x a := by
  unfold kickback
  rw [map_sub, rangeCircuitLinear_single, rangeCircuitLinear_single,
    rangeCompareCircuit_correct threshold x false h,
    rangeCompareCircuit_correct threshold x true h]
  by_cases hx : wordValue x < threshold <;> simp [hx]

end

end SparseHamiltonian.GateConstantCompare
