import GateEfficientHamiltonian.GatePrivatePointer
/-!
# Little-endian words as a power-of-two pointer register

The ripple circuit is defined directly on Boolean words.  This section fixes
the numerical convention needed to compare it with the `Fin`-indexed reuse
proof: bit zero is least significant.  The value recursion, strict
power-of-two bound and injectivity are proved without choosing an arbitrary
finite equivalence.  Thus the eventual equivalence with `Fin (2^r)` has the
same cyclic order as the concrete pointer circuit.
-/

namespace SparseHamiltonian.GatePointerEncoding

noncomputable section

open scoped BigOperators

abbrev Word (r : ℕ) := GatePrivatePointer.Word r

def bitValue (b : Bool) : ℕ := if b then 1 else 0

@[simp] theorem bitValue_false : bitValue false = 0 := rfl
@[simp] theorem bitValue_true : bitValue true = 1 := rfl

theorem bitValue_le_one (b : Bool) : bitValue b ≤ 1 := by
  cases b <;> simp

theorem bitValue_injective : Function.Injective bitValue := by
  intro a b h
  cases a <;> cases b <;> simp_all

/-- Little-endian unsigned value. -/
def wordValue (x : Word r) : ℕ :=
  ∑ j : Fin r, bitValue (x j) * 2 ^ j.val

def tail (x : Word (r + 1)) : Word r := fun j => x j.succ

def prepend (b : Bool) (x : Word r) : Word (r + 1) :=
  Fin.cases b x

@[simp] theorem prepend_zero (b : Bool) (x : Word r) :
    prepend b x 0 = b := rfl

@[simp] theorem prepend_succ (b : Bool) (x : Word r) (j : Fin r) :
    prepend b x j.succ = x j := rfl

theorem prepend_head_tail (x : Word (r + 1)) :
    prepend (x 0) (tail x) = x := by
  funext j
  exact Fin.cases rfl (fun i => rfl) j

theorem tail_prepend (b : Bool) (x : Word r) :
    tail (prepend b x) = x := by
  funext j
  rfl

/-- The numerical representation obeys the expected least-significant-bit
recursion. -/
theorem wordValue_succ (x : Word (r + 1)) :
    wordValue x = bitValue (x 0) + 2 * wordValue (tail x) := by
  rw [wordValue, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, mul_one]
  rw [wordValue, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  simp only [tail, Fin.val_succ]
  rw [pow_succ]
  ring

theorem wordValue_prepend (b : Bool) (x : Word r) :
    wordValue (prepend b x) = bitValue b + 2 * wordValue x := by
  rw [wordValue_succ, prepend_zero, tail_prepend]

/-- Every `r`-bit word is in the promised power-of-two range. -/
theorem wordValue_lt_pow (x : Word r) : wordValue x < 2 ^ r := by
  induction r with
  | zero => simp [wordValue]
  | succ r ih =>
      rw [wordValue_succ, pow_succ]
      have ht := ih (tail x)
      have hb := bitValue_le_one (x 0)
      omega

def wordFin (x : Word r) : Fin (2 ^ r) :=
  ⟨wordValue x, wordValue_lt_pow x⟩

@[simp] theorem wordFin_val (x : Word r) : (wordFin x).val = wordValue x := rfl

theorem bitValue_add_two_mod (b : Bool) (n : ℕ) :
    (bitValue b + 2 * n) % 2 = bitValue b := by
  cases b <;> simp [bitValue, Nat.add_mod]

theorem bitValue_add_two_div (b : Bool) (n : ℕ) :
    (bitValue b + 2 * n) / 2 = n := by
  cases b <;> simp only [bitValue_false, bitValue_true] <;> omega

/-- The numerical convention distinguishes all Boolean words. -/
theorem wordValue_injective : Function.Injective (@wordValue r) := by
  induction r with
  | zero =>
      intro x y h
      funext j
      exact Fin.elim0 j
  | succ r ih =>
      intro x y hxy
      have hm := congrArg (fun n : ℕ => n % 2) hxy
      rw [wordValue_succ, wordValue_succ,
        bitValue_add_two_mod, bitValue_add_two_mod] at hm
      have hhead : x 0 = y 0 := bitValue_injective hm
      have hd := congrArg (fun n : ℕ => n / 2) hxy
      rw [wordValue_succ, wordValue_succ,
        bitValue_add_two_div, bitValue_add_two_div] at hd
      have htail : tail x = tail y := ih hd
      funext j
      exact Fin.cases hhead (fun i => congrFun htail i) j

theorem wordFin_injective : Function.Injective (@wordFin r) := by
  intro x y h
  apply wordValue_injective
  exact congrArg Fin.val h

theorem card_word (r : ℕ) : Fintype.card (Word r) = 2 ^ r := by
  simp [Word]

theorem wordFin_bijective : Function.Bijective (@wordFin r) := by
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨wordFin_injective, by simp⟩

/-- The canonical equivalence uses the numerical little-endian map itself,
not an arbitrary enumeration of the finite type. -/
def wordEquivFin (r : ℕ) : Word r ≃ Fin (2 ^ r) :=
  Equiv.ofBijective wordFin wordFin_bijective

@[simp] theorem wordEquivFin_apply (x : Word r) :
    wordEquivFin r x = wordFin x := rfl

def zeroWord (r : ℕ) : Word r := fun _ => false
def oneWord (r : ℕ) : Word r := fun _ => true

@[simp] theorem wordValue_zero (r : ℕ) : wordValue (zeroWord r) = 0 := by
  simp [wordValue, zeroWord]

/-- The all-one word is the final word before cyclic wraparound. -/
theorem wordValue_one (r : ℕ) : wordValue (oneWord r) = 2 ^ r - 1 := by
  induction r with
  | zero => simp [wordValue]
  | succ r ih =>
      rw [wordValue_succ]
      change 1 + 2 * wordValue (oneWord r) = 2 ^ (r + 1) - 1
      rw [ih, pow_succ]
      have hpos : 0 < 2 ^ r := by positivity
      omega

/-- Coordinate action of the semantic ripple update.  A bit is toggled
exactly when it belongs to the active prefix and all lower input bits are
one. -/
theorem incrementWord_apply (s : Bool) (n : ℕ) (h : n ≤ r)
    (x : Word r) (i : Fin r) :
    GatePrivatePointer.incrementWord s n h x i =
      if i.val < n then
        if s && GatePrivatePointer.onePrefix x i.val then !(x i) else x i
      else x i := by
  induction n generalizing x with
  | zero => simp [GatePrivatePointer.incrementWord]
  | succ n ih =>
      let j : Fin r := ⟨n, by omega⟩
      change GatePrivatePointer.incrementWord s n (by omega)
          (GatePrivatePointer.advance s j x) i = _
      rw [ih]
      rcases lt_trichotomy i.val n with hil | hieq | higt
      · have hij : i ≠ j := by
          intro he
          have hv := congrArg Fin.val he
          change i.val = n at hv
          omega
        have hp := GatePrivatePointer.onePrefix_advance s j x i.val (by
          change i.val ≤ n
          omega)
        have his : i.val < n + 1 := by omega
        simp only [if_pos hil, if_pos his, hp,
          GatePrivatePointer.advance_apply_ne s j x i hij]
      · have hij : i = j := Fin.ext (by simpa [j] using hieq)
        subst i
        have hnot : ¬j.val < n := by simp [j]
        have hyes : j.val < n + 1 := by simp [j]
        simp only [if_neg hnot, if_pos hyes, GatePrivatePointer.advance_apply_self]
      · have hil : ¬ i.val < n := by omega
        have his : ¬ i.val < n + 1 := by omega
        have hij : i ≠ j := by
          intro he
          have hv := congrArg Fin.val he
          change i.val = n at hv
          omega
        simp only [if_neg hil, if_neg his,
          GatePrivatePointer.advance_apply_ne s j x i hij]

def successorWord (x : Word r) : Word r :=
  GatePrivatePointer.incrementWord true r le_rfl x

theorem successorWord_apply (x : Word r) (i : Fin r) :
    successorWord x i =
      if GatePrivatePointer.onePrefix x i.val then !(x i) else x i := by
  rw [successorWord, incrementWord_apply]
  simp

/-- Splitting off the least-significant bit also splits the lower-one
predicate. -/
theorem onePrefix_tail (x : Word (r + 1)) (n : ℕ) (hn : n ≤ r) :
    GatePrivatePointer.onePrefix x (n + 1) =
      (x 0 && GatePrivatePointer.onePrefix (tail x) n) := by
  induction n with
  | zero =>
      simp [GatePrivatePointer.onePrefix, GatePrivatePointer.bit]
  | succ n ih =>
      have hn' : n ≤ r := by omega
      have hnlt : n < r := by omega
      have hb : GatePrivatePointer.bit x (n + 1) =
          GatePrivatePointer.bit (tail x) n := by
        simp [GatePrivatePointer.bit, tail, hnlt]
      rw [GatePrivatePointer.onePrefix, ih hn',
        GatePrivatePointer.onePrefix, hb]
      simp [Bool.and_assoc]

theorem successorWord_head (x : Word (r + 1)) :
    successorWord x 0 = !(x 0) := by
  rw [successorWord_apply]
  simp

/-- The tail increments precisely when the least-significant input bit was
one.  This is the recursive carry law of binary successor. -/
theorem successorWord_tail (x : Word (r + 1)) :
    tail (successorWord x) =
      if x 0 then successorWord (tail x) else tail x := by
  funext j
  change successorWord x j.succ =
    (if x 0 then successorWord (tail x) else tail x) j
  rw [successorWord_apply]
  change (if GatePrivatePointer.onePrefix x (j.val + 1) then
      !(x j.succ) else x j.succ) =
    (if x 0 then successorWord (tail x) else tail x) j
  rw [onePrefix_tail x j.val (Nat.le_of_lt j.isLt)]
  cases hx : x 0 <;> simp [successorWord_apply, tail]

/-- The concrete ripple update is addition by one modulo the word capacity. -/
theorem wordValue_successor (x : Word r) :
    wordValue (successorWord x) = (wordValue x + 1) % (2 ^ r) := by
  induction r with
  | zero => simp [wordValue, successorWord]
  | succ r ih =>
      rw [wordValue_succ, successorWord_head, successorWord_tail,
        wordValue_succ x]
      cases hx : x 0
      · simp only [Bool.not_false, bitValue_true, bitValue_false,
          Bool.false_eq_true, if_false, zero_add]
        have ht := wordValue_lt_pow (tail x)
        have hbound : 2 * wordValue (tail x) + 1 < 2 ^ (r + 1) := by
          rw [pow_succ]
          omega
        rw [Nat.mod_eq_of_lt hbound]
        omega
      · simp only [Bool.not_true, bitValue_false, bitValue_true,
          ↓reduceIte, zero_add]
        rw [ih]
        have ht := wordValue_lt_pow (tail x)
        by_cases hcarry : wordValue (tail x) + 1 < 2 ^ r
        · rw [Nat.mod_eq_of_lt hcarry]
          have hbound : 1 + 2 * wordValue (tail x) + 1 < 2 ^ (r + 1) := by
            rw [pow_succ]
            omega
          rw [Nat.mod_eq_of_lt hbound]
          omega
        · have heq : wordValue (tail x) + 1 = 2 ^ r := by omega
          have hnum : 1 + 2 * wordValue (tail x) + 1 = 2 ^ (r + 1) := by
            rw [pow_succ]
            omega
          simp only [heq, Nat.mod_self, mul_zero, hnum]

/-! ### Identification with the reuse rotation -/

/-- `finRotate` is numerical successor modulo the size of a nonempty finite
type.  The proof includes the final-point branch rather than appealing to an
unstated convention about the enumeration of `Fin`. -/
theorem finRotate_val_mod {N : ℕ} (hN : 0 < N) (j : Fin N) :
    (finRotate N j).val = (j.val + 1) % N := by
  cases N with
  | zero => omega
  | succ capacity =>
      by_cases hj : j.val < capacity
      · have hrotate :
            finRotate (capacity + 1) j =
              (⟨j.val + 1, by omega⟩ : Fin (capacity + 1)) :=
          finRotate_of_lt hj
        rw [hrotate]
        simp only
        exact (Nat.mod_eq_of_lt (by omega)).symm
      · have hjlast : j.val = capacity := by omega
        have hout : (finRotate (capacity + 1) j).val = 0 := by
          by_contra hne
          have hpos : 0 < (finRotate (capacity + 1) j).val :=
            Nat.pos_of_ne_zero hne
          let q : Fin (capacity + 1) :=
            ⟨(finRotate (capacity + 1) j).val - 1, by omega⟩
          have hq : q.val < capacity := by
            dsimp [q]
            omega
          have hqrotate :
              finRotate (capacity + 1) q =
                (⟨q.val + 1, by omega⟩ : Fin (capacity + 1)) :=
            finRotate_of_lt hq
          have htarget :
              (⟨q.val + 1, by omega⟩ : Fin (capacity + 1)) =
                finRotate (capacity + 1) j := by
            apply Fin.ext
            dsimp [q]
            omega
          have hqj : q = j :=
            (finRotate (capacity + 1)).injective (hqrotate.trans htarget)
          have hval := congrArg Fin.val hqj
          dsimp [q] at hval
          omega
        rw [hout, hjlast]
        simp

/-- Under the canonical little-endian equivalence, the concrete ripple
successor is exactly Mathlib's cyclic rotation of `Fin (2^r)`. -/
theorem wordEquivFin_successor (x : Word r) :
    wordEquivFin r (successorWord x) =
      finRotate (2 ^ r) (wordEquivFin r x) := by
  apply Fin.ext
  change wordValue (successorWord x) =
    (finRotate (2 ^ r) (wordFin x)).val
  rw [wordValue_successor, finRotate_val_mod (by positivity)]
  rfl

/-- The permutation induced on words by conjugating `finRotate` through the
canonical numerical encoding. -/
def successorEquiv (r : ℕ) : Word r ≃ Word r :=
  (wordEquivFin r).trans
    ((finRotate (2 ^ r)).trans (wordEquivFin r).symm)

theorem successorEquiv_apply (x : Word r) :
    successorEquiv r x = successorWord x := by
  apply (wordEquivFin r).injective
  rw [wordEquivFin_successor]
  simp [successorEquiv]

/-- On every clean private basis state, the actual `3*r`-gate circuit applies
the word successor identified above. -/
theorem incrementCircuit_clean_private_single (x : Word r) (a : ℂ) :
    GatePrivatePointer.circuitLinear
        (GatePrivatePointer.incrementCircuit r)
        (Finsupp.single (GatePrivatePointer.encoded 0 true x) a) =
      Finsupp.single
        (GatePrivatePointer.encoded 0 true (successorWord x)) a := by
  rw [GatePrivatePointer.circuitLinear_single,
    GatePrivatePointer.private_increment]
  rfl

section Payload

variable {P V : Type*}

/-- Relabel arbitrary payload amplitudes from Boolean words to the canonical
finite pointer.  No operation is performed on the payload. -/
def relabelAmplitude (f : Word r → V) : Fin (2 ^ r) → V :=
  fun j => f ((wordEquivFin r).symm j)

/-- Coherent pullback by the permutation implemented by the ripple circuit. -/
def ripplePullback (f : Word r → V) : Word r → V :=
  fun x => f ((successorEquiv r).symm x)

/-- Coherent pullback by the reuse-register rotation. -/
def rotatePullback (f : Fin (2 ^ r) → V) : Fin (2 ^ r) → V :=
  fun j => f ((finRotate (2 ^ r)).symm j)

/-- The exact word circuit and the abstract reuse rotation induce the same
coherent action on amplitudes with an arbitrary untouched payload. -/
theorem relabel_ripplePullback (f : Word r → V) :
    relabelAmplitude (ripplePullback f) =
      rotatePullback (relabelAmplitude f) := by
  funext j
  simp [relabelAmplitude, ripplePullback, rotatePullback, successorEquiv]

abbrev WordRegisters (r : ℕ) (P V : Type*) :=
  (Word r → P) × (Word r → V)

abbrev FinRegisters (r : ℕ) (P V : Type*) :=
  (Fin (2 ^ r) → P) × (Fin (2 ^ r) → V)

def relabelRegisters (z : WordRegisters r P V) : FinRegisters r P V :=
  (relabelAmplitude z.1, relabelAmplitude z.2)

/-- The public sector is fixed and only private amplitudes are pulled back by
the concrete word permutation. -/
def rippleIncrement (z : WordRegisters r P V) : WordRegisters r P V :=
  (z.1, ripplePullback z.2)

/-- This is the power-of-two instance of the formula defining
`GateBinaryReuse.increment`. -/
def rotateIncrement (z : FinRegisters r P V) : FinRegisters r P V :=
  (z.1, rotatePullback z.2)

/-- Relabelling intertwines the full public/private register action, so the
coherent reuse proof may use the actual ripple circuit instead of an abstract
pointer permutation. -/
theorem relabel_rippleIncrement (z : WordRegisters r P V) :
    relabelRegisters (rippleIncrement z) =
      rotateIncrement (relabelRegisters z) := by
  apply Prod.ext
  · rfl
  · exact relabel_ripplePullback z.2

end Payload

end
end SparseHamiltonian.GatePointerEncoding
