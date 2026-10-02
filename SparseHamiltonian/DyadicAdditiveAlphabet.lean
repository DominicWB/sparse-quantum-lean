import SparseHamiltonian.AmplifiedSimulationBudget

/-!
# A bounded dyadic decoder over a genuine finite additive alphabet

The signed-magnitude code is transported to a finite cyclic group. Its zero
represents the rounded value zero. Codes outside the certified complex disk
are decoded as zero, so the decoder bound holds on every basis label without
inflating the public entry bound. Valid encoded entries retain precisely the
previously proved symmetric dyadic rounding.

This is a finite alphabet and an exact query-model decoder, not a gate-cost
claim for arithmetic or the computation of arbitrary real input entries.
-/

namespace SparseHamiltonian.DyadicAdditiveAlphabet

noncomputable section
open SparseDyadicRounding
open scoped ComplexConjugate

instance code_card_neZero (M : ℕ) : NeZero (Fintype.card (Code M)) := by
  constructor
  rw [card_code]
  positivity

/-- A finite additive group with exactly as many labels as the dyadic code. -/
abbrev Word (M : ℕ) := ZMod (Fintype.card (Code M))

/-- A fixed finite encoding equivalence; it carries no unknown-input data. -/
def rawEquiv (M : ℕ) : Code M ≃ Word M :=
  (Fintype.equivFin (Code M)).trans (ZMod.finEquiv _).toEquiv

/-- Shift the finite equivalence so the all-zero value uses additive zero. -/
def pack (M : ℕ) : Code M ≃ Word M where
  toFun c := rawEquiv M c - rawEquiv M (SparseDyadicRounding.encode 0 M 0)
  invFun w := (rawEquiv M).symm (w + rawEquiv M (SparseDyadicRounding.encode 0 M 0))
  left_inv c := by simp
  right_inv w := by simp

@[simp] theorem encode_zero_eq (b M : ℕ) :
    SparseDyadicRounding.encode b M 0 = SparseDyadicRounding.encode 0 M 0 := by
  simp [SparseDyadicRounding.encode, encodeReal, magnitude]

/-- The rounded value is encoded as an actual cyclic-group element. -/
def encode (b M : ℕ) (z : ℂ) : Word M :=
  pack M (SparseDyadicRounding.encode b M z)

@[simp] theorem encode_zero (b M : ℕ) : encode b M 0 = 0 := by
  simp [encode, pack]

/-- Decode every finite word, mapping unused out-of-disk codes to zero. -/
def decode (b : ℕ) (A : ℝ) {M : ℕ} (w : Word M) : ℂ :=
  let z := SparseDyadicRounding.decode b ((pack M).symm w)
  if ‖z‖ ≤ A then z else 0

/-- Unlike a box decoder, this bound applies to every code in the alphabet. -/
theorem decode_bound (b : ℕ) (A : ℝ) (hA : 0 ≤ A) {M : ℕ} (w : Word M) :
    ‖decode b A w‖ ≤ A := by
  dsimp only [decode]
  split_ifs with h
  · exact h
  · simpa using hA

/-- No modification is made to any encoded entry within the public disk. -/
theorem decode_encode (b M : ℕ) (A : ℝ) (z : ℂ) (hz : ‖z‖ ≤ A) :
    decode b A (encode b M z) = value b M z := by
  simp only [decode, encode, Equiv.symm_apply_apply]
  exact if_pos ((norm_value_le b M z).trans hz)

@[simp] theorem decode_zero (b : ℕ) (A : ℝ) {M : ℕ} :
    decode b A (0 : Word M) = 0 := by
  have hp : (pack M).symm 0 = SparseDyadicRounding.encode 0 M 0 := by
    apply (pack M).injective
    simp [pack]
  have hz : SparseDyadicRounding.decode b (SparseDyadicRounding.encode 0 M 0) = 0 := by
    rw [← encode_zero_eq b M]
    exact SparseDyadicRounding.value_zero b M
  simp [decode, hp, hz]

/-- The additive-code representation has the same certified dyadic error. -/
theorem error_le (b : ℕ) (A : ℝ) (z : ℂ) (hz : ‖z‖ ≤ A) :
    ‖z - decode b A (encode b (capacity b A) z)‖ ≤ 2 / scale b := by
  rw [decode_encode b _ A z hz]
  exact value_error_le b A z hz

/-- Conjugation is exact on the encoded entries used by a bounded matrix. -/
theorem conjugate_encode (b M : ℕ) (A : ℝ) (z : ℂ) (hz : ‖z‖ ≤ A) :
    decode b A (encode b M (conj z)) = conj (decode b A (encode b M z)) := by
  rw [decode_encode b M A z hz,
    decode_encode b M A (conj z) (by simpa using hz)]
  exact value_star b M z

/-- Transport to the additive group does not enlarge the value alphabet. -/
theorem card_word (M : ℕ) : Fintype.card (Word M) = (2 * (M + 1)) ^ 2 := by
  rw [← Fintype.card_congr (rawEquiv M), card_code]

/-- The actual additive alphabet obeys the earlier logarithmic bit capacity. -/
theorem card_word_le_binary (b k : ℕ) (A : ℝ) (hA : A ≤ (2 : ℝ) ^ k) :
    Fintype.card (Word (capacity b A)) ≤ 2 ^ (2 * (b + k + 2)) := by
  rw [← Fintype.card_congr (rawEquiv (capacity b A))]
  exact card_code_le_binary b k A hA

end
end SparseHamiltonian.DyadicAdditiveAlphabet
