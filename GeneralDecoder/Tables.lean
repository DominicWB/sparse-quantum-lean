import GeneralDecoder.PadArith
import GateOptimalBinary.Tables
import GateEfficientBitBudget.Bits

/-!
# The arithmetic of a general decoder can be met: reversible lookup tables

The computational assumptions of the general-decoder theorems (`ManuscriptConformance`:
`comp_rotArith`, `comp_signedArithV`, `comp_clipArithV`) ask for reversible word arithmetic of the
decoder `val` of the stored words, writing the angle and phase words of the local rotation
parameters to a given accuracy with polynomially many gates and work wires. This file shows that
the form and the accuracy of these arithmetics can be met for every decoder and every positive
accuracy by the reversible lookup tables of `GateOptimalBinary.Tables` (of length exponential in
the width `2b` of the stored words), as for the decoder `c₀(X + iY)`
(`GateOptimalBinary.factorWordArith_exists`, `GateOptimalBinary.clipArith_exists`):

* `WordArith.table`: the lookup-table word arithmetic of a pair of word functions, on at least
  `|I| - 1` work wires, with `WordArith.table_length`;
* `factorAcc_table`, `rotAcc_table`: the accuracies `FactorAcc` and `RotAcc` of the rounded words
  of a decoded value (`GateOptimalBinary.facTw`, `GateOptimalBinary.thW`,
  `GateOptimalBinary.phW`);
* **`rotWordArith_exists`**, **`sgWordArith_exists`**, **`clipWordArith_exists`**: the arithmetic
  of `comp_rotArith`, `comp_signedArithV` and `comp_clipArithV` at every accuracy and for every
  decoder, with explicit word lengths, `2b` or `2b + 1` work wires and the table lengths;
* `bitsFor_le`: the word lengths, `bitsFor c e ≤ n + p log₂(1/ξ) + 1` for `c/e ≤ 2^n (1/ξ)^p`;
  `table_cost_le`: the gates and work wires of the tables in the form of the assumptions.

The tables have `2^|I|` patterns, so the polynomial gate bound of the assumptions is not met by
them: `ManuscriptConformance.comp_rotArith_tables` and its companions state the assumptions with
the constants `c_A = 2^{2b+8} (b + 1)`, exponential in `b`, and `d_A = 1`.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GeneralDecoder

noncomputable section
open SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative SparseHamiltonian.GateBinary
  GateOptimalPrecision
open GateOptimalBinary (tableC tableC_elem tableC_classical tableC_compute tableC_length facTw phW
  thW fac_acc th_acc ph_acc bitsFor div_pow_le card_VW card_FIn card_CIn clipBT clipBP)

/-! ### The table arithmetic -/

section Table

variable {I : Type*} [Fintype I] [DecidableEq I] {bT bP A : ℕ}

/-- **The lookup-table word arithmetic** of the word functions `tw` and `pw` on the input wires
`I`, with `A ≥ |I| - 1` work wires (`GateOptimalBinary.tableC`). -/
def WordArith.table (hA : Fintype.card I ≤ A + 1) (tw : Cfg I → Fin bT → Bool)
    (pw : Cfg I → Fin bP → Bool) : WordArith I bT bP A where
  circ := tableC (A := A) (fun w => Sum.elim (tw w) (pw w))
  tw := tw
  pw := pw
  elem := tableC_elem _
  classical := tableC_classical hA _
  compute w := tableC_compute hA _ w

/-- The length of the table: at most `2^|I| (b_T + b_P)(2|I| + 1)` gates. -/
theorem WordArith.table_length (hA : Fintype.card I ≤ A + 1) (tw : Cfg I → Fin bT → Bool)
    (pw : Cfg I → Fin bP → Bool) :
    (WordArith.table hA tw pw).circ.length ≤
      2 ^ Fintype.card I * (bT + bP) * (2 * Fintype.card I + 1) :=
  tableC_length _

end Table

/-! ### The accuracy of the rounded words -/

/-- **The factor accuracy of the rounded words** of a decoded value of modulus at most one, with
`π/2^{b_T} ≤ ξ²` and `2π/2^{b_P} ≤ ξ`. -/
theorem factorAcc_table {I : Type*} (dec : Cfg I → ℂ) (hdec : ∀ w, ‖dec w‖ ≤ 1) {ξ : ℝ}
    (hξ : 0 < ξ) {bT bP : ℕ} (hT : Real.pi / 2 ^ bT ≤ ξ ^ 2) (hP : 2 * Real.pi / 2 ^ bP ≤ ξ) :
    FactorAcc dec ξ (fun w => facTw ξ bT (dec w)) (fun w => phW bP (dec w)) :=
  fun w => fac_acc hξ hT hP _ (hdec w)

/-- **The rotation accuracy of the rounded words** of a decoded value, with `π/2^{b_T} ≤ ζ` and
`2π/2^{b_P} ≤ ζ`. -/
theorem rotAcc_table {I : Type*} (dec : Cfg I → ℂ) {ζ : ℝ} {bT bP : ℕ}
    (hT : Real.pi / 2 ^ bT ≤ ζ) (hP : 2 * Real.pi / 2 ^ bP ≤ ζ) :
    RotAcc dec ζ (fun w => thW bT (dec w)) (fun w => phW bP (dec w)) :=
  ⟨fun _ => th_acc hT _, fun _ _ => ph_acc hP _⟩

/-! ### The arithmetic of a general decoder -/

section Exists

variable {b : ℕ}

/-- **The rotation arithmetic of every decoder can be met** at every accuracy `ζ > 0` (the
arithmetic of `comp_rotArith`): the table of the rounded words of `2 arctan |dec w|` and
`arg (dec w)`, on `2b` work wires. -/
theorem rotWordArith_exists (dec : Cfg (VW b) → ℂ) {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ ar : RotWordArith b dec ζ (bitsFor Real.pi ζ) (bitsFor (2 * Real.pi) ζ) (2 * b),
      ar.circ.length ≤ 2 ^ (2 * b) * (bitsFor Real.pi ζ + bitsFor (2 * Real.pi) ζ) *
        (4 * b + 1) := by
  have hA : Fintype.card (VW b) ≤ 2 * b + 1 := by rw [card_VW]; omega
  have hT : Real.pi / 2 ^ bitsFor Real.pi ζ ≤ ζ := div_pow_le hζ le_rfl
  have hP : 2 * Real.pi / 2 ^ bitsFor (2 * Real.pi) ζ ≤ ζ := div_pow_le hζ le_rfl
  refine ⟨⟨tableC (A := 2 * b) (fun w => Sum.elim (thW (bitsFor Real.pi ζ) (dec w))
      (phW (bitsFor (2 * Real.pi) ζ) (dec w))),
    fun w => thW _ (dec w), fun w => phW _ (dec w), tableC_elem _, tableC_classical hA _,
    fun w => tableC_compute hA _ w, fun _ => th_acc hT _, fun _ _ => ph_acc hP _⟩, ?_⟩
  have h := tableC_length (I := VW b) (A := 2 * b)
    (fun w => Sum.elim (thW (bitsFor Real.pi ζ) (dec w)) (phW (bitsFor (2 * Real.pi) ζ) (dec w)))
  rw [card_VW] at h
  calc _ ≤ _ := h
    _ = _ := by ring

/-- **The factor arithmetic of the signed-factor regime can be met for every decoder** at every
accuracy `ξ > 0` (the arithmetic of `comp_signedArithV`): the table of the rounded words of
`clip(val w/μ)`, on `2b` work wires. -/
theorem sgWordArith_exists (val : Cfg (VW b) → ℂ) (μ : ℝ) {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ ar : WordArith (VW b) (bitsFor Real.pi (ξ ^ 2)) (bitsFor (2 * Real.pi) ξ) (2 * b),
      FactorAcc (sgVal val μ) ξ ar.tw ar.pw ∧
      ar.circ.length ≤ 2 ^ (2 * b) * (bitsFor Real.pi (ξ ^ 2) + bitsFor (2 * Real.pi) ξ) *
        (4 * b + 1) := by
  have hA : Fintype.card (VW b) ≤ 2 * b + 1 := by rw [card_VW]; omega
  refine ⟨WordArith.table hA (fun w => facTw ξ _ (sgVal val μ w)) (fun w => phW _ (sgVal val μ w)),
    factorAcc_table (sgVal val μ) (fun _ => NativeSignedFactor.norm_clip_le _) hξ
      (div_pow_le (by positivity) le_rfl) (div_pow_le hξ le_rfl), ?_⟩
  have h := WordArith.table_length hA
    (fun w => facTw ξ (bitsFor Real.pi (ξ ^ 2)) (sgVal val μ w))
    (fun w => phW (bitsFor (2 * Real.pi) ξ) (sgVal val μ w))
  rw [card_VW] at h
  calc _ ≤ _ := h
    _ = _ := by ring

theorem norm_cfVal_le (val : Cfg (VW b) → ℂ) (μ β : ℝ) (w : Cfg (Unit ⊕ VW b)) :
    ‖cfVal val μ β w‖ ≤ 1 := by
  unfold cfVal
  split_ifs
  · exact LargeSparsityCore.Native.norm_ccorr_le_one _
  · simp

/-- **The factor and angle arithmetic of the clipped regime can be met for every decoder** at
every accuracy `ξ > 0`, on common work wires (the arithmetic of `comp_clipArithV`): the tables of
the rounded words of `[g] c₂(val w)` and of `y(g, f, c₁(val w), c₂(val w))`, on `2b + 1` work
wires. -/
theorem clipWordArith_exists (val : Cfg (VW b) → ℂ) (μ β q : ℝ) {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ (af : WordArith (Unit ⊕ VW b) (clipBT ξ ξ) (clipBP ξ ξ) (2 * b + 1))
      (aa : WordArith ((Unit ⊕ Unit) ⊕ VW b) (clipBT ξ ξ) (clipBP ξ ξ) (2 * b + 1)),
      FactorAcc (cfVal val μ β) ξ af.tw af.pw ∧ RotAcc (ckVal val μ β q) ξ aa.tw aa.pw ∧
      af.circ.length ≤ 2 ^ (2 * b + 1) * (clipBT ξ ξ + clipBP ξ ξ) * (4 * b + 3) ∧
      aa.circ.length ≤ 2 ^ (2 * b + 2) * (clipBT ξ ξ + clipBP ξ ξ) * (4 * b + 5) := by
  have hA1 : Fintype.card (Unit ⊕ VW b) ≤ 2 * b + 1 + 1 := by rw [card_FIn]; omega
  have hA2 : Fintype.card ((Unit ⊕ Unit) ⊕ VW b) ≤ 2 * b + 1 + 1 := by rw [card_CIn]
  have hT1 : Real.pi / 2 ^ clipBT ξ ξ ≤ ξ ^ 2 := div_pow_le (by positivity) (le_max_left _ _)
  have hP1 : 2 * Real.pi / 2 ^ clipBP ξ ξ ≤ ξ := div_pow_le hξ (le_max_left _ _)
  have hT2 : Real.pi / 2 ^ clipBT ξ ξ ≤ ξ := div_pow_le hξ (le_max_right _ _)
  refine ⟨WordArith.table hA1 (fun w => facTw ξ _ (cfVal val μ β w))
      (fun w => phW _ (cfVal val μ β w)),
    WordArith.table hA2 (fun w => thW _ (ckVal val μ β q w)) (fun w => phW _ (ckVal val μ β q w)),
    factorAcc_table (cfVal val μ β) (norm_cfVal_le val μ β) hξ hT1 hP1,
    rotAcc_table (ckVal val μ β q) hT2 hP1, ?_, ?_⟩
  · have h := WordArith.table_length hA1 (fun w => facTw ξ (clipBT ξ ξ) (cfVal val μ β w))
      (fun w => phW (clipBP ξ ξ) (cfVal val μ β w))
    rw [card_FIn] at h
    calc _ ≤ _ := h
      _ = _ := by ring
  · have h := WordArith.table_length hA2 (fun w => thW (clipBT ξ ξ) (ckVal val μ β q w))
      (fun w => phW (clipBP ξ ξ) (ckVal val μ β q w))
    rw [card_CIn] at h
    calc _ ≤ _ := h
      _ = _ := by ring

end Exists

/-! ### Word lengths and costs -/

/-- **The word lengths of the tables**: `bitsFor c e ≤ n + p log₂(1/ξ) + 1` for
`c/e ≤ 2^n (1/ξ)^p`, `0 < ξ ≤ 1`. -/
theorem bitsFor_le {c e ξ : ℝ} (n p : ℕ) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1)
    (h : c / e ≤ 2 ^ n * (1 / ξ) ^ p) :
    (bitsFor c e : ℝ) ≤ n + p * Real.logb 2 (1 / ξ) + 1 := by
  have hX : 1 ≤ 1 / ξ := by rw [le_div_iff₀ hξ]; linarith
  exact GateBitBudget.clog_le_mul_pow (c / e) (2 ^ n) (1 / ξ) n p hX le_rfl h

/-- The angle and phase words of the tables at accuracy `ξ ∈ (0, 1]`: `bitsFor π ξ ≤ L + 3`,
`bitsFor π ξ² ≤ 2L + 3` and `bitsFor 2π ξ ≤ L + 4`, `L = log₂(1/ξ)`. -/
theorem bitsFor_words {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) :
    (bitsFor Real.pi ξ : ℝ) ≤ Real.logb 2 (1 / ξ) + 3 ∧
    (bitsFor Real.pi (ξ ^ 2) : ℝ) ≤ 2 * Real.logb 2 (1 / ξ) + 3 ∧
    (bitsFor (2 * Real.pi) ξ : ℝ) ≤ Real.logb 2 (1 / ξ) + 4 := by
  have hpi := Real.pi_le_four
  refine ⟨?_, ?_, ?_⟩
  · have e : (2 : ℝ) ^ 2 * (1 / ξ) ^ 1 = 4 / ξ := by ring
    have h := bitsFor_le (c := Real.pi) (e := ξ) 2 1 hξ hξ1
      (by rw [e]; exact div_le_div_of_nonneg_right (by linarith) hξ.le)
    push_cast at h
    linarith
  · have e : (2 : ℝ) ^ 2 * (1 / ξ) ^ 2 = 4 / ξ ^ 2 := by ring
    have h := bitsFor_le (c := Real.pi) (e := ξ ^ 2) 2 2 hξ hξ1
      (by rw [e]; exact div_le_div_of_nonneg_right (by linarith) (by positivity))
    push_cast at h
    linarith
  · have e : (2 : ℝ) ^ 3 * (1 / ξ) ^ 1 = 8 / ξ := by ring
    have h := bitsFor_le (c := 2 * Real.pi) (e := ξ) 3 1 hξ hξ1
      (by rw [e]; exact div_le_div_of_nonneg_right (by linarith) hξ.le)
    push_cast at h
    linarith

/-- **The cost of the tables in the form of the assumptions**: a count
`x ≤ P T (24b + 26) + T + 2b + 1` with `P ≥ 1`, `T ≤ 7M` and `1 ≤ M ≤ w` is at most
`256 P (b + 1) w`. -/
theorem table_cost_le {P T M w x : ℝ} (b : ℕ) (hP : 1 ≤ P) (hM : 1 ≤ M) (hw : M ≤ w)
    (hT : T ≤ 7 * M) (hx : x ≤ P * T * (24 * b + 26) + T + 2 * b + 1) :
    x ≤ 256 * P * (b + 1) * w := by
  have hb : (0 : ℝ) ≤ b := Nat.cast_nonneg _
  have hP0 : 0 ≤ P := by linarith
  have hM0 : 0 ≤ M := by linarith
  have hPM : 1 ≤ P * M := one_le_mul_of_one_le_of_one_le hP hM
  have h1 : P * T * (24 * b + 26) ≤ P * (7 * M) * (24 * b + 26) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hT hP0) (by positivity)
  have h2 : T ≤ 7 * (P * M) := hT.trans (by nlinarith)
  have h3 : 2 * (b : ℝ) + 1 ≤ (2 * b + 1) * (P * M) := le_mul_of_one_le_right (by positivity) hPM
  have h4 : P * M ≤ P * w := mul_le_mul_of_nonneg_left hw hP0
  calc x ≤ P * T * (24 * b + 26) + T + 2 * b + 1 := hx
    _ ≤ P * (7 * M) * (24 * b + 26) + 7 * (P * M) + (2 * b + 1) * (P * M) := by linarith
    _ = P * M * (170 * b + 190) := by ring
    _ ≤ P * M * (256 * (b + 1)) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ ≤ P * w * (256 * (b + 1)) := mul_le_mul_of_nonneg_right h4 (by positivity)
    _ = 256 * P * (b + 1) * w := by ring

end

end SparseHamiltonian.GeneralDecoder
