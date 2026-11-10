import GeneralSparseAccess.ImplOK
import GateEfficientBinary.Sparse.Boundary

/-!
# The padded data in the sizes of the binary format

The padded data `QData.padData` of general sparse data `D` (an `N × N` matrix with `s`-sparse lists
on `k`-bit index words) have the sizes of the binary format of the package's gate endpoints on
`k + 1`-bit index words; the decoder of `D` is kept, so they are in the binary format when the
words are decoded as `c₀(X + iY)` (`ManuscriptConformance.padFormat`):

* its slots are the low words of `⌈log₂ s⌉` bits (`pslot_range`);
* its matrix is the matrix of `D` on the valid index words (marker `0`, low word below `N`) and
  zero elsewhere (`padData_matrix`), equivalently the padded matrix `D.padMat` on the words with a
  clear marker (`padData_matrix_mark`);
* it inherits the promises of the matrix: Hermiticity (`padData_isHermitian`), the row and column
  Euclidean norm bounds (`padData_row_le`, `padData_col_le`) and the entry bound
  (`padData_entry_le`).

`exp_comp_of_comp`: an intertwining `A ∘ L = L ∘ B` passes to the exponentials, and
`qlift_refl_matrixOperator`: the qubit lift of a matrix along the identity encoding is its
configuration operator.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GeneralSparseAccess

noncomputable section
open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
  SparseHamiltonian.GateBinary
open SparseHamiltonian.OracleCircuit
open SparseHamiltonian.GatePointerEncoding (wordValue wordValue_lt_pow)
open NativeSparseBlockEncoding (Query)
open scoped InnerProduct Nat

/-! ### The slots -/

section Range

variable {k : ℕ}

theorem testBit_wordValue (d : Cfg (Fin k)) (i : Fin k) : (wordValue d).testBit i.val = d i :=
  congrFun (binW_wordValue d) i

/-- A word whose bits from position `σ` on are clear has value below `2^σ`. -/
theorem wordValue_lt_of_high {σ : ℕ} (d : Cfg (Fin k))
    (h : ∀ i : Fin k, σ ≤ i.val → d i = false) : wordValue d < 2 ^ σ := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  by_cases hik : i < k
  · rw [testBit_wordValue d ⟨i, hik⟩]
    exact h ⟨i, hik⟩ hi
  · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le (wordValue_lt_pow d)
      (Nat.pow_le_pow_right (by norm_num) (by omega)))

/-- **The padded slots are the low words of `⌈log₂ s⌉` bits.** -/
theorem pslot_range {s : ℕ} (hs : s ≤ 2 ^ k) (j : Cfg (Fin (k + 1))) :
    (∃ m : Fin (sP s), pslot k m = j) ↔ ∃ u : Fin (sbP s) → Bool, j = lowWord (sbP s) u := by
  rw [exists_lowWord_iff]
  have hσ := sbP_le hs
  constructor
  · rintro ⟨m, rfl⟩ i hi
    show (if h : i.val < k then binW k m ⟨i.val, h⟩ else false) = false
    split_ifs with h
    · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le m.isLt (Nat.pow_le_pow_right (by norm_num) hi))
    · rfl
  · intro h
    have hm : mark j = false := h (Fin.last k) (by simp only [Fin.val_last]; omega)
    have hlo : ∀ i : Fin k, sbP s ≤ i.val → lo j i = false := fun i hi => h (Fin.castSucc i) hi
    refine ⟨⟨wordValue (lo j), wordValue_lt_of_high (lo j) hlo⟩, ?_⟩
    show idx false (binW k (wordValue (lo j))) = j
    rw [binW_wordValue, ← hm, idx_mark_lo]

end Range

/-! ### Sums over the valid index words -/

section Sums

variable {N k : ℕ}

/-- The valid index word of an index. -/
def penc (k : ℕ) {N : ℕ} (i : Fin N) : Cfg (Fin (k + 1)) := idx false (binW k i)

/-- **A sum over the valid index words is a sum over the indices.** -/
theorem sum_pvalid {M : Type*} [AddCommMonoid M] (hN : N ≤ 2 ^ k) (F : Fin N → M) :
    ∑ y : Cfg (Fin (k + 1)), (if h : PValid N y then F (pdec h) else 0) = ∑ i, F i := by
  have hinj : ∀ i ∈ (Finset.univ : Finset (Fin N)), ∀ i' ∈ (Finset.univ : Finset (Fin N)),
      penc k i = penc k i' → i = i' := by
    intro i _ i' _ h
    have h2 := (idx_injective h).2
    exact Fin.ext (binW_inj (lt_of_lt_of_le i.isLt hN) (lt_of_lt_of_le i'.isLt hN) h2)
  have hG : ∀ i : Fin N, (if h : PValid N (penc k i) then F (pdec h) else 0) = F i := by
    intro i
    have hp : PValid N (penc k i) := pvalid_idx hN i
    rw [dif_pos hp]
    exact congrArg F (pdec_idx hN i)
  calc ∑ y : Cfg (Fin (k + 1)), (if h : PValid N y then F (pdec h) else 0)
      = ∑ y ∈ Finset.univ.image (penc k), (if h : PValid N y then F (pdec h) else 0) := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro y _ hy
        rw [dif_neg]
        intro h
        apply hy
        exact Finset.mem_image.mpr ⟨pdec h, Finset.mem_univ _, idx_binW_pdec h⟩
    _ = ∑ i, (if h : PValid N (penc k i) then F (pdec h) else 0) := Finset.sum_image hinj
    _ = ∑ i, F i := Finset.sum_congr rfl (fun i _ => hG i)

end Sums

/-! ### The padded matrix -/

namespace QData

variable {X : Type*} {N s k b : ℕ} (D : QData X N s k b)

/-- **The matrix of the padded data**: the matrix on valid index words, zero elsewhere. -/
theorem padData_matrix (z₀ : Cfg (VW b)) (hz₀ : D.val z₀ = 0) (x : X)
    (y y' : Cfg (Fin (k + 1))) :
    (D.padData z₀ hz₀).matrix x y y' =
      if h : PValid N y ∧ PValid N y' then D.matrix x (pdec h.1) (pdec h.2) else 0 := by
  show D.val (if PValid N y ∧ PValid N y' then D.table x (edgeW k (lo y) (lo y')) else z₀) = _
  by_cases h : PValid N y ∧ PValid N y'
  · rw [if_pos h, dif_pos h, ← binW_pdec h.1, ← binW_pdec h.2]
    exact D.decoded x _ _
  · rw [if_neg h, dif_neg h]
    exact hz₀

/-- The matrix of the padded data is the padded matrix on the words with a clear marker. -/
theorem padData_matrix_mark (z₀ : Cfg (VW b)) (hz₀ : D.val z₀ = 0) (x : X)
    (y y' : Cfg (Fin (k + 1))) :
    (D.padData z₀ hz₀).matrix x y y' =
      if mark y = false ∧ mark y' = false then D.padMat x (lo y) (lo y') else 0 := by
  rw [padData_matrix]
  by_cases hm : mark y = false ∧ mark y' = false
  · rw [if_pos hm]
    unfold padMat
    by_cases hw : wordValue (lo y) < N ∧ wordValue (lo y') < N
    · rw [dif_pos ⟨⟨hm.1, hw.1⟩, ⟨hm.2, hw.2⟩⟩, dif_pos hw]
      rfl
    · rw [dif_neg (fun h => hw ⟨h.1.2, h.2.2⟩), dif_neg hw]
  · rw [if_neg hm, dif_neg (fun h => hm ⟨h.1.1, h.2.1⟩)]

/-- **The padded matrix is Hermitian** when the matrix is. -/
theorem padData_isHermitian (z₀ : Cfg (VW b)) (hz₀ : D.val z₀ = 0) (x : X)
    (h : (D.matrix x).IsHermitian) : ((D.padData z₀ hz₀).matrix x).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro y y'
  rw [padData_matrix, padData_matrix]
  by_cases hv : PValid N y ∧ PValid N y'
  · rw [dif_pos ⟨hv.2, hv.1⟩, dif_pos hv]
    exact h.apply (pdec hv.1) (pdec hv.2)
  · rw [dif_neg (fun h' => hv ⟨h'.2, h'.1⟩), dif_neg hv, star_zero]

/-- **The row norm bound of the padded matrix.** -/
theorem padData_row_le (z₀ : Cfg (VW b)) (hz₀ : D.val z₀ = 0) (x : X) {η : ℝ}
    (h : ∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) (y : Cfg (Fin (k + 1))) :
    ∑ y', ‖(D.padData z₀ hz₀).matrix x y y'‖ ^ 2 ≤ η ^ 2 := by
  simp only [padData_matrix]
  by_cases hy : PValid N y
  · have e : ∀ y' : Cfg (Fin (k + 1)),
        ‖(if h : PValid N y ∧ PValid N y' then D.matrix x (pdec h.1) (pdec h.2) else 0)‖ ^ 2 =
          if h : PValid N y' then ‖D.matrix x (pdec hy) (pdec h)‖ ^ 2 else 0 := by
      intro y'
      by_cases hy' : PValid N y'
      · rw [dif_pos ⟨hy, hy'⟩, dif_pos hy']
      · rw [dif_neg (fun h' => hy' h'.2), dif_neg hy', norm_zero]
        ring
    rw [Finset.sum_congr rfl (fun y' _ => e y'),
      sum_pvalid D.hN (fun j => ‖D.matrix x (pdec hy) j‖ ^ 2)]
    exact h (pdec hy)
  · have e : ∀ y' : Cfg (Fin (k + 1)),
        ‖(if h : PValid N y ∧ PValid N y' then D.matrix x (pdec h.1) (pdec h.2) else 0)‖ ^ 2 =
          0 := by
      intro y'
      rw [dif_neg (fun h' => hy h'.1), norm_zero]
      ring
    rw [Finset.sum_congr rfl (fun y' _ => e y'), Finset.sum_const_zero]
    positivity

/-- **The column norm bound of the padded matrix.** -/
theorem padData_col_le (z₀ : Cfg (VW b)) (hz₀ : D.val z₀ = 0) (x : X) {η : ℝ}
    (h : ∀ j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) (y' : Cfg (Fin (k + 1))) :
    ∑ y, ‖(D.padData z₀ hz₀).matrix x y y'‖ ^ 2 ≤ η ^ 2 := by
  simp only [padData_matrix]
  by_cases hy' : PValid N y'
  · have e : ∀ y : Cfg (Fin (k + 1)),
        ‖(if h : PValid N y ∧ PValid N y' then D.matrix x (pdec h.1) (pdec h.2) else 0)‖ ^ 2 =
          if h : PValid N y then ‖D.matrix x (pdec h) (pdec hy')‖ ^ 2 else 0 := by
      intro y
      by_cases hy : PValid N y
      · rw [dif_pos ⟨hy, hy'⟩, dif_pos hy]
      · rw [dif_neg (fun h' => hy h'.1), dif_neg hy, norm_zero]
        ring
    rw [Finset.sum_congr rfl (fun y _ => e y),
      sum_pvalid D.hN (fun i => ‖D.matrix x i (pdec hy')‖ ^ 2)]
    exact h (pdec hy')
  · have e : ∀ y : Cfg (Fin (k + 1)),
        ‖(if h : PValid N y ∧ PValid N y' then D.matrix x (pdec h.1) (pdec h.2) else 0)‖ ^ 2 =
          0 := by
      intro y
      rw [dif_neg (fun h' => hy' h'.2), norm_zero]
      ring
    rw [Finset.sum_congr rfl (fun y _ => e y), Finset.sum_const_zero]
    positivity

/-- **The entry bound of the padded matrix.** -/
theorem padData_entry_le (z₀ : Cfg (VW b)) (hz₀ : D.val z₀ = 0) (x : X) {μ : ℝ} (hμ : 0 ≤ μ)
    (h : ∀ i j, ‖D.matrix x i j‖ ≤ μ) (y y' : Cfg (Fin (k + 1))) :
    ‖(D.padData z₀ hz₀).matrix x y y'‖ ≤ μ := by
  rw [padData_matrix]
  split_ifs with hv
  · exact h _ _
  · rw [norm_zero]
    exact hμ

end QData

/-! ### Exponentials and qubit lifts -/

section Exp

/-- **An intertwining passes to the exponentials**: `A ∘ L = L ∘ B` gives
`exp A ∘ L = L ∘ exp B`. -/
theorem exp_comp_of_comp {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (A : E →L[ℂ] E) (B : F →L[ℂ] F) (L : F →L[ℂ] E) (h : A ∘L L = L ∘L B) :
    NormedSpace.exp A ∘L L = L ∘L NormedSpace.exp B := by
  have hpow : ∀ n : ℕ, (A ^ n) ∘L L = L ∘L (B ^ n) := by
    intro n
    induction n with
    | zero =>
        rw [pow_zero, pow_zero]
        exact ContinuousLinearMap.ext fun v => rfl
    | succ n ih =>
        rw [pow_succ, pow_succ, mul_def, mul_def, comp_assoc, h, ← comp_assoc, ih, comp_assoc]
  have h1 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) A).mapL
    ((ContinuousLinearMap.compL ℂ F E E).flip L)
  have h2 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) B).mapL
    (ContinuousLinearMap.compL ℂ F F E L)
  have e : (fun n : ℕ => (ContinuousLinearMap.compL ℂ F E E).flip L (((n ! : ℂ))⁻¹ • A ^ n)) =
      fun n => ContinuousLinearMap.compL ℂ F F E L (((n ! : ℂ))⁻¹ • B ^ n) := by
    funext n
    rw [ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply,
      ContinuousLinearMap.compL_apply, smul_comp, comp_smul, hpow n]
  rw [e] at h1
  have := h1.unique h2
  rwa [ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.compL_apply] at this

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- The configuration matrix of a matrix operator along the identity encoding is the matrix. -/
theorem toMat_refl_matrixOperator (M : Matrix (Cfg V) (Cfg V) ℂ) :
    toMat (Equiv.refl (Cfg V)) (SparseStateOverlap.matrixOperator M) = M := by
  funext c c'
  change SparseStateOverlap.matrixOperator M (EuclideanSpace.single c' 1) c = M c c'
  rw [SparseStateOverlap.matrixOperator_apply, Finset.sum_eq_single c']
  · simp
  · intro j _ hj
    simp [hj]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **The qubit lift of a matrix along the identity encoding is its configuration operator.** -/
theorem qlift_refl_matrixOperator (M : Matrix (Cfg V) (Cfg V) ℂ) :
    qlift (R := R) (Equiv.refl (Cfg V)) (SparseStateOverlap.matrixOperator M) = matOp M := by
  rw [qlift_eq, toMat_refl_matrixOperator]

end Exp

end

end SparseHamiltonian.GeneralSparseAccess
