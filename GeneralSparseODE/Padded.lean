import GeneralSparseODE.Embed
import SparseODE.ODEMatrixEnergy
import GateEfficientBinaryODE.Solver

/-!
# The padded instance of a dissipative problem

For the sparse data of general size `D : GeneralSparseAccess.QData X N s k b` and a public word
`z₀` with `val z₀ = 0`, the padded data `D.padData z₀ hz₀` (`k + 1`-bit index words, `2^⌈log₂ s⌉`
slots) carry the matrix of `D` on the valid index words and zero elsewhere (`zpad`). The hypotheses
of the dissipative solvers transfer from the matrix of `D` to the padded matrix:

* `hamiltonianPart_zpad`, `dissipativePart_zpad`: the Hamiltonian and dissipative parts of the
  padded matrix are the padded parts;
* `zpad_row_le`, `zpad_col_le`: the row and column energy bounds;
* `zpad_accretive`: the accretivity of the dissipative part;
* `mLift_padData`: the qubit lift of the padded matrix is the zero extension `zext` of the lift
  `padLift D x` of the matrix extended by zero to the `2^k` index words (`QData.padMat`), so the
  padded generator is the zero extension of the generator on the index register;
* `padData_range`, `padData_decode`: the binary slot range and the decoder of the padded data.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GeneralSparseODE

noncomputable section
open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
  SparseHamiltonian.GateBinary
open SparseHamiltonian.GeneralSparseAccess
open SparseHamiltonian.OracleCircuit
open scoped InnerProduct ComplexConjugate

/-! ### Matrices extended by zero to the padded index words -/

section Zpad

variable {N k : ℕ}

/-- **The matrix extended by zero** to the `k + 1`-bit index words: the matrix on the valid words
(`GeneralSparseAccess.PValid`), zero elsewhere. -/
def zpad (N k : ℕ) (M : Matrix (Fin N) (Fin N) ℂ) :
    Matrix (Cfg (Fin (k + 1))) (Cfg (Fin (k + 1))) ℂ :=
  fun y y' => if h : PValid N y ∧ PValid N y' then M (pdec h.1) (pdec h.2) else 0

theorem hamiltonianPart_zpad (M : Matrix (Fin N) (Fin N) ℂ) :
    ODEMatrixEnergy.hamiltonianPart (zpad N k M) =
      zpad N k (ODEMatrixEnergy.hamiltonianPart M) := by
  funext y y'
  simp only [ODEMatrixEnergy.hamiltonianPart_apply, zpad]
  by_cases h : PValid N y ∧ PValid N y'
  · rw [dif_pos h, dif_pos ⟨h.2, h.1⟩, dif_pos h]
  · rw [dif_neg h, dif_neg (fun h' => h ⟨h'.2, h'.1⟩), dif_neg h]
    simp

theorem dissipativePart_zpad (M : Matrix (Fin N) (Fin N) ℂ) :
    ODEMatrixEnergy.dissipativePart (zpad N k M) =
      zpad N k (ODEMatrixEnergy.dissipativePart M) := by
  funext y y'
  simp only [ODEMatrixEnergy.dissipativePart_apply, zpad]
  by_cases h : PValid N y ∧ PValid N y'
  · rw [dif_pos h, dif_pos ⟨h.2, h.1⟩, dif_pos h]
  · rw [dif_neg h, dif_neg (fun h' => h ⟨h'.2, h'.1⟩), dif_neg h]
    simp

/-- **The row energy bound of the padded matrix.** -/
theorem zpad_row_le (hN : N ≤ 2 ^ k) (M : Matrix (Fin N) (Fin N) ℂ) {η : ℝ}
    (h : ∀ i, ∑ j, ‖M i j‖ ^ 2 ≤ η ^ 2) (y : Cfg (Fin (k + 1))) :
    ∑ y', ‖zpad N k M y y'‖ ^ 2 ≤ η ^ 2 := by
  simp only [zpad]
  by_cases hy : PValid N y
  · have e : ∀ y' : Cfg (Fin (k + 1)),
        ‖(if h : PValid N y ∧ PValid N y' then M (pdec h.1) (pdec h.2) else 0)‖ ^ 2 =
          if h : PValid N y' then ‖M (pdec hy) (pdec h)‖ ^ 2 else 0 := by
      intro y'
      by_cases hy' : PValid N y'
      · rw [dif_pos ⟨hy, hy'⟩, dif_pos hy']
      · rw [dif_neg (fun h' => hy' h'.2), dif_neg hy', norm_zero]
        ring
    rw [Finset.sum_congr rfl (fun y' _ => e y'), sum_pvalid hN (fun j => ‖M (pdec hy) j‖ ^ 2)]
    exact h (pdec hy)
  · have e : ∀ y' : Cfg (Fin (k + 1)),
        ‖(if h : PValid N y ∧ PValid N y' then M (pdec h.1) (pdec h.2) else 0)‖ ^ 2 = 0 := by
      intro y'
      rw [dif_neg (fun h' => hy h'.1), norm_zero]
      ring
    rw [Finset.sum_congr rfl (fun y' _ => e y'), Finset.sum_const_zero]
    positivity

/-- **The column energy bound of the padded matrix.** -/
theorem zpad_col_le (hN : N ≤ 2 ^ k) (M : Matrix (Fin N) (Fin N) ℂ) {η : ℝ}
    (h : ∀ j, ∑ i, ‖M i j‖ ^ 2 ≤ η ^ 2) (y' : Cfg (Fin (k + 1))) :
    ∑ y, ‖zpad N k M y y'‖ ^ 2 ≤ η ^ 2 := by
  simp only [zpad]
  by_cases hy' : PValid N y'
  · have e : ∀ y : Cfg (Fin (k + 1)),
        ‖(if h : PValid N y ∧ PValid N y' then M (pdec h.1) (pdec h.2) else 0)‖ ^ 2 =
          if h : PValid N y then ‖M (pdec h) (pdec hy')‖ ^ 2 else 0 := by
      intro y
      by_cases hy : PValid N y
      · rw [dif_pos ⟨hy, hy'⟩, dif_pos hy]
      · rw [dif_neg (fun h' => hy h'.1), dif_neg hy, norm_zero]
        ring
    rw [Finset.sum_congr rfl (fun y _ => e y), sum_pvalid hN (fun i => ‖M i (pdec hy')‖ ^ 2)]
    exact h (pdec hy')
  · have e : ∀ y : Cfg (Fin (k + 1)),
        ‖(if h : PValid N y ∧ PValid N y' then M (pdec h.1) (pdec h.2) else 0)‖ ^ 2 = 0 := by
      intro y
      rw [dif_neg (fun h' => hy' h'.2), norm_zero]
      ring
    rw [Finset.sum_congr rfl (fun y _ => e y), Finset.sum_const_zero]
    positivity

/-- **The accretivity of the padded matrix**: the quadratic form of the padded matrix at `w` is that
of the matrix at the values of `w` on the valid index words. -/
theorem zpad_accretive (hN : N ≤ 2 ^ k) (K : Matrix (Fin N) (Fin N) ℂ)
    (h : ∀ w : EuclideanSpace ℂ (Fin N),
      0 ≤ (inner ℂ w (SparseStateOverlap.matrixOperator K w)).re)
    (w : EuclideanSpace ℂ (Cfg (Fin (k + 1)))) :
    0 ≤ (inner ℂ w (SparseStateOverlap.matrixOperator (zpad N k K) w)).re := by
  set w' : EuclideanSpace ℂ (Fin N) := WithLp.toLp 2 (fun i => w (penc k i)) with hw'
  have hval : ∀ {y : Cfg (Fin (k + 1))} (hy : PValid N y), w y = w' (pdec hy) := by
    intro y hy
    show w y = w (idx false (binW k (pdec hy)))
    rw [idx_binW_pdec hy]
  have hinner : inner ℂ w (SparseStateOverlap.matrixOperator (zpad N k K) w) =
      inner ℂ w' (SparseStateOverlap.matrixOperator K w') := by
    rw [PiLp.inner_apply, PiLp.inner_apply]
    have e : ∀ y : Cfg (Fin (k + 1)),
        inner ℂ (w y) (SparseStateOverlap.matrixOperator (zpad N k K) w y) =
          if hy : PValid N y then
            inner ℂ (w' (pdec hy)) (SparseStateOverlap.matrixOperator K w' (pdec hy)) else 0 := by
      intro y
      rw [SparseStateOverlap.matrixOperator_apply]
      by_cases hy : PValid N y
      · rw [dif_pos hy, SparseStateOverlap.matrixOperator_apply, hval hy]
        congr 1
        have e2 : ∀ y' : Cfg (Fin (k + 1)), zpad N k K y y' * w y' =
            if hy' : PValid N y' then K (pdec hy) (pdec hy') * w' (pdec hy') else 0 := by
          intro y'
          simp only [zpad]
          by_cases hy' : PValid N y'
          · rw [dif_pos ⟨hy, hy'⟩, dif_pos hy', hval hy']
          · rw [dif_neg (fun h' => hy' h'.2), dif_neg hy', zero_mul]
        rw [Finset.sum_congr rfl (fun y' _ => e2 y'), sum_pvalid hN (fun j => K (pdec hy) j * w' j)]
      · rw [dif_neg hy]
        have e2 : ∀ y' : Cfg (Fin (k + 1)), zpad N k K y y' * w y' = 0 := by
          intro y'
          simp only [zpad]
          rw [dif_neg (fun h' => hy h'.1), zero_mul]
        rw [Finset.sum_congr rfl (fun y' _ => e2 y'), Finset.sum_const_zero, inner_zero_right]
    rw [Finset.sum_congr rfl (fun y _ => e y),
      sum_pvalid hN (fun i => inner ℂ (w' i) (SparseStateOverlap.matrixOperator K w' i))]
  rw [hinner]
  exact h w'

end Zpad

/-! ### The padded data -/

section PadData

variable {X : Type*} {N s k b : ℕ} (D : QData X N s k b) (z₀ : Cfg (VW b)) (hz₀ : D.val z₀ = 0)

theorem padData_zpad (x : X) : (D.padData z₀ hz₀).matrix x = zpad N k (D.matrix x) := by
  funext y y'
  rw [QData.padData_matrix]
  rfl

/-- **The lift of the matrix extended by zero** to the `2^k` index words (`QData.padMat`) on the
index register. -/
def padLift (x : X) : Reg (Fin k) ℂ →L[ℂ] Reg (Fin k) ℂ :=
  qlift (Equiv.refl _) (SparseStateOverlap.matrixOperator (D.padMat x))

/-- **The lift of the padded matrix is the zero extension of the lift of the matrix extended by
zero.** -/
theorem mLift_padData (x : X) :
    GateBinaryODE.mLift (D.padData z₀ hz₀) (Equiv.refl _) x = zext (padLift D x) := by
  unfold GateBinaryODE.mLift padLift
  rw [qlift_refl_matrixOperator, qlift_refl_matrixOperator]
  refine ContinuousLinearMap.ext fun ψ => PiLp.ext fun y => ?_
  rw [zext, comp_apply, comp_apply, markEmb_apply, matOp_apply]
  simp only [QData.padData_matrix_mark]
  by_cases hy : mark y = false
  · rw [if_pos hy, matOp_apply, ← sum_mark_false (fun d => D.padMat x (lo y) d • lowPart k ψ d)]
    apply Finset.sum_congr rfl
    intro y' _
    by_cases hy' : mark y' = false
    · have hy2 : idx false (lo y') = y' := by
        rw [← hy']
        exact idx_mark_lo y'
      rw [if_pos ⟨hy, hy'⟩, if_pos hy', lowPart_apply, hy2]
    · rw [if_neg (fun h => hy' h.2), if_neg hy', zero_smul]
  · rw [if_neg hy]
    apply Finset.sum_eq_zero
    intro y' _
    rw [if_neg (fun h => hy h.1), zero_smul]

theorem mLift_padData_comp (x : X) :
    GateBinaryODE.mLift (D.padData z₀ hz₀) (Equiv.refl _) x ∘L markEmb k =
      markEmb k ∘L padLift D x := by
  rw [mLift_padData, zext_markEmb]

/-- The slots of the padded data are the index words supported on the low `⌈log₂ s⌉` bits. -/
theorem padData_range (j : Cfg (Fin (k + 1))) :
    (∃ m, (D.padData z₀ hz₀).slot m = j) ↔
      ∃ u : Fin (sbP s) → Bool, j = (Equiv.refl (Cfg (Fin (k + 1)))) (lowWord (sbP s) u) :=
  pslot_range D.s_le_pow j

/-- The decoder of the padded data is the decoder of `D`. -/
theorem padData_decode (e : Cfg (Fin (k + 1)) × Cfg (Fin (k + 1))) (z : Cfg (VW b)) :
    (D.padData z₀ hz₀).decode e z = D.val z := rfl

end PadData

end

end SparseHamiltonian.GeneralSparseODE
