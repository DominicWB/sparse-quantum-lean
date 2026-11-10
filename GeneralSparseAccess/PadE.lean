import GeneralSparseAccess.PadSpec

/-!
# The padded data with a validity decoder

`QData.padData D z₀ hz₀` stores the public zero word `z₀` on the padded entries, so its decoder is
that of `D`; a general decoder need not have a zero word. `QData.padDataE D` stores the supplied
word of the low index words on every pair (`ptableE`) and decodes with the validity of the pair
(`pdecode`: the decoder of `D` on a valid pair, zero otherwise), as the manuscript selects the
zero-entry rotation on an invalid pair "independently of the returned encoding" (Section
`hs:sec:gates`, before Theorem `hs:thm:gates`). Its value oracle is the supplied value oracle on the
low wires; its locators are those of `padData`.

* `padDataE_matrix`: the matrix of `D` on the valid index words and zero elsewhere;
* `PadForm`: a matrix of this form; `PadForm.isHermitian`, `PadForm.row_le`, `PadForm.col_le`,
  `PadForm.entry_le`: the promises of the matrix pass to it.
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
open scoped InnerProduct

namespace QData

variable {X : Type*} {N s k b : ℕ} (D : QData X N s k b)

/-- The stored word of the padded data with a validity decoder: the supplied word of the low index
words on every pair. -/
def ptableE (x : X) (e : Cfg (Fin (k + 1)) × Cfg (Fin (k + 1))) : Cfg (VW b) :=
  D.table x (edgeW k (lo e.1) (lo e.2))

/-- The validity decoder: the decoder of `D` on a pair of valid index words, zero otherwise. -/
def pdecode (e : Cfg (Fin (k + 1)) × Cfg (Fin (k + 1))) (z : Cfg (VW b)) : ℂ :=
  if PValid N e.1 ∧ PValid N e.2 then D.val z else 0

theorem norm_pdecode_le (e : Cfg (Fin (k + 1)) × Cfg (Fin (k + 1))) (z : Cfg (VW b)) :
    ‖D.pdecode e z‖ ≤ D.scale := by
  unfold pdecode
  split_ifs
  · exact D.val_bound z
  · rw [norm_zero]
    exact D.scale_pos.le

theorem pdecode_ptableE (x : X) (y y' : Cfg (Fin (k + 1))) :
    D.pdecode (y, y') (D.ptableE x (y, y')) =
      if h : PValid N y ∧ PValid N y' then D.matrix x (pdec h.1) (pdec h.2) else 0 := by
  unfold pdecode ptableE
  by_cases h : PValid N y ∧ PValid N y'
  · rw [if_pos h, dif_pos h]
    show D.val (D.table x (edgeW k (lo y) (lo y'))) = _
    rw [← binW_pdec h.1, ← binW_pdec h.2]
    exact D.decoded x _ _
  · rw [if_neg h, dif_neg h]

/-- **The padded data with a validity decoder** (native sparse data on `k + 1`-bit index words with
`s' = 2^⌈log₂ s⌉` slots): the supplied word of the low index words on every pair, the validity
decoder, the padded lists and the padded locators of `padData`. -/
def padDataE : NativeSparseBlockEncoding.Data X (Cfg (Fin (k + 1))) (Cfg (VW b)) (sP s) where
  slot := ⟨pslot k, pslot_injective D.s_le_pow⟩
  slots_pos := sP_pos s
  scale := D.scale
  scale_pos := D.scale_pos
  matrix x y y' := D.pdecode (y, y') (D.ptableE x (y, y'))
  table x e := D.ptableE x e
  decode := D.pdecode
  decode_bound := D.norm_pdecode_le
  decoded _ _ _ := rfl
  rowloc := D.prowloc
  colloc := D.pcolloc
  row_injective := D.prowloc_injective
  column_injective := D.pcolloc_injective
  row_covers x y y' h := by
    rw [pdecode_ptableE] at h
    split_ifs at h with hv
    · obtain ⟨a, ha⟩ := D.row_covers x _ _ h
      refine Finset.mem_image.mpr ⟨⟨a.val, lt_of_lt_of_le a.isLt (le_sP s)⟩, Finset.mem_univ _, ?_⟩
      change plist (D.rowloc x) y _ = y'
      unfold plist
      rw [dif_pos ⟨hv.1, a.isLt⟩]
      have : (⟨a.val, a.isLt⟩ : Fin s) = a := rfl
      rw [this, ha]
      exact idx_binW_pdec hv.2
    · exact absurd rfl h
  column_covers x y y' h := by
    rw [pdecode_ptableE] at h
    split_ifs at h with hv
    · obtain ⟨a, ha⟩ := D.column_covers x _ _ h
      refine Finset.mem_image.mpr ⟨⟨a.val, lt_of_lt_of_le a.isLt (le_sP s)⟩, Finset.mem_univ _, ?_⟩
      change plist (D.colloc x) y' _ = y
      unfold plist
      rw [dif_pos ⟨hv.2, a.isLt⟩]
      have : (⟨a.val, a.isLt⟩ : Fin s) = a := rfl
      rw [this, ha]
      exact idx_binW_pdec hv.1
    · exact absurd rfl h
  rowOracle x := ofMat (phiE (Equiv.refl _)) (D.rowMat x)
  columnOracle x := ofMat (phiE (Equiv.refl _)) (D.colMat x)
  row_unitary x := ofMat_isUnitary _ (D.rowMat_isUnitary x)
  column_unitary x := ofMat_isUnitary _ (D.colMat_isUnitary x)
  row_valid x y a := by
    change ofMat (phiE (Equiv.refl _)) (D.rowMat x)
        (EuclideanSpace.single (phiE (Equiv.refl _) (edgeW (k + 1) y (pslot k a))) 1) =
      EuclideanSpace.single (phiE (Equiv.refl _) (edgeW (k + 1) y (D.prowloc x y a))) 1
    exact ofMat_single _ _ _ _ (fun bb => D.rowMat_col x y a bb)
  column_valid x y a := by
    change ofMat (phiE (Equiv.refl _)) (D.colMat x)
        (EuclideanSpace.single (phiE (Equiv.refl _) (edgeW (k + 1) y (pslot k a))) 1) =
      EuclideanSpace.single (phiE (Equiv.refl _) (edgeW (k + 1) (D.pcolloc x y a) y)) 1
    exact ofMat_single _ _ _ _ (fun bb => D.colMat_col x y a bb)

/-- **The matrix of the padded data with a validity decoder**: the matrix on valid index words,
zero elsewhere. -/
theorem padDataE_matrix (x : X) (y y' : Cfg (Fin (k + 1))) :
    D.padDataE.matrix x y y' =
      if h : PValid N y ∧ PValid N y' then D.matrix x (pdec h.1) (pdec h.2) else 0 :=
  D.pdecode_ptableE x y y'

theorem padDataE_decode : D.padDataE.decode = D.pdecode := rfl

theorem padDataE_table (x : X) : D.padDataE.table x = D.ptableE x := rfl

theorem padDataE_rowOracle (x : X) :
    D.padDataE.rowOracle x = ofMat (phiE (Equiv.refl _)) (D.rowMat x) := rfl

theorem padDataE_columnOracle (x : X) :
    D.padDataE.columnOracle x = ofMat (phiE (Equiv.refl _)) (D.colMat x) := rfl

end QData

/-! ### Matrices of the padded form -/

section Form

variable {X : Type*} {N s k b : ℕ} (D : QData X N s k b)

/-- **A matrix of the padded form**: the matrix of `D` on the valid index words, zero elsewhere. -/
def PadForm (M : X → Matrix (Cfg (Fin (k + 1))) (Cfg (Fin (k + 1))) ℂ) : Prop :=
  ∀ x y y', M x y y' = if h : PValid N y ∧ PValid N y' then D.matrix x (pdec h.1) (pdec h.2) else 0

theorem padForm_padDataE : PadForm D D.padDataE.matrix := D.padDataE_matrix

variable {D} {M : X → Matrix (Cfg (Fin (k + 1))) (Cfg (Fin (k + 1))) ℂ}

/-- A matrix of the padded form is the padded matrix on the words with a clear marker. -/
theorem PadForm.eq_mark (hM : PadForm D M) (x : X) (y y' : Cfg (Fin (k + 1))) :
    M x y y' = if mark y = false ∧ mark y' = false then D.padMat x (lo y) (lo y') else 0 := by
  rw [hM]
  by_cases hm : mark y = false ∧ mark y' = false
  · rw [if_pos hm]
    unfold QData.padMat
    by_cases hw : wordValue (lo y) < N ∧ wordValue (lo y') < N
    · rw [dif_pos ⟨⟨hm.1, hw.1⟩, ⟨hm.2, hw.2⟩⟩, dif_pos hw]
      rfl
    · rw [dif_neg (fun h => hw ⟨h.1.2, h.2.2⟩), dif_neg hw]
  · rw [if_neg hm, dif_neg (fun h => hm ⟨h.1.1, h.2.1⟩)]

/-- A matrix of the padded form is Hermitian when the matrix is. -/
theorem PadForm.isHermitian (hM : PadForm D M) (x : X) (h : (D.matrix x).IsHermitian) :
    (M x).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro y y'
  rw [hM, hM]
  by_cases hv : PValid N y ∧ PValid N y'
  · rw [dif_pos ⟨hv.2, hv.1⟩, dif_pos hv]
    exact h.apply (pdec hv.1) (pdec hv.2)
  · rw [dif_neg (fun h' => hv ⟨h'.2, h'.1⟩), dif_neg hv, star_zero]

/-- The row norm bound passes to a matrix of the padded form. -/
theorem PadForm.row_le (hM : PadForm D M) (x : X) {η : ℝ}
    (h : ∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) (y : Cfg (Fin (k + 1))) :
    ∑ y', ‖M x y y'‖ ^ 2 ≤ η ^ 2 := by
  have e0 : ∀ y', ‖M x y y'‖ ^ 2 = ‖(if h : PValid N y ∧ PValid N y' then
      D.matrix x (pdec h.1) (pdec h.2) else 0)‖ ^ 2 := fun y' => by rw [hM]
  rw [Finset.sum_congr rfl (fun y' _ => e0 y')]
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

/-- The column norm bound passes to a matrix of the padded form. -/
theorem PadForm.col_le (hM : PadForm D M) (x : X) {η : ℝ}
    (h : ∀ j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) (y' : Cfg (Fin (k + 1))) :
    ∑ y, ‖M x y y'‖ ^ 2 ≤ η ^ 2 := by
  have e0 : ∀ y, ‖M x y y'‖ ^ 2 = ‖(if h : PValid N y ∧ PValid N y' then
      D.matrix x (pdec h.1) (pdec h.2) else 0)‖ ^ 2 := fun y => by rw [hM]
  rw [Finset.sum_congr rfl (fun y _ => e0 y)]
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

/-- The entry bound passes to a matrix of the padded form. -/
theorem PadForm.entry_le (hM : PadForm D M) (x : X) {μ : ℝ} (hμ : 0 ≤ μ)
    (h : ∀ i j, ‖D.matrix x i j‖ ≤ μ) (y y' : Cfg (Fin (k + 1))) : ‖M x y y'‖ ≤ μ := by
  rw [hM]
  split_ifs with hv
  · exact h _ _
  · rw [norm_zero]
    exact hμ

end Form

end

end SparseHamiltonian.GeneralSparseAccess
