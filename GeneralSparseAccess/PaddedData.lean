import GeneralSparseAccess.Padded

/-!
# The padded data

`QData.padData D z₀ hz₀`: the padded data of `Padded` as native sparse data
(`NativeSparseBlockEncoding.Data`) on the index words `Cfg (Fin (k + 1))`, with `s' = 2^⌈log₂ s⌉`
slots `pslot` (the binary words of `0 ≤ a < s'` with marker `0`), the decoder of `D`, the padded
stored words `ptable` and the padded lists. Its matrix is the matrix of `D` on valid index words
and zero elsewhere (`QData.padData_matrix`, in `PadSpec`); every nonzero entry is listed (`row_covers`,
`column_covers`).

The padded locators `ofMat (phiE (Equiv.refl _)) (rowMat x)` and `ofMat … (colMat x)` have the
prescribed action on every valid list input of the padded data (`rowMat_col`, `colMat_col`, giving
the `row_valid`, `column_valid` fields), from the action of the supplied locators on their own
valid list inputs only.
-/

set_option autoImplicit false

namespace SparseHamiltonian.GeneralSparseAccess

noncomputable section
open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
  SparseHamiltonian.GateBinary
open SparseHamiltonian.OracleCircuit
open SparseHamiltonian.GateODE (overwrite_apply_ι overwrite_apply_out)
open SparseHamiltonian.GatePointerEncoding (wordValue wordValue_lt_pow)
open NativeSparseBlockEncoding (Query)
open scoped InnerProduct

/-! ### Matrix entries -/

section Entries

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem mul_permMat_apply (M : Matrix (Cfg V) (Cfg V) ℂ) (e : Cfg V ≃ Cfg V) (b c : Cfg V) :
    (M * permMat e) b c = M b (e c) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (e c)]
  · simp [permMat]
  · intro d _ hd
    simp [permMat, hd]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem permMat_mul_apply (M : Matrix (Cfg V) (Cfg V) ℂ) (e : Cfg V ≃ Cfg V) (b c : Cfg V) :
    (permMat e * M) b c = M (e.symm b) c := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (e.symm b)]
  · simp [permMat]
  · intro d _ hd
    have : b ≠ e d := fun h => hd (by rw [h, Equiv.symm_apply_apply])
    simp [permMat, this]
  · intro h
    exact absurd (Finset.mem_univ _) h

omit [Fintype V] [DecidableEq V] in
theorem toMat_refl_apply {W : Type*} [Fintype W] [DecidableEq W]
    (F : EuclideanSpace ℂ (Cfg W) →L[ℂ] EuclideanSpace ℂ (Cfg W)) (d' d : Cfg W) :
    toMat (Equiv.refl (Cfg W)) F d' d = F (EuclideanSpace.single d 1) d' := rfl

end Entries

/-! ### Edge configurations of the padded register -/

section Edge

variable {k : ℕ}

@[simp] theorem edgeW_mw₁ (y y' : Cfg (Fin (k + 1))) : edgeW (k + 1) y y' (QData.mw₁ k) = mark y :=
  rfl

@[simp] theorem edgeW_mw₂ (y y' : Cfg (Fin (k + 1))) : edgeW (k + 1) y y' (QData.mw₂ k) = mark y' :=
  rfl

theorem edgeW_lowE (y y' : Cfg (Fin (k + 1))) :
    (fun a => edgeW (k + 1) y y' (QData.lowE k a)) = edgeW k (lo y) (lo y') := by
  funext a
  rcases a with j | j <;> rfl

theorem phiE_refl_edgeW (y y' : Cfg (Fin (k + 1))) :
    phiE (Equiv.refl (Cfg (Fin (k + 1)))) (edgeW (k + 1) y y') = (y, y') := rfl

theorem edgeW_eq_iff (y y' : Cfg (Fin (k + 1))) (b : Cfg (EW (k + 1))) :
    b = edgeW (k + 1) y y' ↔
      b (QData.mw₁ k) = mark y ∧ b (QData.mw₂ k) = mark y' ∧
        (fun a => b (QData.lowE k a)) = edgeW k (lo y) (lo y') := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl, edgeW_lowE y y'⟩
  · rintro ⟨h1, h2, hl⟩
    apply QData.cfg_ext_E
    · rw [h1]; rfl
    · rw [h2]; rfl
    · intro a
      have := congrFun hl a
      rw [this, ← edgeW_lowE y y']

theorem update_mw₂_edgeW (y y' : Cfg (Fin (k + 1))) (v : Bool) :
    Function.update (edgeW (k + 1) y y') (QData.mw₂ k) v = edgeW (k + 1) y (idx v (lo y')) := by
  apply QData.cfg_ext_E
  · rw [Function.update_of_ne (QData.mw₁_ne_mw₂ k)]
    rfl
  · rw [Function.update_self]
    exact (mk_idx v (lo y')).symm
  · intro a
    rw [Function.update_of_ne (QData.lowE_ne_mw₂ k a)]
    have h1 := congrFun (edgeW_lowE y y') a
    have h2 := congrFun (edgeW_lowE y (idx v (lo y'))) a
    rw [h1, h2, lo_idx]

end Edge

namespace QData

variable {X : Type*} {N s k b : ℕ} (D : QData X N s k b)

theorem locMat_lowE_apply (M : Cfg (EW (k + 1)) → Matrix (Cfg (EW k)) (Cfg (EW k)) ℂ)
    (b d : Cfg (EW (k + 1))) :
    locMat (lowE k) M b d =
      if b (mw₁ k) = d (mw₁ k) ∧ b (mw₂ k) = d (mw₂ k) then
        M (clearCfg (lowE k) b) (fun a => b (lowE k a)) (fun a => d (lowE k a)) else 0 := by
  unfold locMat
  by_cases h : b (mw₁ k) = d (mw₁ k) ∧ b (mw₂ k) = d (mw₂ k)
  · rw [if_pos h, if_pos ((outPart_lowE_eq_iff d b).mpr ⟨h.1.symm, h.2.symm⟩)]
  · rw [if_neg h, if_neg (fun h' => h (by
      obtain ⟨h1, h2⟩ := (outPart_lowE_eq_iff d b).mp h'
      exact ⟨h1.symm, h2.symm⟩))]

theorem clearCfg_lowE_mw₂ (b : Cfg (EW (k + 1))) : clearCfg (lowE k) b (mw₂ k) = b (mw₂ k) :=
  overwrite_apply_out _ b _ _ (lowE_ne_mw₂ k)

/-- The validity of an edge `(y, slot a)`. -/
theorem evalid_edge_pslot (hs : s ≤ 2 ^ k) (y : Cfg (Fin (k + 1))) (a : Fin (sP s)) :
    evalid N s (edgeW (k + 1) y (pslot k a)) = decide (PValid N y ∧ a.val < s) := by
  have ha : a.val < 2 ^ k := lt_of_lt_of_le a.isLt (sP_le hs)
  unfold evalid
  have h1 : (fun j => edgeW (k + 1) y (pslot k a) (lowE k (Sum.inl j))) = lo y := rfl
  have h2 : (fun j => edgeW (k + 1) y (pslot k a) (lowE k (Sum.inr j))) = binW k a := by
    funext j
    change pslot k a (Fin.castSucc j) = _
    unfold pslot
    exact congrFun (lo_idx false (binW k a)) j
  rw [h1, h2, wordValue_binW ha, edgeW_mw₁]
  unfold PValid
  rcases Bool.eq_false_or_eq_true (mark y) with h | h <;> simp [h]

/-- The mask on an edge `(y, slot a)`: unchanged for a valid row and position, the marked position
otherwise. -/
theorem maskE_edge_pslot (hs : s ≤ 2 ^ k) (y : Cfg (Fin (k + 1))) (a : Fin (sP s)) :
    maskE N s (edgeW (k + 1) y (pslot k a)) =
      if PValid N y ∧ a.val < s then edgeW (k + 1) y (pslot k a)
      else edgeW (k + 1) y (idx true (binW k a)) := by
  change maskF N s _ = _
  unfold maskF
  rw [evalid_edge_pslot hs]
  have hmk : edgeW (k + 1) y (pslot k a) (mw₂ k) = false := mk_idx _ _
  rw [hmk]
  by_cases hv : PValid N y ∧ a.val < s
  · rw [decide_eq_true hv, if_pos hv]
    conv_rhs => rw [← Function.update_eq_self (mw₂ k) (edgeW (k + 1) y (pslot k a))]
    rw [hmk]
    rfl
  · rw [decide_eq_false hv, if_neg hv, update_mw₂_edgeW, Bool.not_false, Bool.false_xor]
    unfold pslot
    rw [lo_idx]

/-- The entries of the controlled block on an edge column. -/
theorem locMat_ctl_edge (F : EuclideanSpace ℂ (Cfg (EW k)) →L[ℂ] EuclideanSpace ℂ (Cfg (EW k)))
    (bb : Cfg (EW (k + 1))) (y y' : Cfg (Fin (k + 1))) :
    locMat (lowE k) (ctlBlock F) bb (edgeW (k + 1) y y') =
      if bb (mw₁ k) = mark y ∧ bb (mw₂ k) = mark y' then
        (if mark y' then
          (if (fun a => bb (lowE k a)) = edgeW k (lo y) (lo y') then 1 else 0)
        else F (EuclideanSpace.single (edgeW k (lo y) (lo y')) 1) (fun a => bb (lowE k a)))
      else 0 := by
  rw [locMat_lowE_apply, edgeW_mw₁, edgeW_mw₂, edgeW_lowE]
  by_cases hm : bb (mw₁ k) = mark y ∧ bb (mw₂ k) = mark y'
  · rw [if_pos hm, if_pos hm]
    unfold ctlBlock
    rw [clearCfg_lowE_mw₂, hm.2]
    by_cases hq : mark y' = true
    · rw [if_pos hq, if_pos hq, Matrix.one_apply]
    · rw [if_neg hq, if_neg hq, toMat_refl_apply]
  · rw [if_neg hm, if_neg hm]

theorem ite_and_one {p q : Prop} [Decidable p] [Decidable q] :
    (if p then (if q then (1 : ℂ) else 0) else 0) = if p ∧ q then 1 else 0 := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

/-- **The entries of the masked controlled locator** in the column of a valid list input
`(y, slot a)`, for a locator `F` with the action `loc` on its valid list inputs: the standard basis
column of `(y, plist loc y a)`. -/
theorem ctlMask_col (hs : s ≤ 2 ^ k)
    (F : EuclideanSpace ℂ (Cfg (EW k)) →L[ℂ] EuclideanSpace ℂ (Cfg (EW k)))
    (loc : Fin N → Fin s → Fin N)
    (hF : ∀ (i : Fin N) (a : Fin s),
      F (EuclideanSpace.single (edgeW k (binW k i) (binW k a)) 1) =
        EuclideanSpace.single (edgeW k (binW k i) (binW k (loc i a))) 1)
    (y : Cfg (Fin (k + 1))) (a : Fin (sP s)) (bb : Cfg (EW (k + 1))) :
    (locMat (lowE k) (ctlBlock F) * permMat (maskE N s) :
      Matrix (Cfg (EW (k + 1))) (Cfg (EW (k + 1))) ℂ) bb (edgeW (k + 1) y (pslot k a)) =
      if bb = edgeW (k + 1) y (plist loc y a) then 1 else 0 := by
  rw [mul_permMat_apply, maskE_edge_pslot hs]
  by_cases hv : PValid N y ∧ a.val < s
  · have hpl : plist (k := k) loc y a = idx false (binW k (loc (pdec hv.1) ⟨a.val, hv.2⟩)) := by
      unfold plist
      rw [dif_pos hv]
    rw [if_pos hv, locMat_ctl_edge, hpl]
    have hmk : mark (pslot k a) = false := mk_idx _ _
    have hlo : lo (pslot k a) = binW k (⟨a.val, hv.2⟩ : Fin s) := lo_idx _ _
    rw [hmk, if_neg (show ¬(false = true) by simp), hlo, ← binW_pdec hv.1,
      hF (pdec hv.1) ⟨a.val, hv.2⟩, PiLp.single_apply, ite_and_one]
    congr 1
    apply propext
    rw [edgeW_eq_iff, lo_idx, mk_idx, binW_pdec hv.1]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h1, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨h1, h2⟩, h3⟩
  · have hpl : plist (k := k) loc y a = idx true (binW k a) := by
      unfold plist
      rw [dif_neg hv]
    rw [if_neg hv, locMat_ctl_edge, hpl, mk_idx, if_pos rfl, lo_idx, ite_and_one]
    congr 1
    apply propext
    rw [edgeW_eq_iff, lo_idx, mk_idx]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h1, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨h1, h2⟩, h3⟩

/-- **The entries of the padded row locator** in the column of a valid list input `(y, slot a)`:
the standard basis column of `(y, prowloc x y a)`. -/
theorem rowMat_col (x : X) (y : Cfg (Fin (k + 1))) (a : Fin (sP s)) (bb : Cfg (EW (k + 1))) :
    D.rowMat x bb (edgeW (k + 1) y (pslot k a)) =
      if bb = edgeW (k + 1) y (D.prowloc x y a) then 1 else 0 :=
  ctlMask_col D.s_le_pow (D.rowOracle x) (D.rowloc x) (D.row_valid x) y a bb

/-- **The entries of the padded column locator** in the column of a valid list input
`(y, slot a)`: the standard basis column of `(pcolloc x y a, y)`. -/
theorem colMat_col (x : X) (y : Cfg (Fin (k + 1))) (a : Fin (sP s)) (bb : Cfg (EW (k + 1))) :
    D.colMat x bb (edgeW (k + 1) y (pslot k a)) =
      if bb = edgeW (k + 1) (D.pcolloc x y a) y then 1 else 0 := by
  unfold colMat
  rw [permMat_mul_apply,
    ctlMask_col D.s_le_pow (D.columnOracle x) (D.colloc x) (D.column_valid x) y a]
  have key : ((swapE k).symm bb = edgeW (k + 1) y (D.pcolloc x y a)) ↔
      bb = edgeW (k + 1) (D.pcolloc x y a) y := by
    constructor
    · intro h
      rw [← (swapE k).apply_symm_apply bb, h]
      funext w
      rcases w with j | j <;> rfl
    · intro h
      rw [h]
      funext w
      rcases w with j | j <;> rfl
  unfold pcolloc at key ⊢
  by_cases hb : bb = edgeW (k + 1) (plist (D.colloc x) y a) y
  · rw [if_pos (key.mpr hb), if_pos hb]
  · rw [if_neg (fun h => hb (key.mp h)), if_neg hb]

/-! ### The padded data -/

/-- **The padded data** (native sparse data on `k + 1`-bit index words with `s' = 2^⌈log₂ s⌉`
slots): the matrix of `D` on valid index words and zero elsewhere, the padded lists `prowloc`,
`pcolloc` and the padded locators `rowMat`, `colMat` (as operators on `ℓ²(n × n)`), the decoder of
`D` and the zero word `z₀` on the padded entries. -/
def padData (z₀ : Cfg (VW b)) (hz₀ : D.val z₀ = 0) :
    NativeSparseBlockEncoding.Data X (Cfg (Fin (k + 1))) (Cfg (VW b)) (sP s) where
  slot := ⟨pslot k, pslot_injective D.s_le_pow⟩
  slots_pos := sP_pos s
  scale := D.scale
  scale_pos := D.scale_pos
  matrix x y y' := D.val (D.ptable z₀ x (y, y'))
  table x e := D.ptable z₀ x e
  decode _ z := D.val z
  decode_bound _ z := D.val_bound z
  decoded _ _ _ := rfl
  rowloc := D.prowloc
  colloc := D.pcolloc
  row_injective := D.prowloc_injective
  column_injective := D.pcolloc_injective
  row_covers x y y' h := by
    unfold ptable at h
    split_ifs at h with hv
    · rw [show edgeW k (lo y) (lo y') = edgeW k (binW k (pdec hv.1)) (binW k (pdec hv.2)) by
        rw [binW_pdec, binW_pdec], D.decoded] at h
      obtain ⟨a, ha⟩ := D.row_covers x _ _ h
      refine Finset.mem_image.mpr ⟨⟨a.val, lt_of_lt_of_le a.isLt (le_sP s)⟩, Finset.mem_univ _, ?_⟩
      change plist (D.rowloc x) y _ = y'
      unfold plist
      rw [dif_pos ⟨hv.1, a.isLt⟩]
      have : (⟨a.val, a.isLt⟩ : Fin s) = a := rfl
      rw [this, ha]
      exact idx_binW_pdec hv.2
    · exact absurd hz₀ h
  column_covers x y y' h := by
    unfold ptable at h
    split_ifs at h with hv
    · rw [show edgeW k (lo y) (lo y') = edgeW k (binW k (pdec hv.1)) (binW k (pdec hv.2)) by
        rw [binW_pdec, binW_pdec], D.decoded] at h
      obtain ⟨a, ha⟩ := D.column_covers x _ _ h
      refine Finset.mem_image.mpr ⟨⟨a.val, lt_of_lt_of_le a.isLt (le_sP s)⟩, Finset.mem_univ _, ?_⟩
      change plist (D.colloc x) y' _ = y
      unfold plist
      rw [dif_pos ⟨hv.2, a.isLt⟩]
      have : (⟨a.val, a.isLt⟩ : Fin s) = a := rfl
      rw [this, ha]
      exact idx_binW_pdec hv.1
    · exact absurd hz₀ h
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

end QData

end

end SparseHamiltonian.GeneralSparseAccess
