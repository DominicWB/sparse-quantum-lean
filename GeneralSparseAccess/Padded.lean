import GeneralSparseAccess.Data

/-!
# The ingredients of the padded data

From sparse access of general size (`QData`, `N ≤ 2^k`, `s ≤ N`) the padded data of
`PaddedData` live on `k + 1`-bit index words, the top bit a **marker** (`mark`, `lo`, `idx`), with
`s' = 2^⌈log₂ s⌉` slots (`sbP`, `sP`; `s ≤ s' < 2s`, `sP_lt`):

* the valid index words have marker `0` and a low word below `N` (`PValid`, `pdec`); the padded
  stored word is the supplied word on a pair of valid index words and the public zero word `z₀`
  otherwise (`ptable`);
* the row list of a valid row is the supplied list on the positions `a < s`, followed by the
  marked positions `(1, a)`, `s ≤ a < s'`; every other row lists the marked positions (`plist`,
  `prowloc`); the column lists likewise (`pcolloc`); all are injective;
* the padded row locator is the configuration matrix `rowMat`: flip the marker of the position when
  the row or the position is invalid (`maskE`, from the validity test `evalid`), then apply the
  supplied row locator to the low words when the marker is clear (`ctlBlock`); the padded column
  locator (`colMat`) does the same with the supplied column locator and then exchanges the two index
  registers (`swapE`). Both are unitary (`rowMat_isUnitary`, `colMat_isUnitary`) for every action of
  the supplied locators outside their valid list inputs (`matOp_rowMat`, `matOp_colMat`: their
  register operators).
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

/-! ### Marked index words -/

section Words

variable {k : ℕ}

/-- The marker (top bit) of a `k + 1`-bit index word. -/
def mark (y : Cfg (Fin (k + 1))) : Bool := y (Fin.last k)

/-- The low `k` bits of a `k + 1`-bit index word. -/
def lo (y : Cfg (Fin (k + 1))) : Cfg (Fin k) := fun j => y (Fin.castSucc j)

/-- The `k + 1`-bit index word with marker `m` and low word `d`. -/
def idx (m : Bool) (d : Cfg (Fin k)) : Cfg (Fin (k + 1)) :=
  fun j => if h : j.val < k then d ⟨j.val, h⟩ else m

@[simp] theorem mk_idx (m : Bool) (d : Cfg (Fin k)) : mark (idx m d) = m := by
  simp [mark, idx]

@[simp] theorem lo_idx (m : Bool) (d : Cfg (Fin k)) : lo (idx m d) = d := by
  funext j
  simp [lo, idx, j.isLt]

theorem idx_mark_lo (y : Cfg (Fin (k + 1))) : idx (mark y) (lo y) = y := by
  funext j
  by_cases h : j.val < k
  · simp [idx, lo, h]
  · have hj : j = Fin.last k := Fin.ext (by have := j.isLt; simp; omega)
    subst hj
    simp [idx, mark]

theorem idx_injective {m m' : Bool} {d d' : Cfg (Fin k)} (h : idx m d = idx m' d') :
    m = m' ∧ d = d' := by
  refine ⟨?_, ?_⟩
  · have := congrArg mark h
    simpa using this
  · have := congrArg lo h
    simpa using this

theorem idx_eq_iff (m : Bool) (d : Cfg (Fin k)) (y : Cfg (Fin (k + 1))) :
    idx m d = y ↔ m = mark y ∧ d = lo y := by
  constructor
  · rintro rfl
    simp
  · rintro ⟨rfl, rfl⟩
    exact idx_mark_lo y

end Words

/-! ### The padded slot count -/

/-- The exponent of the padded slot count, `⌈log₂ s⌉`. -/
def sbP (s : ℕ) : ℕ := Nat.clog 2 s

/-- The padded slot count `s' = 2^⌈log₂ s⌉`. -/
def sP (s : ℕ) : ℕ := 2 ^ sbP s

theorem le_sP (s : ℕ) : s ≤ sP s := Nat.le_pow_clog (by norm_num) s

theorem sP_pos (s : ℕ) : 0 < sP s := by unfold sP; positivity

theorem sbP_le {s k : ℕ} (h : s ≤ 2 ^ k) : sbP s ≤ k := Nat.clog_le_of_le_pow h

theorem sP_le {s k : ℕ} (h : s ≤ 2 ^ k) : sP s ≤ 2 ^ k :=
  Nat.pow_le_pow_right (by norm_num) (sbP_le h)

/-- The padded slot count is less than twice the slot count. -/
theorem sP_lt {s : ℕ} (hs : 0 < s) : sP s < 2 * s := by
  unfold sP sbP
  by_cases h1 : s = 1
  · subst h1
    simp
  · have hs1 : 1 < s := by omega
    have hpos : 0 < Nat.clog 2 s := Nat.clog_pos (by norm_num) hs1
    have h := Nat.pow_pred_clog_lt_self (by norm_num : 1 < 2) hs1
    obtain ⟨d, hd⟩ : ∃ d, Nat.clog 2 s = d + 1 := ⟨Nat.clog 2 s - 1, by omega⟩
    rw [hd] at h ⊢
    simp only [Nat.pred_succ] at h
    rw [pow_succ]
    omega

/-! ### The padded data -/

section Valid

variable {N k : ℕ}

/-- A valid index word: marker `0` and low word below `N`. -/
def PValid (N : ℕ) (y : Cfg (Fin (k + 1))) : Prop := mark y = false ∧ wordValue (lo y) < N

instance (N : ℕ) (y : Cfg (Fin (k + 1))) : Decidable (PValid N y) := by
  unfold PValid
  infer_instance

/-- The index of a valid index word. -/
def pdec {y : Cfg (Fin (k + 1))} (h : PValid N y) : Fin N := ⟨wordValue (lo y), h.2⟩

theorem binW_pdec {y : Cfg (Fin (k + 1))} (h : PValid N y) : binW k (pdec h) = lo y :=
  binW_wordValue (lo y)

theorem idx_binW_pdec {y : Cfg (Fin (k + 1))} (h : PValid N y) :
    idx false (binW k (pdec h)) = y := by
  rw [binW_pdec, ← h.1]
  exact idx_mark_lo y

theorem pvalid_idx (hN : N ≤ 2 ^ k) (i : Fin N) : PValid N (idx false (binW k i)) := by
  refine ⟨mk_idx _ _, ?_⟩
  rw [lo_idx, wordValue_binW (lt_of_lt_of_le i.isLt hN)]
  exact i.isLt

theorem pdec_idx (hN : N ≤ 2 ^ k) (i : Fin N) : pdec (pvalid_idx hN i) = i := by
  apply Fin.ext
  change wordValue (lo (idx false (binW k i))) = i.val
  rw [lo_idx, wordValue_binW (lt_of_lt_of_le i.isLt hN)]

/-- The padded slot `a`: marker `0` and the binary word of `a`. -/
def pslot (k : ℕ) {s : ℕ} (a : Fin (sP s)) : Cfg (Fin (k + 1)) := idx false (binW k a)

theorem pslot_injective {s : ℕ} (hs : s ≤ 2 ^ k) : Function.Injective (pslot k (s := s)) := by
  intro a a' h
  have h' := (idx_injective h).2
  have ha : a.val < 2 ^ k := lt_of_lt_of_le a.isLt (sP_le hs)
  have ha' : a'.val < 2 ^ k := lt_of_lt_of_le a'.isLt (sP_le hs)
  exact Fin.ext (binW_inj ha ha' h')

end Valid

namespace QData

variable {X : Type*} {N s k b : ℕ} (D : QData X N s k b)

/-- The stored word of the padded data: the supplied word on a pair of valid indices, the public
zero word `z₀` otherwise. -/
def ptable (z₀ : Cfg (VW b)) (x : X) (e : Cfg (Fin (k + 1)) × Cfg (Fin (k + 1))) : Cfg (VW b) :=
  if PValid N e.1 ∧ PValid N e.2 then D.table x (edgeW k (lo e.1) (lo e.2)) else z₀

/-- The padded list of a list function `loc`: the list of a valid index word on the positions
`a < s`, and the marked positions `(1, a)` otherwise. -/
def plist (loc : Fin N → Fin s → Fin N) (y : Cfg (Fin (k + 1))) (a : Fin (sP s)) :
    Cfg (Fin (k + 1)) :=
  if h : PValid N y ∧ a.val < s then idx false (binW k (loc (pdec h.1) ⟨a.val, h.2⟩))
  else idx true (binW k a)

theorem plist_injective (hN : N ≤ 2 ^ k) (hs : s ≤ 2 ^ k) {loc : Fin N → Fin s → Fin N}
    (hloc : ∀ i, Function.Injective (loc i)) (y : Cfg (Fin (k + 1))) :
    Function.Injective (plist (k := k) loc y) := by
  intro a a' h
  have ha : a.val < 2 ^ k := lt_of_lt_of_le a.isLt (sP_le hs)
  have ha' : a'.val < 2 ^ k := lt_of_lt_of_le a'.isLt (sP_le hs)
  unfold plist at h
  split_ifs at h with h1 h2 h2
  · have := (idx_injective h).2
    have e := hloc _ (Fin.ext (binW_inj (lt_of_lt_of_le (Fin.isLt _) hN)
      (lt_of_lt_of_le (Fin.isLt _) hN) this))
    exact Fin.ext (by simpa using congrArg Fin.val e)
  · exact absurd (idx_injective h).1 (by simp)
  · exact absurd (idx_injective h).1 (by simp)
  · exact Fin.ext (binW_inj ha ha' (idx_injective h).2)

/-- The padded row list. -/
def prowloc (x : X) : Cfg (Fin (k + 1)) → Fin (sP s) → Cfg (Fin (k + 1)) := plist (D.rowloc x)

/-- The padded column list. -/
def pcolloc (x : X) : Cfg (Fin (k + 1)) → Fin (sP s) → Cfg (Fin (k + 1)) := plist (D.colloc x)

theorem prowloc_injective (x : X) (y : Cfg (Fin (k + 1))) : Function.Injective (D.prowloc x y) :=
  plist_injective D.hN D.s_le_pow (D.row_injective x) y

theorem pcolloc_injective (x : X) (y : Cfg (Fin (k + 1))) : Function.Injective (D.pcolloc x y) :=
  plist_injective D.hN D.s_le_pow (D.column_injective x) y

/-! ### The padded locators -/

/-- The low wires of the `k + 1`-bit edge register. -/
def lowE (k : ℕ) : EW k → EW (k + 1) := Sum.map Fin.castSucc Fin.castSucc

theorem lowE_injective (k : ℕ) : Function.Injective (lowE k) :=
  Sum.map_injective.mpr ⟨Fin.castSucc_injective k, Fin.castSucc_injective k⟩

/-- The marker wire of the first index. -/
def mw₁ (k : ℕ) : EW (k + 1) := Sum.inl (Fin.last k)

/-- The marker wire of the second index (the list position). -/
def mw₂ (k : ℕ) : EW (k + 1) := Sum.inr (Fin.last k)

theorem lowE_ne_mw₁ (k : ℕ) (a : EW k) : lowE k a ≠ mw₁ k := by
  rcases a with j | j
  · simp only [lowE, mw₁, Sum.map_inl, ne_eq, Sum.inl.injEq]
    exact Fin.castSucc_ne_last j
  · simp [lowE, mw₁]

theorem lowE_ne_mw₂ (k : ℕ) (a : EW k) : lowE k a ≠ mw₂ k := by
  rcases a with j | j
  · simp [lowE, mw₂]
  · simp only [lowE, mw₂, Sum.map_inr, ne_eq, Sum.inr.injEq]
    exact Fin.castSucc_ne_last j

theorem mw₁_ne_mw₂ (k : ℕ) : mw₁ k ≠ mw₂ k := by simp [mw₁, mw₂]

/-- Every wire of the edge register is a low wire or one of the two markers. -/
theorem wire_cases (k : ℕ) (w : EW (k + 1)) : (∃ a, lowE k a = w) ∨ w = mw₁ k ∨ w = mw₂ k := by
  rcases w with j | j
  · by_cases h : j.val < k
    · exact Or.inl ⟨Sum.inl ⟨j.val, h⟩, by simp [lowE]⟩
    · refine Or.inr (Or.inl ?_)
      have : j = Fin.last k := Fin.ext (by have := j.isLt; simp; omega)
      rw [this]
      rfl
  · by_cases h : j.val < k
    · exact Or.inl ⟨Sum.inr ⟨j.val, h⟩, by simp [lowE]⟩
    · refine Or.inr (Or.inr ?_)
      have : j = Fin.last k := Fin.ext (by have := j.isLt; simp; omega)
      rw [this]
      rfl

/-- Two configurations of the edge register agree when their markers and low wires agree. -/
theorem cfg_ext_E {e e' : Cfg (EW (k + 1))} (h1 : e (mw₁ k) = e' (mw₁ k))
    (h2 : e (mw₂ k) = e' (mw₂ k)) (hl : ∀ a, e (lowE k a) = e' (lowE k a)) : e = e' := by
  funext w
  rcases wire_cases k w with ⟨a, rfl⟩ | rfl | rfl
  · exact hl a
  · exact h1
  · exact h2

theorem outPart_lowE_eq_iff (e e' : Cfg (EW (k + 1))) :
    outPart (lowE k) e = outPart (lowE k) e' ↔ e (mw₁ k) = e' (mw₁ k) ∧ e (mw₂ k) = e' (mw₂ k) := by
  constructor
  · intro h
    exact ⟨congrFun h ⟨mw₁ k, lowE_ne_mw₁ k⟩, congrFun h ⟨mw₂ k, lowE_ne_mw₂ k⟩⟩
  · rintro ⟨h1, h2⟩
    funext w
    rcases wire_cases k w.1 with ⟨a, ha⟩ | h | h
    · exact absurd ha (w.2 a)
    · change e w.1 = e' w.1
      rw [h]; exact h1
    · change e w.1 = e' w.1
      rw [h]; exact h2

/-- The validity of the first index and of the list position held by an edge configuration. -/
def evalid (N s : ℕ) (e : Cfg (EW (k + 1))) : Bool :=
  (!e (mw₁ k)) && decide (wordValue (fun j => e (lowE k (Sum.inl j))) < N) &&
    decide (wordValue (fun j => e (lowE k (Sum.inr j))) < s)

theorem evalid_update_mw₂ (N s : ℕ) (e : Cfg (EW (k + 1))) (v : Bool) :
    evalid N s (Function.update e (mw₂ k) v) = evalid N s e := by
  unfold evalid
  rw [Function.update_of_ne (mw₁_ne_mw₂ k)]
  have h1 : (fun j => Function.update e (mw₂ k) v (lowE k (Sum.inl j))) =
      fun j => e (lowE k (Sum.inl j)) :=
    funext fun j => Function.update_of_ne (lowE_ne_mw₂ k _) _ _
  have h2 : (fun j => Function.update e (mw₂ k) v (lowE k (Sum.inr j))) =
      fun j => e (lowE k (Sum.inr j)) :=
    funext fun j => Function.update_of_ne (lowE_ne_mw₂ k _) _ _
  rw [h1, h2]

/-- The configuration map of the mask: flip the marker of the position when the first index or the
position is invalid. -/
def maskF (N s : ℕ) (e : Cfg (EW (k + 1))) : Cfg (EW (k + 1)) :=
  Function.update e (mw₂ k) (e (mw₂ k) ^^ !evalid N s e)

theorem maskF_maskF (N s : ℕ) (e : Cfg (EW (k + 1))) : maskF N s (maskF N s e) = e := by
  unfold maskF
  rw [evalid_update_mw₂, Function.update_self, Function.update_idem]
  conv_rhs => rw [← Function.update_eq_self (mw₂ k) e]
  congr 1
  cases e (mw₂ k) <;> cases evalid N s e <;> rfl

/-- **The mask**, an involution of the edge configurations. -/
def maskE (N s : ℕ) : Cfg (EW (k + 1)) ≃ Cfg (EW (k + 1)) where
  toFun := maskF N s
  invFun := maskF N s
  left_inv := maskF_maskF N s
  right_inv := maskF_maskF N s

/-- The exchange of the two index registers. -/
def swapE (k : ℕ) : Cfg (EW (k + 1)) ≃ Cfg (EW (k + 1)) where
  toFun e := fun w => e (Sum.swap w)
  invFun e := fun w => e (Sum.swap w)
  left_inv e := by funext w; simp
  right_inv e := by funext w; simp

/-- The block of the controlled locator: the supplied locator when the marker of the position is
clear, the identity otherwise. -/
def ctlBlock (F : EuclideanSpace ℂ (Cfg (EW k)) →L[ℂ] EuclideanSpace ℂ (Cfg (EW k)))
    (e : Cfg (EW (k + 1))) : Matrix (Cfg (EW k)) (Cfg (EW k)) ℂ :=
  if e (mw₂ k) then 1 else toMat (Equiv.refl _) F

/-- **The configuration matrix of the padded row locator**: the mask, then the supplied row
locator on the low wires when the marker of the position is clear. -/
def rowMat (x : X) : Matrix (Cfg (EW (k + 1))) (Cfg (EW (k + 1))) ℂ :=
  locMat (lowE k) (ctlBlock (D.rowOracle x)) * permMat (maskE N s)

/-- **The configuration matrix of the padded column locator**: the mask, the supplied column
locator on the low wires when the marker of the position is clear, and the exchange of the two
index registers. -/
def colMat (x : X) : Matrix (Cfg (EW (k + 1))) (Cfg (EW (k + 1))) ℂ :=
  permMat (swapE k) * (locMat (lowE k) (ctlBlock (D.columnOracle x)) * permMat (maskE N s))

variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- The register operator of the controlled block. -/
theorem matOp_ctlBlock (F : EuclideanSpace ℂ (Cfg (EW k)) →L[ℂ] EuclideanSpace ℂ (Cfg (EW k))) :
    localOp (lowE k) (lowE_injective k) (fun e => matOp (Q := R) (ctlBlock F e)) =
      localOp (lowE k) (lowE_injective k)
        (fun e => if e (mw₂ k) then 1 else qlift (Equiv.refl _) F) := by
  congr 1
  funext e
  unfold ctlBlock
  split_ifs
  · exact matOp_one
  · rfl

/-- **The padded row locator on registers**: the controlled supplied locator after the mask. -/
theorem matOp_rowMat (x : X) :
    matOp (Q := R) (D.rowMat x) =
      localOp (lowE k) (lowE_injective k)
          (fun e => if e (mw₂ k) then 1 else qlift (Equiv.refl _) (D.rowOracle x)) ∘L
        permOp (maskE N s) := by
  rw [rowMat, ← matOp_mul, ← localOp_matOp (lowE_injective k), matOp_ctlBlock, permOp_eq_matOp]

/-- **The padded column locator on registers**. -/
theorem matOp_colMat (x : X) :
    matOp (Q := R) (D.colMat x) =
      permOp (swapE k) ∘L (localOp (lowE k) (lowE_injective k)
          (fun e => if e (mw₂ k) then 1 else qlift (Equiv.refl _) (D.columnOracle x)) ∘L
        permOp (maskE N s)) := by
  rw [colMat, ← matOp_mul, ← matOp_mul, ← localOp_matOp (lowE_injective k), matOp_ctlBlock, permOp_eq_matOp,
    permOp_eq_matOp]

theorem ctl_isUnitary {F : EuclideanSpace ℂ (Cfg (EW k)) →L[ℂ] EuclideanSpace ℂ (Cfg (EW k))}
    (hF : IsUnitary F) :
    IsUnitary (localOp (Q := R) (lowE k) (lowE_injective k)
      (fun e => if e (mw₂ k) then 1 else qlift (Equiv.refl _) F)) := by
  apply localOp_isUnitary
  intro e
  split_ifs
  · exact isUnitary_one
  · exact qlift_isUnitary _ hF

theorem rowMat_isUnitary (x : X) : IsUnitary (matOp (Q := ℂ) (D.rowMat x)) := by
  rw [matOp_rowMat]
  exact (ctl_isUnitary (D.row_unitary x)).mul (isUnitary_permOp _)

theorem colMat_isUnitary (x : X) : IsUnitary (matOp (Q := ℂ) (D.colMat x)) := by
  rw [matOp_colMat]
  exact (isUnitary_permOp _).mul ((ctl_isUnitary (D.column_unitary x)).mul (isUnitary_permOp _))

end QData

end

end SparseHamiltonian.GeneralSparseAccess
