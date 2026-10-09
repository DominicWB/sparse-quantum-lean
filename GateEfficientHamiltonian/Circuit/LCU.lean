import GateEfficientHamiltonian.Circuit.Range

/-!
# The LCU circuit and its successful block

`PREP f` prepares the label table with real amplitudes `f` (a binary tree on
the label wires); `RANGE` prepares, for every label `ℓ`, the uniform pointer
state of length `nOf ℓ`.  The LCU circuit is
`L = PREP(f_out)† ∘ RANGE† ∘ SELECT ∘ RANGE ∘ PREP(f_in)`.

`lcu_block` evaluates its block between clean inputs: it is the signed
average `Σ_ℓ (wt ℓ / 2) B(nOf ℓ)` of the coherent-reuse successful blocks.
-/

namespace SparseHamiltonian.GateCircuit.Sim

noncomputable section
open ContinuousLinearMap OracleCircuit
open scoped InnerProduct BigOperators
open GatePointerEncoding (wordValue wordEquivFin wordFin)
open ChronologicalResolvent CoherentReuse FiniteChronologicalInverse

variable {a m r K : ℕ}
variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-! ### Label and pointer wires -/

def labWires : Fin r → Wire a m r K := fun s => Wire.lab s
def ptrWires : Fin r → Wire a m r K := fun s => Wire.ptr s

theorem labWires_injective : Function.Injective (labWires (a := a) (m := m) (r := r) (K := K)) :=
  fun _ _ h => by cases h; rfl

theorem ptrWires_injective : Function.Injective (ptrWires (a := a) (m := m) (r := r) (K := K)) :=
  fun _ _ h => by cases h; rfl

/-- The pointer index of a word. -/
def wIdx (w : Word r) : Fin (cap r + 1) := Fin.cast (cap_succ r).symm (wordEquivFin r w)

theorem pubCfg_ptr (lw : Word r) (k : Fin (cap r + 1)) (i : Fin r) :
    pubCfg (a := a) (m := m) (K := K) lw k (Wire.ptr i) =
      (wordEquivFin r).symm (Fin.cast (cap_succ r) k) i := rfl

theorem setLow_lab_pubCfg (lw : Word r) (k : Fin (cap r + 1)) (w : Word r) :
    setLow labWires r le_rfl (pubCfg (a := a) (m := m) (K := K) lw k) w = pubCfg w k := by
  funext v
  cases v with
  | lab i =>
      have := setLow_apply_low (labWires (a := a) (m := m) (r := r) (K := K))
        labWires_injective r le_rfl (pubCfg lw k) w i
      simp only [labWires, Fin.eta] at this
      rw [this]
      rfl
  | _ =>
      rw [setLow_apply_other _ _ _ _ _ _ (fun t h => by cases h)]
      rfl

theorem setLow_ptr_pubCfg (lw : Word r) (w : Word r) :
    setLow ptrWires r le_rfl (pubCfg (a := a) (m := m) (K := K) lw 0) w = pubCfg lw (wIdx w) := by
  funext v
  cases v with
  | ptr i =>
      have := setLow_apply_low (ptrWires (a := a) (m := m) (r := r) (K := K))
        ptrWires_injective r le_rfl (pubCfg lw 0) w i
      simp only [ptrWires, Fin.eta] at this
      rw [this, pubCfg_ptr, wIdx]
      simp
  | _ =>
      rw [setLow_apply_other _ _ _ _ _ _ (fun t h => by cases h)]
      rfl

theorem ptrOf_pubCfg (lw : Word r) (k : Fin (cap r + 1)) :
    ptrOf (pubCfg (a := a) (m := m) (K := K) lw k) = (wordEquivFin r).symm (Fin.cast (cap_succ r) k) :=
  rfl

theorem labOf_pubCfg (lw : Word r) (k : Fin (cap r + 1)) :
    labOf (pubCfg (a := a) (m := m) (K := K) lw k) = lw := rfl

/-- The all-zero configuration. -/
theorem pubCfg_zero : pubCfg (a := a) (m := m) (K := K) (zw r) 0 = fun _ => false := by
  funext v
  cases v with
  | ptr i =>
      rw [pubCfg_ptr]
      have h0 : Fin.cast (cap_succ r) (0 : Fin (cap r + 1)) = wordEquivFin r (zw r) := by
        apply Fin.ext
        simp [GatePointerEncoding.wordValue, zw]
      rw [h0, Equiv.symm_apply_apply]
  | lab i => rfl
  | _ => rfl

omit [CompleteSpace P] in
/-- A public model state is a sum of public basis configurations. -/
theorem emb_public_sum (lw : Word r) (u : Fin (cap r + 1) → P) :
    emb (K := K) (m := m) (a := a) lw ((u, 0) : Model a m r P) =
      ∑ k, bas (pubCfg lw k) (u k) := by
  apply PiLp.ext
  intro x
  rw [emb_apply, WithLp.ofLp_sum]
  simp only [Finset.sum_apply, bas_apply]
  by_cases hc : labOf x = lw ∧ Clean x
  · cases hs : x .sec
    · rw [embVal_public lw _ x hc hs]
      by_cases hz : slotOf x = zw m ∧ ancOf x = zw a
      · rw [if_pos hz]
        have hx := eq_pubCfg lw x hc hs hz
        rw [Finset.sum_eq_single (ptrIdx x)]
        · rw [if_pos hx]
        · intro k _ hk
          rw [if_neg]
          intro e; apply hk
          rw [e, ptrIdx_pubCfg]
        · intro h; exact absurd (Finset.mem_univ _) h
      · rw [if_neg hz]
        symm
        apply Finset.sum_eq_zero
        intro k _
        rw [if_neg]
        intro e; apply hz
        rw [e]; exact ⟨rfl, rfl⟩
    · rw [embVal_private lw _ x hc hs]
      symm
      simp only [Pi.zero_apply]
      apply Finset.sum_eq_zero
      intro k _
      rw [if_neg]
      intro e; rw [e] at hs; exact absurd hs (by simp [pubCfg])
  · rw [embVal_unclean lw _ x hc]
    symm
    apply Finset.sum_eq_zero
    intro k _
    rw [if_neg]
    intro e; apply hc; rw [e]
    refine ⟨rfl, ?_⟩
    intro v hv; cases v <;> simp_all [isFlag, pubCfg]

/-! ### Uniform pointer states of one label -/

/-- Rotation of pointer bit `s` for label word `lw` and length `n`. -/
def rangeM (lw : Word r) (n : ℕ) (s : Fin r) (x : Cfg (Wire a m r K)) : Matrix Bool Bool ℂ :=
  if labOf x = lw then rangeLevel n s (ptrOf x) else 1

/-- Preparation of `|u_n⟩` on the pointer, on the label sector `lw`. -/
def RANGE1 (lw : Word r) (n : ℕ) : Reg (Wire a m r K) P →L[ℂ] Reg (Wire a m r K) P :=
  treeOp ptrWires (rangeM lw n)

theorem ptrOf_update_ptr (y : Cfg (Wire a m r K)) (t : Fin r) (b : Bool) :
    ptrOf (Function.update y (Wire.ptr t) b) = Function.update (ptrOf y) t b := by
  funext i
  by_cases h : i = t
  · subst h; simp [ptrOf]
  · simp only [ptrOf]
    rw [Function.update_of_ne (fun e => h (by cases e; rfl)), Function.update_of_ne h]
    rfl

theorem rangeM_update_low (lw : Word r) (n : ℕ) (s : Fin r) (y : Cfg (Wire a m r K))
    (t : Fin r) (ht : (t : ℕ) ≤ s) (b : Bool) :
    rangeM lw n s (Function.update y (ptrWires t) b) = rangeM lw n s y := by
  unfold rangeM
  rw [labOf_update_ne y _ b (fun _ h => by cases h)]
  simp only [ptrWires, ptrOf_update_ptr]
  unfold rangeLevel
  rw [wordValue_update_div_high (ptrOf y) t s ht b]

theorem RANGE1_pub (lw : Word r) (n : ℕ) (hn : 0 < n) (hnr : n ≤ 2 ^ r) (hr : 0 < r) (ψ : P) :
    RANGE1 (K := K) (m := m) (a := a) lw n (bas (pubCfg lw 0) ψ) = emb lw (uIn n ψ) := by
  rw [RANGE1, treeOp_bas ptrWires ptrWires_injective (rangeM lw n)
    (fun s y t ht b => rangeM_update_low lw n s y t ht b) (pubCfg lw 0)
    (fun t => by
      change (wordEquivFin r).symm (Fin.cast (cap_succ r) 0) t = false
      have h0 : Fin.cast (cap_succ r) (0 : Fin (cap r + 1)) = wordEquivFin r (zw r) := by
        apply Fin.ext; simp [GatePointerEncoding.wordValue, zw]
      rw [h0, Equiv.symm_apply_apply])]
  have hamp : ∀ w : Word r, (∏ s : Fin r, rangeM lw n s
      (setLow ptrWires r le_rfl (pubCfg (a := a) (m := m) (K := K) lw 0) w) (w s) false) =
        (uf n w : ℂ) := by
    intro w
    rw [setLow_ptr_pubCfg]
    have hp : ptrOf (pubCfg (a := a) (m := m) (K := K) lw (wIdx w)) = w := by
      rw [ptrOf_pubCfg, wIdx]; simp
    simp only [rangeM, labOf_pubCfg, if_true, hp]
    exact tree_telescope (uf n) hr (uf_mass_one n hn hnr)
      (fun s w => rangeLevel n s w (w s) false)
      (fun s w hlive => rangeLevel_col n hn hnr s w hlive (w s)) w
  simp only [hamp]
  rw [uIn, emb_public_sum]
  let e : Word r ≃ Fin (cap r + 1) := (wordEquivFin r).trans (finCongr (cap_succ r).symm)
  apply Fintype.sum_equiv e
  intro w
  have he : e w = wIdx w := rfl
  rw [he, setLow_ptr_pubCfg, ← bas_smul]
  congr 1
  have hv : ((wIdx w : Fin (cap r + 1)) : ℕ) = wordValue w := rfl
  rw [hv]
  simp only [uf, extendSequence]
  split_ifs with h
  · rw [uniformEmbedding_apply, uniformAmplitude]
  · simp

theorem treeFrom_rangeM_fix (lw : Word r) (n : ℕ) (k : ℕ) (hk : k ≤ r)
    (y : Cfg (Wire a m r K)) (hy : labOf y ≠ lw) (q : P) :
    treeFrom ptrWires (rangeM lw n) k hk (bas y q) = bas y q := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [treeFrom, comp_apply, condOp_bas]
      have h1 : rangeM lw n ⟨k, by omega⟩ (Function.update y (ptrWires ⟨k, by omega⟩) false) = 1 := by
        unfold rangeM
        rw [labOf_update_ne y _ false (fun _ h => by cases h), if_neg hy]
      rw [h1, Finset.sum_eq_single (y (ptrWires ⟨k, by omega⟩))]
      · rw [Function.update_eq_self, Matrix.one_apply_eq, one_smul, ih (by omega)]
      · intro b _ hb; rw [Matrix.one_apply_ne hb, zero_smul]
      · intro h; exact absurd (Finset.mem_univ _) h

theorem RANGE1_fix (lw : Word r) (n : ℕ) (ψ : Reg (Wire a m r K) P)
    (hψ : ∀ y, labOf y = lw → ψ y = 0) : RANGE1 lw n ψ = ψ := by
  rw [← sum_bas ψ, map_sum]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hy : labOf y = lw
  · rw [hψ y hy]
    have : bas y (0 : P) = (0 : Reg (Wire a m r K) P) := by
      apply PiLp.ext; intro x; simp
    rw [this, map_zero]
  · exact treeFrom_rangeM_fix lw n r le_rfl y hy _

omit [CompleteSpace P] in
theorem emb_supp (lw : Word r) (z : Model a m r P) (y : Cfg (Wire a m r K))
    (hy : labOf y ≠ lw) : emb (K := K) lw z y = 0 := by
  rw [emb_apply]
  exact embVal_unclean lw z y (fun h => hy h.1)

/-! ### All labels -/

/-- The word of a label value. -/
def labWord {L : ℕ} (hL : L ≤ 2 ^ r) (ℓ : Fin L) : Word r := (wordEquivFin r).symm (Fin.castLE hL ℓ)

theorem labWord_injective {L : ℕ} (hL : L ≤ 2 ^ r) : Function.Injective (labWord hL) := by
  intro ℓ ℓ' h
  have := congrArg (wordEquivFin r) h
  simp only [labWord, Equiv.apply_symm_apply] at this
  exact Fin.castLE_injective hL this

theorem wordValue_labWord {L : ℕ} (hL : L ≤ 2 ^ r) (ℓ : Fin L) :
    wordValue (labWord hL ℓ) = ℓ := by
  have := congrArg Fin.val ((wordEquivFin r).apply_symm_apply (Fin.castLE hL ℓ))
  exact this


/-- Uniform pointer states for the labels of a list. -/
def rangeL {L : ℕ} (hL : L ≤ 2 ^ r) (nOf : Fin L → ℕ) :
    List (Fin L) → Reg (Wire a m r K) P →L[ℂ] Reg (Wire a m r K) P
  | [] => 1
  | ℓ :: l => RANGE1 (labWord hL ℓ) (nOf ℓ) ∘L rangeL hL nOf l

theorem rangeL_pub {L : ℕ} (hL : L ≤ 2 ^ r) (nOf : Fin L → ℕ)
    (hn : ∀ ℓ, 0 < nOf ℓ ∧ nOf ℓ ≤ 2 ^ r) (hr : 0 < r) (l : List (Fin L)) (hl : l.Nodup)
    (ℓ₀ : Fin L) (ψ : P) :
    rangeL (K := K) (m := m) (a := a) hL nOf l (bas (pubCfg (labWord hL ℓ₀) 0) ψ) =
      if ℓ₀ ∈ l then emb (labWord hL ℓ₀) (uIn (nOf ℓ₀) ψ)
      else bas (pubCfg (labWord hL ℓ₀) 0) ψ := by
  induction l with
  | nil => simp [rangeL]
  | cons ℓ l ih =>
      have hl' := List.nodup_cons.mp hl
      rw [rangeL, comp_apply, ih hl'.2]
      by_cases he : ℓ = ℓ₀
      · subst he
        rw [if_neg hl'.1, if_pos List.mem_cons_self]
        exact RANGE1_pub _ _ (hn ℓ).1 (hn ℓ).2 hr ψ
      · have hne : labWord hL ℓ₀ ≠ labWord hL ℓ := fun h => he (labWord_injective hL h).symm
        have hmem : ℓ₀ ∈ ℓ :: l ↔ ℓ₀ ∈ l := by
          simp only [List.mem_cons]; constructor
          · rintro (h | h)
            · exact absurd h.symm he
            · exact h
          · exact Or.inr
        rw [if_congr hmem rfl rfl]
        split_ifs
        · exact RANGE1_fix _ _ _ (fun y hy => emb_supp _ _ y (by rw [hy]; exact hne.symm))
        · apply RANGE1_fix
          intro y hy
          rw [bas_apply, if_neg]
          intro e; rw [e, labOf_pubCfg] at hy; exact hne hy

/-- Uniform pointer states for all labels. -/
def RANGE {L : ℕ} (hL : L ≤ 2 ^ r) (nOf : Fin L → ℕ) :
    Reg (Wire a m r K) P →L[ℂ] Reg (Wire a m r K) P :=
  rangeL hL nOf (List.finRange L)

theorem RANGE_pub {L : ℕ} (hL : L ≤ 2 ^ r) (nOf : Fin L → ℕ)
    (hn : ∀ ℓ, 0 < nOf ℓ ∧ nOf ℓ ≤ 2 ^ r) (hr : 0 < r) (ℓ₀ : Fin L) (ψ : P) :
    RANGE (K := K) (m := m) (a := a) hL nOf (bas (pubCfg (labWord hL ℓ₀) 0) ψ) =
      emb (labWord hL ℓ₀) (uIn (nOf ℓ₀) ψ) := by
  rw [RANGE, rangeL_pub hL nOf hn hr _ (List.nodup_finRange L), if_pos (List.mem_finRange ℓ₀)]

/-! ### The label table -/

/-- The table rotation of label bit `s`. -/
def prepM (f : Word r → ℝ) (s : Fin r) (x : Cfg (Wire a m r K)) : Matrix Bool Bool ℂ :=
  treeMat f s (labOf x)

/-- Preparation of the label table with real amplitudes `f`. -/
def PREP (f : Word r → ℝ) : Reg (Wire a m r K) P →L[ℂ] Reg (Wire a m r K) P :=
  treeOp labWires (prepM f)

theorem labOf_update_lab (y : Cfg (Wire a m r K)) (t : Fin r) (b : Bool) :
    labOf (Function.update y (Wire.lab t) b) = Function.update (labOf y) t b := by
  funext i
  by_cases h : i = t
  · subst h; simp [labOf]
  · simp only [labOf]
    rw [Function.update_of_ne (fun e => h (by cases e; rfl)), Function.update_of_ne h]
    rfl

theorem PREP_zero (f : Word r → ℝ) (hf : ∑ w, f w ^ 2 = 1) (hr : 0 < r) (ψ : P) :
    PREP (K := K) (m := m) (a := a) f (bas (fun _ => false) ψ) =
      ∑ w, (f w : ℂ) • bas (pubCfg w 0) ψ := by
  rw [← pubCfg_zero (a := a) (m := m) (K := K), PREP,
    treeOp_bas labWires labWires_injective (prepM f)
      (fun s y t ht b => by
        simp only [prepM, labWires, labOf_update_lab]
        exact treeMat_update_low f s _ t ht b)
      (pubCfg (zw r) 0) (fun t => rfl)]
  apply Finset.sum_congr rfl
  intro w _
  rw [setLow_lab_pubCfg]
  congr 1
  simp only [prepM, labOf_pubCfg]
  exact tree_telescope f hr hf (fun s w => treeMat f s w (w s) false)
    (fun s w hlive => treeMat_col f s w hlive (w s)) w

/-! ### Table amplitudes from the signed weights -/

variable {L : ℕ}

/-- Square roots of the absolute weights. -/
def fIn (wt : Fin L → ℝ) (w : Word r) : ℝ :=
  if h : wordValue w < L then Real.sqrt (|wt ⟨wordValue w, h⟩| / 2) else 0

/-- Signed square roots of the absolute weights. -/
def fOut (wt : Fin L → ℝ) (w : Word r) : ℝ :=
  if h : wordValue w < L then
    (if wt ⟨wordValue w, h⟩ < 0 then -1 else 1) * Real.sqrt (|wt ⟨wordValue w, h⟩| / 2)
  else 0

theorem fIn_labWord (wt : Fin L → ℝ) (hL : L ≤ 2 ^ r) (ℓ : Fin L) :
    fIn wt (labWord hL ℓ) = Real.sqrt (|wt ℓ| / 2) := by
  unfold fIn
  rw [dif_pos (by rw [wordValue_labWord]; exact ℓ.isLt)]
  have : (⟨wordValue (labWord hL ℓ), by rw [wordValue_labWord]; exact ℓ.isLt⟩ : Fin L) = ℓ :=
    Fin.ext (wordValue_labWord hL ℓ)
  rw [this]

theorem fOut_labWord (wt : Fin L → ℝ) (hL : L ≤ 2 ^ r) (ℓ : Fin L) :
    fOut wt (labWord hL ℓ) = (if wt ℓ < 0 then -1 else 1) * Real.sqrt (|wt ℓ| / 2) := by
  unfold fOut
  rw [dif_pos (by rw [wordValue_labWord]; exact ℓ.isLt)]
  have : (⟨wordValue (labWord hL ℓ), by rw [wordValue_labWord]; exact ℓ.isLt⟩ : Fin L) = ℓ :=
    Fin.ext (wordValue_labWord hL ℓ)
  rw [this]

theorem fIn_eq_zero (wt : Fin L → ℝ) (hL : L ≤ 2 ^ r) (w : Word r)
    (hw : w ∉ Set.range (labWord hL)) : fIn wt w = 0 := by
  unfold fIn
  rw [dif_neg]
  intro h
  apply hw
  refine ⟨⟨wordValue w, h⟩, ?_⟩
  apply GatePointerEncoding.wordValue_injective
  rw [wordValue_labWord]

theorem fOut_eq_zero (wt : Fin L → ℝ) (hL : L ≤ 2 ^ r) (w : Word r)
    (hw : w ∉ Set.range (labWord hL)) : fOut wt w = 0 := by
  unfold fOut
  rw [dif_neg]
  intro h
  apply hw
  refine ⟨⟨wordValue w, h⟩, ?_⟩
  apply GatePointerEncoding.wordValue_injective
  rw [wordValue_labWord]

theorem sum_over_labels {M : Type*} [AddCommMonoid M] (hL : L ≤ 2 ^ r) (g : Word r → M)
    (hg : ∀ w, w ∉ Set.range (labWord hL) → g w = 0) :
    ∑ w, g w = ∑ ℓ, g (labWord hL ℓ) :=
  (Fintype.sum_of_injective (labWord hL) (labWord_injective hL) _ g hg (fun _ => rfl)).symm

theorem fIn_sq_sum (wt : Fin L → ℝ) (hwt : ∑ ℓ, |wt ℓ| = 2) (hL : L ≤ 2 ^ r) :
    ∑ w : Word r, fIn wt w ^ 2 = 1 := by
  rw [sum_over_labels hL _ (fun w hw => by rw [fIn_eq_zero wt hL w hw]; simp)]
  simp only [fIn_labWord, Real.sq_sqrt (div_nonneg (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2))]
  rw [← Finset.sum_div, hwt]
  norm_num

theorem fOut_sq_sum (wt : Fin L → ℝ) (hwt : ∑ ℓ, |wt ℓ| = 2) (hL : L ≤ 2 ^ r) :
    ∑ w : Word r, fOut wt w ^ 2 = 1 := by
  rw [sum_over_labels hL _ (fun w hw => by rw [fOut_eq_zero wt hL w hw]; simp)]
  have h : ∀ ℓ, fOut wt (labWord hL ℓ) ^ 2 = |wt ℓ| / 2 := by
    intro ℓ
    rw [fOut_labWord, mul_pow, Real.sq_sqrt (div_nonneg (abs_nonneg _) (by norm_num))]
    split_ifs <;> norm_num
  simp only [h]
  rw [← Finset.sum_div, hwt]
  norm_num

theorem fOut_mul_fIn (wt : Fin L → ℝ) (hL : L ≤ 2 ^ r) (ℓ : Fin L) :
    fOut wt (labWord hL ℓ) * fIn wt (labWord hL ℓ) = wt ℓ / 2 := by
  rw [fOut_labWord, fIn_labWord, mul_assoc,
    Real.mul_self_sqrt (div_nonneg (abs_nonneg _) (by norm_num))]
  split_ifs with h
  · rw [abs_of_neg h]; ring
  · rw [abs_of_nonneg (not_lt.mp h)]; ring

/-! ### The LCU block -/

omit [CompleteSpace P] in
theorem inner_emb_ne (lw lw' : Word r) (h : lw ≠ lw') (z z' : Model a m r P) :
    inner ℂ (emb (K := K) lw z) (emb lw' z') = 0 := by
  rw [PiLp.inner_apply]
  apply Finset.sum_eq_zero
  intro x _
  by_cases hx : labOf x = lw
  · rw [emb_supp lw' z' x (by rw [hx]; exact h), inner_zero_right]
  · rw [emb_supp lw z x hx, inner_zero_left]

theorem range_prep_zero (hL : L ≤ 2 ^ r) (nOf : Fin L → ℕ)
    (hn : ∀ ℓ, 0 < nOf ℓ ∧ nOf ℓ ≤ 2 ^ r) (hr : 0 < r) (f : Word r → ℝ)
    (hf : ∑ w, f w ^ 2 = 1) (hf0 : ∀ w, w ∉ Set.range (labWord hL) → f w = 0) (ψ : P) :
    RANGE (K := K) (m := m) (a := a) hL nOf (PREP f (bas (fun _ => false) ψ)) =
      ∑ ℓ, (f (labWord hL ℓ) : ℂ) • emb (labWord hL ℓ) (uIn (nOf ℓ) ψ) := by
  rw [PREP_zero f hf hr, map_sum]
  rw [sum_over_labels hL _ (fun w hw => by rw [hf0 w hw]; simp)]
  apply Finset.sum_congr rfl
  intro ℓ _
  rw [map_smul, RANGE_pub hL nOf hn hr ℓ ψ]

/-- The ideal LCU circuit. -/
def LCU (hL : L ≤ 2 ^ r) (nOf : Fin L → ℕ) (wt : Fin L → ℝ) (c σ : ℝ)
    (UJ D : Vsp a P →L[ℂ] Vsp a P) (N : ℕ) : Reg (Wire a m r K) P →L[ℂ] Reg (Wire a m r K) P :=
  (PREP (fOut wt))† ∘L (RANGE hL nOf)† ∘L selectN c σ UJ D N ∘L RANGE hL nOf ∘L PREP (fIn wt)

/-- **The LCU block.** Between clean inputs the LCU circuit is the signed
average of the coherent-reuse successful blocks. -/
theorem lcu_block (hL : L ≤ 2 ^ r) (nOf : Fin L → ℕ) (N : ℕ)
    (hn : ∀ ℓ, 0 < nOf ℓ ∧ nOf ℓ ≤ N) (hN : N ≤ cap r) (hr : 0 < r)
    (wt : Fin L → ℝ) (hwt : ∑ ℓ, |wt ℓ| = 2) (c κ σ : ℝ) (hunit : c ^ 2 + σ ^ 2 = 1)
    (hκ : κ = 1 - c) (UJ D : Vsp a P →L[ℂ] Vsp a P) (hUJ : UJ ∘L UJ† = 1) (ψ ψ' : P) :
    inner ℂ (bas (fun _ => false) ψ')
        (LCU (K := K) (m := m) hL nOf wt c σ UJ D N (bas (fun _ => false) ψ)) =
      inner ℂ ψ' ((∑ ℓ, ((wt ℓ / 2 : ℝ) : ℂ) • successfulBlock (V := HV a m P) (blkA c (2 ^ m))
        (netB (m := m) c σ UJ ∘L diagV D) (netC (m := m) c σ UJ)
        (netG (m := m) c κ σ UJ ∘L diagV D) (nOf ℓ)) ψ) := by
  have hn' : ∀ ℓ, 0 < nOf ℓ ∧ nOf ℓ ≤ 2 ^ r := fun ℓ =>
    ⟨(hn ℓ).1, by have := (hn ℓ).2; have := cap_succ r; omega⟩
  rw [LCU, comp_apply, comp_apply, comp_apply, comp_apply, adjoint_inner_right,
    adjoint_inner_right,
    range_prep_zero hL nOf hn' hr _ (fOut_sq_sum wt hwt hL) (fun w hw => fOut_eq_zero wt hL w hw),
    range_prep_zero hL nOf hn' hr _ (fIn_sq_sum wt hwt hL) (fun w hw => fIn_eq_zero wt hL w hw),
    map_sum]
  simp only [map_smul, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    Complex.conj_ofReal]
  rw [sum_apply, inner_sum]
  apply Finset.sum_congr rfl
  intro ℓ _
  rw [Finset.sum_eq_single ℓ]
  · rw [select_block c κ σ hunit hκ UJ D hUJ _ _ N (hn ℓ).2 hN ψ ψ', smul_apply,
      inner_smul_right, ← mul_assoc]
    congr 1
    rw [← fOut_mul_fIn wt hL ℓ]
    push_cast
    ring
  · intro ℓ' _ hne
    rw [selectN_emb c κ σ hunit hκ UJ D hUJ N,
      inner_emb_ne _ _ (fun h => hne (labWord_injective hL h)), mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

end

end SparseHamiltonian.GateCircuit.Sim
