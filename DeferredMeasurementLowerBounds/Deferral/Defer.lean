import DeferredMeasurementLowerBounds.Deferral.Align

set_option autoImplicit false

/-!
# Deferral of a measured algorithm

Manuscript: the end of the proof of Lemma `hsl:lem:precision` ("Purification and deferred
measurement") and the proof of Lemma `qlsl:lem:xor` ("coherent purification and padding to
their worst-case query count").

`defer` turns a measured algorithm into an aligned schedule over the selection family on
`Joint (Rec W k) K` (`k` record registers of width `W`):

* an instrument becomes its Halmos dilation on a fresh record register (`dilation`), the
  outcome copied coherently into the record; the continuations become the aligned merge of their
  schedules (`Sched.align`), each acting on the sector of its outcome, so classically controlled
  operations become record-controlled known unitaries and record-selected calls;
* a counted call becomes a counted slot, an uncounted call a weight-zero call in a free segment;
* `output` and `reject` add nothing.

The `j`-th counted calls of all branches share the slot `j`, one record-selected call of the
selection family (a record-controlled call, turned into the calls of each access model in
`Access`), so the number of slots is at most the worst-case number of counted calls over all
transcripts (`cost_defer`). On a fresh record the program prepares the **purification**
`purify`: the record of a transcript holds its outcomes and the workspace its unnormalised
branch vector (`eval_defer`), provided there are at least as many registers as instruments
along a transcript and every instrument fits in the register width.
-/

namespace DeferredMeasurementLowerBounds.Deferral

noncomputable section
open SparseHamiltonian SparseLowerBounds ContinuousLinearMap OracleCircuit
open DeferredMeasurementLowerBounds.Model
open scoped InnerProduct

variable {K E X L : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- **The deferred schedule** of a measured algorithm with `k` record registers of width `W`. -/
def defer (O : L → X → K →L[ℂ] K) (counted : L → Prop) [DecidablePred counted] (W : ℕ) :
    Measured O E → (k : ℕ) → Sched O counted (Rec W k)
  | .output _ _, _ => .empty
  | .reject, _ => .empty
  | .call l b next, k =>
      if h : counted l then .consSlot (fun _ => some (⟨l, h⟩, b)) (defer O counted W next k)
      else .prependFree (.query (.inr fun _ => some (⟨l, h⟩, b))) rfl (defer O counted W next k)
  | .instrument _ _ _ _, 0 => .empty
  | .instrument n A hA next, k + 1 =>
      if hn : n ≤ W then
        .prependFree (.fixed (dilation W k A) (dilation_unitary W k hn hA)) rfl
          (.align hn fun j => defer O counted W (next j) k)
      else .empty

/-- **The purification** of a measured algorithm: the record of a transcript holds its
outcomes and the workspace its unnormalised branch vector. -/
def purify {O : L → X → K →L[ℂ] K} (W : ℕ) : Measured O E → (k : ℕ) → X → K → Joint (Rec W k) K
  | .output _ _, k, _, φ => freshInj W k φ
  | .reject, k, _, φ => freshInj W k φ
  | .call l b next, k, x, φ => purify W next k x (queryOp O l b x φ)
  | .instrument _ _ _ _, 0, _, φ => freshInj W 0 φ
  | .instrument n A _ next, k + 1, x, φ =>
      (split W k K).symm (WithLp.toLp 2 fun v => match v with
        | none => 0
        | some v => if h : v.val < n then purify W (next ⟨v.val, h⟩) k x (A ⟨v.val, h⟩ φ) else 0)

variable {O : L → X → K →L[ℂ] K} {counted : L → Prop} [DecidablePred counted]

/-- A record-independent operator commutes with the fresh injection. -/
theorem fiber_const_freshInj (W k : ℕ) (U : K →L[ℂ] K) (φ : K) :
    Joint.fiber (fun _ : Rec W k => U) (freshInj W k φ) = freshInj W k (U φ) := by
  refine PiLp.ext fun r => ?_
  rw [Joint.fiber_apply, freshInj_apply, freshInj_apply]
  split_ifs <;> simp

/-- A call of the same label on every record acts on the fresh record as the call itself. -/
theorem patOp_const_freshInj (W k : ℕ) {L' : Type*} (O' : L' → X → K →L[ℂ] K) (l : L')
    (b : Bool) (x : X) (φ : K) :
    patOp O' (fun _ : Rec W k => some (l, b)) x (freshInj W k φ) =
      freshInj W k (queryOp O' l b x φ) :=
  fiber_const_freshInj W k _ φ

/-- **Padding to the worst case**: the number of counted slots is at most the worst-case number of
counted calls over all transcripts. -/
theorem len_defer_le (W : ℕ) (M : Measured O E) (k : ℕ) :
    (defer O counted W M k).len ≤ M.worstCost (countWeight counted) := by
  induction M generalizing k with
  | output out h => simp [defer, Sched.empty]
  | reject => simp [defer, Sched.empty]
  | call l b next ih =>
    have := ih k
    by_cases h : counted l
    · simp only [defer, dif_pos h, Measured.worstCost, countWeight, if_pos h]
      show (defer O counted W next k).len + 1 ≤ 1 + _
      omega
    · simp only [defer, dif_neg h, Measured.worstCost, countWeight, if_neg h]
      show (defer O counted W next k).len ≤ 0 + _
      omega
  | instrument n A _ next ih =>
    cases k with
    | zero => simp [defer, Sched.empty]
    | succ k =>
      by_cases hn : n ≤ W
      · simp only [defer, dif_pos hn, Measured.worstCost]
        show (Finset.univ.sup fun j => (defer O counted W (next j) k).len) ≤ _
        exact Finset.sup_mono_fun fun j _ => ih j k
      · simp [defer, dif_neg hn, Sched.empty]

/-- The deferred program makes at most the worst-case number of counted calls. -/
theorem cost_defer (W : ℕ) (M : Measured O E) (k : ℕ) :
    (defer O counted W M k).prog.cost selWeight ≤ M.worstCost (countWeight counted) := by
  rw [Sched.cost_prog]
  exact len_defer_le W M k

/-- **Deferred measurement**: on a fresh record the deferred program prepares the purification,
when every transcript has at most `k` instruments and every instrument at most `W` outcomes. -/
theorem eval_defer (W : ℕ) (M : Measured O E) (k : ℕ) (hd : M.depth ≤ k) (hw : M.width ≤ W)
    (x : X) (φ : K) :
    (defer O counted W M k).prog.eval x (freshInj W k φ) = purify W M k x φ := by
  induction M generalizing k φ with
  | output out h => simp [defer, purify, Sched.eval_empty]
  | reject => simp [defer, purify, Sched.eval_empty]
  | call l b next ih =>
    have hd' : next.depth ≤ k := hd
    have hw' : next.width ≤ W := hw
    by_cases h : counted l
    · simp only [defer, dif_pos h, Sched.eval_consSlot, mul_apply_eq_comp, purify]
      rw [show selFamily O counted (Rec W k) (.inl fun _ => some (⟨l, h⟩, b)) x =
        patOp (fun l : {l // counted l} => O l.1) (fun _ => some (⟨l, h⟩, b)) x from rfl,
        patOp_const_freshInj]
      exact ih k hd' hw' _
    · simp only [defer, dif_neg h, Sched.eval_prependFree, mul_apply_eq_comp, purify,
        MultiOracleCircuit.Program.eval_query]
      rw [show selFamily O counted (Rec W k) (.inr fun _ => some (⟨l, h⟩, b)) x =
        patOp (fun l : {l // ¬ counted l} => O l.1) (fun _ => some (⟨l, h⟩, b)) x from rfl,
        patOp_const_freshInj]
      exact ih k hd' hw' _
  | instrument n A _ next ih =>
    simp only [Measured.depth, Measured.width] at hd hw
    cases k with
    | zero => omega
    | succ k =>
      have hn : n ≤ W := le_trans (le_max_left _ _) hw
      have hdj : ∀ j, (next j).depth ≤ k := fun j =>
        le_trans (Finset.le_sup (f := fun j => (next j).depth) (Finset.mem_univ j)) (by omega)
      have hwj : ∀ j, (next j).width ≤ W := fun j =>
        le_trans (Finset.le_sup (f := fun j => (next j).width) (Finset.mem_univ j))
          (le_trans (le_max_right _ _) hw)
      simp only [defer, dif_pos hn, Sched.eval_prependFree, mul_apply_eq_comp,
        MultiOracleCircuit.Program.eval_fixed, Sched.eval_align,
        LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, purify]
      congr 1
      rw [LinearIsometryEquiv.symm_symm]
      refine PiLp.ext fun v => ?_
      rw [Joint.fiber_apply]
      rcases v with _ | v
      · have h0 : split W k K (dilation W k A (freshInj W (k + 1) φ)) none = 0 :=
          PiLp.ext fun r => by rw [dilation_freshInj W k A]; rfl
        rw [h0]
        simp
      · by_cases h : v.val < n
        · have h1 : split W k K (dilation W k A (freshInj W (k + 1) φ)) (some v) =
              freshInj W k (A ⟨v.val, h⟩ φ) :=
            PiLp.ext fun r => by rw [dilation_freshInj W k A]; simp only [dif_pos h]
          rw [h1]
          simp only [dif_pos h]
          exact ih _ k (hdj _) (hwj _) _
        · have h1 : split W k K (dilation W k A (freshInj W (k + 1) φ)) (some v) = 0 :=
            PiLp.ext fun r => by rw [dilation_freshInj W k A]; simp only [dif_neg h]; rfl
          rw [h1]
          simp [dif_neg h]

end

end DeferredMeasurementLowerBounds.Deferral
