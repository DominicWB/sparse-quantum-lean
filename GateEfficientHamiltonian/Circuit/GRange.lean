import GateEfficientHamiltonian.Circuit.GInc

/-!
# Gate-level uniform pointer preparation

For one label word `lw` and length `n < 2^r` the uniform pointer state is
prepared, on the label sector `lw`, by the binary tree of `RANGE1`: at pointer
bit `s` (top bit first) a Hadamard-type rotation, corrected to the tight
rotation when the higher pointer bits equal those of `n`.

Gates: the label flag `lf ← [label = lw]` (many-controlled NOT); for each bit
`s`, the tight flag `tf s ← tf (s+1) ∧ [ptr (s+1) = n_{s+1}]` (one Toffoli, the
higher bits being final), `hadC` controlled by `lf`, and
`tightRot n s · hadC†` controlled by `lf` and `tf s`; finally the tight flags
are erased from the bottom up and `lf` is erased.  `range1_agrees` proves the
agreement with `RANGE1 lw n` on clean configurations; `rangeL_agrees`
combines all labels.
-/

namespace SparseHamiltonian.GateCircuit.Sim

noncomputable section
open ContinuousLinearMap OracleCircuit
open scoped InnerProduct BigOperators
open GatePointerEncoding (wordValue wordEquivFin wordFin)

variable {a m r K : ℕ}
variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

theorem UnitaryMat.mul' {u v : Matrix Bool Bool ℂ} (hu : UnitaryMat u) (hv : UnitaryMat v) :
    UnitaryMat (u * v) := by
  constructor
  · rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc u.conjTranspose, hu.1,
      Matrix.one_mul, hv.1]
  · rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc v, hv.2, Matrix.one_mul,
      hu.2]

theorem UnitaryMat.conj' {u : Matrix Bool Bool ℂ} (hu : UnitaryMat u) : UnitaryMat u.conjTranspose := by
  constructor
  · rw [Matrix.conjTranspose_conjTranspose]; exact hu.2
  · rw [Matrix.conjTranspose_conjTranspose]; exact hu.1

theorem Agrees.mono {W Q : Type*} [Fintype W] [DecidableEq W] [NormedAddCommGroup Q]
    [InnerProductSpace ℂ Q] [CompleteSpace Q] {S S' : Cfg W → Prop}
    {C O : Reg W Q →L[ℂ] Reg W Q} (h : Agrees S' C O) (hS : ∀ x, S x → S' x) : Agrees S C O :=
  fun ψ hψ => h ψ (fun x hx => hψ x (fun h' => hx (hS x h')))

theorem wkClean_of_clean (x : Cfg (Wire a m r K)) (hx : Clean x) : WkClean x := by
  intro f hf
  obtain ⟨i, rfl⟩ := (mem_wkList f).mp hf
  exact hx _ rfl

/-! ### The label flag -/

/-- Literals of the label predicate. -/
def labLits (lw : Word r) : List (Wire a m r K × Bool) :=
  (List.finRange r).map (fun i => (Wire.lab i, lw i))

theorem labLits_length (lw : Word r) : (labLits (a := a) (m := m) (K := K) lw).length = r := by
  simp [labLits]

theorem mem_labLits (lw : Word r) (c : Wire a m r K × Bool) (hc : c ∈ labLits lw) :
    ∃ i, c.1 = Wire.lab i := by
  simp only [labLits, List.mem_map, List.mem_finRange, true_and] at hc
  obtain ⟨i, rfl⟩ := hc
  exact ⟨i, rfl⟩

theorem ctrlOK_labLits (lw : Word r) (x : Cfg (Wire a m r K)) :
    ctrlOK (labLits lw) x = decide (labOf x = lw) := by
  rw [Bool.eq_iff_iff, ctrlOK_iff, decide_eq_true_iff]
  constructor
  · intro h
    funext i
    exact h (Wire.lab i, lw i) (List.mem_map.mpr ⟨i, by simp, rfl⟩)
  · intro h c hc
    simp only [labLits, List.mem_map, List.mem_finRange, true_and] at hc
    obtain ⟨i, rfl⟩ := hc
    exact congrFun h i

/-- Compute (or erase) the label flag. -/
def lfC (lw : Word r) : List (Gate (Wire a m r K)) := mcGate (labLits lw) wkList Wire.lf pauliX

theorem labLits_ne_lf (lw : Word r) : ∀ l ∈ (labLits (a := a) (m := m) (K := K) lw), l.1 ≠ Wire.lf := by
  intro l hl
  obtain ⟨i, h⟩ := mem_labLits lw l hl
  rw [h]; simp

theorem labLits_ne_wk (lw : Word r) :
    ∀ l ∈ (labLits (a := a) (m := m) (K := K) lw), ∀ f ∈ wkList, l.1 ≠ f := by
  intro l hl f hf
  obtain ⟨i, rfl⟩ := (mem_wkList f).mp hf
  obtain ⟨k, h⟩ := mem_labLits lw l hl
  rw [h]; simp

theorem lfC_bas (lw : Word r) (hK : r ≤ K + 1) (y : Cfg (Wire a m r K)) (hy : WkClean y) (q : P) :
    gRun (lfC lw) (bas y q) = bas (flipCfg (labLits lw) Wire.lf y) q :=
  mcGate_pauliX_bas _ _ _ (by rw [labLits_length, wkList_length]; exact hK) wkList_nodup
    (labLits_ne_lf lw) (fun f hf => by obtain ⟨i, rfl⟩ := (mem_wkList f).mp hf; simp)
    (labLits_ne_wk lw) y hy q

theorem lfC_ok (lw : Word r) :
    ∀ g ∈ (lfC (a := a) (m := m) (K := K) lw), GateOK 2 g :=
  mcGate_valid _ _ _ _ pauliX_unitary wkList_nodup (labLits_ne_lf lw)
    (fun f hf => by obtain ⟨i, rfl⟩ := (mem_wkList f).mp hf; simp) (labLits_ne_wk lw)

theorem lfC_length (lw : Word r) : (lfC (a := a) (m := m) (K := K) lw).length ≤ 2 * r + 1 := by
  have := mcGate_length_le (labLits (a := a) (m := m) (K := K) lw) wkList Wire.lf pauliX
  rw [labLits_length] at this
  exact this

/-! ### Tight prefixes -/

/-- The pointer bits above `s` equal those of `n`. -/
def tightB (n s : ℕ) (w : Word r) : Bool := decide (∀ i : Fin r, s < i.val → w i = n.testBit i.val)

theorem tightB_top (n s : ℕ) (hs : r ≤ s + 1) (w : Word r) : tightB n s w = true := by
  unfold tightB
  rw [decide_eq_true_iff]
  intro i hi
  omega

theorem tightB_step (n s : ℕ) (hs : s + 1 < r) (w : Word r) :
    tightB n s w = (tightB n (s + 1) w && (w ⟨s + 1, hs⟩ == n.testBit (s + 1))) := by
  unfold tightB
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq]
  constructor
  · intro h
    exact ⟨fun i hi => h i (by omega), h ⟨s + 1, hs⟩ (by simp)⟩
  · rintro ⟨h1, h2⟩ i hi
    by_cases his : i.val = s + 1
    · have : i = ⟨s + 1, hs⟩ := Fin.ext his
      rw [this]; exact h2
    · exact h1 i (by omega)

/-- The tight predicate is equality of the higher values. -/
theorem tightB_iff (n s : ℕ) (hn : n < 2 ^ r) (w : Word r) :
    tightB n s w = true ↔ wordValue w / 2 ^ (s + 1) = n / 2 ^ (s + 1) := by
  unfold tightB
  rw [decide_eq_true_iff]
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_div_two_pow, Nat.testBit_div_two_pow]
    by_cases hj : j + (s + 1) < r
    · rw [testBit_wordValue w ⟨j + (s + 1), hj⟩]
      exact h ⟨j + (s + 1), hj⟩ (show s < j + (s + 1) by omega)
    · rw [testBit_wordValue_ge w _ (by omega),
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hn (Nat.pow_le_pow_right (by norm_num) (by omega)))]
  · intro h i hi
    have := congrArg (fun v => v.testBit (i.val - (s + 1))) h
    simp only [Nat.testBit_div_two_pow, Nat.sub_add_cancel (show s + 1 ≤ i.val by omega)] at this
    rwa [testBit_wordValue] at this

/-! ### Range annotations -/

/-- Annotation: the label flag and the tight flags `tf s` for `k ≤ s ≤ r-2`. -/
def rgAnn (lw : Word r) (n k : ℕ) (x : Cfg (Wire a m r K)) : Cfg (Wire a m r K) := fun w =>
  match w with
  | .lf => decide (labOf x = lw)
  | .tf s => decide (k ≤ s.val ∧ s.val + 2 ≤ r) && tightB n s.val (ptrOf x)
  | w => x w

section RgAnn

variable (lw : Word r) (n k : ℕ) (x : Cfg (Wire a m r K))

@[simp] theorem rgAnn_lf : rgAnn lw n k x .lf = decide (labOf x = lw) := rfl
@[simp] theorem rgAnn_tf (s : Fin r) :
    rgAnn lw n k x (.tf s) = (decide (k ≤ s.val ∧ s.val + 2 ≤ r) && tightB n s.val (ptrOf x)) := rfl
@[simp] theorem rgAnn_ptr (i : Fin r) : rgAnn lw n k x (.ptr i) = x (.ptr i) := rfl
@[simp] theorem rgAnn_lab (i : Fin r) : rgAnn lw n k x (.lab i) = x (.lab i) := rfl
@[simp] theorem rgAnn_wk (i : Fin K) : rgAnn lw n k x (.wk i) = x (.wk i) := rfl

end RgAnn

theorem rgAnn_succ (lw : Word r) (n s : ℕ) (hs : s + 2 ≤ r) (x : Cfg (Wire a m r K)) :
    rgAnn lw n s x =
      Function.update (rgAnn lw n (s + 1) x) (Wire.tf ⟨s, by omega⟩) (tightB n s (ptrOf x)) := by
  funext w
  by_cases hw : w = Wire.tf ⟨s, by omega⟩
  · subst hw
    simp only [rgAnn_tf, Function.update_self]
    rw [decide_eq_true (show s ≤ s ∧ s + 2 ≤ r by omega), Bool.true_and]
  · rw [Function.update_of_ne hw]
    cases w with
    | tf l =>
        have hl : l.val ≠ s := fun e => hw (by rw [show l = ⟨s, by omega⟩ from Fin.ext e])
        simp only [rgAnn_tf]
        congr 1
        rw [decide_eq_decide]
        omega
    | _ => rfl

theorem rgAnn_succ_eq (lw : Word r) (n s : ℕ) (hs : ¬ s + 2 ≤ r) (x : Cfg (Wire a m r K)) :
    rgAnn lw n (s + 1) x = rgAnn lw n s x := by
  funext w
  cases w with
  | tf l =>
      simp only [rgAnn_tf]
      congr 1
      rw [decide_eq_decide]
      omega
  | _ => rfl

/-- The tight-flag gate for bit `s` (an involution). -/
def tightG (n s : ℕ) (h : s + 2 ≤ r) : Gate (Wire a m r K) :=
  ⟨(if s + 3 ≤ r then [(Wire.tf ⟨s + 1, by omega⟩, true)] else []) ++
    [(Wire.ptr ⟨s + 1, by omega⟩, n.testBit (s + 1))], Wire.tf ⟨s, by omega⟩, pauliX⟩

theorem tightG_ht (n s : ℕ) (h : s + 2 ≤ r) :
    ∀ c ∈ (tightG (a := a) (m := m) (K := K) n s h).cs, c.1 ≠ (tightG n s h).t := by
  intro c hc
  simp only [tightG, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with hc | rfl
  · split_ifs at hc with h3
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      subst hc
      simp [tightG]
    · simp at hc
  · simp [tightG]

theorem tightG_ctrl (lw : Word r) (n s : ℕ) (h : s + 2 ≤ r) (x : Cfg (Wire a m r K)) :
    ctrlOK (tightG n s h).cs (rgAnn lw n (s + 1) x) = tightB n s (ptrOf x) := by
  rw [tightB_step n s (by omega)]
  unfold tightG
  split_ifs with h3
  · simp only [List.cons_append, List.nil_append, ctrlOK_cons, ctrlOK_nil, Bool.and_true,
      rgAnn_tf, rgAnn_ptr]
    rw [decide_eq_true (show s + 1 ≤ s + 1 ∧ s + 1 + 2 ≤ r by omega), Bool.true_and]
    simp only [beq_true]
    rfl
  · rw [tightB_top n (s + 1) (by omega)]
    simp only [List.nil_append, ctrlOK_cons, ctrlOK_nil, Bool.and_true, rgAnn_ptr, Bool.true_and]
    rfl

theorem tightG_flip_down (lw : Word r) (n s : ℕ) (h : s + 2 ≤ r) (x : Cfg (Wire a m r K)) :
    flipCfg (tightG n s h).cs (tightG n s h).t (rgAnn lw n (s + 1) x) = rgAnn lw n s x := by
  rw [flipCfg_eq_update, tightG_ctrl, rgAnn_succ lw n s h]
  congr 1
  simp only [tightG, rgAnn_tf]
  rw [decide_eq_false (show ¬ (s + 1 ≤ s ∧ s + 2 ≤ r) by omega), Bool.false_and, Bool.false_xor]

theorem tightG_flip_up (lw : Word r) (n s : ℕ) (h : s + 2 ≤ r) (x : Cfg (Wire a m r K)) :
    flipCfg (tightG n s h).cs (tightG n s h).t (rgAnn lw n s x) = rgAnn lw n (s + 1) x := by
  rw [← tightG_flip_down lw n s h x, flipCfg_flipCfg _ _ (tightG_ht n s h)]

/-- The tight gate, if bit `s` has a tight flag. -/
def tightL (n s : ℕ) : List (Gate (Wire a m r K)) := if h : s + 2 ≤ r then [tightG n s h] else []

theorem tightL_classical (lw : Word r) (n s : ℕ) (x : Cfg (Wire a m r K)) (q : P) :
    gRun (tightL n s) (bas (rgAnn lw n (s + 1) x) q) = bas (rgAnn lw n s x) q ∧
    gRun (tightL n s) (bas (rgAnn lw n s x) q) = bas (rgAnn lw n (s + 1) x) q := by
  unfold tightL
  split_ifs with h
  · rw [gRun_singleton, Gate.op]
    have hu : (tightG (a := a) (m := m) (K := K) n s h).u = pauliX := rfl
    rw [hu, gateOp_pauliX_bas _ _ (tightG_ht n s h), gateOp_pauliX_bas _ _ (tightG_ht n s h),
      tightG_flip_down, tightG_flip_up]
    exact ⟨rfl, rfl⟩
  · rw [rgAnn_succ_eq lw n s h]
    exact ⟨rfl, rfl⟩

/-! ### The rotations of one bit -/

/-- The two rotations of pointer bit `s`. -/
def bitG (n s : ℕ) (h : s < r) : List (Gate (Wire a m r K)) :=
  [⟨[(Wire.lf, true)], Wire.ptr ⟨s, h⟩, hadC⟩,
   ⟨[(Wire.lf, true)] ++ (if s + 2 ≤ r then [(Wire.tf ⟨s, h⟩, true)] else []), Wire.ptr ⟨s, h⟩,
      tightRot n s * hadC.conjTranspose⟩]

theorem rgAnn_update_ptr (lw : Word r) (n s : ℕ) (hs : s < r) (x : Cfg (Wire a m r K)) (b : Bool) :
    rgAnn lw n s (Function.update x (Wire.ptr ⟨s, hs⟩) b) =
      Function.update (rgAnn lw n s x) (Wire.ptr ⟨s, hs⟩) b := by
  funext w
  by_cases hw : w = Wire.ptr ⟨s, hs⟩
  · subst hw; simp
  · rw [Function.update_of_ne hw]
    cases w with
    | lf => simp only [rgAnn_lf]; rw [labOf_update_ne x _ b (fun _ h => by cases h)]
    | tf l =>
        simp only [rgAnn_tf]
        by_cases hl : s ≤ l.val ∧ l.val + 2 ≤ r
        · rw [decide_eq_true hl, Bool.true_and, Bool.true_and, ptrOf_update_ptr]
          unfold tightB
          rw [decide_eq_decide]
          constructor
          · intro h i hi
            have := h i hi
            rwa [Function.update_of_ne (fun e => by subst e; simp at hi; omega)] at this
          · intro h i hi
            rw [Function.update_of_ne (fun e => by subst e; simp at hi; omega)]
            exact h i hi
        · rw [decide_eq_false hl, Bool.false_and, Bool.false_and]
    | ptr l => simp only [rgAnn_ptr]; rw [Function.update_of_ne hw]
    | _ => simp only [rgAnn]; rw [Function.update_of_ne hw]

theorem tightB_update_ptr (n s : ℕ) (hs : s < r) (w : Word r) (b : Bool) :
    tightB n s (Function.update w ⟨s, hs⟩ b) = tightB n s w := by
  unfold tightB
  rw [decide_eq_decide]
  constructor
  · intro h i hi
    have := h i hi
    rwa [Function.update_of_ne (fun e => by subst e; simp at hi)] at this
  · intro h i hi
    rw [Function.update_of_ne (fun e => by subst e; simp at hi)]
    exact h i hi

theorem bitG_impl (lw : Word r) (n s : ℕ) (hs : s < r) (hn : n < 2 ^ r) :
    Impl Clean (rgAnn lw n s) (rgAnn lw n s) (gRun (Q := P) (bitG (a := a) (m := m) (K := K) n s hs))
      (condOp (ptrWires (a := a) (m := m) (K := K) ⟨s, hs⟩) (rangeM lw n ⟨s, hs⟩)) := by
  have hft : ∀ (x : Cfg (Wire a m r K)) (b : Bool), Clean x →
      rgAnn lw n s (Function.update x (Wire.ptr ⟨s, hs⟩) b) =
      Function.update (rgAnn lw n s x) (Wire.ptr ⟨s, hs⟩) b :=
    fun x b _ => rgAnn_update_ptr lw n s hs x b
  have h1 := Impl.gate (Q := P) (S := Clean) (f := rgAnn lw n s)
    [(Wire.lf, true)] (Wire.ptr ⟨s, hs⟩) hadC (by simp) (fun x => decide (labOf x = lw)) hft
    (fun x _ => by simp [ctrlOK_cons, ctrlOK_nil])
    (fun x b => by rw [labOf_update_ne x _ b (fun _ h => by cases h)])
  have h2 := Impl.gate (Q := P) (S := Clean) (f := rgAnn lw n s)
    ([(Wire.lf, true)] ++ (if s + 2 ≤ r then [(Wire.tf ⟨s, hs⟩, true)] else []))
    (Wire.ptr ⟨s, hs⟩) (tightRot n s * hadC.conjTranspose)
    (by intro c hc; split_ifs at hc <;> simp at hc <;> rcases hc with rfl | rfl <;> simp)
    (fun x => decide (labOf x = lw) && tightB n s (ptrOf x)) hft
    (fun x _ => by
      split_ifs with h
      · simp [ctrlOK_cons, ctrlOK_nil, h]
      · rw [tightB_top n s (by omega)]
        simp [ctrlOK_cons, ctrlOK_nil])
    (fun x b => by
      rw [labOf_update_ne x _ b (fun _ h => by cases h), ptrOf_update_ptr, tightB_update_ptr])
  have h12 := h1.comp (preserves_condOp _ _ _ (fun x b h => clean_update_of_logical x _ b rfl h)) h2
  rw [bitG, show ([⟨[(Wire.lf, true)], Wire.ptr ⟨s, hs⟩, hadC⟩,
      ⟨[(Wire.lf, true)] ++ (if s + 2 ≤ r then [(Wire.tf ⟨s, hs⟩, true)] else []), Wire.ptr ⟨s, hs⟩,
        tightRot n s * hadC.conjTranspose⟩] : List (Gate (Wire a m r K))) =
      [⟨[(Wire.lf, true)], Wire.ptr ⟨s, hs⟩, hadC⟩] ++
        [⟨[(Wire.lf, true)] ++ (if s + 2 ≤ r then [(Wire.tf ⟨s, hs⟩, true)] else []),
          Wire.ptr ⟨s, hs⟩, tightRot n s * hadC.conjTranspose⟩] from rfl,
    gRun_append, gRun_singleton, gRun_singleton]
  refine Impl.congr_ideal h12 ?_
  rw [condOp_comp]
  unfold ptrWires
  congr 1
  funext x
  unfold rangeM rangeLevel
  by_cases hl : labOf x = lw
  · simp only [hl, decide_true, if_true, Bool.true_and]
    have ht := tightB_iff (r := r) n s hn (ptrOf x)
    by_cases hT : tightB n s (ptrOf x) = true
    · rw [if_pos hT, if_pos (ht.mp hT), Matrix.mul_assoc, hadC_unitary.1, Matrix.mul_one]
    · rw [if_neg hT, if_neg (fun e => hT (ht.mpr e)), Matrix.one_mul]
  · simp [hl]

/-! ### One label -/

/-- Rotations of pointer bits `k-1, …, 0` with the tight flags computed on the way. -/
def rangeCore (n : ℕ) : ℕ → List (Gate (Wire a m r K))
  | 0 => []
  | k + 1 => tightL n k ++ (if h : k < r then bitG n k h else []) ++ rangeCore n k

/-- Erase the tight flags `0, …, k-1`. -/
def tightUp (n : ℕ) : ℕ → List (Gate (Wire a m r K))
  | 0 => []
  | k + 1 => tightUp n k ++ tightL n k

theorem rangeCore_impl (lw : Word r) (n : ℕ) (hn : n < 2 ^ r) (k : ℕ) (hk : k ≤ r) :
    Impl Clean (rgAnn lw n k) (rgAnn lw n 0) (gRun (Q := P) (rangeCore (a := a) (m := m) (K := K) n k))
      (treeFrom (ptrWires (a := a) (m := m) (K := K)) (rangeM lw n) k hk) := by
  induction k with
  | zero => exact Impl.one _
  | succ k ih =>
      rw [rangeCore, gRun_append, gRun_append, treeFrom, dif_pos (show k < r by omega)]
      have ht : Impl Clean (rgAnn lw n (k + 1)) (rgAnn lw n k) (gRun (Q := P)
          (tightL (a := a) (m := m) (K := K) n k)) 1 :=
        Impl.of_classical _ (fun x _ q => (tightL_classical lw n k x q).1)
      have hb := bitG_impl (P := P) (a := a) (m := m) (K := K) lw n k (by omega) hn
      have hrest := ih (by omega)
      have h1 := ht.comp (Preserves.one _) hb
      have h2 := h1.comp (preserves_condOp _ _ _
        (fun x b h => clean_update_of_logical x _ b rfl h)) hrest
      exact Impl.congr_ideal h2 (by rw [comp_one'])

theorem tightUp_impl (lw : Word r) (n : ℕ) (k : ℕ) :
    Impl Clean (rgAnn lw n 0) (rgAnn lw n k) (gRun (Q := P) (tightUp (a := a) (m := m) (K := K) n k)) 1 := by
  induction k with
  | zero => exact Impl.one _
  | succ k ih =>
      rw [tightUp, gRun_append]
      have ht : Impl Clean (rgAnn lw n k) (rgAnn lw n (k + 1)) (gRun (Q := P)
          (tightL (a := a) (m := m) (K := K) n k)) 1 :=
        Impl.of_classical _ (fun x _ q => (tightL_classical lw n k x q).2)
      exact Impl.congr_ideal (ih.comp (Preserves.one _) ht) (one_comp' _)

theorem flip_lf_clean (lw : Word r) (n : ℕ) (x : Cfg (Wire a m r K)) (hx : Clean x) :
    flipCfg (labLits lw) Wire.lf x = rgAnn lw n r x := by
  rw [flipCfg_eq_update, ctrlOK_labLits, hx Wire.lf rfl, Bool.false_xor]
  funext w
  by_cases hw : w = Wire.lf
  · subst hw; simp
  · rw [Function.update_of_ne hw]
    cases w with
    | lf => exact absurd rfl hw
    | tf l =>
        simp only [rgAnn_tf]
        rw [hx _ rfl, decide_eq_false (show ¬ (r ≤ l.val ∧ l.val + 2 ≤ r) by omega), Bool.false_and]
    | _ => rfl

theorem flip_lf_back (lw : Word r) (n : ℕ) (x : Cfg (Wire a m r K)) (hx : Clean x) :
    flipCfg (labLits lw) Wire.lf (rgAnn lw n r x) = x := by
  rw [← flip_lf_clean lw n x hx, flipCfg_flipCfg _ _ (labLits_ne_lf lw)]

/-- Gate list preparing the uniform pointer state of length `n` on label `lw`. -/
def range1G (lw : Word r) (n : ℕ) : List (Gate (Wire a m r K)) :=
  lfC lw ++ rangeCore n r ++ tightUp n r ++ lfC lw

theorem range1_agrees (lw : Word r) (n : ℕ) (hn : n < 2 ^ r) (hK : r ≤ K + 1) :
    Agrees Clean (gRun (Q := P) (range1G (a := a) (m := m) (K := K) lw n))
      (RANGE1 (K := K) (m := m) (a := a) (P := P) lw n) := by
  apply Impl.toAgrees
  rw [range1G, gRun_append, gRun_append, gRun_append, RANGE1, treeOp]
  have h1 : Impl Clean (fun x => x) (rgAnn lw n r) (gRun (Q := P) (lfC (a := a) (m := m) (K := K) lw)) 1 :=
    Impl.of_classical _ (fun x hx q => by
      rw [lfC_bas lw hK x (wkClean_of_clean x hx), flip_lf_clean lw n x hx])
  have h4 : Impl Clean (rgAnn lw n r) (fun x => x) (gRun (Q := P) (lfC (a := a) (m := m) (K := K) lw)) 1 :=
    Impl.of_classical _ (fun x hx q => by
      rw [lfC_bas lw hK _ (fun f hf => by
        obtain ⟨i, rfl⟩ := (mem_wkList f).mp hf; exact hx _ rfl), flip_lf_back lw n x hx])
  have h2 := rangeCore_impl (P := P) (a := a) (m := m) (K := K) lw n hn r le_rfl
  have h3 := tightUp_impl (P := P) (a := a) (m := m) (K := K) lw n r
  have h34 := h3.comp (Preserves.one _) h4
  have h234 := h2.comp (pres2_treeFrom _ (fun _ => rfl) _ _ _).1 h34
  have h1234 := h1.comp (Preserves.one _) h234
  refine Impl.congr_ideal h1234 ?_
  ext v
  rfl

/-! ### All labels -/

/-- Gate list of `rangeL`. -/
def rangeLG {L : ℕ} (hL : L ≤ 2 ^ r) (nOf : Fin L → ℕ) : List (Fin L) → List (Gate (Wire a m r K))
  | [] => []
  | ℓ :: l => rangeLG hL nOf l ++ range1G (labWord hL ℓ) (nOf ℓ)

theorem rangeLG_agrees {L : ℕ} (hL : L ≤ 2 ^ r) (nOf : Fin L → ℕ) (hn : ∀ ℓ, nOf ℓ < 2 ^ r)
    (hK : r ≤ K + 1) (l : List (Fin L)) :
    Agrees Clean (gRun (Q := P) (rangeLG (a := a) (m := m) (K := K) hL nOf l))
      (rangeL (K := K) (m := m) (a := a) (P := P) hL nOf l) := by
  induction l with
  | nil => exact Agrees.refl _ _
  | cons ℓ l ih =>
      rw [rangeLG, gRun_append, rangeL]
      exact ih.comp (pres2_rangeL _ _ _).1 (range1_agrees _ _ (hn ℓ) hK)

/-- Gate list of `RANGE`. -/
def rangeG {L : ℕ} (hL : L ≤ 2 ^ r) (nOf : Fin L → ℕ) : List (Gate (Wire a m r K)) :=
  rangeLG hL nOf (List.finRange L)

theorem range_agrees {L : ℕ} (hL : L ≤ 2 ^ r) (nOf : Fin L → ℕ) (hn : ∀ ℓ, nOf ℓ < 2 ^ r)
    (hK : r ≤ K + 1) :
    Agrees Clean (gRun (Q := P) (rangeG (a := a) (m := m) (K := K) hL nOf))
      (RANGE (K := K) (m := m) (a := a) (P := P) hL nOf) :=
  rangeLG_agrees hL nOf hn hK _

/-! ### Validity and counts -/

theorem tightL_ok (n s : ℕ) : ∀ g ∈ (tightL (a := a) (m := m) (r := r) (K := K) n s), GateOK 2 g := by
  intro g hg
  unfold tightL at hg
  split_ifs at hg with h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    subst hg
    refine ⟨?_, tightG_ht n s h, pauliX_unitary⟩
    simp only [tightG, List.length_append, List.length_cons, List.length_nil]
    split_ifs <;> simp
  · simp at hg

theorem bitG_ok (n s : ℕ) (h : s < r) :
    ∀ g ∈ (bitG (a := a) (m := m) (K := K) n s h), GateOK 2 g := by
  intro g hg
  simp only [bitG, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · exact ⟨by simp, by simp, hadC_unitary⟩
  · refine ⟨by split_ifs <;> simp, ?_, UnitaryMat.mul' (tightRot_unitary n s) (UnitaryMat.conj' hadC_unitary)⟩
    intro c hc
    split_ifs at hc <;> simp at hc <;> rcases hc with rfl | rfl <;> simp

theorem rangeCore_ok (n : ℕ) (k : ℕ) :
    ∀ g ∈ (rangeCore (a := a) (m := m) (r := r) (K := K) n k), GateOK 2 g := by
  induction k with
  | zero => intro g hg; simp [rangeCore] at hg
  | succ k ih =>
      intro g hg
      rw [rangeCore, List.mem_append, List.mem_append] at hg
      rcases hg with (hg | hg) | hg
      · exact tightL_ok n k g hg
      · split_ifs at hg with h
        · exact bitG_ok n k h g hg
        · simp at hg
      · exact ih g hg

theorem tightUp_ok (n : ℕ) (k : ℕ) :
    ∀ g ∈ (tightUp (a := a) (m := m) (r := r) (K := K) n k), GateOK 2 g := by
  induction k with
  | zero => intro g hg; simp [tightUp] at hg
  | succ k ih =>
      intro g hg
      rw [tightUp, List.mem_append] at hg
      rcases hg with hg | hg
      · exact ih g hg
      · exact tightL_ok n k g hg

theorem range1G_ok (lw : Word r) (n : ℕ) :
    ∀ g ∈ (range1G (a := a) (m := m) (K := K) lw n), GateOK 2 g := by
  intro g hg
  simp only [range1G, List.mem_append] at hg
  rcases hg with ((hg | hg) | hg) | hg
  · exact lfC_ok lw g hg
  · exact rangeCore_ok n r g hg
  · exact tightUp_ok n r g hg
  · exact lfC_ok lw g hg

theorem tightL_length (n s : ℕ) : (tightL (a := a) (m := m) (r := r) (K := K) n s).length ≤ 1 := by
  unfold tightL; split_ifs <;> simp

theorem rangeCore_length (n k : ℕ) :
    (rangeCore (a := a) (m := m) (r := r) (K := K) n k).length ≤ 3 * k := by
  induction k with
  | zero => simp [rangeCore]
  | succ k ih =>
      rw [rangeCore, List.length_append, List.length_append]
      have h1 := tightL_length (a := a) (m := m) (r := r) (K := K) n k
      have h2 : (if h : k < r then bitG (a := a) (m := m) (K := K) n k h else []).length ≤ 2 := by
        split_ifs <;> simp [bitG]
      omega

theorem tightUp_length (n k : ℕ) : (tightUp (a := a) (m := m) (r := r) (K := K) n k).length ≤ k := by
  induction k with
  | zero => simp [tightUp]
  | succ k ih =>
      rw [tightUp, List.length_append]
      have := tightL_length (a := a) (m := m) (r := r) (K := K) n k
      omega

theorem range1G_length (lw : Word r) (n : ℕ) :
    (range1G (a := a) (m := m) (K := K) lw n).length ≤ 8 * r + 2 := by
  simp only [range1G, List.length_append]
  have := lfC_length (a := a) (m := m) (K := K) lw
  have := rangeCore_length (a := a) (m := m) (r := r) (K := K) n r
  have := tightUp_length (a := a) (m := m) (r := r) (K := K) n r
  omega

theorem rangeLG_ok {L : ℕ} (hL : L ≤ 2 ^ r) (nOf : Fin L → ℕ) (l : List (Fin L)) :
    ∀ g ∈ (rangeLG (a := a) (m := m) (K := K) hL nOf l), GateOK 2 g := by
  induction l with
  | nil => intro g hg; simp [rangeLG] at hg
  | cons ℓ l ih =>
      intro g hg
      rw [rangeLG, List.mem_append] at hg
      rcases hg with hg | hg
      · exact ih g hg
      · exact range1G_ok _ _ g hg

theorem rangeLG_length {L : ℕ} (hL : L ≤ 2 ^ r) (nOf : Fin L → ℕ) (l : List (Fin L)) :
    (rangeLG (a := a) (m := m) (K := K) hL nOf l).length ≤ l.length * (8 * r + 2) := by
  induction l with
  | nil => simp [rangeLG]
  | cons ℓ l ih =>
      rw [rangeLG, List.length_append, List.length_cons]
      have := range1G_length (a := a) (m := m) (K := K) (labWord hL ℓ) (nOf ℓ)
      nlinarith

theorem rangeG_length {L : ℕ} (hL : L ≤ 2 ^ r) (nOf : Fin L → ℕ) :
    (rangeG (a := a) (m := m) (K := K) hL nOf).length ≤ L * (8 * r + 2) := by
  have := rangeLG_length (a := a) (m := m) (K := K) hL nOf (List.finRange L)
  rwa [List.length_finRange] at this

end

end SparseHamiltonian.GateCircuit.Sim
