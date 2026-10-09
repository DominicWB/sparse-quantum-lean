import GateEfficientHamiltonian.Circuit.Impl

/-!
# Gate-level boundary network

The boundary network at pointer word `j` is implemented by elementary gates:

* the enable flag `hf ← [ancillas zero ∧ pointer = j]` by a many-controlled NOT;
* each dyadic frame by one rotation per slot bit, controlled by `hf`, the
  private sector and the prefix flag `pf (i-1) = [slot bits 0..i-1 zero]`; the
  prefix flags form an AND chain, computed and erased in step with the frame
  so that every flag is read only while its slot bits are unchanged;
* the central sector rotation by a many-controlled gate on `hf` and the zero
  slot word;
* `hf` is erased by the same many-controlled NOT.

`net_agrees` proves that this list agrees with the ideal network `NET` on clean
configurations, and `bnet_agrees` adds the two sector-controlled `U_J` calls.
The list has at most `4(a+r) + 8m + 5` gates, each with at most three controls.
-/

namespace SparseHamiltonian.GateCircuit.Sim

noncomputable section
open ContinuousLinearMap OracleCircuit
open scoped InnerProduct BigOperators
open GatePointerEncoding (wordValue wordEquivFin wordFin)
open GateDyadicBoundary (centralCosine centralSine)

variable {a m r K : ℕ}
variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-! ### Generic facts -/

theorem flipCfg_eq_update {W : Type*} [DecidableEq W] (cs : List (W × Bool)) (t : W)
    (y : Cfg W) : flipCfg cs t y = Function.update y t (xor (y t) (ctrlOK cs y)) := by
  unfold flipCfg
  cases h : ctrlOK cs y
  · simp
  · simp

theorem one_comp' {W Q : Type*} [Fintype W] [NormedAddCommGroup Q] [InnerProductSpace ℂ Q]
    (A : Reg W Q →L[ℂ] Reg W Q) : (1 : Reg W Q →L[ℂ] Reg W Q) ∘L A = A := by
  ext v; rfl

theorem comp_one' {W Q : Type*} [Fintype W] [NormedAddCommGroup Q] [InnerProductSpace ℂ Q]
    (A : Reg W Q →L[ℂ] Reg W Q) : A ∘L (1 : Reg W Q →L[ℂ] Reg W Q) = A := by
  ext v; rfl

theorem gRun_singleton_op (g : Gate (Wire a m r K)) :
    gRun (Q := P) [g] = gateOp g.cs g.t g.u := gRun_singleton g

/-! ### The work pool -/

/-- The pool of AND-chain flags. -/
def wkList : List (Wire a m r K) := (List.finRange K).map Wire.wk

theorem wkList_nodup : (wkList (a := a) (m := m) (r := r) (K := K)).Nodup :=
  (List.nodup_finRange K).map (fun _ _ h => by cases h; rfl)

theorem mem_wkList (w : Wire a m r K) : w ∈ wkList ↔ ∃ i, w = Wire.wk i := by
  simp only [wkList, List.mem_map, List.mem_finRange, true_and]
  constructor
  · rintro ⟨i, rfl⟩; exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩; exact ⟨i, rfl⟩

theorem wkList_length : (wkList (a := a) (m := m) (r := r) (K := K)).length = K := by
  simp [wkList]

theorem clean_wk (x : Cfg (Wire a m r K)) (hx : Clean x) : ∀ f ∈ wkList, x f = false := by
  intro f hf
  obtain ⟨i, rfl⟩ := (mem_wkList f).mp hf
  exact hx _ rfl

/-! ### The enable flag -/

/-- The pointer word of a pointer index. -/
def ptrWord (j : Fin (cap r + 1)) : Word r := (wordEquivFin r).symm (Fin.cast (cap_succ r) j)

theorem ptrIdx_eq_iff (x : Cfg (Wire a m r K)) (j : Fin (cap r + 1)) :
    ptrIdx x = j ↔ ptrOf x = ptrWord j := by
  unfold ptrIdx ptrWord
  constructor
  · intro h
    rw [← h]
    simp
  · intro h
    rw [h]
    simp

/-- Literals of the enable predicate. -/
def hfLits (j : Fin (cap r + 1)) : List (Wire a m r K × Bool) :=
  (List.finRange a).map (fun i => (Wire.anc i, false)) ++
    (List.finRange r).map (fun i => (Wire.ptr i, ptrWord j i))

/-- The enable predicate. -/
def hfB (j : Fin (cap r + 1)) (x : Cfg (Wire a m r K)) : Bool :=
  decide (ancOf x = zw a ∧ ptrIdx x = j)

theorem ctrlOK_hfLits (j : Fin (cap r + 1)) (x : Cfg (Wire a m r K)) :
    ctrlOK (hfLits j) x = hfB j x := by
  unfold hfB
  rw [Bool.eq_iff_iff, ctrlOK_iff, decide_eq_true_iff, ptrIdx_eq_iff]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · funext i
      exact h (Wire.anc i, false) (List.mem_append_left _ (List.mem_map.mpr ⟨i, by simp, rfl⟩))
    · funext i
      exact h (Wire.ptr i, ptrWord j i)
        (List.mem_append_right _ (List.mem_map.mpr ⟨i, by simp, rfl⟩))
  · rintro ⟨ha, hp⟩ c hc
    simp only [hfLits, List.mem_append, List.mem_map, List.mem_finRange, true_and] at hc
    rcases hc with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exact congrFun ha i
    · exact congrFun hp i

theorem hfLits_length (j : Fin (cap r + 1)) :
    (hfLits (a := a) (m := m) (K := K) j).length = a + r := by
  simp [hfLits]

theorem mem_hfLits (j : Fin (cap r + 1)) (c : Wire a m r K × Bool) (hc : c ∈ hfLits j) :
    (∃ i, c.1 = Wire.anc i) ∨ (∃ i, c.1 = Wire.ptr i) := by
  simp only [hfLits, List.mem_append, List.mem_map, List.mem_finRange, true_and] at hc
  rcases hc with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · exact Or.inl ⟨i, rfl⟩
  · exact Or.inr ⟨i, rfl⟩

/-! ### Frame annotations -/

/-- Prefix predicate: slot bits `0, …, k` vanish. -/
def pfB (k : Fin m) (x : Cfg (Wire a m r K)) : Bool :=
  decide (∀ l : Fin m, l.val ≤ k.val → x (Wire.slot l) = false)

/-- Annotation with the enable flag and the prefix flags `pf k`, `k < n`. -/
def frAnn (j : Fin (cap r + 1)) (n : ℕ) (x : Cfg (Wire a m r K)) : Cfg (Wire a m r K) :=
  fun w => match w with
  | .hf => hfB j x
  | .pf k => decide (k.val < n) && pfB k x
  | w => x w

section FrAnn

variable (j : Fin (cap r + 1)) (n : ℕ) (x : Cfg (Wire a m r K))

@[simp] theorem frAnn_hf : frAnn j n x .hf = hfB j x := rfl
@[simp] theorem frAnn_pf (k : Fin m) : frAnn j n x (.pf k) = (decide (k.val < n) && pfB k x) := rfl
@[simp] theorem frAnn_sec : frAnn j n x .sec = x .sec := rfl
@[simp] theorem frAnn_slot (i : Fin m) : frAnn j n x (.slot i) = x (.slot i) := rfl
@[simp] theorem frAnn_anc (i : Fin a) : frAnn j n x (.anc i) = x (.anc i) := rfl
@[simp] theorem frAnn_ptr (i : Fin r) : frAnn j n x (.ptr i) = x (.ptr i) := rfl
@[simp] theorem frAnn_lab (i : Fin r) : frAnn j n x (.lab i) = x (.lab i) := rfl
@[simp] theorem frAnn_lf : frAnn j n x .lf = x .lf := rfl
@[simp] theorem frAnn_tf (i : Fin r) : frAnn j n x (.tf i) = x (.tf i) := rfl
@[simp] theorem frAnn_cf (i : Fin r) : frAnn j n x (.cf i) = x (.cf i) := rfl
@[simp] theorem frAnn_wk (i : Fin K) : frAnn j n x (.wk i) = x (.wk i) := rfl

theorem ancOf_frAnn : ancOf (frAnn j n x) = ancOf x := rfl
theorem ptrOf_frAnn : ptrOf (frAnn j n x) = ptrOf x := rfl
theorem ptrIdx_frAnn : ptrIdx (frAnn j n x) = ptrIdx x := rfl
theorem slotOf_frAnn : slotOf (frAnn j n x) = slotOf x := rfl

end FrAnn

theorem hfB_update_slot (j : Fin (cap r + 1)) (x : Cfg (Wire a m r K)) (i : Fin m) (b : Bool) :
    hfB j (Function.update x (Wire.slot i) b) = hfB j x := by
  unfold hfB
  rw [ancOf_update_ne x _ b (fun _ h => by cases h), ptrIdx_update_ne x _ b (fun _ h => by cases h)]

theorem hfB_update_sec (j : Fin (cap r + 1)) (x : Cfg (Wire a m r K)) (b : Bool) :
    hfB j (Function.update x Wire.sec b) = hfB j x := by
  unfold hfB
  rw [ancOf_update_ne x _ b (fun _ h => by cases h), ptrIdx_update_ne x _ b (fun _ h => by cases h)]

theorem pfB_update_slot (k i : Fin m) (hki : k.val < i.val) (x : Cfg (Wire a m r K)) (b : Bool) :
    pfB k (Function.update x (Wire.slot i) b) = pfB k x := by
  unfold pfB
  rw [decide_eq_decide]
  constructor
  · intro h l hl
    have := h l hl
    rwa [Function.update_of_ne (fun e => by cases e; omega)] at this
  · intro h l hl
    rw [Function.update_of_ne (fun e => by cases e; omega)]
    exact h l hl

theorem pfB_update_sec (k : Fin m) (x : Cfg (Wire a m r K)) (b : Bool) :
    pfB k (Function.update x Wire.sec b) = pfB k x := by
  unfold pfB
  rw [decide_eq_decide]
  constructor
  · intro h l hl
    have := h l hl
    rwa [Function.update_of_ne (fun e => by cases e)] at this
  · intro h l hl
    rw [Function.update_of_ne (fun e => by cases e)]
    exact h l hl

theorem pfB_zero (h : 0 < m) (x : Cfg (Wire a m r K)) :
    pfB ⟨0, h⟩ x = !(x (Wire.slot ⟨0, h⟩)) := by
  unfold pfB
  cases hx : x (Wire.slot ⟨0, h⟩)
  · simp only [Bool.not_false, decide_eq_true_eq]
    intro l hl
    have hl' : l.val ≤ 0 := hl
    have : l = ⟨0, h⟩ := Fin.ext (show l.val = 0 by omega)
    rw [this]; exact hx
  · simp only [Bool.not_true, decide_eq_false_iff_not, not_forall]
    exact ⟨⟨0, h⟩, le_rfl, by rw [hx]; simp⟩

theorem pfB_succ (k : ℕ) (h : k + 1 < m) (x : Cfg (Wire a m r K)) :
    pfB ⟨k + 1, h⟩ x = (pfB ⟨k, by omega⟩ x && !(x (Wire.slot ⟨k + 1, h⟩))) := by
  unfold pfB
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true']
  constructor
  · intro hall
    exact ⟨fun l hl => hall l (Nat.le_succ_of_le hl), hall ⟨k + 1, h⟩ le_rfl⟩
  · rintro ⟨hall, hk⟩ l hl
    by_cases hlk : l.val = k + 1
    · have : l = ⟨k + 1, h⟩ := Fin.ext hlk
      rw [this]; exact hk
    · have h1 : l.val ≤ k + 1 := hl
      exact hall l (show l.val ≤ k by omega)

/-- The annotation with one more prefix flag. -/
theorem frAnn_succ (j : Fin (cap r + 1)) (k : ℕ) (hk : k < m) (x : Cfg (Wire a m r K)) :
    frAnn j (k + 1) x = Function.update (frAnn j k x) (Wire.pf ⟨k, hk⟩) (pfB ⟨k, hk⟩ x) := by
  funext w
  by_cases hw : w = Wire.pf ⟨k, hk⟩
  · subst hw
    simp
  · rw [Function.update_of_ne hw]
    cases w with
    | pf l =>
        have hl : l.val ≠ k := fun e => hw (by rw [show l = ⟨k, hk⟩ from Fin.ext e])
        simp only [frAnn_pf]
        congr 1
        rw [decide_eq_decide]
        omega
    | _ => rfl

/-! ### Prefix-chain and rotation gates -/

/-- The chain gate computing prefix flag `pf k` (an involution). -/
def compG : (k : ℕ) → k < m → Gate (Wire a m r K)
  | 0, h => ⟨[(Wire.slot ⟨0, h⟩, false)], Wire.pf ⟨0, h⟩, pauliX⟩
  | k + 1, h => ⟨[(Wire.pf ⟨k, by omega⟩, true), (Wire.slot ⟨k + 1, h⟩, false)],
      Wire.pf ⟨k + 1, h⟩, pauliX⟩

theorem compG_t (k : ℕ) (hk : k < m) : (compG (a := a) (r := r) (K := K) k hk).t = Wire.pf ⟨k, hk⟩ := by
  cases k <;> rfl

theorem compG_u (k : ℕ) (hk : k < m) : (compG (a := a) (r := r) (K := K) k hk).u = pauliX := by
  cases k <;> rfl

theorem compG_ht (k : ℕ) (hk : k < m) :
    ∀ c ∈ (compG (a := a) (r := r) (K := K) k hk).cs, c.1 ≠ (compG k hk).t := by
  cases k with
  | zero => intro c hc; simp [compG] at hc; subst hc; simp [compG]
  | succ k =>
      intro c hc
      simp only [compG, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> simp [compG]

theorem compG_ctrl (j : Fin (cap r + 1)) (k : ℕ) (hk : k < m) (x : Cfg (Wire a m r K)) :
    ctrlOK (compG k hk).cs (frAnn j k x) = pfB ⟨k, hk⟩ x := by
  cases k with
  | zero =>
      rw [pfB_zero hk]
      simp [compG, ctrlOK_cons, ctrlOK_nil]
  | succ k =>
      rw [pfB_succ k hk]
      simp [compG, ctrlOK_cons, ctrlOK_nil]

theorem compG_ok (k : ℕ) (hk : k < m) : GateOK 2 (compG (a := a) (r := r) (K := K) k hk) := by
  refine ⟨by cases k <;> simp [compG], compG_ht k hk, ?_⟩
  rw [compG_u]; exact pauliX_unitary

theorem compG_flip_up (j : Fin (cap r + 1)) (k : ℕ) (hk : k < m) (x : Cfg (Wire a m r K)) :
    flipCfg (compG k hk).cs (compG k hk).t (frAnn j k x) = frAnn j (k + 1) x := by
  rw [flipCfg_eq_update, compG_ctrl, compG_t, frAnn_succ j k hk]
  congr 1
  simp

theorem compG_flip_down (j : Fin (cap r + 1)) (k : ℕ) (hk : k < m) (x : Cfg (Wire a m r K)) :
    flipCfg (compG k hk).cs (compG k hk).t (frAnn j (k + 1) x) = frAnn j k x := by
  rw [← compG_flip_up j k hk x, flipCfg_flipCfg _ _ (compG_ht k hk)]

theorem compG_impl_up (j : Fin (cap r + 1)) (k : ℕ) (hk : k < m) :
    Impl Clean (frAnn j k) (frAnn j (k + 1)) (gRun (Q := P) [compG (a := a) (r := r) (K := K) k hk]) 1 :=
  Impl.of_classical _ (fun x _ q => by
    rw [gRun_singleton, Gate.op, compG_u, gateOp_pauliX_bas _ _ (compG_ht k hk),
      compG_flip_up])

theorem compG_impl_down (j : Fin (cap r + 1)) (k : ℕ) (hk : k < m) :
    Impl Clean (frAnn j (k + 1)) (frAnn j k) (gRun (Q := P) [compG (a := a) (r := r) (K := K) k hk]) 1 :=
  Impl.of_classical _ (fun x _ q => by
    rw [gRun_singleton, Gate.op, compG_u, gateOp_pauliX_bas _ _ (compG_ht k hk),
      compG_flip_down])

/-- Frame rotation of slot bit `i`, controlled by the enable flag, the private
sector and the prefix flag of the lower bits. -/
def rotG (R : Matrix Bool Bool ℂ) : (i : ℕ) → i < m → Gate (Wire a m r K)
  | 0, h => ⟨[(Wire.hf, true), (Wire.sec, true)], Wire.slot ⟨0, h⟩, R⟩
  | i + 1, h => ⟨[(Wire.hf, true), (Wire.sec, true), (Wire.pf ⟨i, by omega⟩, true)],
      Wire.slot ⟨i + 1, h⟩, R⟩

theorem rotG_t (R : Matrix Bool Bool ℂ) (i : ℕ) (hi : i < m) :
    (rotG (a := a) (r := r) (K := K) R i hi).t = Wire.slot ⟨i, hi⟩ := by
  cases i <;> rfl

theorem rotG_u (R : Matrix Bool Bool ℂ) (i : ℕ) (hi : i < m) :
    (rotG (a := a) (r := r) (K := K) R i hi).u = R := by
  cases i <;> rfl

theorem rotG_ht (R : Matrix Bool Bool ℂ) (i : ℕ) (hi : i < m) :
    ∀ c ∈ (rotG (a := a) (r := r) (K := K) R i hi).cs, c.1 ≠ (rotG R i hi).t := by
  cases i with
  | zero =>
      intro c hc
      simp only [rotG, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> simp [rotG]
  | succ i =>
      intro c hc
      simp only [rotG, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl <;> simp [rotG]

theorem rotG_ok (R : Matrix Bool Bool ℂ) (hR : UnitaryMat R) (i : ℕ) (hi : i < m) :
    GateOK 3 (rotG (a := a) (r := r) (K := K) R i hi) := by
  refine ⟨by cases i <;> simp [rotG], rotG_ht R i hi, ?_⟩
  rw [rotG_u]; exact hR

/-- The ideal predicate of a frame rotation. -/
def frPred (j : Fin (cap r + 1)) (i : Fin m) (x : Cfg (Wire a m r K)) : Bool :=
  decide (x .sec = true ∧ ancOf x = zw a ∧ ptrIdx x = j ∧ Dyadic.lowerZero i (slotOf x))

theorem frameCond_eq (j : Fin (cap r + 1)) (i : Fin m) (R : Matrix Bool Bool ℂ) :
    frameCond (a := a) (K := K) (P := P) j i R =
      condOp (Wire.slot i) (fun x => if frPred j i x then R else 1) := by
  unfold frameCond frPred
  simp only [decide_eq_true_eq]

theorem frAnn_update_slot (j : Fin (cap r + 1)) (i : ℕ) (hi : i < m) (x : Cfg (Wire a m r K))
    (b : Bool) : frAnn j i (Function.update x (Wire.slot ⟨i, hi⟩) b) =
      Function.update (frAnn j i x) (Wire.slot ⟨i, hi⟩) b := by
  funext w
  by_cases hw : w = Wire.slot ⟨i, hi⟩
  · subst hw; simp
  · rw [Function.update_of_ne hw]
    cases w with
    | hf => exact hfB_update_slot j x _ b
    | pf k =>
        simp only [frAnn_pf]
        by_cases hk : k.val < i
        · rw [pfB_update_slot k ⟨i, hi⟩ hk]
        · simp [hk]
    | slot l => simp only [frAnn_slot]; rw [Function.update_of_ne hw]
    | _ => simp only [frAnn_anc, frAnn_sec, frAnn_ptr, frAnn_lab, frAnn_lf, frAnn_tf, frAnn_cf,
        frAnn_wk]; rw [Function.update_of_ne hw]

theorem hfB_iff (j : Fin (cap r + 1)) (x : Cfg (Wire a m r K)) :
    hfB j x = true ↔ ancOf x = zw a ∧ ptrIdx x = j := by
  simp [hfB]

theorem pfB_iff (k : ℕ) (hk' : k < m) (x : Cfg (Wire a m r K)) :
    pfB ⟨k, hk'⟩ x = true ↔ ∀ l : Fin m, l.val < k + 1 → slotOf x l = false := by
  simp only [pfB, decide_eq_true_eq]
  constructor
  · intro h l hl; exact h l (show l.val ≤ k by omega)
  · intro h l hl; exact h l (show l.val < k + 1 by have : l.val ≤ k := hl; omega)

theorem rotG_ctrl (j : Fin (cap r + 1)) (R : Matrix Bool Bool ℂ) (i : ℕ) (hi : i < m)
    (x : Cfg (Wire a m r K)) :
    ctrlOK (rotG R i hi).cs (frAnn j i x) = frPred j ⟨i, hi⟩ x := by
  apply Bool.eq_iff_iff.mpr
  unfold frPred
  rw [decide_eq_true_iff]
  cases i with
  | zero =>
      have e : ctrlOK (rotG (a := a) (r := r) (K := K) R 0 hi).cs (frAnn j 0 x) =
          (hfB j x && x .sec) := by
        simp [rotG, ctrlOK_cons, ctrlOK_nil]
      rw [e, Bool.and_eq_true, hfB_iff]
      constructor
      · rintro ⟨hj, hs⟩
        exact ⟨hs, hj.1, hj.2, fun l hl => absurd hl (by simp [Fin.lt_def])⟩
      · rintro ⟨hs, ha, hj, _⟩
        exact ⟨⟨ha, hj⟩, hs⟩
  | succ i =>
      have e : ctrlOK (rotG (a := a) (r := r) (K := K) R (i + 1) hi).cs (frAnn j (i + 1) x) =
          (hfB j x && (x .sec && pfB ⟨i, by omega⟩ x)) := by
        simp [rotG, ctrlOK_cons, ctrlOK_nil]
      rw [e, Bool.and_eq_true, Bool.and_eq_true, hfB_iff, pfB_iff i (by omega)]
      unfold Dyadic.lowerZero
      constructor
      · rintro ⟨hj, hs, hl⟩
        exact ⟨hs, hj.1, hj.2, fun l hli => hl l (by rw [Fin.lt_def] at hli; exact hli)⟩
      · rintro ⟨hs, ha, hj, hl⟩
        exact ⟨⟨ha, hj⟩, hs, fun l hli => hl l (by rw [Fin.lt_def]; exact hli)⟩

theorem frPred_update_slot (j : Fin (cap r + 1)) (i : Fin m) (x : Cfg (Wire a m r K)) (b : Bool) :
    frPred j i (Function.update x (Wire.slot i) b) = frPred j i x := by
  unfold frPred
  rw [decide_eq_decide, ancOf_update_ne x _ b (fun _ h => by cases h),
    ptrIdx_update_ne x _ b (fun _ h => by cases h), slotOf_update_slot,
    Function.update_of_ne (fun h => by cases h)]
  unfold Dyadic.lowerZero
  constructor
  · rintro ⟨hs, ha, hj, hl⟩
    refine ⟨hs, ha, hj, fun l hli => ?_⟩
    have := hl l hli
    rwa [Function.update_of_ne (ne_of_lt hli)] at this
  · rintro ⟨hs, ha, hj, hl⟩
    refine ⟨hs, ha, hj, fun l hli => ?_⟩
    rw [Function.update_of_ne (ne_of_lt hli)]
    exact hl l hli

theorem rotG_impl (j : Fin (cap r + 1)) (R : Matrix Bool Bool ℂ) (i : ℕ) (hi : i < m) :
    Impl Clean (frAnn j i) (frAnn j i) (gRun (Q := P) [rotG (a := a) (r := r) (K := K) R i hi])
      (frameCond j ⟨i, hi⟩ R) := by
  rw [gRun_singleton, Gate.op, frameCond_eq, rotG_t, rotG_u]
  have h := Impl.gate (Q := P) (S := Clean) (f := frAnn j i) (rotG (a := a) (r := r) (K := K) R i hi).cs
    (rotG (a := a) (r := r) (K := K) R i hi).t (rotG (a := a) (r := r) (K := K) R i hi).u (rotG_ht R i hi) (frPred j ⟨i, hi⟩)
    (fun x b _ => by rw [rotG_t]; exact frAnn_update_slot j i hi x b)
    (fun x _ => rotG_ctrl j R i hi x)
    (fun x b => by rw [rotG_t]; exact frPred_update_slot j ⟨i, hi⟩ x b)
  rw [rotG_t, rotG_u] at h
  exact h

/-! ### Frame gate lists -/

/-- The chain gate `pf (n-1)`, if `n ≥ 1`. -/
def compL : ℕ → List (Gate (Wire a m r K))
  | 0 => []
  | k + 1 => if h : k < m then [compG k h] else []

/-- The rotation gate of bit `n`. -/
def rotL (R : ℕ → Matrix Bool Bool ℂ) (n : ℕ) : List (Gate (Wire a m r K)) :=
  if h : n < m then [rotG (R n) n h] else []

/-- Compute prefix flags `0, …, n-1`. -/
def chainUp : ℕ → List (Gate (Wire a m r K))
  | 0 => []
  | n + 1 => chainUp n ++ compL (n + 1)

/-- Erase prefix flags `n-1, …, 0`. -/
def chainDown : ℕ → List (Gate (Wire a m r K))
  | 0 => []
  | n + 1 => compL (n + 1) ++ chainDown n

/-- Ascending frame: rotations of bits `0, …, n-1`, each preceded by the chain
gate of its prefix flag. -/
def ascCore (R : ℕ → Matrix Bool Bool ℂ) : ℕ → List (Gate (Wire a m r K))
  | 0 => []
  | n + 1 => ascCore R n ++ compL n ++ rotL R n

/-- Descending frame: rotations of bits `n-1, …, 0`, each followed by the
erasure of the prefix flag it no longer needs. -/
def descCore (R : ℕ → Matrix Bool Bool ℂ) : ℕ → List (Gate (Wire a m r K))
  | 0 => []
  | n + 1 => rotL R n ++ compL n ++ descCore R n

theorem compL_impl_up (j : Fin (cap r + 1)) (n : ℕ) (hn : n ≤ m) :
    Impl Clean (frAnn j (n - 1)) (frAnn j n) (gRun (Q := P) (compL (a := a) (m := m) (r := r) (K := K) n)) 1 := by
  cases n with
  | zero => exact Impl.one _
  | succ k =>
      simp only [compL, dif_pos (show k < m by omega)]
      exact compG_impl_up j k _

theorem compL_impl_down (j : Fin (cap r + 1)) (n : ℕ) (hn : n ≤ m) :
    Impl Clean (frAnn j n) (frAnn j (n - 1)) (gRun (Q := P) (compL (a := a) (m := m) (r := r) (K := K) n)) 1 := by
  cases n with
  | zero => exact Impl.one _
  | succ k =>
      simp only [compL, dif_pos (show k < m by omega)]
      exact compG_impl_down j k _

theorem chainUp_impl (j : Fin (cap r + 1)) (n : ℕ) (hn : n ≤ m) :
    Impl Clean (frAnn j 0) (frAnn j n) (gRun (Q := P) (chainUp (a := a) (m := m) (r := r) (K := K) n)) 1 := by
  induction n with
  | zero => exact Impl.one _
  | succ n ih =>
      rw [chainUp, gRun_append]
      exact Impl.congr_ideal ((ih (by omega)).comp (Preserves.one _)
        (compL_impl_up j (n + 1) hn)) (one_comp' _)

theorem chainDown_impl (j : Fin (cap r + 1)) (n : ℕ) (hn : n ≤ m) :
    Impl Clean (frAnn j n) (frAnn j 0) (gRun (Q := P) (chainDown (a := a) (m := m) (r := r) (K := K) n)) 1 := by
  induction n with
  | zero => exact Impl.one _
  | succ n ih =>
      rw [chainDown, gRun_append]
      exact Impl.congr_ideal ((compL_impl_down j (n + 1) hn).comp (Preserves.one _)
        (ih (by omega))) (one_comp' _)

theorem rotL_impl (j : Fin (cap r + 1)) (R : ℕ → Matrix Bool Bool ℂ) (n : ℕ) (hn : n < m) :
    Impl Clean (frAnn j n) (frAnn j n) (gRun (Q := P) (rotL (a := a) (m := m) (r := r) (K := K) R n))
      (frameCond j ⟨n, hn⟩ (R n)) := by
  simp only [rotL, dif_pos hn]
  exact rotG_impl j (R n) n hn

theorem ascCore_impl (j : Fin (cap r + 1)) (R : ℕ → Matrix Bool Bool ℂ) (n : ℕ) (hn : n ≤ m) :
    Impl Clean (frAnn j 0) (frAnn j (n - 1)) (gRun (Q := P) (ascCore (a := a) (m := m) (r := r) (K := K) R n))
      (regAscend j R n hn) := by
  induction n with
  | zero => exact Impl.one _
  | succ n ih =>
      rw [ascCore, gRun_append, gRun_append, regAscend]
      have hbc := (compL_impl_up (P := P) (a := a) (m := m) (K := K) j n (by omega)).comp (Preserves.one _)
        (rotL_impl j R n (by omega))
      exact Impl.congr_ideal ((ih (by omega)).comp (pres2_regAscend _ _ _ _).1 hbc)
        (by rw [comp_one'])

theorem descCore_impl (j : Fin (cap r + 1)) (R : ℕ → Matrix Bool Bool ℂ) (n : ℕ) (hn : n ≤ m) :
    Impl Clean (frAnn j (n - 1)) (frAnn j 0)
      (gRun (Q := P) (descCore (a := a) (m := m) (r := r) (K := K) R n)) (regDescend j R n hn) := by
  induction n with
  | zero => exact Impl.one _
  | succ n ih =>
      rw [descCore, gRun_append, gRun_append, regDescend]
      have hcd := (compL_impl_down (P := P) (a := a) (m := m) (K := K) j n (by omega)).comp (Preserves.one _) (ih (by omega))
      exact Impl.congr_ideal ((rotL_impl j R n (by omega)).comp (pres2_frameCond _ _ _).1 hcd)
        (by rw [comp_one'])

/-- The complete ascending frame, with all prefix flags erased. -/
def ascFull (R : ℕ → Matrix Bool Bool ℂ) : List (Gate (Wire a m r K)) :=
  ascCore R m ++ chainDown (m - 1)

/-- The complete descending frame, with all prefix flags computed first. -/
def descFull (R : ℕ → Matrix Bool Bool ℂ) : List (Gate (Wire a m r K)) :=
  chainUp (m - 1) ++ descCore R m

theorem ascFull_impl (j : Fin (cap r + 1)) (R : ℕ → Matrix Bool Bool ℂ) :
    Impl Clean (frAnn j 0) (frAnn j 0) (gRun (Q := P) (ascFull (a := a) (m := m) (r := r) (K := K) R))
      (regAscend j R m le_rfl) := by
  rw [ascFull, gRun_append]
  exact Impl.congr_ideal ((ascCore_impl j R m le_rfl).comp (pres2_regAscend _ _ _ _).1
    (chainDown_impl j (m - 1) (by omega))) (one_comp' _)

theorem descFull_impl (j : Fin (cap r + 1)) (R : ℕ → Matrix Bool Bool ℂ) :
    Impl Clean (frAnn j 0) (frAnn j 0) (gRun (Q := P) (descFull (a := a) (m := m) (r := r) (K := K) R))
      (regDescend j R m le_rfl) := by
  rw [descFull, gRun_append]
  exact Impl.congr_ideal ((chainUp_impl j (m - 1) (by omega)).comp (Preserves.one _)
    (descCore_impl j R m le_rfl)) (comp_one' _)

/-! ### The central rotation -/

/-- Literals of the central rotation: enable flag and zero slot word. -/
def cenLits : List (Wire a m r K × Bool) :=
  (Wire.hf, true) :: (List.finRange m).map (fun i => (Wire.slot i, false))

/-- The central sector rotation. -/
def cenG (zz vv : ℝ) : List (Gate (Wire a m r K)) :=
  mcGate cenLits wkList Wire.sec (rotMat zz vv)

/-- The ideal predicate of the central rotation. -/
def cenPred (j : Fin (cap r + 1)) (x : Cfg (Wire a m r K)) : Bool :=
  decide (ancOf x = zw a ∧ ptrIdx x = j ∧ slotOf x = zw m)

theorem cenLits_length : (cenLits (a := a) (m := m) (r := r) (K := K)).length = m + 1 := by
  simp [cenLits]

theorem mem_cenLits (c : Wire a m r K × Bool) (hc : c ∈ cenLits) :
    c.1 = Wire.hf ∨ ∃ i, c.1 = Wire.slot i := by
  simp only [cenLits, List.mem_cons, List.mem_map, List.mem_finRange, true_and] at hc
  rcases hc with rfl | ⟨i, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨i, rfl⟩

theorem cenLits_ctrl (j : Fin (cap r + 1)) (x : Cfg (Wire a m r K)) :
    ctrlOK cenLits (frAnn j 0 x) = cenPred j x := by
  unfold cenPred
  rw [Bool.eq_iff_iff, ctrlOK_iff, decide_eq_true_iff]
  constructor
  · intro h
    have hhf := h (Wire.hf, true) List.mem_cons_self
    simp only [frAnn_hf, hfB, decide_eq_true_eq] at hhf
    refine ⟨hhf.1, hhf.2, ?_⟩
    funext i
    exact h (Wire.slot i, false) (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨i, by simp, rfl⟩))
  · rintro ⟨ha, hj, hz⟩ c hc
    simp only [cenLits, List.mem_cons, List.mem_map, List.mem_finRange, true_and] at hc
    rcases hc with rfl | ⟨i, rfl⟩
    · simp [hfB, ha, hj]
    · exact congrFun hz i

theorem centralCond_eq (j : Fin (cap r + 1)) (zz vv : ℝ) :
    centralCond (a := a) (K := K) (P := P) (m := m) j zz vv =
      condOp Wire.sec (fun x => if cenPred j x then rotMat zz vv else 1) := by
  unfold centralCond cenPred
  simp only [decide_eq_true_eq]

theorem frAnn_update_sec (j : Fin (cap r + 1)) (x : Cfg (Wire a m r K)) (b : Bool) :
    frAnn j 0 (Function.update x Wire.sec b) = Function.update (frAnn j 0 x) Wire.sec b := by
  funext w
  by_cases hw : w = Wire.sec
  · subst hw; simp
  · rw [Function.update_of_ne hw]
    cases w with
    | hf => exact hfB_update_sec j x b
    | pf k => simp
    | sec => exact absurd rfl hw
    | _ => simp only [frAnn_anc, frAnn_slot, frAnn_ptr, frAnn_lab, frAnn_lf, frAnn_tf, frAnn_cf,
        frAnn_wk]; rw [Function.update_of_ne hw]

theorem cenPred_update_sec (j : Fin (cap r + 1)) (x : Cfg (Wire a m r K)) (b : Bool) :
    cenPred j (Function.update x Wire.sec b) = cenPred j x := by
  unfold cenPred
  rw [ancOf_update_ne x _ b (fun _ h => by cases h), ptrIdx_update_ne x _ b (fun _ h => by cases h),
    slotOf_update_ne x _ b (fun _ h => by cases h)]

/-- The wk-clean configurations. -/
def WkClean (y : Cfg (Wire a m r K)) : Prop := ∀ f ∈ wkList, y f = false

theorem cenG_impl (j : Fin (cap r + 1)) (zz vv : ℝ) (hK : m ≤ K) :
    Impl Clean (frAnn j 0) (frAnn j 0) (gRun (Q := P) (cenG (a := a) (m := m) (r := r) (K := K) zz vv))
      (centralCond j zz vv) := by
  rw [centralCond_eq]
  have hlt : ∀ l ∈ (cenLits (a := a) (m := m) (r := r) (K := K)), l.1 ≠ Wire.sec := by
    intro l hl
    rcases mem_cenLits l hl with h | ⟨i, h⟩ <;> rw [h] <;> simp
  have hg := Impl.gate (Q := P) (S := Clean) (f := frAnn j 0) cenLits Wire.sec (rotMat zz vv) hlt
    (cenPred j) (fun x b _ => frAnn_update_sec j x b) (fun x _ => cenLits_ctrl j x)
    (fun x b => cenPred_update_sec j x b)
  apply hg.congr_left (S' := WkClean)
  · exact mcGate_agrees cenLits wkList Wire.sec (rotMat zz vv)
      (by rw [cenLits_length, wkList_length]; omega) wkList_nodup hlt
      (fun f hf => by obtain ⟨i, rfl⟩ := (mem_wkList f).mp hf; simp)
      (fun l hl f hf => by
        obtain ⟨i, rfl⟩ := (mem_wkList f).mp hf
        rcases mem_cenLits l hl with h | ⟨k, h⟩ <;> rw [h] <;> simp)
      WkClean (fun y hy => hy)
      (fun y b hy f hf => by
        obtain ⟨i, rfl⟩ := (mem_wkList f).mp hf
        rw [Function.update_of_ne (by simp)]
        exact hy _ hf)
  · intro x hx f hf
    obtain ⟨i, rfl⟩ := (mem_wkList f).mp hf
    exact hx _ rfl

/-! ### The enable flag computation -/

/-- Compute (or erase) the enable flag. -/
def hfC (j : Fin (cap r + 1)) : List (Gate (Wire a m r K)) :=
  mcGate (hfLits j) wkList Wire.hf pauliX

theorem hfLits_ne_hf (j : Fin (cap r + 1)) :
    ∀ l ∈ (hfLits (a := a) (m := m) (K := K) j), l.1 ≠ Wire.hf := by
  intro l hl
  rcases mem_hfLits j l hl with ⟨i, h⟩ | ⟨i, h⟩ <;> rw [h] <;> simp

theorem hfLits_ne_wk (j : Fin (cap r + 1)) :
    ∀ l ∈ (hfLits (a := a) (m := m) (K := K) j), ∀ f ∈ wkList, l.1 ≠ f := by
  intro l hl f hf
  obtain ⟨i, rfl⟩ := (mem_wkList f).mp hf
  rcases mem_hfLits j l hl with ⟨k, h⟩ | ⟨k, h⟩ <;> rw [h] <;> simp

theorem hfC_bas (j : Fin (cap r + 1)) (hK : a + r ≤ K + 1) (y : Cfg (Wire a m r K))
    (hy : WkClean y) (q : P) :
    gRun (hfC j) (bas y q) = bas (flipCfg (hfLits j) Wire.hf y) q :=
  mcGate_pauliX_bas _ _ _ (by rw [hfLits_length, wkList_length]; exact hK) wkList_nodup
    (hfLits_ne_hf j) (fun f hf => by obtain ⟨i, rfl⟩ := (mem_wkList f).mp hf; simp)
    (hfLits_ne_wk j) y hy q

theorem flip_hf_clean (j : Fin (cap r + 1)) (x : Cfg (Wire a m r K)) (hx : Clean x) :
    flipCfg (hfLits j) Wire.hf x = frAnn j 0 x := by
  rw [flipCfg_eq_update, ctrlOK_hfLits, hx Wire.hf rfl, Bool.false_xor]
  funext w
  by_cases hw : w = Wire.hf
  · subst hw; simp
  · rw [Function.update_of_ne hw]
    cases w with
    | hf => exact absurd rfl hw
    | pf k => simp [hx (Wire.pf k) rfl]
    | _ => rfl

theorem flip_hf_back (j : Fin (cap r + 1)) (x : Cfg (Wire a m r K)) (hx : Clean x) :
    flipCfg (hfLits j) Wire.hf (frAnn j 0 x) = x := by
  rw [← flip_hf_clean j x hx, flipCfg_flipCfg _ _ (hfLits_ne_hf j)]

theorem hfC_impl_up (j : Fin (cap r + 1)) (hK : a + r ≤ K + 1) :
    Impl Clean (fun x => x) (frAnn j 0) (gRun (Q := P) (hfC (a := a) (m := m) (K := K) j)) 1 :=
  Impl.of_classical _ (fun x hx q => by
    rw [hfC_bas j hK x (fun f hf => by obtain ⟨i, rfl⟩ := (mem_wkList f).mp hf; exact hx _ rfl),
      flip_hf_clean j x hx])

theorem hfC_impl_down (j : Fin (cap r + 1)) (hK : a + r ≤ K + 1) :
    Impl Clean (frAnn j 0) (fun x => x) (gRun (Q := P) (hfC (a := a) (m := m) (K := K) j)) 1 :=
  Impl.of_classical _ (fun x hx q => by
    rw [hfC_bas j hK _ (fun f hf => by obtain ⟨i, rfl⟩ := (mem_wkList f).mp hf; exact hx _ rfl),
      flip_hf_back j x hx])

/-! ### The complete network -/

/-- Gate list of the boundary network at pointer word `j`. -/
def netGates (j : Fin (cap r + 1)) (c σ : ℝ) : List (Gate (Wire a m r K)) :=
  hfC j ++ ascFull (Sim.unMats c) ++ cenG (centralCosine c m) (centralSine c σ m) ++
    descFull (Sim.outMats c) ++ hfC j

theorem net_agrees (j : Fin (cap r + 1)) (c σ : ℝ) (hK : a + m + 2 * r ≤ K) :
    Agrees Clean (gRun (Q := P) (netGates (a := a) (m := m) (K := K) j c σ)) (NET j c σ) := by
  apply Impl.toAgrees
  rw [netGates, gRun_append, gRun_append, gRun_append, gRun_append, NET]
  have h1 := hfC_impl_up (P := P) (a := a) (m := m) (K := K) j (by omega)
  have h2 := ascFull_impl (P := P) (a := a) (m := m) (K := K) j (Sim.unMats c)
  have h3 := cenG_impl (P := P) (a := a) (m := m) (K := K) j (centralCosine c m) (centralSine c σ m)
    (by omega)
  have h4 := descFull_impl (P := P) (a := a) (m := m) (K := K) j (Sim.outMats c)
  have h5 := hfC_impl_down (P := P) (a := a) (m := m) (K := K) j (by omega)
  have h45 := h4.comp (pres2_regDescend _ _ _ _).1 h5
  have h345 := h3.comp (pres2_centralCond _ _ _).1 h45
  have h2345 := h2.comp (pres2_regAscend _ _ _ _).1 h345
  have h12345 := h1.comp (Preserves.one _) h2345
  refine Impl.congr_ideal h12345 ?_
  ext v
  rfl

end

end SparseHamiltonian.GateCircuit.Sim
