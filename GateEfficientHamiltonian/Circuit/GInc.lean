import GateEfficientHamiltonian.Circuit.GNet

/-!
# Gate-level pointer increment

The private-sector increment of the reuse pointer is a ripple circuit with
clean carry flags: `cf k ← sec ∧ ptr 0 ∧ … ∧ ptr (k-1)` is computed for
`k = 1, …, r-1`; then, from the top bit down, bit `i` is flipped under its
carry and the carry is erased while the lower bits are still unchanged.  The
circuit consists of at most `3r` Toffoli/CNOT gates and acts on clean
configurations as the ideal increment `INC` (`inc_agrees`).
-/

namespace SparseHamiltonian.GateCircuit.Sim

noncomputable section
open ContinuousLinearMap OracleCircuit
open scoped InnerProduct BigOperators
open GatePointerEncoding (wordValue wordEquivFin wordFin successorEquiv)

variable {a m r K : ℕ}
variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-! ### Carries and incremented bits -/

theorem onePrefix_congr (w w' : Word r) (k : ℕ) (h : ∀ i : Fin r, i.val < k → w i = w' i) :
    GatePrivatePointer.onePrefix w k = GatePrivatePointer.onePrefix w' k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [GatePrivatePointer.onePrefix]
      rw [ih (fun i hi => h i (by omega))]
      congr 1
      unfold GatePrivatePointer.bit
      split_ifs with hk
      · exact h ⟨k, hk⟩ (by simp)
      · rfl

/-- The carry into pointer bit `k`. -/
def carryB (k : ℕ) (x : Cfg (Wire a m r K)) : Bool :=
  x .sec && GatePrivatePointer.onePrefix (ptrOf x) k

theorem carryB_succ (k : ℕ) (hk : k < r) (x : Cfg (Wire a m r K)) :
    carryB (k + 1) x = (carryB k x && x (Wire.ptr ⟨k, hk⟩)) := by
  unfold carryB
  simp only [GatePrivatePointer.onePrefix, GatePrivatePointer.bit, dif_pos hk, Bool.and_assoc]
  rfl

theorem carryB_zero (x : Cfg (Wire a m r K)) : carryB 0 x = x .sec := by
  simp [carryB]

/-- Pointer bits at and above `n` incremented on the private sector. -/
def updPtr (n : ℕ) (x : Cfg (Wire a m r K)) : Cfg (Wire a m r K) := fun w =>
  match w with
  | .ptr i => if n ≤ i.val then xor (x (.ptr i)) (carryB i.val x) else x (.ptr i)
  | w => x w

/-- Carry flags `1, …, n` stored. -/
def incAnn (n : ℕ) (x : Cfg (Wire a m r K)) : Cfg (Wire a m r K) := fun w =>
  match w with
  | .cf k => decide (1 ≤ k.val ∧ k.val ≤ n) && carryB k.val x
  | w => x w

theorem updPtr_sec (n : ℕ) (x : Cfg (Wire a m r K)) : updPtr n x .sec = x .sec := rfl

theorem carryB_updPtr (k n : ℕ) (hk : k ≤ n) (x : Cfg (Wire a m r K)) :
    carryB k (updPtr n x) = carryB k x := by
  unfold carryB
  rw [updPtr_sec]
  congr 1
  apply onePrefix_congr
  intro i hi
  change (if n ≤ i.val then _ else x (.ptr i)) = x (.ptr i)
  rw [if_neg (by omega)]

theorem carryB_update_cf (k : ℕ) (x : Cfg (Wire a m r K)) (l : Fin r) (b : Bool) :
    carryB k (Function.update x (Wire.cf l) b) = carryB k x := by
  unfold carryB
  rw [Function.update_of_ne (by simp), ptrOf_update_ne x _ b (fun _ h => by cases h)]

theorem carryB_incAnn (k n : ℕ) (x : Cfg (Wire a m r K)) : carryB k (incAnn n x) = carryB k x :=
  rfl

/-- The carry gate computing `cf (k+1)` (an involution). -/
def carryG : (k : ℕ) → k + 1 < r → Gate (Wire a m r K)
  | 0, h => ⟨[(Wire.sec, true), (Wire.ptr ⟨0, by omega⟩, true)], Wire.cf ⟨1, h⟩, pauliX⟩
  | k + 1, h => ⟨[(Wire.cf ⟨k + 1, by omega⟩, true), (Wire.ptr ⟨k + 1, by omega⟩, true)],
      Wire.cf ⟨k + 2, h⟩, pauliX⟩

/-- Flip pointer bit `i` under its carry. -/
def flipG : (i : ℕ) → i < r → Gate (Wire a m r K)
  | 0, h => ⟨[(Wire.sec, true)], Wire.ptr ⟨0, h⟩, pauliX⟩
  | i + 1, h => ⟨[(Wire.cf ⟨i + 1, h⟩, true)], Wire.ptr ⟨i + 1, h⟩, pauliX⟩

theorem carryG_t (k : ℕ) (h : k + 1 < r) :
    (carryG (a := a) (m := m) (K := K) k h).t = Wire.cf ⟨k + 1, h⟩ := by
  cases k <;> rfl

theorem carryG_u (k : ℕ) (h : k + 1 < r) : (carryG (a := a) (m := m) (K := K) k h).u = pauliX := by
  cases k <;> rfl

theorem carryG_ht (k : ℕ) (h : k + 1 < r) :
    ∀ c ∈ (carryG (a := a) (m := m) (K := K) k h).cs, c.1 ≠ (carryG k h).t := by
  cases k with
  | zero =>
      intro c hc
      simp only [carryG, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> simp [carryG]
  | succ k =>
      intro c hc
      simp only [carryG, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> simp [carryG]

theorem flipG_t (i : ℕ) (h : i < r) : (flipG (a := a) (m := m) (K := K) i h).t = Wire.ptr ⟨i, h⟩ := by
  cases i <;> rfl

theorem flipG_u (i : ℕ) (h : i < r) : (flipG (a := a) (m := m) (K := K) i h).u = pauliX := by
  cases i <;> rfl

theorem flipG_ht (i : ℕ) (h : i < r) :
    ∀ c ∈ (flipG (a := a) (m := m) (K := K) i h).cs, c.1 ≠ (flipG i h).t := by
  cases i with
  | zero =>
      intro c hc
      simp only [flipG, List.mem_cons, List.not_mem_nil, or_false] at hc
      subst hc; simp [flipG]
  | succ i =>
      intro c hc
      simp only [flipG, List.mem_cons, List.not_mem_nil, or_false] at hc
      subst hc; simp [flipG]

theorem incAnn_succ (k : ℕ) (h : k + 1 < r) (x : Cfg (Wire a m r K)) :
    incAnn (k + 1) x = Function.update (incAnn k x) (Wire.cf ⟨k + 1, h⟩) (carryB (k + 1) x) := by
  funext w
  by_cases hw : w = Wire.cf ⟨k + 1, h⟩
  · subst hw
    simp [incAnn]
  · rw [Function.update_of_ne hw]
    cases w with
    | cf l =>
        have hl : l.val ≠ k + 1 := fun e => hw (by rw [show l = ⟨k + 1, h⟩ from Fin.ext e])
        simp only [incAnn]
        congr 1
        rw [decide_eq_decide]
        omega
    | _ => rfl

theorem carryG_ctrl (k : ℕ) (h : k + 1 < r) (x : Cfg (Wire a m r K)) :
    ctrlOK (carryG k h).cs (incAnn k x) = carryB (k + 1) x := by
  cases k with
  | zero =>
      rw [carryB_succ 0 (by omega), carryB_zero]
      simp [carryG, ctrlOK_cons, ctrlOK_nil, incAnn]
  | succ k =>
      rw [carryB_succ (k + 1) (by omega)]
      simp [carryG, ctrlOK_cons, ctrlOK_nil, incAnn]

theorem carryG_flip_up (k : ℕ) (h : k + 1 < r) (x : Cfg (Wire a m r K)) :
    flipCfg (carryG k h).cs (carryG k h).t (incAnn k x) = incAnn (k + 1) x := by
  rw [flipCfg_eq_update, carryG_ctrl, carryG_t, incAnn_succ k h]
  congr 1
  simp [incAnn]

theorem carryG_flip_down (k : ℕ) (h : k + 1 < r) (x : Cfg (Wire a m r K)) :
    flipCfg (carryG k h).cs (carryG k h).t (incAnn (k + 1) x) = incAnn k x := by
  rw [← carryG_flip_up k h x, flipCfg_flipCfg _ _ (carryG_ht k h)]

theorem updPtr_succ (n : ℕ) (hn : n < r) (x : Cfg (Wire a m r K)) :
    updPtr n x = Function.update (updPtr (n + 1) x) (Wire.ptr ⟨n, hn⟩)
      (xor (x (Wire.ptr ⟨n, hn⟩)) (carryB n x)) := by
  funext w
  by_cases hw : w = Wire.ptr ⟨n, hn⟩
  · subst hw
    simp [updPtr]
  · rw [Function.update_of_ne hw]
    cases w with
    | ptr l =>
        have hl : l.val ≠ n := fun e => hw (by rw [show l = ⟨n, hn⟩ from Fin.ext e])
        simp only [updPtr]
        by_cases h1 : n + 1 ≤ l.val
        · rw [if_pos (by omega), if_pos h1]
        · rw [if_neg (by omega), if_neg h1]
    | _ => rfl

theorem incAnn_update_ptr (k : ℕ) (x : Cfg (Wire a m r K)) (i : Fin r) (hi : k ≤ i.val) (b : Bool) :
    incAnn k (Function.update x (Wire.ptr i) b) = Function.update (incAnn k x) (Wire.ptr i) b := by
  funext w
  by_cases hw : w = Wire.ptr i
  · subst hw
    simp [incAnn]
  · rw [Function.update_of_ne hw]
    cases w with
    | cf l =>
        simp only [incAnn]
        by_cases hl : 1 ≤ l.val ∧ l.val ≤ k
        · rw [decide_eq_true hl, Bool.true_and, Bool.true_and]
          unfold carryB
          rw [Function.update_of_ne (by simp)]
          congr 1
          apply onePrefix_congr
          intro t ht
          change Function.update x (Wire.ptr i) b (Wire.ptr t) = x (Wire.ptr t)
          rw [Function.update_of_ne (fun e => by cases e; omega)]
        · rw [decide_eq_false hl, Bool.false_and, Bool.false_and]
    | _ => simp only [incAnn]; rw [Function.update_of_ne hw]

theorem flipG_flip (n : ℕ) (hn : n < r) (x : Cfg (Wire a m r K)) :
    flipCfg (flipG n hn).cs (flipG n hn).t (incAnn n (updPtr (n + 1) x)) =
      incAnn n (updPtr n x) := by
  rw [flipCfg_eq_update, flipG_t, updPtr_succ n hn x,
    incAnn_update_ptr n _ ⟨n, hn⟩ le_rfl]
  congr 1
  have hctrl : ctrlOK (flipG n hn).cs (incAnn n (updPtr (n + 1) x)) = carryB n x := by
    cases n with
    | zero =>
        rw [carryB_zero]
        simp [flipG, ctrlOK_cons, ctrlOK_nil, incAnn, updPtr]
    | succ n =>
        simp only [flipG, ctrlOK_cons, ctrlOK_nil, Bool.and_true]
        simp only [incAnn]
        rw [carryB_updPtr _ _ (by omega)]
        simp
  rw [hctrl]
  simp only [incAnn, updPtr]
  rw [if_neg (by simp)]

/-! ### The ripple circuit -/

def carryL (k : ℕ) : List (Gate (Wire a m r K)) := if h : k + 1 < r then [carryG k h] else []

def flipL (i : ℕ) : List (Gate (Wire a m r K)) := if h : i < r then [flipG i h] else []

/-- Uncompute carry flag `cf n` (for `n ≥ 1`). -/
def uncL : ℕ → List (Gate (Wire a m r K))
  | 0 => []
  | k + 1 => carryL k

/-- Compute the carry flags `1, …, n`. -/
def carryUp : ℕ → List (Gate (Wire a m r K))
  | 0 => []
  | n + 1 => carryUp n ++ carryL n

/-- Flip and erase from bit `n-1` down to bit `0`. -/
def topDown : ℕ → List (Gate (Wire a m r K))
  | 0 => []
  | n + 1 => flipL n ++ uncL n ++ topDown n

/-- The ripple increment. -/
def incGates : List (Gate (Wire a m r K)) := carryUp (r - 1) ++ topDown r

theorem cfgRun_carryUp (n : ℕ) (hn : n ≤ r - 1) (x : Cfg (Wire a m r K)) :
    cfgRun (carryUp n) (incAnn 0 x) = incAnn n x := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [carryUp, cfgRun_append, ih (by omega), carryL, dif_pos (show n + 1 < r by omega)]
      exact carryG_flip_up n _ x

theorem cfgRun_topDown (n : ℕ) (hn : n ≤ r) (x : Cfg (Wire a m r K)) :
    cfgRun (topDown n) (incAnn (n - 1) (updPtr n x)) = incAnn 0 (updPtr 0 x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [topDown, cfgRun_append, cfgRun_append, flipL, dif_pos (show n < r by omega)]
      change cfgRun (topDown n) (cfgRun (uncL n) (flipCfg (flipG n _).cs (flipG n _).t
        (incAnn n (updPtr (n + 1) x)))) = _
      rw [flipG_flip]
      cases n with
      | zero => rfl
      | succ k =>
          rw [uncL, carryL, dif_pos (show k + 1 < r by omega)]
          change cfgRun (topDown (k + 1)) (flipCfg (carryG k _).cs (carryG k _).t
            (incAnn (k + 1) (updPtr (k + 1) x))) = _
          rw [carryG_flip_down]
          exact ih (by omega)

theorem incAnn_zero_clean (x : Cfg (Wire a m r K)) (hx : Clean x) : incAnn 0 x = x := by
  funext w
  cases w with
  | cf l =>
      simp only [incAnn]
      rw [hx _ rfl]
      rw [decide_eq_false (show ¬ (1 ≤ l.val ∧ l.val ≤ 0) by omega), Bool.false_and]
  | _ => rfl

theorem updPtr_top (x : Cfg (Wire a m r K)) : updPtr r x = x := by
  funext w
  cases w with
  | ptr i => simp only [updPtr]; rw [if_neg (by omega)]
  | _ => rfl

theorem clean_updPtr (n : ℕ) (x : Cfg (Wire a m r K)) (hx : Clean x) : Clean (updPtr n x) := by
  intro w hw
  cases w <;> first | exact hx _ hw | simp [isFlag] at hw

theorem updPtr_zero_eq (x : Cfg (Wire a m r K)) :
    updPtr 0 x = (incEquiv (K := K) (m := m) (a := a) x) := by
  change updPtr 0 x = incFun (successorEquiv r) x
  unfold incFun
  funext w
  split_ifs with hs
  · cases w with
    | ptr i =>
        simp only [updPtr, Nat.zero_le, if_true]
        change _ = (successorEquiv r (ptrOf x)) i
        rw [GatePointerEncoding.successorEquiv_apply, GatePointerEncoding.successorWord_apply]
        unfold carryB
        rw [hs, Bool.true_and]
        cases GatePrivatePointer.onePrefix (ptrOf x) i.val <;> simp [ptrOf]
    | _ => rfl
  · cases w with
    | ptr i =>
        simp only [updPtr, Nat.zero_le, if_true]
        unfold carryB
        have hs' : x .sec = false := by simpa using hs
        rw [hs', Bool.false_and, Bool.xor_false]
    | _ => rfl

theorem cfgRun_incGates (x : Cfg (Wire a m r K)) (hx : Clean x) :
    cfgRun (incGates (a := a) (m := m) (r := r) (K := K)) x = incEquiv (K := K) (m := m) (a := a) x := by
  have h0 := cfgRun_carryUp (a := a) (m := m) (K := K) (r - 1) le_rfl x
  rw [incAnn_zero_clean x hx] at h0
  have h := cfgRun_topDown r le_rfl x
  rw [updPtr_top] at h
  rw [incGates, cfgRun_append, h0, h, incAnn_zero_clean _ (clean_updPtr 0 x hx), updPtr_zero_eq]

/-! ### Validity, counts and agreement -/

theorem incGates_ok : ∀ g ∈ (incGates (a := a) (m := m) (r := r) (K := K)), GateOK 2 g ∧ g.u = pauliX := by
  have hc : ∀ k, ∀ g ∈ (carryL (a := a) (m := m) (r := r) (K := K) k), GateOK 2 g ∧ g.u = pauliX := by
    intro k g hg
    unfold carryL at hg
    split_ifs at hg with h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      subst hg
      refine ⟨⟨by cases k <;> simp [carryG], carryG_ht k h, ?_⟩, carryG_u k h⟩
      rw [carryG_u]; exact pauliX_unitary
    · simp at hg
  have hf : ∀ k, ∀ g ∈ (flipL (a := a) (m := m) (r := r) (K := K) k), GateOK 2 g ∧ g.u = pauliX := by
    intro k g hg
    unfold flipL at hg
    split_ifs at hg with h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      subst hg
      refine ⟨⟨by cases k <;> simp [flipG], flipG_ht k h, ?_⟩, flipG_u k h⟩
      rw [flipG_u]; exact pauliX_unitary
    · simp at hg
  have hu : ∀ k, ∀ g ∈ (uncL (a := a) (m := m) (r := r) (K := K) k), GateOK 2 g ∧ g.u = pauliX := by
    intro k g hg
    cases k with
    | zero => simp [uncL] at hg
    | succ k => exact hc k g hg
  have hup : ∀ n, ∀ g ∈ (carryUp (a := a) (m := m) (r := r) (K := K) n), GateOK 2 g ∧ g.u = pauliX := by
    intro n
    induction n with
    | zero => intro g hg; simp [carryUp] at hg
    | succ n ih =>
        intro g hg
        rw [carryUp, List.mem_append] at hg
        rcases hg with hg | hg
        · exact ih g hg
        · exact hc n g hg
  have hdn : ∀ n, ∀ g ∈ (topDown (a := a) (m := m) (r := r) (K := K) n), GateOK 2 g ∧ g.u = pauliX := by
    intro n
    induction n with
    | zero => intro g hg; simp [topDown] at hg
    | succ n ih =>
        intro g hg
        rw [topDown, List.mem_append, List.mem_append] at hg
        rcases hg with (hg | hg) | hg
        · exact hf n g hg
        · exact hu n g hg
        · exact ih g hg
  intro g hg
  rw [incGates, List.mem_append] at hg
  rcases hg with hg | hg
  · exact hup _ g hg
  · exact hdn _ g hg

theorem incGates_classical : Classical (incGates (a := a) (m := m) (r := r) (K := K)) := by
  intro g hg
  exact ⟨(incGates_ok g hg).2, (incGates_ok g hg).1.2.1⟩

theorem incGates_length : (incGates (a := a) (m := m) (r := r) (K := K)).length ≤ 3 * r := by
  have hc : ∀ k, (carryL (a := a) (m := m) (r := r) (K := K) k).length ≤ 1 := by
    intro k; unfold carryL; split_ifs <;> simp
  have hf : ∀ k, (flipL (a := a) (m := m) (r := r) (K := K) k).length ≤ 1 := by
    intro k; unfold flipL; split_ifs <;> simp
  have hu : ∀ k, (uncL (a := a) (m := m) (r := r) (K := K) k).length ≤ 1 := by
    intro k; cases k with
    | zero => simp [uncL]
    | succ k => exact hc k
  have hup : ∀ n, (carryUp (a := a) (m := m) (r := r) (K := K) n).length ≤ n := by
    intro n
    induction n with
    | zero => simp [carryUp]
    | succ n ih => rw [carryUp, List.length_append]; have := hc n; omega
  have hdn : ∀ n, (topDown (a := a) (m := m) (r := r) (K := K) n).length ≤ 2 * n := by
    intro n
    induction n with
    | zero => simp [topDown]
    | succ n ih =>
        rw [topDown, List.length_append, List.length_append]
        have := hf n; have := hu n; omega
  rw [incGates, List.length_append]
  have := hup (r - 1); have := hdn r
  omega

theorem inc_agrees :
    Agrees Clean (gRun (Q := P) (incGates (a := a) (m := m) (r := r) (K := K)))
      (INC (K := K) (m := m) (a := a) (r := r) (P := P)) := by
  apply agrees_of_bas
  intro x hx q
  rw [gRun_classical_bas _ incGates_classical, cfgRun_incGates x hx, INC]
  exact (perm_bas _ x q).symm

end

end SparseHamiltonian.GateCircuit.Sim
