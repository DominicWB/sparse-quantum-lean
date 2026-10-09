import GateEfficientHamiltonian.Circuit.Select

/-!
# Binary-tree state preparation

`treeOp ts M` rotates the wires `ts (q-1), …, ts 0` in this order (top bit
first); the matrix used on bit `s` may depend on the configuration of the
other wires, in particular on the higher tree bits.  `treeOp_bas` computes
its action on a basis configuration whose tree bits are zero: the amplitude
of the word `w` is the product of the first columns.

`tree_telescope` evaluates that product when every live column is the
conditional-mass column of a target amplitude `f` (with total mass one):
the product is `f w`.  Columns of prefixes with zero mass are arbitrary.
-/

namespace SparseHamiltonian.GateCircuit

noncomputable section
open ContinuousLinearMap OracleCircuit
open scoped InnerProduct BigOperators

variable {W : Type*} [Fintype W] [DecidableEq W]
variable {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] [CompleteSpace Q]

/-! ### Writing a word into the low tree wires -/

/-- Write `w` into the wires `ts 0, …, ts (k-1)`. -/
def setLow {q : ℕ} (ts : Fin q → W) : (k : ℕ) → k ≤ q → Cfg W → (Fin k → Bool) → Cfg W
  | 0, _, x, _ => x
  | k + 1, h, x, w => Function.update (setLow ts k (by omega) x (Fin.init w)) (ts ⟨k, by omega⟩)
      (w (Fin.last k))

omit [Fintype W] in
theorem setLow_update_comm {q : ℕ} (ts : Fin q → W) (hts : Function.Injective ts)
    (k : ℕ) (hk : k ≤ q) (x : Cfg W) (w : Fin k → Bool) (t : Fin q) (ht : k ≤ t.val)
    (b : Bool) :
    setLow ts k hk (Function.update x (ts t) b) w = Function.update (setLow ts k hk x w) (ts t) b := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [setLow]
      rw [ih (by omega) (Fin.init w) (by omega)]
      apply Function.update_comm
      intro h
      have := hts h
      have hv := congrArg Fin.val this
      simp at hv
      omega

omit [Fintype W] in
theorem setLow_apply_high {q : ℕ} (ts : Fin q → W) (hts : Function.Injective ts)
    (k : ℕ) (hk : k ≤ q) (x : Cfg W) (w : Fin k → Bool) (t : Fin q) (ht : k ≤ t.val) :
    setLow ts k hk x w (ts t) = x (ts t) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [setLow]
      rw [Function.update_of_ne]
      · exact ih (by omega) (Fin.init w) (by omega)
      · intro h
        have := hts h
        have hv := congrArg Fin.val this
        simp at hv
        omega

omit [Fintype W] in
theorem setLow_apply_low {q : ℕ} (ts : Fin q → W) (hts : Function.Injective ts)
    (k : ℕ) (hk : k ≤ q) (x : Cfg W) (w : Fin k → Bool) (i : Fin k) :
    setLow ts k hk x w (ts ⟨i, by omega⟩) = w i := by
  induction k with
  | zero => exact Fin.elim0 i
  | succ k ih =>
      simp only [setLow]
      by_cases hi : i = Fin.last k
      · subst hi
        simp only [Fin.val_last, Function.update_self]
      · have hlt : i.val < k := by
          have := i.isLt
          have : i.val ≠ k := fun e => hi (Fin.ext e)
          omega
        rw [Function.update_of_ne]
        · have := ih (by omega) (Fin.init w) ⟨i.val, hlt⟩
          rw [this]
          simp only [Fin.init]
          congr 1
        · intro h
          have := hts h
          have hv := congrArg Fin.val this
          simp at hv
          omega

omit [Fintype W] in
theorem setLow_apply_other {q : ℕ} (ts : Fin q → W) (k : ℕ) (hk : k ≤ q) (x : Cfg W)
    (w : Fin k → Bool) (v : W) (hv : ∀ t, ts t ≠ v) : setLow ts k hk x w v = x v := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [setLow]
      rw [Function.update_of_ne (Ne.symm (hv _))]
      exact ih (by omega) (Fin.init w)

/-! ### The tree operator -/

/-- Rotations of the tree bits `k-1, …, 0` (bit `k-1` first). -/
def treeFrom {q : ℕ} (ts : Fin q → W) (M : Fin q → Cfg W → Matrix Bool Bool ℂ) :
    (k : ℕ) → k ≤ q → Reg W Q →L[ℂ] Reg W Q
  | 0, _ => 1
  | k + 1, h => treeFrom ts M k (by omega) ∘L condOp (ts ⟨k, by omega⟩) (M ⟨k, by omega⟩)

/-- The complete tree. -/
def treeOp {q : ℕ} (ts : Fin q → W) (M : Fin q → Cfg W → Matrix Bool Bool ℂ) :
    Reg W Q →L[ℂ] Reg W Q :=
  treeFrom ts M q le_rfl

/-- Words of length `k+1` are a word of length `k` and a top bit. -/
def snocEquiv (k : ℕ) : (Fin k → Bool) × Bool ≃ (Fin (k + 1) → Bool) where
  toFun p := Fin.snoc p.1 p.2
  invFun w := (Fin.init w, w (Fin.last k))
  left_inv p := by simp
  right_inv w := by simp

/-- The tree acting on a basis configuration with clear tree bits. -/
theorem treeFrom_bas {q : ℕ} (ts : Fin q → W) (hts : Function.Injective ts)
    (M : Fin q → Cfg W → Matrix Bool Bool ℂ)
    (hM : ∀ s : Fin q, ∀ y : Cfg W, ∀ t : Fin q, t.val ≤ s.val → ∀ b,
      M s (Function.update y (ts t) b) = M s y)
    (k : ℕ) (hk : k ≤ q) (x : Cfg W) (hx : ∀ t : Fin q, t.val < k → x (ts t) = false)
    (q₀ : Q) :
    treeFrom ts M k hk (bas x q₀) =
      ∑ w : Fin k → Bool,
        (∏ s : Fin k, M ⟨s, by omega⟩ (setLow ts k hk x w) (w s) false) •
          bas (setLow ts k hk x w) q₀ := by
  induction k generalizing x with
  | zero => simp [treeFrom, setLow]
  | succ k ih =>
      rw [treeFrom, comp_apply, condOp_bas, map_sum]
      set tk : Fin q := ⟨k, by omega⟩ with htk
      have hxk : x (ts tk) = false := hx tk (by simp [tk])
      have hupd : Function.update x (ts tk) false = x := by
        rw [← hxk, Function.update_eq_self]
      simp only [hupd, hxk, map_smul]
      have hrec : ∀ b : Bool, treeFrom ts M k (by omega) (bas (Function.update x (ts tk) b) q₀) =
          ∑ w : Fin k → Bool, (∏ s : Fin k, M ⟨s, by omega⟩
            (setLow ts k (by omega) (Function.update x (ts tk) b) w) (w s) false) •
              bas (setLow ts k (by omega) (Function.update x (ts tk) b) w) q₀ := by
        intro b
        apply ih
        intro t ht
        rw [Function.update_of_ne]
        · exact hx t (by omega)
        · intro h; have := hts h; subst this; simp [tk] at ht
      simp only [hrec, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      rw [← Fintype.sum_equiv (snocEquiv k) (fun p : (Fin k → Bool) × Bool =>
        (M tk x p.2 false * ∏ s : Fin k, M ⟨s, by omega⟩
          (setLow ts k (by omega) (Function.update x (ts tk) p.2) p.1) (p.1 s) false) •
          bas (setLow ts k (by omega) (Function.update x (ts tk) p.2) p.1) q₀)]
      · rw [Fintype.sum_prod_type]
      · intro p
        obtain ⟨w, b⟩ := p
        have hset : setLow ts (k + 1) hk x (Fin.snoc w b) =
            setLow ts k (by omega) (Function.update x (ts tk) b) w := by
          simp only [setLow, Fin.init_snoc, Fin.snoc_last]
          rw [setLow_update_comm ts hts k (by omega) x w tk (by simp [tk])]
        change _ = (∏ s : Fin (k + 1), M ⟨s, by omega⟩ (setLow ts (k + 1) hk x (Fin.snoc w b))
          ((Fin.snoc w b : Fin (k + 1) → Bool) s) false) • bas (setLow ts (k + 1) hk x
            (Fin.snoc w b)) q₀
        rw [hset, Fin.prod_univ_castSucc]
        simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last]
        congr 1
        rw [mul_comm]
        congr 1
        -- the top matrix does not see the lower tree bits
        have key : ∀ (j : ℕ) (hj : j ≤ k) (y : Cfg W) (u : Fin j → Bool),
            M tk (setLow ts j (by omega) y u) = M tk y := by
          intro j hj y u
          induction j with
          | zero => rfl
          | succ j ihj =>
              simp only [setLow]
              rw [hM tk _ ⟨j, by omega⟩ (by simp [tk]; omega), ihj (by omega)]
        rw [key k le_rfl, hM tk x tk le_rfl]

theorem treeOp_bas {q : ℕ} (ts : Fin q → W) (hts : Function.Injective ts)
    (M : Fin q → Cfg W → Matrix Bool Bool ℂ)
    (hM : ∀ s : Fin q, ∀ y : Cfg W, ∀ t : Fin q, t.val ≤ s.val → ∀ b,
      M s (Function.update y (ts t) b) = M s y)
    (x : Cfg W) (hx : ∀ t : Fin q, x (ts t) = false) (q₀ : Q) :
    treeOp ts M (bas x q₀) =
      ∑ w : Fin q → Bool, (∏ s : Fin q, M s (setLow ts q le_rfl x w) (w s) false) •
        bas (setLow ts q le_rfl x w) q₀ :=
  treeFrom_bas ts hts M hM q le_rfl x (fun t _ => hx t) q₀

/-! ### Conditional masses and the telescoping product -/

section Telescope

variable {q : ℕ} (f : (Fin q → Bool) → ℝ)

/-- Words agreeing with `w` on every bit `≥ s`. -/
def cone (s : ℕ) (w v : Fin q → Bool) : Prop := ∀ i : Fin q, s ≤ i.val → v i = w i

instance (s : ℕ) (w v : Fin q → Bool) : Decidable (cone s w v) := by
  unfold cone; infer_instance

/-- Squared mass of the subtree of `w` at level `s`. -/
def mass (s : ℕ) (w : Fin q → Bool) : ℝ := ∑ v, if cone s w v then f v ^ 2 else 0

theorem mass_nonneg (s : ℕ) (w : Fin q → Bool) : 0 ≤ mass f s w :=
  Finset.sum_nonneg (fun v _ => by split_ifs <;> positivity)

theorem mass_zero (w : Fin q → Bool) : mass f 0 w = f w ^ 2 := by
  unfold mass
  rw [Finset.sum_eq_single w]
  · simp [cone]
  · intro v _ hv
    rw [if_neg]
    intro h
    exact hv (funext (fun i => h i (Nat.zero_le _)))
  · intro h; exact absurd (Finset.mem_univ _) h

theorem mass_top (s : ℕ) (hs : q ≤ s) (w : Fin q → Bool) : mass f s w = ∑ v, f v ^ 2 := by
  unfold mass
  apply Finset.sum_congr rfl
  intro v _
  rw [if_pos]
  intro i hi
  exact absurd i.isLt (by omega)

theorem cone_update (s : Fin q) (w v : Fin q → Bool) (b : Bool) :
    cone s (Function.update w s b) v ↔ (v s = b ∧ cone (s + 1) w v) := by
  unfold cone
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have := h s le_rfl; rwa [Function.update_self] at this
    · intro i hi
      have hne : i ≠ s := fun e => by subst e; omega
      have := h i (by omega)
      rwa [Function.update_of_ne hne] at this
  · rintro ⟨h1, h2⟩ i hi
    by_cases hne : i = s
    · subst hne; rw [Function.update_self]; exact h1
    · rw [Function.update_of_ne hne]
      exact h2 i (by
        have : i.val ≠ s.val := fun e => hne (Fin.ext e)
        omega)

theorem mass_split (s : Fin q) (w : Fin q → Bool) :
    mass f s (Function.update w s false) + mass f s (Function.update w s true) =
      mass f (s + 1) w := by
  unfold mass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  simp only [cone_update]
  cases hv : v s <;> by_cases hc : cone (s + 1) w v <;> simp [hc]

theorem mass_le (s : Fin q) (w : Fin q → Bool) : mass f s w ≤ mass f (s + 1) w := by
  rw [← mass_split f s w]
  cases hw : w s
  · have : Function.update w s false = w := by rw [← hw, Function.update_eq_self]
    rw [this]; linarith [mass_nonneg f s (Function.update w s true)]
  · have : Function.update w s true = w := by rw [← hw, Function.update_eq_self]
    rw [this]; linarith [mass_nonneg f s (Function.update w s false)]

/-- The first column of the live tree rotation at level `s` (row `b`). -/
def treeCol (s : Fin q) (w : Fin q → Bool) (b : Bool) : ℝ :=
  (if s.val = 0 then f (Function.update w s b) else Real.sqrt (mass f s (Function.update w s b))) /
    Real.sqrt (mass f (s + 1) w)

/-- Partial product over the levels `≥ k`. -/
def topProd (amp : Fin q → (Fin q → Bool) → ℂ) (w : Fin q → Bool) (k : ℕ) : ℂ :=
  ∏ s ∈ Finset.univ.filter (fun s : Fin q => k ≤ s.val), amp s w

theorem topProd_step (amp : Fin q → (Fin q → Bool) → ℂ) (w : Fin q → Bool) (k : ℕ) (hk : k < q) :
    topProd amp w k = amp ⟨k, hk⟩ w * topProd amp w (k + 1) := by
  unfold topProd
  have : Finset.univ.filter (fun s : Fin q => k ≤ s.val) =
      insert ⟨k, hk⟩ (Finset.univ.filter (fun s : Fin q => k + 1 ≤ s.val)) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro h
      by_cases hs : s.val = k
      · left; exact Fin.ext hs
      · right; omega
    · rintro (h | h)
      · subst h; simp
      · omega
  rw [this, Finset.prod_insert]
  simp

theorem topProd_live (hf : ∑ v, f v ^ 2 = 1) (amp : Fin q → (Fin q → Bool) → ℂ)
    (hamp : ∀ (s : Fin q) w, 0 < mass f (s.val + 1) w → amp s w = (treeCol f s w (w s) : ℂ))
    (w : Fin q → Bool) (d : ℕ) (hd : d + 1 ≤ q) :
    topProd amp w (q - d) = (Real.sqrt (mass f (q - d) w) : ℂ) := by
  induction d with
  | zero =>
      have h1 : topProd amp w q = 1 := by
        unfold topProd
        rw [Finset.prod_eq_one]
        intro s hs
        simp only [Finset.mem_filter] at hs
        exact absurd s.isLt (by omega)
      simp [h1, mass_top f q le_rfl, hf]
  | succ d ih =>
      have hk : q - (d + 1) < q := by omega
      have hk1 : q - (d + 1) + 1 = q - d := by omega
      rw [topProd_step amp w _ hk, hk1, ih (by omega)]
      have hpos : (⟨q - (d + 1), hk⟩ : Fin q).val ≠ 0 := by simp; omega
      by_cases hm : 0 < mass f (q - d) w
      · rw [hamp ⟨q - (d + 1), hk⟩ w (by simpa [hk1] using hm)]
        simp only [treeCol, if_neg hpos, Function.update_eq_self]
        have : (⟨q - (d + 1), hk⟩ : Fin q).val + 1 = q - d := by simp; omega
        rw [this]
        have hs : Real.sqrt (mass f (q - d) w) ≠ 0 := (Real.sqrt_pos.mpr hm).ne'
        push_cast
        rw [div_mul_cancel₀ _ (by exact_mod_cast hs)]
      · have h0 : mass f (q - d) w = 0 := le_antisymm (not_lt.mp hm) (mass_nonneg f _ w)
        have h0' : mass f (q - (d + 1)) w = 0 := by
          have := mass_le f ⟨q - (d + 1), hk⟩ w
          simp only at this
          rw [hk1, h0] at this
          exact le_antisymm this (mass_nonneg f _ w)
        rw [h0, h0']
        simp

/-- The tree amplitudes telescope to the target amplitude. -/
theorem tree_telescope (hq : 0 < q) (hf : ∑ v, f v ^ 2 = 1) (amp : Fin q → (Fin q → Bool) → ℂ)
    (hamp : ∀ (s : Fin q) w, 0 < mass f (s.val + 1) w → amp s w = (treeCol f s w (w s) : ℂ))
    (w : Fin q → Bool) : ∏ s, amp s w = (f w : ℂ) := by
  have hall : ∏ s, amp s w = topProd amp w 0 := by
    unfold topProd; congr 1; ext s; simp
  rw [hall, topProd_step amp w 0 hq]
  have h1 := topProd_live f hf amp hamp w (q - 1) (by omega)
  rw [show q - (q - 1) = 1 by omega] at h1
  rw [show (0 : ℕ) + 1 = 1 from rfl, h1]
  by_cases hm : 0 < mass f 1 w
  · rw [hamp ⟨0, hq⟩ w (by simpa using hm)]
    simp only [treeCol, if_true, Function.update_eq_self]
    have hs : Real.sqrt (mass f 1 w) ≠ 0 := (Real.sqrt_pos.mpr hm).ne'
    simp only [zero_add]
    push_cast
    rw [div_mul_cancel₀ _ (by exact_mod_cast hs)]
  · have h0 : mass f 1 w = 0 := le_antisymm (not_lt.mp hm) (mass_nonneg f _ w)
    have hfw : f w = 0 := by
      have := mass_le f ⟨0, hq⟩ w
      simp only [zero_add] at this
      rw [h0, mass_zero] at this
      have : f w ^ 2 = 0 := le_antisymm this (sq_nonneg _)
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    simp [h0, hfw]

end Telescope

end

end SparseHamiltonian.GateCircuit
