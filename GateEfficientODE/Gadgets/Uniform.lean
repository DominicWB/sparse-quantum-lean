import GateEfficientODE.Model.Block

/-!
# Uniformly controlled gates on a register of tree wires

For tree wires `ts : Fin q → W` and a pool of clean flags, `ucgT` applies, on
the wire `ts s`, a one-qubit matrix selected by the bits above `s`: one
many-controlled gate (an AND chain on the pool) for every assignment of those
bits.  On configurations with a clean pool it agrees with the ideal
selected gate (`ucgT_agrees`), and it uses at most `2q + 1` elementary gates
per assignment.

Two instances are used by the solver.

* `prepT f`: the rotation tree preparing real amplitudes `f` on the tree
  wires (`prepT_agrees`, `treeOp_zero`), with at most `2^q (2q + 1)` gates.
  This is the explicit state preparation of the LCHS coefficient register.
* `phaseT φ`: the diagonal phase `|w⟩ ↦ φ w |w⟩` (`phaseT_agrees`,
  `phaseOp_bas`), a uniformly controlled diagonal gate on the lowest tree
  wire, with at most `2^q (2q + 1)` gates.

`constT` lists uncontrolled one-qubit gates on distinct wires; it is the
product state preparation of the source labels.
-/

namespace SparseHamiltonian.GateODE

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit
open GateCircuit.Sim (HiZero hiWords canon canon_hiZero mem_hiWords hiWords_nodup
  hiWords_length treeMat_congr geomSum_le)
open scoped InnerProduct BigOperators

variable {W : Type*} [Fintype W] [DecidableEq W]
variable {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] [CompleteSpace Q]
variable {q : ℕ}

/-- The word carried by the tree wires. -/
def wordOf (ts : Fin q → W) (x : Cfg W) : Fin q → Bool := fun i => x (ts i)

omit [Fintype W] in
theorem wordOf_update {ts : Fin q → W} (hts : Function.Injective ts) (x : Cfg W) (t : Fin q)
    (b : Bool) : wordOf ts (Function.update x (ts t) b) = Function.update (wordOf ts x) t b := by
  funext i
  by_cases h : i = t
  · subst h; simp [wordOf]
  · simp only [wordOf]
    rw [Function.update_of_ne (fun e => h (hts e)), Function.update_of_ne h]
    rfl

omit [Fintype W] in
theorem wordOf_update_other (ts : Fin q → W) (x : Cfg W) (v : W) (hv : ∀ i, ts i ≠ v)
    (b : Bool) : wordOf ts (Function.update x v b) = wordOf ts x := by
  funext i
  simp only [wordOf]
  rw [Function.update_of_ne (hv i)]

/-! ### Literals of a higher-bit assignment -/

/-- Literals fixing the bits above `s` to those of `w`. -/
def prefLitsG (ts : Fin q → W) (s : ℕ) (w : Fin q → Bool) : List (W × Bool) :=
  ((List.finRange q).filter (fun i => s < i.val)).map (fun i => (ts i, w i))

omit [Fintype W] [DecidableEq W] in
theorem mem_prefLitsG (ts : Fin q → W) (s : ℕ) (w : Fin q → Bool) (c : W × Bool)
    (hc : c ∈ prefLitsG ts s w) : ∃ i : Fin q, s < i.val ∧ c = (ts i, w i) := by
  simp only [prefLitsG, List.mem_map, List.mem_filter, List.mem_finRange, true_and,
    decide_eq_true_eq] at hc
  obtain ⟨i, hi, rfl⟩ := hc
  exact ⟨i, hi, rfl⟩

omit [Fintype W] [DecidableEq W] in
theorem prefLitsG_length (ts : Fin q → W) (s : ℕ) (w : Fin q → Bool) :
    (prefLitsG ts s w).length ≤ q := by
  simp only [prefLitsG, List.length_map]
  exact (List.length_filter_le _ _).trans (by simp)

omit [Fintype W] [DecidableEq W] in
theorem prefLitsG_iff (ts : Fin q → W) (s : ℕ) (w : Fin q → Bool) (hw : HiZero s w)
    (x : Cfg W) : ctrlOK (prefLitsG ts s w) x = true ↔ canon s (wordOf ts x) = w := by
  rw [ctrlOK_iff]
  constructor
  · intro h
    funext i
    simp only [canon]
    split_ifs with hi
    · exact h (ts i, w i) (List.mem_map.mpr ⟨i, by simp [hi], rfl⟩)
    · exact (hw i (by omega)).symm
  · intro h c hc
    obtain ⟨i, hi, rfl⟩ := mem_prefLitsG ts s w c hc
    rw [← h]
    simp only [canon, if_pos hi]
    rfl

omit [Fintype W] [DecidableEq W] in
theorem prefLitsG_ne_t {ts : Fin q → W} (hts : Function.Injective ts) (s : ℕ) (hs : s < q)
    (w : Fin q → Bool) : ∀ l ∈ prefLitsG ts s w, l.1 ≠ ts ⟨s, hs⟩ := by
  intro l hl
  obtain ⟨i, hi, rfl⟩ := mem_prefLitsG ts s w l hl
  intro e
  have := congrArg Fin.val (hts e)
  simp at this
  omega

/-! ### Uniformly controlled gates -/

/-- The data of a tree register with a pool of clean flags. -/
structure TreePool (W : Type*) (q : ℕ) where
  ts : Fin q → W
  pool : List W

/-- Hypotheses on a tree register and its pool. -/
structure TreePool.OK (T : TreePool W q) (S : Cfg W → Prop) : Prop where
  inj : Function.Injective T.ts
  nodup : T.pool.Nodup
  len : q ≤ T.pool.length + 1
  disj : ∀ i, ∀ f ∈ T.pool, T.ts i ≠ f
  clean : ∀ x, S x → ∀ f ∈ T.pool, x f = false
  stable : ∀ x i b, S x → S (Function.update x (T.ts i) b)

/-- One many-controlled gate on `ts s` for every assignment in `L` of the
bits above `s`. -/
def ucgT (T : TreePool W q) (s : ℕ) (hs : s < q) (M : (Fin q → Bool) → Matrix Bool Bool ℂ)
    (L : List (Fin q → Bool)) : List (Gate W) :=
  L.flatMap (fun w => mcGate (prefLitsG T.ts s w) T.pool (T.ts ⟨s, hs⟩) (M w))

theorem ucgT_agrees (T : TreePool W q) (S : Cfg W → Prop) (hT : T.OK S) (s : ℕ) (hs : s < q)
    (M : (Fin q → Bool) → Matrix Bool Bool ℂ) (L : List (Fin q → Bool)) (hL : L.Nodup)
    (hLz : ∀ w ∈ L, HiZero s w) :
    Agrees S (gRun (Q := Q) (ucgT T s hs M L))
      (condOp (T.ts ⟨s, hs⟩) (fun x => if canon s (wordOf T.ts x) ∈ L then
        M (canon s (wordOf T.ts x)) else 1)) := by
  induction L with
  | nil =>
      simp only [ucgT, List.flatMap_nil, List.not_mem_nil, if_false]
      rw [condOp_one]
      exact Agrees.refl _ _
  | cons w L ih =>
      have hL' := List.nodup_cons.mp hL
      rw [ucgT, List.flatMap_cons, gRun_append]
      have hmc : Agrees S (gRun (Q := Q) (mcGate (prefLitsG T.ts s w) T.pool
          (T.ts ⟨s, hs⟩) (M w))) (gateOp (prefLitsG T.ts s w) (T.ts ⟨s, hs⟩) (M w)) :=
        mcGate_agrees _ _ _ _ ((prefLitsG_length T.ts s w).trans hT.len) hT.nodup
          (prefLitsG_ne_t hT.inj s hs w)
          (fun f hf e => hT.disj ⟨s, hs⟩ f hf e.symm)
          (fun l hl f hf => by
            obtain ⟨i, _, rfl⟩ := mem_prefLitsG T.ts s w l hl
            exact hT.disj i f hf)
          S hT.clean (fun x b hx => hT.stable x ⟨s, hs⟩ b hx)
      have hrest := ih hL'.2 (fun w' hw' => hLz w' (List.mem_cons_of_mem w hw'))
      have h := hmc.comp (pres2_gateOp _ _ _ _ (fun x b hx => hT.stable x ⟨s, hs⟩ b hx)).1
        hrest
      have e : (condOp (Q := Q) (T.ts ⟨s, hs⟩) (fun x =>
          if canon s (wordOf T.ts x) ∈ L then M (canon s (wordOf T.ts x)) else 1)) ∘L
            gateOp (prefLitsG T.ts s w) (T.ts ⟨s, hs⟩) (M w) =
          condOp (T.ts ⟨s, hs⟩) (fun x => if canon s (wordOf T.ts x) ∈ w :: L then
            M (canon s (wordOf T.ts x)) else 1) := by
        rw [gateOp, condOp_comp]
        congr 1
        funext x
        by_cases hc : canon s (wordOf T.ts x) = w
        · have hct : ctrlOK (prefLitsG T.ts s w) x = true :=
            (prefLitsG_iff T.ts s w (hLz w List.mem_cons_self) x).mpr hc
          rw [if_pos hct, if_neg (by rw [hc]; exact hL'.1),
            if_pos (by rw [hc]; exact List.mem_cons_self), Matrix.one_mul, hc]
        · have hcf : ¬ ctrlOK (prefLitsG T.ts s w) x = true :=
            fun h' => hc ((prefLitsG_iff T.ts s w (hLz w List.mem_cons_self) x).mp h')
          rw [if_neg hcf, Matrix.mul_one]
          have hmem : canon s (wordOf T.ts x) ∈ w :: L ↔ canon s (wordOf T.ts x) ∈ L := by
            simp [hc]
          simp only [hmem]
      rw [e] at h
      exact h

/-- Over all assignments of the higher bits, `ucgT` is the selected gate. -/
theorem ucgT_full_agrees (T : TreePool W q) (S : Cfg W → Prop) (hT : T.OK S) (s : ℕ)
    (hs : s < q) (M : (Fin q → Bool) → Matrix Bool Bool ℂ) :
    Agrees S (gRun (Q := Q) (ucgT T s hs M (hiWords s)))
      (condOp (T.ts ⟨s, hs⟩) (fun x => M (canon s (wordOf T.ts x)))) := by
  have h := ucgT_agrees (Q := Q) T S hT s hs M (hiWords s) (hiWords_nodup s)
    (fun w hw => (mem_hiWords s w).mp hw)
  have e : (fun x => if canon s (wordOf T.ts x) ∈ hiWords s then
      M (canon s (wordOf T.ts x)) else 1) = (fun x => M (canon s (wordOf T.ts x))) := by
    funext x
    rw [if_pos ((mem_hiWords s _).mpr (canon_hiZero s _))]
  rw [e] at h
  exact h

omit [Fintype W] [DecidableEq W] in
theorem ucgT_length (T : TreePool W q) (s : ℕ) (hs : s < q)
    (M : (Fin q → Bool) → Matrix Bool Bool ℂ) (L : List (Fin q → Bool)) :
    (ucgT T s hs M L).length ≤ L.length * (2 * q + 1) := by
  induction L with
  | nil => simp [ucgT]
  | cons w L ih =>
      rw [ucgT, List.flatMap_cons, List.length_append, List.length_cons]
      have h1 := mcGate_length_le (prefLitsG T.ts s w) T.pool (T.ts ⟨s, hs⟩) (M w)
      have h2 := prefLitsG_length T.ts s w
      have h3 : (ucgT T s hs M L).length ≤ L.length * (2 * q + 1) := ih
      change (mcGate _ _ _ _).length + (L.flatMap _).length ≤ _
      change _ + (ucgT T s hs M L).length ≤ _
      nlinarith

omit [Fintype W] [DecidableEq W] in
theorem ucgT_ok (T : TreePool W q) (hinj : Function.Injective T.ts) (hnd : T.pool.Nodup)
    (hdisj : ∀ i, ∀ f ∈ T.pool, T.ts i ≠ f) (s : ℕ) (hs : s < q)
    (M : (Fin q → Bool) → Matrix Bool Bool ℂ) (hM : ∀ w, UnitaryMat (M w))
    (L : List (Fin q → Bool)) : ∀ g ∈ ucgT T s hs M L, GateOK 2 g := by
  intro g hg
  simp only [ucgT, List.mem_flatMap] at hg
  obtain ⟨w, _, hg⟩ := hg
  exact mcGate_valid _ _ _ _ (hM w) hnd (prefLitsG_ne_t hinj s hs w)
    (fun f hf e => hdisj ⟨s, hs⟩ f hf e.symm)
    (fun l hl f hf => by
      obtain ⟨i, _, rfl⟩ := mem_prefLitsG T.ts s w l hl
      exact hdisj i f hf) g hg

/-! ### The rotation tree -/

/-- Rotations of the tree bits `k-1, …, 0`. -/
def prepT (T : TreePool W q) (f : (Fin q → Bool) → ℝ) : ℕ → List (Gate W)
  | 0 => []
  | k + 1 => (if h : k < q then ucgT T k h (treeMat f ⟨k, h⟩) (hiWords k) else []) ++ prepT T f k

/-- The ideal tree matrices read from the tree word. -/
def treeSel (ts : Fin q → W) (f : (Fin q → Bool) → ℝ) (s : Fin q) (x : Cfg W) :
    Matrix Bool Bool ℂ :=
  treeMat f s (wordOf ts x)

theorem prepT_agrees (T : TreePool W q) (S : Cfg W → Prop) (hT : T.OK S)
    (f : (Fin q → Bool) → ℝ) (k : ℕ) (hk : k ≤ q) :
    Agrees S (gRun (Q := Q) (prepT T f k)) (treeFrom T.ts (treeSel T.ts f) k hk) := by
  induction k with
  | zero => exact Agrees.refl _ _
  | succ k ih =>
      rw [prepT, gRun_append, treeFrom, dif_pos (show k < q by omega)]
      have hlev := ucgT_full_agrees (Q := Q) T S hT k (by omega) (treeMat f ⟨k, by omega⟩)
      have e : (fun x => treeMat f ⟨k, by omega⟩ (canon k (wordOf T.ts x))) =
          treeSel T.ts f ⟨k, by omega⟩ := by
        funext x
        apply treeMat_congr
        intro i hi
        simp only [canon, if_pos hi]
      rw [e] at hlev
      exact hlev.comp (preserves_condOp _ _ _ (fun x b hx => hT.stable x _ b hx)) (ih (by omega))

omit [Fintype W] [DecidableEq W] in
theorem prepT_length (T : TreePool W q) (f : (Fin q → Bool) → ℝ) (k : ℕ) (hk : k ≤ q) :
    (prepT T f k).length ≤ (∑ s ∈ Finset.range k, 2 ^ (q - 1 - s)) * (2 * q + 1) := by
  induction k with
  | zero => simp [prepT]
  | succ k ih =>
      rw [prepT, List.length_append, dif_pos (show k < q by omega), Finset.sum_range_succ]
      have h1 := ucgT_length T k (by omega) (treeMat f ⟨k, by omega⟩) (hiWords k)
      have h2 := hiWords_length (r := q) k
      have h3 := ih (by omega)
      nlinarith

omit [Fintype W] [DecidableEq W] in
theorem prepT_length_le (T : TreePool W q) (f : (Fin q → Bool) → ℝ) :
    (prepT T f q).length ≤ 2 ^ q * (2 * q + 1) := by
  have h := prepT_length T f q le_rfl
  have hs := geomSum_le (r := q) q le_rfl
  have hS : (∑ s ∈ Finset.range q, 2 ^ (q - 1 - s)) ≤ 2 ^ q := by
    rw [← hs]; exact Nat.le_add_right _ _
  exact h.trans (Nat.mul_le_mul_right _ hS)

omit [Fintype W] [DecidableEq W] in
theorem prepT_ok (T : TreePool W q) (hinj : Function.Injective T.ts) (hnd : T.pool.Nodup)
    (hdisj : ∀ i, ∀ f ∈ T.pool, T.ts i ≠ f) (f : (Fin q → Bool) → ℝ) (k : ℕ) :
    ∀ g ∈ prepT T f k, GateOK 2 g := by
  induction k with
  | zero => intro g hg; simp [prepT] at hg
  | succ k ih =>
      intro g hg
      rw [prepT, List.mem_append] at hg
      rcases hg with hg | hg
      · split_ifs at hg with h
        · exact ucgT_ok T hinj hnd hdisj k h _ (fun w => treeMat_unitary f _ w) _ g hg
        · simp at hg
      · exact ih g hg

/-- The rotation tree prepares the amplitudes `f` from a configuration with
clear tree wires. -/
theorem treeOp_zero {ts : Fin q → W} (hts : Function.Injective ts) (hq : 0 < q)
    (f : (Fin q → Bool) → ℝ) (hf : ∑ w, f w ^ 2 = 1) (x : Cfg W)
    (hx : ∀ i, x (ts i) = false) (p : Q) :
    treeOp ts (treeSel ts f) (bas x p) =
      ∑ w, (f w : ℂ) • bas (setLow ts q le_rfl x w) p := by
  rw [treeOp_bas ts hts (treeSel ts f)
    (fun s y t ht b => by
      simp only [treeSel]
      rw [wordOf_update hts]
      exact treeMat_update_low f s _ t ht b) x hx]
  apply Finset.sum_congr rfl
  intro w _
  congr 1
  have hword : wordOf ts (setLow ts q le_rfl x w) = w := by
    funext i
    exact setLow_apply_low ts hts q le_rfl x w i
  simp only [treeSel, hword]
  exact tree_telescope f hq hf (fun s w => treeMat f s w (w s) false)
    (fun s w hlive => treeMat_col f s w hlive (w s)) w

/-! ### Diagonal phases -/

/-- The diagonal one-qubit matrix of the lowest bit, the other bits read from `w`. -/
def phaseMat (hq : 0 < q) (φ : (Fin q → Bool) → ℂ) (w : Fin q → Bool) :
    Matrix Bool Bool ℂ :=
  fun b c => if b = c then φ (Function.update w ⟨0, hq⟩ b) else 0

theorem phaseMat_unitary (hq : 0 < q) (φ : (Fin q → Bool) → ℂ) (hφ : ∀ w, ‖φ w‖ = 1)
    (w : Fin q → Bool) : UnitaryMat (phaseMat hq φ w) := by
  have hc : ∀ z : ℂ, ‖z‖ = 1 → (starRingEnd ℂ) z * z = 1 := by
    intro z hz
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hz]
    norm_num
  have hc' : ∀ z : ℂ, ‖z‖ = 1 → z * (starRingEnd ℂ) z = 1 := by
    intro z hz
    rw [mul_comm]
    exact hc z hz
  constructor
  · funext b c
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, phaseMat, Matrix.one_apply,
      Fintype.sum_bool]
    cases b <;> cases c <;> simp [hc _ (hφ _)]
  · funext b c
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, phaseMat, Matrix.one_apply,
      Fintype.sum_bool]
    cases b <;> cases c <;> simp [hc' _ (hφ _)]

/-- The diagonal phase as a uniformly controlled gate on `ts 0`. -/
def phaseT (T : TreePool W q) (hq : 0 < q) (φ : (Fin q → Bool) → ℂ) : List (Gate W) :=
  ucgT T 0 hq (phaseMat hq φ) (hiWords 0)

/-- The ideal diagonal phase. -/
def phaseOp (ts : Fin q → W) (hq : 0 < q) (φ : (Fin q → Bool) → ℂ) : Reg W Q →L[ℂ] Reg W Q :=
  condOp (ts ⟨0, hq⟩) (fun x => phaseMat hq φ (wordOf ts x))

theorem phaseT_agrees (T : TreePool W q) (S : Cfg W → Prop) (hT : T.OK S) (hq : 0 < q)
    (φ : (Fin q → Bool) → ℂ) :
    Agrees S (gRun (Q := Q) (phaseT T hq φ)) (phaseOp T.ts hq φ) := by
  have h := ucgT_full_agrees (Q := Q) T S hT 0 hq (phaseMat hq φ)
  have e : (fun x => phaseMat hq φ (canon 0 (wordOf T.ts x))) =
      (fun x => phaseMat hq φ (wordOf T.ts x)) := by
    funext x b c
    simp only [phaseMat]
    congr 2
    funext i
    by_cases hi : i = ⟨0, hq⟩
    · subst hi; simp
    · rw [Function.update_of_ne hi, Function.update_of_ne hi]
      simp only [canon]
      rw [if_pos]
      have : i.val ≠ 0 := fun e => hi (Fin.ext e)
      omega
  rw [e] at h
  exact h

theorem phaseOp_bas {ts : Fin q → W} (hts : Function.Injective ts) (hq : 0 < q)
    (φ : (Fin q → Bool) → ℂ) (x : Cfg W) (p : Q) :
    phaseOp ts hq φ (bas x p) = φ (wordOf ts x) • bas x p := by
  rw [phaseOp, condOp_bas, Fintype.sum_bool]
  have hw : wordOf ts (Function.update x (ts ⟨0, hq⟩) false) =
      Function.update (wordOf ts x) ⟨0, hq⟩ false := wordOf_update hts x _ false
  have hupd : ∀ b, Function.update (wordOf ts x) ⟨0, hq⟩ b =
      Function.update (Function.update (wordOf ts x) ⟨0, hq⟩ false) ⟨0, hq⟩ b := by
    intro b; rw [Function.update_idem]
  cases hx : x (ts ⟨0, hq⟩)
  · simp only [phaseMat, hw, if_true, Bool.true_eq_false, if_false, zero_smul, zero_add]
    have hxw : Function.update x (ts ⟨0, hq⟩) false = x := by
      rw [← hx, Function.update_eq_self]
    rw [hxw, ← hupd]
    have : Function.update (wordOf ts x) ⟨0, hq⟩ false = wordOf ts x := by
      have : wordOf ts x ⟨0, hq⟩ = false := hx
      rw [← this, Function.update_eq_self]
    rw [this]
  · simp only [phaseMat, hw, Bool.false_eq_true, if_false, zero_smul, if_true, add_zero]
    have hxw : Function.update x (ts ⟨0, hq⟩) true = x := by
      rw [← hx, Function.update_eq_self]
    rw [hxw, ← hupd]
    have : Function.update (wordOf ts x) ⟨0, hq⟩ true = wordOf ts x := by
      have : wordOf ts x ⟨0, hq⟩ = true := hx
      rw [← this, Function.update_eq_self]
    rw [this]

omit [Fintype W] [DecidableEq W] in
theorem phaseT_length (T : TreePool W q) (hq : 0 < q) (φ : (Fin q → Bool) → ℂ) :
    (phaseT T hq φ).length ≤ 2 ^ q * (2 * q + 1) := by
  have h1 := ucgT_length T 0 hq (phaseMat hq φ) (hiWords 0)
  have h2 := hiWords_length (r := q) 0
  have h3 : 2 ^ (q - 1 - 0) ≤ 2 ^ q := Nat.pow_le_pow_right (by norm_num) (by omega)
  unfold phaseT
  nlinarith

/-! ### Uncontrolled gates on distinct wires -/

/-- The gates `U (k-1), …, U 0` on the wires `ts (k-1), …, ts 0`. -/
def constT (ts : Fin q → W) (U : Fin q → Matrix Bool Bool ℂ) : ℕ → List (Gate W)
  | 0 => []
  | k + 1 => (if h : k < q then [⟨[], ts ⟨k, h⟩, U ⟨k, h⟩⟩] else []) ++ constT ts U k

theorem gRun_constT (ts : Fin q → W) (U : Fin q → Matrix Bool Bool ℂ) (k : ℕ) (hk : k ≤ q) :
    gRun (Q := Q) (constT ts U k) = treeFrom ts (fun s _ => U s) k hk := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [constT, dif_pos (show k < q by omega), gRun_append, ih (by omega), treeFrom,
        gRun_singleton]
      rfl

omit [Fintype W] [DecidableEq W] in
theorem constT_length (ts : Fin q → W) (U : Fin q → Matrix Bool Bool ℂ) (k : ℕ) :
    (constT ts U k).length ≤ k := by
  induction k with
  | zero => simp [constT]
  | succ k ih =>
      rw [constT, List.length_append]
      split_ifs <;> simp <;> omega

omit [Fintype W] [DecidableEq W] in
theorem constT_ok (ts : Fin q → W) (U : Fin q → Matrix Bool Bool ℂ) (hU : ∀ s, UnitaryMat (U s))
    (k : ℕ) : ∀ g ∈ constT ts U k, GateOK 0 g := by
  induction k with
  | zero => intro g hg; simp [constT] at hg
  | succ k ih =>
      intro g hg
      rw [constT, List.mem_append] at hg
      rcases hg with hg | hg
      · split_ifs at hg with h
        · simp only [List.mem_singleton] at hg
          subst hg
          exact ⟨by simp, by simp, hU _⟩
        · simp at hg
      · exact ih g hg

end

end SparseHamiltonian.GateODE
