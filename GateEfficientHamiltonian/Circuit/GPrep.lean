import GateEfficientHamiltonian.Circuit.GRange

/-!
# Gate-level label-table preparation and clean reflection

`PREP f` rotates label bit `s` (top bit first) by the live tree matrix of the
higher label bits.  It is a uniformly controlled rotation: one
many-controlled rotation for each assignment of the higher bits.  With
`2^(r-1-s)` assignments at level `s`, the whole table uses at most
`(2r+1)·2^r` elementary gates (`prep_agrees`, `prepG_length`).

The reflection about the clean subspace is a many-controlled phase on the zero
logical word followed by a global phase `-1` (`zr_agrees`).
-/

namespace SparseHamiltonian.GateCircuit.Sim

noncomputable section
open ContinuousLinearMap OracleCircuit
open scoped InnerProduct BigOperators
open GatePointerEncoding (wordValue wordEquivFin wordFin)

variable {a m r K : ℕ}
variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-! ### Tree matrices depend only on the higher bits -/

section TreeCongr

variable {q : ℕ} (f : (Fin q → Bool) → ℝ)

theorem mass_congr (k : ℕ) (w w' : Fin q → Bool) (h : ∀ i : Fin q, k ≤ i.val → w i = w' i) :
    mass f k w = mass f k w' := by
  unfold mass
  apply Finset.sum_congr rfl
  intro v _
  have : cone k w v ↔ cone k w' v := by
    unfold cone
    constructor
    · intro hv i hi; rw [hv i hi, h i hi]
    · intro hv i hi; rw [hv i hi, h i hi]
  simp only [this]

theorem treeCol_congr (s : Fin q) (w w' : Fin q → Bool) (h : ∀ i : Fin q, s.val < i.val → w i = w' i)
    (b : Bool) : treeCol f s w b = treeCol f s w' b := by
  unfold treeCol
  have hm : mass f (s + 1) w = mass f (s + 1) w' :=
    mass_congr f _ w w' (fun i hi => h i (by omega))
  rw [hm]
  congr 1
  split_ifs with hs0
  · congr 1
    funext i
    by_cases his : i = s
    · subst his; simp
    · rw [Function.update_of_ne his, Function.update_of_ne his]
      exact h i (by have : i.val ≠ s.val := fun e => his (Fin.ext e); omega)
  · congr 1
    apply mass_congr
    intro i hi
    by_cases his : i = s
    · subst his; simp
    · rw [Function.update_of_ne his, Function.update_of_ne his]
      exact h i (by have : i.val ≠ s.val := fun e => his (Fin.ext e); omega)

theorem treeMat_congr (s : Fin q) (w w' : Fin q → Bool) (h : ∀ i : Fin q, s.val < i.val → w i = w' i) :
    treeMat f s w = treeMat f s w' := by
  unfold treeMat
  rw [mass_congr f _ w w' (fun i hi => h i (by omega)), treeCol_congr f s w w' h,
    treeCol_congr f s w w' h]

end TreeCongr

/-! ### Higher-bit assignments -/

/-- Words vanishing on the bits `≤ s`. -/
def HiZero (s : ℕ) (w : Word r) : Prop := ∀ i : Fin r, i.val ≤ s → w i = false

instance (s : ℕ) (w : Word r) : Decidable (HiZero s w) := by
  unfold HiZero; infer_instance

/-- All assignments of the bits above `s`. -/
def hiWords (s : ℕ) : List (Word r) := (Finset.univ.filter (HiZero s)).toList

/-- The higher bits of a word. -/
def canon (s : ℕ) (w : Word r) : Word r := fun i => if s < i.val then w i else false

theorem canon_hiZero (s : ℕ) (w : Word r) : HiZero s (canon s w) := by
  intro i hi
  simp only [canon]
  rw [if_neg (by omega)]

theorem mem_hiWords (s : ℕ) (w : Word r) : w ∈ hiWords s ↔ HiZero s w := by
  simp [hiWords]

theorem hiWords_nodup (s : ℕ) : (hiWords (r := r) s).Nodup := Finset.nodup_toList _

theorem hiWords_length (s : ℕ) : (hiWords (r := r) s).length ≤ 2 ^ (r - 1 - s) := by
  rw [hiWords, Finset.length_toList]
  have hcard : (Finset.univ : Finset (Fin (r - 1 - s) → Bool)).card = 2 ^ (r - 1 - s) := by
    simp
  rw [← hcard]
  apply Finset.card_le_card_of_injOn (fun w j => w ⟨s + 1 + j.val, by omega⟩)
  · intro w _; simp
  · intro w hw w' hw' heq
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hw hw'
    funext i
    by_cases hi : i.val ≤ s
    · rw [hw i hi, hw' i hi]
    · have h := congrFun heq ⟨i.val - (s + 1), by omega⟩
      simp only at h
      have he : (⟨s + 1 + (i.val - (s + 1)), by omega⟩ : Fin r) = i := Fin.ext (by simp; omega)
      rwa [he] at h

/-- Literals of a higher-bit assignment on the label wires. -/
def prefLits (s : ℕ) (w : Word r) : List (Wire a m r K × Bool) :=
  ((List.finRange r).filter (fun i => s < i.val)).map (fun i => (Wire.lab i, w i))

theorem mem_prefLits (s : ℕ) (w : Word r) (c : Wire a m r K × Bool) (hc : c ∈ prefLits s w) :
    ∃ i : Fin r, s < i.val ∧ c = (Wire.lab i, w i) := by
  simp only [prefLits, List.mem_map, List.mem_filter, List.mem_finRange, true_and,
    decide_eq_true_eq] at hc
  obtain ⟨i, hi, rfl⟩ := hc
  exact ⟨i, hi, rfl⟩

theorem prefLits_length (s : ℕ) (w : Word r) : (prefLits (a := a) (m := m) (K := K) s w).length ≤ r := by
  simp only [prefLits, List.length_map]
  exact (List.length_filter_le _ _).trans (by simp)

theorem prefLits_iff (s : ℕ) (w : Word r) (hw : HiZero s w) (x : Cfg (Wire a m r K)) :
    ctrlOK (prefLits s w) x = true ↔ canon s (labOf x) = w := by
  rw [ctrlOK_iff]
  constructor
  · intro h
    funext i
    simp only [canon]
    split_ifs with hi
    · exact h (Wire.lab i, w i) (List.mem_map.mpr ⟨i, by simp [hi], rfl⟩)
    · exact (hw i (by omega)).symm
  · intro h c hc
    obtain ⟨i, hi, rfl⟩ := mem_prefLits s w c hc
    rw [← h]
    simp only [canon, if_pos hi]
    rfl

/-! ### Uniformly controlled rotations -/

/-- One many-controlled rotation per assignment in `L`. -/
def ucrG (f : Word r → ℝ) (s : ℕ) (hs : s < r) (L : List (Word r)) : List (Gate (Wire a m r K)) :=
  L.flatMap (fun w => mcGate (prefLits s w) wkList (Wire.lab ⟨s, hs⟩) (treeMat f ⟨s, hs⟩ w))

theorem prefLits_ne_lab (s : ℕ) (hs : s < r) (w : Word r) :
    ∀ l ∈ (prefLits (a := a) (m := m) (K := K) s w), l.1 ≠ Wire.lab ⟨s, hs⟩ := by
  intro l hl
  obtain ⟨i, hi, rfl⟩ := mem_prefLits s w l hl
  intro e
  cases e
  simp at hi

theorem prefLits_ne_wk (s : ℕ) (w : Word r) :
    ∀ l ∈ (prefLits (a := a) (m := m) (K := K) s w), ∀ f ∈ wkList, l.1 ≠ f := by
  intro l hl f hf
  obtain ⟨i, rfl⟩ := (mem_wkList f).mp hf
  obtain ⟨k, _, rfl⟩ := mem_prefLits s w l hl
  simp

theorem ucrG_agrees (f : Word r → ℝ) (s : ℕ) (hs : s < r) (hK : r ≤ K + 1) (L : List (Word r))
    (hL : L.Nodup) (hLz : ∀ w ∈ L, HiZero s w) :
    Agrees Clean (gRun (Q := P) (ucrG (a := a) (m := m) (K := K) f s hs L))
      (condOp (Wire.lab ⟨s, hs⟩) (fun x => if canon s (labOf x) ∈ L then
        treeMat f ⟨s, hs⟩ (canon s (labOf x)) else 1)) := by
  induction L with
  | nil =>
      simp only [ucrG, List.flatMap_nil, List.not_mem_nil, if_false]
      rw [condOp_one]
      exact Agrees.refl _ _
  | cons w L ih =>
      have hL' := List.nodup_cons.mp hL
      rw [ucrG, List.flatMap_cons, gRun_append]
      have hmc : Agrees Clean (gRun (Q := P) (mcGate (prefLits (a := a) (m := m) (K := K) s w) wkList
          (Wire.lab ⟨s, hs⟩) (treeMat f ⟨s, hs⟩ w)))
          (gateOp (prefLits s w) (Wire.lab ⟨s, hs⟩) (treeMat f ⟨s, hs⟩ w)) := by
        apply Agrees.mono (S' := WkClean)
        · exact mcGate_agrees _ _ _ _
            (by have := prefLits_length (a := a) (m := m) (K := K) s w; rw [wkList_length]; omega)
            wkList_nodup (prefLits_ne_lab s hs w)
            (fun f hf => by obtain ⟨i, rfl⟩ := (mem_wkList f).mp hf; simp)
            (prefLits_ne_wk s w) WkClean (fun y hy => hy)
            (fun y b hy f hf => by
              obtain ⟨i, rfl⟩ := (mem_wkList f).mp hf
              rw [Function.update_of_ne (by simp)]
              exact hy _ hf)
        · exact wkClean_of_clean
      have hrest := ih hL'.2 (fun w' hw' => hLz w' (List.mem_cons_of_mem w hw'))
      have h := hmc.comp (pres2_gateOp _ _ _ _ (fun x b h => clean_update_of_logical x _ b rfl h)).1
        hrest
      have e : (condOp (Q := P) (Wire.lab (a := a) (m := m) (K := K) ⟨s, hs⟩) (fun x =>
          if canon s (labOf x) ∈ L then treeMat f ⟨s, hs⟩ (canon s (labOf x)) else 1)) ∘L
            gateOp (prefLits s w) (Wire.lab ⟨s, hs⟩) (treeMat f ⟨s, hs⟩ w) =
          condOp (Wire.lab ⟨s, hs⟩) (fun x => if canon s (labOf x) ∈ w :: L then
            treeMat f ⟨s, hs⟩ (canon s (labOf x)) else 1) := by
        rw [gateOp, condOp_comp]
        congr 1
        funext x
        by_cases hc : canon s (labOf x) = w
        · have hct : ctrlOK (prefLits s w) x = true :=
            (prefLits_iff s w (hLz w List.mem_cons_self) x).mpr hc
          rw [if_pos hct, if_neg (by rw [hc]; exact hL'.1),
            if_pos (by rw [hc]; exact List.mem_cons_self), Matrix.one_mul, hc]
        · have hcf : ¬ ctrlOK (prefLits s w) x = true :=
            fun h' => hc ((prefLits_iff s w (hLz w List.mem_cons_self) x).mp h')
          rw [if_neg hcf, Matrix.mul_one]
          have hmem : canon s (labOf x) ∈ w :: L ↔ canon s (labOf x) ∈ L := by
            simp [hc]
          simp only [hmem]
      rw [e] at h
      exact h

theorem ucr_full_agrees (f : Word r → ℝ) (s : ℕ) (hs : s < r) (hK : r ≤ K + 1) :
    Agrees Clean (gRun (Q := P) (ucrG (a := a) (m := m) (K := K) f s hs (hiWords s)))
      (condOp (labWires (a := a) (m := m) (K := K) ⟨s, hs⟩) (prepM f ⟨s, hs⟩)) := by
  have h := ucrG_agrees (P := P) (a := a) (m := m) (K := K) f s hs hK (hiWords s)
    (hiWords_nodup s) (fun w hw => (mem_hiWords s w).mp hw)
  have e : (condOp (Q := P) (Wire.lab (a := a) (m := m) (K := K) ⟨s, hs⟩) (fun x =>
      if canon s (labOf x) ∈ hiWords s then treeMat f ⟨s, hs⟩ (canon s (labOf x)) else 1)) =
      condOp (labWires (a := a) (m := m) (K := K) ⟨s, hs⟩) (prepM f ⟨s, hs⟩) := by
    unfold labWires prepM
    congr 1
    funext x
    rw [if_pos ((mem_hiWords s _).mpr (canon_hiZero s _))]
    apply treeMat_congr
    intro i hi
    simp only [canon, if_pos hi]
  rw [e] at h
  exact h

/-! ### The label table -/

/-- Rotations of label bits `k-1, …, 0`. -/
def prepCore (f : Word r → ℝ) : ℕ → List (Gate (Wire a m r K))
  | 0 => []
  | k + 1 => (if h : k < r then ucrG f k h (hiWords k) else []) ++ prepCore f k

/-- Gate list of `PREP f`. -/
def prepG (f : Word r → ℝ) : List (Gate (Wire a m r K)) := prepCore f r

theorem prepCore_agrees (f : Word r → ℝ) (hK : r ≤ K + 1) (k : ℕ) (hk : k ≤ r) :
    Agrees Clean (gRun (Q := P) (prepCore (a := a) (m := m) (K := K) f k))
      (treeFrom (labWires (a := a) (m := m) (K := K)) (prepM f) k hk) := by
  induction k with
  | zero => exact Agrees.refl _ _
  | succ k ih =>
      rw [prepCore, gRun_append, treeFrom, dif_pos (show k < r by omega)]
      exact (ucr_full_agrees f k (by omega) hK).comp
        (preserves_condOp _ _ _ (fun x b h => clean_update_of_logical x _ b rfl h)) (ih (by omega))

theorem prep_agrees (f : Word r → ℝ) (hK : r ≤ K + 1) :
    Agrees Clean (gRun (Q := P) (prepG (a := a) (m := m) (K := K) f))
      (PREP (K := K) (m := m) (a := a) (P := P) f) :=
  prepCore_agrees f hK r le_rfl

theorem ucrG_ok (f : Word r → ℝ) (s : ℕ) (hs : s < r) (L : List (Word r)) :
    ∀ g ∈ (ucrG (a := a) (m := m) (K := K) f s hs L), GateOK 2 g := by
  intro g hg
  simp only [ucrG, List.mem_flatMap] at hg
  obtain ⟨w, _, hg⟩ := hg
  exact mcGate_valid _ _ _ _ (treeMat_unitary f _ w) wkList_nodup (prefLits_ne_lab s hs w)
    (fun f hf => by obtain ⟨i, rfl⟩ := (mem_wkList f).mp hf; simp) (prefLits_ne_wk s w) g hg

theorem prepCore_ok (f : Word r → ℝ) (k : ℕ) :
    ∀ g ∈ (prepCore (a := a) (m := m) (K := K) f k), GateOK 2 g := by
  induction k with
  | zero => intro g hg; simp [prepCore] at hg
  | succ k ih =>
      intro g hg
      rw [prepCore, List.mem_append] at hg
      rcases hg with hg | hg
      · split_ifs at hg with h
        · exact ucrG_ok f k h _ g hg
        · simp at hg
      · exact ih g hg

theorem ucrG_length (f : Word r → ℝ) (s : ℕ) (hs : s < r) (L : List (Word r)) :
    (ucrG (a := a) (m := m) (K := K) f s hs L).length ≤ L.length * (2 * r + 1) := by
  induction L with
  | nil => simp [ucrG]
  | cons w L ih =>
      rw [ucrG, List.flatMap_cons, List.length_append, List.length_cons]
      have h1 := mcGate_length_le (prefLits (a := a) (m := m) (K := K) s w) wkList
        (Wire.lab ⟨s, hs⟩) (treeMat f ⟨s, hs⟩ w)
      have h2 := prefLits_length (a := a) (m := m) (K := K) s w
      have h3 : (ucrG (a := a) (m := m) (K := K) f s hs L).length ≤ L.length * (2 * r + 1) := ih
      change (mcGate _ _ _ _).length + (L.flatMap _).length ≤ _
      change _ + (ucrG (a := a) (m := m) (K := K) f s hs L).length ≤ _
      nlinarith

theorem geomSum_le (k : ℕ) (hk : k ≤ r) :
    (∑ s ∈ Finset.range k, 2 ^ (r - 1 - s)) + 2 ^ (r - k) = 2 ^ r := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ]
      have h1 : 2 ^ (r - k) = 2 * 2 ^ (r - (k + 1)) := by
        rw [← pow_succ']
        congr 1
        omega
      have h2 : r - 1 - k = r - (k + 1) := by omega
      rw [h2]
      have := ih (by omega)
      omega

theorem prepCore_length (f : Word r → ℝ) (k : ℕ) (hk : k ≤ r) :
    (prepCore (a := a) (m := m) (K := K) f k).length ≤
      (∑ s ∈ Finset.range k, 2 ^ (r - 1 - s)) * (2 * r + 1) := by
  induction k with
  | zero => simp [prepCore]
  | succ k ih =>
      rw [prepCore, List.length_append, dif_pos (show k < r by omega), Finset.sum_range_succ]
      have h1 := ucrG_length (a := a) (m := m) (K := K) f k (by omega) (hiWords k)
      have h2 := hiWords_length (r := r) k
      have h3 := ih (by omega)
      nlinarith

theorem prepG_length (f : Word r → ℝ) :
    (prepG (a := a) (m := m) (K := K) f).length ≤ 2 ^ r * (2 * r + 1) := by
  have h := prepCore_length (a := a) (m := m) (K := K) f r le_rfl
  have hs := geomSum_le (r := r) r le_rfl
  rw [prepG]
  have hS : (∑ s ∈ Finset.range r, 2 ^ (r - 1 - s)) ≤ 2 ^ r := by
    rw [← hs]; exact Nat.le_add_right _ _
  exact h.trans (Nat.mul_le_mul_right _ hS)

/-! ### The clean reflection -/

/-- Literals of the zero logical word. -/
def zeroLits : List (Wire a m r K × Bool) :=
  (List.finRange a).map (fun i => (Wire.anc i, false)) ++
  (List.finRange m).map (fun i => (Wire.slot i, false)) ++
  (List.finRange r).map (fun i => (Wire.ptr i, false)) ++
  (List.finRange r).map (fun i => (Wire.lab i, false))

theorem zeroLits_length : (zeroLits (a := a) (m := m) (r := r) (K := K)).length = a + m + 2 * r := by
  simp [zeroLits]; ring

theorem mem_zeroLits (c : Wire a m r K × Bool) (hc : c ∈ zeroLits) :
    c.2 = false ∧ ((∃ i, c.1 = Wire.anc i) ∨ (∃ i, c.1 = Wire.slot i) ∨ (∃ i, c.1 = Wire.ptr i) ∨
      (∃ i, c.1 = Wire.lab i)) := by
  simp only [zeroLits, List.mem_append, List.mem_map, List.mem_finRange, true_and] at hc
  rcases hc with ((⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩
  · exact ⟨rfl, Or.inl ⟨i, rfl⟩⟩
  · exact ⟨rfl, Or.inr (Or.inl ⟨i, rfl⟩)⟩
  · exact ⟨rfl, Or.inr (Or.inr (Or.inl ⟨i, rfl⟩))⟩
  · exact ⟨rfl, Or.inr (Or.inr (Or.inr ⟨i, rfl⟩))⟩

theorem zeroLits_ne_sec : ∀ l ∈ (zeroLits (a := a) (m := m) (r := r) (K := K)), l.1 ≠ Wire.sec := by
  intro l hl
  rcases (mem_zeroLits l hl).2 with ⟨i, h⟩ | ⟨i, h⟩ | ⟨i, h⟩ | ⟨i, h⟩ <;> rw [h] <;> simp

theorem zeroLits_ne_wk : ∀ l ∈ (zeroLits (a := a) (m := m) (r := r) (K := K)), ∀ f ∈ wkList, l.1 ≠ f := by
  intro l hl f hf
  obtain ⟨k, rfl⟩ := (mem_wkList f).mp hf
  rcases (mem_zeroLits l hl).2 with ⟨i, h⟩ | ⟨i, h⟩ | ⟨i, h⟩ | ⟨i, h⟩ <;> rw [h] <;> simp

theorem clean_eq_cfg0 (x : Cfg (Wire a m r K)) (hx : Clean x) :
    x = cfg0 ↔ ctrlOK zeroLits x = true ∧ x Wire.sec = false := by
  constructor
  · rintro rfl
    refine ⟨?_, rfl⟩
    rw [ctrlOK_iff]
    intro c hc
    rw [(mem_zeroLits c hc).1]
  · rintro ⟨hz, hs⟩
    rw [ctrlOK_iff] at hz
    funext w
    cases w with
    | anc i => exact hz (Wire.anc i, false) (by simp [zeroLits])
    | sec => exact hs
    | slot i => exact hz (Wire.slot i, false) (by simp [zeroLits])
    | ptr i => exact hz (Wire.ptr i, false) (by simp [zeroLits])
    | lab i => exact hz (Wire.lab i, false) (by simp [zeroLits])
    | _ => exact hx _ rfl

/-- Phase `-1` on `|0⟩`, `+1` on `|1⟩`. -/
def zMat : Matrix Bool Bool ℂ := fun b c => if b = c then (if b then 1 else -1) else 0

theorem zMat_unitary : UnitaryMat zMat := by
  constructor <;>
  · funext i j
    cases i <;> cases j <;>
      simp [zMat, Matrix.mul_apply, Matrix.conjTranspose_apply]

theorem negOne_unitary : UnitaryMat (-1 : Matrix Bool Bool ℂ) := by
  constructor <;> simp

/-- Gate list of the clean reflection. -/
def zrG : List (Gate (Wire a m r K)) :=
  mcGate zeroLits wkList Wire.sec zMat ++ [⟨[], Wire.sec, -1⟩]

theorem phase_bas (y : Cfg (Wire a m r K)) (q : P) :
    gateOp [] Wire.sec (-1 : Matrix Bool Bool ℂ) (bas y q) = -bas y q := by
  rw [gateOp_bas [] _ _ (by simp), ctrlOK_nil, if_pos rfl, Fintype.sum_bool]
  cases h : y Wire.sec
  · simp [← h]
  · simp [← h]

theorem zr_agrees (hK : a + m + 2 * r ≤ K + 1) :
    Agrees Clean (gRun (Q := P) (zrG (a := a) (m := m) (r := r) (K := K))) ZR := by
  apply agrees_of_bas
  intro x hx q
  have hmc := mcGate_agrees (Q := P) (zeroLits (a := a) (m := m) (r := r) (K := K)) wkList Wire.sec zMat
    (by rw [zeroLits_length, wkList_length]; exact hK) wkList_nodup zeroLits_ne_sec
    (fun f hf => by obtain ⟨i, rfl⟩ := (mem_wkList f).mp hf; simp) zeroLits_ne_wk WkClean
    (fun y hy => hy)
    (fun y b hy f hf => by
      obtain ⟨i, rfl⟩ := (mem_wkList f).mp hf
      rw [Function.update_of_ne (by simp)]
      exact hy _ hf)
  rw [zrG, gRun_append, comp_apply, hmc _ (supp_bas (S := WkClean) x (wkClean_of_clean x hx) q),
    gRun_singleton, Gate.op]
  simp only
  rw [gateOp_bas _ _ _ zeroLits_ne_sec, ZR_apply]
  have hiff := clean_eq_cfg0 x hx
  have hdiag : ∑ b : Bool, zMat b (x Wire.sec) • bas (Function.update x Wire.sec b) q =
      zMat (x Wire.sec) (x Wire.sec) • bas x q := by
    rw [Finset.sum_eq_single (x Wire.sec)]
    · rw [Function.update_eq_self]
    · intro b _ hb; simp [zMat, hb]
    · intro h; exact absurd (Finset.mem_univ _) h
  by_cases h0 : x = cfg0
  · have hc := (hiff.mp h0)
    rw [if_pos hc.1, hdiag, hc.2, map_smul, phase_bas]
    simp only [zMat, if_true, Bool.false_eq_true, if_false]
    rw [h0]
    simp only [bas_apply, if_true]
    rw [two_smul]
    simp
  · have hb0 : bas x q cfg0 = 0 := by rw [bas_apply, if_neg (Ne.symm h0)]
    have hz : bas (cfg0 : Cfg (Wire a m r K)) (0 : P) = 0 := by
      apply PiLp.ext; intro y; simp
    rw [hb0, hz, smul_zero, zero_sub]
    by_cases hc : ctrlOK zeroLits x = true
    · have hs : x Wire.sec = true := by
        by_contra hs
        exact h0 (hiff.mpr ⟨hc, by simpa using hs⟩)
      rw [if_pos hc, hdiag, hs, map_smul, phase_bas]
      simp [zMat]
    · rw [if_neg hc, phase_bas]

theorem zrG_ok : ∀ g ∈ (zrG (a := a) (m := m) (r := r) (K := K)), GateOK 2 g := by
  intro g hg
  rw [zrG, List.mem_append] at hg
  rcases hg with hg | hg
  · exact mcGate_valid _ _ _ _ zMat_unitary wkList_nodup zeroLits_ne_sec
      (fun f hf => by obtain ⟨i, rfl⟩ := (mem_wkList f).mp hf; simp) zeroLits_ne_wk g hg
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    subst hg
    exact ⟨by simp, by simp, negOne_unitary⟩

theorem zrG_length : (zrG (a := a) (m := m) (r := r) (K := K)).length ≤ 2 * (a + m + 2 * r) + 2 := by
  rw [zrG, List.length_append]
  have := mcGate_length_le (zeroLits (a := a) (m := m) (r := r) (K := K)) wkList Wire.sec zMat
  rw [zeroLits_length] at this
  simp only [List.length_cons, List.length_nil]
  omega

end

end SparseHamiltonian.GateCircuit.Sim
