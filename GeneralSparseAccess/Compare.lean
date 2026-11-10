import GateEfficientHamiltonian.GateConstantCompareNumeric
import GeneralSparseAccess.MatOp

/-!
# Comparing an index word with a public constant

The validity tests of the padded oracles compare an index word with the public bounds `N` and `s`
(`i < N`, `a < s`; the manuscript's "These tests use `O(log(N+1))` gates", Section `hs:sec:gates`,
paragraph *Entry arithmetic and the precise resource bound*). The comparison of an `r`-bit
little-endian word `x` with a constant `c ≤ 2^r` is the borrow of the subtraction `x - c` over
`r + 1` bits (the top bit of `x` zero), computed by a ripple of controlled NOT gates on clean borrow
wires (`ltChain`; the borrow recursion and its numerical meaning are those of `GateConstantCompare`,
`borrowValue_iff_prefix_lt`):

* `cfgRun_ltChain_top`: on clean borrow wires the last borrow wire ends with `[x < c]`;
* `cfgRun_ltChain_out`: only the borrow wires change, and `cfgRun_reverse_cancel` undoes the chain;
* `classical_ltChain`, `gateOK_ltChain`, `length_ltChain_le`: controlled NOT gates with at most two
  controls, at most `2 (r + 1)` of them.
-/

set_option autoImplicit false

namespace SparseHamiltonian.GeneralSparseAccess

noncomputable section
open SparseHamiltonian.GateCircuit
open SparseHamiltonian.GateConstantCompare (borrowValue nextBorrow thresholdBit prefixValue
  borrowValue_iff_prefix_lt prefixValue_succ prefixValue_pointer wordValue_thresholdWord)
open SparseHamiltonian.GatePointerEncoding (wordValue bitValue)

section Compare

variable {W : Type*} [DecidableEq W]

/-- One borrow step: the bit wire `x`, the incoming borrow `i` and the clean output `o` receive
`nextBorrow c (x) (i) j`. -/
def bStep (c j : ℕ) (x i o : W) : List (Gate W) :=
  if thresholdBit c j then [⟨[], o, pauliX⟩, ⟨[(x, true), (i, false)], o, pauliX⟩]
  else [⟨[(x, false), (i, true)], o, pauliX⟩]

/-- The top borrow step, for the zero top bit of the word. -/
def bTop (c j : ℕ) (i o : W) : List (Gate W) :=
  if thresholdBit c j then [⟨[], o, pauliX⟩] else [⟨[(i, true)], o, pauliX⟩]

variable {r : ℕ}

/-- The step `m` of the borrow chain of the word on `xw` with the borrow wires `bw`. -/
def stepAt (c : ℕ) (xw : Fin r → W) (bw : Fin (r + 2) → W) (m : ℕ) : List (Gate W) :=
  if h : m < r then bStep c m (xw ⟨m, h⟩) (bw ⟨m, by omega⟩) (bw ⟨m + 1, by omega⟩)
  else if h' : m = r then bTop c m (bw ⟨m, by omega⟩) (bw ⟨m + 1, by omega⟩) else []

/-- The first `m` steps of the borrow chain. -/
def chainUpTo (c : ℕ) (xw : Fin r → W) (bw : Fin (r + 2) → W) : ℕ → List (Gate W)
  | 0 => []
  | m + 1 => chainUpTo c xw bw m ++ stepAt c xw bw m

/-- **The borrow chain** of the comparison of the word on `xw` with the constant `c`: the borrow
wire `bw 0` stays clean (the incoming borrow of bit `0`), and `bw (j + 1)` receives the borrow after
bit `j`; the last wire `bw (r + 1)` receives `[x < c]`. -/
def ltChain (c : ℕ) (xw : Fin r → W) (bw : Fin (r + 2) → W) : List (Gate W) :=
  chainUpTo c xw bw (r + 1)

/-! ### The borrow steps -/

theorem cfgRun_bStep (c j : ℕ) (x i o : W) (hxo : x ≠ o) (hio : i ≠ o) (z : Cfg W) :
    cfgRun (bStep c j x i o) z =
      Function.update z o (z o ^^ nextBorrow c (z x) (z i) j) := by
  unfold bStep nextBorrow
  by_cases ht : thresholdBit c j
  · simp only [ht, if_true, cfgRun]
    funext w
    unfold flipCfg
    simp only [ctrlOK_nil, if_true, ctrlOK_cons, ctrlOK_nil]
    rw [Function.update_of_ne hxo, Function.update_of_ne hio]
    by_cases hw : w = o
    · subst hw
      cases hx : z x <;> cases hi : z i <;> cases hz : z w <;> simp
    · split_ifs <;> simp [Function.update_of_ne hw]
  · simp only [ht, Bool.false_eq_true, if_false, cfgRun]
    funext w
    unfold flipCfg
    simp only [ctrlOK_cons, ctrlOK_nil]
    by_cases hw : w = o
    · subst hw
      rcases Bool.eq_false_or_eq_true (z x) with hx | hx <;>
        rcases Bool.eq_false_or_eq_true (z i) with hi | hi <;> simp [hx, hi]
    · split_ifs <;> simp [Function.update_of_ne hw]

theorem cfgRun_bTop (c j : ℕ) (i o : W) (hio : i ≠ o) (z : Cfg W) :
    cfgRun (bTop c j i o) z = Function.update z o (z o ^^ nextBorrow c false (z i) j) := by
  unfold bTop nextBorrow
  by_cases ht : thresholdBit c j
  · simp only [ht, if_true, cfgRun]
    funext w
    unfold flipCfg
    simp only [ctrlOK_nil, if_true]
    by_cases hw : w = o
    · subst hw
      cases hz : z w <;> simp
    · simp [Function.update_of_ne hw]
  · simp only [ht, Bool.false_eq_true, if_false, cfgRun]
    funext w
    unfold flipCfg
    simp only [ctrlOK_cons, ctrlOK_nil]
    by_cases hw : w = o
    · subst hw
      rcases Bool.eq_false_or_eq_true (z i) with hi | hi <;> simp [hi]
    · split_ifs <;> simp [Function.update_of_ne hw]

/-! ### The layout and the chain -/

/-- The wires of a comparison: the word and the borrow wires are injective and disjoint. -/
structure CmpLayout (xw : Fin r → W) (bw : Fin (r + 2) → W) : Prop where
  inj_x : Function.Injective xw
  inj_b : Function.Injective bw
  x_ne_b : ∀ i j, xw i ≠ bw j

theorem cfgRun_stepAt (c : ℕ) {xw : Fin r → W} {bw : Fin (r + 2) → W} (L : CmpLayout xw bw)
    (m : ℕ) (hm : m ≤ r) (z : Cfg W) :
    cfgRun (stepAt c xw bw m) z = Function.update z (bw ⟨m + 1, by omega⟩)
      (z (bw ⟨m + 1, by omega⟩) ^^
        nextBorrow c (GatePrivatePointer.bit (fun i => z (xw i)) m) (z (bw ⟨m, by omega⟩)) m) := by
  have hne : bw ⟨m, by omega⟩ ≠ bw ⟨m + 1, by omega⟩ := fun h => by
    have := congrArg Fin.val (L.inj_b h); simp at this
  unfold stepAt
  by_cases h : m < r
  · rw [dif_pos h, cfgRun_bStep c m _ _ _ (L.x_ne_b _ _) hne]
    simp [GatePrivatePointer.bit, h]
  · have hmr : m = r := by omega
    rw [dif_neg h, dif_pos hmr, cfgRun_bTop c m _ _ hne]
    simp [GatePrivatePointer.bit, h]

omit [DecidableEq W] in
/-- The chain never writes the word wires. -/
theorem target_ne_xw (c : ℕ) {xw : Fin r → W} {bw : Fin (r + 2) → W} (L : CmpLayout xw bw)
    (m : ℕ) (i : Fin r) (g : Gate W) (hg : g ∈ chainUpTo c xw bw m) : g.t ≠ xw i := by
  induction m with
  | zero => simp [chainUpTo] at hg
  | succ m ih =>
      rw [chainUpTo, List.mem_append] at hg
      rcases hg with hg | hg
      · exact ih hg
      · unfold stepAt at hg
        split_ifs at hg
        · unfold bStep at hg
          split_ifs at hg <;> simp at hg <;> rcases hg with rfl | rfl <;>
            exact fun h => L.x_ne_b _ _ h.symm
        · unfold bTop at hg
          split_ifs at hg <;> simp at hg <;> subst hg <;>
            exact fun h => L.x_ne_b _ _ h.symm
        · simp at hg


/-- The values of the chain: after `m` steps the borrow wires `bw j`, `j ≤ m`, hold the borrows
`borrowValue c x j`, and the later ones are still clean. -/
theorem cfgRun_chainUpTo (c : ℕ) {xw : Fin r → W} {bw : Fin (r + 2) → W} (L : CmpLayout xw bw)
    (z : Cfg W) (hz : ∀ j, z (bw j) = false) (m : ℕ) (hm : m ≤ r + 1) (j : Fin (r + 2)) :
    cfgRun (chainUpTo c xw bw m) z (bw j) =
      if j.val ≤ m then borrowValue c (fun i => z (xw i)) j.val else false := by
  induction m generalizing j with
  | zero =>
      simp only [chainUpTo, cfgRun, hz j]
      by_cases hj : j.val ≤ 0
      · have : j.val = 0 := by omega
        rw [if_pos hj, this]
        rfl
      · rw [if_neg hj]
  | succ m ih =>
      have hm' : m ≤ r := by omega
      rw [chainUpTo, cfgRun_append, cfgRun_stepAt c L m hm']
      have hx : (fun i => cfgRun (chainUpTo c xw bw m) z (xw i)) = fun i => z (xw i) := by
        funext i
        apply cfgRun_apply_of_not_target
        intro g hg
        exact target_ne_xw c L m i g hg
      rw [hx]
      by_cases hj : j = ⟨m + 1, by omega⟩
      · subst hj
        rw [Function.update_self, ih (by omega), ih (by omega)]
        simp only [show ¬ (m + 1 ≤ m) by omega, if_false, le_refl, if_true, Bool.false_xor]
        rfl
      · rw [Function.update_of_ne (fun h => hj (L.inj_b h)), ih (by omega)]
        have : j.val ≠ m + 1 := fun h => hj (Fin.ext h)
        by_cases hjm : j.val ≤ m
        · rw [if_pos hjm, if_pos (by omega)]
        · rw [if_neg hjm, if_neg (by omega)]
omit [DecidableEq W] in
/-- The targets of the chain are borrow wires `bw (j + 1)`. -/
theorem target_chainUpTo (c : ℕ) (xw : Fin r → W) (bw : Fin (r + 2) → W) (m : ℕ) (g : Gate W)
    (hg : g ∈ chainUpTo c xw bw m) : ∃ j : Fin (r + 2), j.val ≠ 0 ∧ g.t = bw j := by
  induction m with
  | zero => simp [chainUpTo] at hg
  | succ m ih =>
      rw [chainUpTo, List.mem_append] at hg
      rcases hg with hg | hg
      · exact ih hg
      · unfold stepAt at hg
        split_ifs at hg with h1 h2
        · unfold bStep at hg
          split_ifs at hg <;> simp at hg <;> rcases hg with rfl | rfl <;>
            exact ⟨⟨m + 1, by omega⟩, by simp, rfl⟩
        · unfold bTop at hg
          split_ifs at hg <;> simp at hg <;> subst hg <;>
            exact ⟨⟨m + 1, by omega⟩, by simp, rfl⟩
        · simp at hg

omit [DecidableEq W] in
/-- The controls of the chain are word wires and borrow wires. -/
theorem ctrl_chainUpTo (c : ℕ) (xw : Fin r → W) (bw : Fin (r + 2) → W) (m : ℕ) (g : Gate W)
    (hg : g ∈ chainUpTo c xw bw m) (cc : W × Bool) (hcc : cc ∈ g.cs) (w : W)
    (hx : ∀ i, xw i ≠ w) (hb : ∀ j, bw j ≠ w) : cc.1 ≠ w := by
  induction m with
  | zero => simp [chainUpTo] at hg
  | succ m ih =>
      rw [chainUpTo, List.mem_append] at hg
      rcases hg with hg | hg
      · exact ih hg
      · unfold stepAt at hg
        split_ifs at hg with h1 h2
        · unfold bStep at hg
          split_ifs at hg <;> simp at hg
          · rcases hg with rfl | rfl
            · simp at hcc
            · simp only [List.mem_cons, List.not_mem_nil, or_false] at hcc
              rcases hcc with rfl | rfl
              · exact hx _
              · exact hb _
          · subst hg
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hcc
            rcases hcc with rfl | rfl
            · exact hx _
            · exact hb _
        · unfold bTop at hg
          split_ifs at hg <;> simp at hg <;> subst hg
          · simp at hcc
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hcc
            subst hcc
            exact hb _
        · simp at hg

omit [DecidableEq W] in
/-- The gates of the chain: controlled NOT gates with at most two controls, off their targets. -/
theorem gate_chainUpTo (c : ℕ) {xw : Fin r → W} {bw : Fin (r + 2) → W} (L : CmpLayout xw bw)
    (m : ℕ) (g : Gate W) (hg : g ∈ chainUpTo c xw bw m) :
    g.u = pauliX ∧ g.cs.length ≤ 2 ∧ ∀ cc ∈ g.cs, cc.1 ≠ g.t := by
  induction m with
  | zero => simp [chainUpTo] at hg
  | succ m ih =>
      rw [chainUpTo, List.mem_append] at hg
      rcases hg with hg | hg
      · exact ih hg
      · have hne : ∀ (a b : Fin (r + 2)), a.val ≠ b.val → bw a ≠ bw b :=
          fun a b hab h => hab (congrArg Fin.val (L.inj_b h))
        unfold stepAt at hg
        split_ifs at hg with h1 h2
        · unfold bStep at hg
          split_ifs at hg <;> simp at hg
          · rcases hg with rfl | rfl
            · simp
            · refine ⟨rfl, by simp, ?_⟩
              simp only [List.mem_cons, List.not_mem_nil, or_false]
              rintro cc (rfl | rfl)
              · exact L.x_ne_b _ _
              · exact hne _ _ (by simp)
          · subst hg
            refine ⟨rfl, by simp, ?_⟩
            simp only [List.mem_cons, List.not_mem_nil, or_false]
            rintro cc (rfl | rfl)
            · exact L.x_ne_b _ _
            · exact hne _ _ (by simp)
        · unfold bTop at hg
          split_ifs at hg <;> simp at hg <;> subst hg
          · simp
          · refine ⟨rfl, by simp, ?_⟩
            simp only [List.mem_cons, List.not_mem_nil, or_false]
            rintro cc rfl
            exact hne _ _ (by simp)
        · simp at hg

omit [DecidableEq W] in
theorem length_stepAt_le (c : ℕ) (xw : Fin r → W) (bw : Fin (r + 2) → W) (m : ℕ) :
    (stepAt c xw bw m).length ≤ 2 := by
  unfold stepAt bStep bTop
  split_ifs <;> simp

omit [DecidableEq W] in
theorem length_chainUpTo_le (c : ℕ) (xw : Fin r → W) (bw : Fin (r + 2) → W) (m : ℕ) :
    (chainUpTo c xw bw m).length ≤ 2 * m := by
  induction m with
  | zero => simp [chainUpTo]
  | succ m ih =>
      rw [chainUpTo, List.length_append]
      have := length_stepAt_le c xw bw m
      omega

/-! ### The chain -/

/-- The top borrow of the chain is the comparison `[x < c]` for `c < 2^(r+1)`. -/
theorem borrowValue_top (c : ℕ) (x : Cfg (Fin r)) (hc : c < 2 ^ (r + 1)) :
    borrowValue c x (r + 1) = decide (wordValue x < c) := by
  have h := borrowValue_iff_prefix_lt c x (r + 1)
  have hx : prefixValue (GatePrivatePointer.bit x) (r + 1) = wordValue x := by
    rw [prefixValue_succ, prefixValue_pointer]
    simp [GatePrivatePointer.bit, bitValue]
  have hcv : prefixValue (thresholdBit c) (r + 1) = c := wordValue_thresholdWord c (r + 1) hc
  rw [hx, hcv] at h
  cases hb : borrowValue c x (r + 1) <;> simp_all

omit [DecidableEq W] in
theorem classical_ltChain (c : ℕ) {xw : Fin r → W} {bw : Fin (r + 2) → W}
    (L : CmpLayout xw bw) : Classical (ltChain c xw bw) := by
  intro g hg
  obtain ⟨hu, -, hcs⟩ := gate_chainUpTo c L (r + 1) g hg
  exact ⟨hu, hcs⟩

omit [DecidableEq W] in
theorem gateOK_ltChain (c : ℕ) {xw : Fin r → W} {bw : Fin (r + 2) → W}
    (L : CmpLayout xw bw) : ∀ g ∈ ltChain c xw bw, GateOK 3 g := by
  intro g hg
  obtain ⟨hu, hl, hcs⟩ := gate_chainUpTo c L (r + 1) g hg
  refine ⟨by omega, hcs, ?_⟩
  rw [hu]
  exact pauliX_unitary

omit [DecidableEq W] in
theorem length_ltChain_le (c : ℕ) (xw : Fin r → W) (bw : Fin (r + 2) → W) :
    (ltChain c xw bw).length ≤ 2 * (r + 1) :=
  length_chainUpTo_le c xw bw (r + 1)

/-- **The comparison**: on clean borrow wires the chain leaves `[x < c]` on `bw (r + 1)`. -/
theorem cfgRun_ltChain_top (c : ℕ) {xw : Fin r → W} {bw : Fin (r + 2) → W}
    (L : CmpLayout xw bw) (hc : c < 2 ^ (r + 1)) (z : Cfg W) (hz : ∀ j, z (bw j) = false) :
    cfgRun (ltChain c xw bw) z (bw ⟨r + 1, by omega⟩) =
      decide (wordValue (fun i => z (xw i)) < c) := by
  rw [ltChain, cfgRun_chainUpTo c L z hz (r + 1) le_rfl, if_pos le_rfl]
  exact borrowValue_top c _ hc

/-- The chain changes only its borrow wires. -/
theorem cfgRun_ltChain_out (c : ℕ) (xw : Fin r → W) (bw : Fin (r + 2) → W) (z : Cfg W) (w : W)
    (hw : ∀ j, bw j ≠ w) : cfgRun (ltChain c xw bw) z w = z w := by
  apply cfgRun_apply_of_not_target
  intro g hg
  obtain ⟨j, -, hj⟩ := target_chainUpTo c xw bw (r + 1) g hg
  rw [hj]
  exact hw j

/-- Running a classical gate list backwards undoes it. -/
theorem cfgRun_reverse_cancel (gs : List (Gate W)) (h : Classical gs) (z : Cfg W) :
    cfgRun gs.reverse (cfgRun gs z) = z := by
  induction gs generalizing z with
  | nil => rfl
  | cons g gs ih =>
      rw [List.reverse_cons, cfgRun_append]
      change cfgRun [g] (cfgRun gs.reverse (cfgRun gs (flipCfg g.cs g.t z))) = z
      rw [ih (fun g' hg' => h g' (List.mem_cons_of_mem g hg'))]
      exact flipCfg_flipCfg g.cs g.t (h g List.mem_cons_self).2 z

/-- Running a classical gate list after its reverse undoes it. -/
theorem cfgRun_cancel_reverse (gs : List (Gate W)) (h : Classical gs) (z : Cfg W) :
    cfgRun gs (cfgRun gs.reverse z) = z := by
  have h' : Classical gs.reverse := fun g hg => h g (List.mem_reverse.mp hg)
  have := cfgRun_reverse_cancel gs.reverse h' z
  rwa [List.reverse_reverse] at this

end Compare

end

end SparseHamiltonian.GeneralSparseAccess
