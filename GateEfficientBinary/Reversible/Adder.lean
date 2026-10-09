import GateEfficientBinary.Reversible.Basic

/-!
# An out-of-place ripple-carry adder

The adder `adderG a b c s w` writes the sum of the registers `a` and `b` and the carry-in on
the wire `c 0` into the clean register `s`, using the clean carry wires `c 1, …, c (w - 1)`:
a forward pass computes the carries by majority gates (three Toffoli gates each), three
CNOT gates per bit write the sum bits, and the reversed forward pass erases the carries
(`crun_adderG`). The sum is `BitVec` addition with carry-in, by the bit-level description
of addition in Lean's `BitVec` library (`BitVec.getLsbD_add_add_bool`, `BitVec.carry_succ`).
-/

set_option autoImplicit false

namespace SparseHamiltonian.GateBinary

section Parity

variable {W : Type*} [DecidableEq W]

/-- The exclusive or of a list of bits. -/
def xorAll (l : List Bool) : Bool := l.foldr (· ^^ ·) false

/-- A proper gate XORs its control condition into its target. -/
theorem CGate.run_eq (g : CGate W) (x : W → Bool) :
    g.run x = Function.update x g.t (x g.t ^^ lits g.cs x) := by
  unfold CGate.run
  split_ifs with h
  · rw [h, Bool.xor_true]
  · rw [Bool.not_eq_true] at h
    rw [h, Bool.xor_false, Function.update_eq_self]

/-- Gates with a common target `t`, whose controls avoid `t`, XOR the parity of their control
conditions into `t`. -/
theorem crun_same_target (gs : List (CGate W)) (t : W)
    (ht : ∀ g ∈ gs, g.t = t ∧ ∀ c ∈ g.cs, c.1 ≠ t) (x : W → Bool) :
    crun gs x = Function.update x t (x t ^^ xorAll (gs.map (fun g => lits g.cs x))) := by
  induction gs generalizing x with
  | nil =>
      simp only [crun_nil, List.map_nil, xorAll, List.foldr_nil, Bool.xor_false,
        Function.update_eq_self]
  | cons g gs ih =>
      obtain ⟨hgt, hgc⟩ := ht g List.mem_cons_self
      rw [crun_cons, CGate.run_eq, hgt, ih (fun g' hg' => ht g' (List.mem_cons_of_mem g hg'))]
      have hl : ∀ g' ∈ gs, lits g'.cs (Function.update x t (x t ^^ lits g.cs x)) =
          lits g'.cs x := by
        intro g' hg'
        exact lits_congr _ _ _ (fun c hc =>
          Function.update_of_ne ((ht g' (List.mem_cons_of_mem g hg')).2 c hc) _ _)
      rw [List.map_congr_left hl]
      simp only [Function.update_self, Function.update_idem, List.map_cons, xorAll,
        List.foldr_cons, Bool.xor_assoc]

end Parity

section Adder

variable {W : Type*} [DecidableEq W]

/-- The majority of three wires XOR-ed into a fourth one: three Toffoli gates. -/
def majG (a b c t : W) : List (CGate W) :=
  [⟨[(a, true), (b, true)], t⟩, ⟨[(a, true), (c, true)], t⟩, ⟨[(b, true), (c, true)], t⟩]

theorem crun_majG (a b c t : W) (ha : a ≠ t) (hb : b ≠ t) (hc : c ≠ t) (x : W → Bool) :
    crun (majG a b c t) x = Function.update x t (x t ^^ Bool.atLeastTwo (x a) (x b) (x c)) := by
  rw [crun_same_target _ t]
  · congr 2
    simp only [majG, List.map_cons, List.map_nil, lits, List.all_cons, List.all_nil,
      Bool.and_true, beq_true, xorAll, List.foldr_cons, List.foldr_nil, Bool.xor_false]
    cases x a <;> cases x b <;> cases x c <;> rfl
  · intro g hg
    simp only [majG, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl <;>
      exact ⟨rfl, by simp [ha, hb, hc]⟩

/-- The forward carry pass over the bits `0, …, m - 1`. -/
def fwdG (a b c : ℕ → W) (m : ℕ) : List (CGate W) :=
  (List.range m).flatMap (fun i => majG (a i) (b i) (c i) (c (i + 1)))

/-- The sum pass: three CNOT gates per bit. -/
def sumG (a b c s : ℕ → W) (w : ℕ) : List (CGate W) :=
  (List.range w).flatMap (fun i =>
    [⟨[(a i, true)], s i⟩, ⟨[(b i, true)], s i⟩, ⟨[(c i, true)], s i⟩])

/-- The out-of-place adder `s := a + b + c 0` with carry wires `c 1, …, c (w - 1)`. -/
def adderG (a b c s : ℕ → W) (w : ℕ) : List (CGate W) :=
  fwdG a b c (w - 1) ++ sumG a b c s w ++ (fwdG a b c (w - 1)).reverse

omit [DecidableEq W] in
theorem fwdG_succ (a b c : ℕ → W) (m : ℕ) :
    fwdG a b c (m + 1) = fwdG a b c m ++ majG (a m) (b m) (c m) (c (m + 1)) := by
  simp [fwdG, List.range_succ, List.flatMap_append]

omit [DecidableEq W] in
theorem sumG_succ (a b c s : ℕ → W) (m : ℕ) :
    sumG a b c s (m + 1) = sumG a b c s m ++
      [⟨[(a m, true)], s m⟩, ⟨[(b m, true)], s m⟩, ⟨[(c m, true)], s m⟩] := by
  simp [sumG, List.range_succ, List.flatMap_append]

omit [DecidableEq W] in
theorem length_majG (a b c t : W) : (majG a b c t).length = 3 := rfl

omit [DecidableEq W] in
theorem length_fwdG (a b c : ℕ → W) (m : ℕ) : (fwdG a b c m).length = 3 * m := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [fwdG_succ, List.length_append, ih, length_majG]
      omega

omit [DecidableEq W] in
theorem length_sumG (a b c s : ℕ → W) (w : ℕ) : (sumG a b c s w).length = 3 * w := by
  induction w with
  | zero => rfl
  | succ m ih =>
      rw [sumG_succ, List.length_append, ih]
      simp only [List.length_cons, List.length_nil]
      omega

omit [DecidableEq W] in
theorem length_adderG (a b c s : ℕ → W) (w : ℕ) :
    (adderG a b c s w).length = 3 * (w - 1) + 3 * w + 3 * (w - 1) := by
  simp only [adderG, List.length_append, List.length_reverse, length_fwdG, length_sumG]

/-- The wires written by the adder: the carries above the carry-in and the sum bits. -/
def ATgt (c s : ℕ → W) (w : ℕ) (u : W) : Prop :=
  (∃ i, 1 ≤ i ∧ i < w ∧ c i = u) ∨ (∃ i, i < w ∧ s i = u)

/-- The wiring conditions of the adder: the operands and the carry-in are read only, and the
carry and sum wires are distinct. -/
structure AdderOK (a b c s : ℕ → W) (w : ℕ) : Prop where
  a_off : ∀ i < w, ¬ ATgt c s w (a i)
  b_off : ∀ i < w, ¬ ATgt c s w (b i)
  c0_off : ¬ ATgt c s w (c 0)
  c_inj : ∀ i j, 1 ≤ i → i < w → 1 ≤ j → j < w → c i = c j → i = j
  s_inj : ∀ i j, i < w → j < w → s i = s j → i = j
  cs_ne : ∀ i j, 1 ≤ i → i < w → j < w → c i ≠ s j

variable {a b c s : ℕ → W} {w : ℕ}

omit [DecidableEq W] in
theorem AdderOK.c_ne (h : AdderOK a b c s w) {i j : ℕ} (hi : i < w) (hj1 : 1 ≤ j) (hj : j < w)
    (hij : i ≠ j) : c i ≠ c j := by
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · intro he
    exact h.c0_off (Or.inl ⟨j, hj1, hj, he.symm⟩)
  · exact fun he => hij (h.c_inj i j hi0 hi hj1 hj he)

/-- The forward pass computes the carries of `a + b + c 0`. -/
theorem crun_fwdG (h : AdderOK a b c s w) (x : W → Bool)
    (hx : ∀ u, ATgt c s w u → x u = false) (m : ℕ) (hm : m + 1 ≤ w) :
    (∀ j ≤ m, crun (fwdG a b c m) x (c j) =
      BitVec.carry j (readBV a w x) (readBV b w x) (x (c 0))) ∧
    (∀ u, (∀ j, 1 ≤ j → j ≤ m → c j ≠ u) → crun (fwdG a b c m) x u = x u) := by
  induction m with
  | zero =>
      refine ⟨fun j hj => ?_, fun u _ => rfl⟩
      rw [Nat.le_zero.1 hj, BitVec.carry_zero]
      rfl
  | succ m ih =>
      obtain ⟨ih1, ih2⟩ := ih (by omega)
      have hcm : c m ≠ c (m + 1) := h.c_ne (by omega) (by omega) hm (by omega)
      have ham : a m ≠ c (m + 1) := fun he => h.a_off m (by omega)
        (Or.inl ⟨m + 1, by omega, hm, he.symm⟩)
      have hbm : b m ≠ c (m + 1) := fun he => h.b_off m (by omega)
        (Or.inl ⟨m + 1, by omega, hm, he.symm⟩)
      have hnew : ∀ j, 1 ≤ j → j ≤ m → c j ≠ c (m + 1) := fun j hj1 hj =>
        h.c_ne (by omega) (by omega) hm (by omega)
      have hya : crun (fwdG a b c m) x (a m) = x (a m) := ih2 _ (fun j hj1 hj he =>
        h.a_off m (by omega) (Or.inl ⟨j, hj1, by omega, he⟩))
      have hyb : crun (fwdG a b c m) x (b m) = x (b m) := ih2 _ (fun j hj1 hj he =>
        h.b_off m (by omega) (Or.inl ⟨j, hj1, by omega, he⟩))
      have hyc : crun (fwdG a b c m) x (c (m + 1)) = false := by
        rw [ih2 _ hnew]
        exact hx _ (Or.inl ⟨m + 1, by omega, hm, rfl⟩)
      rw [fwdG_succ, crun_append, crun_majG _ _ _ _ ham hbm hcm]
      refine ⟨fun j hj => ?_, fun u hu => ?_⟩
      · rcases Nat.lt_or_ge j (m + 1) with hjm | hjm
        · rw [Function.update_of_ne (h.c_ne (by omega) (by omega) hm (by omega)),
            ih1 j (by omega)]
        · obtain rfl : j = m + 1 := by omega
          rw [Function.update_self, hyc, Bool.false_xor, hya, hyb, ih1 m le_rfl,
            BitVec.carry_succ, getLsbD_readBV, getLsbD_readBV]
          simp [show m < w by omega]
      · rw [Function.update_of_ne (fun he => hu (m + 1) (by omega) le_rfl he.symm)]
        exact ih2 u (fun j hj1 hj => hu j hj1 (by omega))

/-- The sum pass XORs the three operand bits into each sum wire. -/
theorem crun_sumG (h : AdderOK a b c s w) (y : W → Bool) (m : ℕ) (hm : m ≤ w) :
    (∀ i < m, crun (sumG a b c s m) y (s i) = (y (s i) ^^ (y (a i) ^^ (y (b i) ^^ y (c i))))) ∧
    (∀ u, (∀ i < m, s i ≠ u) → crun (sumG a b c s m) y u = y u) := by
  induction m with
  | zero => exact ⟨fun i hi => absurd hi (Nat.not_lt_zero i), fun u _ => rfl⟩
  | succ m ih =>
      obtain ⟨ih1, ih2⟩ := ih (by omega)
      have hsa : ∀ i < w, a i ≠ s m := fun i hi he => h.a_off i hi (Or.inr ⟨m, by omega, he.symm⟩)
      have hsb : ∀ i < w, b i ≠ s m := fun i hi he => h.b_off i hi (Or.inr ⟨m, by omega, he.symm⟩)
      have hsc : ∀ i < w, c i ≠ s m := by
        intro i hi he
        rcases Nat.eq_zero_or_pos i with rfl | hi0
        · exact h.c0_off (Or.inr ⟨m, by omega, he.symm⟩)
        · exact h.cs_ne i m hi0 hi (by omega) he
      have hold : ∀ v, (v = a m ∨ v = b m ∨ v = c m) → crun (sumG a b c s m) y v = y v := by
        intro v hv
        apply ih2
        intro i hi he
        rcases hv with rfl | rfl | rfl
        · exact h.a_off m (by omega) (Or.inr ⟨i, by omega, he⟩)
        · exact h.b_off m (by omega) (Or.inr ⟨i, by omega, he⟩)
        · rcases Nat.eq_zero_or_pos m with hm0 | hm0
          · subst hm0
            exact h.c0_off (Or.inr ⟨i, by omega, he⟩)
          · exact h.cs_ne m i hm0 (by omega) (by omega) he.symm
      rw [sumG_succ, crun_append, crun_same_target _ (s m)]
      · simp only [List.map_cons, List.map_nil, lits, List.all_cons, List.all_nil, Bool.and_true,
          beq_true, xorAll, List.foldr_cons, List.foldr_nil, Bool.xor_false]
        rw [hold _ (Or.inl rfl), hold _ (Or.inr (Or.inl rfl)), hold _ (Or.inr (Or.inr rfl))]
        refine ⟨fun i hi => ?_, fun u hu => ?_⟩
        · rcases Nat.lt_or_ge i m with him | him
          · have hne : s i ≠ s m := fun he => by
              have := h.s_inj i m (by omega) (by omega) he
              omega
            rw [Function.update_of_ne hne, ih1 i him]
          · obtain rfl : i = m := by omega
            rw [Function.update_self, ih2 _ (fun j hj he => by
              have := h.s_inj j i (by omega) (by omega) he
              omega)]
        · rw [Function.update_of_ne (fun he => hu m (by omega) he.symm)]
          exact ih2 u (fun i hi => hu i (by omega))
      · intro g hg
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with rfl | rfl | rfl
        · exact ⟨rfl, by simpa using hsa m (by omega)⟩
        · exact ⟨rfl, by simpa using hsb m (by omega)⟩
        · exact ⟨rfl, by simpa using hsc m (by omega)⟩

omit [DecidableEq W] in
/-- The gates of the forward pass are proper. -/
theorem proper_fwdG (h : AdderOK a b c s w) (m : ℕ) (hm : m + 1 ≤ w) :
    ∀ g ∈ fwdG a b c m, g.Proper := by
  intro g hg
  simp only [fwdG, List.mem_flatMap, List.mem_range] at hg
  obtain ⟨i, hi, hg⟩ := hg
  have ha : a i ≠ c (i + 1) := fun he => h.a_off i (by omega)
    (Or.inl ⟨i + 1, by omega, by omega, he.symm⟩)
  have hb : b i ≠ c (i + 1) := fun he => h.b_off i (by omega)
    (Or.inl ⟨i + 1, by omega, by omega, he.symm⟩)
  have hc : c i ≠ c (i + 1) := h.c_ne (by omega) (by omega) (by omega) (by omega)
  simp only [majG, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl <;>
    · intro c' hc'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
      rcases hc' with rfl | rfl <;> assumption

omit [DecidableEq W] in
/-- The forward pass does not mention the sum wires. -/
theorem within_fwdG (h : AdderOK a b c s w) (m : ℕ) (hm : m + 1 ≤ w) :
    ∀ g ∈ fwdG a b c m, g.Within (fun u => ¬ ∃ i, i < w ∧ s i = u) := by
  have ha : ∀ i < w, ¬ ∃ j, j < w ∧ s j = a i := fun i hi ⟨j, hj, he⟩ =>
    h.a_off i hi (Or.inr ⟨j, hj, he⟩)
  have hb : ∀ i < w, ¬ ∃ j, j < w ∧ s j = b i := fun i hi ⟨j, hj, he⟩ =>
    h.b_off i hi (Or.inr ⟨j, hj, he⟩)
  have hc : ∀ i < w, ¬ ∃ j, j < w ∧ s j = c i := by
    intro i hi ⟨j, hj, he⟩
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · exact h.c0_off (Or.inr ⟨j, hj, he⟩)
    · exact h.cs_ne i j hi0 hi hj he.symm
  intro g hg
  simp only [fwdG, List.mem_flatMap, List.mem_range] at hg
  obtain ⟨i, hi, hg⟩ := hg
  simp only [majG, List.mem_cons, List.not_mem_nil, or_false] at hg
  have hct := hc (i + 1) (by omega)
  have hai := ha i (by omega)
  have hbi := hb i (by omega)
  have hci := hc i (by omega)
  rcases hg with rfl | rfl | rfl
  · refine ⟨hct, fun c' hc' => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
    rcases hc' with rfl | rfl
    · exact hai
    · exact hbi
  · refine ⟨hct, fun c' hc' => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
    rcases hc' with rfl | rfl
    · exact hai
    · exact hci
  · refine ⟨hct, fun c' hc' => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
    rcases hc' with rfl | rfl
    · exact hbi
    · exact hci

/-- **The adder.** On a configuration with clean carry and sum wires, the adder writes the
bits of `a + b + c 0` into the sum wires and changes nothing else. -/
theorem crun_adderG (h : AdderOK a b c s w) (hw : 0 < w) (x : W → Bool)
    (hx : ∀ u, ATgt c s w u → x u = false) :
    (∀ i < w, crun (adderG a b c s w) x (s i) =
      (readBV a w x + readBV b w x + (BitVec.ofBool (x (c 0))).setWidth w).getLsbD i) ∧
    (∀ u, (∀ i < w, s i ≠ u) → crun (adderG a b c s w) x u = x u) := by
  obtain ⟨hf1, hf2⟩ := crun_fwdG h x hx (w - 1) (by omega)
  set y1 := crun (fwdG a b c (w - 1)) x with hy1
  obtain ⟨hs1, hs2⟩ := crun_sumG h y1 w le_rfl
  set y2 := crun (sumG a b c s w) y1 with hy2
  have hsplit : y2 = fun u => if (¬ ∃ i, i < w ∧ s i = u) then y1 u else y2 u := by
    funext u
    by_cases hu : ∃ i, i < w ∧ s i = u
    · rw [if_neg (not_not.2 hu)]
    · rw [if_pos hu]
      exact hs2 u (fun i hi he => hu ⟨i, hi, he⟩)
  have hwithin := within_fwdG h (w - 1) (by omega)
  have hwithin' : ∀ g ∈ (fwdG a b c (w - 1)).reverse,
      g.Within (fun u => ¬ ∃ i, i < w ∧ s i = u) := fun g hg =>
    hwithin g (List.mem_reverse.1 hg)
  have hback : crun (fwdG a b c (w - 1)).reverse y2 =
      fun u => if (¬ ∃ i, i < w ∧ s i = u) then x u else y2 u := by
    have e := crun_override _ _ hwithin' y1 y2
    rw [← hsplit, hy1, crun_reverse _ (proper_fwdG h (w - 1) (by omega))] at e
    exact e
  have hrun : crun (adderG a b c s w) x = crun (fwdG a b c (w - 1)).reverse y2 := by
    rw [adderG, crun_append, crun_append]
  refine ⟨fun i hi => ?_, fun u hu => ?_⟩
  · rw [hrun, hback]
    dsimp only
    rw [if_neg (fun hn => hn ⟨i, hi, rfl⟩), hs1 i hi]
    have hsx : y1 (s i) = false := by
      rw [hf2 _ (fun j hj1 hj he => h.cs_ne j i hj1 (by omega) hi he)]
      exact hx _ (Or.inr ⟨i, hi, rfl⟩)
    have hya : y1 (a i) = x (a i) := hf2 _ (fun j hj1 hj he =>
      h.a_off i hi (Or.inl ⟨j, hj1, by omega, he⟩))
    have hyb : y1 (b i) = x (b i) := hf2 _ (fun j hj1 hj he =>
      h.b_off i hi (Or.inl ⟨j, hj1, by omega, he⟩))
    rw [hsx, hya, hyb, hf1 i (by omega), Bool.false_xor, BitVec.getLsbD_add_add_bool hi,
      getLsbD_readBV, getLsbD_readBV]
    simp [hi]
  · rw [hrun, hback]
    dsimp only
    rw [if_pos (fun ⟨i, hi, he⟩ => hu i hi he)]

omit [DecidableEq W] in
/-- The gates of the adder are proper. -/
theorem proper_adderG (h : AdderOK a b c s w) (hw : 0 < w) : ∀ g ∈ adderG a b c s w, g.Proper := by
  have hf := proper_fwdG h (w - 1) (by omega)
  have hsum : ∀ g ∈ sumG a b c s w, g.Proper := by
    intro g hg
    simp only [sumG, List.mem_flatMap, List.mem_range] at hg
    obtain ⟨i, hi, hg⟩ := hg
    have hci : c i ≠ s i := by
      intro he
      rcases Nat.eq_zero_or_pos i with hi0 | hi0
      · subst hi0
        exact h.c0_off (Or.inr ⟨0, hi, he.symm⟩)
      · exact h.cs_ne i i hi0 hi hi he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl
    · intro c' hc'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
      subst hc'
      exact fun he => h.a_off i hi (Or.inr ⟨i, hi, he.symm⟩)
    · intro c' hc'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
      subst hc'
      exact fun he => h.b_off i hi (Or.inr ⟨i, hi, he.symm⟩)
    · intro c' hc'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
      subst hc'
      exact hci
  intro g hg
  simp only [adderG, List.mem_append, List.mem_reverse] at hg
  rcases hg with (hg | hg) | hg
  · exact hf g hg
  · exact hsum g hg
  · exact hf g hg

omit [DecidableEq W] in
/-- The gates of the adder have at most two controls. -/
theorem cs_adderG (a b c s : ℕ → W) (w : ℕ) : ∀ g ∈ adderG a b c s w, g.cs.length ≤ 2 := by
  intro g hg
  simp only [adderG, fwdG, sumG, List.mem_append, List.mem_reverse, List.mem_flatMap,
    List.mem_range] at hg
  rcases hg with (⟨i, _, hg⟩ | ⟨i, _, hg⟩) | ⟨i, _, hg⟩ <;>
    · simp only [majG, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl <;> simp

end Adder

end SparseHamiltonian.GateBinary
