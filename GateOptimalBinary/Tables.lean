import GateOptimalBinary.Main

set_option autoImplicit false

/-!
# The arithmetic hypotheses can be met: reversible lookup tables

The scalar arithmetic of the signed and clipped regimes enters `gate_optimal_binary` as the
hypotheses `FactorWordArith`, `ClipFactorArith` and `ClipAngleArith`: reversible circuits of
controlled NOT gates with at most three controls that write angle and phase words of the decoded
scalars to a given accuracy and restore their work wires. This file shows that they can be met at
every positive accuracy, by reversible lookup tables (of length exponential in the input width),
so that the theorem holds without arithmetic hypotheses (`gate_optimal_binary_tables`).

* `cfgRun_mcGate`: on clean flags, the AND-chain gate `GateCircuit.mcGate ls fl t X` (released in
  `GateEfficientHamiltonian`) flips `t` exactly when all literals `ls` hold, and restores the
  flags; `mcGate_classical`, `mcGate_cs_length` (at most two controls per gate).
* `tableG`: for every pair `(u, o)` of a list `ps`, the gate `mcGate` on the output wire `o`
  controlled by the pattern `u` of the input wires; `cfgRun_tableG`: on clean flags, every output
  wire `o` is flipped once for each pair `(u, o) ∈ ps` whose pattern holds.
* `tableC`: the table of a word function `F` on the arithmetic register `I ⊕ AWr b_T b_P A`, with
  the pairs `(u, o)` with `F u o`; `tableC_compute` (the `compute` field of the hypotheses for
  `|I| ≤ A + 1` work wires), `tableC_classical`, `tableC_elem`, `tableC_length`
  (`|tableC F| ≤ 2^|I| (b_T + b_P)(2|I| + 1)`).
* Word rounding: `exists_word` (every `a ∈ [0, c]` is within `c/2^n` of the value
  `c · 0.w₀w₁…w_{n-1}` of an `n`-bit word), the decoders `thetaVal`, `phiVal`, `alphaVal` as
  word values (`thetaVal_eq`, `phiVal_eq`, `alphaVal_eq`), `roundW`, and the word lengths
  `bitsFor c e = ⌈log₂ ⌈c/e⌉⌉` with `c/2^n ≤ e` for `n ≥ bitsFor c e` (`div_pow_le`).
* Accuracy: `fac_acc` (the factor accuracy of `FactorArithOK` from the angle word of
  `arcsin √|c|` and the phase word of `arg c`, for `|c| ≤ 1`), `th_acc`, `ph_acc` (the angle
  accuracy of `ArithOK` from the words of `2 arctan |y|` and `arg y`).
* **`factorWordArith_exists`**, **`clipArith_exists`**: the hypotheses at every accuracy, with
  explicit word lengths, `2b` or `2b + 1` work wires and the table lengths;
  **`gate_optimal_binary_tables`**, `gate_optimal_binary_synth_tables`: `gate_optimal_binary_total`
  and `gate_optimal_binary_synth` with the table arithmetic, so with no arithmetic hypothesis.

The tables have `2^|I|` patterns, `|I| = 2b`, `2b + 1` or `2b + 2`; the manuscript's assumption
that the arithmetic has polynomially many gates is not met by them and remains the hypothesis of
the polynomial gate bound. References to the manuscript use its labels.
-/

set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace GateOptimalBinary

noncomputable section

open SparseHamiltonian SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
  SparseHamiltonian.GateBinary GateOptimalPrecision

/-! ### The AND-chain gate on configurations -/

section MC

variable {W : Type*} [Fintype W] [DecidableEq W]

omit [Fintype W] [DecidableEq W] in
theorem andChain_cs_length (p : W × Bool) (ls : List (W × Bool)) (fl : List W) :
    ∀ g ∈ andChain p ls fl, g.cs.length = 2 := by
  induction ls generalizing p fl with
  | nil => intro g hg; simp [andChain] at hg
  | cons l ls ih =>
      cases fl with
      | nil => intro g hg; simp [andChain] at hg
      | cons f fs =>
          intro g hg
          simp only [andChain, List.mem_cons] at hg
          rcases hg with rfl | hg
          · rfl
          · exact ih (f, true) fs g hg

omit [Fintype W] [DecidableEq W] in
theorem andLast_mem (p : W × Bool) (ls : List (W × Bool)) (fl : List W) :
    (andLast p ls fl).1 = p.1 ∨ (andLast p ls fl).1 ∈ fl := by
  induction ls generalizing p fl with
  | nil => exact Or.inl rfl
  | cons l ls ih =>
      cases fl with
      | nil => exact Or.inl rfl
      | cons f fs =>
          have e : andLast p (l :: ls) (f :: fs) = andLast (f, true) ls fs := rfl
          rw [e]
          rcases ih (f, true) fs with h | h
          · exact Or.inr (by rw [h]; exact List.mem_cons_self)
          · exact Or.inr (List.mem_cons_of_mem f h)

omit [Fintype W] [DecidableEq W] in
/-- Every gate of the AND-chain gate has at most two controls. -/
theorem mcGate_cs_length (ls : List (W × Bool)) (fl : List W) (t : W) (u : Matrix Bool Bool ℂ) :
    ∀ g ∈ mcGate ls fl t u, g.cs.length ≤ 2 := by
  cases ls with
  | nil =>
      intro g hg
      simp only [mcGate, List.mem_singleton] at hg
      subst hg
      simp
  | cons l ls' =>
      intro g hg
      simp only [mcGate, List.mem_append, List.mem_singleton] at hg
      rcases hg with (hg | rfl) | hg
      · exact (andChain_cs_length l ls' fl g hg).le
      · simp
      · obtain ⟨h, hh, rfl⟩ := mem_gInv _ g hg
        exact (andChain_cs_length l ls' fl h hh).le

omit [Fintype W] [DecidableEq W] in
/-- The AND-chain NOT gate is a list of classical gates. -/
theorem mcGate_classical (ls : List (W × Bool)) (fl : List W) (t : W) (hnd : fl.Nodup)
    (hlt : ∀ l ∈ ls, l.1 ≠ t) (hft : ∀ f ∈ fl, f ≠ t)
    (hlf : ∀ l ∈ ls, ∀ f ∈ fl, l.1 ≠ f) :
    Classical (mcGate ls fl t pauliX) := by
  cases ls with
  | nil =>
      intro g hg
      simp only [mcGate, List.mem_singleton] at hg
      subst hg
      exact ⟨rfl, fun c hc => by simp at hc⟩
  | cons l ls' =>
      have hch := andChain_classical l ls' fl (fun f hf => hlf l List.mem_cons_self f hf)
        (fun l' hl' f hf => hlf l' (List.mem_cons_of_mem l hl') f hf) hnd
      intro g hg
      simp only [mcGate, List.mem_append, List.mem_singleton] at hg
      rcases hg with (hg | rfl) | hg
      · exact hch g hg
      · refine ⟨rfl, ?_⟩
        intro c hc
        simp only [List.mem_singleton] at hc
        subst hc
        rcases andLast_mem l ls' fl with h | h
        · rw [h]
          exact hlt l List.mem_cons_self
        · exact hft _ h
      · obtain ⟨h, hh, rfl⟩ := mem_gInv _ g hg
        obtain ⟨hu, hc⟩ := hch h hh
        refine ⟨?_, hc⟩
        change h.u.conjTranspose = pauliX
        rw [hu, pauliX_conjTranspose]

omit [DecidableEq W] in
theorem bas_one_injective {x y : Cfg W} (h : bas (Q := ℂ) x 1 = bas y 1) : x = y := by
  have h1 := congrArg (fun ψ : Reg W ℂ => ψ x) h
  simp only [bas_apply, if_true] at h1
  by_contra hxy
  rw [if_neg hxy] at h1
  exact one_ne_zero h1

/-- **The AND-chain NOT gate on configurations**: on clean flags it flips the target exactly
when all literals hold, and the flags are clean again. -/
theorem cfgRun_mcGate (ls : List (W × Bool)) (fl : List W) (t : W)
    (hlen : ls.length ≤ fl.length + 1) (hnd : fl.Nodup)
    (hlt : ∀ l ∈ ls, l.1 ≠ t) (hft : ∀ f ∈ fl, f ≠ t)
    (hlf : ∀ l ∈ ls, ∀ f ∈ fl, l.1 ≠ f) (x : Cfg W) (hx : ∀ f ∈ fl, x f = false) :
    cfgRun (mcGate ls fl t pauliX) x = flipCfg ls t x := by
  have hA := mcGate_agrees (Q := ℂ) ls fl t pauliX hlen hnd hlt hft hlf
    (fun y => ∀ f ∈ fl, y f = false) (fun y hy => hy)
    (fun y b hy f hf => by rw [Function.update_of_ne (hft f hf)]; exact hy f hf)
  have hsupp : Supp (fun y : Cfg W => ∀ f ∈ fl, y f = false) (bas (Q := ℂ) x 1) := by
    intro y hy
    rw [bas_apply]
    split_ifs with hyx
    · subst hyx
      exact absurd hx hy
    · rfl
  have h1 := hA (bas x 1) hsupp
  rw [gRun_classical_bas _ (mcGate_classical ls fl t hnd hlt hft hlf),
    gateOp_pauliX_bas ls t hlt] at h1
  exact bas_one_injective h1

end MC

/-! ### Lookup tables -/

section Table

variable {W : Type*} [Fintype W] [DecidableEq W]
variable {I O : Type*} [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]

/-- The literals of a pattern `u` of the input wires `ι`. -/
def lits (ι : I → W) (u : Cfg I) : List (W × Bool) :=
  (Finset.univ : Finset I).toList.map (fun i => (ι i, u i))

omit [Fintype W] [DecidableEq W] [DecidableEq I] in
theorem lits_length (ι : I → W) (u : Cfg I) : (lits ι u).length = Fintype.card I := by
  simp [lits]

omit [Fintype W] [DecidableEq W] [DecidableEq I] in
theorem mem_lits (ι : I → W) (u : Cfg I) (c : W × Bool) :
    c ∈ lits ι u ↔ ∃ i, c = (ι i, u i) := by
  simp only [lits, List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i, rfl⟩

omit [Fintype W] [DecidableEq W] [DecidableEq I] in
/-- The pattern holds exactly when the inputs read it. -/
theorem ctrlOK_lits (ι : I → W) (u : Cfg I) (x : Cfg W) :
    ctrlOK (lits ι u) x = true ↔ (fun i => x (ι i)) = u := by
  rw [ctrlOK_iff]
  constructor
  · intro h
    funext i
    exact h (ι i, u i) ((mem_lits ι u _).2 ⟨i, rfl⟩)
  · intro h c hc
    obtain ⟨i, rfl⟩ := (mem_lits ι u c).1 hc
    exact congrFun h i

/-- **The lookup-table circuit** of the pairs `ps`: for every pair `(u, o)`, a NOT gate on the
output wire `ow o` controlled by the pattern `u` of the inputs, as an AND chain on the flags. -/
def tableG (ι : I → W) (ow : O → W) (fl : List W) (ps : List (Cfg I × O)) : List (Gate W) :=
  ps.flatMap (fun p => mcGate (lits ι p.1) fl (ow p.2) pauliX)

omit [Fintype W] [DecidableEq W] [DecidableEq I] [Fintype O] [DecidableEq O] in
theorem tableG_length_le (ι : I → W) (ow : O → W) (fl : List W) (ps : List (Cfg I × O)) :
    (tableG ι ow fl ps).length ≤ ps.length * (2 * Fintype.card I + 1) := by
  induction ps with
  | nil => simp [tableG]
  | cons p ps ih =>
      have h1 := mcGate_length_le (lits ι p.1) fl (ow p.2) pauliX
      rw [lits_length] at h1
      have e : tableG ι ow fl (p :: ps) =
          mcGate (lits ι p.1) fl (ow p.2) pauliX ++ tableG ι ow fl ps := by
        simp [tableG]
      rw [e, List.length_append, List.length_cons]
      calc _ ≤ (2 * Fintype.card I + 1) + ps.length * (2 * Fintype.card I + 1) :=
            add_le_add h1 ih
        _ = (ps.length + 1) * (2 * Fintype.card I + 1) := by ring

/-- The side conditions of the table: the flags are distinct and enough, and inputs, outputs and
flags are pairwise different wires. -/
structure TableOK (ι : I → W) (ow : O → W) (fl : List W) : Prop where
  len : Fintype.card I ≤ fl.length + 1
  nodup : fl.Nodup
  ow_inj : Function.Injective ow
  in_out : ∀ i o, ι i ≠ ow o
  in_fl : ∀ i, ∀ f ∈ fl, ι i ≠ f
  fl_out : ∀ o, ∀ f ∈ fl, f ≠ ow o

omit [Fintype W] [DecidableEq W] [DecidableEq I] [Fintype O] [DecidableEq O] in
theorem TableOK.lit_ne_out {ι : I → W} {ow : O → W} {fl : List W} (h : TableOK ι ow fl)
    (u : Cfg I) (o : O) : ∀ l ∈ lits ι u, l.1 ≠ ow o := by
  intro l hl
  obtain ⟨i, rfl⟩ := (mem_lits ι u l).1 hl
  exact h.in_out i o

omit [Fintype W] [DecidableEq W] [DecidableEq I] [Fintype O] [DecidableEq O] in
theorem TableOK.lit_ne_fl {ι : I → W} {ow : O → W} {fl : List W} (h : TableOK ι ow fl)
    (u : Cfg I) : ∀ l ∈ lits ι u, ∀ f ∈ fl, l.1 ≠ f := by
  intro l hl f hf
  obtain ⟨i, rfl⟩ := (mem_lits ι u l).1 hl
  exact h.in_fl i f hf

omit [Fintype W] [DecidableEq W] [DecidableEq I] [Fintype O] [DecidableEq O] in
theorem tableG_classical {ι : I → W} {ow : O → W} {fl : List W} (h : TableOK ι ow fl)
    (ps : List (Cfg I × O)) : Classical (tableG ι ow fl ps) := by
  intro g hg
  simp only [tableG, List.mem_flatMap] at hg
  obtain ⟨p, -, hg⟩ := hg
  exact mcGate_classical _ fl _ h.nodup (h.lit_ne_out p.1 p.2) (fun f hf => h.fl_out p.2 f hf)
    (h.lit_ne_fl p.1) g hg

omit [Fintype W] [DecidableEq W] [DecidableEq I] [Fintype O] [DecidableEq O] in
theorem tableG_cs_length (ι : I → W) (ow : O → W) (fl : List W) (ps : List (Cfg I × O)) :
    ∀ g ∈ tableG ι ow fl ps, g.cs.length ≤ 2 := by
  intro g hg
  simp only [tableG, List.mem_flatMap] at hg
  obtain ⟨p, -, hg⟩ := hg
  exact mcGate_cs_length _ fl _ pauliX g hg

omit [DecidableEq I] in
/-- **The table on configurations**: on clean flags, every output wire `ow o` is flipped exactly
when the pair of the input pattern and `o` belongs to `ps` (a list without repetitions). -/
theorem cfgRun_tableG {ι : I → W} {ow : O → W} {fl : List W} (h : TableOK ι ow fl)
    (ps : List (Cfg I × O)) (hps : ps.Nodup) (x : Cfg W) (hx : ∀ f ∈ fl, x f = false) :
    cfgRun (tableG ι ow fl ps) x =
      fun w => xor (x w) (decide (∃ o, ow o = w ∧ ((fun i => x (ι i)), o) ∈ ps)) := by
  induction ps generalizing x with
  | nil =>
      funext w
      simp [tableG, cfgRun]
  | cons p ps ih =>
      obtain ⟨hp, hps'⟩ := List.nodup_cons.mp hps
      have e : tableG ι ow fl (p :: ps) =
          mcGate (lits ι p.1) fl (ow p.2) pauliX ++ tableG ι ow fl ps := by
        simp [tableG]
      rw [e, cfgRun_append, cfgRun_mcGate _ fl _ (by rw [lits_length]; exact h.len) h.nodup
        (h.lit_ne_out p.1 p.2) (fun f hf => h.fl_out p.2 f hf) (h.lit_ne_fl p.1) x hx]
      set x₁ := flipCfg (lits ι p.1) (ow p.2) x with hx₁
      have hx₁w : ∀ w, w ≠ ow p.2 → x₁ w = x w := by
        intro w hw
        simp only [hx₁, flipCfg]
        split_ifs
        · rw [Function.update_of_ne hw]
        · rfl
      have hin : (fun i => x₁ (ι i)) = (fun i => x (ι i)) := by
        funext i
        exact hx₁w _ (h.in_out i p.2)
      have hfl : ∀ f ∈ fl, x₁ f = false := by
        intro f hf
        rw [hx₁w f (h.fl_out p.2 f hf)]
        exact hx f hf
      rw [ih hps' x₁ hfl, hin]
      funext w
      by_cases hm : (fun i => x (ι i)) = p.1
      · -- the pattern of `p` holds
        have hflip : x₁ = Function.update x (ow p.2) (!x (ow p.2)) := by
          simp only [hx₁, flipCfg]
          rw [if_pos ((ctrlOK_lits ι p.1 x).2 hm)]
        by_cases hw : w = ow p.2
        · subst hw
          have hl : ¬ ∃ o, ow o = ow p.2 ∧ ((fun i => x (ι i)), o) ∈ ps := by
            rintro ⟨o, ho, hmem⟩
            rw [h.ow_inj ho, hm] at hmem
            exact hp hmem
          have hr : ∃ o, ow o = ow p.2 ∧ ((fun i => x (ι i)), o) ∈ p :: ps :=
            ⟨p.2, rfl, by rw [hm]; exact List.mem_cons_self⟩
          rw [decide_eq_false hl, decide_eq_true hr, hflip, Function.update_self]
          cases x (ow p.2) <;> rfl
        · have hiff : (∃ o, ow o = w ∧ ((fun i => x (ι i)), o) ∈ ps) ↔
              (∃ o, ow o = w ∧ ((fun i => x (ι i)), o) ∈ p :: ps) := by
            constructor
            · rintro ⟨o, ho, hmem⟩
              exact ⟨o, ho, List.mem_cons_of_mem p hmem⟩
            · rintro ⟨o, ho, hmem⟩
              refine ⟨o, ho, ?_⟩
              rcases List.mem_cons.mp hmem with heq | hmem
              · exfalso
                apply hw
                rw [← ho]
                exact congrArg ow (congrArg Prod.snd heq)
              · exact hmem
          rw [hx₁w w hw]
          simp only [hiff]
      · -- the pattern of `p` does not hold
        have hflip : x₁ = x := by
          simp only [hx₁, flipCfg]
          rw [if_neg (fun hc => hm ((ctrlOK_lits ι p.1 x).1 hc))]
        have hiff : (∃ o, ow o = w ∧ ((fun i => x (ι i)), o) ∈ ps) ↔
            (∃ o, ow o = w ∧ ((fun i => x (ι i)), o) ∈ p :: ps) := by
          constructor
          · rintro ⟨o, ho, hmem⟩
            exact ⟨o, ho, List.mem_cons_of_mem p hmem⟩
          · rintro ⟨o, ho, hmem⟩
            refine ⟨o, ho, ?_⟩
            rcases List.mem_cons.mp hmem with heq | hmem
            · exfalso
              apply hm
              exact congrArg Prod.fst heq
            · exact hmem
        rw [hflip]
        simp only [hiff]

end Table

/-! ### The table on the arithmetic register -/

section ArithTable

variable {I : Type*} [Fintype I] [DecidableEq I] {bT bP A : ℕ}

/-- The output wires of the arithmetic register: the angle word and the phase word. -/
def outW (I : Type*) (bT bP A : ℕ) : Fin bT ⊕ Fin bP → I ⊕ AWr bT bP A :=
  fun o => Sum.inr (Sum.inl o)

/-- The work wires of the arithmetic register, used as the flags of the AND chains. -/
def flW (I : Type*) (bT bP A : ℕ) : List (I ⊕ AWr bT bP A) :=
  (List.finRange A).map (fun k => Sum.inr (Sum.inr k))

/-- The pairs of the table of a word function `F`: the patterns and the bits set by `F`. -/
def tablePairs (F : Cfg I → Fin bT ⊕ Fin bP → Bool) : List (Cfg I × (Fin bT ⊕ Fin bP)) :=
  (Finset.univ.filter (fun p : Cfg I × (Fin bT ⊕ Fin bP) => F p.1 p.2 = true)).toList

/-- **The lookup-table arithmetic** of a word function `F` on the input wires `I` and the
arithmetic wires `AWr b_T b_P A`. -/
def tableC (F : Cfg I → Fin bT ⊕ Fin bP → Bool) : List (Gate (I ⊕ AWr bT bP A)) :=
  tableG Sum.inl (outW I bT bP A) (flW I bT bP A) (tablePairs F)

omit [Fintype I] [DecidableEq I] in
theorem mem_flW (f : I ⊕ AWr bT bP A) : f ∈ flW I bT bP A ↔ ∃ k, f = Sum.inr (Sum.inr k) := by
  simp only [flW, List.mem_map, List.mem_finRange, true_and]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k, rfl⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k, rfl⟩

omit [DecidableEq I] in
theorem tableOK_arith (hA : Fintype.card I ≤ A + 1) :
    TableOK (Sum.inl : I → I ⊕ AWr bT bP A) (outW I bT bP A) (flW I bT bP A) where
  len := by simpa [flW] using hA
  nodup := (List.nodup_finRange A).map (fun a b h => by simpa using h)
  ow_inj := fun a b h => by simpa [outW] using h
  in_out := fun i o h => by simp [outW] at h
  in_fl := fun i f hf h => by
    obtain ⟨k, rfl⟩ := (mem_flW f).1 hf
    simp at h
  fl_out := fun o f hf h => by
    obtain ⟨k, rfl⟩ := (mem_flW f).1 hf
    simp [outW] at h

theorem mem_tablePairs (F : Cfg I → Fin bT ⊕ Fin bP → Bool) (p : Cfg I × (Fin bT ⊕ Fin bP)) :
    p ∈ tablePairs F ↔ F p.1 p.2 = true := by
  simp [tablePairs]

/-- **The `compute` field**: on clean arithmetic wires the table writes the words of `F` and
restores the work wires, for `|I| ≤ A + 1`. -/
theorem tableC_compute (hA : Fintype.card I ≤ A + 1) (F : Cfg I → Fin bT ⊕ Fin bP → Bool)
    (w : Cfg I) :
    cfgRun (tableC (A := A) F) (Sum.elim w (fun _ => false)) =
      Sum.elim w (Sum.elim (F w) (fun _ => false)) := by
  have hclean : ∀ f ∈ flW I bT bP A, (Sum.elim w (fun _ => false) : Cfg (I ⊕ AWr bT bP A)) f =
      false := by
    intro f hf
    obtain ⟨k, rfl⟩ := (mem_flW f).1 hf
    rfl
  rw [tableC, cfgRun_tableG (tableOK_arith hA) (tablePairs F) (Finset.nodup_toList _) _ hclean]
  have hin : (fun i => (Sum.elim w (fun _ => false) : Cfg (I ⊕ AWr bT bP A)) (Sum.inl i)) = w :=
    rfl
  rw [hin]
  funext y
  rcases y with i | (o | k)
  · simp [outW]
  · simp [outW, mem_tablePairs]
  · simp [outW]

theorem tableC_classical (hA : Fintype.card I ≤ A + 1) (F : Cfg I → Fin bT ⊕ Fin bP → Bool) :
    Classical (tableC (A := A) F) :=
  tableG_classical (tableOK_arith hA) _

theorem tableC_elem (F : Cfg I → Fin bT ⊕ Fin bP → Bool) :
    ∀ g ∈ tableC (A := A) F, g.cs.length ≤ 3 :=
  fun g hg => (tableG_cs_length _ _ _ _ g hg).trans (by norm_num)

/-- The length of the table: at most `2^|I| (b_T + b_P)` AND-chain gates of at most
`2|I| + 1` gates each. -/
theorem tableC_length (F : Cfg I → Fin bT ⊕ Fin bP → Bool) :
    (tableC (A := A) F).length ≤ 2 ^ Fintype.card I * (bT + bP) * (2 * Fintype.card I + 1) := by
  refine (tableG_length_le _ _ _ _).trans ?_
  have hc : (tablePairs F).length ≤ 2 ^ Fintype.card I * (bT + bP) := by
    rw [tablePairs, Finset.length_toList]
    refine (Finset.card_filter_le _ _).trans ?_
    simp [Fintype.card_prod, Fintype.card_sum]
  exact Nat.mul_le_mul_right _ hc

end ArithTable

/-! ### Rounding to binary angle words -/

section Words

/-- The value `c · 0.w₀w₁…w_{n-1}` of an `n`-bit word: bit `j` is worth `c/2^{j+1}`. -/
def wval (c : ℝ) {n : ℕ} (w : Fin n → Bool) : ℝ :=
  ∑ j : Fin n, if w j then c / 2 ^ (j.val + 1) else 0

theorem thetaVal_eq {n : ℕ} (w : Fin n → Bool) : thetaVal w = wval Real.pi w := rfl

theorem phiVal_eq {n : ℕ} (w : Fin n → Bool) : phiVal w = wval (2 * Real.pi) w := rfl

theorem alphaVal_eq {n : ℕ} (w : Fin n → Bool) : alphaVal w = wval (Real.pi / 2) w := by
  unfold alphaVal wval
  apply Finset.sum_congr rfl
  intro j _
  split_ifs
  · rw [pow_succ]
    ring
  · rfl

theorem wval_cons (c : ℝ) {n : ℕ} (b : Bool) (w : Fin n → Bool) :
    wval c (Fin.cons b w : Fin (n + 1) → Bool) = (if b then c / 2 else 0) + wval (c / 2) w := by
  unfold wval
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, Fin.val_zero, Fin.val_succ, zero_add, pow_one]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  split_ifs
  · rw [pow_succ]
    ring
  · rfl

/-- **Rounding**: every `a ∈ [0, c]` is within `c/2^n` of the value of an `n`-bit word. -/
theorem exists_word (n : ℕ) : ∀ (c a : ℝ), 0 ≤ a → a ≤ c →
    ∃ w : Fin n → Bool, |wval c w - a| ≤ c / 2 ^ n := by
  induction n with
  | zero =>
      intro c a ha0 hac
      refine ⟨Fin.elim0, ?_⟩
      simp only [wval, Finset.univ_eq_empty, Finset.sum_empty, zero_sub, abs_neg, pow_zero,
        div_one]
      rw [abs_of_nonneg ha0]
      exact hac
  | succ n ih =>
      intro c a ha0 hac
      have e : c / 2 ^ (n + 1) = c / 2 / 2 ^ n := by
        rw [pow_succ]
        ring
      by_cases hb : c / 2 ≤ a
      · obtain ⟨w, hw⟩ := ih (c / 2) (a - c / 2) (by linarith) (by linarith)
        refine ⟨Fin.cons true w, ?_⟩
        rw [wval_cons, if_pos rfl, e]
        have : c / 2 + wval (c / 2) w - a = wval (c / 2) w - (a - c / 2) := by ring
        rw [this]
        exact hw
      · push Not at hb
        obtain ⟨w, hw⟩ := ih (c / 2) a ha0 hb.le
        refine ⟨Fin.cons false w, ?_⟩
        rw [wval_cons, e]
        simpa using hw

/-- The rounded word of `a` (any word if `a ∉ [0, c]`). -/
def roundW (c : ℝ) (n : ℕ) (a : ℝ) : Fin n → Bool :=
  if h : 0 ≤ a ∧ a ≤ c then Classical.choose (exists_word n c a h.1 h.2) else fun _ => false

theorem roundW_spec {c a : ℝ} (n : ℕ) (h0 : 0 ≤ a) (h1 : a ≤ c) :
    |wval c (roundW c n a) - a| ≤ c / 2 ^ n := by
  unfold roundW
  rw [dif_pos ⟨h0, h1⟩]
  exact Classical.choose_spec (exists_word n c a h0 h1)

/-- The word length `⌈log₂ ⌈c/e⌉⌉` for the accuracy `e`. -/
def bitsFor (c e : ℝ) : ℕ := Nat.clog 2 ⌈c / e⌉₊

theorem div_pow_le {c e : ℝ} (he : 0 < e) {n : ℕ} (hn : bitsFor c e ≤ n) : c / 2 ^ n ≤ e := by
  have h1 : c / e ≤ (⌈c / e⌉₊ : ℝ) := Nat.le_ceil _
  have h2 : (⌈c / e⌉₊ : ℝ) ≤ (2 : ℝ) ^ bitsFor c e := by
    exact_mod_cast Nat.le_pow_clog (by norm_num) _
  have h3 : (2 : ℝ) ^ bitsFor c e ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
  have hpos : (0 : ℝ) < 2 ^ n := by positivity
  rw [div_le_iff₀ hpos]
  have h4 := (div_le_iff₀ he).1 (h1.trans (h2.trans h3))
  linarith

end Words

/-! ### Accuracy of the rounded words -/

section Accuracy

theorem sin_sq_sub_le (a b : ℝ) : |Real.sin a ^ 2 - Real.sin b ^ 2| ≤ 2 * |a - b| := by
  have e : Real.sin a ^ 2 - Real.sin b ^ 2 =
      (Real.sin a - Real.sin b) * (Real.sin a + Real.sin b) := by ring
  rw [e, abs_mul]
  have h1 := Real.abs_sin_sub_sin_le a b
  have h2 : |Real.sin a + Real.sin b| ≤ 2 := by
    have ha := Real.abs_sin_le_one a
    have hb := Real.abs_sin_le_one b
    calc |Real.sin a + Real.sin b| ≤ |Real.sin a| + |Real.sin b| := abs_add_le _ _
      _ ≤ 2 := by linarith
  calc |Real.sin a - Real.sin b| * |Real.sin a + Real.sin b| ≤ |a - b| * 2 :=
        mul_le_mul h1 h2 (abs_nonneg _) (abs_nonneg _)
    _ = 2 * |a - b| := by ring

theorem phase_eq_exp {z : ℂ} (hz : z ≠ 0) :
    NativeSignedFactor.phase z = Complex.exp (Complex.arg z * Complex.I) := by
  unfold NativeSignedFactor.phase
  rw [if_neg hz]
  have hn : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hz
  rw [div_eq_iff hn, mul_comm (Complex.exp _) _]
  exact (Complex.norm_mul_exp_arg_mul_I z).symm

/-- The phase target `arg z`, taken in `[0, 2π]`. -/
def phT (z : ℂ) : ℝ := if 0 ≤ Complex.arg z then Complex.arg z else Complex.arg z + 2 * Real.pi

theorem phT_mem (z : ℂ) : 0 ≤ phT z ∧ phT z ≤ 2 * Real.pi := by
  have h1 := Complex.neg_pi_lt_arg z
  have h2 := Complex.arg_le_pi z
  have hπ := Real.pi_pos
  unfold phT
  split_ifs with h
  · exact ⟨h, by linarith⟩
  · exact ⟨by linarith, by linarith⟩

theorem exp_phT (z : ℂ) :
    Complex.exp (phT z * Complex.I) = Complex.exp (Complex.arg z * Complex.I) := by
  unfold phT
  split_ifs
  · rfl
  · push_cast
    rw [add_mul, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

/-- The angle word of the factor arithmetic for the entry `z`: zero below the threshold `ξ²/16`,
otherwise the rounded word of `arcsin √|z|`. -/
def facTw (ξ : ℝ) (n : ℕ) (z : ℂ) : Fin n → Bool :=
  if ‖z‖ ≤ ξ ^ 2 / 16 then fun _ => false else roundW (Real.pi / 2) n (Real.arcsin (Real.sqrt ‖z‖))

/-- The rounded phase word of `arg z`. -/
def phW (n : ℕ) (z : ℂ) : Fin n → Bool := roundW (2 * Real.pi) n (phT z)

/-- The rounded angle word of `2 arctan |z|`. -/
def thW (n : ℕ) (z : ℂ) : Fin n → Bool := roundW Real.pi n (2 * Real.arctan ‖z‖)

/-- **The factor accuracy** (`FactorArithOK.acc`) of the rounded words, for `|z| ≤ 1`, with
`π/2^{b_T} ≤ ξ²` and `2π/2^{b_P} ≤ ξ`. -/
theorem fac_acc {ξ : ℝ} (hξ : 0 < ξ) {bT bP : ℕ} (hT : Real.pi / 2 ^ bT ≤ ξ ^ 2)
    (hP : 2 * Real.pi / 2 ^ bP ≤ ξ) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    (‖z‖ ≤ ξ ^ 2 / 16 ∧ alphaVal (facTw ξ bT z) = 0) ∨
    (|Real.sin (alphaVal (facTw ξ bT z)) ^ 2 - ‖z‖| ≤ ξ ^ 2 ∧
      ‖Complex.exp (phiVal (phW bP z) * Complex.I) - NativeSignedFactor.phase z‖ ≤ ξ) := by
  by_cases hs : ‖z‖ ≤ ξ ^ 2 / 16
  · left
    refine ⟨hs, ?_⟩
    simp [facTw, if_pos hs, alphaVal]
  · right
    have hz0 : z ≠ 0 := by
      intro h0
      apply hs
      rw [h0, norm_zero]
      positivity
    have hα0 : 0 ≤ Real.arcsin (Real.sqrt ‖z‖) := Real.arcsin_nonneg.mpr (Real.sqrt_nonneg _)
    have hα1 : Real.arcsin (Real.sqrt ‖z‖) ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two _
    have hsq1 : Real.sqrt ‖z‖ ≤ 1 := (Real.sqrt_le_sqrt hz).trans_eq Real.sqrt_one
    have hsin : Real.sin (Real.arcsin (Real.sqrt ‖z‖)) ^ 2 = ‖z‖ := by
      rw [Real.sin_arcsin (by linarith [Real.sqrt_nonneg ‖z‖]) hsq1]
      exact Real.sq_sqrt (norm_nonneg _)
    have hw := roundW_spec (c := Real.pi / 2) bT hα0 hα1
    rw [facTw, if_neg hs, alphaVal_eq]
    refine ⟨?_, ?_⟩
    · calc |Real.sin (wval (Real.pi / 2) (roundW (Real.pi / 2) bT
            (Real.arcsin (Real.sqrt ‖z‖)))) ^ 2 - ‖z‖|
          = |Real.sin (wval (Real.pi / 2) (roundW (Real.pi / 2) bT
            (Real.arcsin (Real.sqrt ‖z‖)))) ^ 2 -
              Real.sin (Real.arcsin (Real.sqrt ‖z‖)) ^ 2| := by rw [hsin]
        _ ≤ 2 * |wval (Real.pi / 2) (roundW (Real.pi / 2) bT
            (Real.arcsin (Real.sqrt ‖z‖))) - Real.arcsin (Real.sqrt ‖z‖)| := sin_sq_sub_le _ _
        _ ≤ 2 * (Real.pi / 2 / 2 ^ bT) := by linarith
        _ = Real.pi / 2 ^ bT := by ring
        _ ≤ ξ ^ 2 := hT
    · rw [phase_eq_exp hz0, ← exp_phT z, phiVal_eq]
      calc _ ≤ |wval (2 * Real.pi) (phW bP z) - phT z| := norm_exp_sub_exp_le _ _
        _ ≤ 2 * Real.pi / 2 ^ bP := roundW_spec bP (phT_mem z).1 (phT_mem z).2
        _ ≤ ξ := hP

/-- **The angle accuracy** (`ArithOK.theta`) of the rounded word of `2 arctan |z|`. -/
theorem th_acc {ζ : ℝ} {bT : ℕ} (hT : Real.pi / 2 ^ bT ≤ ζ) (z : ℂ) :
    |thetaVal (thW bT z) - 2 * Real.arctan ‖z‖| ≤ ζ := by
  have h0 : 0 ≤ 2 * Real.arctan ‖z‖ := by
    have := Real.arctan_nonneg.mpr (norm_nonneg z)
    linarith
  have h1 : 2 * Real.arctan ‖z‖ ≤ Real.pi := by
    have := Real.arctan_lt_pi_div_two ‖z‖
    linarith
  rw [thetaVal_eq]
  exact (roundW_spec bT h0 h1).trans hT

/-- **The phase accuracy** (`ArithOK.phi`) of the rounded word of `arg z`, modulo `2π`. -/
theorem ph_acc {ζ : ℝ} {bP : ℕ} (hP : 2 * Real.pi / 2 ^ bP ≤ ζ) (z : ℂ) :
    ∃ m : ℤ, |phiVal (phW bP z) - Complex.arg z - 2 * Real.pi * m| ≤ ζ := by
  have hw : |phiVal (phW bP z) - phT z| ≤ 2 * Real.pi / 2 ^ bP :=
    roundW_spec bP (phT_mem z).1 (phT_mem z).2
  by_cases h : 0 ≤ Complex.arg z
  · refine ⟨0, ?_⟩
    have e : phiVal (phW bP z) - Complex.arg z - 2 * Real.pi * ((0 : ℤ) : ℝ) =
        phiVal (phW bP z) - phT z := by
      unfold phT
      rw [if_pos h]
      push_cast
      ring
    rw [e]
    exact hw.trans hP
  · refine ⟨1, ?_⟩
    have e : phiVal (phW bP z) - Complex.arg z - 2 * Real.pi * ((1 : ℤ) : ℝ) =
        phiVal (phW bP z) - phT z := by
      unfold phT
      rw [if_neg h]
      push_cast
      ring
    rw [e]
    exact hw.trans hP

end Accuracy

/-! ### The arithmetic hypotheses from tables -/

section Hypotheses

variable {b : ℕ}

theorem norm_wdec_le (κ : ℝ) (w : Cfg (VW b)) : ‖wdec κ w‖ ≤ 1 :=
  NativeSignedFactor.norm_clip_le _

theorem card_VW (b : ℕ) : Fintype.card (VW b) = 2 * b := by
  simp [VW, Fintype.card_sum]
  ring

/-- **The table arithmetic of the signed factor**, with the rounded words of the decoded entry. -/
def factorTable (b : ℕ) (κ : ℝ) {ξ : ℝ} (hξ : 0 < ξ) {bT bP A : ℕ} (hA : 2 * b ≤ A + 1)
    (hT : Real.pi / 2 ^ bT ≤ ξ ^ 2) (hP : 2 * Real.pi / 2 ^ bP ≤ ξ) :
    FactorWordArith b κ ξ bT bP A where
  circ := tableC (A := A) (fun w => Sum.elim (facTw ξ bT (wdec κ w)) (phW bP (wdec κ w)))
  tw w := facTw ξ bT (wdec κ w)
  pw w := phW bP (wdec κ w)
  elem := tableC_elem _
  classical := tableC_classical (by rw [card_VW]; exact hA) _
  compute w := tableC_compute (by rw [card_VW]; exact hA) _ w
  acc w := fac_acc hξ hT hP _ (norm_wdec_le κ w)

theorem card_FIn (b : ℕ) : Fintype.card (Unit ⊕ VW b) = 2 * b + 1 := by
  rw [Fintype.card_sum, card_VW]
  simp
  ring

theorem card_CIn (b : ℕ) : Fintype.card ((Unit ⊕ Unit) ⊕ VW b) = 2 * b + 2 := by
  rw [Fintype.card_sum, card_VW]
  simp [Fintype.card_sum]
  ring

/-- **The table arithmetic of the clipped factor**. -/
def clipFactorTable (b : ℕ) (μ β c0 : ℝ) {ξ : ℝ} (hξ : 0 < ξ) {bT bP A : ℕ}
    (hA : 2 * b + 1 ≤ A + 1) (hT : Real.pi / 2 ^ bT ≤ ξ ^ 2) (hP : 2 * Real.pi / 2 ^ bP ≤ ξ) :
    ClipFactorArith b μ β c0 ξ bT bP A where
  circ := tableC (A := A)
    (fun w => Sum.elim (facTw ξ bT (cfdec μ β c0 w)) (phW bP (cfdec μ β c0 w)))
  tw w := facTw ξ bT (cfdec μ β c0 w)
  pw w := phW bP (cfdec μ β c0 w)
  elem := tableC_elem _
  classical := tableC_classical (by rw [card_FIn]; exact hA) _
  compute w := tableC_compute (by rw [card_FIn]; exact hA) _ w
  acc w := fac_acc hξ hT hP _ (norm_cfdec_le μ β c0 w)

/-- **The table arithmetic of the clipped rotation**. -/
def clipAngleTable (b : ℕ) (μ β q c0 : ℝ) {ζ : ℝ} {bT bP A : ℕ} (hA : 2 * b + 2 ≤ A + 1)
    (hT : Real.pi / 2 ^ bT ≤ ζ) (hP : 2 * Real.pi / 2 ^ bP ≤ ζ) :
    ClipAngleArith b μ β q c0 ζ bT bP A where
  circ := tableC (A := A)
    (fun w => Sum.elim (thW bT (ckdec μ β q c0 w)) (phW bP (ckdec μ β q c0 w)))
  tw w := thW bT (ckdec μ β q c0 w)
  pw w := phW bP (ckdec μ β q c0 w)
  elem := tableC_elem _
  classical := tableC_classical (by rw [card_CIn]; exact hA) _
  compute w := tableC_compute (by rw [card_CIn]; exact hA) _ w
  theta w := th_acc hT _
  phi w _ := ph_acc hP _

/-- The angle-word length of the clipped tables: `π/2^{b_T} ≤ min(ξ², ζ)`. -/
def clipBT (ξ ζ : ℝ) : ℕ := max (bitsFor Real.pi (ξ ^ 2)) (bitsFor Real.pi ζ)

/-- The phase-word length of the clipped tables: `2π/2^{b_P} ≤ min(ξ, ζ)`. -/
def clipBP (ξ ζ : ℝ) : ℕ := max (bitsFor (2 * Real.pi) ξ) (bitsFor (2 * Real.pi) ζ)

/-- **The signed-factor arithmetic hypothesis can be met at every accuracy `ξ > 0`**: by the
lookup table `factorTable` on `2b` work wires, with the word lengths `bitsFor π ξ²` and
`bitsFor 2π ξ` and at most `2^{2b} (b_T + b_P)(4b + 1)` gates. -/
theorem factorWordArith_exists (b : ℕ) (κ : ℝ) {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ ar : FactorWordArith b κ ξ (bitsFor Real.pi (ξ ^ 2)) (bitsFor (2 * Real.pi) ξ) (2 * b),
      ar.circ.length ≤ 2 ^ (2 * b) * (bitsFor Real.pi (ξ ^ 2) + bitsFor (2 * Real.pi) ξ) *
        (4 * b + 1) := by
  refine ⟨factorTable b κ hξ (by omega) (div_pow_le (by positivity) le_rfl)
    (div_pow_le hξ le_rfl), ?_⟩
  have h := tableC_length (I := VW b) (A := 2 * b)
    (fun w => Sum.elim (facTw ξ (bitsFor Real.pi (ξ ^ 2)) (wdec κ w))
      (phW (bitsFor (2 * Real.pi) ξ) (wdec κ w)))
  rw [card_VW] at h
  calc _ ≤ _ := h
    _ = _ := by ring

/-- **The clipped arithmetic hypotheses can be met at all accuracies `ξ, ζ > 0`**, on common
arithmetic wires: by the lookup tables `clipFactorTable` and `clipAngleTable` on `2b + 1` work
wires, with the word lengths `clipBT ξ ζ`, `clipBP ξ ζ`. -/
theorem clipArith_exists (b : ℕ) (μ β q c0 : ℝ) {ξ ζ : ℝ} (hξ : 0 < ξ) (hζ : 0 < ζ) :
    ∃ (af : ClipFactorArith b μ β c0 ξ (clipBT ξ ζ) (clipBP ξ ζ) (2 * b + 1))
      (aa : ClipAngleArith b μ β q c0 ζ (clipBT ξ ζ) (clipBP ξ ζ) (2 * b + 1)),
      af.circ.length ≤ 2 ^ (2 * b + 1) * (clipBT ξ ζ + clipBP ξ ζ) * (4 * b + 3) ∧
      aa.circ.length ≤ 2 ^ (2 * b + 2) * (clipBT ξ ζ + clipBP ξ ζ) * (4 * b + 5) := by
  have hT1 : Real.pi / 2 ^ clipBT ξ ζ ≤ ξ ^ 2 := div_pow_le (by positivity) (le_max_left _ _)
  have hP1 : 2 * Real.pi / 2 ^ clipBP ξ ζ ≤ ξ := div_pow_le hξ (le_max_left _ _)
  have hT2 : Real.pi / 2 ^ clipBT ξ ζ ≤ ζ := div_pow_le hζ (le_max_right _ _)
  have hP2 : 2 * Real.pi / 2 ^ clipBP ξ ζ ≤ ζ := div_pow_le hζ (le_max_right _ _)
  refine ⟨clipFactorTable b μ β c0 hξ (by omega) hT1 hP1,
    clipAngleTable b μ β q c0 (by omega) hT2 hP2, ?_, ?_⟩
  · have h := tableC_length (I := Unit ⊕ VW b) (A := 2 * b + 1)
      (fun w => Sum.elim (facTw ξ (clipBT ξ ζ) (cfdec μ β c0 w))
        (phW (clipBP ξ ζ) (cfdec μ β c0 w)))
    rw [card_FIn] at h
    calc _ ≤ _ := h
      _ = _ := by ring
  · have h := tableC_length (I := (Unit ⊕ Unit) ⊕ VW b) (A := 2 * b + 1)
      (fun w => Sum.elim (thW (clipBT ξ ζ) (ckdec μ β q c0 w))
        (phW (clipBP ξ ζ) (ckdec μ β q c0 w)))
    rw [card_CIn] at h
    calc _ ≤ _ := h
      _ = _ := by ring

end Hypotheses

/-! ### Theorem `gate:thm:main` without arithmetic hypotheses -/

section Endpoint

open NativeSparseBlockEncoding (Data Query)
open LargeSparsityCore.Parameters (hval qval Lval Regime)

variable {X n : Type*} [Fintype n] [DecidableEq n] {s k b : ℕ}
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
variable {D : Data X n (Cfg (VW b)) s} {en : Cfg (Fin k) ≃ n} {sb : ℕ} {c0 : ℝ} {x : X}
  {η μ t ε σ θ : ℝ}

/-- **Theorem `gate:thm:main` from binary sparse oracles with lookup-table arithmetic**
(native form, total error `ε`). For the parameters of the theorem at `ε/2` and accuracies
`ξ > 0`, `0 < ζ ≤ 1` with `8·10¹¹ Q_μ (6ξ + 4ζ) ≤ ε`, the lookup tables `ar`, `af`, `aa` of
`factorWordArith_exists` and `clipArith_exists`, with their lengths, are fixed before the instance;
for every binary sparse input they give the conclusion of `gate_optimal_binary_total`, with no
arithmetic hypothesis. -/
theorem gate_optimal_binary_tables [FiniteDimensional ℂ R]
    (hP : MainParams s η μ t (ε / 2) σ θ) {ξ ζ : ℝ} (hξ : 0 < ξ) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hδε : 8 * 10 ^ 11 * Qmu s η μ t ε * (6 * ξ + 4 * ζ) ≤ ε) :
    ∃ (ar : FactorWordArith b (c0 / μ) ξ (bitsFor Real.pi (ξ ^ 2)) (bitsFor (2 * Real.pi) ξ)
        (2 * b))
      (af : ClipFactorArith b μ (hval θ (ε / 2)) c0 ξ (clipBT ξ ζ) (clipBP ξ ζ) (2 * b + 1))
      (aa : ClipAngleArith b μ (hval θ (ε / 2)) (qval σ θ (ε / 2)) c0 ζ (clipBT ξ ζ)
        (clipBP ξ ζ) (2 * b + 1)),
      ar.circ.length ≤ 2 ^ (2 * b) * (bitsFor Real.pi (ξ ^ 2) + bitsFor (2 * Real.pi) ξ) *
        (4 * b + 1) ∧
      af.circ.length ≤ 2 ^ (2 * b + 1) * (clipBT ξ ζ + clipBP ξ ζ) * (4 * b + 3) ∧
      aa.circ.length ≤ 2 ^ (2 * b + 2) * (clipBT ξ ζ + clipBP ξ ζ) * (4 * b + 5) ∧
      ∀ (D : Data X n (Cfg (VW b)) s) (x : X) (hI : BinaryInput D en sb c0 x η μ),
      ((hval θ (ε / 2) < 10 ^ 4 ∧
        NativeClaims (prims (R := R) D en x)
          (bdNativeCircuit k b sb hI.hsb s c0 η σ θ (ε / 2) ζ t) (sysH (R := R) D en x) t
          (ε / 2) (2 * Qmu s η μ t ε) (fun p => 2 * nCallsN p (computeV k b))
          (bdNativeCost k b sb s c0 η σ θ (ε / 2) ζ) ε) ∨
      (∃ (_ : 10 ^ 4 ≤ hval θ (ε / 2)) (_ : σ * θ < Lval (ε / 2) * hval θ (ε / 2)),
        NativeClaims (prims (R := R) D en x)
          (sgNativeCircuit k b sb hI.hsb s μ σ t (ε / 2) c0 ar) (sysH (R := R) D en x) t
          (ε / 2) (2 * Qmu s η μ t ε) (fun p => 2 * nCallsN p (computeV k b))
          (sgNativeCost k sb ar) ε) ∨
      (∃ _ : Regime σ θ (ε / 2),
        NativeClaims (prims (R := R) D en x)
          (clNativeCircuit k b sb hI.hsb σ θ (ε / 2) t af aa) (sysH (R := R) D en x) t
          (ε / 2) (2 * Qmu s η μ t ε) (fun p => 6 * nCallsN p (computeV k b))
          (clNativeCost k sb af aa) ε)) := by
  obtain ⟨ar, har⟩ := factorWordArith_exists b (c0 / μ) hξ
  obtain ⟨af, aa, haf, haa⟩ := clipArith_exists b μ (hval θ (ε / 2)) (qval σ θ (ε / 2)) c0 hξ hζ
  exact ⟨ar, af, aa, har, haf, haa, fun _ _ hI => gate_optimal_binary_total hI hP hξ.le hζ hζ1
    hδε (fun _ _ => ar) (fun _ => af) (fun _ => aa)⟩

/-- **Theorem `gate:thm:main` from binary sparse oracles over a finite gate set, with
lookup-table arithmetic**: `gate_optimal_binary_synth` with the tables of
`gate_optimal_binary_tables`, fixed with their lengths before the instance; the only hypothesis
beyond the data and the parameters is the synthesis hypothesis `Synthesis 𝒢 X_a L`. -/
theorem gate_optimal_binary_synth_tables [FiniteDimensional ℂ R]
    (hP : MainParams s η μ t (ε / 2) σ θ) {ξ ζ : ℝ}
    (hξ : 0 < ξ) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hδε : 8 * 10 ^ 11 * Qmu s η μ t ε * (6 * ξ + 4 * ζ) ≤ ε)
    {𝒢 : Set GateSynth.Kind} {Xa : Type*} [Fintype Xa] [DecidableEq Xa] {L : ℝ → ℕ}
    (hS : GateSynth.Synthesis 𝒢 Xa L) {ε' : ℝ} (hε' : 0 < ε') :
    ∃ (ar : FactorWordArith b (c0 / μ) ξ (bitsFor Real.pi (ξ ^ 2)) (bitsFor (2 * Real.pi) ξ)
        (2 * b))
      (af : ClipFactorArith b μ (hval θ (ε / 2)) c0 ξ (clipBT ξ ζ) (clipBP ξ ζ) (2 * b + 1))
      (aa : ClipAngleArith b μ (hval θ (ε / 2)) (qval σ θ (ε / 2)) c0 ζ (clipBT ξ ζ)
        (clipBP ξ ζ) (2 * b + 1)),
      ar.circ.length ≤ 2 ^ (2 * b) * (bitsFor Real.pi (ξ ^ 2) + bitsFor (2 * Real.pi) ξ) *
        (4 * b + 1) ∧
      af.circ.length ≤ 2 ^ (2 * b + 1) * (clipBT ξ ζ + clipBP ξ ζ) * (4 * b + 3) ∧
      aa.circ.length ≤ 2 ^ (2 * b + 2) * (clipBT ξ ζ + clipBP ξ ζ) * (4 * b + 5) ∧
      ∀ (D : Data X n (Cfg (VW b)) s) (x : X) (hI : BinaryInput D en sb c0 x η μ),
      ((hval θ (ε / 2) < 10 ^ 4 ∧
        SynthClaims (prims (R := R) D en x) 𝒢 Xa L ε'
          (GateSynth.synthBudget hS ε' (bdNativeCircuit k b sb hI.hsb s c0 η σ θ (ε / 2) ζ t))
          (sysH (R := R) D en x) t (ε / 2) (2 * Qmu s η μ t ε)
          (fun p => 2 * nCallsN p (computeV k b))
          (nGatesN (bdNativeCircuit k b sb hI.hsb s c0 η σ θ (ε / 2) ζ t))
          (bdNativeCost k b sb s c0 η σ θ (ε / 2) ζ) (ε + ε')) ∨
      (∃ (_ : 10 ^ 4 ≤ hval θ (ε / 2)) (_ : σ * θ < Lval (ε / 2) * hval θ (ε / 2)),
        SynthClaims (prims (R := R) D en x) 𝒢 Xa L ε'
          (GateSynth.synthBudget hS ε' (sgNativeCircuit k b sb hI.hsb s μ σ t (ε / 2) c0 ar))
          (sysH (R := R) D en x) t (ε / 2) (2 * Qmu s η μ t ε)
          (fun p => 2 * nCallsN p (computeV k b))
          (nGatesN (sgNativeCircuit k b sb hI.hsb s μ σ t (ε / 2) c0 ar))
          (sgNativeCost k sb ar) (ε + ε')) ∨
      (∃ _ : Regime σ θ (ε / 2),
        SynthClaims (prims (R := R) D en x) 𝒢 Xa L ε'
          (GateSynth.synthBudget hS ε' (clNativeCircuit k b sb hI.hsb σ θ (ε / 2) t af aa))
          (sysH (R := R) D en x) t (ε / 2) (2 * Qmu s η μ t ε)
          (fun p => 6 * nCallsN p (computeV k b))
          (nGatesN (clNativeCircuit k b sb hI.hsb σ θ (ε / 2) t af aa))
          (clNativeCost k sb af aa) (ε + ε'))) := by
  obtain ⟨ar, har⟩ := factorWordArith_exists b (c0 / μ) hξ
  obtain ⟨af, aa, haf, haa⟩ := clipArith_exists b μ (hval θ (ε / 2)) (qval σ θ (ε / 2)) c0 hξ hζ
  exact ⟨ar, af, aa, har, haf, haa, fun _ _ hI => gate_optimal_binary_synth hI hP hξ.le hζ hζ1
    hδε (fun _ _ => ar) (fun _ => af) (fun _ => aa) hS hε'⟩

end Endpoint

end

end GateOptimalBinary
