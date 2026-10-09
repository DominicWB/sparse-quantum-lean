import GateEfficientBinary.Cordic.Params
import GateEfficientBinary.Reversible.Rename
import GateEfficientNative.Native.Private

/-!
# The angle arithmetic as a native `Arith`

The CORDIC program is placed on the arithmetic wires of a native private operation: its input
bits are the wires `xw j`, `yw j` of the base register (the two `b`-bit two's complement
components `X`, `Y` of the entry), and its work wires are the arithmetic work wires. The
circuit (`cordicArith`) runs the program, copies the angle words (`φ`: the low `bP` bits of the
stage-1 angle register; `θ`: the clamped stage-2 angle) into the word wires, and runs the
program backwards, which restores all work wires.

`cordicArith_ok` proves the arithmetic hypothesis `ArithOK` of `GateEfficientNative` for the
decoded entry `κ (X + i Y)` (`binDec`), at every accuracy `0 < ζ ≤ 1`. The gates are classical
controlled NOT gates with at most three controls, and `cordicArith_counts` gives the gate and
wire counts: at most `156 w (n + 1) + bP + 2 bT` gates and `1 + 2w + (6 (n+1) + 1) w` work
wires, where `n` is the number of steps per stage and `w` the register width of
`Cordic.params`.
-/

set_option autoImplicit false

namespace SparseHamiltonian.GateBinary

open SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative

noncomputable section

/-! ### Classical gates as elementary gates -/

section Bridge

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- A classical gate as an elementary gate: `X` on the target. -/
def CGate.toGate (g : CGate W) : Gate W := ⟨g.cs, g.t, pauliX⟩

omit [Fintype W] in
theorem cfgRun_map_toGate (gs : List (CGate W)) (x : Cfg W) :
    cfgRun (gs.map CGate.toGate) x = crun gs x := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih => exact ih _

omit [Fintype W] [DecidableEq W] in
theorem classical_map_toGate (gs : List (CGate W)) (h : ∀ g ∈ gs, g.Proper) :
    Classical (gs.map CGate.toGate) := by
  intro g hg
  simp only [List.mem_map] at hg
  obtain ⟨g', hg', rfl⟩ := hg
  exact ⟨rfl, h g' hg'⟩

end Bridge

/-! ### Placing the program -/

open Cordic

variable {B : Type*} [Fintype B] [DecidableEq B]

/-- The number of work wires of the program. -/
abbrev nWork (P : CParams) : ℕ := Fintype.card (CW (RN P.n) P.w)

/-- The arithmetic wires of a private operation for the program. -/
abbrev AW (B : Type*) (P : CParams) := B ⊕ AWr P.bT P.bP (nWork P)

/-- The embedding of the program wires into the arithmetic wires. -/
def embW (P : CParams) (xw yw : Fin P.b → B) : Wr P → AW B P :=
  Sum.elim (fun i => .inl (Sum.elim xw yw i)) (fun c => .inr (.inr (Fintype.equivFin _ c)))

omit [Fintype B] [DecidableEq B] in
theorem embW_injective (P : CParams) {xw yw : Fin P.b → B}
    (hxy : Function.Injective (Sum.elim xw yw)) : Function.Injective (embW P xw yw) := by
  intro u u' h
  rcases u with i | c <;> rcases u' with i' | c' <;> simp only [embW, Sum.elim_inl,
    Sum.elim_inr, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq] at h
  · rw [hxy h]
  · rw [(Fintype.equivFin _).injective h]

/-- The `θ` word wire `j`. -/
def tWire (P : CParams) (j : Fin P.bT) : AW B P := .inr (.inl (.inl j))

/-- The `φ` word wire `j`. -/
def pWire (P : CParams) (j : Fin P.bP) : AW B P := .inr (.inl (.inr j))

/-- The copy gates of one word wire. -/
def cpy (P : CParams) (xw yw : Fin P.b → B) : Fin P.bT ⊕ Fin P.bP → List (CGate (AW B P))
  | .inl j =>
    [⟨[(embW P xw yw (msbW P (.a2 (ix P P.n))), false), (embW P xw yw (msbW P .dc), false)],
        tWire P j⟩,
      ⟨[(embW P xw yw (msbW P (.a2 (ix P P.n))), false), (embW P xw yw (msbW P .dc), true),
        (embW P xw yw (regW (.a2 (ix P P.n)) (P.bT - 1 - j)), true)], tWire P j⟩]
  | .inr j => [⟨[(embW P xw yw (regW (.a1 (ix P P.n)) (P.bP - 1 - j)), true)], pWire P j⟩]

/-- The copy gates: the clamped `θ` word and the `φ` word. -/
def copyG (P : CParams) (xw yw : Fin P.b → B) : List (CGate (AW B P)) :=
  (List.finRange P.bT).flatMap (fun j => cpy P xw yw (.inl j)) ++
    (List.finRange P.bP).flatMap (fun j => cpy P xw yw (.inr j))

/-- The program on the arithmetic wires. -/
def progW (P : CParams) (xw yw : Fin P.b → B) : List (CGate (AW B P)) :=
  (progG (prog P)).map (CGate.map (embW P xw yw))

/-- The arithmetic circuit: program, copy, program backwards. -/
def circW (P : CParams) (xw yw : Fin P.b → B) : List (CGate (AW B P)) :=
  progW P xw yw ++ copyG P xw yw ++ (progW P xw yw).reverse

/-- The two's complement value of a `b`-bit component on the wires `r`. -/
def twos {b : ℕ} (r : Fin b → B) (x : Cfg B) : ℤ :=
  (ofBits (fun j => if h : j < b then x (r ⟨j, h⟩) else false) b).toInt

/-- The decoded entry `κ (X + i Y)` of `b`-bit two's complement components. -/
def binDec {b : ℕ} (xw yw : Fin b → B) (κ : ℝ) (x : Cfg B) : ℂ :=
  (κ : ℂ) * ((twos xw x : ℂ) + (twos yw x : ℂ) * Complex.I)

/-- **The CORDIC arithmetic** for `b`-bit components on the wires `xw`, `yw`, scale `κ` and
accuracy `ζ`. -/
def cordicArith (b : ℕ) (xw yw : Fin b → B) (κ ζ : ℝ) : Arith B where
  bT := (params b κ ζ).bT
  bP := (params b κ ζ).bP
  A := nWork (params b κ ζ)
  circ := (circW (params b κ ζ) xw yw).map CGate.toGate
  tw := fun x => thetaBits (P := params b κ ζ) (x ∘ Sum.elim xw yw)
  pw := fun x => phiBits (P := params b κ ζ) (x ∘ Sum.elim xw yw)

/-! ### Gate properties -/

omit [Fintype B] [DecidableEq B] in
theorem embW_ne_tWire (P : CParams) (xw yw : Fin P.b → B) (u : Wr P) (j : Fin P.bT) :
    embW P xw yw u ≠ tWire P j := by
  rcases u with i | c <;> simp [embW, tWire]

omit [Fintype B] [DecidableEq B] in
theorem embW_ne_pWire (P : CParams) (xw yw : Fin P.b → B) (u : Wr P) (j : Fin P.bP) :
    embW P xw yw u ≠ pWire P j := by
  rcases u with i | c <;> simp [embW, pWire]

omit [Fintype B] in
theorem progG_proper {P : CParams} (hP : P.OK) :
    ∀ g ∈ progG (prog P), g.Proper := by
  intro g hg
  simp only [progG, List.mem_flatMap] at hg
  obtain ⟨o, ho, hg⟩ := hg
  exact ROp.proper_gates o _ (progOK.ok o ho) hP.w0 g hg

omit [Fintype B] [DecidableEq B] in
theorem progW_proper {P : CParams} (hP : P.OK) {xw yw : Fin P.b → B}
    (hxy : Function.Injective (Sum.elim xw yw)) : ∀ g ∈ progW P xw yw, g.Proper := by
  intro g hg
  simp only [progW, List.mem_map] at hg
  obtain ⟨g', hg', rfl⟩ := hg
  exact CGate.proper_map _ (embW_injective P hxy) g' (progG_proper hP g' hg')

omit [Fintype B] [DecidableEq B] in
theorem progW_cs (P : CParams) (xw yw : Fin P.b → B) :
    ∀ g ∈ progW P xw yw, g.cs.length ≤ 2 := by
  intro g hg
  simp only [progW, List.mem_map] at hg
  obtain ⟨g', hg', rfl⟩ := hg
  simp only [progG, List.mem_flatMap] at hg'
  obtain ⟨o, _, hg'⟩ := hg'
  simpa [CGate.map] using ROp.cs_gates o g' hg'

omit [Fintype B] [DecidableEq B] in
theorem cpy_t (P : CParams) (xw yw : Fin P.b → B) (q : Fin P.bT ⊕ Fin P.bP) :
    ∀ g ∈ cpy P xw yw q, g.t = Sum.elim (tWire P) (pWire P) q := by
  intro g hg
  rcases q with j | j <;> simp only [cpy, List.mem_cons, List.not_mem_nil, or_false] at hg <;>
    rcases hg with rfl | rfl <;> rfl

omit [Fintype B] [DecidableEq B] in
theorem cpy_cs (P : CParams) (xw yw : Fin P.b → B) (q : Fin P.bT ⊕ Fin P.bP) :
    ∀ g ∈ cpy P xw yw q, g.cs.length ≤ 3 ∧ ∀ c ∈ g.cs, ∃ u, c.1 = embW P xw yw u := by
  intro g hg
  rcases q with j | j
  · simp only [cpy, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · refine ⟨by simp, fun c hc => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact ⟨_, rfl⟩
      · exact ⟨_, rfl⟩
    · refine ⟨by simp, fun c hc => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact ⟨_, rfl⟩
      · exact ⟨_, rfl⟩
      · exact ⟨_, rfl⟩
  · simp only [cpy, List.mem_cons, List.not_mem_nil, or_false] at hg
    subst hg
    refine ⟨by simp, fun c hc => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    subst hc
    exact ⟨_, rfl⟩

omit [Fintype B] [DecidableEq B] in
theorem copyG_mem (P : CParams) (xw yw : Fin P.b → B) (g : CGate (AW B P))
    (hg : g ∈ copyG P xw yw) : ∃ q, g ∈ cpy P xw yw q := by
  simp only [copyG, List.mem_append, List.mem_flatMap] at hg
  rcases hg with ⟨j, _, hg⟩ | ⟨j, _, hg⟩
  · exact ⟨_, hg⟩
  · exact ⟨_, hg⟩

omit [Fintype B] [DecidableEq B] in
theorem copyG_controls (P : CParams) (xw yw : Fin P.b → B) :
    ∀ g ∈ copyG P xw yw, ∀ c ∈ g.cs, ∀ g' ∈ copyG P xw yw, c.1 ≠ g'.t := by
  intro g hg c hc g' hg'
  obtain ⟨q, hq⟩ := copyG_mem P xw yw g hg
  obtain ⟨q', hq'⟩ := copyG_mem P xw yw g' hg'
  obtain ⟨u, hu⟩ := (cpy_cs P xw yw q g hq).2 c hc
  rw [hu, cpy_t P xw yw q' g' hq']
  rcases q' with j | j
  · exact embW_ne_tWire P xw yw u j
  · exact embW_ne_pWire P xw yw u j

omit [Fintype B] [DecidableEq B] in
theorem copyG_proper (P : CParams) (xw yw : Fin P.b → B) : ∀ g ∈ copyG P xw yw, g.Proper :=
  fun g hg c hc => copyG_controls P xw yw g hg c hc g hg

/-! ### What the circuit computes -/

theorem flatMap_ite_self {α β : Type*} [DecidableEq α] (l : List α) (hl : l.Nodup) (a : α)
    (f : α → List β) :
    l.flatMap (fun b => if b = a then f b else []) = if a ∈ l then f a else [] := by
  induction l with
  | nil => simp
  | cons b l ih =>
      rw [List.flatMap_cons, ih (List.nodup_cons.1 hl).2]
      by_cases hb : b = a
      · subst hb
        simp [(List.nodup_cons.1 hl).1]
      · simp [hb, Ne.symm hb]

omit [Fintype B] in
theorem copyG_filter (P : CParams) (xw yw : Fin P.b → B) (u : AW B P) :
    (copyG P xw yw).filter (fun g => g.t = u) =
      match u with
      | .inr (.inl (.inl j)) => cpy P xw yw (.inl j)
      | .inr (.inl (.inr j)) => cpy P xw yw (.inr j)
      | _ => [] := by
  have hcpy : ∀ q : Fin P.bT ⊕ Fin P.bP, (cpy P xw yw q).filter (fun g => g.t = u) =
      if Sum.elim (tWire P) (pWire P) q = u then cpy P xw yw q else [] := by
    intro q
    split_ifs with hq
    · rw [List.filter_eq_self]
      intro g hg
      rw [cpy_t P xw yw q g hg, hq]
      simp
    · rw [List.filter_eq_nil_iff]
      intro g hg
      rw [cpy_t P xw yw q g hg]
      simpa using hq
  rw [copyG, List.filter_append, List.filter_flatMap, List.filter_flatMap]
  simp only [hcpy]
  rcases u with b | (j | j) | i
  · simp [tWire, pWire]
  · have h1 : (fun a : Fin P.bT => if Sum.elim (tWire P) (pWire P) (Sum.inl a) =
        (Sum.inr (Sum.inl (Sum.inl j)) : AW B P) then cpy P xw yw (.inl a) else []) =
        fun a => if a = j then cpy P xw yw (.inl a) else [] := by
      funext a
      simp [tWire]
    have h2 : (fun a : Fin P.bP => if Sum.elim (tWire P) (pWire P) (Sum.inr a) =
        (Sum.inr (Sum.inl (Sum.inl j)) : AW B P) then cpy P xw yw (.inr a) else []) =
        fun _ => [] := by
      funext a
      simp [pWire]
    rw [h1, h2, flatMap_ite_self _ (List.nodup_finRange _), if_pos (List.mem_finRange j)]
    simp
  · have h1 : (fun a : Fin P.bT => if Sum.elim (tWire P) (pWire P) (Sum.inl a) =
        (Sum.inr (Sum.inl (Sum.inr j)) : AW B P) then cpy P xw yw (.inl a) else []) =
        fun _ => [] := by
      funext a
      simp [tWire]
    have h2 : (fun a : Fin P.bP => if Sum.elim (tWire P) (pWire P) (Sum.inr a) =
        (Sum.inr (Sum.inl (Sum.inr j)) : AW B P) then cpy P xw yw (.inr a) else []) =
        fun a => if a = j then cpy P xw yw (.inr a) else [] := by
      funext a
      simp [pWire]
    rw [h1, h2, flatMap_ite_self _ (List.nodup_finRange _), if_pos (List.mem_finRange j)]
    simp
  · simp [tWire, pWire]

omit [Fintype B] [DecidableEq B] in
theorem init_comp_embW (P : CParams) (xw yw : Fin P.b → B) (x : Cfg B) :
    (Sum.elim x (fun _ => false) : AW B P → Bool) ∘ embW P xw yw =
      cfgOf (x ∘ Sum.elim xw yw) 0 := by
  funext u
  rcases u with i | (_ | i | i | ⟨r, i⟩) <;> simp [embW, cfgOf]

omit [Fintype B] in
theorem progW_run {P : CParams} (hP : P.OK) {xw yw : Fin P.b → B}
    (hxy : Function.Injective (Sum.elim xw yw)) (x : Cfg B) :
    crun (progW P xw yw) (Sum.elim x (fun _ => false)) ∘ embW P xw yw =
      cfgOf (x ∘ Sum.elim xw yw) (regs P (x ∘ Sum.elim xw yw)) := by
  rw [progW, crun_map _ (embW_injective P hxy), init_comp_embW,
    crun_progG (lv P) (prog P) progOK hP.w0 _ 0 (fun _ _ => rfl)]
  rfl

theorem bool_clamp (m d a : Bool) :
    ((!m && !d) ^^ (!m && d && a)) = (!m && (!d || a)) := by
  cases m <;> cases d <;> cases a <;> rfl

omit [Fintype B] in
/-- **The circuit computes the words and restores its work wires.** -/
theorem circW_run {P : CParams} (hP : P.OK) {xw yw : Fin P.b → B}
    (hxy : Function.Injective (Sum.elim xw yw)) (x : Cfg B) :
    crun (circW P xw yw) (Sum.elim x (fun _ => false)) =
      Sum.elim x (Sum.elim (Sum.elim (thetaBits (x ∘ Sum.elim xw yw))
        (phiBits (x ∘ Sum.elim xw yw))) (fun _ => false)) := by
  set E := embW P xw yw with hE
  set v := x ∘ Sum.elim xw yw with hv
  set z0 : AW B P → Bool := Sum.elim x (fun _ => false) with hz0
  set z1 := crun (progW P xw yw) z0 with hz1
  set z2 := crun (copyG P xw yw) z1 with hz2
  have h1 : z1 ∘ E = cfgOf v (regs P v) := progW_run hP hxy x
  have h1' : ∀ u, (∀ a, E a ≠ u) → z1 u = z0 u := fun u hu =>
    crun_map_of_not_mem E _ z0 u hu
  have h2 := crun_xor (copyG P xw yw) (copyG_controls P xw yw) z1
  have h2E : z2 ∘ E = z1 ∘ E := by
    funext a
    simp only [Function.comp, hz2, h2, copyG_filter]
    rcases a with i | c <;> simp [hE, embW, xorAll]
  have hrev : (progW P xw yw).reverse = (progG (prog P)).reverse.map (CGate.map E) := by
    rw [progW, List.map_reverse]
  have h3 : crun (progW P xw yw).reverse z2 ∘ E = z0 ∘ E := by
    rw [hrev, crun_map _ (embW_injective P hxy), h2E, hz1, progW, crun_map _ (embW_injective P hxy),
      crun_reverse _ (progG_proper hP)]
  have h3' : ∀ u, (∀ a, E a ≠ u) → crun (progW P xw yw).reverse z2 u = z2 u := by
    intro u hu
    rw [hrev]
    exact crun_map_of_not_mem E _ z2 u hu
  have hlit : ∀ u : Wr P, z1 (E u) = cfgOf v (regs P v) u := fun u => congrFun h1 u
  rw [circW, crun_append, crun_append, ← hz1, ← hz2]
  funext w'
  rcases w' with b | (j | j) | i
  · by_cases hb : ∃ i, Sum.elim xw yw i = b
    · obtain ⟨i, rfl⟩ := hb
      have := congrFun h3 (Sum.inl i)
      simpa [hE, embW, hz0] using this
    · have hnot : ∀ a, E a ≠ Sum.inl b := by
        intro a ha
        rcases a with i | c
        · exact hb ⟨i, by simpa [hE, embW] using ha⟩
        · simp [hE, embW] at ha
      rw [h3' _ hnot, hz2, h2]
      dsimp only
      rw [copyG_filter]
      simp only [List.map_nil, xorAll, List.foldr_nil, Bool.xor_false]
      rw [h1' _ hnot]
      rfl
  · have hnot : ∀ a, E a ≠ (Sum.inr (Sum.inl (Sum.inl j)) : AW B P) := fun a =>
      embW_ne_tWire P xw yw a j
    rw [h3' _ hnot, hz2, h2]
    dsimp only
    rw [copyG_filter]
    simp only [cpy, List.map_cons, List.map_nil, xorAll, List.foldr_cons, List.foldr_nil,
      Bool.xor_false, lits, List.all_cons, List.all_nil, Bool.and_true]
    rw [h1' _ hnot, hlit, hlit, hlit]
    simp only [msbW, cfg_regW _ _ _ (show P.w - 1 < P.w by have := hP.w0; omega)]
    have hj : P.bT - 1 - j.val < P.w := by
      have := hP.acc2
      have : P.bT < P.w := by
        by_contra hc
        have h5 : 2 ^ (P.w - 1) ≤ 2 ^ P.bT := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      omega
    rw [cfg_regW _ _ _ hj]
    simp only [hz0, Sum.elim_inr, Sum.elim_inl, Bool.false_xor, Sum.elim_inl]
    show _ = tBit v (P.bT - 1 - j)
    unfold tBit
    cases (regs P v (.a2 (ix P P.n))).getLsbD (P.w - 1) <;>
      cases (regs P v .dc).getLsbD (P.w - 1) <;>
      cases (regs P v (.a2 (ix P P.n))).getLsbD (P.bT - 1 - j) <;> rfl
  · have hnot : ∀ a, E a ≠ (Sum.inr (Sum.inl (Sum.inr j)) : AW B P) := fun a =>
      embW_ne_pWire P xw yw a j
    rw [h3' _ hnot, hz2, h2]
    dsimp only
    rw [copyG_filter]
    simp only [cpy, List.map_cons, List.map_nil, xorAll, List.foldr_cons, List.foldr_nil,
      Bool.xor_false, lits, List.all_cons, List.all_nil, Bool.and_true, beq_true]
    rw [h1' _ hnot, hlit, cfg_regW _ _ _ (show P.bP - 1 - j.val < P.w by
      have := hP.bPw; omega)]
    simp only [hz0, Sum.elim_inr, Sum.elim_inl, Bool.false_xor]
    rfl
  · obtain ⟨c, rfl⟩ : ∃ c, Fintype.equivFin (CW (RN P.n) P.w) c = i :=
      ⟨(Fintype.equivFin _).symm i, by simp⟩
    have := congrFun h3 (Sum.inr c)
    simpa [hE, embW, hz0] using this

/-! ### The arithmetic hypothesis -/

omit [Fintype B] [DecidableEq B] in
theorem binDec_eq (b : ℕ) (xw yw : Fin b → B) (κ ζ : ℝ) (x : Cfg B) :
    binDec xw yw κ x = (κ : ℂ) * zIn (P := params b κ ζ) (x ∘ Sum.elim xw yw) := by
  rfl

omit [Fintype B] [DecidableEq B] in
theorem circW_proper {P : CParams} (hP : P.OK) {xw yw : Fin P.b → B}
    (hxy : Function.Injective (Sum.elim xw yw)) : ∀ g ∈ circW P xw yw, g.Proper := by
  intro g hg
  simp only [circW, List.mem_append, List.mem_reverse] at hg
  rcases hg with (hg | hg) | hg
  · exact progW_proper hP hxy g hg
  · exact copyG_proper P xw yw g hg
  · exact progW_proper hP hxy g hg

omit [Fintype B] [DecidableEq B] in
theorem circW_cs (P : CParams) (xw yw : Fin P.b → B) : ∀ g ∈ circW P xw yw, g.cs.length ≤ 3 := by
  intro g hg
  simp only [circW, List.mem_append, List.mem_reverse] at hg
  rcases hg with (hg | hg) | hg
  · exact (progW_cs P xw yw g hg).trans (by norm_num)
  · obtain ⟨q, hq⟩ := copyG_mem P xw yw g hg
    exact (cpy_cs P xw yw q g hq).1
  · exact (progW_cs P xw yw g hg).trans (by norm_num)

omit [Fintype B] in
/-- **The arithmetic hypothesis.** The CORDIC arithmetic satisfies `ArithOK` for the decoded
entry `κ (X + i Y)` at every accuracy `0 < ζ ≤ 1`, provided the input wires are distinct and
avoid the orientation wire `o`. -/
theorem cordicArith_ok (b : ℕ) (hb : 0 < b) (xw yw : Fin b → B)
    (hxy : Function.Injective (Sum.elim xw yw)) (o : B) (ho : ∀ i, Sum.elim xw yw i ≠ o)
    (κ ζ : ℝ) (hκ : 0 < κ) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) :
    ArithOK (cordicArith b xw yw κ ζ) o (binDec xw yw κ) ζ := by
  have hP := params_OK b hb κ ζ hκ
  have hupd : ∀ (x : Cfg B) (c : Bool),
      Function.update x o c ∘ Sum.elim xw yw = x ∘ Sum.elim xw yw := by
    intro x c
    funext i
    simp [Function.update_of_ne (ho i)]
  have hnorm : ∀ x : Cfg B,
      ‖binDec xw yw κ x‖ = κ * ‖zIn (P := params b κ ζ) (x ∘ Sum.elim xw yw)‖ := by
    intro x
    rw [binDec_eq b xw yw κ ζ, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hκ]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g', hg', hgg⟩ := List.mem_map.1 hg
    rw [← hgg]
    exact circW_cs (params b κ ζ) xw yw g' hg'
  · exact classical_map_toGate _ (circW_proper hP hxy)
  · intro x
    have h := cfgRun_map_toGate (circW (params b κ ζ) xw yw) (Sum.elim x (fun _ => false))
    rw [circW_run hP hxy x] at h
    exact h
  · intro x c
    exact congrArg (thetaBits (P := params b κ ζ)) (hupd x c)
  · intro x c
    exact congrArg (phiBits (P := params b κ ζ)) (hupd x c)
  · intro x
    have hU2 : (2 : ℝ) ≤ (params b κ ζ).U := by
      have h := params_U_ge b κ ζ hκ
      have : (2 : ℝ) ≤ 2 ^ ((params b κ ζ).n + 4) :=
        le_self_pow₀ (by norm_num) (by omega)
      linarith
    have h := theta_error hP (x ∘ Sum.elim xw yw) κ hκ (params_c2 b κ ζ) (params_U b κ ζ hκ) hU2
    rw [hnorm]
    exact h.trans (params_theta b κ ζ hκ hζ hζ1)
  · intro x hx
    have hz : zIn (P := params b κ ζ) (x ∘ Sum.elim xw yw) ≠ 0 := by
      intro hz
      apply hx
      rw [binDec_eq b xw yw κ ζ, hz, mul_zero]
    obtain ⟨m, hm⟩ := phi_error hP (x ∘ Sum.elim xw yw) hz (params_c1 b κ ζ)
    refine ⟨m, ?_⟩
    rw [binDec_eq b xw yw κ ζ, Complex.arg_real_mul _ hκ]
    exact hm.trans (params_phi b κ ζ hζ)

/-! ### Counts -/

/-- The register names as a sum type. -/
def RN.equiv (n : ℕ) : RN n ≃ (Fin 6 × Fin (n + 1)) ⊕ Unit where
  toFun
    | .x1 k => .inl (0, k)
    | .y1 k => .inl (1, k)
    | .a1 k => .inl (2, k)
    | .x2 k => .inl (3, k)
    | .y2 k => .inl (4, k)
    | .a2 k => .inl (5, k)
    | .dc => .inr ()
  invFun
    | .inl (0, k) => .x1 k
    | .inl (1, k) => .y1 k
    | .inl (2, k) => .a1 k
    | .inl (3, k) => .x2 k
    | .inl (4, k) => .y2 k
    | .inl (5, k) => .a2 k
    | .inr _ => .dc
  left_inv r := by cases r <;> rfl
  right_inv u := by
    rcases u with ⟨i, k⟩ | u
    · fin_cases i <;> rfl
    · rfl

theorem card_RN (n : ℕ) : Fintype.card (RN n) = 6 * (n + 1) + 1 := by
  rw [Fintype.card_congr (RN.equiv n)]
  simp

omit [Fintype B] [DecidableEq B] in
theorem length_copyG (P : CParams) (xw yw : Fin P.b → B) :
    (copyG P xw yw).length = 2 * P.bT + P.bP := by
  have h1 : ∀ m (f : Fin m → List (CGate (AW B P))) (c : ℕ), (∀ j, (f j).length = c) →
      ((List.finRange m).flatMap f).length = c * m := by
    intro m f c hf
    rw [List.length_flatMap, List.map_congr_left (fun j _ => hf j), List.map_const',
      List.sum_replicate, List.length_finRange, smul_eq_mul, mul_comm]
  rw [copyG, List.length_append, h1 _ _ 2 (fun j => rfl), h1 _ _ 1 (fun j => rfl)]
  ring

/-- The parameter values. -/
theorem params_fields (b : ℕ) (κ ζ : ℝ) :
    (params b κ ζ).n = nOf ζ ∧ (params b κ ζ).bT = wordOf (nOf ζ) ∧
      (params b κ ζ).bP = wordOf (nOf ζ) ∧
      (params b κ ζ).w = 2 * (nOf ζ * nOf ζ) + g2Of (nOf ζ) κ + lkOf κ + b +
        2 * wordOf (nOf ζ) + 8 :=
  ⟨rfl, rfl, rfl, rfl⟩

omit [Fintype B] [DecidableEq B] in
/-- **Counts.** The CORDIC arithmetic has at most `156 w (n + 1) + bP + 2 bT` gates, all with at
most three controls, and `1 + 2w + (6 (n+1) + 1) w` work wires, for the `n` steps per stage,
the register width `w` and the word lengths `bP`, `bT` of `params b κ ζ`. -/
theorem cordicArith_counts (b : ℕ) (xw yw : Fin b → B) (κ ζ : ℝ) :
    (cordicArith b xw yw κ ζ).circ.length ≤
      156 * (params b κ ζ).w * ((params b κ ζ).n + 1) + (params b κ ζ).bP +
        2 * (params b κ ζ).bT ∧
    (cordicArith b xw yw κ ζ).A =
      1 + 2 * (params b κ ζ).w + (6 * ((params b κ ζ).n + 1) + 1) * (params b κ ζ).w ∧
    (cordicArith b xw yw κ ζ).bT = (params b κ ζ).bT ∧
    (cordicArith b xw yw κ ζ).bP = (params b κ ζ).bP := by
  have hw : 0 < (params b κ ζ).w := by
    rw [(params_fields b κ ζ).2.2.2]
    omega
  refine ⟨?_, ?_, rfl, rfl⟩
  · change ((circW (params b κ ζ) xw yw).map CGate.toGate).length ≤ _
    have h := length_progG (prog (params b κ ζ)) hw
    rw [length_prog] at h
    have h2 : (progW (params b κ ζ) xw yw).length = (progG (prog (params b κ ζ))).length :=
      List.length_map _
    rw [List.length_map, circW, List.length_append, List.length_append, List.length_reverse,
      length_copyG, h2]
    nlinarith
  · change Fintype.card (CW (RN (params b κ ζ).n) (params b κ ζ).w) = _
    rw [card_CW, card_RN]
    ring

end

end SparseHamiltonian.GateBinary
