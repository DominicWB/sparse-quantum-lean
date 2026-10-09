import GateEfficientBinary.Reversible.Adder

/-!
# Register programs

A register program acts on base wires `B` (read only) and work wires `CW Rn w`: a constant
zero wire, an operand scratch register `tb`, a carry scratch register `tc`, and named
registers `reg r` of width `w`. A configuration with clean scratch is described by the base
configuration and the register file (`cfgOf`).

One operation (`ROp`) writes `dst := a + (b ^^^ fill s) + s` into a clean register: the
sign bit `s` selects `a + b` or the two's complement difference `a - b`. Its gates prepare
`tb := b ^^^ fill s` and the carry-in `tc 0 := s`, run the adder of `Reversible/Adder`, and
erase the scratch again (`ROp.crun_gates`).

A program is a list of operations in single-assignment form: the destinations have strictly
increasing levels and each operation reads only registers of lower level (`ProgOK`). Its
gates map the clean configuration of a register file to that of the file computed by
`runOps` (`crun_progG`), and the final file satisfies the equation of every operation
(`runOps_dst`).
-/

set_option autoImplicit false

namespace SparseHamiltonian.GateBinary

/-- Work wires of a register program with registers named by `Rn`, each of width `w`: a
constant zero wire, the operand and carry scratch registers, and the named registers. -/
inductive CW (Rn : Type) (w : ℕ) where
  | zero
  | tb (i : Fin w)
  | tc (i : Fin w)
  | reg (r : Rn) (i : Fin w)
  deriving DecidableEq

/-- The work wires as a sum type. -/
def CW.equiv (Rn : Type) (w : ℕ) : CW Rn w ≃ Unit ⊕ Fin w ⊕ Fin w ⊕ (Rn × Fin w) where
  toFun
    | .zero => .inl ()
    | .tb i => .inr (.inl i)
    | .tc i => .inr (.inr (.inl i))
    | .reg r i => .inr (.inr (.inr (r, i)))
  invFun
    | .inl _ => .zero
    | .inr (.inl i) => .tb i
    | .inr (.inr (.inl i)) => .tc i
    | .inr (.inr (.inr (r, i))) => .reg r i
  left_inv u := by cases u <;> rfl
  right_inv u := by rcases u with _ | i | i | ⟨r, i⟩ <;> rfl

instance (Rn : Type) [Fintype Rn] (w : ℕ) : Fintype (CW Rn w) :=
  Fintype.ofEquiv _ (CW.equiv Rn w).symm

theorem card_CW (Rn : Type) [Fintype Rn] (w : ℕ) :
    Fintype.card (CW Rn w) = 1 + w + w + Fintype.card Rn * w := by
  rw [Fintype.card_congr (CW.equiv Rn w)]
  simp only [Fintype.card_sum, Fintype.card_unit, Fintype.card_fin, Fintype.card_prod]
  omega

section Program

variable {B Rn : Type} [DecidableEq B] [DecidableEq Rn] {w : ℕ}

/-- The wire `i` of the operand scratch register (the zero wire beyond the width). -/
def tbW (i : ℕ) : B ⊕ CW Rn w := if h : i < w then .inr (.tb ⟨i, h⟩) else .inr .zero

/-- The wire `i` of the carry scratch register (the zero wire beyond the width). -/
def tcW (i : ℕ) : B ⊕ CW Rn w := if h : i < w then .inr (.tc ⟨i, h⟩) else .inr .zero

/-- The wire `i` of the register `r` (the zero wire beyond the width). -/
def regW (r : Rn) (i : ℕ) : B ⊕ CW Rn w := if h : i < w then .inr (.reg r ⟨i, h⟩) else .inr .zero

omit [DecidableEq B] [DecidableEq Rn] in
theorem tbW_of_lt {i : ℕ} (h : i < w) : (tbW i : B ⊕ CW Rn w) = .inr (.tb ⟨i, h⟩) := dif_pos h

omit [DecidableEq B] [DecidableEq Rn] in
theorem tcW_of_lt {i : ℕ} (h : i < w) : (tcW i : B ⊕ CW Rn w) = .inr (.tc ⟨i, h⟩) := dif_pos h

omit [DecidableEq B] [DecidableEq Rn] in
theorem regW_of_lt (r : Rn) {i : ℕ} (h : i < w) :
    (regW r i : B ⊕ CW Rn w) = .inr (.reg r ⟨i, h⟩) := dif_pos h

/-- The configuration of a register file: base wires `x`, registers `vals`, clean scratch. -/
def cfgOf (x : B → Bool) (vals : Rn → BitVec w) : B ⊕ CW Rn w → Bool
  | .inl b => x b
  | .inr .zero => false
  | .inr (.tb _) => false
  | .inr (.tc _) => false
  | .inr (.reg r i) => (vals r).getLsbD i

omit [DecidableEq B] [DecidableEq Rn] in
theorem readBV_regW (x : B → Bool) (vals : Rn → BitVec w) (r : Rn) :
    readBV (regW r) w (cfgOf x vals) = vals r := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_readBV, regW_of_lt r hi]
  simp [hi, cfgOf]

/-- The wires a program may read: base wires, the zero wire, and the registers in `P`. -/
def Readable (P : Rn → Prop) : B ⊕ CW Rn w → Prop
  | .inl _ => True
  | .inr .zero => True
  | .inr (.tb _) => False
  | .inr (.tc _) => False
  | .inr (.reg r _) => P r

/-- The all-ones or all-zeros bit vector. -/
def fill (w : ℕ) (s : Bool) : BitVec w := if s then BitVec.allOnes w else 0

/-- One register operation `dst := a + (b ^^^ fill s) + s`. -/
structure ROp (B Rn : Type) (w : ℕ) where
  dst : Rn
  a : ℕ → B ⊕ CW Rn w
  b : ℕ → BSrc (B ⊕ CW Rn w)
  s : BSrc (B ⊕ CW Rn w)

/-- The value written by an operation. -/
def ROp.val (o : ROp B Rn w) (y : B ⊕ CW Rn w → Bool) : BitVec w :=
  readBV o.a w y + (ofBits (fun i => (o.b i).val y) w ^^^ fill w (o.s.val y)) +
    (BitVec.ofBool (o.s.val y)).setWidth w

/-- An operation reads only readable wires for `P`, and `P` excludes its destination. -/
structure ROp.OK (o : ROp B Rn w) (P : Rn → Prop) : Prop where
  dst : ¬ P o.dst
  a : ∀ i < w, Readable P (o.a i)
  b : ∀ i < w, (o.b i).On (Readable P)
  s : o.s.On (Readable P)

/-- The scratch preparation `tb := b ^^^ fill s` and `tc 0 := s`. -/
def ROp.prepG (o : ROp B Rn w) : List (CGate (B ⊕ CW Rn w)) :=
  (List.range w).flatMap (fun i => (o.b i).gates (tbW i) ++ o.s.gates (tbW i)) ++
    o.s.gates (tcW 0)

/-- The gates of an operation: preparation, adder, and the preparation again. -/
def ROp.gates (o : ROp B Rn w) : List (CGate (B ⊕ CW Rn w)) :=
  o.prepG ++ adderG o.a tbW tcW (regW o.dst) w ++ o.prepG

omit [DecidableEq B] [DecidableEq Rn] in
theorem readable_ne_tb {P : Rn → Prop} {u : B ⊕ CW Rn w} (hu : Readable P u) (i : Fin w) :
    u ≠ .inr (.tb i) := by
  rintro rfl
  exact hu

omit [DecidableEq B] [DecidableEq Rn] in
theorem readable_ne_tc {P : Rn → Prop} {u : B ⊕ CW Rn w} (hu : Readable P u) (i : Fin w) :
    u ≠ .inr (.tc i) := by
  rintro rfl
  exact hu

omit [DecidableEq B] [DecidableEq Rn] in
theorem readable_ne_reg {P : Rn → Prop} {u : B ⊕ CW Rn w} (hu : Readable P u) {r : Rn}
    (hr : ¬ P r) (i : Fin w) : u ≠ .inr (.reg r i) := by
  rintro rfl
  exact hr hu

omit [DecidableEq B] [DecidableEq Rn] in
theorem BSrc.On.mono {S S' : B ⊕ CW Rn w → Prop} {s : BSrc (B ⊕ CW Rn w)} (hs : s.On S)
    (h : ∀ u, S u → S' u) : s.On S' := by
  cases s with
  | lit u pol => exact h u hs
  | const b => trivial

/-- The scratch-free part of a configuration: everything except the scratch registers. -/
def NotScratch (u : B ⊕ CW Rn w) : Prop :=
  match u with
  | .inr (.tb _) => False
  | .inr (.tc _) => False
  | _ => True

/-- The configuration after the scratch preparation of the first `m` operand bits. -/
def prepCfg (o : ROp B Rn w) (y : B ⊕ CW Rn w → Bool) (m : ℕ) : B ⊕ CW Rn w → Bool
  | .inr (.tb i) => y (.inr (.tb i)) ^^ (decide (i.val < m) && ((o.b i).val y ^^ o.s.val y))
  | u => y u

theorem crun_prep_bits (o : ROp B Rn w) (P : Rn → Prop) (ho : o.OK P)
    (y : B ⊕ CW Rn w → Bool) (m : ℕ) (hm : m ≤ w) :
    crun ((List.range m).flatMap (fun i => (o.b i).gates (tbW i) ++ o.s.gates (tbW i))) y =
      prepCfg o y m := by
  induction m with
  | zero =>
      funext u
      rcases u with b | (_ | i | i | ⟨r, i⟩) <;> simp [prepCfg]
  | succ m ih =>
      rw [List.range_succ, List.flatMap_append, crun_append, ih (by omega)]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rw [crun_append, tbW_of_lt (show m < w by omega)]
      have hbm : (o.b m).On (· ≠ (.inr (.tb ⟨m, by omega⟩) : B ⊕ CW Rn w)) :=
        BSrc.On.mono (ho.b m (by omega)) (fun u hu => readable_ne_tb hu _)
      have hs : o.s.On (· ≠ (.inr (.tb ⟨m, by omega⟩) : B ⊕ CW Rn w)) :=
        BSrc.On.mono ho.s (fun u hu => readable_ne_tb hu _)
      rw [BSrc.crun_gates _ _ hbm, BSrc.crun_gates _ _ hs]
      have hvb : (o.b m).val (prepCfg o y m) = (o.b m).val y := by
        apply BSrc.val_congr _ _ (ho.b m (by omega))
        intro u hu
        rcases u with b | (_ | i | i | ⟨r, i⟩)
        · rfl
        · rfl
        · exact absurd hu id
        · rfl
        · rfl
      have hvs : ∀ z : B ⊕ CW Rn w → Bool, (∀ u, Readable P u → z u = y u) →
          o.s.val z = o.s.val y := fun z hz => BSrc.val_congr _ _ ho.s _ _ hz
      have hagree : ∀ u, Readable P u → prepCfg o y m u = y u := by
        intro u hu
        rcases u with b | (_ | i | i | ⟨r, i⟩)
        · rfl
        · rfl
        · exact absurd hu id
        · rfl
        · rfl
      rw [hvb]
      funext u
      rcases u with b | (_ | i | i | ⟨r, i⟩)
      · simp [prepCfg]
      · simp [prepCfg]
      · by_cases hi : i = ⟨m, by omega⟩
        · subst hi
          have hagree2 : ∀ v u, Readable P u →
              Function.update (prepCfg o y m) (.inr (.tb ⟨m, by omega⟩)) v u = y u := by
            intro v u hu
            rw [Function.update_of_ne (readable_ne_tb hu _)]
            exact hagree u hu
          simp only [Function.update_self, prepCfg]
          rw [hvs _ (hagree2 _)]
          simp only [lt_self_iff_false, decide_false, Bool.false_and, Bool.xor_false,
            Nat.lt_add_one, decide_true, Bool.true_and, Bool.xor_assoc]
        · have hne : (Sum.inr (CW.tb i) : B ⊕ CW Rn w) ≠ .inr (.tb ⟨m, by omega⟩) := by
            intro he
            exact hi (CW.tb.inj (Sum.inr_injective he))
          rw [Function.update_of_ne hne, Function.update_of_ne hne]
          simp only [prepCfg]
          have him : (i.val < m + 1) = (i.val < m) := by
            have : i.val ≠ m := fun h => hi (Fin.ext h)
            apply propext
            omega
          simp only [him]
      · simp [prepCfg]
      · simp [prepCfg]

/-- The scratch preparation on an arbitrary configuration. -/
theorem crun_prepG (o : ROp B Rn w) (P : Rn → Prop) (ho : o.OK P) (hw : 0 < w)
    (y : B ⊕ CW Rn w → Bool) :
    crun o.prepG y = Function.update (prepCfg o y w) (tcW 0) (y (tcW 0) ^^ o.s.val y) := by
  rw [ROp.prepG, crun_append, crun_prep_bits o P ho y w le_rfl, tcW_of_lt hw]
  have hs : o.s.On (· ≠ (.inr (.tc ⟨0, hw⟩) : B ⊕ CW Rn w)) :=
    BSrc.On.mono ho.s (fun u hu => readable_ne_tc hu _)
  rw [BSrc.crun_gates _ _ hs]
  have hv : o.s.val (prepCfg o y w) = o.s.val y := by
    apply BSrc.val_congr _ _ ho.s
    intro u hu
    rcases u with b | (_ | i | i | ⟨r, i⟩)
    · rfl
    · rfl
    · exact absurd hu id
    · rfl
    · rfl
  rw [hv]
  rfl

omit [DecidableEq B] [DecidableEq Rn] in
theorem prepCfg_tb (o : ROp B Rn w) (y : B ⊕ CW Rn w → Bool) (i : Fin w) :
    prepCfg o y w (.inr (.tb i)) = (y (.inr (.tb i)) ^^ ((o.b i).val y ^^ o.s.val y)) := by
  simp [prepCfg]

omit [DecidableEq B] [DecidableEq Rn] in
theorem prepCfg_of_not_tb (o : ROp B Rn w) (y : B ⊕ CW Rn w → Bool) (m : ℕ)
    (u : B ⊕ CW Rn w) (hu : ∀ i, u ≠ .inr (.tb i)) : prepCfg o y m u = y u := by
  rcases u with b | (_ | i | i | ⟨r, i⟩)
  · rfl
  · rfl
  · exact absurd rfl (hu i)
  · rfl
  · rfl

omit [DecidableEq B] in
theorem readable_cfg_update (P : Rn → Prop) (x : B → Bool) (vals : Rn → BitVec w) (r : Rn)
    (hr : ¬ P r) (v : BitVec w) (u : B ⊕ CW Rn w) (hu : Readable P u) :
    cfgOf x (Function.update vals r v) u = cfgOf x vals u := by
  rcases u with b | (_ | i | i | ⟨r', i⟩)
  · rfl
  · rfl
  · exact absurd hu id
  · exact absurd hu id
  · have hr' : r' ≠ r := fun he => hr (he ▸ hu)
    simp [cfgOf, Function.update_of_ne hr']

omit [DecidableEq B] [DecidableEq Rn] in
/-- The adder wiring of an operation. -/
theorem ROp.adderOK (o : ROp B Rn w) (P : Rn → Prop) (ho : o.OK P) :
    AdderOK o.a tbW tcW (regW o.dst) w := by
  have hnot : ∀ u : B ⊕ CW Rn w, Readable P u → ¬ ATgt tcW (regW o.dst) w u := by
    intro u hu ht
    rcases ht with ⟨i, _, hi, he⟩ | ⟨i, hi, he⟩
    · rw [tcW_of_lt hi] at he
      exact readable_ne_tc hu _ he.symm
    · rw [regW_of_lt o.dst hi] at he
      exact readable_ne_reg hu ho.dst _ he.symm
  refine ⟨fun i hi => hnot _ (ho.a i hi), ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi ht
    rcases ht with ⟨j, _, hj, he⟩ | ⟨j, hj, he⟩
    · rw [tcW_of_lt hj, tbW_of_lt hi] at he
      exact absurd he (by simp)
    · rw [regW_of_lt o.dst hj, tbW_of_lt hi] at he
      exact absurd he (by simp)
  · intro ht
    rcases ht with ⟨j, hj1, hj, he⟩ | ⟨j, hj, he⟩
    · rw [tcW_of_lt hj, tcW_of_lt (show 0 < w by omega)] at he
      have := congrArg Fin.val (CW.tc.inj (Sum.inr_injective he))
      simp at this
      omega
    · rw [regW_of_lt o.dst hj, tcW_of_lt (show 0 < w by omega)] at he
      exact absurd he (by simp)
  · intro i j _ hi _ hj he
    rw [tcW_of_lt hi, tcW_of_lt hj] at he
    exact congrArg Fin.val (CW.tc.inj (Sum.inr_injective he))
  · intro i j hi hj he
    rw [regW_of_lt o.dst hi, regW_of_lt o.dst hj] at he
    have := (CW.reg.inj (Sum.inr_injective he)).2
    exact congrArg Fin.val this
  · intro i j _ hi hj he
    rw [tcW_of_lt hi, regW_of_lt o.dst hj] at he
    exact absurd he (by simp)

theorem ofBits_xor_fill (f : ℕ → Bool) (s : Bool) :
    ofBits (fun i => f i ^^ s) w = ofBits f w ^^^ fill w s := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_ofBits, BitVec.getLsbD_xor, getLsbD_ofBits]
  cases s <;> simp [fill, hi]

/-- **One operation.** On the clean configuration of a register file whose destination is
zero, the gates of an operation write its value into the destination register. -/
theorem ROp.crun_gates (o : ROp B Rn w) (P : Rn → Prop) (ho : o.OK P) (hw : 0 < w)
    (x : B → Bool) (vals : Rn → BitVec w) (hd : vals o.dst = 0) :
    crun o.gates (cfgOf x vals) =
      cfgOf x (Function.update vals o.dst (o.val (cfgOf x vals))) := by
  set x0 := cfgOf x vals with hx0
  set sv := o.s.val x0 with hsv
  have htc0 : (tcW 0 : B ⊕ CW Rn w) = .inr (.tc ⟨0, hw⟩) := tcW_of_lt hw
  -- the first preparation
  set y1 := crun o.prepG x0 with hy1
  have hy1e : y1 = Function.update (prepCfg o x0 w) (tcW 0) (x0 (tcW 0) ^^ sv) :=
    crun_prepG o P ho hw x0
  have F1 : ∀ u, (∀ i, u ≠ .inr (.tb i)) → u ≠ tcW 0 → y1 u = x0 u := by
    intro u hu hu0
    rw [hy1e, Function.update_of_ne hu0, prepCfg_of_not_tb _ _ _ _ hu]
  have hy1r : ∀ u, Readable P u → y1 u = x0 u := fun u hu =>
    F1 u (fun i => readable_ne_tb hu i) (by rw [htc0]; exact readable_ne_tc hu _)
  have hy1tb : ∀ i (hi : i < w), y1 (tbW i) = ((o.b i).val x0 ^^ sv) := by
    intro i hi
    rw [hy1e, tbW_of_lt hi, htc0, Function.update_of_ne (by simp), prepCfg_tb,
      show x0 (.inr (.tb ⟨i, hi⟩)) = false from rfl, Bool.false_xor]
  have hy1tc0 : y1 (tcW 0) = sv := by
    rw [hy1e, Function.update_self, htc0, show x0 (.inr (.tc ⟨0, hw⟩)) = false from rfl,
      Bool.false_xor]
  have hy1clean : ∀ u, ATgt tcW (regW o.dst) w u → y1 u = false := by
    intro u hu
    rcases hu with ⟨i, hi1, hi, rfl⟩ | ⟨i, hi, rfl⟩
    · rw [tcW_of_lt hi, F1 _ (fun j => by simp) (by
        rw [htc0]
        intro he
        have := congrArg Fin.val (CW.tc.inj (Sum.inr_injective he))
        simp at this
        omega)]
      rfl
    · rw [regW_of_lt o.dst hi, F1 _ (fun j => by simp) (by rw [htc0]; simp)]
      simp [hx0, cfgOf, hd]
  -- the adder
  obtain ⟨had1, had2⟩ := crun_adderG (o.adderOK P ho) hw y1 hy1clean
  set y2 := crun (adderG o.a tbW tcW (regW o.dst) w) y1 with hy2
  have hsum : readBV o.a w y1 + readBV tbW w y1 + (BitVec.ofBool (y1 (tcW 0))).setWidth w =
      o.val x0 := by
    rw [readBV_congr o.a w y1 x0 (fun i hi => hy1r _ (ho.a i hi)), hy1tc0]
    have htb : readBV tbW w y1 = ofBits (fun i => (o.b i).val x0) w ^^^ fill w sv := by
      rw [← ofBits_xor_fill]
      exact ofBits_congr _ _ w (fun i hi => hy1tb i hi)
    rw [htb]
    rfl
  have F2 : ∀ u, (∀ i, u ≠ .inr (.reg o.dst i)) → y2 u = y1 u := by
    intro u hu
    apply had2
    intro i hi he
    rw [regW_of_lt o.dst hi] at he
    exact hu _ he.symm
  have hy2r : ∀ u, Readable P u → y2 u = x0 u := fun u hu => by
    rw [F2 u (fun i => readable_ne_reg hu ho.dst i), hy1r u hu]
  -- the second preparation
  have hfinal : crun o.prepG y2 =
      Function.update (prepCfg o y2 w) (tcW 0) (y2 (tcW 0) ^^ o.s.val y2) :=
    crun_prepG o P ho hw y2
  have hsv2 : o.s.val y2 = sv := BSrc.val_congr _ _ ho.s _ _ hy2r
  have hbv2 : ∀ i < w, (o.b i).val y2 = (o.b i).val x0 := fun i hi =>
    BSrc.val_congr _ _ (ho.b i hi) _ _ hy2r
  rw [ROp.gates, crun_append, crun_append, ← hy1, ← hy2, hfinal]
  funext u
  rcases u with b | (_ | i | i | ⟨r, i⟩)
  · rw [Function.update_of_ne (by rw [htc0]; simp), prepCfg_of_not_tb _ _ _ _ (by simp),
      hy2r (.inl b) trivial]
    rfl
  · rw [Function.update_of_ne (by rw [htc0]; simp), prepCfg_of_not_tb _ _ _ _ (by simp),
      hy2r (.inr .zero) trivial]
    rfl
  · have h1 := hy1tb i i.2
    rw [tbW_of_lt i.2] at h1
    rw [Function.update_of_ne (by rw [htc0]; simp), prepCfg_tb, hbv2 i i.2, hsv2,
      F2 _ (fun j => by simp), h1]
    simp [cfgOf]
  · by_cases hi0 : i.val = 0
    · have hi : (Sum.inr (CW.tc i) : B ⊕ CW Rn w) = tcW 0 := by
        rw [htc0]
        congr
        exact Fin.ext hi0
      rw [hi, Function.update_self, hsv2, F2 (tcW 0) (fun j => by rw [htc0]; simp), hy1tc0,
        htc0]
      simp [cfgOf]
    · have hne : (Sum.inr (CW.tc i) : B ⊕ CW Rn w) ≠ tcW 0 := by
        rw [htc0]
        intro he
        exact hi0 (congrArg Fin.val (CW.tc.inj (Sum.inr_injective he)))
      rw [Function.update_of_ne hne, prepCfg_of_not_tb _ _ _ _ (by simp),
        F2 _ (fun j => by simp), ← tcW_of_lt i.2,
        hy1clean _ (Or.inl ⟨i, by omega, i.2, rfl⟩), tcW_of_lt i.2]
      rfl
  · rw [Function.update_of_ne (by rw [htc0]; simp), prepCfg_of_not_tb _ _ _ _ (by simp)]
    by_cases hr : r = o.dst
    · subst hr
      have h1 := had1 i i.2
      rw [regW_of_lt o.dst i.2, hsum] at h1
      rw [h1]
      simp [cfgOf]
    · rw [F2 _ (fun j he => hr (CW.reg.inj (Sum.inr_injective he)).1),
        F1 _ (fun j => by simp) (by rw [htc0]; simp)]
      simp [hx0, cfgOf, Function.update_of_ne hr]

omit [DecidableEq B] [DecidableEq Rn] in
/-- The value of an operation depends only on the wires it may read. -/
theorem ROp.val_congr (o : ROp B Rn w) (P : Rn → Prop) (ho : o.OK P)
    (y y' : B ⊕ CW Rn w → Bool) (h : ∀ u, Readable P u → y u = y' u) : o.val y = o.val y' := by
  have hs : o.s.val y = o.s.val y' := BSrc.val_congr _ _ ho.s _ _ h
  unfold ROp.val
  rw [readBV_congr o.a w y y' (fun i hi => h _ (ho.a i hi)), hs,
    ofBits_congr _ (fun i => (o.b i).val y') w
      (fun i hi => BSrc.val_congr _ _ (ho.b i hi) _ _ h)]

/-- Run a list of operations on a register file. -/
def runOps (x : B → Bool) : List (ROp B Rn w) → (Rn → BitVec w) → Rn → BitVec w
  | [], vals => vals
  | o :: os, vals => runOps x os (Function.update vals o.dst (o.val (cfgOf x vals)))

/-- The gates of a program. -/
def progG (ops : List (ROp B Rn w)) : List (CGate (B ⊕ CW Rn w)) := ops.flatMap ROp.gates

/-- Single assignment by levels: the destinations have strictly increasing levels, and each
operation reads only registers of lower level than its destination. -/
structure ProgOK (lv : Rn → ℕ) (ops : List (ROp B Rn w)) : Prop where
  sorted : ops.Pairwise (fun o o' => lv o.dst < lv o'.dst)
  ok : ∀ o ∈ ops, o.OK (fun r => lv r < lv o.dst)

omit [DecidableEq B] [DecidableEq Rn] in
theorem ProgOK.tail {lv : Rn → ℕ} {o : ROp B Rn w} {os : List (ROp B Rn w)}
    (h : ProgOK lv (o :: os)) : ProgOK lv os :=
  ⟨(List.pairwise_cons.1 h.sorted).2, fun o' ho' => h.ok o' (List.mem_cons_of_mem o ho')⟩

omit [DecidableEq B] [DecidableEq Rn] in
theorem ProgOK.head_lt {lv : Rn → ℕ} {o : ROp B Rn w} {os : List (ROp B Rn w)}
    (h : ProgOK lv (o :: os)) : ∀ o' ∈ os, lv o.dst < lv o'.dst :=
  (List.pairwise_cons.1 h.sorted).1

omit [DecidableEq B] in
/-- Registers that no operation writes keep their values. -/
theorem runOps_of_forall_ne (x : B → Bool) (ops : List (ROp B Rn w)) (vals : Rn → BitVec w)
    (r : Rn) (h : ∀ o ∈ ops, o.dst ≠ r) : runOps x ops vals r = vals r := by
  induction ops generalizing vals with
  | nil => rfl
  | cons o os ih =>
      rw [runOps, ih _ (fun o' ho' => h o' (List.mem_cons_of_mem o ho')),
        Function.update_of_ne (h o List.mem_cons_self).symm]

/-- **Programs.** The gates of a single-assignment program map the clean configuration of a
register file with zero destinations to that of the computed register file. -/
theorem crun_progG (lv : Rn → ℕ) (ops : List (ROp B Rn w)) (h : ProgOK lv ops) (hw : 0 < w)
    (x : B → Bool) (vals : Rn → BitVec w) (hv : ∀ o ∈ ops, vals o.dst = 0) :
    crun (progG ops) (cfgOf x vals) = cfgOf x (runOps x ops vals) := by
  induction ops generalizing vals with
  | nil => rfl
  | cons o os ih =>
      rw [progG, List.flatMap_cons, crun_append,
        ROp.crun_gates o _ (h.ok o List.mem_cons_self) hw x vals (hv o List.mem_cons_self)]
      apply ih h.tail
      intro o' ho'
      rw [Function.update_of_ne (fun he => by
        have := h.head_lt o' ho'
        rw [he] at this
        exact lt_irrefl _ this)]
      exact hv o' (List.mem_cons_of_mem o ho')

omit [DecidableEq B] in
/-- **Single assignment.** The final register file satisfies the equation of every
operation of the program. -/
theorem runOps_dst (lv : Rn → ℕ) (ops : List (ROp B Rn w)) (h : ProgOK lv ops) (x : B → Bool)
    (vals : Rn → BitVec w) :
    ∀ o ∈ ops, runOps x ops vals o.dst = o.val (cfgOf x (runOps x ops vals)) := by
  induction ops generalizing vals with
  | nil => intro o ho; exact absurd ho List.not_mem_nil
  | cons o os ih =>
      intro o' ho'
      rcases List.mem_cons.1 ho' with rfl | ho'
      · have hlt := h.head_lt
        have hne : ∀ r, lv r ≤ lv o'.dst → ∀ o'' ∈ os, o''.dst ≠ r := by
          intro r hr o'' ho'' he
          have := hlt o'' ho''
          rw [he] at this
          omega
        rw [runOps, runOps_of_forall_ne x os _ o'.dst (hne _ le_rfl), Function.update_self]
        apply ROp.val_congr o' _ (h.ok o' List.mem_cons_self)
        intro u hu
        rcases u with b | (_ | i | i | ⟨r, i⟩)
        · rfl
        · rfl
        · exact absurd hu id
        · exact absurd hu id
        · have hr : lv r < lv o'.dst := hu
          simp only [cfgOf]
          rw [runOps_of_forall_ne x os _ r (hne r hr.le),
            Function.update_of_ne (fun he => by rw [he] at hr; exact lt_irrefl _ hr)]
      · exact ih h.tail _ o' ho'

omit [DecidableEq B] [DecidableEq Rn] in
/-- The gates of an operation are proper. -/
theorem ROp.proper_gates (o : ROp B Rn w) (P : Rn → Prop) (ho : o.OK P) (hw : 0 < w) :
    ∀ g ∈ o.gates, g.Proper := by
  have hprep : ∀ g ∈ o.prepG, g.Proper := by
    intro g hg
    simp only [ROp.prepG, List.mem_append, List.mem_flatMap, List.mem_range] at hg
    rcases hg with ⟨i, hi, hg | hg⟩ | hg
    · exact BSrc.proper_gates _ _ (BSrc.On.mono (ho.b i hi) (fun u hu => by
        rw [tbW_of_lt hi]; exact readable_ne_tb hu _)) g hg
    · exact BSrc.proper_gates _ _ (BSrc.On.mono ho.s (fun u hu => by
        rw [tbW_of_lt hi]; exact readable_ne_tb hu _)) g hg
    · exact BSrc.proper_gates _ _ (BSrc.On.mono ho.s (fun u hu => by
        rw [tcW_of_lt hw]; exact readable_ne_tc hu _)) g hg
  intro g hg
  simp only [ROp.gates, List.mem_append] at hg
  rcases hg with (hg | hg) | hg
  · exact hprep g hg
  · exact proper_adderG (o.adderOK P ho) hw g hg
  · exact hprep g hg

omit [DecidableEq B] [DecidableEq Rn] in
/-- The gates of an operation have at most two controls. -/
theorem ROp.cs_gates (o : ROp B Rn w) : ∀ g ∈ o.gates, g.cs.length ≤ 2 := by
  have hprep : ∀ g ∈ o.prepG, g.cs.length ≤ 2 := by
    intro g hg
    simp only [ROp.prepG, List.mem_append, List.mem_flatMap, List.mem_range] at hg
    rcases hg with ⟨i, _, hg | hg⟩ | hg <;>
      exact (BSrc.cs_length_gates _ _ g hg).trans (Nat.le_succ 1)
  intro g hg
  simp only [ROp.gates, List.mem_append] at hg
  rcases hg with (hg | hg) | hg
  · exact hprep g hg
  · exact cs_adderG _ _ _ _ _ g hg
  · exact hprep g hg

omit [DecidableEq B] [DecidableEq Rn] in
theorem ROp.length_prepG (o : ROp B Rn w) : o.prepG.length ≤ 2 * w + 1 := by
  have h : ∀ m, ((List.range m).flatMap (fun i => (o.b i).gates (tbW i) ++
      o.s.gates (tbW i))).length ≤ 2 * m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        rw [List.range_succ, List.flatMap_append, List.length_append]
        simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_append]
        have h1 := BSrc.length_gates_le (o.b m) (tbW m)
        have h2 := BSrc.length_gates_le o.s (tbW m)
        omega
  rw [ROp.prepG, List.length_append]
  have h3 := BSrc.length_gates_le o.s (tcW 0)
  have h4 := h w
  omega

omit [DecidableEq B] [DecidableEq Rn] in
/-- An operation has at most `13 w` gates. -/
theorem ROp.length_gates (o : ROp B Rn w) (hw : 0 < w) : o.gates.length ≤ 13 * w := by
  rw [ROp.gates, List.length_append, List.length_append, length_adderG]
  have := o.length_prepG
  omega

omit [DecidableEq B] [DecidableEq Rn] in
/-- The gates of an operation target only scratch wires and its destination register. -/
theorem ROp.target_gates (o : ROp B Rn w) (hw : 0 < w) :
    ∀ g ∈ o.gates, (∃ i, g.t = .inr (.tb i)) ∨ (∃ i, g.t = .inr (.tc i)) ∨
      (∃ i, g.t = .inr (.reg o.dst i)) := by
  have hprep : ∀ g ∈ o.prepG, (∃ i, g.t = .inr (.tb i)) ∨ (∃ i, g.t = .inr (.tc i)) := by
    intro g hg
    simp only [ROp.prepG, List.mem_append, List.mem_flatMap, List.mem_range] at hg
    rcases hg with ⟨i, hi, hg | hg⟩ | hg
    · exact Or.inl ⟨⟨i, hi⟩, by rw [BSrc.t_gates _ _ g hg, tbW_of_lt hi]⟩
    · exact Or.inl ⟨⟨i, hi⟩, by rw [BSrc.t_gates _ _ g hg, tbW_of_lt hi]⟩
    · exact Or.inr ⟨⟨0, hw⟩, by rw [BSrc.t_gates _ _ g hg, tcW_of_lt hw]⟩
  have hadd : ∀ g ∈ adderG o.a tbW tcW (regW o.dst) w,
      (∃ i, g.t = .inr (.tc i)) ∨ (∃ i, g.t = .inr (.reg o.dst i)) := by
    intro g hg
    simp only [adderG, fwdG, sumG, List.mem_append, List.mem_reverse, List.mem_flatMap,
      List.mem_range] at hg
    rcases hg with (⟨i, hi, hg⟩ | ⟨i, hi, hg⟩) | ⟨i, hi, hg⟩
    · simp only [majG, List.mem_cons, List.not_mem_nil, or_false] at hg
      have ht : (tcW (i + 1) : B ⊕ CW Rn w) = .inr (.tc ⟨i + 1, by omega⟩) :=
        tcW_of_lt (by omega)
      rcases hg with rfl | rfl | rfl <;> exact Or.inl ⟨_, ht⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      have ht : (regW o.dst i : B ⊕ CW Rn w) = .inr (.reg o.dst ⟨i, hi⟩) := regW_of_lt _ hi
      rcases hg with rfl | rfl | rfl <;> exact Or.inr ⟨_, ht⟩
    · simp only [majG, List.mem_cons, List.not_mem_nil, or_false] at hg
      have ht : (tcW (i + 1) : B ⊕ CW Rn w) = .inr (.tc ⟨i + 1, by omega⟩) :=
        tcW_of_lt (by omega)
      rcases hg with rfl | rfl | rfl <;> exact Or.inl ⟨_, ht⟩
  intro g hg
  simp only [ROp.gates, List.mem_append] at hg
  rcases hg with (hg | hg) | hg
  · rcases hprep g hg with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · rcases hadd g hg with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · rcases hprep g hg with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

omit [DecidableEq B] [DecidableEq Rn] in
/-- A program has at most `13 w` gates per operation. -/
theorem length_progG (ops : List (ROp B Rn w)) (hw : 0 < w) :
    (progG ops).length ≤ 13 * w * ops.length := by
  induction ops with
  | nil => simp [progG]
  | cons o os ih =>
      rw [progG, List.flatMap_cons, List.length_append]
      have := o.length_gates hw
      change (List.flatMap ROp.gates os).length ≤ _ at ih
      rw [List.length_cons, Nat.mul_succ]
      omega

end Program

end SparseHamiltonian.GateBinary
