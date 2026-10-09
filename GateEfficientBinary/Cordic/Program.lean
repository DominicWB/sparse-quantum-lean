import GateEfficientBinary.Reversible.TwosComp
import GateEfficientBinary.Cordic.Integer

/-!
# The CORDIC register program

The angle arithmetic is a single-assignment register program (`Reversible/Program`) on the
input bits of the two components `X`, `Y` of an entry and work registers of width `w`.

* Stage 1 computes `arg (X + i Y)`. The initial vector is `±(X, Y) 2^T`, negated when `X < 0`,
  and the angle register starts at `π` (the bit `bP - 1`) in that case. Each of the `n` steps
  `k` adds `σ ⌊y / 2^k⌋` to `x`, subtracts `σ ⌊x / 2^k⌋` from `y` and adds `σ c₁ k` to the angle,
  where `σ` is the sign of `y`; the angle register counts in units of `2π / 2^bP`.
* Stage 2 computes `arctan (κ |X + i Y|)` from the stage-1 output `x_n ≈ g_n 2^T |X + i Y|`: its
  initial vector is `(U 2^T, x_n 2^S₂)` with a public integer `U`, and its angle register counts
  in units of `π / 2^(bT+1)`, so that it holds half of the angle `θ` in the units of the
  `bT`-bit word `θ`.
* The last register holds the stage-2 angle minus `2^bT`; with the sign bits of both registers
  the output word is clamped to `[0, 2^bT)`.

Registers are written once, in the order of their levels (`lv`), and each operation reads only
registers of lower levels (`progOK`). The two's complement values of the registers satisfy the
integer CORDIC recurrences up to reduction modulo `2^w` (`x_succ`, `y_succ`, `a_succ` and the
initial values).
-/

set_option autoImplicit false

namespace SparseHamiltonian.GateBinary.Cordic

/-- Register names: the `x`, `y` and angle registers of both stages after each step, and the
difference register of the clamp. -/
inductive RN (n : ℕ) where
  | x1 (k : Fin (n + 1))
  | y1 (k : Fin (n + 1))
  | a1 (k : Fin (n + 1))
  | x2 (k : Fin (n + 1))
  | y2 (k : Fin (n + 1))
  | a2 (k : Fin (n + 1))
  | dc
  deriving DecidableEq, Fintype

/-- Public parameters of the CORDIC program: steps per stage `n`, input bits `b`, register
width `w`, exactness scale `T`, word lengths `bP` and `bT`, the stage-2 constant `U` and shift
`S2`, and the angle constants of both stages. -/
structure CParams where
  n : ℕ
  b : ℕ
  w : ℕ
  T : ℕ
  bP : ℕ
  bT : ℕ
  U : ℕ
  S2 : ℕ
  c1 : ℕ → ℕ
  c2 : ℕ → ℕ

variable (P : CParams)

/-- The wires of the program: the input bits of both components and the work wires. -/
abbrev Wr := (Fin P.b ⊕ Fin P.b) ⊕ CW (RN P.n) P.w

/-- The step index `k`, clamped to `n`. -/
def ix (k : ℕ) : Fin (P.n + 1) := ⟨min k P.n, by omega⟩

/-- Levels: the order in which the registers are written. -/
def lv : RN P.n → ℕ
  | .x1 k => 3 * k.val
  | .y1 k => 3 * k.val + 1
  | .a1 k => 3 * k.val + 2
  | .x2 k => 3 * (P.n + 1) + 3 * k.val
  | .y2 k => 3 * (P.n + 1) + 3 * k.val + 1
  | .a2 k => 3 * (P.n + 1) + 3 * k.val + 2
  | .dc => 6 * (P.n + 1)

/-- The constant zero wire. -/
def zW : Wr P := .inr .zero

/-- Bit `j` of an input component (`false`: `X`, `true`: `Y`); the zero wire beyond. -/
def inW (side : Bool) (j : ℕ) : Wr P :=
  if h : j < P.b then .inl (if side then .inr ⟨j, h⟩ else .inl ⟨j, h⟩) else .inr .zero

/-- The register `r` shifted right arithmetically by `k`. -/
def shrS (r : RN P.n) (k : ℕ) : ℕ → BSrc (Wr P) :=
  fun i => .lit (regW r (min (i + k) (P.w - 1))) true

/-- The register `r` shifted left by `s`. -/
def shlS (r : RN P.n) (s : ℕ) : ℕ → BSrc (Wr P) :=
  fun i => if i < s then .const false else .lit (regW r (i - s)) true

/-- An input component, sign-extended and shifted left by `t`. -/
def inpS (side : Bool) (t : ℕ) : ℕ → BSrc (Wr P) :=
  fun i => if i < t then .const false else .lit (inW P side (min (i - t) (P.b - 1))) true

/-- A constant. -/
def cstS (c : ℕ) : ℕ → BSrc (Wr P) := fun i => .const ((BitVec.ofNat P.w c).getLsbD i)

/-- The sign bit of the input component `X`. -/
def signX : BSrc (Wr P) := .lit (inW P false (P.b - 1)) true

/-- The sign bit of a register. -/
def msbW (r : RN P.n) : Wr P := regW r (P.w - 1)

/-- Stage-1 initialisation: `x := ±X 2^T`, `y := ±Y 2^T`, angle `:= π` if `X < 0`. -/
def init1 : List (ROp (Fin P.b ⊕ Fin P.b) (RN P.n) P.w) :=
  [⟨.x1 (ix P 0), fun _ => zW P, inpS P false P.T, signX P⟩,
   ⟨.y1 (ix P 0), fun _ => zW P, inpS P true P.T, signX P⟩,
   ⟨.a1 (ix P 0), fun _ => zW P,
     fun i => if i = P.bP - 1 then signX P else .const false, .const false⟩]

/-- One CORDIC step `k` on the registers `xr`, `yr`, `ar` with angle constants `c`. -/
def iterOps (xr yr ar : Fin (P.n + 1) → RN P.n) (c : ℕ → ℕ) (k : ℕ) :
    List (ROp (Fin P.b ⊕ Fin P.b) (RN P.n) P.w) :=
  [⟨xr (ix P (k + 1)), regW (xr (ix P k)), shrS P (yr (ix P k)) k,
     .lit (msbW P (yr (ix P k))) true⟩,
   ⟨yr (ix P (k + 1)), regW (yr (ix P k)), shrS P (xr (ix P k)) k,
     .lit (msbW P (yr (ix P k))) false⟩,
   ⟨ar (ix P (k + 1)), regW (ar (ix P k)), cstS P (c k), .lit (msbW P (yr (ix P k))) true⟩]

/-- Stage-2 initialisation: `x := U 2^T`, `y := x₁ 2^S₂`; the angle register stays zero. -/
def init2 : List (ROp (Fin P.b ⊕ Fin P.b) (RN P.n) P.w) :=
  [⟨.x2 (ix P 0), fun _ => zW P, cstS P (P.U * 2 ^ P.T), .const false⟩,
   ⟨.y2 (ix P 0), fun _ => zW P, shlS P (.x1 (ix P P.n)) P.S2, .const false⟩]

/-- The clamp difference: the stage-2 angle minus `2^bT`. -/
def clampOp : ROp (Fin P.b ⊕ Fin P.b) (RN P.n) P.w :=
  ⟨.dc, regW (.a2 (ix P P.n)), cstS P (2 ^ P.bT), .const true⟩

/-- **The CORDIC program.** -/
def prog : List (ROp (Fin P.b ⊕ Fin P.b) (RN P.n) P.w) :=
  init1 P ++ (List.range P.n).flatMap (iterOps P RN.x1 RN.y1 RN.a1 P.c1) ++ init2 P ++
    (List.range P.n).flatMap (iterOps P RN.x2 RN.y2 RN.a2 P.c2) ++ [clampOp P]

theorem length_prog : (prog P).length = 6 * P.n + 6 := by
  have h : ∀ (xr yr ar : Fin (P.n + 1) → RN P.n) (c : ℕ → ℕ) (m : ℕ),
      ((List.range m).flatMap (iterOps P xr yr ar c)).length = 3 * m := by
    intro xr yr ar c m
    induction m with
    | zero => simp
    | succ m ih =>
        rw [List.range_succ, List.flatMap_append, List.length_append, ih]
        simp [iterOps]
        omega
  simp only [prog, List.length_append, h, init1, init2, List.length_cons, List.length_nil]
  omega

/-! ### Single assignment -/

variable {P}

theorem ix_val {k : ℕ} (hk : k ≤ P.n) : (ix P k).val = k := by
  simp [ix, Nat.min_eq_left hk]

theorem readable_regW {Q : RN P.n → Prop} {r : RN P.n} (h : Q r) (i : ℕ) :
    Readable Q (regW r i : Wr P) := by
  unfold regW
  split_ifs
  · exact h
  · trivial

theorem readable_inW (Q : RN P.n → Prop) (side : Bool) (j : ℕ) : Readable Q (inW P side j) := by
  unfold inW
  split_ifs <;> trivial

theorem readable_zW (Q : RN P.n → Prop) : Readable Q (zW P) := trivial

/-- The level pattern of the registers of one stage. -/
structure StageLv (L : ℕ) (xr yr ar : Fin (P.n + 1) → RN P.n) : Prop where
  x : ∀ j, lv P (xr j) = L + 3 * j.val
  y : ∀ j, lv P (yr j) = L + 3 * j.val + 1
  a : ∀ j, lv P (ar j) = L + 3 * j.val + 2

theorem stageLv1 : StageLv (P := P) 0 RN.x1 RN.y1 RN.a1 :=
  ⟨fun j => by simp [lv], fun j => by simp [lv], fun j => by simp [lv]⟩

theorem stageLv2 : StageLv (P := P) (3 * (P.n + 1)) RN.x2 RN.y2 RN.a2 :=
  ⟨fun j => by simp [lv], fun j => by simp [lv], fun j => by simp [lv]⟩

theorem iterOps_levels {L : ℕ} {xr yr ar : Fin (P.n + 1) → RN P.n} (h : StageLv L xr yr ar)
    (c : ℕ → ℕ) {k : ℕ} (hk : k < P.n) :
    ∀ o ∈ iterOps P xr yr ar c k,
      L + 3 * (k + 1) ≤ lv P o.dst ∧ lv P o.dst ≤ L + 3 * (k + 1) + 2 := by
  intro o ho
  simp only [iterOps, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl
  · rw [h.x, ix_val (by omega)]
    omega
  · rw [h.y, ix_val (by omega)]
    omega
  · rw [h.a, ix_val (by omega)]
    omega

theorem iterOps_pairwise {L : ℕ} {xr yr ar : Fin (P.n + 1) → RN P.n} (h : StageLv L xr yr ar)
    (c : ℕ → ℕ) {k : ℕ} (hk : k < P.n) :
    (iterOps P xr yr ar c k).Pairwise (fun o o' => lv P o.dst < lv P o'.dst) := by
  simp only [iterOps, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true, IsEmpty.forall_iff,
    implies_true]
  rw [h.x, h.y, h.a, ix_val (by omega)]
  omega

theorem iterOps_ok {L : ℕ} {xr yr ar : Fin (P.n + 1) → RN P.n} (h : StageLv L xr yr ar)
    (c : ℕ → ℕ) {k : ℕ} (hk : k < P.n) :
    ∀ o ∈ iterOps P xr yr ar c k, o.OK (fun r => lv P r < lv P o.dst) := by
  have hx : lv P (xr (ix P k)) = L + 3 * k := by rw [h.x, ix_val (by omega)]
  have hy : lv P (yr (ix P k)) = L + 3 * k + 1 := by rw [h.y, ix_val (by omega)]
  have ha : lv P (ar (ix P k)) = L + 3 * k + 2 := by rw [h.a, ix_val (by omega)]
  have hx' : lv P (xr (ix P (k + 1))) = L + 3 * (k + 1) := by rw [h.x, ix_val (by omega)]
  have hy' : lv P (yr (ix P (k + 1))) = L + 3 * (k + 1) + 1 := by rw [h.y, ix_val (by omega)]
  have ha' : lv P (ar (ix P (k + 1))) = L + 3 * (k + 1) + 2 := by rw [h.a, ix_val (by omega)]
  intro o ho
  simp only [iterOps, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl
  · refine ⟨lt_irrefl _, fun i _ => readable_regW (by simp only; omega) i,
      fun i _ => readable_regW (by simp only; omega) _, readable_regW (by simp only; omega) _⟩
  · refine ⟨lt_irrefl _, fun i _ => readable_regW (by simp only; omega) i,
      fun i _ => readable_regW (by simp only; omega) _, readable_regW (by simp only; omega) _⟩
  · refine ⟨lt_irrefl _, fun i _ => readable_regW (by simp only; omega) i,
      fun i _ => trivial, readable_regW (by simp only; omega) _⟩

theorem stage_levels {L : ℕ} {xr yr ar : Fin (P.n + 1) → RN P.n} (h : StageLv L xr yr ar)
    (c : ℕ → ℕ) : ∀ o ∈ (List.range P.n).flatMap (iterOps P xr yr ar c),
      L + 3 ≤ lv P o.dst ∧ lv P o.dst ≤ L + 3 * P.n + 2 := by
  intro o ho
  simp only [List.mem_flatMap, List.mem_range] at ho
  obtain ⟨k, hk, ho⟩ := ho
  have := iterOps_levels h c hk o ho
  constructor <;> omega

theorem stage_pairwise {L : ℕ} {xr yr ar : Fin (P.n + 1) → RN P.n} (h : StageLv L xr yr ar)
    (c : ℕ → ℕ) : ((List.range P.n).flatMap (iterOps P xr yr ar c)).Pairwise
      (fun o o' => lv P o.dst < lv P o'.dst) := by
  rw [List.pairwise_flatMap]
  refine ⟨fun k hk => iterOps_pairwise h c (List.mem_range.1 hk), ?_⟩
  refine List.Pairwise.imp_of_mem ?_ List.pairwise_lt_range
  intro k k' hk hk' hkk' o ho o' ho'
  have h1 := iterOps_levels h c (List.mem_range.1 hk) o ho
  have h2 := iterOps_levels h c (List.mem_range.1 hk') o' ho'
  omega

theorem stage_ok {L : ℕ} {xr yr ar : Fin (P.n + 1) → RN P.n} (h : StageLv L xr yr ar)
    (c : ℕ → ℕ) : ∀ o ∈ (List.range P.n).flatMap (iterOps P xr yr ar c),
      o.OK (fun r => lv P r < lv P o.dst) := by
  intro o ho
  simp only [List.mem_flatMap, List.mem_range] at ho
  obtain ⟨k, hk, ho⟩ := ho
  exact iterOps_ok h c hk o ho

theorem init1_levels : ∀ o ∈ init1 P, lv P o.dst ≤ 2 := by
  intro o ho
  simp only [init1, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl <;> simp [lv, ix]

theorem init2_levels : ∀ o ∈ init2 P,
    3 * (P.n + 1) ≤ lv P o.dst ∧ lv P o.dst ≤ 3 * (P.n + 1) + 1 := by
  intro o ho
  simp only [init2, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl <;> simp [lv, ix]

theorem readable_inpS (Q : RN P.n → Prop) (side : Bool) (t i : ℕ) :
    (inpS P side t i).On (Readable Q) := by
  unfold inpS
  split_ifs
  · trivial
  · exact readable_inW Q side _

theorem readable_signX (Q : RN P.n → Prop) : (signX P).On (Readable Q) :=
  readable_inW Q false _

/-- **The CORDIC program is a single-assignment program.** -/
theorem progOK : ProgOK (lv P) (prog P) := by
  have h1 := stage_levels (P := P) stageLv1 P.c1
  have h2 := stage_levels (P := P) stageLv2 P.c2
  have hi1 := init1_levels (P := P)
  have hi2 := init2_levels (P := P)
  refine ⟨?_, ?_⟩
  · simp only [prog, List.pairwise_append]
    refine ⟨⟨⟨⟨?_, stage_pairwise stageLv1 P.c1, ?_⟩, ?_, ?_⟩, stage_pairwise stageLv2 P.c2,
      ?_⟩, List.pairwise_singleton _ _, ?_⟩
    · simp [init1, lv, ix]
    · intro o ho o' ho'
      have := hi1 o ho
      have := h1 o' ho'
      omega
    · simp [init2, lv, ix]
    · intro o ho o' ho'
      rcases List.mem_append.1 ho with ho | ho
      · have := hi1 o ho
        have := hi2 o' ho'
        omega
      · have := h1 o ho
        have := hi2 o' ho'
        omega
    · intro o ho o' ho'
      rcases List.mem_append.1 ho with ho | ho
      · rcases List.mem_append.1 ho with ho | ho
        · have := hi1 o ho
          have := h2 o' ho'
          omega
        · have := h1 o ho
          have := h2 o' ho'
          omega
      · have := hi2 o ho
        have := h2 o' ho'
        omega
    · intro o ho o' ho'
      simp only [List.mem_singleton] at ho'
      subst ho'
      show lv P o.dst < 6 * (P.n + 1)
      rcases List.mem_append.1 ho with ho | ho
      · rcases List.mem_append.1 ho with ho | ho
        · rcases List.mem_append.1 ho with ho | ho
          · have := hi1 o ho
            omega
          · have := h1 o ho
            omega
        · have := hi2 o ho
          omega
      · have := h2 o ho
        omega
  · intro o ho
    simp only [prog, List.mem_append, List.mem_singleton] at ho
    rcases ho with (((ho | ho) | ho) | ho) | rfl
    · simp only [init1, List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl
      · exact ⟨lt_irrefl _, fun i _ => readable_zW _, fun i _ => readable_inpS _ _ _ _,
          readable_signX _⟩
      · exact ⟨lt_irrefl _, fun i _ => readable_zW _, fun i _ => readable_inpS _ _ _ _,
          readable_signX _⟩
      · refine ⟨lt_irrefl _, fun i _ => readable_zW _, fun i _ => ?_, trivial⟩
        simp only
        split_ifs
        · exact readable_signX _
        · trivial
    · exact stage_ok stageLv1 P.c1 o ho
    · simp only [init2, List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl
      · exact ⟨lt_irrefl _, fun i _ => readable_zW _, fun i _ => trivial, trivial⟩
      · refine ⟨lt_irrefl _, fun i _ => readable_zW _, fun i _ => ?_, trivial⟩
        simp only [shlS]
        split_ifs
        · trivial
        · exact readable_regW (by simp [lv, ix]) _
    · exact stage_ok stageLv2 P.c2 o ho
    · exact ⟨lt_irrefl _, fun i _ => readable_regW (by simp [lv, ix, clampOp]; omega) _,
        fun i _ => trivial, trivial⟩

/-! ### Register values -/

variable (P)

/-- The input component `X` (`side = false`) or `Y` (`side = true`) of the input bits `v`. -/
def inBV (v : Fin P.b ⊕ Fin P.b → Bool) (side : Bool) : BitVec P.b :=
  ofBits (fun j => if h : j < P.b then v (if side then .inr ⟨j, h⟩ else .inl ⟨j, h⟩) else false)
    P.b

/-- The final register file of the program on the input bits `v`. -/
def regs (v : Fin P.b ⊕ Fin P.b → Bool) : RN P.n → BitVec P.w := runOps v (prog P) 0

variable {P}

theorem regs_dst (v : Fin P.b ⊕ Fin P.b → Bool) :
    ∀ o ∈ prog P, regs P v o.dst = o.val (cfgOf v (regs P v)) :=
  runOps_dst (lv P) (prog P) progOK v 0

theorem cfg_inW (v : Fin P.b ⊕ Fin P.b → Bool) (F : RN P.n → BitVec P.w) (side : Bool)
    {j : ℕ} (hj : j < P.b) : cfgOf v F (inW P side j) = (inBV P v side).getLsbD j := by
  rw [inBV, getLsbD_ofBits]
  simp only [inW, hj, dif_pos, decide_true, Bool.true_and]
  cases side <;> rfl

theorem cfg_regW (v : Fin P.b ⊕ Fin P.b → Bool) (F : RN P.n → BitVec P.w) (r : RN P.n)
    {i : ℕ} (hi : i < P.w) : cfgOf v F (regW r i) = (F r).getLsbD i := by
  rw [regW_of_lt r hi]
  rfl

theorem readBV_zW (v : Fin P.b ⊕ Fin P.b → Bool) (F : RN P.n → BitVec P.w) :
    readBV (fun _ => zW P) P.w (cfgOf v F) = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_readBV]
  simp [zW, cfgOf]

theorem ofBits_cstS (v : Fin P.b ⊕ Fin P.b → Bool) (F : RN P.n → BitVec P.w) (c : ℕ) :
    ofBits (fun i => (cstS P c i).val (cfgOf v F)) P.w = BitVec.ofNat P.w c := by
  simp only [cstS, BSrc.val]
  exact ofBits_getLsbD _

theorem msb_val (hw : 0 < P.w) (v : Fin P.b ⊕ Fin P.b → Bool) (F : RN P.n → BitVec P.w)
    (r : RN P.n) (pol : Bool) :
    (BSrc.lit (msbW P r) pol).val (cfgOf v F) = (decide ((F r).toInt < 0) == pol) := by
  simp only [BSrc.val, msbW]
  rw [cfg_regW v F r (by omega), getLsbD_last_eq _ hw]

theorem ofBits_shrS (hw : 0 < P.w) (v : Fin P.b ⊕ Fin P.b → Bool) (F : RN P.n → BitVec P.w)
    (r : RN P.n) (k : ℕ) :
    (ofBits (fun i => (shrS P r k i).val (cfgOf v F)) P.w).toInt = (F r).toInt / 2 ^ k := by
  rw [← toInt_ofBits_shiftRight (F r) k hw]
  congr 1
  apply ofBits_congr
  intro i _
  simp only [shrS, BSrc.val, beq_true]
  exact cfg_regW v F r (by omega)

/-- The `x` register of a CORDIC step. -/
theorem val_iter_x (hw : 0 < P.w) (v : Fin P.b ⊕ Fin P.b → Bool) (F : RN P.n → BitVec P.w)
    (xr yr : Fin (P.n + 1) → RN P.n) (k : ℕ) :
    (ROp.val (⟨xr (ix P (k + 1)), regW (xr (ix P k)), shrS P (yr (ix P k)) k,
      .lit (msbW P (yr (ix P k))) true⟩ : ROp (Fin P.b ⊕ Fin P.b) (RN P.n) P.w)
      (cfgOf v F)).toInt =
    (cstep k ((F (xr (ix P k))).toInt, (F (yr (ix P k))).toInt)).1.bmod (2 ^ P.w) := by
  rw [ROp.val, readBV_regW, msb_val hw, toInt_add_xor_fill, ofBits_shrS hw]
  by_cases h : (F (yr (ix P k))).toInt < 0 <;> simp [cstep, isgn, h]

/-- The `y` register of a CORDIC step. -/
theorem val_iter_y (hw : 0 < P.w) (v : Fin P.b ⊕ Fin P.b → Bool) (F : RN P.n → BitVec P.w)
    (xr yr : Fin (P.n + 1) → RN P.n) (k : ℕ) :
    (ROp.val (⟨yr (ix P (k + 1)), regW (yr (ix P k)), shrS P (xr (ix P k)) k,
      .lit (msbW P (yr (ix P k))) false⟩ : ROp (Fin P.b ⊕ Fin P.b) (RN P.n) P.w)
      (cfgOf v F)).toInt =
    (cstep k ((F (xr (ix P k))).toInt, (F (yr (ix P k))).toInt)).2.bmod (2 ^ P.w) := by
  rw [ROp.val, readBV_regW, msb_val hw, toInt_add_xor_fill, ofBits_shrS hw]
  by_cases h : (F (yr (ix P k))).toInt < 0 <;> simp [cstep, isgn, h, sub_eq_add_neg]

/-- The angle register of a CORDIC step. -/
theorem val_iter_a (hw : 0 < P.w) (v : Fin P.b ⊕ Fin P.b → Bool) (F : RN P.n → BitVec P.w)
    (xr yr ar : Fin (P.n + 1) → RN P.n) (c : ℕ → ℕ) (k : ℕ) (hc : c k < 2 ^ (P.w - 1)) :
    (ROp.val (⟨ar (ix P (k + 1)), regW (ar (ix P k)), cstS P (c k),
      .lit (msbW P (yr (ix P k))) true⟩ : ROp (Fin P.b ⊕ Fin P.b) (RN P.n) P.w)
      (cfgOf v F)).toInt =
    ((F (ar (ix P k))).toInt +
      isgn ((F (xr (ix P k))).toInt, (F (yr (ix P k))).toInt) * c k).bmod (2 ^ P.w) := by
  rw [ROp.val, readBV_regW, msb_val hw, toInt_add_xor_fill, ofBits_cstS,
    toInt_ofNat_of_lt _ hc]
  by_cases h : (F (yr (ix P k))).toInt < 0 <;> simp [isgn, h]

theorem abs_toInt_le (X : BitVec P.b) : |X.toInt| ≤ 2 ^ (P.b - 1) := by
  have h1 := BitVec.toInt_lt (x := X)
  have h2 := BitVec.le_toInt X
  rw [abs_le]
  constructor <;> omega

theorem ofBits_inpS (hb : 0 < P.b) (v : Fin P.b ⊕ Fin P.b → Bool) (F : RN P.n → BitVec P.w)
    (side : Bool) (t : ℕ) :
    ofBits (fun i => (inpS P side t i).val (cfgOf v F)) P.w =
      ofBits (fun i => if i < t then false else (inBV P v side).getLsbD (min (i - t) (P.b - 1)))
        P.w := by
  apply ofBits_congr
  intro i _
  simp only [inpS]
  split_ifs
  · rfl
  · simp only [BSrc.val, beq_true]
    exact cfg_inW v F side (by omega)

theorem signX_val (hb : 0 < P.b) (v : Fin P.b ⊕ Fin P.b → Bool) (F : RN P.n → BitVec P.w) :
    (signX P).val (cfgOf v F) = decide ((inBV P v false).toInt < 0) := by
  simp only [signX, BSrc.val, beq_true]
  rw [cfg_inW v F false (by omega), getLsbD_last_eq _ hb]

/-- The initial stage-1 `x` register: `|X| 2^T`. -/
theorem val_x1_init (hw : 0 < P.w) (hb : 0 < P.b) (hbw : P.b + P.T + 1 ≤ P.w)
    (v : Fin P.b ⊕ Fin P.b → Bool) (F : RN P.n → BitVec P.w) :
    (ROp.val (⟨.x1 (ix P 0), fun _ => zW P, inpS P false P.T, signX P⟩ :
      ROp (Fin P.b ⊕ Fin P.b) (RN P.n) P.w) (cfgOf v F)).toInt =
    |(inBV P v false).toInt| * 2 ^ P.T := by
  have h0 : (0 : BitVec P.w).toInt = 0 := by simp
  rw [ROp.val, readBV_zW, signX_val hb, toInt_add_xor_fill, ofBits_inpS hb,
    toInt_ofBits_extend _ hb _ (by omega), h0, zero_add]
  have hX := abs_toInt_le (inBV P v false)
  have hpow : (2 : ℤ) ^ (P.b - 1) * 2 ^ P.T < 2 ^ (P.w - 1) := by
    rw [← pow_add]
    exact pow_lt_pow_right₀ (by norm_num) (by omega)
  by_cases h : (inBV P v false).toInt < 0
  · simp only [h, decide_true, if_true]
    rw [bmod_two_pow_eq_self hw, abs_of_neg h, neg_mul]
    rw [abs_neg, abs_mul, abs_of_pos (by positivity : (0 : ℤ) < 2 ^ P.T)]
    calc |(inBV P v false).toInt| * 2 ^ P.T ≤ 2 ^ (P.b - 1) * 2 ^ P.T :=
          mul_le_mul_of_nonneg_right hX (by positivity)
      _ < 2 ^ (P.w - 1) := hpow
  · simp only [h, decide_false]
    rw [if_neg (by simp), bmod_two_pow_eq_self hw, abs_of_nonneg (not_lt.1 h)]
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℤ) < 2 ^ P.T)]
    calc |(inBV P v false).toInt| * 2 ^ P.T ≤ 2 ^ (P.b - 1) * 2 ^ P.T :=
          mul_le_mul_of_nonneg_right hX (by positivity)
      _ < 2 ^ (P.w - 1) := hpow

/-- The initial stage-1 `y` register: `±Y 2^T`, negated when `X < 0`. -/
theorem val_y1_init (hw : 0 < P.w) (hb : 0 < P.b) (hbw : P.b + P.T + 1 ≤ P.w)
    (v : Fin P.b ⊕ Fin P.b → Bool) (F : RN P.n → BitVec P.w) :
    (ROp.val (⟨.y1 (ix P 0), fun _ => zW P, inpS P true P.T, signX P⟩ :
      ROp (Fin P.b ⊕ Fin P.b) (RN P.n) P.w) (cfgOf v F)).toInt =
    (if (inBV P v false).toInt < 0 then -(inBV P v true).toInt else (inBV P v true).toInt) *
      2 ^ P.T := by
  have h0 : (0 : BitVec P.w).toInt = 0 := by simp
  rw [ROp.val, readBV_zW, signX_val hb, toInt_add_xor_fill, ofBits_inpS hb,
    toInt_ofBits_extend _ hb _ (by omega), h0, zero_add]
  have hY := abs_toInt_le (inBV P v true)
  have hpow : (2 : ℤ) ^ (P.b - 1) * 2 ^ P.T < 2 ^ (P.w - 1) := by
    rw [← pow_add]
    exact pow_lt_pow_right₀ (by norm_num) (by omega)
  have hb2 : |(inBV P v true).toInt * 2 ^ P.T| < 2 ^ (P.w - 1) := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℤ) < 2 ^ P.T)]
    calc |(inBV P v true).toInt| * 2 ^ P.T ≤ 2 ^ (P.b - 1) * 2 ^ P.T :=
          mul_le_mul_of_nonneg_right hY (by positivity)
      _ < 2 ^ (P.w - 1) := hpow
  by_cases h : (inBV P v false).toInt < 0
  · simp only [h, decide_true, if_true]
    rw [bmod_two_pow_eq_self hw (by rwa [abs_neg]), neg_mul]
  · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]
    rw [bmod_two_pow_eq_self hw hb2]

theorem val_of_const_false (o : ROp (Fin P.b ⊕ Fin P.b) (RN P.n) P.w) (ho : o.s = .const false)
    (y : Wr P → Bool) : o.val y = readBV o.a P.w y + ofBits (fun i => (o.b i).val y) P.w := by
  have h1 : fill P.w false = 0 := rfl
  rw [ROp.val, ho]
  simp [BSrc.val, h1]

theorem bv_zero_add (x : BitVec P.w) : 0 + x = x := by simp

/-- The initial stage-1 angle register: `2^(bP-1)` (the angle `π`) when `X < 0`. -/
theorem val_a1_init (hb : 0 < P.b) (hbP : 0 < P.bP) (hbw : P.bP ≤ P.w)
    (v : Fin P.b ⊕ Fin P.b → Bool) (F : RN P.n → BitVec P.w) :
    (ROp.val (⟨.a1 (ix P 0), fun _ => zW P,
      fun i => if i = P.bP - 1 then signX P else .const false, .const false⟩ :
      ROp (Fin P.b ⊕ Fin P.b) (RN P.n) P.w) (cfgOf v F)).toNat =
    if (inBV P v false).toInt < 0 then 2 ^ (P.bP - 1) else 0 := by
  rw [val_of_const_false _ rfl, readBV_zW, bv_zero_add]
  have h : ofBits (fun i => ((if i = P.bP - 1 then signX P else .const false : BSrc (Wr P))).val
      (cfgOf v F)) P.w = ofBits (fun i => if i = P.bP - 1 then
        decide ((inBV P v false).toInt < 0) else false) P.w := by
    apply ofBits_congr
    intro i _
    split_ifs
    · exact signX_val hb v F
    · rfl
  rw [h, toNat_ofBits_single _ (by omega)]
  simp

/-- The initial stage-2 `x` register: `U 2^T`. -/
theorem val_x2_init (hU : P.U * 2 ^ P.T < 2 ^ (P.w - 1)) (v : Fin P.b ⊕ Fin P.b → Bool)
    (F : RN P.n → BitVec P.w) :
    (ROp.val (⟨.x2 (ix P 0), fun _ => zW P, cstS P (P.U * 2 ^ P.T), .const false⟩ :
      ROp (Fin P.b ⊕ Fin P.b) (RN P.n) P.w) (cfgOf v F)).toInt = P.U * 2 ^ P.T := by
  rw [val_of_const_false _ rfl, readBV_zW, bv_zero_add, ofBits_cstS,
    toInt_ofNat_of_lt _ hU]
  push_cast
  ring

/-- The initial stage-2 `y` register: the stage-1 output `x` shifted left by `S₂`. -/
theorem val_y2_init (v : Fin P.b ⊕ Fin P.b → Bool) (F : RN P.n → BitVec P.w)
    (h0 : 0 ≤ (F (.x1 (ix P P.n))).toInt)
    (h : (F (.x1 (ix P P.n))).toInt * 2 ^ P.S2 < 2 ^ (P.w - 1)) :
    (ROp.val (⟨.y2 (ix P 0), fun _ => zW P, shlS P (.x1 (ix P P.n)) P.S2, .const false⟩ :
      ROp (Fin P.b ⊕ Fin P.b) (RN P.n) P.w) (cfgOf v F)).toInt =
    (F (.x1 (ix P P.n))).toInt * 2 ^ P.S2 := by
  rw [val_of_const_false _ rfl, readBV_zW, bv_zero_add, ← toInt_ofBits_shiftLeft _ _ h0 h]
  congr 1
  apply ofBits_congr
  intro i hi
  simp only [shlS]
  split_ifs
  · rfl
  · simp only [BSrc.val, beq_true]
    exact cfg_regW v F _ (by omega)

/-- The clamp register: the stage-2 angle minus `2^bT`. -/
theorem val_dc (hT : 2 ^ P.bT < 2 ^ (P.w - 1)) (v : Fin P.b ⊕ Fin P.b → Bool)
    (F : RN P.n → BitVec P.w) :
    (ROp.val (clampOp P) (cfgOf v F)).toInt =
      ((F (.a2 (ix P P.n))).toInt - 2 ^ P.bT).bmod (2 ^ P.w) := by
  have hs : (BSrc.const true : BSrc (Wr P)).val (cfgOf v F) = true := rfl
  rw [clampOp, ROp.val, readBV_regW, hs, toInt_add_xor_fill, ofBits_cstS,
    toInt_ofNat_of_lt _ (by exact_mod_cast hT)]
  simp [sub_eq_add_neg]

end SparseHamiltonian.GateBinary.Cordic
