import GateEfficientBinaryODETime.Compare
import GateEfficientBinaryODE.Arith

/-!
# The angle arithmetic of the time-dependent private operation

The decoding and the polynomial-cost reversible public arithmetic of Theorem `ode:thm:gates`
for the time-dependent selection of Lemma `ode:lem:gate-select`.

The decoded value of the time-dependent four-sector private operation at the slot word `r` and
the label `(ini, u, w)` is that of the constant-coefficient operation (`GateBinaryODE.decO`)
with the branch duration replaced by the slot mask `[start ≤ r]`. The released register program
(`GateBinaryODE.prog`) computes the duration factor `dv = (ini ? U : 2^kq)` from a source bit
and a node word. Its input wiring `InpT.lift` feeds it, as the source bit, the comparator bit
`ini ∧ r < u` of `Compare` and, as the node word, the zero wire, so that `U = 0` and
`dv = 2^kq [start ≤ r]` (`dv_lift`).

* `circT`: the comparator program, the released arithmetic circuit `GateBinaryODE.circO` (program,
  CORDIC, program backwards) on the base wires and the comparator registers, and the comparator
  backwards; `circT_run`: on clean work wires it writes the angle words of the decoded value and
  restores every work wire.
* `arithT`: the arithmetic as a native `Arith`; `decT`: its decoder;
  `arithT_ok`: the arithmetic hypothesis `ArithOK`, from `GateBinaryODE.odeArith_ok`;
  `arithT_counts`: gates and work wires.
-/

set_option autoImplicit false

namespace SparseHamiltonian.GateBinaryODETime

noncomputable section
open SparseHamiltonian.GateBinary SparseHamiltonian.GateBinary.Cordic
open SparseHamiltonian.GateBinaryODE
open SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
open GatePointerEncoding (wordValue)

/-! ### Input wires -/

/-- The input wires of the time-dependent arithmetic in a base register `B`: the source sector
bit, the slot word and the node word (for the comparator), the LCHS word, the part and the tag
wire, and the two stored entries. -/
structure InpT (B : Type) (L : Lay) (m : ℕ) where
  ini : B
  sl : Fin m → B
  u : Fin m → B
  wd : Fin L.lq → B
  pt : B
  tg : B
  x1 : Fin L.b → B
  y1 : Fin L.b → B
  x2 : Fin L.b → B
  y2 : Fin L.b → B

namespace InpT

variable {B : Type} {L : Lay} {m : ℕ}

/-- **The input wiring of the released program**: the comparator bit as the source bit, the zero
wire as the node word, the other inputs on the base wires. -/
def lift (J : InpT B L m) : Inp (PW B (cLay m)) L where
  ini := msbO .de
  u _ := .inr .zero
  wd j := .inl (J.wd j)
  pt := .inl J.pt
  tg := .inl J.tg
  x1 i := .inl (J.x1 i)
  y1 i := .inl (J.y1 i)
  x2 i := .inl (J.x2 i)
  y2 i := .inl (J.y2 i)

/-- The comparator program of the inputs. -/
def cmp (J : InpT B L m) : List (ROp B (RO (cLay m)) (cLay m).w) := cmpOps J.ini J.sl J.u

/-- The base wires together with the computed comparator registers. -/
def ext (J : InpT B L m) (x : B → Bool) : PW B (cLay m) → Bool :=
  cfgOf x (cregs J.ini J.sl J.u x)

/-- The wire `o` is none of the input wires. -/
structure Avoids (J : InpT B L m) (o : B) : Prop where
  ini : J.ini ≠ o
  sl : ∀ j, J.sl j ≠ o
  u : ∀ j, J.u j ≠ o
  wd : ∀ j, J.wd j ≠ o
  pt : J.pt ≠ o
  tg : J.tg ≠ o
  x1 : ∀ j, J.x1 j ≠ o
  y1 : ∀ j, J.y1 j ≠ o
  x2 : ∀ j, J.x2 j ≠ o
  y2 : ∀ j, J.y2 j ≠ o

theorem lift_avoids (J : InpT B L m) {o : B} (h : J.Avoids o) : J.lift.Avoids (.inl o) where
  ini := by
    simp only [lift, msbO, regW]
    split_ifs <;> simp
  u _ := by simp [lift]
  wd j := by simp [lift, h.wd j]
  pt := by simp [lift, h.pt]
  tg := by simp [lift, h.tg]
  x1 j := by simp [lift, h.x1 j]
  y1 j := by simp [lift, h.y1 j]
  x2 j := by simp [lift, h.x2 j]
  y2 j := by simp [lift, h.y2 j]

end InpT

/-! ### The mask -/

section Mask

variable {B : Type} {L : Lay} {m : ℕ}

/-- The comparator bit read by the released program is `ini ∧ r < u`. -/
theorem ext_ini (J : InpT B L m) (x : B → Bool) :
    J.ext x J.lift.ini =
      (x J.ini && decide (wordValue (fun j => x (J.sl j)) < wordValue (fun j => x (J.u j)))) := by
  change cfgOf x (cregs J.ini J.sl J.u x) (regW .de ((cLay m).w - 1)) = _
  rw [cfgOf_regW x _ _ (by rw [cLay_w]; omega)]
  exact msb_cde J.ini J.sl J.u x

/-- **The duration factor** of the released program on the lifted inputs is
`2^kq [start ≤ r]`, for the start slot `start = (ini ? u : 0)` and the slot `r`. -/
theorem dv_lift (J : InpT B L m) (x : B → Bool) :
    J.lift.dv (J.ext x) = if (if x J.ini then wordValue (fun j => x (J.u j)) else 0) ≤
      wordValue (fun j => x (J.sl j)) then 2 ^ L.kq else 0 := by
  have hU : J.lift.U (J.ext x) = 0 := by
    unfold Inp.U
    have : (fun j => J.ext x (J.lift.u j)) = fun _ => false := by
      funext j
      rfl
    rw [this]
    simp [GatePointerEncoding.wordValue]
  unfold Inp.dv
  rw [ext_ini, hU]
  rcases Bool.eq_false_or_eq_true (x J.ini) with h | h
  · simp only [h, Bool.true_and, decide_eq_true_eq, if_true]
    by_cases hlt : wordValue (fun j => x (J.sl j)) < wordValue (fun j => x (J.u j))
    · simp [hlt, Nat.not_le.2 hlt]
    · simp [hlt, Nat.not_lt.1 hlt]
  · simp [h]

end Mask

/-! ### The circuit -/

section Circuit

variable {B : Type} [DecidableEq B] {L : Lay} {m : ℕ}

/-- The number of comparator work wires. -/
abbrev nCmp (m : ℕ) : ℕ := Fintype.card (CW (RO (cLay m)) (cLay m).w)

/-- The work wires of the time-dependent arithmetic: the comparator wires, then the work wires of
the released arithmetic. -/
def wkT (L : Lay) (m : ℕ) (P : CParams) :
    CW (RO (cLay m)) (cLay m).w ⊕ Fin (nPrep L + nWork P) ≃ Fin (nCmp m + (nPrep L + nWork P)) :=
  (Equiv.sumCongr (Fintype.equivFin _) (Equiv.refl _)).trans finSumFinEquiv

/-- The arithmetic wires of the time-dependent arithmetic. -/
abbrev AWt (L : Lay) (m : ℕ) (P : CParams) := AWr P.bT P.bP (nCmp m + (nPrep L + nWork P))

/-- The comparator wires as arithmetic wires. -/
def eC (L : Lay) (m : ℕ) (P : CParams) : PW B (cLay m) → B ⊕ AWt L m P
  | .inl b => .inl b
  | .inr c => .inr (.inr (wkT L m P (.inl c)))

/-- The wires of the released arithmetic as arithmetic wires. -/
def eO (L : Lay) (m : ℕ) (P : CParams) : PW B (cLay m) ⊕ AWo L P → B ⊕ AWt L m P
  | .inl u => eC L m P u
  | .inr (.inl q) => .inr (.inl q)
  | .inr (.inr i) => .inr (.inr (wkT L m P (.inr i)))

omit [DecidableEq B] in
theorem eC_injective (L : Lay) (m : ℕ) (P : CParams) :
    Function.Injective (eC (B := B) L m P) := by
  intro a a' h
  rcases a with b | c <;> rcases a' with b' | c' <;> simp_all [eC]

omit [DecidableEq B] in
theorem eO_injective (L : Lay) (m : ℕ) (P : CParams) :
    Function.Injective (eO (B := B) L m P) := by
  intro a a' h
  rcases a with (b | c) | (q | i) <;> rcases a' with (b' | c') | (q' | i') <;>
    simp_all [eO, eC]

/-- **The circuit**: the comparator, the released arithmetic on the base wires and the comparator
registers, the comparator backwards. -/
def circT (J : InpT B L m) (κ ζ : ℝ) : List (CGate (B ⊕ AWt L m (params L.w κ ζ))) :=
  (progG J.cmp).map (CGate.map (eC L m (params L.w κ ζ))) ++
    (circO J.lift κ ζ).map (CGate.map (eO L m (params L.w κ ζ))) ++
    ((progG J.cmp).map (CGate.map (eC L m (params L.w κ ζ)))).reverse

omit [DecidableEq B] in
theorem cfgOf_zero_eC (x : B → Bool) (P : CParams) :
    (Sum.elim x (fun _ => false) : B ⊕ AWt L m P → Bool) ∘ eC L m P =
      cfgOf x (0 : RO (cLay m) → BitVec (cLay m).w) := by
  funext u
  rcases u with b | (_ | i | i | ⟨r, i⟩) <;> simp [eC, cfgOf]

omit [DecidableEq B] in
theorem eC_ne_word (P : CParams) (q : Fin P.bT ⊕ Fin P.bP) (a : PW B (cLay m)) :
    eC L m P a ≠ .inr (.inl q) := by
  rcases a with b | c <;> simp [eC]

omit [DecidableEq B] in
theorem eC_ne_work (P : CParams) (j : Fin (nPrep L + nWork P)) (a : PW B (cLay m)) :
    eC L m P a ≠ .inr (.inr (wkT L m P (.inr j))) := by
  rcases a with b | c
  · simp [eC]
  · simp only [eC, ne_eq, Sum.inr.injEq, EmbeddingLike.apply_eq_iff_eq, reduceCtorEq,
      not_false_eq_true]

omit [DecidableEq B] in
theorem cmp_proper (J : InpT B L m) : ∀ g ∈ progG J.cmp, g.Proper := by
  intro g hg
  simp only [progG, List.mem_flatMap] at hg
  obtain ⟨o, ho, hg⟩ := hg
  exact ROp.proper_gates o _ ((cmpOK J.ini J.sl J.u).ok o ho) w_pos g hg

/-- **The circuit computes the angle words of the decoded value and restores its work wires.** -/
theorem circT_run (J : InpT B L m) (hL : L.OK) (κ ζ : ℝ) (hκ : 0 < κ) (x : B → Bool) :
    crun (circT J κ ζ) (Sum.elim x (fun _ => false)) =
      Sum.elim x (Sum.elim (Sum.elim (thetaBits (P := params L.w κ ζ) (inBits J.lift (J.ext x)))
        (phiBits (P := params L.w κ ζ) (inBits J.lift (J.ext x)))) (fun _ => false)) := by
  set P := params L.w κ ζ with hPdef
  set EC := eC (B := B) L m P with hEC
  set EO := eO (B := B) L m P with hEO
  set z0 : B ⊕ AWt L m P → Bool := Sum.elim x (fun _ => false) with hz0
  set z1 := crun ((progG J.cmp).map (CGate.map EC)) z0 with hz1
  set z2 := crun ((circO J.lift κ ζ).map (CGate.map EO)) z1 with hz2
  have h1 : z1 ∘ EC = J.ext x := by
    rw [hz1, crun_map _ (eC_injective L m P), hz0, cfgOf_zero_eC,
      crun_progG (lvO (cLay m)) J.cmp (cmpOK J.ini J.sl J.u) w_pos x 0 (fun _ _ => rfl)]
    rfl
  have h1' : ∀ u, (∀ a, EC a ≠ u) → z1 u = z0 u := fun u hu =>
    crun_map_of_not_mem EC _ z0 u hu
  have h1O : z1 ∘ EO = Sum.elim (J.ext x) (fun _ => false) := by
    funext a
    rcases a with u | (q | j)
    · exact congrFun h1 u
    · show z1 (Sum.inr (Sum.inl q)) = false
      rw [h1' _ (fun a => eC_ne_word P q a)]
      rfl
    · show z1 (Sum.inr (Sum.inr (wkT L m P (Sum.inr j)))) = false
      rw [h1' _ (fun a => eC_ne_work P j a)]
      rfl
  have h2 : z2 ∘ EO = Sum.elim (J.ext x) (Sum.elim (Sum.elim
      (thetaBits (P := P) (inBits J.lift (J.ext x))) (phiBits (P := P) (inBits J.lift (J.ext x))))
        (fun _ => false)) := by
    rw [hz2, crun_map _ (eO_injective L m P), h1O, circO_run J.lift hL κ ζ hκ]
  have h2C : z2 ∘ EC = crun (progG J.cmp) (cfgOf x 0) := by
    rw [crun_progG (lvO (cLay m)) J.cmp (cmpOK J.ini J.sl J.u) w_pos x 0 (fun _ _ => rfl)]
    funext u
    exact congrFun h2 (Sum.inl u)
  have hrev : ((progG J.cmp).map (CGate.map EC)).reverse =
      (progG J.cmp).reverse.map (CGate.map EC) := by
    rw [List.map_reverse]
  have h3 : crun ((progG J.cmp).map (CGate.map EC)).reverse z2 ∘ EC = cfgOf x 0 := by
    rw [hrev, crun_map _ (eC_injective L m P), h2C, crun_reverse _ (cmp_proper J)]
  have h3' : ∀ u, (∀ a, EC a ≠ u) →
      crun ((progG J.cmp).map (CGate.map EC)).reverse z2 u = z2 u := by
    intro u hu
    rw [hrev]
    exact crun_map_of_not_mem EC _ z2 u hu
  rw [circT, crun_append, crun_append, ← hz1, ← hz2]
  funext w'
  rcases w' with b | (q | i)
  · have := congrFun h3 (Sum.inl b)
    simpa [hEC, eC, cfgOf] using this
  · rw [h3' _ (fun a => eC_ne_word P q a)]
    have h2q := congrFun h2 (Sum.inr (Sum.inl q))
    simp only [Function.comp_apply, Sum.elim_inr, Sum.elim_inl] at h2q
    simp only [Sum.elim_inr, Sum.elim_inl]
    exact h2q
  · obtain ⟨u, rfl⟩ := (wkT L m P).surjective i
    rcases u with c | j
    · have := congrFun h3 (Sum.inr c)
      simp only [Function.comp_apply, hEC, eC] at this
      rw [this]
      rcases c with _ | i | i | ⟨r, i⟩ <;> simp [cfgOf]
    · rw [h3' _ (fun a => eC_ne_work P j a)]
      have h2j := congrFun h2 (Sum.inr (Sum.inr j))
      simp only [Function.comp_apply, Sum.elim_inr] at h2j
      simp only [Sum.elim_inr]
      exact h2j

end Circuit

/-! ### The arithmetic and its hypothesis -/

section OK

variable {B : Type} [DecidableEq B] {L : Lay} {m : ℕ}

/-- **The angle arithmetic** of the time-dependent private operation, with CORDIC scale `κ` and
CORDIC accuracy `ζ`. -/
def arithT (J : InpT B L m) (κ ζ : ℝ) : Arith B where
  bT := (params L.w κ ζ).bT
  bP := (params L.w κ ζ).bP
  A := nCmp m + (nPrep L + nWork (params L.w κ ζ))
  circ := (circT J κ ζ).map CGate.toGate
  tw := fun x => thetaBits (P := params L.w κ ζ) (inBits J.lift (J.ext x))
  pw := fun x => phiBits (P := params L.w κ ζ) (inBits J.lift (J.ext x))

/-- **The decoder** of the time-dependent private operation: `decO` of the released program on the
lifted inputs. -/
def decT (J : InpT B L m) (κ ρ : ℝ) (x : B → Bool) : ℂ := decO J.lift κ ρ (J.ext x)

theorem cregs_update (J : InpT B L m) {o : B} (h : J.Avoids o) (x : B → Bool) (v : Bool) :
    cregs J.ini J.sl J.u (Function.update x o v) = cregs J.ini J.sl J.u x := by
  funext r
  by_cases hdu : r = .du
  · subst hdu
    rw [v_cdu, v_cdu, word_update _ x o v h.sl, word_update _ x o v h.u]
  · by_cases hde : r = .de
    · subst hde
      rw [v_cde, v_cde, word_update _ x o v h.sl, word_update _ x o v h.u,
        Function.update_of_ne h.ini]
    · have hne : ∀ op ∈ cmpOps J.ini J.sl J.u, op.dst ≠ r := by
        intro op hop
        simp only [cmpOps, List.mem_cons, List.not_mem_nil, or_false] at hop
        rcases hop with rfl | rfl
        · exact Ne.symm hdu
        · exact Ne.symm hde
      unfold cregs
      rw [runOps_of_forall_ne _ _ _ r hne, runOps_of_forall_ne _ _ _ r hne]

theorem ext_update (J : InpT B L m) {o : B} (h : J.Avoids o) (x : B → Bool) (v : Bool) :
    J.ext (Function.update x o v) = Function.update (J.ext x) (.inl o) v := by
  unfold InpT.ext
  rw [cregs_update J h x v]
  funext u
  rcases u with b | c
  · by_cases hb : b = o
    · subst hb
      simp [cfgOf]
    · rw [Function.update_of_ne (fun h' => hb (Sum.inl_injective h'))]
      simp [cfgOf, Function.update_of_ne hb]
  · rw [Function.update_of_ne (fun h' => by cases h')]
    rcases c with _ | i | i | ⟨r, i⟩ <;> rfl

/-- The decoder does not read the wire `o` when no input wire is `o`. -/
theorem decT_update (J : InpT B L m) {o : B} (h : J.Avoids o) (κ ρ : ℝ) (x : B → Bool)
    (v : Bool) : decT J κ ρ (Function.update x o v) = decT J κ ρ x := by
  have ho := J.lift_avoids h
  unfold decT decO
  rw [ext_update J h x v, Inp.zx_update _ _ ho v, Inp.zy_update _ _ ho v,
    Function.update_of_ne ho.pt]

omit [DecidableEq B] in
theorem circT_cs (J : InpT B L m) (κ ζ : ℝ) : ∀ g ∈ circT J κ ζ, g.cs.length ≤ 3 := by
  have hp : ∀ g ∈ (progG J.cmp).map (CGate.map (eC (B := B) L m (params L.w κ ζ))),
      g.cs.length ≤ 3 := by
    intro g hg
    simp only [List.mem_map] at hg
    obtain ⟨g', hg', rfl⟩ := hg
    simp only [progG, List.mem_flatMap] at hg'
    obtain ⟨o, _, hg'⟩ := hg'
    have := ROp.cs_gates o g' hg'
    simp only [CGate.map, List.length_map]
    omega
  intro g hg
  simp only [circT, List.mem_append, List.mem_reverse] at hg
  rcases hg with (hg | hg) | hg
  · exact hp g hg
  · simp only [List.mem_map] at hg
    obtain ⟨g', hg', rfl⟩ := hg
    simp only [CGate.map, List.length_map]
    exact circO_cs _ _ _ g' hg'
  · exact hp g hg

omit [DecidableEq B] in
theorem circT_proper (J : InpT B L m) (κ ζ : ℝ) (hκ : 0 < κ) :
    ∀ g ∈ circT J κ ζ, g.Proper := by
  have hp : ∀ g ∈ (progG J.cmp).map (CGate.map (eC (B := B) L m (params L.w κ ζ))),
      g.Proper := by
    intro g hg
    simp only [List.mem_map] at hg
    obtain ⟨g', hg', rfl⟩ := hg
    exact CGate.proper_map _ (eC_injective L m _) g' (cmp_proper J g' hg')
  intro g hg
  simp only [circT, List.mem_append, List.mem_reverse] at hg
  rcases hg with (hg | hg) | hg
  · exact hp g hg
  · simp only [List.mem_map] at hg
    obtain ⟨g', hg', rfl⟩ := hg
    exact CGate.proper_map _ (eO_injective L m _) g' (circO_proper _ κ ζ hκ g' hg')
  · exact hp g hg

/-- **The arithmetic hypothesis.** Under the layout bounds, for `κ > 0`, a CORDIC accuracy
`0 < ζc ≤ 1` and a factor `ρ` with `|ρ - 1| ≤ 1/2` and `ζc + 2 |ρ - 1| ≤ ζ`, the arithmetic
satisfies `ArithOK` at accuracy `ζ` for the decoder `decT`, provided the wire `o` is not an
input wire. -/
theorem arithT_ok (J : InpT B L m) (hL : L.OK) (o : B) (ho : J.Avoids o) (κ ρ ζc ζ : ℝ)
    (hκ : 0 < κ) (hζc : 0 < ζc) (hζc1 : ζc ≤ 1) (hρ : |ρ - 1| ≤ 1 / 2)
    (hζ : ζc + 2 * |ρ - 1| ≤ ζ) : ArithOK (arithT J κ ζc) o (decT J κ ρ) ζ := by
  have hO := odeArith_ok J.lift hL (.inl o) (J.lift_avoids ho) κ ρ ζc ζ hκ hζc hζc1 hρ hζ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
    exact circT_cs J κ ζc g' hg'
  · exact classical_map_toGate _ (circT_proper J κ ζc hκ)
  · intro x
    have h := cfgRun_map_toGate (circT J κ ζc) (Sum.elim x (fun _ => false))
    rw [circT_run J hL κ ζc hκ x] at h
    exact h
  · intro x v
    change thetaBits (P := params L.w κ ζc) (inBits J.lift (J.ext (Function.update x o v))) =
      thetaBits (P := params L.w κ ζc) (inBits J.lift (J.ext x))
    rw [ext_update J ho x v, inBits_update J.lift (J.lift_avoids ho)]
  · intro x v
    change phiBits (P := params L.w κ ζc) (inBits J.lift (J.ext (Function.update x o v))) =
      phiBits (P := params L.w κ ζc) (inBits J.lift (J.ext x))
    rw [ext_update J ho x v, inBits_update J.lift (J.lift_avoids ho)]
  · intro x
    exact hO.theta (J.ext x)
  · intro x hx
    exact hO.phi (J.ext x) hx

/-! ### Counts -/

omit [DecidableEq B] in
/-- **Counts.** Besides the gates and work wires of the released arithmetic
(`GateBinaryODE.odeArith_counts`), the arithmetic has at most `52 (m + 14)` comparator gates
(`26 (m + 14)` in each direction) and the `1 + 2 (m + 14) + 62 (m + 14)` work wires of the
comparator registers. -/
theorem arithT_counts (J : InpT B L m) (κ ζ : ℝ) :
    (arithT J κ ζ).circ.length ≤ 52 * (m + 14) + (odeArith J.lift κ ζ).circ.length ∧
    (arithT J κ ζ).A = (1 + 2 * (m + 14) + (31 + 2 + 3 + 6 + 2 * 10) * (m + 14)) +
      (odeArith J.lift κ ζ).A ∧
    (arithT J κ ζ).bT = (odeArith J.lift κ ζ).bT ∧
    (arithT J κ ζ).bP = (odeArith J.lift κ ζ).bP := by
  refine ⟨?_, ?_, rfl, rfl⟩
  · have hp := length_progG J.cmp (w_pos (L := cLay m))
    have hl : J.cmp.length = 2 := rfl
    have hw := cLay_w m
    rw [hl] at hp
    change ((circT J κ ζ).map CGate.toGate).length ≤
      52 * (m + 14) + ((circO J.lift κ ζ).map CGate.toGate).length
    simp only [List.length_map, circT, List.length_append, List.length_reverse]
    omega
  · change nCmp m + (nPrep L + nWork (params L.w κ ζ)) = _ + (nPrep L + nWork (params L.w κ ζ))
    rw [nCmp, card_CW, card_RO, cLay_w]
    simp only [cLay, Lay.mA, Lay.mS]
    ring

end OK

end

end SparseHamiltonian.GateBinaryODETime
