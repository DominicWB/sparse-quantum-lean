import GateEfficientBinaryODE.ProgramVal

/-!
# The angle arithmetic of the four-sector private operation

The reversible arithmetic of the native private operation (`odeArith`) runs the pre-processing
program of `Program` on its own work wires, the CORDIC circuit of `GateEfficientBinary` on the
two output registers (the two's complement words of `zx` and `zy`, `inBits`), and the
pre-processing program backwards. It writes the angle words of CORDIC for the Gaussian integer
`Z' = zx + i zy` and restores all work wires (`circO_run`).

`odeArith_ok`: under the layout bounds `Lay.OK`, for a decoder `κ ρ_x Z'` with `κ > 0` and a
positive factor `ρ_x` that is `1` except on the dissipative part, where it is a fixed `ρ` with
`|ρ - 1| ≤ 1/2`, the arithmetic satisfies the arithmetic hypothesis `ArithOK` at accuracy `ζ`
whenever the CORDIC accuracy `0 < ζc ≤ 1` satisfies `ζc + 2 |ρ - 1| ≤ ζ`: the `φ` word is
unaffected by the positive factor, and the factor moves `2 arctan |·|` by at most `2 |ρ - 1|`
(`Cordic.abs_arctan_sub_le`).

`odeArith_counts`: the gate and wire counts.
-/

set_option autoImplicit false

namespace SparseHamiltonian.GateBinaryODE

noncomputable section
open SparseHamiltonian.GateBinary SparseHamiltonian.GateBinary.Cordic
open SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
open GatePointerEncoding (wordValue)

/-! ### Avoiding a wire -/

section Avoid

variable {B : Type} [DecidableEq B] {L : Lay}

/-- The wire `o` is none of the input wires of the program. -/
structure Inp.Avoids (I : Inp B L) (o : B) : Prop where
  ini : I.ini ≠ o
  u : ∀ j, I.u j ≠ o
  wd : ∀ j, I.wd j ≠ o
  pt : I.pt ≠ o
  tg : I.tg ≠ o
  x1 : ∀ j, I.x1 j ≠ o
  y1 : ∀ j, I.y1 j ≠ o
  x2 : ∀ j, I.x2 j ≠ o
  y2 : ∀ j, I.y2 j ≠ o

theorem twos_update' {m : ℕ} (r : Fin m → B) (x : B → Bool) (o : B) (v : Bool)
    (h : ∀ j, r j ≠ o) : twos r (Function.update x o v) = twos r x := by
  unfold twos
  congr 2
  funext j
  split_ifs
  · exact Function.update_of_ne (h _) _ _
  · rfl

theorem word_update {m : ℕ} (r : Fin m → B) (x : B → Bool) (o : B) (v : Bool)
    (h : ∀ j, r j ≠ o) :
    wordValue (fun j => Function.update x o v (r j)) = wordValue (fun j => x (r j)) := by
  congr 1
  funext j
  exact Function.update_of_ne (h j) _ _

namespace Inp

variable (I : Inp B L) (x : B → Bool) {o : B}

theorem zx_update (h : I.Avoids o) (v : Bool) : I.zx (Function.update x o v) = I.zx x := by
  simp only [zx, ct, dv, mu, nv, ax, X1, X2, Y1, Y2, U, V,
    twos_update' _ x o v h.x1, twos_update' _ x o v h.x2, twos_update' _ x o v h.y1,
    twos_update' _ x o v h.y2, word_update _ x o v h.u, word_update _ x o v h.wd,
    Function.update_of_ne h.ini, Function.update_of_ne h.pt]

theorem zy_update (h : I.Avoids o) (v : Bool) : I.zy (Function.update x o v) = I.zy x := by
  simp only [zy, ct, dv, mu, nv, ay, X1, X2, Y1, Y2, U, V,
    twos_update' _ x o v h.x1, twos_update' _ x o v h.x2, twos_update' _ x o v h.y1,
    twos_update' _ x o v h.y2, word_update _ x o v h.u, word_update _ x o v h.wd,
    Function.update_of_ne h.ini, Function.update_of_ne h.pt, Function.update_of_ne h.tg]

end Inp

end Avoid

/-! ### The circuit -/

section Circuit

variable {B : Type} [DecidableEq B] {L : Lay}

/-- The real output register as CORDIC input wires. -/
def xwO (L : Lay) : Fin L.w → PW B L := fun j => .inr (.reg (.xc (Fin.last _)) j)

/-- The imaginary output register as CORDIC input wires. -/
def ywO (L : Lay) : Fin L.w → PW B L := fun j => .inr (.reg (.yc (Fin.last _)) j)

omit [DecidableEq B] in
theorem xy_injective (L : Lay) : Function.Injective (Sum.elim (xwO (B := B) L) (ywO L)) := by
  rintro (i | i) (j | j) h <;> simp_all [xwO, ywO]

/-- The input bits of CORDIC: the two's complement words of `zx` and `zy`. -/
def inBits (I : Inp B L) (x : B → Bool) : Fin L.w ⊕ Fin L.w → Bool :=
  Sum.elim (fun j => (BitVec.ofInt L.w (I.zx x)).getLsbD j)
    (fun j => (BitVec.ofInt L.w (I.zy x)).getLsbD j)

/-- The number of work wires of the pre-processing program. -/
abbrev nPrep (L : Lay) : ℕ := Fintype.card (CW (RO L) L.w)

/-- The arithmetic wires of the composite arithmetic. -/
abbrev AWo (L : Lay) (P : CParams) := AWr P.bT P.bP (nPrep L + nWork P)

/-- The work wires of the composite arithmetic: the program work wires, then the CORDIC work
wires. -/
def wkE (L : Lay) (P : CParams) : CW (RO L) L.w ⊕ Fin (nWork P) ≃ Fin (nPrep L + nWork P) :=
  (Equiv.sumCongr (Fintype.equivFin _) (Equiv.refl _)).trans finSumFinEquiv

/-- The wires of the program and of CORDIC as arithmetic wires: the base wires, the program
work wires, the angle words and the CORDIC work wires. -/
def embA (L : Lay) (P : CParams) : AW (PW B L) P → B ⊕ AWo L P
  | .inl (.inl b) => .inl b
  | .inl (.inr c) => .inr (.inr (wkE L P (.inl c)))
  | .inr (.inl q) => .inr (.inl q)
  | .inr (.inr i) => .inr (.inr (wkE L P (.inr i)))

omit [DecidableEq B] in
theorem embA_injective (L : Lay) (P : CParams) : Function.Injective (embA (B := B) L P) := by
  intro a a' h
  rcases a with (b | c) | (q | i) <;> rcases a' with (b' | c') | (q' | i') <;>
    simp_all [embA]

/-- The program wires as arithmetic wires. -/
def embP (L : Lay) (P : CParams) (u : PW B L) : B ⊕ AWo L P := embA L P (.inl u)

omit [DecidableEq B] in
theorem embP_injective (L : Lay) (P : CParams) : Function.Injective (embP (B := B) L P) :=
  fun _ _ h => Sum.inl_injective (embA_injective L P h)

/-- The gates of the pre-processing program on the arithmetic wires. -/
def prepW (I : Inp B L) (P : CParams) : List (CGate (B ⊕ AWo L P)) :=
  (progG (prog I)).map (CGate.map (embP L P))

/-- **The circuit of the arithmetic**: the program, CORDIC on its output registers, the
program backwards. -/
def circO (I : Inp B L) (κ ζ : ℝ) : List (CGate (B ⊕ AWo L (params L.w κ ζ))) :=
  prepW I (params L.w κ ζ) ++
    (circW (params L.w κ ζ) (xwO L) (ywO L)).map (CGate.map (embA L (params L.w κ ζ))) ++
    (prepW I (params L.w κ ζ)).reverse

/-- **The angle arithmetic** of the four-sector private operation, with CORDIC scale `κ` and
CORDIC accuracy `ζ`. -/
def odeArith (I : Inp B L) (κ ζ : ℝ) : Arith B where
  bT := (params L.w κ ζ).bT
  bP := (params L.w κ ζ).bP
  A := nPrep L + nWork (params L.w κ ζ)
  circ := (circO I κ ζ).map CGate.toGate
  tw := fun x => thetaBits (P := params L.w κ ζ) (inBits I x)
  pw := fun x => phiBits (P := params L.w κ ζ) (inBits I x)

/-! ### What the circuit computes -/

omit [DecidableEq B] in
theorem prog_proper (I : Inp B L) : ∀ g ∈ progG (prog I), g.Proper := by
  intro g hg
  simp only [progG, List.mem_flatMap] at hg
  obtain ⟨o, ho, hg⟩ := hg
  exact ROp.proper_gates o _ ((progOK I).ok o ho) w_pos g hg

omit [DecidableEq B] in
theorem cfgOf_zero_comp (x : B → Bool) (P : CParams) :
    (Sum.elim x (fun _ => false) : B ⊕ AWo L P → Bool) ∘ embP L P =
      cfgOf x (0 : RO L → BitVec L.w) := by
  funext u
  rcases u with b | (_ | i | i | ⟨r, i⟩) <;> simp [embP, embA, cfgOf]

omit [DecidableEq B] in
theorem inBits_eq (I : Inp B L) (hL : L.OK) (x : B → Bool) :
    cfgOf x (regsO I x) ∘ Sum.elim (xwO L) (ywO L) = inBits I x := by
  funext i
  rcases i with j | j
  · simp only [Function.comp_apply, Sum.elim_inl, xwO, cfgOf, inBits]
    rw [v_xc I x hL]
  · simp only [Function.comp_apply, Sum.elim_inr, ywO, cfgOf, inBits]
    rw [v_yc I x hL]

omit [DecidableEq B] in
theorem embP_ne_word (P : CParams) (q : Fin P.bT ⊕ Fin P.bP) (a : PW B L) :
    embP L P a ≠ .inr (.inl q) := by
  rcases a with b | c <;> simp [embP, embA]

omit [DecidableEq B] in
theorem embP_ne_cordic (P : CParams) (j : Fin (nWork P)) (a : PW B L) :
    embP L P a ≠ .inr (.inr (wkE L P (.inr j))) := by
  rcases a with b | c <;> simp [embP, embA]

/-- **The circuit computes the angle words of `Z' = zx + i zy` and restores its work wires.** -/
theorem circO_run (I : Inp B L) (hL : L.OK) (κ ζ : ℝ) (hκ : 0 < κ) (x : B → Bool) :
    crun (circO I κ ζ) (Sum.elim x (fun _ => false)) =
      Sum.elim x (Sum.elim (Sum.elim (thetaBits (P := params L.w κ ζ) (inBits I x))
        (phiBits (P := params L.w κ ζ) (inBits I x))) (fun _ => false)) := by
  set P := params L.w κ ζ with hPdef
  have hP : P.OK := params_OK L.w w_pos κ ζ hκ
  set E := embA (B := B) L P with hE
  set EP := embP (B := B) L P with hEP
  set y : PW B L → Bool := cfgOf x (regsO I x) with hy
  set z0 : B ⊕ AWo L P → Bool := Sum.elim x (fun _ => false) with hz0
  set z1 := crun (prepW I P) z0 with hz1
  set z2 := crun ((circW P (xwO L) (ywO L)).map (CGate.map E)) z1 with hz2
  have h1 : z1 ∘ EP = y := by
    rw [hz1, prepW, crun_map _ (embP_injective L P), hz0, cfgOf_zero_comp,
      crun_progG (lvO L) (prog I) (progOK I) w_pos x 0 (fun _ _ => rfl)]
    rfl
  have h1' : ∀ u, (∀ a, EP a ≠ u) → z1 u = z0 u := fun u hu =>
    crun_map_of_not_mem EP _ z0 u hu
  have h1E : z1 ∘ E = Sum.elim y (fun _ => false) := by
    funext a
    rcases a with u | (q | j)
    · exact congrFun h1 u
    · show z1 (Sum.inr (Sum.inl q)) = false
      rw [h1' _ (fun a => embP_ne_word P q a)]
      rfl
    · show z1 (Sum.inr (Sum.inr (wkE L P (Sum.inr j)))) = false
      rw [h1' _ (fun a => embP_ne_cordic P j a)]
      rfl
  have h2 : z2 ∘ E = Sum.elim y (Sum.elim (Sum.elim (thetaBits (y ∘ Sum.elim (xwO L) (ywO L)))
      (phiBits (y ∘ Sum.elim (xwO L) (ywO L)))) (fun _ => false)) := by
    rw [hz2, crun_map _ (embA_injective L P), h1E, circW_run hP (xy_injective L)]
  have hrev : (prepW I P).reverse = (progG (prog I)).reverse.map (CGate.map EP) := by
    rw [prepW, List.map_reverse]
  have h3 : crun (prepW I P).reverse z2 ∘ EP = cfgOf x 0 := by
    have h2P : z2 ∘ EP = y := by
      funext u
      exact congrFun h2 (Sum.inl u)
    rw [hrev, crun_map _ (embP_injective L P), h2P, hy, regsO,
      ← crun_progG (lvO L) (prog I) (progOK I) w_pos x 0 (fun _ _ => rfl),
      crun_reverse _ (prog_proper I)]
  have h3' : ∀ u, (∀ a, EP a ≠ u) → crun (prepW I P).reverse z2 u = z2 u := by
    intro u hu
    rw [hrev]
    exact crun_map_of_not_mem EP _ z2 u hu
  rw [circO, crun_append, crun_append, ← hz1, ← hz2, ← inBits_eq I hL x, ← hy]
  funext w'
  rcases w' with b | (q | i)
  · have := congrFun h3 (Sum.inl b)
    simpa [hEP, embP, embA, cfgOf] using this
  · rw [h3' _ (fun a => embP_ne_word P q a)]
    exact congrFun h2 (Sum.inr (Sum.inl q))
  · obtain ⟨u, rfl⟩ := (wkE L P).surjective i
    rcases u with c | j
    · have := congrFun h3 (Sum.inr c)
      simp only [Function.comp_apply, hEP, embP, embA] at this
      rw [this]
      rcases c with _ | i | i | ⟨r, i⟩ <;> simp [cfgOf]
    · rw [h3' _ (fun a => embP_ne_cordic P j a)]
      have h2j := congrFun h2 (Sum.inr (Sum.inr j))
      simp only [Function.comp_apply, Sum.elim_inr] at h2j
      simp only [Sum.elim_inr]
      exact h2j

end Circuit

/-! ### The arithmetic hypothesis -/

section OK

variable {B : Type} [DecidableEq B] {L : Lay}

/-- **The decoded value** `κ ρ_x (zx + i zy)`, with `ρ_x = ρ` on the dissipative part and
`ρ_x = 1` on the Hamiltonian part. -/
def decO (I : Inp B L) (κ ρ : ℝ) (x : B → Bool) : ℂ :=
  ((κ * (if x I.pt then ρ else 1) : ℝ) : ℂ) * ((I.zx x : ℂ) + (I.zy x : ℂ) * Complex.I)

omit [DecidableEq B] in
theorem ofBits_inBits (I : Inp B L) (x : B → Bool) (side : Bool) :
    ofBits (fun j => if h : j < L.w then
      inBits I x (if side then .inr ⟨j, h⟩ else .inl ⟨j, h⟩) else false) L.w =
      BitVec.ofInt L.w (if side then I.zy x else I.zx x) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_ofBits]
  cases side <;> simp [hi, inBits]

omit [DecidableEq B] in
/-- The CORDIC input is `Z' = zx + i zy`. -/
theorem zIn_inBits (I : Inp B L) (hL : L.OK) (κ ζ : ℝ) (x : B → Bool) :
    zIn (P := params L.w κ ζ) (inBits I x) = (I.zx x : ℂ) + (I.zy x : ℂ) * Complex.I := by
  have hx : inX (P := params L.w κ ζ) (inBits I x) = I.zx x := by
    show (ofBits (fun j => if h : j < L.w then
      inBits I x (if false then .inr ⟨j, h⟩ else .inl ⟨j, h⟩) else false) L.w).toInt = _
    rw [ofBits_inBits, if_neg Bool.false_ne_true, toInt_ofInt_of _ w_pos (I.zx_abs_lt x hL)]
  have hy : inY (P := params L.w κ ζ) (inBits I x) = I.zy x := by
    show (ofBits (fun j => if h : j < L.w then
      inBits I x (if true then .inr ⟨j, h⟩ else .inl ⟨j, h⟩) else false) L.w).toInt = _
    rw [ofBits_inBits, if_pos rfl, toInt_ofInt_of _ w_pos (I.zy_abs_lt x hL)]
  rw [zIn, toC, hx, hy]

omit [DecidableEq B] in
theorem decO_eq (I : Inp B L) (hL : L.OK) (κ ρ ζ : ℝ) (x : B → Bool) :
    decO I κ ρ x = ((κ * (if x I.pt then ρ else 1) : ℝ) : ℂ) *
      zIn (P := params L.w κ ζ) (inBits I x) := by
  rw [zIn_inBits I hL]
  rfl

theorem inBits_update (I : Inp B L) {o : B} (ho : I.Avoids o) (x : B → Bool) (v : Bool) :
    inBits I (Function.update x o v) = inBits I x := by
  unfold inBits
  rw [Inp.zx_update I x ho v, Inp.zy_update I x ho v]

omit [DecidableEq B] in
theorem circO_cs (I : Inp B L) (κ ζ : ℝ) : ∀ g ∈ circO I κ ζ, g.cs.length ≤ 3 := by
  have hp : ∀ g ∈ prepW I (params L.w κ ζ), g.cs.length ≤ 3 := by
    intro g hg
    simp only [prepW, List.mem_map] at hg
    obtain ⟨g', hg', rfl⟩ := hg
    simp only [progG, List.mem_flatMap] at hg'
    obtain ⟨o, _, hg'⟩ := hg'
    have := ROp.cs_gates o g' hg'
    simp only [CGate.map, List.length_map]
    omega
  intro g hg
  simp only [circO, List.mem_append, List.mem_reverse] at hg
  rcases hg with (hg | hg) | hg
  · exact hp g hg
  · simp only [List.mem_map] at hg
    obtain ⟨g', hg', rfl⟩ := hg
    simp only [CGate.map, List.length_map]
    exact circW_cs _ _ _ g' hg'
  · exact hp g hg

omit [DecidableEq B] in
theorem circO_proper (I : Inp B L) (κ ζ : ℝ) (hκ : 0 < κ) : ∀ g ∈ circO I κ ζ, g.Proper := by
  have hP := params_OK L.w w_pos κ ζ hκ
  have hp : ∀ g ∈ prepW I (params L.w κ ζ), g.Proper := by
    intro g hg
    simp only [prepW, List.mem_map] at hg
    obtain ⟨g', hg', rfl⟩ := hg
    exact CGate.proper_map _ (embP_injective L _) g' (prog_proper I g' hg')
  intro g hg
  simp only [circO, List.mem_append, List.mem_reverse] at hg
  rcases hg with (hg | hg) | hg
  · exact hp g hg
  · simp only [List.mem_map] at hg
    obtain ⟨g', hg', rfl⟩ := hg
    exact CGate.proper_map _ (embA_injective L _) g' (circW_proper hP (xy_injective L) g' hg')
  · exact hp g hg

/-- **The arithmetic hypothesis.** For `κ > 0`, a CORDIC accuracy `0 < ζc ≤ 1` and a factor `ρ`
with `|ρ - 1| ≤ 1/2` and `ζc + 2 |ρ - 1| ≤ ζ`, the arithmetic satisfies `ArithOK` at accuracy `ζ`
for the decoder `decO I κ ρ`, provided the orientation wire `o` is not an input wire. -/
theorem odeArith_ok (I : Inp B L) (hL : L.OK) (o : B) (ho : I.Avoids o) (κ ρ ζc ζ : ℝ)
    (hκ : 0 < κ) (hζc : 0 < ζc) (hζc1 : ζc ≤ 1) (hρ : |ρ - 1| ≤ 1 / 2)
    (hζ : ζc + 2 * |ρ - 1| ≤ ζ) : ArithOK (odeArith I κ ζc) o (decO I κ ρ) ζ := by
  have hP := params_OK L.w w_pos κ ζc hκ
  have hρ0 : 0 < ρ := by
    have := (abs_le.1 hρ).1
    linarith
  have hf : ∀ x : B → Bool, 0 < (if x I.pt then ρ else 1) := fun x => by
    split_ifs
    · exact hρ0
    · exact one_pos
  have hf1 : ∀ x : B → Bool, |(if x I.pt then ρ else 1) - 1| ≤ |ρ - 1| := fun x => by
    split_ifs
    · exact le_rfl
    · simp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
    exact circO_cs I κ ζc g' hg'
  · exact classical_map_toGate _ (circO_proper I κ ζc hκ)
  · intro x
    have h := cfgRun_map_toGate (circO I κ ζc) (Sum.elim x (fun _ => false))
    rw [circO_run I hL κ ζc hκ x] at h
    exact h
  · intro x v
    exact congrArg (thetaBits (P := params L.w κ ζc)) (inBits_update I ho x v)
  · intro x v
    exact congrArg (phiBits (P := params L.w κ ζc)) (inBits_update I ho x v)
  · intro x
    have hU2 : (2 : ℝ) ≤ (params L.w κ ζc).U := by
      have h := params_U_ge L.w κ ζc hκ
      have : (2 : ℝ) ≤ 2 ^ ((params L.w κ ζc).n + 4) :=
        le_self_pow₀ (by norm_num) (by omega)
      linarith
    have h := theta_error hP (inBits I x) κ hκ (params_c2 L.w κ ζc) (params_U L.w κ ζc hκ) hU2
    have hb := params_theta L.w κ ζc hκ hζc hζc1
    set f := (if x I.pt then ρ else 1) with hfdef
    set r := ‖zIn (P := params L.w κ ζc) (inBits I x)‖ with hr
    have hn : ‖decO I κ ρ x‖ = (1 + (f - 1)) * (κ * r) := by
      rw [decO_eq I hL κ ρ ζc, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (mul_pos hκ (hf x))]
      ring
    have ha := Cordic.abs_arctan_sub_le (κ * r) (f - 1) (by positivity)
      ((hf1 x).trans hρ)
    change |thetaVal (thetaBits (P := params L.w κ ζc) (inBits I x)) -
      2 * Real.arctan ‖decO I κ ρ x‖| ≤ ζ
    rw [hn]
    unfold thetaVal
    have h3 : |2 * Real.arctan ((1 + (f - 1)) * (κ * r)) - 2 * Real.arctan (κ * r)| ≤
        2 * |ρ - 1| := by
      rw [← mul_sub, abs_mul, abs_two]
      linarith [hf1 x]
    calc _ ≤ |(∑ j : Fin (params L.w κ ζc).bT,
          if thetaBits (P := params L.w κ ζc) (inBits I x) j then
            Real.pi / 2 ^ (j.val + 1) else 0) - 2 * Real.arctan (κ * r)| +
          |2 * Real.arctan (κ * r) - 2 * Real.arctan ((1 + (f - 1)) * (κ * r))| :=
          abs_sub_le _ _ _
      _ ≤ ζc + 2 * |ρ - 1| := add_le_add (h.trans hb) (by rw [abs_sub_comm]; exact h3)
      _ ≤ ζ := hζ
  · intro x hx
    have hz : zIn (P := params L.w κ ζc) (inBits I x) ≠ 0 := by
      intro h0
      apply hx
      rw [decO_eq I hL κ ρ ζc, h0, mul_zero]
    obtain ⟨m, hm⟩ := phi_error hP (inBits I x) hz (params_c1 L.w κ ζc)
    refine ⟨m, ?_⟩
    have harg : Complex.arg (decO I κ ρ x) = Complex.arg (zIn (P := params L.w κ ζc) (inBits I x))
        := by
      rw [decO_eq I hL κ ρ ζc, Complex.arg_real_mul _ (mul_pos hκ (hf x))]
    change |phiVal (phiBits (P := params L.w κ ζc) (inBits I x)) -
      Complex.arg (decO I κ ρ x) - 2 * Real.pi * m| ≤ ζ
    rw [harg]
    unfold phiVal
    have := params_phi L.w κ ζc hζc
    have := abs_nonneg (ρ - 1)
    linarith

end OK


/-! ### Counts -/

section Counts

variable {B : Type} {L : Lay}

/-- The registers of the program as a sum type. -/
def RO.equiv (L : Lay) : RO L ≃ Fin 31 ⊕ (Fin (L.F + 2) ⊕ (Fin 3 ⊕ (Fin (L.mA + 1) ⊕
    (Fin (L.mS + 1) ⊕ Fin (L.mS + 1))))) where
  toFun
    | .ax1 => .inl 0 | .n1 => .inl 1 | .z1 => .inl 2 | .ax2 => .inl 3 | .n2 => .inl 4
    | .z2 => .inl 5 | .q0 => .inl 6 | .q1 => .inl 7 | .du => .inl 8 | .de => .inl 9
    | .dd => .inl 10 | .nw => .inl 11 | .rg => .inl 12 | .nn => .inl 13 | .hx => .inl 14
    | .hy => .inl 15 | .lx => .inl 16 | .ly => .inl 17 | .sx => .inl 18 | .ex => .inl 19
    | .ax => .inl 20 | .sy => .inl 21 | .ey => .inl 22 | .ay => .inl 23 | .ayt => .inl 24
    | .md => .inl 25 | .me => .inl 26 | .mu => .inl 27 | .am => .inl 28 | .axs => .inl 29
    | .ays => .inl 30
    | .hc j => .inr (.inl j)
    | .cc j => .inr (.inr (.inl j))
    | .ec j => .inr (.inr (.inr (.inl j)))
    | .xc j => .inr (.inr (.inr (.inr (.inl j))))
    | .yc j => .inr (.inr (.inr (.inr (.inr j))))
  invFun
    | .inl i => ![.ax1, .n1, .z1, .ax2, .n2, .z2, .q0, .q1, .du, .de, .dd, .nw, .rg, .nn, .hx,
        .hy, .lx, .ly, .sx, .ex, .ax, .sy, .ey, .ay, .ayt, .md, .me, .mu, .am, .axs, .ays] i
    | .inr (.inl j) => .hc j
    | .inr (.inr (.inl j)) => .cc j
    | .inr (.inr (.inr (.inl j))) => .ec j
    | .inr (.inr (.inr (.inr (.inl j)))) => .xc j
    | .inr (.inr (.inr (.inr (.inr j)))) => .yc j
  left_inv r := by cases r <;> rfl
  right_inv u := by
    rcases u with i | j | j | j | j | j
    · fin_cases i <;> rfl
    all_goals rfl

/-- The number of registers of the program. -/
theorem card_RO (L : Lay) :
    Fintype.card (RO L) = 31 + (L.F + 2) + 3 + (L.mA + 1) + 2 * (L.mS + 1) := by
  rw [Fintype.card_congr (RO.equiv L)]
  simp only [Fintype.card_sum, Fintype.card_fin]
  ring

/-- **Counts.** The arithmetic has at most `26 w |prog|` gates of the program and its inverse,
plus the CORDIC gates of `cordicArith_counts` for `b = w`; its work wires are those of the
program (`1 + 2w + |registers| w`) and those of CORDIC. -/
theorem odeArith_counts [DecidableEq B] (I : Inp B L) (κ ζ : ℝ) :
    (odeArith I κ ζ).circ.length ≤
      26 * L.w * (31 + (L.F + 2) + 3 + (L.mA + 1) + 2 * (L.mS + 1)) +
        (156 * (params L.w κ ζ).w * ((params L.w κ ζ).n + 1) + (params L.w κ ζ).bP +
          2 * (params L.w κ ζ).bT) ∧
    (odeArith I κ ζ).A =
      (1 + 2 * L.w + (31 + (L.F + 2) + 3 + (L.mA + 1) + 2 * (L.mS + 1)) * L.w) +
        (1 + 2 * (params L.w κ ζ).w + (6 * ((params L.w κ ζ).n + 1) + 1) * (params L.w κ ζ).w) ∧
    (odeArith I κ ζ).bT = (params L.w κ ζ).bT ∧ (odeArith I κ ζ).bP = (params L.w κ ζ).bP := by
  obtain ⟨hc, hA, -, -⟩ := cordicArith_counts L.w (xwO (B := B) L) (ywO L) κ ζ
  refine ⟨?_, ?_, rfl, rfl⟩
  · have hp := length_progG (prog I) (w_pos (L := L))
    rw [length_prog] at hp
    have hcw : (circW (params L.w κ ζ) (xwO (B := B) L) (ywO L)).length ≤
        156 * (params L.w κ ζ).w * ((params L.w κ ζ).n + 1) + (params L.w κ ζ).bP +
          2 * (params L.w κ ζ).bT := by
      have e : (cordicArith L.w (xwO (B := B) L) (ywO L) κ ζ).circ.length =
          (circW (params L.w κ ζ) (xwO (B := B) L) (ywO L)).length := List.length_map _
      omega
    change ((circO I κ ζ).map CGate.toGate).length ≤ _
    simp only [List.length_map, circO, List.length_append, List.length_reverse, prepW]
    nlinarith
  · change nPrep L + nWork (params L.w κ ζ) = _
    have e : (cordicArith L.w (xwO (B := B) L) (ywO L) κ ζ).A = nWork (params L.w κ ζ) := rfl
    rw [nPrep, card_CW, card_RO, ← e, hA]
    ring

end Counts

end

end SparseHamiltonian.GateBinaryODE
