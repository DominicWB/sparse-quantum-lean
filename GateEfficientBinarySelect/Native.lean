import GateEfficientBinarySelect.Address
import GateEfficientBinarySelect.Computed
import GateEfficientBinaryODETime.Clock

/-!
# The private operation on branch-dependent meshes from time-indexed binary data

The private operation of Lemma `ode:lem:gate-select` at the joint label `z = ((ini, u), w)` and
the slot `r < 2^m` of its branch, with the tagged representation of Lemma `ode:lem:tags`, is
the four-sector Cayley action (`GateBinaryODE.act4`) of the sample at the branch address
`g = 2^m u' + r (2^m - u')` (`u' = (ini ? u : 0)`, `addrN`) of the grid of `2^(2m)` points, at the
LCHS node of `w` and the Cayley parameter `γ (2^m - u') / 2^m`: the branch scale
`(T - v_u)/T` of the node `v_u = u' T / 2^m` (`privFamB`). Its native form:

* the compute circuit (`odeOpB`) runs the address program of `Address` on the label and slot
  wires (`apG`), writing the address and the duration word into scratch registers, and then the
  compute circuit `GateBinaryODE.computeV4` of the constant-coefficient library, every primitive
  call also reading the `2m` address bits (`slotOpR`, reassociated by `reW`); the primitives are
  the coherent sampled-time oracles `GateBinary.primsT` on the grid of `2^(2m)` points;
* the decoder is the released `GateBinaryODE.decO` with the duration word read from the register
  `n1` (`inpB`, `inpBB`), so the released arithmetic `GateBinaryODE.odeArith` applies unchanged
  (`odeArB`);
* `decOK_B`: at every context word (slot and address registers) the decoder satisfies the
  released decoder hypothesis `GateBinaryODE.DecOK` of the sample at the address read from the
  context, with the Cayley parameter read from its duration word;
* `nativeOK_B`: the native identity of the label- and slot-selected family `privFamB`, from the
  released `GateBinaryODE.nativeOK4` at every context word, `nativeOK_slotR` and
  `nativeOK_computed`;
* `odeOpB_public`, `odeOpB_nGates`, `odeOpB_nCalls`, `odeArB_ok`: the public conditions, the
  counts and the arithmetic hypothesis.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateBinarySelect

noncomputable section
open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
open SparseHamiltonian.GateBinary SparseHamiltonian.GateBinaryODE SparseHamiltonian.OracleCircuit
open SparseHamiltonian.GateBinaryODETime (baseW2 selW2 glue2 atSlot2 glue2_apply_baseW2
  atSlot2_public gridP nodeWT_eq)
open SparseHamiltonian.GateODE (Label)
open SparseHamiltonian.GateODE.Time (TParams)
open SparseHamiltonian.GatePointerEncoding (wordEquivFin wordValue)
open NativeSparseBlockEncoding (Data Query)
open scoped InnerProduct

/-! ### Wires -/

/-- The wires of the address registers. -/
abbrev ZA (m : ℕ) := CW (RO (aLay m)) (aLay m).w

/-- The context wires of the intermediate operation: the slot wires and the address registers. -/
abbrev CtxW (m : ℕ) := Fin m ⊕ ZA m

/-- The wires of the intermediate operation, whose context wires are selection wires. -/
abbrev BWA (k b m l : ℕ) := NB (LabW m l ⊕ CtxW m) (PR4 k) (SZ4 k b)

/-- The wires of the branch operation: label and slot wires, the private register, and the
scratch of the address registers and of the constant-coefficient operation. -/
abbrev BWB (k b m l : ℕ) := NB (TSel m l m) (PR4 k) (ZA m ⊕ SZ4 k b)

theorem addrBit_lt (m : ℕ) (j : Fin (2 * m)) : j.val + 2 < (aLay m).w := by
  rw [aLay_w]
  omega

/-- **The address bits**: the bits `2, …, 2m + 1` of the register `md`. -/
def addrBit (m : ℕ) : Fin (2 * m) ↪ CtxW m :=
  ⟨fun j => Sum.inr (CW.reg .md ⟨j.val + 2, addrBit_lt m j⟩), fun i j h => by
    simp only [Sum.inr.injEq, CW.reg.injEq, Fin.mk.injEq, true_and] at h
    exact Fin.ext (by omega)⟩

/-- A wire of the register `n1`, as a context wire (the zero wire beyond the width). -/
def n1W (m : ℕ) (i : ℕ) : CtxW m :=
  if h : i < (aLay m).w then Sum.inr (CW.reg .n1 ⟨i, h⟩) else Sum.inr CW.zero

/-! ### Input wirings -/

/-- An input wiring of the released program transported along a map of wires. -/
def mapInp {B B' : Type} {L : Lay} (I : Inp B L) (e : B → B') : Inp B' L where
  ini := e I.ini
  u j := e (I.u j)
  wd j := e (I.wd j)
  pt := e I.pt
  tg := e I.tg
  x1 i := e (I.x1 i)
  y1 i := e (I.y1 i)
  x2 i := e (I.x2 i)
  y2 i := e (I.y2 i)

theorem mapInp_avoids {B B' : Type} [DecidableEq B] [DecidableEq B'] {L : Lay} (I : Inp B L)
    (e : B → B') (he : Function.Injective e) {o : B} (h : I.Avoids o) :
    (mapInp I e).Avoids (e o) where
  ini := fun h' => h.ini (he h')
  u j := fun h' => h.u j (he h')
  wd j := fun h' => h.wd j (he h')
  pt := fun h' => h.pt (he h')
  tg := fun h' => h.tg (he h')
  x1 j := fun h' => h.x1 j (he h')
  y1 j := fun h' => h.y1 j (he h')
  x2 j := fun h' => h.x2 j (he h')
  y2 j := fun h' => h.y2 j (he h')

theorem decO_mapInp {B B' : Type} {L : Lay} (I : Inp B L) (e : B → B') (κ ρ : ℝ)
    (y : B' → Bool) : decO (mapInp I e) κ ρ y = decO I κ ρ (fun w => y (e w)) := rfl

/-- The decoder does not read a wire that is none of the input wires. -/
theorem decO_update {B : Type} [DecidableEq B] {L : Lay} (I : Inp B L) {o : B}
    (ho : I.Avoids o) (κ ρ : ℝ) (x : B → Bool) (v : Bool) :
    decO I κ ρ (Function.update x o v) = decO I κ ρ x := by
  unfold decO
  rw [Inp.zx_update _ x ho v, Inp.zy_update _ x ho v, Function.update_of_ne ho.pt]

/-- **The input wiring** of the angle arithmetic on the intermediate operation: the sign bit of
`n1` as the source bit and its bits `1, …, kq` as the node word (the duration word), the LCHS
word, the part and the tag wire, and the two value registers. -/
def inpB (k : ℕ) (L : Lay) (m : ℕ) : Inp (BWA k L.b m L.lq) L where
  ini := selW2 (n1W m ((aLay m).w - 1))
  u j := selW2 (n1W m (j.val + 1))
  wd j := baseW2 (lB4 (.inr j))
  pt := baseW2 pB4
  tg := baseW2 tB4
  x1 i := baseW2 (v14 (.inl i))
  y1 i := baseW2 (v14 (.inr i))
  x2 i := baseW2 (v24 (.inl i))
  y2 i := baseW2 (v24 (.inr i))

theorem inpB_avoids (k : ℕ) (L : Lay) (m : ℕ) :
    (inpB k L m).Avoids (Sum.inl (Sum.inr (oW k))) where
  ini := by simp [inpB, selW2]
  u j := by simp [inpB, selW2]
  wd j := by simp [inpB, baseW2, lB4]
  pt := by simp [inpB, baseW2, pB4, Ne.symm (oW_ne_pW (k := k))]
  tg := by simp [inpB, baseW2, tB4, Ne.symm (oW_ne_tW (k := k))]
  x1 i := by simp [inpB, baseW2, v14]
  y1 i := by simp [inpB, baseW2, v14]
  x2 i := by simp [inpB, baseW2, v24]
  y2 i := by simp [inpB, baseW2, v24]

/-- The input wiring on the wires of the branch operation. -/
def inpBB (k : ℕ) (L : Lay) (m : ℕ) : Inp (BWB k L.b m L.lq) L := mapInp (inpB k L m) reW

theorem inpBB_avoids (k : ℕ) (L : Lay) (m : ℕ) :
    (inpBB k L m).Avoids (Sum.inl (Sum.inr (oW k))) :=
  mapInp_avoids (inpB k L m) reW reW.injective (inpB_avoids k L m)

/-! ### The operations -/

/-- **The intermediate operation**: the compute circuit `computeV4` with every primitive call also
reading the address bits, the orientation wire and the decoder `decO` on `inpB`. -/
def ndA (k : ℕ) (L : Lay) (m : ℕ) (κ ρ : ℝ) :
    NativeOp (LabW m L.lq ⊕ CtxW m) (PR4 k) (SZ4 k L.b) (Fin (2 * m) ⊕ PY k L.b) Query :=
  slotOpR (addrBit m) (computeV4 k L.b m L.lq) (oW k) (decO (inpB k L m) κ ρ)

/-- The source sector bit of the selection wires. -/
def iniT (m l : ℕ) : TSel m l m := Sum.inl (Sum.inl (Sum.inl ()))

/-- The node word of the selection wires. -/
def uT (m l : ℕ) (j : Fin m) : TSel m l m := Sum.inl (Sum.inl (Sum.inr j))

/-- The slot word of the selection wires. -/
def slT (m l : ℕ) (j : Fin m) : TSel m l m := Sum.inr j

theorem embP_injective (k b m l : ℕ) :
    Function.Injective (fun w : PW (TSel m l m) (aLay m) => (match w with
      | .inl s => .inl (.inl s)
      | .inr c => .inr (.inl c) : BWB k b m l)) := by
  intro a a' h
  rcases a with s | c <;> rcases a' with s' | c' <;> simp_all

/-- The wires of the address program inside the branch operation. -/
def embP (k b m l : ℕ) : PW (TSel m l m) (aLay m) ↪ BWB k b m l :=
  ⟨fun w => match w with
    | .inl s => .inl (.inl s)
    | .inr c => .inr (.inl c), embP_injective k b m l⟩

/-- **The address program** as gates of the branch operation. -/
def apG (k b m l : ℕ) : List (Gate (BWB k b m l)) :=
  ((addrG (iniT m l) (uT m l) (slT m l)).map (CGate.map (embP k b m l))).map CGate.toGate

/-- **The branch operation**: the address program, then the compute circuit of the intermediate
operation on the reassociated wires; the orientation wire and the decoder on `inpBB`. -/
def odeOpB (k : ℕ) (L : Lay) (m : ℕ) (κ ρ : ℝ) :
    NativeOp (TSel m L.lq m) (PR4 k) (ZA m ⊕ SZ4 k L.b) (Fin (2 * m) ⊕ PY k L.b) Query where
  V := nGatesOf (apG k L.b m L.lq) ++ (ndA k L m κ ρ).V.map (NInstr.map reW)
  o := oW k
  dec := decO (inpBB k L m) κ ρ

/-- **The angle arithmetic** of the branch operation: the released arithmetic on `inpBB`. -/
def odeArB (k : ℕ) (L : Lay) (m : ℕ) (κ ζ : ℝ) : Arith (BWB k L.b m L.lq) :=
  odeArith (inpBB k L m) κ ζ

/-- **The arithmetic hypothesis** of the branch operation (the released `odeArith_ok`). -/
theorem odeArB_ok (k : ℕ) (L : Lay) (m : ℕ) (hL : L.OK) (κ ρ ζc ζ : ℝ) (hκ : 0 < κ)
    (hζc : 0 < ζc) (hζc1 : ζc ≤ 1) (hρ : |ρ - 1| ≤ 1 / 2) (hζ : ζc + 2 * |ρ - 1| ≤ ζ) :
    ArithOK (odeArB k L m κ ζc) (Sum.inl (Sum.inr (odeOpB k L m κ ρ).o))
      (odeOpB k L m κ ρ).dec ζ :=
  odeArith_ok (inpBB k L m) hL _ (inpBB_avoids k L m) κ ρ ζc ζ hκ hζc hζc1 hρ hζ

/-! ### Validity and counts -/

theorem apG_ok (k b m l : ℕ) : ∀ g ∈ apG k b m l, GateOK 3 g := by
  intro g hg
  simp only [apG, List.mem_map] at hg
  obtain ⟨g1, ⟨g0, hg0, rfl⟩, rfl⟩ := hg
  refine ⟨?_, ?_, ?_⟩
  · simp only [CGate.toGate, CGate.map, List.length_map]
    have := addrG_cs (iniT m l) (uT m l) (slT m l) g0 hg0
    omega
  · exact CGate.proper_map _ (embP k b m l).injective g0
      (addrG_proper (iniT m l) (uT m l) (slT m l) g0 hg0)
  · exact pauliX_unitary

theorem apG_classical (k b m l : ℕ) : Classical (apG k b m l) :=
  classical_map_toGate _ (fun g hg => by
    simp only [List.mem_map] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    exact CGate.proper_map _ (embP k b m l).injective g0
      (addrG_proper (iniT m l) (uT m l) (slT m l) g0 hg0))

theorem length_apG (k b m l : ℕ) : (apG k b m l).length ≤ 13 * (2 * m + 14) * (m + 5) := by
  simp only [apG, List.length_map]
  exact length_addrG _ _ _

/-- The branch operation is public: its compute circuit is valid and the decoder does not read
the orientation wire. -/
theorem odeOpB_public (k : ℕ) (L : Lay) (m : ℕ) (κ ρ : ℝ) : (odeOpB k L m κ ρ).Public where
  valid := by
    intro i hi
    simp only [odeOpB, List.mem_append] at hi
    rcases hi with hi | hi
    · exact valid_nGatesOf _ (apG_ok k L.b m L.lq) i hi
    · exact valid_map_list reW _ (valid_slotR (addrBit m) _ (computeV4_valid k L.b m L.lq)) i hi
  dec_indep x v := decO_update (inpBB k L m) (inpBB_avoids k L m) κ ρ x v

/-- **The gates of the compute circuit**: the address program and the `28 k + 2` gates of the
constant-coefficient circuit. -/
theorem odeOpB_nGates (k : ℕ) (L : Lay) (m : ℕ) (κ ρ : ℝ) :
    nGatesN (odeOpB k L m κ ρ).V = (apG k L.b m L.lq).length + (28 * k + 2) := by
  change nGatesN (nGatesOf (apG k L.b m L.lq) ++ ((computeV4 k L.b m L.lq).map
    (slotInstrR (addrBit m))).map (NInstr.map reW)) = _
  rw [nGatesN_append, nGatesN_nGatesOf, nGatesN_map, nGatesN_slotR, computeV4_nGates]

/-- The compute circuit makes two calls of each oracle, as the constant-coefficient one. -/
theorem odeOpB_nCalls (k : ℕ) (L : Lay) (m : ℕ) (κ ρ : ℝ) (p : Query → Bool) :
    nCallsN p (odeOpB k L m κ ρ).V = 2 * (if p Query.rowLocation then 1 else 0) +
      2 * (if p Query.columnLocation then 1 else 0) + 2 * (if p Query.value then 1 else 0) := by
  change nCallsN p (nGatesOf (apG k L.b m L.lq) ++ ((computeV4 k L.b m L.lq).map
    (slotInstrR (addrBit m))).map (NInstr.map reW)) = _
  rw [nCallsN_append, nCallsN_nGatesOf, nCallsN_map, nCallsN_slotR, computeV4_nCalls, zero_add]

end

end SparseHamiltonian.GateBinarySelect
