import GateEfficientBinaryNodes.NodeAddr
import GateEfficientBinaryNodes.ConstSolver

/-!
# The private operation for computed source nodes

Theorem `ode:thm:gates` allows a positive source quadrature whose nodes are computed coherently
from their labels at polynomial cost, and Lemma `ode:lem:gate-select` reads the samples of the
branch of a label at the addresses `v_z + r u_z/M`; "for other efficiently computed nodes, any
time-address rounding is included in the stated represented-sample error". Here:

* **the node program** (`NodeProg`, hypothesis `NodeProg.OK`): a list of classical reversible
  gates (at most three controls each) on the node-index wires of the source label (`m` bits),
  a node register of `μ` bits and a scratch `Zn`, writing the node word `word u` of every node
  index `u` into the clean node register and returning the scratch clean; the node of the label
  `(true, u)` is `v_u = word u · T / 2^μ`. Its gates are counted (`|N.gates|`), as the paper's
  "polynomial-cost reversible arithmetic";
* **the address program** `addrGN` of `NodeAddr` on the label, the node register and the slot
  word computes the address `A = 2^m ν' + r (2^μ - ν')` on the grid of `2^(μ+m)` points exactly
  and the duration word `2^μ - ν'`;
* **the time-indexed data** are sampled on a grid of `2^nd` points, `nd ≤ μ + m`: every
  primitive call reads the top `nd` bits of the address (`addrBitN`), the grid point
  `⌊A / 2^(μ+m-nd)⌋` — the time-address rounding of the proof;
* the branch operation `odeOpN`: the node program and the address program (`apGN`), then the
  constant-coefficient compute circuit `GateBinaryODE.computeV4` with every call reading the
  data address, the decoder `decO` with the duration word read from the address registers
  (`inpBN`), and the released arithmetic `GateBinaryODE.odeArith` with `μ` duration bits
  (`odeArN`).

`apGN_run`: on clean scratch the node and address programs XOR the node word and the register
file into the scratch (`xorF fN`); `odeOpN_public`, `odeOpN_nGates`, `odeOpN_nCalls`,
`odeArN_ok`: the public conditions, the counts and the arithmetic hypothesis.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateBinaryNodes

noncomputable section
open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
open SparseHamiltonian.GateBinary SparseHamiltonian.GateBinaryODE SparseHamiltonian.OracleCircuit
open SparseHamiltonian.GateBinaryODETime (baseW2 selW2 glue2 atSlot2 glue2_apply_baseW2
  atSlot2_public)
open SparseHamiltonian.GateBinarySelect (slotOpR slotInstrR reW xorF mapInp mapInp_avoids
  decO_mapInp decO_update iniT uT slT nGatesN_slotR nCallsN_slotR valid_slotR selP)
open SparseHamiltonian.GateODE (Label)
open SparseHamiltonian.GatePointerEncoding (wordEquivFin wordValue)
open NativeSparseBlockEncoding (Data Query)
open scoped InnerProduct

/-! ### The node program -/

/-- **A coherent node program**: classical reversible gates on the node-index wires `Fin m` of
the source label, the node register `Fin μ` and a scratch `Zn`, and the node word `word u` it
computes for the node index `u`. -/
structure NodeProg (m mu : ℕ) (Zn : Type) where
  gates : List (CGate (Fin m ⊕ (Fin mu ⊕ Zn)))
  word : (Fin m → Bool) → Fin mu → Bool

/-- **The conditions on a node program**: proper gates with at most three controls, which on
every node index `u` write `word u` into the clean node register and return the scratch clean. -/
structure NodeProg.OK {m mu : ℕ} {Zn : Type} [DecidableEq Zn] (N : NodeProg m mu Zn) : Prop where
  proper : ∀ g ∈ N.gates, g.Proper
  ctrl : ∀ g ∈ N.gates, g.cs.length ≤ 3
  run : ∀ u : Fin m → Bool, crun N.gates (Sum.elim u (fun _ => false)) =
    Sum.elim u (Sum.elim (N.word u) (fun _ => false))

/-! ### Wires -/

/-- The address registers for computed nodes. -/
abbrev ZAN (m mu : ℕ) := CW (RO (aLayN m mu)) (aLayN m mu).w

/-- The computed scratch: the node register, the node scratch and the address registers. -/
abbrev ZaN (m mu : ℕ) (Zn : Type) := (Fin mu ⊕ Zn) ⊕ ZAN m mu

/-- The context wires of the intermediate operation: the slot wires and the computed scratch. -/
abbrev CtxN (m mu : ℕ) (Zn : Type) := Fin m ⊕ ZaN m mu Zn

/-- The wires of the intermediate operation, whose context wires are selection wires. -/
abbrev BWAN (k b m l mu : ℕ) (Zn : Type) := NB (LabW m l ⊕ CtxN m mu Zn) (PR4 k) (SZ4 k b)

/-- The wires of the branch operation for computed nodes. -/
abbrev BWBN (k b m l mu : ℕ) (Zn : Type) := NB (TSel m l m) (PR4 k) (ZaN m mu Zn ⊕ SZ4 k b)

theorem addrBitN_lt (m mu nd : ℕ) (hnd : nd ≤ mu + m) (j : Fin nd) :
    j.val + (mu + m - nd) + 2 < (aLayN m mu).w := by
  rw [aLayN_w]
  omega

/-- **The data address bits**: data time bit `j` is bit `j + (μ + m - nd) + 2` of `md`, so the
data address is the top `nd` bits of the address `A`. -/
def addrBitN (m mu nd : ℕ) (hnd : nd ≤ mu + m) (Zn : Type) : Fin nd ↪ CtxN m mu Zn :=
  ⟨fun j => Sum.inr (Sum.inr (CW.reg .md ⟨j.val + (mu + m - nd) + 2,
    addrBitN_lt m mu nd hnd j⟩)), fun i j h => by
    simp only [Sum.inr.injEq, CW.reg.injEq, Fin.mk.injEq, true_and] at h
    exact Fin.ext (by omega)⟩

/-- A wire of the register `n1`, as a context wire (the zero wire beyond the width). -/
def n1WN (m mu : ℕ) (Zn : Type) (i : ℕ) : CtxN m mu Zn :=
  if h : i < (aLayN m mu).w then Sum.inr (Sum.inr (CW.reg .n1 ⟨i, h⟩))
  else Sum.inr (Sum.inr CW.zero)

/-! ### Input wirings -/

/-- **The input wiring** of the angle arithmetic on the intermediate operation: the sign bit of
`n1` as the source bit and its bits `1, …, kq` as the node word (the duration word, `kq = μ`),
the LCHS word, the part and the tag wire, and the two value registers. -/
def inpBN (k : ℕ) (L : Lay) (m mu : ℕ) (Zn : Type) : Inp (BWAN k L.b m L.lq mu Zn) L where
  ini := selW2 (n1WN m mu Zn ((aLayN m mu).w - 1))
  u j := selW2 (n1WN m mu Zn (j.val + 1))
  wd j := baseW2 (lB4 (.inr j))
  pt := baseW2 pB4
  tg := baseW2 tB4
  x1 i := baseW2 (v14 (.inl i))
  y1 i := baseW2 (v14 (.inr i))
  x2 i := baseW2 (v24 (.inl i))
  y2 i := baseW2 (v24 (.inr i))

theorem inpBN_avoids (k : ℕ) (L : Lay) (m mu : ℕ) (Zn : Type) [DecidableEq Zn] :
    (inpBN k L m mu Zn).Avoids (Sum.inl (Sum.inr (oW k))) where
  ini := by simp [inpBN, selW2]
  u j := by simp [inpBN, selW2]
  wd j := by simp [inpBN, baseW2, lB4]
  pt := by simp [inpBN, baseW2, pB4, Ne.symm (oW_ne_pW (k := k))]
  tg := by simp [inpBN, baseW2, tB4, Ne.symm (oW_ne_tW (k := k))]
  x1 i := by simp [inpBN, baseW2, v14]
  y1 i := by simp [inpBN, baseW2, v14]
  x2 i := by simp [inpBN, baseW2, v24]
  y2 i := by simp [inpBN, baseW2, v24]

/-- The input wiring on the wires of the branch operation. -/
def inpBBN (k : ℕ) (L : Lay) (m mu : ℕ) (Zn : Type) : Inp (BWBN k L.b m L.lq mu Zn) L :=
  mapInp (inpBN k L m mu Zn) reW

theorem inpBBN_avoids (k : ℕ) (L : Lay) (m mu : ℕ) (Zn : Type) [DecidableEq Zn] :
    (inpBBN k L m mu Zn).Avoids (Sum.inl (Sum.inr (oW k))) :=
  mapInp_avoids (inpBN k L m mu Zn) reW reW.injective (inpBN_avoids k L m mu Zn)

/-! ### The computed scratch -/

section Prog

variable {k b m l mu : ℕ} {Zn : Type} [Fintype Zn] [DecidableEq Zn]

/-- The wires of the node program inside the branch operation. -/
def eNodeFun (k b m l mu : ℕ) (Zn : Type) : Fin m ⊕ (Fin mu ⊕ Zn) → BWBN k b m l mu Zn
  | .inl j => .inl (.inl (uT m l j))
  | .inr (.inl i) => .inr (.inl (.inl (.inl i)))
  | .inr (.inr z) => .inr (.inl (.inl (.inr z)))

theorem eNodeFun_injective (k b m l mu : ℕ) (Zn : Type) :
    Function.Injective (eNodeFun k b m l mu Zn) := by
  intro x y h
  rcases x with j | i | z <;> rcases y with j' | i' | z' <;>
    simp_all [eNodeFun, uT]

/-- The wires of the node program inside the branch operation. -/
def eNode (k b m l mu : ℕ) (Zn : Type) : Fin m ⊕ (Fin mu ⊕ Zn) ↪ BWBN k b m l mu Zn :=
  ⟨eNodeFun k b m l mu Zn, eNodeFun_injective k b m l mu Zn⟩

/-- The wires of the address program inside the branch operation: the selection wires, the
node register as inputs, and the address registers. -/
def eAddrFun (k b m l mu : ℕ) (Zn : Type) :
    PW (TSel m l m ⊕ Fin mu) (aLayN m mu) → BWBN k b m l mu Zn
  | .inl (.inl s) => .inl (.inl s)
  | .inl (.inr i) => .inr (.inl (.inl (.inl i)))
  | .inr c => .inr (.inl (.inr c))

theorem eAddrFun_injective (k b m l mu : ℕ) (Zn : Type) :
    Function.Injective (eAddrFun k b m l mu Zn) := by
  intro x y h
  rcases x with (s | i) | c <;> rcases y with (s' | i') | c' <;> simp_all [eAddrFun]

/-- The wires of the address program inside the branch operation. -/
def eAddr (k b m l mu : ℕ) (Zn : Type) : PW (TSel m l m ⊕ Fin mu) (aLayN m mu) ↪
    BWBN k b m l mu Zn :=
  ⟨eAddrFun k b m l mu Zn, eAddrFun_injective k b m l mu Zn⟩

/-- The address program on the selection wires and the node register. -/
def addrGT (m l mu : ℕ) : List (CGate (PW (TSel m l m ⊕ Fin mu) (aLayN m mu))) :=
  addrGN (Sum.inl (iniT m l)) (fun i => Sum.inr i) (fun j => Sum.inl (slT m l j))

/-- **The node and address programs** as gates of the branch operation. -/
def apGN (k b m l mu : ℕ) (Zn : Type) (N : NodeProg m mu Zn) : List (Gate (BWBN k b m l mu Zn)) :=
  ((N.gates.map (CGate.map (eNode k b m l mu Zn))).map CGate.toGate) ++
    (((addrGT m l mu).map (CGate.map (eAddr k b m l mu Zn))).map CGate.toGate)

/-- The node word of the source label of a selection. -/
def nodeOf (N : NodeProg m mu Zn) (σ : Cfg (TSel m l m)) : Fin mu → Bool :=
  N.word (fun j => σ (uT m l j))

/-- The inputs of the address program: the selection and the computed node word. -/
def xIn (N : NodeProg m mu Zn) (σ : Cfg (TSel m l m)) : TSel m l m ⊕ Fin mu → Bool :=
  Sum.elim σ (nodeOf N σ)

/-- The register file of the address program on a selection. -/
def regsT (N : NodeProg m mu Zn) (σ : Cfg (TSel m l m)) : RO (aLayN m mu) → BitVec (aLayN m mu).w :=
  regsN (Sum.inl (iniT m l)) (fun i => Sum.inr i) (fun j => Sum.inl (slT m l j)) (xIn N σ)

/-- **The computed scratch** of a selection: the node word, the clean node scratch and the
register file of the address program. -/
def fN (N : NodeProg m mu Zn) (σ : Cfg (TSel m l m)) : Cfg (ZaN m mu Zn) :=
  Sum.elim (Sum.elim (nodeOf N σ) (fun _ => false))
    (fun cw => cfgOf (xIn N σ) (regsT N σ) (Sum.inr cw))

omit [Fintype Zn] [DecidableEq Zn] in
theorem fN_reg (N : NodeProg m mu Zn) (σ : Cfg (TSel m l m)) (r : RO (aLayN m mu))
    (i : Fin (aLayN m mu).w) :
    fN N σ (Sum.inr (CW.reg r i)) = (regsT N σ r).getLsbD i := rfl

omit [Fintype Zn] in
theorem apGN_ok (N : NodeProg m mu Zn) (hN : N.OK) : ∀ g ∈ apGN k b m l mu Zn N, GateOK 3 g := by
  intro g hg
  simp only [apGN, List.mem_append, List.mem_map] at hg
  rcases hg with ⟨g1, ⟨g0, hg0, rfl⟩, rfl⟩ | ⟨g1, ⟨g0, hg0, rfl⟩, rfl⟩
  · refine ⟨?_, ?_, ?_⟩
    · simp only [CGate.toGate, CGate.map, List.length_map]
      exact hN.ctrl g0 hg0
    · exact CGate.proper_map _ (eNode k b m l mu Zn).injective g0 (hN.proper g0 hg0)
    · exact pauliX_unitary
  · refine ⟨?_, ?_, ?_⟩
    · simp only [CGate.toGate, CGate.map, List.length_map]
      have := addrGN_cs _ _ _ g0 hg0
      omega
    · exact CGate.proper_map _ (eAddr k b m l mu Zn).injective g0 (addrGN_proper _ _ _ g0 hg0)
    · exact pauliX_unitary

omit [Fintype Zn] in
theorem apGN_classical (N : NodeProg m mu Zn) (hN : N.OK) : Classical (apGN k b m l mu Zn N) := by
  apply classical_append
  · exact classical_map_toGate _ (fun g hg => by
      simp only [List.mem_map] at hg
      obtain ⟨g0, hg0, rfl⟩ := hg
      exact CGate.proper_map _ (eNode k b m l mu Zn).injective g0 (hN.proper g0 hg0))
  · exact classical_map_toGate _ (fun g hg => by
      simp only [List.mem_map] at hg
      obtain ⟨g0, hg0, rfl⟩ := hg
      exact CGate.proper_map _ (eAddr k b m l mu Zn).injective g0 (addrGN_proper _ _ _ g0 hg0))

omit [Fintype Zn] [DecidableEq Zn] in
theorem length_apGN (N : NodeProg m mu Zn) :
    (apGN k b m l mu Zn N).length = N.gates.length + (addrGT m l mu).length := by
  simp [apGN]

omit [Fintype Zn] in
/-- **The node and address programs write the computed scratch**: on every clean
configuration, the gates `apGN` XOR the computed scratch `fN σ` of the selection `σ` into the
scratch. -/
theorem apGN_run (N : NodeProg m mu Zn) (hN : N.OK) (c : Cfg ((TSel m l m) ⊕ PR4 k)) :
    cfgRun (apGN k b m l mu Zn N) (Sum.elim c (fun _ => false)) =
      xorF (PR := PR4 k) (Z := SZ4 k b) (fN N) (Sum.elim c (fun _ => false)) := by
  set z : Cfg (BWBN k b m l mu Zn) := Sum.elim c (fun _ => false) with hz
  set σ : Cfg (TSel m l m) := fun s => c (Sum.inl s) with hσ
  rw [apGN, cfgRun_append, cfgRun_map_toGate, cfgRun_map_toGate]
  -- the node program
  set z1 := crun (N.gates.map (CGate.map (eNode k b m l mu Zn))) z with hz1
  have hmap1 := crun_map (eNode k b m l mu Zn) (eNode k b m l mu Zn).injective N.gates z
  have hin1 : z ∘ eNode k b m l mu Zn = Sum.elim (fun j => σ (uT m l j)) (fun _ => false) := by
    funext w
    rcases w with j | i | zz <;> rfl
  rw [hin1, hN.run] at hmap1
  have hz1_node : ∀ i, z1 (Sum.inr (Sum.inl (Sum.inl (Sum.inl i)))) = nodeOf N σ i := by
    intro i
    have := congrFun hmap1 (Sum.inr (Sum.inl i))
    exact this
  have hz1_nsc : ∀ zz, z1 (Sum.inr (Sum.inl (Sum.inl (Sum.inr zz)))) = false := by
    intro zz
    have := congrFun hmap1 (Sum.inr (Sum.inr zz))
    exact this
  have hz1_out : ∀ w, (∀ a, eNode k b m l mu Zn a ≠ w) → z1 w = z w :=
    fun w hw => crun_map_of_not_mem _ _ _ _ hw
  have hz1_sel : ∀ s, z1 (Sum.inl (Sum.inl s)) = σ s := by
    intro s
    by_cases h : ∃ j, uT m l j = s
    · obtain ⟨j, rfl⟩ := h
      have := congrFun hmap1 (Sum.inl j)
      exact this
    · push Not at h
      rw [hz1_out _ (fun a => by
        rcases a with j | i | zz
        · simp only [eNode, eNodeFun, Function.Embedding.coeFn_mk, ne_eq, Sum.inl.injEq]
          exact h j
        · simp [eNode, eNodeFun]
        · simp [eNode, eNodeFun])]
      rfl
  -- the address program
  have hmap2 := crun_map (eAddr k b m l mu Zn) (eAddr k b m l mu Zn).injective (addrGT m l mu) z1
  have hin2 : z1 ∘ eAddr k b m l mu Zn = cfgOf (xIn N σ) (0 : RO (aLayN m mu) →
      BitVec (aLayN m mu).w) := by
    funext w
    rcases w with (s | i) | cw
    · change z1 (Sum.inl (Sum.inl s)) = σ s
      exact hz1_sel s
    · change z1 (Sum.inr (Sum.inl (Sum.inl (Sum.inl i)))) = nodeOf N σ i
      exact hz1_node i
    · change z1 (Sum.inr (Sum.inl (Sum.inr cw))) = cfgOf (xIn N σ) 0 (Sum.inr cw)
      rw [hz1_out _ (fun a => by rcases a with j | i | zz <;> simp [eNode, eNodeFun])]
      rcases cw with _ | _ | _ | ⟨r, i⟩ <;> simp [hz, cfgOf]
  rw [hin2] at hmap2
  have hreg : crun (addrGT m l mu) (cfgOf (xIn N σ) 0) = cfgOf (xIn N σ) (regsT N σ) :=
    crun_addrGN _ _ _ _
  rw [hreg] at hmap2
  have hnotA : ∀ w : BWBN k b m l mu Zn, (∀ a, eAddr k b m l mu Zn a ≠ w) →
      crun ((addrGT m l mu).map (CGate.map (eAddr k b m l mu Zn))) z1 w = z1 w :=
    fun w hw => crun_map_of_not_mem _ _ _ _ hw
  funext w
  rcases w with (s | p) | (((i | zz) | cw) | t)
  · have := congrFun hmap2 (Sum.inl (Sum.inl s))
    exact this
  · rw [hnotA _ (fun a h => by rcases a with (s | i) | c <;> cases h)]
    rw [hz1_out _ (fun a h => by rcases a with j | i | zz <;> cases h)]
    rfl
  · have := congrFun hmap2 (Sum.inl (Sum.inr i))
    refine this.trans ?_
    change nodeOf N σ i = (false ^^ fN N σ (Sum.inl (Sum.inl i)))
    rw [Bool.false_xor]
    rfl
  · rw [hnotA _ (fun a h => by rcases a with (s | i) | c <;> cases h), hz1_nsc zz]
    change false = (false ^^ fN N σ (Sum.inl (Sum.inr zz)))
    rfl
  · have := congrFun hmap2 (Sum.inr cw)
    refine this.trans ?_
    change cfgOf (xIn N σ) (regsT N σ) (Sum.inr cw) = (false ^^ fN N σ (Sum.inr cw))
    rw [Bool.false_xor]
    rfl
  · rw [hnotA _ (fun a h => by rcases a with (s | i) | c <;> cases h)]
    rw [hz1_out _ (fun a h => by rcases a with j | i | zz <;> cases h)]
    rfl

end Prog

/-! ### The operations -/

section Ops

variable {Zn : Type} [Fintype Zn] [DecidableEq Zn]

/-- **The intermediate operation**: the compute circuit `computeV4` with every primitive call also
reading the data address bits, the orientation wire and the decoder `decO` on `inpBN`. -/
def ndAN (k : ℕ) (L : Lay) (m mu nd : ℕ) (hnd : nd ≤ mu + m) (Zn : Type) (κ ρ : ℝ) :
    NativeOp (LabW m L.lq ⊕ CtxN m mu Zn) (PR4 k) (SZ4 k L.b) (Fin nd ⊕ PY k L.b) Query :=
  slotOpR (addrBitN m mu nd hnd Zn) (computeV4 k L.b m L.lq) (oW k)
    (decO (inpBN k L m mu Zn) κ ρ)

/-- **The branch operation for computed nodes**: the node program and the address program, then
the compute circuit of the intermediate operation on the reassociated wires; the orientation
wire and the decoder on `inpBBN`. -/
def odeOpN (k : ℕ) (L : Lay) (m mu nd : ℕ) (hnd : nd ≤ mu + m) (N : NodeProg m mu Zn)
    (κ ρ : ℝ) :
    NativeOp (TSel m L.lq m) (PR4 k) (ZaN m mu Zn ⊕ SZ4 k L.b) (Fin nd ⊕ PY k L.b) Query where
  V := nGatesOf (apGN k L.b m L.lq mu Zn N) ++ (ndAN k L m mu nd hnd Zn κ ρ).V.map (NInstr.map reW)
  o := oW k
  dec := decO (inpBBN k L m mu Zn) κ ρ

/-- **The angle arithmetic** of the branch operation: the released arithmetic on `inpBBN`. -/
def odeArN (k : ℕ) (L : Lay) (m mu : ℕ) (Zn : Type) (κ ζ : ℝ) :
    Arith (BWBN k L.b m L.lq mu Zn) :=
  odeArith (inpBBN k L m mu Zn) κ ζ

omit [Fintype Zn] in
/-- **The arithmetic hypothesis** of the branch operation (the released `odeArith_ok`). -/
theorem odeArN_ok (k : ℕ) (L : Lay) (m mu nd : ℕ) (hnd : nd ≤ mu + m) (N : NodeProg m mu Zn)
    (hL : L.OK) (κ ρ ζc ζ : ℝ) (hκ : 0 < κ) (hζc : 0 < ζc) (hζc1 : ζc ≤ 1)
    (hρ : |ρ - 1| ≤ 1 / 2) (hζ : ζc + 2 * |ρ - 1| ≤ ζ) :
    ArithOK (odeArN k L m mu Zn κ ζc) (Sum.inl (Sum.inr (odeOpN k L m mu nd hnd N κ ρ).o))
      (odeOpN k L m mu nd hnd N κ ρ).dec ζ :=
  odeArith_ok (inpBBN k L m mu Zn) hL _ (inpBBN_avoids k L m mu Zn) κ ρ ζc ζ hκ hζc hζc1 hρ hζ

omit [Fintype Zn] in
/-- The branch operation is public: its compute circuit is valid and the decoder does not read
the orientation wire. -/
theorem odeOpN_public (k : ℕ) (L : Lay) (m mu nd : ℕ) (hnd : nd ≤ mu + m)
    (N : NodeProg m mu Zn) (hN : N.OK) (κ ρ : ℝ) : (odeOpN k L m mu nd hnd N κ ρ).Public where
  valid := by
    intro i hi
    simp only [odeOpN, List.mem_append] at hi
    rcases hi with hi | hi
    · exact valid_nGatesOf _ (apGN_ok N hN) i hi
    · exact valid_map_list reW _ (valid_slotR (addrBitN m mu nd hnd Zn) _
        (computeV4_valid k L.b m L.lq)) i hi
  dec_indep x v := decO_update (inpBBN k L m mu Zn) (inpBBN_avoids k L m mu Zn) κ ρ x v

omit [Fintype Zn] [DecidableEq Zn] in
/-- **The gates of the compute circuit**: the node program, the address program and the
`28 k + 2` gates of the constant-coefficient circuit. -/
theorem odeOpN_nGates (k : ℕ) (L : Lay) (m mu nd : ℕ) (hnd : nd ≤ mu + m)
    (N : NodeProg m mu Zn) (κ ρ : ℝ) :
    nGatesN (odeOpN k L m mu nd hnd N κ ρ).V =
      N.gates.length + (addrGT m L.lq mu).length + (28 * k + 2) := by
  change nGatesN (nGatesOf (apGN k L.b m L.lq mu Zn N) ++ ((computeV4 k L.b m L.lq).map
    (slotInstrR (addrBitN m mu nd hnd Zn))).map (NInstr.map reW)) = _
  rw [nGatesN_append, nGatesN_nGatesOf, nGatesN_map, nGatesN_slotR, computeV4_nGates,
    length_apGN]

omit [Fintype Zn] [DecidableEq Zn] in
/-- The compute circuit makes two calls of each oracle, as the constant-coefficient one. -/
theorem odeOpN_nCalls (k : ℕ) (L : Lay) (m mu nd : ℕ) (hnd : nd ≤ mu + m)
    (N : NodeProg m mu Zn) (κ ρ : ℝ) (p : Query → Bool) :
    nCallsN p (odeOpN k L m mu nd hnd N κ ρ).V = 2 * (if p Query.rowLocation then 1 else 0) +
      2 * (if p Query.columnLocation then 1 else 0) + 2 * (if p Query.value then 1 else 0) := by
  change nCallsN p (nGatesOf (apGN k L.b m L.lq mu Zn N) ++ ((computeV4 k L.b m L.lq).map
    (slotInstrR (addrBitN m mu nd hnd Zn))).map (NInstr.map reW)) = _
  rw [nCallsN_append, nCallsN_nGatesOf, nCallsN_map, nCallsN_slotR, computeV4_nCalls, zero_add]

/-- The address program has at most `13 (μ + m + 14)(m + 5)` gates. -/
theorem length_addrGT (m l mu : ℕ) : (addrGT m l mu).length ≤ 13 * (mu + m + 14) * (m + 5) :=
  length_addrGN _ _ _

end Ops

end

end SparseHamiltonian.GateBinaryNodes
