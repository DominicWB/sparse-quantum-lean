import GateEfficientBinaryODE.Arith
import GateEfficientBinaryODE.Qubit
import GateEfficientNative.ODE.Constant

/-!
# The compute circuit of the four-sector private operation

The native private operation of the dissipative solver acts on the label wires of the solver
(`LabW`: the source sector `ini`, the node word, the LCHS word), the private register
`PR4 k` (orientation, tag, part, the two indices) and scratch (`SZ4`): a dummy edge register,
the row and the column reference registers and two value registers.

The public compute circuit (`computeV4`)

1. writes the images of the all-zero edge under the row and the column location oracle into the
   reference registers (one call each);
2. XORs the orientation into the tag wire, applies the row location oracle to the index wires
   when the tag wire is `0` and the column location oracle when it is `1` (the controlled-call
   gadgets of `GateEfficientBinary`, one call each), and XORs the orientation back: the row
   oracle acts exactly when the orientation and the tag agree;
3. XORs the stored entry of the located edge `(i, j)` into the first value register and the
   stored entry of the transposed edge `(j, i)` into the second (two value calls, the second
   with the two indices exchanged).

The decoder (`odeOp`) is `decO` of `Arith` on the input wiring `inp4`. The circuit consists of
valid instructions (`computeV4_valid`), makes two calls of each oracle (`computeV4_nCalls`) and
has `28 k + 2` elementary gates (`computeV4_nGates`); the decoder does not read the orientation
wire (`odeOp_public`).
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateBinaryODE

noncomputable section
open SparseHamiltonian.GateBinary SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
open NativeSparseBlockEncoding (Query)

/-! ### Wires -/

/-- The scratch wires: a dummy edge register, the row and the column reference registers, and the
two value registers. -/
abbrev SZ4 (k b : ℕ) := ((EW k ⊕ EW k) ⊕ EW k) ⊕ (VW b ⊕ VW b)

/-- The base wires of the private operation: label wires, private register, scratch. -/
abbrev BW4 (k b kq lq : ℕ) := NB (LabW kq lq) (PR4 k) (SZ4 k b)

section Wires

variable {k b kq lq : ℕ}

/-- The orientation wire. -/
def oB4 : BW4 k b kq lq := .inl (.inr (oW k))

/-- The tag wire. -/
def tB4 : BW4 k b kq lq := .inl (.inr (tW k))

/-- The part wire. -/
def pB4 : BW4 k b kq lq := .inl (.inr (pW k))

/-- A label wire. -/
def lB4 (s : LabW kq lq) : BW4 k b kq lq := .inl (.inl s)

/-- The index wires. -/
def xB4 (e : EW k) : BW4 k b kq lq := .inl (.inr (ix4 k e))

/-- The exchange of the two indices of an edge register. -/
def swE : EW k → EW k
  | .inl j => .inr j
  | .inr j => .inl j

@[simp] theorem swE_swE (e : EW k) : swE (swE e) = e := by
  rcases e with j | j <;> rfl

theorem swE_injective : Function.Injective (swE (k := k)) := by
  intro e e' h
  rw [← swE_swE e, h, swE_swE]

/-- The dummy register. -/
def dm4 (e : EW k) : BW4 k b kq lq := .inr (.inl (.inl (.inl e)))

/-- The row reference register. -/
def rr4 (e : EW k) : BW4 k b kq lq := .inr (.inl (.inl (.inr e)))

/-- The column reference register. -/
def rc4 (e : EW k) : BW4 k b kq lq := .inr (.inl (.inr e))

/-- The first value register. -/
def v14 (v : VW b) : BW4 k b kq lq := .inr (.inr (.inl v))

/-- The second value register. -/
def v24 (v : VW b) : BW4 k b kq lq := .inr (.inr (.inr v))

theorem xB4_injective : Function.Injective (xB4 (k := k) (b := b) (kq := kq) (lq := lq)) := by
  intro e e' h
  exact ix4_injective k (Sum.inr_injective (Sum.inl_injective h))

theorem dm4_injective : Function.Injective (dm4 (k := k) (b := b) (kq := kq) (lq := lq)) := by
  intro e e' h
  simpa [dm4] using h

theorem rr4_injective : Function.Injective (rr4 (k := k) (b := b) (kq := kq) (lq := lq)) := by
  intro e e' h
  simpa [rr4] using h

theorem rc4_injective : Function.Injective (rc4 (k := k) (b := b) (kq := kq) (lq := lq)) := by
  intro e e' h
  simpa [rc4] using h

theorem v14_injective : Function.Injective (v14 (k := k) (b := b) (kq := kq) (lq := lq)) := by
  intro v v' h
  simpa [v14] using h

theorem v24_injective : Function.Injective (v24 (k := k) (b := b) (kq := kq) (lq := lq)) := by
  intro v v' h
  simpa [v24] using h

@[simp] theorem xB4_ne_oB4 (e : EW k) : xB4 (b := b) (kq := kq) (lq := lq) e ≠ oB4 := by
  simp [xB4, oB4]

@[simp] theorem xB4_ne_tB4 (e : EW k) : xB4 (b := b) (kq := kq) (lq := lq) e ≠ tB4 := by
  simp [xB4, tB4]

@[simp] theorem xB4_ne_pB4 (e : EW k) : xB4 (b := b) (kq := kq) (lq := lq) e ≠ pB4 := by
  simp [xB4, pB4]

@[simp] theorem xB4_ne_lB4 (e : EW k) (s : LabW kq lq) : xB4 (b := b) e ≠ lB4 s := by
  simp [xB4, lB4]

@[simp] theorem xB4_ne_dm4 (e e' : EW k) : xB4 (b := b) (kq := kq) (lq := lq) e ≠ dm4 e' := by
  simp [xB4, dm4]

@[simp] theorem xB4_ne_rr4 (e e' : EW k) : xB4 (b := b) (kq := kq) (lq := lq) e ≠ rr4 e' := by
  simp [xB4, rr4]

@[simp] theorem xB4_ne_rc4 (e e' : EW k) : xB4 (b := b) (kq := kq) (lq := lq) e ≠ rc4 e' := by
  simp [xB4, rc4]

@[simp] theorem xB4_ne_v14 (e : EW k) (v : VW b) : xB4 (kq := kq) (lq := lq) e ≠ v14 v := by
  simp [xB4, v14]

@[simp] theorem xB4_ne_v24 (e : EW k) (v : VW b) : xB4 (kq := kq) (lq := lq) e ≠ v24 v := by
  simp [xB4, v24]

@[simp] theorem dm4_ne_tB4 (e : EW k) : dm4 (b := b) (kq := kq) (lq := lq) e ≠ tB4 := by
  simp [dm4, tB4]

@[simp] theorem dm4_ne_oB4 (e : EW k) : dm4 (b := b) (kq := kq) (lq := lq) e ≠ oB4 := by
  simp [dm4, oB4]

@[simp] theorem dm4_ne_rr4 (e e' : EW k) : dm4 (b := b) (kq := kq) (lq := lq) e ≠ rr4 e' := by
  simp [dm4, rr4]

@[simp] theorem dm4_ne_rc4 (e e' : EW k) : dm4 (b := b) (kq := kq) (lq := lq) e ≠ rc4 e' := by
  simp [dm4, rc4]

@[simp] theorem rr4_ne_rc4 (e e' : EW k) : rr4 (b := b) (kq := kq) (lq := lq) e ≠ rc4 e' := by
  simp [rr4, rc4]

@[simp] theorem rr4_ne_v14 (e : EW k) (v : VW b) : rr4 (kq := kq) (lq := lq) e ≠ v14 v := by
  simp [rr4, v14]

@[simp] theorem rc4_ne_v14 (e : EW k) (v : VW b) : rc4 (kq := kq) (lq := lq) e ≠ v14 v := by
  simp [rc4, v14]

@[simp] theorem oB4_ne_tB4 : oB4 (k := k) (b := b) (kq := kq) (lq := lq) ≠ tB4 := by
  simp [oB4, tB4]

/-- The positions of a call on the row reference register (and the first value register). -/
def posRR4 : PY k b ↪ BW4 k b kq lq :=
  ⟨Sum.elim rr4 v14, rr4_injective.sumElim v14_injective rr4_ne_v14⟩

/-- The positions of a call on the column reference register (and the first value register). -/
def posRC4 : PY k b ↪ BW4 k b kq lq :=
  ⟨Sum.elim rc4 v14, rc4_injective.sumElim v14_injective rc4_ne_v14⟩

/-- The positions of a call on the index wires and the first value register. -/
def posT4 : PY k b ↪ BW4 k b kq lq :=
  ⟨Sum.elim xB4 v14, xB4_injective.sumElim v14_injective xB4_ne_v14⟩

/-- The positions of a call on the exchanged index wires and the second value register. -/
def posS4 : PY k b ↪ BW4 k b kq lq :=
  ⟨Sum.elim (xB4 ∘ swE) v24, (xB4_injective.comp swE_injective).sumElim v24_injective
    (fun e v => xB4_ne_v24 (swE e) v)⟩

end Wires

/-! ### The compute circuit -/

section Circuit

variable (k b kq lq : ℕ)

/-- The orientation XOR-ed into the tag wire. -/
def cnot4 : Gate (BW4 k b kq lq) := ⟨[(oB4, true)], tB4, pauliX⟩

/-- The locator block: the tag XOR, the two controlled location calls, the tag XOR again. -/
def locC : List (NInstr (BW4 k b kq lq) (PY k b) Query) :=
  [NInstr.gate (cnot4 k b kq lq)] ++
    gadget tB4 false xB4 dm4 rr4 [NInstr.call Query.rowLocation false posT4] ++
    gadget tB4 true xB4 dm4 rc4 [NInstr.call Query.columnLocation false posT4] ++
    [NInstr.gate (cnot4 k b kq lq)]

/-- **The compute circuit** of the four-sector private operation. -/
def computeV4 : List (NInstr (BW4 k b kq lq) (PY k b) Query) :=
  [NInstr.call Query.rowLocation false posRR4, NInstr.call Query.columnLocation false posRC4] ++
    locC k b kq lq ++
    [NInstr.call Query.value false posT4, NInstr.call Query.value false posS4]

theorem gateOK_cnot4 : GateOK 3 (cnot4 k b kq lq) := by
  refine ⟨by simp [cnot4], ?_, pauliX_unitary⟩
  intro c hc
  simp only [cnot4, List.mem_cons, List.not_mem_nil, or_false] at hc
  subst hc
  exact oB4_ne_tB4

theorem computeV4_valid : ∀ i ∈ computeV4 k b kq lq, i.Valid := by
  have hc : ∀ (j : Query) (pos : PY k b ↪ BW4 k b kq lq),
      ∀ i ∈ [NInstr.call (V := BW4 k b kq lq) j false pos], i.Valid := by
    intro j pos i hi
    rw [List.mem_singleton] at hi
    subst hi
    trivial
  intro i hi
  simp only [computeV4, locC, List.mem_append] at hi
  rcases hi with (h | (((h | h) | h) | h)) | h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> trivial
  · simp only [List.mem_singleton] at h
    subst h
    exact gateOK_cnot4 k b kq lq
  · exact gadget_valid _ _ _ _ _ xB4_ne_dm4 xB4_ne_rr4 xB4_ne_tB4 dm4_ne_tB4 _ (hc _ _) i h
  · exact gadget_valid _ _ _ _ _ xB4_ne_dm4 xB4_ne_rc4 xB4_ne_tB4 dm4_ne_tB4 _ (hc _ _) i h
  · simp only [List.mem_singleton] at h
    subst h
    exact gateOK_cnot4 k b kq lq
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> trivial

theorem computeV4_nGates : nGatesN (computeV4 k b kq lq) = 28 * k + 2 := by
  simp only [computeV4, locC, nGatesN_append, gadget_nGates, Fintype.card_sum, Fintype.card_fin]
  simp [nGatesN, NInstr.isGate]
  ring

theorem computeV4_nCalls (p : Query → Bool) :
    nCallsN p (computeV4 k b kq lq) = 2 * (if p Query.rowLocation then 1 else 0) +
      2 * (if p Query.columnLocation then 1 else 0) + 2 * (if p Query.value then 1 else 0) := by
  simp only [computeV4, locC, nCallsN_append, gadget_nCalls]
  cases h1 : p Query.rowLocation <;> cases h2 : p Query.columnLocation <;>
    cases h3 : p Query.value <;> simp [nCallsN, NInstr.isCall, h1, h2, h3]

end Circuit

/-! ### The native private operation -/

section Op

variable {k : ℕ}

/-- The input wiring of the arithmetic: the source sector, the node word, the LCHS word, the part
and the tag wire, and the two value registers. -/
def inp4 (k : ℕ) (L : Lay) : Inp (BW4 k L.b L.kq L.lq) L where
  ini := lB4 (.inl (.inl ()))
  u j := lB4 (.inl (.inr j))
  wd j := lB4 (.inr j)
  pt := pB4
  tg := tB4
  x1 i := v14 (.inl i)
  y1 i := v14 (.inr i)
  x2 i := v24 (.inl i)
  y2 i := v24 (.inr i)

theorem inp4_avoids (k : ℕ) (L : Lay) : (inp4 k L).Avoids oB4 where
  ini := by simp [inp4, lB4, oB4]
  u j := by simp [inp4, lB4, oB4]
  wd j := by simp [inp4, lB4, oB4]
  pt := by simp [inp4, pB4, oB4, Ne.symm (oW_ne_pW (k := k))]
  tg := by simp [inp4, tB4, oB4, Ne.symm (oW_ne_tW (k := k))]
  x1 i := by simp [inp4, v14, oB4]
  y1 i := by simp [inp4, v14, oB4]
  x2 i := by simp [inp4, v24, oB4]
  y2 i := by simp [inp4, v24, oB4]

/-- **The native private operation**: the compute circuit, the orientation wire and the decoder
`κ ρ_x Z'` of `Arith`. -/
def odeOp (k : ℕ) (L : Lay) (κ ρ : ℝ) :
    NativeOp (LabW L.kq L.lq) (PR4 k) (SZ4 k L.b) (PY k L.b) Query where
  V := computeV4 k L.b L.kq L.lq
  o := oW k
  dec := decO (inp4 k L) κ ρ

/-- The compute circuit is valid and the decoder does not read the orientation wire. -/
theorem odeOp_public (k : ℕ) (L : Lay) (κ ρ : ℝ) : (odeOp k L κ ρ).Public where
  valid := computeV4_valid k L.b L.kq L.lq
  dec_indep x v := by
    have ho := inp4_avoids k L
    change decO (inp4 k L) κ ρ (Function.update x oB4 v) = decO (inp4 k L) κ ρ x
    unfold decO
    rw [Inp.zx_update _ x ho v, Inp.zy_update _ x ho v, Function.update_of_ne ho.pt]

/-- The arithmetic of the native private operation. -/
def odeAr (k : ℕ) (L : Lay) (κ ζ : ℝ) : Arith (NB (LabW L.kq L.lq) (PR4 k) (SZ4 k L.b)) :=
  odeArith (inp4 k L) κ ζ

/-- **The arithmetic hypothesis** of the native private operation. -/
theorem odeAr_ok (k : ℕ) (L : Lay) (hL : L.OK) (κ ρ ζc ζ : ℝ) (hκ : 0 < κ) (hζc : 0 < ζc)
    (hζc1 : ζc ≤ 1) (hρ : |ρ - 1| ≤ 1 / 2) (hζ : ζc + 2 * |ρ - 1| ≤ ζ) :
    ArithOK (odeAr k L κ ζc) (Sum.inl (Sum.inr (odeOp k L κ ρ).o)) (odeOp k L κ ρ).dec ζ :=
  odeArith_ok (inp4 k L) hL oB4 (inp4_avoids k L) κ ρ ζc ζ hκ hζc hζc1 hρ hζ

end Op

end

end SparseHamiltonian.GateBinaryODE
