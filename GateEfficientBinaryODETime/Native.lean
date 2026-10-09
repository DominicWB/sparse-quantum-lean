import GateEfficientBinaryODETime.Slot
import GateEfficientBinaryODETime.Grid
import GateEfficientBinaryODE.Decoder
import GateEfficientBinaryTime.Oracles

/-!
# The label- and slot-selected native private operation

The private operation of the time-dependent solver (Lemma `ode:lem:gate-select`, with the tagged
representation of Lemma `ode:lem:tags` at every sample) at the joint label `z = ((ini, u), w)`
and the time slot `r` is the four-sector Cayley action of the sample `D.matrix (x, r)` at the
LCHS node of `w` and the Cayley parameter `γ [start ≤ r]`, `start = (ini ? u : 0)` (`privFamT`).
Its native form (Theorem `ode:thm:gates`):

* the compute circuit is the constant-coefficient circuit `computeV4` with every primitive call
  also reading the `m` slot wires (`slotInstr2`), for the coherent sampled-time primitive oracles
  `GateBinary.primsT`; the decoder is `decT` on the wiring `inpT4` (`odeOpT`, public:
  `odeOpT_public`);
* the arithmetic is `arithT` on the same wiring (`odeArT`, `odeArT_ok`);
* `decOK_T`: at every slot word `w`, the decoder read at `w` satisfies the decoder hypothesis
  `GateBinaryODE.DecOK` of the sample `wordEquivFin m w`, with the LCHS node `nodeW` and the
  Cayley parameter `γ [start ≤ w]` of every label;
* `nativeOK_T`: the native identity of the label- and slot-selected family `tlabFam privFamT`,
  from the released `GateBinaryODE.nativeOK4` at every slot word and the transfer
  `nativeOK_slot2`.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateBinaryODETime

noncomputable section
open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
open SparseHamiltonian.GateBinary SparseHamiltonian.GateBinaryODE SparseHamiltonian.OracleCircuit
open SparseHamiltonian.GateODE (Label)
open SparseHamiltonian.GateODE.Time (TParams)
open SparseHamiltonian.GatePointerEncoding (wordEquivFin wordValue)
open NativeSparseBlockEncoding (Data Query)
open scoped InnerProduct

/-! ### Wires and the native operation -/

/-- The base wires of the time-dependent private operation: the label and slot wires, the private
register and the scratch. -/
abbrev BWT (k b m l : ℕ) := NB (TSel m l m) (PR4 k) (SZ4 k b)

/-- **The input wiring** of the time-dependent arithmetic: the source sector bit and the node word
of the label wires and the slot wires (comparator), the LCHS word, the part and the tag wire,
and the two value registers. -/
def inpT4 (k : ℕ) (L : Lay) (m : ℕ) : InpT (BWT k L.b m L.lq) L m where
  ini := baseW2 (lB4 (.inl (.inl ())))
  sl i := selW2 i
  u j := baseW2 (lB4 (.inl (.inr j)))
  wd j := baseW2 (lB4 (.inr j))
  pt := baseW2 pB4
  tg := baseW2 tB4
  x1 i := baseW2 (v14 (.inl i))
  y1 i := baseW2 (v14 (.inr i))
  x2 i := baseW2 (v24 (.inl i))
  y2 i := baseW2 (v24 (.inr i))

theorem inpT4_avoids (k : ℕ) (L : Lay) (m : ℕ) :
    (inpT4 k L m).Avoids (Sum.inl (Sum.inr (oW k))) where
  ini := by simp [inpT4, baseW2, lB4]
  sl i := by simp [inpT4, selW2]
  u j := by simp [inpT4, baseW2, lB4]
  wd j := by simp [inpT4, baseW2, lB4]
  pt := by simp [inpT4, baseW2, pB4, Ne.symm (oW_ne_pW (k := k))]
  tg := by simp [inpT4, baseW2, tB4, Ne.symm (oW_ne_tW (k := k))]
  x1 i := by simp [inpT4, baseW2, v14]
  y1 i := by simp [inpT4, baseW2, v14]
  x2 i := by simp [inpT4, baseW2, v24]
  y2 i := by simp [inpT4, baseW2, v24]

/-- **The label- and slot-selected native private operation**: the compute circuit `computeV4`
with every call also reading the slot wires, the orientation wire and the decoder `decT` with
scale `κ` and step factor `ρ_L`. -/
def odeOpT (k : ℕ) (L : Lay) (m : ℕ) (κ ρ : ℝ) :
    NativeOp (TSel m L.lq m) (PR4 k) (SZ4 k L.b) (Fin m ⊕ PY k L.b) Query :=
  slotOp2 (computeV4 k L.b m L.lq) (oW k) (decT (inpT4 k L m) κ ρ)

/-- The compute circuit is valid and the decoder does not read the orientation wire. -/
theorem odeOpT_public (k : ℕ) (L : Lay) (m : ℕ) (κ ρ : ℝ) : (odeOpT k L m κ ρ).Public :=
  slotOp2_public _ (computeV4_valid k L.b m L.lq) _ _
    (fun x b => decT_update _ (inpT4_avoids k L m) κ ρ x b)

/-- The arithmetic of the time-dependent private operation. -/
def odeArT (k : ℕ) (L : Lay) (m : ℕ) (κ ζ : ℝ) : Arith (BWT k L.b m L.lq) :=
  arithT (inpT4 k L m) κ ζ

/-- **The arithmetic hypothesis** of the time-dependent private operation. -/
theorem odeArT_ok (k : ℕ) (L : Lay) (m : ℕ) (hL : L.OK) (κ ρ ζc ζ : ℝ) (hκ : 0 < κ)
    (hζc : 0 < ζc) (hζc1 : ζc ≤ 1) (hρ : |ρ - 1| ≤ 1 / 2) (hζ : ζc + 2 * |ρ - 1| ≤ ζ) :
    ArithOK (odeArT k L m κ ζc) (Sum.inl (Sum.inr (odeOpT k L m κ ρ).o))
      (odeOpT k L m κ ρ).dec ζ :=
  arithT_ok (inpT4 k L m) hL _ (inpT4_avoids k L m) κ ρ ζc ζ hκ hζc hζc1 hρ hζ

/-- The compute circuit has the `28 k + 2` gates of the constant-coefficient one. -/
theorem odeOpT_nGates (k : ℕ) (L : Lay) (m : ℕ) (κ ρ : ℝ) :
    nGatesN (odeOpT k L m κ ρ).V = 28 * k + 2 := by
  change nGatesN ((computeV4 k L.b m L.lq).map slotInstr2) = _
  rw [nGatesN_slot2, computeV4_nGates]

/-- The compute circuit makes two calls of each oracle, as the constant-coefficient one. -/
theorem odeOpT_nCalls (k : ℕ) (L : Lay) (m : ℕ) (κ ρ : ℝ) (p : Query → Bool) :
    nCallsN p (odeOpT k L m κ ρ).V = 2 * (if p Query.rowLocation then 1 else 0) +
      2 * (if p Query.columnLocation then 1 else 0) + 2 * (if p Query.value then 1 else 0) := by
  change nCallsN p ((computeV4 k L.b m L.lq).map slotInstr2) = _
  rw [nCallsN_slot2, computeV4_nCalls]

/-! ### The decoder at every slot word -/

section Dec

variable {X n : Type*} [Fintype n] [DecidableEq n] {s k b : ℕ}

theorem twos_ext {m : ℕ} (L : Lay) (E : PW (BWT k L.b m L.lq) (cLay m) → Bool) (W : Cfg (VW L.b))
    (f : VW L.b → BW4 k L.b m L.lq)
    (hf : ∀ v, E (Sum.inl (baseW2 (f v))) = W v) (side : Bool) :
    twos (fun i : Fin L.b => (Sum.inl (baseW2 (f (if side then .inr i else .inl i))) :
        PW (BWT k L.b m L.lq) (cLay m))) E =
      twos (B := VW L.b) (fun i => if side then .inr i else .inl i) W := by
  unfold twos
  congr 2
  funext j
  split_ifs <;> simp [hf]

/-- **The decoder hypothesis at every slot word**: the decoder `decT` with scale `kapT` and step
factor `ρ_L`, read at the slot word `w`, takes after the compute circuit the value of the
label-selected edgewise gate of the sample `wordEquivFin m w`, with the LCHS node `nodeW` and the
Cayley parameter `γ [start ≤ w]` of every label. -/
theorem decOK_T (p : TParams) (D : Data (X × Fin (2 ^ p.m)) n (Cfg (VW b)) s)
    (en : Cfg (Fin k) ≃ n) (k0 : Fin s) (x : X) (c0 : ℝ) (hc0 : c0 ≠ 0)
    (hdec : ∀ e z, D.decode e z = (c0 : ℂ) * gauss z) (ρ γ : ℝ) (hρ : ρ ≠ 0) (F : ℕ)
    (hHn : hRound (gridP p) F ≠ 0) (w : Cfg (Fin p.m)) :
    DecOK D en k0 (x, wordEquivFin p.m w) (fun z => p.nodeW z.2)
      (fun z => γ * TimeDependentODE.mask (p.start z.1) (wordValue w)) ρ
      (atSlot2 (computeV4 k b p.m p.l) (oW k)
        (decT (inpT4 k (layT p b F) p.m) (kapT s c0 ρ γ F) (rhoL (gridP p) F)) w).dec := by
  intro c
  set xw := (x, wordEquivFin p.m w) with hxw
  set y := sigma4 D en k0 xw (Sum.elim c (fun _ => false)) with hy
  set J := inpT4 k (layT p b F) p.m with hJ
  set E := J.ext (glue2 w y) with hE
  have hEb : ∀ v : BW4 k b p.m p.l, E (Sum.inl (baseW2 v)) = y v :=
    fun v => glue2_apply_baseW2 w y v
  set d : Cfg (EW k) := fun e => c (Sum.inr (ix4 k e)) with hd
  have hij : phiE en d = ((phiE en d).1, (phiE en d).2) := rfl
  set i := (phiE en d).1 with hi
  set j := (phiE en d).2 with hj
  have hv1 : ∀ v : VW b, E (Sum.inl (baseW2 (v14 v : BW4 k b p.m p.l))) = D.table xw (i, j) v :=
    fun v => by
    rw [hEb, hy, sigma4_v14, ← hd, hij]
  have hv2 : ∀ v : VW b, E (Sum.inl (baseW2 (v24 v : BW4 k b p.m p.l))) = D.table xw (j, i) v :=
    fun v => by
    rw [hEb, hy, sigma4_v24]
    rfl
  have hlab : ∀ q, E (Sum.inl (baseW2 (Sum.inl q))) = c q := fun q => by
    rw [hEb]
    exact sigma4_inl D en k0 xw c q
  have hM1 : D.matrix xw i j = (c0 : ℂ) *
      (((twos (B := VW b) Sum.inl (D.table xw (i, j)) : ℤ) : ℂ)
        + ((twos (B := VW b) Sum.inr (D.table xw (i, j)) : ℤ) : ℂ) * Complex.I) := by
    rw [← D.decoded, hdec]
    rfl
  have hM2 : D.matrix xw j i = (c0 : ℂ) *
      (((twos (B := VW b) Sum.inl (D.table xw (j, i)) : ℤ) : ℂ)
        + ((twos (B := VW b) Sum.inr (D.table xw (j, i)) : ℤ) : ℂ) * Complex.I) := by
    rw [← D.decoded, hdec]
    rfl
  have hX1 : J.lift.X1 E = twos (B := VW b) Sum.inl (D.table xw (i, j)) :=
    twos_ext (layT p b F) E (D.table xw (i, j)) v14 hv1 false
  have hY1 : J.lift.Y1 E = twos (B := VW b) Sum.inr (D.table xw (i, j)) :=
    twos_ext (layT p b F) E (D.table xw (i, j)) v14 hv1 true
  have hX2 : J.lift.X2 E = twos (B := VW b) Sum.inl (D.table xw (j, i)) :=
    twos_ext (layT p b F) E (D.table xw (j, i)) v24 hv2 false
  have hY2 : J.lift.Y2 E = twos (B := VW b) Sum.inr (D.table xw (j, i)) :=
    twos_ext (layT p b F) E (D.table xw (j, i)) v24 hv2 true
  have hpt : E J.lift.pt = c (Sum.inr (pW k)) := hlab _
  have htg : E J.lift.tg = c (Sum.inr (tW k)) := hlab _
  have hV : J.lift.V E = wordValue (fun j => c (Sum.inl (Sum.inr j))) := by
    unfold Inp.V
    congr 1
    funext j
    exact hlab _
  have hdv : J.lift.dv E = if (if c (Sum.inl (Sum.inl (Sum.inl ()))) then
      wordValue (fun j => c (Sum.inl (Sum.inl (Sum.inr j)))) else 0) ≤ wordValue w then 1
      else 0 := by
    rw [hE, dv_lift]
    have h1 : glue2 w y J.ini = c (Sum.inl (Sum.inl (Sum.inl ()))) := by
      rw [show J.ini = baseW2 (lB4 (Sum.inl (Sum.inl ()))) from rfl, glue2_apply_baseW2]
      exact sigma4_inl D en k0 xw c _
    have h2 : (fun j => glue2 w y (J.u j)) = fun j => c (Sum.inl (Sum.inl (Sum.inr j))) := by
      funext j
      rw [show J.u j = baseW2 (lB4 (Sum.inl (Sum.inr j))) from rfl, glue2_apply_baseW2]
      exact sigma4_inl D en k0 xw c _
    have h3 : (fun j => glue2 w y (J.sl j)) = w := rfl
    rw [h1, h2, h3]
    rfl
  have hte : te en (fun v => c (Sum.inr v)) =
      if c (Sum.inr (tW k)) then Sum.inr (i, j) else Sum.inl (i, j) := by
    unfold te
    rw [← hij]
  have hkn : p.nodeW (labOfW fun s => c (Sum.inl s)).2 = ((J.lift.nv E : ℤ) : ℝ) *
      hStep (gridP p) := by
    rw [nodeWT_eq]
    unfold Inp.nv
    rw [hV]
    rfl
  have hγ : γ * TimeDependentODE.mask (p.start (labOfW fun s => c (Sum.inl s)).1) (wordValue w) =
      γ * (((J.lift.dv E : ℤ) : ℝ) / 2 ^ 0) := by
    rw [hdv, pow_zero, div_one]
    unfold TimeDependentODE.mask GateODE.Time.TParams.start labOfW
    split_ifs <;> simp
  show decO J.lift (kapT s c0 ρ γ F) (rhoL (gridP p) F) E = val4 D en xw
    (p.nodeW (labOfW fun s => c (Sum.inl s)).2) ρ
    (γ * TimeDependentODE.mask (p.start (labOfW fun s => c (Sum.inl s)).1) (wordValue w))
      fun v => c (Sum.inr v)
  unfold val4
  rw [hkn, hγ, hte, core_identity (D.matrix xw) i j c0 hc0 _ _ _ _ hM1 hM2]
  unfold decO Inp.zx Inp.zy Inp.ct Inp.mu Inp.ax Inp.ay
  rw [hX1, hY1, hX2, hY2, hpt, htg]
  have hHnR : (hRound (gridP p) F : ℝ) ≠ 0 := by exact_mod_cast hHn
  have hs := scale_eq γ (Real.sqrt (4 * s)) c0 ρ (hStep (gridP p))
    ((J.lift.dv E : ℤ) : ℝ) ((J.lift.nv E : ℤ) : ℝ) (hRound (gridP p) F : ℝ) 0 F hHnR hρ
    (c (Sum.inr (pW k)))
  change _ = ((γ * (((J.lift.dv E : ℤ) : ℝ) / 2 ^ 0) * Real.sqrt (4 * s) / ρ * c0 / 4 *
    (if c (Sum.inr (pW k)) = true then ((J.lift.nv E : ℤ) : ℝ) * hStep (gridP p) else 1) : ℝ) :
      ℂ) * _ * _
  rw [← hs]
  unfold kapT rhoL
  rw [zero_add]
  beta_reduce
  cases c (Sum.inr (pW k)) <;> cases c (Sum.inr (tW k)) <;>
    simp only [Bool.false_eq_true, if_false, if_true] <;> push_cast <;> ring

end Dec

/-! ### The native identity -/

section OK

variable {X n : Type*} [Fintype n] [DecidableEq n] {s k b : ℕ}

/-- **The label- and slot-selected private operation**: at the label `z` and the slot `r < 2^m`,
the lifted four-sector Cayley action of the sample of slot `r` at the LCHS node of `z` and the
Cayley parameter `γ [start ≤ r]`; the identity beyond the last slot. -/
def privFamT (p : TParams) (D : Data (X × Fin (2 ^ p.m)) n (Cfg (VW b)) s)
    (en : Cfg (Fin k) ≃ n) (x : X) (ρ γ : ℝ) (z : Label p.m p.l) (r : ℕ) :
    Reg (Fin (k + 3)) (Reg (Fin k) ℂ) →L[ℂ] Reg (Fin (k + 3)) (Reg (Fin k) ℂ) :=
  if h : r < 2 ^ p.m then
    elift4 en (act4 D (x, ⟨r, h⟩) (p.nodeW z.2) ρ (γ * TimeDependentODE.mask (p.start z.1) r))
  else 1

theorem privFamT_word (p : TParams) (D : Data (X × Fin (2 ^ p.m)) n (Cfg (VW b)) s)
    (en : Cfg (Fin k) ≃ n) (x : X) (ρ γ : ℝ) (z : Label p.m p.l) (w : Cfg (Fin p.m)) :
    privFamT p D en x ρ γ z (wordEquivFin p.m w) =
      elift4 en (act4 D (x, wordEquivFin p.m w) (p.nodeW z.2) ρ
        (γ * TimeDependentODE.mask (p.start z.1) (wordValue w))) := by
  rw [privFamT, dif_pos (wordEquivFin p.m w).isLt]
  rfl

theorem privFamT_isUnitary (p : TParams) (D : Data (X × Fin (2 ^ p.m)) n (Cfg (VW b)) s)
    (en : Cfg (Fin k) ≃ n) (x : X) (ρ γ : ℝ) (z : Label p.m p.l) (r : ℕ) :
    IsUnitary (privFamT p D en x ρ γ z r) := by
  unfold privFamT
  split_ifs
  · exact elift4_isUnitary _ (act4_unitary _ _ _ _ _)
  · exact isUnitary_one

/-- **The native identity** of the label- and slot-selected private operation: for the
time-indexed binary data, `V† R_val V` acts on clean scratch as the family `privFamT` selected by
the label and the slot wires. -/
theorem nativeOK_T (p : TParams) (D : Data (X × Fin (2 ^ p.m)) n (Cfg (VW b)) s)
    (en : Cfg (Fin k) ≃ n) (k0 : Fin s) (hk0 : D.slot k0 = zIdx en) (x : X) (c0 : ℝ)
    (hc0 : c0 ≠ 0) (hdec : ∀ e z, D.decode e z = (c0 : ℂ) * gauss z) (ρ γ : ℝ) (hρ : ρ ≠ 0)
    (F : ℕ) (hHn : hRound (gridP p) F ≠ 0) :
    NativeOK (primsT (R := ℂ) D en x)
      (odeOpT k (layT p b F) p.m (kapT s c0 ρ γ F) (rhoL (gridP p) F))
      (selOp (tlabFam (P := Reg (Fin k) ℂ) (privFamT p D en x ρ γ) false)) := by
  have hOK : ∀ w : Cfg (Fin p.m), NativeOK (prims (R := ℂ) D en (x, wordEquivFin p.m w))
      (atSlot2 (computeV4 k b p.m p.l) (oW k)
        (decT (inpT4 k (layT p b F) p.m) (kapT s c0 ρ γ F) (rhoL (gridP p) F)) w)
      (selOp (labFam (fun z => elift4 (R := ℂ) en (act4 D (x, wordEquivFin p.m w)
        (p.nodeW z.2) ρ (γ * TimeDependentODE.mask (p.start z.1) (wordValue w)))) false)) := by
    intro w
    exact nativeOK4 (kq := p.m) (lq := p.l) D en k0 hk0 (x, wordEquivFin p.m w)
      (fun z => p.nodeW z.2) (fun z => γ * TimeDependentODE.mask (p.start z.1) (wordValue w)) ρ
      _ rfl rfl
      (atSlot2_public _ (computeV4_valid k b p.m p.l) _ _
        (fun y v => decT_update _ (inpT4_avoids k (layT p b F) p.m) _ _ y v) w)
      (decOK_T p D en k0 x c0 hc0 hdec ρ γ hρ F hHn w)
  have h := nativeOK_slot2 (fun w => prims (R := ℂ) D en (x, wordEquivFin p.m w))
    (computeV4 k b p.m p.l) (oW k)
    (decT (inpT4 k (layT p b F) p.m) (kapT s c0 ρ γ F) (rhoL (gridP p) F))
    (fun w => labFam (fun z => elift4 (R := ℂ) en (act4 D (x, wordEquivFin p.m w)
      (p.nodeW z.2) ρ (γ * TimeDependentODE.mask (p.start z.1) (wordValue w)))) false) hOK
  have hfam : (fun y : Cfg (TSel p.m p.l p.m) =>
      labFam (fun z => elift4 (R := ℂ) en (act4 D (x, wordEquivFin p.m (fun i => y (Sum.inr i)))
        (p.nodeW z.2) ρ (γ * TimeDependentODE.mask (p.start z.1)
          (wordValue (fun i => y (Sum.inr i)))))) false (fun s => y (Sum.inl s))) =
      tlabFam (P := Reg (Fin k) ℂ) (privFamT p D en x ρ γ) false := by
    funext y
    simp only [labFam, tlabFam, GateODE.adjIf, SlotSim.adjT, Bool.false_eq_true, if_false]
    rw [privFamT_word]
  rw [← hfam]
  exact h

end OK

end

end SparseHamiltonian.GateBinaryODETime
