import GateEfficientBinaryNodes.NodeNative

/-!
# The native identity of the private operation for computed nodes

* `layN`, `kapN`: the integer layout of the released arithmetic with `μ` duration bits on the
  LCHS grid of the time-dependent solver, and the decoder scale
  `κ = γ √(4s) c₀ / (2^(μ + F + 10) ρ)`; `layN_ok`: the layout is admissible.
* `dvWN`, `addrCN`: the duration word and the data address read from a context word.
* `decOK_N`: at every context word the decoder satisfies `GateBinaryODE.DecOK` of the sample at
  the data address of the context, with the LCHS node of each label and the Cayley parameter
  `γ dvWN / 2^μ` of the context.
* `startWN`, `addrNN`, `addrFN`, `privFamN`: the start word `ν' = (ini ? word u : 0)`, the
  address `A = 2^m ν' + r (2^μ - ν')`, the data grid point `⌊A / 2^(μ+m-nd)⌋` and the label- and
  slot-selected private family (identity beyond the last slot).
* `nativeOK_N`: **the native identity** of the branch operation for the family `privFamN`.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateBinaryNodes

noncomputable section
open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
open SparseHamiltonian.GateBinary SparseHamiltonian.GateBinaryODE SparseHamiltonian.OracleCircuit
open SparseHamiltonian.GateBinaryODETime (baseW2 selW2 glue2 atSlot2 glue2_apply_baseW2
  atSlot2_public gridP nodeWT_eq layT layT_ok)
open SparseHamiltonian.GateBinarySelect (slotOpR reW xorF mapInp decO_update iniT uT slT
  nativeOK_slotR nativeOK_computed classical_hAP wordValue_testBit wordValue_congr)
open SparseHamiltonian.GateODE (Label)
open SparseHamiltonian.GateODE.Time (TParams)
open SparseHamiltonian.GatePointerEncoding (wordEquivFin wordValue)
open NativeSparseBlockEncoding (Data Query)
open scoped InnerProduct

/-! ### The layout and the decoder scale -/

/-- **The integer layout** of the arithmetic: the released layout of the LCHS grid of the
time-dependent solver with `μ` duration bits. -/
abbrev layN (p : TParams) (mu b F : ℕ) : Lay :=
  ⟨b, mu, p.l, GateODE.AnalyticLCHS.halfCount (p.T * p.lamD) p.ratio p.acc, p.J, F,
    hRound (gridP p) F⟩

theorem layN_kq (p : TParams) (mu b F : ℕ) : (layN p mu b F).kq = mu := rfl

/-- The layout is admissible. -/
theorem layN_ok (p : TParams) (mu b F : ℕ) (hb : 0 < b) (hg : 1 ≤ p.g) (hε : 0 < p.ε)
    (hε1 : p.ε ≤ 1) (hTD : 0 ≤ p.T * p.lamD) : (layN p mu b F).OK := by
  have h := layT_ok p b F hb hg hε hε1 hTD
  exact ⟨h.b_pos, h.J_le, h.K_lt, h.Hn_lt⟩

/-- **The decoder scale** `κ = γ √(4s) c₀ / (2^(μ + F + 10) ρ)`. -/
def kapN (s : ℕ) (c0 ρ γ : ℝ) (F mu : ℕ) : ℝ :=
  γ * Real.sqrt (4 * s) * c0 / (2 ^ (mu + F + 10) * ρ)

theorem kapN_pos (s : ℕ) (c0 ρ γ : ℝ) (F mu : ℕ) (hs : 0 < s) (hc0 : 0 < c0) (hρ : 0 < ρ)
    (hγ : 0 < γ) : 0 < kapN s c0 ρ γ F mu := by
  have : 0 < Real.sqrt (4 * (s : ℝ)) := Real.sqrt_pos.mpr (by positivity)
  unfold kapN
  positivity

/-! ### The decoder at every context word -/

/-- The duration word read from a context word: the source bit is the sign bit of `n1`, the
duration word its bits `1, …, kq`. -/
def dvWN (L : Lay) (m mu : ℕ) (Zn : Type) (c : Cfg (CtxN m mu Zn)) : ℤ :=
  if c (n1WN m mu Zn ((aLayN m mu).w - 1)) then
    (wordValue (fun j : Fin L.kq => c (n1WN m mu Zn (j.val + 1))) : ℤ)
  else 2 ^ L.kq

/-- The data address read from a context word. -/
def addrCN (m mu nd : ℕ) (hnd : nd ≤ mu + m) (Zn : Type) (c : Cfg (CtxN m mu Zn)) :
    Fin (2 ^ nd) :=
  wordEquivFin nd (fun j => c (addrBitN m mu nd hnd Zn j))

section Dec

variable {X n : Type*} [Fintype n] [DecidableEq n] {s k b : ℕ} {Zn : Type} [Fintype Zn]
  [DecidableEq Zn]

omit [Fintype Zn] [DecidableEq Zn] in
theorem twos_baseWN {m mu : ℕ} (L : Lay) (E : Cfg (BWAN k L.b m L.lq mu Zn)) (W : Cfg (VW L.b))
    (f : VW L.b → BW4 k L.b m L.lq)
    (hf : ∀ v, E (baseW2 (f v)) = W v) (side : Bool) :
    twos (fun i : Fin L.b => (baseW2 (f (if side then .inr i else .inl i)) :
        BWAN k L.b m L.lq mu Zn)) E =
      twos (B := VW L.b) (fun i => if side then .inr i else .inl i) W := by
  unfold twos
  congr 2
  funext j
  split_ifs <;> simp [hf]

omit [Fintype Zn] [DecidableEq Zn] in
/-- **The decoder hypothesis at every context word**: the decoder `decO` on `inpBN` with scale
`kapN` and step factor `ρ_L`, read at the context word `c`, takes after the compute circuit the
value of the label-selected edgewise gate of the sample at the data address `addrCN c`, with
the LCHS node `nodeW` of every label and the Cayley parameter `γ dvWN c / 2^μ`. -/
theorem decOK_N (p : TParams) (mu nd : ℕ) (hnd : nd ≤ mu + p.m)
    (D : Data (X × Fin (2 ^ nd)) n (Cfg (VW b)) s)
    (en : Cfg (Fin k) ≃ n) (k0 : Fin s) (x : X) (c0 : ℝ) (hc0 : c0 ≠ 0)
    (hdec : ∀ e z, D.decode e z = (c0 : ℂ) * gauss z) (ρ γ : ℝ) (hρ : ρ ≠ 0) (F : ℕ)
    (hHn : hRound (gridP p) F ≠ 0) (c : Cfg (CtxN p.m mu Zn)) :
    DecOK D en k0 (x, addrCN p.m mu nd hnd Zn c) (fun z => p.nodeW z.2)
      (fun _ => γ * (((dvWN (layN p mu b F) p.m mu Zn c : ℤ) : ℝ) / 2 ^ mu)) ρ
      (atSlot2 (computeV4 k b p.m p.l) (oW k)
        (decO (inpBN k (layN p mu b F) p.m mu Zn) (kapN s c0 ρ γ F mu)
          (rhoL (gridP p) F)) c).dec := by
  intro cl
  set xw := (x, addrCN p.m mu nd hnd Zn c) with hxw
  set y := sigma4 D en k0 xw (Sum.elim cl (fun _ => false)) with hy
  set I := inpBN k (layN p mu b F) p.m mu Zn with hI
  set E : Cfg (BWAN k b p.m p.l mu Zn) := glue2 c y with hE
  have hEb : ∀ v : BW4 k b p.m p.l, E (baseW2 v) = y v := fun v => glue2_apply_baseW2 c y v
  set d : Cfg (EW k) := fun e => cl (Sum.inr (ix4 k e)) with hd
  have hij : phiE en d = ((phiE en d).1, (phiE en d).2) := rfl
  set i := (phiE en d).1 with hi
  set j := (phiE en d).2 with hj
  have hv1 : ∀ v : VW b, E (baseW2 (v14 v : BW4 k b p.m p.l)) = D.table xw (i, j) v :=
    fun v => by rw [hEb, hy, sigma4_v14, ← hd, hij]
  have hv2 : ∀ v : VW b, E (baseW2 (v24 v : BW4 k b p.m p.l)) = D.table xw (j, i) v :=
    fun v => by
    rw [hEb, hy, sigma4_v24]
    rfl
  have hlab : ∀ q, E (baseW2 (Sum.inl q)) = cl q := fun q => by
    rw [hEb]
    exact sigma4_inl D en k0 xw cl q
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
  have hX1 : I.X1 E = twos (B := VW b) Sum.inl (D.table xw (i, j)) :=
    twos_baseWN (layN p mu b F) E (D.table xw (i, j)) v14 hv1 false
  have hY1 : I.Y1 E = twos (B := VW b) Sum.inr (D.table xw (i, j)) :=
    twos_baseWN (layN p mu b F) E (D.table xw (i, j)) v14 hv1 true
  have hX2 : I.X2 E = twos (B := VW b) Sum.inl (D.table xw (j, i)) :=
    twos_baseWN (layN p mu b F) E (D.table xw (j, i)) v24 hv2 false
  have hY2 : I.Y2 E = twos (B := VW b) Sum.inr (D.table xw (j, i)) :=
    twos_baseWN (layN p mu b F) E (D.table xw (j, i)) v24 hv2 true
  have hpt : E I.pt = cl (Sum.inr (pW k)) := hlab _
  have htg : E I.tg = cl (Sum.inr (tW k)) := hlab _
  have hV : I.V E = wordValue (fun j => cl (Sum.inl (Sum.inr j))) := by
    unfold Inp.V
    congr 1
    funext j
    exact hlab _
  have hdv : I.dv E = dvWN (layN p mu b F) p.m mu Zn c := rfl
  have hte : te en (fun v => cl (Sum.inr v)) =
      if cl (Sum.inr (tW k)) then Sum.inr (i, j) else Sum.inl (i, j) := by
    unfold te
    rw [← hij]
  have hkn : p.nodeW (labOfW fun s => cl (Sum.inl s)).2 = ((I.nv E : ℤ) : ℝ) *
      hStep (gridP p) := by
    rw [nodeWT_eq]
    unfold Inp.nv
    rw [hV]
    rfl
  show decO I (kapN s c0 ρ γ F mu) (rhoL (gridP p) F) E = val4 D en xw
    (p.nodeW (labOfW fun s => cl (Sum.inl s)).2) ρ
    (γ * (((dvWN (layN p mu b F) p.m mu Zn c : ℤ) : ℝ) / 2 ^ mu)) fun v => cl (Sum.inr v)
  unfold val4
  rw [hkn, ← hdv, hte, core_identity (D.matrix xw) i j c0 hc0 _ _ _ _ hM1 hM2]
  unfold decO Inp.zx Inp.zy Inp.ct Inp.mu Inp.ax Inp.ay
  rw [hX1, hY1, hX2, hY2, hpt, htg]
  have hHnR : (hRound (gridP p) F : ℝ) ≠ 0 := by exact_mod_cast hHn
  have hs := scale_eq γ (Real.sqrt (4 * s)) c0 ρ (hStep (gridP p))
    ((I.dv E : ℤ) : ℝ) ((I.nv E : ℤ) : ℝ) (hRound (gridP p) F : ℝ) mu F hHnR hρ
    (cl (Sum.inr (pW k)))
  change _ = ((γ * (((I.dv E : ℤ) : ℝ) / 2 ^ mu) * Real.sqrt (4 * s) / ρ * c0 / 4 *
    (if cl (Sum.inr (pW k)) = true then ((I.nv E : ℤ) : ℝ) * hStep (gridP p) else 1) : ℝ) :
      ℂ) * _ * _
  rw [← hs]
  unfold kapN rhoL
  beta_reduce
  cases cl (Sum.inr (pW k)) <;> cases cl (Sum.inr (tW k)) <;>
    simp only [Bool.false_eq_true, if_false, if_true] <;> push_cast <;> ring

end Dec

/-! ### The branch family -/

section Family

variable {X n : Type*} [Fintype n] [DecidableEq n] {s k b : ℕ} {Zn : Type}

/-- The start word `ν' = (ini ? word u : 0)` of a source label. -/
def startWN {m mu : ℕ} (N : NodeProg m mu Zn) (z : Bool × (Fin m → Bool)) : ℕ :=
  if z.1 then wordValue (N.word z.2) else 0

theorem startWN_lt {m mu : ℕ} (N : NodeProg m mu Zn) (z : Bool × (Fin m → Bool)) :
    startWN N z < 2 ^ mu := by
  unfold startWN
  split_ifs
  · exact GatePointerEncoding.wordValue_lt_pow _
  · exact Nat.pos_of_ne_zero (by positivity)

/-- **The address** of slot `r` of the branch of the source label `z`:
`A = 2^m ν' + r (2^μ - ν')` on the grid of `2^(μ+m)` points. -/
def addrNN {m mu : ℕ} (N : NodeProg m mu Zn) (z : Bool × (Fin m → Bool)) (r : ℕ) : ℕ :=
  2 ^ m * startWN N z + r * (2 ^ mu - startWN N z)

theorem addrNN_lt {m mu : ℕ} (N : NodeProg m mu Zn) (z : Bool × (Fin m → Bool)) (r : ℕ)
    (hr : r < 2 ^ m) : addrNN N z r < 2 ^ (mu + m) :=
  addr_lt _ _ (startWN_lt N z) hr

/-- **The data grid point** of slot `r` of the branch of `z`: the top `nd` bits of the address,
`⌊A / 2^(μ+m-nd)⌋`. -/
def addrFN {m mu : ℕ} (nd : ℕ) (hnd : nd ≤ mu + m) (N : NodeProg m mu Zn)
    (z : Bool × (Fin m → Bool)) (r : ℕ) (hr : r < 2 ^ m) : Fin (2 ^ nd) :=
  ⟨addrNN N z r / 2 ^ (mu + m - nd), by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, Nat.add_sub_cancel' hnd]
    exact addrNN_lt N z r hr⟩

/-- **The label- and slot-selected private family for computed nodes**: at the label `z` and the
slot `r < 2^m`, the lifted four-sector Cayley action of the sample at the data grid point of the
branch address, at the LCHS node of `z` and the Cayley parameter `γ (2^μ - ν') / 2^μ`; the
identity beyond the last slot. -/
def privFamN (p : TParams) (mu nd : ℕ) (hnd : nd ≤ mu + p.m) (N : NodeProg p.m mu Zn)
    (D : Data (X × Fin (2 ^ nd)) n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (x : X) (ρ γ : ℝ)
    (z : Label p.m p.l) (r : ℕ) :
    Reg (Fin (k + 3)) (Reg (Fin k) ℂ) →L[ℂ] Reg (Fin (k + 3)) (Reg (Fin k) ℂ) :=
  if h : r < 2 ^ p.m then
    elift4 en (act4 D (x, addrFN nd hnd N z.1 r h) (p.nodeW z.2) ρ
      (γ * (((2 ^ mu - startWN N z.1 : ℕ) : ℝ) / 2 ^ mu)))
  else 1

theorem privFamN_isUnitary (p : TParams) (mu nd : ℕ) (hnd : nd ≤ mu + p.m)
    (N : NodeProg p.m mu Zn) (D : Data (X × Fin (2 ^ nd)) n (Cfg (VW b)) s)
    (en : Cfg (Fin k) ≃ n) (x : X) (ρ γ : ℝ) (z : Label p.m p.l) (r : ℕ) :
    IsUnitary (privFamN p mu nd hnd N D en x ρ γ z r) := by
  unfold privFamN
  split_ifs
  · exact elift4_isUnitary _ (act4_unitary _ _ _ _ _)
  · exact isUnitary_one

end Family

/-! ### The native identity -/

section OK

variable {X n : Type*} [Fintype n] [DecidableEq n] {s k b : ℕ} {Zn : Type} [Fintype Zn]
  [DecidableEq Zn]

omit [Fintype Zn] [DecidableEq Zn] in
/-- The start word of the computed scratch is the start word of the label. -/
theorem nuP_fN (p : TParams) (mu : ℕ) (N : NodeProg p.m mu Zn) (σ : Cfg (TSel p.m p.l p.m)) :
    nuP (Sum.inl (iniT p.m p.l)) (fun i => Sum.inr i) (xIn N σ) =
      startWN N (labOfW (fun s => σ (Sum.inl s))).1 := rfl

omit [Fintype Zn] [DecidableEq Zn] in
/-- The data address bits of the computed scratch form the data grid point of the label and
slot. -/
theorem addrCN_fN (p : TParams) (mu nd : ℕ) (hnd : nd ≤ mu + p.m) (N : NodeProg p.m mu Zn)
    (σ : Cfg (TSel p.m p.l p.m)) :
    addrCN p.m mu nd hnd Zn (Sum.elim (fun i => σ (Sum.inr i)) (fN N σ)) =
      addrFN nd hnd N (labOfW (fun s => σ (Sum.inl s))).1
        (wordEquivFin p.m (fun i => σ (Sum.inr i)))
        (wordEquivFin p.m (fun i => σ (Sum.inr i))).isLt := by
  apply Fin.ext
  unfold addrCN addrFN
  rw [GatePointerEncoding.wordEquivFin_apply, GatePointerEncoding.wordFin_val]
  set A := gAN (Sum.inl (iniT p.m p.l)) (fun i => Sum.inr i)
    (fun j => Sum.inl (slT p.m p.l j)) (xIn N σ) with hA
  have hbits : (fun j : Fin nd =>
      Sum.elim (fun i => σ (Sum.inr i)) (fN N σ) (addrBitN p.m mu nd hnd Zn j)) =
      fun j : Fin nd => A.testBit (j.val + (mu + p.m - nd)) := by
    funext j
    change (regsT N σ .md).getLsbD (j.val + (mu + p.m - nd) + 2) = _
    exact mdN_bit _ _ _ _ _ (by omega)
  rw [hbits]
  have hAlt : A < 2 ^ (mu + p.m) := gAN_lt _ _ _ _
  have hdiv : A / 2 ^ (mu + p.m - nd) < 2 ^ nd := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, Nat.add_sub_cancel' hnd]
    exact hAlt
  have hw : wordValue (fun j : Fin nd => A.testBit (j.val + (mu + p.m - nd))) =
      A / 2 ^ (mu + p.m - nd) := by
    rw [← wordValue_testBit (A / 2 ^ (mu + p.m - nd)) hdiv]
    apply wordValue_congr
    intro j
    rw [Nat.testBit_div_two_pow, add_comm]
  rw [hw]
  have hr : rSN (fun j => Sum.inl (slT p.m p.l j)) (xIn N σ) =
      ((wordEquivFin p.m (fun i => σ (Sum.inr i)) : Fin (2 ^ p.m)) : ℕ) := by
    rw [GatePointerEncoding.wordEquivFin_apply, GatePointerEncoding.wordFin_val]
    rfl
  rw [hA]
  unfold gAN addrNN
  rw [nuP_fN, hr]

omit [Fintype Zn] [DecidableEq Zn] in
/-- The duration word of the computed scratch is `2^μ - ν'`. -/
theorem dvWN_fN (p : TParams) (mu b F : ℕ) (N : NodeProg p.m mu Zn)
    (σ : Cfg (TSel p.m p.l p.m)) :
    dvWN (layN p mu b F) p.m mu Zn (Sum.elim (fun i => σ (Sum.inr i)) (fN N σ)) =
      ((2 ^ mu - startWN N (labOfW (fun s => σ (Sum.inl s))).1 : ℕ) : ℤ) := by
  have h := n1N_dv (Sum.inl (iniT p.m p.l)) (fun i => Sum.inr i)
    (fun j => Sum.inl (slT p.m p.l j)) (xIn N σ)
  have hw : (aLayN p.m mu).w - 1 < (aLayN p.m mu).w := by rw [aLayN_w]; omega
  have hmsb : Sum.elim (fun i => σ (Sum.inr i)) (fN N σ)
      (n1WN p.m mu Zn ((aLayN p.m mu).w - 1)) =
      (regsT N σ .n1).getLsbD ((aLayN p.m mu).w - 1) := by
    rw [n1WN, dif_pos hw]
    exact fN_reg N σ .n1 ⟨(aLayN p.m mu).w - 1, hw⟩
  have hbit : (fun j : Fin (layN p mu b F).kq =>
      Sum.elim (fun i => σ (Sum.inr i)) (fN N σ) (n1WN p.m mu Zn (j.val + 1))) =
      fun j : Fin mu => (regsT N σ .n1).getLsbD (j.val + 1) := by
    funext j
    have hj : j.val + 1 < (aLayN p.m mu).w := by
      have := j.isLt
      rw [aLayN_w]
      change j.val < mu at this
      omega
    rw [n1WN, dif_pos hj]
    exact fN_reg N σ .n1 ⟨j.val + 1, hj⟩
  dsimp only [dvWN, layN]
  rw [hmsb, hbit]
  change (if (regsT N σ .n1).getLsbD ((aLayN p.m mu).w - 1) then
      (wordValue (fun j : Fin mu => (regsT N σ .n1).getLsbD (j.val + 1)) : ℤ) else 2 ^ mu) = _
  unfold regsT
  rw [h, nuP_fN]
  have hu := startWN_lt N (labOfW (fun s => σ (Sum.inl s))).1
  push_cast [Nat.cast_sub hu.le]
  ring

/-- **The native identity** of the branch operation for computed nodes: for the time-indexed
binary data on the grid of `2^nd` points, `V† R_val V` acts on clean scratch as the family
`privFamN` selected by the label and the slot wires. -/
theorem nativeOK_N (p : TParams) (mu nd : ℕ) (hnd : nd ≤ mu + p.m) (N : NodeProg p.m mu Zn)
    (hN : N.OK) (D : Data (X × Fin (2 ^ nd)) n (Cfg (VW b)) s)
    (en : Cfg (Fin k) ≃ n) (k0 : Fin s) (hk0 : D.slot k0 = zIdx en) (x : X) (c0 : ℝ)
    (hc0 : c0 ≠ 0) (hdec : ∀ e z, D.decode e z = (c0 : ℂ) * gauss z) (ρ γ : ℝ) (hρ : ρ ≠ 0)
    (F : ℕ) (hHn : hRound (gridP p) F ≠ 0) :
    NativeOK (primsT (R := ℂ) (m := nd) D en x)
      (odeOpN k (layN p mu b F) p.m mu nd hnd N (kapN s c0 ρ γ F mu) (rhoL (gridP p) F))
      (selOp (tlabFam (P := Reg (Fin k) ℂ) (privFamN p mu nd hnd N D en x ρ γ) false)) := by
  set κ := kapN s c0 ρ γ F mu with hκ
  set ρL := rhoL (gridP p) F with hρL
  set L := layN p mu b F with hL
  -- the native identity at every context word
  set Dat : Cfg (CtxN p.m mu Zn) → Cfg (LabW p.m p.l) →
      (Reg (Fin (k + 3)) (Reg (Fin k) ℂ) →L[ℂ] Reg (Fin (k + 3)) (Reg (Fin k) ℂ)) :=
    fun c => labFam (fun z => elift4 (R := ℂ) en (act4 D (x, addrCN p.m mu nd hnd Zn c)
      (p.nodeW z.2) ρ (γ * (((dvWN L p.m mu Zn c : ℤ) : ℝ) / 2 ^ mu)))) false with hDat
  have hOKc : ∀ c : Cfg (CtxN p.m mu Zn),
      NativeOK (prims (R := ℂ) D en (x, wordEquivFin nd
        (fun j => c (addrBitN p.m mu nd hnd Zn j))))
        (atSlot2 (computeV4 k b p.m p.l) (oW k) (decO (inpBN k L p.m mu Zn) κ ρL) c)
        (selOp (Dat c)) := by
    intro c
    exact nativeOK4 (kq := p.m) (lq := p.l) D en k0 hk0 (x, addrCN p.m mu nd hnd Zn c)
      (fun z => p.nodeW z.2) (fun _ => γ * (((dvWN L p.m mu Zn c : ℤ) : ℝ) / 2 ^ mu)) ρ _ rfl
      rfl
      (atSlot2_public _ (computeV4_valid k b p.m p.l) _ _
        (fun y v => decO_update _ (inpBN_avoids k L p.m mu Zn) _ _ y v) c)
      (decOK_N p mu nd hnd D en k0 x c0 hc0 hdec ρ γ hρ F hHn c)
  -- the operation with the computed scratch as context
  have hA : NativeOK (primsT (R := ℂ) (m := nd) D en x) (ndAN k L p.m mu nd hnd Zn κ ρL)
      (selOp (fun y => Dat (fun s => y (Sum.inr s)) (fun s => y (Sum.inl s)))) :=
    nativeOK_slotR (addrBitN p.m mu nd hnd Zn)
      (fun w => prims (R := ℂ) D en (x, wordEquivFin nd w))
      (computeV4 k b p.m p.l) (oW k) (decO (inpBN k L p.m mu Zn) κ ρL) Dat hOKc
  -- the node and address programs as a computed selection
  obtain ⟨hAPu, hAP⟩ := classical_hAP (primsT (R := ℂ) (m := nd) D en x)
    (apGN k b p.m p.l mu Zn N) (apGN_classical N hN) (fN N) (apGN_run N hN)
  have hB := nativeOK_computed (primsT (R := ℂ) (m := nd) D en x)
    (ndAN k L p.m mu nd hnd Zn κ ρL) (odeOpN k L p.m mu nd hnd N κ ρL)
    (nGatesOf (apGN k b p.m p.l mu Zn N)) rfl rfl (fun _ => rfl) (fN N) hAPu hAP _ hA
  -- the family
  have hfam : (fun σ : Cfg (TSel p.m p.l p.m) =>
      (fun y : Cfg (LabW p.m p.l ⊕ CtxN p.m mu Zn) => Dat (fun s => y (Sum.inr s))
        (fun s => y (Sum.inl s))) (Sum.elim (fun s => σ (Sum.inl s))
          (Sum.elim (fun s => σ (Sum.inr s)) (fN N σ)))) =
      tlabFam (P := Reg (Fin k) ℂ) (privFamN p mu nd hnd N D en x ρ γ) false := by
    funext σ
    simp only [hDat, labFam, tlabFam, GateODE.adjIf, SlotSim.adjT, Bool.false_eq_true,
      if_false]
    have hc : (fun s => (Sum.elim (fun s => σ (Sum.inl s))
        (Sum.elim (fun s => σ (Sum.inr s)) (fN N σ)) : Cfg (LabW p.m p.l ⊕ CtxN p.m mu Zn))
          (Sum.inr s)) = Sum.elim (fun i => σ (Sum.inr i)) (fN N σ) := rfl
    have hl : (fun s => (Sum.elim (fun s => σ (Sum.inl s))
        (Sum.elim (fun s => σ (Sum.inr s)) (fN N σ)) : Cfg (LabW p.m p.l ⊕ CtxN p.m mu Zn))
          (Sum.inl s)) = fun s => σ (Sum.inl s) := rfl
    rw [hc, hl, privFamN, dif_pos (wordEquivFin p.m (fun i => σ (Sum.inr i))).isLt,
      addrCN_fN, hL, dvWN_fN, Int.cast_natCast]
  rw [← hfam]
  exact hB

end OK

end

end SparseHamiltonian.GateBinaryNodes
