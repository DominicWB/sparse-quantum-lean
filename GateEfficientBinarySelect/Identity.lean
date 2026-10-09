import GateEfficientBinarySelect.Native

/-!
# The native identity of the private operation on branch-dependent meshes

* `layB`, `kapB`: the integer layout of the released arithmetic with `m` node bits (the
  duration word) on the LCHS grid of the time-dependent solver, and the decoder scale
  `κ = γ √(4s) c₀ / (2^(m + F + 10) ρ)`; `layB_ok`: the layout is admissible.
* `dvW`, `addrC`: the duration word and the address read from a context word (slot and address
  registers).
* `decOK_B`: at every context word the decoder satisfies `GateBinaryODE.DecOK` of the sample at
  the address of the context, with the LCHS node of each label and the Cayley parameter
  `γ dvW / 2^m` of the context.
* `startW`, `addrN`, `privFamB`: the start word `u'`, the address `2^m u' + r (2^m - u')` and the
  label- and slot-selected private family (identity beyond the last slot).
* `fA`, `apG_run`: the address program writes the register file of `Address` into the address
  registers.
* `nativeOK_B`: **the native identity** of the branch operation for the family `privFamB`.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateBinarySelect

noncomputable section
open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
open SparseHamiltonian.GateBinary SparseHamiltonian.GateBinaryODE SparseHamiltonian.OracleCircuit
open SparseHamiltonian.GateBinaryODETime (baseW2 selW2 glue2 atSlot2 glue2_apply_baseW2
  atSlot2_public gridP nodeWT_eq layT layT_ok)
open SparseHamiltonian.GateODE (Label)
open SparseHamiltonian.GateODE.Time (TParams)
open SparseHamiltonian.GatePointerEncoding (wordEquivFin wordValue)
open NativeSparseBlockEncoding (Data Query)
open scoped InnerProduct

/-! ### The layout and the decoder scale -/

/-- **The integer layout** of the arithmetic: the released layout of the LCHS grid of the
time-dependent solver with `m` node bits (the duration word). -/
abbrev layB (p : TParams) (b F : ℕ) : Lay :=
  ⟨b, p.m, p.l, GateODE.AnalyticLCHS.halfCount (p.T * p.lamD) p.ratio p.acc, p.J, F,
    hRound (gridP p) F⟩

theorem layB_kq (p : TParams) (b F : ℕ) : (layB p b F).kq = p.m := rfl

/-- The layout is admissible. -/
theorem layB_ok (p : TParams) (b F : ℕ) (hb : 0 < b) (hg : 1 ≤ p.g) (hε : 0 < p.ε)
    (hε1 : p.ε ≤ 1) (hTD : 0 ≤ p.T * p.lamD) : (layB p b F).OK := by
  have h := layT_ok p b F hb hg hε hε1 hTD
  exact ⟨h.b_pos, h.J_le, h.K_lt, h.Hn_lt⟩

/-- **The decoder scale** `κ = γ √(4s) c₀ / (2^(m + F + 10) ρ)`. -/
def kapB (s : ℕ) (c0 ρ γ : ℝ) (F m : ℕ) : ℝ :=
  γ * Real.sqrt (4 * s) * c0 / (2 ^ (m + F + 10) * ρ)

theorem kapB_pos (s : ℕ) (c0 ρ γ : ℝ) (F m : ℕ) (hs : 0 < s) (hc0 : 0 < c0) (hρ : 0 < ρ)
    (hγ : 0 < γ) : 0 < kapB s c0 ρ γ F m := by
  have : 0 < Real.sqrt (4 * (s : ℝ)) := Real.sqrt_pos.mpr (by positivity)
  unfold kapB
  positivity

/-! ### The decoder at every context word -/

/-- The duration word read from a context word: the source bit is the sign bit of `n1`, the node
word its bits `1, …, kq`. -/
def dvW (L : Lay) (m : ℕ) (c : Cfg (CtxW m)) : ℤ :=
  if c (n1W m ((aLay m).w - 1)) then (wordValue (fun j : Fin L.kq => c (n1W m (j.val + 1))) : ℤ)
  else 2 ^ L.kq

/-- The address read from a context word. -/
def addrC (m : ℕ) (c : Cfg (CtxW m)) : Fin (2 ^ (2 * m)) :=
  wordEquivFin (2 * m) (fun j => c (addrBit m j))

section Dec

variable {X n : Type*} [Fintype n] [DecidableEq n] {s k b : ℕ}

theorem twos_baseW2 {m : ℕ} (L : Lay) (E : Cfg (BWA k L.b m L.lq)) (W : Cfg (VW L.b))
    (f : VW L.b → BW4 k L.b m L.lq)
    (hf : ∀ v, E (baseW2 (f v)) = W v) (side : Bool) :
    twos (fun i : Fin L.b => (baseW2 (f (if side then .inr i else .inl i)) :
        BWA k L.b m L.lq)) E =
      twos (B := VW L.b) (fun i => if side then .inr i else .inl i) W := by
  unfold twos
  congr 2
  funext j
  split_ifs <;> simp [hf]

/-- **The decoder hypothesis at every context word**: the decoder `decO` on `inpB` with scale
`kapB` and step factor `ρ_L`, read at the context word `c`, takes after the compute circuit the
value of the label-selected edgewise gate of the sample at the address `addrC c`, with the LCHS
node `nodeW` of every label and the Cayley parameter `γ dvW c / 2^m`. -/
theorem decOK_B (p : TParams) (D : Data (X × Fin (2 ^ (2 * p.m))) n (Cfg (VW b)) s)
    (en : Cfg (Fin k) ≃ n) (k0 : Fin s) (x : X) (c0 : ℝ) (hc0 : c0 ≠ 0)
    (hdec : ∀ e z, D.decode e z = (c0 : ℂ) * gauss z) (ρ γ : ℝ) (hρ : ρ ≠ 0) (F : ℕ)
    (hHn : hRound (gridP p) F ≠ 0) (c : Cfg (CtxW p.m)) :
    DecOK D en k0 (x, addrC p.m c) (fun z => p.nodeW z.2)
      (fun _ => γ * (((dvW (layB p b F) p.m c : ℤ) : ℝ) / 2 ^ p.m)) ρ
      (atSlot2 (computeV4 k b p.m p.l) (oW k)
        (decO (inpB k (layB p b F) p.m) (kapB s c0 ρ γ F p.m) (rhoL (gridP p) F)) c).dec := by
  intro cl
  set xw := (x, addrC p.m c) with hxw
  set y := sigma4 D en k0 xw (Sum.elim cl (fun _ => false)) with hy
  set I := inpB k (layB p b F) p.m with hI
  set E : Cfg (BWA k b p.m p.l) := glue2 c y with hE
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
    twos_baseW2 (layB p b F) E (D.table xw (i, j)) v14 hv1 false
  have hY1 : I.Y1 E = twos (B := VW b) Sum.inr (D.table xw (i, j)) :=
    twos_baseW2 (layB p b F) E (D.table xw (i, j)) v14 hv1 true
  have hX2 : I.X2 E = twos (B := VW b) Sum.inl (D.table xw (j, i)) :=
    twos_baseW2 (layB p b F) E (D.table xw (j, i)) v24 hv2 false
  have hY2 : I.Y2 E = twos (B := VW b) Sum.inr (D.table xw (j, i)) :=
    twos_baseW2 (layB p b F) E (D.table xw (j, i)) v24 hv2 true
  have hpt : E I.pt = cl (Sum.inr (pW k)) := hlab _
  have htg : E I.tg = cl (Sum.inr (tW k)) := hlab _
  have hV : I.V E = wordValue (fun j => cl (Sum.inl (Sum.inr j))) := by
    unfold Inp.V
    congr 1
    funext j
    exact hlab _
  have hdv : I.dv E = dvW (layB p b F) p.m c := rfl
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
  show decO I (kapB s c0 ρ γ F p.m) (rhoL (gridP p) F) E = val4 D en xw
    (p.nodeW (labOfW fun s => cl (Sum.inl s)).2) ρ
    (γ * (((dvW (layB p b F) p.m c : ℤ) : ℝ) / 2 ^ p.m)) fun v => cl (Sum.inr v)
  unfold val4
  rw [hkn, ← hdv, hte, core_identity (D.matrix xw) i j c0 hc0 _ _ _ _ hM1 hM2]
  unfold decO Inp.zx Inp.zy Inp.ct Inp.mu Inp.ax Inp.ay
  rw [hX1, hY1, hX2, hY2, hpt, htg]
  have hHnR : (hRound (gridP p) F : ℝ) ≠ 0 := by exact_mod_cast hHn
  have hs := scale_eq γ (Real.sqrt (4 * s)) c0 ρ (hStep (gridP p))
    ((I.dv E : ℤ) : ℝ) ((I.nv E : ℤ) : ℝ) (hRound (gridP p) F : ℝ) p.m F hHnR hρ
    (cl (Sum.inr (pW k)))
  change _ = ((γ * (((I.dv E : ℤ) : ℝ) / 2 ^ p.m) * Real.sqrt (4 * s) / ρ * c0 / 4 *
    (if cl (Sum.inr (pW k)) = true then ((I.nv E : ℤ) : ℝ) * hStep (gridP p) else 1) : ℝ) :
      ℂ) * _ * _
  rw [← hs]
  unfold kapB rhoL
  beta_reduce
  cases cl (Sum.inr (pW k)) <;> cases cl (Sum.inr (tW k)) <;>
    simp only [Bool.false_eq_true, if_false, if_true] <;> push_cast <;> ring

end Dec

/-! ### The branch family -/

section Family

variable {X n : Type*} [Fintype n] [DecidableEq n] {s k b : ℕ}

/-- The start word `u' = (ini ? u : 0)` of a source label. -/
def startW {m : ℕ} (z : Bool × (Fin m → Bool)) : ℕ := if z.1 then wordValue z.2 else 0

theorem startW_lt {m : ℕ} (z : Bool × (Fin m → Bool)) : startW z < 2 ^ m := by
  unfold startW
  split_ifs
  · exact GatePointerEncoding.wordValue_lt_pow _
  · exact Nat.pos_of_ne_zero (by positivity)

/-- **The address** of slot `r` of the branch of the source label `z`:
`2^m u' + r (2^m - u')`. -/
def addrN {m : ℕ} (z : Bool × (Fin m → Bool)) (r : ℕ) : ℕ :=
  2 ^ m * startW z + r * (2 ^ m - startW z)

theorem addrN_lt {m : ℕ} (z : Bool × (Fin m → Bool)) (r : ℕ) (hr : r < 2 ^ m) :
    addrN z r < 2 ^ (2 * m) := by
  have hu := startW_lt z
  unfold addrN
  have hle : r * (2 ^ m - startW z) ≤ (2 ^ m - 1) * (2 ^ m - startW z) :=
    Nat.mul_le_mul_right _ (by omega)
  have h2 : 2 ^ (2 * m) = 2 ^ m * 2 ^ m := by rw [two_mul, pow_add]
  rw [h2]
  have e1 : (2 ^ m - 1) * (2 ^ m - startW z) =
      2 ^ m * (2 ^ m - startW z) - (2 ^ m - startW z) := by
    rw [Nat.sub_mul, one_mul]
  have e2 : 2 ^ m * (2 ^ m - startW z) + 2 ^ m * startW z = 2 ^ m * 2 ^ m := by
    rw [← Nat.mul_add, Nat.sub_add_cancel hu.le]
  have e3 : (2 ^ m - startW z) ≤ 2 ^ m * (2 ^ m - startW z) :=
    Nat.le_mul_of_pos_left _ (by positivity)
  have h4 : 0 < 2 ^ m - startW z := by omega
  omega

/-- The address as a grid index. -/
def addrF {m : ℕ} (z : Bool × (Fin m → Bool)) (r : ℕ) (hr : r < 2 ^ m) : Fin (2 ^ (2 * m)) :=
  ⟨addrN z r, addrN_lt z r hr⟩

/-- **The label- and slot-selected private family on branch-dependent meshes**: at the label `z`
and the slot `r < 2^m`, the lifted four-sector Cayley action of the sample at the branch address,
at the LCHS node of `z` and the Cayley parameter `γ (2^m - u') / 2^m`; the identity beyond the
last slot. -/
def privFamB (p : TParams) (D : Data (X × Fin (2 ^ (2 * p.m))) n (Cfg (VW b)) s)
    (en : Cfg (Fin k) ≃ n) (x : X) (ρ γ : ℝ) (z : Label p.m p.l) (r : ℕ) :
    Reg (Fin (k + 3)) (Reg (Fin k) ℂ) →L[ℂ] Reg (Fin (k + 3)) (Reg (Fin k) ℂ) :=
  if h : r < 2 ^ p.m then
    elift4 en (act4 D (x, addrF z.1 r h) (p.nodeW z.2) ρ
      (γ * (((2 ^ p.m - startW z.1 : ℕ) : ℝ) / 2 ^ p.m)))
  else 1

theorem privFamB_isUnitary (p : TParams) (D : Data (X × Fin (2 ^ (2 * p.m))) n (Cfg (VW b)) s)
    (en : Cfg (Fin k) ≃ n) (x : X) (ρ γ : ℝ) (z : Label p.m p.l) (r : ℕ) :
    IsUnitary (privFamB p D en x ρ γ z r) := by
  unfold privFamB
  split_ifs
  · exact elift4_isUnitary _ (act4_unitary _ _ _ _ _)
  · exact isUnitary_one

end Family

/-! ### The address program as a computed selection -/

section Run

variable {k b m l : ℕ}

/-- The register file written by the address program on the selection `σ`, as a configuration
of the address registers. -/
def fA (m l : ℕ) (σ : Cfg (TSel m l m)) : Cfg (ZA m) :=
  fun cw => cfgOf σ (regsA (iniT m l) (uT m l) (slT m l) σ) (Sum.inr cw)

theorem fA_reg (σ : Cfg (TSel m l m)) (r : RO (aLay m)) (i : Fin (aLay m).w) :
    fA m l σ (CW.reg r i) = (regsA (iniT m l) (uT m l) (slT m l) σ r).getLsbD i := rfl

theorem cfgOf_zero_comp_embP (c : Cfg ((TSel m l m) ⊕ PR4 k)) :
    (Sum.elim c (fun _ => false) : Cfg (BWB k b m l)) ∘ embP k b m l =
      cfgOf (fun s => c (Sum.inl s)) (0 : RO (aLay m) → BitVec (aLay m).w) := by
  funext w
  rcases w with s | (_ | i | i | ⟨r, i⟩) <;> simp [embP, cfgOf]

/-- **The address program writes the address registers**: on every clean configuration, the
gates `apG` XOR the register file `fA σ` of the selection `σ` into the address registers. -/
theorem apG_run (c : Cfg ((TSel m l m) ⊕ PR4 k)) :
    cfgRun (apG k b m l) (Sum.elim c (fun _ => false)) =
      xorF (PR := PR4 k) (Z := SZ4 k b) (fA m l) (Sum.elim c (fun _ => false)) := by
  rw [apG, cfgRun_map_toGate]
  set z : Cfg (BWB k b m l) := Sum.elim c (fun _ => false) with hz
  have hmap := crun_map (embP k b m l) (embP k b m l).injective
    (addrG (iniT m l) (uT m l) (slT m l)) z
  rw [hz, cfgOf_zero_comp_embP, crun_addrG] at hmap
  funext w
  rcases w with (s | p) | t | zz
  · have := congrFun hmap (Sum.inl s)
    exact this
  · rw [crun_map_of_not_mem _ _ _ _ (fun a h => by rcases a with s | c <;> cases h)]
    rfl
  · have := congrFun hmap (Sum.inr t)
    refine this.trans ?_
    change fA m l (fun s => c (Sum.inl s)) t =
      (false ^^ fA m l (selP (Sum.elim c (fun _ => false) : Cfg (BWB k b m l))) t)
    rw [Bool.false_xor]
    rfl
  · rw [crun_map_of_not_mem _ _ _ _ (fun a h => by rcases a with s | c <;> cases h)]
    rfl

end Run

/-! ### The native identity -/

section OK

variable {X n : Type*} [Fintype n] [DecidableEq n] {s k b : ℕ}

/-- The address bits of the computed register file form the address of the label and slot. -/
theorem addrC_fA (p : TParams) (σ : Cfg (TSel p.m p.l p.m)) :
    addrC p.m (Sum.elim (fun i => σ (Sum.inr i)) (fA p.m p.l σ)) =
      addrF (labOfW (fun s => σ (Sum.inl s))).1 (wordEquivFin p.m (fun i => σ (Sum.inr i)))
        (wordEquivFin p.m (fun i => σ (Sum.inr i))).isLt := by
  apply Fin.ext
  unfold addrC
  rw [GatePointerEncoding.wordEquivFin_apply, GatePointerEncoding.wordFin_val]
  have h := md_word (iniT p.m p.l) (uT p.m p.l) (slT p.m p.l) σ
  have hbits : (fun j : Fin (2 * p.m) =>
      Sum.elim (fun i => σ (Sum.inr i)) (fA p.m p.l σ) (addrBit p.m j)) =
      fun j : Fin (2 * p.m) =>
        (regsA (iniT p.m p.l) (uT p.m p.l) (slT p.m p.l) σ .md).getLsbD (j.val + 2) := by
    funext j
    exact fA_reg σ .md ⟨j.val + 2, addrBit_lt p.m j⟩
  rw [hbits, h]
  have hu : uP (iniT p.m p.l) (uT p.m p.l) σ = startW (labOfW (fun s => σ (Sum.inl s))).1 := rfl
  have hr : rS (slT p.m p.l) σ = ((wordEquivFin p.m (fun i => σ (Sum.inr i)) : Fin (2 ^ p.m)) :
      ℕ) := by
    rw [GatePointerEncoding.wordEquivFin_apply, GatePointerEncoding.wordFin_val]
    rfl
  change gA _ _ _ σ = addrN _ _
  unfold gA addrN
  rw [hu, hr]

/-- The duration word of the computed register file is `2^m - u'`. -/
theorem dvW_fA (p : TParams) (b F : ℕ) (σ : Cfg (TSel p.m p.l p.m)) :
    dvW (layB p b F) p.m (Sum.elim (fun i => σ (Sum.inr i)) (fA p.m p.l σ)) =
      ((2 ^ p.m - startW (labOfW (fun s => σ (Sum.inl s))).1 : ℕ) : ℤ) := by
  have h := n1_dv (iniT p.m p.l) (uT p.m p.l) (slT p.m p.l) σ
  have hw : (aLay p.m).w - 1 < (aLay p.m).w := by rw [aLay_w]; omega
  have hmsb : Sum.elim (fun i => σ (Sum.inr i)) (fA p.m p.l σ) (n1W p.m ((aLay p.m).w - 1)) =
      (regsA (iniT p.m p.l) (uT p.m p.l) (slT p.m p.l) σ .n1).getLsbD ((aLay p.m).w - 1) := by
    rw [n1W, dif_pos hw]
    exact fA_reg σ .n1 ⟨(aLay p.m).w - 1, hw⟩
  have hbit : (fun j : Fin (layB p b F).kq =>
      Sum.elim (fun i => σ (Sum.inr i)) (fA p.m p.l σ) (n1W p.m (j.val + 1))) =
      fun j : Fin p.m => (regsA (iniT p.m p.l) (uT p.m p.l) (slT p.m p.l) σ .n1).getLsbD
        (j.val + 1) := by
    funext j
    have hj : j.val + 1 < (aLay p.m).w := by
      have := j.isLt
      rw [aLay_w]
      change j.val < p.m at this
      omega
    rw [n1W, dif_pos hj]
    exact fA_reg σ .n1 ⟨j.val + 1, hj⟩
  dsimp only [dvW, layB]
  rw [hmsb, hbit, h]
  have hu := startW_lt (labOfW (fun s => σ (Sum.inl s))).1
  have hus : uP (iniT p.m p.l) (uT p.m p.l) σ = startW (labOfW (fun s => σ (Sum.inl s))).1 := rfl
  rw [hus]
  push_cast [Nat.cast_sub hu.le]
  ring

/-- **The native identity** of the branch operation: for the time-indexed binary data on the grid
of `2^(2m)` points, `V† R_val V` acts on clean scratch as the family `privFamB` selected by the
label and the slot wires. -/
theorem nativeOK_B (p : TParams) (D : Data (X × Fin (2 ^ (2 * p.m))) n (Cfg (VW b)) s)
    (en : Cfg (Fin k) ≃ n) (k0 : Fin s) (hk0 : D.slot k0 = zIdx en) (x : X) (c0 : ℝ)
    (hc0 : c0 ≠ 0) (hdec : ∀ e z, D.decode e z = (c0 : ℂ) * gauss z) (ρ γ : ℝ) (hρ : ρ ≠ 0)
    (F : ℕ) (hHn : hRound (gridP p) F ≠ 0) :
    NativeOK (primsT (R := ℂ) (m := 2 * p.m) D en x)
      (odeOpB k (layB p b F) p.m (kapB s c0 ρ γ F p.m) (rhoL (gridP p) F))
      (selOp (tlabFam (P := Reg (Fin k) ℂ) (privFamB p D en x ρ γ) false)) := by
  set κ := kapB s c0 ρ γ F p.m with hκ
  set ρL := rhoL (gridP p) F with hρL
  set L := layB p b F with hL
  -- the native identity at every context word
  set Dat : Cfg (CtxW p.m) → Cfg (LabW p.m p.l) →
      (Reg (Fin (k + 3)) (Reg (Fin k) ℂ) →L[ℂ] Reg (Fin (k + 3)) (Reg (Fin k) ℂ)) :=
    fun c => labFam (fun z => elift4 (R := ℂ) en (act4 D (x, addrC p.m c) (p.nodeW z.2) ρ
      (γ * (((dvW L p.m c : ℤ) : ℝ) / 2 ^ p.m)))) false with hDat
  have hOKc : ∀ c : Cfg (CtxW p.m),
      NativeOK (prims (R := ℂ) D en (x, wordEquivFin (2 * p.m) (fun j => c (addrBit p.m j))))
        (atSlot2 (computeV4 k b p.m p.l) (oW k) (decO (inpB k L p.m) κ ρL) c) (selOp (Dat c)) := by
    intro c
    exact nativeOK4 (kq := p.m) (lq := p.l) D en k0 hk0 (x, addrC p.m c)
      (fun z => p.nodeW z.2) (fun _ => γ * (((dvW L p.m c : ℤ) : ℝ) / 2 ^ p.m)) ρ _ rfl rfl
      (atSlot2_public _ (computeV4_valid k b p.m p.l) _ _
        (fun y v => decO_update _ (inpB_avoids k L p.m) _ _ y v) c)
      (decOK_B p D en k0 x c0 hc0 hdec ρ γ hρ F hHn c)
  -- the operation with the address registers as context
  have hA : NativeOK (primsT (R := ℂ) (m := 2 * p.m) D en x) (ndA k L p.m κ ρL)
      (selOp (fun y => Dat (fun s => y (Sum.inr s)) (fun s => y (Sum.inl s)))) :=
    nativeOK_slotR (addrBit p.m)
      (fun w => prims (R := ℂ) D en (x, wordEquivFin (2 * p.m) w))
      (computeV4 k b p.m p.l) (oW k) (decO (inpB k L p.m) κ ρL) Dat hOKc
  -- the address program as a computed selection
  obtain ⟨hAPu, hAP⟩ := classical_hAP (primsT (R := ℂ) (m := 2 * p.m) D en x)
    (apG k b p.m p.l) (apG_classical k b p.m p.l) (fA p.m p.l) apG_run
  have hB := nativeOK_computed (primsT (R := ℂ) (m := 2 * p.m) D en x) (ndA k L p.m κ ρL)
    (odeOpB k L p.m κ ρL) (nGatesOf (apG k b p.m p.l)) rfl rfl (fun _ => rfl) (fA p.m p.l)
    hAPu hAP _ hA
  -- the family
  have hfam : (fun σ : Cfg (TSel p.m p.l p.m) =>
      (fun y : Cfg (LabW p.m p.l ⊕ CtxW p.m) => Dat (fun s => y (Sum.inr s))
        (fun s => y (Sum.inl s))) (Sum.elim (fun s => σ (Sum.inl s))
          (Sum.elim (fun s => σ (Sum.inr s)) (fA p.m p.l σ)))) =
      tlabFam (P := Reg (Fin k) ℂ) (privFamB p D en x ρ γ) false := by
    funext σ
    simp only [hDat, labFam, tlabFam, GateODE.adjIf, SlotSim.adjT, Bool.false_eq_true, if_false]
    have hc : (fun s => (Sum.elim (fun s => σ (Sum.inl s))
        (Sum.elim (fun s => σ (Sum.inr s)) (fA p.m p.l σ)) : Cfg (LabW p.m p.l ⊕ CtxW p.m))
          (Sum.inr s)) = Sum.elim (fun i => σ (Sum.inr i)) (fA p.m p.l σ) := rfl
    have hl : (fun s => (Sum.elim (fun s => σ (Sum.inl s))
        (Sum.elim (fun s => σ (Sum.inr s)) (fA p.m p.l σ)) : Cfg (LabW p.m p.l ⊕ CtxW p.m))
          (Sum.inl s)) = fun s => σ (Sum.inl s) := rfl
    rw [hc, hl, privFamB, dif_pos (wordEquivFin p.m (fun i => σ (Sum.inr i))).isLt,
      addrC_fA, hL, dvW_fA, Int.cast_natCast]
  rw [← hfam]
  exact hB

end OK

end

end SparseHamiltonian.GateBinarySelect
