import GeneralDecoderODE.Solver
import GeneralSparseODE.Time

/-!
# The time-dependent general solver for any implementation of the padded oracles

The time-dependent gate solver for time-indexed sparse access of general size
(`GeneralSparseODE.general_time_outcome`) calls the coherent sampled-time supplied oracles through
the implementation `GeneralSparseAccess.implP` of the padded oracles at every slot word. This module
states it for **any implementation** `impl` of the padded oracles of the samples of sparse access
`D` in the binary format, from any unitary primitives `Pw w` (one family per slot word `w`) on a
register `Y` and on clean ancillas `Xa` (`GeneralSparseAccess.ImplOK` at every slot word):

* `ndTI q impl`: the released label- and slot-selected operation of the padded problem with every
  padded call replaced by `impl`, every call also reading the slot wires
  (`GeneralSparseODE.substSlot`);
* `arTI q Xa`: the arithmetic of the released solver on the base wires;
* `prepTI q impl loadC wpC`: the direct source assembly in the zero case, the native preparation
  with `ndTI q impl` otherwise; the loading circuit on the low wires of the padded system register;
* `nativeOKTI`: the native identity of `ndTI q impl` for the selection-controlled primitives
  `slotPrim Pw`;
* `general_time_outcomeI`: the guarantees of `GeneralSparseODE.general_time_outcome` for the
  protocol `nprotocol (prepTI q impl loadC wpC) (2g)` and the primitives `slotPrim Pw`.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GeneralDecoderODE

noncomputable section
open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
  SparseHamiltonian.GateBinary
open SparseHamiltonian.GeneralSparseAccess
open SparseHamiltonian.GeneralSparseODE
open SparseHamiltonian.OracleCircuit
open GateBinaryODE (SZ4 mLift computeV4 computeV4_valid computeV4_nGates computeV4_nCalls oW
  elift4 act4 nativeOK4 hadUJ4_ok)
open GateBinaryODETime (PubT privFamT privFamT_word decOK_T HsT LsT)
open ZeroTimeGateODE (BTPublicOK0 BTZeroCase tzprepC btpublicOK_of btparams_ok0
  btzeroCase_params)
open SourceAccuracyODE (WOutcome)
open RepresentedSampleODE.GateTime (RobustRest robust_instanceOK robust_tzInstanceOK repairedLs)
open GatePointerEncoding (wordValue wordEquivFin)
open NativeSparseBlockEncoding (Query)
open ODEStateNormalization (unitDirection)
open scoped InnerProduct

/-! ### The operation, the arithmetic and the preparation -/

section Def

variable (q : GPubT) {Y Xa : Type*}

/-- **The private operation calling the primitives through `impl`**: the released label- and
slot-selected operation of the padded problem with every padded call replaced by its
implementation `impl` (`substSlot`). -/
def ndTI (impl : Query → List (NInstr (PY (q.k + 1) q.b ⊕ Xa) Y Query)) :
    NativeOp (TSel q.pub.params.m q.pub.params.l q.pub.params.m)
      (Fin q.pub.params.a ⊕ Fin (q.k + 1)) (SZ4 (q.k + 1) q.b ⊕ Xa) (Fin q.m ⊕ Y) Query :=
  substSlot (computeV4 (q.k + 1) q.b q.m q.pub.params.l) (oW (q.k + 1)) q.pub.nd.dec impl

/-- **The arithmetic** of the released operation on the base wires, with the ancillas `Xa` in the
scratch. -/
def arTI (Xa : Type*) : Arith (NB (TSel q.pub.params.m q.pub.params.l q.pub.params.m)
    (Fin q.pub.params.a ⊕ Fin (q.k + 1)) (SZ4 (q.k + 1) q.b ⊕ Xa)) :=
  liftA q.pub.ar

/-- **The preparation through `impl`**: the direct source assembly in the zero case, the native
preparation with the operation `ndTI q impl` otherwise; the loading circuit on the low wires of the
padded system register. -/
def prepTI {Zs : Type*} [Fintype Zs] [DecidableEq Zs] [Fintype Xa] [DecidableEq Xa]
    (impl : Query → List (NInstr (PY (q.k + 1) q.b ⊕ Xa) Y Query))
    (loadC : List (NInstr ((Fin (q.m + 1) ⊕ Fin q.k) ⊕ Zs) (Fin q.m ⊕ Y) Query))
    (wpC : List (NInstr (Fin (q.m + 1) ⊕ Zs) (Fin q.m ⊕ Y) Query)) :
    List (NInstr (TNW q.pub.params (Fin (q.k + 1)) Zs (SZ4 (q.k + 1) q.b ⊕ Xa)
      (arTI q Xa).bT (arTI q Xa).bP (arTI q Xa).A) (Fin q.m ⊕ Y) Query) :=
  if BTZeroCase q.pub then tzprepC (liftC loadC) wpC
  else tnprepC q.pub.params q.pub.UJg (ndTI q impl) (arTI q Xa) (liftC loadC) wpC

end Def

section Props

variable (q : GPubT) {Y Xa : Type*} [Fintype Y] [DecidableEq Y] [Fintype Xa] [DecidableEq Xa]

omit [Fintype Y] [DecidableEq Y] [Fintype Xa] in
theorem ndTI_public {impl : Query → List (NInstr (PY (q.k + 1) q.b ⊕ Xa) Y Query)}
    (hv : ∀ j, ∀ i ∈ impl j, i.Valid) : (ndTI q impl).Public :=
  substSlot_public _ (computeV4_valid _ _ _ _) _ _ q.pub.nd_public.dec_indep hv

omit [Fintype Y] [DecidableEq Y] [Fintype Xa] in
theorem arTI_ok (hq : q.pub.OK) (impl : Query → List (NInstr (PY (q.k + 1) q.b ⊕ Xa) Y Query)) :
    ArithOK (arTI q Xa) (Sum.inl (Sum.inr (ndTI q impl).o)) (ndTI q impl).dec q.ζ :=
  arithOK_liftA q.pub.ar _ _ _ (q.pub.ar_ok hq)

omit [Fintype Y] [DecidableEq Y] [Fintype Xa] [DecidableEq Xa] in
/-- The compute circuit has at most `28 (k + 1) + 2 + 6 G` gates for `G` gates per call of
`impl`. -/
theorem ndTI_nGates (impl : Query → List (NInstr (PY (q.k + 1) q.b ⊕ Xa) Y Query)) (G : ℕ)
    (hG : ∀ j, nGatesN (impl j) ≤ G) :
    nGatesN (ndTI q impl).V ≤ 28 * (q.k + 1) + 2 + G * 6 := by
  have h := nGatesN_substSlot_le (computeV4 (q.k + 1) q.b q.m q.pub.params.l) (oW (q.k + 1))
    q.pub.nd.dec impl G hG
  have hg : nGatesN (computeV4 (q.k + 1) q.b q.m q.pub.params.l) = 28 * (q.k + 1) + 2 :=
    computeV4_nGates (q.k + 1) q.b q.m q.pub.params.l
  have hc : nCallsN (fun _ => true) (computeV4 (q.k + 1) q.b q.m q.pub.params.l) = 6 := by
    have := computeV4_nCalls (k := q.k + 1) (b := q.b) (kq := q.m) (lq := q.pub.params.l)
      (fun _ => true)
    simp only [if_true] at this
    exact this
  rw [hg, hc] at h
  exact h

omit [Fintype Y] [DecidableEq Y] [Fintype Xa] [DecidableEq Xa] in
/-- The compute circuit makes at most `2 c` calls of each kind it calls, for at most `c` calls
per call of `impl`, all of the kind of the call. -/
theorem ndTI_nCalls {impl : Query → List (NInstr (PY (q.k + 1) q.b ⊕ Xa) Y Query)} {c : ℕ}
    (hK : KindOK impl id c) (p : Query → Bool) :
    nCallsN p (ndTI q impl).V ≤ 2 * c * ((if p Query.rowLocation then 1 else 0) +
      (if p Query.columnLocation then 1 else 0) + (if p Query.value then 1 else 0)) := by
  have h := nCallsN_substSlot_le (computeV4 (q.k + 1) q.b q.m q.pub.params.l) (oW (q.k + 1))
    q.pub.nd.dec hK p
  have hc := computeV4_nCalls (k := q.k + 1) (b := q.b) (kq := q.m) (lq := q.pub.params.l) p
  have h' : nCallsN p (ndTI q impl).V ≤
      c * nCallsN p (computeV4 (q.k + 1) q.b q.m q.pub.params.l) := h
  rw [hc] at h'
  refine h'.trans (le_of_eq ?_)
  ring

end Props

/-! ### The native identity -/

section Native

variable (q : GPubT) {X : Type*} {N : ℕ}
variable {Y Xa : Type*} [Fintype Y] [DecidableEq Y] [Fintype Xa] [DecidableEq Xa]

/-- **The native identity of the operation through `impl`**: for the decoder `c₀(X + iY)`, a
public word `z₀` decoded as `0`, unitary primitives `Pw w` at every slot word `w` and an
implementation `impl` of the padded oracles of the sample `wordEquivFin m w` from `Pw w` at every
`w`, `V† R_val V` acts on clean scratch, for the selection-controlled primitives `slotPrim Pw`, as
the label- and slot-selected family `privFamT` of the padded data. -/
theorem nativeOKTI (hq : q.pub.OK) (D : QData (X × Fin (2 ^ q.m)) N q.s q.k q.b)
    (z₀ : Cfg (VW q.b)) (hz₀ : D.val z₀ = 0) (hdec : ∀ z, D.val z = (q.c0 : ℂ) * gauss z)
    (x : X) (Pw : Cfg (Fin q.m) → Query → Reg Y ℂ →L[ℂ] Reg Y ℂ)
    (hPw : ∀ w j, IsUnitary (Pw w j))
    (impl : Query → List (NInstr (PY (q.k + 1) q.b ⊕ Xa) Y Query))
    (himpl : ∀ w, ImplOK (Pw w)
      (prims (R := ℂ) (D.padData z₀ hz₀) (Equiv.refl _) (x, wordEquivFin q.m w)) impl) :
    NativeOK (slotPrim Pw) (ndTI q impl)
      (selOp (tlabFam (P := Reg (Fin (q.k + 1)) ℂ)
        (privFamT q.pub.params (D.padData z₀ hz₀) (Equiv.refl (Cfg (Fin (q.k + 1)))) x q.pub.rho
          q.pub.γ) false)) := by
  have hrange := padData_range D z₀ hz₀
  have hdecP : ∀ e z, (D.padData z₀ hz₀).decode e z = (q.pub.c0 : ℂ) * gauss z := fun e z =>
    (padData_decode D z₀ hz₀ e z).trans (hdec z)
  obtain ⟨k0, hk0⟩ : ∃ m, (D.padData z₀ hz₀).slot m = zIdx (Equiv.refl (Cfg (Fin (q.k + 1)))) := by
    refine (hrange _).2 ⟨fun _ => false, ?_⟩
    unfold zIdx
    congr 1
    funext i
    simp [lowWord]
  have hOK : ∀ w : Cfg (Fin q.m),
      NativeOK (prims (R := ℂ) (D.padData z₀ hz₀) (Equiv.refl _) (x, wordEquivFin q.m w))
        (GateBinaryODETime.atSlot2 (computeV4 (q.k + 1) q.b q.m q.pub.params.l) (oW (q.k + 1))
          q.pub.nd.dec w)
        (selOp (labFam (fun z => elift4 (R := ℂ) (Equiv.refl _)
          (act4 (D.padData z₀ hz₀) (x, wordEquivFin q.m w) (q.pub.params.nodeW z.2) q.pub.rho
            (q.pub.γ * TimeDependentODE.mask (q.pub.params.start z.1) (wordValue w)))) false)) := by
    intro w
    exact nativeOK4 (kq := q.m) (lq := q.pub.params.l) (D.padData z₀ hz₀) (Equiv.refl _) k0 hk0
      (x, wordEquivFin q.m w) (fun z => q.pub.params.nodeW z.2)
      (fun z => q.pub.γ * TimeDependentODE.mask (q.pub.params.start z.1) (wordValue w)) q.pub.rho _
      rfl rfl
      (GateBinaryODETime.atSlot2_public _ (computeV4_valid _ _ _ _) _ _ q.pub.nd_public.dec_indep w)
      (decOK_T q.pub.params (D.padData z₀ hz₀) (Equiv.refl _) k0 x q.c0 hq.c0_pos.ne' hdecP
        q.pub.rho q.pub.γ (q.pub.rho_pos hq).ne' q.pub.F
        (GateBinaryODETime.hRoundT_ne q.pub.params q.pub.ζ hq.ζ_pos hq.ζ_le hq.g_ge hq.ε_pos
          (q.pub.ε_le_one hq) (q.pub.TD_nonneg hq)) w)
  have h := nativeOK_substSlot Pw
    (fun w => prims (R := ℂ) (D.padData z₀ hz₀) (Equiv.refl _) (x, wordEquivFin q.m w))
    hPw (fun w j => prims_isUnitary (D.padData z₀ hz₀) (Equiv.refl _) (x, wordEquivFin q.m w) j)
    himpl (computeV4 (q.k + 1) q.b q.m q.pub.params.l) (computeV4_valid _ _ _ _) (oW (q.k + 1))
    q.pub.nd.dec q.pub.nd_public.dec_indep
    (fun w => labFam (fun z => elift4 (R := ℂ) (Equiv.refl _)
      (act4 (D.padData z₀ hz₀) (x, wordEquivFin q.m w) (q.pub.params.nodeW z.2) q.pub.rho
        (q.pub.γ * TimeDependentODE.mask (q.pub.params.start z.1) (wordValue w)))) false) hOK
  have hfam : (fun y : Cfg (TSel q.pub.params.m q.pub.params.l q.pub.params.m) =>
      labFam (fun z => elift4 (R := ℂ) (Equiv.refl _) (act4 (D.padData z₀ hz₀)
        (x, wordEquivFin q.m (fun i => y (Sum.inr i))) (q.pub.params.nodeW z.2) q.pub.rho
          (q.pub.γ * TimeDependentODE.mask (q.pub.params.start z.1)
            (wordValue (fun i => y (Sum.inr i)))))) false (fun s => y (Sum.inl s))) =
      tlabFam (P := Reg (Fin (q.k + 1)) ℂ)
        (privFamT q.pub.params (D.padData z₀ hz₀) (Equiv.refl (Cfg (Fin (q.k + 1)))) x q.pub.rho
          q.pub.γ) false := by
    funext y
    simp only [labFam, tlabFam, GateODE.adjIf, SlotSim.adjT, Bool.false_eq_true, if_false]
    rw [privFamT_word]
    rfl
  exact (congrArg (fun F => NativeOK (slotPrim Pw) (ndTI q impl) (selOp F)) hfam).mp h

end Native

/-! ### The outcome -/

section Outcome

variable {X : Type*} {N : ℕ} {Zs : Type*} [Fintype Zs] [DecidableEq Zs]
variable {Y Xa : Type*} [Fintype Y] [DecidableEq Y] [Fintype Xa] [DecidableEq Xa]

set_option maxHeartbeats 1600000 in
/-- **The outcome of the general time-dependent solver through any implementation** (every
`T ≥ 0`, represented samples of any sign): for public data with `BTPublicOK0 q.pub` and the public
rescaling outside the zero case, time-indexed sparse access of general size with the decoder
`c₀(X + iY)`, a public word `z₀` decoded as `0`, unitary primitives `Pw w` at every slot word, an
implementation `impl` of the padded oracles of the samples from them on clean ancillas, and every
input as in `GeneralSparseODE.general_time_outcome` with loading and weight-preparation circuits
calling `slotPrim Pw`, the protocol `nprotocol (prepTI q impl loadC wpC) (2g)` has the guarantees
`WOutcome … (ε / 100)` for `slotPrim Pw`, against the marker embedding of `x(T)`. -/
theorem general_time_outcomeI (q : GPubT) (hq : BTPublicOK0 q.pub)
    (hγ : ¬ BTZeroCase q.pub →
      q.γ = GateODEBudget.gammaOf q.T q.etaH q.etaD (2 * q.g) (q.ε / 2))
    (D : QData (X × Fin (2 ^ q.m)) N q.s q.k q.b) (z₀ : Cfg (VW q.b)) (hz₀ : D.val z₀ = 0)
    (hdec : ∀ z, D.val z = (q.c0 : ℂ) * gauss z) (x : X)
    (Pw : Cfg (Fin q.m) → Query → Reg Y ℂ →L[ℂ] Reg Y ℂ) (hPw : ∀ w j, IsUnitary (Pw w j))
    (impl : Query → List (NInstr (PY (q.k + 1) q.b ⊕ Xa) Y Query))
    (himpl : ∀ w, ImplOK (Pw w)
      (prims (R := ℂ) (D.padData z₀ hz₀) (Equiv.refl _) (x, wordEquivFin q.m w)) impl)
    (loadC : List (NInstr ((Fin (q.m + 1) ⊕ Fin q.k) ⊕ Zs) (Fin q.m ⊕ Y) Query))
    (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (q.m + 1) ⊕ Zs) (Fin q.m ⊕ Y) Query))
    (hwpV : ∀ i ∈ wpC, i.Valid)
    (hrH : ∀ r i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaH ^ 2)
    (hcH : ∀ r j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaH ^ 2)
    (hrD : ∀ r i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaD ^ 2)
    (hcD : ∀ r j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaD ^ 2)
    (Jl : Bool × (Fin q.m → Bool) → Reg (Fin q.k) ℂ →L[ℂ] Reg (Fin q.k) ℂ)
    (Wp : Matrix (Cfg (Fin (q.m + 1))) (Cfg (Fin (q.m + 1))) ℂ)
    (G : ℝ → Reg (Fin q.k) ℂ →L[ℂ] Reg (Fin q.k) ℂ) (bf xs : ℝ → Reg (Fin q.k) ℂ)
    (bs : ℕ → Reg (Fin q.k) ℂ) (βG δG βb δb bmax ζs : ℝ) (hζs : 0 ≤ ζs)
    (hload : ApproxOn CleanX (nrun (slotPrim Pw) loadC) (liftB (loadIdeal Jl)) ζs)
    (hwp : ApproxOn CleanX (nrun (slotPrim Pw) wpC) (liftB (matOp Wp)) ζs)
    (hbud : 98304 * GateODEBudget.qOf q.pub.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * q.ζ +
      3 * ζs ≤ 13 * q.pub.params.nu)
    (hR : RobustRestG q D x Jl Wp G bf xs bs βG δG βb δb bmax) :
    WOutcome (prepTI q impl loadC wpC) q.pub.params.ratio (q.ε / 100)
      (q.pub.params.ratio_ge hq.g_ge) (slotPrim Pw) (markEmb q.k (xs q.T)) := by
  have hPs : ∀ j, IsUnitary (slotPrim Pw j) := fun j => slotPrim_isUnitary _ hPw j
  -- the padded data and the padded instance
  have hrange := padData_range D z₀ hz₀
  have hrH' : ∀ r i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart ((D.padData z₀ hz₀).matrix (x, r)) i
      j‖ ^ 2 ≤ q.pub.etaH ^ 2 := by
    intro r i
    rw [padData_zpad, hamiltonianPart_zpad]
    exact zpad_row_le D.hN _ (hrH r) i
  have hcH' : ∀ r j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart ((D.padData z₀ hz₀).matrix (x, r)) i
      j‖ ^ 2 ≤ q.pub.etaH ^ 2 := by
    intro r j
    rw [padData_zpad, hamiltonianPart_zpad]
    exact zpad_col_le D.hN _ (hcH r) j
  have hrD' : ∀ r i, ∑ j, ‖ODEMatrixEnergy.dissipativePart ((D.padData z₀ hz₀).matrix (x, r)) i
      j‖ ^ 2 ≤ q.pub.etaD ^ 2 := by
    intro r i
    rw [padData_zpad, dissipativePart_zpad]
    exact zpad_row_le D.hN _ (hrD r) i
  have hcD' : ∀ r j, ∑ i, ‖ODEMatrixEnergy.dissipativePart ((D.padData z₀ hz₀).matrix (x, r)) i
      j‖ ^ 2 ≤ q.pub.etaD ^ 2 := by
    intro r j
    rw [padData_zpad, dissipativePart_zpad]
    exact zpad_col_le D.hN _ (hcD r) j
  have hR' := hR.padded z₀ hz₀
  have hloadV' : ∀ i ∈ liftC loadC, i.Valid := valid_liftC _ hloadV
  have hload' : ApproxOn CleanX (nrun (slotPrim Pw) (liftC loadC))
      (liftB (loadIdeal (fun c => lowOp (Jl c)))) ζs :=
    approxOn_liftLoad (slotPrim Pw) loadC Jl hζs hload
  have hε0 : (0 : ℝ) < q.ε := hq.ε_pos
  have hεh : q.ε ≤ 1 / 2 := hq.ε_half
  have hg1 : (1 : ℝ) ≤ q.g := hq.g_ge
  have hε2 : (0 : ℝ) < q.ε / 2 := by linarith
  have hQ1 : 1 ≤ GateODEBudget.qOf q.pub.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) :=
    GateRemarks.ODE.one_le_qOf hq.T_nonneg hq.etaH_nonneg hq.etaD_nonneg
      (by linarith) hε2 (by linarith)
  by_cases hz : BTZeroCase q.pub
  · -- the direct source assembly
    have hp := btparams_ok0 hq
    have hpr : prepTI q impl loadC wpC = tzprepC (liftC loadC) wpC := by
      rw [prepTI, if_pos hz]
      rfl
    have h0 : 0 ≤ 98304 * GateODEBudget.qOf q.pub.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
        q.ζ := mul_nonneg (mul_nonneg (by norm_num) (by linarith)) hq.ζ_pos.le
    have hI := robust_tzInstanceOK q.pub hq (D.padData z₀ hz₀) (Equiv.refl _) x hrH' hcH' hrD'
      hcD' (fun c => lowOp (Jl c)) Wp (fun u => zext (G u)) (fun u => markEmb q.k (bf u))
      (fun u => markEmb q.k (xs u)) (fun r => markEmb q.k (bs r)) βG δG βb δb bmax hR'
    rw [hpr]
    exact SourceAccuracyODE.native_time_zero_outcome (S := Fin (q.k + 1)) (Zs := Zs)
      (Z := SZ4 (q.k + 1) q.b ⊕ Xa) (Y := Fin q.m ⊕ Y)
      (J := Query) q.pub.params q.pub.params.a q.pub.params.m q.pub.params.r q.pub.params.K
      q.pub.params.l q.pub.params.f (arTI q Xa).bT (arTI q Xa).bP (arTI q Xa).A hq.T_nonneg
      hq.g_ge hq.ε_pos
      hq.ε_half hp.lamH_nonneg hp.lamD_nonneg (btzeroCase_params hq hz) (liftC loadC) hloadV' wpC
      hwpV (slotPrim Pw) (fun c => lowOp (Jl c)) Wp (HsT (D.padData z₀ hz₀) (Equiv.refl _) x)
      (repairedLs (LsT (D.padData z₀ hz₀) (Equiv.refl _) x) δG) (fun u => zext (G u))
      (fun u => markEmb q.k (bf u)) (fun u => markEmb q.k (xs u)) (fun r => markEmb q.k (bs r))
      βG (3 * δG) βb δb bmax ζs hPs hζs hload' hwp (by linarith) hI
  · -- the native preparation
    have hP := btpublicOK_of hq hz
    obtain ⟨-, hd, -, -, -, -⟩ := GateODEBudget.binary_ode_time_sizes q.pub hP (hγ hz)
    have hd' : (q.pub.params.d : ℝ) ≤
        4096 * GateODEBudget.qOf q.pub.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) := hd
    have hpr : prepTI q impl loadC wpC =
        tnprepC q.pub.params q.pub.UJg (ndTI q impl) (arTI q Xa) (liftC loadC) wpC := by
      rw [prepTI, if_neg hz]
    have hbud' : 24 * (q.pub.params.d : ℝ) * q.ζ + 3 * ζs ≤ 13 * q.pub.params.nu := by
      have hζ0 : (0 : ℝ) ≤ q.ζ := hP.ζ_pos.le
      have := mul_le_mul_of_nonneg_right hd' hζ0
      linarith
    rw [hpr]
    exact SourceAccuracyODE.native_time_outcome q.pub.params (q.pub.params_ok hP) q.pub.UJg
      (hadUJ4_ok q.pub.σ q.pub.hσ) (ndTI q impl) (ndTI_public q (himpl (fun _ => false)).valid)
      (arTI q Xa) q.ζ hP.ζ_pos.le
      (arTI_ok q hP impl) (liftC loadC) hloadV' wpC hwpV (slotPrim Pw) hPs
      ⟨UJop (R := ℂ) q.pub.UJg,
        privFamT q.pub.params (D.padData z₀ hz₀) (Equiv.refl _) x q.pub.rho q.pub.γ,
        fun c => lowOp (Jl c), Wp⟩
      rfl (nativeOKTI q hP D z₀ hz₀ hdec x Pw hPw impl himpl) ζs hζs hload' hwp hbud'
      (HsT (D.padData z₀ hz₀) (Equiv.refl _) x) (LsT (D.padData z₀ hz₀) (Equiv.refl _) x)
      (fun u => zext (G u)) (fun u => markEmb q.k (bf u)) (fun u => markEmb q.k (xs u))
      (fun r => markEmb q.k (bs r)) βG δG βb δb bmax
      (robust_instanceOK q.pub hP (D.padData z₀ hz₀) (Equiv.refl _) hrange x hrH' hcH' hrD' hcD'
        (fun c => lowOp (Jl c)) Wp (fun u => zext (G u)) (fun u => markEmb q.k (bf u))
        (fun u => markEmb q.k (xs u)) (fun r => markEmb q.k (bs r)) βG δG βb δb bmax hR')

end Outcome

end

end SparseHamiltonian.GeneralDecoderODE
