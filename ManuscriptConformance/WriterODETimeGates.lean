import ManuscriptConformance.WriterODEGates
import ManuscriptConformance.GateODETimeGeneral

/-!
# Conformance: Theorem `ode:thm:gates` of general size with a writer, time-dependent coefficients

Theorem `ode:thm:gates` for time-indexed sparse access of general size
(`ode_thm_gates_time_general`), with the value oracle given by a reversible writer of the stored
words of every sample specified on the clean inputs of the valid index pairs only
(`GeneralSparseAccess.QData.Writer` of the time-indexed data, handover item B4).

* `primsTGW Wr x = Σ_w |w⟩⟨w| ⊗ Wr.prims (x, w)`: the coherent sampled-time primitives of the
  writer model (`GateBinary.slotPrim`), which the protocol and the source circuits call;
* `GPubT.ndW`, `GPubT.prepW`, `ndW_public`, `arW_ok`, `ndW_nGates`, `ndW_nCalls`, `nativeOKW`,
  `privGatesW_le`: the private operation (`substSlot` with `GeneralSparseAccess.implPW`) and the
  preparation in the writer model, with the bounds and the native identity of `nd`;
* `general_time_outcome_writer`, `general_time_budget_writer`: the outcome and the budget of
  `general_time_outcome`, `general_time_budget` (the released proofs, with `implOKW` in place of
  `implOK`);
* `ode_thm_gates_time_general_writer`: the endpoint, with the constants of
  `ode_thm_gates_time_general`.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4096

namespace SparseHamiltonian.GeneralSparseODE

noncomputable section
open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
  SparseHamiltonian.GateBinary
open SparseHamiltonian.GeneralSparseAccess
open SparseHamiltonian.OracleCircuit
open GateBinaryODE (SZ4 card_SZ4 mLift computeV4 computeV4_valid computeV4_nGates computeV4_nCalls
  oW elift4 act4 nativeOK4 hadUJ4_ok)
open GateBinaryODETime (PubT privFamT privFamT_word decOK_T HsT LsT)
open ZeroTimeGateODE (BTPublicOK0 BTZeroCase tzprepC btpublicOK_of btparams_ok0
  btzeroCase_params)
open SourceAccuracyODE (WOutcome)
open RepresentedSampleODE.GateTime (RobustRest robust_instanceOK robust_tzInstanceOK repairedLs)
open GatePointerEncoding (wordValue wordEquivFin)
open SparseHamiltonian.GateBitBudget (bitB bitB_nonneg HasBits)
open GateODEBudget (qOf wordsT gammaOf)
open ImprovedODEQueryBudget (logBudget)
open NativeSparseBlockEncoding (Query)
open ODEStateNormalization (unitDirection)
open scoped InnerProduct

/-! ### The coherent sampled-time primitives of the writer model -/

section PrimsW

variable {X : Type*} {N s k b m : ℕ}

/-- **The coherent sampled-time primitives of the writer model**: at the slot word `w` of the slot
wires, the supplied locators and the writer of the sample `wordEquivFin m w`. -/
def primsTGW {D : QData (X × Fin (2 ^ m)) N s k b} (Wr : D.Writer) (x : X) :
    Query → Reg (Fin m ⊕ PY k b) ℂ →L[ℂ] Reg (Fin m ⊕ PY k b) ℂ :=
  slotPrim (fun w => Wr.prims (R := ℂ) (x, wordEquivFin m w))

theorem primsTGW_isUnitary {D : QData (X × Fin (2 ^ m)) N s k b} (Wr : D.Writer) (x : X)
    (j : Query) : IsUnitary (primsTGW Wr x j) :=
  slotPrim_isUnitary _ (fun w j => Wr.prims_isUnitary (x, wordEquivFin m w) j) j

end PrimsW

/-! ### The private operation and the preparation in the writer model -/

namespace GPubT

variable (q : GPubT)

/-- **The private operation in the writer model**: the released label- and slot-selected operation
of the padded problem with every padded call replaced by its implementation from the supplied
locators and a value writer (`GeneralSparseAccess.implPW`, `substSlot`). -/
def ndW (N : ℕ) (z₀ : Cfg (VW q.b)) :
    NativeOp (TSel q.pub.params.m q.pub.params.l q.pub.params.m)
      (Fin q.pub.params.a ⊕ Fin (q.k + 1)) (SZ4 (q.k + 1) q.b ⊕ GeneralSparseAccess.AW q.k q.b)
      (Fin q.m ⊕ PY q.k q.b) Query :=
  substSlot (computeV4 (q.k + 1) q.b q.m q.pub.params.l) (oW (q.k + 1)) q.pub.nd.dec
    (implPW N q.s z₀)

/-- **The preparation of the general problem in the writer model**: `GPubT.prep` with the private
operation `ndW`. -/
def prepW {Zs : Type*} [Fintype Zs] [DecidableEq Zs] (N : ℕ) (z₀ : Cfg (VW q.b))
    (loadC : List (NInstr ((Fin (q.m + 1) ⊕ Fin q.k) ⊕ Zs) (Fin q.m ⊕ PY q.k q.b) Query))
    (wpC : List (NInstr (Fin (q.m + 1) ⊕ Zs) (Fin q.m ⊕ PY q.k q.b) Query)) :
    List (NInstr (TNW q.pub.params (Fin (q.k + 1)) Zs
      (SZ4 (q.k + 1) q.b ⊕ GeneralSparseAccess.AW q.k q.b) q.ar.bT q.ar.bP q.ar.A)
      (Fin q.m ⊕ PY q.k q.b) Query) :=
  if BTZeroCase q.pub then tzprepC (liftC loadC) wpC
  else tnprepC q.pub.params q.pub.UJg (q.ndW N z₀) q.ar (liftC loadC) wpC

theorem ndW_public (N : ℕ) (z₀ : Cfg (VW q.b)) : (q.ndW N z₀).Public :=
  substSlot_public _ (computeV4_valid _ _ _ _) _ _ q.pub.nd_public.dec_indep (valid_implPW N q.s z₀)

theorem arW_ok (hq : q.pub.OK) (N : ℕ) (z₀ : Cfg (VW q.b)) :
    ArithOK q.ar (Sum.inl (Sum.inr (q.ndW N z₀).o)) (q.ndW N z₀).dec q.ζ :=
  arithOK_liftA q.pub.ar _ _ _ (q.pub.ar_ok hq)

/-- The compute circuit has at most `28 (k + 1) + 2 + 6 implG k b` gates. -/
theorem ndW_nGates (N : ℕ) (z₀ : Cfg (VW q.b)) :
    nGatesN (q.ndW N z₀).V ≤ 28 * (q.k + 1) + 2 + implG q.k q.b * 6 := by
  have h := nGatesN_substSlot_le (computeV4 (q.k + 1) q.b q.m q.pub.params.l) (oW (q.k + 1))
    q.pub.nd.dec (implPW N q.s z₀) (implG q.k q.b) (nGatesN_implPW_le N q.s z₀)
  have hg : nGatesN (computeV4 (q.k + 1) q.b q.m q.pub.params.l) = 28 * (q.k + 1) + 2 :=
    computeV4_nGates (q.k + 1) q.b q.m q.pub.params.l
  have hc : nCallsN (fun _ => true) (computeV4 (q.k + 1) q.b q.m q.pub.params.l) = 6 := by
    have := computeV4_nCalls (k := q.k + 1) (b := q.b) (kq := q.m) (lq := q.pub.params.l)
      (fun _ => true)
    simp only [if_true] at this
    exact this
  rw [hg, hc] at h
  exact h

/-- The compute circuit makes at most `6` supplied calls of each kind it calls. -/
theorem ndW_nCalls (N : ℕ) (z₀ : Cfg (VW q.b)) (c : Query → Bool) :
    nCallsN c (q.ndW N z₀).V ≤ 6 * ((if c Query.rowLocation then 1 else 0) +
      (if c Query.columnLocation then 1 else 0) + (if c Query.value then 1 else 0)) := by
  have h := nCallsN_substSlot_le (computeV4 (q.k + 1) q.b q.m q.pub.params.l) (oW (q.k + 1))
    q.pub.nd.dec (kindOK_implPW (k := q.k) (b := q.b) N q.s z₀) c
  have hc := computeV4_nCalls (k := q.k + 1) (b := q.b) (kq := q.m) (lq := q.pub.params.l) c
  have h' : nCallsN c (q.ndW N z₀).V ≤ 3 * nCallsN c (computeV4 (q.k + 1) q.b q.m q.pub.params.l) :=
    h
  rw [hc] at h'
  omega

variable {X : Type*} {N : ℕ}

/-- **The native identity of the operation in the writer model**: as `nativeOK`, for the coherent
sampled-time primitives of the writer model and every writer of the stored words on valid clean
inputs. -/
theorem nativeOKW (hq : q.pub.OK) (D : QData (X × Fin (2 ^ q.m)) N q.s q.k q.b)
    (Wr : D.Writer) (z₀ : Cfg (VW q.b)) (hz₀ : D.val z₀ = 0) (hdec : ∀ z, D.val z = (q.c0 : ℂ) * gauss z)
    (x : X) :
    NativeOK (primsTGW Wr x) (q.ndW N z₀)
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
  have h := nativeOK_substSlot (fun w => Wr.prims (R := ℂ) (x, wordEquivFin q.m w))
    (fun w => prims (R := ℂ) (D.padData z₀ hz₀) (Equiv.refl _) (x, wordEquivFin q.m w))
    (fun w j => Wr.prims_isUnitary (x, wordEquivFin q.m w) j)
    (fun w j => prims_isUnitary (D.padData z₀ hz₀) (Equiv.refl _) (x, wordEquivFin q.m w) j)
    (fun w => implOKW Wr z₀ hz₀ (x, wordEquivFin q.m w))
    (computeV4 (q.k + 1) q.b q.m q.pub.params.l) (computeV4_valid _ _ _ _) (oW (q.k + 1))
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
  exact (congrArg (fun F => NativeOK (primsTGW Wr x) (q.ndW N z₀) (selOp F)) hfam).mp h

/-- **The per-call cost of the time-dependent writer-model operation in the words**: at most
`65944 (𝔴+1)³`. -/
theorem privGatesW_le (N : ℕ) (z₀ : Cfg (VW q.b)) :
    privGates (q.ndW N z₀) q.ar ≤ 65944 * (wordsT q.pub + 1) ^ 3 := by
  have hV := q.ndW_nGates N z₀
  obtain ⟨hGC, -, -, -⟩ := GateODEBudget.binary_time_arith_words q.pub
  have hk : q.k + 1 ≤ wordsT q.pub := by
    show q.pub.kx ≤ wordsT q.pub
    unfold wordsT
    omega
  have hb : q.b ≤ wordsT q.pub := by
    show q.pub.b ≤ wordsT q.pub
    unfold wordsT
    omega
  have hp1 : wordsT q.pub + 1 ≤ (wordsT q.pub + 1) ^ 3 := le_self_pow₀ (by omega) (by norm_num)
  have hl : q.ar.circ.length = q.pub.ar.circ.length := liftA_circ_length _
  have hb2 : q.ar.bP = q.pub.ar.bP := rfl
  have hb3 : q.ar.bT = q.pub.ar.bT := rfl
  have hkx : q.pub.kx = q.k + 1 := rfl
  unfold privGates
  rw [hl, hb2, hb3]
  unfold implG at hV
  omega

end GPubT

/-! ### The outcome in the writer model -/

section OutcomeW

variable {X : Type*} {N : ℕ} {Zs : Type*} [Fintype Zs] [DecidableEq Zs]

set_option maxHeartbeats 1600000 in
/-- **The outcome of the general time-dependent solver in the writer model**: the hypotheses of
`general_time_outcome`, with a writer `Wr` of the stored words of every sample on valid clean inputs
and the loading and weight-preparation circuits within `ζ_s` for the coherent sampled-time
primitives of the writer model `primsTGW Wr x`; the protocol `nprotocol (q.prepW N z₀ loadC wpC)
(2g)` has the guarantees `WOutcome … (ε / 100)` for `primsTGW Wr x`, against the marker embedding of
`x(T)`. -/
theorem general_time_outcome_writer (q : GPubT) (hq : BTPublicOK0 q.pub)
    (hγ : ¬ BTZeroCase q.pub →
      q.γ = GateODEBudget.gammaOf q.T q.etaH q.etaD (2 * q.g) (q.ε / 2))
    (D : QData (X × Fin (2 ^ q.m)) N q.s q.k q.b) (z₀ : Cfg (VW q.b)) (hz₀ : D.val z₀ = 0)
    (hdec : ∀ z, D.val z = (q.c0 : ℂ) * gauss z) (Wr : D.Writer)
    (loadC : List (NInstr ((Fin (q.m + 1) ⊕ Fin q.k) ⊕ Zs) (Fin q.m ⊕ PY q.k q.b) Query))
    (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (q.m + 1) ⊕ Zs) (Fin q.m ⊕ PY q.k q.b) Query))
    (hwpV : ∀ i ∈ wpC, i.Valid) (x : X)
    (hrH : ∀ r i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaH ^ 2)
    (hcH : ∀ r j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaH ^ 2)
    (hrD : ∀ r i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaD ^ 2)
    (hcD : ∀ r j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaD ^ 2)
    (Jl : Bool × (Fin q.m → Bool) → Reg (Fin q.k) ℂ →L[ℂ] Reg (Fin q.k) ℂ)
    (Wp : Matrix (Cfg (Fin (q.m + 1))) (Cfg (Fin (q.m + 1))) ℂ)
    (G : ℝ → Reg (Fin q.k) ℂ →L[ℂ] Reg (Fin q.k) ℂ) (bf xs : ℝ → Reg (Fin q.k) ℂ)
    (bs : ℕ → Reg (Fin q.k) ℂ) (βG δG βb δb bmax ζs : ℝ) (hζs : 0 ≤ ζs)
    (hload : ApproxOn CleanX (nrun (primsTGW Wr x) loadC) (liftB (loadIdeal Jl)) ζs)
    (hwp : ApproxOn CleanX (nrun (primsTGW Wr x) wpC) (liftB (matOp Wp)) ζs)
    (hbud : 98304 * GateODEBudget.qOf q.pub.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * q.ζ +
      3 * ζs ≤ 13 * q.pub.params.nu)
    (hR : RobustRestG q D x Jl Wp G bf xs bs βG δG βb δb bmax) :
    WOutcome (q.prepW N z₀ loadC wpC) q.pub.params.ratio (q.ε / 100)
      (q.pub.params.ratio_ge hq.g_ge) (primsTGW Wr x) (markEmb q.k (xs q.T)) := by
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
  have hload' : ApproxOn CleanX (nrun (primsTGW Wr x) (liftC loadC))
      (liftB (loadIdeal (fun c => lowOp (Jl c)))) ζs :=
    approxOn_liftLoad (primsTGW Wr x) loadC Jl hζs hload
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
    have hpr : q.prepW N z₀ loadC wpC = tzprepC (liftC loadC) wpC := by
      rw [GPubT.prepW, if_pos hz]
      rfl
    have h0 : 0 ≤ 98304 * GateODEBudget.qOf q.pub.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
        q.ζ := mul_nonneg (mul_nonneg (by norm_num) (by linarith)) hq.ζ_pos.le
    have hI := robust_tzInstanceOK q.pub hq (D.padData z₀ hz₀) (Equiv.refl _) x hrH' hcH' hrD'
      hcD' (fun c => lowOp (Jl c)) Wp (fun u => zext (G u)) (fun u => markEmb q.k (bf u))
      (fun u => markEmb q.k (xs u)) (fun r => markEmb q.k (bs r)) βG δG βb δb bmax hR'
    rw [hpr]
    exact SourceAccuracyODE.native_time_zero_outcome (S := Fin (q.k + 1)) (Zs := Zs)
      (Z := SZ4 (q.k + 1) q.b ⊕ GeneralSparseAccess.AW q.k q.b) (Y := Fin q.m ⊕ PY q.k q.b)
      (J := Query) q.pub.params q.pub.params.a q.pub.params.m q.pub.params.r q.pub.params.K
      q.pub.params.l q.pub.params.f q.ar.bT q.ar.bP q.ar.A hq.T_nonneg hq.g_ge hq.ε_pos
      hq.ε_half hp.lamH_nonneg hp.lamD_nonneg (btzeroCase_params hq hz) (liftC loadC) hloadV' wpC
      hwpV (primsTGW Wr x) (fun c => lowOp (Jl c)) Wp
      (GateBinaryODETime.HsT (D.padData z₀ hz₀) (Equiv.refl _) x)
      (repairedLs (GateBinaryODETime.LsT (D.padData z₀ hz₀) (Equiv.refl _) x) δG)
      (fun u => zext (G u))
      (fun u => markEmb q.k (bf u)) (fun u => markEmb q.k (xs u)) (fun r => markEmb q.k (bs r))
      βG (3 * δG) βb δb bmax ζs (primsTGW_isUnitary Wr x) hζs hload' hwp (by linarith) hI
  · -- the native preparation
    have hP := btpublicOK_of hq hz
    obtain ⟨-, hd, -, -, -, -⟩ := GateODEBudget.binary_ode_time_sizes q.pub hP (hγ hz)
    have hd' : (q.pub.params.d : ℝ) ≤
        4096 * GateODEBudget.qOf q.pub.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) := hd
    have hpr : q.prepW N z₀ loadC wpC =
        tnprepC q.pub.params q.pub.UJg (q.ndW N z₀) q.ar (liftC loadC) wpC := by
      rw [GPubT.prepW, if_neg hz]
    have hbud' : 24 * (q.pub.params.d : ℝ) * q.ζ + 3 * ζs ≤ 13 * q.pub.params.nu := by
      have hζ0 : (0 : ℝ) ≤ q.ζ := hP.ζ_pos.le
      have := mul_le_mul_of_nonneg_right hd' hζ0
      linarith
    rw [hpr]
    exact SourceAccuracyODE.native_time_outcome q.pub.params (q.pub.params_ok hP) q.pub.UJg
      (hadUJ4_ok q.pub.σ q.pub.hσ) (q.ndW N z₀) (q.ndW_public N z₀) q.ar q.ζ hP.ζ_pos.le
      (q.arW_ok hP N z₀) (liftC loadC) hloadV' wpC hwpV (primsTGW Wr x) (primsTGW_isUnitary Wr x)
      ⟨UJop (R := ℂ) q.pub.UJg,
        privFamT q.pub.params (D.padData z₀ hz₀) (Equiv.refl _) x q.pub.rho q.pub.γ,
        fun c => lowOp (Jl c), Wp⟩
      rfl (q.nativeOKW hP D Wr z₀ hz₀ hdec x) ζs hζs hload' hwp hbud'
      (GateBinaryODETime.HsT (D.padData z₀ hz₀) (Equiv.refl _) x)
      (GateBinaryODETime.LsT (D.padData z₀ hz₀) (Equiv.refl _) x)
      (fun u => zext (G u)) (fun u => markEmb q.k (bf u)) (fun u => markEmb q.k (xs u))
      (fun r => markEmb q.k (bs r)) βG δG βb δb bmax
      (robust_instanceOK q.pub hP (D.padData z₀ hz₀) (Equiv.refl _) hrange x hrH' hcH' hrD' hcD'
        (fun c => lowOp (Jl c)) Wp (fun u => zext (G u)) (fun u => markEmb q.k (bf u))
        (fun u => markEmb q.k (xs u)) (fun r => markEmb q.k (bs r)) βG δG βb δb bmax hR')

end OutcomeW

/-! ### The budget in the writer model -/

section BudgetW

variable {Zs : Type*} [Fintype Zs] [DecidableEq Zs]

set_option maxHeartbeats 8000000 in
/-- **The budget of the time-dependent general solver in the writer model**: the bounds of
`general_time_budget` for the protocol `nprotocol (q.prepW N z₀ loadC wpC) (2g)` (valid trials,
gates in every history, qubits and calls of every kind of the primitives of the writer model; each
writer call or inverse writer call counted as a call of the value kind). -/
theorem general_time_budget_writer (bd : ℕ) (q : GPubT) (hq : BTPublicOK0 q.pub)
    (hγ : if BTZeroCase q.pub then HasBits bd q.γ
      else q.γ = gammaOf q.T q.etaH q.etaD (2 * q.g) (q.ε / 2))
    (hζ : q.pub.params.nu ≤ 196608 * qOf q.pub.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * q.ζ)
    (hb : q.b ≤ bd) (hc0 : HasBits bd q.c0) (hT : HasBits bd q.T) (hH : HasBits bd q.etaH)
    (hD : HasBits bd q.etaD) (N : ℕ) (z₀ : Cfg (VW q.b))
    (loadC : List (NInstr ((Fin (q.m + 1) ⊕ Fin q.k) ⊕ Zs) (Fin q.m ⊕ PY q.k q.b) Query))
    (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (q.m + 1) ⊕ Zs) (Fin q.m ⊕ PY q.k q.b) Query))
    (hwpV : ∀ i ∈ wpC, i.Valid) :
    (∀ j, ∀ i ∈ trialN (q.prepW N z₀ loadC wpC) j, i.Valid) ∧
    ((nprotocol (q.prepW N z₀ loadC wpC) q.pub.params.ratio
        (q.pub.params.ratio_ge hq.g_ge)).worstCost wGateN : ℝ) ≤
      2 * 10 ^ 20 * q.g * (qOf q.pub.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
          (bitB bd (2 ^ (q.k + 1)) (2 ^ q.m) (2 ^ q.m)
            (qOf q.pub.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ 3 +
        ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) + Fintype.card Zs) ∧
    (Fintype.card (q.reg Zs) : ℝ) ≤
      3 * 10 ^ 11 * (bitB bd (2 ^ (q.k + 1)) (2 ^ q.m) (2 ^ q.m)
          (qOf q.pub.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ 3 +
        2 * Fintype.card Zs ∧
    (∀ c : Query → Bool, ((nprotocol (q.prepW N z₀ loadC wpC) q.pub.params.ratio
        (q.pub.params.ratio_ge hq.g_ge)).worstCost (wCallN c) : ℝ) ≤
      (if BTZeroCase q.pub then 0 else
        23592960 * q.g * qOf q.pub.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
          ((if c Query.rowLocation then 1 else 0) + (if c Query.columnLocation then 1 else 0) +
            (if c Query.value then 1 else 0))) +
        80 * q.g * ((nCallsN c loadC : ℝ) + 2 * nCallsN c wpC)) := by
  have hε1 : q.ε ≤ 1 := hq.ε_half.trans (by norm_num)
  have hε0 : (0 : ℝ) < q.ε := hq.ε_pos
  have hεh : q.ε ≤ 1 / 2 := hq.ε_half
  have hg1 : (1 : ℝ) ≤ q.g := hq.g_ge
  have hg0 : 0 ≤ q.g := le_trans zero_le_one hq.g_ge
  have hg2 : (1 : ℝ) ≤ 2 * q.g := by linarith
  have hε2 : (0 : ℝ) < q.ε / 2 := by linarith
  have hε2' : q.ε / 2 ≤ 1 := by linarith
  have hQ1 : 1 ≤ qOf q.pub.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) :=
    GateRemarks.ODE.one_le_qOf hq.T_nonneg hq.etaH_nonneg hq.etaD_nonneg hg2 hε2 hε2'
  have hℓ1 : 1 ≤ logBudget (2 * q.g) (q.ε / 2) :=
    ImprovedODEQueryBudget.logBudget_ge_one (2 * q.g) (q.ε / 2) hg2 hε2 hε2'
  have hQg : 0 ≤ qOf q.pub.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * q.g := by positivity
  have hB0 : 0 ≤ bitB bd (2 ^ (q.k + 1)) (2 ^ q.m) (2 ^ q.m)
      (qOf q.pub.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε :=
    bitB_nonneg bd _ _ _ hQg hq.ε_pos hε1
  -- the words in `𝔟'`
  have hw : (wordsT q.pub : ℝ) + logBudget (2 * q.g) (q.ε / 2) ≤
      300 * (bitB bd (2 ^ (q.k + 1)) (2 ^ q.m) (2 ^ q.m)
        (qOf q.pub.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) := by
    by_cases hz : BTZeroCase q.pub
    · rw [if_pos hz] at hγ
      exact GateRemarks.ODE.zero_wordsT_le bd q.pub hq hz hγ hζ hb hc0 hH hD
    · rw [if_neg hz] at hγ
      exact GateBitBudget.wordsT_le bd q.pub (btpublicOK_of hq hz) hγ hζ hb hc0 hT hH hD
  generalize hBdef : bitB bd (2 ^ (q.k + 1)) (2 ^ q.m) (2 ^ q.m)
    (qOf q.pub.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε = B at hB0 hw ⊢
  have hwr0 : (0 : ℝ) ≤ wordsT q.pub := Nat.cast_nonneg _
  have hY1 : 1 ≤ (B + 1) ^ 3 := one_le_pow₀ (by linarith)
  have hZ0 : (0 : ℝ) ≤ Fintype.card Zs := Nat.cast_nonneg _
  have hG0 : (0 : ℝ) ≤ (nGatesN loadC : ℝ) + 2 * nGatesN wpC := by positivity
  -- the register
  have hspace : (Fintype.card (q.reg Zs) : ℝ) ≤ 3 * 10 ^ 11 * (B + 1) ^ 3 +
      2 * Fintype.card Zs := by
    have h1 : (Fintype.card (q.reg Zs) : ℝ) ≤ 10016 * ((wordsT q.pub : ℝ) + 1) ^ 3 +
        2 * Fintype.card Zs := by exact_mod_cast q.card_reg_le Zs
    have hcube := GateBitBudget.cube_le hwr0 hB0 (c := 300) (by linarith)
    have : (10016 : ℝ) * ((wordsT q.pub : ℝ) + 1) ^ 3 ≤ 10016 * ((300 + 1) ^ 3 * (B + 1) ^ 3) :=
      mul_le_mul_of_nonneg_left hcube (by norm_num)
    linarith
  have hloadV' : ∀ i ∈ liftC loadC, i.Valid := valid_liftC _ hloadV
  have hGl : nGatesN (liftC loadC) = nGatesN loadC := nGatesN_liftC _
  have hCl : ∀ p : Query → Bool, nCallsN p (liftC loadC) = nCallsN p loadC :=
    fun p => nCallsN_liftC p _
  have hr : q.pub.params.ratio = 2 * q.g := rfl
  by_cases hz : BTZeroCase q.pub
  · -- the direct source assembly
    have hp := btparams_ok0 hq
    obtain ⟨hV, -, -, hWG, hWC, -, hcardZ, -⟩ := ZeroTimeGateODE.native_ode_time_solver_zero
      (S := Fin (q.k + 1)) (Zs := Zs) (Z := SZ4 (q.k + 1) q.b ⊕ GeneralSparseAccess.AW q.k q.b)
      (Y := Fin q.m ⊕ PY q.k q.b) (J := Query) q.pub.params q.pub.params.a q.pub.params.m
      q.pub.params.r q.pub.params.K q.pub.params.l q.pub.params.f q.ar.bT q.ar.bP q.ar.A
      hq.T_nonneg hq.g_ge hq.ε_pos hq.ε_half hp.lamH_nonneg hp.lamD_nonneg
      (btzeroCase_params hq hz) (liftC loadC) hloadV' wpC hwpV
    have hpr : q.prepW N z₀ loadC wpC = tzprepC (liftC loadC) wpC := by
      rw [GPubT.prepW, if_pos hz]
      rfl
    have htest : Fintype.card (GateODE.AW q.pub.params.a q.pub.params.m q.pub.params.r
        q.pub.params.K q.pub.params.m q.pub.params.l q.pub.params.f) +
        Fintype.card (XW (SZ4 (q.k + 1) q.b ⊕ GeneralSparseAccess.AW q.k q.b) q.ar.bT q.ar.bP
          q.ar.A) + Fintype.card Zs + Fintype.card (Fin (q.k + 1)) ≤
        Fintype.card (q.reg Zs) := by
      have h1 := (hcardZ : Fintype.card (q.reg Zs) = _)
      have h2 : Fintype.card (XW (SZ4 (q.k + 1) q.b ⊕ GeneralSparseAccess.AW q.k q.b) q.ar.bT
          q.ar.bP q.ar.A) = Fintype.card (SZ4 (q.k + 1) q.b ⊕ GeneralSparseAccess.AW q.k q.b) +
            q.ar.bT + q.ar.bP + q.ar.A + 3 := by
        simp only [XW, AWr, Fintype.card_sum, Fintype.card_fin]
        ring
      rw [h1, h2]
      omega
    have htest' : (Fintype.card (GateODE.AW q.pub.params.a q.pub.params.m q.pub.params.r
        q.pub.params.K q.pub.params.m q.pub.params.l q.pub.params.f) : ℝ) +
        Fintype.card (XW (SZ4 (q.k + 1) q.b ⊕ GeneralSparseAccess.AW q.k q.b) q.ar.bT q.ar.bP
          q.ar.A) + Fintype.card Zs + Fintype.card (Fin (q.k + 1)) ≤
        Fintype.card (q.reg Zs) := by
      exact_mod_cast htest
    refine ⟨?_, ?_, hspace, ?_⟩
    · rw [hpr]
      exact hV
    · -- gates
      rw [hpr]
      have hWG' : ((nprotocol (tzprepC (liftC loadC) wpC : List (NInstr (q.reg Zs)
          (Fin q.m ⊕ PY q.k q.b) Query)) q.pub.params.ratio
          (q.pub.params.ratio_ge hq.g_ge)).worstCost wGateN : ℝ) ≤
          40 * q.pub.params.ratio * ((nGatesN (liftC loadC) + 2 * nGatesN wpC : ℕ) : ℝ) +
            20 * q.pub.params.ratio * (4 * ((Fintype.card (GateODE.AW q.pub.params.a
              q.pub.params.m q.pub.params.r q.pub.params.K q.pub.params.m q.pub.params.l
              q.pub.params.f) : ℝ) +
              Fintype.card (XW (SZ4 (q.k + 1) q.b ⊕ GeneralSparseAccess.AW q.k q.b) q.ar.bT
                q.ar.bP q.ar.A) + Fintype.card Zs + Fintype.card (Fin (q.k + 1))) + 3) := hWG
      rw [hGl] at hWG'
      push_cast at hWG'
      refine hWG'.trans ?_
      rw [hr]
      have h1 := mul_le_mul_of_nonneg_left htest' hg0
      have h2 : q.g * (Fintype.card (q.reg Zs) : ℝ) ≤
          q.g * (3 * 10 ^ 11 * (B + 1) ^ 3 + 2 * Fintype.card Zs) :=
        mul_le_mul_of_nonneg_left hspace hg0
      have h3 : q.g * (B + 1) ^ 3 ≤ q.g * (qOf q.pub.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
          (B + 1) ^ 3) :=
        mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (by linarith) hQ1) hg0
      have h4 : q.g * 1 ≤ q.g * (qOf q.pub.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
          (B + 1) ^ 3) :=
        mul_le_mul_of_nonneg_left (one_le_mul_of_one_le_of_one_le hQ1 hY1) hg0
      have h5 : 0 ≤ q.g * ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) := mul_nonneg hg0 hG0
      have h6 : 0 ≤ q.g * (Fintype.card Zs : ℝ) := mul_nonneg hg0 hZ0
      nlinarith
    · -- calls
      intro c
      rw [hpr, if_pos hz, zero_add]
      have hW : ((nprotocol (tzprepC (liftC loadC) wpC : List (NInstr (q.reg Zs)
          (Fin q.m ⊕ PY q.k q.b) Query)) q.pub.params.ratio
          (q.pub.params.ratio_ge hq.g_ge)).worstCost (wCallN c) : ℝ) ≤
          40 * q.pub.params.ratio * ((nCallsN c (liftC loadC) + 2 * nCallsN c wpC : ℕ) : ℝ) :=
        hWC c
      rw [hCl] at hW
      refine hW.trans (le_of_eq ?_)
      rw [hr]
      push_cast
      ring
  · -- the native preparation
    have hP := btpublicOK_of hq hz
    rw [if_neg hz] at hγ
    obtain ⟨-, hd, -, -, hJ, -⟩ := GateODEBudget.binary_ode_time_sizes q.pub hP hγ
    have hd' : (q.pub.params.d : ℝ) ≤
        4096 * qOf q.pub.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) := hd
    have hJ' : (q.pub.params.J : ℝ) ≤ 60 * qOf q.pub.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
        logBudget (2 * q.g) (q.ε / 2) := hJ
    have hpr : q.prepW N z₀ loadC wpC =
        tnprepC q.pub.params q.pub.UJg (q.ndW N z₀) q.ar (liftC loadC) wpC := by
      rw [GPubT.prepW, if_neg hz]
    obtain ⟨hV, -, hC, -, hWC, -, -⟩ := native_ode_time_solver q.pub.params (q.pub.params_ok hP)
      q.pub.UJg (hadUJ4_ok q.pub.σ q.pub.hσ) (q.ndW N z₀) (q.ndW_public N z₀) q.ar q.ζ hP.ζ_pos.le
      (q.ar_ok hP N z₀) (liftC loadC) hloadV' wpC hwpV
    have hgc := native_ode_time_gate_count q.pub.params (q.pub.params_ok hP) q.pub.UJg
      (hadUJ4_ok q.pub.σ q.pub.hσ) (q.ndW N z₀) (q.ndW_public N z₀) q.ar q.ζ hP.ζ_pos.le
      (q.ar_ok hP N z₀) (liftC loadC) hloadV' wpC hwpV
    refine ⟨?_, ?_, hspace, ?_⟩
    · rw [hpr]
      exact hV
    · -- gates
      rw [hpr]
      have hUJl : q.pub.UJg.length = q.pub.σ + 3 := GateBinaryODE.hadUJ4_length q.pub.σ q.pub.hσ
      have hPG := q.privGatesW_le N z₀
      have hAp := q.wires_le
      have hcZ := q.card_Zg
      have hgc' : ((nprotocol (tnprepC q.pub.params q.pub.UJg (q.ndW N z₀) q.ar (liftC loadC) wpC)
          q.pub.params.ratio (q.pub.params.ratio_ge hq.g_ge)).worstCost wGateN : ℝ) ≤
          18000 * q.pub.params.g * (((q.pub.params.d : ℝ) + 1) * ((q.pub.params.a : ℝ) +
            q.pub.params.m + q.pub.params.r + 1 + ((q.pub.UJg.length : ℕ) : ℝ) +
            ((privGates (q.ndW N z₀) q.ar : ℕ) : ℝ)) +
            ((q.pub.params.J : ℝ) + 2) * ((q.pub.params.l : ℝ) + 1) +
            ((nGatesN (liftC loadC) : ℝ) + 2 * nGatesN wpC) +
            ((Fintype.card (Fin (q.k + 1)) : ℝ) + Fintype.card Zs +
              Fintype.card (SZ4 (q.k + 1) q.b ⊕ GeneralSparseAccess.AW q.k q.b) + q.ar.bT +
              q.ar.bP + q.ar.A)) := hgc
      rw [hUJl, hGl, Fintype.card_fin, hcZ] at hgc'
      have hgg : q.pub.params.g = q.g := rfl
      rw [hgg] at hgc'
      have hSm : (q.k + 1 : ℝ) + q.pub.σ + q.pub.params.m + q.pub.params.r ≤
          2 * (wordsT q.pub : ℝ) := by
        have hσ := q.pub.hσ
        have : q.pub.kx + q.pub.σ + q.pub.params.m + q.pub.params.r ≤ 2 * wordsT q.pub := by
          unfold wordsT
          omega
        exact_mod_cast this
      have hl : (q.pub.params.l : ℝ) ≤ wordsT q.pub := by
        have : q.pub.params.l ≤ wordsT q.pub := by
          unfold wordsT
          omega
        exact_mod_cast this
      have hPG' : ((privGates (q.ndW N z₀) q.ar : ℕ) : ℝ) ≤
          65944 * ((wordsT q.pub : ℝ) + 1) ^ 3 := by
        exact_mod_cast hPG
      have hcube := GateBitBudget.cube_le (add_nonneg hwr0 (by linarith)) hB0 (c := 300) hw
      have e1 : ((q.pub.params.a : ℕ) : ℝ) = (q.k : ℝ) + 4 := by
        show ((q.k + 1 + 3 : ℕ) : ℝ) = _
        push_cast
        ring
      generalize hQd : qOf (q.pub.s : ℝ) q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) = Q
        at hQ1 hd' hJ' ⊢
      have hXs0 : (0 : ℝ) ≤ ((q.pub.params.a : ℕ) : ℝ) + q.pub.params.m + q.pub.params.r + 1 +
          ((q.pub.σ + 3 : ℕ) : ℝ) + ((privGates (q.ndW N z₀) q.ar : ℕ) : ℝ) := by
        have h1 : (0 : ℝ) ≤ ((q.pub.params.a : ℕ) : ℝ) := Nat.cast_nonneg _
        have h2 : (0 : ℝ) ≤ (q.pub.params.m : ℝ) := Nat.cast_nonneg _
        have h3 : (0 : ℝ) ≤ (q.pub.params.r : ℝ) := Nat.cast_nonneg _
        have h4 : (0 : ℝ) ≤ ((q.pub.σ + 3 : ℕ) : ℝ) := Nat.cast_nonneg _
        have h5 : (0 : ℝ) ≤ ((privGates (q.ndW N z₀) q.ar : ℕ) : ℝ) := Nat.cast_nonneg _
        linarith
      have hAw0 : (0 : ℝ) ≤ ((q.k + 1 : ℕ) : ℝ) + Fintype.card Zs +
          ((12 * q.k + 12 + 6 * q.b : ℕ) : ℝ) + q.ar.bT + q.ar.bP + q.ar.A := by
        have h1 : (0 : ℝ) ≤ ((q.k + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
        have h2 : (0 : ℝ) ≤ ((12 * q.k + 12 + 6 * q.b : ℕ) : ℝ) := Nat.cast_nonneg _
        have h3 : (0 : ℝ) ≤ (q.ar.bT : ℝ) := Nat.cast_nonneg _
        have h4 : (0 : ℝ) ≤ (q.ar.bP : ℝ) := Nat.cast_nonneg _
        have h5 : (0 : ℝ) ≤ (q.ar.A : ℝ) := Nat.cast_nonneg _
        linarith
      have key1 := GateODEBudget.gate_budget_arith' 18000 q.g Q
        (logBudget (2 * q.g) (q.ε / 2)) (q.pub.params.d : ℝ) (q.pub.params.J : ℝ)
        (q.pub.params.l : ℝ)
        (((q.pub.params.a : ℕ) : ℝ) + q.pub.params.m + q.pub.params.r + 1 +
          ((q.pub.σ + 3 : ℕ) : ℝ) + ((privGates (q.ndW N z₀) q.ar : ℕ) : ℝ))
        ((nGatesN loadC : ℝ) + 2 * nGatesN wpC)
        (((q.k + 1 : ℕ) : ℝ) + Fintype.card Zs + ((12 * q.k + 12 + 6 * q.b : ℕ) : ℝ) + q.ar.bT +
          q.ar.bP + q.ar.A)
        (by norm_num) hg0 hQ1 hℓ1 hd' hJ' (Nat.cast_nonneg _) hXs0 hG0 hAw0
      have key2 := words_gate_arith_g 73746000 (6 * 10 ^ 12) q.g Q (logBudget (2 * q.g) (q.ε / 2))
        (wordsT q.pub : ℝ) ((privGates (q.ndW N z₀) q.ar : ℕ) : ℝ)
        ((q.k + 1 : ℝ) + q.pub.σ + q.pub.params.m + q.pub.params.r)
        (q.pub.params.l : ℝ) ((nGatesN loadC : ℝ) + 2 * nGatesN wpC)
        (Fintype.card Zs : ℝ)
        (((q.k + 1 : ℕ) : ℝ) + ((12 * q.k + 12 + 6 * q.b : ℕ) : ℝ) + q.ar.bT + q.ar.bP + q.ar.A)
        (by norm_num) (by norm_num) hg0 hQ1 hℓ1 hwr0 hPG' hSm (Nat.cast_nonneg _) hl hAp hG0 hZ0
      have key3 := GateBitBudget.budget_mono (c := 6 * 10 ^ 12) (C := 2 * 10 ^ 20)
        (k := (300 + 1) ^ 3) (g := q.g) (Q := Q)
        (a := ((wordsT q.pub : ℝ) + logBudget (2 * q.g) (q.ε / 2) + 1) ^ 3)
        (b := (B + 1) ^ 3) (S₁ := (nGatesN loadC : ℝ) + 2 * nGatesN wpC)
        (S₂ := (Fintype.card Zs : ℝ)) (by norm_num) hg0 (by linarith) (by positivity) hG0 hZ0
        (by norm_num) hcube (by norm_num)
      have e2 : 4097 * 18000 * q.g * (Q * ((((q.pub.params.a : ℕ) : ℝ) + q.pub.params.m +
            q.pub.params.r + 1 + ((q.pub.σ + 3 : ℕ) : ℝ) +
            ((privGates (q.ndW N z₀) q.ar : ℕ) : ℝ)) + 1 +
            logBudget (2 * q.g) (q.ε / 2) * ((q.pub.params.l : ℝ) + 1)) +
            ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) +
            (((q.k + 1 : ℕ) : ℝ) + Fintype.card Zs + ((12 * q.k + 12 + 6 * q.b : ℕ) : ℝ) +
              q.ar.bT + q.ar.bP + q.ar.A)) =
          73746000 * q.g * (Q * (((privGates (q.ndW N z₀) q.ar : ℕ) : ℝ) +
            ((q.k + 1 : ℝ) + q.pub.σ + q.pub.params.m + q.pub.params.r) +
            logBudget (2 * q.g) (q.ε / 2) * ((q.pub.params.l : ℝ) + 1) + 8) +
            ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) +
            ((Fintype.card Zs : ℝ) + (((q.k + 1 : ℕ) : ℝ) + ((12 * q.k + 12 + 6 * q.b : ℕ) : ℝ) +
              q.ar.bT + q.ar.bP + q.ar.A))) := by
        rw [e1]
        push_cast
        ring
      have hgc'' : ((nprotocol (tnprepC q.pub.params q.pub.UJg (q.ndW N z₀) q.ar (liftC loadC) wpC)
          q.pub.params.ratio (q.pub.params.ratio_ge hq.g_ge)).worstCost wGateN : ℝ) ≤
          18000 * q.g * (((q.pub.params.d : ℝ) + 1) * (((q.pub.params.a : ℕ) : ℝ) +
            q.pub.params.m + q.pub.params.r + 1 + ((q.pub.σ + 3 : ℕ) : ℝ) +
            ((privGates (q.ndW N z₀) q.ar : ℕ) : ℝ)) +
            ((q.pub.params.J : ℝ) + 2) * ((q.pub.params.l : ℝ) + 1) +
            ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) +
            (((q.k + 1 : ℕ) : ℝ) + Fintype.card Zs + ((12 * q.k + 12 + 6 * q.b : ℕ) : ℝ) +
              q.ar.bT + q.ar.bP + q.ar.A)) := by
        refine hgc'.trans (le_of_eq ?_)
        push_cast
        ring
      exact hgc''.trans (key1.trans (le_of_eq e2 |>.trans (key2.trans key3)))
    · -- calls
      intro c
      rw [hpr, if_neg hz]
      have hI0 : (0 : ℝ) ≤ (if c Query.rowLocation then 1 else 0) +
          (if c Query.columnLocation then 1 else 0) + (if c Query.value then 1 else 0) := by
        split_ifs <;> norm_num
      have hcV := q.ndW_nCalls N z₀ c
      have hcP : (nCallsN c (tnprepC q.pub.params q.pub.UJg (q.ndW N z₀) q.ar (liftC loadC) wpC) :
          ℝ) ≤ 12 * (q.pub.params.d : ℝ) * (6 *
            ((if c Query.rowLocation then 1 else 0) + (if c Query.columnLocation then 1 else 0) +
              (if c Query.value then 1 else 0))) +
          ((nCallsN c loadC : ℝ) + 2 * nCallsN c wpC) := by
        have h1 : nCallsN c (tnprepC q.pub.params q.pub.UJg (q.ndW N z₀) q.ar (liftC loadC) wpC) ≤
            12 * q.pub.params.d * nCallsN c (q.ndW N z₀).V + nCallsN c (liftC loadC) +
              2 * nCallsN c wpC := hC c
        rw [hCl] at h1
        have h2 : nCallsN c (tnprepC q.pub.params q.pub.UJg (q.ndW N z₀) q.ar (liftC loadC) wpC) ≤
            12 * q.pub.params.d * (6 *
              ((if c Query.rowLocation then 1 else 0) + (if c Query.columnLocation then 1 else 0) +
                (if c Query.value then 1 else 0))) + nCallsN c loadC + 2 * nCallsN c wpC :=
          h1.trans (Nat.add_le_add_right (Nat.add_le_add_right
            (Nat.mul_le_mul_left _ hcV) _) _)
        have h3 : ((nCallsN c (tnprepC q.pub.params q.pub.UJg (q.ndW N z₀) q.ar (liftC loadC) wpC) :
            ℕ) : ℝ) ≤ ((12 * q.pub.params.d * (6 *
              ((if c Query.rowLocation then 1 else 0) + (if c Query.columnLocation then 1 else 0) +
                (if c Query.value then 1 else 0))) + nCallsN c loadC + 2 * nCallsN c wpC : ℕ) :
                  ℝ) := by
          exact_mod_cast h2
        refine h3.trans (le_of_eq ?_)
        push_cast
        split_ifs <;> ring
      have hW : ((nprotocol (tnprepC q.pub.params q.pub.UJg (q.ndW N z₀) q.ar (liftC loadC) wpC)
          q.pub.params.ratio (q.pub.params.ratio_ge hq.g_ge)).worstCost (wCallN c) : ℝ) ≤
          40 * q.pub.params.ratio * (nCallsN c (tnprepC q.pub.params q.pub.UJg (q.ndW N z₀) q.ar
            (liftC loadC) wpC) : ℝ) := hWC c
      generalize hQd : qOf (q.pub.s : ℝ) q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) = Q at hd' ⊢
      generalize hId : ((if c Query.rowLocation then 1 else 0) +
          (if c Query.columnLocation then 1 else 0) + (if c Query.value then 1 else 0) : ℝ) = I
        at hI0 hcP ⊢
      have h4 := mul_le_mul_of_nonneg_left hd' (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤
        80 * 72) hg0) hI0)
      have h5 := mul_le_mul_of_nonneg_left hcP (mul_nonneg (by norm_num : (0 : ℝ) ≤ 80) hg0)
      have e6 : 80 * q.g * (12 * (q.pub.params.d : ℝ) * (6 * I) + ((nCallsN c loadC : ℝ) +
          2 * nCallsN c wpC)) = 80 * 72 * q.g * I * (q.pub.params.d : ℝ) +
          80 * q.g * ((nCallsN c loadC : ℝ) + 2 * nCallsN c wpC) := by ring
      have e7 : 80 * 72 * q.g * I * (4096 * Q) = 23592960 * q.g * Q * I := by ring
      have e8 : 40 * q.pub.params.ratio * (nCallsN c (tnprepC q.pub.params q.pub.UJg (q.ndW N z₀)
          q.ar (liftC loadC) wpC) : ℝ) = 80 * q.g * (nCallsN c (tnprepC q.pub.params q.pub.UJg
            (q.ndW N z₀) q.ar (liftC loadC) wpC) : ℝ) := by
        rw [hr]
        ring
      rw [e6] at h5
      rw [e7] at h4
      rw [e8] at hW
      exact hW.trans (h5.trans (add_le_add h4 le_rfl))

end BudgetW

end

end SparseHamiltonian.GeneralSparseODE

namespace ManuscriptConformance

noncomputable section
open ContinuousLinearMap SparseHamiltonian SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
  SparseHamiltonian.GateBinary SparseHamiltonian.GateBitBudget SparseHamiltonian.GeneralSparseAccess
open SparseHamiltonian.GeneralSparseODE (GPubT markEmb padLift primsTG primsTGW)
open SparseHamiltonian.GateBinaryODETime (PubT)
open SparseHamiltonian.ZeroTimeGateODE (BTPublicOK0 BTZeroCase)
open NativeSparseBlockEncoding (Query)
open scoped InnerProduct

universe u

/-! ### Theorem `ode:thm:gates` of general size with a writer, time-dependent coefficients -/

set_option maxHeartbeats 8000000 in
/-- **Theorem `ode:thm:gates` for sparse access of general size with a writer, time-dependent
coefficients, special case under the package's uniform-mesh conditions** (handover item B4). The
hypotheses, constants and conclusions of `ode_thm_gates_time_general`, for the protocol
`nprotocol ((odePubTG …).prepW N 0 loadC wpC) (2ḡ)` (fixed before the writer and the instance):
the private operation calls the supplied locators and a time-indexed value writer through
`GeneralSparseAccess.implPW`, with the gates and calls of `implP`; valid trials, the gate, qubit
and call bounds (writer calls counted as value calls), and for **every writer of the stored words of
every sample on valid clean inputs** (`GeneralSparseAccess.QData.Writer` of the time-indexed data)
and every instance with the uniform-mesh conditions and loading and weight-preparation circuits
within `ν = ε/(10⁴ ḡ)` for the coherent sampled-time primitives of the writer model
(`primsTGW`): success at least `2/3`, conditional output within trace distance `ε` of `x(T)/‖x(T)‖`
on the index register (marker clean), and every successful trial within `ε` of it up to a global
phase. Formal restrictions: `formal_binaryDecoder`, `formal_gbarOne`, `formal_uniformMeshG`. -/
theorem ode_thm_gates_time_general_writer :
    ∃ C : ℝ, 0 < C ∧
      ∀ {X : Type u} {N s k b : ℕ} (bd : ℕ) (c0 etaH etaD T gbar ε : ℝ) (m : ℕ)
        (D : GeneralSparseAccess.QData (X × Fin (2 ^ m)) N s k b),
        odeMeshG k s D.s_le_pow b c0 etaH etaD T gbar ε ≤ m →
        2 ^ k < 2 * N → formal_binaryDecoder D c0 → comp_bits b bd [c0, T, etaH, etaD] →
        ∀ (hg : formal_gbarOne gbar) {Zs : Type} [Fintype Zs] [DecidableEq Zs]
          (loadC : List (NInstr ((Fin (m + 1) ⊕ Fin k) ⊕ Zs) (Fin m ⊕ PY k b) Query))
          (wpC : List (NInstr (Fin (m + 1) ⊕ Zs) (Fin m ⊕ PY k b) Query)),
          (∀ i ∈ loadC, i.Valid) → (∀ i ∈ wpC, i.Valid) →
          0 ≤ etaH → 0 ≤ etaD → 0 ≤ T → 0 < ε → ε ≤ 1 / 2 →
          (∀ j, ∀ i ∈ trialN ((odePubTG k s D.s_le_pow b c0 etaH etaD T gbar ε m).prepW N
            (fun _ => false) loadC wpC) j, i.Valid) ∧
          ((nprotocol ((odePubTG k s D.s_le_pow b c0 etaH etaD T gbar ε m).prepW N
              (fun _ => false) loadC wpC) (2 * gbar) (one_le_two_mul hg)).worstCost wGateN : ℝ) ≤
            C * gbar * (odeShape s T etaH etaD gbar ε *
                (bitB bd N (2 ^ m) (2 ^ m) (odeShape s T etaH etaD gbar ε) gbar ε + 1) ^ 3 +
              ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) + Fintype.card Zs) ∧
          (odeQubitsTG (odePubTG k s D.s_le_pow b c0 etaH etaD T gbar ε m) Zs : ℝ) ≤
            C * (bitB bd N (2 ^ m) (2 ^ m) (odeShape s T etaH etaD gbar ε) gbar ε + 1) ^ 3 +
              C * Fintype.card Zs ∧
          (∀ c : Query → Bool,
            ((nprotocol ((odePubTG k s D.s_le_pow b c0 etaH etaD T gbar ε m).prepW N
              (fun _ => false) loadC wpC) (2 * gbar) (one_le_two_mul hg)).worstCost
                (wCallN c) : ℝ) ≤
            (if T = 0 ∨ etaH + etaD = 0 then 0 else
              C * gbar * odeShape s T etaH etaD gbar ε *
                ((if c Query.rowLocation then 1 else 0) +
                  (if c Query.columnLocation then 1 else 0) + (if c Query.value then 1 else 0))) +
            C * gbar * ((nCallsN c loadC : ℝ) + 2 * nCallsN c wpC)) ∧
          ∀ (Wr : GeneralSparseAccess.QData.Writer D) (x : X),
            (∀ r i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤
              etaH ^ 2) →
            (∀ r j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤
              etaH ^ 2) →
            (∀ r i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤
              etaD ^ 2) →
            (∀ r j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤
              etaD ^ 2) →
            ∀ (Jl : Bool × (Fin m → Bool) → Reg (Fin k) ℂ →L[ℂ] Reg (Fin k) ℂ)
              (Wp : Matrix (Cfg (Fin (m + 1))) (Cfg (Fin (m + 1))) ℂ)
              (G : ℝ → Reg (Fin k) ℂ →L[ℂ] Reg (Fin k) ℂ) (bf xs : ℝ → Reg (Fin k) ℂ)
              (bs : ℕ → Reg (Fin k) ℂ) (βG δG βb δb bmax ζs : ℝ),
            0 ≤ ζs →
            ApproxOn CleanX (nrun (primsTGW Wr x) loadC) (liftB (loadIdeal Jl)) ζs →
            ApproxOn CleanX (nrun (primsTGW Wr x) wpC) (liftB (matOp Wp)) ζs →
            ζs ≤ ImprovedODEQueryBudget.precision gbar ε →
            formal_uniformMeshG (odePubTG k s D.s_le_pow b c0 etaH etaD T gbar ε m) D x Jl Wp G
              bf xs bs βG δG βb δb bmax →
            HeraldedOutput (nprotocol ((odePubTG k s D.s_le_pow b c0 etaH etaD T gbar ε m).prepW N
                (fun _ => false) loadC wpC) (2 * gbar) (one_le_two_mul hg))
              (primsTGW Wr x) (ODEStateNormalization.unitDirection
                (cleanAlong (Fin.castSuccEmb : Fin k ↪ Fin (k + 1)) (xs T))) ε ∧
            ∀ j : ℕ, ((goodN)†) (nrun (primsTGW Wr x)
                (trialN ((odePubTG k s D.s_le_pow b c0 etaH etaD T gbar ε m).prepW N
                  (fun _ => false) loadC wpC) j) sN) ≠ 0 →
              ∃ ω : ℂ, ‖ω‖ = 1 ∧
                ‖ω • ODEStateNormalization.unitDirection (((goodN)†)
                    (nrun (primsTGW Wr x) (trialN ((odePubTG k s D.s_le_pow b c0 etaH etaD T gbar
                      ε m).prepW N (fun _ => false) loadC wpC) j) sN)) -
                  ODEStateNormalization.unitDirection
                    (cleanAlong (Fin.castSuccEmb : Fin k ↪ Fin (k + 1)) (xs T))‖ ≤ ε := by
  refine ⟨10 ^ 24, by norm_num, ?_⟩
  intro X N s k b bd c0 etaH etaD T gbar ε m D hm hk hF hbits hg Zs _ _ loadC wpC hloadV hwpV hH
    hD hT hε hε2
  obtain ⟨hbd, hc0b, hTb, hHb, hDb⟩ := hbits
  have hg1 : 1 ≤ gbar := hg
  have hε1 : ε ≤ 1 := by linarith
  have hg0 : 0 ≤ gbar := by linarith
  set q := odePubTG k s D.s_le_pow b c0 etaH etaD T gbar ε m with hqdef
  have hqp : q.pub = odePubT (k + 1) (sbP s) ((sbP_le D.s_le_pow).trans (Nat.le_succ k)) b c0
      etaH etaD T gbar ε m := rfl
  have hq : BTPublicOK0 q.pub := by
    rw [hqp]
    exact odePubT_ok _ hF.hb hF.hc0 hH hD hT hg hε hε2 hm
  have hγ := odePubT_gamma hqp hF.hb hbd
  obtain ⟨hζ, hζs⟩ := odePubT_zeta hqp hH hD hT hg hε hε2
  obtain ⟨hV, hWg0, hWq0, hWc0⟩ := GeneralSparseODE.general_time_budget_writer bd q hq hγ hζ hbd hc0b
    hTb hHb hDb N (fun _ => false) loadC hloadV wpC hwpV
  have hWg : ((nprotocol (q.prepW N (fun _ => false) loadC wpC) (2 * gbar)
      (one_le_two_mul hg)).worstCost wGateN : ℝ) ≤
      2 * 10 ^ 20 * gbar * (GateODEBudget.qOf ((sP s : ℕ) : ℝ) T etaH etaD (2 * gbar) (ε / 2) *
        (bitB bd (2 ^ (k + 1)) (2 ^ m) (2 ^ m)
          (GateODEBudget.qOf ((sP s : ℕ) : ℝ) T etaH etaD (2 * gbar) (ε / 2)) gbar ε + 1) ^ 3 +
        ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) + Fintype.card Zs) := hWg0
  have hWq : (Fintype.card (q.reg Zs) : ℝ) ≤ 3 * 10 ^ 11 * (bitB bd (2 ^ (k + 1)) (2 ^ m) (2 ^ m)
      (GateODEBudget.qOf ((sP s : ℕ) : ℝ) T etaH etaD (2 * gbar) (ε / 2)) gbar ε + 1) ^ 3 +
      2 * Fintype.card Zs := hWq0
  have hWc : ∀ c : Query → Bool, ((nprotocol (q.prepW N (fun _ => false) loadC wpC) (2 * gbar)
      (one_le_two_mul hg)).worstCost (wCallN c) : ℝ) ≤ (if T = 0 ∨ etaH + etaD = 0 then 0 else
        23592960 * gbar * GateODEBudget.qOf ((sP s : ℕ) : ℝ) T etaH etaD (2 * gbar) (ε / 2) *
          ((if c Query.rowLocation then 1 else 0) + (if c Query.columnLocation then 1 else 0) +
            (if c Query.value then 1 else 0))) +
        80 * gbar * ((nCallsN c loadC : ℝ) + 2 * nCallsN c wpC) := hWc0
  -- the query shapes and the word budgets
  have hsP : (((sP s : ℕ) : ℝ)) ≤ 2 * (s : ℝ) := by
    have h' : ((sP s : ℕ) : ℝ) ≤ ((2 * s : ℕ) : ℝ) := by exact_mod_cast (sP_lt D.slots_pos).le
    push_cast at h'
    exact h'
  have hQQ1 : GateODEBudget.qOf ((sP s : ℕ) : ℝ) T etaH etaD gbar ε ≤
      2 * GateODEBudget.qOf s T etaH etaD gbar ε :=
    qOf_le_of_le (Nat.cast_nonneg _) hsP hT hH hD hg hε hε1
  have hQQ2 : GateODEBudget.qOf ((sP s : ℕ) : ℝ) T etaH etaD (2 * gbar) (ε / 2) ≤
      3 * GateODEBudget.qOf ((sP s : ℕ) : ℝ) T etaH etaD gbar ε :=
    qOf_two_le0 (Nat.cast_nonneg _) hT hH hD hg hε hε1
  have hQQ : GateODEBudget.qOf ((sP s : ℕ) : ℝ) T etaH etaD (2 * gbar) (ε / 2) ≤
      6 * GateODEBudget.qOf s T etaH etaD gbar ε := by linarith
  have hQ1 : 1 ≤ GateODEBudget.qOf s T etaH etaD gbar ε :=
    GateRemarks.ODE.one_le_qOf hT hH hD hg hε hε1
  have hQ1' : 1 ≤ GateODEBudget.qOf ((sP s : ℕ) : ℝ) T etaH etaD (2 * gbar) (ε / 2) :=
    GateRemarks.ODE.one_le_qOf hT hH hD (by linarith) (by linarith) (by linarith)
  have hB0 : 0 ≤ bitB bd N (2 ^ m) (2 ^ m) (GateODEBudget.qOf s T etaH etaD gbar ε) gbar ε :=
    bitB_nonneg _ _ _ _ (mul_nonneg (by linarith) hg0) hε hε1
  have hB0' : 0 ≤ bitB bd (2 ^ (k + 1)) (2 ^ m) (2 ^ m)
      (GateODEBudget.qOf ((sP s : ℕ) : ℝ) T etaH etaD (2 * gbar) (ε / 2)) gbar ε :=
    bitB_nonneg _ _ _ _ (mul_nonneg (by linarith) hg0) hε hε1
  have hBB := bitB_padT_le (bd := bd) (M := 2 ^ m) hk (by linarith) hQQ (by linarith) hg0 hε hε1
  have hcube := cube_padT_le hB0 hB0' hBB
  have hY : 0 ≤ (bitB bd N (2 ^ m) (2 ^ m) (GateODEBudget.qOf s T etaH etaD gbar ε) gbar ε + 1) ^ 3 :=
    by positivity
  have hY' : 0 ≤ (bitB bd (2 ^ (k + 1)) (2 ^ m) (2 ^ m)
      (GateODEBudget.qOf ((sP s : ℕ) : ℝ) T etaH etaD (2 * gbar) (ε / 2)) gbar ε + 1) ^ 3 := by
    positivity
  have hZ0 : (0 : ℝ) ≤ Fintype.card Zs := Nat.cast_nonneg _
  rw [odeShape_eq]
  refine ⟨hV, ?_, ?_, ?_, ?_⟩
  · -- gates
    refine hWg.trans ?_
    generalize GateODEBudget.qOf ((sP s : ℕ) : ℝ) T etaH etaD (2 * gbar) (ε / 2) = Q'
      at hQQ hQ1' hcube hY' ⊢
    generalize GateODEBudget.qOf s T etaH etaD gbar ε = Q at hQQ hQ1 hcube hB0 hY ⊢
    generalize (bitB bd (2 ^ (k + 1)) (2 ^ m) (2 ^ m) Q' gbar ε + 1) ^ 3 = Y' at hcube hY' ⊢
    generalize (bitB bd N (2 ^ m) (2 ^ m) Q gbar ε + 1) ^ 3 = Y at hcube hY ⊢
    have hG0 : (0 : ℝ) ≤ (nGatesN loadC : ℝ) + 2 * nGatesN wpC := by positivity
    have h1 : Q' * Y' ≤ 1296 * (Q * Y) := by
      have h2 : Q' * Y' ≤ (6 * Q) * Y' := mul_le_mul_of_nonneg_right hQQ hY'
      have h3 : (6 * Q) * Y' ≤ (6 * Q) * (216 * Y) := mul_le_mul_of_nonneg_left hcube (by linarith)
      nlinarith
    have hQY : 0 ≤ Q * Y := mul_nonneg (by linarith) hY
    have h4 : (2 * 10 ^ 20 : ℝ) * gbar * (Q' * Y' + ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) +
        Fintype.card Zs) ≤ 2 * 10 ^ 20 * gbar * (1296 * (Q * Y) + ((nGatesN loadC : ℝ) +
          2 * nGatesN wpC) + Fintype.card Zs) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h5 : (2 * 10 ^ 20 : ℝ) * gbar * (1296 * (Q * Y) + ((nGatesN loadC : ℝ) +
          2 * nGatesN wpC) + Fintype.card Zs) ≤ 10 ^ 24 * gbar * (Q * Y +
          ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) + Fintype.card Zs) := by
      have h6 : (2 * 10 ^ 20 : ℝ) * (1296 * (Q * Y) + ((nGatesN loadC : ℝ) +
          2 * nGatesN wpC) + Fintype.card Zs) ≤ 10 ^ 24 * (Q * Y +
          ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) + Fintype.card Zs) := by
        nlinarith
      have := mul_le_mul_of_nonneg_left h6 hg0
      linarith
    exact h4.trans h5
  · -- qubits
    have h1 := mul_le_mul_of_nonneg_left hcube (by norm_num : (0 : ℝ) ≤ 3 * 10 ^ 11)
    have h2 : (2 : ℝ) * Fintype.card Zs ≤ 10 ^ 24 * Fintype.card Zs :=
      mul_le_mul_of_nonneg_right (by norm_num) hZ0
    have h3 : (3 * 10 ^ 11 : ℝ) * (216 * (bitB bd N (2 ^ m) (2 ^ m)
        (GateODEBudget.qOf s T etaH etaD gbar ε) gbar ε + 1) ^ 3) ≤ 10 ^ 24 * (bitB bd N (2 ^ m)
          (2 ^ m) (GateODEBudget.qOf s T etaH etaD gbar ε) gbar ε + 1) ^ 3 := by nlinarith
    have hq' : (odeQubitsTG q Zs : ℝ) = (Fintype.card (q.reg Zs) : ℝ) := rfl
    rw [hq']
    exact hWq.trans (add_le_add (h1.trans h3) h2)
  · -- calls
    intro c
    have hW := hWc c
    have hI0 : (0 : ℝ) ≤ (if c Query.rowLocation then 1 else 0) +
        (if c Query.columnLocation then 1 else 0) + (if c Query.value then 1 else 0) := by
      split_ifs <;> norm_num
    have hS0 : (0 : ℝ) ≤ (nCallsN c loadC : ℝ) + 2 * nCallsN c wpC := by positivity
    have hS : 80 * gbar * ((nCallsN c loadC : ℝ) + 2 * nCallsN c wpC) ≤
        10 ^ 24 * gbar * ((nCallsN c loadC : ℝ) + 2 * nCallsN c wpC) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by norm_num) hg0) hS0
    by_cases hz : T = 0 ∨ etaH + etaD = 0
    · rw [if_pos hz] at hW
      rw [if_pos hz]
      exact hW.trans (add_le_add le_rfl hS)
    · rw [if_neg hz] at hW
      rw [if_neg hz]
      generalize hId : ((if c Query.rowLocation then 1 else 0) +
          (if c Query.columnLocation then 1 else 0) + (if c Query.value then 1 else 0) : ℝ) = I
        at hI0 hW ⊢
      generalize GateODEBudget.qOf ((sP s : ℕ) : ℝ) T etaH etaD (2 * gbar) (ε / 2) = Q' at hQQ hW
      have h1 : 23592960 * gbar * Q' * I ≤ 10 ^ 24 * gbar * GateODEBudget.qOf s T etaH etaD gbar ε *
          I := by
        have h2 : Q' * I ≤ (6 * GateODEBudget.qOf s T etaH etaD gbar ε) * I :=
          mul_le_mul_of_nonneg_right hQQ hI0
        have h3 : 0 ≤ GateODEBudget.qOf s T etaH etaD gbar ε * I :=
          mul_nonneg (by linarith) hI0
        have h4 : 23592960 * (Q' * I) ≤ 10 ^ 24 * (GateODEBudget.qOf s T etaH etaD gbar ε * I) := by
          nlinarith
        have h5 := mul_le_mul_of_nonneg_left h4 hg0
        nlinarith
      exact hW.trans (add_le_add h1 hS)
  · -- the guarantees
    intro Wr x hrH hcH hrD hcD Jl Wp G bf xs bs βG δG βb δb bmax ζs hζs0 hload hwp hacc hR
    have hγ' : ¬ BTZeroCase q.pub →
        q.γ = GateODEBudget.gammaOf q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) := by
      intro hz
      have h := hγ
      rw [if_neg hz] at h
      exact h
    -- the public data is passed literally (not as the local definition `q`), so that the
    -- outcome has the types of the statement and the final unification is syntactic
    have o := (GeneralSparseODE.general_time_outcome_writer
      (odePubTG k s D.s_le_pow b c0 etaH etaD T gbar ε m) hq hγ' D (fun _ => false) hF.zero
      hF.dec Wr loadC hloadV wpC hwpV x hrH hcH hrD hcD Jl Wp G bf xs bs βG δG βb δb bmax ζs hζs0
      hload hwp (hζs ζs hacc) hR).mono (β' := ε) (by
        show ε / 100 ≤ ε
        linarith)
    rw [markEmb_eq_cleanAlong] at o
    exact ⟨⟨o.success_two_thirds, o.output_density, o.conditional_error⟩, o.trial_direction⟩

end

end ManuscriptConformance
