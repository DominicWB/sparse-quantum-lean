import ManuscriptConformance.WriterGateAccess
import ManuscriptConformance.GateODEGeneral

/-!
# Conformance: Theorem `ode:thm:gates` of general size with a writer, constant coefficients

Theorem `ode:thm:gates` for sparse access of general size, constant coefficients
(`ode_thm_gates_general`), with the value oracle given by a reversible writer of the stored words
specified on the clean inputs of the valid index pairs only (`GeneralSparseAccess.QData.Writer`,
handover item B4).

The released solver of general size runs the released constant-coefficient solver on the padded
data, its private operation calling the supplied oracles through the implementation
`GeneralSparseAccess.implP` of the padded primitives (`GeneralSparseODE.GPub.nd`, `GPub.prep`). The
writer versions use `GeneralSparseAccess.implPW` instead (the same gates; the writer and its
inverse in the places of the two XOR calls of the padded value oracle, the copy masked by the
validity flag), which acts on clean ancillas as the padded primitives for every writer
(`GeneralSparseAccess.implOKW`):

* `GPub.ndW`, `GPub.prepW`, `ndW_public`, `arW_ok`, `ndW_nGates`, `ndW_nCalls`, `privGatesW_le`:
  the private operation and the preparation in the writer model, with the bounds of `nd`;
* `general_ode_outcome_writer`, `general_ode_budget_writer`: the outcome and the budget of
  `general_ode_outcome`, `general_ode_budget` (the released proofs, with `implOKW` in place of
  `implOK`);
* `ode_thm_gates_general_writer`: the endpoint, with the constants of `ode_thm_gates_general`; the
  source circuits call the primitives of the writer model.
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
open GateBinaryODE (Pub SZ4 card_SZ4 mLift privFam hLift lLift target_lift hadUJ4_ok)
open ZeroTimeGateODE (BPublicOK0 BZeroCase zprepC srcRot binary_target_zero bpublicOK_of)
open SourceAccuracyODE (WOutcome)
open SparseHamiltonian.GateBitBudget (bitB bitB_nonneg HasBits)
open GateODEBudget (qOf words gammaOf)
open ImprovedODEQueryBudget (logBudget)
open NativeSparseBlockEncoding (Query)
open ODEStateNormalization (unitDirection)
open scoped InnerProduct

/-! ### The private operation and the preparation in the writer model -/

namespace GPub

variable (q : GPub)

/-- **The private Cayley operation in the writer model**: the released operation of the padded
problem with every padded call replaced by its implementation from the supplied locators and a
value writer (`GeneralSparseAccess.implPW`). -/
def ndW (N : ℕ) (z₀ : Cfg (VW q.b)) :
    NativeOp (LabW q.pub.params.k q.pub.params.l) (Fin q.pub.params.a ⊕ Fin (q.k + 1))
      (SZ4 (q.k + 1) q.b ⊕ GeneralSparseAccess.AW q.k q.b) (PY q.k q.b) Query :=
  substOp q.pub.nd (implPW N q.s z₀)

/-- **The preparation of the general problem in the writer model**: `GPub.prep` with the private
operation `ndW`. -/
def prepW {Zs : Type*} [Fintype Zs] [DecidableEq Zs] (N : ℕ) (z₀ : Cfg (VW q.b))
    (srcC : Bool → List (NInstr ((Unit ⊕ Fin q.k) ⊕ Zs) (PY q.k q.b) Query)) :
    List (NInstr (NW q.pub.params (Fin (q.k + 1)) Zs
      (SZ4 (q.k + 1) q.b ⊕ GeneralSparseAccess.AW q.k q.b) q.ar.bT q.ar.bP q.ar.A)
      (PY q.k q.b) Query) :=
  if BZeroCase q.pub then zprepC (srcRot q.T q.r₀ q.rb) (fun c => liftC (srcC c))
  else nprepC q.pub.params q.pub.UJg (q.ndW N z₀) q.ar (fun c => liftC (srcC c))

theorem ndW_public (N : ℕ) (z₀ : Cfg (VW q.b)) : (q.ndW N z₀).Public :=
  substOp_public q.pub.nd_public (valid_implPW N q.s z₀)

theorem arW_ok (hq : q.pub.OK) (N : ℕ) (z₀ : Cfg (VW q.b)) :
    ArithOK q.ar (Sum.inl (Sum.inr (q.ndW N z₀).o)) (q.ndW N z₀).dec q.ζ :=
  arithOK_liftA q.pub.ar _ _ _ (q.pub.ar_ok hq)

/-- The compute circuit has at most `28 (k + 1) + 2 + 6 implG k b` gates. -/
theorem ndW_nGates (N : ℕ) (z₀ : Cfg (VW q.b)) :
    nGatesN (q.ndW N z₀).V ≤ 28 * (q.k + 1) + 2 + implG q.k q.b * 6 := by
  have h := nGatesN_substOp_le q.pub.nd (implPW N q.s z₀) (implG q.k q.b)
    (nGatesN_implPW_le N q.s z₀)
  have hg : nGatesN q.pub.nd.V = 28 * (q.k + 1) + 2 :=
    GateBinaryODE.computeV4_nGates (q.k + 1) q.b q.pub.params.k q.pub.params.l
  have hc : nCallsN (fun _ => true) q.pub.nd.V = 6 := by
    have := GateBinaryODE.computeV4_nCalls (k := q.k + 1) (b := q.b) (kq := q.pub.params.k)
      (lq := q.pub.params.l) (fun _ => true)
    simp only [if_true] at this
    exact this
  unfold ndW
  rw [hg, hc] at h
  exact h

/-- The compute circuit makes at most `6` supplied calls of each kind it calls. -/
theorem ndW_nCalls (N : ℕ) (z₀ : Cfg (VW q.b)) (c : Query → Bool) :
    nCallsN c (q.ndW N z₀).V ≤ 6 * ((if c Query.rowLocation then 1 else 0) +
      (if c Query.columnLocation then 1 else 0) + (if c Query.value then 1 else 0)) := by
  have h := nCallsN_substOp_le q.pub.nd (kindOK_implPW (k := q.k) (b := q.b) N q.s z₀) c
  have hc := GateBinaryODE.computeV4_nCalls (k := q.k + 1) (b := q.b) (kq := q.pub.params.k)
    (lq := q.pub.params.l) c
  have hc' : nCallsN c q.pub.nd.V = 2 * (if c Query.rowLocation then 1 else 0) +
      2 * (if c Query.columnLocation then 1 else 0) + 2 * (if c Query.value then 1 else 0) := hc
  have h' : nCallsN c (q.ndW N z₀).V ≤ 3 * nCallsN c q.pub.nd.V := h
  rw [hc'] at h'
  omega

/-- **The per-call cost of the writer-model operation in the words**: at most `65944 (𝔴+1)³`. -/
theorem privGatesW_le (N : ℕ) (z₀ : Cfg (VW q.b)) :
    privGates (q.ndW N z₀) q.ar ≤ 65944 * (words q.pub + 1) ^ 3 := by
  have hV := q.ndW_nGates N z₀
  obtain ⟨hGC, -, -, -⟩ := GateODEBudget.binary_arith_words q.pub
  have hk : q.k + 1 ≤ words q.pub := by
    show q.pub.kx ≤ words q.pub
    unfold words
    omega
  have hb : q.b ≤ words q.pub := by
    show q.pub.b ≤ words q.pub
    unfold words
    omega
  have hp1 : words q.pub + 1 ≤ (words q.pub + 1) ^ 3 := le_self_pow₀ (by omega) (by norm_num)
  have hl : q.ar.circ.length = q.pub.ar.circ.length := liftA_circ_length _
  have hb2 : q.ar.bP = q.pub.ar.bP := rfl
  have hb3 : q.ar.bT = q.pub.ar.bT := rfl
  have hkx : q.pub.kx = q.k + 1 := rfl
  unfold privGates
  rw [hl, hb2, hb3]
  unfold implG at hV
  omega

end GPub

/-! ### The outcome in the writer model -/

section OutcomeW

variable {X : Type*} {N : ℕ} {Zs : Type*} [Fintype Zs] [DecidableEq Zs]

set_option maxHeartbeats 1600000 in
/-- **The outcome of the general solver in the writer model** (constant coefficients, every
`T ≥ 0`): the hypotheses of `general_ode_outcome`, with a writer `Wr` of the stored words on valid
clean inputs and the source circuits within `ζ_s` for the primitives of the writer model
`Wr.prims x`; the protocol `nprotocol (q.prepW N z₀ srcC) g` has the guarantees
`WOutcome … (ε / 250)` for `Wr.prims x`, against the marker embedding of the solution of
`x' = -A x + b`, `A = padLift D x`. -/
theorem general_ode_outcome_writer (q : GPub) (hq : BPublicOK0 q.pub)
    (hγ : ¬ BZeroCase q.pub →
      q.γ = GateODEBudget.gammaOf q.T q.etaH q.etaD q.g q.ε)
    (D : QData X N q.s q.k q.b) (z₀ : Cfg (VW q.b)) (hz₀ : D.val z₀ = 0)
    (hdec : ∀ z, D.val z = (q.c0 : ℂ) * gauss z) (Wr : D.Writer)
    (srcC : Bool → List (NInstr ((Unit ⊕ Fin q.k) ⊕ Zs) (PY q.k q.b) Query))
    (hsrcV : ∀ c, ∀ i ∈ srcC c, i.Valid) (x : X)
    (hrH : ∀ i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ q.etaH ^ 2)
    (hcH : ∀ j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ q.etaH ^ 2)
    (hrD : ∀ i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ q.etaD ^ 2)
    (hcD : ∀ j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ q.etaD ^ 2)
    (hPSD : ∀ w : EuclideanSpace ℂ (Fin N), 0 ≤ (inner ℂ w (SparseStateOverlap.matrixOperator
      (ODEMatrixEnergy.dissipativePart (D.matrix x)) w)).re)
    (Jsrc : Bool → Reg (Fin q.k) ℂ →L[ℂ] Reg (Fin q.k) ℂ) (x0 v : Reg (Fin q.k) ℂ) (ζs : ℝ)
    (hJ : ∀ c, IsUnitary (Jsrc c)) (hζs : 0 ≤ ζs)
    (hsrc : ∀ c, ApproxOn CleanX (nrun (Wr.prims (R := ℂ) x) (srcC c))
      (liftB (srcIdeal c (Jsrc c))) ζs)
    (hbud : 98304 * GateODEBudget.qOf q.pub.s q.T q.etaH q.etaD q.g q.ε * q.ζ + 2 * ζs ≤
      4 * q.pub.params.nu)
    (hx0 : ‖x0‖ = q.r₀) (hv : ‖v‖ = q.rb)
    (hpx : x0 ≠ 0 → Jsrc false (seedV (S := Fin q.k)) = unitDirection x0)
    (hpv : v ≠ 0 → Jsrc true (seedV (S := Fin q.k)) = unitDirection v)
    (hne : ODEConstantForcing.solution (-padLift D x) x0 v q.T ≠ 0)
    (hB : q.r₀ + q.T * q.rb ≤ q.g * ‖ODEConstantForcing.solution (-padLift D x) x0 v q.T‖) :
    WOutcome (q.prepW N z₀ srcC) q.g (q.ε / 250) hq.g_ge (Wr.prims (R := ℂ) x)
      (markEmb q.k (ODEConstantForcing.solution (-padLift D x) x0 v q.T)) := by
  -- the padded data and the padded instance
  set Dp := D.padData z₀ hz₀ with hDp
  have hrange : ∀ j : Cfg (Fin (q.k + 1)), (∃ m, Dp.slot m = j) ↔
      ∃ u : Fin q.pub.σ → Bool, j = (Equiv.refl (Cfg (Fin (q.k + 1)))) (lowWord q.pub.σ u) :=
    padData_range D z₀ hz₀
  have hdecP : ∀ e z, Dp.decode e z = (q.pub.c0 : ℂ) * gauss z := fun e z =>
    (padData_decode D z₀ hz₀ e z).trans (hdec z)
  have hrH' : ∀ i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (Dp.matrix x) i j‖ ^ 2 ≤ q.pub.etaH ^ 2 := by
    intro i
    rw [hDp, padData_zpad, hamiltonianPart_zpad]
    exact zpad_row_le D.hN _ hrH i
  have hcH' : ∀ j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (Dp.matrix x) i j‖ ^ 2 ≤ q.pub.etaH ^ 2 := by
    intro j
    rw [hDp, padData_zpad, hamiltonianPart_zpad]
    exact zpad_col_le D.hN _ hcH j
  have hrD' : ∀ i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (Dp.matrix x) i j‖ ^ 2 ≤
      q.pub.etaD ^ 2 := by
    intro i
    rw [hDp, padData_zpad, dissipativePart_zpad]
    exact zpad_row_le D.hN _ hrD i
  have hcD' : ∀ j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (Dp.matrix x) i j‖ ^ 2 ≤
      q.pub.etaD ^ 2 := by
    intro j
    rw [hDp, padData_zpad, dissipativePart_zpad]
    exact zpad_col_le D.hN _ hcD j
  have hPSD' : ∀ w : EuclideanSpace ℂ (Cfg (Fin (q.k + 1))), 0 ≤ (inner ℂ w
      (SparseStateOverlap.matrixOperator (ODEMatrixEnergy.dissipativePart (Dp.matrix x)) w)).re := by
    intro w
    rw [hDp, padData_zpad, dissipativePart_zpad]
    exact zpad_accretive D.hN _ hPSD w
  -- the sources on the padded system register
  have hJ' : ∀ c, IsUnitary (lowOp (Jsrc c)) := fun c => lowOp_isUnitary (hJ c)
  have hx0' : ‖markEmb q.k x0‖ = q.pub.r₀ := by rw [norm_markEmb]; exact hx0
  have hv' : ‖markEmb q.k v‖ = q.pub.rb := by rw [norm_markEmb]; exact hv
  have hseed : ∀ c, lowOp (Jsrc c) (seedV (S := Fin (q.k + 1))) =
      markEmb q.k (Jsrc c (seedV (S := Fin q.k))) := by
    intro c
    rw [seedV_markEmb, ← comp_apply, lowOp_markEmb, comp_apply]
  have hne0 : ∀ y : Reg (Fin q.k) ℂ, markEmb q.k y ≠ 0 → y ≠ 0 := by
    intro y hy h0
    apply hy
    rw [h0, map_zero]
  have hpx' : markEmb q.k x0 ≠ 0 →
      lowOp (Jsrc false) (seedV (S := Fin q.pub.kx)) = unitDirection (markEmb q.k x0) := by
    intro h
    rw [unitDirection_markEmb, ← hpx (hne0 x0 h)]
    exact hseed false
  have hpv' : markEmb q.k v ≠ 0 →
      lowOp (Jsrc true) (seedV (S := Fin q.pub.kx)) = unitDirection (markEmb q.k v) := by
    intro h
    rw [unitDirection_markEmb, ← hpv (hne0 v h)]
    exact hseed true
  have hsrcV' : ∀ c, ∀ i ∈ liftC (srcC c), i.Valid := fun c => valid_liftC _ (hsrcV c)
  have hsrc' : ∀ c, ApproxOn CleanX (nrun (Wr.prims (R := ℂ) x) (liftC (srcC c)))
      (liftB (srcIdeal c (lowOp (Jsrc c)))) ζs := fun c =>
    approxOn_liftSrc (Wr.prims x) (srcC c) c (Jsrc c) hζs (hsrc c)
  -- the solution along the marker embedding
  have hsol : ODEConstantForcing.solution (-mLift Dp (Equiv.refl _) x) (markEmb q.k x0)
      (markEmb q.k v) q.T = markEmb q.k (ODEConstantForcing.solution (-padLift D x) x0 v q.T) := by
    apply solution_comp
    rw [neg_comp, comp_neg, hDp, mLift_padData_comp]
  have hne' : ODEConstantForcing.solution (-mLift Dp (Equiv.refl _) x) (markEmb q.k x0)
      (markEmb q.k v) q.T ≠ 0 := by
    rw [hsol]
    intro h
    apply hne
    have := congrArg (lowPart q.k) h
    rwa [← comp_apply (lowPart q.k) (markEmb q.k), lowPart_markEmb, map_zero] at this
  have hB' : q.r₀ + q.T * q.rb ≤ q.g * ‖ODEConstantForcing.solution
      (-mLift Dp (Equiv.refl _) x) (markEmb q.k x0) (markEmb q.k v) q.T‖ := by
    rw [hsol, norm_markEmb]
    exact hB
  by_cases hz : BZeroCase q.pub
  · -- the direct source assembly
    have ht : ODEConstantForcing.solution (-mLift Dp (Equiv.refl _) x) (markEmb q.k x0)
        (markEmb q.k v) q.T = markEmb q.k x0 + q.T • markEmb q.k v :=
      binary_target_zero q.pub hq hz Dp (Equiv.refl _) x hrH' hrD' (markEmb q.k x0)
        (markEmb q.k v)
    have hε1 : q.pub.ε ≤ 1 := hq.ε_half.trans (by norm_num)
    have hQ1 : 1 ≤ GateODEBudget.qOf q.pub.s q.T q.etaH q.etaD q.g q.ε :=
      GateRemarks.ODE.one_le_qOf hq.T_nonneg hq.etaH_nonneg hq.etaD_nonneg hq.g_ge hq.ε_pos hε1
    have h0 : 0 ≤ 98304 * GateODEBudget.qOf q.pub.s q.T q.etaH q.etaD q.g q.ε * q.ζ :=
      mul_nonneg (mul_nonneg (by norm_num) (by linarith)) hq.ζ_pos.le
    have hnu : q.pub.params.nu = ImprovedODEQueryBudget.precision q.pub.g q.pub.ε := rfl
    rw [hnu] at hbud
    rw [ht] at hne' hB'
    have hp : q.prepW N z₀ srcC = zprepC (srcRot q.T q.r₀ q.rb) (fun c => liftC (srcC c)) := by
      rw [GPub.prepW, if_pos hz]
    rw [hp, ← hsol, ht]
    exact SourceAccuracyODE.native_zero_outcome (Z := SZ4 (q.k + 1) q.b ⊕ GeneralSparseAccess.AW q.k q.b)
      (Y := PY q.k q.b) (J := Query) q.pub.params.a q.pub.params.m q.pub.params.r q.pub.params.K
      q.pub.params.k q.pub.params.l q.pub.params.f q.ar.bT q.ar.bP q.ar.A q.pub.T q.pub.g q.pub.ε
      q.pub.r₀ q.pub.rb hq.T_nonneg hq.g_ge hq.ε_pos hq.ε_half hq.r₀_nonneg hq.rb_nonneg hq.B_pos
      (fun c => liftC (srcC c)) hsrcV' (Wr.prims (R := ℂ) x) (fun c => lowOp (Jsrc c))
      (markEmb q.k x0) (markEmb q.k v) ζs (Wr.prims_isUnitary x) hJ' hζs hsrc' (by linarith) hx0'
      hv' hpx' hpv' hne' hB'
  · -- the native preparation
    have hP := bpublicOK_of hq hz
    obtain ⟨-, hd, -, -, -, -, -⟩ := GateODEBudget.binary_ode_sizes q.pub hP (hγ hz)
    have hd' : (q.pub.params.d : ℝ) ≤ 4096 * GateODEBudget.qOf q.pub.s q.T q.etaH q.etaD q.g q.ε :=
      hd
    have hζ0 : (0 : ℝ) ≤ q.ζ := hP.ζ_pos.le
    have hbud' : 24 * (q.pub.params.d : ℝ) * q.ζ + 2 * ζs ≤ 4 * q.pub.params.nu := by
      have := mul_le_mul_of_nonneg_right hd' hζ0
      linarith
    have hN : NativeOK (Wr.prims (R := ℂ) x) (q.ndW N z₀)
        (selOp (labFam (privFam q.pub.params Dp (Equiv.refl _) x q.pub.rho q.pub.γ) false)) :=
      nativeOK_substOp (Wr.prims x) (prims (R := ℂ) Dp (Equiv.refl _) x) (Wr.prims_isUnitary x)
        (prims_isUnitary Dp (Equiv.refl _) x) (implOKW Wr z₀ hz₀ x) q.pub.nd q.pub.nd_public _
        (q.pub.nativeOK hP Dp (Equiv.refl _) hrange hdecP x)
    have hp : q.prepW N z₀ srcC =
        nprepC q.pub.params q.pub.UJg (q.ndW N z₀) q.ar (fun c => liftC (srcC c)) := by
      rw [GPub.prepW, if_neg hz]
    have h := SourceAccuracyODE.native_ode_outcome q.pub.params (q.pub.params_ok hP) q.pub.UJg
      (hadUJ4_ok q.pub.σ q.pub.hσ) (q.ndW N z₀) (q.ndW_public N z₀) q.ar q.pub.ζ hP.ζ_pos.le
      (q.arW_ok hP N z₀) (fun c => liftC (srcC c)) hsrcV' (Wr.prims (R := ℂ) x)
      (privFam q.pub.params Dp (Equiv.refl _) x q.pub.rho q.pub.γ) (fun c => lowOp (Jsrc c))
      (hLift Dp (Equiv.refl _) x) (lLift Dp (Equiv.refl _) x) (markEmb q.k x0) (markEmb q.k v) ζs
      (Wr.prims_isUnitary x) hN hζs hsrc' hbud'
      (q.pub.instanceOK hP Dp (Equiv.refl _) hrange x hrH' hcH' hrD' hcD' hPSD'
        (fun c => lowOp (Jsrc c)) (markEmb q.k x0) (markEmb q.k v) hJ' hx0' hv' hpx' hpv' hne' hB')
    rw [hp]
    exact wOutcome_target h ((target_lift q.pub.params Dp (Equiv.refl _) x (markEmb q.k x0)
      (markEmb q.k v)).trans hsol)

end OutcomeW

/-! ### The budget in the writer model -/

section BudgetW

variable {Zs : Type*} [Fintype Zs] [DecidableEq Zs]

set_option maxHeartbeats 8000000 in
/-- **The budget of the general solver in the writer model**: the bounds of `general_ode_budget`
for the protocol `nprotocol (q.prepW N z₀ srcC) g` (valid trials, gates in every history, qubits
and calls of every kind of the primitives of the writer model; each writer call or inverse writer
call counted as a call of the value kind). -/
theorem general_ode_budget_writer (bd : ℕ) (q : GPub) (hq : BPublicOK0 q.pub)
    (hγ : if BZeroCase q.pub then HasBits bd q.γ else q.γ = gammaOf q.T q.etaH q.etaD q.g q.ε)
    (hζ : q.pub.params.nu ≤ 196608 * qOf q.pub.s q.T q.etaH q.etaD q.g q.ε * q.ζ)
    (hb : q.b ≤ bd) (hc0 : HasBits bd q.c0) (hT : HasBits bd q.T) (hH : HasBits bd q.etaH)
    (hD : HasBits bd q.etaD) (N : ℕ) (z₀ : Cfg (VW q.b))
    (srcC : Bool → List (NInstr ((Unit ⊕ Fin q.k) ⊕ Zs) (PY q.k q.b) Query))
    (hsrcV : ∀ c, ∀ i ∈ srcC c, i.Valid) :
    (∀ j, ∀ i ∈ trialN (q.prepW N z₀ srcC) j, i.Valid) ∧
    ((nprotocol (q.prepW N z₀ srcC) q.g hq.g_ge).worstCost wGateN : ℝ) ≤
      10 ^ 20 * q.g * (qOf q.pub.s q.T q.etaH q.etaD q.g q.ε *
          (bitB bd (2 ^ (q.k + 1)) 0 0 (qOf q.pub.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε + 1) ^ 3 +
        ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true)) + Fintype.card Zs) ∧
    (Fintype.card (q.reg Zs) : ℝ) ≤
      3 * 10 ^ 11 * (bitB bd (2 ^ (q.k + 1)) 0 0 (qOf q.pub.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε +
        1) ^ 3 + 2 * Fintype.card Zs ∧
    (∀ c : Query → Bool, ((nprotocol (q.prepW N z₀ srcC) q.g hq.g_ge).worstCost (wCallN c) : ℝ) ≤
      (if BZeroCase q.pub then 0 else 11796480 * q.g * qOf q.pub.s q.T q.etaH q.etaD q.g q.ε *
          ((if c Query.rowLocation then 1 else 0) + (if c Query.columnLocation then 1 else 0) +
            (if c Query.value then 1 else 0))) +
        40 * q.g * ((nCallsN c (srcC false) : ℝ) + nCallsN c (srcC true))) := by
  have hε1 : q.ε ≤ 1 := hq.ε_half.trans (by norm_num)
  have hg0 : 0 ≤ q.g := le_trans zero_le_one hq.g_ge
  have hQ1 : 1 ≤ qOf q.pub.s q.T q.etaH q.etaD q.g q.ε :=
    GateRemarks.ODE.one_le_qOf hq.T_nonneg hq.etaH_nonneg hq.etaD_nonneg hq.g_ge hq.ε_pos hε1
  have hℓ1 : 1 ≤ logBudget q.g q.ε := ImprovedODEQueryBudget.logBudget_ge_one q.g q.ε hq.g_ge
    hq.ε_pos hε1
  have hQg : 0 ≤ qOf q.pub.s q.T q.etaH q.etaD q.g q.ε * q.g := by positivity
  have hB0 : 0 ≤ bitB bd (2 ^ (q.k + 1)) 0 0 (qOf q.pub.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε :=
    bitB_nonneg bd _ 0 0 hQg hq.ε_pos hε1
  -- the words in `𝔟₀`
  have hw : (words q.pub : ℝ) + logBudget q.g q.ε ≤
      300 * (bitB bd (2 ^ (q.k + 1)) 0 0 (qOf q.pub.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε + 1) := by
    by_cases hz : BZeroCase q.pub
    · rw [if_pos hz] at hγ
      exact GateRemarks.ODE.zero_words_le bd q.pub hq hz hγ hζ hb hc0 hH hD
    · rw [if_neg hz] at hγ
      exact GateBitBudget.words_le bd q.pub (bpublicOK_of hq hz) hγ hζ hb hc0 hT hH hD
  generalize hBdef : bitB bd (2 ^ (q.k + 1)) 0 0 (qOf q.pub.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε =
    B at hB0 hw ⊢
  have hwr0 : (0 : ℝ) ≤ words q.pub := Nat.cast_nonneg _
  have hY1 : 1 ≤ (B + 1) ^ 3 := one_le_pow₀ (by linarith)
  have hZ0 : (0 : ℝ) ≤ Fintype.card Zs := Nat.cast_nonneg _
  have hG0 : (0 : ℝ) ≤ (nGatesN (srcC false) : ℝ) + nGatesN (srcC true) := by positivity
  -- the register
  have hspace : (Fintype.card (q.reg Zs) : ℝ) ≤ 3 * 10 ^ 11 * (B + 1) ^ 3 + 2 * Fintype.card Zs := by
    have h1 : (Fintype.card (q.reg Zs) : ℝ) ≤ 10016 * ((words q.pub : ℝ) + 1) ^ 3 +
        2 * Fintype.card Zs := by exact_mod_cast q.card_reg_le Zs
    have hcube := GateBitBudget.cube_le hwr0 hB0 (c := 300) (by linarith)
    have : (10016 : ℝ) * ((words q.pub : ℝ) + 1) ^ 3 ≤ 10016 * ((300 + 1) ^ 3 * (B + 1) ^ 3) :=
      mul_le_mul_of_nonneg_left hcube (by norm_num)
    linarith
  have hsrcV' : ∀ c, ∀ i ∈ liftC (srcC c), i.Valid := fun c => valid_liftC _ (hsrcV c)
  have hGs : ∀ c, nGatesN (liftC (srcC c)) = nGatesN (srcC c) := fun c => nGatesN_liftC _
  have hCs : ∀ (p : Query → Bool) c, nCallsN p (liftC (srcC c)) = nCallsN p (srcC c) :=
    fun p c => nCallsN_liftC p _
  by_cases hz : BZeroCase q.pub
  · -- the direct source assembly
    obtain ⟨hV, -, -, hWG, hWC, -, hcardZ, -⟩ := ZeroTimeGateODE.native_ode_solver_zero
      (S := Fin (q.k + 1)) (Zs := Zs) (Z := SZ4 (q.k + 1) q.b ⊕ GeneralSparseAccess.AW q.k q.b)
      (Y := PY q.k q.b) (J := Query) q.pub.params.a q.pub.params.m q.pub.params.r q.pub.params.K
      q.pub.params.k q.pub.params.l q.pub.params.f q.ar.bT q.ar.bP q.ar.A q.T q.g q.ε q.r₀ q.rb
      hq.T_nonneg hq.g_ge hq.ε_pos hq.ε_half hq.r₀_nonneg hq.rb_nonneg hq.B_pos
      (fun c => liftC (srcC c)) hsrcV'
    have hp : q.prepW N z₀ srcC = zprepC (srcRot q.T q.r₀ q.rb) (fun c => liftC (srcC c)) := by
      rw [GPub.prepW, if_pos hz]
    have htest : Fintype.card (GateODE.AW q.pub.params.a q.pub.params.m q.pub.params.r
        q.pub.params.K q.pub.params.k q.pub.params.l q.pub.params.f) +
        Fintype.card (XW (SZ4 (q.k + 1) q.b ⊕ GeneralSparseAccess.AW q.k q.b) q.ar.bT q.ar.bP
          q.ar.A) + Fintype.card Zs + Fintype.card (Fin (q.k + 1)) ≤ Fintype.card (q.reg Zs) := by
      have h1 := (hcardZ : Fintype.card (q.reg Zs) = _)
      have h2 : Fintype.card (XW (SZ4 (q.k + 1) q.b ⊕ GeneralSparseAccess.AW q.k q.b) q.ar.bT
          q.ar.bP q.ar.A) = Fintype.card (SZ4 (q.k + 1) q.b ⊕ GeneralSparseAccess.AW q.k q.b) +
            q.ar.bT + q.ar.bP + q.ar.A + 3 := by
        simp only [XW, AWr, Fintype.card_sum, Fintype.card_fin]
        ring
      rw [h1, h2]
      omega
    have htest' : (Fintype.card (GateODE.AW q.pub.params.a q.pub.params.m q.pub.params.r
        q.pub.params.K q.pub.params.k q.pub.params.l q.pub.params.f) : ℝ) +
        Fintype.card (XW (SZ4 (q.k + 1) q.b ⊕ GeneralSparseAccess.AW q.k q.b) q.ar.bT q.ar.bP
          q.ar.A) + Fintype.card Zs + Fintype.card (Fin (q.k + 1)) ≤ Fintype.card (q.reg Zs) := by
      exact_mod_cast htest
    refine ⟨?_, ?_, hspace, ?_⟩
    · rw [hp]
      exact hV
    · -- gates
      rw [hp]
      have hWG' : ((nprotocol (zprepC (srcRot q.T q.r₀ q.rb) (fun c => liftC (srcC c)) :
          List (NInstr (q.reg Zs) (PY q.k q.b) Query)) q.g hq.g_ge).worstCost wGateN : ℝ) ≤
          40 * q.g * ((nGatesN (liftC (srcC false)) + nGatesN (liftC (srcC true)) + 2 : ℕ) : ℝ) +
            20 * q.g * (4 * ((Fintype.card (GateODE.AW q.pub.params.a q.pub.params.m q.pub.params.r
              q.pub.params.K q.pub.params.k q.pub.params.l q.pub.params.f) : ℝ) +
              Fintype.card (XW (SZ4 (q.k + 1) q.b ⊕ GeneralSparseAccess.AW q.k q.b) q.ar.bT q.ar.bP
                q.ar.A) + Fintype.card Zs + Fintype.card (Fin (q.k + 1))) + 3) := hWG
      rw [hGs, hGs] at hWG'
      push_cast at hWG'
      refine hWG'.trans ?_
      have h1 := mul_le_mul_of_nonneg_left htest' hg0
      have h2 : q.g * (Fintype.card (q.reg Zs) : ℝ) ≤
          q.g * (3 * 10 ^ 11 * (B + 1) ^ 3 + 2 * Fintype.card Zs) :=
        mul_le_mul_of_nonneg_left hspace hg0
      have h3 : q.g * (B + 1) ^ 3 ≤ q.g * (qOf q.pub.s q.T q.etaH q.etaD q.g q.ε * (B + 1) ^ 3) :=
        mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (by linarith) hQ1) hg0
      have h4 : q.g * 1 ≤ q.g * (qOf q.pub.s q.T q.etaH q.etaD q.g q.ε * (B + 1) ^ 3) :=
        mul_le_mul_of_nonneg_left (one_le_mul_of_one_le_of_one_le hQ1 hY1) hg0
      have h5 : 0 ≤ q.g * ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true)) := mul_nonneg hg0 hG0
      have h6 : 0 ≤ q.g * (Fintype.card Zs : ℝ) := mul_nonneg hg0 hZ0
      nlinarith
    · -- calls
      intro c
      rw [hp, if_pos hz, zero_add]
      have hW : ((nprotocol (zprepC (srcRot q.T q.r₀ q.rb) (fun c => liftC (srcC c)) :
          List (NInstr (q.reg Zs) (PY q.k q.b) Query)) q.g hq.g_ge).worstCost (wCallN c) : ℝ) ≤
          40 * q.g * ((nCallsN c (liftC (srcC false)) + nCallsN c (liftC (srcC true)) : ℕ) : ℝ) :=
        hWC c
      rw [hCs, hCs] at hW
      push_cast at hW
      exact hW
  · -- the native preparation
    have hP := bpublicOK_of hq hz
    rw [if_neg hz] at hγ
    obtain ⟨-, hd, -, -, hJ, -, -⟩ := GateODEBudget.binary_ode_sizes q.pub hP hγ
    have hd' : (q.pub.params.d : ℝ) ≤ 4096 * qOf q.pub.s q.T q.etaH q.etaD q.g q.ε := hd
    have hJ' : (q.pub.params.J : ℝ) ≤ 60 * qOf q.pub.s q.T q.etaH q.etaD q.g q.ε *
        logBudget q.g q.ε := hJ
    have hp : q.prepW N z₀ srcC =
        nprepC q.pub.params q.pub.UJg (q.ndW N z₀) q.ar (fun c => liftC (srcC c)) := by
      rw [GPub.prepW, if_neg hz]
    obtain ⟨hV, -, hC, -, hWC, -, -⟩ := native_ode_solver q.pub.params (q.pub.params_ok hP)
      q.pub.UJg (hadUJ4_ok q.pub.σ q.pub.hσ) (q.ndW N z₀) (q.ndW_public N z₀) q.ar q.ζ hP.ζ_pos.le
      (q.ar_ok hP N z₀) (fun c => liftC (srcC c)) hsrcV'
    have hgc := native_ode_gate_count q.pub.params (q.pub.params_ok hP) q.pub.UJg
      (hadUJ4_ok q.pub.σ q.pub.hσ) (q.ndW N z₀) (q.ndW_public N z₀) q.ar q.ζ hP.ζ_pos.le
      (q.ar_ok hP N z₀) (fun c => liftC (srcC c)) hsrcV'
    refine ⟨?_, ?_, hspace, ?_⟩
    · rw [hp]
      exact hV
    · -- gates
      rw [hp]
      have hUJl : q.pub.UJg.length = q.pub.σ + 3 := GateBinaryODE.hadUJ4_length q.pub.σ q.pub.hσ
      have hPG := q.privGatesW_le N z₀
      have hAp := q.wires_le
      have hcZ := q.card_Zg
      have hgc' : ((nprotocol (nprepC q.pub.params q.pub.UJg (q.ndW N z₀) q.ar
          (fun c => liftC (srcC c))) q.g hq.g_ge).worstCost wGateN : ℝ) ≤
          9000 * q.g * (((q.pub.params.d : ℝ) + 1) * ((q.pub.params.a : ℝ) + q.pub.params.m +
            q.pub.params.r + 1 + ((q.pub.UJg.length : ℕ) : ℝ) +
            ((privGates (q.ndW N z₀) q.ar : ℕ) : ℝ)) + ((q.pub.params.k : ℝ) + 1) +
            ((q.pub.params.J : ℝ) + 2) * ((q.pub.params.l : ℝ) + 1) +
            ((nGatesN (liftC (srcC false)) : ℝ) + nGatesN (liftC (srcC true))) +
            ((Fintype.card (Fin (q.k + 1)) : ℝ) + Fintype.card Zs +
              Fintype.card (SZ4 (q.k + 1) q.b ⊕ GeneralSparseAccess.AW q.k q.b) + q.ar.bT +
              q.ar.bP + q.ar.A)) := hgc
      rw [hUJl, hGs, hGs, Fintype.card_fin, hcZ] at hgc'
      have hSm : (q.k + 1 : ℝ) + q.pub.σ + q.pub.params.m + q.pub.params.r + q.pub.params.k ≤
          2 * (words q.pub : ℝ) := by
        have hσ := q.pub.hσ
        have : q.pub.kx + q.pub.σ + q.pub.params.m + q.pub.params.r + q.pub.params.k ≤
            2 * words q.pub := by
          unfold words
          omega
        exact_mod_cast this
      have hl : (q.pub.params.l : ℝ) ≤ words q.pub := by
        have : q.pub.params.l ≤ words q.pub := by
          unfold words
          omega
        exact_mod_cast this
      have hPG' : ((privGates (q.ndW N z₀) q.ar : ℕ) : ℝ) ≤ 65944 * ((words q.pub : ℝ) + 1) ^ 3 := by
        exact_mod_cast hPG
      have hcube := GateBitBudget.cube_le (add_nonneg hwr0 (by linarith)) hB0 (c := 300) hw
      have e1 : ((q.pub.params.a : ℕ) : ℝ) = (q.k : ℝ) + 4 := by
        show ((q.k + 1 + 3 : ℕ) : ℝ) = _
        push_cast
        ring
      generalize hQd : qOf (q.pub.s : ℝ) q.T q.etaH q.etaD q.g q.ε = Q at hQ1 hd' hJ' ⊢
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
      have key1 := GateODEBudget.gate_budget_arith 9000 q.g Q
        (logBudget q.g q.ε) (q.pub.params.d : ℝ) (q.pub.params.J : ℝ) (q.pub.params.k : ℝ)
        (q.pub.params.l : ℝ)
        (((q.pub.params.a : ℕ) : ℝ) + q.pub.params.m + q.pub.params.r + 1 +
          ((q.pub.σ + 3 : ℕ) : ℝ) + ((privGates (q.ndW N z₀) q.ar : ℕ) : ℝ))
        ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true))
        (((q.k + 1 : ℕ) : ℝ) + Fintype.card Zs + ((12 * q.k + 12 + 6 * q.b : ℕ) : ℝ) + q.ar.bT +
          q.ar.bP + q.ar.A)
        (by norm_num) hg0 hQ1 hℓ1 hd' hJ' (Nat.cast_nonneg _) (Nat.cast_nonneg _) hXs0 hG0 hAw0
      have key2 := words_gate_arith_g 36873000 (3 * 10 ^ 12) q.g Q (logBudget q.g q.ε)
        (words q.pub : ℝ) ((privGates (q.ndW N z₀) q.ar : ℕ) : ℝ)
        ((q.k + 1 : ℝ) + q.pub.σ + q.pub.params.m + q.pub.params.r + q.pub.params.k)
        (q.pub.params.l : ℝ) ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true))
        (Fintype.card Zs : ℝ)
        (((q.k + 1 : ℕ) : ℝ) + ((12 * q.k + 12 + 6 * q.b : ℕ) : ℝ) + q.ar.bT + q.ar.bP + q.ar.A)
        (by norm_num) (by norm_num) hg0 hQ1 hℓ1 hwr0 hPG' hSm (Nat.cast_nonneg _) hl hAp hG0 hZ0
      have key3 := GateBitBudget.budget_mono (c := 3 * 10 ^ 12) (C := 10 ^ 20) (k := (300 + 1) ^ 3)
        (g := q.g) (Q := Q) (a := ((words q.pub : ℝ) + logBudget q.g q.ε + 1) ^ 3)
        (b := (B + 1) ^ 3) (S₁ := (nGatesN (srcC false) : ℝ) + nGatesN (srcC true))
        (S₂ := (Fintype.card Zs : ℝ)) (by norm_num) hg0 (by linarith) (by positivity) hG0 hZ0
        (by norm_num) hcube (by norm_num)
      have e2 : 4097 * 9000 * q.g * (Q * ((((q.pub.params.a : ℕ) : ℝ) + q.pub.params.m +
            q.pub.params.r + 1 + ((q.pub.σ + 3 : ℕ) : ℝ) + ((privGates (q.ndW N z₀) q.ar : ℕ) : ℝ)) +
            q.pub.params.k + 1 + logBudget q.g q.ε * ((q.pub.params.l : ℝ) + 1)) +
            ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true)) +
            (((q.k + 1 : ℕ) : ℝ) + Fintype.card Zs + ((12 * q.k + 12 + 6 * q.b : ℕ) : ℝ) + q.ar.bT +
              q.ar.bP + q.ar.A)) =
          36873000 * q.g * (Q * (((privGates (q.ndW N z₀) q.ar : ℕ) : ℝ) +
            ((q.k + 1 : ℝ) + q.pub.σ + q.pub.params.m + q.pub.params.r + q.pub.params.k) +
            logBudget q.g q.ε * ((q.pub.params.l : ℝ) + 1) + 8) +
            ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true)) +
            ((Fintype.card Zs : ℝ) + (((q.k + 1 : ℕ) : ℝ) + ((12 * q.k + 12 + 6 * q.b : ℕ) : ℝ) +
              q.ar.bT + q.ar.bP + q.ar.A))) := by
        rw [e1]
        push_cast
        ring
      exact hgc'.trans (key1.trans (le_of_eq e2 |>.trans (key2.trans key3)))
    · -- calls
      intro c
      rw [hp, if_neg hz]
      have hI0 : (0 : ℝ) ≤ (if c Query.rowLocation then 1 else 0) +
          (if c Query.columnLocation then 1 else 0) + (if c Query.value then 1 else 0) := by
        split_ifs <;> norm_num
      have hcV := q.ndW_nCalls N z₀ c
      have hcP : (nCallsN c (nprepC q.pub.params q.pub.UJg (q.ndW N z₀) q.ar
          (fun c => liftC (srcC c))) : ℝ) ≤ 12 * (q.pub.params.d : ℝ) * (6 *
            ((if c Query.rowLocation then 1 else 0) + (if c Query.columnLocation then 1 else 0) +
              (if c Query.value then 1 else 0))) +
          ((nCallsN c (srcC false) : ℝ) + nCallsN c (srcC true)) := by
        have h1 : nCallsN c (nprepC q.pub.params q.pub.UJg (q.ndW N z₀) q.ar
            (fun c => liftC (srcC c))) ≤ 12 * q.pub.params.d * nCallsN c (q.ndW N z₀).V +
              nCallsN c (liftC (srcC false)) + nCallsN c (liftC (srcC true)) := hC c
        rw [hCs, hCs] at h1
        have h2 : nCallsN c (nprepC q.pub.params q.pub.UJg (q.ndW N z₀) q.ar
            (fun c => liftC (srcC c))) ≤ 12 * q.pub.params.d * (6 *
              ((if c Query.rowLocation then 1 else 0) + (if c Query.columnLocation then 1 else 0) +
                (if c Query.value then 1 else 0))) + nCallsN c (srcC false) +
              nCallsN c (srcC true) :=
          h1.trans (Nat.add_le_add_right (Nat.add_le_add_right
            (Nat.mul_le_mul_left _ hcV) _) _)
        have h3 : ((nCallsN c (nprepC q.pub.params q.pub.UJg (q.ndW N z₀) q.ar
            (fun c => liftC (srcC c))) : ℕ) : ℝ) ≤ ((12 * q.pub.params.d * (6 *
              ((if c Query.rowLocation then 1 else 0) + (if c Query.columnLocation then 1 else 0) +
                (if c Query.value then 1 else 0))) + nCallsN c (srcC false) +
              nCallsN c (srcC true) : ℕ) : ℝ) := by exact_mod_cast h2
        refine h3.trans (le_of_eq ?_)
        push_cast
        split_ifs <;> ring
      have hW : ((nprotocol (nprepC q.pub.params q.pub.UJg (q.ndW N z₀) q.ar
          (fun c => liftC (srcC c))) q.g hq.g_ge).worstCost (wCallN c) : ℝ) ≤
          40 * q.g * (nCallsN c (nprepC q.pub.params q.pub.UJg (q.ndW N z₀) q.ar
            (fun c => liftC (srcC c))) : ℝ) := hWC c
      generalize hQd : qOf (q.pub.s : ℝ) q.T q.etaH q.etaD q.g q.ε = Q at hd' ⊢
      generalize hId : ((if c Query.rowLocation then 1 else 0) +
          (if c Query.columnLocation then 1 else 0) + (if c Query.value then 1 else 0) : ℝ) = I
        at hI0 hcP ⊢
      have h4 := mul_le_mul_of_nonneg_left hd' (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤
        40 * 72) hg0) hI0)
      have h5 := mul_le_mul_of_nonneg_left hcP (mul_nonneg (by norm_num : (0 : ℝ) ≤ 40) hg0)
      have e6 : 40 * q.g * (12 * (q.pub.params.d : ℝ) * (6 * I) + ((nCallsN c (srcC false) : ℝ) +
          nCallsN c (srcC true))) = 40 * 72 * q.g * I * (q.pub.params.d : ℝ) +
          40 * q.g * ((nCallsN c (srcC false) : ℝ) + nCallsN c (srcC true)) := by ring
      have e7 : 40 * 72 * q.g * I * (4096 * Q) = 11796480 * q.g * Q * I := by ring
      rw [e6] at h5
      rw [e7] at h4
      exact hW.trans (h5.trans (add_le_add h4 le_rfl))

end BudgetW

end

end SparseHamiltonian.GeneralSparseODE

namespace ManuscriptConformance

noncomputable section
open ContinuousLinearMap SparseHamiltonian SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
  SparseHamiltonian.GateBinary SparseHamiltonian.GateBitBudget SparseHamiltonian.GeneralSparseAccess
open SparseHamiltonian.GeneralSparseODE (GPub markEmb padLift)
open SparseHamiltonian.GateBinaryODE (Pub SZ4)
open SparseHamiltonian.ZeroTimeGateODE (BPublicOK0 BZeroCase)
open NativeSparseBlockEncoding (Query)
open scoped InnerProduct

universe u

/-! ### Theorem `ode:thm:gates` of general size with a writer -/

set_option maxHeartbeats 8000000 in
/-- **Theorem `ode:thm:gates` for sparse access of general size with a writer, constant
coefficients** (handover item B4). The hypotheses, constants and conclusions of
`ode_thm_gates_general`, for the protocol `nprotocol ((odePubG …).prepW N 0 srcC) ḡ` (fixed before
the writer and the instance): the private operation calls the supplied locators and a value
writer through `GeneralSparseAccess.implPW` (the writer and its inverse in the places of the two
XOR calls of the padded value oracle, the copy masked by the validity flag), with the gates and
calls of `implP`; valid trials, the gate, qubit and call bounds (writer calls counted as value
calls), and for **every writer of the stored words on valid clean inputs**
(`GeneralSparseAccess.QData.Writer`) and every admissible instance with source circuits within
`ν = ε/(10⁴ ḡ)` of the controlled source preparations for the primitives of the writer model:
success at least `2/3`, conditional output within trace distance `ε` of the normalised solution
of `x' = -A x + b` on the index register (marker clean), and every successful trial within `ε` of
it up to a global phase. Formal restrictions: `formal_binaryDecoder`, `formal_nondegenerate`. -/
theorem ode_thm_gates_general_writer :
    ∃ C : ℝ, 0 < C ∧
      ∀ {X : Type u} {N s k b : ℕ} (D : GeneralSparseAccess.QData X N s k b) (bd : ℕ)
        (c0 etaH etaD T gbar ε r₀ rb : ℝ),
        2 ^ k < 2 * N → formal_binaryDecoder D c0 → comp_bits b bd [c0, T, etaH, etaD] →
        ∀ (hnd : formal_nondegenerate gbar (r₀ + T * rb))
        {Zs : Type} [Fintype Zs] [DecidableEq Zs]
        (srcC : Bool → List (NInstr ((Unit ⊕ Fin k) ⊕ Zs) (PY k b) Query)),
        (∀ c, ∀ i ∈ srcC c, i.Valid) →
        0 ≤ etaH → 0 ≤ etaD → 0 ≤ T → 0 < ε → ε ≤ 1 / 2 → 0 ≤ r₀ → 0 ≤ rb →
        (∀ j, ∀ i ∈ trialN ((odePubG k s D.s_le_pow b c0 etaH etaD T gbar ε r₀ rb).prepW N
          (fun _ => false) srcC) j, i.Valid) ∧
        ((nprotocol ((odePubG k s D.s_le_pow b c0 etaH etaD T gbar ε r₀ rb).prepW N
            (fun _ => false) srcC) gbar hnd.1).worstCost wGateN : ℝ) ≤
          C * gbar * (odeShape s T etaH etaD gbar ε *
              (bitB bd N 0 0 (odeShape s T etaH etaD gbar ε) gbar ε + 1) ^ 3 +
            ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true)) + Fintype.card Zs) ∧
        (odeQubitsG (odePubG k s D.s_le_pow b c0 etaH etaD T gbar ε r₀ rb) Zs : ℝ) ≤
          C * (bitB bd N 0 0 (odeShape s T etaH etaD gbar ε) gbar ε + 1) ^ 3 +
            C * Fintype.card Zs ∧
        (∀ c : Query → Bool,
          ((nprotocol ((odePubG k s D.s_le_pow b c0 etaH etaD T gbar ε r₀ rb).prepW N
            (fun _ => false) srcC) gbar hnd.1).worstCost (wCallN c) : ℝ) ≤
          (if T = 0 ∨ etaH + etaD = 0 then 0 else
            C * gbar * odeShape s T etaH etaD gbar ε *
              ((if c Query.rowLocation then 1 else 0) + (if c Query.columnLocation then 1 else 0) +
                (if c Query.value then 1 else 0))) +
          C * gbar * ((nCallsN c (srcC false) : ℝ) + nCallsN c (srcC true))) ∧
        ∀ (Wr : GeneralSparseAccess.QData.Writer D) (x : X),
          (∀ i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ etaH ^ 2) →
          (∀ j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ etaH ^ 2) →
          (∀ i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ etaD ^ 2) →
          (∀ j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ etaD ^ 2) →
          (∀ w : EuclideanSpace ℂ (Fin N), 0 ≤ (inner ℂ w (SparseStateOverlap.matrixOperator
            (ODEMatrixEnergy.dissipativePart (D.matrix x)) w)).re) →
          ∀ (Jsrc : Bool → Reg (Fin k) ℂ →L[ℂ] Reg (Fin k) ℂ) (x0 v : Reg (Fin k) ℂ) (ζs : ℝ),
          (∀ c, OracleCircuit.IsUnitary (Jsrc c)) → 0 ≤ ζs →
          (∀ c, ApproxOn CleanX (nrun (Wr.prims (R := ℂ) x) (srcC c))
            (liftB (srcIdeal c (Jsrc c))) ζs) →
          ζs ≤ ImprovedODEQueryBudget.precision gbar ε →
          ‖x0‖ = r₀ → ‖v‖ = rb →
          (x0 ≠ 0 → Jsrc false (seedV (S := Fin k)) = ODEStateNormalization.unitDirection x0) →
          (v ≠ 0 → Jsrc true (seedV (S := Fin k)) = ODEStateNormalization.unitDirection v) →
          ODEConstantForcing.solution (-padLift D x) x0 v T ≠ 0 →
          r₀ + T * rb ≤ gbar * ‖ODEConstantForcing.solution (-padLift D x) x0 v T‖ →
          HeraldedOutput (nprotocol ((odePubG k s D.s_le_pow b c0 etaH etaD T gbar ε r₀ rb).prepW N
              (fun _ => false) srcC) gbar hnd.1) (Wr.prims (R := ℂ) x)
            (ODEStateNormalization.unitDirection
              (cleanAlong (Fin.castSuccEmb : Fin k ↪ Fin (k + 1))
                (ODEConstantForcing.solution (-padLift D x) x0 v T))) ε ∧
          ∀ j : ℕ, ((goodN (S := Fin (k + 1)))†) (nrun (Wr.prims (R := ℂ) x)
              (trialN ((odePubG k s D.s_le_pow b c0 etaH etaD T gbar ε r₀ rb).prepW N
                (fun _ => false) srcC) j) sN) ≠ 0 →
            ∃ ω : ℂ, ‖ω‖ = 1 ∧
              ‖ω • ODEStateNormalization.unitDirection (((goodN (S := Fin (k + 1)))†)
                  (nrun (Wr.prims (R := ℂ) x) (trialN ((odePubG k s D.s_le_pow b c0 etaH etaD T
                    gbar ε r₀ rb).prepW N (fun _ => false) srcC) j) sN)) -
                ODEStateNormalization.unitDirection
                  (cleanAlong (Fin.castSuccEmb : Fin k ↪ Fin (k + 1))
                    (ODEConstantForcing.solution (-padLift D x) x0 v T))‖ ≤ ε := by
  refine ⟨10 ^ 23, by norm_num, ?_⟩
  intro X N s k b D bd c0 etaH etaD T gbar ε r₀ rb hk hF hbits hnd Zs _ _ srcC hsrcV hH hD hT hε
    hε2 hr0 hrb
  obtain ⟨hbd, hc0b, hTb, hHb, hDb⟩ := hbits
  have hg := hnd.1
  have hB := hnd.2
  have hε1 : ε ≤ 1 := by linarith
  have hg0 : 0 ≤ gbar := by linarith
  set q := odePubG k s D.s_le_pow b c0 etaH etaD T gbar ε r₀ rb with hqdef
  have hqp : q.pub = odePub (k + 1) (sbP s) ((sbP_le D.s_le_pow).trans (Nat.le_succ k)) b c0
      etaH etaD T gbar ε r₀ rb := rfl
  have hq : BPublicOK0 q.pub := by
    rw [hqp]
    exact odePub_ok _ hF.hb hF.hc0 hH hD hT hg hε hε2 hr0 hrb hB
  have hγ := odePub_gamma hqp hF.hb hbd
  obtain ⟨hζ, hζs⟩ := odePub_zeta hqp hH hD hT hg hε hε1
  obtain ⟨hV, hWg0, hWq0, hWc0⟩ := GeneralSparseODE.general_ode_budget_writer bd q hq hγ hζ hbd hc0b hTb
    hHb hDb N (fun _ => false) srcC hsrcV
  have hWg : ((nprotocol (q.prepW N (fun _ => false) srcC) gbar hnd.1).worstCost wGateN : ℝ) ≤
      10 ^ 20 * gbar * (GateODEBudget.qOf ((sP s : ℕ) : ℝ) T etaH etaD gbar ε *
        (bitB bd (2 ^ (k + 1)) 0 0 (GateODEBudget.qOf ((sP s : ℕ) : ℝ) T etaH etaD gbar ε) gbar ε +
          1) ^ 3 + ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true)) + Fintype.card Zs) := hWg0
  have hWq : (Fintype.card (q.reg Zs) : ℝ) ≤ 3 * 10 ^ 11 * (bitB bd (2 ^ (k + 1)) 0 0
      (GateODEBudget.qOf ((sP s : ℕ) : ℝ) T etaH etaD gbar ε) gbar ε + 1) ^ 3 +
      2 * Fintype.card Zs := hWq0
  have hWc : ∀ c : Query → Bool, ((nprotocol (q.prepW N (fun _ => false) srcC) gbar
      hnd.1).worstCost (wCallN c) : ℝ) ≤ (if T = 0 ∨ etaH + etaD = 0 then 0 else
        11796480 * gbar * GateODEBudget.qOf ((sP s : ℕ) : ℝ) T etaH etaD gbar ε *
          ((if c Query.rowLocation then 1 else 0) + (if c Query.columnLocation then 1 else 0) +
            (if c Query.value then 1 else 0))) +
        40 * gbar * ((nCallsN c (srcC false) : ℝ) + nCallsN c (srcC true)) := hWc0
  -- the query shapes and the word budgets
  have hsP : (((sP s : ℕ) : ℝ)) ≤ 2 * (s : ℝ) := by
    have h' : ((sP s : ℕ) : ℝ) ≤ ((2 * s : ℕ) : ℝ) := by exact_mod_cast (sP_lt D.slots_pos).le
    push_cast at h'
    exact h'
  have hQQ : GateODEBudget.qOf ((sP s : ℕ) : ℝ) T etaH etaD gbar ε ≤
      2 * GateODEBudget.qOf s T etaH etaD gbar ε :=
    qOf_le_of_le (Nat.cast_nonneg _) hsP hT hH hD hg hε hε1
  have hQ1 : 1 ≤ GateODEBudget.qOf s T etaH etaD gbar ε :=
    GateRemarks.ODE.one_le_qOf hT hH hD hg hε hε1
  have hQ1' : 1 ≤ GateODEBudget.qOf ((sP s : ℕ) : ℝ) T etaH etaD gbar ε :=
    GateRemarks.ODE.one_le_qOf hT hH hD hg hε hε1
  have hB0 : 0 ≤ bitB bd N 0 0 (GateODEBudget.qOf s T etaH etaD gbar ε) gbar ε :=
    bitB_nonneg _ _ _ _ (mul_nonneg (by linarith) hg0) hε hε1
  have hB0' : 0 ≤ bitB bd (2 ^ (k + 1)) 0 0 (GateODEBudget.qOf ((sP s : ℕ) : ℝ) T etaH etaD gbar ε)
      gbar ε := bitB_nonneg _ _ _ _ (mul_nonneg (by linarith) hg0) hε hε1
  have hBB := bitB_pad_le (bd := bd) hk (by linarith) hQQ (by linarith) hg0 hε
  have hcube := cube_pad_le hB0 hB0' hBB
  have hY : 0 ≤ (bitB bd N 0 0 (GateODEBudget.qOf s T etaH etaD gbar ε) gbar ε + 1) ^ 3 := by
    positivity
  have hY' : 0 ≤ (bitB bd (2 ^ (k + 1)) 0 0 (GateODEBudget.qOf ((sP s : ℕ) : ℝ) T etaH etaD gbar ε)
      gbar ε + 1) ^ 3 := by positivity
  have hZ0 : (0 : ℝ) ≤ Fintype.card Zs := Nat.cast_nonneg _
  rw [odeShape_eq]
  refine ⟨hV, ?_, ?_, ?_, ?_⟩
  · -- gates
    refine hWg.trans ?_
    generalize GateODEBudget.qOf ((sP s : ℕ) : ℝ) T etaH etaD gbar ε = Q' at hQQ hQ1' hcube hY' ⊢
    generalize GateODEBudget.qOf s T etaH etaD gbar ε = Q at hQQ hQ1 hcube hB0 hY ⊢
    generalize (bitB bd (2 ^ (k + 1)) 0 0 Q' gbar ε + 1) ^ 3 = Y' at hcube hY' ⊢
    generalize (bitB bd N 0 0 Q gbar ε + 1) ^ 3 = Y at hcube hY ⊢
    have hG0 : (0 : ℝ) ≤ (nGatesN (srcC false) : ℝ) + nGatesN (srcC true) := by positivity
    have h1 : Q' * Y' ≤ 128 * (Q * Y) := by
      have h2 : Q' * Y' ≤ (2 * Q) * Y' := mul_le_mul_of_nonneg_right hQQ hY'
      have h3 : (2 * Q) * Y' ≤ (2 * Q) * (64 * Y) := mul_le_mul_of_nonneg_left hcube (by linarith)
      nlinarith
    have hQY : 0 ≤ Q * Y := mul_nonneg (by linarith) hY
    have h4 : (10 : ℝ) ^ 20 * gbar * (Q' * Y' + ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true)) +
        Fintype.card Zs) ≤ 10 ^ 20 * gbar * (128 * (Q * Y) + ((nGatesN (srcC false) : ℝ) +
          nGatesN (srcC true)) + Fintype.card Zs) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h5 : (10 : ℝ) ^ 20 * gbar * (128 * (Q * Y) + ((nGatesN (srcC false) : ℝ) +
          nGatesN (srcC true)) + Fintype.card Zs) ≤ 10 ^ 23 * gbar * (Q * Y +
          ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true)) + Fintype.card Zs) := by
      have h6 : (10 : ℝ) ^ 20 * (128 * (Q * Y) + ((nGatesN (srcC false) : ℝ) +
          nGatesN (srcC true)) + Fintype.card Zs) ≤ 10 ^ 23 * (Q * Y +
          ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true)) + Fintype.card Zs) := by
        nlinarith
      have := mul_le_mul_of_nonneg_left h6 hg0
      linarith
    linarith
  · -- qubits
    have h1 := mul_le_mul_of_nonneg_left hcube (by norm_num : (0 : ℝ) ≤ 3 * 10 ^ 11)
    have h2 : (2 : ℝ) * Fintype.card Zs ≤ 10 ^ 23 * Fintype.card Zs :=
      mul_le_mul_of_nonneg_right (by norm_num) hZ0
    have h3 : (3 * 10 ^ 11 : ℝ) * (64 * (bitB bd N 0 0 (GateODEBudget.qOf s T etaH etaD gbar ε)
        gbar ε + 1) ^ 3) ≤ 10 ^ 23 * (bitB bd N 0 0 (GateODEBudget.qOf s T etaH etaD gbar ε)
        gbar ε + 1) ^ 3 := by nlinarith
    have hq' : (odeQubitsG q Zs : ℝ) = (Fintype.card (q.reg Zs) : ℝ) := rfl
    rw [hq']
    linarith
  · -- calls
    intro c
    have hW := hWc c
    have hI0 : (0 : ℝ) ≤ (if c Query.rowLocation then 1 else 0) +
        (if c Query.columnLocation then 1 else 0) + (if c Query.value then 1 else 0) := by
      split_ifs <;> norm_num
    have hS0 : (0 : ℝ) ≤ (nCallsN c (srcC false) : ℝ) + nCallsN c (srcC true) := by positivity
    have hS : 40 * gbar * ((nCallsN c (srcC false) : ℝ) + nCallsN c (srcC true)) ≤
        10 ^ 23 * gbar * ((nCallsN c (srcC false) : ℝ) + nCallsN c (srcC true)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by norm_num) hg0) hS0
    by_cases hz : T = 0 ∨ etaH + etaD = 0
    · rw [if_pos hz] at hW
      rw [if_pos hz]
      linarith
    · rw [if_neg hz] at hW
      rw [if_neg hz]
      generalize hId : ((if c Query.rowLocation then 1 else 0) +
          (if c Query.columnLocation then 1 else 0) + (if c Query.value then 1 else 0) : ℝ) = I
        at hI0 hW ⊢
      generalize GateODEBudget.qOf ((sP s : ℕ) : ℝ) T etaH etaD gbar ε = Q' at hQQ hW
      have h1 : 11796480 * gbar * Q' * I ≤ 10 ^ 23 * gbar * GateODEBudget.qOf s T etaH etaD gbar ε *
          I := by
        have h2 : Q' * I ≤ (2 * GateODEBudget.qOf s T etaH etaD gbar ε) * I :=
          mul_le_mul_of_nonneg_right hQQ hI0
        have h3 : 0 ≤ GateODEBudget.qOf s T etaH etaD gbar ε * I :=
          mul_nonneg (by linarith) hI0
        have h4 : 11796480 * (Q' * I) ≤ 10 ^ 23 * (GateODEBudget.qOf s T etaH etaD gbar ε * I) := by
          nlinarith
        have h5 := mul_le_mul_of_nonneg_left h4 hg0
        nlinarith
      linarith
  · -- the guarantees
    intro Wr x hrH hcH hrD hcD hPSD Jsrc x0 v ζs hJ hζs0 hsrc hacc hx0 hv hpx hpv hne hBud
    have hγ' : ¬ BZeroCase q.pub → q.γ = GateODEBudget.gammaOf q.T q.etaH q.etaD q.g q.ε := by
      intro hz
      have h := hγ
      rw [if_neg hz] at h
      exact h
    -- the public data is passed literally (not as the local definition `q`), so that the
    -- outcome has the types of the statement and the final unification is syntactic
    have o := (GeneralSparseODE.general_ode_outcome_writer
      (odePubG k s D.s_le_pow b c0 etaH etaD T gbar ε r₀ rb) hq hγ' D (fun _ => false) hF.zero
      hF.dec Wr srcC hsrcV x hrH hcH hrD hcD hPSD Jsrc x0 v ζs hJ hζs0 hsrc (hζs ζs hacc) hx0 hv hpx
      hpv hne hBud).mono (β' := ε) (by
        show ε / 250 ≤ ε
        linarith)
    rw [markEmb_eq_cleanAlong] at o
    exact ⟨⟨o.success_two_thirds, o.output_density, o.conditional_error⟩, o.trial_direction⟩

end

end ManuscriptConformance
