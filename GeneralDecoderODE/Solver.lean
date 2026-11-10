import GeneralSparseODE.Constant

/-!
# The constant-coefficient general solver for any implementation of the padded oracles

The constant-coefficient gate solver for sparse access of general size (`GeneralSparseODE`) calls
the supplied oracles through the implementation `GeneralSparseAccess.implP` of the padded oracles.
This module states it for **any implementation** `impl` of the padded oracles of sparse access `D`
in the binary format, from any unitary primitives `P` on any register `Y` and on clean ancillas
`Xa` (`GeneralSparseAccess.ImplOK`):

* `ndI q impl`: the released private Cayley operation of the padded problem with every padded call
  replaced by `impl` (`GeneralSparseODE.substOp`), the ancillas added to its scratch;
* `arI q Xa`: the arithmetic of the released solver on the base wires (`GeneralSparseODE.liftA`);
* `prepI q impl srcC`: the direct source assembly in the zero case, the native preparation with
  `ndI q impl` otherwise; the source circuits, calling `P`, on the low wires of the padded system
  register;
* `general_ode_outcomeI`: the guarantees of `GeneralSparseODE.general_ode_outcome` for the
  protocol `nprotocol (prepI q impl srcC) g` and the primitives `P`.

The supplied-oracle solver of `GeneralSparseODE` is the case `impl = implP N s z₀`, `P = D.prims x`;
the decoder solver of `GeneralDecoderODE.Decoder` is the case of the decoded data with the
composite implementation through the decoding circuit.
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
open GateBinaryODE (Pub SZ4 mLift privFam hLift lLift target_lift hadUJ4_ok)
open ZeroTimeGateODE (BPublicOK0 BZeroCase zprepC srcRot binary_target_zero bpublicOK_of)
open SourceAccuracyODE (WOutcome)
open NativeSparseBlockEncoding (Query)
open ODEStateNormalization (unitDirection)
open scoped InnerProduct

/-! ### The operation, the arithmetic and the preparation -/

section Def

variable (q : GPub) {Y Xa : Type*}

/-- **The private Cayley operation calling the primitives through `impl`**: the released operation
of the padded problem with every padded call replaced by its implementation `impl`. -/
def ndI (impl : Query → List (NInstr (PY (q.k + 1) q.b ⊕ Xa) Y Query)) :
    NativeOp (LabW q.pub.params.k q.pub.params.l) (Fin q.pub.params.a ⊕ Fin (q.k + 1))
      (SZ4 (q.k + 1) q.b ⊕ Xa) Y Query :=
  substOp q.pub.nd impl

/-- **The arithmetic** of the released operation on the base wires, with the ancillas `Xa` in the
scratch. -/
def arI (Xa : Type*) : Arith (NB (LabW q.pub.params.k q.pub.params.l)
    (Fin q.pub.params.a ⊕ Fin (q.k + 1)) (SZ4 (q.k + 1) q.b ⊕ Xa)) :=
  liftA q.pub.ar

/-- **The preparation through `impl`**: the direct source assembly in the zero case, the native
preparation with the operation `ndI q impl` otherwise; the source circuits on the low wires of the
padded system register. -/
def prepI {Zs : Type*} [Fintype Zs] [DecidableEq Zs] [Fintype Xa] [DecidableEq Xa]
    (impl : Query → List (NInstr (PY (q.k + 1) q.b ⊕ Xa) Y Query))
    (srcC : Bool → List (NInstr ((Unit ⊕ Fin q.k) ⊕ Zs) Y Query)) :
    List (NInstr (NW q.pub.params (Fin (q.k + 1)) Zs (SZ4 (q.k + 1) q.b ⊕ Xa)
      (arI q Xa).bT (arI q Xa).bP (arI q Xa).A) Y Query) :=
  if BZeroCase q.pub then zprepC (srcRot q.T q.r₀ q.rb) (fun c => liftC (srcC c))
  else nprepC q.pub.params q.pub.UJg (ndI q impl) (arI q Xa) (fun c => liftC (srcC c))

end Def

section Props

variable (q : GPub) {Y Xa : Type*} [Fintype Y] [DecidableEq Y] [Fintype Xa] [DecidableEq Xa]

omit [Fintype Y] [DecidableEq Y] [Fintype Xa] in
theorem ndI_public {impl : Query → List (NInstr (PY (q.k + 1) q.b ⊕ Xa) Y Query)}
    (hv : ∀ j, ∀ i ∈ impl j, i.Valid) : (ndI q impl).Public :=
  substOp_public q.pub.nd_public hv

omit [Fintype Y] [DecidableEq Y] [Fintype Xa] in
theorem arI_ok (hq : q.pub.OK) (impl : Query → List (NInstr (PY (q.k + 1) q.b ⊕ Xa) Y Query)) :
    ArithOK (arI q Xa) (Sum.inl (Sum.inr (ndI q impl).o)) (ndI q impl).dec q.ζ :=
  arithOK_liftA q.pub.ar _ _ _ (q.pub.ar_ok hq)

omit [Fintype Y] [DecidableEq Y] [Fintype Xa] [DecidableEq Xa] in
/-- The compute circuit has at most `28 (k + 1) + 2 + 6 G` gates for `G` gates per call of
`impl`. -/
theorem ndI_nGates (impl : Query → List (NInstr (PY (q.k + 1) q.b ⊕ Xa) Y Query)) (G : ℕ)
    (hG : ∀ j, nGatesN (impl j) ≤ G) :
    nGatesN (ndI q impl).V ≤ 28 * (q.k + 1) + 2 + G * 6 := by
  have h := nGatesN_substOp_le q.pub.nd impl G hG
  have hg : nGatesN q.pub.nd.V = 28 * (q.k + 1) + 2 :=
    GateBinaryODE.computeV4_nGates (q.k + 1) q.b q.pub.params.k q.pub.params.l
  have hc : nCallsN (fun _ => true) q.pub.nd.V = 6 := by
    have := GateBinaryODE.computeV4_nCalls (k := q.k + 1) (b := q.b) (kq := q.pub.params.k)
      (lq := q.pub.params.l) (fun _ => true)
    simp only [if_true] at this
    exact this
  unfold ndI
  rw [hg, hc] at h
  exact h

omit [Fintype Y] [DecidableEq Y] [Fintype Xa] [DecidableEq Xa] in
/-- The compute circuit makes at most `2 c` calls of each kind it calls, for at most `c` calls
per call of `impl`, all of the kind of the call. -/
theorem ndI_nCalls {impl : Query → List (NInstr (PY (q.k + 1) q.b ⊕ Xa) Y Query)} {c : ℕ}
    (hK : KindOK impl id c) (p : Query → Bool) :
    nCallsN p (ndI q impl).V ≤ 2 * c * ((if p Query.rowLocation then 1 else 0) +
      (if p Query.columnLocation then 1 else 0) + (if p Query.value then 1 else 0)) := by
  have h := nCallsN_substOp_le q.pub.nd hK p
  have hc := GateBinaryODE.computeV4_nCalls (k := q.k + 1) (b := q.b) (kq := q.pub.params.k)
    (lq := q.pub.params.l) p
  have hc' : nCallsN p q.pub.nd.V = 2 * (if p Query.rowLocation then 1 else 0) +
      2 * (if p Query.columnLocation then 1 else 0) + 2 * (if p Query.value then 1 else 0) := hc
  have h' : nCallsN p (ndI q impl).V ≤ c * nCallsN p q.pub.nd.V := h
  rw [hc'] at h'
  refine h'.trans (le_of_eq ?_)
  ring

end Props

/-! ### The outcome -/

section Outcome

variable {X : Type*} {N : ℕ} {Zs : Type*} [Fintype Zs] [DecidableEq Zs]
variable {Y Xa : Type*} [Fintype Y] [DecidableEq Y] [Fintype Xa] [DecidableEq Xa]

set_option maxHeartbeats 1600000 in
/-- **The outcome of the general solver through any implementation** (constant coefficients,
every `T ≥ 0`): for public data with `BPublicOK0 q.pub` and the public rescaling outside the zero
case, sparse access of general size with the decoder `c₀(X + iY)`, a public word `z₀` decoded as
`0`, unitary primitives `P` on a register `Y`, an implementation `impl` of the padded oracles at
`x` from `P` on clean ancillas, and every input as in `GeneralSparseODE.general_ode_outcome` with
source circuits calling `P`, the protocol `nprotocol (prepI q impl srcC) g` has the guarantees
`WOutcome … (ε / 250)` for `P`, against the marker embedding of the solution of
`x' = -A x + b`, `A = padLift D x`. -/
theorem general_ode_outcomeI (q : GPub) (hq : BPublicOK0 q.pub)
    (hγ : ¬ BZeroCase q.pub →
      q.γ = GateODEBudget.gammaOf q.T q.etaH q.etaD q.g q.ε)
    (D : QData X N q.s q.k q.b) (z₀ : Cfg (VW q.b)) (hz₀ : D.val z₀ = 0)
    (hdec : ∀ z, D.val z = (q.c0 : ℂ) * gauss z) (x : X)
    (P : Query → Reg Y ℂ →L[ℂ] Reg Y ℂ) (hP : ∀ j, IsUnitary (P j))
    (impl : Query → List (NInstr (PY (q.k + 1) q.b ⊕ Xa) Y Query))
    (himpl : ImplOK P (GateBinary.prims (R := ℂ) (D.padData z₀ hz₀) (Equiv.refl _) x) impl)
    (srcC : Bool → List (NInstr ((Unit ⊕ Fin q.k) ⊕ Zs) Y Query))
    (hsrcV : ∀ c, ∀ i ∈ srcC c, i.Valid)
    (hrH : ∀ i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ q.etaH ^ 2)
    (hcH : ∀ j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ q.etaH ^ 2)
    (hrD : ∀ i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ q.etaD ^ 2)
    (hcD : ∀ j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ q.etaD ^ 2)
    (hPSD : ∀ w : EuclideanSpace ℂ (Fin N), 0 ≤ (inner ℂ w (SparseStateOverlap.matrixOperator
      (ODEMatrixEnergy.dissipativePart (D.matrix x)) w)).re)
    (Jsrc : Bool → Reg (Fin q.k) ℂ →L[ℂ] Reg (Fin q.k) ℂ) (x0 v : Reg (Fin q.k) ℂ) (ζs : ℝ)
    (hJ : ∀ c, IsUnitary (Jsrc c)) (hζs : 0 ≤ ζs)
    (hsrc : ∀ c, ApproxOn CleanX (nrun P (srcC c)) (liftB (srcIdeal c (Jsrc c))) ζs)
    (hbud : 98304 * GateODEBudget.qOf q.pub.s q.T q.etaH q.etaD q.g q.ε * q.ζ + 2 * ζs ≤
      4 * q.pub.params.nu)
    (hx0 : ‖x0‖ = q.r₀) (hv : ‖v‖ = q.rb)
    (hpx : x0 ≠ 0 → Jsrc false (seedV (S := Fin q.k)) = unitDirection x0)
    (hpv : v ≠ 0 → Jsrc true (seedV (S := Fin q.k)) = unitDirection v)
    (hne : ODEConstantForcing.solution (-padLift D x) x0 v q.T ≠ 0)
    (hB : q.r₀ + q.T * q.rb ≤ q.g * ‖ODEConstantForcing.solution (-padLift D x) x0 v q.T‖) :
    WOutcome (prepI q impl srcC) q.g (q.ε / 250) hq.g_ge P
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
  have hsrc' : ∀ c, ApproxOn CleanX (nrun P (liftC (srcC c)))
      (liftB (srcIdeal c (lowOp (Jsrc c)))) ζs := fun c =>
    approxOn_liftSrc P (srcC c) c (Jsrc c) hζs (hsrc c)
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
    have hp : prepI q impl srcC = zprepC (srcRot q.T q.r₀ q.rb) (fun c => liftC (srcC c)) := by
      rw [prepI, if_pos hz]
    rw [hp, ← hsol, ht]
    exact SourceAccuracyODE.native_zero_outcome (Z := SZ4 (q.k + 1) q.b ⊕ Xa)
      (Y := Y) (J := Query) q.pub.params.a q.pub.params.m q.pub.params.r q.pub.params.K
      q.pub.params.k q.pub.params.l q.pub.params.f (arI q Xa).bT (arI q Xa).bP (arI q Xa).A
      q.pub.T q.pub.g q.pub.ε
      q.pub.r₀ q.pub.rb hq.T_nonneg hq.g_ge hq.ε_pos hq.ε_half hq.r₀_nonneg hq.rb_nonneg hq.B_pos
      (fun c => liftC (srcC c)) hsrcV' P (fun c => lowOp (Jsrc c))
      (markEmb q.k x0) (markEmb q.k v) ζs hP hJ' hζs hsrc' (by linarith) hx0'
      hv' hpx' hpv' hne' hB'
  · -- the native preparation
    have hP' := bpublicOK_of hq hz
    obtain ⟨-, hd, -, -, -, -, -⟩ := GateODEBudget.binary_ode_sizes q.pub hP' (hγ hz)
    have hd' : (q.pub.params.d : ℝ) ≤ 4096 * GateODEBudget.qOf q.pub.s q.T q.etaH q.etaD q.g q.ε :=
      hd
    have hζ0 : (0 : ℝ) ≤ q.ζ := hP'.ζ_pos.le
    have hbud' : 24 * (q.pub.params.d : ℝ) * q.ζ + 2 * ζs ≤ 4 * q.pub.params.nu := by
      have := mul_le_mul_of_nonneg_right hd' hζ0
      linarith
    have hN : NativeOK P (ndI q impl)
        (selOp (labFam (privFam q.pub.params Dp (Equiv.refl _) x q.pub.rho q.pub.γ) false)) :=
      nativeOK_substOp P (prims (R := ℂ) Dp (Equiv.refl _) x) hP
        (prims_isUnitary Dp (Equiv.refl _) x) himpl q.pub.nd q.pub.nd_public _
        (q.pub.nativeOK hP' Dp (Equiv.refl _) hrange hdecP x)
    have hp : prepI q impl srcC =
        nprepC q.pub.params q.pub.UJg (ndI q impl) (arI q Xa) (fun c => liftC (srcC c)) := by
      rw [prepI, if_neg hz]
    have h := SourceAccuracyODE.native_ode_outcome q.pub.params (q.pub.params_ok hP') q.pub.UJg
      (hadUJ4_ok q.pub.σ q.pub.hσ) (ndI q impl) (ndI_public q himpl.valid) (arI q Xa) q.pub.ζ
      hP'.ζ_pos.le (arI_ok q hP' impl) (fun c => liftC (srcC c)) hsrcV' P
      (privFam q.pub.params Dp (Equiv.refl _) x q.pub.rho q.pub.γ) (fun c => lowOp (Jsrc c))
      (hLift Dp (Equiv.refl _) x) (lLift Dp (Equiv.refl _) x) (markEmb q.k x0) (markEmb q.k v) ζs
      hP hN hζs hsrc' hbud'
      (q.pub.instanceOK hP' Dp (Equiv.refl _) hrange x hrH' hcH' hrD' hcD' hPSD'
        (fun c => lowOp (Jsrc c)) (markEmb q.k x0) (markEmb q.k v) hJ' hx0' hv' hpx' hpv' hne' hB')
    rw [hp]
    exact wOutcome_target h ((target_lift q.pub.params Dp (Equiv.refl _) x (markEmb q.k x0)
      (markEmb q.k v)).trans hsol)

end Outcome

end

end SparseHamiltonian.GeneralDecoderODE
