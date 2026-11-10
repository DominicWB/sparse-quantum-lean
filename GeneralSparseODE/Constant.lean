import GeneralSparseODE.Padded
import GeneralSparseODE.Source
import SourceAccuracyODE.Constant

/-!
# The constant-coefficient gate solver for sparse access of general size

The released constant-coefficient gate solver from binary sparse data (`ZeroTimeGateODE.bprepC`,
`SourceAccuracyODE.binary_ode_outcome_nonneg`) on the padded data of a general sparse access
`D : GeneralSparseAccess.QData X N s k b` (`QData.padData`: `k + 1`-bit index words,
`2^⌈log₂ s⌉` slots, the stored words decoded by `val = c₀(X + iY)`), with

* the private Cayley operation calling the supplied oracles: every call of the padded oracles in its
  compute circuit replaced by the implementation `GeneralSparseAccess.implP` from the supplied ones
  (`GPub.nd`, `substOp`), the ancillas of the implementations added to its scratch;
* the arithmetic of the released solver on the base wires (`GPub.ar`, `liftA`);
* the source circuits of the general problem, on the `k` qubits of the index register and calling
  the supplied oracles, placed on the low wires of the padded system register (`liftC`).

`GPub` is the public data: the index bits `k` of the general access, the sparsity `s ≤ 2^k`, the
stored bits and the public parameters of `GateBinaryODE.Pub` (`GPub.pub`: `k + 1` system qubits,
`⌈log₂ s⌉` slot bits). `GPub.prep`: the direct source assembly in the zero case
(`ZeroTimeGateODE.BZeroCase`), the native preparation otherwise.

`general_ode_outcome`: for every input whose matrix has the released energy bounds and an accretive
dissipative part, with source circuits within `ζ_s` of the controlled preparations of unitary
interfaces `J_src` of the `k`-qubit system and the source budget `98304 q* ζ + 2 ζ_s ≤ 4 ν` of
`SourceAccuracyODE`, the protocol `nprotocol (q.prep N z₀ srcC) g` has the guarantees
`WOutcome … (ε / 250)` for the supplied oracles `D.prims x`, against the marker embedding of the
solution `x(T)` of `x' = -A x + b`, `A = padLift D x` the matrix extended by zero to the `2^k`
index words. The padded problem is the zero extension of this one (`Padded`, `Embed`).
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GeneralSparseODE

noncomputable section
open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
  SparseHamiltonian.GateBinary
open SparseHamiltonian.GeneralSparseAccess
open SparseHamiltonian.OracleCircuit
open GateBinaryODE (Pub SZ4 mLift privFam hLift lLift target_lift hadUJ4_ok)
open ZeroTimeGateODE (BPublicOK0 BZeroCase zprepC srcRot binary_target_zero bpublicOK_of)
open SourceAccuracyODE (WOutcome)
open NativeSparseBlockEncoding (Query)
open ODEStateNormalization (unitDirection)
open scoped InnerProduct

/-! ### The public data -/

/-- **The public data of the constant-coefficient solver for sparse access of general size**:
the index bits `k`, the sparsity `s ≤ 2^k`, the stored bits `b` and the public parameters of the
solver from binary data. -/
structure GPub where
  /-- The index bits of the general access (`N ≤ 2^k`). -/
  k : ℕ
  /-- The sparsity. -/
  s : ℕ
  /-- The sparsity fits the index register. -/
  hs : s ≤ 2 ^ k
  /-- The stored bits of each component. -/
  b : ℕ
  /-- The decoder scale. -/
  c0 : ℝ
  /-- The energy bound of the Hamiltonian part. -/
  etaH : ℝ
  /-- The energy bound of the dissipative part. -/
  etaD : ℝ
  /-- The Cayley rescaling. -/
  γ : ℝ
  /-- The time. -/
  T : ℝ
  /-- The public amplification bound. -/
  g : ℝ
  /-- The accuracy. -/
  ε : ℝ
  /-- The norm of the initial state. -/
  r₀ : ℝ
  /-- The norm of the forcing. -/
  rb : ℝ
  /-- The arithmetic accuracy. -/
  ζ : ℝ

namespace GPub

variable (q : GPub)

/-- **The public data of the padded problem**: `k + 1` system qubits and `⌈log₂ s⌉` slot bits. -/
def pub : Pub where
  kx := q.k + 1
  σ := sbP q.s
  hσ := (sbP_le q.hs).trans (Nat.le_succ q.k)
  b := q.b
  c0 := q.c0
  etaH := q.etaH
  etaD := q.etaD
  γ := q.γ
  T := q.T
  g := q.g
  ε := q.ε
  r₀ := q.r₀
  rb := q.rb
  ζ := q.ζ

/-- **The private Cayley operation calling the supplied oracles**: the released operation of the
padded problem with every padded call replaced by its implementation from the supplied oracles. -/
def nd (N : ℕ) (z₀ : Cfg (VW q.b)) :
    NativeOp (LabW q.pub.params.k q.pub.params.l) (Fin q.pub.params.a ⊕ Fin (q.k + 1))
      (SZ4 (q.k + 1) q.b ⊕ GeneralSparseAccess.AW q.k q.b) (PY q.k q.b) Query :=
  substOp q.pub.nd (implP N q.s z₀)

/-- **The arithmetic** of the released operation on the base wires. -/
def ar : Arith (NB (LabW q.pub.params.k q.pub.params.l) (Fin q.pub.params.a ⊕ Fin (q.k + 1))
    (SZ4 (q.k + 1) q.b ⊕ GeneralSparseAccess.AW q.k q.b)) :=
  liftA q.pub.ar

/-- **The preparation of the general problem**: the direct source assembly in the zero case, the
native preparation with the operation calling the supplied oracles otherwise; the source circuits
on the low wires of the padded system register. -/
def prep {Zs : Type*} [Fintype Zs] [DecidableEq Zs] (N : ℕ) (z₀ : Cfg (VW q.b))
    (srcC : Bool → List (NInstr ((Unit ⊕ Fin q.k) ⊕ Zs) (PY q.k q.b) Query)) :
    List (NInstr (NW q.pub.params (Fin (q.k + 1)) Zs
      (SZ4 (q.k + 1) q.b ⊕ GeneralSparseAccess.AW q.k q.b) q.ar.bT q.ar.bP q.ar.A)
      (PY q.k q.b) Query) :=
  if BZeroCase q.pub then zprepC (srcRot q.T q.r₀ q.rb) (fun c => liftC (srcC c))
  else nprepC q.pub.params q.pub.UJg (q.nd N z₀) q.ar (fun c => liftC (srcC c))

theorem nd_public (N : ℕ) (z₀ : Cfg (VW q.b)) : (q.nd N z₀).Public :=
  substOp_public q.pub.nd_public (valid_implP N q.s z₀)

theorem ar_ok (hq : q.pub.OK) (N : ℕ) (z₀ : Cfg (VW q.b)) :
    ArithOK q.ar (Sum.inl (Sum.inr (q.nd N z₀).o)) (q.nd N z₀).dec q.ζ :=
  arithOK_liftA q.pub.ar _ _ _ (q.pub.ar_ok hq)

/-- The compute circuit has at most `28 (k + 1) + 2 + 6 implG k b` gates. -/
theorem nd_nGates (N : ℕ) (z₀ : Cfg (VW q.b)) :
    nGatesN (q.nd N z₀).V ≤ 28 * (q.k + 1) + 2 + implG q.k q.b * 6 := by
  have h := nGatesN_substOp_le q.pub.nd (implP N q.s z₀) (implG q.k q.b)
    (nGatesN_implP_le N q.s z₀)
  have hg : nGatesN q.pub.nd.V = 28 * (q.k + 1) + 2 :=
    GateBinaryODE.computeV4_nGates (q.k + 1) q.b q.pub.params.k q.pub.params.l
  have hc : nCallsN (fun _ => true) q.pub.nd.V = 6 := by
    have := GateBinaryODE.computeV4_nCalls (k := q.k + 1) (b := q.b) (kq := q.pub.params.k)
      (lq := q.pub.params.l) (fun _ => true)
    simp only [if_true] at this
    exact this
  unfold nd
  rw [hg, hc] at h
  exact h

/-- The compute circuit makes at most `6` supplied calls of each kind it calls. -/
theorem nd_nCalls (N : ℕ) (z₀ : Cfg (VW q.b)) (c : Query → Bool) :
    nCallsN c (q.nd N z₀).V ≤ 6 * ((if c Query.rowLocation then 1 else 0) +
      (if c Query.columnLocation then 1 else 0) + (if c Query.value then 1 else 0)) := by
  have h := nCallsN_substOp_le q.pub.nd (kindOK_implP (k := q.k) (b := q.b) N q.s z₀) c
  have hc := GateBinaryODE.computeV4_nCalls (k := q.k + 1) (b := q.b) (kq := q.pub.params.k)
    (lq := q.pub.params.l) c
  have hc' : nCallsN c q.pub.nd.V = 2 * (if c Query.rowLocation then 1 else 0) +
      2 * (if c Query.columnLocation then 1 else 0) + 2 * (if c Query.value then 1 else 0) := hc
  have h' : nCallsN c (q.nd N z₀).V ≤ 3 * nCallsN c q.pub.nd.V := h
  rw [hc'] at h'
  omega

end GPub

/-! ### The outcome -/

section Target

variable {a m r K k l f : ℕ} {S Zs Z Y J : Type*} {nP bT bP A : ℕ}
variable [Fintype S] [DecidableEq S] [Fintype Zs] [DecidableEq Zs] [Fintype Z] [DecidableEq Z]
  [Fintype Y] [DecidableEq Y]

/-- The guarantees against equal targets. -/
theorem wOutcome_target {prepN : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J)}
    {g β : ℝ} {hg : 1 ≤ g} {prim : J → Reg Y ℂ →L[ℂ] Reg Y ℂ} {x y : Reg S ℂ}
    (h : WOutcome prepN g β hg prim x) (e : x = y) : WOutcome prepN g β hg prim y := by
  subst e
  exact h

end Target

section Outcome

variable {X : Type*} {N : ℕ} {Zs : Type*} [Fintype Zs] [DecidableEq Zs]

set_option maxHeartbeats 1600000 in
/-- **The outcome of the general solver** (constant coefficients, every `T ≥ 0`): for public data
with `BPublicOK0 q.pub` and the public rescaling outside the zero case, sparse access of general size
with the decoder `c₀(X + iY)`, a public word `z₀` decoded as `0`, and every input as in
`SourceAccuracyODE.binary_ode_outcome_nonneg` stated for the matrix of `D` (the energy bounds and
the accretivity on `ℂ^N`) and for source circuits calling the supplied oracles on the `k`-qubit
system, the protocol `nprotocol (q.prep N z₀ srcC) g` has the guarantees `WOutcome … (ε / 250)`
for the supplied oracles, against the marker embedding of the solution of `x' = -A x + b`,
`A = padLift D x`. -/
theorem general_ode_outcome (q : GPub) (hq : BPublicOK0 q.pub)
    (hγ : ¬ BZeroCase q.pub →
      q.γ = GateODEBudget.gammaOf q.T q.etaH q.etaD q.g q.ε)
    (D : QData X N q.s q.k q.b) (z₀ : Cfg (VW q.b)) (hz₀ : D.val z₀ = 0)
    (hdec : ∀ z, D.val z = (q.c0 : ℂ) * gauss z)
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
    (hsrc : ∀ c, ApproxOn CleanX (nrun (D.prims (R := ℂ) x) (srcC c))
      (liftB (srcIdeal c (Jsrc c))) ζs)
    (hbud : 98304 * GateODEBudget.qOf q.pub.s q.T q.etaH q.etaD q.g q.ε * q.ζ + 2 * ζs ≤
      4 * q.pub.params.nu)
    (hx0 : ‖x0‖ = q.r₀) (hv : ‖v‖ = q.rb)
    (hpx : x0 ≠ 0 → Jsrc false (seedV (S := Fin q.k)) = unitDirection x0)
    (hpv : v ≠ 0 → Jsrc true (seedV (S := Fin q.k)) = unitDirection v)
    (hne : ODEConstantForcing.solution (-padLift D x) x0 v q.T ≠ 0)
    (hB : q.r₀ + q.T * q.rb ≤ q.g * ‖ODEConstantForcing.solution (-padLift D x) x0 v q.T‖) :
    WOutcome (q.prep N z₀ srcC) q.g (q.ε / 250) hq.g_ge (D.prims (R := ℂ) x)
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
  have hsrc' : ∀ c, ApproxOn CleanX (nrun (D.prims (R := ℂ) x) (liftC (srcC c)))
      (liftB (srcIdeal c (lowOp (Jsrc c)))) ζs := fun c =>
    approxOn_liftSrc (D.prims x) (srcC c) c (Jsrc c) hζs (hsrc c)
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
    have hp : q.prep N z₀ srcC = zprepC (srcRot q.T q.r₀ q.rb) (fun c => liftC (srcC c)) := by
      rw [GPub.prep, if_pos hz]
    rw [hp, ← hsol, ht]
    exact SourceAccuracyODE.native_zero_outcome (Z := SZ4 (q.k + 1) q.b ⊕ GeneralSparseAccess.AW q.k q.b)
      (Y := PY q.k q.b) (J := Query) q.pub.params.a q.pub.params.m q.pub.params.r q.pub.params.K
      q.pub.params.k q.pub.params.l q.pub.params.f q.ar.bT q.ar.bP q.ar.A q.pub.T q.pub.g q.pub.ε
      q.pub.r₀ q.pub.rb hq.T_nonneg hq.g_ge hq.ε_pos hq.ε_half hq.r₀_nonneg hq.rb_nonneg hq.B_pos
      (fun c => liftC (srcC c)) hsrcV' (D.prims (R := ℂ) x) (fun c => lowOp (Jsrc c))
      (markEmb q.k x0) (markEmb q.k v) ζs (D.prims_isUnitary x) hJ' hζs hsrc' (by linarith) hx0'
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
    have hN : NativeOK (D.prims (R := ℂ) x) (q.nd N z₀)
        (selOp (labFam (privFam q.pub.params Dp (Equiv.refl _) x q.pub.rho q.pub.γ) false)) :=
      nativeOK_substOp (D.prims x) (prims (R := ℂ) Dp (Equiv.refl _) x) (D.prims_isUnitary x)
        (prims_isUnitary Dp (Equiv.refl _) x) (implOK D z₀ hz₀ x) q.pub.nd q.pub.nd_public _
        (q.pub.nativeOK hP Dp (Equiv.refl _) hrange hdecP x)
    have hp : q.prep N z₀ srcC =
        nprepC q.pub.params q.pub.UJg (q.nd N z₀) q.ar (fun c => liftC (srcC c)) := by
      rw [GPub.prep, if_neg hz]
    have h := SourceAccuracyODE.native_ode_outcome q.pub.params (q.pub.params_ok hP) q.pub.UJg
      (hadUJ4_ok q.pub.σ q.pub.hσ) (q.nd N z₀) (q.nd_public N z₀) q.ar q.pub.ζ hP.ζ_pos.le
      (q.ar_ok hP N z₀) (fun c => liftC (srcC c)) hsrcV' (D.prims (R := ℂ) x)
      (privFam q.pub.params Dp (Equiv.refl _) x q.pub.rho q.pub.γ) (fun c => lowOp (Jsrc c))
      (hLift Dp (Equiv.refl _) x) (lLift Dp (Equiv.refl _) x) (markEmb q.k x0) (markEmb q.k v) ζs
      (D.prims_isUnitary x) hN hζs hsrc' hbud'
      (q.pub.instanceOK hP Dp (Equiv.refl _) hrange x hrH' hcH' hrD' hcD' hPSD'
        (fun c => lowOp (Jsrc c)) (markEmb q.k x0) (markEmb q.k v) hJ' hx0' hv' hpx' hpv' hne' hB')
    rw [hp]
    exact wOutcome_target h ((target_lift q.pub.params Dp (Equiv.refl _) x (markEmb q.k x0)
      (markEmb q.k v)).trans hsol)

end Outcome

end

end SparseHamiltonian.GeneralSparseODE
