import SourceAccuracyODE.Outcome
import GateEfficientODEBudget.Constant
import ZeroTimeGateODE.Binary
import GateEfficientRemarks.ODE.MinRegister

/-!
# Source circuits within `ν`: the constant-coefficient gate solver

The released constant-coefficient native gate solver (`GateNative.native_ode_solver`, from binary
data `GateBinaryODE.binary_ode_solver`, every `T ≥ 0` `ZeroTimeGateODE.binary_ode_solver_nonneg`)
certifies its protocol under the error budget `24 d ζ + 2 ζ_s ≤ ν`, `ν = ε/(10⁴ ḡ)`, for source
circuits within `ζ_s` of the controlled source preparations; with the released arithmetic accuracy
`98304 q* ζ ≤ ν/2` (`q* = qOf s T η_H η_D ḡ ε`, `d ≤ 4096 q*`) this asks each source circuit to be
within `ν/4`. Theorem `ode:thm:gates` asks of the source circuits only a combined implementation
error `ν` (`G_src(ν)`, defined in the paragraph before the theorem; for constant forcing
`G_src(ν) = G_{x₀}(cν) + G_b(cν) + …`, eq. `ode:eq:gate-constant-source`), and its proof absorbs the
source error into the vector error `9 ν B_m + ν B ≤ 19 ν B` (eq. `ode:eq:gate-vector-error`). Here
the same protocol is certified under `24 d ζ + 2 ζ_s ≤ 4 ν`, so source circuits within `ν` each
suffice, with every successful trial within `ε / 250` of the solution direction and the conditional
output within trace distance `ε / 250` (`WOutcome`):

* `native_ode_outcome` (native data, `T > 0`), `native_zero_outcome` (direct source assembly,
  `2 ζ_s ≤ 4 ν`) and `binary_ode_outcome` (binary data, `T > 0`): the hypotheses of
  `GateNative.native_ode_solver`, `ZeroTimeGateODE.native_zero_outcome` and
  `GateBinaryODE.binary_ode_solver` with the source budget multiplied by `4`;
* `binary_ode_outcome_nonneg` (every `T ≥ 0`, the released protocol `bprepC q srcC`): the input and
  source hypotheses of `ZeroTimeGateODE.binary_ode_solver_nonneg` with the public rescaling outside
  the zero case and the bit budget `98304 q* ζ + 2 ζ_s ≤ 4 ν`, as in the outcome of
  `GateRemarks.ODE.binary_ode_budget_bits_nonneg` (whose budget is `98304 q* ζ + 2 ζ_s ≤ ν`).

The protocols and their counts are the released ones; only the source budget and the per-trial
bound change.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.SourceAccuracyODE

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit GateNative
open GateCircuit.Sim (Wire)
open GateODE (OInstr OWire AW goodF Params Label wiring Oracles)
open ODEStateNormalization (unitDirection)
open scoped InnerProduct BigOperators

/-! ### The native solver -/

section Native

variable {S Zs Z Y J : Type*} [Fintype S] [DecidableEq S] [Fintype Zs] [DecidableEq Zs]
  [Fintype Z] [DecidableEq Z] [Fintype Y] [DecidableEq Y]

set_option maxHeartbeats 1600000 in
/-- **The released native constant-coefficient protocol with source circuits within `ν`**: for
every instance of the released native solver (`GateNative.native_ode_solver`: unitary primitive
oracles, `NativeOK`, the released instance conditions) whose source circuits are within `ζ_s` of
the controlled source preparations, under `24 d ζ + 2 ζ_s ≤ 4 ν`, the protocol has the guarantees
`WOutcome … (ε / 250)`. -/
theorem native_ode_outcome (p : Params) (hp : p.PublicOK)
    (UJg : List (Gate (Fin p.a ⊕ S))) (hUJg : ∀ g ∈ UJg, GateOK 3 g)
    (nd : NativeOp (LabW p.k p.l) (Fin p.a ⊕ S) Z Y J) (hnd : nd.Public)
    (ar : Arith (NB (LabW p.k p.l) (Fin p.a ⊕ S) Z)) (ζ : ℝ) (hζ : 0 ≤ ζ)
    (har : ArithOK ar (Sum.inl (Sum.inr nd.o)) nd.dec ζ)
    (srcC : Bool → List (NInstr ((Unit ⊕ S) ⊕ Zs) Y J)) (hsrcV : ∀ b, ∀ i ∈ srcC b, i.Valid)
    (prim : J → Reg Y ℂ →L[ℂ] Reg Y ℂ)
    (D : Label p.k p.l → Anc p.a (Reg S ℂ) →L[ℂ] Anc p.a (Reg S ℂ))
    (Jsrc : Bool → Reg S ℂ →L[ℂ] Reg S ℂ) (H L : Reg S ℂ →L[ℂ] Reg S ℂ) (x0 b : Reg S ℂ)
    (ζs : ℝ) (hprim : ∀ j, IsUnitary (prim j)) (hN : NativeOK prim nd (selOp (labFam D false)))
    (hζs : 0 ≤ ζs)
    (hsrc : ∀ c, ApproxOn CleanX (nrun prim (srcC c)) (liftB (srcIdeal c (Jsrc c))) ζs)
    (hbudget : 24 * (p.d : ℝ) * ζ + 2 * ζs ≤ 4 * p.nu)
    (hI : p.InstanceOK (seedV (S := S))
      (⟨UJop (R := ℂ) UJg, D, Jsrc⟩ : Oracles p.a (Label p.k p.l) (Reg S ℂ)) H L x0 b) :
    WOutcome (nprepC p UJg nd ar srcC) p.g (p.ε / 250) hp.g_ge prim (p.target H L x0 b) := by
  have hτ := hp.tau_pos.le
  have hν := hp.nu_pos
  obtain ⟨cP, -, cS, -, -⟩ := p.prepC_counts hτ hν
  have hvalid := p.prepC_valid hτ hν hp.r₀_nonneg hp.rb_nonneg hp.T_pos.le hp.B_pos
  have hsec := osec_prepC p
  have hnoseed := noseed_prepC p hτ hν
  have hprepV : ∀ i ∈ nprepC p UJg nd ar srcC, i.Valid := by
    intro i hi
    simp only [nprepC, List.mem_flatMap] at hi
    obtain ⟨o, ho, hi⟩ := hi
    exact omacro_valid labSel UJg hUJg nd hnd ar har.elem har.classical (srcMacro p srcC)
      (srcMacro_valid p srcC hsrcV) o (hsec o ho) (hvalid o ho) i hi
  have hnP : Fintype.card (AW p.a p.m p.r p.K p.k p.l p.f) +
      Fintype.card (XW Z ar.bT ar.bP ar.A) + Fintype.card Zs + Fintype.card S ≤
      nPool p S Zs Z ar.bT ar.bP ar.A + 1 := by
    have e : Fintype.card p.W = Fintype.card (AW p.a p.m p.r p.K p.k p.l p.f) := rfl
    unfold nPool
    omega
  let σ : Oracles p.a (Label p.k p.l) (Reg S ℂ) := ⟨UJop (R := ℂ) UJg, D, Jsrc⟩
  have hU := p.unitaries_of (norm_seedV (S := S)) hI
  have hJ : ∀ c, IsUnitary (Jsrc c) := hU.src
  have hDu : ∀ w, IsUnitary (labFam D false w) := fun w => hU.priv _
  have hDadj : ∀ w, labFam D true w = (labFam D false w)† := fun _ => rfl
  have hP : Pres2 (ZeroOn reflWire) (nrun prim (nprepC p UJg nd ar srcC)) := by
    apply pres2_nrun_zeroOn
    intro i hi
    simp only [nprepC, List.mem_flatMap] at hi
    obtain ⟨o, _, hi⟩ := hi
    exact omacro_not_touches labSel UJg nd ar (srcMacro p srcC)
      (srcMacro_not_touches p srcC) o i hi
  have hA := oprep_approx prim hprim labSel UJg hUJg nd hnd ar hζ har (labFam D) hDu hDadj hN
    (OInstr.eval (wiring (seedV (S := S))) σ) (fun _ => rfl)
    (fun adj => ode_eval_uj (seedV (S := S)) σ UJg rfl labSel (labFam D) adj)
    (fun adj => ode_eval_priv (seedV (S := S)) σ UJg adj)
    (srcMacro p srcC) hζs
    (fun c adj => srcMacro_approx p prim hprim srcC hsrcV Jsrc hJ hζs hsrc (seedV (S := S)) D
      (UJop (R := ℂ) UJg) c adj)
    (srcMacro_valid p srcC hsrcV) p.prepC hsec hnoseed hvalid
    (fun i hi => OInstr.eval_isUnitary (wiring (seedV (S := S))) σ hU.uj hU.priv hU.src hU.seed i
      (hvalid i hi))
  rw [prodOps_oeval, nSrcAny_eq, cP, cS false, cS true] at hA
  -- the released certificate
  have hT := hp.T_pos.le
  have hS := hI.select
  have hC := p.prep_certificate hp (seedV (S := S)) norm_seedV σ H L x0 b hI
  have hdec := p.decoded_eq hp (seedV (S := S)) σ x0 b hI.init_norm hI.forcing_norm
  have hmass := p.mass_zsrc x0 b hT hI.init_norm hI.forcing_norm
  have hNorm : ‖p.target H L x0 b‖ ≤ p.B := by
    rw [← hmass]
    exact p.solution_le_mass hT H L hS.selfH hS.selfL hI.psd x0 b hI.init_norm hI.forcing_norm
  have h := hC.vector_error
  rw [hmass, ← hdec] at h
  have hδ : ((6 * p.d : ℕ) : ℝ) * (4 * ζ) + ((1 + 1 : ℕ) : ℝ) * ζs ≤ 4 * p.nu := by
    have e2 : ((6 * p.d : ℕ) : ℝ) = 6 * (p.d : ℝ) := by rw [Nat.cast_mul, Nat.cast_ofNat]
    have e3 : ((1 + 1 : ℕ) : ℝ) = 2 := by norm_num
    rw [e2, e3]
    linarith only [hbudget]
  have hA' := hA.mono hδ
  have hne := hI.target_ne
  have hbud := hI.budget
  generalize GateODE.run (wiring (seedV (S := S))) σ p.prepC = Urel at h hA'
  generalize p.target H L x0 b = x at h hNorm hne hbud ⊢
  have hB : 0 < p.B := (norm_pos_iff.mpr hne).trans_le hNorm
  have hg0 : 0 < p.g := by linarith [hp.g_ge]
  have hνg : p.nu * p.g = p.ε / 10000 := precision_mul p.g p.ε hg0
  have hρ : (3 * (4 * p.nu) + 6 * p.nu) * p.g ≤ 9 * p.ε / 5000 := by
    have e : (3 * (4 * p.nu) + 6 * p.nu) * p.g = 18 * (p.nu * p.g) := by ring
    rw [e, hνg]
    linarith
  have hw := woutcome_lifted hnP (nprepC p UJg nd ar srcC) prim hprim hprepV hP Urel hA' x x p.B
    p.g p.nu (9 * p.ε / 5000) 0 hne hne hp.g_ge hB hbud h (by linarith [hp.nu_pos]) hρ
    (by linarith [hp.ε_half]) (by simp)
  exact hw.mono (by linarith [hp.ε_pos])

end Native

/-! ### The zero case -/

section Zero

variable {S Zs Z Y J : Type*} [Fintype S] [DecidableEq S] [Fintype Zs] [DecidableEq Zs]
  [Fintype Z] [DecidableEq Z] [Fintype Y] [DecidableEq Y]

open ZeroTimeGateODE (ZNW zPool zprepC srcRot srcRot_unitary zprepC_valid zprepC_approx
  srcRot_decoded zrelC zprepC_pres)

/-- **The zero case with source circuits within `ν`** (direct source assembly of
`ZeroTimeGateODE.native_zero_outcome`): under `2 ζ_s ≤ 4 ν` the protocol has the guarantees
`WOutcome … (ε / 250)` against `x₀ + T b`. -/
theorem native_zero_outcome (a m r K k l f bT bP A : ℕ) (T g ε r₀ rb : ℝ) (hT : 0 ≤ T)
    (hg : 1 ≤ g) (hε : 0 < ε) (hεHalf : ε ≤ 1 / 2) (hr₀ : 0 ≤ r₀) (hrb : 0 ≤ rb)
    (hB : 0 < r₀ + T * rb) (srcC : Bool → List (NInstr ((Unit ⊕ S) ⊕ Zs) Y J))
    (hsrcV : ∀ c, ∀ i ∈ srcC c, i.Valid) (prim : J → Reg Y ℂ →L[ℂ] Reg Y ℂ)
    (Jsrc : Bool → Reg S ℂ →L[ℂ] Reg S ℂ) (x0 b : Reg S ℂ) (ζs : ℝ)
    (hprim : ∀ j, IsUnitary (prim j)) (hJ : ∀ c, IsUnitary (Jsrc c)) (hζs : 0 ≤ ζs)
    (hsrc : ∀ c, ApproxOn CleanX (nrun prim (srcC c)) (liftB (srcIdeal c (Jsrc c))) ζs)
    (hbudget : 2 * ζs ≤ 4 * ImprovedODEQueryBudget.precision g ε)
    (h₀ : ‖x0‖ = r₀) (hb : ‖b‖ = rb)
    (hJ0 : x0 ≠ 0 → Jsrc false seedV = unitDirection x0)
    (hJb : b ≠ 0 → Jsrc true seedV = unitDirection b)
    (hne : x0 + T • b ≠ 0) (hbud : r₀ + T * rb ≤ g * ‖x0 + T • b‖) :
    WOutcome (zprepC (srcRot T r₀ rb) srcC :
      List (NInstr (ZNW a m r K k l f S Zs Z bT bP A) Y J)) g (ε / 250) hg prim (x0 + T • b) := by
  have hu := srcRot_unitary T r₀ rb hT hr₀ hrb hB
  have hprepV := zprepC_valid (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f)
    (nP := zPool a m r K k l f S Zs Z bT bP A) (Z := Z) (bT := bT) (bP := bP) (A := A)
    (srcRot T r₀ rb) hu srcC hsrcV
  let σ : Oracles a (Label k l) (Reg S ℂ) := ⟨1, fun _ => 1, Jsrc⟩
  have hA := zprepC_approx (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f)
    (nP := zPool a m r K k l f S Zs Z bT bP A) (Z := Z) (bT := bT) (bP := bP) (A := A) prim hprim
    (srcRot T r₀ rb) hu srcC hsrcV seedV σ hJ hζs hsrc
  have hrel := srcRot_decoded (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f)
    T r₀ rb hT hr₀ hrb hB seedV σ x0 b h₀ hb hJ0 hJb
  generalize GateODE.run (wiring (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f)
    seedV) σ (zrelC (srcRot T r₀ rb)) = Urel at hA hrel
  have hg0 : 0 < g := by linarith
  have hνg := precision_mul g ε hg0
  have hρ : 2 * ζs * g ≤ ε / 2500 := by
    have h1 := mul_le_mul_of_nonneg_right hbudget hg0.le
    rw [show 4 * ImprovedODEQueryBudget.precision g ε * g =
      4 * (ImprovedODEQueryBudget.precision g ε * g) by ring, hνg] at h1
    linarith
  have hw := woutcome_direct (Nat.le_succ _) (zprepC (srcRot T r₀ rb) srcC :
    List (NInstr (ZNW a m r K k l f S Zs Z bT bP A) Y J)) prim hprim hprepV
    (zprepC_pres _ srcC prim) Urel hA (x0 + T • b) (x0 + T • b) (r₀ + T * rb) g (ε / 2500) 0 hne
    hne hg hB hbud hrel (by linarith) hρ (by linarith) (by simp)
  exact hw.mono (by linarith)

end Zero

/-! ### Binary data -/

section Binary

variable {X n : Type*} [Fintype n] [DecidableEq n] {Zs : Type*} [Fintype Zs] [DecidableEq Zs]

open GateBinary
open GateBinaryODE (Pub mLift privFam hLift lLift target_lift hadUJ4_ok)
open ZeroTimeGateODE (BPublicOK0 BZeroCase bprepC binary_target_zero bpublicOK_of)
open NativeSparseBlockEncoding (Data Query)

set_option maxHeartbeats 1600000 in
/-- **Binary data, `T > 0`, source circuits within `ν`**: for the released public data `q.OK`,
every input with the released energy and accretivity promises and the released source hypotheses,
circuits within `ζ_s` with `24 d ζ + 2 ζ_s ≤ 4 ν` (the hypotheses of
`GateBinaryODE.binary_ode_solver`, whose budget is `24 d ζ + 2 ζ_s ≤ ν`), the protocol
`nprotocol (q.prep srcC) g` has the guarantees `WOutcome … (ε / 250)` against the solution `x(T)`
of `x' = -M̂ x + b`. -/
theorem binary_ode_outcome (q : Pub) (hq : q.OK)
    (D : Data X n (Cfg (VW q.b)) q.s) (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (hdec : ∀ e z, D.decode e z = (q.c0 : ℂ) * gauss z)
    (srcC : Bool → List (NInstr ((Unit ⊕ Fin q.kx) ⊕ Zs) (PY q.kx q.b) Query))
    (hsrcV : ∀ c, ∀ i ∈ srcC c, i.Valid) (x : X)
    (hrH : ∀ i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ q.etaH ^ 2)
    (hcH : ∀ j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ q.etaH ^ 2)
    (hrD : ∀ i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ q.etaD ^ 2)
    (hcD : ∀ j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ q.etaD ^ 2)
    (hPSD : ∀ w : EuclideanSpace ℂ n, 0 ≤ (inner ℂ w (SparseStateOverlap.matrixOperator
      (ODEMatrixEnergy.dissipativePart (D.matrix x)) w)).re)
    (Jsrc : Bool → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ) (x0 v : Reg (Fin q.kx) ℂ) (ζs : ℝ)
    (hJ : ∀ c, IsUnitary (Jsrc c)) (hζs : 0 ≤ ζs)
    (hsrc : ∀ c, ApproxOn CleanX (nrun (prims (R := ℂ) D en x) (srcC c))
      (liftB (srcIdeal c (Jsrc c))) ζs)
    (hbud : 24 * (q.params.d : ℝ) * q.ζ + 2 * ζs ≤ 4 * q.params.nu)
    (hx0 : ‖x0‖ = q.r₀) (hv : ‖v‖ = q.rb)
    (hpx : x0 ≠ 0 → Jsrc false (seedV (S := Fin q.kx)) = unitDirection x0)
    (hpv : v ≠ 0 → Jsrc true (seedV (S := Fin q.kx)) = unitDirection v)
    (hne : ODEConstantForcing.solution (-mLift D en x) x0 v q.T ≠ 0)
    (hB : q.r₀ + q.T * q.rb ≤ q.g * ‖ODEConstantForcing.solution (-mLift D en x) x0 v q.T‖) :
    WOutcome (q.prep srcC) q.g (q.ε / 250) hq.g_ge (prims (R := ℂ) D en x)
      (ODEConstantForcing.solution (-mLift D en x) x0 v q.T) := by
  have h := native_ode_outcome q.params (q.params_ok hq) q.UJg (hadUJ4_ok q.σ q.hσ)
    q.nd q.nd_public q.ar q.ζ hq.ζ_pos.le (q.ar_ok hq) srcC hsrcV (prims (R := ℂ) D en x)
    (privFam q.params D en x q.rho q.γ) Jsrc (hLift D en x) (lLift D en x) x0 v ζs
    (prims_isUnitary D en x) (q.nativeOK hq D en hrange hdec x) hζs hsrc hbud
    (q.instanceOK hq D en hrange x hrH hcH hrD hcD hPSD Jsrc x0 v hJ hx0 hv hpx hpv hne hB)
  rw [target_lift] at h
  exact h

set_option maxHeartbeats 1600000 in
/-- **Binary data, every `T ≥ 0`, source circuits within `ν`**: for binary public data with
`BPublicOK0 q`, the public rescaling outside the zero case, and the released input and source
hypotheses with circuits within `ζ_s` and the bit budget `98304 q* ζ + 2 ζ_s ≤ 4 ν` (as in the
outcome of `GateRemarks.ODE.binary_ode_budget_bits_nonneg`, whose budget is
`98304 q* ζ + 2 ζ_s ≤ ν`), the protocol `nprotocol (bprepC q srcC) g` of
`ZeroTimeGateODE.binary_ode_solver_nonneg` has the guarantees `WOutcome … (ε / 250)` against
`x(T)`. -/
theorem binary_ode_outcome_nonneg (q : Pub) (hq : BPublicOK0 q)
    (hγ : ¬ BZeroCase q → q.γ = GateODEBudget.gammaOf q.T q.etaH q.etaD q.g q.ε)
    (D : Data X n (Cfg (VW q.b)) q.s) (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (hdec : ∀ e z, D.decode e z = (q.c0 : ℂ) * gauss z)
    (srcC : Bool → List (NInstr ((Unit ⊕ Fin q.kx) ⊕ Zs) (PY q.kx q.b) Query))
    (hsrcV : ∀ c, ∀ i ∈ srcC c, i.Valid) (x : X)
    (hrH : ∀ i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ q.etaH ^ 2)
    (hcH : ∀ j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ q.etaH ^ 2)
    (hrD : ∀ i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ q.etaD ^ 2)
    (hcD : ∀ j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ q.etaD ^ 2)
    (hPSD : ∀ w : EuclideanSpace ℂ n, 0 ≤ (inner ℂ w (SparseStateOverlap.matrixOperator
      (ODEMatrixEnergy.dissipativePart (D.matrix x)) w)).re)
    (Jsrc : Bool → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ) (x0 v : Reg (Fin q.kx) ℂ) (ζs : ℝ)
    (hJ : ∀ c, IsUnitary (Jsrc c)) (hζs : 0 ≤ ζs)
    (hsrc : ∀ c, ApproxOn CleanX (nrun (prims (R := ℂ) D en x) (srcC c))
      (liftB (srcIdeal c (Jsrc c))) ζs)
    (hbud : 98304 * GateODEBudget.qOf q.s q.T q.etaH q.etaD q.g q.ε * q.ζ + 2 * ζs ≤
      4 * q.params.nu)
    (hx0 : ‖x0‖ = q.r₀) (hv : ‖v‖ = q.rb)
    (hpx : x0 ≠ 0 → Jsrc false (seedV (S := Fin q.kx)) = unitDirection x0)
    (hpv : v ≠ 0 → Jsrc true (seedV (S := Fin q.kx)) = unitDirection v)
    (hne : ODEConstantForcing.solution (-mLift D en x) x0 v q.T ≠ 0)
    (hB : q.r₀ + q.T * q.rb ≤ q.g * ‖ODEConstantForcing.solution (-mLift D en x) x0 v q.T‖) :
    WOutcome (bprepC q srcC) q.g (q.ε / 250) hq.g_ge (prims (R := ℂ) D en x)
      (ODEConstantForcing.solution (-mLift D en x) x0 v q.T) := by
  by_cases hz : BZeroCase q
  · have ht := binary_target_zero q hq hz D en x hrH hrD x0 v
    rw [ht] at hne hB ⊢
    have hε1 : q.ε ≤ 1 := hq.ε_half.trans (by norm_num)
    have hQ1 : 1 ≤ GateODEBudget.qOf q.s q.T q.etaH q.etaD q.g q.ε :=
      GateRemarks.ODE.one_le_qOf hq.T_nonneg hq.etaH_nonneg hq.etaD_nonneg hq.g_ge hq.ε_pos hε1
    have h0 : 0 ≤ 98304 * GateODEBudget.qOf q.s q.T q.etaH q.etaD q.g q.ε * q.ζ :=
      mul_nonneg (mul_nonneg (by norm_num) (by linarith)) hq.ζ_pos.le
    have hnu : q.params.nu = ImprovedODEQueryBudget.precision q.g q.ε := rfl
    rw [hnu] at hbud
    rw [bprepC, if_pos hz]
    exact native_zero_outcome (Z := GateBinaryODE.SZ4 q.kx q.b) (Y := PY q.kx q.b) (J := Query)
      q.params.a q.params.m q.params.r q.params.K q.params.k q.params.l q.params.f q.ar.bT
      q.ar.bP q.ar.A q.T q.g q.ε q.r₀ q.rb hq.T_nonneg hq.g_ge hq.ε_pos hq.ε_half hq.r₀_nonneg
      hq.rb_nonneg hq.B_pos srcC hsrcV (prims (R := ℂ) D en x) Jsrc x0 v ζs
      (prims_isUnitary D en x) hJ hζs hsrc (by linarith) hx0 hv hpx hpv hne hB
  · have hP := bpublicOK_of hq hz
    obtain ⟨-, hd, -, -, -, -, -⟩ := GateODEBudget.binary_ode_sizes q hP (hγ hz)
    have hbud' : 24 * (q.params.d : ℝ) * q.ζ + 2 * ζs ≤ 4 * q.params.nu := by
      have := mul_le_mul_of_nonneg_right hd hP.ζ_pos.le
      linarith
    rw [bprepC, if_neg hz]
    exact binary_ode_outcome q hP D en hrange hdec srcC hsrcV x hrH hcH hrD hcD hPSD Jsrc
      x0 v ζs hJ hζs hsrc hbud' hx0 hv hpx hpv hne hB

end Binary

end

end SparseHamiltonian.SourceAccuracyODE
