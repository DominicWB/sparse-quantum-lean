import GateEfficientBinaryODE.Clock
import GateEfficientNative.Corollaries

/-!
# Theorem `ode:thm:gates` from binary sparse data, constant coefficients

The native solver `native_ode_solver` of `GateEfficientNative` takes as hypotheses the gates of
`U_J`, a native private operation with its compute circuit, decoder and arithmetic (`NativeOK`,
`ArithOK`), and the clock promises of the instance (`InstanceOK.select`). For binary sparse data
(`k`-qubit indices, `s = 2^σ` slots on the lowest `σ` index bits, entries `c₀ (X + i Y)` with
`b`-bit two's complement components) all of them are constructed here from the public data
`q : Pub`, and the norm, self-adjointness and accretivity conditions on the lifted parts are
derived from energy bounds and the accretivity of the input; the source circuits (with their
accuracy `ζs` and the budget `24 d ζ + 2 ζs ≤ ν`) and the source and target conditions of the
instance remain hypotheses.

* `Pub.params`: the released public parameters, with `a = k + 3` ancillas, `Q = width(4s, γ)`,
  `q̄ = moment γ`, `λ_H = √(4s) η_H / γ` and `λ_D = √(4s) η_D / γ`; they satisfy the public
  conditions (`Pub.params_ok`).
* `U_J` is `hadUJ4` (`σ + 3` Hadamard gates), the private operation is `odeOp` with the compute
  circuit `computeV4`, and the arithmetic is `odeAr` with the layout `layOf` and `F = fOf` bits of
  the LCHS step: the rounded step factor is within `ζ/4` of one (`rhoL_close`), so the CORDIC
  accuracy `ζ/2` gives `ArithOK` with accuracy `ζ` (`Pub.ar_ok`).
* The label-selected private operation is the lifted four-sector Cayley action `privFam` at the
  LCHS node of the label and the rescaling `γ dur / T` (`Pub.nativeOK`, from `nativeOK4` and
  `decOK`).
* Its clock promises hold for every label with `R₁` the lifted four-sector resolvent at one and
  `b = endpoint (γ dur / T)` (`clock4`), and the lifted Hamiltonian and dissipative parts `hLift`,
  `lLift` are self-adjoint with norms at most `λ_H`, `λ_D` (`norm_matrixOperator_le`): this is
  `Pub.selectHyp`. The lifted dissipative part is accretive when the dissipative part is
  (`re_inner_qlift_nonneg`, used in `Pub.instanceOK`).

`binary_ode_counts`: the native preparation from binary data depends only on the public data and
the source circuits; its trials are valid and its gate, call and qubit counts are explicit.
`binary_ode_solver`: in addition, for every input whose Hamiltonian and dissipative parts have row
and column energies at most `η_H²`, `η_D²`, with accretive dissipative part, the protocol succeeds
with probability at least `2/3` and its conditional output is within trace distance `ε` of the
normalised solution of `x' = -M̂ x + b`, given source circuits within `ζs` of the controlled source
interfaces and `24 d ζ + 2 ζs ≤ ν`. `binary_ode_gate_count` states the explicit worst-case gate
count. The released parameters `q.params`, hence `d` and `ν`, do not depend on the arithmetic
accuracy `ζ`, so the budget can be met by choosing `ζ` last.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateBinaryODE

noncomputable section
open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
open SparseHamiltonian.GateBinary SparseHamiltonian.OracleCircuit CayleyClockInterface
open SparseHamiltonian.GateCircuit.Sim (iota0)
open SparseHamiltonian.GateODE (Params Label Oracles ClockPromise)
open NativeSparseBlockEncoding (Data Query)
open scoped InnerProduct

/-! ### The public data -/

/-- **The public data** of the dissipative solver from binary sparse data. -/
structure Pub where
  /-- The system qubits. -/
  kx : ℕ
  /-- The slot bits: `s = 2^σ` slots. -/
  σ : ℕ
  /-- The slot bits fit in the system register. -/
  hσ : σ ≤ kx
  /-- The stored bits of each component. -/
  b : ℕ
  /-- The decoder scale `c₀` of the stored entries. -/
  c0 : ℝ
  /-- The row and column energy bound of the Hamiltonian part. -/
  etaH : ℝ
  /-- The row and column energy bound of the dissipative part. -/
  etaD : ℝ
  /-- The Cayley rescaling. -/
  γ : ℝ
  /-- The time. -/
  T : ℝ
  /-- The public bound `g ≥ (r₀ + T rb) / ‖x(T)‖`. -/
  g : ℝ
  /-- The accuracy. -/
  ε : ℝ
  /-- The norm of the initial state. -/
  r₀ : ℝ
  /-- The norm of the forcing. -/
  rb : ℝ
  /-- The arithmetic accuracy. -/
  ζ : ℝ

namespace Pub

variable (q : Pub)

/-- The number of slots. -/
abbrev s : ℕ := 2 ^ q.σ

/-- The public conditions. -/
structure OK : Prop where
  b_pos : 0 < q.b
  c0_pos : 0 < q.c0
  etaH_nonneg : 0 ≤ q.etaH
  etaD_nonneg : 0 ≤ q.etaD
  eta_pos : 0 < q.etaH + q.etaD
  γ_pos : 0 < q.γ
  γ_le : q.γ ≤ 1
  T_pos : 0 < q.T
  g_ge : 1 ≤ q.g
  ε_pos : 0 < q.ε
  ε_half : q.ε ≤ 1 / 2
  r₀_nonneg : 0 ≤ q.r₀
  rb_nonneg : 0 ≤ q.rb
  B_pos : 0 < q.r₀ + q.T * q.rb
  ζ_pos : 0 < q.ζ
  ζ_le : q.ζ ≤ 1

/-- **The released public parameters**: `a = k + 3` ancillas, `Q = width(4s, γ)`,
`q̄ = moment γ`, `λ_H = √(4s) η_H / γ` and `λ_D = √(4s) η_D / γ`. -/
def params : Params where
  a := q.kx + 3
  Q := width (4 * (q.s : ℝ)) q.γ
  qbar := moment q.γ
  T := q.T
  lamH := Real.sqrt (4 * (q.s : ℝ)) * q.etaH / q.γ
  lamD := Real.sqrt (4 * (q.s : ℝ)) * q.etaD / q.γ
  g := q.g
  ε := q.ε
  r₀ := q.r₀
  rb := q.rb

/-- The scale `ρ = η_H + R η_D` of the four sectors. -/
def rho : ℝ := q.etaH + ImprovedODEQueryBudget.radius q.g q.ε * q.etaD

/-- The fractional bits of the LCHS step. -/
def F : ℕ := fOf q.params q.ζ

/-- The integer layout of the arithmetic. -/
def lay : Lay := layOf q.params q.b q.F

/-- The decoder scale `κ = γ √(4s) c₀ / (2^(k_T + F + 10) ρ)`, `k_T` the node bits of
`q.params`. -/
def kap : ℝ := kapOf q.params q.s q.c0 q.rho q.γ q.F

/-- The gates of `U_J`: `σ + 3` Hadamard gates. -/
def UJg : List (Gate (Fin q.params.a ⊕ Fin q.kx)) := hadUJ4 q.kx q.σ q.hσ

/-- **The native private operation**: the compute circuit `computeV4`, the orientation wire and
the decoder with scale `κ` and step factor `ρ_L`. -/
def nd : NativeOp (LabW q.params.k q.params.l) (Fin q.params.a ⊕ Fin q.kx) (SZ4 q.kx q.b)
    (PY q.kx q.b) Query :=
  odeOp q.kx q.lay q.kap (rhoL q.params q.F)

/-- **The arithmetic** of the native private operation, with CORDIC accuracy `ζ/2`. -/
def ar : Arith (NB (LabW q.params.k q.params.l) (Fin q.params.a ⊕ Fin q.kx) (SZ4 q.kx q.b)) :=
  odeAr q.kx q.lay q.kap (q.ζ / 2)

/-- **One native preparation** of the solver from binary data, for the source circuits `srcC`. -/
def prep {Zs : Type*} [Fintype Zs] [DecidableEq Zs]
    (srcC : Bool → List (NInstr ((Unit ⊕ Fin q.kx) ⊕ Zs) (PY q.kx q.b) Query)) :
    List (NInstr (NW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A)
      (PY q.kx q.b) Query) :=
  nprepC q.params q.UJg q.nd q.ar srcC

theorem sqrt4s_pos : 0 < Real.sqrt (4 * (q.s : ℝ)) := by
  apply Real.sqrt_pos.mpr
  have : (1 : ℝ) ≤ (q.s : ℝ) := by exact_mod_cast Nat.one_le_two_pow
  linarith

theorem rho_pos (hq : q.OK) : 0 < q.rho := by
  have hR : 0 < ImprovedODEQueryBudget.radius q.g q.ε :=
    GateODE.AnalyticLCHS.radius_pos hq.g_ge hq.ε_pos (hq.ε_half.trans (by norm_num))
  unfold rho
  rcases lt_or_eq_of_le hq.etaH_nonneg with h | h
  · have := mul_nonneg hR.le hq.etaD_nonneg
    linarith
  · have hD : 0 < q.etaD := by
      have := hq.eta_pos
      linarith
    have := mul_pos hR hD
    linarith

theorem lam_sum :
    q.params.lamH + q.params.R * q.params.lamD = Real.sqrt (4 * (q.s : ℝ)) * q.rho / q.γ := by
  show Real.sqrt (4 * (q.s : ℝ)) * q.etaH / q.γ +
    ImprovedODEQueryBudget.radius q.g q.ε * (Real.sqrt (4 * (q.s : ℝ)) * q.etaD / q.γ) = _
  unfold rho
  ring

/-- The common simulation time is `τ = T √(4s) ρ / γ`. -/
theorem tau_eq : q.params.tau = q.params.T * (Real.sqrt (4 * (q.s : ℝ)) * q.rho) / q.γ := by
  show q.params.T * (q.params.lamH + q.params.R * q.params.lamD) = _
  rw [q.lam_sum]
  ring

/-- **The public conditions** of the released solver hold. -/
theorem params_ok (hq : q.OK) : q.params.PublicOK where
  T_pos := hq.T_pos
  g_ge := hq.g_ge
  ε_pos := hq.ε_pos
  ε_half := hq.ε_half
  lamH_nonneg := div_nonneg (mul_nonneg (Real.sqrt_nonneg _) hq.etaH_nonneg) hq.γ_pos.le
  lamD_nonneg := div_nonneg (mul_nonneg (Real.sqrt_nonneg _) hq.etaD_nonneg) hq.γ_pos.le
  energy_pos := by
    rw [q.lam_sum]
    exact div_pos (mul_pos q.sqrt4s_pos (q.rho_pos hq)) hq.γ_pos
  Q_ge := width_ge_one _ _
  qbar_nonneg := moment_nonneg _
  qbar_le := moment_le_width _ _ hq.γ_pos.le hq.γ_le
  r₀_nonneg := hq.r₀_nonneg
  rb_nonneg := hq.rb_nonneg
  B_pos := hq.B_pos

theorem TD_nonneg (hq : q.OK) : 0 ≤ q.params.T * q.params.lamD :=
  mul_nonneg hq.T_pos.le (q.params_ok hq).lamD_nonneg

theorem step_pos (hq : q.OK) : 0 < hStep q.params :=
  hStep_pos q.params hq.g_ge hq.ε_pos (hq.ε_half.trans (by norm_num)) (q.TD_nonneg hq)

theorem lay_ok (hq : q.OK) : q.lay.OK :=
  layOf_ok q.params q.b q.F hq.b_pos hq.g_ge hq.ε_pos (hq.ε_half.trans (by norm_num))
    (q.TD_nonneg hq)

theorem kap_pos (hq : q.OK) : 0 < q.kap := by
  have h1 := q.sqrt4s_pos
  have h2 := q.rho_pos hq
  have h3 := hq.c0_pos
  have h4 := hq.γ_pos
  unfold kap kapOf
  positivity

theorem nd_public : q.nd.Public := odeOp_public _ _ _ _

/-- **The arithmetic hypothesis** with accuracy `ζ`. -/
theorem ar_ok (hq : q.OK) : ArithOK q.ar (Sum.inl (Sum.inr q.nd.o)) q.nd.dec q.ζ := by
  have hr : |rhoL q.params q.F - 1| ≤ q.ζ / 4 :=
    rhoL_close q.params q.ζ hq.ζ_pos hq.ζ_le (q.step_pos hq)
  have h1 := hq.ζ_pos
  have h2 := hq.ζ_le
  exact odeAr_ok q.kx q.lay (q.lay_ok hq) q.kap (rhoL q.params q.F) (q.ζ / 2) q.ζ (q.kap_pos hq)
    (by linarith) (by linarith) (by linarith) (by linarith)

variable {X n : Type*} [Fintype n] [DecidableEq n]

/-- **The native identity** of the label-selected private operation. -/
theorem nativeOK (hq : q.OK) (D : Data X n (Cfg (VW q.b)) q.s) (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (hdec : ∀ e z, D.decode e z = (q.c0 : ℂ) * gauss z) (x : X) :
    NativeOK (prims (R := ℂ) D en x) q.nd
      (selOp (labFam (privFam q.params D en x q.rho q.γ) false)) := by
  obtain ⟨k0, hk0⟩ : ∃ m, D.slot m = zIdx en := by
    refine (hrange _).2 ⟨fun _ => false, ?_⟩
    unfold zIdx
    congr 1
    funext i
    simp [lowWord]
  have hHn : hRound q.params q.F ≠ 0 := by
    have h1 : 2 / q.ζ ≤ (hRound q.params q.F : ℝ) :=
      hRound_ge q.params q.ζ hq.ζ_pos hq.ζ_le (q.step_pos hq)
    have h2 : (0 : ℝ) < hRound q.params q.F :=
      lt_of_lt_of_le (div_pos two_pos hq.ζ_pos) h1
    have h3 : 0 < hRound q.params q.F := by exact_mod_cast h2
    exact h3.ne'
  have hd := decOK q.params hq.T_pos.ne' D en k0 x q.c0 hq.c0_pos.ne' hdec q.rho q.γ
    (q.rho_pos hq).ne' q.F hHn
  exact nativeOK4 (kq := q.params.k) (lq := q.params.l) D en k0 hk0 x
    (fun z => q.params.nodeW z.2) (fun z => q.γ * q.params.dur z.1 / q.params.T) q.rho q.nd rfl
    rfl q.nd_public hd

/-- `√(2s) η ≤ √(4s) η / γ`. -/
theorem sqrt_le_lam (hq : q.OK) (η : ℝ) (hη : 0 ≤ η) :
    Real.sqrt (2 * (q.s : ℝ)) * η ≤ Real.sqrt (4 * (q.s : ℝ)) * η / q.γ := by
  have h1 : Real.sqrt (2 * (q.s : ℝ)) ≤ Real.sqrt (4 * (q.s : ℝ)) :=
    Real.sqrt_le_sqrt (by have : (0 : ℝ) ≤ q.s := Nat.cast_nonneg _; linarith)
  rw [le_div_iff₀ hq.γ_pos]
  have h2 : Real.sqrt (2 * (q.s : ℝ)) * η ≤ Real.sqrt (4 * (q.s : ℝ)) * η :=
    mul_le_mul_of_nonneg_right h1 hη
  have h4 : Real.sqrt (2 * (q.s : ℝ)) * η * q.γ ≤ Real.sqrt (2 * (q.s : ℝ)) * η :=
    mul_le_of_le_one_right (mul_nonneg (Real.sqrt_nonneg _) hη) hq.γ_le
  linarith

/-- **The selection hypotheses** of the released solver: `U_J` and the private operations are
unitary, the lifted Hamiltonian and dissipative parts are self-adjoint with norms at most `λ_H`
and `λ_D`, and the clock promises hold for every label. -/
theorem selectHyp (hq : q.OK) (D : Data X n (Cfg (VW q.b)) q.s) (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (x : X)
    (hrH : ∀ i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ q.etaH ^ 2)
    (hcH : ∀ j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ q.etaH ^ 2)
    (hrD : ∀ i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ q.etaD ^ 2)
    (hcD : ∀ j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ q.etaD ^ 2)
    (Jsrc : Bool → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ) :
    q.params.SelectHyp (⟨UJop (R := ℂ) q.UJg, privFam q.params D en x q.rho q.γ, Jsrc⟩ :
      Oracles q.params.a (Label q.params.k q.params.l) (Reg (Fin q.kx) ℂ))
      (hLift D en x) (lLift D en x) where
  uj := UJop_isUnitary _ (hadUJ4_ok q.σ q.hσ)
  priv _ := elift4_isUnitary _ (act4_unitary D x _ _ _)
  selfH := by
    unfold hLift
    rw [← qlift_star, SparseValuePrecision.matrixOperator_star_eq _
      (ODEMatrixEnergy.hamiltonianPart_isHermitian _)]
  selfL := by
    unfold lLift
    rw [← qlift_star, SparseValuePrecision.matrixOperator_star_eq _
      (ODEMatrixEnergy.dissipativePart_isHermitian _)]
  normH := (norm_qlift_le _ _).trans ((norm_matrixOperator_le D x _
    (ODEMatrixEnergy.hamiltonianPart_isHermitian _)
    (fun i j hij hji => by simp [ODEMatrixEnergy.hamiltonianPart_apply, hij, hji]) q.etaH
    hq.etaH_nonneg hrH hcH).trans (q.sqrt_le_lam hq q.etaH hq.etaH_nonneg))
  normL := (norm_qlift_le _ _).trans ((norm_matrixOperator_le D x _
    (ODEMatrixEnergy.dissipativePart_isHermitian _)
    (fun i j hij hji => by simp [ODEMatrixEnergy.dissipativePart_apply, hij, hji]) q.etaD
    hq.etaD_nonneg hrD hcD).trans (q.sqrt_le_lam hq q.etaD hq.etaD_nonneg))
  clock z := clock4 q.params D en q.σ q.hσ rfl hrange x q.etaH q.etaD q.rho q.γ
    hq.etaH_nonneg hq.etaD_nonneg rfl (q.rho_pos hq) hq.γ_pos hq.T_pos hq.g_ge hq.ε_pos
    (hq.ε_half.trans (by norm_num)) (q.TD_nonneg hq) q.tau_eq hrH hcH hrD hcD z

/-- **The instance conditions** of the released solver, from the energy bounds and the accretivity
of the input and the source and target conditions of the instance. -/
theorem instanceOK (hq : q.OK) (D : Data X n (Cfg (VW q.b)) q.s) (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (x : X)
    (hrH : ∀ i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ q.etaH ^ 2)
    (hcH : ∀ j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ q.etaH ^ 2)
    (hrD : ∀ i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ q.etaD ^ 2)
    (hcD : ∀ j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ q.etaD ^ 2)
    (hPSD : ∀ w : EuclideanSpace ℂ n, 0 ≤ (inner ℂ w (SparseStateOverlap.matrixOperator
      (ODEMatrixEnergy.dissipativePart (D.matrix x)) w)).re)
    (Jsrc : Bool → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ) (x0 v : Reg (Fin q.kx) ℂ)
    (hJ : ∀ c, IsUnitary (Jsrc c)) (hx0 : ‖x0‖ = q.r₀) (hv : ‖v‖ = q.rb)
    (hpx : x0 ≠ 0 → Jsrc false (seedV (S := Fin q.kx)) = ODEStateNormalization.unitDirection x0)
    (hpv : v ≠ 0 → Jsrc true (seedV (S := Fin q.kx)) = ODEStateNormalization.unitDirection v)
    (hne : ODEConstantForcing.solution (-mLift D en x) x0 v q.T ≠ 0)
    (hB : q.r₀ + q.T * q.rb ≤ q.g * ‖ODEConstantForcing.solution (-mLift D en x) x0 v q.T‖) :
    q.params.InstanceOK (seedV (S := Fin q.kx))
      (⟨UJop (R := ℂ) q.UJg, privFam q.params D en x q.rho q.γ, Jsrc⟩ :
        Oracles q.params.a (Label q.params.k q.params.l) (Reg (Fin q.kx) ℂ))
      (hLift D en x) (lLift D en x) x0 v where
  select := q.selectHyp hq D en hrange x hrH hcH hrD hcD Jsrc
  src_unitary := hJ
  psd := re_inner_qlift_nonneg en _ hPSD
  init_norm := hx0
  forcing_norm := hv
  init_prep := hpx
  forcing_prep := hpv
  target_ne := by
    rw [target_lift]
    exact hne
  budget := by
    rw [target_lift]
    exact hB

end Pub

/-- **The counts of the arithmetic**: `odeArith_counts` for the layout `q.lay`, the decoder scale
`q.kap` and the CORDIC accuracy `ζ/2`. -/
theorem Pub.ar_counts (q : Pub) :
    q.ar.circ.length ≤
      26 * q.lay.w * (31 + (q.lay.F + 2) + 3 + (q.lay.mA + 1) + 2 * (q.lay.mS + 1)) +
        (156 * (Cordic.params q.lay.w q.kap (q.ζ / 2)).w *
            ((Cordic.params q.lay.w q.kap (q.ζ / 2)).n + 1) +
          (Cordic.params q.lay.w q.kap (q.ζ / 2)).bP +
          2 * (Cordic.params q.lay.w q.kap (q.ζ / 2)).bT) ∧
    q.ar.A =
      (1 + 2 * q.lay.w + (31 + (q.lay.F + 2) + 3 + (q.lay.mA + 1) + 2 * (q.lay.mS + 1)) * q.lay.w) +
        (1 + 2 * (Cordic.params q.lay.w q.kap (q.ζ / 2)).w +
          (6 * ((Cordic.params q.lay.w q.kap (q.ζ / 2)).n + 1) + 1) *
            (Cordic.params q.lay.w q.kap (q.ζ / 2)).w) ∧
    q.ar.bT = (Cordic.params q.lay.w q.kap (q.ζ / 2)).bT ∧
    q.ar.bP = (Cordic.params q.lay.w q.kap (q.ζ / 2)).bP :=
  odeArith_counts (inp4 q.kx q.lay) q.kap (q.ζ / 2)

theorem card_SZ4 (k b : ℕ) : Fintype.card (SZ4 k b) = 6 * k + 4 * b := by
  simp only [SZ4, EW, VW, Fintype.card_sum, Fintype.card_fin]
  ring

/-! ### The theorem -/

section Main

variable {X n : Type*} [Fintype n] [DecidableEq n] {Zs : Type*} [Fintype Zs] [DecidableEq Zs]

/-- **The counts of the native solver from binary data.** For valid source circuits `srcC`, the
native preparation `q.prep srcC` (`U_J` from `σ + 3` Hadamard gates, the binary compute circuit
and the reversible arithmetic) depends only on the public data and the source circuits; its
trials are valid; it has at most
`prepGates + 84 d (σ + 3) + 6 d (2 (28 k + 2) + 2 |arith| + 2 bP + bT + 1) + |srcC 0| + |srcC 1|`
elementary gates (with the arithmetic counts `Pub.ar_counts`) and at most `24 d` calls of each
oracle besides those of the source circuits; in every history the protocol uses at most
`40 g N + 20 g (4 (|W| + |XW| + |Zs| + k) + 3)` elementary gates (`N` the gates of the
preparation) and at most `40 g` times the calls of the preparation; and its register has
`k + 2 (|W| + (6 k + 4 b + bT + bP + A + 3) + |Zs|) + k + 1` qubits. -/
theorem binary_ode_counts (q : Pub) (hq : q.OK)
    (srcC : Bool → List (NInstr ((Unit ⊕ Fin q.kx) ⊕ Zs) (PY q.kx q.b) Query))
    (hsrcV : ∀ c, ∀ i ∈ srcC c, i.Valid) :
    (∀ j, ∀ i ∈ trialN (q.prep srcC) j, i.Valid) ∧
    nGatesN (q.prep srcC) ≤ q.params.prepGates + 84 * q.params.d * (q.σ + 3) +
      6 * q.params.d * (2 * (28 * q.kx + 2) + 2 * q.ar.circ.length +
        (2 * q.ar.bP + q.ar.bT + 1)) + nGatesN (srcC false) + nGatesN (srcC true) ∧
    (∀ c : Query → Bool, nCallsN c (q.prep srcC) ≤
      12 * q.params.d * (2 * (if c Query.rowLocation then 1 else 0) +
        2 * (if c Query.columnLocation then 1 else 0) + 2 * (if c Query.value then 1 else 0)) +
        nCallsN c (srcC false) + nCallsN c (srcC true)) ∧
    ((nprotocol (q.prep srcC) q.g hq.g_ge).worstCost wGateN : ℝ) ≤
      40 * q.g * nGatesN (q.prep srcC) +
        20 * q.g * (4 * (Fintype.card q.params.W +
          Fintype.card (XW (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) + Fintype.card Zs + q.kx) +
          3) ∧
    (∀ c : Query → Bool, ((nprotocol (q.prep srcC) q.g hq.g_ge).worstCost (wCallN c) : ℝ) ≤
      40 * q.g * nCallsN c (q.prep srcC)) ∧
    Fintype.card (NW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) =
      q.kx + 2 * (Fintype.card q.params.W +
        (6 * q.kx + 4 * q.b + q.ar.bT + q.ar.bP + q.ar.A + 3) + Fintype.card Zs) + q.kx + 1 := by
  obtain ⟨hV, hG, hC, hW, hWC, hcard, -⟩ :=
    native_ode_solver q.params (q.params_ok hq) q.UJg (hadUJ4_ok q.σ q.hσ) q.nd q.nd_public q.ar
      q.ζ hq.ζ_pos.le (q.ar_ok hq) srcC hsrcV
  have hVg : nGatesN q.nd.V = 28 * q.kx + 2 := computeV4_nGates q.kx q.b q.params.k q.params.l
  have hVc : ∀ c : Query → Bool, nCallsN c q.nd.V = 2 * (if c Query.rowLocation then 1 else 0) +
      2 * (if c Query.columnLocation then 1 else 0) + 2 * (if c Query.value then 1 else 0) :=
    computeV4_nCalls q.kx q.b q.params.k q.params.l
  have hUJl : q.UJg.length = q.σ + 3 := hadUJ4_length q.σ q.hσ
  refine ⟨hV, ?_, ?_, ?_, hWC, ?_⟩
  · rw [privGates, hVg, hUJl] at hG
    exact hG
  · intro c
    have h := hC c
    rw [hVc] at h
    exact h
  · rw [Fintype.card_fin] at hW
    exact hW
  · rw [hcard, card_SZ4, Fintype.card_fin]

/-- **Native gate-efficient dissipative ODE solver from binary sparse data, constant
coefficients** (Theorem `ode:thm:gates`, constant coefficients, before finite-set synthesis).

Let the public data `q` satisfy the public conditions, and let the native sparse data `D` of the
matrices `M` have `k`-bit indices (`en`), `s = 2^σ` slots that are exactly the index words
supported on the lowest `σ` bits (`hrange`), and entries stored as two `b`-bit two's complement
components with decoder `c₀ (X + i Y)` (`hdec`). For valid source circuits `srcC`, the native
preparation `q.prep srcC` depends only on the public data and the source circuits, its trials are
valid, and its counts and those of the protocol are those of `binary_ode_counts`. For every input
`x` whose Hamiltonian and dissipative parts have row and column energies at most `η_H²` and
`η_D²` and whose dissipative part is accretive, every unitary source interface `J_src`
approximated within `ζs` by the source circuits with `24 d ζ + 2 ζs ≤ ν`, initial state `x₀` of
norm `r₀` and forcing `b` of norm `rb` prepared by `J_src` from the seed, with nonzero solution
`x(T)` of `x' = -M̂ x + b` and `r₀ + T rb ≤ g ‖x(T)‖`, the protocol succeeds with probability at
least `2/3` and its conditional output is within trace distance `ε` of `x(T)/‖x(T)‖`. -/
theorem binary_ode_solver (q : Pub) (hq : q.OK) (D : Data X n (Cfg (VW q.b)) q.s)
    (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (hdec : ∀ e z, D.decode e z = (q.c0 : ℂ) * gauss z)
    (srcC : Bool → List (NInstr ((Unit ⊕ Fin q.kx) ⊕ Zs) (PY q.kx q.b) Query))
    (hsrcV : ∀ c, ∀ i ∈ srcC c, i.Valid) :
    (∀ j, ∀ i ∈ trialN (q.prep srcC) j, i.Valid) ∧
    nGatesN (q.prep srcC) ≤ q.params.prepGates + 84 * q.params.d * (q.σ + 3) +
      6 * q.params.d * (2 * (28 * q.kx + 2) + 2 * q.ar.circ.length +
        (2 * q.ar.bP + q.ar.bT + 1)) + nGatesN (srcC false) + nGatesN (srcC true) ∧
    (∀ c : Query → Bool, nCallsN c (q.prep srcC) ≤
      12 * q.params.d * (2 * (if c Query.rowLocation then 1 else 0) +
        2 * (if c Query.columnLocation then 1 else 0) + 2 * (if c Query.value then 1 else 0)) +
        nCallsN c (srcC false) + nCallsN c (srcC true)) ∧
    ((nprotocol (q.prep srcC) q.g hq.g_ge).worstCost wGateN : ℝ) ≤
      40 * q.g * nGatesN (q.prep srcC) +
        20 * q.g * (4 * (Fintype.card q.params.W +
          Fintype.card (XW (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) + Fintype.card Zs + q.kx) +
          3) ∧
    (∀ c : Query → Bool, ((nprotocol (q.prep srcC) q.g hq.g_ge).worstCost (wCallN c) : ℝ) ≤
      40 * q.g * nCallsN c (q.prep srcC)) ∧
    Fintype.card (NW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) =
      q.kx + 2 * (Fintype.card q.params.W +
        (6 * q.kx + 4 * q.b + q.ar.bT + q.ar.bP + q.ar.A + 3) + Fintype.card Zs) + q.kx + 1 ∧
    ∀ x : X,
      (∀ i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ q.etaH ^ 2) →
      (∀ j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ q.etaH ^ 2) →
      (∀ i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ q.etaD ^ 2) →
      (∀ j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ q.etaD ^ 2) →
      (∀ w : EuclideanSpace ℂ n, 0 ≤ (inner ℂ w (SparseStateOverlap.matrixOperator
        (ODEMatrixEnergy.dissipativePart (D.matrix x)) w)).re) →
      ∀ (Jsrc : Bool → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ) (x0 v : Reg (Fin q.kx) ℂ)
        (ζs : ℝ),
      (∀ c, IsUnitary (Jsrc c)) →
      0 ≤ ζs →
      (∀ c, ApproxOn CleanX (nrun (prims (R := ℂ) D en x) (srcC c))
        (liftB (srcIdeal c (Jsrc c))) ζs) →
      24 * (q.params.d : ℝ) * q.ζ + 2 * ζs ≤ q.params.nu →
      ‖x0‖ = q.r₀ → ‖v‖ = q.rb →
      (x0 ≠ 0 → Jsrc false (seedV (S := Fin q.kx)) = ODEStateNormalization.unitDirection x0) →
      (v ≠ 0 → Jsrc true (seedV (S := Fin q.kx)) = ODEStateNormalization.unitDirection v) →
      ODEConstantForcing.solution (-mLift D en x) x0 v q.T ≠ 0 →
      q.r₀ + q.T * q.rb ≤ q.g * ‖ODEConstantForcing.solution (-mLift D en x) x0 v q.T‖ →
      NOutcome (q.prep srcC) q.g q.ε hq.g_ge (prims (R := ℂ) D en x)
        (ODEConstantForcing.solution (-mLift D en x) x0 v q.T) := by
  obtain ⟨hV, hG, hC, hW, hWC, hcard⟩ := binary_ode_counts q hq srcC hsrcV
  obtain ⟨-, -, -, -, -, -, hout⟩ :=
    native_ode_solver q.params (q.params_ok hq) q.UJg (hadUJ4_ok q.σ q.hσ) q.nd q.nd_public q.ar
      q.ζ hq.ζ_pos.le (q.ar_ok hq) srcC hsrcV
  refine ⟨hV, hG, hC, hW, hWC, hcard, ?_⟩
  intro x hrH hcH hrD hcD hPSD Jsrc x0 v ζs hJ hζs hsrc hbud hx0 hv hpx hpv hne hB
  have h := hout (prims (R := ℂ) D en x) (privFam q.params D en x q.rho q.γ) Jsrc
    (hLift D en x) (lLift D en x) x0 v ζs (prims_isUnitary D en x)
    (q.nativeOK hq D en hrange hdec x) hζs hsrc hbud
    (q.instanceOK hq D en hrange x hrH hcH hrD hcD hPSD Jsrc x0 v hJ hx0 hv hpx hpv hne hB)
  rw [target_lift] at h
  exact h

/-- **The worst-case gate count of the native solver from binary data** (the explicit count
underlying equation `ode:eq:gate-main`, for binary data): in every history the protocol uses at
most `9000 g [(d+1)(a + m + r + 1 + C_J + G_C) + (k_T + 1) + (J+2)(l+1) + G_src + A]` elementary
gates, with `a = k + 3`, `C_J = σ + 3` the Hadamard gates of `U_J`,
`G_C = 2 (28 k + 2) + 2 |arith| + 2 bP + bT + 1` the gates of one native private call (with the
arithmetic counts `Pub.ar_counts`), `k_T` the node bits, `G_src = |srcC 0| + |srcC 1|` and
`A = k + |Zs| + (6 k + 4 b) + bT + bP + A_arith` the system, source-scratch, private-scratch and
arithmetic wires; `d`, `m`, `r`, `l` and `J` are the released public sizes. -/
theorem binary_ode_gate_count (q : Pub) (hq : q.OK)
    (srcC : Bool → List (NInstr ((Unit ⊕ Fin q.kx) ⊕ Zs) (PY q.kx q.b) Query))
    (hsrcV : ∀ c, ∀ i ∈ srcC c, i.Valid) :
    ((nprotocol (q.prep srcC) q.g hq.g_ge).worstCost wGateN : ℝ) ≤
      9000 * q.g * (((q.params.d : ℝ) + 1) * (((q.kx + 3 : ℕ) : ℝ) + q.params.m + q.params.r + 1 +
          ((q.σ + 3 : ℕ) : ℝ) + ((2 * (28 * q.kx + 2) + 2 * q.ar.circ.length +
            (2 * q.ar.bP + q.ar.bT + 1) : ℕ) : ℝ)) +
        ((q.params.k : ℝ) + 1) + ((q.params.J : ℝ) + 2) * ((q.params.l : ℝ) + 1) +
        ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true)) +
        ((q.kx : ℝ) + Fintype.card Zs + ((6 * q.kx + 4 * q.b : ℕ) : ℝ) + q.ar.bT + q.ar.bP +
          q.ar.A)) := by
  have h := native_ode_gate_count q.params (q.params_ok hq) q.UJg (hadUJ4_ok q.σ q.hσ) q.nd
    q.nd_public q.ar q.ζ hq.ζ_pos.le (q.ar_ok hq) srcC hsrcV
  have hVg : nGatesN q.nd.V = 28 * q.kx + 2 := computeV4_nGates q.kx q.b q.params.k q.params.l
  have hUJl : q.UJg.length = q.σ + 3 := hadUJ4_length q.σ q.hσ
  rw [privGates, hVg, hUJl, Fintype.card_fin, card_SZ4] at h
  exact h

end Main

end

end SparseHamiltonian.GateBinaryODE
