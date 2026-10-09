import GateEfficientBinaryODETime.Clock
import GateEfficientBinaryODE.Solver

/-!
# The public data and the instance conditions of the time-dependent solver from binary data

The time-dependent problem of Theorem `ode:thm:time` in the gate-level form of Theorem
`ode:thm:gates`, for a generator sampled by time-indexed binary sparse oracles.

* `PubT`: the public data (system qubits, slot bits `σ`, stored bits, decoder scale, energy
  bounds, Cayley rescaling, time, amplification bound, accuracy, time-slot bits `m`, arithmetic
  accuracy) and its conditions `PubT.OK`, including the mesh condition of the released
  time-dependent solver.
* `PubT.params`: the released public parameters (`GateODE.Time.TParams`) with `a = k + 3`
  ancillas, `Q = width(4s, γ)`, `q̄ = moment γ`, `λ_H = √(4s) η_H / γ`, `λ_D = √(4s) η_D / γ` and
  `2^m` time slots; `PubT.params_ok`: the released public conditions.
* The native data: `U_J` from `hadUJ4`, the private operation `odeOpT` and the arithmetic
  `odeArT` with the layout `layT` (`PubT.nd`, `PubT.ar`, `PubT.ar_ok`); the native identity
  of the label- and slot-selected family `privFamT` (`PubT.nativeOK`).
* `PubT.selectHyp`: the selection hypotheses of the released solver (unitarity,
  self-adjointness, the norm bounds `‖H_r‖ ≤ λ_H`, `‖L_r‖ ≤ λ_D` and the clock promises at
  every label and slot) from row and column energy bounds of every sample.
* `PubT.Rest`: the instance conditions that do not concern the selection (source loading,
  weight preparation, generator path, forcing, solution, discretisation budget), with the
  sample bound of the generator path stated against the lifted samples `M̂_r`;
  `PubT.instanceOK`: the released instance conditions from the energy bounds, the accretivity
  of every sample and `PubT.Rest`.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateBinaryODETime

noncomputable section
open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
open SparseHamiltonian.GateBinary SparseHamiltonian.GateBinaryODE SparseHamiltonian.OracleCircuit
open CayleyClockInterface
open SparseHamiltonian.GateODE (Label)
open SparseHamiltonian.GateODE.Time (TParams TOracles)
open SparseHamiltonian.GatePointerEncoding (wordValue)
open NativeSparseBlockEncoding (Data Query)
open scoped InnerProduct

/-! ### The public data -/

/-- **The public data** of the time-dependent dissipative solver from binary sparse data. -/
structure PubT where
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
  /-- The row and column energy bound of the Hamiltonian part of every sample. -/
  etaH : ℝ
  /-- The row and column energy bound of the dissipative part of every sample. -/
  etaD : ℝ
  /-- The Cayley rescaling. -/
  γ : ℝ
  /-- The time. -/
  T : ℝ
  /-- The public amplification bound `g`. -/
  g : ℝ
  /-- The accuracy. -/
  ε : ℝ
  /-- The time-slot bits: `2^m` time slots. -/
  m : ℕ
  /-- The arithmetic accuracy. -/
  ζ : ℝ

namespace PubT

variable (q : PubT)

/-- The number of sparsity slots. -/
abbrev s : ℕ := 2 ^ q.σ

/-- **The released public parameters**: `a = k + 3` ancillas, `Q = width(4s, γ)`,
`q̄ = moment γ`, `λ_H = √(4s) η_H / γ`, `λ_D = √(4s) η_D / γ` and `2^m` time slots. -/
def params : TParams where
  a := q.kx + 3
  Q := width (4 * (q.s : ℝ)) q.γ
  qbar := moment q.γ
  T := q.T
  lamH := Real.sqrt (4 * (q.s : ℝ)) * q.etaH / q.γ
  lamD := Real.sqrt (4 * (q.s : ℝ)) * q.etaD / q.γ
  g := q.g
  ε := q.ε
  m := q.m

/-- The scale `ρ = η_H + R η_D` of the four sectors, `R` the LCHS radius of the released
time-dependent solver (ratio `2g`, accuracy `ε/2`). -/
def rho : ℝ := q.etaH + ImprovedODEQueryBudget.radius (2 * q.g) (q.ε / 2) * q.etaD

/-- **The public conditions.** The mesh condition is that of the released time-dependent solver
for the common time `τ = T √(4s) ρ / γ` (`tau_eq`). -/
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
  ζ_pos : 0 < q.ζ
  ζ_le : q.ζ ≤ 1
  mesh : TimeSchedule.steps q.params.tau (q.params.nu / 3) ≤ 2 ^ q.m

/-- The fractional bits of the LCHS step. -/
def F : ℕ := fOf (gridP q.params) q.ζ

/-- The integer layout of the arithmetic. -/
abbrev lay : Lay := layT q.params q.b q.F

/-- The decoder scale `κ = γ √(4s) c₀ / (2^(F + 10) ρ)`. -/
def kap : ℝ := kapT q.s q.c0 q.rho q.γ q.F

/-- The gates of `U_J`: `σ + 3` Hadamard gates. -/
def UJg : List (Gate (Fin q.params.a ⊕ Fin q.kx)) := hadUJ4 q.kx q.σ q.hσ

/-- **The native private operation**: the compute circuit `computeV4` with every call also reading
the slot wires, the orientation wire and the decoder `decT` with scale `κ` and step factor
`ρ_L`. -/
def nd : NativeOp (TSel q.params.m q.params.l q.params.m) (Fin q.params.a ⊕ Fin q.kx)
    (SZ4 q.kx q.b) (Fin q.m ⊕ PY q.kx q.b) Query :=
  odeOpT q.kx q.lay q.m q.kap (rhoL (gridP q.params) q.F)

/-- **The arithmetic** of the native private operation, with CORDIC accuracy `ζ/2`. -/
def ar : Arith (NB (TSel q.params.m q.params.l q.params.m) (Fin q.params.a ⊕ Fin q.kx)
    (SZ4 q.kx q.b)) :=
  odeArT q.kx q.lay q.m q.kap (q.ζ / 2)

/-- **One native preparation** of the solver from binary data, for the loading circuit `loadC`
and the weight-preparation circuit `wpC`. -/
def prep {Zs : Type*} [Fintype Zs] [DecidableEq Zs]
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b) Query))
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b) Query)) :
    List (NInstr (TNW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A)
      (Fin q.m ⊕ PY q.kx q.b) Query) :=
  tnprepC q.params q.UJg q.nd q.ar loadC wpC

theorem sqrt4s_pos : 0 < Real.sqrt (4 * (q.s : ℝ)) := by
  apply Real.sqrt_pos.mpr
  have : (1 : ℝ) ≤ (q.s : ℝ) := by exact_mod_cast Nat.one_le_two_pow
  linarith

theorem radius_pos (hq : q.OK) : 0 < ImprovedODEQueryBudget.radius (2 * q.g) (q.ε / 2) :=
  GateODE.AnalyticLCHS.radius_pos (by linarith [hq.g_ge]) (by linarith [hq.ε_pos])
    (by linarith [hq.ε_half])

theorem rho_pos (hq : q.OK) : 0 < q.rho := by
  have hR := q.radius_pos hq
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
    ImprovedODEQueryBudget.radius (2 * q.g) (q.ε / 2) *
      (Real.sqrt (4 * (q.s : ℝ)) * q.etaD / q.γ) = _
  unfold rho
  ring

/-- The common simulation time is `τ = T √(4s) ρ / γ`. -/
theorem tau_eq : q.params.tau = q.params.T * (Real.sqrt (4 * (q.s : ℝ)) * q.rho) / q.γ := by
  show q.params.T * (q.params.lamH + q.params.R * q.params.lamD) = _
  rw [q.lam_sum]
  ring

/-- **The public conditions** of the released time-dependent solver hold. -/
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
  mesh := hq.mesh

theorem TD_nonneg (hq : q.OK) : 0 ≤ q.params.T * q.params.lamD :=
  mul_nonneg hq.T_pos.le (q.params_ok hq).lamD_nonneg

theorem ε_le_one (hq : q.OK) : q.ε ≤ 1 := hq.ε_half.trans (by norm_num)

theorem lay_ok (hq : q.OK) : q.lay.OK :=
  layT_ok q.params q.b q.F hq.b_pos hq.g_ge hq.ε_pos (q.ε_le_one hq) (q.TD_nonneg hq)

theorem kap_pos (hq : q.OK) : 0 < q.kap :=
  kapT_pos q.s q.c0 q.rho q.γ q.F (Nat.two_pow_pos _) hq.c0_pos (q.rho_pos hq) hq.γ_pos

/-- The native private operation is public. -/
theorem nd_public : q.nd.Public := odeOpT_public _ _ _ _ _

/-- **The arithmetic hypothesis** with accuracy `ζ`. -/
theorem ar_ok (hq : q.OK) : ArithOK q.ar (Sum.inl (Sum.inr q.nd.o)) q.nd.dec q.ζ := by
  have hr : |rhoL (gridP q.params) q.F - 1| ≤ q.ζ / 4 :=
    rhoLT_close q.params q.ζ hq.ζ_pos hq.ζ_le hq.g_ge hq.ε_pos (q.ε_le_one hq) (q.TD_nonneg hq)
  have h1 := hq.ζ_pos
  have h2 := hq.ζ_le
  exact odeArT_ok q.kx q.lay q.m (q.lay_ok hq) q.kap (rhoL (gridP q.params) q.F) (q.ζ / 2) q.ζ
    (q.kap_pos hq) (by linarith) (by linarith) (by linarith) (by linarith)

/-- **The counts of the arithmetic**: `arithT_counts` and `GateBinaryODE.odeArith_counts` for the
layout `q.lay`, the decoder scale `q.kap` and the CORDIC accuracy `ζ/2`. -/
theorem ar_counts :
    q.ar.circ.length ≤ 52 * (q.m + 14) +
      (26 * q.lay.w * (31 + (q.lay.F + 2) + 3 + (q.lay.mA + 1) + 2 * (q.lay.mS + 1)) +
        (156 * (Cordic.params q.lay.w q.kap (q.ζ / 2)).w *
            ((Cordic.params q.lay.w q.kap (q.ζ / 2)).n + 1) +
          (Cordic.params q.lay.w q.kap (q.ζ / 2)).bP +
          2 * (Cordic.params q.lay.w q.kap (q.ζ / 2)).bT)) ∧
    q.ar.A = (1 + 2 * (q.m + 14) + (31 + 2 + 3 + 6 + 2 * 10) * (q.m + 14)) +
      ((1 + 2 * q.lay.w + (31 + (q.lay.F + 2) + 3 + (q.lay.mA + 1) + 2 * (q.lay.mS + 1)) *
          q.lay.w) +
        (1 + 2 * (Cordic.params q.lay.w q.kap (q.ζ / 2)).w +
          (6 * ((Cordic.params q.lay.w q.kap (q.ζ / 2)).n + 1) + 1) *
            (Cordic.params q.lay.w q.kap (q.ζ / 2)).w)) ∧
    q.ar.bT = (Cordic.params q.lay.w q.kap (q.ζ / 2)).bT ∧
    q.ar.bP = (Cordic.params q.lay.w q.kap (q.ζ / 2)).bP := by
  obtain ⟨h1, h2, h3, h4⟩ := arithT_counts (inpT4 q.kx q.lay q.m) q.kap (q.ζ / 2)
  obtain ⟨g1, g2, g3, g4⟩ := odeArith_counts (inpT4 q.kx q.lay q.m).lift q.kap (q.ζ / 2)
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact h1.trans (by omega)
  · change (arithT (inpT4 q.kx q.lay q.m) q.kap (q.ζ / 2)).A = _
    rw [h2, g2]
  · exact h3.trans g3
  · exact h4.trans g4

variable {X n : Type*} [Fintype n] [DecidableEq n]

/-- **The native identity** of the label- and slot-selected private operation. -/
theorem nativeOK (hq : q.OK) (D : Data (X × Fin (2 ^ q.m)) n (Cfg (VW q.b)) q.s)
    (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (hdec : ∀ e z, D.decode e z = (q.c0 : ℂ) * gauss z) (x : X) :
    NativeOK (primsT (R := ℂ) D en x) q.nd
      (selOp (tlabFam (P := Reg (Fin q.kx) ℂ) (privFamT q.params D en x q.rho q.γ) false)) := by
  obtain ⟨k0, hk0⟩ : ∃ m, D.slot m = zIdx en := by
    refine (hrange _).2 ⟨fun _ => false, ?_⟩
    unfold zIdx
    congr 1
    funext i
    simp [lowWord]
  exact nativeOK_T q.params D en k0 hk0 x q.c0 hq.c0_pos.ne' hdec q.rho q.γ (q.rho_pos hq).ne'
    q.F (hRoundT_ne q.params q.ζ hq.ζ_pos hq.ζ_le hq.g_ge hq.ε_pos (q.ε_le_one hq)
      (q.TD_nonneg hq))

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

/-- **The selection hypotheses** of the released time-dependent solver: `U_J` and the private
operations are unitary, the lifted Hamiltonian and dissipative parts of every sample are
self-adjoint with norms at most `λ_H` and `λ_D`, and the clock promises hold at every label and
slot. -/
theorem selectHyp (hq : q.OK) (D : Data (X × Fin (2 ^ q.m)) n (Cfg (VW q.b)) q.s)
    (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (x : X)
    (hrH : ∀ r i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaH ^ 2)
    (hcH : ∀ r j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaH ^ 2)
    (hrD : ∀ r i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaD ^ 2)
    (hcD : ∀ r j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaD ^ 2)
    (Jl : Bool × (Fin q.m → Bool) → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
    (Wp : Matrix (Cfg (Fin (q.m + 1))) (Cfg (Fin (q.m + 1))) ℂ) :
    q.params.SelectHypT (⟨UJop (R := ℂ) q.UJg, privFamT q.params D en x q.rho q.γ, Jl, Wp⟩ :
      TOracles q.params.a q.params.m q.params.l (Reg (Fin q.kx) ℂ))
      (HsT D en x) (LsT D en x) where
  uj := UJop_isUnitary _ (hadUJ4_ok q.σ q.hσ)
  priv z r _ := privFamT_isUnitary _ _ _ _ _ _ z r
  selfH r hr := by
    rw [HsT_of_lt D en x r hr]
    unfold hLift
    rw [← qlift_star, SparseValuePrecision.matrixOperator_star_eq _
      (ODEMatrixEnergy.hamiltonianPart_isHermitian _)]
  selfL r hr := by
    rw [LsT_of_lt D en x r hr]
    unfold lLift
    rw [← qlift_star, SparseValuePrecision.matrixOperator_star_eq _
      (ODEMatrixEnergy.dissipativePart_isHermitian _)]
  normH r hr := by
    rw [HsT_of_lt D en x r hr]
    exact (norm_qlift_le _ _).trans ((norm_matrixOperator_le D (x, ⟨r, hr⟩) _
      (ODEMatrixEnergy.hamiltonianPart_isHermitian _)
      (fun i j hij hji => by simp [ODEMatrixEnergy.hamiltonianPart_apply, hij, hji]) q.etaH
      hq.etaH_nonneg (hrH _) (hcH _)).trans (q.sqrt_le_lam hq q.etaH hq.etaH_nonneg))
  normL r hr := by
    rw [LsT_of_lt D en x r hr]
    exact (norm_qlift_le _ _).trans ((norm_matrixOperator_le D (x, ⟨r, hr⟩) _
      (ODEMatrixEnergy.dissipativePart_isHermitian _)
      (fun i j hij hji => by simp [ODEMatrixEnergy.dissipativePart_apply, hij, hji]) q.etaD
      hq.etaD_nonneg (hrD _) (hcD _)).trans (q.sqrt_le_lam hq q.etaD hq.etaD_nonneg))
  clock z r hr := clockT q.params D en q.σ q.hσ rfl hrange x q.etaH q.etaD q.rho q.γ
    hq.etaH_nonneg hq.etaD_nonneg rfl (q.rho_pos hq) hq.γ_pos hq.T_pos hq.g_ge hq.ε_pos
    (q.ε_le_one hq) (q.TD_nonneg hq) q.tau_eq hrH hcH hrD hcD z r hr

/-- **The remaining instance conditions**: those of the released instance conditions
(`GateODE.Time.TParams.InstanceOK`) that do not concern the selection. The loading `Jl` is
unitary and prepares the normalised initial state and forcing samples from the seed, the weight
preparation `Wp` is unitary with the amplitudes `√(‖z_s‖ / B)` in its zero column; `x` solves
`x' = -G(u) x + b(u)` on `[0, T]` for an accretive `βG`-Lipschitz generator path `G` within `δG`
of the lifted samples `M̂_r` at the slot times and a `βb`-Lipschitz forcing `b` with `‖b‖ ≤ bmax`
within `δb` of the samples `b_r`; `x(T) ≠ 0`, `B ≤ g ‖x(T)‖` for the source mass `B`, and the
discretisation budget holds. These conditions concern the source preparations, the continuous
problem and its solution, not the binary data of the generator samples; they remain hypotheses,
as the source and target conditions of the constant-coefficient library. -/
structure Rest (D : Data (X × Fin (2 ^ q.m)) n (Cfg (VW q.b)) q.s) (en : Cfg (Fin q.kx) ≃ n)
    (x : X) (Jl : Bool × (Fin q.m → Bool) → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
    (Wp : Matrix (Cfg (Fin (q.m + 1))) (Cfg (Fin (q.m + 1))) ℂ)
    (G : ℝ → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ) (bf xs : ℝ → Reg (Fin q.kx) ℂ)
    (bs : ℕ → Reg (Fin q.kx) ℂ) (βG δG βb δb bmax : ℝ) : Prop where
  load_unitary : ∀ c, IsUnitary (Jl c)
  prep_left : Wp.conjTranspose * Wp = 1
  prep_right : Wp * Wp.conjTranspose = 1
  prep : ∀ w : Cfg (Fin (q.m + 1)),
    Wp w (fun _ => false) = ((q.params.srcAmp (xs 0) bs (w 0, Fin.tail w) : ℝ) : ℂ)
  init_load : xs 0 ≠ 0 →
    Jl (false, fun _ => false) (seedV (S := Fin q.kx)) = ODEStateNormalization.unitDirection (xs 0)
  forcing_load : ∀ w : Fin q.m → Bool, bs (wordValue w) ≠ 0 →
    Jl (true, w) (seedV (S := Fin q.kx)) = ODEStateNormalization.unitDirection (bs (wordValue w))
  solves : TimeDependentODE.SolvesODE G bf xs 0 q.T
  accretive : ∀ u ∈ Set.Icc 0 q.T, TimeDependentODE.Accretive (G u)
  lipG : ∀ u ∈ Set.Icc 0 q.T, ∀ u' ∈ Set.Icc 0 q.T, ‖G u - G u'‖ ≤ βG * |u - u'|
  sampleG : ∀ (r : ℕ) (hr : r < 2 ^ q.m),
    ‖G (r * q.T / ((2 ^ q.m : ℕ) : ℝ)) - mLift D en (x, ⟨r, hr⟩)‖ ≤ δG
  lipb : ∀ u ∈ Set.Icc 0 q.T, ∀ u' ∈ Set.Icc 0 q.T, ‖bf u - bf u'‖ ≤ βb * |u - u'|
  sampleb : ∀ r : ℕ, r < 2 ^ q.m → ‖bf (r * q.T / ((2 ^ q.m : ℕ) : ℝ)) - bs r‖ ≤ δb
  boundb : ∀ u ∈ Set.Icc 0 q.T, ‖bf u‖ ≤ bmax
  βG_nonneg : 0 ≤ βG
  βb_nonneg : 0 ≤ βb
  target_ne : xs q.T ≠ 0
  budget : q.params.mass (xs 0) bs ≤ q.g * ‖xs q.T‖
  disc : q.params.discretisation βG δG βb δb bmax ‖xs 0‖ ≤
    q.ε * q.params.mass (xs 0) bs / (2000 * q.g)

/-- **The instance conditions** of the released time-dependent solver, from the energy bounds and
the accretivity of every sample and the remaining conditions `Rest`. -/
theorem instanceOK (hq : q.OK) (D : Data (X × Fin (2 ^ q.m)) n (Cfg (VW q.b)) q.s)
    (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (x : X)
    (hrH : ∀ r i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaH ^ 2)
    (hcH : ∀ r j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaH ^ 2)
    (hrD : ∀ r i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaD ^ 2)
    (hcD : ∀ r j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaD ^ 2)
    (hPSD : ∀ r, ∀ w : EuclideanSpace ℂ n, 0 ≤ (inner ℂ w (SparseStateOverlap.matrixOperator
      (ODEMatrixEnergy.dissipativePart (D.matrix (x, r))) w)).re)
    (Jl : Bool × (Fin q.m → Bool) → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
    (Wp : Matrix (Cfg (Fin (q.m + 1))) (Cfg (Fin (q.m + 1))) ℂ)
    (G : ℝ → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ) (bf xs : ℝ → Reg (Fin q.kx) ℂ)
    (bs : ℕ → Reg (Fin q.kx) ℂ) (βG δG βb δb bmax : ℝ)
    (hR : q.Rest D en x Jl Wp G bf xs bs βG δG βb δb bmax) :
    q.params.InstanceOK (seedV (S := Fin q.kx))
      (⟨UJop (R := ℂ) q.UJg, privFamT q.params D en x q.rho q.γ, Jl, Wp⟩ :
        TOracles q.params.a q.params.m q.params.l (Reg (Fin q.kx) ℂ))
      (HsT D en x) (LsT D en x) G bf xs bs βG δG βb δb bmax where
  select := q.selectHyp hq D en hrange x hrH hcH hrD hcD Jl Wp
  psd r hr w := by
    rw [LsT_of_lt D en x r hr]
    exact re_inner_qlift_nonneg en _ (hPSD _) w
  load_unitary := hR.load_unitary
  prep_left := hR.prep_left
  prep_right := hR.prep_right
  prep := hR.prep
  init_load := hR.init_load
  forcing_load := hR.forcing_load
  solves := hR.solves
  accretive := hR.accretive
  lipG := hR.lipG
  sampleG r hr := by
    rw [gensT_eq D en x r hr]
    exact hR.sampleG r hr
  lipb := hR.lipb
  sampleb := hR.sampleb
  boundb := hR.boundb
  βG_nonneg := hR.βG_nonneg
  βb_nonneg := hR.βb_nonneg
  target_ne := hR.target_ne
  budget := hR.budget
  disc := hR.disc

end PubT

end

end SparseHamiltonian.GateBinaryODETime
