import ZeroTimeGateODE.TimeCombined
import GateEfficientBinaryODETime.Solver

/-!
# Zero time or a known zero generator from time-indexed binary data

The released time-dependent solver from binary sparse data
`GateBinaryODETime.binary_ode_time_solver` takes the public data `GateBinaryODETime.PubT` with
`PubT.OK`, which requires `T > 0` and `η_H + η_D > 0`.  For every `T ≥ 0` and all energy bounds
`η_H, η_D ≥ 0` (`BTPublicOK0`, with the released mesh condition), one circuit per public
parameter choice on the released binary register:

`btprepC q loadC wpC = if T = 0 ∨ η_H + η_D = 0 then tzprepC loadC wpC else q.prep loadC wpC`

(`BTZeroCase`).  In the zero case the released public parameters are in the zero case
(`btzeroCase_params`), the zero-case instance conditions follow from the energy promises of
every sample and the released remaining conditions `PubT.Rest` (`binary_tzInstanceOK`), and the
protocol makes no call of the time-indexed binary sparse oracles besides those of the loading
and weight-preparation circuits (`binary_time_zero_no_matrix_calls`).
`binary_ode_time_solver_nonneg` states the released solver for every `T ≥ 0` with the released
hypotheses and the counts `if BTZeroCase q then <direct source assembly> else <released>`.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.ZeroTimeGateODE

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit GateNative GateBinary
open GateBinaryODE (SZ4 card_SZ4 hLift lLift norm_matrixOperator_le re_inner_qlift_nonneg)
open GateBinaryODETime (PubT HsT LsT HsT_of_lt LsT_of_lt gensT_eq)
open GateODE.Time (TParams)
open NativeSparseBlockEncoding (Data Query)
open scoped InnerProduct BigOperators

/-! ### Public data for every `T ≥ 0` -/

/-- The public conditions for every `T ≥ 0`: the released `GateBinaryODETime.PubT.OK` with
`0 ≤ T` in place of `0 < T` and without `0 < η_H + η_D`. -/
structure BTPublicOK0 (q : PubT) : Prop where
  b_pos : 0 < q.b
  c0_pos : 0 < q.c0
  etaH_nonneg : 0 ≤ q.etaH
  etaD_nonneg : 0 ≤ q.etaD
  γ_pos : 0 < q.γ
  γ_le : q.γ ≤ 1
  T_nonneg : 0 ≤ q.T
  g_ge : 1 ≤ q.g
  ε_pos : 0 < q.ε
  ε_half : q.ε ≤ 1 / 2
  ζ_pos : 0 < q.ζ
  ζ_le : q.ζ ≤ 1
  mesh : TimeSchedule.steps q.params.tau (q.params.nu / 3) ≤ 2 ^ q.m

/-- **The zero case** of the time-indexed binary data: zero time or zero energy bounds. -/
abbrev BTZeroCase (q : PubT) : Prop := q.T = 0 ∨ q.etaH + q.etaD = 0

/-- The released public conditions give those for every `T ≥ 0`. -/
theorem btpublicOK0_of {q : PubT} (hq : q.OK) : BTPublicOK0 q :=
  ⟨hq.b_pos, hq.c0_pos, hq.etaH_nonneg, hq.etaD_nonneg, hq.γ_pos, hq.γ_le, hq.T_pos.le, hq.g_ge,
    hq.ε_pos, hq.ε_half, hq.ζ_pos, hq.ζ_le, hq.mesh⟩

/-- Outside the zero case the conditions for every `T ≥ 0` are the released ones. -/
theorem btpublicOK_of {q : PubT} (hq : BTPublicOK0 q) (hz : ¬ BTZeroCase q) : q.OK := by
  have hT : q.T ≠ 0 := fun h => hz (Or.inl h)
  have hE : q.etaH + q.etaD ≠ 0 := fun h => hz (Or.inr h)
  exact ⟨hq.b_pos, hq.c0_pos, hq.etaH_nonneg, hq.etaD_nonneg,
    lt_of_le_of_ne (add_nonneg hq.etaH_nonneg hq.etaD_nonneg) (Ne.symm hE), hq.γ_pos, hq.γ_le,
    lt_of_le_of_ne hq.T_nonneg (Ne.symm hT), hq.g_ge, hq.ε_pos, hq.ε_half, hq.ζ_pos, hq.ζ_le,
    hq.mesh⟩

/-- The released public parameters of the binary data satisfy the conditions for every
`T ≥ 0`. -/
theorem btparams_ok0 {q : PubT} (hq : BTPublicOK0 q) : TPublicOK0 q.params where
  T_nonneg := hq.T_nonneg
  g_ge := hq.g_ge
  ε_pos := hq.ε_pos
  ε_half := hq.ε_half
  lamH_nonneg := div_nonneg (mul_nonneg (Real.sqrt_nonneg _) hq.etaH_nonneg) hq.γ_pos.le
  lamD_nonneg := div_nonneg (mul_nonneg (Real.sqrt_nonneg _) hq.etaD_nonneg) hq.γ_pos.le
  Q_ge := CayleyClockInterface.width_ge_one _ _
  qbar_nonneg := CayleyClockInterface.moment_nonneg _
  qbar_le := CayleyClockInterface.moment_le_width _ _ hq.γ_pos.le hq.γ_le
  mesh := hq.mesh

/-- The zero case of the binary data is the zero case of its released public parameters:
zero energy bounds give `λ_H = λ_D = 0`. -/
theorem btzeroCase_params {q : PubT} (hq : BTPublicOK0 q) (hz : BTZeroCase q) :
    TZeroCase q.params := by
  rcases hz with h | h
  · exact Or.inl h
  · right
    have hH : q.etaH = 0 := by linarith [hq.etaH_nonneg, hq.etaD_nonneg]
    have hD : q.etaD = 0 := by linarith [hq.etaH_nonneg, hq.etaD_nonneg]
    have h1 : q.params.lamH = 0 := by
      show Real.sqrt (4 * (q.s : ℝ)) * q.etaH / q.γ = 0
      rw [hH, mul_zero, zero_div]
    have h2 : q.params.lamD = 0 := by
      show Real.sqrt (4 * (q.s : ℝ)) * q.etaD / q.γ = 0
      rw [hD, mul_zero, zero_div]
    rw [h1, h2, mul_zero, add_zero]

/-- `√(2s) η ≤ √(4s) η / γ` for `0 < γ ≤ 1` (the released `PubT.sqrt_le_lam` without the other
public conditions). -/
theorem sqrt_le_lam0 (q : PubT) (hγ : 0 < q.γ) (hγ1 : q.γ ≤ 1) (η : ℝ) (hη : 0 ≤ η) :
    Real.sqrt (2 * (q.s : ℝ)) * η ≤ Real.sqrt (4 * (q.s : ℝ)) * η / q.γ := by
  have h1 : Real.sqrt (2 * (q.s : ℝ)) ≤ Real.sqrt (4 * (q.s : ℝ)) :=
    Real.sqrt_le_sqrt (by have : (0 : ℝ) ≤ q.s := Nat.cast_nonneg _; linarith)
  rw [le_div_iff₀ hγ]
  have h2 : Real.sqrt (2 * (q.s : ℝ)) * η ≤ Real.sqrt (4 * (q.s : ℝ)) * η :=
    mul_le_mul_of_nonneg_right h1 hη
  have h4 : Real.sqrt (2 * (q.s : ℝ)) * η * q.γ ≤ Real.sqrt (2 * (q.s : ℝ)) * η :=
    mul_le_of_le_one_right (mul_nonneg (Real.sqrt_nonneg _) hη) hγ1
  linarith

/-! ### The zero-case instance conditions -/

section Inst

variable {X n : Type*} [Fintype n] [DecidableEq n]

/-- **The zero-case instance conditions from binary data**: the self-adjointness and the norm
bounds of the lifted parts of every sample from the row and column energy bounds, their
accretivity, and the released remaining conditions `PubT.Rest`. -/
theorem binary_tzInstanceOK (q : PubT) (hq : BTPublicOK0 q)
    (D : Data (X × Fin (2 ^ q.m)) n (Cfg (VW q.b)) q.s) (en : Cfg (Fin q.kx) ≃ n) (x : X)
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
    TZInstanceOK q.params (seedV (S := Fin q.kx)) Jl Wp (HsT D en x) (LsT D en x) G bf xs bs
      βG δG βb δb bmax where
  selfH r hr := by
    rw [HsT_of_lt D en x r hr]
    unfold hLift
    rw [← qlift_star, SparseValuePrecision.matrixOperator_star_eq _
      (ODEMatrixEnergy.hamiltonianPart_isHermitian _)]
  normH r hr := by
    rw [HsT_of_lt D en x r hr]
    exact (norm_qlift_le _ _).trans ((norm_matrixOperator_le D (x, ⟨r, hr⟩) _
      (ODEMatrixEnergy.hamiltonianPart_isHermitian _)
      (fun i j hij hji => by simp [ODEMatrixEnergy.hamiltonianPart_apply, hij, hji]) q.etaH
      hq.etaH_nonneg (hrH _) (hcH _)).trans
        (sqrt_le_lam0 q hq.γ_pos hq.γ_le q.etaH hq.etaH_nonneg))
  normL r hr := by
    rw [LsT_of_lt D en x r hr]
    exact (norm_qlift_le _ _).trans ((norm_matrixOperator_le D (x, ⟨r, hr⟩) _
      (ODEMatrixEnergy.dissipativePart_isHermitian _)
      (fun i j hij hji => by simp [ODEMatrixEnergy.dissipativePart_apply, hij, hji]) q.etaD
      hq.etaD_nonneg (hrD _) (hcD _)).trans
        (sqrt_le_lam0 q hq.γ_pos hq.γ_le q.etaD hq.etaD_nonneg))
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

end Inst

/-! ### The circuit and the solver -/

section Main

variable {Zs : Type*} [Fintype Zs] [DecidableEq Zs]

/-- **The preparation from time-indexed binary data for every `T ≥ 0`**: the direct source
assembly in the zero case, the released preparation from binary data otherwise, on the released
register. -/
def btprepC (q : PubT)
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b)
      Query))
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b) Query)) :
    List (NInstr (TNW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A)
      (Fin q.m ⊕ PY q.kx q.b) Query) :=
  if BTZeroCase q then tzprepC loadC wpC else q.prep loadC wpC

/-- **No matrix call in the zero case, time-indexed binary data**: if the loading and
weight-preparation circuits make no call of the oracle kinds `c` (for example the three
time-indexed binary sparse oracles), the protocol makes none in any history. -/
theorem binary_time_zero_no_matrix_calls (q : PubT) (hq : BTPublicOK0 q) (hz : BTZeroCase q)
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b)
      Query)) (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b) Query))
    (hwpV : ∀ i ∈ wpC, i.Valid) (c : Query → Bool)
    (h0 : nCallsN c loadC = 0) (h1 : nCallsN c wpC = 0) :
    (nprotocol (btprepC q loadC wpC) q.params.ratio (q.params.ratio_ge hq.g_ge)).worstCost
      (wCallN c) = 0 := by
  have hp := btparams_ok0 hq
  obtain ⟨-, -, -, -, -, hno, -, -⟩ := native_ode_time_solver_zero (S := Fin q.kx) (Zs := Zs)
    (Z := SZ4 q.kx q.b) (Y := Fin q.m ⊕ PY q.kx q.b) (J := Query) q.params q.params.a
    q.params.m q.params.r q.params.K q.params.l q.params.f q.ar.bT q.ar.bP q.ar.A hq.T_nonneg
    hq.g_ge hq.ε_pos hq.ε_half hp.lamH_nonneg hp.lamD_nonneg (btzeroCase_params hq hz) loadC
    hloadV wpC hwpV
  rw [btprepC, if_pos hz]
  exact hno c h0 h1

/-- **Dissipative ODE from time-indexed binary sparse data for every `T ≥ 0`** (Theorem
`ode:thm:gates`, time-dependent part, with its remark on zero time and a known zero generator).

For binary public data with `BTPublicOK0 q`, the protocol `nprotocol (btprepC q loadC wpC) (2g)`
on the released binary register has valid trials; one preparation uses at most
`if BTZeroCase q then |loadC| + 2 |wpC| else <the released binary count>` gates and at most
`if BTZeroCase q then calls(loadC) + 2 calls(wpC) else 12 d (2 [row] + 2 [col] + 2 [value]) +
calls(loadC) + 2 calls(wpC)` calls of every kind; every history uses at most `40 · 2g` times
these per preparation plus `20 · 2g (4 n + 3)` gates; the register has the released qubit count.
For every input with the released energy and accretivity promises of every sample, loading and
weight-preparation circuits within `ζs` with `24 d ζ + 3 ζs ≤ ν`, and the released remaining
conditions `PubT.Rest`, the protocol has the guarantees `NOutcome` against `x(T)`. -/
theorem binary_ode_time_solver_nonneg (q : PubT) (hq : BTPublicOK0 q) {X n : Type*}
    [Fintype n] [DecidableEq n] (D : Data (X × Fin (2 ^ q.m)) n (Cfg (VW q.b)) q.s)
    (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (hdec : ∀ e z, D.decode e z = (q.c0 : ℂ) * gauss z)
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b)
      Query)) (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b) Query))
    (hwpV : ∀ i ∈ wpC, i.Valid) :
    (∀ j, ∀ i ∈ trialN (btprepC q loadC wpC) j, i.Valid) ∧
    nGatesN (btprepC q loadC wpC) ≤
      (if BTZeroCase q then nGatesN loadC + 2 * nGatesN wpC
      else q.params.prepGates + 84 * q.params.d * (q.σ + 3) +
        6 * q.params.d * (2 * (28 * q.kx + 2) + 2 * q.ar.circ.length +
          (2 * q.ar.bP + q.ar.bT + 1)) + nGatesN loadC + 2 * nGatesN wpC) ∧
    (∀ c : Query → Bool, nCallsN c (btprepC q loadC wpC) ≤
      (if BTZeroCase q then nCallsN c loadC + 2 * nCallsN c wpC
      else 12 * q.params.d * (2 * (if c Query.rowLocation then 1 else 0) +
        2 * (if c Query.columnLocation then 1 else 0) + 2 * (if c Query.value then 1 else 0)) +
        nCallsN c loadC + 2 * nCallsN c wpC)) ∧
    ((nprotocol (btprepC q loadC wpC) q.params.ratio (q.params.ratio_ge hq.g_ge)).worstCost
        wGateN : ℝ) ≤
      40 * q.params.ratio * nGatesN (btprepC q loadC wpC) +
        20 * q.params.ratio * (4 * (Fintype.card q.params.W +
          Fintype.card (XW (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) + Fintype.card Zs + q.kx) +
          3) ∧
    (∀ c : Query → Bool,
      ((nprotocol (btprepC q loadC wpC) q.params.ratio (q.params.ratio_ge hq.g_ge)).worstCost
        (wCallN c) : ℝ) ≤ 40 * q.params.ratio * nCallsN c (btprepC q loadC wpC)) ∧
    Fintype.card (TNW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) =
      q.kx + 2 * (Fintype.card q.params.W +
        (6 * q.kx + 4 * q.b + q.ar.bT + q.ar.bP + q.ar.A + 3) + Fintype.card Zs) + q.kx + 1 ∧
    ∀ x : X,
      (∀ r i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaH ^ 2) →
      (∀ r j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaH ^ 2) →
      (∀ r i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaD ^ 2) →
      (∀ r j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaD ^ 2) →
      (∀ r, ∀ w : EuclideanSpace ℂ n, 0 ≤ (inner ℂ w (SparseStateOverlap.matrixOperator
        (ODEMatrixEnergy.dissipativePart (D.matrix (x, r))) w)).re) →
      ∀ (Jl : Bool × (Fin q.m → Bool) → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
        (Wp : Matrix (Cfg (Fin (q.m + 1))) (Cfg (Fin (q.m + 1))) ℂ)
        (G : ℝ → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ) (bf xs : ℝ → Reg (Fin q.kx) ℂ)
        (bs : ℕ → Reg (Fin q.kx) ℂ) (βG δG βb δb bmax ζs : ℝ),
      0 ≤ ζs →
      ApproxOn CleanX (nrun (primsT (R := ℂ) D en x) loadC) (liftB (loadIdeal Jl)) ζs →
      ApproxOn CleanX (nrun (primsT (R := ℂ) D en x) wpC) (liftB (matOp Wp)) ζs →
      24 * (q.params.d : ℝ) * q.ζ + 3 * ζs ≤ q.params.nu →
      q.Rest D en x Jl Wp G bf xs bs βG δG βb δb bmax →
      NOutcome (btprepC q loadC wpC) q.params.ratio q.ε (q.params.ratio_ge hq.g_ge)
        (primsT (R := ℂ) D en x) (xs q.T) := by
  by_cases hz : BTZeroCase q
  · have hp := btparams_ok0 hq
    obtain ⟨hV, hG, hC, hWG, hWC, -, hcardZ, hout⟩ := native_ode_time_solver_zero
      (S := Fin q.kx) (Zs := Zs) (Z := SZ4 q.kx q.b) (Y := Fin q.m ⊕ PY q.kx q.b) (J := Query)
      q.params q.params.a q.params.m q.params.r q.params.K q.params.l q.params.f q.ar.bT q.ar.bP
      q.ar.A hq.T_nonneg hq.g_ge hq.ε_pos hq.ε_half hp.lamH_nonneg hp.lamD_nonneg
      (btzeroCase_params hq hz) loadC hloadV wpC hwpV
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [btprepC, if_pos hz]
      exact hV
    · rw [btprepC, if_pos hz, if_pos hz]
      exact hG.le
    · intro c
      rw [btprepC, if_pos hz, if_pos hz]
      exact (hC c).le
    · rw [btprepC, if_pos hz, hG]
      rw [Fintype.card_fin] at hWG
      exact hWG
    · intro c
      rw [btprepC, if_pos hz, hC c]
      exact hWC c
    · rw [card_SZ4, Fintype.card_fin] at hcardZ
      exact hcardZ
    · intro x hrH hcH hrD hcD hPSD Jl Wp G bf xs bs βG δG βb δb bmax ζs hζs hload hwp hbud hR
      have hI := binary_tzInstanceOK q hq D en x hrH hcH hrD hcD hPSD Jl Wp G bf xs bs βG δG βb
        δb bmax hR
      have hd : 0 ≤ 24 * (q.params.d : ℝ) * q.ζ :=
        mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hq.ζ_pos.le
      rw [btprepC, if_pos hz]
      exact hout (primsT (R := ℂ) D en x) Jl Wp (HsT D en x) (LsT D en x) G bf xs bs βG δG βb δb
        bmax ζs (primsT_isUnitary D en x) hζs hload hwp (by linarith) hI
  · have hP := btpublicOK_of hq hz
    obtain ⟨hV, hG, hC, hWG, hWC, hcard, hout⟩ :=
      GateBinaryODETime.binary_ode_time_solver q hP D en hrange hdec loadC hloadV wpC hwpV
    refine ⟨?_, ?_, ?_, ?_, ?_, hcard, ?_⟩
    · rw [btprepC, if_neg hz]
      exact hV
    · rw [btprepC, if_neg hz, if_neg hz]
      exact hG
    · intro c
      rw [btprepC, if_neg hz, if_neg hz]
      exact hC c
    · rw [btprepC, if_neg hz]
      exact hWG
    · intro c
      rw [btprepC, if_neg hz]
      exact hWC c
    · intro x hrH hcH hrD hcD hPSD Jl Wp G bf xs bs βG δG βb δb bmax ζs hζs hload hwp hbud hR
      rw [btprepC, if_neg hz]
      exact hout x hrH hcH hrD hcD hPSD Jl Wp G bf xs bs βG δG βb δb bmax ζs hζs hload hwp hbud hR

end Main

end

end SparseHamiltonian.ZeroTimeGateODE
