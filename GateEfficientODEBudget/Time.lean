import GateEfficientODEBudget.Constant
import GateEfficientBinaryODETime.Solver

/-!
# The budget of the dissipative solver from binary data, time-dependent coefficients

For the public data `q : GateBinaryODETime.PubT` of the time-dependent solver from time-indexed
binary sparse data, the released time-dependent solver works internally with the ratio `2g` and
the accuracy `ε/2`: `ν = ε/(40000 g)`, `ℓ = log(40000 g/ε) = log(1/ν)`. Put
`Θ = T η_H + T η_D ℓ` and `q* = √s Θ + √(s Θ ℓ) + ℓ` (`qOf s T η_H η_D (2g) (ε/2)`). The public
rescaling is `γ = gammaOf T η_H η_D (2g) (ε/2) = min(1, √(Θ/ℓ))`, chosen from `T`, `η_H`, `η_D`,
`g` and `ε` before the binary data, the generator path, the mesh, the source circuits and the
instance.

* `binary_ode_time_sizes`: `τ ≤ 16 q*`, `d ≤ 4096 q*`, `2^r ≤ 4 (4096 q* + 1)`, `J ≤ 60 q* ℓ`,
  `2^l < 2 (60 q* ℓ + 2)`, and the finest schedule of the released simulator has
  `2^(simM τ ν) < 2 (2 + 64 q* + √(12288 q*³/ν))` slots: the mesh condition
  `steps τ (ν/3) ≤ 2^m` of `PubT.OK` holds for every `m ≥ simM τ ν`
  (`GateODE.Time.TParams.mesh_of_le`), and the mesh exponent `m` enters the counts only through
  the slot words; it also carries the regularity of the generator path.
* `binary_ode_time_budget`: for valid loading and weight-preparation circuits, in every history
  the native protocol (ratio `2g`) uses at most
  `73746000 g [q* (G_C + k_x + σ + m + r + ℓ (l+1) + 8) + G_src + A]` elementary gates
  (`G_src = |loadC| + 2 |wpC|`), at most `7864320 g q*` calls of each coherent sampled-time
  oracle besides `80 g` times the calls of `loadC` and twice those of `wpC`, its register has
  `22 k_x + 16 m + 24 r + 4 l + 8 b + 2 (bT + bP + A_arith) + 2 |Zs| + 47` qubits, and with the
  arithmetic budget `98304 q* ζ + 3 ζs ≤ ν` it has the guarantees of
  `GateBinaryODETime.binary_ode_time_solver`.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateODEBudget

noncomputable section
open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
open SparseHamiltonian.GateBinary SparseHamiltonian.GateBinaryODE
open SparseHamiltonian.GateBinaryODETime SparseHamiltonian.OracleCircuit
open ImprovedODEQueryBudget (precision logBudget radius)
open CayleyClockInterface (width moment)
open GateCircuit.Sim (simM simM_spec)
open NativeSparseBlockEncoding (Data Query)
open scoped InnerProduct

/-- The public conditions of the time-dependent solver from binary data give those of the size
bounds, for the internal ratio `2g` and accuracy `ε/2`. -/
theorem pubT_shapeOK (q : PubT) (hq : q.OK) :
    ShapeOK (q.s : ℝ) q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) where
  s_ge := by exact_mod_cast Nat.one_le_two_pow
  T_pos := hq.T_pos
  etaH_nonneg := hq.etaH_nonneg
  etaD_nonneg := hq.etaD_nonneg
  eta_pos := hq.eta_pos
  g_ge := by linarith [hq.g_ge]
  ε_pos := by linarith [hq.ε_pos]
  ε_le := by linarith [hq.ε_half]

/-- **The public sizes of the time-dependent solver from binary data with the public
rescaling** (Theorem `ode:thm:gates`, time-dependent part, the sizes behind equation
`ode:eq:gate-main`). For the public data `q` with `γ = gammaOf T η_H η_D (2g) (ε/2)` and
`q* = qOf s T η_H η_D (2g) (ε/2)`, `ℓ = log(1/ν)`: `τ ≤ 16 q*`, `d ≤ 4096 q*`,
`2^r ≤ 4 (4096 q* + 1)`, `J ≤ 60 q* ℓ`, `2^l < 2 (60 q* ℓ + 2)`, and the finest admissible mesh
of the released simulator has `2^(simM τ ν) < 2 (2 + 64 q* + √(12288 q*³/ν))` slots. -/
theorem binary_ode_time_sizes (q : PubT) (hq : q.OK)
    (hγ : q.γ = gammaOf q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) :
    q.params.tau ≤ 16 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) ∧
    (q.params.d : ℝ) ≤ 4096 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) ∧
    ((2 ^ simM q.params.tau q.params.nu : ℕ) : ℝ) <
      2 * (2 + 64 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) +
        Real.sqrt (12288 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) ^ 3 / q.params.nu)) ∧
    ((2 ^ q.params.r : ℕ) : ℝ) ≤ 4 * (4096 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) + 1) ∧
    (q.params.J : ℝ) ≤
      60 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * logBudget (2 * q.g) (q.ε / 2) ∧
    ((2 ^ q.params.l : ℕ) : ℝ) <
      2 * (60 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * logBudget (2 * q.g) (q.ε / 2) +
        2) := by
  have h := pubT_shapeOK q hq
  have hp := q.params_ok hq
  have hν := hp.nu_pos
  have hτ : q.params.tau ≤ 16 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) := by
    have e : q.params.tau = q.T * (Real.sqrt (4 * (q.s : ℝ)) * q.etaH / q.γ +
        radius (2 * q.g) (q.ε / 2) * (Real.sqrt (4 * (q.s : ℝ)) * q.etaD / q.γ)) := rfl
    rw [e, hγ]
    exact h.tau_le
  have hτ0 : 0 ≤ q.params.tau := hp.tau_pos.le
  have hd : (q.params.d : ℝ) ≤ 4096 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) := by
    have hdeg := q.params.degree_bound hp
    change (q.params.d : ℝ) ≤ 128 * (q.params.tau * moment q.γ +
      width (4 * (q.s : ℝ)) q.γ * (1 + Real.log (3 / precision (2 * q.g) (q.ε / 2)))) at hdeg
    rw [hγ] at hdeg
    exact hdeg.trans (h.degree_shape_le _ hτ0 hτ)
  have hJ : (q.params.J : ℝ) ≤
      60 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * logBudget (2 * q.g) (q.ε / 2) := by
    have hJ := q.params.J_le hp
    change (q.params.J : ℝ) ≤ radius (2 * q.g) (q.ε / 2) *
      (q.T * (Real.sqrt (4 * (q.s : ℝ)) * q.etaD / q.γ) +
        2 * Real.log (512 / precision (2 * q.g) (q.ε / 2))) / Real.pi + 3 at hJ
    rw [hγ] at hJ
    exact hJ.trans h.grid_le
  refine ⟨hτ, hd, ?_, ?_, hJ, ?_⟩
  · -- the finest schedule
    have hm : ((2 ^ simM q.params.tau q.params.nu : ℕ) : ℝ) <
        2 * (TimeSchedule.steps q.params.tau (q.params.nu / 3) : ℝ) := by
      exact_mod_cast (simM_spec q.params.tau q.params.nu).2
    have hs := steps_le q.params.tau _ q.params.nu hτ0 hτ hν
    linarith
  · -- the reuse word
    have hr' : ((2 ^ q.params.r : ℕ) : ℝ) ≤ 4 * ((q.params.d : ℝ) + 1) := by
      exact_mod_cast q.params.r_bounds.2
    linarith
  · -- the LCHS word
    have hl : ((2 ^ q.params.l : ℕ) : ℝ) < 2 * ((q.params.J : ℝ) + 2) := by
      exact_mod_cast q.params.l_bounds.2
    linarith

section Budget

variable {X n : Type*} [Fintype n] [DecidableEq n] {Zs : Type*} [Fintype Zs] [DecidableEq Zs]

/-- **The gate, call and qubit budget of the time-dependent solver from binary data with the
public rescaling** (Theorem `ode:thm:gates`, time-dependent part, equations `ode:eq:gate-main`
and `ode:eq:gate-space` before finite-gate-set synthesis). Let the public data `q` have
`γ = gammaOf T η_H η_D (2g) (ε/2)`, and put `q* = qOf s T η_H η_D (2g) (ε/2)`, `ℓ = log(1/ν)`.
For the time-indexed binary data and the valid circuits `loadC`, `wpC` of
`binary_ode_time_solver`, in every history the native protocol (ratio `2g`)

* uses at most `73746000 g [q* (G_C + k_x + σ + m + r + ℓ (l+1) + 8) + G_src + A]` elementary
  gates, `G_C = 2 (28 k_x + 2) + 2 |arith| + 2 bP + bT + 1`, `G_src = |loadC| + 2 |wpC|` and
  `A = k_x + |Zs| + (6 k_x + 4 b) + bT + bP + A_arith`;
* makes at most `7864320 g q*` calls of each coherent sampled-time oracle besides `80 g` times
  the calls of `loadC` and twice those of `wpC`;

its register has `22 k_x + 16 m + 24 r + 4 l + 8 b + 2 (bT + bP + A_arith) + 2 |Zs| + 47`
qubits; and for every input and instance as in `binary_ode_time_solver`, with the arithmetic
budget `98304 q* ζ + 3 ζs ≤ ν`, it has the guarantees `NOutcome`. -/
theorem binary_ode_time_budget (q : PubT) (hq : q.OK)
    (hγ : q.γ = gammaOf q.T q.etaH q.etaD (2 * q.g) (q.ε / 2))
    (D : Data (X × Fin (2 ^ q.m)) n (Cfg (VW q.b)) q.s) (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (hdec : ∀ e z, D.decode e z = (q.c0 : ℂ) * gauss z)
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b)
      Query)) (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b) Query))
    (hwpV : ∀ i ∈ wpC, i.Valid) :
    ((nprotocol (q.prep loadC wpC) q.params.ratio (q.params.ratio_ge hq.g_ge)).worstCost
        wGateN : ℝ) ≤
      73746000 * q.g * (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
          (((2 * (28 * q.kx + 2) + 2 * q.ar.circ.length + (2 * q.ar.bP + q.ar.bT + 1) : ℕ) : ℝ) +
            q.kx + q.σ + q.params.m + q.params.r +
            logBudget (2 * q.g) (q.ε / 2) * ((q.params.l : ℝ) + 1) + 8) +
        ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) +
        ((q.kx : ℝ) + Fintype.card Zs + ((6 * q.kx + 4 * q.b : ℕ) : ℝ) + q.ar.bT + q.ar.bP +
          q.ar.A)) ∧
    (∀ c : Query → Bool,
      ((nprotocol (q.prep loadC wpC) q.params.ratio (q.params.ratio_ge hq.g_ge)).worstCost
        (wCallN c) : ℝ) ≤
      7864320 * q.g * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
          ((if c Query.rowLocation then 1 else 0) + (if c Query.columnLocation then 1 else 0) +
            (if c Query.value then 1 else 0)) +
        80 * q.g * ((nCallsN c loadC : ℝ) + 2 * nCallsN c wpC)) ∧
    Fintype.card (TNW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) =
      22 * q.kx + 16 * q.params.m + 24 * q.params.r + 4 * q.params.l + 8 * q.b +
        2 * (q.ar.bT + q.ar.bP + q.ar.A) + 2 * Fintype.card Zs + 47 ∧
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
      98304 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * q.ζ + 3 * ζs ≤ q.params.nu →
      q.Rest D en x Jl Wp G bf xs bs βG δG βb δb bmax →
      NOutcome (q.prep loadC wpC) q.params.ratio q.ε (q.params.ratio_ge hq.g_ge)
        (primsT (R := ℂ) D en x) (xs q.T) := by
  have h := pubT_shapeOK q hq
  obtain ⟨-, hd, -, -, hJ, -⟩ := binary_ode_time_sizes q hq hγ
  have hq1 := h.one_le_q
  have hℓ := h.ell_ge
  have hg0 : 0 ≤ q.g := le_trans zero_le_one hq.g_ge
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- gates
    refine (binary_ode_time_gate_count q hq loadC hloadV wpC hwpV).trans
      ((gate_budget_arith' 18000 q.g _ _ _ _ _ _ _ _ (by norm_num) hg0 hq1 hℓ hd hJ
        (Nat.cast_nonneg _) (by positivity) (by positivity) (by positivity)).trans
        (le_of_eq ?_))
    push_cast
    ring
  · -- calls
    intro c
    obtain ⟨-, -, hC, -, hWC, -⟩ := binary_ode_time_counts q hq loadC hloadV wpC hwpV
    have hI0 : (0 : ℝ) ≤ (if c Query.rowLocation then 1 else 0) +
        (if c Query.columnLocation then 1 else 0) + (if c Query.value then 1 else 0) := by
      split_ifs <;> norm_num
    have hc : (nCallsN c (q.prep loadC wpC) : ℝ) ≤ 12 * (q.params.d : ℝ) *
        (2 * ((if c Query.rowLocation then 1 else 0) + (if c Query.columnLocation then 1 else 0)
          + (if c Query.value then 1 else 0))) +
        ((nCallsN c loadC : ℝ) + 2 * nCallsN c wpC) := by
      have h1 : (nCallsN c (q.prep loadC wpC) : ℝ) ≤ ((12 * q.params.d *
          (2 * (if c Query.rowLocation then 1 else 0) +
            2 * (if c Query.columnLocation then 1 else 0) +
            2 * (if c Query.value then 1 else 0)) +
          nCallsN c loadC + 2 * nCallsN c wpC : ℕ) : ℝ) := by
        exact_mod_cast hC c
      refine h1.trans (le_of_eq ?_)
      push_cast
      ring
    have hr0 : 0 ≤ q.params.ratio := by
      show 0 ≤ 2 * q.g
      linarith
    refine (hWC c).trans ((call_budget_arith 40 q.params.ratio _ _ _ _ _ (by norm_num) hr0 hI0
      hd hc).trans (le_of_eq ?_))
    show 98304 * 40 * (2 * q.g) * _ * _ + 40 * (2 * q.g) * _ = _
    ring
  · -- qubits
    obtain ⟨-, -, -, -, -, hcard⟩ := binary_ode_time_counts q hq loadC hloadV wpC hwpV
    rw [hcard, q.params.card_W]
    show q.kx + 2 * (4 * (q.kx + 3) + 8 * q.params.m + 12 * q.params.r + 2 * q.params.l + 8 +
      (6 * q.kx + 4 * q.b + q.ar.bT + q.ar.bP + q.ar.A + 3) + Fintype.card Zs) + q.kx + 1 = _
    ring
  · -- guarantees
    obtain ⟨-, -, -, -, -, -, hout⟩ :=
      binary_ode_time_solver q hq D en hrange hdec loadC hloadV wpC hwpV
    intro x hrH hcH hrD hcD hPSD Jl Wp G bf xs bs βG δG βb δb bmax ζs hζs hload hwp hbud hR
    refine hout x hrH hcH hrD hcD hPSD Jl Wp G bf xs bs βG δG βb δb bmax ζs hζs hload hwp ?_ hR
    have hζ := hq.ζ_pos.le
    have := mul_le_mul_of_nonneg_right hd hζ
    linarith

end Budget

end

end SparseHamiltonian.GateODEBudget
