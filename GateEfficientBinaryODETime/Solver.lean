import GateEfficientBinaryODETime.Pub
import GateEfficientNative.Corollaries

/-!
# Theorem `ode:thm:gates` from time-indexed binary sparse data, time-dependent coefficients

The native time-dependent solver `GateNative.native_ode_time_solver` takes as hypotheses the
gates of `U_J`, a label- and slot-selected native private operation with its compute circuit,
decoder and arithmetic (`NativeOK`, `ArithOK`), and the released instance conditions
(`GateODE.Time.TParams.InstanceOK`). For time-indexed binary sparse data (the sample of slot `r`
on input `x` is `D.matrix (x, r)`; `k`-qubit indices, `s = 2^σ` slots on the lowest `σ` index
bits, entries `c₀ (X + i Y)` with `b`-bit two's complement components) all of them are
constructed here from the public data `q : PubT` (`PubT.nd`, `PubT.ar`, `PubT.UJg`), and the
selection conditions of the instance are derived from row and column energy bounds and the
accretivity of every sample (`PubT.instanceOK`); the loading and weight-preparation circuits
(with their accuracy `ζs` and the budget `24 d ζ + 3 ζs ≤ ν`) and the source, path and target
conditions of the instance (`PubT.Rest`) remain hypotheses.

* `binary_ode_time_counts`: the native preparation depends only on the public data and the two
  source circuits; its trials are valid and its gate, call and qubit counts are explicit.
* `binary_ode_time_solver`: in addition, the protocol succeeds with probability at least `2/3`
  and its conditional output is within trace distance `ε` of `x(T)/‖x(T)‖`.
* `binary_ode_time_gate_count`: the explicit worst-case gate count.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateBinaryODETime

noncomputable section
open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
open SparseHamiltonian.GateBinary SparseHamiltonian.GateBinaryODE SparseHamiltonian.OracleCircuit
open NativeSparseBlockEncoding (Data Query)
open scoped InnerProduct

section Main

variable {X n : Type*} [Fintype n] [DecidableEq n] {Zs : Type*} [Fintype Zs] [DecidableEq Zs]

/-- **The counts of the time-dependent native solver from binary data.** For valid loading and
weight-preparation circuits `loadC`, `wpC`, the native preparation `q.prep loadC wpC` (`U_J`
from `σ + 3` Hadamard gates, the binary compute circuit reading the slot wires, and the
reversible arithmetic with the slot comparator) depends only on the public data and the two
source circuits; its trials are valid; it has at most
`prepGates + 84 d (σ + 3) + 6 d (2 (28 k + 2) + 2 |arith| + 2 bP + bT + 1) + |loadC| + 2 |wpC|`
elementary gates (with the arithmetic counts `PubT.ar_counts`) and at most `24 d` calls of each
coherent sampled-time oracle besides those of the source circuits; in every history the protocol
(ratio `2g`) uses at most `80 g N + 40 g (4 (|W| + |XW| + |Zs| + k) + 3)` elementary gates (`N`
the gates of the preparation) and at most `80 g` times the calls of the preparation; and its
register has `k + 2 (|W| + (6 k + 4 b + bT + bP + A + 3) + |Zs|) + k + 1` qubits. -/
theorem binary_ode_time_counts (q : PubT) (hq : q.OK)
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b)
      Query)) (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b) Query))
    (hwpV : ∀ i ∈ wpC, i.Valid) :
    (∀ j, ∀ i ∈ trialN (q.prep loadC wpC) j, i.Valid) ∧
    nGatesN (q.prep loadC wpC) ≤ q.params.prepGates + 84 * q.params.d * (q.σ + 3) +
      6 * q.params.d * (2 * (28 * q.kx + 2) + 2 * q.ar.circ.length +
        (2 * q.ar.bP + q.ar.bT + 1)) + nGatesN loadC + 2 * nGatesN wpC ∧
    (∀ c : Query → Bool, nCallsN c (q.prep loadC wpC) ≤
      12 * q.params.d * (2 * (if c Query.rowLocation then 1 else 0) +
        2 * (if c Query.columnLocation then 1 else 0) + 2 * (if c Query.value then 1 else 0)) +
        nCallsN c loadC + 2 * nCallsN c wpC) ∧
    ((nprotocol (q.prep loadC wpC) q.params.ratio (q.params.ratio_ge hq.g_ge)).worstCost
        wGateN : ℝ) ≤
      40 * q.params.ratio * nGatesN (q.prep loadC wpC) +
        20 * q.params.ratio * (4 * (Fintype.card q.params.W +
          Fintype.card (XW (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) + Fintype.card Zs + q.kx) +
          3) ∧
    (∀ c : Query → Bool,
      ((nprotocol (q.prep loadC wpC) q.params.ratio (q.params.ratio_ge hq.g_ge)).worstCost
        (wCallN c) : ℝ) ≤ 40 * q.params.ratio * nCallsN c (q.prep loadC wpC)) ∧
    Fintype.card (TNW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) =
      q.kx + 2 * (Fintype.card q.params.W +
        (6 * q.kx + 4 * q.b + q.ar.bT + q.ar.bP + q.ar.A + 3) + Fintype.card Zs) + q.kx + 1 := by
  obtain ⟨hV, hG, hC, hW, hWC, hcard, -⟩ :=
    native_ode_time_solver q.params (q.params_ok hq) q.UJg (hadUJ4_ok q.σ q.hσ) q.nd q.nd_public
      q.ar q.ζ hq.ζ_pos.le (q.ar_ok hq) loadC hloadV wpC hwpV
  have hVg : nGatesN q.nd.V = 28 * q.kx + 2 := odeOpT_nGates _ _ _ _ _
  have hVc : ∀ c : Query → Bool, nCallsN c q.nd.V = 2 * (if c Query.rowLocation then 1 else 0) +
      2 * (if c Query.columnLocation then 1 else 0) + 2 * (if c Query.value then 1 else 0) :=
    fun c => odeOpT_nCalls _ _ _ _ _ c
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

/-- **Native gate-efficient dissipative ODE solver from time-indexed binary sparse data,
time-dependent coefficients** (Theorem `ode:thm:gates`, time-dependent part, before finite-set
synthesis).

Let the public data `q` satisfy the public conditions (including the mesh condition
`steps τ (ν/3) ≤ 2^m` of the released solver), and let the time-indexed native sparse data `D`
of the samples `M_r = D.matrix (x, r)` have `k`-bit indices (`en`), `s = 2^σ` slots that are
exactly the index words supported on the lowest `σ` bits (`hrange`), and entries stored as two
`b`-bit two's complement components with decoder `c₀ (X + i Y)` (`hdec`). For valid loading and
weight-preparation circuits, the native preparation `q.prep loadC wpC` depends only on the public
data and the two circuits, its trials are valid, and its counts and those of the protocol are
those of `binary_ode_time_counts`. For every input `x` whose samples have Hamiltonian and
dissipative parts with row and column energies at most `η_H²` and `η_D²` and accretive
dissipative parts, every loading `Jl` and weight preparation `Wp` approximated within `ζs` by the
two circuits with `24 d ζ + 3 ζs ≤ ν`, and every generator path `G`, forcing `b`, solution `x`
and forcing samples `b_r` satisfying the remaining conditions `PubT.Rest` (with `G` within `δG`
of the lifted samples `M̂_r` at the slot times), the protocol succeeds with probability at least
`2/3` and its conditional output is within trace distance `ε` of `x(T)/‖x(T)‖`. -/
theorem binary_ode_time_solver (q : PubT) (hq : q.OK)
    (D : Data (X × Fin (2 ^ q.m)) n (Cfg (VW q.b)) q.s) (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (hdec : ∀ e z, D.decode e z = (q.c0 : ℂ) * gauss z)
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b)
      Query)) (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b) Query))
    (hwpV : ∀ i ∈ wpC, i.Valid) :
    (∀ j, ∀ i ∈ trialN (q.prep loadC wpC) j, i.Valid) ∧
    nGatesN (q.prep loadC wpC) ≤ q.params.prepGates + 84 * q.params.d * (q.σ + 3) +
      6 * q.params.d * (2 * (28 * q.kx + 2) + 2 * q.ar.circ.length +
        (2 * q.ar.bP + q.ar.bT + 1)) + nGatesN loadC + 2 * nGatesN wpC ∧
    (∀ c : Query → Bool, nCallsN c (q.prep loadC wpC) ≤
      12 * q.params.d * (2 * (if c Query.rowLocation then 1 else 0) +
        2 * (if c Query.columnLocation then 1 else 0) + 2 * (if c Query.value then 1 else 0)) +
        nCallsN c loadC + 2 * nCallsN c wpC) ∧
    ((nprotocol (q.prep loadC wpC) q.params.ratio (q.params.ratio_ge hq.g_ge)).worstCost
        wGateN : ℝ) ≤
      40 * q.params.ratio * nGatesN (q.prep loadC wpC) +
        20 * q.params.ratio * (4 * (Fintype.card q.params.W +
          Fintype.card (XW (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) + Fintype.card Zs + q.kx) +
          3) ∧
    (∀ c : Query → Bool,
      ((nprotocol (q.prep loadC wpC) q.params.ratio (q.params.ratio_ge hq.g_ge)).worstCost
        (wCallN c) : ℝ) ≤ 40 * q.params.ratio * nCallsN c (q.prep loadC wpC)) ∧
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
      NOutcome (q.prep loadC wpC) q.params.ratio q.ε (q.params.ratio_ge hq.g_ge)
        (primsT (R := ℂ) D en x) (xs q.T) := by
  obtain ⟨hV, hG, hC, hW, hWC, hcard⟩ := binary_ode_time_counts q hq loadC hloadV wpC hwpV
  obtain ⟨-, -, -, -, -, -, hout⟩ :=
    native_ode_time_solver q.params (q.params_ok hq) q.UJg (hadUJ4_ok q.σ q.hσ) q.nd q.nd_public
      q.ar q.ζ hq.ζ_pos.le (q.ar_ok hq) loadC hloadV wpC hwpV
  refine ⟨hV, hG, hC, hW, hWC, hcard, ?_⟩
  intro x hrH hcH hrD hcD hPSD Jl Wp G bf xs bs βG δG βb δb bmax ζs hζs hload hwp hbud hR
  exact hout (primsT (R := ℂ) D en x) (privFamT q.params D en x q.rho q.γ) Jl Wp (HsT D en x)
    (LsT D en x) G bf xs bs βG δG βb δb bmax ζs (primsT_isUnitary D en x)
    (q.nativeOK hq D en hrange hdec x) hζs hload hwp hbud
    (q.instanceOK hq D en hrange x hrH hcH hrD hcD hPSD Jl Wp G bf xs bs βG δG βb δb bmax hR)

/-- **The worst-case gate count of the time-dependent native solver from binary data** (the
explicit count underlying equation `ode:eq:gate-main`, for time-indexed binary data): in every
history the protocol uses at most
`18000 g [(d+1)(a + m + r + 1 + C_J + G_C) + (J+2)(l+1) + G_src + A]` elementary gates, with
`a = k + 3`, `C_J = σ + 3` the Hadamard gates of `U_J`,
`G_C = 2 (28 k + 2) + 2 |arith| + 2 bP + bT + 1` the gates of one native private call (with the
arithmetic counts `PubT.ar_counts`), `G_src = |loadC| + 2 |wpC|` and
`A = k + |Zs| + (6 k + 4 b) + bT + bP + A_arith` the system, source-scratch, private-scratch and
arithmetic wires; `d`, `m`, `r`, `l` and `J` are the released public sizes. -/
theorem binary_ode_time_gate_count (q : PubT) (hq : q.OK)
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b)
      Query)) (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b) Query))
    (hwpV : ∀ i ∈ wpC, i.Valid) :
    ((nprotocol (q.prep loadC wpC) q.params.ratio (q.params.ratio_ge hq.g_ge)).worstCost
        wGateN : ℝ) ≤
      18000 * q.g * (((q.params.d : ℝ) + 1) * (((q.kx + 3 : ℕ) : ℝ) + q.params.m +
          q.params.r + 1 + ((q.σ + 3 : ℕ) : ℝ) + ((2 * (28 * q.kx + 2) + 2 * q.ar.circ.length +
            (2 * q.ar.bP + q.ar.bT + 1) : ℕ) : ℝ)) +
        ((q.params.J : ℝ) + 2) * ((q.params.l : ℝ) + 1) +
        ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) +
        ((q.kx : ℝ) + Fintype.card Zs + ((6 * q.kx + 4 * q.b : ℕ) : ℝ) + q.ar.bT + q.ar.bP +
          q.ar.A)) := by
  have h := native_ode_time_gate_count q.params (q.params_ok hq) q.UJg (hadUJ4_ok q.σ q.hσ) q.nd
    q.nd_public q.ar q.ζ hq.ζ_pos.le (q.ar_ok hq) loadC hloadV wpC hwpV
  have hVg : nGatesN q.nd.V = 28 * q.kx + 2 := odeOpT_nGates _ _ _ _ _
  have hUJl : q.UJg.length = q.σ + 3 := hadUJ4_length q.σ q.hσ
  rw [privGates, hVg, hUJl, Fintype.card_fin, card_SZ4] at h
  exact h

end Main

end

end SparseHamiltonian.GateBinaryODETime
