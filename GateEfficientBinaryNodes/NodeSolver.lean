import GateEfficientBinaryNodes.NodePub
import GateEfficientNative.Corollaries

/-!
# Theorem `ode:thm:gates` from binary data with coherently computed source nodes

The native protocol `nprotocol (prepQN q μ nd N loadC wpC) (2g)` is the released protocol of
`GateNative.native_ode_time_solver` on the native branch operation `ndQN` for computed nodes and
its arithmetic `arQN`. Its validity and counts are those of the released solver with one private
call of `G_C = 2 (|N| + |addrGT| + 28 k + 2) + 2 |arith| + 2 bP + bT + 1` gates (`|N|` the gates
of the node program, `|addrGT| ≤ 13 (μ + m + 14)(m + 5)` those of the address program); its
guarantees follow from the integrated instance `instanceN`.

* `binary_nodes_counts`, `binary_nodes_gate_count`: validity and counts of the native protocol,
  and the explicit worst-case gate count.
* `binary_nodes_solver`: the guarantees `NOutcome` for every input whose samples at the data grid
  points read by the branches satisfy `SampleOK` and every instance satisfying `RestN`.
* `binary_nodes_synth_counts`, `binary_nodes_solver_synth`: synthesis of every trial over a finite
  gate set, its validity, gate-set membership and counts, and the guarantee `GateSynth.SOutcome`.
* `binary_nodes_trials_counts`, `binary_nodes_solver_trials`: synthesis of the preparation with
  exact reflections, its gate-set membership and counts, and the guarantees `NOutcome` (every
  successful trial within `ε/500` of `x(T)/‖x(T)‖` up to a global phase).
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateBinaryNodes

noncomputable section
open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
open SparseHamiltonian.GateBinary SparseHamiltonian.GateBinaryODE SparseHamiltonian.OracleCircuit
open SparseHamiltonian.GateBinaryODETime (PubT)
open SparseHamiltonian.GateODE.Time (TParams TOracles)
open SparseHamiltonian.GateSynthTrials (synthPrep STW SX)
open NativeSparseBlockEncoding (Data Query)
open scoped InnerProduct

section Counts

variable {Zs : Type*} [Fintype Zs] [DecidableEq Zs] {Zn : Type} [Fintype Zn] [DecidableEq Zn]

omit [Fintype Zn] [DecidableEq Zn] in
/-- The gates of one native private call for computed nodes. -/
theorem privGatesQN (q : PubT) (mu nd : ℕ) (hnd : nd ≤ mu + q.m) (N : NodeProg q.m mu Zn) :
    privGates (ndQN q mu nd hnd N) (arQN q mu Zn) =
      2 * (N.gates.length + (addrGT q.m q.params.l mu).length + (28 * q.kx + 2)) +
        2 * (arQN q mu Zn).circ.length + (2 * (arQN q mu Zn).bP + (arQN q mu Zn).bT + 1) := by
  rw [privGates, ndQN_nGates]

omit [DecidableEq Zn] in
/-- The scratch wires of the branch operation for computed nodes: the node register and scratch,
the address registers and the scratch of the constant-coefficient operation. -/
theorem card_ZN (m mu k b : ℕ) : Fintype.card (ZaN m mu Zn ⊕ SZ4 k b) =
    (mu + Fintype.card Zn + (1 + 2 * (mu + m + 14) + (4 * m + 62) * (mu + m + 14))) +
      (6 * k + 4 * b) := by
  rw [Fintype.card_sum, card_ZaN, card_SZ4]

/-- **The counts of the native solver from binary data with computed nodes.** For a node
program `N` satisfying `NodeProg.OK` and valid loading and weight-preparation circuits `loadC`,
`wpC`, the native preparation `prepQN q μ nd N loadC wpC` depends only on the public data, the
node program and the two circuits; its trials are valid; it has at most
`prepGates + 84 d (σ + 3) + 6 d G_C + |loadC| + 2 |wpC|` elementary gates,
`G_C = 2 (|N| + |addrGT| + 28 k + 2) + 2 |arith| + 2 bP + bT + 1` the gates of one private call
(the node program, the address program and the constant-coefficient compute circuit, all
computed and uncomputed), and at most `24 d` calls of each coherent sampled-time oracle on the
data grid besides those of the source circuits; in every history the protocol (ratio `2g`) uses
at most `80 g N_P + 40 g (4 (|W| + |XW| + |Zs| + k) + 3)` elementary gates (`N_P` the gates of the
preparation) and at most `80 g` times the calls of the preparation; its register has
`k + 2 (|W| + (|Z_N| + 6 k + 4 b + bT + bP + A + 3) + |Zs|) + k + 1` qubits, with
`|Z_N| = μ + |Zn| + 1 + 2 (μ + m + 14) + (4m + 62)(μ + m + 14)` node and address wires. -/
theorem binary_nodes_counts (q : PubT) (hq : q.OK) (mu nd : ℕ) (hnd : nd ≤ mu + q.m)
    (N : NodeProg q.m mu Zn) (hN : N.OK)
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin nd ⊕ PY q.kx q.b)
      Query)) (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin nd ⊕ PY q.kx q.b) Query))
    (hwpV : ∀ i ∈ wpC, i.Valid) :
    (∀ j, ∀ i ∈ trialN (prepQN q mu nd hnd N loadC wpC) j, i.Valid) ∧
    nGatesN (prepQN q mu nd hnd N loadC wpC) ≤ q.params.prepGates + 84 * q.params.d * (q.σ + 3) +
      6 * q.params.d * (2 * (N.gates.length + (addrGT q.m q.params.l mu).length +
        (28 * q.kx + 2)) + 2 * (arQN q mu Zn).circ.length +
        (2 * (arQN q mu Zn).bP + (arQN q mu Zn).bT + 1)) + nGatesN loadC + 2 * nGatesN wpC ∧
    (∀ c : Query → Bool, nCallsN c (prepQN q mu nd hnd N loadC wpC) ≤
      12 * q.params.d * (2 * (if c Query.rowLocation then 1 else 0) +
        2 * (if c Query.columnLocation then 1 else 0) + 2 * (if c Query.value then 1 else 0)) +
        nCallsN c loadC + 2 * nCallsN c wpC) ∧
    ((nprotocol (prepQN q mu nd hnd N loadC wpC) q.params.ratio
        (q.params.ratio_ge hq.g_ge)).worstCost wGateN : ℝ) ≤
      40 * q.params.ratio * nGatesN (prepQN q mu nd hnd N loadC wpC) +
        20 * q.params.ratio * (4 * (Fintype.card q.params.W +
          Fintype.card (XW (ZaN q.m mu Zn ⊕ SZ4 q.kx q.b) (arQN q mu Zn).bT (arQN q mu Zn).bP
            (arQN q mu Zn).A) + Fintype.card Zs + q.kx) + 3) ∧
    (∀ c : Query → Bool,
      ((nprotocol (prepQN q mu nd hnd N loadC wpC) q.params.ratio
        (q.params.ratio_ge hq.g_ge)).worstCost (wCallN c) : ℝ) ≤
        40 * q.params.ratio * nCallsN c (prepQN q mu nd hnd N loadC wpC)) ∧
    Fintype.card (TNW q.params (Fin q.kx) Zs (ZaN q.m mu Zn ⊕ SZ4 q.kx q.b) (arQN q mu Zn).bT
        (arQN q mu Zn).bP (arQN q mu Zn).A) =
      q.kx + 2 * (Fintype.card q.params.W +
        ((mu + Fintype.card Zn + (1 + 2 * (mu + q.m + 14) + (4 * q.m + 62) * (mu + q.m + 14))) +
          (6 * q.kx + 4 * q.b) + (arQN q mu Zn).bT + (arQN q mu Zn).bP + (arQN q mu Zn).A + 3) +
        Fintype.card Zs) + q.kx + 1 := by
  obtain ⟨hV, hG, hC, hW, hWC, hcard, -⟩ :=
    native_ode_time_solverBI q.params (q.params_ok hq) q.UJg (hadUJ4_ok q.σ q.hσ)
      (ndQN q mu nd hnd N) (ndQN_public q mu nd hnd N hN) (arQN q mu Zn) q.ζ hq.ζ_pos.le
      (arQN_ok q mu nd hnd N hq) loadC hloadV wpC hwpV
  have hUJl : q.UJg.length = q.σ + 3 := hadUJ4_length q.σ q.hσ
  refine ⟨hV, ?_, ?_, ?_, hWC, ?_⟩
  · rw [privGatesQN, hUJl] at hG
    exact hG
  · intro c
    have h := hC c
    rw [ndQN_nCalls] at h
    exact h
  · rw [Fintype.card_fin] at hW
    exact hW
  · rw [hcard, card_ZN, Fintype.card_fin]

/-- **The worst-case gate count of the native solver from binary data with computed nodes** (the
explicit count underlying equation `ode:eq:gate-main`): in every history the protocol uses at
most `18000 g [(d+1)(a + m + r + 1 + C_J + G_C) + (J+2)(l+1) + G_src + A]` elementary gates, with
`a = k + 3`, `C_J = σ + 3`, `G_C = 2 (|N| + |addrGT| + 28 k + 2) + 2 |arith| + 2 bP + bT + 1` the
gates of one native private call, `G_src = |loadC| + 2 |wpC|` and
`A = k + |Zs| + (|Z_N| + 6 k + 4 b) + bT + bP + A_arith`. -/
theorem binary_nodes_gate_count (q : PubT) (hq : q.OK) (mu nd : ℕ) (hnd : nd ≤ mu + q.m)
    (N : NodeProg q.m mu Zn) (hN : N.OK)
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin nd ⊕ PY q.kx q.b)
      Query)) (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin nd ⊕ PY q.kx q.b) Query))
    (hwpV : ∀ i ∈ wpC, i.Valid) :
    ((nprotocol (prepQN q mu nd hnd N loadC wpC) q.params.ratio
        (q.params.ratio_ge hq.g_ge)).worstCost wGateN : ℝ) ≤
      18000 * q.g * (((q.params.d : ℝ) + 1) * (((q.kx + 3 : ℕ) : ℝ) + q.params.m +
          q.params.r + 1 + ((q.σ + 3 : ℕ) : ℝ) +
          ((2 * (N.gates.length + (addrGT q.m q.params.l mu).length + (28 * q.kx + 2)) +
            2 * (arQN q mu Zn).circ.length + (2 * (arQN q mu Zn).bP + (arQN q mu Zn).bT + 1) :
              ℕ) : ℝ)) +
        ((q.params.J : ℝ) + 2) * ((q.params.l : ℝ) + 1) +
        ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) +
        ((q.kx : ℝ) + Fintype.card Zs +
          (((mu + Fintype.card Zn + (1 + 2 * (mu + q.m + 14) + (4 * q.m + 62) * (mu + q.m + 14))) +
            (6 * q.kx + 4 * q.b) : ℕ) : ℝ) + (arQN q mu Zn).bT + (arQN q mu Zn).bP +
          (arQN q mu Zn).A)) := by
  have h := native_ode_time_gate_count q.params (q.params_ok hq) q.UJg (hadUJ4_ok q.σ q.hσ)
    (ndQN q mu nd hnd N) (ndQN_public q mu nd hnd N hN) (arQN q mu Zn) q.ζ hq.ζ_pos.le
    (arQN_ok q mu nd hnd N hq) loadC hloadV wpC hwpV
  have hUJl : q.UJg.length = q.σ + 3 := hadUJ4_length q.σ q.hσ
  rw [privGatesQN, hUJl, Fintype.card_fin, card_ZN] at h
  exact h

end Counts

/-! ### The solvers -/

section Solvers

variable {X n : Type*} [Fintype n] [DecidableEq n] {Zs : Type*} [Fintype Zs] [DecidableEq Zs]
variable {Zn : Type} [Fintype Zn] [DecidableEq Zn]
variable {Xa : Type*} [Fintype Xa] [DecidableEq Xa] {𝒢 : Set GateSynth.Kind} {len : ℝ → ℕ}

/-- **Native gate-efficient dissipative ODE solver from time-indexed binary sparse data with
coherently computed source nodes** (Theorem `ode:thm:gates`, time-dependent part, with general
source nodes, the branch-dependent meshes of Lemma `ode:lem:gate-select` and the integrated
represented-sample certificate, before finite-set synthesis).

Let the public data `q` satisfy the public conditions; let the node program `N` compute the
`μ`-bit node words `N.word u` of the labels `u` (nodes `word u · T / 2^μ`) with the counts
`NodeProg.OK`; let the time-indexed native sparse data `D` of the samples at the `2^nd` data grid
times `g T / 2^nd`, `nd ≤ μ + m`, have `k`-bit indices (`en`), `s = 2^σ` slots on the lowest `σ`
index bits (`hrange`) and entries `c₀ (X + i Y)` with `b`-bit two's complement components
(`hdec`). For valid loading and weight-preparation circuits the native preparation
`prepQN q μ nd N loadC wpC` and its counts are those of `binary_nodes_counts`. For every input
`x` whose samples at the data grid points `addrFN s r` read by the branches (only those) satisfy
the energy bounds and are accretive (`SampleOK`), every loading `Jl` and weight preparation `Wp`
approximated within `ζs` by the two circuits with `24 d ζ + 3 ζs ≤ ν`, every positive source
quadrature with the computed nodes, weights `w_u ≥ 0` and vectors `f_u`, and every generator
path, forcing, solution, branch solutions and certificate `κ` satisfying `RestN` (with the
integrated represented-sample error `δI`, which contains the rounding of the exact branch
addresses to the data grid), the protocol has the guarantees `NOutcome`: success probability at
least `175/256 ≥ 2/3`, every successful trial within `ε/500` of `x(T)/‖x(T)‖` up to a global
phase, and a conditional output within trace distance `ε`. -/
theorem binary_nodes_solver (q : PubT) (hq : q.OK) (mu nd : ℕ) (hnd : nd ≤ mu + q.m)
    (N : NodeProg q.m mu Zn) (hN : N.OK)
    (D : Data (X × Fin (2 ^ nd)) n (Cfg (VW q.b)) q.s) (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (hdec : ∀ e z, D.decode e z = (q.c0 : ℂ) * gauss z)
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin nd ⊕ PY q.kx q.b)
      Query)) (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin nd ⊕ PY q.kx q.b) Query))
    (hwpV : ∀ i ∈ wpC, i.Valid) (x : X)
    (hS : ∀ (s : Bool × (Fin q.m → Bool)) (r : ℕ) (hr : r < 2 ^ q.m),
      SampleOK D x q.etaH q.etaD (addrFN nd hnd N s r hr))
    (Jl : Bool × (Fin q.m → Bool) → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
    (Wp : Matrix (Cfg (Fin (q.m + 1))) (Cfg (Fin (q.m + 1))) ℂ) (wq : ℕ → ℝ)
    (fv : ℕ → Reg (Fin q.kx) ℂ) (G : ℝ → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
    (bf xs : ℝ → Reg (Fin q.kx) ℂ) (ys : Bool × (Fin q.m → Bool) → ℝ → Reg (Fin q.kx) ℂ)
    (βG δI κ ζs : ℝ) (hζs : 0 ≤ ζs)
    (hload : ApproxOn CleanX (nrun (primsT (R := ℂ) (m := nd) D en x) loadC)
      (liftB (loadIdeal Jl)) ζs)
    (hwp : ApproxOn CleanX (nrun (primsT (R := ℂ) (m := nd) D en x) wpC)
      (liftB (matOp Wp)) ζs)
    (hbud : 24 * (q.params.d : ℝ) * q.ζ + 3 * ζs ≤ q.params.nu)
    (hR : RestN q mu nd hnd N D en x Jl Wp wq fv G bf xs ys βG δI κ) :
    NOutcome (prepQN q mu nd hnd N loadC wpC) q.params.ratio q.ε (q.params.ratio_ge hq.g_ge)
      (primsT (R := ℂ) (m := nd) D en x) (xs q.T) :=
  native_time_outcomeBI q.params (q.params_ok hq) q.UJg (hadUJ4_ok q.σ q.hσ)
    (ndQN q mu nd hnd N) (ndQN_public q mu nd hnd N hN) (arQN q mu Zn) q.ζ hq.ζ_pos.le
    (arQN_ok q mu nd hnd N hq) loadC hloadV wpC hwpV (primsT (R := ℂ) (m := nd) D en x)
    (primsT_isUnitary D en x)
    ⟨UJop (R := ℂ) q.UJg, privFamN q.params mu nd hnd N D en x q.rho q.γ, Jl, Wp⟩ rfl
    (nativeOKQN q mu nd hnd N hq hN D en hrange hdec x) ζs hζs hload hwp hbud
    (vN q.params mu N) wq fv (HbN q.params mu nd hnd N D en x) (LbN q.params mu nd hnd N D en x)
    G bf xs ys βG δI κ
    (instanceN q mu nd hnd N hq D en hrange x hS Jl Wp wq fv G bf xs ys βG δI κ hR)

/-- **The finite-gate-set protocol for computed nodes and its counts**: the synthesised protocol
`sprotocol hS (ε/200) (prepQN q μ nd N loadC wpC) (2g)` depends only on the public data, the node
program and the two source circuits; its trials consist of valid gates of `𝒢` and primitive
calls; in every history it makes at most `80 g` times the primitive calls of one native
preparation (bounded in `binary_nodes_counts`) and, if `len ζ ≤ c₁ log(1/ζ) + c₀`, uses at most
`(80 g N_P + 40 g (4 n + 3)) (c₁ log((G + 1)/(ε/200)) + c₀)` elementary gates (`N_P` the gates of
one native preparation, `n = |W| + |XW| + |Zs| + k` and `G = 20 g N_P + 10 g (4 n + 3)`); its
register has the native wires and the `|Xa|` synthesis ancillas. -/
theorem binary_nodes_synth_counts (hS : GateSynth.Synthesis 𝒢 Xa len) (q : PubT) (hq : q.OK)
    (mu nd : ℕ) (hnd : nd ≤ mu + q.m) (N : NodeProg q.m mu Zn) (hN : N.OK)
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin nd ⊕ PY q.kx q.b)
      Query)) (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin nd ⊕ PY q.kx q.b) Query))
    (hwpV : ∀ i ∈ wpC, i.Valid) :
    (∀ j, (∀ i ∈ GateSynth.synthBudget hS (q.ε / 200)
        (trialN (prepQN q mu nd hnd N loadC wpC) j), i.Valid) ∧
      ∀ g, NInstr.gate g ∈ GateSynth.synthBudget hS (q.ε / 200)
        (trialN (prepQN q mu nd hnd N loadC wpC) j) → GateSynth.GateOf 𝒢 g) ∧
    (∀ c : Query → Bool,
      ((GateSynth.sprotocol hS (q.ε / 200) (prepQN q mu nd hnd N loadC wpC) q.params.ratio
        (q.params.ratio_ge hq.g_ge)).worstCost (wCallN c) : ℝ) ≤
        40 * q.params.ratio * nCallsN c (prepQN q mu nd hnd N loadC wpC)) ∧
    (∀ c₀ c₁ : ℝ, 0 ≤ c₀ → 0 ≤ c₁ →
      (∀ ζ' : ℝ, 0 < ζ' → ζ' ≤ 1 → (len ζ' : ℝ) ≤ c₁ * Real.log (1 / ζ') + c₀) →
      ((GateSynth.sprotocol hS (q.ε / 200) (prepQN q mu nd hnd N loadC wpC) q.params.ratio
        (q.params.ratio_ge hq.g_ge)).worstCost wGateN : ℝ) ≤
        (40 * q.params.ratio * nGatesN (prepQN q mu nd hnd N loadC wpC) +
          20 * q.params.ratio * (4 * (Fintype.card q.params.W +
            Fintype.card (XW (ZaN q.m mu Zn ⊕ SZ4 q.kx q.b) (arQN q mu Zn).bT (arQN q mu Zn).bP
              (arQN q mu Zn).A) + Fintype.card Zs + q.kx) + 3)) *
        (c₁ * Real.log ((10 * q.params.ratio * nGatesN (prepQN q mu nd hnd N loadC wpC) +
          5 * q.params.ratio * (4 * (Fintype.card q.params.W +
            Fintype.card (XW (ZaN q.m mu Zn ⊕ SZ4 q.kx q.b) (arQN q mu Zn).bT (arQN q mu Zn).bP
              (arQN q mu Zn).A) + Fintype.card Zs + q.kx) + 3) + 1) / (q.ε / 200)) + c₀)) ∧
    Fintype.card (TNW q.params (Fin q.kx) Zs (ZaN q.m mu Zn ⊕ SZ4 q.kx q.b) (arQN q mu Zn).bT
        (arQN q mu Zn).bP (arQN q mu Zn).A ⊕ Xa) =
      q.kx + 2 * (Fintype.card q.params.W +
        ((mu + Fintype.card Zn + (1 + 2 * (mu + q.m + 14) + (4 * q.m + 62) * (mu + q.m + 14))) +
          (6 * q.kx + 4 * q.b) + (arQN q mu Zn).bT + (arQN q mu Zn).bP + (arQN q mu Zn).A + 3) +
        Fintype.card Zs) + q.kx + 1 + Fintype.card Xa := by
  obtain ⟨hV, -, -, -, -, hcard⟩ := binary_nodes_counts q hq mu nd hnd N hN loadC hloadV wpC hwpV
  have hp := q.params_ok hq
  have hε : 0 < q.ε := hp.ε_pos
  have hεh : q.ε ≤ 1 / 2 := hp.ε_half
  have hη : 0 < q.ε / 200 := by positivity
  refine ⟨fun j => GateSynth.sprotocol_valid hS hη _ hV j,
    fun c => (GateSynth.sprotocol_worst hS hη _ hV q.params.ratio
      (q.params.ratio_ge hq.g_ge) c).2, fun c₀ c₁ hc₀ hc₁ hlen => ?_, ?_⟩
  · have h := GateSynth.sprotocol_worst_log hS hη (by linarith) _ hV q.params.ratio
      (q.params.ratio_ge hq.g_ge) hc₀ hc₁ hlen
    rw [Fintype.card_fin] at h
    exact h
  · rw [Fintype.card_sum, hcard]

/-- **Gate-efficient dissipative ODE solver from binary data with computed nodes over a finite
gate set** (partial formalisation, under this package's format hypotheses, of the finite-set
statement of Theorem `ode:thm:gates`, time-dependent part, with general source
nodes and finite-set synthesis as a hypothesis): under the hypotheses of `binary_nodes_solver` the
synthesised protocol of `binary_nodes_synth_counts` succeeds with probability at least `2/3`, and
its conditional output is within trace distance `ε` of `x(T)/‖x(T)‖` (`GateSynth.SOutcome`). -/
theorem binary_nodes_solver_synth (hS : GateSynth.Synthesis 𝒢 Xa len) (q : PubT) (hq : q.OK)
    (mu nd : ℕ) (hnd : nd ≤ mu + q.m) (N : NodeProg q.m mu Zn) (hN : N.OK)
    (D : Data (X × Fin (2 ^ nd)) n (Cfg (VW q.b)) q.s) (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (hdec : ∀ e z, D.decode e z = (q.c0 : ℂ) * gauss z)
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin nd ⊕ PY q.kx q.b)
      Query)) (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin nd ⊕ PY q.kx q.b) Query))
    (hwpV : ∀ i ∈ wpC, i.Valid) (x : X)
    (hSm : ∀ (s : Bool × (Fin q.m → Bool)) (r : ℕ) (hr : r < 2 ^ q.m),
      SampleOK D x q.etaH q.etaD (addrFN nd hnd N s r hr))
    (Jl : Bool × (Fin q.m → Bool) → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
    (Wp : Matrix (Cfg (Fin (q.m + 1))) (Cfg (Fin (q.m + 1))) ℂ) (wq : ℕ → ℝ)
    (fv : ℕ → Reg (Fin q.kx) ℂ) (G : ℝ → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
    (bf xs : ℝ → Reg (Fin q.kx) ℂ) (ys : Bool × (Fin q.m → Bool) → ℝ → Reg (Fin q.kx) ℂ)
    (βG δI κ ζs : ℝ) (hζs : 0 ≤ ζs)
    (hload : ApproxOn CleanX (nrun (primsT (R := ℂ) (m := nd) D en x) loadC)
      (liftB (loadIdeal Jl)) ζs)
    (hwp : ApproxOn CleanX (nrun (primsT (R := ℂ) (m := nd) D en x) wpC)
      (liftB (matOp Wp)) ζs)
    (hbud : 24 * (q.params.d : ℝ) * q.ζ + 3 * ζs ≤ q.params.nu)
    (hR : RestN q mu nd hnd N D en x Jl Wp wq fv G bf xs ys βG δI κ) :
    GateSynth.SOutcome (GateSynth.sprotocol hS (q.ε / 200) (prepQN q mu nd hnd N loadC wpC)
      q.params.ratio (q.params.ratio_ge hq.g_ge)) q.ε (primsT (R := ℂ) (m := nd) D en x)
      (xs q.T) := by
  obtain ⟨hV, -⟩ := binary_nodes_counts q hq mu nd hnd N hN loadC hloadV wpC hwpV
  have hp := q.params_ok hq
  have hε : 0 < q.ε := hp.ε_pos
  have hεh : q.ε ≤ 1 / 2 := hp.ε_half
  have hη : 0 < q.ε / 200 := by positivity
  exact GateSynth.soutcome hS hη (by linarith) (by linarith) _ hV q.params.ratio
    (q.params.ratio_ge hq.g_ge) (primsT (R := ℂ) (m := nd) D en x)
    (primsT_isUnitary D en x) _ hR.target_ne
    (binary_nodes_solver q hq mu nd hnd N hN D en hrange hdec loadC hloadV wpC hwpV x hSm Jl Wp
      wq fv G bf xs ys βG δI κ ζs hζs hload hwp hbud hR)

/-- **The protocol with the synthesised preparation for computed nodes and its counts**: the
protocol `nprotocol (synthPrep hS (ν/3) (prepQN q μ nd N loadC wpC)) (2g)` depends only on the
public data, the node program and the two source circuits. Under `Synthesis 𝒢 Xa len`,
`AdjClosed 𝒢` and `zeroTestKinds ⊆ 𝒢` its trials consist of valid gates of `𝒢` and primitive
calls; the synthesised preparation has at most `N_P len(ν/3/(N_P+1))` gates (`N_P` the gates of
one native preparation, `binary_nodes_counts`) and exactly the native calls; in every history the
protocol makes at most `80 g` times the native calls and uses at most `80 g N_S + 40 g (4 n + 3)`
gates (`n = |W| + |XW| + |SX| + k`), at most `80 g N_P (c₁ log((N_P+1)/(ν/3)) + c₀) +
40 g (4 n + 3)` if `len ζ ≤ c₁ log(1/ζ) + c₀`. -/
theorem binary_nodes_trials_counts (hS : GateSynth.Synthesis 𝒢 Xa len)
    (hadj : GateSynthTrials.AdjClosed 𝒢) (hzt : GateSynthTrials.zeroTestKinds ⊆ 𝒢) (q : PubT)
    (hq : q.OK) (mu nd : ℕ) (hnd : nd ≤ mu + q.m) (N : NodeProg q.m mu Zn) (hN : N.OK)
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin nd ⊕ PY q.kx q.b)
      Query)) (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin nd ⊕ PY q.kx q.b) Query))
    (hwpV : ∀ i ∈ wpC, i.Valid) :
    (∀ j, (∀ i ∈ trialN (synthPrep hS (q.params.nu / 3) (prepQN q mu nd hnd N loadC wpC)) j,
        i.Valid) ∧
      ∀ g, NInstr.gate g ∈
        trialN (synthPrep hS (q.params.nu / 3) (prepQN q mu nd hnd N loadC wpC)) j →
        GateSynth.GateOf 𝒢 g) ∧
    nGatesN (synthPrep hS (q.params.nu / 3) (prepQN q mu nd hnd N loadC wpC)) ≤
      nGatesN (prepQN q mu nd hnd N loadC wpC) *
        len (q.params.nu / 3 / (nGatesN (prepQN q mu nd hnd N loadC wpC) + 1)) ∧
    (∀ c : Query → Bool,
      nCallsN c (synthPrep hS (q.params.nu / 3) (prepQN q mu nd hnd N loadC wpC)) =
        nCallsN c (prepQN q mu nd hnd N loadC wpC)) ∧
    (∀ c : Query → Bool,
      ((nprotocol (synthPrep hS (q.params.nu / 3) (prepQN q mu nd hnd N loadC wpC))
        q.params.ratio (q.params.ratio_ge hq.g_ge)).worstCost (wCallN c) : ℝ) ≤
        40 * q.params.ratio * nCallsN c (prepQN q mu nd hnd N loadC wpC)) ∧
    ((nprotocol (synthPrep hS (q.params.nu / 3) (prepQN q mu nd hnd N loadC wpC))
        q.params.ratio (q.params.ratio_ge hq.g_ge)).worstCost wGateN : ℝ) ≤
      40 * q.params.ratio *
          nGatesN (synthPrep hS (q.params.nu / 3) (prepQN q mu nd hnd N loadC wpC)) +
        20 * q.params.ratio * (4 * (Fintype.card q.params.W +
          Fintype.card (XW (ZaN q.m mu Zn ⊕ SZ4 q.kx q.b) (arQN q mu Zn).bT (arQN q mu Zn).bP
            (arQN q mu Zn).A) +
          Fintype.card (SX Zs (tnPool q.params (Fin q.kx) Zs (ZaN q.m mu Zn ⊕ SZ4 q.kx q.b)
            (arQN q mu Zn).bT (arQN q mu Zn).bP (arQN q mu Zn).A) Xa) + q.kx) + 3) ∧
    (∀ c₀ c₁ : ℝ, 0 ≤ c₀ → 0 ≤ c₁ →
      (∀ ζ' : ℝ, 0 < ζ' → ζ' ≤ 1 → (len ζ' : ℝ) ≤ c₁ * Real.log (1 / ζ') + c₀) →
      ((nprotocol (synthPrep hS (q.params.nu / 3) (prepQN q mu nd hnd N loadC wpC))
          q.params.ratio (q.params.ratio_ge hq.g_ge)).worstCost wGateN : ℝ) ≤
        40 * q.params.ratio * (nGatesN (prepQN q mu nd hnd N loadC wpC) *
          (c₁ * Real.log ((nGatesN (prepQN q mu nd hnd N loadC wpC) + 1) / (q.params.nu / 3)) +
            c₀)) +
        20 * q.params.ratio * (4 * (Fintype.card q.params.W +
          Fintype.card (XW (ZaN q.m mu Zn ⊕ SZ4 q.kx q.b) (arQN q mu Zn).bT (arQN q mu Zn).bP
            (arQN q mu Zn).A) +
          Fintype.card (SX Zs (tnPool q.params (Fin q.kx) Zs (ZaN q.m mu Zn ⊕ SZ4 q.kx q.b)
            (arQN q mu Zn).bT (arQN q mu Zn).bP (arQN q mu Zn).A) Xa) + q.kx) + 3)) ∧
    Fintype.card (STW q.params (Fin q.kx) Zs (ZaN q.m mu Zn ⊕ SZ4 q.kx q.b) (arQN q mu Zn).bT
        (arQN q mu Zn).bP (arQN q mu Zn).A Xa) =
      q.kx + 2 * (Fintype.card q.params.W +
        ((mu + Fintype.card Zn + (1 + 2 * (mu + q.m + 14) + (4 * q.m + 62) * (mu + q.m + 14))) +
          (6 * q.kx + 4 * q.b) + (arQN q mu Zn).bT + (arQN q mu Zn).bP + (arQN q mu Zn).A + 3) +
        (Fintype.card Zs + 1 + tnPool q.params (Fin q.kx) Zs (ZaN q.m mu Zn ⊕ SZ4 q.kx q.b)
          (arQN q mu Zn).bT (arQN q mu Zn).bP (arQN q mu Zn).A + Fintype.card Xa)) + q.kx + 1 := by
  obtain ⟨hV, -, -, hSG, hSC, hWC, hWG, hWL, hcard, -⟩ :=
    GateSynthTrials.native_ode_time_solver_trials hS hadj hzt q.params (q.params_ok hq) q.UJg
      (hadUJ4_ok q.σ q.hσ) (ndQN q mu nd hnd N) (ndQN_public q mu nd hnd N hN) (arQN q mu Zn)
      q.ζ hq.ζ_pos.le (arQN_ok q mu nd hnd N hq) loadC hloadV wpC hwpV
  refine ⟨hV, hSG, hSC, hWC, ?_, ?_, ?_⟩
  · rw [Fintype.card_fin] at hWG
    exact hWG
  · intro c₀ c₁ hc₀ hc₁ hlen
    have h := hWL c₀ c₁ hc₀ hc₁ hlen
    rw [Fintype.card_fin] at h
    exact h
  · rw [hcard, card_ZN, Fintype.card_fin]

/-- **Gate-efficient dissipative ODE solver from binary data with computed nodes and the
synthesised preparation** (partial formalisation, under this package's format hypotheses, of the
finite-set statement of Theorem `ode:thm:gates`, time-dependent part, with
general source nodes and finite-set synthesis as a hypothesis, including the per-trial claim): under
the hypotheses of `binary_nodes_solver` the protocol of `binary_nodes_trials_counts` has the
guarantees `NOutcome` (no hypothesis on the gate set is needed for them): every successful trial
is within `ε/500` of `x(T)/‖x(T)‖` up to a global phase, the success probability is at least
`2/3`, and the conditional output is within trace distance `ε`. -/
theorem binary_nodes_solver_trials (hS : GateSynth.Synthesis 𝒢 Xa len) (q : PubT) (hq : q.OK)
    (mu nd : ℕ) (hnd : nd ≤ mu + q.m) (N : NodeProg q.m mu Zn) (hN : N.OK)
    (D : Data (X × Fin (2 ^ nd)) n (Cfg (VW q.b)) q.s) (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (hdec : ∀ e z, D.decode e z = (q.c0 : ℂ) * gauss z)
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin nd ⊕ PY q.kx q.b)
      Query)) (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin nd ⊕ PY q.kx q.b) Query))
    (hwpV : ∀ i ∈ wpC, i.Valid) (x : X)
    (hSm : ∀ (s : Bool × (Fin q.m → Bool)) (r : ℕ) (hr : r < 2 ^ q.m),
      SampleOK D x q.etaH q.etaD (addrFN nd hnd N s r hr))
    (Jl : Bool × (Fin q.m → Bool) → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
    (Wp : Matrix (Cfg (Fin (q.m + 1))) (Cfg (Fin (q.m + 1))) ℂ) (wq : ℕ → ℝ)
    (fv : ℕ → Reg (Fin q.kx) ℂ) (G : ℝ → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
    (bf xs : ℝ → Reg (Fin q.kx) ℂ) (ys : Bool × (Fin q.m → Bool) → ℝ → Reg (Fin q.kx) ℂ)
    (βG δI κ ζs : ℝ) (hζs : 0 ≤ ζs)
    (hload : ApproxOn CleanX (nrun (primsT (R := ℂ) (m := nd) D en x) loadC)
      (liftB (loadIdeal Jl)) ζs)
    (hwp : ApproxOn CleanX (nrun (primsT (R := ℂ) (m := nd) D en x) wpC)
      (liftB (matOp Wp)) ζs)
    (hbud : 24 * (q.params.d : ℝ) * q.ζ + 3 * ζs ≤ q.params.nu)
    (hR : RestN q mu nd hnd N D en x Jl Wp wq fv G bf xs ys βG δI κ) :
    NOutcome (synthPrep hS (q.params.nu / 3) (prepQN q mu nd hnd N loadC wpC)) q.params.ratio
      q.ε (q.params.ratio_ge hq.g_ge) (primsT (R := ℂ) (m := nd) D en x) (xs q.T) :=
  native_time_trials_outcomeBI hS q.params (q.params_ok hq) q.UJg (hadUJ4_ok q.σ q.hσ)
    (ndQN q mu nd hnd N) (ndQN_public q mu nd hnd N hN) (arQN q mu Zn) q.ζ hq.ζ_pos.le
    (arQN_ok q mu nd hnd N hq) loadC hloadV wpC hwpV (primsT (R := ℂ) (m := nd) D en x)
    (primsT_isUnitary D en x)
    ⟨UJop (R := ℂ) q.UJg, privFamN q.params mu nd hnd N D en x q.rho q.γ, Jl, Wp⟩ rfl
    (nativeOKQN q mu nd hnd N hq hN D en hrange hdec x) ζs hζs hload hwp hbud
    (vN q.params mu N) wq fv (HbN q.params mu nd hnd N D en x) (LbN q.params mu nd hnd N D en x)
    G bf xs ys βG δI κ
    (instanceN q mu nd hnd N hq D en hrange x hSm Jl Wp wq fv G bf xs ys βG δI κ hR)

end Solvers

end

end SparseHamiltonian.GateBinaryNodes
