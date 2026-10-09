import GateEfficientBinarySelect.Pub
import GateEfficientQuadrature.Native
import GateEfficientNative.Corollaries

/-!
# Theorem `ode:thm:gates` from binary data on branch-dependent meshes

The native solver on branch-dependent meshes (`GateSelect.ODE.native_ode_time_solverB`) takes as
hypotheses the gates of `U_J`, a label- and slot-selected native private operation with its
native identity and arithmetic, and the instance conditions `GateSelect.ODE.BInstanceOK`, among
them the clock promises for the rescaled branch Hamiltonians. For time-indexed binary sparse data
on the grid of `2^(2m)` points all of them are constructed here from the public data `q : PubT`
(`ndQ`, `arQ`, `PubT.UJg`), and the selection conditions of the instance follow from row and
column energy bounds and the accretivity of every grid sample (`instanceB`, `instanceL`); the
loading and weight-preparation circuits and the source, path and certificate conditions
(`RestB`, `RestL`) remain hypotheses.

* `binary_select_counts`: the native preparation `prepQ q loadC wpC` depends only on the public
  data and the two source circuits; its trials are valid and its counts are explicit, with the
  gates `2 (|apG| + 28 k + 2) + 2 |arith| + 2 bP + bT + 1` of one private call (`|apG|` the address
  program, at most `13 (2m + 14)(m + 5)` gates, `length_apG`).
* `binary_select_solver`: in addition, for every positive source quadrature on the `2^m`
  left-endpoint nodes satisfying `RestB`, the protocol succeeds with probability at least `2/3`
  and its conditional output is within trace distance `ε` of `x(T)/‖x(T)‖`, every successful
  trial within `ε/500` up to a global phase.
* `binary_select_solverL`: the same for the left-endpoint quadrature with the weights `T/2^m`
  (`RestL`, the certificate of `GateEfficientQuadrature`).
* `binary_select_gate_count`: the explicit worst-case gate count.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateBinarySelect

noncomputable section
open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
open SparseHamiltonian.GateBinary SparseHamiltonian.GateBinaryODE SparseHamiltonian.OracleCircuit
open SparseHamiltonian.GateBinaryODETime (PubT)
open SparseHamiltonian.GateODE.Time (TParams TOracles)
open SparseHamiltonian.GateQuad (vQ wQ)
open NativeSparseBlockEncoding (Data Query)
open scoped InnerProduct

section Main

variable {X n : Type*} [Fintype n] [DecidableEq n] {Zs : Type*} [Fintype Zs] [DecidableEq Zs]

/-- The scratch wires of the branch operation: the address registers and the scratch of the
constant-coefficient operation. -/
theorem card_ZB (m k b : ℕ) : Fintype.card (ZA m ⊕ SZ4 k b) =
    (1 + 2 * (2 * m + 14) + (4 * m + 62) * (2 * m + 14)) + (6 * k + 4 * b) := by
  rw [Fintype.card_sum, card_ZA, card_SZ4]

/-- The gates of one native private call on branch-dependent meshes. -/
theorem privGatesQ (q : PubT) :
    privGates (ndQ q) (arQ q) = 2 * ((apG q.kx q.b q.m q.params.l).length + (28 * q.kx + 2)) +
      2 * (arQ q).circ.length + (2 * (arQ q).bP + (arQ q).bT + 1) := by
  rw [privGates, ndQ_nGates]

/-- **The counts of the native solver on branch-dependent meshes from binary data.** For valid
loading and weight-preparation circuits `loadC`, `wpC`, the native preparation
`prepQ q loadC wpC` depends only on the public data and the two circuits; its trials are valid;
it has at most `prepGates + 84 d (σ + 3) + 6 d G_C + |loadC| + 2 |wpC|` elementary gates,
`G_C = 2 (|apG| + 28 k + 2) + 2 |arith| + 2 bP + bT + 1` the gates of one private call (the
address program `apG` and the constant-coefficient compute circuit, both computed and
uncomputed), and at most `24 d` calls of each coherent sampled-time oracle on the grid besides
those of the source circuits; in every history the protocol (ratio `2g`) uses at most
`80 g N + 40 g (4 (|W| + |XW| + |Zs| + k) + 3)` elementary gates (`N` the gates of the
preparation) and at most `80 g` times the calls of the preparation; its register has
`k + 2 (|W| + (|ZA| + 6 k + 4 b + bT + bP + A + 3) + |Zs|) + k + 1` qubits, with
`|ZA| = 1 + 2 (2m + 14) + (4m + 62)(2m + 14)` address-register wires. -/
theorem binary_select_counts (q : PubT) (hq : q.OK)
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin (2 * q.m) ⊕ PY q.kx q.b)
      Query)) (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin (2 * q.m) ⊕ PY q.kx q.b) Query))
    (hwpV : ∀ i ∈ wpC, i.Valid) :
    (∀ j, ∀ i ∈ trialN (prepQ q loadC wpC) j, i.Valid) ∧
    nGatesN (prepQ q loadC wpC) ≤ q.params.prepGates + 84 * q.params.d * (q.σ + 3) +
      6 * q.params.d * (2 * ((apG q.kx q.b q.m q.params.l).length + (28 * q.kx + 2)) +
        2 * (arQ q).circ.length + (2 * (arQ q).bP + (arQ q).bT + 1)) + nGatesN loadC +
      2 * nGatesN wpC ∧
    (∀ c : Query → Bool, nCallsN c (prepQ q loadC wpC) ≤
      12 * q.params.d * (2 * (if c Query.rowLocation then 1 else 0) +
        2 * (if c Query.columnLocation then 1 else 0) + 2 * (if c Query.value then 1 else 0)) +
        nCallsN c loadC + 2 * nCallsN c wpC) ∧
    ((nprotocol (prepQ q loadC wpC) q.params.ratio (q.params.ratio_ge hq.g_ge)).worstCost
        wGateN : ℝ) ≤
      40 * q.params.ratio * nGatesN (prepQ q loadC wpC) +
        20 * q.params.ratio * (4 * (Fintype.card q.params.W +
          Fintype.card (XW (ZA q.m ⊕ SZ4 q.kx q.b) (arQ q).bT (arQ q).bP (arQ q).A) +
          Fintype.card Zs + q.kx) + 3) ∧
    (∀ c : Query → Bool,
      ((nprotocol (prepQ q loadC wpC) q.params.ratio (q.params.ratio_ge hq.g_ge)).worstCost
        (wCallN c) : ℝ) ≤ 40 * q.params.ratio * nCallsN c (prepQ q loadC wpC)) ∧
    Fintype.card (TNW q.params (Fin q.kx) Zs (ZA q.m ⊕ SZ4 q.kx q.b) (arQ q).bT (arQ q).bP
        (arQ q).A) =
      q.kx + 2 * (Fintype.card q.params.W +
        ((1 + 2 * (2 * q.m + 14) + (4 * q.m + 62) * (2 * q.m + 14)) + (6 * q.kx + 4 * q.b) +
          (arQ q).bT + (arQ q).bP + (arQ q).A + 3) + Fintype.card Zs) + q.kx + 1 := by
  obtain ⟨hV, hG, hC, hW, hWC, hcard, -⟩ :=
    GateSelect.ODE.native_ode_time_solverB q.params (q.params_ok hq) q.UJg
      (hadUJ4_ok q.σ q.hσ) (ndQ q) (ndQ_public q) (arQ q) q.ζ hq.ζ_pos.le (arQ_ok q hq) loadC
      hloadV wpC hwpV
  have hUJl : q.UJg.length = q.σ + 3 := hadUJ4_length q.σ q.hσ
  refine ⟨hV, ?_, ?_, ?_, hWC, ?_⟩
  · rw [privGatesQ, hUJl] at hG
    exact hG
  · intro c
    have h := hC c
    rw [ndQ_nCalls] at h
    exact h
  · rw [Fintype.card_fin] at hW
    exact hW
  · rw [hcard, card_ZB, Fintype.card_fin]

/-- **Native gate-efficient dissipative ODE solver from time-indexed binary sparse data on
branch-dependent meshes** (Theorem `ode:thm:gates`, time-dependent part, with the branch-dependent
meshes of Lemma `ode:lem:gate-select`, before finite-set synthesis).

Let the public data `q` satisfy the public conditions, and let the time-indexed native sparse
data `D` of the samples `M_g = D.matrix (x, g)` at the `2^(2m)` grid times `g T / 2^(2m)` have
`k`-bit indices (`en`), `s = 2^σ` slots on the lowest `σ` index bits (`hrange`) and entries
`c₀ (X + i Y)` with `b`-bit two's complement components (`hdec`). For valid loading and
weight-preparation circuits the native preparation `prepQ q loadC wpC` and its counts are those
of `binary_select_counts`. For every input `x` whose grid samples have Hamiltonian and
dissipative parts with row and column energies at most `η_H²` and `η_D²` and accretive
dissipative parts, every loading `Jl` and weight preparation `Wp` approximated within `ζs` by
the two circuits with `24 d ζ + 3 ζs ≤ ν`, every positive source quadrature on the `2^m`
left-endpoint nodes with weights `w_u` and vectors `f_u`, and every generator path, forcing,
solution, branch solutions and certificate `κ` satisfying `RestB`, the protocol has the
guarantees `NOutcome`: success probability at least `175/256 ≥ 2/3`, every successful trial
within `ε/500` of `x(T)/‖x(T)‖` up to a global phase, and a conditional output within trace
distance `ε`. -/
theorem binary_select_solver (q : PubT) (hq : q.OK)
    (D : Data (X × Fin (2 ^ (2 * q.m))) n (Cfg (VW q.b)) q.s) (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (hdec : ∀ e z, D.decode e z = (q.c0 : ℂ) * gauss z)
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin (2 * q.m) ⊕ PY q.kx q.b)
      Query)) (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin (2 * q.m) ⊕ PY q.kx q.b) Query))
    (hwpV : ∀ i ∈ wpC, i.Valid) :
    (∀ j, ∀ i ∈ trialN (prepQ q loadC wpC) j, i.Valid) ∧
    nGatesN (prepQ q loadC wpC) ≤ q.params.prepGates + 84 * q.params.d * (q.σ + 3) +
      6 * q.params.d * (2 * ((apG q.kx q.b q.m q.params.l).length + (28 * q.kx + 2)) +
        2 * (arQ q).circ.length + (2 * (arQ q).bP + (arQ q).bT + 1)) + nGatesN loadC +
      2 * nGatesN wpC ∧
    (∀ c : Query → Bool, nCallsN c (prepQ q loadC wpC) ≤
      12 * q.params.d * (2 * (if c Query.rowLocation then 1 else 0) +
        2 * (if c Query.columnLocation then 1 else 0) + 2 * (if c Query.value then 1 else 0)) +
        nCallsN c loadC + 2 * nCallsN c wpC) ∧
    ((nprotocol (prepQ q loadC wpC) q.params.ratio (q.params.ratio_ge hq.g_ge)).worstCost
        wGateN : ℝ) ≤
      40 * q.params.ratio * nGatesN (prepQ q loadC wpC) +
        20 * q.params.ratio * (4 * (Fintype.card q.params.W +
          Fintype.card (XW (ZA q.m ⊕ SZ4 q.kx q.b) (arQ q).bT (arQ q).bP (arQ q).A) +
          Fintype.card Zs + q.kx) + 3) ∧
    (∀ c : Query → Bool,
      ((nprotocol (prepQ q loadC wpC) q.params.ratio (q.params.ratio_ge hq.g_ge)).worstCost
        (wCallN c) : ℝ) ≤ 40 * q.params.ratio * nCallsN c (prepQ q loadC wpC)) ∧
    Fintype.card (TNW q.params (Fin q.kx) Zs (ZA q.m ⊕ SZ4 q.kx q.b) (arQ q).bT (arQ q).bP
        (arQ q).A) =
      q.kx + 2 * (Fintype.card q.params.W +
        ((1 + 2 * (2 * q.m + 14) + (4 * q.m + 62) * (2 * q.m + 14)) + (6 * q.kx + 4 * q.b) +
          (arQ q).bT + (arQ q).bP + (arQ q).A + 3) + Fintype.card Zs) + q.kx + 1 ∧
    ∀ x : X,
      (∀ g i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, g)) i j‖ ^ 2 ≤ q.etaH ^ 2) →
      (∀ g j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, g)) i j‖ ^ 2 ≤ q.etaH ^ 2) →
      (∀ g i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, g)) i j‖ ^ 2 ≤ q.etaD ^ 2) →
      (∀ g j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, g)) i j‖ ^ 2 ≤ q.etaD ^ 2) →
      (∀ g, ∀ w : EuclideanSpace ℂ n, 0 ≤ (inner ℂ w (SparseStateOverlap.matrixOperator
        (ODEMatrixEnergy.dissipativePart (D.matrix (x, g))) w)).re) →
      ∀ (Jl : Bool × (Fin q.m → Bool) → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
        (Wp : Matrix (Cfg (Fin (q.m + 1))) (Cfg (Fin (q.m + 1))) ℂ) (wq : ℕ → ℝ)
        (fv : ℕ → Reg (Fin q.kx) ℂ) (G : ℝ → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
        (bf xs : ℝ → Reg (Fin q.kx) ℂ) (ys : Bool × (Fin q.m → Bool) → ℝ → Reg (Fin q.kx) ℂ)
        (βG δG κ ζs : ℝ),
      0 ≤ ζs →
      ApproxOn CleanX (nrun (primsT (R := ℂ) (m := 2 * q.m) D en x) loadC)
        (liftB (loadIdeal Jl)) ζs →
      ApproxOn CleanX (nrun (primsT (R := ℂ) (m := 2 * q.m) D en x) wpC) (liftB (matOp Wp)) ζs →
      24 * (q.params.d : ℝ) * q.ζ + 3 * ζs ≤ q.params.nu →
      RestB q D en x Jl Wp wq fv G bf xs ys βG δG κ →
      NOutcome (prepQ q loadC wpC) q.params.ratio q.ε (q.params.ratio_ge hq.g_ge)
        (primsT (R := ℂ) (m := 2 * q.m) D en x) (xs q.T) := by
  obtain ⟨hV, hG, hC, hW, hWC, hcard⟩ := binary_select_counts q hq loadC hloadV wpC hwpV
  obtain ⟨-, -, -, -, -, -, hout⟩ :=
    GateSelect.ODE.native_ode_time_solverB q.params (q.params_ok hq) q.UJg
      (hadUJ4_ok q.σ q.hσ) (ndQ q) (ndQ_public q) (arQ q) q.ζ hq.ζ_pos.le (arQ_ok q hq) loadC
      hloadV wpC hwpV
  refine ⟨hV, hG, hC, hW, hWC, hcard, ?_⟩
  intro x hrH hcH hrD hcD hPSD Jl Wp wq fv G bf xs ys βG δG κ ζs hζs hload hwp hbud hR
  exact hout (primsT (R := ℂ) (m := 2 * q.m) D en x) (privFamB q.params D en x q.rho q.γ) Jl Wp
    (vQ q.params q.params.M) wq fv (HbB q.params D en x) (LbB q.params D en x) G bf xs ys βG δG
    κ ζs (primsT_isUnitary D en x) (nativeOKQ q hq D en hrange hdec x) hζs hload hwp hbud
    (instanceB q hq D en hrange x hrH hcH hrD hcD hPSD Jl Wp wq fv G bf xs ys βG δG κ hR)

/-- **The native solver from binary data with the left-endpoint quadrature** (the sufficient
positive quadrature of the proof of Theorem `ode:thm:gates` with `2^m` nodes `u T / 2^m` and the
weights `T / 2^m`): the guarantees of `binary_select_solver` under `RestL`, whose source
certificate `(Λ b_s + L) T² / 2^(m+1) + T δb` is proved in `GateEfficientQuadrature`. -/
theorem binary_select_solverL (q : PubT) (hq : q.OK)
    (D : Data (X × Fin (2 ^ (2 * q.m))) n (Cfg (VW q.b)) q.s) (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (hdec : ∀ e z, D.decode e z = (q.c0 : ℂ) * gauss z)
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin (2 * q.m) ⊕ PY q.kx q.b)
      Query)) (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin (2 * q.m) ⊕ PY q.kx q.b) Query))
    (hwpV : ∀ i ∈ wpC, i.Valid) (x : X)
    (hrH : ∀ g i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, g)) i j‖ ^ 2 ≤ q.etaH ^ 2)
    (hcH : ∀ g j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, g)) i j‖ ^ 2 ≤ q.etaH ^ 2)
    (hrD : ∀ g i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, g)) i j‖ ^ 2 ≤ q.etaD ^ 2)
    (hcD : ∀ g j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, g)) i j‖ ^ 2 ≤ q.etaD ^ 2)
    (hPSD : ∀ g, ∀ w : EuclideanSpace ℂ n, 0 ≤ (inner ℂ w (SparseStateOverlap.matrixOperator
      (ODEMatrixEnergy.dissipativePart (D.matrix (x, g))) w)).re)
    (Jl : Bool × (Fin q.m → Bool) → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
    (Wp : Matrix (Cfg (Fin (q.m + 1))) (Cfg (Fin (q.m + 1))) ℂ)
    (fv : ℕ → Reg (Fin q.kx) ℂ) (G : ℝ → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
    (bf xs : ℝ → Reg (Fin q.kx) ℂ) (ys : Bool × (Fin q.m → Bool) → ℝ → Reg (Fin q.kx) ℂ)
    (βG δG Λ L bs δb ζs : ℝ) (hζs : 0 ≤ ζs)
    (hload : ApproxOn CleanX (nrun (primsT (R := ℂ) (m := 2 * q.m) D en x) loadC)
      (liftB (loadIdeal Jl)) ζs)
    (hwp : ApproxOn CleanX (nrun (primsT (R := ℂ) (m := 2 * q.m) D en x) wpC)
      (liftB (matOp Wp)) ζs)
    (hbud : 24 * (q.params.d : ℝ) * q.ζ + 3 * ζs ≤ q.params.nu)
    (hR : RestL q D en x Jl Wp fv G bf xs ys βG δG Λ L bs δb) :
    NOutcome (prepQ q loadC wpC) q.params.ratio q.ε (q.params.ratio_ge hq.g_ge)
      (primsT (R := ℂ) (m := 2 * q.m) D en x) (xs q.T) :=
  GateQuad.native_time_outcomeL q.params (q.params_ok hq) q.UJg (hadUJ4_ok q.σ q.hσ) (ndQ q)
    (ndQ_public q) (arQ q) q.ζ hq.ζ_pos.le (arQ_ok q hq) loadC hloadV wpC hwpV
    (primsT (R := ℂ) (m := 2 * q.m) D en x) (primsT_isUnitary D en x)
    ⟨UJop (R := ℂ) q.UJg, privFamB q.params D en x q.rho q.γ, Jl, Wp⟩ rfl
    (nativeOKQ q hq D en hrange hdec x) ζs hζs hload hwp hbud q.params.M fv
    (HbB q.params D en x) (LbB q.params D en x) G bf xs ys βG δG Λ L bs δb
    (instanceL q hq D en hrange x hrH hcH hrD hcD hPSD Jl Wp fv G bf xs ys βG δG Λ L bs δb hR)

/-- **The worst-case gate count of the native solver on branch-dependent meshes from binary
data** (the explicit count underlying equation `ode:eq:gate-main`): in every history the
protocol uses at most `18000 g [(d+1)(a + m + r + 1 + C_J + G_C) + (J+2)(l+1) + G_src + A]`
elementary gates, with `a = k + 3`, `C_J = σ + 3`,
`G_C = 2 (|apG| + 28 k + 2) + 2 |arith| + 2 bP + bT + 1` the gates of one native private call
(the address program at most `13 (2m + 14)(m + 5)` gates, `length_apG`),
`G_src = |loadC| + 2 |wpC|` and `A = k + |Zs| + (|ZA| + 6 k + 4 b) + bT + bP + A_arith`. -/
theorem binary_select_gate_count (q : PubT) (hq : q.OK)
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin (2 * q.m) ⊕ PY q.kx q.b)
      Query)) (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin (2 * q.m) ⊕ PY q.kx q.b) Query))
    (hwpV : ∀ i ∈ wpC, i.Valid) :
    ((nprotocol (prepQ q loadC wpC) q.params.ratio (q.params.ratio_ge hq.g_ge)).worstCost
        wGateN : ℝ) ≤
      18000 * q.g * (((q.params.d : ℝ) + 1) * (((q.kx + 3 : ℕ) : ℝ) + q.params.m +
          q.params.r + 1 + ((q.σ + 3 : ℕ) : ℝ) +
          ((2 * ((apG q.kx q.b q.m q.params.l).length + (28 * q.kx + 2)) +
            2 * (arQ q).circ.length + (2 * (arQ q).bP + (arQ q).bT + 1) : ℕ) : ℝ)) +
        ((q.params.J : ℝ) + 2) * ((q.params.l : ℝ) + 1) +
        ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) +
        ((q.kx : ℝ) + Fintype.card Zs +
          (((1 + 2 * (2 * q.m + 14) + (4 * q.m + 62) * (2 * q.m + 14)) +
            (6 * q.kx + 4 * q.b) : ℕ) : ℝ) + (arQ q).bT + (arQ q).bP + (arQ q).A)) := by
  have h := native_ode_time_gate_count q.params (q.params_ok hq) q.UJg (hadUJ4_ok q.σ q.hσ)
    (ndQ q) (ndQ_public q) (arQ q) q.ζ hq.ζ_pos.le (arQ_ok q hq) loadC hloadV wpC hwpV
  have hUJl : q.UJg.length = q.σ + 3 := hadUJ4_length q.σ q.hσ
  rw [privGatesQ, hUJl, Fintype.card_fin, card_ZB] at h
  exact h

end Main

end

end SparseHamiltonian.GateBinarySelect
