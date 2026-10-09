import GateEfficientSelective.ODEBudget
import GateEfficientBinaryNodes.NodeBits
import GateEfficientBinaryNodes.NodeSolver

/-!
# Theorem `ode:thm:gates` with computed nodes and retained source circuits

The solver from binary data with coherently computed source nodes (`GateEfficientBinaryNodes`)
prepares `prepQN q μ nd N loadC wpC`, the native time-dependent preparation `GateNative.tnprepC`
on the branch operation `ndQN` of the node program `N`. Here the preparation is compiled
selectively (`selPrep`): the gates of the supplied loading and weight-preparation circuits that
are gates of `𝒢` are retained verbatim, as are the oracle calls, and only the remaining exact
gates are synthesised. With `loadC`, `wpC` circuits over `𝒢` (and `𝒢` adjoint-closed), the
synthesised gate occurrences are bounded by the native preparation bound with empty source
circuits, `R = prepBoundN q μ nd N ∅ ∅ ≤ 2·10¹⁸ q* ((𝔟+μ+1)³ + |N|)`, a bound that does not
depend on the source circuits.

* `binary_nodes_solver_sel`: the guarantees `NOutcome` of the selective protocol under the
  hypotheses of `GateBinaryNodes.binary_nodes_solver`.
* `binary_nodes_budget_sel`: in every history at most
  `80 g (G_src + 2·10¹⁸ q* ((𝔟+μ+1)³ + |N|) (c₁ (64 (𝔟+μ+1) + log(|N|+1)) + c₀ + 1))
  + 40 g (4 (3·10¹¹ (𝔟+μ+1)³ + 2 |Zn| + 2 |Zs| + |Xa|) + 3)` gates of `𝒢`,
  `G_src = |loadC| + 2 |wpC|`, entering linearly and outside every logarithm; the calls and the
  register of the released budget; the guarantees `NOutcome` with `98304 q* ζ + 3 ζs ≤ ν`.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateSelective

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit GateNative GateSynth GateSynthTrials
open GateBinary GateBinaryODE GateBinaryODETime
open GateODEBudget (gammaOf qOf binary_ode_time_sizes call_budget_arith card_SX pubT_shapeOK)
open GateBitBudget (HasBits)
open GateBinaryNodes (prepQN NodeProg ZaN arQN ndQN RestN instanceN privFamN vN HbN LbN
  nativeOKQN addrFN SampleOK bitN bitN_nonneg prepBoundN prepBoundN_le log_factorN_le testedN_le
  binary_nodes_counts binary_nodes_budget_trials binary_nodes_budget_trials_bits card_XW_ZN
  ndQN_public arQN_ok)
open NativeSparseBlockEncoding (Data Query)
open scoped InnerProduct

section Nodes

variable {X n : Type*} [Fintype n] [DecidableEq n] {Zs : Type*} [Fintype Zs] [DecidableEq Zs]
variable {Zn : Type} [Fintype Zn] [DecidableEq Zn]
variable {Xa : Type*} [Fintype Xa] [DecidableEq Xa] {𝒢 : Set Kind} {len : ℝ → ℕ}

omit [Fintype Zs] [DecidableEq Zs] [Fintype Zn] [DecidableEq Zn] in
/-- The gate bound of one native preparation for computed nodes splits into the bound with empty
loading and weight-preparation circuits and `|loadC| + 2 |wpC|`. -/
theorem prepBoundN_split (q : PubT) (mu nd : ℕ) (N : NodeProg q.m mu Zn)
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin nd ⊕ PY q.kx q.b)
      Query))
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin nd ⊕ PY q.kx q.b) Query)) :
    prepBoundN q mu nd N loadC wpC = prepBoundN (Zs := Zs) q mu nd N [] [] +
      ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) := by
  simp only [prepBoundN, nGatesN_empty, Nat.cast_zero, mul_zero, add_zero]

/-- **Gate-efficient dissipative ODE solver from binary data with computed nodes and retained
source circuits** (Theorem `ode:thm:gates`, time-dependent part with general source nodes): under
the hypotheses of `GateBinaryNodes.binary_nodes_solver` the selective protocol
`nprotocol (selPrep hS (ν/3) (prepQN q μ nd N loadC wpC)) (2g)` has the guarantees `NOutcome`
(no hypothesis on the gate set or on the source circuits is needed for them): every successful
trial is within `ε/500` of `x(T)/‖x(T)‖` up to a global phase, the success probability is at
least `2/3`, and the conditional output is within trace distance `ε`. -/
theorem binary_nodes_solver_sel (hS : Synthesis 𝒢 Xa len) (q : PubT) (hq : q.OK)
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
    NOutcome (selPrep hS (q.params.nu / 3) (prepQN q mu nd hnd N loadC wpC)) q.params.ratio
      q.ε (q.params.ratio_ge hq.g_ge) (primsT (R := ℂ) (m := nd) D en x) (xs q.T) :=
  native_time_sel_outcomeBI hS q.params (q.params_ok hq) q.UJg (hadUJ4_ok q.σ q.hσ)
    (ndQN q mu nd hnd N) (ndQN_public q mu nd hnd N hN) (arQN q mu Zn) q.ζ hq.ζ_pos.le
    (arQN_ok q mu nd hnd N hq) loadC hloadV wpC hwpV (primsT (R := ℂ) (m := nd) D en x)
    (primsT_isUnitary D en x)
    ⟨UJop (R := ℂ) q.UJg, privFamN q.params mu nd hnd N D en x q.rho q.γ, Jl, Wp⟩ rfl
    (nativeOKQN q mu nd hnd N hq hN D en hrange hdec x) ζs hζs hload hwp hbud
    (vN q.params mu N) wq fv (HbN q.params mu nd hnd N D en x) (LbN q.params mu nd hnd N D en x)
    G bf xs ys βG δI κ
    (instanceN q mu nd hnd N hq D en hrange x hSm Jl Wp wq fv G bf xs ys βG δI κ hR)

/-- **Equations `ode:eq:gate-main` and `ode:eq:gate-space` in `𝔟` with computed nodes and
retained source circuits** (Theorem `ode:thm:gates`, time-dependent part with general source
nodes). Under the hypotheses of `GateBinaryNodes.binary_nodes_budget_trials_bits`
(`Synthesis 𝒢 Xa len` with `len ζ ≤ c₁ log(1/ζ) + c₀`, `AdjClosed 𝒢`, `zeroTestKinds ⊆ 𝒢`, the
public rescaling, `ζ ≥ ν/(196608 q*)` and the bit lengths) and loading and weight-preparation
circuits over `𝒢`, with `𝔟 + μ = bitN b_data q μ` and `G_src = |loadC| + 2 |wpC|`, the selective
protocol `nprotocol (selPrep hS (ν/3) (prepQN q μ nd N loadC wpC)) (2g)`: (1) has valid trials
whose gates are gates of `𝒢`; (2) synthesises at most `R = prepBoundN q μ nd N ∅ ∅` gate
occurrences per preparation, (3) with `R ≤ 2·10¹⁸ q* ((𝔟+μ+1)³ + |N|)`, a bound that does not
depend on the source circuits; (4) uses in every history at most
`80 g (G_src + 2·10¹⁸ q* ((𝔟+μ+1)³ + |N|) (c₁ (64 (𝔟+μ+1) + log(|N|+1)) + c₀ + 1))
+ 40 g (4 (3·10¹¹ (𝔟+μ+1)³ + 2 |Zn| + 2 |Zs| + |Xa|) + 3)` gates; (5) makes at most
`7864320 g q*` calls of each coherent sampled-time oracle besides `80 g` times the calls of
`loadC` and twice those of `wpC`; (6) has at most `7·10¹¹ (𝔟+μ+1)³ + 4 |Zn| + 4 |Zs| + 2 |Xa|`
qubits; and (7) has the guarantees `NOutcome` for every input and instance as in
`GateBinaryNodes.binary_nodes_solver` with `98304 q* ζ + 3 ζs ≤ ν`. -/
theorem binary_nodes_budget_sel (hS : Synthesis 𝒢 Xa len) (hadj : AdjClosed 𝒢)
    (hzt : zeroTestKinds ⊆ 𝒢) {c₀ c₁ : ℝ} (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁)
    (hlen : ∀ ζ' : ℝ, 0 < ζ' → ζ' ≤ 1 → (len ζ' : ℝ) ≤ c₁ * Real.log (1 / ζ') + c₀)
    (bd : ℕ) (q : PubT) (hq : q.OK) (hγ : q.γ = gammaOf q.T q.etaH q.etaD (2 * q.g) (q.ε / 2))
    (hζ : q.params.nu ≤ 196608 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * q.ζ)
    (hb : q.b ≤ bd) (hc0 : HasBits bd q.c0) (hT : HasBits bd q.T) (hH : HasBits bd q.etaH)
    (hD : HasBits bd q.etaD) (mu nd : ℕ) (hnd : nd ≤ mu + q.m) (N : NodeProg q.m mu Zn)
    (hN : N.OK)
    (D : Data (X × Fin (2 ^ nd)) n (Cfg (VW q.b)) q.s) (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (hdec : ∀ e z, D.decode e z = (q.c0 : ℂ) * gauss z)
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin nd ⊕ PY q.kx q.b)
      Query)) (hloadV : ∀ i ∈ loadC, i.Valid) (hloadG : ∀ g, NInstr.gate g ∈ loadC → GateOf 𝒢 g)
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin nd ⊕ PY q.kx q.b) Query))
    (hwpV : ∀ i ∈ wpC, i.Valid) (hwpG : ∀ g, NInstr.gate g ∈ wpC → GateOf 𝒢 g) :
    (∀ j, (∀ i ∈ trialN (selPrep hS (q.params.nu / 3) (prepQN q mu nd hnd N loadC wpC)) j,
        i.Valid) ∧
      ∀ g, NInstr.gate g ∈
        trialN (selPrep hS (q.params.nu / 3) (prepQN q mu nd hnd N loadC wpC)) j →
        GateOf 𝒢 g) ∧
    (nSynN 𝒢 (prepQN q mu nd hnd N loadC wpC) : ℝ) ≤ prepBoundN (Zs := Zs) q mu nd N [] [] ∧
    prepBoundN (Zs := Zs) q mu nd N [] [] ≤
      2 * 10 ^ 18 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
        ((bitN bd q mu + 1) ^ 3 + N.gates.length) ∧
    ((nprotocol (selPrep hS (q.params.nu / 3) (prepQN q mu nd hnd N loadC wpC))
        q.params.ratio (q.params.ratio_ge hq.g_ge)).worstCost wGateN : ℝ) ≤
      80 * q.g * (((nGatesN loadC : ℝ) + 2 * nGatesN wpC) +
        2 * 10 ^ 18 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
          ((bitN bd q mu + 1) ^ 3 + N.gates.length) *
          (c₁ * (64 * (bitN bd q mu + 1) + Real.log ((N.gates.length : ℝ) + 1)) + c₀ + 1)) +
      40 * q.g * (4 * (3 * 10 ^ 11 * (bitN bd q mu + 1) ^ 3 + 2 * Fintype.card Zn +
        2 * Fintype.card Zs + Fintype.card Xa) + 3) ∧
    (∀ c : Query → Bool,
      ((nprotocol (selPrep hS (q.params.nu / 3) (prepQN q mu nd hnd N loadC wpC))
        q.params.ratio (q.params.ratio_ge hq.g_ge)).worstCost (wCallN c) : ℝ) ≤
      7864320 * q.g * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
          ((if c Query.rowLocation then 1 else 0) + (if c Query.columnLocation then 1 else 0) +
            (if c Query.value then 1 else 0)) +
        80 * q.g * ((nCallsN c loadC : ℝ) + 2 * nCallsN c wpC)) ∧
    (Fintype.card (STW q.params (Fin q.kx) Zs (ZaN q.m mu Zn ⊕ SZ4 q.kx q.b) (arQN q mu Zn).bT
        (arQN q mu Zn).bP (arQN q mu Zn).A Xa) : ℝ) ≤
      7 * 10 ^ 11 * (bitN bd q mu + 1) ^ 3 + 4 * Fintype.card Zn + 4 * Fintype.card Zs +
        2 * Fintype.card Xa ∧
    ∀ x : X,
      (∀ (s : Bool × (Fin q.m → Bool)) (r : ℕ) (hr : r < 2 ^ q.m),
        SampleOK D x q.etaH q.etaD (addrFN nd hnd N s r hr)) →
      ∀ (Jl : Bool × (Fin q.m → Bool) → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
        (Wp : Matrix (Cfg (Fin (q.m + 1))) (Cfg (Fin (q.m + 1))) ℂ) (wq : ℕ → ℝ)
        (fv : ℕ → Reg (Fin q.kx) ℂ) (G : ℝ → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
        (bf xs : ℝ → Reg (Fin q.kx) ℂ) (ys : Bool × (Fin q.m → Bool) → ℝ → Reg (Fin q.kx) ℂ)
        (βG δI κ ζs : ℝ),
      0 ≤ ζs →
      ApproxOn CleanX (nrun (primsT (R := ℂ) (m := nd) D en x) loadC)
        (liftB (loadIdeal Jl)) ζs →
      ApproxOn CleanX (nrun (primsT (R := ℂ) (m := nd) D en x) wpC) (liftB (matOp Wp)) ζs →
      98304 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * q.ζ + 3 * ζs ≤ q.params.nu →
      RestN q mu nd hnd N D en x Jl Wp wq fv G bf xs ys βG δI κ →
      NOutcome (selPrep hS (q.params.nu / 3) (prepQN q mu nd hnd N loadC wpC)) q.params.ratio
        q.ε (q.params.ratio_ge hq.g_ge) (primsT (R := ℂ) (m := nd) D en x) (xs q.T) := by
  obtain ⟨-, hd, -, -, -, -⟩ := binary_ode_time_sizes q hq hγ
  obtain ⟨-, -, hC, -, -, -⟩ := binary_nodes_counts q hq mu nd hnd N hN loadC hloadV wpC hwpV
  have hprepV : ∀ i ∈ prepQN q mu nd hnd N loadC wpC, i.Valid :=
    tnprepC_valid q.params (q.params_ok hq) q.UJg (hadUJ4_ok q.σ q.hσ) (ndQN q mu nd hnd N)
      (ndQN_public q mu nd hnd N hN) (arQN q mu Zn) (arQN_ok q mu nd hnd N hq) loadC hloadV wpC
      hwpV
  -- the released budgets, for the source circuits and for empty ones
  obtain ⟨-, hNS, -, -, -⟩ := binary_nodes_budget_trials hS hadj hzt hc₀ hc₁ hlen q hq hγ mu nd
    hnd N hN loadC hloadV wpC hwpV
  obtain ⟨-, hN0, -, -, -⟩ := binary_nodes_budget_trials hS hadj hzt hc₀ hc₁ hlen q hq hγ mu nd
    hnd N hN (Zs := Zs) [] (by simp) [] (by simp)
  obtain ⟨-, -, hqub⟩ := binary_nodes_budget_trials_bits hS hadj hzt hc₀ hc₁ hlen bd q hq hγ hζ
    hb hc0 hT hH hD mu nd hnd N hN loadC hloadV wpC hwpV
  have hBp0 := prepBoundN_le bd q hq hγ hζ hb hc0 hT hH hD mu nd N (Zs := Zs) [] []
  simp only [nGatesN_empty, Nat.cast_zero, mul_zero, add_zero] at hBp0
  have hR0 : 0 ≤ prepBoundN (Zs := Zs) q mu nd N [] [] := le_trans (Nat.cast_nonneg _) hN0
  have hsyn : (nSynN 𝒢 (prepQN q mu nd hnd N loadC wpC) : ℝ) ≤
      prepBoundN (Zs := Zs) q mu nd N [] [] := by
    have h1 := nSynN_tnprepC_le 𝒢 hadj q.params q.UJg (ndQN q mu nd hnd N) (arQN q mu Zn) loadC
      hloadG wpC hwpG
    have h2 : ((nSynN 𝒢 (prepQN q mu nd hnd N loadC wpC) : ℕ) : ℝ) ≤
        ((nGatesN (prepQN (Zs := Zs) q mu nd hnd N [] []) : ℕ) : ℝ) := by exact_mod_cast h1
    exact h2.trans hN0
  have hlog := log_factorN_le bd q hq hγ hζ hb hc0 hT hH hD mu nd N (Zs := Zs) [] [] hR0
  simp only [nGatesN_empty, Nat.cast_zero, mul_zero, add_zero, zero_add, Real.log_one]
    at hlog
  have hn := testedN_le bd q hq hγ hζ hb hc0 hT hH hD mu Zn
  have hg0 : 0 ≤ q.g := le_trans zero_le_one hq.g_ge
  have hp := q.params_ok hq
  have hν := hp.nu_pos
  have hν1 : q.params.nu ≤ 1 / 10000 :=
    ImprovedODEQueryBudget.precision_le_one_ten_thousandth (2 * q.g) (q.ε / 2)
      (by linarith [hq.g_ge]) (by linarith [hq.ε_half])
  have hη : 0 < q.params.nu / 3 := by positivity
  have hη1 : q.params.nu / 3 ≤ 1 := by linarith
  have hr2 : q.params.ratio = 2 * q.g := rfl
  have hB0 := bitN_nonneg bd q hq mu
  obtain ⟨hWC, -⟩ := sel_protocol_worst hS hη _ hprepV q.params.ratio (q.params.ratio_ge hq.g_ge)
  refine ⟨fun j => ⟨trialSel_valid hS hη _ hprepV j, trialSel_gateOf hS hadj hzt hη _ hprepV j⟩,
    hsyn, hBp0, ?_, ?_, hqub, ?_⟩
  · -- gates
    have hW := sel_protocol_worst_log hS hη hη1 _ hprepV q.params.ratio
      (q.params.ratio_ge hq.g_ge) hc₀ hc₁ hlen _ hsyn
    have hnc : Fintype.card q.params.W +
        Fintype.card (XW (ZaN q.m mu Zn ⊕ SZ4 q.kx q.b) (arQN q mu Zn).bT (arQN q mu Zn).bP
          (arQN q mu Zn).A) +
        Fintype.card (SX Zs (tnPool q.params (Fin q.kx) Zs (ZaN q.m mu Zn ⊕ SZ4 q.kx q.b)
          (arQN q mu Zn).bT (arQN q mu Zn).bP (arQN q mu Zn).A) Xa) + Fintype.card (Fin q.kx) =
        (22 * q.kx + 16 * q.params.m + 24 * q.params.r + 4 * q.params.l + 8 * q.b +
          2 * ((mu + Fintype.card Zn + (1 + 2 * (mu + q.m + 14) +
            (4 * q.m + 62) * (mu + q.m + 14))) + (arQN q mu Zn).bT + (arQN q mu Zn).bP +
            (arQN q mu Zn).A) + 47) + 2 * Fintype.card Zs + Fintype.card Xa := by
      have ha : q.params.a = q.kx + 3 := rfl
      rw [card_SX, tnPool, card_XW_ZN, q.params.card_W, Fintype.card_fin]
      generalize 1 + 2 * (mu + q.m + 14) + (4 * q.m + 62) * (mu + q.m + 14) = Z
      omega
    have hnc' : ((Fintype.card q.params.W : ℕ) : ℝ) +
        (Fintype.card (XW (ZaN q.m mu Zn ⊕ SZ4 q.kx q.b) (arQN q mu Zn).bT (arQN q mu Zn).bP
          (arQN q mu Zn).A) : ℕ) +
        (Fintype.card (SX Zs (tnPool q.params (Fin q.kx) Zs (ZaN q.m mu Zn ⊕ SZ4 q.kx q.b)
          (arQN q mu Zn).bT (arQN q mu Zn).bP (arQN q mu Zn).A) Xa) : ℕ) +
        (Fintype.card (Fin q.kx) : ℕ) ≤
        3 * 10 ^ 11 * (bitN bd q mu + 1) ^ 3 + 2 * Fintype.card Zn + 2 * Fintype.card Zs +
          Fintype.card Xa := by
      have e : ((Fintype.card q.params.W : ℕ) : ℝ) +
          (Fintype.card (XW (ZaN q.m mu Zn ⊕ SZ4 q.kx q.b) (arQN q mu Zn).bT (arQN q mu Zn).bP
            (arQN q mu Zn).A) : ℕ) +
          (Fintype.card (SX Zs (tnPool q.params (Fin q.kx) Zs (ZaN q.m mu Zn ⊕ SZ4 q.kx q.b)
            (arQN q mu Zn).bT (arQN q mu Zn).bP (arQN q mu Zn).A) Xa) : ℕ) +
          (Fintype.card (Fin q.kx) : ℕ) =
          ((22 * q.kx + 16 * q.params.m + 24 * q.params.r + 4 * q.params.l + 8 * q.b +
            2 * ((mu + Fintype.card Zn + (1 + 2 * (mu + q.m + 14) +
              (4 * q.m + 62) * (mu + q.m + 14))) + (arQN q mu Zn).bT + (arQN q mu Zn).bP +
              (arQN q mu Zn).A) + 47 : ℕ) : ℝ) + 2 * Fintype.card Zs + Fintype.card Xa := by
        rw [← Nat.cast_add, ← Nat.cast_add, ← Nat.cast_add, hnc]
        push_cast
        ring
      rw [e]
      linarith
    have hNk : (nKeepN 𝒢 (prepQN q mu nd hnd N loadC wpC) : ℝ) ≤
        ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) + prepBoundN (Zs := Zs) q mu nd N [] [] := by
      have h1 : ((nKeepN 𝒢 (prepQN q mu nd hnd N loadC wpC) : ℕ) : ℝ) ≤
          (nGatesN (prepQN q mu nd hnd N loadC wpC) : ℝ) := by
        exact_mod_cast nKeepN_le 𝒢 (prepQN q mu nd hnd N loadC wpC)
      rw [prepBoundN_split q mu nd N loadC wpC] at hNS
      linarith
    have hΛ : 0 ≤ 64 * (bitN bd q mu + 1) + Real.log ((N.gates.length : ℝ) + 1) := by
      have h1 : (1 : ℝ) ≤ (N.gates.length : ℝ) + 1 := by
        have := (Nat.cast_nonneg N.gates.length : (0 : ℝ) ≤ N.gates.length)
        linarith
      have := Real.log_nonneg h1
      linarith
    generalize ((nprotocol (selPrep hS (q.params.nu / 3) (prepQN q mu nd hnd N loadC wpC))
      q.params.ratio (q.params.ratio_ge hq.g_ge)).worstCost wGateN : ℝ) = W at hW ⊢
    rw [hr2] at hW
    have hS1 := sep_arith (c := 80) (c₀ := c₀) (c₁ := c₁)
      (lam := Real.log ((prepBoundN (Zs := Zs) q mu nd N [] [] + 1) / (q.params.nu / 3)))
      (by norm_num) hg0 hNk
      (T := W - 40 * q.g *
          (4 * (Fintype.card q.params.W +
          Fintype.card (XW (ZaN q.m mu Zn ⊕ SZ4 q.kx q.b) (arQN q mu Zn).bT (arQN q mu Zn).bP
            (arQN q mu Zn).A) +
          Fintype.card (SX Zs (tnPool q.params (Fin q.kx) Zs (ZaN q.m mu Zn ⊕ SZ4 q.kx q.b)
            (arQN q mu Zn).bT (arQN q mu Zn).bP (arQN q mu Zn).A) Xa) +
          Fintype.card (Fin q.kx)) + 3))
      (by linarith)
    have hS2 := sep_mono (c := 80) (d := 40) (g := q.g)
      (G := (nGatesN loadC : ℝ) + 2 * nGatesN wpC) (c₀ := c₀) (c₁ := c₁)
      (by norm_num) (by norm_num) hg0 hR0 hBp0 hlog hΛ hc₀ hc₁ hnc'
    linarith
  · -- calls
    intro c
    have hI0 : (0 : ℝ) ≤ (if c Query.rowLocation then 1 else 0) +
        (if c Query.columnLocation then 1 else 0) + (if c Query.value then 1 else 0) := by
      split_ifs <;> norm_num
    have hc : (nCallsN c (prepQN q mu nd hnd N loadC wpC) : ℝ) ≤ 12 * (q.params.d : ℝ) *
        (2 * ((if c Query.rowLocation then 1 else 0) + (if c Query.columnLocation then 1 else 0)
          + (if c Query.value then 1 else 0))) +
        ((nCallsN c loadC : ℝ) + 2 * nCallsN c wpC) := by
      have h1 : (nCallsN c (prepQN q mu nd hnd N loadC wpC) : ℝ) ≤ ((12 * q.params.d *
          (2 * (if c Query.rowLocation then 1 else 0) +
            2 * (if c Query.columnLocation then 1 else 0) +
            2 * (if c Query.value then 1 else 0)) +
          nCallsN c loadC + 2 * nCallsN c wpC : ℕ) : ℝ) := by
        exact_mod_cast hC c
      refine h1.trans (le_of_eq ?_)
      push_cast
      ring
    have h := (hWC c).trans ((call_budget_arith 40 q.params.ratio _ _ _ _ _ (by norm_num)
      (le_trans zero_le_one (q.params.ratio_ge hq.g_ge)) hI0 hd hc))
    refine h.trans (le_of_eq ?_)
    rw [hr2]
    ring
  · -- guarantees
    intro x hSm Jl Wp wq fv G bf xs ys βG δI κ ζs hζs hload hwp hbud hR
    have hbud' : 24 * (q.params.d : ℝ) * q.ζ + 3 * ζs ≤ q.params.nu := by
      have hζ0 := hq.ζ_pos.le
      have := mul_le_mul_of_nonneg_right hd hζ0
      linarith
    exact binary_nodes_solver_sel hS q hq mu nd hnd N hN D en hrange hdec loadC hloadV wpC hwpV x
      hSm Jl Wp wq fv G bf xs ys βG δI κ ζs hζs hload hwp hbud' hR

end Nodes

end

end SparseHamiltonian.GateSelective
