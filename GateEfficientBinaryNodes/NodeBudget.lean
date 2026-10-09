import GateEfficientBinaryNodes.NodeSolver
import GateEfficientBinarySelect.Budget

/-!
# Equations `ode:eq:gate-main` and `ode:eq:gate-space` for computed nodes, in the query shape
and in the register words

For the public data `q : GateBinaryODETime.PubT` with the public rescaling
`γ = gammaOf T η_H η_D (2g) (ε/2)` the released size bounds `GateODEBudget.binary_ode_time_sizes`
hold (`d ≤ 4096 q*`, `J ≤ 60 q* ℓ`, …, `q* = qOf s T η_H η_D (2g) (ε/2)`, `ℓ = log(1/ν)`). The
computed nodes add the node program `N` (`|N|` gates, `|Zn|` scratch wires, computed and
uncomputed in every private call) and the node register of `μ` wires; the address program for
`μ`-bit node words has at most `13 (μ + m + 14)(m + 5) ≤ 910 (μ + m + 1)²` gates
(`card_addrGT_le`), the address registers at most `897 (μ + m + 1)²` wires (`card_ZAN_le`), and the
arithmetic has a duration word of `μ` bits.

* `wordsN`, `binary_nodes_arith_words`: the register words
  `𝔴 = k_x + b + m + μ + r + l + F + n_c + ⌈log₂ ⌈κ⌉⌉ + ⌈log₂ ⌈1/κ⌉⌉` (decoder scale `kapQN`);
  the gates of one private call without the node program are at most `65536 (𝔴+1)³`, the added
  work wires without the node scratch at most `4096 (𝔴+1)³`.
* `binary_nodes_budget`: equations `ode:eq:gate-main`, `ode:eq:gate-space` in `q*`: at most
  `73746000 g [q* (G_C + k_x + σ + m + r + ℓ (l+1) + 8) + G_src + A]` gates
  (`G_C = 2 (|N| + |addrGT| + 28 k_x + 2) + 2 |arith| + 2 bP + bT + 1`), at most `7864320 g q*`
  calls of each coherent sampled-time oracle besides the source calls, and the register.
* `binary_nodes_budget_solver`: the guarantees `NOutcome` under `98304 q* ζ + 3 ζs ≤ ν`.
* `binary_nodes_budget_words`: at most `6·10¹² g [q* ((𝔴 + ℓ + 1)³ + |N|) + G_src + |Zs| + |Zn|]`
  gates and `10000 (𝔴+1)³ + 2 |Zs| + 2 |Zn|` qubits; the node program enters through its gate
  count `|N|` (multiplied by `q*`) and its scratch `|Zn|`.
* `words_gate_arithN`: the arithmetic of the word budget with the node program.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateBinaryNodes

noncomputable section
open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
open SparseHamiltonian.GateBinary SparseHamiltonian.GateBinaryODE SparseHamiltonian.OracleCircuit
open SparseHamiltonian.GateBinaryODETime (PubT)
open SparseHamiltonian.GateODEBudget (gammaOf qOf binary_ode_time_sizes pubT_shapeOK
  gate_budget_arith' call_budget_arith arith_words wordOf_le)
open ImprovedODEQueryBudget (precision logBudget radius)
open NativeSparseBlockEncoding (Data Query)
open scoped InnerProduct

/-! ### The words -/

/-- The address program for `μ`-bit node words has at most `910 (μ + m + 1)²` gates. -/
theorem card_addrGT_le (m l mu : ℕ) : (addrGT m l mu).length ≤ 910 * (mu + m + 1) ^ 2 := by
  refine (length_addrGT m l mu).trans ?_
  have h1 : mu + m + 14 ≤ 14 * (mu + m + 1) := by omega
  have h2 : m + 5 ≤ 5 * (mu + m + 1) := by omega
  calc 13 * (mu + m + 14) * (m + 5) ≤ 13 * (14 * (mu + m + 1)) * (5 * (mu + m + 1)) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ h1) h2
    _ = 910 * (mu + m + 1) ^ 2 := by ring

/-- The address registers for `μ`-bit node words have at most `897 (μ + m + 1)²` wires. -/
theorem card_ZAN_le (m mu : ℕ) : Fintype.card (ZAN m mu) ≤ 897 * (mu + m + 1) ^ 2 := by
  rw [card_ZAN]
  have h1 : mu + m + 14 ≤ 14 * (mu + m + 1) := by omega
  have h2 : 4 * m + 62 ≤ 62 * (mu + m + 1) := by omega
  have h3 : (4 * m + 62) * (mu + m + 14) ≤ 62 * (mu + m + 1) * (14 * (mu + m + 1)) :=
    Nat.mul_le_mul h2 h1
  have ht : 1 ≤ mu + m + 1 := by omega
  have ht2 : mu + m + 1 ≤ (mu + m + 1) ^ 2 := by nlinarith
  have e : 62 * (mu + m + 1) * (14 * (mu + m + 1)) = 868 * (mu + m + 1) ^ 2 := by ring
  rw [e] at h3
  omega

/-- **The register words of the solver with computed nodes**: the system qubits `k_x`, the stored
bits `b`, the simulator words `m`, `r`, the node precision `μ`, the LCHS word `l`, the
fractional bits `F` of the LCHS step, the CORDIC steps `n_c` for the accuracy `ζ/2` and the bits
`⌈log₂ ⌈κ⌉⌉`, `⌈log₂ ⌈1/κ⌉⌉` of the decoder scale `κ = kapQN q μ`. -/
def wordsN (q : PubT) (mu : ℕ) : ℕ :=
  q.kx + q.b + q.params.m + mu + q.params.r + q.params.l + q.F + Cordic.nOf (q.ζ / 2) +
    Nat.clog 2 ⌈kapQN q mu⌉₊ + Nat.clog 2 ⌈1 / kapQN q mu⌉₊

/-- **The per-call cost and the added work wires as polynomials in the words** (computed
nodes): without the node program, the gates `2 (|addrGT| + 28 k_x + 2) + 2 |arith| + 2 bP + bT + 1`
of one private call are at most `65536 (𝔴+1)³`, and without the node scratch the added work
wires `μ + |ZAN| + 6 k_x + 4 b + bT + bP + A_arith` at most `4096 (𝔴+1)³`; `bT, bP ≤ 5 (𝔴+1)`,
`𝔴 = wordsN q μ`. -/
theorem binary_nodes_arith_words (q : PubT) (mu : ℕ) (Zn : Type) [Fintype Zn] [DecidableEq Zn] :
    2 * ((addrGT q.m q.params.l mu).length + (28 * q.kx + 2)) + 2 * (arQN q mu Zn).circ.length +
        (2 * (arQN q mu Zn).bP + (arQN q mu Zn).bT + 1) ≤ 65536 * (wordsN q mu + 1) ^ 3 ∧
    mu + (1 + 2 * (mu + q.m + 14) + (4 * q.m + 62) * (mu + q.m + 14)) + (6 * q.kx + 4 * q.b) +
        (arQN q mu Zn).bT + (arQN q mu Zn).bP + (arQN q mu Zn).A ≤
      4096 * (wordsN q mu + 1) ^ 3 ∧
    (arQN q mu Zn).bT ≤ 5 * (wordsN q mu + 1) ∧ (arQN q mu Zn).bP ≤ 5 * (wordsN q mu + 1) := by
  obtain ⟨hc, hA, hT, hP⟩ := arQN_counts q mu (Zn := Zn)
  have hg2 : Cordic.g2Of (Cordic.nOf (q.ζ / 2)) (kapQN q mu) =
      Nat.clog 2 ⌈kapQN q mu⌉₊ + Cordic.nOf (q.ζ / 2) + 5 := by
    unfold Cordic.g2Of
    rfl
  have hlk : Cordic.lkOf (kapQN q mu) = Nat.clog 2 ⌈1 / kapQN q mu⌉₊ := by
    unfold Cordic.lkOf
    rfl
  have hx : q.b + mu + q.params.l + q.F + Cordic.g2Of (Cordic.nOf (q.ζ / 2)) (kapQN q mu) +
      Cordic.lkOf (kapQN q mu) ≤ wordsN q mu + 5 := by
    unfold wordsN
    omega
  obtain ⟨h1, h2, h3⟩ := arith_words q.b mu q.params.l q.F (Cordic.nOf (q.ζ / 2))
    (Cordic.g2Of (Cordic.nOf (q.ζ / 2)) (kapQN q mu)) (Cordic.lkOf (kapQN q mu))
    (Cordic.wordOf (Cordic.nOf (q.ζ / 2))) (wordsN q mu) hx (by omega) (wordOf_le _)
  have hlen : (arQN q mu Zn).circ.length ≤ 28355 * (wordsN q mu + 1) ^ 3 := hc.trans h1
  have hA' : (arQN q mu Zn).A ≤ 1231 * (wordsN q mu + 1) ^ 3 := hA.le.trans h2
  have hT' : (arQN q mu Zn).bT ≤ 5 * (wordsN q mu + 1) := hT.le.trans h3
  have hP' : (arQN q mu Zn).bP ≤ 5 * (wordsN q mu + 1) := hP.le.trans h3
  have hkx : q.kx + q.b + q.m + mu ≤ wordsN q mu := by
    have e : q.params.m = q.m := rfl
    unfold wordsN
    omega
  have hm1 : (mu + q.m + 1) ^ 2 ≤ (wordsN q mu + 1) ^ 3 := by
    calc (mu + q.m + 1) ^ 2 ≤ (wordsN q mu + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      _ ≤ (wordsN q mu + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hp1 : wordsN q mu + 1 ≤ (wordsN q mu + 1) ^ 3 := le_self_pow₀ (by omega) (by norm_num)
  have hap : (addrGT q.m q.params.l mu).length ≤ 910 * (wordsN q mu + 1) ^ 3 :=
    (card_addrGT_le q.m q.params.l mu).trans (Nat.mul_le_mul_left _ hm1)
  have hZA : 1 + 2 * (mu + q.m + 14) + (4 * q.m + 62) * (mu + q.m + 14) ≤
      897 * (wordsN q mu + 1) ^ 3 := by
    have h := card_ZAN_le q.m mu
    rw [card_ZAN] at h
    exact h.trans (Nat.mul_le_mul_left _ hm1)
  generalize (wordsN q mu + 1) ^ 3 = W at hlen hA' hap hZA hp1
  generalize 1 + 2 * (mu + q.m + 14) + (4 * q.m + 62) * (mu + q.m + 14) = Z at hZA ⊢
  refine ⟨by omega, by omega, hT', hP'⟩

/-! ### The budget in the query shape -/

section Budget

variable {X n : Type*} [Fintype n] [DecidableEq n] {Zs : Type*} [Fintype Zs] [DecidableEq Zs]
variable {Zn : Type} [Fintype Zn] [DecidableEq Zn]

/-- **The gate, call and qubit budget of the solver with computed nodes with the public
rescaling** (Theorem `ode:thm:gates`, time-dependent part with general source nodes, equations
`ode:eq:gate-main` and `ode:eq:gate-space` before finite-gate-set synthesis). Let the public data
`q` have `γ = gammaOf T η_H η_D (2g) (ε/2)`, and put `q* = qOf s T η_H η_D (2g) (ε/2)`,
`ℓ = log(1/ν)`. For the node program `N`, the data grid of `2^nd` points and the valid circuits
`loadC`, `wpC` of `binary_nodes_solver`, in every history the native protocol (ratio `2g`)

* uses at most `73746000 g [q* (G_C + k_x + σ + m + r + ℓ (l+1) + 8) + G_src + A]` elementary
  gates, `G_C = 2 (|N| + |addrGT| + 28 k_x + 2) + 2 |arith| + 2 bP + bT + 1` the gates of one
  private call (the node program, the address program and the compute circuit, computed and
  uncomputed), `G_src = |loadC| + 2 |wpC|` and
  `A = k_x + |Zs| + (|Z_N| + 6 k_x + 4 b) + bT + bP + A_arith`,
  `|Z_N| = μ + |Zn| + 1 + 2 (μ + m + 14) + (4m + 62)(μ + m + 14)`;
* makes at most `7864320 g q*` calls of each coherent sampled-time oracle besides `80 g` times
  the calls of `loadC` and twice those of `wpC`;

and its register has `22 k_x + 16 m + 24 r + 4 l + 8 b + 2 (|Z_N| + bT + bP + A_arith) + 2 |Zs| +
47` qubits. -/
theorem binary_nodes_budget (q : PubT) (hq : q.OK)
    (hγ : q.γ = gammaOf q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) (mu nd : ℕ) (hnd : nd ≤ mu + q.m)
    (N : NodeProg q.m mu Zn) (hN : N.OK)
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin nd ⊕ PY q.kx q.b)
      Query)) (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin nd ⊕ PY q.kx q.b) Query))
    (hwpV : ∀ i ∈ wpC, i.Valid) :
    ((nprotocol (prepQN q mu nd hnd N loadC wpC) q.params.ratio
        (q.params.ratio_ge hq.g_ge)).worstCost wGateN : ℝ) ≤
      73746000 * q.g * (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
          (((2 * (N.gates.length + (addrGT q.m q.params.l mu).length + (28 * q.kx + 2)) +
              2 * (arQN q mu Zn).circ.length +
              (2 * (arQN q mu Zn).bP + (arQN q mu Zn).bT + 1) : ℕ) : ℝ) +
            q.kx + q.σ + q.params.m + q.params.r +
            logBudget (2 * q.g) (q.ε / 2) * ((q.params.l : ℝ) + 1) + 8) +
        ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) +
        ((q.kx : ℝ) + Fintype.card Zs +
          (((mu + Fintype.card Zn + (1 + 2 * (mu + q.m + 14) + (4 * q.m + 62) * (mu + q.m + 14))) +
            (6 * q.kx + 4 * q.b) : ℕ) : ℝ) + (arQN q mu Zn).bT + (arQN q mu Zn).bP +
          (arQN q mu Zn).A)) ∧
    (∀ c : Query → Bool,
      ((nprotocol (prepQN q mu nd hnd N loadC wpC) q.params.ratio
        (q.params.ratio_ge hq.g_ge)).worstCost (wCallN c) : ℝ) ≤
      7864320 * q.g * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
          ((if c Query.rowLocation then 1 else 0) + (if c Query.columnLocation then 1 else 0) +
            (if c Query.value then 1 else 0)) +
        80 * q.g * ((nCallsN c loadC : ℝ) + 2 * nCallsN c wpC)) ∧
    Fintype.card (TNW q.params (Fin q.kx) Zs (ZaN q.m mu Zn ⊕ SZ4 q.kx q.b) (arQN q mu Zn).bT
        (arQN q mu Zn).bP (arQN q mu Zn).A) =
      22 * q.kx + 16 * q.params.m + 24 * q.params.r + 4 * q.params.l + 8 * q.b +
        2 * ((mu + Fintype.card Zn + (1 + 2 * (mu + q.m + 14) + (4 * q.m + 62) * (mu + q.m + 14))) +
          (arQN q mu Zn).bT + (arQN q mu Zn).bP + (arQN q mu Zn).A) + 2 * Fintype.card Zs + 47 := by
  have h := pubT_shapeOK q hq
  obtain ⟨-, hd, -, -, hJ, -⟩ := binary_ode_time_sizes q hq hγ
  have hq1 := h.one_le_q
  have hℓ := h.ell_ge
  have hg0 : 0 ≤ q.g := le_trans zero_le_one hq.g_ge
  refine ⟨?_, ?_, ?_⟩
  · -- gates
    have hG := binary_nodes_gate_count q hq mu nd hnd N hN loadC hloadV wpC hwpV
    generalize (2 * (N.gates.length + (addrGT q.m q.params.l mu).length + (28 * q.kx + 2)) +
      2 * (arQN q mu Zn).circ.length + (2 * (arQN q mu Zn).bP + (arQN q mu Zn).bT + 1) : ℕ) =
      GC at hG ⊢
    have hA0 : (0 : ℝ) ≤ (q.kx : ℝ) + Fintype.card Zs +
      (((mu + Fintype.card Zn + (1 + 2 * (mu + q.m + 14) + (4 * q.m + 62) * (mu + q.m + 14))) +
        (6 * q.kx + 4 * q.b) : ℕ) : ℝ) + (arQN q mu Zn).bT + (arQN q mu Zn).bP +
      (arQN q mu Zn).A :=
      add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (Nat.cast_nonneg _)
        (Nat.cast_nonneg _)) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)) (Nat.cast_nonneg _))
        (Nat.cast_nonneg _)
    generalize ((q.kx : ℝ) + Fintype.card Zs +
      (((mu + Fintype.card Zn + (1 + 2 * (mu + q.m + 14) + (4 * q.m + 62) * (mu + q.m + 14))) +
        (6 * q.kx + 4 * q.b) : ℕ) : ℝ) + (arQN q mu Zn).bT + (arQN q mu Zn).bP +
      (arQN q mu Zn).A) = Aw at hG hA0 ⊢
    have hG0 : (0 : ℝ) ≤ (nGatesN loadC : ℝ) + 2 * nGatesN wpC :=
      add_nonneg (Nat.cast_nonneg _) (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
    generalize ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) = Gs at hG hG0 ⊢
    have key := gate_budget_arith' 18000 q.g (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2))
      (logBudget (2 * q.g) (q.ε / 2)) (q.params.d : ℝ) (q.params.J : ℝ) (q.params.l : ℝ)
      (((q.kx + 3 : ℕ) : ℝ) + q.params.m + q.params.r + 1 + ((q.σ + 3 : ℕ) : ℝ) + (GC : ℝ)) Gs Aw
      (by norm_num) hg0 hq1 hℓ hd hJ (Nat.cast_nonneg _) (by positivity) hG0 hA0
    refine hG.trans (key.trans (le_of_eq ?_))
    push_cast
    ring
  · -- calls
    intro c
    obtain ⟨-, -, hC, -, hWC, -⟩ := binary_nodes_counts q hq mu nd hnd N hN loadC hloadV wpC hwpV
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
    have hr0 : 0 ≤ q.params.ratio := by
      show 0 ≤ 2 * q.g
      linarith
    refine (hWC c).trans ((call_budget_arith 40 q.params.ratio _ _ _ _ _ (by norm_num) hr0 hI0
      hd hc).trans (le_of_eq ?_))
    show 98304 * 40 * (2 * q.g) * _ * _ + 40 * (2 * q.g) * _ = _
    ring
  · -- qubits
    obtain ⟨-, -, -, -, -, hcard⟩ := binary_nodes_counts q hq mu nd hnd N hN loadC hloadV wpC hwpV
    rw [hcard, q.params.card_W]
    show q.kx + 2 * (4 * (q.kx + 3) + 8 * q.params.m + 12 * q.params.r + 2 * q.params.l + 8 +
      ((mu + Fintype.card Zn + (1 + 2 * (mu + q.m + 14) + (4 * q.m + 62) * (mu + q.m + 14))) +
        (6 * q.kx + 4 * q.b) + (arQN q mu Zn).bT + (arQN q mu Zn).bP + (arQN q mu Zn).A + 3) +
      Fintype.card Zs) + q.kx + 1 = _
    ring

/-- **The guarantees of the solver with computed nodes under the arithmetic budget in `q*`**:
with the public rescaling `γ = gammaOf T η_H η_D (2g) (ε/2)`, the hypotheses of
`binary_nodes_solver` with the error budget `98304 q* ζ + 3 ζs ≤ ν` in place of
`24 d ζ + 3 ζs ≤ ν` (`q* = qOf s T η_H η_D (2g) (ε/2)`) give the guarantees `NOutcome`. -/
theorem binary_nodes_budget_solver (q : PubT) (hq : q.OK)
    (hγ : q.γ = gammaOf q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) (mu nd : ℕ) (hnd : nd ≤ mu + q.m)
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
    (hbud : 98304 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * q.ζ + 3 * ζs ≤ q.params.nu)
    (hR : RestN q mu nd hnd N D en x Jl Wp wq fv G bf xs ys βG δI κ) :
    NOutcome (prepQN q mu nd hnd N loadC wpC) q.params.ratio q.ε (q.params.ratio_ge hq.g_ge)
      (primsT (R := ℂ) (m := nd) D en x) (xs q.T) := by
  obtain ⟨-, hd, -, -, -, -⟩ := binary_ode_time_sizes q hq hγ
  refine binary_nodes_solver q hq mu nd hnd N hN D en hrange hdec loadC hloadV wpC hwpV x hS Jl Wp
    wq fv G bf xs ys βG δI κ ζs hζs hload hwp ?_ hR
  have hζ := hq.ζ_pos.le
  have := mul_le_mul_of_nonneg_right hd hζ
  linarith

end Budget

/-! ### The budget in the words -/

/-- The arithmetic of the gate budget in the words with the node program: `q* (G_C + … +
ℓ (l+1) + 8)` and the wires are absorbed in `q* ((w + ℓ + 1)³ + |N|)` and `|Zn|`, for
`G_C ≤ 2 |N| + 65536 (w+1)³` and added wires at most `|Zn| + 4097 (w+1)³`. -/
theorem words_gate_arithN (c C g Q ℓ w GC Sm l Gs Zs Ap Ng Zn : ℝ) (hcC : 69644 * c ≤ C)
    (hc : 0 ≤ c) (hg : 0 ≤ g) (hQ : 1 ≤ Q) (hℓ : 1 ≤ ℓ) (hw : 0 ≤ w)
    (hGC : GC ≤ 2 * Ng + 65536 * (w + 1) ^ 3) (hSm : Sm ≤ 2 * w) (hl0 : 0 ≤ l) (hl : l ≤ w)
    (hAp : Ap ≤ Zn + 4097 * (w + 1) ^ 3) (hGs : 0 ≤ Gs) (hZs : 0 ≤ Zs) (hNg : 0 ≤ Ng)
    (hZn : 0 ≤ Zn) :
    c * g * (Q * (GC + Sm + ℓ * (l + 1) + 8) + Gs + (Zs + Ap)) ≤
      C * g * (Q * ((w + ℓ + 1) ^ 3 + Ng) + Gs + Zs + Zn) := by
  have hy1 : 1 ≤ w + ℓ + 1 := by linarith
  have hy3 : w + ℓ + 1 ≤ (w + ℓ + 1) ^ 3 := le_self_pow₀ hy1 (by norm_num)
  have h13 : 1 ≤ (w + ℓ + 1) ^ 3 := one_le_pow₀ hy1
  have hwy : (w + 1) ^ 3 ≤ (w + ℓ + 1) ^ 3 := pow_le_pow_left₀ (by linarith) (by linarith) 3
  have hsq : (w + ℓ + 1) * (w + ℓ + 1) ≤ (w + ℓ + 1) ^ 3 := by
    have e : (w + ℓ + 1) ^ 3 = (w + ℓ + 1) * (w + ℓ + 1) * (w + ℓ + 1) := by ring
    rw [e]
    exact le_mul_of_one_le_right (by positivity) hy1
  have hℓl : ℓ * (l + 1) ≤ (w + ℓ + 1) * (w + ℓ + 1) :=
    mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
  generalize (w + ℓ + 1) ^ 3 = Y at hy3 h13 hwy hsq ⊢
  have hS : GC + Sm + ℓ * (l + 1) + 8 ≤ 65547 * Y + 2 * Ng := by linarith
  have hQ0 : 0 ≤ Q := by linarith
  have hY0 : 0 ≤ Y := by linarith
  have hQY : Y ≤ Q * Y := le_mul_of_one_le_left hY0 hQ
  have h1 := mul_le_mul_of_nonneg_left hS hQ0
  have hQN : 0 ≤ Q * Ng := mul_nonneg hQ0 hNg
  have e1 : Q * (65547 * Y + 2 * Ng) = 65547 * (Q * Y) + 2 * (Q * Ng) := by ring
  have e2 : Q * (Y + Ng) = Q * Y + Q * Ng := by ring
  rw [e1] at h1
  have hin : Q * (GC + Sm + ℓ * (l + 1) + 8) + Gs + (Zs + Ap) ≤
      69644 * (Q * (Y + Ng) + Gs + Zs + Zn) := by
    rw [e2]
    linarith
  have hpos : 0 ≤ Q * (Y + Ng) + Gs + Zs + Zn := by positivity
  calc c * g * (Q * (GC + Sm + ℓ * (l + 1) + 8) + Gs + (Zs + Ap))
      ≤ c * g * (69644 * (Q * (Y + Ng) + Gs + Zs + Zn)) :=
        mul_le_mul_of_nonneg_left hin (mul_nonneg hc hg)
    _ = 69644 * c * g * (Q * (Y + Ng) + Gs + Zs + Zn) := by ring
    _ ≤ C * g * (Q * (Y + Ng) + Gs + Zs + Zn) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcC hg) hpos

section Words

variable {Zs : Type*} [Fintype Zs] [DecidableEq Zs] {Zn : Type} [Fintype Zn] [DecidableEq Zn]

/-- **Equations `ode:eq:gate-main` and `ode:eq:gate-space` in the words, computed nodes.** With
the public rescaling `γ = gammaOf T η_H η_D (2g) (ε/2)` of `binary_nodes_budget`,
`q* = qOf s T η_H η_D (2g) (ε/2)`, `ℓ = log(1/ν)` and `𝔴 = wordsN q μ`, for the node program `N`
and the valid circuits `loadC`, `wpC` of `binary_nodes_solver`, in every history the native
protocol uses at most `6·10¹² g [q* ((𝔴 + ℓ + 1)³ + |N|) + G_src + |Zs| + |Zn|]` elementary gates
(`G_src = |loadC| + 2 |wpC|`), and its register has at most `10000 (𝔴+1)³ + 2 |Zs| + 2 |Zn|`
qubits. The calls are those of `binary_nodes_budget`. -/
theorem binary_nodes_budget_words (q : PubT) (hq : q.OK)
    (hγ : q.γ = gammaOf q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) (mu nd : ℕ) (hnd : nd ≤ mu + q.m)
    (N : NodeProg q.m mu Zn) (hN : N.OK)
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin nd ⊕ PY q.kx q.b)
      Query)) (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin nd ⊕ PY q.kx q.b) Query))
    (hwpV : ∀ i ∈ wpC, i.Valid) :
    ((nprotocol (prepQN q mu nd hnd N loadC wpC) q.params.ratio
        (q.params.ratio_ge hq.g_ge)).worstCost wGateN : ℝ) ≤
      6 * 10 ^ 12 * q.g * (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
          (((wordsN q mu : ℝ) + logBudget (2 * q.g) (q.ε / 2) + 1) ^ 3 + N.gates.length) +
        ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) + Fintype.card Zs + Fintype.card Zn) ∧
    Fintype.card (TNW q.params (Fin q.kx) Zs (ZaN q.m mu Zn ⊕ SZ4 q.kx q.b) (arQN q mu Zn).bT
        (arQN q mu Zn).bP (arQN q mu Zn).A) ≤
      10000 * (wordsN q mu + 1) ^ 3 + 2 * Fintype.card Zs + 2 * Fintype.card Zn := by
  obtain ⟨hW, -, hcard⟩ := binary_nodes_budget q hq hγ mu nd hnd N hN loadC hloadV wpC hwpV
  obtain ⟨hGC, hAw, -, -⟩ := binary_nodes_arith_words q mu Zn
  have h := pubT_shapeOK q hq
  have hσ := q.hσ
  have hp1 : wordsN q mu + 1 ≤ (wordsN q mu + 1) ^ 3 := le_self_pow₀ (by omega) (by norm_num)
  refine ⟨?_, ?_⟩
  · have hGC' : (((2 * (N.gates.length + (addrGT q.m q.params.l mu).length + (28 * q.kx + 2)) +
        2 * (arQN q mu Zn).circ.length + (2 * (arQN q mu Zn).bP + (arQN q mu Zn).bT + 1) :
          ℕ) : ℝ)) ≤ 2 * (N.gates.length : ℝ) + 65536 * ((wordsN q mu : ℝ) + 1) ^ 3 := by
      have : 2 * (N.gates.length + (addrGT q.m q.params.l mu).length + (28 * q.kx + 2)) +
          2 * (arQN q mu Zn).circ.length + (2 * (arQN q mu Zn).bP + (arQN q mu Zn).bT + 1) ≤
          2 * N.gates.length + 65536 * (wordsN q mu + 1) ^ 3 := by omega
      exact_mod_cast this
    have hSm : (q.kx : ℝ) + q.σ + q.params.m + q.params.r ≤ 2 * (wordsN q mu : ℝ) := by
      have : q.kx + q.σ + q.params.m + q.params.r ≤ 2 * wordsN q mu := by
        unfold wordsN
        omega
      exact_mod_cast this
    have hl : (q.params.l : ℝ) ≤ wordsN q mu := by
      have : q.params.l ≤ wordsN q mu := by
        unfold wordsN
        omega
      exact_mod_cast this
    have hAp : (q.kx : ℝ) + ((((mu + Fintype.card Zn + (1 + 2 * (mu + q.m + 14) +
        (4 * q.m + 62) * (mu + q.m + 14))) + (6 * q.kx + 4 * q.b) : ℕ) : ℝ) +
        (arQN q mu Zn).bT + (arQN q mu Zn).bP + (arQN q mu Zn).A) ≤
        (Fintype.card Zn : ℝ) + 4097 * ((wordsN q mu : ℝ) + 1) ^ 3 := by
      have hkx : q.kx ≤ wordsN q mu := by
        unfold wordsN
        omega
      have : q.kx + ((mu + Fintype.card Zn + (1 + 2 * (mu + q.m + 14) +
          (4 * q.m + 62) * (mu + q.m + 14))) + (6 * q.kx + 4 * q.b) + (arQN q mu Zn).bT +
          (arQN q mu Zn).bP + (arQN q mu Zn).A) ≤
          Fintype.card Zn + 4097 * (wordsN q mu + 1) ^ 3 := by omega
      exact_mod_cast this
    have key := words_gate_arithN 73746000 (6 * 10 ^ 12) q.g
      (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) (logBudget (2 * q.g) (q.ε / 2))
      (wordsN q mu) _ _ (q.params.l : ℝ) ((nGatesN loadC : ℝ) + 2 * nGatesN wpC)
      (Fintype.card Zs : ℝ) _ (N.gates.length : ℝ) (Fintype.card Zn : ℝ)
      (by norm_num) (by norm_num) (le_trans zero_le_one hq.g_ge) h.one_le_q h.ell_ge
      (Nat.cast_nonneg _) hGC' hSm (Nat.cast_nonneg _) hl hAp
      (add_nonneg (Nat.cast_nonneg _) (mul_nonneg (by norm_num) (Nat.cast_nonneg _)))
      (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    refine hW.trans (le_trans (le_of_eq ?_) key)
    ring
  · rw [hcard]
    have h24 : 22 * q.kx + 16 * q.params.m + 24 * q.params.r + 4 * q.params.l + 8 * q.b ≤
        24 * wordsN q mu := by
      unfold wordsN
      omega
    omega

end Words

end

end SparseHamiltonian.GateBinaryNodes
