import GateEfficientBinaryNodes.NodeBudget
import GateEfficientBinarySelect.BudgetTrials

/-!
# Equations `ode:eq:gate-main` and `ode:eq:gate-space` for computed nodes in `𝔟`, and over a
finite gate set

The word budget of equation `ode:eq:gate-word-budget` with the bit-length model of
`GateEfficientBitBudget` (`HasBits`, `bitB`), for the public data `q` with the public rescaling
`γ = gammaOf T η_H η_D (2g) (ε/2)`, an arithmetic accuracy `ζ ≥ ν/(196608 q*)`, stored bits
`b ≤ b_data` and `c₀`, `T`, `η_H`, `η_D` of bit length `b_data`:
`𝔟 = bitB b_data (2^k_x) (2^m) (2^m) q* g ε` as for the dyadic nodes (time mesh `M = 2^m`, `2^m`
source labels). The node words of `μ` bits enter the register words and the decoder scale; they
are counted by `bitN = 𝔟 + μ` (`μ ≤ b_data` gives `bitN ≤ 2 𝔟`). The node program enters
through its gates `|N|` (one copy per private call, so multiplied by `q*`) and its scratch
`|Zn|`.

* `wordsN_le` (the key lemma): `𝔴 + ℓ ≤ 300 (𝔟 + μ + 1)` for `𝔴 = wordsN q μ`.
* `binary_nodes_budget_bits`: at most `2·10²⁰ g [q* ((𝔟+μ+1)³ + |N|) + G_src + |Zs| + |Zn|]`
  gates and `3·10¹¹ (𝔟+μ+1)³ + 2 |Zs| + 2 |Zn|` qubits.
* `prepBoundN`, `binary_nodes_budget_trials`: over a finite gate set (`synthPrep`), the bound
  `B = 819400 q* (G_C + k_x + σ + m + r + ℓ (l+1) + 8) + G_src` of one native preparation, at most
  `80 g B (c₁ log((B+1)/(ν/3)) + c₀) + 40 g (4 n + 3)` gates of `𝒢`, the calls and the register;
  `binary_nodes_budget_solver_trials`: the guarantees `NOutcome` under `98304 q* ζ + 3 ζs ≤ ν`.
* `prepBoundN_le`, `log_factorN_le`, `testedN_le`, `binary_nodes_budget_trials_bits`: the
  finite-gate-set budget in `𝔟 + μ`, with the factor `log(|N| + 1)` of the node program in the
  synthesis logarithm.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateBinaryNodes

noncomputable section
open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
open SparseHamiltonian.GateBinary SparseHamiltonian.GateBinaryODE SparseHamiltonian.OracleCircuit
open SparseHamiltonian.GateBinaryODETime (PubT gridP)
open SparseHamiltonian.GateSynth SparseHamiltonian.GateSynthTrials
open SparseHamiltonian.GateBitBudget
open SparseHamiltonian.GateODEBudget (gammaOf qOf binary_ode_time_sizes pubT_shapeOK
  gammaOf_le_one prep_budget_arith' call_budget_arith card_SX)
open ImprovedODEQueryBudget (precision logBudget radius)
open NativeSparseBlockEncoding (Data Query)
open scoped InnerProduct

/-! ### The word budget with the node precision -/

/-- **The word budget for computed nodes**: `𝔟 + μ`, with
`𝔟 = bitB b_data (2^k_x) (2^m) (2^m) q* g ε` the word budget of equation
`ode:eq:gate-word-budget` (`q* = qOf s T η_H η_D (2g) (ε/2)`) and `μ` the bits of the node words. -/
def bitN (bd : ℕ) (q : PubT) (mu : ℕ) : ℝ :=
  bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m) (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε +
    mu

theorem bitN_nonneg (bd : ℕ) (q : PubT) (hq : q.OK) (mu : ℕ) : 0 ≤ bitN bd q mu := by
  have h := pubT_shapeOK q hq
  have hε1 : q.ε ≤ 1 := hq.ε_half.trans (by norm_num)
  exact add_nonneg (bitB_nonneg _ _ _ _ (mul_nonneg (by linarith [h.one_le_q])
    (by linarith [hq.g_ge])) hq.ε_pos hε1) (Nat.cast_nonneg _)

/-- **The register words in the word budget, computed nodes** (the key lemma of equations
`ode:eq:gate-main` and `ode:eq:gate-space` in `𝔟`). For the public data `q` with the public
rescaling `γ = gammaOf T η_H η_D (2g) (ε/2)`, an arithmetic accuracy `ζ ≥ ν/(196608 q*)`, stored
bits `b ≤ b_data` and `c₀`, `T`, `η_H`, `η_D` of bit length `b_data`, the register words
`𝔴 = wordsN q μ` (decoder scale `κ = γ √(4s) c₀ / (2^(μ + F + 10) ρ)`) and `ℓ = log(1/ν)` satisfy
`𝔴 + ℓ ≤ 300 (𝔟 + μ + 1)`. -/
theorem wordsN_le (bd : ℕ) (q : PubT) (hq : q.OK)
    (hγ : q.γ = gammaOf q.T q.etaH q.etaD (2 * q.g) (q.ε / 2))
    (hζ : q.params.nu ≤ 196608 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * q.ζ)
    (hb : q.b ≤ bd) (hc0 : HasBits bd q.c0) (hT : HasBits bd q.T) (hH : HasBits bd q.etaH)
    (hD : HasBits bd q.etaD) (mu : ℕ) :
    (wordsN q mu : ℝ) + logBudget (2 * q.g) (q.ε / 2) ≤ 300 * (bitN bd q mu + 1) := by
  have h := pubT_shapeOK q hq
  obtain ⟨-, -, -, hr, hJ, hl⟩ := binary_ode_time_sizes q hq hγ
  have hQ1 := h.one_le_q
  have hX := shape_one_le_X h
  have hQX := shape_q_le_X h
  have hνX : 1 / q.params.nu ≤ 10000 *
      ((qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * (2 * q.g) + 1) / (q.ε / 2)) :=
    shape_inv_precision_le h
  have hℓX := shape_ell_le_X h
  have hℓL := shape_ell_le_logb h
  have hν : 0 < q.params.nu := q.params.nu_pos hq.g_ge hq.ε_pos
  have hℓ1 := h.ell_ge
  have hε1 : q.ε ≤ 1 := hq.ε_half.trans (by norm_num)
  have wkx := nat_le_logb q.kx
  have wb : (q.b : ℝ) ≤ bd := by exact_mod_cast hb
  have wm := nat_le_logb q.m
  have wr := r_word q.params.r hQ1 hQX hr
  have wl := l_word q.params.l hQ1 hQX (by linarith) hℓX hl
  have wF : (q.F : ℝ) ≤ 54 + 4 * Real.logb 2
      ((qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * (2 * q.g) + 1) / (q.ε / 2)) :=
    F_word (gridP q.params) (by show (1 : ℝ) ≤ 2 * q.g; linarith [hq.g_ge])
      (by show (0 : ℝ) < q.ε / 2; linarith [hq.ε_pos])
      (by show q.ε / 2 ≤ 1; linarith [hq.ε_half]) (q.TD_nonneg hq) hq.ζ_pos hQ1 hQX hJ hℓX
      hνX hζ
  have wn := nOf_word hq.ζ_pos hν hQ1 hQX hνX hζ
  obtain ⟨wκ, wκi⟩ := kap_words bd q.kx q.s (mu + q.F + 10) h
    (Nat.pow_le_pow_right (by norm_num) q.hσ) hc0 hq.c0_pos hT hH hD
  have hkap : kapQN q mu = gammaOf q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
      Real.sqrt (4 * (q.s : ℝ)) * q.c0 /
        (2 ^ (mu + q.F + 10) * (q.etaH + radius (2 * q.g) (q.ε / 2) * q.etaD)) := by
    rw [← hγ]
    rfl
  rw [← hkap] at wκ wκi
  simp only [Nat.cast_add, Nat.cast_ofNat] at wκi
  have hLL := logb_X_two_le (Q := qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) (g := q.g)
    (by linarith) (by linarith [hq.g_ge]) hq.ε_pos hε1
  have hw : (wordsN q mu : ℝ) = q.kx + q.b + q.m + mu + q.params.r + q.params.l + q.F +
      (Cordic.nOf (q.ζ / 2) : ℝ) + (Nat.clog 2 ⌈kapQN q mu⌉₊ : ℝ) +
      (Nat.clog 2 ⌈1 / kapQN q mu⌉₊ : ℝ) := by
    unfold wordsN
    push_cast
    rfl
  have hb0 : bitN bd q mu =
      bd + Real.logb 2 (((2 ^ q.kx : ℕ) : ℝ) + 1) + Real.logb 2 (((2 ^ q.m : ℕ) : ℝ) + 1) +
        Real.logb 2 (((2 ^ q.m : ℕ) : ℝ) + 1) +
        Real.logb 2 ((qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * q.g + 1) / q.ε) + mu := rfl
  rw [hw, hb0]
  have hL0 := Real.logb_nonneg one_lt_two hX
  have hN0 := logb_succ_nonneg (2 ^ q.kx)
  have hM0 := logb_succ_nonneg (2 ^ q.m)
  have hbd0 : (0 : ℝ) ≤ bd := Nat.cast_nonneg _
  have hmu0 : (0 : ℝ) ≤ mu := Nat.cast_nonneg _
  have hL'0 : 0 ≤ Real.logb 2
      ((qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * q.g + 1) / q.ε) := by
    apply Real.logb_nonneg one_lt_two
    rw [le_div_iff₀ hq.ε_pos]
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2))
      (by linarith [hq.g_ge] : (0 : ℝ) ≤ q.g)
    linarith
  linarith

section Budget

variable {Zs : Type*} [Fintype Zs] [DecidableEq Zs] {Zn : Type} [Fintype Zn] [DecidableEq Zn]

/-- **Equations `ode:eq:gate-main` and `ode:eq:gate-space` in the word budget, computed nodes**
(Theorem `ode:thm:gates`, time-dependent part with general source nodes, equation
`ode:eq:gate-word-budget`). Under the hypotheses of `wordsN_le` (public rescaling,
`ζ ≥ ν/(196608 q*)`, `b ≤ b_data`, `c₀`, `T`, `η_H`, `η_D` of bit length `b_data`), for the node
program `N` and the valid circuits `loadC`, `wpC` of `binary_nodes_solver`, in every history the
native protocol (ratio `2g`) uses at most `2·10²⁰ g [q* ((𝔟+μ+1)³ + |N|) + G_src + |Zs| + |Zn|]`
elementary gates (`G_src = |loadC| + 2 |wpC|`), its register has at most
`3·10¹¹ (𝔟+μ+1)³ + 2 |Zs| + 2 |Zn|` qubits, and `𝔴 + ℓ ≤ 300 (𝔟 + μ + 1)` (`𝔴 = wordsN q μ`). The
calls and the guarantees are those of `binary_nodes_budget` and `binary_nodes_budget_solver`. -/
theorem binary_nodes_budget_bits (bd : ℕ) (q : PubT) (hq : q.OK)
    (hγ : q.γ = gammaOf q.T q.etaH q.etaD (2 * q.g) (q.ε / 2))
    (hζ : q.params.nu ≤ 196608 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * q.ζ)
    (hb : q.b ≤ bd) (hc0 : HasBits bd q.c0) (hT : HasBits bd q.T) (hH : HasBits bd q.etaH)
    (hD : HasBits bd q.etaD) (mu nd : ℕ) (hnd : nd ≤ mu + q.m) (N : NodeProg q.m mu Zn)
    (hN : N.OK)
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin nd ⊕ PY q.kx q.b)
      Query)) (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin nd ⊕ PY q.kx q.b) Query))
    (hwpV : ∀ i ∈ wpC, i.Valid) :
    ((nprotocol (prepQN q mu nd hnd N loadC wpC) q.params.ratio
        (q.params.ratio_ge hq.g_ge)).worstCost wGateN : ℝ) ≤
      2 * 10 ^ 20 * q.g * (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
          ((bitN bd q mu + 1) ^ 3 + N.gates.length) +
        ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) + Fintype.card Zs + Fintype.card Zn) ∧
    (Fintype.card (TNW q.params (Fin q.kx) Zs (ZaN q.m mu Zn ⊕ SZ4 q.kx q.b) (arQN q mu Zn).bT
        (arQN q mu Zn).bP (arQN q mu Zn).A) : ℝ) ≤
      3 * 10 ^ 11 * (bitN bd q mu + 1) ^ 3 + 2 * Fintype.card Zs + 2 * Fintype.card Zn ∧
    (wordsN q mu : ℝ) + logBudget (2 * q.g) (q.ε / 2) ≤ 300 * (bitN bd q mu + 1) := by
  have h := pubT_shapeOK q hq
  have hw := wordsN_le bd q hq hγ hζ hb hc0 hT hH hD mu
  obtain ⟨hWg, hWc⟩ := binary_nodes_budget_words q hq hγ mu nd hnd N hN loadC hloadV wpC hwpV
  have hQ1 := h.one_le_q
  have hg0 : 0 ≤ q.g := le_trans zero_le_one hq.g_ge
  have hB0 := bitN_nonneg bd q hq mu
  have hℓ := h.ell_ge
  have hw0 : (0 : ℝ) ≤ wordsN q mu := Nat.cast_nonneg _
  have hY : 0 ≤ (bitN bd q mu + 1) ^ 3 := by positivity
  refine ⟨?_, ?_, hw⟩
  · -- gates
    have hcube := cube_le (by linarith) hB0 hw
    have hNg : (0 : ℝ) ≤ N.gates.length := Nat.cast_nonneg _
    have hab : ((wordsN q mu : ℝ) + logBudget (2 * q.g) (q.ε / 2) + 1) ^ 3 +
        (N.gates.length : ℝ) ≤ (300 + 1) ^ 3 * ((bitN bd q mu + 1) ^ 3 + N.gates.length) := by
      have e : ((300 : ℝ) + 1) ^ 3 * ((bitN bd q mu + 1) ^ 3 + N.gates.length) =
          (300 + 1) ^ 3 * (bitN bd q mu + 1) ^ 3 + (300 + 1) ^ 3 * (N.gates.length : ℝ) := by
        ring
      rw [e]
      have : (N.gates.length : ℝ) ≤ (300 + 1) ^ 3 * (N.gates.length : ℝ) :=
        le_mul_of_one_le_left hNg (by norm_num)
      linarith
    have key := budget_mono (c := 6 * 10 ^ 12) (C := 2 * 10 ^ 20) (k := (300 + 1) ^ 3) (g := q.g)
      (Q := qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2))
      (S₁ := (nGatesN loadC : ℝ) + 2 * nGatesN wpC)
      (S₂ := (Fintype.card Zs : ℝ) + Fintype.card Zn) (by norm_num) hg0 (by linarith)
      (by positivity) (add_nonneg (Nat.cast_nonneg _) (mul_nonneg (by norm_num)
        (Nat.cast_nonneg _))) (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (by norm_num) hab (by norm_num)
    refine hWg.trans (le_trans (le_of_eq (by ring)) (key.trans (le_of_eq (by ring))))
  · -- qubits
    have hcube := cube_le hw0 hB0 (c := 300) (by linarith)
    have hc : ((Fintype.card (TNW q.params (Fin q.kx) Zs (ZaN q.m mu Zn ⊕ SZ4 q.kx q.b)
        (arQN q mu Zn).bT (arQN q mu Zn).bP (arQN q mu Zn).A) : ℕ) : ℝ) ≤
        10000 * ((wordsN q mu : ℝ) + 1) ^ 3 + 2 * Fintype.card Zs + 2 * Fintype.card Zn := by
      exact_mod_cast hWc
    linarith

end Budget

/-! ### The budget over a finite gate set -/

/-- The added work wires of the solver with computed nodes (the node register and scratch, the
address registers, the scratch wires `SZ4 k_x b`, the arithmetic wires and three further
wires). -/
theorem card_XW_ZN {Zn : Type} [Fintype Zn] (m mu kx b bT bP A : ℕ) :
    Fintype.card (XW (ZaN m mu Zn ⊕ SZ4 kx b) bT bP A) =
      (mu + Fintype.card Zn + (1 + 2 * (mu + m + 14) + (4 * m + 62) * (mu + m + 14))) +
        (6 * kx + 4 * b) + bT + bP + A + 3 := by
  simp only [XW, AWr, Fintype.card_sum, Fintype.card_fin, card_ZAN]
  ring

/-- **The gate bound of one native preparation for computed nodes**:
`B = 819400 q* (G_C + k_x + σ + m + r + ℓ (l+1) + 8) + G_src`, with `q*` and `ℓ` for `(2g, ε/2)`,
`G_C = 2 (|N| + |addrGT| + 28 k_x + 2) + 2 |arith| + 2 bP + bT + 1` the gates of one private call
and `G_src = |loadC| + 2 |wpC|`. -/
def prepBoundN {Zs : Type*} (q : PubT) (mu nd : ℕ) {Zn : Type} (N : NodeProg q.m mu Zn)
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin nd ⊕ PY q.kx q.b)
      Query))
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin nd ⊕ PY q.kx q.b) Query)) : ℝ :=
  819400 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
      (((2 * (N.gates.length + (addrGT q.m q.params.l mu).length + (28 * q.kx + 2)) +
          2 * (arQN q mu Zn).circ.length + (2 * (arQN q mu Zn).bP + (arQN q mu Zn).bT + 1) :
            ℕ) : ℝ) +
        q.kx + q.σ + q.params.m + q.params.r +
        logBudget (2 * q.g) (q.ε / 2) * ((q.params.l : ℝ) + 1) + 8) +
    ((nGatesN loadC : ℝ) + 2 * nGatesN wpC)

section Trials

variable {X n : Type*} [Fintype n] [DecidableEq n] {Zs : Type*} [Fintype Zs] [DecidableEq Zs]
variable {Zn : Type} [Fintype Zn] [DecidableEq Zn]
variable {Xa : Type*} [Fintype Xa] [DecidableEq Xa] {𝒢 : Set Kind} {len : ℝ → ℕ}

/-- **The gate, call and qubit budget over a finite gate set, computed nodes** (partial
formalisation, under this package's format hypotheses, of the finite-set statement of Theorem
`ode:thm:gates`, time-dependent part with general source nodes, equations `ode:eq:gate-main`
and `ode:eq:gate-space` over a finite gate set). Under `Synthesis 𝒢 Xa len` with
`len ζ ≤ c₁ log(1/ζ) + c₀` on `(0, 1]`, `AdjClosed 𝒢` and `zeroTestKinds ⊆ 𝒢`, for the public
data `q` with `γ = gammaOf T η_H η_D (2g) (ε/2)`, `q* = qOf s T η_H η_D (2g) (ε/2)`,
`ℓ = log(1/ν)`, the node program `N` and the valid circuits `loadC`, `wpC` of
`binary_nodes_solver`, with `B = prepBoundN q μ nd N loadC wpC`: every instruction of every trial
of the synthesised protocol `nprotocol (synthPrep hS (ν/3) (prepQN q μ nd N loadC wpC)) (2g)` is
valid and every gate is a gate of `𝒢`; one native preparation has at most `B` gates; in every
history the synthesised protocol uses at most `80 g B (c₁ log((B+1)/(ν/3)) + c₀) + 40 g (4 n + 3)`
gates of `𝒢`, with
`n = 22 k_x + 16 m + 24 r + 4 l + 8 b + 2 (|Z_N| + bT + bP + A_arith) + 2 |Zs| + |Xa| + 47`
(`|Z_N| = μ + |Zn| + 1 + 2 (μ + m + 14) + (4m + 62)(μ + m + 14)`), and at most `7864320 g q*` calls
of each coherent sampled-time oracle besides `80 g` times the calls of `loadC` and twice those of
`wpC`; its register has
`44 k_x + 32 m + 48 r + 8 l + 16 b + 4 (|Z_N| + bT + bP + A_arith) + 4 |Zs| + 2 |Xa| + 95`
qubits. -/
theorem binary_nodes_budget_trials (hS : Synthesis 𝒢 Xa len) (hadj : AdjClosed 𝒢)
    (hzt : zeroTestKinds ⊆ 𝒢) {c₀ c₁ : ℝ} (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁)
    (hlen : ∀ ζ' : ℝ, 0 < ζ' → ζ' ≤ 1 → (len ζ' : ℝ) ≤ c₁ * Real.log (1 / ζ') + c₀)
    (q : PubT) (hq : q.OK) (hγ : q.γ = gammaOf q.T q.etaH q.etaD (2 * q.g) (q.ε / 2))
    (mu nd : ℕ) (hnd : nd ≤ mu + q.m) (N : NodeProg q.m mu Zn) (hN : N.OK)
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin nd ⊕ PY q.kx q.b)
      Query)) (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin nd ⊕ PY q.kx q.b) Query))
    (hwpV : ∀ i ∈ wpC, i.Valid) :
    (∀ j, (∀ i ∈ trialN (synthPrep hS (q.params.nu / 3) (prepQN q mu nd hnd N loadC wpC)) j,
        i.Valid) ∧
      ∀ g, NInstr.gate g ∈
        trialN (synthPrep hS (q.params.nu / 3) (prepQN q mu nd hnd N loadC wpC)) j →
        GateOf 𝒢 g) ∧
    (nGatesN (prepQN q mu nd hnd N loadC wpC) : ℝ) ≤ prepBoundN q mu nd N loadC wpC ∧
    ((nprotocol (synthPrep hS (q.params.nu / 3) (prepQN q mu nd hnd N loadC wpC))
        q.params.ratio (q.params.ratio_ge hq.g_ge)).worstCost wGateN : ℝ) ≤
      80 * q.g * (prepBoundN q mu nd N loadC wpC *
        (c₁ * Real.log ((prepBoundN q mu nd N loadC wpC + 1) / (q.params.nu / 3)) + c₀)) +
      40 * q.g * (4 * ((22 * q.kx + 16 * q.params.m + 24 * q.params.r + 4 * q.params.l +
        8 * q.b + 2 * ((mu + Fintype.card Zn + (1 + 2 * (mu + q.m + 14) +
          (4 * q.m + 62) * (mu + q.m + 14))) + (arQN q mu Zn).bT + (arQN q mu Zn).bP +
          (arQN q mu Zn).A) + 2 * Fintype.card Zs + Fintype.card Xa + 47 : ℕ) : ℝ) + 3) ∧
    (∀ c : Query → Bool,
      ((nprotocol (synthPrep hS (q.params.nu / 3) (prepQN q mu nd hnd N loadC wpC))
        q.params.ratio (q.params.ratio_ge hq.g_ge)).worstCost (wCallN c) : ℝ) ≤
      7864320 * q.g * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
          ((if c Query.rowLocation then 1 else 0) + (if c Query.columnLocation then 1 else 0) +
            (if c Query.value then 1 else 0)) +
        80 * q.g * ((nCallsN c loadC : ℝ) + 2 * nCallsN c wpC)) ∧
    Fintype.card (STW q.params (Fin q.kx) Zs (ZaN q.m mu Zn ⊕ SZ4 q.kx q.b) (arQN q mu Zn).bT
        (arQN q mu Zn).bP (arQN q mu Zn).A Xa) =
      44 * q.kx + 32 * q.params.m + 48 * q.params.r + 8 * q.params.l + 16 * q.b +
        4 * ((mu + Fintype.card Zn + (1 + 2 * (mu + q.m + 14) + (4 * q.m + 62) * (mu + q.m + 14))) +
          (arQN q mu Zn).bT + (arQN q mu Zn).bP + (arQN q mu Zn).A) + 4 * Fintype.card Zs +
        2 * Fintype.card Xa + 95 := by
  have h := pubT_shapeOK q hq
  obtain ⟨-, hd, -, -, hJ, -⟩ := binary_ode_time_sizes q hq hγ
  obtain ⟨-, hG, hC, -, -, -⟩ := binary_nodes_counts q hq mu nd hnd N hN loadC hloadV wpC hwpV
  obtain ⟨hV, hSG, -, hWC, hWG, -, hcard⟩ :=
    binary_nodes_trials_counts hS hadj hzt q hq mu nd hnd N hN loadC hloadV wpC hwpV
  have hq1 := h.one_le_q
  have hℓ := h.ell_ge
  have hg0 : 0 ≤ q.g := le_trans zero_le_one hq.g_ge
  have hp := q.params_ok hq
  have hν := hp.nu_pos
  have hν1 : q.params.nu ≤ 1 / 10000 :=
    ImprovedODEQueryBudget.precision_le_one_ten_thousandth (2 * q.g) (q.ε / 2)
      (by linarith [hq.g_ge]) (by linarith [hq.ε_half])
  have hη : 0 < q.params.nu / 3 := by positivity
  have hη1 : q.params.nu / 3 ≤ 1 := by linarith
  have ha : q.params.a = q.kx + 3 := rfl
  have hr2 : q.params.ratio = 2 * q.g := rfl
  -- one native preparation
  have hNP : (nGatesN (prepQN q mu nd hnd N loadC wpC) : ℝ) ≤ prepBoundN q mu nd N loadC wpC := by
    unfold prepBoundN
    have h1 : (nGatesN (prepQN q mu nd hnd N loadC wpC) : ℝ) ≤ ((q.params.prepGates +
        84 * q.params.d * (q.σ + 3) + 6 * q.params.d *
          (2 * (N.gates.length + (addrGT q.m q.params.l mu).length + (28 * q.kx + 2)) +
          2 * (arQN q mu Zn).circ.length + (2 * (arQN q mu Zn).bP + (arQN q mu Zn).bT + 1)) +
          nGatesN loadC + 2 * nGatesN wpC : ℕ) : ℝ) := by
      exact_mod_cast hG
    have hP : ((2 ^ q.params.l : ℕ) : ℝ) ≤ 2 * ((q.params.J : ℝ) + 2) := by
      exact_mod_cast q.params.l_bounds.2.le
    have ha' : ((q.params.a : ℕ) : ℝ) = (q.kx : ℝ) + 3 := by rw [ha]; push_cast; ring
    rw [q.params.prepGates_eq] at h1
    generalize q.params.d = d at h1 hd
    generalize 2 * (N.gates.length + (addrGT q.m q.params.l mu).length + (28 * q.kx + 2)) +
        2 * (arQN q mu Zn).circ.length + (2 * (arQN q mu Zn).bP + (arQN q mu Zn).bT + 1) =
      GC at h1 ⊢
    generalize nGatesN loadC = gL at h1 ⊢
    generalize nGatesN wpC = gW at h1 ⊢
    push_cast at h1 hP
    rw [ha'] at h1
    exact prep_budget_arith' (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2))
      (logBudget (2 * q.g) (q.ε / 2)) (d : ℝ) (q.params.J : ℝ) ((2 : ℝ) ^ q.params.l)
      (q.params.l : ℝ) (q.kx : ℝ) (q.params.m : ℝ) (q.params.r : ℝ) (q.σ : ℝ) (GC : ℝ)
      ((gL : ℝ) + 2 * (gW : ℝ)) _ hq1 hℓ hd hJ hP (by positivity)
      (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      (Nat.cast_nonneg _) (Nat.cast_nonneg _) (by linarith)
  refine ⟨hV, hNP, ?_, ?_, ?_⟩
  · -- gates
    have hNS := (Nat.cast_le.mpr hSG).trans (gates_log_le hc₀ hc₁ hlen hη hη1 _ _ hNP)
    have hn : Fintype.card q.params.W +
        Fintype.card (XW (ZaN q.m mu Zn ⊕ SZ4 q.kx q.b) (arQN q mu Zn).bT (arQN q mu Zn).bP
          (arQN q mu Zn).A) +
        Fintype.card (SX Zs (tnPool q.params (Fin q.kx) Zs (ZaN q.m mu Zn ⊕ SZ4 q.kx q.b)
          (arQN q mu Zn).bT (arQN q mu Zn).bP (arQN q mu Zn).A) Xa) + q.kx =
        22 * q.kx + 16 * q.params.m + 24 * q.params.r + 4 * q.params.l + 8 * q.b +
          2 * ((mu + Fintype.card Zn + (1 + 2 * (mu + q.m + 14) +
            (4 * q.m + 62) * (mu + q.m + 14))) + (arQN q mu Zn).bT + (arQN q mu Zn).bP +
            (arQN q mu Zn).A) + 2 * Fintype.card Zs + Fintype.card Xa + 47 := by
      rw [card_SX, tnPool, card_XW_ZN, q.params.card_W, Fintype.card_fin]
      generalize 1 + 2 * (mu + q.m + 14) + (4 * q.m + 62) * (mu + q.m + 14) = Z
      omega
    have hn' : ((Fintype.card q.params.W : ℕ) : ℝ) +
        (Fintype.card (XW (ZaN q.m mu Zn ⊕ SZ4 q.kx q.b) (arQN q mu Zn).bT (arQN q mu Zn).bP
          (arQN q mu Zn).A) : ℕ) +
        (Fintype.card (SX Zs (tnPool q.params (Fin q.kx) Zs (ZaN q.m mu Zn ⊕ SZ4 q.kx q.b)
          (arQN q mu Zn).bT (arQN q mu Zn).bP (arQN q mu Zn).A) Xa) : ℕ) + (q.kx : ℝ) =
        ((22 * q.kx + 16 * q.params.m + 24 * q.params.r + 4 * q.params.l + 8 * q.b +
          2 * ((mu + Fintype.card Zn + (1 + 2 * (mu + q.m + 14) +
            (4 * q.m + 62) * (mu + q.m + 14))) + (arQN q mu Zn).bT + (arQN q mu Zn).bP +
            (arQN q mu Zn).A) + 2 * Fintype.card Zs + Fintype.card Xa + 47 : ℕ) : ℝ) := by
      rw [← hn]
      push_cast
      ring
    rw [hn'] at hWG
    have e1 : (40 : ℝ) * q.params.ratio = 80 * q.g := by rw [hr2]; ring
    have e2 : (20 : ℝ) * q.params.ratio = 40 * q.g := by rw [hr2]; ring
    rw [e1, e2] at hWG
    have h80 := mul_le_mul_of_nonneg_left hNS (by positivity : (0 : ℝ) ≤ 80 * q.g)
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
    have hr0 : 0 ≤ q.params.ratio := by
      rw [hr2]
      linarith
    refine (hWC c).trans ((call_budget_arith 40 q.params.ratio _ _ _ _ _ (by norm_num) hr0 hI0
      hd hc).trans (le_of_eq ?_))
    rw [hr2]
    ring
  · -- qubits
    rw [hcard, tnPool, card_XW_ZN, q.params.card_W, Fintype.card_fin]
    generalize 1 + 2 * (mu + q.m + 14) + (4 * q.m + 62) * (mu + q.m + 14) = Z
    omega

/-- **The guarantees of the synthesised preparation for computed nodes under the arithmetic
budget in `q*`**: with the public rescaling, the hypotheses of `binary_nodes_solver` with
`98304 q* ζ + 3 ζs ≤ ν` give the guarantees `NOutcome` of the protocol of
`binary_nodes_budget_trials` (every successful trial within `ε/500` of `x(T)/‖x(T)‖` up to a
global phase). -/
theorem binary_nodes_budget_solver_trials (hS : Synthesis 𝒢 Xa len) (q : PubT) (hq : q.OK)
    (hγ : q.γ = gammaOf q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) (mu nd : ℕ) (hnd : nd ≤ mu + q.m)
    (N : NodeProg q.m mu Zn) (hN : N.OK)
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
    (hbud : 98304 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * q.ζ + 3 * ζs ≤ q.params.nu)
    (hR : RestN q mu nd hnd N D en x Jl Wp wq fv G bf xs ys βG δI κ) :
    NOutcome (synthPrep hS (q.params.nu / 3) (prepQN q mu nd hnd N loadC wpC)) q.params.ratio
      q.ε (q.params.ratio_ge hq.g_ge) (primsT (R := ℂ) (m := nd) D en x) (xs q.T) := by
  obtain ⟨-, hd, -, -, -, -⟩ := binary_ode_time_sizes q hq hγ
  refine binary_nodes_solver_trials hS q hq mu nd hnd N hN D en hrange hdec loadC hloadV wpC hwpV
    x hSm Jl Wp wq fv G bf xs ys βG δI κ ζs hζs hload hwp ?_ hR
  have hζ := hq.ζ_pos.le
  have := mul_le_mul_of_nonneg_right hd hζ
  linarith

end Trials

section Words

variable {Zs : Type*} [Fintype Zs] [DecidableEq Zs] {Zn : Type} [Fintype Zn] [DecidableEq Zn]

omit [Fintype Zs] [DecidableEq Zs] in
/-- **The preparation bound in `𝔟`, computed nodes**: under the hypotheses of `wordsN_le`,
`prepBoundN q μ nd N loadC wpC ≤ 2·10¹⁸ q* ((𝔟+μ+1)³ + |N|) + G_src`,
`G_src = |loadC| + 2 |wpC|`. -/
theorem prepBoundN_le (bd : ℕ) (q : PubT) (hq : q.OK)
    (hγ : q.γ = gammaOf q.T q.etaH q.etaD (2 * q.g) (q.ε / 2))
    (hζ : q.params.nu ≤ 196608 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * q.ζ)
    (hb : q.b ≤ bd) (hc0 : HasBits bd q.c0) (hT : HasBits bd q.T) (hH : HasBits bd q.etaH)
    (hD : HasBits bd q.etaD) (mu nd : ℕ) (N : NodeProg q.m mu Zn)
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin nd ⊕ PY q.kx q.b)
      Query))
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin nd ⊕ PY q.kx q.b) Query)) :
    prepBoundN q mu nd N loadC wpC ≤ 2 * 10 ^ 18 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
        ((bitN bd q mu + 1) ^ 3 + N.gates.length) + ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) := by
  have h := pubT_shapeOK q hq
  have hw := wordsN_le bd q hq hγ hζ hb hc0 hT hH hD mu
  obtain ⟨hGC, -, -, -⟩ := binary_nodes_arith_words q mu Zn
  have hℓ := h.ell_ge
  have hQ1 := h.one_le_q
  have hσ := q.hσ
  have hB0 := bitN_nonneg bd q hq mu
  have hw0 : (0 : ℝ) ≤ wordsN q mu := Nat.cast_nonneg _
  have hGC' : (((2 * ((addrGT q.m q.params.l mu).length + (28 * q.kx + 2)) +
      2 * (arQN q mu Zn).circ.length + (2 * (arQN q mu Zn).bP + (arQN q mu Zn).bT + 1) :
        ℕ) : ℝ)) ≤ 65536 * ((wordsN q mu : ℝ) + 1) ^ 3 := by exact_mod_cast hGC
  have hS : (q.kx : ℝ) + q.σ + q.params.m + q.params.r ≤ 2 * (wordsN q mu : ℝ) := by
    have : q.kx + q.σ + q.params.m + q.params.r ≤ 2 * wordsN q mu := by
      unfold wordsN
      omega
    exact_mod_cast this
  have hl : (q.params.l : ℝ) ≤ wordsN q mu := by
    have : q.params.l ≤ wordsN q mu := by
      unfold wordsN
      omega
    exact_mod_cast this
  have hin := inner_le hw0 hℓ hGC' hS (Nat.cast_nonneg _) hl
  have hcube := cube_le (by linarith) hB0 hw
  have hsplit : (((2 * (N.gates.length + (addrGT q.m q.params.l mu).length + (28 * q.kx + 2)) +
      2 * (arQN q mu Zn).circ.length + (2 * (arQN q mu Zn).bP + (arQN q mu Zn).bT + 1) :
        ℕ) : ℝ)) = 2 * (N.gates.length : ℝ) +
      (((2 * ((addrGT q.m q.params.l mu).length + (28 * q.kx + 2)) +
        2 * (arQN q mu Zn).circ.length + (2 * (arQN q mu Zn).bP + (arQN q mu Zn).bT + 1) :
          ℕ) : ℝ)) := by
    push_cast
    ring
  unfold prepBoundN
  rw [hsplit]
  have hQ0 : 0 ≤ qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) := by linarith
  have hNg : (0 : ℝ) ≤ N.gates.length := Nat.cast_nonneg _
  have h1 : 2 * (N.gates.length : ℝ) +
      (((2 * ((addrGT q.m q.params.l mu).length + (28 * q.kx + 2)) +
        2 * (arQN q mu Zn).circ.length + (2 * (arQN q mu Zn).bP + (arQN q mu Zn).bT + 1) :
          ℕ) : ℝ)) + q.kx + q.σ + q.params.m + q.params.r +
      logBudget (2 * q.g) (q.ε / 2) * ((q.params.l : ℝ) + 1) + 8 ≤
      2 * (N.gates.length : ℝ) + 65547 * ((300 + 1) ^ 3 * (bitN bd q mu + 1) ^ 3) := by
    linarith
  have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 819400 *
    qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2))
  have hY2 : 0 ≤ qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * (bitN bd q mu + 1) ^ 3 := by
    positivity
  have hQN : 0 ≤ qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * (N.gates.length : ℝ) :=
    mul_nonneg hQ0 hNg
  have e1 : 819400 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
      (2 * (N.gates.length : ℝ) + 65547 * ((300 + 1) ^ 3 * (bitN bd q mu + 1) ^ 3)) =
      1638800 * (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * (N.gates.length : ℝ)) +
        819400 * 65547 * (300 + 1) ^ 3 *
          (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * (bitN bd q mu + 1) ^ 3) := by ring
  have e2 : 2 * 10 ^ 18 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
      ((bitN bd q mu + 1) ^ 3 + N.gates.length) =
      2 * 10 ^ 18 * (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * (bitN bd q mu + 1) ^ 3) +
        2 * 10 ^ 18 * (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
          (N.gates.length : ℝ)) := by ring
  rw [e1] at h2
  rw [e2]
  have hc1 : (819400 : ℝ) * 65547 * (300 + 1) ^ 3 ≤ 2 * 10 ^ 18 := by norm_num
  have h3 := mul_le_mul_of_nonneg_right hc1 hY2
  have h4 : 1638800 * (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * (N.gates.length : ℝ)) ≤
      2 * 10 ^ 18 * (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * (N.gates.length : ℝ)) :=
    mul_le_mul_of_nonneg_right (by norm_num) hQN
  linarith

omit [Fintype Zs] [DecidableEq Zs] in
/-- **The synthesis factor in `𝔟`, computed nodes**: under the hypotheses of `wordsN_le`,
`log((B+1)/(ν/3)) ≤ 64 (𝔟+μ+1) + log(G_src+1) + log(|N|+1)` for
`B = prepBoundN q μ nd N loadC wpC`. -/
theorem log_factorN_le (bd : ℕ) (q : PubT) (hq : q.OK)
    (hγ : q.γ = gammaOf q.T q.etaH q.etaD (2 * q.g) (q.ε / 2))
    (hζ : q.params.nu ≤ 196608 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * q.ζ)
    (hb : q.b ≤ bd) (hc0 : HasBits bd q.c0) (hT : HasBits bd q.T) (hH : HasBits bd q.etaH)
    (hD : HasBits bd q.etaD) (mu nd : ℕ) (N : NodeProg q.m mu Zn)
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin nd ⊕ PY q.kx q.b)
      Query))
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin nd ⊕ PY q.kx q.b) Query))
    (hB0 : 0 ≤ prepBoundN q mu nd N loadC wpC) :
    Real.log ((prepBoundN q mu nd N loadC wpC + 1) / (q.params.nu / 3)) ≤
      64 * (bitN bd q mu + 1) + Real.log ((nGatesN loadC : ℝ) + 2 * nGatesN wpC + 1) +
        Real.log ((N.gates.length : ℝ) + 1) := by
  have h := pubT_shapeOK q hq
  have hε1 : q.ε ≤ 1 := hq.ε_half.trans (by norm_num)
  have hQ1 := h.one_le_q
  have hX := shape_one_le_X h
  have hQX := shape_q_le_X h
  have hνX : 1 / q.params.nu ≤ 10000 *
      ((qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * (2 * q.g) + 1) / (q.ε / 2)) :=
    shape_inv_precision_le h
  have hν : 0 < q.params.nu := q.params.nu_pos hq.g_ge hq.ε_pos
  have hB0' := bitN_nonneg bd q hq mu
  have hNg : (0 : ℝ) ≤ N.gates.length := Nat.cast_nonneg _
  have hY1 : 1 ≤ (bitN bd q mu + 1) ^ 3 := one_le_pow₀ (by linarith)
  have hP : 1 ≤ qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
      ((bitN bd q mu + 1) ^ 3 + N.gates.length) :=
    one_le_mul_of_one_le_of_one_le hQ1 (by linarith)
  have hBp := prepBoundN_le bd q hq hγ hζ hb hc0 hT hH hD mu nd N loadC wpC
  have hBp' : prepBoundN q mu nd N loadC wpC ≤ 2 * 10 ^ 18 *
      (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
        ((bitN bd q mu + 1) ^ 3 + N.gates.length)) +
      ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) :=
    hBp.trans (le_of_eq (by ring))
  have h1 := log_prep_le hB0 hBp' hP (by positivity) hν
  have h2 := log_q_cube_le (by linarith) hQX hX hB0'
  have h3 := log_three_div_le hν hX hνX
  have hLL := logb_X_two_le (Q := qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) (g := q.g)
    (by linarith) (by linarith [hq.g_ge]) hq.ε_pos hε1
  have hL : Real.logb 2 ((qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * q.g + 1) / q.ε) ≤
      bitN bd q mu := by
    have h4 := logb_succ_nonneg (2 ^ q.kx)
    have h5 := logb_succ_nonneg (2 ^ q.m)
    have h7 : (0 : ℝ) ≤ bd := Nat.cast_nonneg _
    have h8 : (0 : ℝ) ≤ mu := Nat.cast_nonneg _
    unfold bitN bitB
    linarith
  -- the node program inside the logarithm
  have hQ0 : 0 < qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) := by linarith
  have hsplit : Real.log (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
      ((bitN bd q mu + 1) ^ 3 + N.gates.length)) ≤
      Real.log (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * (bitN bd q mu + 1) ^ 3) +
        Real.log ((N.gates.length : ℝ) + 1) := by
    have hle : qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
        ((bitN bd q mu + 1) ^ 3 + N.gates.length) ≤
        qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * (bitN bd q mu + 1) ^ 3 *
          ((N.gates.length : ℝ) + 1) := by
      have : (bitN bd q mu + 1) ^ 3 + N.gates.length ≤
          (bitN bd q mu + 1) ^ 3 * ((N.gates.length : ℝ) + 1) := by nlinarith
      calc qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
            ((bitN bd q mu + 1) ^ 3 + N.gates.length)
          ≤ qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
            ((bitN bd q mu + 1) ^ 3 * ((N.gates.length : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_left this hQ0.le
        _ = _ := by ring
    have hpos : 0 < qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
        ((bitN bd q mu + 1) ^ 3 + N.gates.length) := by linarith
    refine (Real.log_le_log hpos hle).trans (le_of_eq ?_)
    rw [Real.log_mul (by positivity) (by positivity)]
  linarith

/-- **The tested register in `𝔟`, computed nodes**: under the hypotheses of `wordsN_le`, the
native part `22 k_x + 16 m + 24 r + 4 l + 8 b + 2 (|Z_N| + bT + bP + A_arith) + 47` of the register
tested by the zero tests is at most `3·10¹¹ (𝔟+μ+1)³ + 2 |Zn|`. -/
theorem testedN_le (bd : ℕ) (q : PubT) (hq : q.OK)
    (hγ : q.γ = gammaOf q.T q.etaH q.etaD (2 * q.g) (q.ε / 2))
    (hζ : q.params.nu ≤ 196608 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * q.ζ)
    (hb : q.b ≤ bd) (hc0 : HasBits bd q.c0) (hT : HasBits bd q.T) (hH : HasBits bd q.etaH)
    (hD : HasBits bd q.etaD) (mu : ℕ) (Zn : Type) [Fintype Zn] [DecidableEq Zn] :
    ((22 * q.kx + 16 * q.params.m + 24 * q.params.r + 4 * q.params.l + 8 * q.b +
        2 * ((mu + Fintype.card Zn + (1 + 2 * (mu + q.m + 14) +
          (4 * q.m + 62) * (mu + q.m + 14))) + (arQN q mu Zn).bT + (arQN q mu Zn).bP +
          (arQN q mu Zn).A) + 47 : ℕ) : ℝ) ≤
      3 * 10 ^ 11 * (bitN bd q mu + 1) ^ 3 + 2 * Fintype.card Zn := by
  have h := pubT_shapeOK q hq
  have hw := wordsN_le bd q hq hγ hζ hb hc0 hT hH hD mu
  obtain ⟨-, hA, hT', hP'⟩ := binary_nodes_arith_words q mu Zn
  have hσ := q.hσ
  have hℓ := h.ell_ge
  have hB0 := bitN_nonneg bd q hq mu
  have h24 : 22 * q.kx + 16 * q.params.m + 24 * q.params.r + 4 * q.params.l + 8 * q.b ≤
      24 * wordsN q mu := by
    unfold wordsN
    omega
  have hp1 : wordsN q mu + 1 ≤ (wordsN q mu + 1) ^ 3 := le_self_pow₀ (by omega) (by norm_num)
  have hn : 22 * q.kx + 16 * q.params.m + 24 * q.params.r + 4 * q.params.l + 8 * q.b +
      2 * ((mu + Fintype.card Zn + (1 + 2 * (mu + q.m + 14) +
        (4 * q.m + 62) * (mu + q.m + 14))) + (arQN q mu Zn).bT + (arQN q mu Zn).bP +
        (arQN q mu Zn).A) + 47 ≤ 8283 * (wordsN q mu + 1) ^ 3 + 2 * Fintype.card Zn := by
    generalize (wordsN q mu + 1) ^ 3 = W at hA hp1 ⊢
    generalize 1 + 2 * (mu + q.m + 14) + (4 * q.m + 62) * (mu + q.m + 14) = Z at hA ⊢
    omega
  have hn' : ((22 * q.kx + 16 * q.params.m + 24 * q.params.r + 4 * q.params.l + 8 * q.b +
      2 * ((mu + Fintype.card Zn + (1 + 2 * (mu + q.m + 14) +
        (4 * q.m + 62) * (mu + q.m + 14))) + (arQN q mu Zn).bT + (arQN q mu Zn).bP +
        (arQN q mu Zn).A) + 47 : ℕ) : ℝ) ≤
      8283 * ((wordsN q mu : ℝ) + 1) ^ 3 + 2 * Fintype.card Zn := by
    exact_mod_cast hn
  have hcube := cube_le (Nat.cast_nonneg (wordsN q mu)) hB0 (c := 300) (by linarith)
  have hY : 0 ≤ (bitN bd q mu + 1) ^ 3 := by positivity
  linarith

end Words

section TrialsBits

variable {X n : Type*} [Fintype n] [DecidableEq n] {Zs : Type*} [Fintype Zs] [DecidableEq Zs]
variable {Zn : Type} [Fintype Zn] [DecidableEq Zn]
variable {Xa : Type*} [Fintype Xa] [DecidableEq Xa] {𝒢 : Set Kind} {len : ℝ → ℕ}

/-- **Equations `ode:eq:gate-main` and `ode:eq:gate-space` in `𝔟` over a finite gate set,
computed nodes** (partial formalisation, under this package's format hypotheses, of the finite-set
statement of Theorem `ode:thm:gates`, time-dependent part with general
source nodes). Under the synthesis hypotheses of `binary_nodes_budget_trials` (`c₀, c₁ ≥ 0` the
synthesis constants) and the hypotheses of `wordsN_le`, with `G_src = |loadC| + 2 |wpC|`: the native
preparation bound is `B = prepBoundN q μ nd N loadC wpC ≤ 2·10¹⁸ q* ((𝔟+μ+1)³ + |N|) + G_src`; in
every history the synthesised protocol (ratio `2g`) uses at most
`80 g (2·10¹⁸ q* ((𝔟+μ+1)³ + |N|) + G_src) (c₁ (64 (𝔟+μ+1) + log(G_src+1) + log(|N|+1)) + c₀) +
40 g (4 (3·10¹¹ (𝔟+μ+1)³ + 2 |Zn| + 2 |Zs| + |Xa|) + 3)` gates of `𝒢`; and its register has at
most `7·10¹¹ (𝔟+μ+1)³ + 4 |Zn| + 4 |Zs| + 2 |Xa|` qubits. The validity, gate-set membership,
calls and register size are those of `binary_nodes_budget_trials`. -/
theorem binary_nodes_budget_trials_bits (hS : Synthesis 𝒢 Xa len) (hadj : AdjClosed 𝒢)
    (hzt : zeroTestKinds ⊆ 𝒢) {c₀ c₁ : ℝ} (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁)
    (hlen : ∀ ζ' : ℝ, 0 < ζ' → ζ' ≤ 1 → (len ζ' : ℝ) ≤ c₁ * Real.log (1 / ζ') + c₀)
    (bd : ℕ) (q : PubT) (hq : q.OK) (hγ : q.γ = gammaOf q.T q.etaH q.etaD (2 * q.g) (q.ε / 2))
    (hζ : q.params.nu ≤ 196608 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * q.ζ)
    (hb : q.b ≤ bd) (hc0 : HasBits bd q.c0) (hT : HasBits bd q.T) (hH : HasBits bd q.etaH)
    (hD : HasBits bd q.etaD) (mu nd : ℕ) (hnd : nd ≤ mu + q.m) (N : NodeProg q.m mu Zn)
    (hN : N.OK)
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin nd ⊕ PY q.kx q.b)
      Query)) (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin nd ⊕ PY q.kx q.b) Query))
    (hwpV : ∀ i ∈ wpC, i.Valid) :
    prepBoundN q mu nd N loadC wpC ≤ 2 * 10 ^ 18 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
        ((bitN bd q mu + 1) ^ 3 + N.gates.length) + ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) ∧
    ((nprotocol (synthPrep hS (q.params.nu / 3) (prepQN q mu nd hnd N loadC wpC))
        q.params.ratio (q.params.ratio_ge hq.g_ge)).worstCost wGateN : ℝ) ≤
      80 * q.g * ((2 * 10 ^ 18 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
          ((bitN bd q mu + 1) ^ 3 + N.gates.length) + ((nGatesN loadC : ℝ) + 2 * nGatesN wpC)) *
        (c₁ * (64 * (bitN bd q mu + 1) + Real.log ((nGatesN loadC : ℝ) + 2 * nGatesN wpC + 1) +
          Real.log ((N.gates.length : ℝ) + 1)) + c₀)) +
      40 * q.g * (4 * (3 * 10 ^ 11 * (bitN bd q mu + 1) ^ 3 + 2 * Fintype.card Zn +
        2 * Fintype.card Zs + Fintype.card Xa) + 3) ∧
    (Fintype.card (STW q.params (Fin q.kx) Zs (ZaN q.m mu Zn ⊕ SZ4 q.kx q.b) (arQN q mu Zn).bT
        (arQN q mu Zn).bP (arQN q mu Zn).A Xa) : ℝ) ≤
      7 * 10 ^ 11 * (bitN bd q mu + 1) ^ 3 + 4 * Fintype.card Zn + 4 * Fintype.card Zs +
        2 * Fintype.card Xa := by
  obtain ⟨-, hNP, hWG, -, hcard⟩ :=
    binary_nodes_budget_trials hS hadj hzt hc₀ hc₁ hlen q hq hγ mu nd hnd N hN loadC hloadV wpC
      hwpV
  have hBp := prepBoundN_le bd q hq hγ hζ hb hc0 hT hH hD mu nd N loadC wpC
  have hB0 : 0 ≤ prepBoundN q mu nd N loadC wpC := le_trans (Nat.cast_nonneg _) hNP
  have hlog := log_factorN_le bd q hq hγ hζ hb hc0 hT hH hD mu nd N loadC wpC hB0
  have hn := testedN_le bd q hq hγ hζ hb hc0 hT hH hD mu Zn
  have hg0 : 0 ≤ q.g := le_trans zero_le_one hq.g_ge
  have hY : 1 ≤ (bitN bd q mu + 1) ^ 3 := one_le_pow₀ (by linarith [bitN_nonneg bd q hq mu])
  refine ⟨hBp, ?_, ?_⟩
  · refine hWG.trans (synth_arith (by norm_num) (by norm_num) hg0 hB0 hBp ?_ hlog hc₀ hc₁ ?_)
    · apply Real.log_nonneg
      have hν : 0 < q.params.nu := q.params.nu_pos hq.g_ge hq.ε_pos
      have hν1 : q.params.nu ≤ 1 :=
        (ImprovedODEQueryBudget.precision_le_one_ten_thousandth (2 * q.g) (q.ε / 2)
          (by linarith [hq.g_ge]) (by linarith [hq.ε_half])).trans (by norm_num)
      rw [le_div_iff₀ (by positivity)]
      linarith
    · push_cast at hn ⊢
      linarith
  · rw [hcard]
    push_cast at hn hY ⊢
    linarith

end TrialsBits

end

end SparseHamiltonian.GateBinaryNodes
