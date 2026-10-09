import GateEfficientBinarySelect.Budget
import GateEfficientBitBudget.Time

/-!
# Equations `ode:eq:gate-main` and `ode:eq:gate-space` in `𝔟`, branch-dependent meshes

The word budget of equation `ode:eq:gate-word-budget` for the solver on branch-dependent meshes
from time-indexed binary data, with the bit-length model of `GateEfficientBitBudget` (`HasBits`,
`bitB`): for the public data `q` with the public rescaling `γ = gammaOf T η_H η_D (2g) (ε/2)`,
an arithmetic accuracy `ζ ≥ ν/(196608 q*)`, stored bits `b ≤ b_data` and `c₀`, `T`, `η_H`, `η_D`
of bit length `b_data`,

`𝔟 = bitB b_data (2^k_x) (2^m) (2^m) q* g ε
   = b_data + log₂(N+1) + log₂(M+1) + log₂(m_nodes+1) + log₂((q* g + 1)/ε)`

with the time mesh `M = 2^m`, the `m_nodes = 2^m` nodes of the positive source quadrature, and
`q* = qOf s T η_H η_D (2g) (ε/2)`. The decoder scale `κ` of the branch operation carries the
extra factor `2^(-m)` of the duration word, which costs `m ≤ log₂(M+1)` further bits.

* `wordsB_le` (the key lemma): `𝔴 + ℓ ≤ 300 (𝔟 + 1)` for the register words `𝔴 = wordsB q`.
* `binary_select_budget_bits`: in every history the native protocol uses at most
  `2·10²⁰ g [q* (𝔟+1)³ + G_src + |Zs|]` elementary gates (`G_src = |loadC| + 2 |wpC|`) and its
  register has at most `3·10¹¹ (𝔟+1)³ + 2 |Zs|` qubits, together with every conclusion of
  `binary_select_budget_words` and `binary_select_budget`.
* `select_gates_bits`: the gates `G_sel` and work wires `A_sel` of coherent selection
  (`binary_native_gate_select`) are at most `11·10¹² d (𝔟+1)³` and `2·10¹¹ (𝔟+1)³ + 3`
  (equation `ode:eq:gate-select-gates` in `𝔟`; for the circuit itself see
  `binary_select_lemma_bits`).
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateBinarySelect

noncomputable section
open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
open SparseHamiltonian.GateBinary SparseHamiltonian.GateBinaryODE SparseHamiltonian.OracleCircuit
open SparseHamiltonian.GateBinaryODETime (PubT gridP)
open SparseHamiltonian.GateBitBudget
open SparseHamiltonian.GateODEBudget (gammaOf qOf binary_ode_time_sizes pubT_shapeOK
  gammaOf_le_one)
open ImprovedODEQueryBudget (precision logBudget radius)
open NativeSparseBlockEncoding (Data Query)
open scoped InnerProduct

/-- **The register words in the word budget** (branch-dependent meshes; the key lemma of
equations `ode:eq:gate-main` and `ode:eq:gate-space` in `𝔟`). For the public data `q` with the
public rescaling `γ = gammaOf T η_H η_D (2g) (ε/2)`, an arithmetic accuracy
`ζ ≥ ν/(196608 q*)` (`q* = qOf s T η_H η_D (2g) (ε/2)`), stored bits `b ≤ b_data` and `c₀`, `T`,
`η_H`, `η_D` of bit length `b_data`, the register words
`𝔴 = wordsB q = k_x + b + m + r + l + F + n_c + ⌈log₂ ⌈κ⌉⌉ + ⌈log₂ ⌈1/κ⌉⌉` (decoder scale
`κ = γ √(4s) c₀ / (2^(m + F + 10) ρ)`) and `ℓ = log(1/ν)` satisfy `𝔴 + ℓ ≤ 300 (𝔟 + 1)` for
`𝔟 = bitB b_data (2^k_x) (2^m) (2^m) q* g ε` (the time mesh `M = 2^m` and the `2^m` source
nodes). -/
theorem wordsB_le (bd : ℕ) (q : PubT) (hq : q.OK)
    (hγ : q.γ = gammaOf q.T q.etaH q.etaD (2 * q.g) (q.ε / 2))
    (hζ : q.params.nu ≤ 196608 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * q.ζ)
    (hb : q.b ≤ bd) (hc0 : HasBits bd q.c0) (hT : HasBits bd q.T) (hH : HasBits bd q.etaH)
    (hD : HasBits bd q.etaD) :
    (wordsB q : ℝ) + logBudget (2 * q.g) (q.ε / 2) ≤
      300 * (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
        (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) := by
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
  obtain ⟨wκ, wκi⟩ := kap_words bd q.kx q.s (q.m + q.F + 10) h
    (Nat.pow_le_pow_right (by norm_num) q.hσ) hc0 hq.c0_pos hT hH hD
  have hkap : kapQ q = gammaOf q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
      Real.sqrt (4 * (q.s : ℝ)) * q.c0 /
        (2 ^ (q.m + q.F + 10) * (q.etaH + radius (2 * q.g) (q.ε / 2) * q.etaD)) := by
    rw [← hγ]
    rfl
  rw [← hkap] at wκ wκi
  simp only [Nat.cast_add, Nat.cast_ofNat] at wκi
  have hLL := logb_X_two_le (Q := qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) (g := q.g)
    (by linarith) (by linarith [hq.g_ge]) hq.ε_pos hε1
  have hw : (wordsB q : ℝ) = q.kx + q.b + q.m + q.params.r + q.params.l + q.F +
      (Cordic.nOf (q.ζ / 2) : ℝ) + (Nat.clog 2 ⌈kapQ q⌉₊ : ℝ) +
      (Nat.clog 2 ⌈1 / kapQ q⌉₊ : ℝ) := by
    unfold wordsB
    push_cast
    rfl
  have hb0 : bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
      (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε =
      bd + Real.logb 2 (((2 ^ q.kx : ℕ) : ℝ) + 1) + Real.logb 2 (((2 ^ q.m : ℕ) : ℝ) + 1) +
        Real.logb 2 (((2 ^ q.m : ℕ) : ℝ) + 1) +
        Real.logb 2 ((qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * q.g + 1) / q.ε) := rfl
  rw [hw, hb0]
  have hL0 := Real.logb_nonneg one_lt_two hX
  have hN0 := logb_succ_nonneg (2 ^ q.kx)
  have hM0 := logb_succ_nonneg (2 ^ q.m)
  have hbd0 : (0 : ℝ) ≤ bd := Nat.cast_nonneg _
  have hL'0 : 0 ≤ Real.logb 2
      ((qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * q.g + 1) / q.ε) := by
    apply Real.logb_nonneg one_lt_two
    rw [le_div_iff₀ hq.ε_pos]
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2))
      (by linarith [hq.g_ge] : (0 : ℝ) ≤ q.g)
    linarith
  linarith

/-- **The gates and work wires of coherent selection in `𝔟`** (equation
`ode:eq:gate-select-gates`, under the hypotheses of `wordsB_le`, for every `d`; for the circuit
itself at `δ = 4ν` see `binary_select_lemma_bits`). For the native selection circuit of
`binary_native_gate_select` with filter degree `d`, the gates beyond those of the released
circuit, `G_sel = 84 d (σ+3) + 6 d G_C`, are at most
`11·10¹² d (𝔟+1)³`, and the work wires added to the released register,
`A_sel = |ZA| + 6 k_x + 4 b + bT + bP + A_arith + 3`, at most `2·10¹¹ (𝔟+1)³ + 3`, with
`𝔟 = bitB b_data (2^k_x) (2^m) (2^m) q* g ε`. -/
theorem select_gates_bits (bd : ℕ) (q : PubT) (hq : q.OK)
    (hγ : q.γ = gammaOf q.T q.etaH q.etaD (2 * q.g) (q.ε / 2))
    (hζ : q.params.nu ≤ 196608 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * q.ζ)
    (hb : q.b ≤ bd) (hc0 : HasBits bd q.c0) (hT : HasBits bd q.T) (hH : HasBits bd q.etaH)
    (hD : HasBits bd q.etaD) (d : ℕ) :
    ((84 * d * (q.σ + 3) + 6 * d * (2 * ((apG q.kx q.b q.m q.params.l).length + (28 * q.kx + 2)) +
        2 * (arQ q).circ.length + (2 * (arQ q).bP + (arQ q).bT + 1)) : ℕ) : ℝ) ≤
      11 * 10 ^ 12 * d * (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
        (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ 3 ∧
    (((1 + 2 * (2 * q.m + 14) + (4 * q.m + 62) * (2 * q.m + 14)) + (6 * q.kx + 4 * q.b) +
        (arQ q).bT + (arQ q).bP + (arQ q).A + 3 : ℕ) : ℝ) ≤
      2 * 10 ^ 11 * (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
        (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ 3 + 3 := by
  obtain ⟨h1, h2⟩ := select_gates_words q d
  have hw := wordsB_le bd q hq hγ hζ hb hc0 hT hH hD
  have h := pubT_shapeOK q hq
  have hℓ := h.ell_ge
  have hε1 : q.ε ≤ 1 := hq.ε_half.trans (by norm_num)
  have hg0 : 0 ≤ q.g := le_trans zero_le_one hq.g_ge
  have hB0 : 0 ≤ bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
      (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε :=
    bitB_nonneg _ _ _ _ (mul_nonneg (by linarith [h.one_le_q]) hg0) hq.ε_pos hε1
  have hw' : (wordsB q : ℝ) ≤ 300 * (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
      (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) := by linarith
  have hcube := cube_le (Nat.cast_nonneg (wordsB q)) hB0 hw'
  have hY : 0 ≤ (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
      (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ 3 := by positivity
  generalize (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
      (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ 3 = Y at hcube hY ⊢
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  constructor
  · have h1' : ((84 * d * (q.σ + 3) + 6 * d * (2 * ((apG q.kx q.b q.m q.params.l).length +
        (28 * q.kx + 2)) + 2 * (arQ q).circ.length + (2 * (arQ q).bP + (arQ q).bT + 1)) : ℕ) :
        ℝ) ≤ 393500 * d * ((wordsB q : ℝ) + 1) ^ 3 := by exact_mod_cast h1
    have h3 : (393500 : ℝ) * d * ((wordsB q : ℝ) + 1) ^ 3 ≤ 393500 * d * ((300 + 1) ^ 3 * Y) :=
      mul_le_mul_of_nonneg_left hcube (by positivity)
    have h4 : (393500 : ℝ) * d * ((300 + 1) ^ 3 * Y) ≤ 11 * 10 ^ 12 * d * Y := by
      have e : (393500 : ℝ) * d * ((300 + 1) ^ 3 * Y) = 10731099543500 * (d * Y) := by ring
      have e' : (11 * 10 ^ 12 : ℝ) * d * Y = 11000000000000 * (d * Y) := by ring
      rw [e, e']
      have : 0 ≤ (d : ℝ) * Y := mul_nonneg hd0 hY
      linarith
    linarith
  · have h2' : (((1 + 2 * (2 * q.m + 14) + (4 * q.m + 62) * (2 * q.m + 14)) +
        (6 * q.kx + 4 * q.b) + (arQ q).bT + (arQ q).bP + (arQ q).A + 3 : ℕ) : ℝ) ≤
        4096 * ((wordsB q : ℝ) + 1) ^ 3 + 3 := by exact_mod_cast h2
    linarith

section Budget

variable {X n : Type*} [Fintype n] [DecidableEq n] {Zs : Type*} [Fintype Zs] [DecidableEq Zs]

/-- **Equations `ode:eq:gate-main` and `ode:eq:gate-space` in the word budget `𝔟`,
branch-dependent meshes** (Theorem `ode:thm:gates`, time-dependent part, with the
branch-dependent meshes of Lemma `ode:lem:gate-select`, equation `ode:eq:gate-word-budget`).
Let the public data `q` have the public rescaling
`γ = gammaOf T η_H η_D (2g) (ε/2)` and an arithmetic accuracy `ζ ≥ ν/(196608 q*)`
(`q* = qOf s T η_H η_D (2g) (ε/2)`, `ν = ε/(40000 g)`, `ℓ = log(1/ν)`), let the stored bits be
`b ≤ b_data` and `c₀`, `T`, `η_H`, `η_D` have bit length `b_data`, and put
`𝔟 = bitB b_data (2^k_x) (2^m) (2^m) q* g ε` (dimension `N = 2^k_x`, time mesh `M = 2^m`, and
`2^m` source nodes). For the time-indexed binary data and the valid circuits `loadC`, `wpC` of
`binary_select_solver`, in every history the native protocol (ratio `2g`) uses at most
`2·10²⁰ g [q* (𝔟+1)³ + G_src + |Zs|]` elementary gates (`G_src = |loadC| + 2 |wpC|`), and its
register has at most `3·10¹¹ (𝔟+1)³ + 2 |Zs|` qubits. The register words satisfy
`𝔴 + ℓ ≤ 300 (𝔟 + 1)` (`𝔴 = wordsB q`), and every conclusion of
`binary_select_budget_words` and `binary_select_budget` is kept:
at most `6·10¹² g [q* (𝔴 + ℓ + 1)³ + G_src + |Zs|]` gates and `10000 (𝔴+1)³ + 2 |Zs|` qubits; at
most `73746000 g [q* (G_C + k_x + σ + m + r + ℓ (l+1) + 8) + G_src + A]` gates; at most
`7864320 g q*` calls of each coherent sampled-time oracle besides `80 g` times the calls of
`loadC` and twice those of `wpC`; the register size; and, for every input and instance as in
`binary_select_solver` with `98304 q* ζ + 3 ζs ≤ ν`, the guarantees `NOutcome`. -/
theorem binary_select_budget_bits (bd : ℕ) (q : PubT) (hq : q.OK)
    (hγ : q.γ = gammaOf q.T q.etaH q.etaD (2 * q.g) (q.ε / 2))
    (hζ : q.params.nu ≤ 196608 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * q.ζ)
    (hb : q.b ≤ bd) (hc0 : HasBits bd q.c0) (hT : HasBits bd q.T) (hH : HasBits bd q.etaH)
    (hD : HasBits bd q.etaD)
    (D : Data (X × Fin (2 ^ (2 * q.m))) n (Cfg (VW q.b)) q.s) (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (hdec : ∀ e z, D.decode e z = (q.c0 : ℂ) * gauss z)
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin (2 * q.m) ⊕ PY q.kx q.b)
      Query)) (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin (2 * q.m) ⊕ PY q.kx q.b) Query))
    (hwpV : ∀ i ∈ wpC, i.Valid) :
    ((nprotocol (prepQ q loadC wpC) q.params.ratio (q.params.ratio_ge hq.g_ge)).worstCost
        wGateN : ℝ) ≤
      2 * 10 ^ 20 * q.g * (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
          (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
            (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ 3 +
        ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) + Fintype.card Zs) ∧
    (Fintype.card (TNW q.params (Fin q.kx) Zs (ZA q.m ⊕ SZ4 q.kx q.b) (arQ q).bT (arQ q).bP
        (arQ q).A) : ℝ) ≤
      3 * 10 ^ 11 * (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
          (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ 3 +
        2 * Fintype.card Zs ∧
    (wordsB q : ℝ) + logBudget (2 * q.g) (q.ε / 2) ≤
      300 * (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
        (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ∧
    ((nprotocol (prepQ q loadC wpC) q.params.ratio (q.params.ratio_ge hq.g_ge)).worstCost
        wGateN : ℝ) ≤
      6 * 10 ^ 12 * q.g * (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
          ((wordsB q : ℝ) + logBudget (2 * q.g) (q.ε / 2) + 1) ^ 3 +
        ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) + Fintype.card Zs) ∧
    Fintype.card (TNW q.params (Fin q.kx) Zs (ZA q.m ⊕ SZ4 q.kx q.b) (arQ q).bT (arQ q).bP
        (arQ q).A) ≤
      10000 * (wordsB q + 1) ^ 3 + 2 * Fintype.card Zs ∧
    ((nprotocol (prepQ q loadC wpC) q.params.ratio (q.params.ratio_ge hq.g_ge)).worstCost
        wGateN : ℝ) ≤
      73746000 * q.g * (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
          (((2 * ((apG q.kx q.b q.m q.params.l).length + (28 * q.kx + 2)) +
              2 * (arQ q).circ.length + (2 * (arQ q).bP + (arQ q).bT + 1) : ℕ) : ℝ) +
            q.kx + q.σ + q.params.m + q.params.r +
            logBudget (2 * q.g) (q.ε / 2) * ((q.params.l : ℝ) + 1) + 8) +
        ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) +
        ((q.kx : ℝ) + Fintype.card Zs +
          (((1 + 2 * (2 * q.m + 14) + (4 * q.m + 62) * (2 * q.m + 14)) +
            (6 * q.kx + 4 * q.b) : ℕ) : ℝ) + (arQ q).bT + (arQ q).bP + (arQ q).A)) ∧
    (∀ c : Query → Bool,
      ((nprotocol (prepQ q loadC wpC) q.params.ratio (q.params.ratio_ge hq.g_ge)).worstCost
        (wCallN c) : ℝ) ≤
      7864320 * q.g * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
          ((if c Query.rowLocation then 1 else 0) + (if c Query.columnLocation then 1 else 0) +
            (if c Query.value then 1 else 0)) +
        80 * q.g * ((nCallsN c loadC : ℝ) + 2 * nCallsN c wpC)) ∧
    Fintype.card (TNW q.params (Fin q.kx) Zs (ZA q.m ⊕ SZ4 q.kx q.b) (arQ q).bT (arQ q).bP
        (arQ q).A) =
      22 * q.kx + 16 * q.params.m + 24 * q.params.r + 4 * q.params.l + 8 * q.b +
        2 * ((1 + 2 * (2 * q.m + 14) + (4 * q.m + 62) * (2 * q.m + 14)) + (arQ q).bT +
          (arQ q).bP + (arQ q).A) + 2 * Fintype.card Zs + 47 ∧
    ∀ x : X,
      (∀ r i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaH ^ 2) →
      (∀ r j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaH ^ 2) →
      (∀ r i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaD ^ 2) →
      (∀ r j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaD ^ 2) →
      (∀ r, ∀ w : EuclideanSpace ℂ n, 0 ≤ (inner ℂ w (SparseStateOverlap.matrixOperator
        (ODEMatrixEnergy.dissipativePart (D.matrix (x, r))) w)).re) →
      ∀ (Jl : Bool × (Fin q.m → Bool) → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
        (Wp : Matrix (Cfg (Fin (q.m + 1))) (Cfg (Fin (q.m + 1))) ℂ) (wq : ℕ → ℝ)
        (fv : ℕ → Reg (Fin q.kx) ℂ) (G : ℝ → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
        (bf xs : ℝ → Reg (Fin q.kx) ℂ) (ys : Bool × (Fin q.m → Bool) → ℝ → Reg (Fin q.kx) ℂ)
        (βG δG κ ζs : ℝ),
      0 ≤ ζs →
      ApproxOn CleanX (nrun (primsT (R := ℂ) (m := 2 * q.m) D en x) loadC)
        (liftB (loadIdeal Jl)) ζs →
      ApproxOn CleanX (nrun (primsT (R := ℂ) (m := 2 * q.m) D en x) wpC) (liftB (matOp Wp)) ζs →
      98304 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * q.ζ + 3 * ζs ≤ q.params.nu →
      RestB q D en x Jl Wp wq fv G bf xs ys βG δG κ →
      NOutcome (prepQ q loadC wpC) q.params.ratio q.ε (q.params.ratio_ge hq.g_ge)
        (primsT (R := ℂ) (m := 2 * q.m) D en x) (xs q.T) := by
  have h := pubT_shapeOK q hq
  have hw := wordsB_le bd q hq hγ hζ hb hc0 hT hH hD
  obtain ⟨hWg, hWc⟩ :=
    binary_select_budget_words q hq hγ D en hrange hdec loadC hloadV wpC hwpV
  obtain ⟨hG, hC, hcard, hout⟩ :=
    binary_select_budget q hq hγ D en hrange hdec loadC hloadV wpC hwpV
  have hε1 : q.ε ≤ 1 := hq.ε_half.trans (by norm_num)
  have hQ1 := h.one_le_q
  have hg0 : 0 ≤ q.g := le_trans zero_le_one hq.g_ge
  have hB0 : 0 ≤ bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
      (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε :=
    bitB_nonneg _ _ _ _ (mul_nonneg (by linarith) hg0) hq.ε_pos hε1
  have hℓ := h.ell_ge
  have hw0 : (0 : ℝ) ≤ wordsB q := Nat.cast_nonneg _
  refine ⟨?_, ?_, hw, hWg, hWc, hG, hC, hcard, hout⟩
  · -- gates
    have hcube := cube_le (by linarith) hB0 hw
    refine hWg.trans (budget_mono (by norm_num) hg0 (by linarith) (by positivity)
      (add_nonneg (Nat.cast_nonneg _) (mul_nonneg (by norm_num) (Nat.cast_nonneg _)))
      (Nat.cast_nonneg _) (by norm_num) hcube (by norm_num))
  · -- qubits
    have hcube := cube_le hw0 hB0 (c := 300) (by linarith)
    have hc : ((Fintype.card (TNW q.params (Fin q.kx) Zs (ZA q.m ⊕ SZ4 q.kx q.b) (arQ q).bT
        (arQ q).bP (arQ q).A) : ℕ) : ℝ) ≤
        10000 * ((wordsB q : ℝ) + 1) ^ 3 + 2 * Fintype.card Zs := by
      exact_mod_cast hWc
    have hY : 0 ≤ (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
        (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ 3 := by positivity
    linarith

end Budget

end

end SparseHamiltonian.GateBinarySelect
