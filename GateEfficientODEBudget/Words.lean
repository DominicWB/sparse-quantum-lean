import GateEfficientODEBudget.Time

/-!
# The budget as a polynomial in the register words

Equation `ode:eq:gate-main` bounds the gates by `C ḡ [q P(𝔟) + G_src + A_src]` and equation
`ode:eq:gate-space` the qubits by `P(𝔟) + C A_src`, for a fixed polynomial `P` determined by the
arithmetic and decoding implementations. For the solvers from binary data the arithmetic is the
released `GateBinaryODE.odeArith` (respectively `GateBinaryODETime.odeArT`) with the released
counts `Pub.ar_counts` (respectively `PubT.ar_counts`); its size is governed by the register
words of the construction:

* `words q` (constant coefficients): `k_x + b + m + r + k + l + F + n_c + ⌈log₂ ⌈κ⌉⌉ +
  ⌈log₂ ⌈1/κ⌉⌉`, with `k_x` the system qubits, `b` the stored bits, `m`, `r` the simulator words,
  `k`, `l` the quadrature and LCHS words, `F` the fractional bits of the LCHS step, `n_c` the CORDIC
  steps for the accuracy `ζ/2`, and `κ` the decoder scale; `wordsT q` (time-dependent
  coefficients) is the same without the quadrature word.
* `binary_arith_words`, `binary_time_arith_words`: the per-call gates
  `G_C = 2 (28 k_x + 2) + 2 |arith| + 2 bP + bT + 1` are at most `65536 (𝔴+1)³`, the arithmetic
  work wires at most `4096 (𝔴+1)³`, and `bT, bP ≤ 5 (𝔴+1)`.
* `binary_ode_budget_words`, `binary_ode_time_budget_words`: with the public rescaling of
  `binary_ode_budget` (respectively `binary_ode_time_budget`) the native protocol uses at most
  `3·10¹² g [q* (𝔴 + ℓ + 1)³ + G_src + |Zs|]` (respectively `6·10¹²`) elementary gates, and its
  register has at most `10000 (𝔴+1)³ + 2 |Zs|` qubits.

This is equations `ode:eq:gate-main` and `ode:eq:gate-space` with `P(x) = C (x+1)³` in the word
parameter `𝔴 + ℓ` in place of `𝔟` and `A_src = |Zs|`. The words `m`, `r`, `k`, `l` are
`O(log(q*/ν))` (`binary_ode_sizes`, `binary_ode_time_sizes`); `F`, `n_c` and the bits of `κ` are
not bounded in Lean in terms of `𝔟` (in the paper they are `O(𝔟)`; the Lean model has real public
parameters, a free arithmetic accuracy and a rescaling without the floor `p^{-1/2}`, see the
statement guide `GateEfficientODEBudget/Statements.lean`).
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateODEBudget

noncomputable section
open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
open SparseHamiltonian.GateBinary SparseHamiltonian.GateBinaryODE
open SparseHamiltonian.GateBinaryODETime SparseHamiltonian.OracleCircuit
open ImprovedODEQueryBudget (logBudget)
open NativeSparseBlockEncoding (Data Query)
open scoped InnerProduct

/-! ### Arithmetic -/

/-- `⌈log₂ (n + 2)⌉ ≤ n + 1`. -/
theorem clog_two_add_two_le (n : ℕ) : Nat.clog 2 (n + 2) ≤ n + 1 := by
  apply Nat.clog_le_of_le_pow
  have := Nat.lt_two_pow_self (n := n + 1)
  omega

/-- The CORDIC words have at most `2 n + 5` bits. -/
theorem wordOf_le (n : ℕ) : Cordic.wordOf n ≤ 2 * n + 5 := by
  have := clog_two_add_two_le n
  unfold Cordic.wordOf
  omega

/-- **Polynomial bounds for the released arithmetic counts**: for the integer layout width
`L ≤ 14 (w+1)`, the number of registers `R ≤ 62 (w+1)`, the CORDIC width `Wc ≤ 37 (w+1)²`, the
CORDIC steps `N ≤ w` and the CORDIC words `W ≤ 5 (w+1)`, the gates of the program and of CORDIC
are at most `28355 (w+1)³` and their work wires at most `1231 (w+1)³`. -/
theorem arith_poly (L R Wc N W w : ℕ) (hL : L ≤ 14 * (w + 1)) (hR : R ≤ 62 * (w + 1))
    (hWc : Wc ≤ 37 * ((w + 1) * (w + 1))) (hN : N ≤ w) (hW : W ≤ 5 * (w + 1)) :
    26 * L * R + (156 * Wc * (N + 1) + W + 2 * W) ≤ 28355 * (w + 1) ^ 3 ∧
    (1 + 2 * L + R * L) + (1 + 2 * Wc + (6 * (N + 1) + 1) * Wc) ≤ 1231 * (w + 1) ^ 3 := by
  have hp2 : (w + 1) * (w + 1) ≤ (w + 1) ^ 3 := by
    have e : (w + 1) ^ 3 = (w + 1) * (w + 1) * (w + 1) := by ring
    rw [e]
    exact Nat.le_mul_of_pos_right _ (by omega)
  have hp1 : w + 1 ≤ (w + 1) ^ 3 := le_self_pow₀ (by omega) (by norm_num)
  have h1 : 26 * L * R ≤ 22568 * ((w + 1) * (w + 1)) := by
    calc 26 * L * R ≤ 26 * (14 * (w + 1)) * (62 * (w + 1)) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 26 hL) hR
      _ = 22568 * ((w + 1) * (w + 1)) := by ring
  have h2 : 156 * Wc * (N + 1) ≤ 5772 * (w + 1) ^ 3 := by
    calc 156 * Wc * (N + 1) ≤ 156 * (37 * ((w + 1) * (w + 1))) * (w + 1) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 156 hWc) (by omega)
      _ = 5772 * (w + 1) ^ 3 := by ring
  have h3 : R * L ≤ 868 * ((w + 1) * (w + 1)) := by
    calc R * L ≤ 62 * (w + 1) * (14 * (w + 1)) := Nat.mul_le_mul hR hL
      _ = 868 * ((w + 1) * (w + 1)) := by ring
  have h4 : (6 * (N + 1) + 1) * Wc ≤ 259 * (w + 1) ^ 3 := by
    calc (6 * (N + 1) + 1) * Wc ≤ 7 * (w + 1) * (37 * ((w + 1) * (w + 1))) :=
          Nat.mul_le_mul (by omega) hWc
      _ = 259 * (w + 1) ^ 3 := by ring
  constructor
  · omega
  · omega

/-- **The released arithmetic counts as polynomials in the words**: the counts of
`GateBinaryODE.odeArith_counts` for `b` stored bits, `k` quadrature bits, `l` LCHS bits, `F`
fractional bits, `N` CORDIC steps with words `W ≤ 2 N + 5`, the stage-2 scale bits
`G2 ≥ N + 5` (`Cordic.g2Of`) and the bits `LK` of `1/κ` (`Cordic.lkOf`), when
`b + k + l + F + G2 + LK ≤ w + 5`. -/
theorem arith_words (b k l F N G2 LK W w : ℕ) (hx : b + k + l + F + G2 + LK ≤ w + 5)
    (hN : N + 5 ≤ G2) (hW : W ≤ 2 * N + 5) :
    26 * (b + k + F + l + 14) * (31 + (F + 2) + 3 + (F + l + 5 + 1) + 2 * (k + F + l + 9 + 1)) +
        (156 * (2 * (N * N) + G2 + LK + (b + k + F + l + 14) + 2 * W + 8) * (N + 1) + W +
          2 * W) ≤ 28355 * (w + 1) ^ 3 ∧
    (1 + 2 * (b + k + F + l + 14) + (31 + (F + 2) + 3 + (F + l + 5 + 1) +
        2 * (k + F + l + 9 + 1)) * (b + k + F + l + 14)) +
      (1 + 2 * (2 * (N * N) + G2 + LK + (b + k + F + l + 14) + 2 * W + 8) +
        (6 * (N + 1) + 1) * (2 * (N * N) + G2 + LK + (b + k + F + l + 14) + 2 * W + 8)) ≤
      1231 * (w + 1) ^ 3 ∧
    W ≤ 5 * (w + 1) := by
  have hNN : N * N ≤ w * w := Nat.mul_le_mul (by omega) (by omega)
  have hWc : 2 * (N * N) + G2 + LK + (b + k + F + l + 14) + 2 * W + 8 ≤
      37 * ((w + 1) * (w + 1)) := by
    have e : (w + 1) * (w + 1) = w * w + 2 * w + 1 := by ring
    rw [e]
    omega
  obtain ⟨h1, h2⟩ := arith_poly (b + k + F + l + 14)
    (31 + (F + 2) + 3 + (F + l + 5 + 1) + 2 * (k + F + l + 9 + 1))
    (2 * (N * N) + G2 + LK + (b + k + F + l + 14) + 2 * W + 8) N W w (by omega) (by omega) hWc
    (by omega) (by omega)
  exact ⟨h1, h2, by omega⟩

/-- The arithmetic of the gate budget in the words: `q* (G_C + … + ℓ (l+1) + 8)` and the
wires are absorbed in `q* (w + ℓ + 1)³`. -/
theorem words_gate_arith (c C g Q ℓ w GC Sm l Gs Zs Ap : ℝ) (hcC : 69664 * c ≤ C) (hc : 0 ≤ c)
    (hg : 0 ≤ g) (hQ : 1 ≤ Q) (hℓ : 1 ≤ ℓ) (hw : 0 ≤ w) (hGC : GC ≤ 65536 * (w + 1) ^ 3)
    (hSm : Sm ≤ 2 * w) (hl0 : 0 ≤ l) (hl : l ≤ w) (hAp : Ap ≤ 4117 * (w + 1) ^ 3)
    (hGs : 0 ≤ Gs) (hZs : 0 ≤ Zs) :
    c * g * (Q * (GC + Sm + ℓ * (l + 1) + 8) + Gs + (Zs + Ap)) ≤
      C * g * (Q * (w + ℓ + 1) ^ 3 + Gs + Zs) := by
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
  have hS : GC + Sm + ℓ * (l + 1) + 8 ≤ 65547 * Y := by linarith
  have hQ0 : 0 ≤ Q := by linarith
  have hY0 : 0 ≤ Y := by linarith
  have hQY : Y ≤ Q * Y := le_mul_of_one_le_left hY0 hQ
  have h1 := mul_le_mul_of_nonneg_left hS hQ0
  have hin : Q * (GC + Sm + ℓ * (l + 1) + 8) + Gs + (Zs + Ap) ≤ 69664 * (Q * Y + Gs + Zs) := by
    linarith
  have hpos : 0 ≤ Q * Y + Gs + Zs := by positivity
  calc c * g * (Q * (GC + Sm + ℓ * (l + 1) + 8) + Gs + (Zs + Ap))
      ≤ c * g * (69664 * (Q * Y + Gs + Zs)) :=
        mul_le_mul_of_nonneg_left hin (mul_nonneg hc hg)
    _ = 69664 * c * g * (Q * Y + Gs + Zs) := by ring
    _ ≤ C * g * (Q * Y + Gs + Zs) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcC hg) hpos

/-! ### Constant coefficients -/

/-- **The register words of the solver from binary data** (constant coefficients): the system
qubits `k_x`, the stored bits `b`, the simulator words `m`, `r`, the quadrature and LCHS words `k`,
`l`, the fractional bits `F` of the LCHS step, the CORDIC steps `n_c` for the accuracy `ζ/2` and the
bits `⌈log₂ ⌈κ⌉⌉`, `⌈log₂ ⌈1/κ⌉⌉` of the decoder scale `κ`. -/
def words (q : Pub) : ℕ :=
  q.kx + q.b + q.params.m + q.params.r + q.params.k + q.params.l + q.F + Cordic.nOf (q.ζ / 2) +
    Nat.clog 2 ⌈q.kap⌉₊ + Nat.clog 2 ⌈1 / q.kap⌉₊

/-- **The per-call cost and the arithmetic wires as polynomials in the words** (constant
coefficients, the polynomial `P` of `ode:eq:gate-main` for the released arithmetic): the gates
`G_C = 2 (28 k_x + 2) + 2 |arith| + 2 bP + bT + 1` of one private call are at most
`65536 (𝔴+1)³`, the work wires of the arithmetic at most `4096 (𝔴+1)³`, and the CORDIC output words
`bT, bP ≤ 5 (𝔴+1)`, `𝔴 = words q`. -/
theorem binary_arith_words (q : Pub) :
    2 * (28 * q.kx + 2) + 2 * q.ar.circ.length + (2 * q.ar.bP + q.ar.bT + 1) ≤
      65536 * (words q + 1) ^ 3 ∧
    q.ar.A ≤ 4096 * (words q + 1) ^ 3 ∧ q.ar.bT ≤ 5 * (words q + 1) ∧
    q.ar.bP ≤ 5 * (words q + 1) := by
  obtain ⟨hc, hA, hT, hP⟩ := q.ar_counts
  have hg2 : Cordic.g2Of (Cordic.nOf (q.ζ / 2)) q.kap =
      Nat.clog 2 ⌈q.kap⌉₊ + Cordic.nOf (q.ζ / 2) + 5 := by
    unfold Cordic.g2Of
    rfl
  have hlk : Cordic.lkOf q.kap = Nat.clog 2 ⌈1 / q.kap⌉₊ := by
    unfold Cordic.lkOf
    rfl
  have hx : q.b + q.params.k + q.params.l + q.F + Cordic.g2Of (Cordic.nOf (q.ζ / 2)) q.kap +
      Cordic.lkOf q.kap ≤ words q + 5 := by
    unfold words
    omega
  obtain ⟨h1, h2, h3⟩ := arith_words q.b q.params.k q.params.l q.F (Cordic.nOf (q.ζ / 2))
    (Cordic.g2Of (Cordic.nOf (q.ζ / 2)) q.kap) (Cordic.lkOf q.kap)
    (Cordic.wordOf (Cordic.nOf (q.ζ / 2))) (words q) hx (by omega) (wordOf_le _)
  have hlen : q.ar.circ.length ≤ 28355 * (words q + 1) ^ 3 := hc.trans h1
  have hA' : q.ar.A ≤ 1231 * (words q + 1) ^ 3 := hA.le.trans h2
  have hT' : q.ar.bT ≤ 5 * (words q + 1) := hT.le.trans h3
  have hP' : q.ar.bP ≤ 5 * (words q + 1) := hP.le.trans h3
  have hkx : q.kx ≤ words q := by
    unfold words
    omega
  have hp1 : words q + 1 ≤ (words q + 1) ^ 3 := le_self_pow₀ (by omega) (by norm_num)
  refine ⟨by omega, by omega, hT', hP'⟩

section Budget

variable {X n : Type*} [Fintype n] [DecidableEq n] {Zs : Type*} [Fintype Zs] [DecidableEq Zs]

/-- **Equations `ode:eq:gate-main` and `ode:eq:gate-space` in the words, constant
coefficients.** With the public rescaling `γ = gammaOf T η_H η_D g ε` of `binary_ode_budget`,
`q* = qOf s T η_H η_D g ε`, `ℓ = log(1/ν)` and `𝔴 = words q`, for the binary data and the valid
source circuits of `binary_ode_solver`, in every history the native protocol uses at most
`3·10¹² g [q* (𝔴 + ℓ + 1)³ + G_src + |Zs|]` elementary gates (`G_src = |srcC 0| + |srcC 1|`,
`|Zs|` the source scratch), and its register has at most `10000 (𝔴+1)³ + 2 |Zs|` qubits. The calls
and the guarantees are those of `binary_ode_budget`. -/
theorem binary_ode_budget_words (q : Pub) (hq : q.OK)
    (hγ : q.γ = gammaOf q.T q.etaH q.etaD q.g q.ε)
    (D : Data X n (Cfg (VW q.b)) q.s) (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (hdec : ∀ e z, D.decode e z = (q.c0 : ℂ) * gauss z)
    (srcC : Bool → List (NInstr ((Unit ⊕ Fin q.kx) ⊕ Zs) (PY q.kx q.b) Query))
    (hsrcV : ∀ c, ∀ i ∈ srcC c, i.Valid) :
    ((nprotocol (q.prep srcC) q.g hq.g_ge).worstCost wGateN : ℝ) ≤
      3 * 10 ^ 12 * q.g * (qOf q.s q.T q.etaH q.etaD q.g q.ε *
          ((words q : ℝ) + logBudget q.g q.ε + 1) ^ 3 +
        ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true)) + Fintype.card Zs) ∧
    Fintype.card (NW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) ≤
      10000 * (words q + 1) ^ 3 + 2 * Fintype.card Zs := by
  obtain ⟨hW, -, hcard, -⟩ := binary_ode_budget q hq hγ D en hrange hdec srcC hsrcV
  obtain ⟨hGC, hA, hT, hP⟩ := binary_arith_words q
  have h := pub_shapeOK q hq
  have hσ := q.hσ
  have hp1 : words q + 1 ≤ (words q + 1) ^ 3 := le_self_pow₀ (by omega) (by norm_num)
  refine ⟨?_, ?_⟩
  · have hGC' : (((2 * (28 * q.kx + 2) + 2 * q.ar.circ.length + (2 * q.ar.bP + q.ar.bT + 1) :
        ℕ) : ℝ)) ≤ 65536 * ((words q : ℝ) + 1) ^ 3 := by exact_mod_cast hGC
    have hSm : (q.kx : ℝ) + q.σ + q.params.m + q.params.r + q.params.k ≤ 2 * (words q : ℝ) := by
      have : q.kx + q.σ + q.params.m + q.params.r + q.params.k ≤ 2 * words q := by
        unfold words
        omega
      exact_mod_cast this
    have hl : (q.params.l : ℝ) ≤ words q := by
      have : q.params.l ≤ words q := by
        unfold words
        omega
      exact_mod_cast this
    have hAp : (q.kx : ℝ) + ((6 * q.kx + 4 * q.b : ℕ) : ℝ) + q.ar.bT + q.ar.bP + q.ar.A ≤
        4117 * ((words q : ℝ) + 1) ^ 3 := by
      have h7 : q.kx + (6 * q.kx + 4 * q.b) ≤ 7 * words q := by
        unfold words
        omega
      have : q.kx + (6 * q.kx + 4 * q.b) + q.ar.bT + q.ar.bP + q.ar.A ≤
          4117 * (words q + 1) ^ 3 := by omega
      exact_mod_cast this
    have key := words_gate_arith 36873000 (3 * 10 ^ 12) q.g (qOf q.s q.T q.etaH q.etaD q.g q.ε)
      (logBudget q.g q.ε) (words q) _ _ (q.params.l : ℝ)
      ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true)) (Fintype.card Zs : ℝ) _
      (by norm_num) (by norm_num) (le_trans zero_le_one hq.g_ge) h.one_le_q h.ell_ge
      (Nat.cast_nonneg _) hGC' hSm (Nat.cast_nonneg _) hl hAp
      (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
    refine hW.trans (le_trans (le_of_eq ?_) key)
    ring
  · rw [hcard]
    have h24 : 22 * q.kx + 12 * q.params.m + 24 * q.params.r + 4 * q.params.k + 4 * q.params.l +
        8 * q.b ≤ 24 * words q := by
      unfold words
      omega
    omega

end Budget

/-! ### Time-dependent coefficients -/

/-- **The register words of the time-dependent solver from binary data**: as `words`, without
the quadrature word (`m` is the mesh exponent). -/
def wordsT (q : PubT) : ℕ :=
  q.kx + q.b + q.params.m + q.params.r + q.params.l + q.F + Cordic.nOf (q.ζ / 2) +
    Nat.clog 2 ⌈q.kap⌉₊ + Nat.clog 2 ⌈1 / q.kap⌉₊

/-- **The per-call cost and the arithmetic wires as polynomials in the words** (time-dependent
coefficients): `G_C ≤ 65536 (𝔴+1)³`, `A_arith ≤ 4096 (𝔴+1)³` and `bT, bP ≤ 5 (𝔴+1)`,
`𝔴 = wordsT q`. -/
theorem binary_time_arith_words (q : PubT) :
    2 * (28 * q.kx + 2) + 2 * q.ar.circ.length + (2 * q.ar.bP + q.ar.bT + 1) ≤
      65536 * (wordsT q + 1) ^ 3 ∧
    q.ar.A ≤ 4096 * (wordsT q + 1) ^ 3 ∧ q.ar.bT ≤ 5 * (wordsT q + 1) ∧
    q.ar.bP ≤ 5 * (wordsT q + 1) := by
  obtain ⟨hc, hA, hT, hP⟩ := q.ar_counts
  have hg2 : Cordic.g2Of (Cordic.nOf (q.ζ / 2)) q.kap =
      Nat.clog 2 ⌈q.kap⌉₊ + Cordic.nOf (q.ζ / 2) + 5 := by
    unfold Cordic.g2Of
    rfl
  have hlk : Cordic.lkOf q.kap = Nat.clog 2 ⌈1 / q.kap⌉₊ := by
    unfold Cordic.lkOf
    rfl
  have hx : q.b + 0 + q.params.l + q.F + Cordic.g2Of (Cordic.nOf (q.ζ / 2)) q.kap +
      Cordic.lkOf q.kap ≤ wordsT q + 5 := by
    unfold wordsT
    omega
  obtain ⟨h1, h2, h3⟩ := arith_words q.b 0 q.params.l q.F (Cordic.nOf (q.ζ / 2))
    (Cordic.g2Of (Cordic.nOf (q.ζ / 2)) q.kap) (Cordic.lkOf q.kap)
    (Cordic.wordOf (Cordic.nOf (q.ζ / 2))) (wordsT q) hx (by omega) (wordOf_le _)
  have hlen : q.ar.circ.length ≤ 52 * (q.m + 14) + 28355 * (wordsT q + 1) ^ 3 :=
    hc.trans (Nat.add_le_add_left h1 _)
  have hA' : q.ar.A ≤ (1 + 2 * (q.m + 14) + (31 + 2 + 3 + 6 + 2 * 10) * (q.m + 14)) +
      1231 * (wordsT q + 1) ^ 3 := hA.le.trans (Nat.add_le_add_left h2 _)
  have hT' : q.ar.bT ≤ 5 * (wordsT q + 1) := hT.le.trans h3
  have hP' : q.ar.bP ≤ 5 * (wordsT q + 1) := hP.le.trans h3
  have hkx : q.kx + q.m ≤ wordsT q := by
    have e : q.params.m = q.m := rfl
    unfold wordsT
    omega
  have hp1 : wordsT q + 1 ≤ (wordsT q + 1) ^ 3 := le_self_pow₀ (by omega) (by norm_num)
  refine ⟨by omega, by omega, hT', hP'⟩

section BudgetT

variable {X n : Type*} [Fintype n] [DecidableEq n] {Zs : Type*} [Fintype Zs] [DecidableEq Zs]

/-- **Equations `ode:eq:gate-main` and `ode:eq:gate-space` in the words, time-dependent
coefficients.** With the public rescaling `γ = gammaOf T η_H η_D (2g) (ε/2)` of
`binary_ode_time_budget`, `q* = qOf s T η_H η_D (2g) (ε/2)`, `ℓ = log(1/ν)` and `𝔴 = wordsT q`,
for the time-indexed binary data and the valid circuits `loadC`, `wpC` of
`binary_ode_time_solver`, in every history the native protocol uses at most
`6·10¹² g [q* (𝔴 + ℓ + 1)³ + G_src + |Zs|]` elementary gates (`G_src = |loadC| + 2 |wpC|`), and its
register has at most `10000 (𝔴+1)³ + 2 |Zs|` qubits. The calls and the guarantees are those of
`binary_ode_time_budget`. -/
theorem binary_ode_time_budget_words (q : PubT) (hq : q.OK)
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
      6 * 10 ^ 12 * q.g * (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
          ((wordsT q : ℝ) + logBudget (2 * q.g) (q.ε / 2) + 1) ^ 3 +
        ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) + Fintype.card Zs) ∧
    Fintype.card (TNW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) ≤
      10000 * (wordsT q + 1) ^ 3 + 2 * Fintype.card Zs := by
  obtain ⟨hW, -, hcard, -⟩ := binary_ode_time_budget q hq hγ D en hrange hdec loadC hloadV wpC hwpV
  obtain ⟨hGC, hA, hT, hP⟩ := binary_time_arith_words q
  have h := pubT_shapeOK q hq
  have hσ := q.hσ
  have hp1 : wordsT q + 1 ≤ (wordsT q + 1) ^ 3 := le_self_pow₀ (by omega) (by norm_num)
  refine ⟨?_, ?_⟩
  · have hGC' : (((2 * (28 * q.kx + 2) + 2 * q.ar.circ.length + (2 * q.ar.bP + q.ar.bT + 1) :
        ℕ) : ℝ)) ≤ 65536 * ((wordsT q : ℝ) + 1) ^ 3 := by exact_mod_cast hGC
    have hSm : (q.kx : ℝ) + q.σ + q.params.m + q.params.r ≤ 2 * (wordsT q : ℝ) := by
      have : q.kx + q.σ + q.params.m + q.params.r ≤ 2 * wordsT q := by
        unfold wordsT
        omega
      exact_mod_cast this
    have hl : (q.params.l : ℝ) ≤ wordsT q := by
      have : q.params.l ≤ wordsT q := by
        unfold wordsT
        omega
      exact_mod_cast this
    have hAp : (q.kx : ℝ) + ((6 * q.kx + 4 * q.b : ℕ) : ℝ) + q.ar.bT + q.ar.bP + q.ar.A ≤
        4117 * ((wordsT q : ℝ) + 1) ^ 3 := by
      have h7 : q.kx + (6 * q.kx + 4 * q.b) ≤ 7 * wordsT q := by
        unfold wordsT
        omega
      have : q.kx + (6 * q.kx + 4 * q.b) + q.ar.bT + q.ar.bP + q.ar.A ≤
          4117 * (wordsT q + 1) ^ 3 := by omega
      exact_mod_cast this
    have key := words_gate_arith 73746000 (6 * 10 ^ 12) q.g
      (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) (logBudget (2 * q.g) (q.ε / 2))
      (wordsT q) _ _ (q.params.l : ℝ) ((nGatesN loadC : ℝ) + 2 * nGatesN wpC)
      (Fintype.card Zs : ℝ) _
      (by norm_num) (by norm_num) (le_trans zero_le_one hq.g_ge) h.one_le_q h.ell_ge
      (Nat.cast_nonneg _) hGC' hSm (Nat.cast_nonneg _) hl hAp
      (add_nonneg (Nat.cast_nonneg _) (mul_nonneg (by norm_num) (Nat.cast_nonneg _)))
      (Nat.cast_nonneg _)
    refine hW.trans (le_trans (le_of_eq ?_) key)
    ring
  · rw [hcard]
    have h24 : 22 * q.kx + 16 * q.params.m + 24 * q.params.r + 4 * q.params.l + 8 * q.b ≤
        24 * wordsT q := by
      unfold wordsT
      omega
    omega

end BudgetT

end

end SparseHamiltonian.GateODEBudget
