import GateEfficientRemarks.ODE.Absorb
import GateEfficientBitBudget.Time

/-!
# Source costs polynomial in `𝔟`: the gate bound `ḡ q poly(𝔟)`

Theorem `ode:thm:gates` of the accompanying paper (equations `ode:eq:gate-word-budget`,
`ode:eq:gate-main`, `ode:eq:gate-space`) remarks: "If the source gate and work costs are
polynomial in `𝔟`, the total gate bound is `ḡ q poly(𝔟)`." The released library
`GateEfficientBitBudget` proves the two equations in the word budget
`𝔟 = bitB b_data (2^k_x) (2^m) (2^k) q* g ε` with explicit constants and the source costs
`G_src` (gates of the source circuits) and `|Zs|` (their scratch) as parameters; its guide lists
the absorption of polynomial source costs into `q poly(𝔟)` as not a Lean statement. These are
that statement, as corollaries of the released endpoints under their hypotheses: if
`G_src ≤ c (𝔟+1)^j` and `|Zs| ≤ c (𝔟+1)^j` (then `c ≥ 0`), with `J = max j 3`,

* `binary_ode_budget_poly` (from `GateBitBudget.binary_ode_budget_bits`): at most
  `10²⁰ (1 + 2c) g q* (𝔟+1)^J` gates in every history and at most `(3·10¹¹ + 2c) (𝔟+1)^J`
  qubits;
* `binary_ode_time_budget_poly` (from `GateBitBudget.binary_ode_time_budget_bits`, internal
  `q*` of `(2g, ε/2)`): `2·10²⁰ (1 + 2c) g q* (𝔟+1)^J` gates, `(3·10¹¹ + 2c) (𝔟+1)^J` qubits;
* `binary_ode_time_budget_poly_user` (from `GateBitBudget.binary_ode_time_budget_bits_user`,
  the `q*` of the user's `(g, ε)` and its `𝔟`): `2·10²² (1 + 2c) g q* (𝔟+1)^J` gates,
  `(9·10¹² + 2c) (𝔟+1)^J` qubits.

The protocols are those of the endpoints, whose other conclusions (calls, register words,
guarantees) hold under the same hypotheses. The arithmetic uses `q* ≥ 1` and `𝔟 ≥ 0`.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateRemarks.ODE

noncomputable section
open SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
open SparseHamiltonian.GateBinary SparseHamiltonian.GateBinaryODE
open SparseHamiltonian.GateBinaryODETime
open SparseHamiltonian.GateBitBudget (bitB HasBits bitB_nonneg)
open GateODEBudget (gammaOf qOf)
open NativeSparseBlockEncoding (Data Query)

section Budget

variable {X n : Type*} [Fintype n] [DecidableEq n] {Zs : Type*} [Fintype Zs] [DecidableEq Zs]

/-- **Source costs polynomial in `𝔟`, constant coefficients** (remark of Theorem
`ode:thm:gates`: the total gate bound is `ḡ q poly(𝔟)`). Under the hypotheses of
`GateBitBudget.binary_ode_budget_bits` (public rescaling, `ζ ≥ ν/(196608 q*)`, `b ≤ b_data`,
`c₀`, `T`, `η_H`, `η_D` of bit length `b_data`, the binary data and valid source circuits), with
`𝔟 = bitB b_data (2^k_x) (2^m) (2^k) q* g ε`: if the source gates `G_src = |srcC 0| + |srcC 1|`
and the source scratch `|Zs|` are at most `c (𝔟+1)^j`, then in every history the native protocol
`nprotocol (q.prep srcC) g` uses at most `10²⁰ (1 + 2c) g q* (𝔟+1)^(max j 3)` elementary gates,
and its register has at most `(3·10¹¹ + 2c) (𝔟+1)^(max j 3)` qubits. -/
theorem binary_ode_budget_poly (bd : ℕ) (q : Pub) (hq : q.OK)
    (hγ : q.γ = gammaOf q.T q.etaH q.etaD q.g q.ε)
    (hζ : q.params.nu ≤ 196608 * qOf q.s q.T q.etaH q.etaD q.g q.ε * q.ζ) (hb : q.b ≤ bd)
    (hc0 : HasBits bd q.c0) (hT : HasBits bd q.T) (hH : HasBits bd q.etaH)
    (hD : HasBits bd q.etaD)
    (D : Data X n (Cfg (VW q.b)) q.s) (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (hdec : ∀ e z, D.decode e z = (q.c0 : ℂ) * gauss z)
    (srcC : Bool → List (NInstr ((Unit ⊕ Fin q.kx) ⊕ Zs) (PY q.kx q.b) Query))
    (hsrcV : ∀ c, ∀ i ∈ srcC c, i.Valid) (c : ℝ) (j : ℕ)
    (hG : (nGatesN (srcC false) : ℝ) + nGatesN (srcC true) ≤
      c * (bitB bd (2 ^ q.kx) (2 ^ q.params.m) (2 ^ q.params.k)
        (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε + 1) ^ j)
    (hZ : (Fintype.card Zs : ℝ) ≤
      c * (bitB bd (2 ^ q.kx) (2 ^ q.params.m) (2 ^ q.params.k)
        (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε + 1) ^ j) :
    ((nprotocol (q.prep srcC) q.g hq.g_ge).worstCost wGateN : ℝ) ≤
      10 ^ 20 * (1 + 2 * c) * q.g * qOf q.s q.T q.etaH q.etaD q.g q.ε *
        (bitB bd (2 ^ q.kx) (2 ^ q.params.m) (2 ^ q.params.k)
          (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε + 1) ^ max j 3 ∧
    (Fintype.card (NW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) : ℝ) ≤
      (3 * 10 ^ 11 + 2 * c) * (bitB bd (2 ^ q.kx) (2 ^ q.params.m) (2 ^ q.params.k)
        (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε + 1) ^ max j 3 := by
  obtain ⟨hW, hA, -⟩ := GateBitBudget.binary_ode_budget_bits bd q hq hγ hζ hb hc0 hT hH hD D en
    hrange hdec srcC hsrcV
  have hQ1 := (GateODEBudget.pub_shapeOK q hq).one_le_q
  have hg0 : 0 ≤ q.g := le_trans zero_le_one hq.g_ge
  have hε1 : q.ε ≤ 1 := hq.ε_half.trans (by norm_num)
  have hB0 := bitB_nonneg bd (2 ^ q.kx) (2 ^ q.params.m) (2 ^ q.params.k)
    (mul_nonneg (by linarith : (0 : ℝ) ≤ qOf q.s q.T q.etaH q.etaD q.g q.ε) hg0) hq.ε_pos hε1
  have hY : (1 : ℝ) ≤ bitB bd (2 ^ q.kx) (2 ^ q.params.m) (2 ^ q.params.k)
      (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε + 1 := by linarith
  have hc := nonneg_of_le_mul_pow j (Nat.cast_nonneg _) (by linarith) hZ
  exact ⟨hW.trans (gates_absorb j (by norm_num) hg0 hQ1 hY hc hG hZ),
    hA.trans (space_absorb 2 j (by norm_num) (by norm_num) hY hc hZ)⟩

/-- **Source costs polynomial in `𝔟`, time-dependent coefficients** (remark of Theorem
`ode:thm:gates`, time-dependent part). Under the hypotheses of
`GateBitBudget.binary_ode_time_budget_bits`, with the internal `q* = qOf s T η_H η_D (2g) (ε/2)`
and `𝔟 = bitB b_data (2^k_x) (2^m) (2^m) q* g ε`: if `G_src = |loadC| + 2 |wpC|` and `|Zs|` are
at most `c (𝔟+1)^j`, then in every history the native protocol (ratio `2g`) uses at most
`2·10²⁰ (1 + 2c) g q* (𝔟+1)^(max j 3)` elementary gates, and its register has at most
`(3·10¹¹ + 2c) (𝔟+1)^(max j 3)` qubits. -/
theorem binary_ode_time_budget_poly (bd : ℕ) (q : PubT) (hq : q.OK)
    (hγ : q.γ = gammaOf q.T q.etaH q.etaD (2 * q.g) (q.ε / 2))
    (hζ : q.params.nu ≤ 196608 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * q.ζ)
    (hb : q.b ≤ bd) (hc0 : HasBits bd q.c0) (hT : HasBits bd q.T) (hH : HasBits bd q.etaH)
    (hD : HasBits bd q.etaD)
    (D : Data (X × Fin (2 ^ q.m)) n (Cfg (VW q.b)) q.s) (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (hdec : ∀ e z, D.decode e z = (q.c0 : ℂ) * gauss z)
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b)
      Query)) (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b) Query))
    (hwpV : ∀ i ∈ wpC, i.Valid) (c : ℝ) (j : ℕ)
    (hG : (nGatesN loadC : ℝ) + 2 * nGatesN wpC ≤
      c * (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
        (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ j)
    (hZ : (Fintype.card Zs : ℝ) ≤
      c * (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
        (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ j) :
    ((nprotocol (q.prep loadC wpC) q.params.ratio (q.params.ratio_ge hq.g_ge)).worstCost
        wGateN : ℝ) ≤
      2 * 10 ^ 20 * (1 + 2 * c) * q.g * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
        (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
          (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ max j 3 ∧
    (Fintype.card (TNW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) : ℝ) ≤
      (3 * 10 ^ 11 + 2 * c) * (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
        (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ max j 3 := by
  obtain ⟨hW, hA, -⟩ := GateBitBudget.binary_ode_time_budget_bits bd q hq hγ hζ hb hc0 hT hH
    hD D en hrange hdec loadC hloadV wpC hwpV
  have hQ1 := (GateODEBudget.pubT_shapeOK q hq).one_le_q
  have hg0 : 0 ≤ q.g := le_trans zero_le_one hq.g_ge
  have hε1 : q.ε ≤ 1 := hq.ε_half.trans (by norm_num)
  have hB0 := bitB_nonneg bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
    (mul_nonneg (by linarith : (0 : ℝ) ≤ qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) hg0)
    hq.ε_pos hε1
  have hY : (1 : ℝ) ≤ bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
      (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1 := by linarith
  have hc := nonneg_of_le_mul_pow j (Nat.cast_nonneg _) (by linarith) hZ
  exact ⟨hW.trans (gates_absorb j (by norm_num) hg0 hQ1 hY hc hG hZ),
    hA.trans (space_absorb 2 j (by norm_num) (by norm_num) hY hc hZ)⟩

/-- **Source costs polynomial in `𝔟`, time-dependent coefficients, with the query shape of
`(g, ε)`** (remark of Theorem `ode:thm:gates`, time-dependent part). Under the hypotheses of
`GateBitBudget.binary_ode_time_budget_bits_user`, with `q* = qOf s T η_H η_D g ε` and
`𝔟 = bitB b_data (2^k_x) (2^m) (2^m) q* g ε`: if `G_src = |loadC| + 2 |wpC|` and `|Zs|` are at
most `c (𝔟+1)^j`, then in every history the native protocol uses at most
`2·10²² (1 + 2c) g q* (𝔟+1)^(max j 3)` elementary gates, and its register has at most
`(9·10¹² + 2c) (𝔟+1)^(max j 3)` qubits. -/
theorem binary_ode_time_budget_poly_user (bd : ℕ) (q : PubT) (hq : q.OK)
    (hγ : q.γ = gammaOf q.T q.etaH q.etaD (2 * q.g) (q.ε / 2))
    (hζ : q.params.nu ≤ 196608 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * q.ζ)
    (hb : q.b ≤ bd) (hc0 : HasBits bd q.c0) (hT : HasBits bd q.T) (hH : HasBits bd q.etaH)
    (hD : HasBits bd q.etaD)
    (D : Data (X × Fin (2 ^ q.m)) n (Cfg (VW q.b)) q.s) (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (hdec : ∀ e z, D.decode e z = (q.c0 : ℂ) * gauss z)
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b)
      Query)) (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b) Query))
    (hwpV : ∀ i ∈ wpC, i.Valid) (c : ℝ) (j : ℕ)
    (hG : (nGatesN loadC : ℝ) + 2 * nGatesN wpC ≤
      c * (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m) (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε +
        1) ^ j)
    (hZ : (Fintype.card Zs : ℝ) ≤
      c * (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m) (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε +
        1) ^ j) :
    ((nprotocol (q.prep loadC wpC) q.params.ratio (q.params.ratio_ge hq.g_ge)).worstCost
        wGateN : ℝ) ≤
      2 * 10 ^ 22 * (1 + 2 * c) * q.g * qOf q.s q.T q.etaH q.etaD q.g q.ε *
        (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m) (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε +
          1) ^ max j 3 ∧
    (Fintype.card (TNW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) : ℝ) ≤
      (9 * 10 ^ 12 + 2 * c) * (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
        (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε + 1) ^ max j 3 := by
  obtain ⟨hW, hA⟩ := GateBitBudget.binary_ode_time_budget_bits_user bd q hq hγ hζ hb hc0 hT hH
    hD D en hrange hdec loadC hloadV wpC hwpV
  have h : GateODEBudget.ShapeOK (q.s : ℝ) q.T q.etaH q.etaD q.g q.ε :=
    ⟨by exact_mod_cast Nat.one_le_two_pow, hq.T_pos, hq.etaH_nonneg, hq.etaD_nonneg, hq.eta_pos,
      hq.g_ge, hq.ε_pos, by linarith [hq.ε_half]⟩
  have hQ1 := h.one_le_q
  have hg0 : 0 ≤ q.g := le_trans zero_le_one hq.g_ge
  have hB0 := bitB_nonneg bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
    (mul_nonneg (by linarith : (0 : ℝ) ≤ qOf q.s q.T q.etaH q.etaD q.g q.ε) hg0) hq.ε_pos h.ε_le
  have hY : (1 : ℝ) ≤ bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
      (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε + 1 := by linarith
  have hc := nonneg_of_le_mul_pow j (Nat.cast_nonneg _) (by linarith) hZ
  exact ⟨hW.trans (gates_absorb j (by norm_num) hg0 hQ1 hY hc hG hZ),
    hA.trans (space_absorb 2 j (by norm_num) (by norm_num) hY hc hZ)⟩

end Budget

end

end SparseHamiltonian.GateRemarks.ODE
