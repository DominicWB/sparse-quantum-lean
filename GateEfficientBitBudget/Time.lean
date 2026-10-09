import GateEfficientBitBudget.Constant

/-!
# Equations `ode:eq:gate-main` and `ode:eq:gate-space` in `𝔟`, time-dependent coefficients

For the public data `q : GateBinaryODETime.PubT` of the time-dependent dissipative solver from
time-indexed binary sparse data, the released solver works internally with the ratio `2g` and the
accuracy `ε/2`: `ν = ε/(40000 g)`, `ℓ = log(1/ν)`, `q* = qOf s T η_H η_D (2g) (ε/2)` and the public
rescaling `γ = gammaOf T η_H η_D (2g) (ε/2)` of `GateODEBudget.binary_ode_time_budget`. The time
mesh has `M = 2^m` slots (the mesh exponent `m` is a public choice with `steps τ (ν/3) ≤ 2^m`,
which also carries the regularity of the generator path), and the source quadrature uses the same
`2^m` nodes. The word budget of equation `ode:eq:gate-word-budget` is taken with the internal
`q*` and the user's amplification bound `g` and accuracy `ε`:

`𝔟 = bitB b_data (2^k_x) (2^m) (2^m) q* g ε
   = b_data + log₂(N+1) + 2 log₂(2^m+1) + log₂((q* g + 1)/ε)`

(with the internal `(2g, ε/2)` in the last term it changes by at most `2`: `logb_X_two_le`).
The hypotheses are those of the constant case: `b ≤ b_data`, `c₀`, `T`, `η_H`, `η_D` of bit
length `b_data`, and `ζ ≥ ν/(196608 q*)`.

* `wordsT_le` (the key lemma): `𝔴 + ℓ ≤ 300 (𝔟 + 1)` for the register words
  `𝔴 = GateODEBudget.wordsT q`.
* `binary_ode_time_budget_bits`: in every history the native protocol uses at most
  `2·10²⁰ g [q* (𝔟+1)³ + G_src + |Zs|]` elementary gates (`G_src = |loadC| + 2 |wpC|`) and its
  register has at most `3·10¹¹ (𝔟+1)³ + 2 |Zs|` qubits, together with every conclusion of the
  released `binary_ode_time_budget_words` and `binary_ode_time_budget`.
* `withChoiceT`, `withChoiceT_spec`: the public choices `γ = gammaOf T η_H η_D (2g) (ε/2)`,
  `ζ = ν/(196608 q*)` and the coarsest admissible mesh (least admissible exponent)
  `m = simM τ ν` are compatible with the released public conditions `PubT.OK` (the mesh condition
  included).
* `logBudget_two`, `qOf_two_le`, `bitB_two_le`: the internal ratio and accuracy change the
  logarithmic envelope by `log 4`, the query shape by at most a factor `3`
  (`q*(2g, ε/2) ≤ 3 q*(g, ε)`) and the word budget by at most `2`.
* `time_budget_user`, `binary_ode_time_budget_bits_user`: hence the time-dependent budgets with
  the query shape `q* = qOf s T η_H η_D g ε` of the user's `(g, ε)` and its `𝔟`: at most
  `2·10²² g [q* (𝔟+1)³ + G_src + |Zs|]` gates and `9·10¹² (𝔟+1)³ + 2 |Zs|` qubits.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateBitBudget

noncomputable section
open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
open SparseHamiltonian.GateBinary SparseHamiltonian.GateBinaryODE
open SparseHamiltonian.GateBinaryODETime SparseHamiltonian.OracleCircuit
open GateODEBudget (gammaOf qOf wordsT binary_ode_time_sizes binary_ode_time_budget
  binary_ode_time_budget_words pubT_shapeOK gammaOf_le_one)
open ImprovedODEQueryBudget (precision logBudget radius)
open NativeSparseBlockEncoding (Data Query)
open scoped InnerProduct

/-- **The register words in the word budget** (time-dependent coefficients; the key lemma of
equations `ode:eq:gate-main` and `ode:eq:gate-space` in `𝔟`). For the public data `q` with the
public rescaling `γ = gammaOf T η_H η_D (2g) (ε/2)`, an arithmetic accuracy
`ζ ≥ ν/(196608 q*)` (`q* = qOf s T η_H η_D (2g) (ε/2)`), stored bits `b ≤ b_data` and `c₀`, `T`,
`η_H`, `η_D` of bit length `b_data`, the register words
`𝔴 = wordsT q = k_x + b + m + r + l + F + n_c + ⌈log₂ ⌈κ⌉⌉ + ⌈log₂ ⌈1/κ⌉⌉` and
`ℓ = log(1/ν) = log(40000 g/ε)` satisfy `𝔴 + ℓ ≤ 300 (𝔟 + 1)` for
`𝔟 = bitB b_data (2^k_x) (2^m) (2^m) q* g ε`. -/
theorem wordsT_le (bd : ℕ) (q : PubT) (hq : q.OK)
    (hγ : q.γ = gammaOf q.T q.etaH q.etaD (2 * q.g) (q.ε / 2))
    (hζ : q.params.nu ≤ 196608 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * q.ζ)
    (hb : q.b ≤ bd) (hc0 : HasBits bd q.c0) (hT : HasBits bd q.T) (hH : HasBits bd q.etaH)
    (hD : HasBits bd q.etaD) :
    (wordsT q : ℝ) + logBudget (2 * q.g) (q.ε / 2) ≤
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
  obtain ⟨wκ, wκi⟩ := kap_words bd q.kx q.s (q.F + 10) h
    (Nat.pow_le_pow_right (by norm_num) q.hσ) hc0 hq.c0_pos hT hH hD
  have hkap : q.kap = gammaOf q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * Real.sqrt (4 * (q.s : ℝ)) *
      q.c0 / (2 ^ (q.F + 10) * (q.etaH + radius (2 * q.g) (q.ε / 2) * q.etaD)) := by
    rw [← hγ]
    rfl
  rw [← hkap] at wκ wκi
  simp only [Nat.cast_add, Nat.cast_ofNat] at wκi
  have hLL := logb_X_two_le (Q := qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) (g := q.g)
    (by linarith) (by linarith [hq.g_ge]) hq.ε_pos hε1
  have hw : (wordsT q : ℝ) = q.kx + q.b + q.m + q.params.r + q.params.l + q.F +
      (Cordic.nOf (q.ζ / 2) : ℝ) + (Nat.clog 2 ⌈q.kap⌉₊ : ℝ) +
      (Nat.clog 2 ⌈1 / q.kap⌉₊ : ℝ) := by
    unfold wordsT
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

section Budget

variable {X n : Type*} [Fintype n] [DecidableEq n] {Zs : Type*} [Fintype Zs] [DecidableEq Zs]

/-- **Equations `ode:eq:gate-main` and `ode:eq:gate-space` in the word budget `𝔟`,
time-dependent coefficients** (Theorem `ode:thm:gates`, time-dependent part, equation
`ode:eq:gate-word-budget`). Let the public data `q` have the public rescaling
`γ = gammaOf T η_H η_D (2g) (ε/2)` and an arithmetic accuracy `ζ ≥ ν/(196608 q*)`
(`q* = qOf s T η_H η_D (2g) (ε/2)`, `ν = ε/(40000 g)`, `ℓ = log(1/ν)`), let the stored bits be
`b ≤ b_data` and `c₀`, `T`, `η_H`, `η_D` have bit length `b_data`, and put
`𝔟 = bitB b_data (2^k_x) (2^m) (2^m) q* g ε` (dimension `N = 2^k_x`, time mesh `M = 2^m`, and
`2^m` source nodes). For the time-indexed binary data and the valid circuits `loadC`, `wpC` of
`binary_ode_time_solver`, in every history the native protocol (ratio `2g`) uses at most
`2·10²⁰ g [q* (𝔟+1)³ + G_src + |Zs|]` elementary gates (`G_src = |loadC| + 2 |wpC|`), and its
register has at most `3·10¹¹ (𝔟+1)³ + 2 |Zs|` qubits. The register words satisfy
`𝔴 + ℓ ≤ 300 (𝔟 + 1)` (`𝔴 = wordsT q`), and every conclusion of
`GateODEBudget.binary_ode_time_budget_words` and `GateODEBudget.binary_ode_time_budget` is kept:
at most `6·10¹² g [q* (𝔴 + ℓ + 1)³ + G_src + |Zs|]` gates and `10000 (𝔴+1)³ + 2 |Zs|` qubits; at
most `73746000 g [q* (G_C + k_x + σ + m + r + ℓ (l+1) + 8) + G_src + A]` gates; at most
`7864320 g q*` calls of each coherent sampled-time oracle besides `80 g` times the calls of
`loadC` and twice those of `wpC`; the register size; and, for every input and instance as in
`binary_ode_time_solver` with `98304 q* ζ + 3 ζs ≤ ν`, the guarantees `NOutcome`. -/
theorem binary_ode_time_budget_bits (bd : ℕ) (q : PubT) (hq : q.OK)
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
    (hwpV : ∀ i ∈ wpC, i.Valid) :
    ((nprotocol (q.prep loadC wpC) q.params.ratio (q.params.ratio_ge hq.g_ge)).worstCost
        wGateN : ℝ) ≤
      2 * 10 ^ 20 * q.g * (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
          (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
            (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ 3 +
        ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) + Fintype.card Zs) ∧
    (Fintype.card (TNW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) : ℝ) ≤
      3 * 10 ^ 11 * (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
          (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ 3 +
        2 * Fintype.card Zs ∧
    (wordsT q : ℝ) + logBudget (2 * q.g) (q.ε / 2) ≤
      300 * (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
        (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ∧
    ((nprotocol (q.prep loadC wpC) q.params.ratio (q.params.ratio_ge hq.g_ge)).worstCost
        wGateN : ℝ) ≤
      6 * 10 ^ 12 * q.g * (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
          ((wordsT q : ℝ) + logBudget (2 * q.g) (q.ε / 2) + 1) ^ 3 +
        ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) + Fintype.card Zs) ∧
    Fintype.card (TNW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) ≤
      10000 * (wordsT q + 1) ^ 3 + 2 * Fintype.card Zs ∧
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
  have hw := wordsT_le bd q hq hγ hζ hb hc0 hT hH hD
  obtain ⟨hWg, hWc⟩ :=
    binary_ode_time_budget_words q hq hγ D en hrange hdec loadC hloadV wpC hwpV
  obtain ⟨hG, hC, hcard, hout⟩ :=
    binary_ode_time_budget q hq hγ D en hrange hdec loadC hloadV wpC hwpV
  have hε1 : q.ε ≤ 1 := hq.ε_half.trans (by norm_num)
  have hQ1 := h.one_le_q
  have hg0 : 0 ≤ q.g := le_trans zero_le_one hq.g_ge
  have hB0 : 0 ≤ bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
      (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε :=
    bitB_nonneg _ _ _ _ (mul_nonneg (by linarith) hg0) hq.ε_pos hε1
  have hℓ := h.ell_ge
  have hw0 : (0 : ℝ) ≤ wordsT q := Nat.cast_nonneg _
  refine ⟨?_, ?_, hw, hWg, hWc, hG, hC, hcard, hout⟩
  · -- gates
    have hcube := cube_le (by linarith) hB0 hw
    refine hWg.trans (budget_mono (by norm_num) hg0 (by linarith) (by positivity)
      (by positivity) (by positivity) (by norm_num) hcube (by norm_num))
  · -- qubits
    have hcube := cube_le hw0 hB0 (c := 300) (by linarith)
    have hc : ((Fintype.card (TNW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP
        q.ar.A) : ℕ) : ℝ) ≤ 10000 * ((wordsT q : ℝ) + 1) ^ 3 + 2 * Fintype.card Zs := by
      exact_mod_cast hWc
    have hY : 0 ≤ (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
        (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ 3 := by positivity
    nlinarith

end Budget

/-! ### Compatibility of the public choices -/

/-- The public choices of the rescaling and of the arithmetic accuracy of the time-dependent
solver, before the mesh: `γ = gammaOf T η_H η_D (2g) (ε/2)` and `ζ = ν/(196608 q*)`. -/
def withChoiceT₀ (q : PubT) : PubT :=
  { q with
    γ := gammaOf q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)
    ζ := zetaOf (precision (2 * q.g) (q.ε / 2)) (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) }

/-- **The public choices of the time-dependent solver**: `γ = gammaOf T η_H η_D (2g) (ε/2)`,
`ζ = ν/(196608 q*)` and the least admissible mesh exponent `m = simM τ ν` (the coarsest
admissible mesh) of the released simulator for the common time `τ` of this rescaling, the other
public data unchanged. -/
def withChoiceT (q : PubT) : PubT :=
  { withChoiceT₀ q with m := Sim.simM (withChoiceT₀ q).params.tau (withChoiceT₀ q).params.nu }

/-- **The public choices are admissible** (time-dependent coefficients): for public data
satisfying the released conditions `PubT.OK`, the data `withChoiceT q` satisfy `PubT.OK` (the
mesh condition `steps τ (ν/3) ≤ 2^m` included), the rescaling hypothesis of
`binary_ode_time_budget_bits` and its accuracy hypothesis `ν ≤ 196608 q* ζ`, and the released
arithmetic budget `98304 q* ζ + 3 ζs ≤ ν` holds exactly for `ζs ≤ ν/6`. -/
theorem withChoiceT_spec (q : PubT) (hq : q.OK) :
    (withChoiceT q).OK ∧
    (withChoiceT q).γ = gammaOf (withChoiceT q).T (withChoiceT q).etaH (withChoiceT q).etaD
      (2 * (withChoiceT q).g) ((withChoiceT q).ε / 2) ∧
    (withChoiceT q).params.nu ≤ 196608 * qOf (withChoiceT q).s (withChoiceT q).T
      (withChoiceT q).etaH (withChoiceT q).etaD (2 * (withChoiceT q).g)
        ((withChoiceT q).ε / 2) * (withChoiceT q).ζ ∧
    ∀ ζs : ℝ, 98304 * qOf (withChoiceT q).s (withChoiceT q).T (withChoiceT q).etaH
        (withChoiceT q).etaD (2 * (withChoiceT q).g) ((withChoiceT q).ε / 2) *
          (withChoiceT q).ζ + 3 * ζs ≤ (withChoiceT q).params.nu ↔
        ζs ≤ (withChoiceT q).params.nu / 6 := by
  have h := pubT_shapeOK q hq
  have hν : 0 < precision (2 * q.g) (q.ε / 2) := q.params.nu_pos hq.g_ge hq.ε_pos
  have hν1 : precision (2 * q.g) (q.ε / 2) ≤ 1 :=
    (ImprovedODEQueryBudget.precision_le_one_ten_thousandth (2 * q.g) (q.ε / 2)
      (by linarith [hq.g_ge]) (by linarith [hq.ε_half])).trans (by norm_num)
  obtain ⟨hz0, hz1, hzν, hz2⟩ := zetaOf_spec hν hν1 h.one_le_q
  refine ⟨?_, rfl, hzν, fun ζs => ?_⟩
  · exact ⟨hq.b_pos, hq.c0_pos, hq.etaH_nonneg, hq.etaD_nonneg, hq.eta_pos, h.gammaOf_pos,
      gammaOf_le_one _ _ _ _ _, hq.T_pos, hq.g_ge, hq.ε_pos, hq.ε_half, hz0, hz1,
      (Sim.simM_spec (withChoiceT₀ q).params.tau (withChoiceT₀ q).params.nu).1⟩
  · change 98304 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
        zetaOf (precision (2 * q.g) (q.ε / 2)) (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) +
          3 * ζs ≤ precision (2 * q.g) (q.ε / 2) ↔ ζs ≤ precision (2 * q.g) (q.ε / 2) / 6
    rw [hz2]
    constructor <;> intro h' <;> linarith

/-! ### The internal ratio and accuracy -/

/-- **The logarithmic envelope of the internal ratio and accuracy**:
`log(1/ν)` for `(2g, ε/2)` is `ℓ + log 4`, `ℓ = log(10000 g/ε)`. -/
theorem logBudget_two (g ε : ℝ) (hg : 0 < g) (hε : 0 < ε) :
    logBudget (2 * g) (ε / 2) = logBudget g ε + Real.log 4 := by
  unfold ImprovedODEQueryBudget.logBudget
  have e : 10000 * (2 * g) / (ε / 2) = 4 * (10000 * g / ε) := by
    rw [div_div_eq_mul_div]
    ring
  rw [e, Real.log_mul (by norm_num) (by positivity)]
  ring

/-- **The query shape of the internal ratio and accuracy**: `q*(2g, ε/2) ≤ 3 q*(g, ε)` for the
public conditions `ShapeOK` of `(g, ε)`. -/
theorem qOf_two_le {s T ηH ηD g ε : ℝ} (h : GateODEBudget.ShapeOK s T ηH ηD g ε) :
    qOf s T ηH ηD (2 * g) (ε / 2) ≤ 3 * qOf s T ηH ηD g ε := by
  have hg0 : 0 < g := lt_of_lt_of_le one_pos h.g_ge
  have hℓ := h.ell_ge
  have e := logBudget_two g ε hg0 h.ε_pos
  have hlog4 : Real.log 4 ≤ 2 := by
    have h1 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    have := Real.log_two_lt_d9
    norm_num at this
    linarith
  have hlog40 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hℓ' : logBudget (2 * g) (ε / 2) ≤ 3 * logBudget g ε := by
    rw [e]
    linarith
  have hℓ'0 : 0 ≤ logBudget (2 * g) (ε / 2) := by
    rw [e]
    linarith
  have hTH : 0 ≤ T * ηH := mul_nonneg h.T_pos.le h.etaH_nonneg
  have hTD : 0 ≤ T * ηD := mul_nonneg h.T_pos.le h.etaD_nonneg
  have hΘ : GateODEBudget.thetaOf T ηH ηD (2 * g) (ε / 2) ≤
      3 * GateODEBudget.thetaOf T ηH ηD g ε := by
    unfold GateODEBudget.thetaOf ImprovedODEQueryBudget.theta
    have := mul_le_mul_of_nonneg_left hℓ' hTD
    nlinarith
  have hΘ0 : 0 ≤ GateODEBudget.thetaOf T ηH ηD (2 * g) (ε / 2) := by
    unfold GateODEBudget.thetaOf ImprovedODEQueryBudget.theta
    positivity
  have hs0 : 0 ≤ s := by linarith [h.s_ge]
  unfold GateODEBudget.qOf ImprovedODEQueryBudget.queryShape
  have h1 : Real.sqrt s * GateODEBudget.thetaOf T ηH ηD (2 * g) (ε / 2) ≤
      3 * (Real.sqrt s * GateODEBudget.thetaOf T ηH ηD g ε) := by
    have := mul_le_mul_of_nonneg_left hΘ (Real.sqrt_nonneg s)
    linarith
  have h2 : Real.sqrt (s * GateODEBudget.thetaOf T ηH ηD (2 * g) (ε / 2) *
      logBudget (2 * g) (ε / 2)) ≤
      3 * Real.sqrt (s * GateODEBudget.thetaOf T ηH ηD g ε * logBudget g ε) := by
    have h3 : s * GateODEBudget.thetaOf T ηH ηD (2 * g) (ε / 2) * logBudget (2 * g) (ε / 2) ≤
        9 * (s * GateODEBudget.thetaOf T ηH ηD g ε * logBudget g ε) := by
      have h4 := mul_le_mul hΘ hℓ' hℓ'0 (by linarith)
      have h5 := mul_le_mul_of_nonneg_left h4 hs0
      nlinarith
    have h6 := Real.sqrt_le_sqrt h3
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 9),
      show Real.sqrt 9 = 3 by rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      at h6
    exact h6
  linarith

/-- **The word budget of the internal ratio and accuracy**: `𝔟` taken with
`q*(2g, ε/2)` exceeds `𝔟` taken with `q*(g, ε)` by at most `2`. -/
theorem bitB_two_le (bd N M m : ℕ) {s T ηH ηD g ε : ℝ}
    (h : GateODEBudget.ShapeOK s T ηH ηD g ε) :
    bitB bd N M m (qOf s T ηH ηD (2 * g) (ε / 2)) g ε ≤
      bitB bd N M m (qOf s T ηH ηD g ε) g ε + 2 := by
  have hg0 : 0 < g := lt_of_lt_of_le one_pos h.g_ge
  have hq := qOf_two_le h
  have hQ1 := h.one_le_q
  have hε := h.ε_pos
  have hX : 1 ≤ (qOf s T ηH ηD g ε * g + 1) / ε := shape_one_le_X h
  have hpos : 0 < (qOf s T ηH ηD (2 * g) (ε / 2) * g + 1) / ε := by
    have h1 : 0 ≤ qOf s T ηH ηD (2 * g) (ε / 2) := by
      have h2 : GateODEBudget.ShapeOK s T ηH ηD (2 * g) (ε / 2) :=
        ⟨h.s_ge, h.T_pos, h.etaH_nonneg, h.etaD_nonneg, h.eta_pos, by linarith [h.g_ge],
          by linarith, by linarith [h.ε_le]⟩
      linarith [h2.one_le_q]
    positivity
  have h1 : (qOf s T ηH ηD (2 * g) (ε / 2) * g + 1) / ε ≤
      4 * ((qOf s T ηH ηD g ε * g + 1) / ε) ^ 1 := by
    rw [pow_one, mul_div_assoc']
    apply div_le_div_of_nonneg_right _ hε.le
    have := mul_le_mul_of_nonneg_right hq hg0.le
    nlinarith
  have h2 := logb_le_mul_pow _ 4 _ 2 1 hpos hX (by norm_num) h1
  push_cast at h2
  unfold bitB
  linarith


/-! ### The time-dependent budgets with the query shape of `(g, ε)` -/

/-- **The time-dependent budgets with the query shape of `(g, ε)`**: for the public conditions
`ShapeOK` of `(g, ε)`, a gate bound `2·10²⁰ g [q*' (𝔟' + 1)³ + G + Z]` and a qubit bound
`3·10¹¹ (𝔟' + 1)³ + 2 Z` in the internal `q*' = qOf s T η_H η_D (2g) (ε/2)` and its word budget
`𝔟'` (the forms of `binary_ode_time_budget_bits`) give `2·10²² g [q* (𝔟 + 1)³ + G + Z]` and
`9·10¹² (𝔟 + 1)³ + 2 Z` with `q* = qOf s T η_H η_D g ε` and its `𝔟` (`qOf_two_le`,
`bitB_two_le`). -/
theorem time_budget_user (bd N M m : ℕ) {s T ηH ηD g ε W A G Z : ℝ}
    (h : GateODEBudget.ShapeOK s T ηH ηD g ε) (hG : 0 ≤ G) (hZ : 0 ≤ Z)
    (hW : W ≤ 2 * 10 ^ 20 * g * (qOf s T ηH ηD (2 * g) (ε / 2) *
      (bitB bd N M m (qOf s T ηH ηD (2 * g) (ε / 2)) g ε + 1) ^ 3 + G + Z))
    (hA : A ≤ 3 * 10 ^ 11 * (bitB bd N M m (qOf s T ηH ηD (2 * g) (ε / 2)) g ε + 1) ^ 3 +
      2 * Z) :
    W ≤ 2 * 10 ^ 22 * g * (qOf s T ηH ηD g ε * (bitB bd N M m (qOf s T ηH ηD g ε) g ε + 1) ^ 3 +
      G + Z) ∧
    A ≤ 9 * 10 ^ 12 * (bitB bd N M m (qOf s T ηH ηD g ε) g ε + 1) ^ 3 + 2 * Z := by
  have hq := qOf_two_le h
  have hb := bitB_two_le bd N M m h
  have hq1 := h.one_le_q
  have hg0 : 0 ≤ g := le_trans zero_le_one h.g_ge
  have hB0 : 0 ≤ bitB bd N M m (qOf s T ηH ηD g ε) g ε :=
    bitB_nonneg bd N M m (mul_nonneg (by linarith) hg0) h.ε_pos h.ε_le
  have h2 : GateODEBudget.ShapeOK s T ηH ηD (2 * g) (ε / 2) :=
    ⟨h.s_ge, h.T_pos, h.etaH_nonneg, h.etaD_nonneg, h.eta_pos, by linarith [h.g_ge],
      by linarith [h.ε_pos], by linarith [h.ε_le]⟩
  have hq'1 := h2.one_le_q
  have hB'0 : 0 ≤ bitB bd N M m (qOf s T ηH ηD (2 * g) (ε / 2)) g ε :=
    bitB_nonneg bd N M m (mul_nonneg (by linarith) hg0) h.ε_pos h.ε_le
  generalize bitB bd N M m (qOf s T ηH ηD g ε) g ε = B at hb hB0 ⊢
  generalize bitB bd N M m (qOf s T ηH ηD (2 * g) (ε / 2)) g ε = B' at hb hB'0 hW hA ⊢
  generalize qOf s T ηH ηD g ε = Q at hq hq1 ⊢
  generalize qOf s T ηH ηD (2 * g) (ε / 2) = Q' at hq hq'1 hW ⊢
  have hc : (B' + 1) ^ 3 ≤ 27 * (B + 1) ^ 3 := by
    have h1 : B' + 1 ≤ 3 * (B + 1) := by linarith
    calc (B' + 1) ^ 3 ≤ (3 * (B + 1)) ^ 3 := pow_le_pow_left₀ (by linarith) h1 3
      _ = 27 * (B + 1) ^ 3 := by ring
  have hY : 0 ≤ (B + 1) ^ 3 := by positivity
  have hQ' : 0 ≤ Q' := by linarith
  refine ⟨hW.trans ?_, by linarith⟩
  have h1 : Q' * (B' + 1) ^ 3 ≤ 81 * (Q * (B + 1) ^ 3) := by
    have := mul_le_mul hq hc (by positivity) (by linarith)
    nlinarith
  have h2 : 0 ≤ Q * (B + 1) ^ 3 + G + Z := by positivity
  have h3 : Q' * (B' + 1) ^ 3 + G + Z ≤ 81 * (Q * (B + 1) ^ 3 + G + Z) := by linarith
  calc 2 * 10 ^ 20 * g * (Q' * (B' + 1) ^ 3 + G + Z)
      ≤ 2 * 10 ^ 20 * g * (81 * (Q * (B + 1) ^ 3 + G + Z)) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ ≤ 2 * 10 ^ 22 * g * (Q * (B + 1) ^ 3 + G + Z) := by nlinarith

/-- **Equations `ode:eq:gate-main` and `ode:eq:gate-space` in `𝔟`, time-dependent coefficients,
with the query shape of `(g, ε)`**: under the hypotheses of `binary_ode_time_budget_bits`, with
`q* = qOf s T η_H η_D g ε` and `𝔟 = bitB b_data (2^k_x) (2^m) (2^m) q* g ε`, the native protocol
uses at most `2·10²² g [q* (𝔟+1)³ + G_src + |Zs|]` elementary gates in every history and its
register has at most `9·10¹² (𝔟+1)³ + 2 |Zs|` qubits (`time_budget_user`). -/
theorem binary_ode_time_budget_bits_user {X n : Type*} [Fintype n] [DecidableEq n]
    {Zs : Type*} [Fintype Zs] [DecidableEq Zs] (bd : ℕ) (q : PubT) (hq : q.OK)
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
    (hwpV : ∀ i ∈ wpC, i.Valid) :
    ((nprotocol (q.prep loadC wpC) q.params.ratio (q.params.ratio_ge hq.g_ge)).worstCost
        wGateN : ℝ) ≤
      2 * 10 ^ 22 * q.g * (qOf q.s q.T q.etaH q.etaD q.g q.ε *
          (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m) (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε +
            1) ^ 3 +
        ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) + Fintype.card Zs) ∧
    (Fintype.card (TNW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) : ℝ) ≤
      9 * 10 ^ 12 * (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
          (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε + 1) ^ 3 + 2 * Fintype.card Zs := by
  have h : GateODEBudget.ShapeOK (q.s : ℝ) q.T q.etaH q.etaD q.g q.ε :=
    ⟨by exact_mod_cast Nat.one_le_two_pow, hq.T_pos, hq.etaH_nonneg, hq.etaD_nonneg, hq.eta_pos,
      hq.g_ge, hq.ε_pos, by linarith [hq.ε_half]⟩
  obtain ⟨hW, hA, -⟩ :=
    binary_ode_time_budget_bits bd q hq hγ hζ hb hc0 hT hH hD D en hrange hdec loadC hloadV wpC
      hwpV
  exact time_budget_user bd _ _ _ h (by positivity) (by positivity) hW hA

end

end SparseHamiltonian.GateBitBudget
