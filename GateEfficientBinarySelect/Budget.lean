import GateEfficientBinarySelect.Synth
import GateEfficientBinarySelect.SelectBinary
import GateEfficientODEBudget.Words

/-!
# Equations `ode:eq:gate-main`, `ode:eq:gate-space` and `ode:eq:gate-select-gates` in the query
shape and in the register words, branch-dependent meshes

For the public data `q : GateBinaryODETime.PubT` with the public rescaling
`γ = gammaOf T η_H η_D (2g) (ε/2)` the released size bounds `GateODEBudget.binary_ode_time_sizes`
hold (`d ≤ 4096 q*`, `J ≤ 60 q* ℓ`, …, `q* = qOf s T η_H η_D (2g) (ε/2)`, `ℓ = log(1/ν)`); the
public data and parameters are those of the common-mesh solver, so the sizes are the same. The
branch-dependent meshes add the address program (`|apG| ≤ 13 (2m+14)(m+5) ≤ 910 (m+1)²` gates,
`card_apG_le`) and the address registers (`|ZA| ≤ 897 (m+1)²` wires, `card_ZA_le`), and the
arithmetic has the duration word of `m` bits in place of the quadrature word.

* `wordsB`, `binary_select_arith_words`: the register words
  `𝔴 = k_x + b + m + r + l + F + n_c + ⌈log₂ ⌈κ⌉⌉ + ⌈log₂ ⌈1/κ⌉⌉` (with the decoder scale `kapQ`);
  the gates `G_C` of one private call are at most `65536 (𝔴+1)³` and the added work wires
  `|ZA| + 6 k_x + 4 b + bT + bP + A_arith` at most `4096 (𝔴+1)³`.
* `select_gates_words`: for the native selection circuit of `binary_native_gate_select` with
  filter degree `d`, the gates beyond the released circuit are
  `G_sel = 84 d (σ+3) + 6 d G_C ≤ 393500 d (𝔴+1)³` and the added work wires
  `A_sel ≤ 4096 (𝔴+1)³ + 3` (equation `ode:eq:gate-select-gates`: `d` times a polynomial in the
  word lengths, and reusable work space without the factor `d`); the bounds for the circuit
  itself, at `δ = 4ν` (`ν` the accuracy parameter of the solver), are
  `binary_select_lemma_words` (module `SelectCost`).
* `binary_select_budget`: equations `ode:eq:gate-main`, `ode:eq:gate-space` in `q*`: at most
  `73746000 g [q* (G_C + k_x + σ + m + r + ℓ (l+1) + 8) + G_src + A]` gates, at most
  `7864320 g q*` calls of each coherent sampled-time oracle besides the source calls, the
  register, and the guarantees `NOutcome` under `98304 q* ζ + 3 ζs ≤ ν`.
* `binary_select_budget_words`: at most `6·10¹² g [q* (𝔴 + ℓ + 1)³ + G_src + |Zs|]` gates and
  `10000 (𝔴+1)³ + 2 |Zs|` qubits.
* `words_gate_arithB`: the arithmetic of the word budget with the address registers.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateBinarySelect

noncomputable section
open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
open SparseHamiltonian.GateBinary SparseHamiltonian.GateBinaryODE SparseHamiltonian.OracleCircuit
open SparseHamiltonian.GateBinaryODETime (PubT)
open SparseHamiltonian.GateODEBudget (gammaOf qOf binary_ode_time_sizes pubT_shapeOK
  gate_budget_arith' call_budget_arith arith_words wordOf_le)
open SparseHamiltonian.GateSelect.ODE (bsW)
open ImprovedODEQueryBudget (precision logBudget radius)
open NativeSparseBlockEncoding (Data Query)
open scoped InnerProduct

/-! ### The words -/

/-- The address registers have at most `897 (m+1)²` wires. -/
theorem card_ZA_le (m : ℕ) : Fintype.card (ZA m) ≤ 897 * (m + 1) ^ 2 := by
  rw [card_ZA]
  nlinarith

/-- The address program has at most `910 (m+1)²` gates. -/
theorem card_apG_le (k b m l : ℕ) : (apG k b m l).length ≤ 910 * (m + 1) ^ 2 := by
  refine (length_apG k b m l).trans ?_
  nlinarith

/-- **The register words of the solver on branch-dependent meshes**: the system qubits `k_x`, the
stored bits `b`, the simulator words `m`, `r`, the LCHS word `l`, the fractional bits `F` of the
LCHS step, the CORDIC steps `n_c` for the accuracy `ζ/2` and the bits `⌈log₂ ⌈κ⌉⌉`,
`⌈log₂ ⌈1/κ⌉⌉` of the decoder scale `κ = kapQ q`. -/
def wordsB (q : PubT) : ℕ :=
  q.kx + q.b + q.params.m + q.params.r + q.params.l + q.F + Cordic.nOf (q.ζ / 2) +
    Nat.clog 2 ⌈kapQ q⌉₊ + Nat.clog 2 ⌈1 / kapQ q⌉₊

/-- **The per-call cost and the added work wires as polynomials in the words**: the gates
`G_C = 2 (|apG| + 28 k_x + 2) + 2 |arith| + 2 bP + bT + 1` of one private call are at most
`65536 (𝔴+1)³`, the added work wires `|ZA| + 6 k_x + 4 b + bT + bP + A_arith` at most
`4096 (𝔴+1)³`, and `bT, bP ≤ 5 (𝔴+1)`, `𝔴 = wordsB q`. -/
theorem binary_select_arith_words (q : PubT) :
    2 * ((apG q.kx q.b q.m q.params.l).length + (28 * q.kx + 2)) + 2 * (arQ q).circ.length +
        (2 * (arQ q).bP + (arQ q).bT + 1) ≤ 65536 * (wordsB q + 1) ^ 3 ∧
    (1 + 2 * (2 * q.m + 14) + (4 * q.m + 62) * (2 * q.m + 14)) + (6 * q.kx + 4 * q.b) +
        (arQ q).bT + (arQ q).bP + (arQ q).A ≤ 4096 * (wordsB q + 1) ^ 3 ∧
    (arQ q).bT ≤ 5 * (wordsB q + 1) ∧ (arQ q).bP ≤ 5 * (wordsB q + 1) := by
  obtain ⟨hc, hA, hT, hP⟩ := arQ_counts q
  have hg2 : Cordic.g2Of (Cordic.nOf (q.ζ / 2)) (kapQ q) =
      Nat.clog 2 ⌈kapQ q⌉₊ + Cordic.nOf (q.ζ / 2) + 5 := by
    unfold Cordic.g2Of
    rfl
  have hlk : Cordic.lkOf (kapQ q) = Nat.clog 2 ⌈1 / kapQ q⌉₊ := by
    unfold Cordic.lkOf
    rfl
  have hx : q.b + q.params.m + q.params.l + q.F + Cordic.g2Of (Cordic.nOf (q.ζ / 2)) (kapQ q) +
      Cordic.lkOf (kapQ q) ≤ wordsB q + 5 := by
    unfold wordsB
    omega
  obtain ⟨h1, h2, h3⟩ := arith_words q.b q.params.m q.params.l q.F (Cordic.nOf (q.ζ / 2))
    (Cordic.g2Of (Cordic.nOf (q.ζ / 2)) (kapQ q)) (Cordic.lkOf (kapQ q))
    (Cordic.wordOf (Cordic.nOf (q.ζ / 2))) (wordsB q) hx (by omega) (wordOf_le _)
  have hlen : (arQ q).circ.length ≤ 28355 * (wordsB q + 1) ^ 3 := hc.trans h1
  have hA' : (arQ q).A ≤ 1231 * (wordsB q + 1) ^ 3 := hA.le.trans h2
  have hT' : (arQ q).bT ≤ 5 * (wordsB q + 1) := hT.le.trans h3
  have hP' : (arQ q).bP ≤ 5 * (wordsB q + 1) := hP.le.trans h3
  have hkx : q.kx + q.b + q.m ≤ wordsB q := by
    have e : q.params.m = q.m := rfl
    unfold wordsB
    omega
  have hm1 : (q.m + 1) ^ 2 ≤ (wordsB q + 1) ^ 3 := by
    calc (q.m + 1) ^ 2 ≤ (wordsB q + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      _ ≤ (wordsB q + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hp1 : wordsB q + 1 ≤ (wordsB q + 1) ^ 3 := le_self_pow₀ (by omega) (by norm_num)
  have hap : (apG q.kx q.b q.m q.params.l).length ≤ 910 * (wordsB q + 1) ^ 3 :=
    (card_apG_le q.kx q.b q.m q.params.l).trans (Nat.mul_le_mul_left _ hm1)
  have hZA : 1 + 2 * (2 * q.m + 14) + (4 * q.m + 62) * (2 * q.m + 14) ≤
      897 * (wordsB q + 1) ^ 3 := by
    have h := card_ZA_le q.m
    rw [card_ZA] at h
    exact h.trans (Nat.mul_le_mul_left _ hm1)
  generalize (wordsB q + 1) ^ 3 = W at hlen hA' hap hZA hp1
  generalize 1 + 2 * (2 * q.m + 14) + (4 * q.m + 62) * (2 * q.m + 14) = Z at hZA ⊢
  refine ⟨by omega, by omega, hT', hP'⟩

/-- **The gates and work wires of coherent selection in the words** (equation
`ode:eq:gate-select-gates`). For the native selection circuit of `binary_native_gate_select`,
with `d` the filter degree, the gates beyond those of the released circuit,
`G_sel = 84 d (σ+3) + 6 d G_C`, are at most `393500 d (𝔴+1)³`, and the work wires added to the
released register, `A_sel = |ZA| + 6 k_x + 4 b + bT + bP + A_arith + 3`, at most
`4096 (𝔴+1)³ + 3`, for every `d` (`𝔴 = wordsB q` contains the reuse register `r` of the solver,
of about `log₂ (4 (d+1))` bits for its degree, but no factor `d`; for the circuit itself at
`δ = 4ν` see `binary_select_lemma_words`). -/
theorem select_gates_words (q : PubT) (d : ℕ) :
    84 * d * (q.σ + 3) + 6 * d * (2 * ((apG q.kx q.b q.m q.params.l).length + (28 * q.kx + 2)) +
        2 * (arQ q).circ.length + (2 * (arQ q).bP + (arQ q).bT + 1)) ≤
      393500 * d * (wordsB q + 1) ^ 3 ∧
    (1 + 2 * (2 * q.m + 14) + (4 * q.m + 62) * (2 * q.m + 14)) + (6 * q.kx + 4 * q.b) +
        (arQ q).bT + (arQ q).bP + (arQ q).A + 3 ≤ 4096 * (wordsB q + 1) ^ 3 + 3 := by
  obtain ⟨hGC, hAw, -, -⟩ := binary_select_arith_words q
  have hσ : q.σ + 3 ≤ 3 * (wordsB q + 1) ^ 3 := by
    have h1 : q.σ ≤ wordsB q := by
      have := q.hσ
      unfold wordsB
      omega
    have hp1 : wordsB q + 1 ≤ (wordsB q + 1) ^ 3 := le_self_pow₀ (by omega) (by norm_num)
    omega
  refine ⟨?_, by omega⟩
  have h1 : 84 * d * (q.σ + 3) ≤ 84 * d * (3 * (wordsB q + 1) ^ 3) :=
    Nat.mul_le_mul_left _ hσ
  have h2 : 6 * d * (2 * ((apG q.kx q.b q.m q.params.l).length + (28 * q.kx + 2)) +
      2 * (arQ q).circ.length + (2 * (arQ q).bP + (arQ q).bT + 1)) ≤
      6 * d * (65536 * (wordsB q + 1) ^ 3) := Nat.mul_le_mul_left _ hGC
  have e1 : 84 * d * (3 * (wordsB q + 1) ^ 3) = 252 * (d * (wordsB q + 1) ^ 3) := by ring
  have e2 : 6 * d * (65536 * (wordsB q + 1) ^ 3) = 393216 * (d * (wordsB q + 1) ^ 3) := by ring
  have e3 : 393500 * d * (wordsB q + 1) ^ 3 = 393500 * (d * (wordsB q + 1) ^ 3) := by ring
  rw [e1] at h1
  rw [e2] at h2
  rw [e3]
  omega

/-! ### The budget in the query shape -/

section Budget

variable {X n : Type*} [Fintype n] [DecidableEq n] {Zs : Type*} [Fintype Zs] [DecidableEq Zs]

/-- **The gate, call and qubit budget of the solver on branch-dependent meshes from binary data
with the public rescaling** (Theorem `ode:thm:gates`, time-dependent part, equations
`ode:eq:gate-main` and `ode:eq:gate-space` before finite-gate-set synthesis). Let the public data
`q` have `γ = gammaOf T η_H η_D (2g) (ε/2)`, and put `q* = qOf s T η_H η_D (2g) (ε/2)`,
`ℓ = log(1/ν)`. For the time-indexed binary data on the grid of `2^(2m)` points and the valid
circuits `loadC`, `wpC` of `binary_select_solver`, in every history the native protocol
(ratio `2g`)

* uses at most `73746000 g [q* (G_C + k_x + σ + m + r + ℓ (l+1) + 8) + G_src + A]` elementary
  gates, `G_C = 2 (|apG| + 28 k_x + 2) + 2 |arith| + 2 bP + bT + 1` the gates of one private call
  (the address program and the compute circuit, computed and uncomputed),
  `G_src = |loadC| + 2 |wpC|` and `A = k_x + |Zs| + (|ZA| + 6 k_x + 4 b) + bT + bP + A_arith`;
* makes at most `7864320 g q*` calls of each coherent sampled-time oracle besides `80 g` times
  the calls of `loadC` and twice those of `wpC`;

its register has `22 k_x + 16 m + 24 r + 4 l + 8 b + 2 (|ZA| + bT + bP + A_arith) + 2 |Zs| + 47`
qubits; and for every input and instance as in `binary_select_solver` (a positive source
quadrature on the `2^m` left-endpoint nodes, `RestB`), with the arithmetic budget
`98304 q* ζ + 3 ζs ≤ ν`, it has the guarantees `NOutcome`. -/
theorem binary_select_budget (q : PubT) (hq : q.OK)
    (hγ : q.γ = gammaOf q.T q.etaH q.etaD (2 * q.g) (q.ε / 2))
    (D : Data (X × Fin (2 ^ (2 * q.m))) n (Cfg (VW q.b)) q.s) (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (hdec : ∀ e z, D.decode e z = (q.c0 : ℂ) * gauss z)
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin (2 * q.m) ⊕ PY q.kx q.b)
      Query)) (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin (2 * q.m) ⊕ PY q.kx q.b) Query))
    (hwpV : ∀ i ∈ wpC, i.Valid) :
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
      98304 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * q.ζ + 3 * ζs ≤ q.params.nu →
      RestB q D en x Jl Wp wq fv G bf xs ys βG δG κ →
      NOutcome (prepQ q loadC wpC) q.params.ratio q.ε (q.params.ratio_ge hq.g_ge)
        (primsT (R := ℂ) (m := 2 * q.m) D en x) (xs q.T) := by
  have h := pubT_shapeOK q hq
  obtain ⟨-, hd, -, -, hJ, -⟩ := binary_ode_time_sizes q hq hγ
  have hq1 := h.one_le_q
  have hℓ := h.ell_ge
  have hg0 : 0 ≤ q.g := le_trans zero_le_one hq.g_ge
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- gates
    refine (binary_select_gate_count q hq loadC hloadV wpC hwpV).trans
      ((gate_budget_arith' 18000 q.g _ _ _ _ _ _ _ _ (by norm_num) hg0 hq1 hℓ hd hJ
        (Nat.cast_nonneg _) (by positivity) (by positivity) (by positivity)).trans
        (le_of_eq ?_))
    push_cast
    ring
  · -- calls
    intro c
    obtain ⟨-, -, hC, -, hWC, -⟩ := binary_select_counts q hq loadC hloadV wpC hwpV
    have hI0 : (0 : ℝ) ≤ (if c Query.rowLocation then 1 else 0) +
        (if c Query.columnLocation then 1 else 0) + (if c Query.value then 1 else 0) := by
      split_ifs <;> norm_num
    have hc : (nCallsN c (prepQ q loadC wpC) : ℝ) ≤ 12 * (q.params.d : ℝ) *
        (2 * ((if c Query.rowLocation then 1 else 0) + (if c Query.columnLocation then 1 else 0)
          + (if c Query.value then 1 else 0))) +
        ((nCallsN c loadC : ℝ) + 2 * nCallsN c wpC) := by
      have h1 : (nCallsN c (prepQ q loadC wpC) : ℝ) ≤ ((12 * q.params.d *
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
    obtain ⟨-, -, -, -, -, hcard⟩ := binary_select_counts q hq loadC hloadV wpC hwpV
    rw [hcard, q.params.card_W]
    show q.kx + 2 * (4 * (q.kx + 3) + 8 * q.params.m + 12 * q.params.r + 2 * q.params.l + 8 +
      ((1 + 2 * (2 * q.m + 14) + (4 * q.m + 62) * (2 * q.m + 14)) + (6 * q.kx + 4 * q.b) +
        (arQ q).bT + (arQ q).bP + (arQ q).A + 3) + Fintype.card Zs) + q.kx + 1 = _
    ring
  · -- guarantees
    obtain ⟨-, -, -, -, -, -, hout⟩ :=
      binary_select_solver q hq D en hrange hdec loadC hloadV wpC hwpV
    intro x hrH hcH hrD hcD hPSD Jl Wp wq fv G bf xs ys βG δG κ ζs hζs hload hwp hbud hR
    refine hout x hrH hcH hrD hcD hPSD Jl Wp wq fv G bf xs ys βG δG κ ζs hζs hload hwp ?_ hR
    have hζ := hq.ζ_pos.le
    have := mul_le_mul_of_nonneg_right hd hζ
    linarith

/-- The arithmetic of the gate budget in the words with the address registers: `q* (G_C + … +
ℓ (l+1) + 8)` and the wires are absorbed in `q* (w + ℓ + 1)³`. -/
theorem words_gate_arithB (c C g Q ℓ w GC Sm l Gs Zs Ap : ℝ) (hcC : 69644 * c ≤ C)
    (hc : 0 ≤ c) (hg : 0 ≤ g) (hQ : 1 ≤ Q) (hℓ : 1 ≤ ℓ) (hw : 0 ≤ w)
    (hGC : GC ≤ 65536 * (w + 1) ^ 3) (hSm : Sm ≤ 2 * w) (hl0 : 0 ≤ l) (hl : l ≤ w)
    (hAp : Ap ≤ 4097 * (w + 1) ^ 3) (hGs : 0 ≤ Gs) (hZs : 0 ≤ Zs) :
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
  have hin : Q * (GC + Sm + ℓ * (l + 1) + 8) + Gs + (Zs + Ap) ≤ 69644 * (Q * Y + Gs + Zs) := by
    linarith
  have hpos : 0 ≤ Q * Y + Gs + Zs := by positivity
  calc c * g * (Q * (GC + Sm + ℓ * (l + 1) + 8) + Gs + (Zs + Ap))
      ≤ c * g * (69644 * (Q * Y + Gs + Zs)) :=
        mul_le_mul_of_nonneg_left hin (mul_nonneg hc hg)
    _ = 69644 * c * g * (Q * Y + Gs + Zs) := by ring
    _ ≤ C * g * (Q * Y + Gs + Zs) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcC hg) hpos

/-- **Equations `ode:eq:gate-main` and `ode:eq:gate-space` in the words, branch-dependent
meshes.** With the public rescaling `γ = gammaOf T η_H η_D (2g) (ε/2)` of `binary_select_budget`,
`q* = qOf s T η_H η_D (2g) (ε/2)`, `ℓ = log(1/ν)` and `𝔴 = wordsB q`, for the time-indexed binary
data and the valid circuits `loadC`, `wpC` of `binary_select_solver`, in every history the native
protocol uses at most `6·10¹² g [q* (𝔴 + ℓ + 1)³ + G_src + |Zs|]` elementary gates
(`G_src = |loadC| + 2 |wpC|`), and its register has at most `10000 (𝔴+1)³ + 2 |Zs|` qubits. The
calls and the guarantees are those of `binary_select_budget`. -/
theorem binary_select_budget_words (q : PubT) (hq : q.OK)
    (hγ : q.γ = gammaOf q.T q.etaH q.etaD (2 * q.g) (q.ε / 2))
    (D : Data (X × Fin (2 ^ (2 * q.m))) n (Cfg (VW q.b)) q.s) (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (hdec : ∀ e z, D.decode e z = (q.c0 : ℂ) * gauss z)
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin (2 * q.m) ⊕ PY q.kx q.b)
      Query)) (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin (2 * q.m) ⊕ PY q.kx q.b) Query))
    (hwpV : ∀ i ∈ wpC, i.Valid) :
    ((nprotocol (prepQ q loadC wpC) q.params.ratio (q.params.ratio_ge hq.g_ge)).worstCost
        wGateN : ℝ) ≤
      6 * 10 ^ 12 * q.g * (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
          ((wordsB q : ℝ) + logBudget (2 * q.g) (q.ε / 2) + 1) ^ 3 +
        ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) + Fintype.card Zs) ∧
    Fintype.card (TNW q.params (Fin q.kx) Zs (ZA q.m ⊕ SZ4 q.kx q.b) (arQ q).bT (arQ q).bP
        (arQ q).A) ≤
      10000 * (wordsB q + 1) ^ 3 + 2 * Fintype.card Zs := by
  obtain ⟨hW, -, hcard, -⟩ := binary_select_budget q hq hγ D en hrange hdec loadC hloadV wpC hwpV
  obtain ⟨hGC, hAw, -, -⟩ := binary_select_arith_words q
  have h := pubT_shapeOK q hq
  have hσ := q.hσ
  have hp1 : wordsB q + 1 ≤ (wordsB q + 1) ^ 3 := le_self_pow₀ (by omega) (by norm_num)
  refine ⟨?_, ?_⟩
  · have hGC' : (((2 * ((apG q.kx q.b q.m q.params.l).length + (28 * q.kx + 2)) +
        2 * (arQ q).circ.length + (2 * (arQ q).bP + (arQ q).bT + 1) : ℕ) : ℝ)) ≤
        65536 * ((wordsB q : ℝ) + 1) ^ 3 := by exact_mod_cast hGC
    have hSm : (q.kx : ℝ) + q.σ + q.params.m + q.params.r ≤ 2 * (wordsB q : ℝ) := by
      have : q.kx + q.σ + q.params.m + q.params.r ≤ 2 * wordsB q := by
        unfold wordsB
        omega
      exact_mod_cast this
    have hl : (q.params.l : ℝ) ≤ wordsB q := by
      have : q.params.l ≤ wordsB q := by
        unfold wordsB
        omega
      exact_mod_cast this
    have hAp : (q.kx : ℝ) + ((((1 + 2 * (2 * q.m + 14) + (4 * q.m + 62) * (2 * q.m + 14)) +
        (6 * q.kx + 4 * q.b) : ℕ) : ℝ) + (arQ q).bT + (arQ q).bP + (arQ q).A) ≤
        4097 * ((wordsB q : ℝ) + 1) ^ 3 := by
      have hkx : q.kx ≤ wordsB q := by
        unfold wordsB
        omega
      have : q.kx + ((1 + 2 * (2 * q.m + 14) + (4 * q.m + 62) * (2 * q.m + 14)) +
          (6 * q.kx + 4 * q.b) + (arQ q).bT + (arQ q).bP + (arQ q).A) ≤
          4097 * (wordsB q + 1) ^ 3 := by omega
      exact_mod_cast this
    have key := words_gate_arithB 73746000 (6 * 10 ^ 12) q.g
      (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) (logBudget (2 * q.g) (q.ε / 2))
      (wordsB q) _ _ (q.params.l : ℝ) ((nGatesN loadC : ℝ) + 2 * nGatesN wpC)
      (Fintype.card Zs : ℝ) _
      (by norm_num) (by norm_num) (le_trans zero_le_one hq.g_ge) h.one_le_q h.ell_ge
      (Nat.cast_nonneg _) hGC' hSm (Nat.cast_nonneg _) hl hAp
      (add_nonneg (Nat.cast_nonneg _) (mul_nonneg (by norm_num) (Nat.cast_nonneg _)))
      (Nat.cast_nonneg _)
    refine hW.trans (le_trans (le_of_eq ?_) key)
    ring
  · rw [hcard]
    have h24 : 22 * q.kx + 16 * q.params.m + 24 * q.params.r + 4 * q.params.l + 8 * q.b ≤
        24 * wordsB q := by
      unfold wordsB
      omega
    omega

end Budget

end

end SparseHamiltonian.GateBinarySelect
