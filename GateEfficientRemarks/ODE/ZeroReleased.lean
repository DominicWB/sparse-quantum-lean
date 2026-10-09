import GateEfficientRemarks.ODE.ZeroWordsSum
import ZeroTimeGateODE.Binary

/-!
# Zero time or a known zero generator: the budgets in `𝔟` on the released binary register

The released library `GateEfficientBitBudget` proves equations `ode:eq:gate-main` and
`ode:eq:gate-space` of Theorem `ode:thm:gates` in the word budget `𝔟` of
`ode:eq:gate-word-budget` for the solver from binary data under the released public conditions
(`T > 0`, `η_H + η_D > 0`, the public rescaling `γ = gammaOf T η_H η_D g ε`), and the released
library `ZeroTimeGateODE` gives, for every `T ≥ 0`, the combined preparation
`ZeroTimeGateODE.bprepC q srcC` on the released binary register (the direct source assembly in the
zero case `BZeroCase`: `T = 0 ∨ η_H + η_D = 0`). The public rescaling vanishes in the zero case,
where the rescaling `γ ∈ (0, 1]` is a free public parameter; with `γ` of bit length `b_data` the
released register keeps every bound of the positive case with the same constants:

* `binary_ode_budget_count_zero` (zero case, no hypothesis on `γ`, `ζ` or the bit lengths): the
  explicit count `36873000 g [q* (G_C + k_x + σ + m + r + k + ℓ (l+1) + 8) + G_src + A]` of
  `GateODEBudget.binary_ode_budget` (`count_arith` is its arithmetic);
* `binary_ode_budget_bits_zero_released` (zero case): the protocol `nprotocol (bprepC q srcC) g`
  on the released register has, in the order of `GateBitBudget.binary_ode_budget_bits`, at most
  `10²⁰ g [q* (𝔟+1)³ + G_src + |Zs|]` gates and `3·10¹¹ (𝔟+1)³ + 2 |Zs|` qubits (for
  `𝔟 = bitB b_data (2^k_x) M m_src q* g ε` with every `M`, `m_src`), the words
  `𝔴 + ℓ ≤ 300 (𝔟+1)`, the word forms `3·10¹² g [q* (𝔴+ℓ+1)³ + G_src + |Zs|]` and
  `10⁴ (𝔴+1)³ + 2 |Zs|`, the explicit count, at most `40 g` times the calls of the source circuits
  (no matrix call), the register identity (`card_NW_eq`), and further `q* = ℓ`, valid trials, no
  call of a kind that the source circuits do not call, and `NOutcome` under the zero-case
  conditions;
* `binary_ode_budget_bits_nonneg` (every `T ≥ 0`): every conclusion of the released
  `GateBitBudget.binary_ode_budget_bits` (gates and qubits in `𝔟`, words, word forms, the explicit
  count, the calls with the matrix part `if BZeroCase q then 0 else 3932160 g q* (…)`, the register
  identity and `NOutcome` under the released hypotheses), in the same order, for the protocol
  `nprotocol (bprepC q srcC) g`, with the validity of the trials inserted before `NOutcome`, with
  `γ` of bit length `b_data` in the zero case and the public rescaling otherwise.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateRemarks.ODE

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit GateNative GateBinary
open ZeroTimeGateODE (zprepC srcRot bprepC BPublicOK0 BZeroCase)
open GateBinaryODE (Pub mLift SZ4 card_SZ4)
open SparseHamiltonian.GateBitBudget (bitB bitB_nonneg HasBits)
open GateODEBudget (qOf words gammaOf)
open ImprovedODEQueryBudget (logBudget)
open NativeSparseBlockEncoding (Data Query)
open ODEStateNormalization (unitDirection)
open scoped InnerProduct BigOperators

variable {X n : Type*} [Fintype n] [DecidableEq n] {Zs : Type*} [Fintype Zs] [DecidableEq Zs]

/-- **The arithmetic of the explicit count in the zero case**: the gates
`40 g (G + 2) + 20 g (4 (|W| + |XW| + Z + k_x) + 3)` of the direct source assembly on the released
binary register are at most the released explicit count
`36873000 g [Q (G_C + k_x + σ + m + r + k + L (l+1) + 8) + G + (k_x + Z + (6 k_x + 4 b) + bT + bP +
A)]` for `Q, L ≥ 1` and nonnegative data (`G_C = 2 (28 k_x + 2) + 2 c + 2 bP + bT + 1`, `c` the
length of the arithmetic circuit). -/
theorem count_arith {g Q L G Z kx σ m r k l b bT bP A c : ℝ} (hg : 0 ≤ g) (hQ : 1 ≤ Q)
    (hL : 1 ≤ L) (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hkx : 0 ≤ kx) (hσ : 0 ≤ σ) (hm : 0 ≤ m)
    (hr : 0 ≤ r) (hk : 0 ≤ k) (hl : 0 ≤ l) (hb : 0 ≤ b) (hbT : 0 ≤ bT) (hbP : 0 ≤ bP)
    (hA : 0 ≤ A) (hc : 0 ≤ c) :
    40 * g * (G + 2) + 20 * g * (4 * (4 * (kx + 3) + 6 * m + 12 * r + 2 * k + 2 * l + 8 +
      (6 * kx + 4 * b + bT + bP + A + 3) + Z + kx) + 3) ≤
    36873000 * g * (Q * (2 * (28 * kx + 2) + 2 * c + (2 * bP + bT + 1) + kx + σ + m + r + k +
      L * (l + 1) + 8) + G + (kx + Z + (6 * kx + 4 * b) + bT + bP + A)) := by
  set S := 2 * (28 * kx + 2) + 2 * c + (2 * bP + bT + 1) + kx + σ + m + r + k + L * (l + 1) + 8
    with hS
  have hl1 : l + 1 ≤ L * (l + 1) := le_mul_of_one_le_left (by linarith) hL
  have hS1 : kx + m + r + k + l + 9 ≤ S := by rw [hS]; linarith
  have hQS : S ≤ Q * S := le_mul_of_one_le_left (by linarith) hQ
  have key : 40 * (G + 2) + 20 * (4 * (4 * (kx + 3) + 6 * m + 12 * r + 2 * k + 2 * l + 8 +
      (6 * kx + 4 * b + bT + bP + A + 3) + Z + kx) + 3) ≤
      36873000 * (Q * S + G + (kx + Z + (6 * kx + 4 * b) + bT + bP + A)) := by linarith
  have h := mul_le_mul_of_nonneg_left key hg
  linarith

/-- **The explicit count of `GateODEBudget.binary_ode_budget` in the zero case** (equation
`ode:eq:gate-main` with the remark on zero time and a known zero generator): for binary public data
with `BPublicOK0 q` in the zero case and valid source circuits, the protocol
`nprotocol (bprepC q srcC) g` on the released register uses at most
`36873000 g [q* (G_C + k_x + σ + m + r + k + ℓ (l+1) + 8) + G_src + A]` gates in every history
(`G_C = 2 (28 k_x + 2) + 2 |arith| + 2 bP + bT + 1`,
`A = k_x + |Zs| + (6 k_x + 4 b) + bT + bP + A_arith`), with no hypothesis on the rescaling, the
arithmetic accuracy or the bit lengths. -/
theorem binary_ode_budget_count_zero (q : Pub) (hq : BPublicOK0 q) (hz : BZeroCase q)
    (srcC : Bool → List (NInstr ((Unit ⊕ Fin q.kx) ⊕ Zs) (PY q.kx q.b) Query))
    (hsrcV : ∀ c, ∀ i ∈ srcC c, i.Valid) :
    ((nprotocol (bprepC q srcC) q.g hq.g_ge).worstCost wGateN : ℝ) ≤
      36873000 * q.g * (qOf q.s q.T q.etaH q.etaD q.g q.ε *
          (((2 * (28 * q.kx + 2) + 2 * q.ar.circ.length + (2 * q.ar.bP + q.ar.bT + 1) : ℕ) : ℝ) +
            q.kx + q.σ + q.params.m + q.params.r + q.params.k +
            logBudget q.g q.ε * ((q.params.l : ℝ) + 1) + 8) +
        ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true)) +
        ((q.kx : ℝ) + Fintype.card Zs + ((6 * q.kx + 4 * q.b : ℕ) : ℝ) + q.ar.bT + q.ar.bP +
          q.ar.A)) := by
  obtain ⟨-, -, -, hWG, -, -, -, -⟩ := ZeroTimeGateODE.native_ode_solver_zero
    (S := Fin q.kx) (Zs := Zs) (Z := SZ4 q.kx q.b) (Y := PY q.kx q.b) (J := Query)
    q.params.a q.params.m q.params.r q.params.K q.params.k q.params.l q.params.f
    q.ar.bT q.ar.bP q.ar.A q.T q.g q.ε q.r₀ q.rb hq.T_nonneg hq.g_ge hq.ε_pos hq.ε_half
    hq.r₀_nonneg hq.rb_nonneg hq.B_pos srcC hsrcV
  have hp : bprepC q srcC = zprepC (srcRot q.T q.r₀ q.rb) srcC := by
    rw [bprepC, if_pos hz]
  rw [hp]
  refine hWG.trans ?_
  have hε1 : q.ε ≤ 1 := hq.ε_half.trans (by norm_num)
  have hQ1 : 1 ≤ qOf q.s q.T q.etaH q.etaD q.g q.ε :=
    one_le_qOf hq.T_nonneg hq.etaH_nonneg hq.etaD_nonneg hq.g_ge hq.ε_pos hε1
  have hℓ1 := ImprovedODEQueryBudget.logBudget_ge_one q.g q.ε hq.g_ge hq.ε_pos hε1
  have hg0 : 0 ≤ q.g := le_trans zero_le_one hq.g_ge
  have h2 : Fintype.card (GateODE.AW q.params.a q.params.m q.params.r q.params.K q.params.k
      q.params.l q.params.f) =
      4 * (q.kx + 3) + 6 * q.params.m + 12 * q.params.r + 2 * q.params.k + 2 * q.params.l +
        8 := q.params.card_W
  have hXW : Fintype.card (XW (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) =
      6 * q.kx + 4 * q.b + q.ar.bT + q.ar.bP + q.ar.A + 3 := by
    simp only [XW, AWr, Fintype.card_sum, Fintype.card_fin]
    ring
  rw [h2, hXW, Fintype.card_fin]
  generalize qOf q.s q.T q.etaH q.etaD q.g q.ε = Q at hQ1 ⊢
  generalize logBudget q.g q.ε = L at hℓ1 ⊢
  push_cast
  exact count_arith (G := (nGatesN (srcC false) : ℝ) + nGatesN (srcC true))
    (Z := (Fintype.card Zs : ℝ)) (kx := (q.kx : ℝ)) (σ := (q.σ : ℝ)) (m := (q.params.m : ℝ))
    (r := (q.params.r : ℝ)) (k := (q.params.k : ℝ)) (l := (q.params.l : ℝ)) (b := (q.b : ℝ))
    (bT := (q.ar.bT : ℝ)) (bP := (q.ar.bP : ℝ)) (A := (q.ar.A : ℝ))
    (c := (q.ar.circ.length : ℝ)) hg0 hQ1 hℓ1
    (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- **Equations `ode:eq:gate-main` and `ode:eq:gate-space` in `𝔟` on the released binary register
for zero time or a known zero generator, constant coefficients** (Theorem `ode:thm:gates` with its
remark: direct source assembly, no matrix calls).

For binary public data with `BPublicOK0 q` in the zero case `T = 0 ∨ η_H + η_D = 0`, a rescaling
`γ` of bit length `b_data`, an arithmetic accuracy `ζ ≥ ν/(196608 q*)`, stored bits `b ≤ b_data`,
`c₀`, `η_H`, `η_D` of bit length `b_data`, valid source circuits `srcC` and any `M`, `m_src`, put
`q* = qOf s T η_H η_D g ε` (`= ℓ`) and `𝔟 = bitB b_data (2^k_x) M m_src q* g ε`. The protocol
`nprotocol (bprepC q srcC) g` on the released binary register has every bound of
`GateBitBudget.binary_ode_budget_bits`, in its order: at most `10²⁰ g [q* (𝔟+1)³ + G_src + |Zs|]`
elementary gates in every history (`G_src = |srcC 0| + |srcC 1|`) and `3·10¹¹ (𝔟+1)³ + 2 |Zs|`
qubits; the words `𝔴 = GateODEBudget.words q` satisfy `𝔴 + ℓ ≤ 300 (𝔟+1)`; at most
`3·10¹² g [q* (𝔴+ℓ+1)³ + G_src + |Zs|]` gates and `10⁴ (𝔴+1)³ + 2 |Zs|` qubits; at most
`36873000 g [q* (G_C + k_x + σ + m + r + k + ℓ (l+1) + 8) + G_src + A]` gates; at most
`40 g (calls_c(srcC 0) + calls_c(srcC 1))` calls of every kind `c` (no matrix call); and
`|NW| = 22 k_x + 12 m + 24 r + 4 k + 4 l + 8 b + 2 (bT + bP + A_arith) + 2 |Zs| + 47`; further
`q* = ℓ`, the trials are valid, every history makes no call of a kind that the source circuits do
not call, and for every input with the
row energy promises, unitary source interfaces approximated by the source circuits within `ζs`,
`2 ζs ≤ ν`, the public norms, the seed promises, `x(T) ≠ 0` and `r₀ + T r_b ≤ g ‖x(T)‖`, the
protocol has the guarantee `NOutcome` against the solution `x(T)` of `x' = -M̂ x + b`. -/
theorem binary_ode_budget_bits_zero_released (bd : ℕ) (q : Pub) (hq : BPublicOK0 q)
    (hz : BZeroCase q) (hγb : HasBits bd q.γ)
    (hζ : q.params.nu ≤ 196608 * qOf q.s q.T q.etaH q.etaD q.g q.ε * q.ζ) (hb : q.b ≤ bd)
    (hc0 : HasBits bd q.c0) (hH : HasBits bd q.etaH) (hD : HasBits bd q.etaD)
    (D : Data X n (Cfg (VW q.b)) q.s) (en : Cfg (Fin q.kx) ≃ n)
    (srcC : Bool → List (NInstr ((Unit ⊕ Fin q.kx) ⊕ Zs) (PY q.kx q.b) Query))
    (hsrcV : ∀ c, ∀ i ∈ srcC c, i.Valid) (M msrc : ℕ) :
    ((nprotocol (bprepC q srcC) q.g hq.g_ge).worstCost wGateN : ℝ) ≤
      10 ^ 20 * q.g * (qOf q.s q.T q.etaH q.etaD q.g q.ε *
          (bitB bd (2 ^ q.kx) M msrc (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε + 1) ^ 3 +
        ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true)) + Fintype.card Zs) ∧
    (Fintype.card (NW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) : ℝ) ≤
      3 * 10 ^ 11 * (bitB bd (2 ^ q.kx) M msrc (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε +
        1) ^ 3 + 2 * Fintype.card Zs ∧
    (words q : ℝ) + logBudget q.g q.ε ≤
      300 * (bitB bd (2 ^ q.kx) M msrc (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε + 1) ∧
    ((nprotocol (bprepC q srcC) q.g hq.g_ge).worstCost wGateN : ℝ) ≤
      3 * 10 ^ 12 * q.g * (qOf q.s q.T q.etaH q.etaD q.g q.ε *
          ((words q : ℝ) + logBudget q.g q.ε + 1) ^ 3 +
        ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true)) + Fintype.card Zs) ∧
    Fintype.card (NW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) ≤
      10000 * (words q + 1) ^ 3 + 2 * Fintype.card Zs ∧
    ((nprotocol (bprepC q srcC) q.g hq.g_ge).worstCost wGateN : ℝ) ≤
      36873000 * q.g * (qOf q.s q.T q.etaH q.etaD q.g q.ε *
          (((2 * (28 * q.kx + 2) + 2 * q.ar.circ.length + (2 * q.ar.bP + q.ar.bT + 1) : ℕ) : ℝ) +
            q.kx + q.σ + q.params.m + q.params.r + q.params.k +
            logBudget q.g q.ε * ((q.params.l : ℝ) + 1) + 8) +
        ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true)) +
        ((q.kx : ℝ) + Fintype.card Zs + ((6 * q.kx + 4 * q.b : ℕ) : ℝ) + q.ar.bT + q.ar.bP +
          q.ar.A)) ∧
    (∀ c : Query → Bool, ((nprotocol (bprepC q srcC) q.g hq.g_ge).worstCost (wCallN c) : ℝ) ≤
      40 * q.g * ((nCallsN c (srcC false) : ℝ) + nCallsN c (srcC true))) ∧
    Fintype.card (NW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) =
      22 * q.kx + 12 * q.params.m + 24 * q.params.r + 4 * q.params.k + 4 * q.params.l +
        8 * q.b + 2 * (q.ar.bT + q.ar.bP + q.ar.A) + 2 * Fintype.card Zs + 47 ∧
    qOf q.s q.T q.etaH q.etaD q.g q.ε = logBudget q.g q.ε ∧
    (∀ j, ∀ i ∈ trialN (bprepC q srcC) j, i.Valid) ∧
    (∀ c : Query → Bool, nCallsN c (srcC false) = 0 → nCallsN c (srcC true) = 0 →
      (nprotocol (bprepC q srcC) q.g hq.g_ge).worstCost (wCallN c) = 0) ∧
    ∀ x : X,
      (∀ i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ q.etaH ^ 2) →
      (∀ i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ q.etaD ^ 2) →
      ∀ (Jsrc : Bool → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ) (x0 v : Reg (Fin q.kx) ℂ)
        (ζs : ℝ),
      (∀ c, IsUnitary (Jsrc c)) →
      0 ≤ ζs →
      (∀ c, ApproxOn CleanX (nrun (prims (R := ℂ) D en x) (srcC c))
        (liftB (srcIdeal c (Jsrc c))) ζs) →
      2 * ζs ≤ q.params.nu →
      ‖x0‖ = q.r₀ → ‖v‖ = q.rb →
      (x0 ≠ 0 → Jsrc false (seedV (S := Fin q.kx)) = unitDirection x0) →
      (v ≠ 0 → Jsrc true (seedV (S := Fin q.kx)) = unitDirection v) →
      ODEConstantForcing.solution (-mLift D en x) x0 v q.T ≠ 0 →
      q.r₀ + q.T * q.rb ≤ q.g * ‖ODEConstantForcing.solution (-mLift D en x) x0 v q.T‖ →
      NOutcome (bprepC q srcC) q.g q.ε hq.g_ge (prims (R := ℂ) D en x)
        (ODEConstantForcing.solution (-mLift D en x) x0 v q.T) := by
  obtain ⟨hV, -, -, hWG, hWC, hno, hcardZ, hout⟩ := ZeroTimeGateODE.native_ode_solver_zero
    (S := Fin q.kx) (Zs := Zs) (Z := SZ4 q.kx q.b) (Y := PY q.kx q.b) (J := Query)
    q.params.a q.params.m q.params.r q.params.K q.params.k q.params.l q.params.f
    q.ar.bT q.ar.bP q.ar.A q.T q.g q.ε q.r₀ q.rb hq.T_nonneg hq.g_ge hq.ε_pos hq.ε_half
    hq.r₀_nonneg hq.rb_nonneg hq.B_pos srcC hsrcV
  have hp : bprepC q srcC = zprepC (srcRot q.T q.r₀ q.rb) srcC := by
    rw [bprepC, if_pos hz]
  -- the arithmetic of the bounds
  have hε1 : q.ε ≤ 1 := hq.ε_half.trans (by norm_num)
  have hg0 : 0 ≤ q.g := le_trans zero_le_one hq.g_ge
  have hQ1 : 1 ≤ qOf q.s q.T q.etaH q.etaD q.g q.ε :=
    one_le_qOf hq.T_nonneg hq.etaH_nonneg hq.etaD_nonneg hq.g_ge hq.ε_pos hε1
  have hQz : qOf q.s q.T q.etaH q.etaD q.g q.ε = logBudget q.g q.ε :=
    qOf_zero hq.etaH_nonneg hq.etaD_nonneg hz
  have hℓ1 := ImprovedODEQueryBudget.logBudget_ge_one q.g q.ε hq.g_ge hq.ε_pos hε1
  have hQg : 0 ≤ qOf q.s q.T q.etaH q.etaD q.g q.ε * q.g := by positivity
  have hB0 := bitB_nonneg bd (2 ^ q.kx) M msrc hQg hq.ε_pos hε1
  have hw0 := zero_words_le bd q hq hz hγb hζ hb hc0 hH hD
  have hmono := GateBitBudget.bitB_mono bd (2 ^ q.kx) 0 0 M msrc
    (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε (Nat.zero_le _) (Nat.zero_le _)
  have hw : (words q : ℝ) + logBudget q.g q.ε ≤
      300 * (bitB bd (2 ^ q.kx) M msrc (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε + 1) := by
    linarith
  have hcW := card_NW_le q (Zs := Zs)
  have hcnt := binary_ode_budget_count_zero q hq hz srcC hsrcV
  have hcardEq := card_NW_eq q (Zs := Zs)
  have hcW' : (Fintype.card (NW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) :
      ℝ) ≤ 10000 * ((words q : ℝ) + 1) ^ 3 + 2 * Fintype.card Zs := by
    exact_mod_cast hcW
  rw [card_SZ4] at hcardZ
  have htest : Fintype.card (GateODE.AW q.params.a q.params.m q.params.r q.params.K q.params.k
      q.params.l q.params.f) + Fintype.card (XW (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) +
      Fintype.card Zs + Fintype.card (Fin q.kx) ≤
      Fintype.card (NW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) := by
    have h1 := (hcardZ : Fintype.card
      (NW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) = _)
    have h2 : Fintype.card (XW (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) =
        6 * q.kx + 4 * q.b + q.ar.bT + q.ar.bP + q.ar.A + 3 := by
      simp only [XW, AWr, Fintype.card_sum, Fintype.card_fin]
      ring
    rw [h1, h2]
    omega
  have htest' : (Fintype.card (GateODE.AW q.params.a q.params.m q.params.r q.params.K q.params.k
      q.params.l q.params.f) : ℝ) + Fintype.card (XW (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) +
      Fintype.card Zs + Fintype.card (Fin q.kx) ≤
      Fintype.card (NW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) := by
    exact_mod_cast htest
  have hW : ((nprotocol (bprepC q srcC) q.g hq.g_ge).worstCost wGateN : ℝ) ≤
      40 * q.g * ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true)) + 140 * q.g +
        80 * q.g * Fintype.card
          (NW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) := by
    rw [hp]
    refine hWG.trans ?_
    push_cast
    have := mul_le_mul_of_nonneg_left htest' hg0
    linarith
  generalize hB : bitB bd (2 ^ q.kx) M msrc (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε = B
    at hB0 hw
  generalize hQ : qOf q.s q.T q.etaH q.etaD q.g q.ε = Q at hQ1 hQg hQz hcnt
  generalize hN : Fintype.card
    (NW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) = N at hcW hcW' hW hcardEq
  have hwr0 : (0 : ℝ) ≤ words q := Nat.cast_nonneg _
  have hZ0 : (0 : ℝ) ≤ Fintype.card Zs := Nat.cast_nonneg _
  have hG0 : (0 : ℝ) ≤ (nGatesN (srcC false) : ℝ) + nGatesN (srcC true) := by positivity
  have hcube := GateBitBudget.cube_le hwr0 hB0 (c := 300) (by linarith)
  have hY1 : 1 ≤ (B + 1) ^ 3 := one_le_pow₀ (by linarith)
  have hspace : (N : ℝ) ≤ 3 * 10 ^ 11 * (B + 1) ^ 3 + 2 * Fintype.card Zs := by
    have : (10000 : ℝ) * ((words q : ℝ) + 1) ^ 3 ≤ 10000 * ((300 + 1) ^ 3 * (B + 1) ^ 3) :=
      mul_le_mul_of_nonneg_left hcube (by norm_num)
    linarith
  have hV1 : 1 ≤ ((words q : ℝ) + logBudget q.g q.ε + 1) ^ 3 := one_le_pow₀ (by linarith)
  have hV2 : ((words q : ℝ) + 1) ^ 3 ≤ ((words q : ℝ) + logBudget q.g q.ε + 1) ^ 3 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 3
  refine ⟨?_, hspace, hw, ?_, hcW, hcnt, ?_, hcardEq, hQz, ?_, ?_, ?_⟩
  · -- gates in `𝔟`
    refine hW.trans ?_
    have h1 : q.g * N ≤ q.g * (3 * 10 ^ 11 * (B + 1) ^ 3 + 2 * Fintype.card Zs) :=
      mul_le_mul_of_nonneg_left hspace hg0
    have h2 : q.g * (B + 1) ^ 3 ≤ q.g * (Q * (B + 1) ^ 3) :=
      mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (by linarith) hQ1) hg0
    have h3 : q.g * 1 ≤ q.g * (Q * (B + 1) ^ 3) :=
      mul_le_mul_of_nonneg_left (one_le_mul_of_one_le_of_one_le hQ1 hY1) hg0
    have h4 : 0 ≤ q.g * ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true)) := mul_nonneg hg0 hG0
    have h5 : 0 ≤ q.g * (Fintype.card Zs : ℝ) := mul_nonneg hg0 hZ0
    linarith
  · -- gates in the words
    refine hW.trans ?_
    have h1 : q.g * N ≤ q.g * (10000 * ((words q : ℝ) + 1) ^ 3 + 2 * Fintype.card Zs) :=
      mul_le_mul_of_nonneg_left hcW' hg0
    have h2 : q.g * ((words q : ℝ) + logBudget q.g q.ε + 1) ^ 3 ≤
        q.g * (Q * ((words q : ℝ) + logBudget q.g q.ε + 1) ^ 3) :=
      mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (by linarith) hQ1) hg0
    have h3 : q.g * ((words q : ℝ) + 1) ^ 3 ≤ q.g * ((words q : ℝ) + logBudget q.g q.ε + 1) ^ 3 :=
      mul_le_mul_of_nonneg_left hV2 hg0
    have h3' : q.g * 1 ≤ q.g * ((words q : ℝ) + logBudget q.g q.ε + 1) ^ 3 :=
      mul_le_mul_of_nonneg_left hV1 hg0
    have h4 : 0 ≤ q.g * ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true)) := mul_nonneg hg0 hG0
    have h5 : 0 ≤ q.g * (Fintype.card Zs : ℝ) := mul_nonneg hg0 hZ0
    linarith
  · intro c
    rw [hp]
    have h := hWC c
    push_cast at h
    exact h
  · rw [hp]
    exact hV
  · intro c h0 h1
    rw [hp]
    exact hno c h0 h1
  · intro x hrH hrD Jsrc x0 v ζs hJ hζs hsrc hbud hx0 hv hpx hpv hne hBud
    have ht := ZeroTimeGateODE.binary_target_zero q hq hz D en x hrH hrD x0 v
    rw [ht] at hne hBud ⊢
    have hnu : q.params.nu = ImprovedODEQueryBudget.precision q.g q.ε := rfl
    rw [hnu] at hbud
    rw [hp]
    exact hout (prims (R := ℂ) D en x) Jsrc x0 v ζs (prims_isUnitary D en x) hJ hζs hsrc hbud
      hx0 hv hpx hpv hne hBud

/-- **Equations `ode:eq:gate-main` and `ode:eq:gate-space` in `𝔟` from binary sparse data for
every `T ≥ 0`, constant coefficients** (Theorem `ode:thm:gates`, equation
`ode:eq:gate-word-budget`, with its remark on zero time and a known zero generator).

For binary public data with `BPublicOK0 q` (every `T ≥ 0`), the rescaling `γ` of bit length
`b_data` in the zero case `BZeroCase q` and the public rescaling `γ = gammaOf T η_H η_D g ε`
otherwise, an arithmetic accuracy `ζ ≥ ν/(196608 q*)`, stored bits `b ≤ b_data` and `c₀`, `T`,
`η_H`, `η_D` of bit length `b_data`, and the binary data and valid source circuits of the released
`GateBitBudget.binary_ode_budget_bits`, put `𝔟 = bitB b_data (2^k_x) (2^m) (2^k) q* g ε`. The
protocol `nprotocol (bprepC q srcC) g` on the released binary register uses at most
`10²⁰ g [q* (𝔟+1)³ + G_src + |Zs|]` gates in every history and has at most
`3·10¹¹ (𝔟+1)³ + 2 |Zs|` qubits; the words satisfy `𝔴 + ℓ ≤ 300 (𝔟+1)`; at most
`3·10¹² g [q* (𝔴+ℓ+1)³ + G_src + |Zs|]` gates and `10⁴ (𝔴+1)³ + 2 |Zs|` qubits; at most
`36873000 g [q* (G_C + k_x + σ + m + r + k + ℓ (l+1) + 8) + G_src + A]` gates; every history
makes at most `(if BZeroCase q then 0 else 3932160 g q* ([row] + [col] + [value])) +
40 g (calls_c(srcC 0) + calls_c(srcC 1))` calls of every kind `c`; the register has
`22 k_x + 12 m + 24 r + 4 k + 4 l + 8 b + 2 (bT + bP + A_arith) + 2 |Zs| + 47` qubits; and for
every input with the released energy and accretivity promises and the released source hypotheses
(`98304 q* ζ + 2 ζs ≤ ν`), the protocol has the guarantee `NOutcome` against the solution `x(T)`
of `x' = -M̂ x + b`: every conclusion of `GateBitBudget.binary_ode_budget_bits`, in its order,
with the validity of the trials inserted before `NOutcome`. -/
theorem binary_ode_budget_bits_nonneg (bd : ℕ) (q : Pub) (hq : BPublicOK0 q)
    (hγ : if BZeroCase q then HasBits bd q.γ else q.γ = gammaOf q.T q.etaH q.etaD q.g q.ε)
    (hζ : q.params.nu ≤ 196608 * qOf q.s q.T q.etaH q.etaD q.g q.ε * q.ζ) (hb : q.b ≤ bd)
    (hc0 : HasBits bd q.c0) (hT : HasBits bd q.T) (hH : HasBits bd q.etaH)
    (hD : HasBits bd q.etaD)
    (D : Data X n (Cfg (VW q.b)) q.s) (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (hdec : ∀ e z, D.decode e z = (q.c0 : ℂ) * gauss z)
    (srcC : Bool → List (NInstr ((Unit ⊕ Fin q.kx) ⊕ Zs) (PY q.kx q.b) Query))
    (hsrcV : ∀ c, ∀ i ∈ srcC c, i.Valid) :
    ((nprotocol (bprepC q srcC) q.g hq.g_ge).worstCost wGateN : ℝ) ≤
      10 ^ 20 * q.g * (qOf q.s q.T q.etaH q.etaD q.g q.ε *
          (bitB bd (2 ^ q.kx) (2 ^ q.params.m) (2 ^ q.params.k)
            (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε + 1) ^ 3 +
        ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true)) + Fintype.card Zs) ∧
    (Fintype.card (NW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) : ℝ) ≤
      3 * 10 ^ 11 * (bitB bd (2 ^ q.kx) (2 ^ q.params.m) (2 ^ q.params.k)
          (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε + 1) ^ 3 + 2 * Fintype.card Zs ∧
    (words q : ℝ) + logBudget q.g q.ε ≤
      300 * (bitB bd (2 ^ q.kx) (2 ^ q.params.m) (2 ^ q.params.k)
        (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε + 1) ∧
    ((nprotocol (bprepC q srcC) q.g hq.g_ge).worstCost wGateN : ℝ) ≤
      3 * 10 ^ 12 * q.g * (qOf q.s q.T q.etaH q.etaD q.g q.ε *
          ((words q : ℝ) + logBudget q.g q.ε + 1) ^ 3 +
        ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true)) + Fintype.card Zs) ∧
    Fintype.card (NW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) ≤
      10000 * (words q + 1) ^ 3 + 2 * Fintype.card Zs ∧
    ((nprotocol (bprepC q srcC) q.g hq.g_ge).worstCost wGateN : ℝ) ≤
      36873000 * q.g * (qOf q.s q.T q.etaH q.etaD q.g q.ε *
          (((2 * (28 * q.kx + 2) + 2 * q.ar.circ.length + (2 * q.ar.bP + q.ar.bT + 1) : ℕ) : ℝ) +
            q.kx + q.σ + q.params.m + q.params.r + q.params.k +
            logBudget q.g q.ε * ((q.params.l : ℝ) + 1) + 8) +
        ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true)) +
        ((q.kx : ℝ) + Fintype.card Zs + ((6 * q.kx + 4 * q.b : ℕ) : ℝ) + q.ar.bT + q.ar.bP +
          q.ar.A)) ∧
    (∀ c : Query → Bool, ((nprotocol (bprepC q srcC) q.g hq.g_ge).worstCost (wCallN c) : ℝ) ≤
      (if BZeroCase q then 0 else 3932160 * q.g * qOf q.s q.T q.etaH q.etaD q.g q.ε *
          ((if c Query.rowLocation then 1 else 0) + (if c Query.columnLocation then 1 else 0) +
            (if c Query.value then 1 else 0))) +
        40 * q.g * ((nCallsN c (srcC false) : ℝ) + nCallsN c (srcC true))) ∧
    Fintype.card (NW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) =
      22 * q.kx + 12 * q.params.m + 24 * q.params.r + 4 * q.params.k + 4 * q.params.l +
        8 * q.b + 2 * (q.ar.bT + q.ar.bP + q.ar.A) + 2 * Fintype.card Zs + 47 ∧
    (∀ j, ∀ i ∈ trialN (bprepC q srcC) j, i.Valid) ∧
    ∀ x : X,
      (∀ i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ q.etaH ^ 2) →
      (∀ j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ q.etaH ^ 2) →
      (∀ i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ q.etaD ^ 2) →
      (∀ j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ q.etaD ^ 2) →
      (∀ w : EuclideanSpace ℂ n, 0 ≤ (inner ℂ w (SparseStateOverlap.matrixOperator
        (ODEMatrixEnergy.dissipativePart (D.matrix x)) w)).re) →
      ∀ (Jsrc : Bool → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ) (x0 v : Reg (Fin q.kx) ℂ)
        (ζs : ℝ),
      (∀ c, IsUnitary (Jsrc c)) →
      0 ≤ ζs →
      (∀ c, ApproxOn CleanX (nrun (prims (R := ℂ) D en x) (srcC c))
        (liftB (srcIdeal c (Jsrc c))) ζs) →
      98304 * qOf q.s q.T q.etaH q.etaD q.g q.ε * q.ζ + 2 * ζs ≤ q.params.nu →
      ‖x0‖ = q.r₀ → ‖v‖ = q.rb →
      (x0 ≠ 0 → Jsrc false (seedV (S := Fin q.kx)) = unitDirection x0) →
      (v ≠ 0 → Jsrc true (seedV (S := Fin q.kx)) = unitDirection v) →
      ODEConstantForcing.solution (-mLift D en x) x0 v q.T ≠ 0 →
      q.r₀ + q.T * q.rb ≤ q.g * ‖ODEConstantForcing.solution (-mLift D en x) x0 v q.T‖ →
      NOutcome (bprepC q srcC) q.g q.ε hq.g_ge (prims (R := ℂ) D en x)
        (ODEConstantForcing.solution (-mLift D en x) x0 v q.T) := by
  have hV := (ZeroTimeGateODE.binary_ode_solver_nonneg q hq D en hrange hdec srcC hsrcV).1
  by_cases hz : BZeroCase q
  · rw [if_pos hz] at hγ
    obtain ⟨hWg, hWc, hw, hWg', hWc', hcnt, hWC, hcard, -, -, -, hout⟩ :=
      binary_ode_budget_bits_zero_released bd q hq hz hγ hζ hb hc0 hH hD D en srcC hsrcV
        (2 ^ q.params.m) (2 ^ q.params.k)
    refine ⟨hWg, hWc, hw, hWg', hWc', hcnt, fun c => ?_, hcard, hV, ?_⟩
    · rw [if_pos hz, zero_add]
      exact hWC c
    · intro x hrH _ hrD _ _ Jsrc x0 v ζs hJ hζs hsrc hbud hx0 hv hpx hpv hne hB
      have hε1 : q.ε ≤ 1 := hq.ε_half.trans (by norm_num)
      have hQ1 : 1 ≤ qOf q.s q.T q.etaH q.etaD q.g q.ε :=
        one_le_qOf hq.T_nonneg hq.etaH_nonneg hq.etaD_nonneg hq.g_ge hq.ε_pos hε1
      have h0 : 0 ≤ 98304 * qOf q.s q.T q.etaH q.etaD q.g q.ε * q.ζ :=
        mul_nonneg (mul_nonneg (by norm_num) (by linarith)) hq.ζ_pos.le
      exact hout x hrH hrD Jsrc x0 v ζs hJ hζs hsrc (by linarith) hx0 hv hpx hpv hne hB
  · rw [if_neg hz] at hγ
    have hP := ZeroTimeGateODE.bpublicOK_of hq hz
    obtain ⟨hWg, hWc, hw, hWg', hWc', hcnt, hWC, hcard, hout⟩ :=
      GateBitBudget.binary_ode_budget_bits bd q hP hγ hζ hb hc0 hT hH hD D en hrange hdec srcC
        hsrcV
    have hp : bprepC q srcC = q.prep srcC := by
      rw [bprepC, if_neg hz]
    refine ⟨?_, hWc, hw, ?_, hWc', ?_, fun c => ?_, hcard, hV, ?_⟩
    · rw [hp]
      exact hWg
    · rw [hp]
      exact hWg'
    · rw [hp]
      exact hcnt
    · rw [hp, if_neg hz]
      exact hWC c
    · rw [hp]
      exact hout

end

end SparseHamiltonian.GateRemarks.ODE
