import GateEfficientRemarks.ODE.ZeroWords
import GateEfficientBitBudget.Time
import ZeroTimeGateODE.BinaryTime

/-!
# Zero time or a known zero generator: the words of the released time-dependent binary register

The time-dependent counterpart of `ZeroWords`/`ZeroWordsSum` (the word budget
`ode:eq:gate-word-budget` of Theorem `ode:thm:gates`, time-dependent part): the register words
`𝔴 = GateODEBudget.wordsT q = k_x + b + m + r + l + F + n_c + ⌈log₂ ⌈κ⌉⌉ + ⌈log₂ ⌈1/κ⌉⌉` of the
solver from time-indexed binary data (`m` the mesh exponent) in the zero case
(`ZeroTimeGateODE.BTZeroCase`: `T = 0 ∨ η_H + η_D = 0`, with `ZeroTimeGateODE.BTPublicOK0`), with
the rescaling `γ ∈ (0, 1]` a public parameter of bit length `b_data`:

* the common simulation time and the dissipative time vanish (`zeroT_tau`, `zeroT_TlamD`), so
  the filter degree is `d ≤ 128 Q_w (1 + log(3/ν))` (`zeroT_degree`), the reuse word is
  `r ≤ 24 + k_x + log₂ X'` (`zeroT_r_word`) and the LCHS grid has `J ≤ 60 Q ℓ'` (`zeroT_J_le`),
  for the internal ratio `2g` and accuracy `ε/2` of the released time-dependent solver
  (`X' = (Q · 2g + 1)/(ε/2)`, `ℓ' = log(10⁴ · 2g/(ε/2))`);
* `zeroT_kap_words`: the decoder words `⌈log₂ ⌈κ⌉⌉ ≤ 1 + k_x + 2 b_data` and
  `⌈log₂ ⌈1/κ⌉⌉ ≤ F + 27 + 3 b_data + log₂ X'`;
* `zero_wordsT_le`: `𝔴 + ℓ' ≤ 300 (𝔟' + 1)`, `𝔟' = bitB b_data (2^k_x) (2^m) (2^m) q*' g ε` with the
  internal query shape `q*' = qOf s T η_H η_D (2g) (ε/2)` (`= ℓ'`): the bound of the released key
  lemma `GateBitBudget.wordsT_le` with the same constant;
* `card_TNW_eq`, `card_TNW_le`: the released register has exactly
  `22 k_x + 16 m + 24 r + 4 l + 8 b + 2 (bT + bP + A) + 2 |Zs| + 47` and at most
  `10⁴ (𝔴+1)³ + 2 |Zs|` qubits, for all public data (the register identity of
  `GateODEBudget.binary_ode_time_budget` and the qubit bound of
  `GateODEBudget.binary_ode_time_budget_words`);
* `logBudget_two_le`, `bitB_le_succ`: `ℓ' ≤ 2 ℓ` and the `bitB` of a query shape at most twice
  another is at most one more, for the forms with the query shape `q* = ℓ` of `(g, ε)`.
-/

set_option autoImplicit false

namespace SparseHamiltonian.GateRemarks.ODE

noncomputable section
open GateCircuit GateNative
open SparseHamiltonian.GateBinary SparseHamiltonian.GateBinaryODE
open GateBinaryODETime (PubT)
open SparseHamiltonian.GateBitBudget (bitB HasBits)
open GateODEBudget (qOf wordsT)
open ImprovedODEQueryBudget (precision logBudget radius)
open ZeroTimeGateODE (BTPublicOK0 BTZeroCase)
open CayleyClockInterface (width)

/-! ### The internal and the user accuracy -/

/-- `ℓ' = log(10⁴ · 2g/(ε/2)) ≤ 2 ℓ`, `ℓ = log(10⁴ g/ε)`, for `g ≥ 1` and `0 < ε ≤ 1` (from the
released `GateBitBudget.logBudget_two`: `ℓ' = ℓ + log 4`). -/
theorem logBudget_two_le {g ε : ℝ} (hg : 1 ≤ g) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    logBudget (2 * g) (ε / 2) ≤ 2 * logBudget g ε := by
  have hg0 : 0 < g := by linarith
  rw [GateBitBudget.logBudget_two g ε hg0 hε]
  have h4 : Real.log 4 ≤ logBudget g ε := by
    unfold ImprovedODEQueryBudget.logBudget
    apply Real.log_le_log (by norm_num)
    rw [le_div_iff₀ hε]
    nlinarith
  linarith

/-- The `bitB` of a query shape `Q' ≤ 2 Q` is at most one more than that of `Q` (for all
`Q, Q' ≥ 0`; the released `GateBitBudget.bitB_two_le` compares the query shapes of `(2g, ε/2)`
and `(g, ε)` under the positive-case conditions `ShapeOK`). -/
theorem bitB_le_succ (bd N M m : ℕ) {Q Q' g ε : ℝ} (hQ : 0 ≤ Q) (hQ' : 0 ≤ Q')
    (hQQ : Q' ≤ 2 * Q) (hg : 0 ≤ g) (hε : 0 < ε) :
    bitB bd N M m Q' g ε ≤ bitB bd N M m Q g ε + 1 := by
  have hQg : 0 ≤ Q * g := mul_nonneg hQ hg
  have hQg' : 0 ≤ Q' * g := mul_nonneg hQ' hg
  have hx : 0 < (Q * g + 1) / ε := by positivity
  have h1 : (Q' * g + 1) / ε ≤ 2 * ((Q * g + 1) / ε) := by
    rw [← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ hε.le
    have := mul_le_mul_of_nonneg_right hQQ hg
    nlinarith
  have h2 : Real.logb 2 ((Q' * g + 1) / ε) ≤ Real.logb 2 (2 * ((Q * g + 1) / ε)) :=
    Real.logb_le_logb_of_le one_lt_two (by positivity) h1
  rw [Real.logb_mul (by norm_num) hx.ne', Real.logb_self_eq_one one_lt_two] at h2
  unfold bitB
  linarith

/-! ### The zero case of the time-dependent public data -/

section Zero

variable (q : PubT)

/-- In the zero case `T λ_D = 0`. -/
theorem zeroT_TlamD (hq : BTPublicOK0 q) (hz : BTZeroCase q) :
    q.params.T * q.params.lamD = 0 := by
  rcases hz with h | h
  · show q.T * _ = 0
    rw [h, zero_mul]
  · have hD : q.etaD = 0 := by linarith [hq.etaH_nonneg, hq.etaD_nonneg]
    show q.T * (Real.sqrt (4 * (q.s : ℝ)) * q.etaD / q.γ) = 0
    rw [hD, mul_zero, zero_div, mul_zero]

/-- In the zero case the common simulation time `τ = T (λ_H + R λ_D)` vanishes. -/
theorem zeroT_tau (hq : BTPublicOK0 q) (hz : BTZeroCase q) : q.params.tau = 0 := by
  have h := ZeroTimeGateODE.btzeroCase_params hq hz
  show q.params.T * (q.params.lamH + q.params.R * q.params.lamD) = 0
  rcases h with h | h
  · rw [h, zero_mul]
  · rw [h, mul_zero]

/-- **The filter degree in the zero case**: `d ≤ 128 Q_w (1 + log(3/ν))`, `Q_w = width(4s, γ)`,
`ν = precision (2g) (ε/2)`. -/
theorem zeroT_degree (hq : BTPublicOK0 q) (hz : BTZeroCase q) :
    (q.params.d : ℝ) ≤ 128 * (q.params.Q * (1 + Real.log (3 / q.params.nu))) := by
  have hg2 : (1 : ℝ) ≤ 2 * q.g := by linarith [hq.g_ge]
  have hν : 0 < q.params.nu :=
    ImprovedODEQueryBudget.precision_pos (2 * q.g) (q.ε / 2) hg2 (by linarith [hq.ε_pos])
  have hν1 : q.params.nu ≤ 1 / 10000 :=
    ImprovedODEQueryBudget.precision_le_one_ten_thousandth (2 * q.g) (q.ε / 2) hg2
      (by linarith [hq.ε_half])
  have hτ := zeroT_tau q hq hz
  have h := SharpFilterSchedule.degree_le q.params.Q (q.params.tau * q.params.qbar)
    (q.params.nu / 3) (CayleyClockInterface.width_ge_one _ _) (by rw [hτ, zero_mul])
    (by positivity) (by linarith)
  have e1 : (q.params.d : ℝ) =
      (SharpFilterSchedule.degree q.params.Q (q.params.tau * q.params.qbar) (q.params.nu / 3) :
        ℝ) := rfl
  have e2 : Real.log (3 / q.params.nu) = SharpFilterSchedule.logBudget (q.params.nu / 3) := by
    unfold SharpFilterSchedule.logBudget
    rw [one_div_div]
  rw [e1, e2]
  refine h.trans (le_of_eq ?_)
  rw [hτ, zero_mul, zero_add]

/-- **The clock width**: `Q_w = width(4s, γ) ≤ 3 · 2^k_x` (`width_le_of`). -/
theorem widthT_le (hq : BTPublicOK0 q) : q.params.Q ≤ 3 * 2 ^ q.kx := by
  show width (4 * (q.s : ℝ)) q.γ ≤ 3 * 2 ^ q.kx
  exact width_le_of hq.γ_le Nat.one_le_two_pow (Nat.pow_le_pow_right (by norm_num) q.hσ)

/-- **The reuse word in the zero case**: `r ≤ 24 + k_x + log₂ X'`, `X' = (Q · 2g + 1)/(ε/2)`,
`Q ≥ 1`. -/
theorem zeroT_r_word (hq : BTPublicOK0 q) (hz : BTZeroCase q) {Q : ℝ} (hQ : 1 ≤ Q) :
    (q.params.r : ℝ) ≤ 24 + q.kx + Real.logb 2 ((Q * (2 * q.g) + 1) / (q.ε / 2)) :=
  r_word_of (g := 2 * q.g) (ε := q.ε / 2) (by linarith [hq.g_ge]) (by linarith [hq.ε_pos])
    (by linarith [hq.ε_half]) hQ (zeroT_degree q hq hz) (widthT_le q hq) q.params.r_bounds.2

/-- **The LCHS grid in the zero case**: `J ≤ 60 Q ℓ'` for every `Q ≥ ℓ' = log(10⁴ · 2g/(ε/2))`
(in particular for `q*' = ℓ'`). -/
theorem zeroT_J_le (hq : BTPublicOK0 q) (hz : BTZeroCase q) {Q : ℝ}
    (hQ : logBudget (2 * q.g) (q.ε / 2) ≤ Q) :
    (q.params.J : ℝ) ≤ 60 * Q * logBudget (2 * q.g) (q.ε / 2) := by
  have hg2 : (1 : ℝ) ≤ 2 * q.g := by linarith [hq.g_ge]
  have hε2 : (0 : ℝ) < q.ε / 2 := by linarith [hq.ε_pos]
  have hε2' : q.ε / 2 ≤ 1 := by linarith [hq.ε_half]
  have hJ := GateODE.AnalyticLCHS.gridSize_le (le_of_eq (zeroT_TlamD q hq hz).symm) hg2 hε2
    hε2'
  change (q.params.J : ℝ) ≤ radius (2 * q.g) (q.ε / 2) *
    (q.params.T * q.params.lamD + 2 * Real.log (512 / precision (2 * q.g) (q.ε / 2))) /
      Real.pi + 3 at hJ
  rw [zeroT_TlamD q hq hz, zero_add] at hJ
  exact J_le_of hg2 hε2 hε2' hJ hQ

end Zero

/-! ### The word budget -/

/-- **The bits of the decoder scale for a rescaling of bit length `b_data`** (`kap_words_of`):
for time-indexed binary public data with `BTPublicOK0 q`, `γ`, `c₀`, `η_H`, `η_D` of bit length
`b_data` and `Q ≥ 1`: `⌈log₂ ⌈κ⌉⌉ ≤ 1 + k_x + 2 b_data` and
`⌈log₂ ⌈1/κ⌉⌉ ≤ F + 27 + 3 b_data + log₂ X'`, `X' = (Q · 2g + 1)/(ε/2)`. -/
theorem zeroT_kap_words (bd : ℕ) (q : PubT) (hq : BTPublicOK0 q) (hγb : HasBits bd q.γ)
    (hc0 : HasBits bd q.c0) (hH : HasBits bd q.etaH) (hD : HasBits bd q.etaD) {Q : ℝ}
    (hQ : 1 ≤ Q) :
    (Nat.clog 2 ⌈q.kap⌉₊ : ℝ) ≤ 1 + q.kx + 2 * bd ∧
    (Nat.clog 2 ⌈1 / q.kap⌉₊ : ℝ) ≤
      q.F + 27 + 3 * bd + Real.logb 2 ((Q * (2 * q.g) + 1) / (q.ε / 2)) := by
  have hg2 : (1 : ℝ) ≤ 2 * q.g := by linarith [hq.g_ge]
  have hε2 : (0 : ℝ) < q.ε / 2 := by linarith [hq.ε_pos]
  have hε2' : q.ε / 2 ≤ 1 := by linarith [hq.ε_half]
  obtain ⟨h1, h2⟩ := kap_words_of bd q.kx (q.F + 10) q.s (γ := q.γ) (c0 := q.c0)
    (ηH := q.etaH) (ηD := q.etaD) (R := radius (2 * q.g) (q.ε / 2)) (κ := q.kap) rfl hq.γ_pos
    hq.γ_le hγb Nat.one_le_two_pow (Nat.pow_le_pow_right (by norm_num) q.hσ) hc0 hq.c0_pos hH
    hD hq.etaH_nonneg hq.etaD_nonneg (GateBitBudget.one_le_radius hg2 hε2 hε2')
    (env_radius_le hQ hg2 hε2) (env_one_le hQ hg2 hε2 hε2')
  push_cast at h2
  exact ⟨h1, by linarith⟩

/-- **The register words in the zero case, time-dependent coefficients** (key lemma of
`ode:eq:gate-main`, `ode:eq:gate-space` in the word budget `ode:eq:gate-word-budget`, for the
budgets in `𝔟` on the released register): for time-indexed binary public data with
`BTPublicOK0 q` in the zero case, an arithmetic accuracy `ζ ≥ ν/(196608 q*')`, stored bits
`b ≤ b_data` and `γ`, `c₀`, `η_H`, `η_D` of bit length `b_data`, the words
`𝔴 = GateODEBudget.wordsT q` satisfy `𝔴 + ℓ' ≤ 300 (𝔟' + 1)`,
`𝔟' = bitB b_data (2^k_x) (2^m) (2^m) q*' g ε`, `q*' = qOf s T η_H η_D (2g) (ε/2)`: the bound of
`GateBitBudget.wordsT_le`. -/
theorem zero_wordsT_le (bd : ℕ) (q : PubT) (hq : BTPublicOK0 q) (hz : BTZeroCase q)
    (hγb : HasBits bd q.γ)
    (hζ : q.params.nu ≤ 196608 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * q.ζ)
    (hb : q.b ≤ bd) (hc0 : HasBits bd q.c0) (hH : HasBits bd q.etaH)
    (hD : HasBits bd q.etaD) :
    (wordsT q : ℝ) + logBudget (2 * q.g) (q.ε / 2) ≤
      300 * (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
        (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) := by
  have hε1 : q.ε ≤ 1 := hq.ε_half.trans (by norm_num)
  have hg2 : (1 : ℝ) ≤ 2 * q.g := by linarith [hq.g_ge]
  have hε2 : (0 : ℝ) < q.ε / 2 := by linarith [hq.ε_pos]
  have hε2' : q.ε / 2 ≤ 1 := by linarith [hq.ε_half]
  have hQ1 : 1 ≤ qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) :=
    one_le_qOf hq.T_nonneg hq.etaH_nonneg hq.etaD_nonneg hg2 hε2 hε2'
  have hQz : qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) = logBudget (2 * q.g) (q.ε / 2) :=
    qOf_zero hq.etaH_nonneg hq.etaD_nonneg hz
  have hX := env_one_le hQ1 hg2 hε2 hε2'
  have hQX := env_q_le hQ1 hg2 hε2 hε2'
  have hνX : 1 / q.params.nu ≤ 10000 *
      ((qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * (2 * q.g) + 1) / (q.ε / 2)) :=
    env_inv_precision_le hQ1 hg2 hε2
  have hℓX := env_ell_le hQ1 hg2 hε2
  have hℓL := env_ell_le_logb hQ1 hg2 hε2 hε2'
  have hν : 0 < q.params.nu := ImprovedODEQueryBudget.precision_pos (2 * q.g) (q.ε / 2) hg2 hε2
  have hℓ1 := ImprovedODEQueryBudget.logBudget_ge_one (2 * q.g) (q.ε / 2) hg2 hε2 hε2'
  have hJ := zeroT_J_le q hq hz (le_of_eq hQz.symm)
  have wkx := GateBitBudget.nat_le_logb q.kx
  have wb : (q.b : ℝ) ≤ bd := by exact_mod_cast hb
  have wm := GateBitBudget.nat_le_logb q.m
  have wr := zeroT_r_word q hq hz hQ1
  have hl : ((2 ^ q.params.l : ℕ) : ℝ) <
      2 * (60 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
        logBudget (2 * q.g) (q.ε / 2) + 2) := by
    have h := q.params.l_bounds.2
    have h' : ((2 ^ q.params.l : ℕ) : ℝ) < 2 * ((q.params.J : ℝ) + 2) := by exact_mod_cast h
    linarith
  have wl := GateBitBudget.l_word q.params.l hQ1 hQX (by linarith) hℓX hl
  have wF : (q.F : ℝ) ≤ 54 + 4 * Real.logb 2
      ((qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * (2 * q.g) + 1) / (q.ε / 2)) :=
    GateBitBudget.F_word (GateBinaryODETime.gridP q.params) hg2 hε2 hε2'
      (le_of_eq (zeroT_TlamD q hq hz).symm) hq.ζ_pos hQ1 hQX hJ hℓX hνX hζ
  have wn := GateBitBudget.nOf_word hq.ζ_pos hν hQ1 hQX hνX hζ
  obtain ⟨wκ, wκi⟩ := zeroT_kap_words bd q hq hγb hc0 hH hD hQ1
  have hLL := GateBitBudget.logb_X_two_le (Q := qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2))
    (g := q.g) (by linarith) (by linarith [hq.g_ge]) hq.ε_pos hε1
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
  have hN0 := GateBitBudget.logb_succ_nonneg (2 ^ q.kx)
  have hM0 := GateBitBudget.logb_succ_nonneg (2 ^ q.m)
  have hbd0 : (0 : ℝ) ≤ bd := Nat.cast_nonneg _
  have hL'0 : 0 ≤ Real.logb 2
      ((qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * q.g + 1) / q.ε) := by
    apply Real.logb_nonneg one_lt_two
    rw [le_div_iff₀ hq.ε_pos]
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2))
      (by linarith [hq.g_ge] : (0 : ℝ) ≤ q.g)
    linarith
  linarith

/-- **The qubits of the released time-dependent binary register** (equation `ode:eq:gate-space`, for
all public data): the register identity
`|TNW| = 22 k_x + 16 m + 24 r + 4 l + 8 b + 2 (bT + bP + A) + 2 |Zs| + 47` of
`GateODEBudget.binary_ode_time_budget`, without `PubT.OK`. -/
theorem card_TNW_eq (q : PubT) {Zs : Type*} [Fintype Zs] :
    Fintype.card (TNW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) =
      22 * q.kx + 16 * q.params.m + 24 * q.params.r + 4 * q.params.l + 8 * q.b +
        2 * (q.ar.bT + q.ar.bP + q.ar.A) + 2 * Fintype.card Zs + 47 := by
  have h1 := ZeroTimeGateODE.card_ZNW (S := Fin q.kx) (Zs := Zs) (Z := SZ4 q.kx q.b) q.params.a
    q.params.m q.params.r q.params.K q.params.m q.params.l q.params.f q.ar.bT q.ar.bP q.ar.A
  have h2 : Fintype.card (GateODE.AW q.params.a q.params.m q.params.r q.params.K q.params.m
      q.params.l q.params.f) =
      4 * (q.kx + 3) + 8 * q.params.m + 12 * q.params.r + 2 * q.params.l + 8 :=
    q.params.card_W
  rw [h2, card_SZ4, Fintype.card_fin] at h1
  have h1' := (h1 : Fintype.card
    (TNW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) = _)
  rw [h1']
  omega

/-- **The qubits of the released time-dependent binary register in the words** (for all public
data): `|TNW| ≤ 10⁴ (𝔴+1)³ + 2 |Zs|`, `𝔴 = GateODEBudget.wordsT q`. -/
theorem card_TNW_le (q : PubT) {Zs : Type*} [Fintype Zs] :
    Fintype.card (TNW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) ≤
      10000 * (wordsT q + 1) ^ 3 + 2 * Fintype.card Zs := by
  rw [card_TNW_eq]
  obtain ⟨-, hA, hT, hP⟩ := GateODEBudget.binary_time_arith_words q
  have h24 : 22 * q.kx + 16 * q.params.m + 24 * q.params.r + 4 * q.params.l + 8 * q.b ≤
      24 * wordsT q := by
    unfold wordsT
    omega
  have hp1 : wordsT q + 1 ≤ (wordsT q + 1) ^ 3 := le_self_pow₀ (by omega) (by norm_num)
  omega

end

end SparseHamiltonian.GateRemarks.ODE
