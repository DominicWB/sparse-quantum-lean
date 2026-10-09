import GateEfficientRemarks.ODE.ZeroWords

/-!
# Zero time or a known zero generator: the word budget of the released binary register

The decoder scale and the sum of the register words (the word budget `ode:eq:gate-word-budget` of
Theorem `ode:thm:gates`) of the solver from binary data in the zero case
(`ZeroTimeGateODE.BZeroCase`), with the rescaling `γ ∈ (0, 1]` a public parameter of bit length
`b_data`:

* `zero_kap_words`: `⌈log₂ ⌈κ⌉⌉ ≤ 1 + k_x + 2 b_data` and
  `⌈log₂ ⌈1/κ⌉⌉ ≤ k + F + 27 + 3 b_data + log₂ X` (`κ = 0` for zero energy bounds);
* `zero_words_le`: `𝔴 + ℓ ≤ 300 (𝔟₀ + 1)`, `𝔴 = GateODEBudget.words q`,
  `𝔟₀ = bitB b_data (2^k_x) 0 0 q* g ε`: the bound of the released key lemma
  `GateBitBudget.words_le` with the same constant;
* `card_NW_eq`, `card_NW_le`: the released register has exactly
  `22 k_x + 12 m + 24 r + 4 k + 4 l + 8 b + 2 (bT + bP + A) + 2 |Zs| + 47` and at most
  `10⁴ (𝔴+1)³ + 2 |Zs|` qubits, for all public data (the register identity of
  `GateODEBudget.binary_ode_budget` and the qubit bound of `GateODEBudget.binary_ode_budget_words`,
  whose proofs use only the register count and `GateODEBudget.binary_arith_words`).
-/

set_option autoImplicit false

namespace SparseHamiltonian.GateRemarks.ODE

noncomputable section
open GateCircuit GateNative
open SparseHamiltonian.GateBinary SparseHamiltonian.GateBinaryODE
open SparseHamiltonian.GateBitBudget (bitB HasBits)
open GateODEBudget (qOf words)
open ImprovedODEQueryBudget (precision logBudget radius)
open ZeroTimeGateODE (BPublicOK0 BZeroCase)

/-- **The bits of the decoder scale for a rescaling of bit length `b_data`** (`kap_words_of`):
for binary public data with `BPublicOK0 q`, `γ`, `c₀`, `η_H`, `η_D` of bit length `b_data` and
`Q ≥ 1`:
`⌈log₂ ⌈κ⌉⌉ ≤ 1 + k_x + 2 b_data` and `⌈log₂ ⌈1/κ⌉⌉ ≤ k + F + 27 + 3 b_data + log₂ X`,
`X = (Q g + 1)/ε`. -/
theorem zero_kap_words (bd : ℕ) (q : Pub) (hq : BPublicOK0 q) (hγb : HasBits bd q.γ)
    (hc0 : HasBits bd q.c0) (hH : HasBits bd q.etaH) (hD : HasBits bd q.etaD) {Q : ℝ}
    (hQ : 1 ≤ Q) :
    (Nat.clog 2 ⌈q.kap⌉₊ : ℝ) ≤ 1 + q.kx + 2 * bd ∧
    (Nat.clog 2 ⌈1 / q.kap⌉₊ : ℝ) ≤
      q.params.k + q.F + 27 + 3 * bd + Real.logb 2 ((Q * q.g + 1) / q.ε) := by
  have hε1 : q.ε ≤ 1 := hq.ε_half.trans (by norm_num)
  obtain ⟨h1, h2⟩ := kap_words_of bd q.kx (q.params.k + q.F + 10) q.s (γ := q.γ) (c0 := q.c0)
    (ηH := q.etaH) (ηD := q.etaD) (R := radius q.g q.ε) (κ := q.kap) rfl hq.γ_pos hq.γ_le hγb
    Nat.one_le_two_pow (Nat.pow_le_pow_right (by norm_num) q.hσ) hc0 hq.c0_pos hH hD
    hq.etaH_nonneg hq.etaD_nonneg (GateBitBudget.one_le_radius hq.g_ge hq.ε_pos hε1)
    (env_radius_le hQ hq.g_ge hq.ε_pos) (env_one_le hQ hq.g_ge hq.ε_pos hε1)
  push_cast at h2
  exact ⟨h1, by linarith⟩

/-- **The register words in the zero case** (key lemma of `ode:eq:gate-main`, `ode:eq:gate-space`
in the word budget `ode:eq:gate-word-budget`, for the budgets in `𝔟` on the released register): for
binary public data with `BPublicOK0 q` in the zero case, an arithmetic accuracy
`ζ ≥ ν/(196608 q*)`, stored bits `b ≤ b_data` and `γ`, `c₀`, `η_H`, `η_D` of bit length
`b_data`, the words `𝔴 = GateODEBudget.words q` satisfy
`𝔴 + ℓ ≤ 300 (b_data + log₂(N+1) + log₂((q* g + 1)/ε) + 1)`, `N = 2^k_x`: the bound of
`GateBitBudget.words_le`. -/
theorem zero_words_le (bd : ℕ) (q : Pub) (hq : BPublicOK0 q) (hz : BZeroCase q)
    (hγb : HasBits bd q.γ)
    (hζ : q.params.nu ≤ 196608 * qOf q.s q.T q.etaH q.etaD q.g q.ε * q.ζ) (hb : q.b ≤ bd)
    (hc0 : HasBits bd q.c0) (hH : HasBits bd q.etaH) (hD : HasBits bd q.etaD) :
    (words q : ℝ) + logBudget q.g q.ε ≤
      300 * (bitB bd (2 ^ q.kx) 0 0 (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε + 1) := by
  have hε1 : q.ε ≤ 1 := hq.ε_half.trans (by norm_num)
  have hQ1 : 1 ≤ qOf q.s q.T q.etaH q.etaD q.g q.ε :=
    one_le_qOf hq.T_nonneg hq.etaH_nonneg hq.etaD_nonneg hq.g_ge hq.ε_pos hε1
  have hQz : qOf q.s q.T q.etaH q.etaD q.g q.ε = logBudget q.g q.ε :=
    qOf_zero hq.etaH_nonneg hq.etaD_nonneg hz
  have hX := env_one_le hQ1 hq.g_ge hq.ε_pos hε1
  have hQX := env_q_le hQ1 hq.g_ge hq.ε_pos hε1
  have hνX := env_inv_precision_le hQ1 hq.g_ge hq.ε_pos
  have hℓX := env_ell_le hQ1 hq.g_ge hq.ε_pos
  have hℓL := env_ell_le_logb hQ1 hq.g_ge hq.ε_pos hε1
  have hν : 0 < q.params.nu := ImprovedODEQueryBudget.precision_pos q.g q.ε hq.g_ge hq.ε_pos
  have hℓ1 := ImprovedODEQueryBudget.logBudget_ge_one q.g q.ε hq.g_ge hq.ε_pos hε1
  have hJ := zero_J_le q hq hz (le_of_eq hQz.symm)
  have wkx := GateBitBudget.nat_le_logb q.kx
  have wb : (q.b : ℝ) ≤ bd := by exact_mod_cast hb
  have wm : (q.params.m : ℝ) = 0 := by rw [zero_m q hq hz]; simp
  have wk : (q.params.k : ℝ) = 0 := by rw [zero_k q hq hz]; simp
  have wr := zero_r_word q hq hz hQ1
  have hl : ((2 ^ q.params.l : ℕ) : ℝ) <
      2 * (60 * qOf q.s q.T q.etaH q.etaD q.g q.ε * logBudget q.g q.ε + 2) := by
    have h := q.params.l_bounds.2
    have h' : ((2 ^ q.params.l : ℕ) : ℝ) < 2 * ((q.params.J : ℝ) + 2) := by exact_mod_cast h
    linarith
  have wl := GateBitBudget.l_word q.params.l hQ1 hQX (by linarith) hℓX hl
  have wF : (q.F : ℝ) ≤ 54 + 4 * Real.logb 2
      ((qOf q.s q.T q.etaH q.etaD q.g q.ε * q.g + 1) / q.ε) :=
    GateBitBudget.F_word q.params hq.g_ge hq.ε_pos hε1 (le_of_eq (zero_TlamD q hq hz).symm)
      hq.ζ_pos hQ1 hQX hJ hℓX hνX hζ
  have wn := GateBitBudget.nOf_word hq.ζ_pos hν hQ1 hQX hνX hζ
  obtain ⟨wκ, wκi⟩ := zero_kap_words bd q hq hγb hc0 hH hD hQ1
  have hw : (words q : ℝ) = q.kx + q.b + q.params.m + q.params.r + q.params.k + q.params.l +
      q.F + (Cordic.nOf (q.ζ / 2) : ℝ) + (Nat.clog 2 ⌈q.kap⌉₊ : ℝ) +
      (Nat.clog 2 ⌈1 / q.kap⌉₊ : ℝ) := by
    unfold words
    push_cast
    ring
  have hb0 : bitB bd (2 ^ q.kx) 0 0 (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε =
      bd + Real.logb 2 (((2 ^ q.kx : ℕ) : ℝ) + 1) +
        Real.logb 2 ((qOf q.s q.T q.etaH q.etaD q.g q.ε * q.g + 1) / q.ε) := by
    unfold bitB
    simp only [Nat.cast_zero, zero_add, Real.logb_one, add_zero]
  rw [hw, hb0]
  have hL0 := Real.logb_nonneg one_lt_two hX
  have hbd0 : (0 : ℝ) ≤ bd := Nat.cast_nonneg _
  linarith

/-- **The qubits of the released binary register** (equation `ode:eq:gate-space`, for all public
data): the register identity
`|NW| = 22 k_x + 12 m + 24 r + 4 k + 4 l + 8 b + 2 (bT + bP + A) + 2 |Zs| + 47` of
`GateODEBudget.binary_ode_budget`, without `Pub.OK`. -/
theorem card_NW_eq (q : Pub) {Zs : Type*} [Fintype Zs] :
    Fintype.card (NW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) =
      22 * q.kx + 12 * q.params.m + 24 * q.params.r + 4 * q.params.k + 4 * q.params.l +
        8 * q.b + 2 * (q.ar.bT + q.ar.bP + q.ar.A) + 2 * Fintype.card Zs + 47 := by
  have h1 := ZeroTimeGateODE.card_ZNW (S := Fin q.kx) (Zs := Zs) (Z := SZ4 q.kx q.b) q.params.a
    q.params.m q.params.r q.params.K q.params.k q.params.l q.params.f q.ar.bT q.ar.bP q.ar.A
  have h2 : Fintype.card (GateODE.AW q.params.a q.params.m q.params.r q.params.K q.params.k
      q.params.l q.params.f) =
      4 * (q.kx + 3) + 6 * q.params.m + 12 * q.params.r + 2 * q.params.k + 2 * q.params.l + 8 :=
    q.params.card_W
  rw [h2, card_SZ4, Fintype.card_fin] at h1
  have h1' := (h1 : Fintype.card
    (NW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) = _)
  rw [h1']
  omega

/-- **The qubits of the released binary register in the words** (for all public data):
`|NW| ≤ 10⁴ (𝔴+1)³ + 2 |Zs|`, `𝔴 = GateODEBudget.words q`. -/
theorem card_NW_le (q : Pub) {Zs : Type*} [Fintype Zs] :
    Fintype.card (NW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) ≤
      10000 * (words q + 1) ^ 3 + 2 * Fintype.card Zs := by
  rw [card_NW_eq]
  obtain ⟨-, hA, hT, hP⟩ := GateODEBudget.binary_arith_words q
  have h24 : 22 * q.kx + 12 * q.params.m + 24 * q.params.r + 4 * q.params.k + 4 * q.params.l +
      8 * q.b ≤ 24 * words q := by
    unfold words
    omega
  have hp1 : words q + 1 ≤ (words q + 1) ^ 3 := le_self_pow₀ (by omega) (by norm_num)
  omega

end

end SparseHamiltonian.GateRemarks.ODE
