import GateEfficientBitBudget.Scale
import GateEfficientBinary.Cordic.Params

/-!
# The register words of the dissipative solvers in the word budget

For the public data of the dissipative solvers (the conditions `GateODEBudget.ShapeOK`), put
`q* = qOf s T η_H η_D g ε ≥ 1`, `ℓ = log(10000 g/ε) = log(1/ν)` and the reference quantity
`X = (q* g + 1)/ε`, whose base-2 logarithm is the last term of the word budget
`𝔟 = b_data + log₂(N+1) + log₂(M+1) + log₂(m+1) + log₂((q* g + 1)/ε)` (`bitB`, equation
`ode:eq:gate-word-budget` of Theorem `ode:thm:gates`). Then
`1 ≤ X`, `q* ≤ X`, `g/ε ≤ X`, `1/ν ≤ 10000 X`, `ℓ ≤ 10000 X` and `ℓ ≤ 14 + log₂ X`
(`shape_one_le_X`, `shape_q_le_X`, `shape_div_le_X`, `shape_inv_precision_le`,
`shape_ell_le_X`, `shape_ell_le_logb`), and the register words of the constructions are linear
in `log₂ X`, the bit lengths and the system qubits:

* from the released size bounds: `r_word` (`2^r ≤ 4 (4096 q* + 1)`: `r ≤ 15 + log₂ X`),
  `l_word` (`2^l < 2 (60 q* ℓ + 2)`: `l ≤ 21 + 2 log₂ X`), `m_word`
  (`2^m < 2 (2 + 64 q* + √(12288 q*³/ν))`: `m ≤ 15 + 2 log₂ X`) and `k_word`
  (`2^k < 2 (2 q*/ν + 2)`: `k ≤ 16 + 2 log₂ X`);
* for an arithmetic accuracy `ζ ≥ ν/(196608 q*)` (so `1/ζ ≤ 196608 q* · 10000 X`,
  `inv_zeta_le`): the fractional bits of the LCHS step `F = fOf p ζ ≤ 54 + 4 log₂ X` (`F_word`,
  for `J ≤ 60 q* ℓ`) and the CORDIC steps `nOf (ζ/2) ≤ 38 + 2 log₂ X` (`nOf_word`);
* for the decoder scale `κ = γ √(4s) c₀ / (2^e ρ)`, `ρ = η_H + R η_D`, with the public rescaling
  `γ = gammaOf T η_H η_D g ε` and `c₀`, `T`, `η_H`, `η_D` of bit length `bd`:
  `⌈log₂ ⌈κ⌉⌉ ≤ 1 + k_x + 2 bd` and `⌈log₂ ⌈1/κ⌉⌉ ≤ e + 4 bd + 31 + 2 log₂ X` (`kap_words`).

The time-dependent solver uses these with its internal ratio `2g` and accuracy `ε/2`;
`logb_X_two_le` compares its reference quantity with that of `(g, ε)`.
-/

set_option autoImplicit false

namespace SparseHamiltonian.GateBitBudget

noncomputable section
open GateODEBudget (gammaOf qOf ShapeOK gammaOf_le_one)
open ImprovedODEQueryBudget (precision logBudget radius)

/-! ### The reference quantity `X = (q* g + 1)/ε` -/

section Shape

variable {s T ηH ηD g ε : ℝ}

/-- The reference quantity is at least one: `1 ≤ X = (q* g + 1)/ε`. -/
theorem shape_one_le_X (h : ShapeOK s T ηH ηD g ε) :
    1 ≤ (qOf s T ηH ηD g ε * g + 1) / ε := by
  have hQ := h.one_le_q
  have hg := h.g_ge
  rw [le_div_iff₀ h.ε_pos]
  nlinarith [h.ε_le]

/-- The query shape is at most the reference quantity: `q* ≤ X = (q* g + 1)/ε`. -/
theorem shape_q_le_X (h : ShapeOK s T ηH ηD g ε) :
    qOf s T ηH ηD g ε ≤ (qOf s T ηH ηD g ε * g + 1) / ε := by
  have hQ := h.one_le_q
  have hg := h.g_ge
  have hε := h.ε_pos
  have hε1 := h.ε_le
  rw [le_div_iff₀ hε]
  nlinarith

/-- The ratio of the amplification bound and the accuracy is at most the reference quantity:
`g/ε ≤ X = (q* g + 1)/ε`. -/
theorem shape_div_le_X (h : ShapeOK s T ηH ηD g ε) :
    g / ε ≤ (qOf s T ηH ηD g ε * g + 1) / ε := by
  have hQ := h.one_le_q
  have hg := h.g_ge
  apply div_le_div_of_nonneg_right _ h.ε_pos.le
  nlinarith

/-- `1/ν = 10000 g/ε ≤ 10000 X`. -/
theorem shape_inv_precision_le (h : ShapeOK s T ηH ηD g ε) :
    1 / precision g ε ≤ 10000 * ((qOf s T ηH ηD g ε * g + 1) / ε) := by
  have hg0 : 0 < g := lt_of_lt_of_le one_pos h.g_ge
  have hε := h.ε_pos
  have e : 1 / precision g ε = 10000 * (g / ε) := by
    unfold ImprovedODEQueryBudget.precision
    field_simp
  rw [e]
  have := shape_div_le_X h
  linarith

/-- `ℓ = log(10000 g/ε) ≤ 10000 X`. -/
theorem shape_ell_le_X (h : ShapeOK s T ηH ηD g ε) :
    logBudget g ε ≤ 10000 * ((qOf s T ηH ηD g ε * g + 1) / ε) := by
  have hg0 : 0 < g := lt_of_lt_of_le one_pos h.g_ge
  have hε := h.ε_pos
  have h1 := Real.log_le_sub_one_of_pos (by positivity : 0 < 10000 * g / ε)
  have e : 10000 * g / ε = 10000 * (g / ε) := by ring
  have := shape_div_le_X h
  unfold ImprovedODEQueryBudget.logBudget
  rw [e] at h1 ⊢
  linarith

/-- `ℓ = log(10000 g/ε) ≤ 14 + log₂ X`. -/
theorem shape_ell_le_logb (h : ShapeOK s T ηH ηD g ε) :
    logBudget g ε ≤ 14 + Real.logb 2 ((qOf s T ηH ηD g ε * g + 1) / ε) := by
  have hg0 : 0 < g := lt_of_lt_of_le one_pos h.g_ge
  have hε := h.ε_pos
  have harg : 1 ≤ 10000 * g / ε := by
    rw [le_div_iff₀ hε]
    nlinarith [h.ε_le, h.g_ge]
  have h1 := log_le_logb _ harg
  have h2 := logb_le_mul_pow (10000 * g / ε) 10000 _ 14 1 (by positivity) (shape_one_le_X h)
    (by norm_num) (by
      have := shape_div_le_X h
      rw [pow_one, mul_div_assoc]
      linarith)
  unfold ImprovedODEQueryBudget.logBudget
  push_cast at h2
  linarith

end Shape

/-- **The reference quantity of the internal ratio and accuracy**:
`log₂((2 q g + 1)/(ε/2)) ≤ 2 + log₂((q g + 1)/ε)` for `q, g ≥ 0` and `0 < ε ≤ 1`. -/
theorem logb_X_two_le {Q g ε : ℝ} (hQ : 0 ≤ Q) (hg : 0 ≤ g) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Real.logb 2 ((Q * (2 * g) + 1) / (ε / 2)) ≤ 2 + Real.logb 2 ((Q * g + 1) / ε) := by
  have hQg : 0 ≤ Q * g := mul_nonneg hQ hg
  have hX1 : 1 ≤ (Q * g + 1) / ε := by
    rw [le_div_iff₀ hε]
    linarith
  have e1 : (Q * (2 * g) + 1) / (ε / 2) = (4 * (Q * g) + 2) / ε := by
    rw [div_div_eq_mul_div]
    ring
  have e2 : 4 * ((Q * g + 1) / ε) ^ 1 = (4 * (Q * g) + 4) / ε := by
    ring
  have h2 : (Q * (2 * g) + 1) / (ε / 2) ≤ 4 * ((Q * g + 1) / ε) ^ 1 := by
    rw [e1, e2]
    exact div_le_div_of_nonneg_right (by linarith) hε.le
  have hpos : 0 < (Q * (2 * g) + 1) / (ε / 2) := by
    rw [e1]
    exact div_pos (by linarith) hε
  have h := logb_le_mul_pow _ 4 _ 2 1 hpos hX1 (by norm_num) h2
  push_cast at h
  linarith

/-! ### The words from the released size bounds -/

/-- **The reuse word**: `2^r ≤ 4 (4096 q* + 1)` gives `r ≤ 15 + log₂ X` for `1 ≤ q* ≤ X`. -/
theorem r_word (r : ℕ) {Q X : ℝ} (hQ : 1 ≤ Q) (hQX : Q ≤ X)
    (h : ((2 ^ r : ℕ) : ℝ) ≤ 4 * (4096 * Q + 1)) : (r : ℝ) ≤ 15 + Real.logb 2 X := by
  have hX : 1 ≤ X := hQ.trans hQX
  have h1 : 4 * (4096 * Q + 1) ≤ (2 : ℝ) ^ 15 * X ^ 1 := by
    rw [pow_one]
    linarith
  have h2 := nat_le_mul_pow r (2 ^ 15) X 15 1 hX le_rfl (h.trans h1)
  push_cast at h2
  linarith

/-- **The LCHS word**: `2^l < 2 (60 q* ℓ + 2)` gives `l ≤ 21 + 2 log₂ X` for `1 ≤ q* ≤ X` and
`0 ≤ ℓ ≤ 10000 X`. -/
theorem l_word (l : ℕ) {Q ℓ X : ℝ} (hQ : 1 ≤ Q) (hQX : Q ≤ X) (hℓ : 0 ≤ ℓ)
    (hℓX : ℓ ≤ 10000 * X) (h : ((2 ^ l : ℕ) : ℝ) < 2 * (60 * Q * ℓ + 2)) :
    (l : ℝ) ≤ 21 + 2 * Real.logb 2 X := by
  have hX : 1 ≤ X := hQ.trans hQX
  have hQℓ : Q * ℓ ≤ X * (10000 * X) := mul_le_mul hQX hℓX hℓ (by linarith)
  have hX2 : 1 ≤ X ^ 2 := one_le_pow₀ hX
  have h1 : 2 * (60 * Q * ℓ + 2) ≤ (2 : ℝ) ^ 21 * X ^ 2 := by
    linarith
  have h2 := nat_le_mul_pow l (2 ^ 21) X 21 2 hX le_rfl (h.le.trans h1)
  push_cast at h2
  linarith

/-- **The time word of the released simulator**: `2^m < 2 (2 + 64 q* + √(12288 q*³/ν))` gives
`m ≤ 15 + 2 log₂ X` for `1 ≤ q* ≤ X` and `1/ν ≤ 10000 X`. -/
theorem m_word (m : ℕ) {Q ν X : ℝ} (hQ : 1 ≤ Q) (hQX : Q ≤ X) (hν : 0 < ν)
    (hνX : 1 / ν ≤ 10000 * X)
    (h : ((2 ^ m : ℕ) : ℝ) < 2 * (2 + 64 * Q + Real.sqrt (12288 * Q ^ 3 / ν))) :
    (m : ℝ) ≤ 15 + 2 * Real.logb 2 X := by
  have hX : 1 ≤ X := hQ.trans hQX
  have hX0 : 0 ≤ X := by linarith
  have hQ3 : Q ^ 3 ≤ X ^ 3 := pow_le_pow_left₀ (by linarith) hQX 3
  have hX2 : 1 ≤ X ^ 2 := one_le_pow₀ hX
  have hXX : X ≤ X ^ 2 := by nlinarith
  have hin : 12288 * Q ^ 3 / ν ≤ (11086 * X ^ 2) ^ 2 := by
    have e : 12288 * Q ^ 3 / ν = 12288 * Q ^ 3 * (1 / ν) := by ring
    rw [e]
    have h1 : 12288 * Q ^ 3 * (1 / ν) ≤ 12288 * X ^ 3 * (10000 * X) :=
      mul_le_mul (by linarith) hνX (by positivity) (by positivity)
    have e2 : 12288 * X ^ 3 * (10000 * X) = 122880000 * X ^ 4 := by ring
    have e3 : (11086 * X ^ 2) ^ 2 = 122899396 * X ^ 4 := by ring
    have hX4 : 0 ≤ X ^ 4 := by positivity
    linarith
  have hsq : Real.sqrt (12288 * Q ^ 3 / ν) ≤ 11086 * X ^ 2 := by
    have := Real.sqrt_le_sqrt hin
    rwa [Real.sqrt_sq (by positivity)] at this
  have h1 : 2 * (2 + 64 * Q + Real.sqrt (12288 * Q ^ 3 / ν)) ≤ (2 : ℝ) ^ 15 * X ^ 2 := by
    linarith
  have h2 := nat_le_mul_pow m (2 ^ 15) X 15 2 hX le_rfl (h.le.trans h1)
  push_cast at h2
  linarith

/-- **The quadrature word**: `2^k < 2 (2 q*/ν + 2)` gives `k ≤ 16 + 2 log₂ X` for `1 ≤ q* ≤ X`
and `1/ν ≤ 10000 X`. -/
theorem k_word (k : ℕ) {Q ν X : ℝ} (hQ : 1 ≤ Q) (hQX : Q ≤ X) (hν : 0 < ν)
    (hνX : 1 / ν ≤ 10000 * X) (h : ((2 ^ k : ℕ) : ℝ) < 2 * (2 * Q / ν + 2)) :
    (k : ℝ) ≤ 16 + 2 * Real.logb 2 X := by
  have hX : 1 ≤ X := hQ.trans hQX
  have hX2 : 1 ≤ X ^ 2 := one_le_pow₀ hX
  have h1 : 2 * Q / ν ≤ 20000 * X ^ 2 := by
    have e : 2 * Q / ν = 2 * Q * (1 / ν) := by ring
    rw [e]
    have h2 : 2 * Q * (1 / ν) ≤ 2 * X * (10000 * X) :=
      mul_le_mul (by linarith) hνX (by positivity) (by linarith)
    linarith
  have h3 : 2 * (2 * Q / ν + 2) ≤ (2 : ℝ) ^ 16 * X ^ 2 := by
    linarith
  have h4 := nat_le_mul_pow k (2 ^ 16) X 16 2 hX le_rfl (h.le.trans h3)
  push_cast at h4
  linarith

/-! ### The words of the arithmetic accuracy -/

/-- `1/ζ ≤ 196608 q* · 10000 X` for `ν ≤ 196608 q* ζ` and `1/ν ≤ 10000 X`. -/
theorem inv_zeta_le {Q ζ ν X : ℝ} (hζ : 0 < ζ) (hν : 0 < ν)
    (hνX : 1 / ν ≤ 10000 * X) (hζν : ν ≤ 196608 * Q * ζ) :
    1 / ζ ≤ 196608 * Q * (10000 * X) := by
  have h1 : ν / ζ ≤ 196608 * Q := by
    rw [div_le_iff₀ hζ]
    exact hζν
  have hν' := hν.ne'
  have hζ' := hζ.ne'
  have e : 1 / ζ = (1 / ν) * (ν / ζ) := by
    field_simp
  rw [e]
  have h0 : 0 ≤ ν / ζ := by positivity
  have h1ν : (0 : ℝ) ≤ 1 / ν := by positivity
  have hX0 : (0 : ℝ) ≤ 10000 * X := h1ν.trans hνX
  calc 1 / ν * (ν / ζ) ≤ 10000 * X * (196608 * Q) := mul_le_mul hνX h1 h0 hX0
    _ = 196608 * Q * (10000 * X) := by ring

/-- **The fractional bits of the LCHS step**: for an arithmetic accuracy `ζ ≥ ν/(196608 q*)` and
the released grid bound `J ≤ 60 q* ℓ`, `F = fOf p ζ ≤ 54 + 4 log₂ X`. -/
theorem F_word (p : GateODE.Params) {Q ζ X : ℝ} (hg : 1 ≤ p.g) (hε : 0 < p.ε) (hε1 : p.ε ≤ 1)
    (hTD : 0 ≤ p.T * p.lamD) (hζ : 0 < ζ) (hQ : 1 ≤ Q) (hQX : Q ≤ X)
    (hJ : (p.J : ℝ) ≤ 60 * Q * logBudget p.g p.ε) (hℓX : logBudget p.g p.ε ≤ 10000 * X)
    (hνX : 1 / precision p.g p.ε ≤ 10000 * X) (hζν : precision p.g p.ε ≤ 196608 * Q * ζ) :
    (GateBinaryODE.fOf p ζ : ℝ) ≤ 54 + 4 * Real.logb 2 X := by
  have hX : 1 ≤ X := hQ.trans hQX
  have hν := ImprovedODEQueryBudget.precision_pos p.g p.ε hg hε
  have hℓ := ImprovedODEQueryBudget.logBudget_ge_one p.g p.ε hg hε hε1
  have hz := inv_zeta_le hζ hν hνX hζν
  have h1 := four_div_step_le p hg hε hε1 hTD hζ
  have hQℓ : Q * logBudget p.g p.ε ≤ X * (10000 * X) := mul_le_mul hQX hℓX (by linarith)
    (by linarith)
  have hJ0 : (0 : ℝ) ≤ p.J := Nat.cast_nonneg _
  have h2 : 4 * (p.J : ℝ) / ζ ≤ 2 ^ 53 * X ^ 4 := by
    have e : 4 * (p.J : ℝ) / ζ = 4 * (p.J : ℝ) * (1 / ζ) := by ring
    rw [e]
    have hQX' : Q * X ≤ X * X := mul_le_mul_of_nonneg_right hQX (by linarith)
    have hz0 : (0 : ℝ) ≤ 1 / ζ := (one_div_pos.mpr hζ).le
    have h3 : 4 * (p.J : ℝ) * (1 / ζ) ≤
        4 * (60 * (X * (10000 * X))) * (196608 * X * (10000 * X)) := by
      apply mul_le_mul _ _ hz0 (by positivity)
      · linarith
      · nlinarith
    have e2 : 4 * (60 * (X * (10000 * X))) * (196608 * X * (10000 * X)) =
        4718592000000000 * X ^ 4 := by ring
    have hX4 : 0 ≤ X ^ 4 := by positivity
    linarith
  have h4 := clog_le_mul_pow (4 / (ζ * GateBinaryODE.hStep p)) (2 ^ 53) X 53 4 hX le_rfl
    (h1.trans h2)
  unfold GateBinaryODE.fOf
  push_cast at h4
  linarith

/-- **The CORDIC steps**: for an arithmetic accuracy `ζ ≥ ν/(196608 q*)`, the steps of the
CORDIC accuracy `ζ/2` are `nOf (ζ/2) ≤ 38 + 2 log₂ X`. -/
theorem nOf_word {Q ζ ν X : ℝ} (hζ : 0 < ζ) (hν : 0 < ν) (hQ : 1 ≤ Q) (hQX : Q ≤ X)
    (hνX : 1 / ν ≤ 10000 * X) (hζν : ν ≤ 196608 * Q * ζ) :
    (GateBinary.Cordic.nOf (ζ / 2) : ℝ) ≤ 38 + 2 * Real.logb 2 X := by
  have hX : 1 ≤ X := hQ.trans hQX
  have hz := inv_zeta_le hζ hν hνX hζν
  have h1 : 8 / (ζ / 2) ≤ 2 ^ 35 * X ^ 2 := by
    have e : 8 / (ζ / 2) = 16 * (1 / ζ) := by
      rw [div_div_eq_mul_div]
      ring
    rw [e]
    have hQX' : Q * X ≤ X * X := mul_le_mul_of_nonneg_right hQX (by linarith)
    have h2 : 196608 * Q * (10000 * X) ≤ 196608 * X * (10000 * X) := by nlinarith
    have hX2 : 0 ≤ X ^ 2 := by positivity
    linarith
  have h3 := clog_le_mul_pow (8 / (ζ / 2)) (2 ^ 35) X 35 2 hX le_rfl h1
  unfold GateBinary.Cordic.nOf
  push_cast at h3 ⊢
  linarith

/-! ### The bits of the decoder scale -/

/-- **The bits of the decoder scale**: for `κ = γ √(4s) c₀ / (2^e ρ)` with the public rescaling
`γ = gammaOf T η_H η_D g ε`, `ρ = η_H + R η_D`, `R = radius g ε`, `1 ≤ s ≤ 2^k_x` and `c₀ > 0`,
`T`, `η_H`, `η_D` of bit length `bd`: `⌈log₂ ⌈κ⌉⌉ ≤ 1 + k_x + 2 bd` and
`⌈log₂ ⌈1/κ⌉⌉ ≤ e + 4 bd + 31 + 2 log₂ X`. -/
theorem kap_words (bd kx s e : ℕ) {T ηH ηD g ε c0 : ℝ} (h : ShapeOK (s : ℝ) T ηH ηD g ε)
    (hskx : s ≤ 2 ^ kx) (hc0 : HasBits bd c0) (hc0p : 0 < c0) (hT : HasBits bd T)
    (hH : HasBits bd ηH) (hD : HasBits bd ηD) :
    (Nat.clog 2 ⌈gammaOf T ηH ηD g ε * Real.sqrt (4 * (s : ℝ)) * c0 /
        (2 ^ e * (ηH + radius g ε * ηD))⌉₊ : ℝ) ≤ 1 + kx + 2 * bd ∧
    (Nat.clog 2 ⌈1 / (gammaOf T ηH ηD g ε * Real.sqrt (4 * (s : ℝ)) * c0 /
        (2 ^ e * (ηH + radius g ε * ηD)))⌉₊ : ℝ) ≤
      e + 4 * bd + 31 + 2 * Real.logb 2 ((qOf s T ηH ηD g ε * g + 1) / ε) := by
  have hs : 1 ≤ s := by exact_mod_cast h.s_ge
  have hR := one_le_radius h.g_ge h.ε_pos h.ε_le
  have hR8 := ImprovedODEQueryBudget.radius_le g ε h.g_ge h.ε_pos h.ε_le
  have hℓ := h.ell_ge
  have hℓX := shape_ell_le_X h
  have hX := shape_one_le_X h
  have hρ1 := one_le_mul_rho bd hH hD h.etaH_nonneg h.etaD_nonneg h.eta_pos hR
  have hρ : 0 < ηH + radius g ε * ηD := by
    have h2 : (0 : ℝ) < 2 ^ bd := by positivity
    by_contra hc
    have h3 := mul_le_mul_of_nonneg_left (not_lt.mp hc) h2.le
    linarith
  have hγ := h.gammaOf_pos
  have hγ1 := gammaOf_le_one T ηH ηD g ε
  refine ⟨?_, ?_⟩
  · have h1 := kap_le bd kx e s hγ1 hs hskx hc0 hc0p hρ hρ1
    have h2 := clog_ceil_le_nat _ _ h1
    have h3 : ((Nat.clog 2 ⌈gammaOf T ηH ηD g ε * Real.sqrt (4 * (s : ℝ)) * c0 /
        (2 ^ e * (ηH + radius g ε * ηD))⌉₊ : ℕ) : ℝ) ≤ ((1 + kx + 2 * bd : ℕ) : ℝ) := by
      exact_mod_cast h2
    push_cast at h3
    exact h3
  · have hρle := rho_le bd hH hD (by linarith : (0 : ℝ) ≤ radius g ε)
    have hγinv := gammaOf_inv_le bd h hT hH hD
    have hinv := kap_inv_le bd e s hγ hs hc0 hc0p hρ
    set ℓ := logBudget g ε with hℓdef
    set X := (qOf (s : ℝ) T ηH ηD g ε * g + 1) / ε with hXdef
    set R := radius g ε with hRdef
    have hRl : (1 + R) * ℓ ≤ 2 ^ 30 * X ^ 2 := by
      have h1 : (1 + R) * ℓ ≤ 9 * ℓ ^ 2 := by nlinarith
      have h2 : ℓ ^ 2 ≤ (10000 * X) ^ 2 := pow_le_pow_left₀ (by linarith) hℓX 2
      have hX2 : 0 ≤ X ^ 2 := by positivity
      linarith
    have hpos : (0 : ℝ) < 2 ^ bd := by positivity
    have hκ : 1 / (gammaOf T ηH ηD g ε * Real.sqrt (4 * (s : ℝ)) * c0 / (2 ^ e * (ηH + R * ηD))) ≤
        (2 : ℝ) ^ (e + 4 * bd + 30) * X ^ 2 := by
      rw [one_div]
      calc (gammaOf T ηH ηD g ε * Real.sqrt (4 * (s : ℝ)) * c0 / (2 ^ e * (ηH + R * ηD)))⁻¹
          ≤ 2 ^ e * (ηH + R * ηD) * (gammaOf T ηH ηD g ε)⁻¹ * 2 ^ bd / 2 := hinv
        _ ≤ 2 ^ e * ((1 + R) * 2 ^ bd) * (2 * ℓ * (2 ^ bd * 2 ^ bd)) * 2 ^ bd / 2 := by
          gcongr
        _ = 2 ^ e * (2 ^ bd * 2 ^ bd * 2 ^ bd * 2 ^ bd) * ((1 + R) * ℓ) := by ring
        _ ≤ 2 ^ e * (2 ^ bd * 2 ^ bd * 2 ^ bd * 2 ^ bd) * (2 ^ 30 * X ^ 2) := by gcongr
        _ = (2 : ℝ) ^ (e + 4 * bd + 30) * X ^ 2 := by ring
    have h4 := clog_le_mul_pow _ ((2 : ℝ) ^ (e + 4 * bd + 30)) X (e + 4 * bd + 30) 2 hX le_rfl
      hκ
    push_cast at h4
    linarith

end

end SparseHamiltonian.GateBitBudget
