import GateEfficientBitBudget.Time
import GateEfficientODEBudget.Synth

/-!
# The preparation bound and the synthesis factor in the word budget

For equations `ode:eq:gate-main` and `ode:eq:gate-space` of Theorem `ode:thm:gates` over a finite
gate set, in the word budget of equation `ode:eq:gate-word-budget`: the released solvers
(`GateODEBudget.binary_ode_budget_trials`, `GateODEBudget.binary_ode_time_budget_trials`)
synthesise one native preparation with at most
`B = prepBound` gates (respectively `prepBoundT`) at accuracy `ν/3`, so that their gate count
carries the logarithmic factor `c₁ log((B+1)/(ν/3)) + c₀`. In the word budget `𝔟`
(`bitB`, hypotheses of `binary_ode_budget_bits`, respectively `binary_ode_time_budget_bits`):

* `inner_le`: the per-preparation polynomial `G_C + k_x + σ + m + r + k + ℓ (l+1) + 8` is at most
  `65547 (𝔴 + ℓ + 1)³`;
* `prepBound_le`, `prepBoundT_le`: `B ≤ 2·10¹⁸ q* (𝔟+1)³ + G_src`;
* `log_prep_le`: `log((B+1)/(ν/3)) ≤ 43 + log P + log(3/ν) + log(G+1)` for `B ≤ 2·10¹⁸ P + G`;
  `log_three_div_le`: `log(3/ν) ≤ 11 + log₂ X` for `1/ν ≤ 10⁴ X`; `log_q_cube_le`:
  `log(q (𝔟+1)³) ≤ log₂ X + 3 𝔟` for `q ≤ X`;
* `log_factor_le`, `log_factorT_le`: `log((B+1)/(ν/3)) ≤ 64 (𝔟+1) + log(G_src + 1)`;
* `tested_le`, `testedT_le`: the tested register of the zero tests has at most
  `3·10¹¹ (𝔟+1)³ + 2 |Zs| + |Xa|` qubits.
-/

set_option autoImplicit false

namespace SparseHamiltonian.GateBitBudget

noncomputable section
open SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
open SparseHamiltonian.GateBinary SparseHamiltonian.GateBinaryODE
open SparseHamiltonian.GateBinaryODETime SparseHamiltonian.OracleCircuit
open GateODEBudget (gammaOf qOf words wordsT prepBound prepBoundT binary_arith_words
  binary_time_arith_words pub_shapeOK pubT_shapeOK)
open ImprovedODEQueryBudget (precision logBudget)
open NativeSparseBlockEncoding (Query)

/-! ### Generic arithmetic -/

/-- The per-preparation polynomial: `G_C + S + ℓ (l+1) + 8 ≤ 65547 (w + ℓ + 1)³` for
`G_C ≤ 65536 (w+1)³`, `S ≤ 2w`, `0 ≤ l ≤ w`, `ℓ ≥ 1`, `w ≥ 0`. -/
theorem inner_le {GC S ℓ l w : ℝ} (hw : 0 ≤ w) (hℓ : 1 ≤ ℓ) (hGC : GC ≤ 65536 * (w + 1) ^ 3)
    (hS : S ≤ 2 * w) (hl0 : 0 ≤ l) (hl : l ≤ w) :
    GC + S + ℓ * (l + 1) + 8 ≤ 65547 * (w + ℓ + 1) ^ 3 := by
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
  linarith

/-- **The logarithmic synthesis factor**: for `0 ≤ B ≤ 2·10¹⁸ P + G` with `P ≥ 1`, `G ≥ 0` and
`ν > 0`, `log((B+1)/(ν/3)) ≤ 43 + log P + log(3/ν) + log(G+1)`. -/
theorem log_prep_le {B P G ν : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ 2 * 10 ^ 18 * P + G) (hP : 1 ≤ P)
    (hG : 0 ≤ G) (hν : 0 < ν) :
    Real.log ((B + 1) / (ν / 3)) ≤ 43 + Real.log P + Real.log (3 / ν) + Real.log (G + 1) := by
  have h1 : B + 1 ≤ 3 * 10 ^ 18 * P * (G + 1) := by nlinarith
  have e : (B + 1) / (ν / 3) = (B + 1) * (3 / ν) := by
    rw [div_div_eq_mul_div, mul_div_assoc]
  rw [e]
  have h2 : Real.log ((B + 1) * (3 / ν)) ≤ Real.log (3 * 10 ^ 18 * P * (G + 1) * (3 / ν)) :=
    Real.log_le_log (by positivity) (mul_le_mul_of_nonneg_right h1 (by positivity))
  have hP0 : 0 < P := by linarith
  have e2 : Real.log (3 * 10 ^ 18 * P * (G + 1) * (3 / ν)) =
      Real.log (3 * 10 ^ 18) + Real.log P + Real.log (G + 1) + Real.log (3 / ν) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity)]
  have h3 : Real.log (3 * 10 ^ 18) ≤ 43 := by
    have h4 : Real.log (3 * 10 ^ 18) ≤ Real.log (2 ^ 62) :=
      Real.log_le_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at h4
    have := Real.log_two_lt_d9
    norm_num at h4 this ⊢
    linarith
  rw [e2] at h2
  generalize Real.log (3 * 10 ^ 18) = a at h2 h3
  linarith

/-- `log(3/ν) ≤ 11 + log₂ X` for `1/ν ≤ 10000 X`, `X ≥ 1`, `ν > 0`. -/
theorem log_three_div_le {ν X : ℝ} (hν : 0 < ν) (hX : 1 ≤ X) (hνX : 1 / ν ≤ 10000 * X) :
    Real.log (3 / ν) ≤ 11 + Real.logb 2 X := by
  have h1 : 3 / ν ≤ 30000 * X := by
    have e : 3 / ν = 3 * (1 / ν) := by ring
    rw [e]
    linarith
  have h2 : Real.log (3 / ν) ≤ Real.log (30000 * X) := Real.log_le_log (by positivity) h1
  have e3 : Real.log (30000 * X) = Real.log 30000 + Real.log X :=
    Real.log_mul (by norm_num) (by positivity)
  have h4 : Real.log 30000 ≤ 11 := by
    have h5 : Real.log 30000 ≤ Real.log (2 ^ 15) := Real.log_le_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at h5
    have := Real.log_two_lt_d9
    norm_num at h5 this ⊢
    linarith
  have h6 := log_le_logb X hX
  linarith

/-- `log(q (𝔟+1)³) ≤ log₂ X + 3 𝔟` for `0 < q ≤ X`, `X ≥ 1`, `𝔟 ≥ 0`. -/
theorem log_q_cube_le {Q X B : ℝ} (hQ : 0 < Q) (hQX : Q ≤ X) (hX : 1 ≤ X) (hB : 0 ≤ B) :
    Real.log (Q * (B + 1) ^ 3) ≤ Real.logb 2 X + 3 * B := by
  rw [Real.log_mul hQ.ne' (by positivity), Real.log_pow]
  have h1 : Real.log Q ≤ Real.log X := Real.log_le_log hQ hQX
  have h2 := log_le_logb X hX
  have h3 := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < B + 1)
  push_cast
  linarith

/-! ### Constant coefficients -/

/-- **The preparation bound in `𝔟`** (constant coefficients): under the hypotheses of
`binary_ode_budget_bits`, `prepBound q srcC ≤ 2·10¹⁸ q* (𝔟+1)³ + G_src`. -/
theorem prepBound_le (bd : ℕ) (q : Pub) (hq : q.OK)
    (hγ : q.γ = gammaOf q.T q.etaH q.etaD q.g q.ε)
    (hζ : q.params.nu ≤ 196608 * qOf q.s q.T q.etaH q.etaD q.g q.ε * q.ζ) (hb : q.b ≤ bd)
    (hc0 : HasBits bd q.c0) (hT : HasBits bd q.T) (hH : HasBits bd q.etaH)
    (hD : HasBits bd q.etaD) {Zs : Type*}
    (srcC : Bool → List (NInstr ((Unit ⊕ Fin q.kx) ⊕ Zs) (PY q.kx q.b) Query)) :
    prepBound q srcC ≤ 2 * 10 ^ 18 * qOf q.s q.T q.etaH q.etaD q.g q.ε *
        (bitB bd (2 ^ q.kx) (2 ^ q.params.m) (2 ^ q.params.k)
          (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε + 1) ^ 3 +
      ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true)) := by
  have h := pub_shapeOK q hq
  have hw := words_le_bitB bd q hq hγ hζ hb hc0 hT hH hD
  obtain ⟨hGC, -, -, -⟩ := binary_arith_words q
  have hℓ := h.ell_ge
  have hQ1 := h.one_le_q
  have hσ := q.hσ
  have hε1 : q.ε ≤ 1 := hq.ε_half.trans (by norm_num)
  have hB0 : 0 ≤ bitB bd (2 ^ q.kx) (2 ^ q.params.m) (2 ^ q.params.k)
      (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε :=
    bitB_nonneg _ _ _ _ (mul_nonneg (by linarith) (by linarith [hq.g_ge])) hq.ε_pos hε1
  have hw0 : (0 : ℝ) ≤ words q := Nat.cast_nonneg _
  have hGC' : (((2 * (28 * q.kx + 2) + 2 * q.ar.circ.length + (2 * q.ar.bP + q.ar.bT + 1) :
      ℕ) : ℝ)) ≤ 65536 * ((words q : ℝ) + 1) ^ 3 := by exact_mod_cast hGC
  have hS : (q.kx : ℝ) + q.σ + q.params.m + q.params.r + q.params.k ≤ 2 * (words q : ℝ) := by
    have : q.kx + q.σ + q.params.m + q.params.r + q.params.k ≤ 2 * words q := by
      unfold words
      omega
    exact_mod_cast this
  have hl : (q.params.l : ℝ) ≤ words q := by
    have : q.params.l ≤ words q := by
      unfold words
      omega
    exact_mod_cast this
  have hin := inner_le hw0 hℓ hGC' hS (Nat.cast_nonneg _) hl
  have hcube := cube_le (by linarith) hB0 hw
  have hY := one_le_pow₀ (by linarith : (1 : ℝ) ≤ (words q : ℝ) + logBudget q.g q.ε + 1)
    (n := 3)
  unfold prepBound
  have hQ0 : 0 ≤ qOf q.s q.T q.etaH q.etaD q.g q.ε := by linarith
  have h1 : (((2 * (28 * q.kx + 2) + 2 * q.ar.circ.length + (2 * q.ar.bP + q.ar.bT + 1) : ℕ) :
      ℝ) + q.kx + q.σ + q.params.m + q.params.r + q.params.k +
      logBudget q.g q.ε * ((q.params.l : ℝ) + 1) + 8) ≤
      65547 * ((300 + 1) ^ 3 * (bitB bd (2 ^ q.kx) (2 ^ q.params.m) (2 ^ q.params.k)
        (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε + 1) ^ 3) := by
    linarith
  have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 819400 *
    qOf q.s q.T q.etaH q.etaD q.g q.ε)
  have hY2 : 0 ≤ qOf q.s q.T q.etaH q.etaD q.g q.ε *
      (bitB bd (2 ^ q.kx) (2 ^ q.params.m) (2 ^ q.params.k)
        (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε + 1) ^ 3 := by positivity
  linarith

/-- **The synthesis factor in `𝔟`** (constant coefficients): under the hypotheses of
`binary_ode_budget_bits`, `log((B+1)/(ν/3)) ≤ 64 (𝔟+1) + log(G_src+1)` for
`B = prepBound q srcC`. -/
theorem log_factor_le (bd : ℕ) (q : Pub) (hq : q.OK)
    (hγ : q.γ = gammaOf q.T q.etaH q.etaD q.g q.ε)
    (hζ : q.params.nu ≤ 196608 * qOf q.s q.T q.etaH q.etaD q.g q.ε * q.ζ) (hb : q.b ≤ bd)
    (hc0 : HasBits bd q.c0) (hT : HasBits bd q.T) (hH : HasBits bd q.etaH)
    (hD : HasBits bd q.etaD) {Zs : Type*}
    (srcC : Bool → List (NInstr ((Unit ⊕ Fin q.kx) ⊕ Zs) (PY q.kx q.b) Query))
    (hB0 : 0 ≤ prepBound q srcC) :
    Real.log ((prepBound q srcC + 1) / (q.params.nu / 3)) ≤
      64 * (bitB bd (2 ^ q.kx) (2 ^ q.params.m) (2 ^ q.params.k)
        (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε + 1) +
      Real.log ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true) + 1) := by
  have h := pub_shapeOK q hq
  have hε1 : q.ε ≤ 1 := hq.ε_half.trans (by norm_num)
  have hQ1 := h.one_le_q
  have hX := shape_one_le_X h
  have hQX := shape_q_le_X h
  have hνX : 1 / q.params.nu ≤
      10000 * ((qOf q.s q.T q.etaH q.etaD q.g q.ε * q.g + 1) / q.ε) :=
    shape_inv_precision_le h
  have hν : 0 < q.params.nu := (q.params_ok hq).nu_pos
  have hB0' : 0 ≤ bitB bd (2 ^ q.kx) (2 ^ q.params.m) (2 ^ q.params.k)
      (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε :=
    bitB_nonneg _ _ _ _ (mul_nonneg (by linarith) (by linarith [hq.g_ge])) hq.ε_pos hε1
  have hP : 1 ≤ qOf q.s q.T q.etaH q.etaD q.g q.ε *
      (bitB bd (2 ^ q.kx) (2 ^ q.params.m) (2 ^ q.params.k)
        (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε + 1) ^ 3 :=
    one_le_mul_of_one_le_of_one_le hQ1 (one_le_pow₀ (by linarith))
  have hBp := prepBound_le bd q hq hγ hζ hb hc0 hT hH hD srcC
  have hBp' : prepBound q srcC ≤ 2 * 10 ^ 18 * (qOf q.s q.T q.etaH q.etaD q.g q.ε *
      (bitB bd (2 ^ q.kx) (2 ^ q.params.m) (2 ^ q.params.k)
        (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε + 1) ^ 3) +
      ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true)) :=
    hBp.trans (le_of_eq (by ring))
  have h1 := log_prep_le hB0 hBp' hP (by positivity) hν
  have h2 := log_q_cube_le (by linarith) hQX hX hB0'
  have h3 := log_three_div_le hν hX hνX
  have hL : Real.logb 2 ((qOf q.s q.T q.etaH q.etaD q.g q.ε * q.g + 1) / q.ε) ≤
      bitB bd (2 ^ q.kx) (2 ^ q.params.m) (2 ^ q.params.k)
        (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε := by
    have h4 := logb_succ_nonneg (2 ^ q.kx)
    have h5 := logb_succ_nonneg (2 ^ q.params.m)
    have h6 := logb_succ_nonneg (2 ^ q.params.k)
    have h7 : (0 : ℝ) ≤ bd := Nat.cast_nonneg _
    unfold bitB
    linarith
  have e : ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true) + 1) =
      ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true)) + 1 := rfl
  linarith

/-- **The tested register in `𝔟`** (constant coefficients): under the hypotheses of
`binary_ode_budget_bits`, the native part `22 k_x + 12 m + 24 r + 4 k + 4 l + 8 b +
2 (bT + bP + A_arith) + 47` of the register tested by the zero tests is at most
`3·10¹¹ (𝔟+1)³`. -/
theorem tested_le (bd : ℕ) (q : Pub) (hq : q.OK)
    (hγ : q.γ = gammaOf q.T q.etaH q.etaD q.g q.ε)
    (hζ : q.params.nu ≤ 196608 * qOf q.s q.T q.etaH q.etaD q.g q.ε * q.ζ) (hb : q.b ≤ bd)
    (hc0 : HasBits bd q.c0) (hT : HasBits bd q.T) (hH : HasBits bd q.etaH)
    (hD : HasBits bd q.etaD) :
    ((22 * q.kx + 12 * q.params.m + 24 * q.params.r + 4 * q.params.k + 4 * q.params.l +
        8 * q.b + 2 * (q.ar.bT + q.ar.bP + q.ar.A) + 47 : ℕ) : ℝ) ≤
      3 * 10 ^ 11 * (bitB bd (2 ^ q.kx) (2 ^ q.params.m) (2 ^ q.params.k)
        (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε + 1) ^ 3 := by
  have h := pub_shapeOK q hq
  have hw := words_le_bitB bd q hq hγ hζ hb hc0 hT hH hD
  obtain ⟨-, hA, hT', hP'⟩ := binary_arith_words q
  have hσ := q.hσ
  have hε1 : q.ε ≤ 1 := hq.ε_half.trans (by norm_num)
  have hℓ := h.ell_ge
  have hB0 : 0 ≤ bitB bd (2 ^ q.kx) (2 ^ q.params.m) (2 ^ q.params.k)
      (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε :=
    bitB_nonneg _ _ _ _ (mul_nonneg (by linarith [h.one_le_q]) (by linarith [hq.g_ge]))
      hq.ε_pos hε1
  have h24 : 22 * q.kx + 12 * q.params.m + 24 * q.params.r + 4 * q.params.k + 4 * q.params.l +
      8 * q.b ≤ 24 * words q := by
    unfold words
    omega
  have hp1 : words q + 1 ≤ (words q + 1) ^ 3 := le_self_pow₀ (by omega) (by norm_num)
  have hn : 22 * q.kx + 12 * q.params.m + 24 * q.params.r + 4 * q.params.k + 4 * q.params.l +
      8 * q.b + 2 * (q.ar.bT + q.ar.bP + q.ar.A) + 47 ≤ 8283 * (words q + 1) ^ 3 := by
    omega
  have hn' : ((22 * q.kx + 12 * q.params.m + 24 * q.params.r + 4 * q.params.k +
      4 * q.params.l + 8 * q.b + 2 * (q.ar.bT + q.ar.bP + q.ar.A) + 47 : ℕ) : ℝ) ≤
      8283 * ((words q : ℝ) + 1) ^ 3 := by exact_mod_cast hn
  have hcube := cube_le (Nat.cast_nonneg (words q)) hB0 (c := 300) (by linarith)
  have hY : 0 ≤ (bitB bd (2 ^ q.kx) (2 ^ q.params.m) (2 ^ q.params.k)
      (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε + 1) ^ 3 := by positivity
  linarith

/-! ### Time-dependent coefficients -/

/-- **The preparation bound in `𝔟`** (time-dependent coefficients): under the hypotheses of
`binary_ode_time_budget_bits`, `prepBoundT q loadC wpC ≤ 2·10¹⁸ q* (𝔟+1)³ + G_src`,
`G_src = |loadC| + 2 |wpC|`. -/
theorem prepBoundT_le (bd : ℕ) (q : PubT) (hq : q.OK)
    (hγ : q.γ = gammaOf q.T q.etaH q.etaD (2 * q.g) (q.ε / 2))
    (hζ : q.params.nu ≤ 196608 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * q.ζ)
    (hb : q.b ≤ bd) (hc0 : HasBits bd q.c0) (hT : HasBits bd q.T) (hH : HasBits bd q.etaH)
    (hD : HasBits bd q.etaD) {Zs : Type*}
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b)
      Query))
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b) Query)) :
    prepBoundT q loadC wpC ≤ 2 * 10 ^ 18 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
        (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
          (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ 3 +
      ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) := by
  have h := pubT_shapeOK q hq
  have hw := wordsT_le bd q hq hγ hζ hb hc0 hT hH hD
  obtain ⟨hGC, -, -, -⟩ := binary_time_arith_words q
  have hℓ := h.ell_ge
  have hQ1 := h.one_le_q
  have hσ := q.hσ
  have hε1 : q.ε ≤ 1 := hq.ε_half.trans (by norm_num)
  have hB0 : 0 ≤ bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
      (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε :=
    bitB_nonneg _ _ _ _ (mul_nonneg (by linarith) (by linarith [hq.g_ge])) hq.ε_pos hε1
  have hw0 : (0 : ℝ) ≤ wordsT q := Nat.cast_nonneg _
  have hGC' : (((2 * (28 * q.kx + 2) + 2 * q.ar.circ.length + (2 * q.ar.bP + q.ar.bT + 1) :
      ℕ) : ℝ)) ≤ 65536 * ((wordsT q : ℝ) + 1) ^ 3 := by exact_mod_cast hGC
  have hS : (q.kx : ℝ) + q.σ + q.params.m + q.params.r ≤ 2 * (wordsT q : ℝ) := by
    have : q.kx + q.σ + q.params.m + q.params.r ≤ 2 * wordsT q := by
      unfold wordsT
      omega
    exact_mod_cast this
  have hl : (q.params.l : ℝ) ≤ wordsT q := by
    have : q.params.l ≤ wordsT q := by
      unfold wordsT
      omega
    exact_mod_cast this
  have hin := inner_le hw0 hℓ hGC' hS (Nat.cast_nonneg _) hl
  have hcube := cube_le (by linarith) hB0 hw
  have hY := one_le_pow₀
    (by linarith : (1 : ℝ) ≤ (wordsT q : ℝ) + logBudget (2 * q.g) (q.ε / 2) + 1) (n := 3)
  unfold prepBoundT
  have hQ0 : 0 ≤ qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) := by linarith
  have h1 : (((2 * (28 * q.kx + 2) + 2 * q.ar.circ.length + (2 * q.ar.bP + q.ar.bT + 1) : ℕ) :
      ℝ) + q.kx + q.σ + q.params.m + q.params.r +
      logBudget (2 * q.g) (q.ε / 2) * ((q.params.l : ℝ) + 1) + 8) ≤
      65547 * ((300 + 1) ^ 3 * (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
        (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ 3) := by
    linarith
  have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 819400 *
    qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2))
  have hY2 : 0 ≤ qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
      (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
        (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ 3 := by positivity
  linarith

/-- **The synthesis factor in `𝔟`** (time-dependent coefficients): under the hypotheses of
`binary_ode_time_budget_bits`, `log((B+1)/(ν/3)) ≤ 64 (𝔟+1) + log(G_src+1)` for
`B = prepBoundT q loadC wpC`. -/
theorem log_factorT_le (bd : ℕ) (q : PubT) (hq : q.OK)
    (hγ : q.γ = gammaOf q.T q.etaH q.etaD (2 * q.g) (q.ε / 2))
    (hζ : q.params.nu ≤ 196608 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * q.ζ)
    (hb : q.b ≤ bd) (hc0 : HasBits bd q.c0) (hT : HasBits bd q.T) (hH : HasBits bd q.etaH)
    (hD : HasBits bd q.etaD) {Zs : Type*}
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b)
      Query))
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b) Query))
    (hB0 : 0 ≤ prepBoundT q loadC wpC) :
    Real.log ((prepBoundT q loadC wpC + 1) / (q.params.nu / 3)) ≤
      64 * (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
        (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) +
      Real.log ((nGatesN loadC : ℝ) + 2 * nGatesN wpC + 1) := by
  have h := pubT_shapeOK q hq
  have hε1 : q.ε ≤ 1 := hq.ε_half.trans (by norm_num)
  have hQ1 := h.one_le_q
  have hX := shape_one_le_X h
  have hQX := shape_q_le_X h
  have hνX : 1 / q.params.nu ≤ 10000 *
      ((qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * (2 * q.g) + 1) / (q.ε / 2)) :=
    shape_inv_precision_le h
  have hν : 0 < q.params.nu := q.params.nu_pos hq.g_ge hq.ε_pos
  have hB0' : 0 ≤ bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
      (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε :=
    bitB_nonneg _ _ _ _ (mul_nonneg (by linarith) (by linarith [hq.g_ge])) hq.ε_pos hε1
  have hP : 1 ≤ qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
      (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
        (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ 3 :=
    one_le_mul_of_one_le_of_one_le hQ1 (one_le_pow₀ (by linarith))
  have hBp := prepBoundT_le bd q hq hγ hζ hb hc0 hT hH hD loadC wpC
  have hBp' : prepBoundT q loadC wpC ≤ 2 * 10 ^ 18 *
      (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
        (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
          (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ 3) +
      ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) :=
    hBp.trans (le_of_eq (by ring))
  have h1 := log_prep_le hB0 hBp' hP (by positivity) hν
  have h2 := log_q_cube_le (by linarith) hQX hX hB0'
  have h3 := log_three_div_le hν hX hνX
  have hLL := logb_X_two_le (Q := qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) (g := q.g)
    (by linarith) (by linarith [hq.g_ge]) hq.ε_pos hε1
  have hL : Real.logb 2 ((qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * q.g + 1) / q.ε) ≤
      bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
        (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε := by
    have h4 := logb_succ_nonneg (2 ^ q.kx)
    have h5 := logb_succ_nonneg (2 ^ q.m)
    have h7 : (0 : ℝ) ≤ bd := Nat.cast_nonneg _
    unfold bitB
    linarith
  linarith

/-- **The tested register in `𝔟`** (time-dependent coefficients): under the hypotheses of
`binary_ode_time_budget_bits`, the native part `22 k_x + 16 m + 24 r + 4 l + 8 b +
2 (bT + bP + A_arith) + 47` of the register tested by the zero tests is at most
`3·10¹¹ (𝔟+1)³`. -/
theorem testedT_le (bd : ℕ) (q : PubT) (hq : q.OK)
    (hγ : q.γ = gammaOf q.T q.etaH q.etaD (2 * q.g) (q.ε / 2))
    (hζ : q.params.nu ≤ 196608 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * q.ζ)
    (hb : q.b ≤ bd) (hc0 : HasBits bd q.c0) (hT : HasBits bd q.T) (hH : HasBits bd q.etaH)
    (hD : HasBits bd q.etaD) :
    ((22 * q.kx + 16 * q.params.m + 24 * q.params.r + 4 * q.params.l + 8 * q.b +
        2 * (q.ar.bT + q.ar.bP + q.ar.A) + 47 : ℕ) : ℝ) ≤
      3 * 10 ^ 11 * (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
        (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ 3 := by
  have h := pubT_shapeOK q hq
  have hw := wordsT_le bd q hq hγ hζ hb hc0 hT hH hD
  obtain ⟨-, hA, hT', hP'⟩ := binary_time_arith_words q
  have hσ := q.hσ
  have hε1 : q.ε ≤ 1 := hq.ε_half.trans (by norm_num)
  have hℓ := h.ell_ge
  have hB0 : 0 ≤ bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
      (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε :=
    bitB_nonneg _ _ _ _ (mul_nonneg (by linarith [h.one_le_q]) (by linarith [hq.g_ge]))
      hq.ε_pos hε1
  have h24 : 22 * q.kx + 16 * q.params.m + 24 * q.params.r + 4 * q.params.l + 8 * q.b ≤
      24 * wordsT q := by
    unfold wordsT
    omega
  have hp1 : wordsT q + 1 ≤ (wordsT q + 1) ^ 3 := le_self_pow₀ (by omega) (by norm_num)
  have hn : 22 * q.kx + 16 * q.params.m + 24 * q.params.r + 4 * q.params.l + 8 * q.b +
      2 * (q.ar.bT + q.ar.bP + q.ar.A) + 47 ≤ 8283 * (wordsT q + 1) ^ 3 := by
    omega
  have hn' : ((22 * q.kx + 16 * q.params.m + 24 * q.params.r + 4 * q.params.l + 8 * q.b +
      2 * (q.ar.bT + q.ar.bP + q.ar.A) + 47 : ℕ) : ℝ) ≤ 8283 * ((wordsT q : ℝ) + 1) ^ 3 := by
    exact_mod_cast hn
  have hcube := cube_le (Nat.cast_nonneg (wordsT q)) hB0 (c := 300) (by linarith)
  have hY : 0 ≤ (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
      (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ 3 := by positivity
  linarith

end

end SparseHamiltonian.GateBitBudget
