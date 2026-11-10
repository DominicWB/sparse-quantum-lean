import ManuscriptConformance.GateDefs

/-!
# Conformance: Theorem `gate:thm:main` (gate-efficient improved-precision simulation)

Theorem `gate:thm:main` in its polynomial form (eq. `gate:eq:main-gates`),
derived from the package's binary endpoint `GateOptimalBinary.gate_optimal_binary_synth` and its
explicit counts.

**Hypotheses, as in the manuscript.** The access and compatible norm bounds of `hs:thm:two-norm`
(Hermitian `H`, row and column Euclidean norms at most `η`, entries of modulus at most `μ`,
`μ ≤ η ≤ √s μ`), `η²|t|/μ ≥ 1`, `0 < ε ≤ 1/64`, and the computational assumptions of Section
`gate:sec:result` (the paragraph before Theorem `gate:thm:main`):

* `comp_bits`: the entry words and the public parameters have at most `b_data` bits (stored bits
  `b ≤ b_data`; the decoder scale `c₀` and the norm bounds `η`, `μ` of bit length `b_data` in the
  package's fixed-point model `GateBitBudget.HasBits`);
* `comp_signedArith`, `comp_clipArith`: the decoder and reversible scalar arithmetic of the
  signed-factor and clipped regimes evaluate their local rotation parameters to every accuracy
  `ξ ∈ (0, 1]` with gates and clean work at most `c_A (b_data + k + log₂(1/ξ) + 1)^{d_A}`, a fixed
  polynomial in `b_data`, the index width and `log(1/ξ)` (`comp_signedArith`, `comp_clipArith`; the
  angle arithmetic of the bounded regime is the package's CORDIC circuit, whose counts are proved);
* the finite-gate assumptions of Section `gate:sec:result`: "An arbitrary one-qubit unitary can
  be synthesised to error `ζ` with `O(log(1/ζ))` gates for `0 < ζ ≤ 1/2`" (Ref. KMM2013;
  `ext_singleQubitSynthesis`, `ext_singleQubitLength`) and "A one-qubit unitary with at most three
  controls (on specified bits equal to zero or one) has an exact decomposition into a bounded
  number of gates from the set and uncontrolled one-qubit unitaries" (Ref. Barenco et al.;
  `ext_controlDecomposition`); both are external results, not reproved.

The one formal restriction is `formal_binaryInput` (`BinaryFormat`, review item B): `N = 2^k`,
`s = 2^{s_b}` with the slots enumerated by the low index words, two's complement entries decoded
as `c₀(X + iY)`. Besides this named restriction, the value oracle is additive, the package's
convention: it XOR-writes the stored word, `|i, j, z⟩ ↦ |i, j, z ⊕ w_ij⟩`, on every pair of index
words. The manuscript gives XOR-writing as an example of a reversible writer (eq.
`access:eq:value`), so a writer specified only on clean targets is not covered.

**Conclusion, as in the manuscript.** One circuit over the gate set and the primitive sparse
oracles, fixed before the instance, with `O(Q_μ)` primitive sparse queries (eq.
`gate:eq:query-scale`, `twoNormBound`), `Q_μ · C (𝔟 + 1)^K` gates (eq. `gate:eq:main-gates`,
`𝔟 = gateWord b_data N s Q_μ ε`), at most `k + C (𝔟 + 1)^K` qubits (`k` system qubits; the
auxiliary qubits polynomial in the same arguments, without the factor `Q_μ`), and full-output error
at most `ε` on the clean embedding (eq. `gate:eq:full`) with an untouched reference of any finite
dimension. The constants `C` and `K = max(3, d_A) + 1` depend only on the arithmetic polynomial and
the synthesis data.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4096

namespace ManuscriptConformance

noncomputable section
open ContinuousLinearMap SparseHamiltonian SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
  SparseHamiltonian.GateSynth SparseHamiltonian.GateBinary SparseHamiltonian.GateBitBudget
open scoped InnerProduct

/-! ### Real estimates -/

section Real

theorem one_le_div_of_le {Q ε : ℝ} (hQ : 0 ≤ Q) (hε : 0 < ε) (hε1 : ε ≤ 1) : 1 ≤ (Q + 1) / ε := by
  rw [le_div_iff₀ hε]; linarith

theorem logb_nonneg_of_one_le {x : ℝ} (hx : 1 ≤ x) : 0 ≤ Real.logb 2 x :=
  Real.logb_nonneg one_lt_two hx

/-- **The mesh and label words**: from the bounds `2^m ≤ 10³⁶ (Q'+1)⁴/(ε/4)` and
`2^r ≤ 10⁸ (Q'+1)` of the native claims, `Q' ≤ 4Q`, `m ≤ 135 B` and `r ≤ 30 B` for every
`B ≥ max(1, log₂((Q+1)/ε))`. -/
theorem mesh_label_words {Q Q' ε B : ℝ} {m r : ℕ} (hQ : 0 ≤ Q) (hQ' : 0 ≤ Q') (hQQ : Q' ≤ 4 * Q)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hB1 : 1 ≤ B) (hB : Real.logb 2 ((Q + 1) / ε) ≤ B)
    (hm : ((2 ^ m : ℕ) : ℝ) ≤ 10 ^ 36 * (Q' + 1) ^ 4 / (ε / 4))
    (hr : ((2 ^ r : ℕ) : ℝ) ≤ 10 ^ 8 * (Q' + 1)) :
    (m : ℝ) ≤ 135 * B ∧ (r : ℝ) ≤ 30 * B := by
  set Y := (Q + 1) / ε with hY
  have hY1 : 1 ≤ Y := one_le_div_of_le hQ hε hε1
  have hQ1 : Q' + 1 ≤ 4 * Y := by
    have : Q + 1 ≤ Y := by rw [hY, le_div_iff₀ hε]; nlinarith
    linarith
  have hεY : 1 / ε ≤ Y := div_le_div_of_nonneg_right (by linarith) hε.le
  constructor
  · have h1 : 10 ^ 36 * (Q' + 1) ^ 4 / (ε / 4) ≤ (2 : ℝ) ^ 130 * Y ^ 5 := by
      have e : 10 ^ 36 * (Q' + 1) ^ 4 / (ε / 4) = 4 * 10 ^ 36 * (Q' + 1) ^ 4 * (1 / ε) := by
        field_simp
      rw [e]
      have h4 : (Q' + 1) ^ 4 ≤ (4 * Y) ^ 4 := pow_le_pow_left₀ (by linarith) hQ1 4
      have h5 : 4 * 10 ^ 36 * (Q' + 1) ^ 4 * (1 / ε) ≤ 4 * 10 ^ 36 * (4 * Y) ^ 4 * Y :=
        mul_le_mul (by linarith) hεY (by positivity) (by positivity)
      have e2 : 4 * 10 ^ 36 * (4 * Y) ^ 4 * Y = 1024 * 10 ^ 36 * Y ^ 5 := by ring
      have h6 : (1024 * 10 ^ 36 : ℝ) ≤ 2 ^ 130 := by norm_num
      nlinarith [pow_pos (by linarith : (0 : ℝ) < Y) 5]
    have h2 := nat_le_mul_pow m ((2 : ℝ) ^ 130) Y 130 5 hY1 le_rfl (hm.trans h1)
    push_cast at h2
    linarith
  · have h1 : 10 ^ 8 * (Q' + 1) ≤ (2 : ℝ) ^ 29 * Y ^ 1 := by
      rw [pow_one]
      have h6 : (4 * 10 ^ 8 : ℝ) ≤ 2 ^ 29 := by norm_num
      nlinarith
    have h2 := nat_le_mul_pow r ((2 : ℝ) ^ 29) Y 29 1 hY1 le_rfl (hr.trans h1)
    push_cast at h2
    linarith

/-- **The synthesis factor**: for `0 ≤ M ≤ Q c_N B^K` (`Q, B ≥ 1`, `c_N ≥ 1`, `K ≥ 1`) and
`log₂((Q+1)/ε) ≤ B`, `M (c₁ log((M+1)/(ε/2)) + c₀) ≤ Q c_N (c₁ (log(4 c_N) + K + 2) + c₀) B^{K+1}`. -/
theorem synth_factor {M Q cN B ε c₀ c₁ : ℝ} {K : ℕ} (hM0 : 0 ≤ M) (hQ : 1 ≤ Q) (hcN : 1 ≤ cN)
    (hB1 : 1 ≤ B) (hε : 0 < ε) (hε1 : ε ≤ 1) (hB : Real.logb 2 ((Q + 1) / ε) ≤ B)
    (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁) (hM : M ≤ Q * cN * B ^ K) :
    M * (c₁ * Real.log ((M + 1) / (ε / 2)) + c₀) ≤
      Q * cN * (c₁ * (Real.log (4 * cN) + K + 2) + c₀) * B ^ (K + 1) := by
  set M' := Q * cN * B ^ K with hM'
  have hBK : 1 ≤ B ^ K := one_le_pow₀ hB1
  have hM'1 : 1 ≤ M' := by
    have := one_le_mul_of_one_le_of_one_le hQ hcN
    exact one_le_mul_of_one_le_of_one_le this hBK
  -- the logarithm
  have hY1 : 1 ≤ (Q + 1) / ε := one_le_div_of_le (by linarith) hε hε1
  have hlogY : Real.log ((Q + 1) / ε) ≤ B :=
    (log_le_logb _ hY1).trans hB
  have hlogQ : Real.log Q ≤ B := by
    refine le_trans ?_ hlogY
    apply Real.log_le_log (by linarith)
    rw [le_div_iff₀ hε]; nlinarith
  have hlogε : Real.log (1 / ε) ≤ B := by
    refine le_trans ?_ hlogY
    apply Real.log_le_log (by positivity)
    exact div_le_div_of_nonneg_right (by linarith) hε.le
  have hlogB : Real.log B ≤ B := by
    have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < B)
    linarith
  have hlogM' : Real.log ((M' + 1) / (ε / 2)) ≤ Real.log (4 * cN) + (K + 2) * B := by
    have h1 : (M' + 1) / (ε / 2) ≤ 4 * cN * Q * B ^ K * (1 / ε) := by
      rw [div_le_iff₀ (by positivity)]
      have e : 4 * cN * Q * B ^ K * (1 / ε) * (ε / 2) = 2 * M' := by
        rw [hM']; field_simp; ring
      rw [e]; linarith
    have hpos : 0 < (M' + 1) / (ε / 2) := by positivity
    have h2 := Real.log_le_log hpos h1
    have e : Real.log (4 * cN * Q * B ^ K * (1 / ε)) =
        Real.log (4 * cN) + Real.log Q + K * Real.log B + Real.log (1 / ε) := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity), Real.log_pow]
    rw [e] at h2
    have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    nlinarith
  -- monotonicity in `M`
  have hmono : M * (c₁ * Real.log ((M + 1) / (ε / 2)) + c₀) ≤
      M' * (c₁ * Real.log ((M' + 1) / (ε / 2)) + c₀) := by
    have hl0 : 0 ≤ Real.log ((M + 1) / (ε / 2)) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ (by positivity)]; linarith
    have hl : Real.log ((M + 1) / (ε / 2)) ≤ Real.log ((M' + 1) / (ε / 2)) := by
      apply Real.log_le_log (by positivity)
      exact div_le_div_of_nonneg_right (by linarith) (by positivity)
    have hf : c₁ * Real.log ((M + 1) / (ε / 2)) + c₀ ≤
        c₁ * Real.log ((M' + 1) / (ε / 2)) + c₀ := by nlinarith
    exact mul_le_mul hM hf (by positivity) (by linarith)
  refine hmono.trans ?_
  have hL0 : 0 ≤ Real.log (4 * cN) := Real.log_nonneg (by linarith)
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hf : c₁ * Real.log ((M' + 1) / (ε / 2)) + c₀ ≤
      (c₁ * (Real.log (4 * cN) + K + 2) + c₀) * B := by
    have h1 : c₁ * Real.log ((M' + 1) / (ε / 2)) ≤ c₁ * (Real.log (4 * cN) + (K + 2) * B) :=
      mul_le_mul_of_nonneg_left hlogM' hc₁
    have h2 : c₁ * (Real.log (4 * cN) + (K + 2) * B) ≤ c₁ * (Real.log (4 * cN) + K + 2) * B := by
      have : Real.log (4 * cN) ≤ Real.log (4 * cN) * B := le_mul_of_one_le_right hL0 hB1
      nlinarith
    have h3 : c₀ ≤ c₀ * B := le_mul_of_one_le_right hc₀ hB1
    nlinarith
  have hM'0 : 0 ≤ M' := by linarith
  calc M' * (c₁ * Real.log ((M' + 1) / (ε / 2)) + c₀)
      ≤ M' * ((c₁ * (Real.log (4 * cN) + K + 2) + c₀) * B) := mul_le_mul_of_nonneg_left hf hM'0
    _ = Q * cN * (c₁ * (Real.log (4 * cN) + K + 2) + c₀) * B ^ (K + 1) := by
        rw [hM', pow_succ]; ring

end Real

/-! ### The per-call costs of the three regimes -/

section Costs

/-- `log₂(1/ξ) ≤ 49 B` for the arithmetic accuracy `ξ = ε/(2·10¹⁴ Q)`. -/
theorem logb_inv_xi_le {Q ε B : ℝ} (hQ : 1 ≤ Q) (hε : 0 < ε) (hε1 : ε ≤ 1) (hB1 : 1 ≤ B)
    (hB : Real.logb 2 ((Q + 1) / ε) ≤ B) :
    Real.logb 2 (1 / (ε / (2 * 10 ^ 14 * Q))) ≤ 49 * B := by
  set Y := (Q + 1) / ε with hY
  have hY1 : 1 ≤ Y := one_le_div_of_le (by linarith) hε hε1
  have h1 : 1 / (ε / (2 * 10 ^ 14 * Q)) ≤ 2 * 10 ^ 14 * Y ^ 1 := by
    rw [pow_one, one_div_div, hY, div_le_iff₀ hε]
    have : 2 * 10 ^ 14 * ((Q + 1) / ε) * ε = 2 * 10 ^ 14 * (Q + 1) := by field_simp
    rw [this]; nlinarith
  have h2 := logb_le_mul_pow _ (2 * 10 ^ 14) Y 48 1 (by positivity) hY1 (by norm_num) h1
  push_cast at h2
  linarith

/-- **The CORDIC words of the bounded regime**: for the decoder scale
`κ = bdScale s c₀ η σ θ ε₄ = γ √s c₀/η` and the accuracy `ζ = ε/(2·10¹⁴ Q)`, with `c₀`, `η`, `μ` of
bit length `b_data` and `√σ = √s μ/η`, `cordicWords k b κ ζ ≤ 62 B`. -/
theorem bd_words_le {k b sb s bd : ℕ} {c0 η μ σ θ ε₄ Q ε B : ℝ} (hsb : sb ≤ k)
    (hs : s = 2 ^ sb) (hbd : b ≤ bd) (hc0 : HasBits bd c0) (hc0p : 0 < c0) (hηb : HasBits bd η)
    (hηp : 0 < η) (hμb : HasBits bd μ) (hμp : 0 < μ) (hσ : (s : ℝ) * μ ^ 2 = σ * η ^ 2)
    (hσ1 : 1 ≤ σ) (hθ : 0 ≤ θ) (hε₄ : 0 < ε₄) (hε₄1 : ε₄ ≤ 1) (hQ : 1 ≤ Q) (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hB1 : 1 ≤ B) (hBk : (k : ℝ) ≤ B) (hBd : (bd : ℝ) ≤ B)
    (hB : Real.logb 2 ((Q + 1) / ε) ≤ B) :
    (cordicWords k b (GateOptimalBinary.bdScale s c0 η σ θ ε₄) (ε / (2 * 10 ^ 14 * Q)) : ℝ) ≤
      62 * B := by
  obtain ⟨hγ0, hγ1, hγσ, -⟩ :=
    GateOptimalPrecision.bdGamma_spec (σ := σ) (θ := θ) (ε := ε₄) ⟨hσ1, hθ, hε₄, hε₄1⟩
  set γ := GateOptimalPrecision.bdGamma σ θ ε₄ with hγ
  set κ := GateOptimalBinary.bdScale s c0 η σ θ ε₄ with hκ
  have hκe : κ = γ * Real.sqrt s * (c0 / η) := rfl
  have hs1 : (1 : ℝ) ≤ s := by rw [hs]; exact_mod_cast Nat.one_le_two_pow
  have hsk : (s : ℝ) ≤ 2 ^ k := by
    rw [hs]; exact_mod_cast Nat.pow_le_pow_right (by norm_num) hsb
  have hsq : Real.sqrt (s : ℝ) ≤ 2 ^ k := (sqrt_le_self_of_one_le hs1).trans hsk
  have hsq0 : 0 < Real.sqrt (s : ℝ) := Real.sqrt_pos.2 (by linarith)
  have hc0' : c0 ≤ 2 ^ bd := hc0.lt.le
  have hμ' : μ ≤ 2 ^ bd := hμb.lt.le
  have hηi : 1 / η ≤ 2 ^ bd := by
    rw [div_le_iff₀ hηp]; have := hηb.one_le_mul hηp; linarith
  have hc0i : 1 / c0 ≤ 2 ^ bd := by
    rw [div_le_iff₀ hc0p]; have := hc0.one_le_mul hc0p; linarith
  have hκp : 0 < κ := by rw [hκe]; positivity
  -- `κ ≤ 2^(k + 2 b_data)`
  have hκu : κ ≤ 2 ^ (k + 2 * bd) := by
    rw [hκe]
    have h1 : c0 / η ≤ 2 ^ bd * 2 ^ bd := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul hc0' hηi (by positivity) (by positivity)
    have h2 : γ * Real.sqrt s ≤ 2 ^ k := by
      have := mul_le_mul_of_nonneg_right hγ1 hsq0.le
      linarith
    calc γ * Real.sqrt s * (c0 / η) ≤ 2 ^ k * (2 ^ bd * 2 ^ bd) :=
          mul_le_mul h2 h1 (by positivity) (by positivity)
      _ = 2 ^ (k + 2 * bd) := by ring
  -- `1/κ ≤ 2^(2 b_data)`
  have hσq : Real.sqrt σ = Real.sqrt s * (μ / η) :=
    GateOptimalBinary.sqrt_sigma_eq hηp hμp.le hσ
  have hκl : c0 / μ ≤ κ := by
    rw [hκe]
    have h1 : 1 ≤ γ * Real.sqrt s * (μ / η) := by
      have e : γ * Real.sqrt σ = γ * Real.sqrt s * (μ / η) := by rw [hσq]; ring
      linarith
    have e : γ * Real.sqrt s * (c0 / η) = (γ * Real.sqrt s * (μ / η)) * (c0 / μ) := by
      field_simp
    rw [e]
    exact le_mul_of_one_le_left (by positivity) h1
  have hκi : 1 / κ ≤ 2 ^ (2 * bd) := by
    have h1 : 1 / κ ≤ μ / c0 := by
      rw [div_le_div_iff₀ hκp hc0p]
      have := mul_le_mul_of_nonneg_left hκl hμp.le
      have e : μ * (c0 / μ) = c0 := by field_simp
      linarith
    have h2 : μ / c0 ≤ 2 ^ bd * 2 ^ bd := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul hμ' hc0i (by positivity) (by positivity)
    calc 1 / κ ≤ 2 ^ bd * 2 ^ bd := h1.trans h2
      _ = 2 ^ (2 * bd) := by ring
  have wκ : (Nat.clog 2 ⌈κ⌉₊ : ℝ) ≤ k + 2 * bd := by
    have := clog_ceil_le_nat _ _ hκu; exact_mod_cast this
  have wκi : (Nat.clog 2 ⌈1 / κ⌉₊ : ℝ) ≤ 2 * bd := by
    have := clog_ceil_le_nat _ _ hκi; exact_mod_cast this
  -- the CORDIC steps
  set Y := (Q + 1) / ε with hY
  have hY1 : 1 ≤ Y := one_le_div_of_le (by linarith) hε hε1
  have hz : 8 / (ε / (2 * 10 ^ 14 * Q)) ≤ 16 * 10 ^ 14 * Y ^ 1 := by
    rw [pow_one, div_div_eq_mul_div, hY, div_le_iff₀ hε]
    have : 16 * 10 ^ 14 * ((Q + 1) / ε) * ε = 16 * 10 ^ 14 * (Q + 1) := by field_simp
    rw [this]; nlinarith
  have wn : (Cordic.nOf (ε / (2 * 10 ^ 14 * Q)) : ℝ) ≤ 54 + B := by
    have h := clog_le_mul_pow _ (16 * 10 ^ 14) Y 51 1 hY1 (by norm_num) hz
    unfold Cordic.nOf
    push_cast at h ⊢
    linarith
  have hw : (cordicWords k b κ (ε / (2 * 10 ^ 14 * Q)) : ℝ) = k + b +
      (Cordic.nOf (ε / (2 * 10 ^ 14 * Q)) : ℝ) + (Nat.clog 2 ⌈κ⌉₊ : ℝ) +
        (Nat.clog 2 ⌈1 / κ⌉₊ : ℝ) := by
    unfold cordicWords; push_cast; ring
  have hb' : (b : ℝ) ≤ bd := by exact_mod_cast hbd
  rw [hw]
  linarith

/-- **The per-call gates and the work wires of the bounded regime** are at most
`(14 + 57000·63³) B³` and `(300 + 1231·63³) B³`. -/
theorem bd_cost_le {k b sb s bd : ℕ} {c0 η μ σ θ ε₄ Q ε B : ℝ} (hsb : sb ≤ k)
    (hs : s = 2 ^ sb) (hbd : b ≤ bd) (hc0 : HasBits bd c0) (hc0p : 0 < c0) (hηb : HasBits bd η)
    (hηp : 0 < η) (hμb : HasBits bd μ) (hμp : 0 < μ) (hσ : (s : ℝ) * μ ^ 2 = σ * η ^ 2)
    (hσ1 : 1 ≤ σ) (hθ : 0 ≤ θ) (hε₄ : 0 < ε₄) (hε₄1 : ε₄ ≤ 1) (hQ : 1 ≤ Q) (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hB1 : 1 ≤ B) (hBk : (k : ℝ) ≤ B) (hBd : (bd : ℝ) ≤ B)
    (hB : Real.logb 2 ((Q + 1) / ε) ≤ B) :
    (GateOptimalBinary.bdNativeCost k b sb s c0 η σ θ ε₄ (ε / (2 * 10 ^ 14 * Q)) : ℝ) ≤
        (14 + 57000 * 63 ^ 3) * B ^ 3 ∧
    ((Fintype.card (SZ k b) +
        (binArith k b (GateOptimalBinary.bdScale s c0 η σ θ ε₄) (ε / (2 * 10 ^ 14 * Q))).bT +
        (binArith k b (GateOptimalBinary.bdScale s c0 η σ θ ε₄) (ε / (2 * 10 ^ 14 * Q))).bP +
        (binArith k b (GateOptimalBinary.bdScale s c0 η σ θ ε₄) (ε / (2 * 10 ^ 14 * Q))).A :
          ℕ) : ℝ) ≤ (300 + 1231 * 63 ^ 3) * B ^ 3 := by
  set κ := GateOptimalBinary.bdScale s c0 η σ θ ε₄ with hκ
  set ζ := ε / (2 * 10 ^ 14 * Q) with hζ
  have hU := bd_words_le hsb hs hbd hc0 hc0p hηb hηp hμb hμp hσ hσ1 hθ hε₄ hε₄1 hQ hε hε1 hB1
    hBk hBd hB
  set U := cordicWords k b κ ζ with hUdef
  have hU0 : (0 : ℝ) ≤ U := Nat.cast_nonneg _
  have hB3 : B ≤ B ^ 3 := le_self_pow₀ hB1 (by norm_num)
  have hU1 : (U : ℝ) + 1 ≤ 63 * B := by linarith
  have hU3 : ((U : ℝ) + 1) ^ 3 ≤ 63 ^ 3 * B ^ 3 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by linarith) hU1 3
  have hsbB : (sb : ℝ) ≤ B := by
    have : (sb : ℝ) ≤ k := by exact_mod_cast hsb
    linarith
  constructor
  · -- the gates
    have hc := cordic_words k b (valX k b) (valY k b) κ ζ
    have e : GateOptimalBinary.bdNativeCost k b sb s c0 η σ θ ε₄ ζ = 7 * (sb + 1) +
        (2 * (28 * k) + 2 * (cordicArith b (valX k b) (valY k b) κ ζ).circ.length +
          (2 * (cordicArith b (valX k b) (valY k b) κ ζ).bP +
            (cordicArith b (valX k b) (valY k b) κ ζ).bT + 1)) := rfl
    rw [e]
    have hc' : ((2 * (28 * k) + 2 * (cordicArith b (valX k b) (valY k b) κ ζ).circ.length +
        (2 * (cordicArith b (valX k b) (valY k b) κ ζ).bP +
          (cordicArith b (valX k b) (valY k b) κ ζ).bT + 1) : ℕ) : ℝ) ≤
        57000 * ((U : ℝ) + 1) ^ 3 := by exact_mod_cast hc
    have h57 : 57000 * ((U : ℝ) + 1) ^ 3 ≤ 57000 * (63 ^ 3 * B ^ 3) :=
      mul_le_mul_of_nonneg_left hU3 (by norm_num)
    push_cast at hc' ⊢
    linarith
  · -- the work wires
    obtain ⟨-, hA, hT, hP⟩ := cordicArith_counts b (valX k b) (valY k b) κ ζ
    obtain ⟨hn, hbT, hbP, hw⟩ := params_fields b κ ζ
    have hW := GateODEBudget.wordOf_le (Cordic.nOf ζ)
    have hg2 : Cordic.g2Of (Cordic.nOf ζ) κ = Nat.clog 2 ⌈κ⌉₊ + Cordic.nOf ζ + 5 := by
      unfold Cordic.g2Of; rfl
    have hlk : Cordic.lkOf κ = Nat.clog 2 ⌈1 / κ⌉₊ := by
      unfold Cordic.lkOf; rfl
    have hu : U = k + b + Cordic.nOf ζ + Nat.clog 2 ⌈κ⌉₊ + Nat.clog 2 ⌈1 / κ⌉₊ := rfl
    have hnu : Cordic.nOf ζ ≤ U := by rw [hu]; omega
    have hWc : (Cordic.params b κ ζ).w ≤ 37 * ((U + 1) * (U + 1)) := by
      rw [hw, hg2, hlk]
      have e : (U + 1) * (U + 1) = U * U + 2 * U + 1 := by ring
      rw [e]
      have hNN : Cordic.nOf ζ * Cordic.nOf ζ ≤ U * U := Nat.mul_le_mul hnu hnu
      have h1 : Nat.clog 2 ⌈κ⌉₊ + Nat.clog 2 ⌈1 / κ⌉₊ + b ≤ U := by rw [hu]; omega
      omega
    obtain ⟨-, h2⟩ := GateODEBudget.arith_poly 0 0 (Cordic.params b κ ζ).w
      (Cordic.params b κ ζ).n (Cordic.wordOf (Cordic.nOf ζ)) U (by omega) (by omega) hWc
      (by rw [hn]; exact hnu) (by omega)
    have hbin : binArith k b κ ζ = cordicArith b (valX k b) (valY k b) κ ζ := rfl
    rw [hbin, card_SZ, hA, hT, hP, hbT, hbP]
    have hA' : 1 + 2 * (Cordic.params b κ ζ).w +
        (6 * ((Cordic.params b κ ζ).n + 1) + 1) * (Cordic.params b κ ζ).w ≤
        1231 * (U + 1) ^ 3 := by omega
    have hA'' : ((1 + 2 * (Cordic.params b κ ζ).w +
        (6 * ((Cordic.params b κ ζ).n + 1) + 1) * (Cordic.params b κ ζ).w : ℕ) : ℝ) ≤
        1231 * ((U : ℝ) + 1) ^ 3 := by exact_mod_cast hA'
    have hWr : (Cordic.wordOf (Cordic.nOf ζ) : ℝ) ≤ 2 * U + 5 := by
      have : Cordic.wordOf (Cordic.nOf ζ) ≤ 2 * U + 5 := by omega
      exact_mod_cast this
    have hkb : ((6 * k + 2 * b : ℕ) : ℝ) ≤ 8 * B := by
      have hb' : (b : ℝ) ≤ bd := by exact_mod_cast hbd
      push_cast; linarith
    have h1231 : 1231 * ((U : ℝ) + 1) ^ 3 ≤ 1231 * (63 ^ 3 * B ^ 3) :=
      mul_le_mul_of_nonneg_left hU3 (by norm_num)
    push_cast at hA'' hkb ⊢
    linarith

/-- **The per-call gates of the signed-factor regime** for an arithmetic with
`|circ| + b_T + b_P + A ≤ P`: `sgNativeCost ≤ 74 B + 5 P`. -/
theorem sg_cost_le {k sb b bT bP A : ℕ} {κ ξ B P : ℝ}
    (ar : GateOptimalBinary.FactorWordArith b κ ξ bT bP A) (hsb : (sb : ℝ) ≤ B)
    (hk : (k : ℝ) ≤ B) (hB1 : 1 ≤ B)
    (hP : ((ar.circ.length + bT + bP + A : ℕ) : ℝ) ≤ P) :
    (GateOptimalBinary.sgNativeCost k sb ar : ℝ) ≤ 74 * B + 5 * P := by
  have e : GateOptimalBinary.sgNativeCost k sb ar =
      7 * (sb + 1) + (2 * (28 * k) + 2 * ar.circ.length + (2 * bP + bT + 4)) := rfl
  rw [e]
  have h1 : 2 * ar.circ.length + (2 * bP + bT + 4) ≤ 5 * (ar.circ.length + bT + bP + A) + 4 := by
    omega
  have h1' : ((2 * ar.circ.length + (2 * bP + bT + 4) : ℕ) : ℝ) ≤
      5 * ((ar.circ.length + bT + bP + A : ℕ) : ℝ) + 4 := by exact_mod_cast h1
  push_cast at h1' hP ⊢
  linarith

/-- **The per-call gates of the clipped regime** for arithmetic with
`|circ_f| + |circ_a| + b_T + b_P + A ≤ P`: `clNativeCost ≤ 198 B + 15 P`. -/
theorem cl_cost_le {k sb b bT bP A : ℕ} {μ β q c0 ξ ζ B P : ℝ}
    (af : GateOptimalBinary.ClipFactorArith b μ β c0 ξ bT bP A)
    (aa : GateOptimalBinary.ClipAngleArith b μ β q c0 ζ bT bP A) (hsb : (sb : ℝ) ≤ B)
    (hk : (k : ℝ) ≤ B) (hB1 : 1 ≤ B)
    (hP : ((af.circ.length + aa.circ.length + bT + bP + A : ℕ) : ℝ) ≤ P) :
    (GateOptimalBinary.clNativeCost k sb af aa : ℝ) ≤ 198 * B + 15 * P := by
  have e : GateOptimalBinary.clNativeCost k sb af aa =
      7 * (sb + 2) + (2 * (2 * (28 * k) + 2 * af.circ.length + (2 * bP + bT + 4)) +
        (2 * (28 * k) + 2 * aa.circ.length + (2 * bP + bT + 1))) := rfl
  rw [e]
  have h1 : 2 * (2 * af.circ.length + (2 * bP + bT + 4)) + (2 * aa.circ.length + (2 * bP + bT + 1))
      ≤ 15 * (af.circ.length + aa.circ.length + bT + bP + A) + 9 := by omega
  have h1' : ((2 * (2 * af.circ.length + (2 * bP + bT + 4)) +
      (2 * aa.circ.length + (2 * bP + bT + 1)) : ℕ) : ℝ) ≤
      15 * ((af.circ.length + aa.circ.length + bT + bP + A : ℕ) : ℝ) + 9 := by exact_mod_cast h1
  push_cast at h1' hP ⊢
  linarith

end Costs

/-! ### From the synthesis claims to the polynomial form -/

section Claims

variable {S Y J : Type*} [Fintype S] [DecidableEq S] [Fintype Y] [DecidableEq Y]
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- **The polynomial form of the synthesis claims.** For a synthesised circuit with the claims of
`GateOptimalBinary.SynthClaims` at the internal accuracy `ε/4`, the synthesis budget `ε/2` and the
count parameter `Q' ≤ 4Q`, with `a ≤ |S| + 4` ancillas, per-call gates `G ≤ c_G B^K` and work wires
`|Z| + b_T + b_P + A ≤ c_W B^K`, for every `B ≥ max(1, |S|, log₂((Q+1)/ε))`: at most
`Q c_N (c₁ (log(4 c_N) + K + 2) + c₀) B^{K+1}` gates (`c_N = 9·10¹⁵ + 8·10¹¹ c_G`), at most
`|S| + (630 + c_W) B^K + |X_a|` wires and at most `8·10¹¹ Q` times `calls p` primitive calls. -/
theorem claims_poly {prim : J → Reg Y R →L[ℂ] Reg Y R} {Z : Type*} [Fintype Z] [DecidableEq Z]
    {a m r K bT bP A : ℕ} {𝒢 : Set Kind} {Xa : Type*} [Fintype Xa] [DecidableEq Xa]
    {L : ℝ → ℕ} {ε' : ℝ} {C : List (NInstr (HW (Sim.Wire a m r K) S Empty Z bT bP A ⊕ Xa) Y J)}
    {H : Reg S R →L[ℂ] Reg S R} {t ε₄ Q' : ℝ} {calls : (J → Bool) → ℕ} {N G : ℕ} {δ : ℝ}
    (h : GateOptimalBinary.SynthClaims prim 𝒢 Xa L ε' C H t ε₄ Q' calls N G δ)
    {Q ε B cG cW c₀ c₁ : ℝ} {KG : ℕ} (hQ : 1 ≤ Q) (hQ' : 0 ≤ Q') (hQQ : Q' ≤ 4 * Q)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hε₄ : ε₄ = ε / 4) (hε' : ε' = ε / 2) (hB1 : 1 ≤ B)
    (hB : Real.logb 2 ((Q + 1) / ε) ≤ B) (hS : (Fintype.card S : ℝ) ≤ B)
    (ha : (a : ℝ) ≤ Fintype.card S + 4) (hKG : 1 ≤ KG) (hcG : 0 ≤ cG)
    (hG : (G : ℝ) ≤ cG * B ^ KG) (hW : ((Fintype.card Z + bT + bP + A : ℕ) : ℝ) ≤ cW * B ^ KG)
    (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁)
    (hL : ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 → (L ζ : ℝ) ≤ c₁ * Real.log (1 / ζ) + c₀) :
    (nGatesN C : ℝ) ≤ Q * (9 * 10 ^ 15 + 8 * 10 ^ 11 * cG) *
        (c₁ * (Real.log (4 * (9 * 10 ^ 15 + 8 * 10 ^ 11 * cG)) + KG + 2) + c₀) * B ^ (KG + 1) ∧
    (Fintype.card (HW (Sim.Wire a m r K) S Empty Z bT bP A ⊕ Xa) : ℝ) ≤
        Fintype.card S + (630 + cW) * B ^ KG + Fintype.card Xa ∧
    ∀ p, (nCallsN p C : ℝ) ≤ 8 * 10 ^ 11 * Q * calls p := by
  obtain ⟨hm, hr⟩ := mesh_label_words (m := m) (r := r) (by linarith) hQ' hQQ hε hε1 hB1 hB
    (by rw [← hε₄]; exact h.mesh) h.labels
  have hBK : B ≤ B ^ KG := le_self_pow₀ hB1 (by omega)
  have hBK1 : 1 ≤ B ^ KG := one_le_pow₀ hB1
  have hamr : (a : ℝ) + m + r + 1 ≤ 171 * B := by linarith
  have hG0 : (0 : ℝ) ≤ G := Nat.cast_nonneg _
  have hNbQ : 10 ^ 13 * (Q' + 1) * ((a : ℝ) + m + r + 1) + 2 * 10 ^ 11 * Q' * G ≤
      Q * (9 * 10 ^ 15 + 8 * 10 ^ 11 * cG) * B ^ KG := by
    have h1 : 10 ^ 13 * (Q' + 1) * ((a : ℝ) + m + r + 1) ≤ 10 ^ 13 * (5 * Q) * (171 * B) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) (by norm_num)) hamr (by positivity)
        (by positivity)
    have h2 : 2 * 10 ^ 11 * Q' * G ≤ 2 * 10 ^ 11 * (4 * Q) * (cG * B ^ KG) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hQQ (by norm_num)) hG hG0 (by positivity)
    have h3 : 10 ^ 13 * (5 * Q) * (171 * B) ≤ 9 * 10 ^ 15 * Q * B ^ KG := by
      have : Q * B ≤ Q * B ^ KG := mul_le_mul_of_nonneg_left hBK (by linarith)
      nlinarith
    have e : 2 * 10 ^ 11 * (4 * Q) * (cG * B ^ KG) = 8 * 10 ^ 11 * cG * (Q * B ^ KG) := by ring
    have e2 : Q * (9 * 10 ^ 15 + 8 * 10 ^ 11 * cG) * B ^ KG =
        9 * 10 ^ 15 * Q * B ^ KG + 8 * 10 ^ 11 * cG * (Q * B ^ KG) := by ring
    linarith
  have hNb0 : 0 ≤ 10 ^ 13 * (Q' + 1) * ((a : ℝ) + m + r + 1) + 2 * 10 ^ 11 * Q' * G := by
    positivity
  have hgates := h.gates_log hc₀ hc₁ hL (by rw [hε']; positivity) (by rw [hε']; linarith)
  rw [hε'] at hgates
  have hcN : (1 : ℝ) ≤ 9 * 10 ^ 15 + 8 * 10 ^ 11 * cG := by nlinarith
  have hfac := synth_factor (K := KG) hNb0 hQ hcN hB1 hε hε1 hB hc₀ hc₁ hNbQ
  refine ⟨hgates.trans hfac, ?_, fun p => ?_⟩
  · have hw : (Fintype.card (HW (Sim.Wire a m r K) S Empty Z bT bP A ⊕ Xa) : ℝ) ≤
        2 * a + 3 * m + 6 * r + 5 + Fintype.card S +
          (((Fintype.card Z + bT + bP + A : ℕ) : ℝ) + 3) + Fintype.card Xa := by
      have := h.wires
      have h' : ((Fintype.card (HW (Sim.Wire a m r K) S Empty Z bT bP A ⊕ Xa) : ℕ) : ℝ) ≤
          ((2 * a + 3 * m + 6 * r + 5 + Fintype.card S +
            (Fintype.card Z + bT + bP + A + 3) + Fintype.card Xa : ℕ) : ℝ) := by
        exact_mod_cast this
      push_cast at h' ⊢
      linarith
    nlinarith
  · have h1 := h.calls_le p
    have h2 : 2 * 10 ^ 11 * Q' * (calls p : ℝ) ≤ 8 * 10 ^ 11 * Q * calls p := by
      have : (0 : ℝ) ≤ calls p := Nat.cast_nonneg _
      nlinarith
    linarith

end Claims

/-! ### The computational assumptions of the signed and clipped regimes -/

/-- **The scalar-arithmetic assumption of the signed-factor regime** (Section `gate:sec:result`, the
paragraph before Theorem `gate:thm:main`): for the decoder scale `κ` of the normalised factor
entries and every accuracy `ξ ∈ (0, 1]`, a reversible factor arithmetic
(`GateOptimalBinary.FactorWordArith`: the angle word of `arcsin √|c|` to magnitude accuracy `ξ²`,
the phase word of `arg c` to accuracy `ξ`, work restored) with gates and work wires at most
`c_A (b_data + k + log₂(1/ξ) + 1)^{d_A}`. -/
def comp_signedArith (cA : ℝ) (dA : ℕ) (bd k b : ℕ) (κ : ℝ) : Prop :=
  ∀ ξ : ℝ, 0 < ξ → ξ ≤ 1 → ∃ (bT bP A : ℕ) (ar : GateOptimalBinary.FactorWordArith b κ ξ bT bP A),
    ((ar.circ.length + bT + bP + A : ℕ) : ℝ) ≤
      cA * ((bd : ℝ) + k + Real.logb 2 (1 / ξ) + 1) ^ dA

/-- **The scalar-arithmetic assumption of the clipped regime**: for the entry bound `μ`, the
clipping parameter `β`, the Cayley scale `q`, the decoder scale `c₀` and every accuracy
`ξ ∈ (0, 1]`, the factor arithmetic (`GateOptimalBinary.ClipFactorArith`) and the angle arithmetic
(`GateOptimalBinary.ClipAngleArith`, the angle words of `2 arctan |y|` and `arg y` to accuracy
`ξ`) on common work wires, with gates and work wires at most
`c_A (b_data + k + log₂(1/ξ) + 1)^{d_A}`. -/
def comp_clipArith (cA : ℝ) (dA : ℕ) (bd k b : ℕ) (μ β q c0 : ℝ) : Prop :=
  ∀ ξ : ℝ, 0 < ξ → ξ ≤ 1 → ∃ (bT bP A : ℕ)
    (af : GateOptimalBinary.ClipFactorArith b μ β c0 ξ bT bP A)
    (aa : GateOptimalBinary.ClipAngleArith b μ β q c0 ξ bT bP A),
    ((af.circ.length + aa.circ.length + bT + bP + A : ℕ) : ℝ) ≤
      cA * ((bd : ℝ) + k + Real.logb 2 (1 / ξ) + 1) ^ dA

/-- The clipping parameter `h = log(e + L/θ)` of the clipped construction, `θ = η²|t|/μ`, at its
internal accuracy `ε/4` (written `ε/2/2`). -/
def clipBeta (η μ t ε : ℝ) : ℝ :=
  LargeSparsityCore.Parameters.hval (η ^ 2 * |t| / μ) (ε / 2 / 2)

/-- The Cayley scale `q` of the clipped construction at its internal accuracy `ε/4`, with the
moment parameter `σ = sμ²/η²`. -/
def clipScale (s : ℕ) (η μ t ε : ℝ) : ℝ :=
  LargeSparsityCore.Parameters.qval ((s : ℝ) * μ ^ 2 / η ^ 2) (η ^ 2 * |t| / μ) (ε / 2 / 2)

/-! ### Theorem `gate:thm:main` -/

universe u v w

set_option maxHeartbeats 8000000 in
/-- **Theorem `gate:thm:main`: gate-efficient improved-precision
simulation.** Fix the computational assumptions (scalar arithmetic with gates and work at most
`c_A (b_data + k + log₂(1/ξ) + 1)^{d_A}` at accuracy `ξ`) and a finite gate set admitting
single-qubit synthesis of length at most `c₁ log(1/ζ) + c₀` at accuracy `ζ`, with an exact
decomposition of its controlled one-qubit gates. There are constants `C` and `K = max(3, d_A) + 1`
such that: for sparse data in the binary format (`formal_binaryInput`) whose stored components have
at most `b_data` bits and whose decoder scale `c0` and parameters `η`, `μ` have `b_data`-bit
descriptions (`comp_bits`), with the arithmetic assumption at the public scales of the
signed-factor and clipped constructions, `μ ≤ η ≤ √s μ`, `η²|t|/μ ≥ 1` and `0 < ε ≤ 1/64`, one
circuit over the gate set and the primitive sparse oracles, fixed before the instance, uses at
most `24·10¹² Q_μ` primitive sparse queries (eq. `gate:eq:query-scale`, an absolute constant), at
most `C Q_μ (𝔟 + 1)^K` gates with `𝔟 = b_data + log₂(N+1) + log₂(s+1) + log₂((Q_μ+1)/ε)` (eq.
`gate:eq:main-gates`), at most `k + C (𝔟 + 1)^K` qubits (the `k` system qubits and the auxiliary
qubits, polynomial in the same arguments), and on every instance whose matrix is Hermitian with row
and column Euclidean norms at most `η` and entries of modulus at most `μ` has full-output error at
most `ε` on the clean embedding (eq. `gate:eq:full`), with an untouched reference of any finite
dimension. Formal restrictions: `formal_binaryInput` (review item B). -/
theorem gate_thm_main (cA : ℝ) (dA : ℕ) (hcA : 0 ≤ cA) {c₀ c₁ : ℝ} (hc₀ : 0 ≤ c₀)
    (hc₁ : 0 ≤ c₁) (Kd : ℕ) {𝒢 : Set Kind} {X₁ X₂ : Type} [Fintype X₁] [DecidableEq X₁]
    [Fintype X₂] [DecidableEq X₂] {L : ℝ → ℕ}
    (ext_singleQubitSynthesis : OneQubitSynthesis 𝒢 X₁ L)
    (ext_singleQubitLength : ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 → (L ζ : ℝ) ≤ c₁ * Real.log (1 / ζ) + c₀)
    (ext_controlDecomposition : ControlDecomposition 𝒢 X₂ Kd) :
    ∃ (C : ℝ) (K : ℕ), 0 < C ∧
      ∀ {X : Type u} {n : Type v} [Fintype n] [DecidableEq n] {s k b : ℕ}
        (D : NativeSparseBlockEncoding.Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n)
        (sb bd : ℕ) (c0 η μ t ε : ℝ),
        formal_binaryInput D en sb c0 → comp_bits b bd [c0, η, μ] →
        comp_signedArith cA dA bd k b (c0 / μ) →
        comp_clipArith cA dA bd k b μ (clipBeta η μ t ε) (clipScale s η μ t ε) c0 →
        μ ≤ η → η ≤ Real.sqrt s * μ → 1 ≤ η ^ 2 * |t| / μ → 0 < ε → ε ≤ 1 / 64 →
        ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (sys : Fin k ↪ W)
          (Cc : List (NInstr W (PY k b) NativeSparseBlockEncoding.Query)),
          (∀ i ∈ Cc, i.Valid) ∧ (∀ g, NInstr.gate g ∈ Cc → GateOf 𝒢 g) ∧
          (nCallsN (fun _ => true) Cc : ℝ) ≤ 24 * 10 ^ 12 * twoNormBound s η μ t ε ∧
          (nGatesN Cc : ℝ) ≤ C * twoNormBound s η μ t ε *
            (gateWord bd (Fintype.card n) s (twoNormBound s η μ t ε) ε + 1) ^ K ∧
          (Fintype.card W : ℝ) ≤
            k + C * (gateWord bd (Fintype.card n) s (twoNormBound s η μ t ε) ε + 1) ^ K ∧
          ∀ {R : Type w} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
            [FiniteDimensional ℂ R] (x : X),
            (D.matrix x).IsHermitian → (∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) →
            (∀ j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) → (∀ i j, ‖D.matrix x i j‖ ≤ μ) →
            FullOutputError (nrun (prims (R := R) D en x) Cc) (cleanAlong sys)
              (NormedSpace.exp ((-Complex.I * (t : ℂ)) •
                qlift (R := R) en (SparseStateOverlap.matrixOperator (D.matrix x)))) ε := by
  obtain ⟨L', c₀', c₁', hc₀', hc₁', hS, hL'⟩ := synthesis_of_parts hc₀ hc₁
    ext_singleQubitSynthesis ext_singleQubitLength ext_controlDecomposition
  -- the constants
  set KG := max 3 dA with hKG
  set PA := cA * 52 ^ dA with hPA
  have hPA0 : 0 ≤ PA := by positivity
  set cG : ℝ := 14 + 57000 * 63 ^ 3 + 198 + 15 * PA with hcG
  set cW : ℝ := 300 + 1231 * 63 ^ 3 + 8 + PA with hcW
  set cN : ℝ := 9 * 10 ^ 15 + 8 * 10 ^ 11 * cG with hcN
  set Cg : ℝ := cN * (c₁' * (Real.log (4 * cN) + KG + 2) + c₀') with hCg
  have hcG0 : 0 ≤ cG := by positivity
  have hcW0 : 0 ≤ cW := by positivity
  have hcN1 : 1 ≤ cN := by rw [hcN]; nlinarith
  have hCg0 : 0 ≤ Cg := by
    have : 0 ≤ Real.log (4 * cN) := Real.log_nonneg (by linarith)
    positivity
  set C : ℝ := 24 * 10 ^ 12 + Cg + 630 + cW + Fintype.card (X₂ ⊕ X₁) with hC
  refine ⟨C, KG + 1, by positivity, ?_⟩
  intro X n _ _ s k b D en sb bd c0 η μ t ε hF hbits hsa hca hμη hηs hθ hε hε1
  obtain ⟨hbd, hc0b, hηb, hμb⟩ := hbits
  -- the parameters
  have hμ0 : 0 < μ := by
    by_contra h
    have h' : μ ≤ 0 := not_lt.mp h
    have : η ^ 2 * |t| / μ ≤ 0 :=
      div_nonpos_of_nonneg_of_nonpos (mul_nonneg (sq_nonneg η) (abs_nonneg t)) h'
    linarith
  have hη0 : 0 < η := lt_of_lt_of_le hμ0 hμη
  set σ : ℝ := (s : ℝ) * μ ^ 2 / η ^ 2 with hσdef
  set θ : ℝ := η ^ 2 * |t| / μ with hθdef
  have hσ : (s : ℝ) * μ ^ 2 = σ * η ^ 2 := by rw [hσdef]; field_simp
  obtain ⟨-, -, hs0, hσ1, hST, hSq⟩ := GateOptimalPrecision.two_norm_params hμη hηs hσ rfl hθ
  set Q := twoNormBound s η μ t ε with hQdef
  have hQmu : GateOptimalPrecision.Qmu s η μ t ε = Q := qmu_eq s η μ t ε
  have hQ1 : 1 ≤ Q := by
    rw [← hQmu, GateOptimalPrecision.Qmu_eq rfl hST hSq]
    have h1 : 1 ≤ Real.sqrt σ := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hσ1
    have h2 : 1 ≤ Real.sqrt σ * θ := one_le_mul_of_one_le_of_one_le h1 hθ
    have h3 := OptimalSparseSimulation.r_pos hθ hε hε1
    have h4 := Real.sqrt_nonneg (σ * θ * LargeSparsityCore.Parameters.rval θ ε)
    linarith
  have hε1' : ε ≤ 1 := by linarith
  have hε2 : 0 < ε / 2 := by positivity
  -- the budget word
  set B := gateWord bd (Fintype.card n) s Q ε + 1 with hBdef
  have hcard : Fintype.card n = 2 ^ k := card_eq_two_pow en
  have hY1 : 1 ≤ (Q + 1) / ε := one_le_div_of_le (by linarith) hε hε1'
  have hlogN : (k : ℝ) ≤ Real.logb 2 ((Fintype.card n : ℝ) + 1) := by
    rw [hcard]; exact nat_le_logb k
  have hlogs : 0 ≤ Real.logb 2 ((s : ℝ) + 1) :=
    logb_nonneg_of_one_le (by have := Nat.cast_nonneg (α := ℝ) s; linarith)
  have hlogY : 0 ≤ Real.logb 2 ((Q + 1) / ε) := logb_nonneg_of_one_le hY1
  have hbd0 : (0 : ℝ) ≤ bd := Nat.cast_nonneg _
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hB1 : 1 ≤ B := by rw [hBdef]; unfold gateWord; linarith
  have hBk : (k : ℝ) ≤ B := by rw [hBdef]; unfold gateWord; linarith
  have hBd : (bd : ℝ) ≤ B := by rw [hBdef]; unfold gateWord; linarith
  have hBY : Real.logb 2 ((Q + 1) / ε) ≤ B := by rw [hBdef]; unfold gateWord; linarith
  have hsbB : (sb : ℝ) ≤ B := by
    have : (sb : ℝ) ≤ k := by exact_mod_cast hF.hsb
    linarith
  have hBK : 1 ≤ B ^ KG := one_le_pow₀ hB1
  have hB3K : B ^ 3 ≤ B ^ KG := pow_le_pow_right₀ hB1 (le_max_left 3 dA)
  have hBdK : B ^ dA ≤ B ^ KG := pow_le_pow_right₀ hB1 (le_max_right 3 dA)
  have hB1K : B ≤ B ^ KG := le_self_pow₀ hB1 (by omega)
  have hKK : B ^ KG ≤ B ^ (KG + 1) := pow_le_pow_right₀ hB1 (by omega)
  -- the arithmetic accuracy
  set ξ : ℝ := ε / (2 * 10 ^ 14 * Q) with hξdef
  have hξ0 : 0 < ξ := by positivity
  have hξ1 : ξ ≤ 1 := by
    rw [hξdef, div_le_one (by positivity)]; nlinarith
  have hlogξ : Real.logb 2 (1 / ξ) ≤ 49 * B := logb_inv_xi_le hQ1 hε hε1' hB1 hBY
  have hPb : cA * ((bd : ℝ) + k + Real.logb 2 (1 / ξ) + 1) ^ dA ≤ PA * B ^ KG := by
    have h1 : 0 ≤ (bd : ℝ) + k + Real.logb 2 (1 / ξ) + 1 := by
      have : 0 ≤ Real.logb 2 (1 / ξ) :=
        logb_nonneg_of_one_le (by rw [le_div_iff₀ hξ0]; linarith)
      linarith
    have h2 : (bd : ℝ) + k + Real.logb 2 (1 / ξ) + 1 ≤ 52 * B := by linarith
    have h3 : ((bd : ℝ) + k + Real.logb 2 (1 / ξ) + 1) ^ dA ≤ (52 * B) ^ dA :=
      pow_le_pow_left₀ h1 h2 dA
    rw [mul_pow] at h3
    have h4 : cA * ((bd : ℝ) + k + Real.logb 2 (1 / ξ) + 1) ^ dA ≤ cA * (52 ^ dA * B ^ dA) :=
      mul_le_mul_of_nonneg_left h3 hcA
    have h5 : cA * (52 ^ dA * B ^ dA) ≤ PA * B ^ KG := by
      rw [hPA, mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hBdK (by positivity)) hcA
    linarith
  -- the internal accuracy and the error budget
  have hP : GateOptimalBinary.MainParams s η μ t (ε / 2 / 2) σ θ :=
    ⟨hμη, hηs, hσ, rfl, hθ, by positivity, by linarith⟩
  have hQh : GateOptimalPrecision.Qmu s η μ t (ε / 2) ≤ 2 * Q := by
    rw [← hQmu]
    exact GateOptimalPrecision.Qmu_half_le hη0.le hμ0 (by linarith) hε (by linarith)
  have hQh0 : 0 ≤ GateOptimalPrecision.Qmu s η μ t (ε / 2) :=
    GateOptimalPrecision.Qmu_nonneg rfl hST hSq hθ hε2 (by linarith)
  have hδε : 8 * 10 ^ 11 * GateOptimalPrecision.Qmu s η μ t (ε / 2) * (6 * ξ + 4 * ξ) ≤ ε / 2 := by
    have e : 6 * ξ + 4 * ξ = 10 * ε / (2 * 10 ^ 14 * Q) := by rw [hξdef]; ring
    rw [e]
    have hQ0 : 0 < Q := by linarith
    have h1 : 8 * 10 ^ 11 * GateOptimalPrecision.Qmu s η μ t (ε / 2) * (10 * ε / (2 * 10 ^ 14 * Q))
        ≤ 8 * 10 ^ 11 * (2 * Q) * (10 * ε / (2 * 10 ^ 14 * Q)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hQh (by norm_num)) (by positivity)
    have e2 : 8 * 10 ^ 11 * (2 * Q) * (10 * ε / (2 * 10 ^ 14 * Q)) = 8 * ε / 100 := by
      field_simp; ring
    linarith
  -- the arithmetic of the signed and clipped regimes
  obtain ⟨bT, bP, A, ar, har⟩ := hsa ξ hξ0 hξ1
  obtain ⟨bT', bP', A', af, aa, haf⟩ := hca ξ hξ0 hξ1
  -- the promises
  let Prom : X → Prop := fun x => (D.matrix x).IsHermitian ∧
    (∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) ∧ (∀ j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) ∧
    (∀ i j, ‖D.matrix x i j‖ ≤ μ)
  have hI : ∀ x, Prom x → GateOptimalBinary.BinaryInput D en sb c0 x η μ := fun x hx =>
    ⟨hF.hsb, hF.hs, hF.range, hF.hb, hF.hc0, hF.dec, hx.1, hx.2.1, hx.2.2.1, hx.2.2.2⟩
  have hQ'0 : 0 ≤ 2 * GateOptimalPrecision.Qmu s η μ t (ε / 2) := by linarith
  have hQ'4 : 2 * GateOptimalPrecision.Qmu s η μ t (ε / 2) ≤ 4 * Q := by linarith
  have hε₄ : ε / 2 / 2 = ε / 4 := by ring
  have hεε : ε / 2 + ε / 2 = ε := by ring
  have hS' : (Fintype.card (Fin k) : ℝ) ≤ B := by rw [Fintype.card_fin]; exact hBk
  by_cases hx : ∃ x, Prom x
  swap
  · -- no admissible instance: the empty circuit
    refine ⟨Fin k, inferInstance, inferInstance, Function.Embedding.refl _, [], by simp, by simp,
      ?_, ?_, ?_, fun x hH hrow hcol hent => absurd ⟨x, hH, hrow, hcol, hent⟩ hx⟩
    · simp only [nCallsN, List.countP_nil, Nat.cast_zero]; positivity
    · simp only [nGatesN, List.countP_nil, Nat.cast_zero]; positivity
    · rw [Fintype.card_fin]
      have : 0 ≤ C * B ^ (KG + 1) := by positivity
      linarith
  obtain ⟨x₀, hx₀⟩ := hx
  have hcalls5 := GateOptimalBinary.computeV_calls_total k b
  by_cases hbd' : LargeSparsityCore.Parameters.hval θ (ε / 2 / 2) < 10 ^ 4
  · -- the bounded regime
    have key : ∀ {R : Type w} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
        [FiniteDimensional ℂ R] (x : X), Prom x →
        GateOptimalBinary.SynthClaims (prims (R := R) D en x) 𝒢 (X₂ ⊕ X₁) L' (ε / 2)
          (synthBudget hS (ε / 2)
            (GateOptimalBinary.bdNativeCircuit k b sb hF.hsb s c0 η σ θ (ε / 2 / 2) ξ t))
          (GateOptimalBinary.sysH (R := R) D en x) t (ε / 2 / 2)
          (2 * GateOptimalPrecision.Qmu s η μ t (ε / 2)) (fun p => 2 * nCallsN p (computeV k b))
          (nGatesN (GateOptimalBinary.bdNativeCircuit k b sb hF.hsb s c0 η σ θ (ε / 2 / 2) ξ t))
          (GateOptimalBinary.bdNativeCost k b sb s c0 η σ θ (ε / 2 / 2) ξ) (ε / 2 + ε / 2) := by
      intro R _ _ _ _ x hxp
      rcases GateOptimalBinary.gate_optimal_binary_synth (R := R) (hI x hxp) hP hξ0.le hξ0 hξ1 hδε
          (fun _ _ => ar) (fun _ => af) (fun _ => aa) hS hε2 with
        ⟨-, h⟩ | ⟨h1, -, -⟩ | ⟨Rg, -⟩
      · exact h
      · exact absurd h1 (not_le.mpr hbd')
      · exact absurd Rg.h_large (not_le.mpr hbd')
    obtain ⟨hG, hW⟩ := bd_cost_le (θ := θ) (ε₄ := ε / 2 / 2) hF.hsb hF.hs hbd hc0b hF.hc0 hηb hη0
      hμb hμ0 hσ hσ1 (by linarith) (by positivity) (by linarith) hQ1 hε hε1' hB1 hBk hBd hBY
    rw [← hξdef] at hG hW
    have hG' : (GateOptimalBinary.bdNativeCost k b sb s c0 η σ θ (ε / 2 / 2) ξ : ℝ) ≤
        cG * B ^ KG := by
      have h1 : (14 + 57000 * 63 ^ 3 : ℝ) * B ^ 3 ≤ (14 + 57000 * 63 ^ 3) * B ^ KG :=
        mul_le_mul_of_nonneg_left hB3K (by norm_num)
      have h2 : (14 + 57000 * 63 ^ 3 : ℝ) * B ^ KG ≤ cG * B ^ KG :=
        mul_le_mul_of_nonneg_right (by rw [hcG]; linarith) (by positivity)
      linarith
    have hW' : ((Fintype.card (SZ k b) +
        (binArith k b (GateOptimalBinary.bdScale s c0 η σ θ (ε / 2 / 2)) ξ).bT +
        (binArith k b (GateOptimalBinary.bdScale s c0 η σ θ (ε / 2 / 2)) ξ).bP +
        (binArith k b (GateOptimalBinary.bdScale s c0 η σ θ (ε / 2 / 2)) ξ).A : ℕ) : ℝ) ≤
        cW * B ^ KG := by
      have h1 : (300 + 1231 * 63 ^ 3 : ℝ) * B ^ 3 ≤ (300 + 1231 * 63 ^ 3) * B ^ KG :=
        mul_le_mul_of_nonneg_left hB3K (by norm_num)
      have h2 : (300 + 1231 * 63 ^ 3 : ℝ) * B ^ KG ≤ cW * B ^ KG :=
        mul_le_mul_of_nonneg_right (by rw [hcW]; linarith) (by positivity)
      linarith
    obtain ⟨hgates, hcardW, hcalls⟩ := claims_poly
      (key (R := EuclideanSpace ℂ (ULift.{w} (Fin 1))) x₀ hx₀) (KG := KG) (cG := cG)
      (cW := cW) hQ1 hQ'0 hQ'4 hε hε1' hε₄ rfl hB1 hBY hS'
      (by rw [Fintype.card_fin]; push_cast; linarith) (by omega) hcG0 hG' hW' hc₀' hc₁' hL'
    refine ⟨_, inferInstance, inferInstance, sysWire _ _ _ _ _ _ _ _,
      synthBudget hS (ε / 2)
        (GateOptimalBinary.bdNativeCircuit k b sb hF.hsb s c0 η σ θ (ε / 2 / 2) ξ t),
      (key (R := EuclideanSpace ℂ (ULift.{w} (Fin 1))) x₀ hx₀).valid, (key (R := EuclideanSpace ℂ (ULift.{w} (Fin 1))) x₀ hx₀).gateset, ?_, ?_, ?_, ?_⟩
    · have h1 := hcalls (fun _ => true)
      rw [hcalls5] at h1
      push_cast at h1
      have : 0 ≤ Q := by linarith
      nlinarith
    · have : Q * cN * (c₁' * (Real.log (4 * cN) + KG + 2) + c₀') * B ^ (KG + 1) ≤
          C * Q * B ^ (KG + 1) := by
        have hle : Cg ≤ C := by rw [hC]; have := Nat.cast_nonneg (α := ℝ) (Fintype.card (X₂ ⊕ X₁)); linarith
        have e : Q * cN * (c₁' * (Real.log (4 * cN) + KG + 2) + c₀') * B ^ (KG + 1) =
            Cg * (Q * B ^ (KG + 1)) := by rw [hCg]; ring
        rw [e]
        have : 0 ≤ Q * B ^ (KG + 1) := by positivity
        nlinarith
      exact hgates.trans this
    · rw [Fintype.card_fin] at hcardW
      have hle : 630 + cW + Fintype.card (X₂ ⊕ X₁) ≤ C := by rw [hC]; linarith
      have hX0 : (0 : ℝ) ≤ Fintype.card (X₂ ⊕ X₁) := Nat.cast_nonneg _
      have h1 : (630 + cW) * B ^ KG + Fintype.card (X₂ ⊕ X₁) ≤
          (630 + cW + Fintype.card (X₂ ⊕ X₁)) * B ^ (KG + 1) := by
        have h2 : (630 + cW) * B ^ KG ≤ (630 + cW) * B ^ (KG + 1) :=
          mul_le_mul_of_nonneg_left hKK (by linarith)
        have h3 : (Fintype.card (X₂ ⊕ X₁) : ℝ) ≤ Fintype.card (X₂ ⊕ X₁) * B ^ (KG + 1) :=
          le_mul_of_one_le_right hX0 (one_le_pow₀ hB1)
        nlinarith
      have h4 : (630 + cW + Fintype.card (X₂ ⊕ X₁)) * B ^ (KG + 1) ≤ C * B ^ (KG + 1) :=
        mul_le_mul_of_nonneg_right hle (by positivity)
      linarith
    · intro R _ _ _ _ x hH hrow hcol hent
      have h := (key (R := R) x ⟨hH, hrow, hcol, hent⟩).error
      rw [cleanEmb_sysEmb_io, hεε] at h
      exact fullOutputError_of_norm h
  by_cases hsg : σ * θ < LargeSparsityCore.Parameters.Lval (ε / 2 / 2) *
      LargeSparsityCore.Parameters.hval θ (ε / 2 / 2)
  · -- the signed-factor regime
    have hh : 10 ^ 4 ≤ LargeSparsityCore.Parameters.hval θ (ε / 2 / 2) := not_lt.mp hbd'
    have key : ∀ {R : Type w} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
        [FiniteDimensional ℂ R] (x : X), Prom x →
        GateOptimalBinary.SynthClaims (prims (R := R) D en x) 𝒢 (X₂ ⊕ X₁) L' (ε / 2)
          (synthBudget hS (ε / 2)
            (GateOptimalBinary.sgNativeCircuit k b sb hF.hsb s μ σ t (ε / 2 / 2) c0 ar))
          (GateOptimalBinary.sysH (R := R) D en x) t (ε / 2 / 2)
          (2 * GateOptimalPrecision.Qmu s η μ t (ε / 2)) (fun p => 2 * nCallsN p (computeV k b))
          (nGatesN (GateOptimalBinary.sgNativeCircuit k b sb hF.hsb s μ σ t (ε / 2 / 2) c0 ar))
          (GateOptimalBinary.sgNativeCost k sb ar) (ε / 2 + ε / 2) := by
      intro R _ _ _ _ x hxp
      rcases GateOptimalBinary.gate_optimal_binary_synth (R := R) (hI x hxp) hP hξ0.le hξ0 hξ1 hδε
          (fun _ _ => ar) (fun _ => af) (fun _ => aa) hS hε2 with
        ⟨h0, -⟩ | ⟨-, -, h⟩ | ⟨Rg, -⟩
      · exact absurd h0 (not_lt.mpr hh)
      · exact h
      · exact absurd Rg.core (not_le.mpr hsg)
    have hG : (GateOptimalBinary.sgNativeCost k sb ar : ℝ) ≤ cG * B ^ KG := by
      have h1 := sg_cost_le ar hsbB hBk hB1 (har.trans hPb)
      have h3 : (74 + 5 * PA) * B ^ KG ≤ cG * B ^ KG :=
        mul_le_mul_of_nonneg_right (by rw [hcG]; linarith) (by positivity)
      have e : (74 + 5 * PA) * B ^ KG = 74 * B ^ KG + 5 * (PA * B ^ KG) := by ring
      linarith
    have hW : ((Fintype.card (SZ k b) + bT + bP + A : ℕ) : ℝ) ≤ cW * B ^ KG := by
      have h1 : ((Fintype.card (SZ k b) + bT + bP + A : ℕ) : ℝ) ≤ 8 * B + PA * B ^ KG := by
        rw [card_SZ]
        have h2 := har.trans hPb
        have hb' : (b : ℝ) ≤ bd := by exact_mod_cast hbd
        push_cast at h2 ⊢
        have : (0 : ℝ) ≤ ar.circ.length := Nat.cast_nonneg _
        linarith
      have h3 : (8 + PA) * B ^ KG ≤ cW * B ^ KG :=
        mul_le_mul_of_nonneg_right (by rw [hcW]; linarith) (by positivity)
      have e : (8 + PA) * B ^ KG = 8 * B ^ KG + PA * B ^ KG := by ring
      linarith
    obtain ⟨hgates, hcardW, hcalls⟩ := claims_poly (key (R := EuclideanSpace ℂ (ULift.{w} (Fin 1))) x₀ hx₀) (KG := KG) (cG := cG)
      (cW := cW) hQ1 hQ'0 hQ'4 hε hε1' hε₄ rfl hB1 hBY hS'
      (by rw [Fintype.card_fin]; push_cast; linarith) (by omega) hcG0 hG hW hc₀' hc₁' hL'
    refine ⟨_, inferInstance, inferInstance, sysWire _ _ _ _ _ _ _ _,
      synthBudget hS (ε / 2)
        (GateOptimalBinary.sgNativeCircuit k b sb hF.hsb s μ σ t (ε / 2 / 2) c0 ar),
      (key (R := EuclideanSpace ℂ (ULift.{w} (Fin 1))) x₀ hx₀).valid, (key (R := EuclideanSpace ℂ (ULift.{w} (Fin 1))) x₀ hx₀).gateset, ?_, ?_, ?_, ?_⟩
    · have h1 := hcalls (fun _ => true)
      rw [hcalls5] at h1
      push_cast at h1
      have : 0 ≤ Q := by linarith
      nlinarith
    · have : Q * cN * (c₁' * (Real.log (4 * cN) + KG + 2) + c₀') * B ^ (KG + 1) ≤
          C * Q * B ^ (KG + 1) := by
        have hle : Cg ≤ C := by rw [hC]; have := Nat.cast_nonneg (α := ℝ) (Fintype.card (X₂ ⊕ X₁)); linarith
        have e : Q * cN * (c₁' * (Real.log (4 * cN) + KG + 2) + c₀') * B ^ (KG + 1) =
            Cg * (Q * B ^ (KG + 1)) := by rw [hCg]; ring
        rw [e]
        have : 0 ≤ Q * B ^ (KG + 1) := by positivity
        nlinarith
      exact hgates.trans this
    · rw [Fintype.card_fin] at hcardW
      have hle : 630 + cW + Fintype.card (X₂ ⊕ X₁) ≤ C := by rw [hC]; linarith
      have hX0 : (0 : ℝ) ≤ Fintype.card (X₂ ⊕ X₁) := Nat.cast_nonneg _
      have h1 : (630 + cW) * B ^ KG + Fintype.card (X₂ ⊕ X₁) ≤
          (630 + cW + Fintype.card (X₂ ⊕ X₁)) * B ^ (KG + 1) := by
        have h2 : (630 + cW) * B ^ KG ≤ (630 + cW) * B ^ (KG + 1) :=
          mul_le_mul_of_nonneg_left hKK (by linarith)
        have h3 : (Fintype.card (X₂ ⊕ X₁) : ℝ) ≤ Fintype.card (X₂ ⊕ X₁) * B ^ (KG + 1) :=
          le_mul_of_one_le_right hX0 (one_le_pow₀ hB1)
        nlinarith
      have h4 : (630 + cW + Fintype.card (X₂ ⊕ X₁)) * B ^ (KG + 1) ≤ C * B ^ (KG + 1) :=
        mul_le_mul_of_nonneg_right hle (by positivity)
      linarith
    · intro R _ _ _ _ x hH hrow hcol hent
      have h := (key (R := R) x ⟨hH, hrow, hcol, hent⟩).error
      rw [cleanEmb_sysEmb_io, hεε] at h
      exact fullOutputError_of_norm h
  · -- the clipped regime
    have Rg : LargeSparsityCore.Parameters.Regime σ θ (ε / 2 / 2) :=
      ⟨hσ1, hθ, by positivity, by linarith, not_lt.mp hbd', not_lt.mp hsg⟩
    have key : ∀ {R : Type w} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
        [FiniteDimensional ℂ R] (x : X), Prom x →
        GateOptimalBinary.SynthClaims (prims (R := R) D en x) 𝒢 (X₂ ⊕ X₁) L' (ε / 2)
          (synthBudget hS (ε / 2)
            (GateOptimalBinary.clNativeCircuit k b sb hF.hsb σ θ (ε / 2 / 2) t af aa))
          (GateOptimalBinary.sysH (R := R) D en x) t (ε / 2 / 2)
          (2 * GateOptimalPrecision.Qmu s η μ t (ε / 2)) (fun p => 6 * nCallsN p (computeV k b))
          (nGatesN (GateOptimalBinary.clNativeCircuit k b sb hF.hsb σ θ (ε / 2 / 2) t af aa))
          (GateOptimalBinary.clNativeCost k sb af aa) (ε / 2 + ε / 2) := by
      intro R _ _ _ _ x hxp
      rcases GateOptimalBinary.gate_optimal_binary_synth (R := R) (hI x hxp) hP hξ0.le hξ0 hξ1 hδε
          (fun _ _ => ar) (fun _ => af) (fun _ => aa) hS hε2 with
        ⟨h0, -⟩ | ⟨-, h2, -⟩ | ⟨-, h⟩
      · exact absurd h0 (not_lt.mpr Rg.h_large)
      · exact absurd h2 hsg
      · exact h
    have hG : (GateOptimalBinary.clNativeCost k sb af aa : ℝ) ≤ cG * B ^ KG := by
      have h1 := cl_cost_le af aa hsbB hBk hB1 (haf.trans hPb)
      have h3 : (198 + 15 * PA) * B ^ KG ≤ cG * B ^ KG :=
        mul_le_mul_of_nonneg_right (by rw [hcG]; linarith) (by positivity)
      have e : (198 + 15 * PA) * B ^ KG = 198 * B ^ KG + 15 * (PA * B ^ KG) := by ring
      linarith
    have hW : ((Fintype.card (SZ k b) + bT' + bP' + A' : ℕ) : ℝ) ≤ cW * B ^ KG := by
      have h1 : ((Fintype.card (SZ k b) + bT' + bP' + A' : ℕ) : ℝ) ≤ 8 * B + PA * B ^ KG := by
        rw [card_SZ]
        have h2 := haf.trans hPb
        have hb' : (b : ℝ) ≤ bd := by exact_mod_cast hbd
        push_cast at h2 ⊢
        have : (0 : ℝ) ≤ af.circ.length := Nat.cast_nonneg _
        have : (0 : ℝ) ≤ aa.circ.length := Nat.cast_nonneg _
        linarith
      have h3 : (8 + PA) * B ^ KG ≤ cW * B ^ KG :=
        mul_le_mul_of_nonneg_right (by rw [hcW]; linarith) (by positivity)
      have e : (8 + PA) * B ^ KG = 8 * B ^ KG + PA * B ^ KG := by ring
      linarith
    obtain ⟨hgates, hcardW, hcalls⟩ := claims_poly (key (R := EuclideanSpace ℂ (ULift.{w} (Fin 1))) x₀ hx₀) (KG := KG) (cG := cG)
      (cW := cW) hQ1 hQ'0 hQ'4 hε hε1' hε₄ rfl hB1 hBY hS'
      (by rw [Fintype.card_fin]; push_cast; linarith) (by omega) hcG0 hG hW hc₀' hc₁' hL'
    refine ⟨_, inferInstance, inferInstance, sysWire _ _ _ _ _ _ _ _,
      synthBudget hS (ε / 2)
        (GateOptimalBinary.clNativeCircuit k b sb hF.hsb σ θ (ε / 2 / 2) t af aa),
      (key (R := EuclideanSpace ℂ (ULift.{w} (Fin 1))) x₀ hx₀).valid, (key (R := EuclideanSpace ℂ (ULift.{w} (Fin 1))) x₀ hx₀).gateset, ?_, ?_, ?_, ?_⟩
    · have h1 := hcalls (fun _ => true)
      rw [hcalls5] at h1
      push_cast at h1
      have : 0 ≤ Q := by linarith
      nlinarith
    · have : Q * cN * (c₁' * (Real.log (4 * cN) + KG + 2) + c₀') * B ^ (KG + 1) ≤
          C * Q * B ^ (KG + 1) := by
        have hle : Cg ≤ C := by rw [hC]; have := Nat.cast_nonneg (α := ℝ) (Fintype.card (X₂ ⊕ X₁)); linarith
        have e : Q * cN * (c₁' * (Real.log (4 * cN) + KG + 2) + c₀') * B ^ (KG + 1) =
            Cg * (Q * B ^ (KG + 1)) := by rw [hCg]; ring
        rw [e]
        have : 0 ≤ Q * B ^ (KG + 1) := by positivity
        nlinarith
      exact hgates.trans this
    · rw [Fintype.card_fin] at hcardW
      have hle : 630 + cW + Fintype.card (X₂ ⊕ X₁) ≤ C := by rw [hC]; linarith
      have hX0 : (0 : ℝ) ≤ Fintype.card (X₂ ⊕ X₁) := Nat.cast_nonneg _
      have h1 : (630 + cW) * B ^ KG + Fintype.card (X₂ ⊕ X₁) ≤
          (630 + cW + Fintype.card (X₂ ⊕ X₁)) * B ^ (KG + 1) := by
        have h2 : (630 + cW) * B ^ KG ≤ (630 + cW) * B ^ (KG + 1) :=
          mul_le_mul_of_nonneg_left hKK (by linarith)
        have h3 : (Fintype.card (X₂ ⊕ X₁) : ℝ) ≤ Fintype.card (X₂ ⊕ X₁) * B ^ (KG + 1) :=
          le_mul_of_one_le_right hX0 (one_le_pow₀ hB1)
        nlinarith
      have h4 : (630 + cW + Fintype.card (X₂ ⊕ X₁)) * B ^ (KG + 1) ≤ C * B ^ (KG + 1) :=
        mul_le_mul_of_nonneg_right hle (by positivity)
      linarith
    · intro R _ _ _ _ x hH hrow hcol hent
      have h := (key (R := R) x ⟨hH, hrow, hcol, hent⟩).error
      rw [cleanEmb_sysEmb_io, hεε] at h
      exact fullOutputError_of_norm h

end

end ManuscriptConformance
