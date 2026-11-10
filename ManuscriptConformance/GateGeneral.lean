import ManuscriptConformance.GateGeneralDefs
import ManuscriptConformance.GateHamiltonian

/-!
# Conformance: the gate theorems for sparse access of general size

Theorems `gate:thm:main` and `hs:thm:gates` (eq. `hs:eq:gate-binary`) for the sparse access of the
manuscript in general sizes (`SparseHamiltonian.GeneralSparseAccess.QData`, Section
`hs:sec:control`): an `N × N` matrix with `s`-sparse lists, `1 ≤ s ≤ N`, on index registers of
`k = ⌈log₂ N⌉` qubits (`2^{k-1} < N ≤ 2^k`), locators prescribed on valid list inputs only (any
unitary action elsewhere), the value oracle XOR-writing a stored word on every pair of index words
(the manuscript gives XOR-writing as an example and stores words for the valid pairs), and the
evolution on the index register of the matrix extended by zero to the index words `≥ N`
(`QData.padMat`). Both are derived from the binary endpoints (`gate_thm_main`, `hs_thm_gates`) on
the padded data (`QData.padData`: `k + 1`-bit index words, `2^⌈log₂ s⌉` slots): the circuit of the
padded data with every call replaced by its implementation from the supplied oracles
(`SparseHamiltonian.GeneralSparseAccess.implP`: masked and controlled locators with a reference,
the value oracle with a validity flag, at most three supplied calls each) and the implementation
gates synthesised over the gate set (`genCirc`). The query counts have absolute constants; the
gate and qubit constants depend on the gate set and, for `gate:thm:main`, on the arithmetic.

The formal restriction `formal_binaryInput` of the binary endpoints is replaced by
`formal_binaryDecoder` (review item B2): the stored words are `b`-bit two's complement pairs read by
the public decoder `c0 (X + iY)`. The sizes `N`, `s` and the locator lists are general.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4096

namespace ManuscriptConformance

noncomputable section
open ContinuousLinearMap SparseHamiltonian SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
  SparseHamiltonian.GateSynth SparseHamiltonian.GateBinary SparseHamiltonian.GateBitBudget
  SparseHamiltonian.GeneralSparseAccess
open scoped InnerProduct

/-! ### The decoder of the general sparse data -/

/-- **The binary decoder** (review item B2): the stored words of the general sparse data are pairs
of `b`-bit two's complement words, `b > 0`, read by the public decoder `c0 (X + iY)`, `c0 > 0`. -/
structure BinaryDecoder {X : Type*} {N s k b : ℕ} (D : GeneralSparseAccess.QData X N s k b)
    (c0 : ℝ) : Prop where
  hb : 0 < b
  hc0 : 0 < c0
  dec : ∀ z, D.val z = (c0 : ℂ) * gauss z

/-- **`formal_binaryDecoder`** (review item B2): the decoder of the general sparse data is
`c0 (X + iY)` on `b`-bit two's complement words (`BinaryDecoder`). -/
abbrev formal_binaryDecoder {X : Type*} {N s k b : ℕ} (D : GeneralSparseAccess.QData X N s k b)
    (c0 : ℝ) : Prop :=
  BinaryDecoder D c0

theorem BinaryDecoder.zero {X : Type*} {N s k b : ℕ} {D : GeneralSparseAccess.QData X N s k b}
    {c0 : ℝ} (h : BinaryDecoder D c0) : D.val (fun _ => false) = 0 := by
  rw [h.dec, gauss_false, mul_zero]

/-! ### Real estimates -/

section Real

/-- `√x ≤ 2 √y` for `x ≤ 4 y`. -/
theorem sqrt_le_two_mul_sqrt {x y : ℝ} (_hy : 0 ≤ y) (h : x ≤ 4 * y) :
    Real.sqrt x ≤ 2 * Real.sqrt y := by
  calc Real.sqrt x ≤ Real.sqrt (4 * y) := Real.sqrt_le_sqrt h
    _ = 2 * Real.sqrt y := by
        rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 * 2 by norm_num,
          Real.sqrt_mul_self (by norm_num)]

/-- `k ≤ log₂(N + 1) + 1` for `2^k < 2N`. -/
theorem k_le_logb {k N : ℕ} (hk : 2 ^ k < 2 * N) : (k : ℝ) ≤ Real.logb 2 ((N : ℝ) + 1) + 1 := by
  have h1 : (2 : ℝ) ^ k ≤ 2 * ((N : ℝ) + 1) := by
    have : ((2 ^ k : ℕ) : ℝ) < ((2 * N : ℕ) : ℝ) := by exact_mod_cast hk
    push_cast at this
    linarith
  have h2 := Real.logb_le_logb_of_le one_lt_two (by positivity) h1
  rw [Real.logb_pow, Real.logb_self_eq_one one_lt_two, mul_one,
    Real.logb_mul (by norm_num) (by positivity), Real.logb_self_eq_one one_lt_two] at h2
  linarith

/-- `log₂(2^{k+1} + 1) ≤ log₂(N + 1) + 2` for `2^k < 2N`. -/
theorem logb_pow_succ_le {k N : ℕ} (hk : 2 ^ k < 2 * N) :
    Real.logb 2 (((2 ^ (k + 1) : ℕ) : ℝ) + 1) ≤ Real.logb 2 ((N : ℝ) + 1) + 2 := by
  have h1 : ((2 ^ (k + 1) : ℕ) : ℝ) + 1 ≤ 2 ^ 2 * ((N : ℝ) + 1) := by
    have : 2 ^ (k + 1) ≤ 4 * N := by rw [pow_succ]; omega
    have h' : ((2 ^ (k + 1) : ℕ) : ℝ) ≤ ((4 * N : ℕ) : ℝ) := by exact_mod_cast this
    rw [Nat.cast_mul, Nat.cast_ofNat] at h'
    linarith
  have h2 := Real.logb_le_logb_of_le one_lt_two (by positivity) h1
  rw [Real.logb_mul (by norm_num) (by positivity), Real.logb_pow,
    Real.logb_self_eq_one one_lt_two] at h2
  simp only [Nat.cast_ofNat] at h2
  linarith

/-- `log₂(2^⌈log₂ s⌉ + 1) ≤ log₂(s + 1) + 1`. -/
theorem logb_sP_le {s : ℕ} (hs : 0 < s) :
    Real.logb 2 (((sP s : ℕ) : ℝ) + 1) ≤ Real.logb 2 ((s : ℝ) + 1) + 1 := by
  have h1 : ((sP s : ℕ) : ℝ) + 1 ≤ 2 * ((s : ℝ) + 1) := by
    have h' : ((sP s : ℕ) : ℝ) ≤ ((2 * s : ℕ) : ℝ) := by exact_mod_cast (sP_lt hs).le
    push_cast at h'
    linarith
  have h2 := Real.logb_le_logb_of_le one_lt_two (by positivity) h1
  rw [Real.logb_mul (by norm_num) (by positivity), Real.logb_self_eq_one one_lt_two] at h2
  linarith

/-- `log₂((Q' + 1)/(ε/2)) ≤ log₂((Q + 1)/ε) + 3` for `0 ≤ Q' ≤ 4Q`. -/
theorem logb_scale_le {Q Q' ε : ℝ} (hQ' : 0 ≤ Q') (hQQ : Q' ≤ 4 * Q) (hε : 0 < ε) :
    Real.logb 2 ((Q' + 1) / (ε / 2)) ≤ Real.logb 2 ((Q + 1) / ε) + 3 := by
  have hQ : 0 ≤ Q := by linarith
  have h1 : (Q' + 1) / (ε / 2) ≤ 2 ^ 3 * ((Q + 1) / ε) := by
    rw [div_le_iff₀ (by positivity)]
    have e : 2 ^ 3 * ((Q + 1) / ε) * (ε / 2) = 4 * (Q + 1) := by field_simp; ring
    rw [e]
    linarith
  have h2 := Real.logb_le_logb_of_le one_lt_two (by positivity) h1
  rw [Real.logb_mul (by norm_num) (by positivity), Real.logb_pow,
    Real.logb_self_eq_one one_lt_two] at h2
  push_cast at h2
  linarith

theorem logInv_nonneg {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) : 0 ≤ logInv ε :=
  Real.log_nonneg (by rw [le_div_iff₀ hε]; linarith)

/-- **The query shape of `hs:thm:main` at most doubles when the sparsity at most doubles.** -/
theorem mainBound_le_of_le {s s' τ ε : ℝ} (hs : 0 ≤ s) (_hs' : 0 ≤ s') (hss : s' ≤ 2 * s)
    (hτ : 0 ≤ τ) (hε : 0 < ε) (hε1 : ε ≤ 1) : mainBound s' τ ε ≤ 2 * mainBound s τ ε := by
  unfold mainBound
  have hL := logInv_nonneg hε hε1
  have h1 : Real.sqrt s' ≤ 2 * Real.sqrt s := sqrt_le_two_mul_sqrt hs (by linarith)
  have h2 : Real.sqrt (s' * τ * logInv ε) ≤ 2 * Real.sqrt (s * τ * logInv ε) := by
    apply sqrt_le_two_mul_sqrt (by positivity)
    have : s' * (τ * logInv ε) ≤ 4 * s * (τ * logInv ε) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    nlinarith
  have h3 : Real.sqrt s' * τ ≤ 2 * Real.sqrt s * τ := mul_le_mul_of_nonneg_right h1 hτ
  have h4 : 0 ≤ Real.sqrt (s * τ * logInv ε) := Real.sqrt_nonneg _
  have h5 : 0 ≤ Real.sqrt s * τ := by positivity
  nlinarith

/-- `q(2^⌈log₂ s⌉, ε/2) ≤ 4 q(s, ε)` for the query shape of `hs:thm:main`. -/
theorem mainBound_pad_le {s : ℕ} (hs : 0 < s) {τ ε : ℝ} (hτ : 0 ≤ τ) (hε : 0 < ε)
    (hε2 : ε ≤ 1 / 2) : mainBound (sP s) τ (ε / 2) ≤ 4 * mainBound s τ ε := by
  have hsP : ((sP s : ℕ) : ℝ) ≤ 2 * (s : ℝ) := by
    have h' : ((sP s : ℕ) : ℝ) ≤ ((2 * s : ℕ) : ℝ) := by exact_mod_cast (sP_lt hs).le
    push_cast at h'
    exact h'
  have h1 := mainBound_le_of_le (s := s) (s' := sP s) (Nat.cast_nonneg _) (Nat.cast_nonneg _) hsP
    hτ (by positivity : 0 < ε / 2) (by linarith)
  have h2 : mainBound s τ (ε / 2) ≤ 2 * mainBound s τ ε := by
    rw [← shape_eq_mainBound, ← shape_eq_mainBound]
    exact shape_half_le s hτ hε hε2
  linarith

/-- **The query scale `Q_μ` at most doubles when the sparsity at most doubles.** -/
theorem twoNormBound_le_of_le {s s' η μ t ε : ℝ} (hs : 0 ≤ s) (_hs' : 0 ≤ s') (hss : s' ≤ 2 * s)
    (hη : 0 ≤ η) (hμ : 0 ≤ μ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    twoNormBound s' η μ t ε ≤ 2 * twoNormBound s η μ t ε := by
  unfold twoNormBound
  have hL := logInv_nonneg hε hε1
  set h := Real.log (Real.exp 1 + μ * logInv ε / (η ^ 2 * |t|)) with hh
  have hh0 : 0 < h := by
    apply Real.log_pos
    have he : 1 < Real.exp 1 := by
      have := Real.add_one_le_exp 1
      linarith
    have : 0 ≤ μ * logInv ε / (η ^ 2 * |t|) := by positivity
    linarith
  have h1 : Real.sqrt s' ≤ 2 * Real.sqrt s := sqrt_le_two_mul_sqrt hs (by linarith)
  have h2 : Real.sqrt (s' * μ * |t| * logInv ε / h) ≤ 2 * Real.sqrt (s * μ * |t| * logInv ε / h) := by
    apply sqrt_le_two_mul_sqrt (by positivity)
    have hc : 0 ≤ μ * |t| * logInv ε / h := by positivity
    have : s' * (μ * |t| * logInv ε / h) ≤ 4 * s * (μ * |t| * logInv ε / h) :=
      mul_le_mul_of_nonneg_right (by linarith) hc
    have e1 : s' * μ * |t| * logInv ε / h = s' * (μ * |t| * logInv ε / h) := by ring
    have e2 : 4 * (s * μ * |t| * logInv ε / h) = 4 * s * (μ * |t| * logInv ε / h) := by ring
    rw [e1, e2]
    exact this
  have h3 : Real.sqrt s' * η * |t| ≤ 2 * Real.sqrt s * η * |t| := by
    have := mul_le_mul_of_nonneg_right h1 (by positivity : 0 ≤ η * |t|)
    nlinarith
  have h4 : 0 ≤ Real.sqrt (s * μ * |t| * logInv ε / h) := Real.sqrt_nonneg _
  have h5 : 0 ≤ Real.sqrt s * η * |t| := by positivity
  have h6 : 0 ≤ logInv ε / h := by positivity
  nlinarith

/-- **The gates of the general circuit**: the gates of the circuit of the padded data and, for each
of its calls, at most `implG k b ≤ 64 B` implementation gates, each synthesised with at most
`L ζ ≤ c₁ log(1/ζ) + c₀` gates at the accuracy `ζ = (ε/2)/(n + 1)`. -/
theorem gen_gates_le {Q B C₀ a c₀ c₁ ε : ℝ} {K : ℕ} (hK : 2 ≤ K) (hQ : 1 / 2 ≤ Q) (hB : 1 ≤ B)
    (hC₀ : 0 ≤ C₀) (ha : 0 ≤ a) (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hY : Real.logb 2 ((Q + 1) / ε) ≤ B) {nG nC G n : ℕ} {L : ℝ → ℕ}
    (hnG : (nG : ℝ) ≤ a * C₀ * Q * B ^ K) (hnC : (nC : ℝ) ≤ 4 * C₀ * Q) (hG : (G : ℝ) ≤ 64 * B)
    (hn : n ≤ nG + G * nC)
    (hL : ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 → (L ζ : ℝ) ≤ c₁ * Real.log (1 / ζ) + c₀) :
    ((nG + G * nC * (1 + L (ε / 2 / ((n : ℝ) + 1))) : ℕ) : ℝ) ≤
      (a + 256 * (1 + (c₁ * (Real.log (2 * ((a + 256) * C₀ + 2)) + K + 1) + c₀))) * C₀ * Q *
        B ^ K := by
  set cN := (a + 256) * C₀ with hcN
  set cL := c₁ * (Real.log (2 * (cN + 2)) + K + 1) + c₀ with hcL
  have hB1K : B ≤ B ^ K := le_self_pow₀ hB (by omega)
  have hB2K : B ^ 2 ≤ B ^ K := pow_le_pow_right₀ hB hK
  have hBK1 : 1 ≤ B ^ K := one_le_pow₀ hB
  have hQ0 : 0 < Q := by linarith
  have hcN0 : 0 ≤ cN := by positivity
  have hB0 : 0 ≤ B := by linarith
  -- the count `n`
  have hn' : (n : ℝ) ≤ cN * Q * B ^ K := by
    have h1 : (n : ℝ) ≤ nG + G * nC := by exact_mod_cast hn
    have h2 : (G : ℝ) * nC ≤ 64 * B * (4 * C₀ * Q) :=
      mul_le_mul hG hnC (Nat.cast_nonneg _) (by positivity)
    have h3 : 64 * B * (4 * C₀ * Q) ≤ 256 * C₀ * Q * B ^ K := by
      have : 256 * C₀ * Q * B ≤ 256 * C₀ * Q * B ^ K :=
        mul_le_mul_of_nonneg_left hB1K (by positivity)
      nlinarith
    have e : cN * Q * B ^ K = a * C₀ * Q * B ^ K + 256 * C₀ * Q * B ^ K := by rw [hcN]; ring
    rw [e]
    linarith
  -- the accuracy of the synthesis
  set ζ := ε / 2 / ((n : ℝ) + 1) with hζ
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hζ0 : 0 < ζ := by positivity
  have hζ1 : ζ ≤ 1 := by
    rw [hζ, div_le_one (by positivity)]
    linarith
  have hY1 : 1 ≤ (Q + 1) / ε := by rw [le_div_iff₀ hε]; linarith
  have hinv : 1 / ζ ≤ 2 * (cN + 2) * (B ^ K * ((Q + 1) / ε)) := by
    rw [hζ, one_div_div, div_le_iff₀ (by positivity)]
    have e : 2 * (cN + 2) * (B ^ K * ((Q + 1) / ε)) * (ε / 2) = (cN + 2) * B ^ K * (Q + 1) := by
      field_simp
    rw [e]
    have h1 : (n : ℝ) + 1 ≤ cN * Q * B ^ K + 2 * Q * B ^ K := by
      have : 1 ≤ 2 * Q * B ^ K := by nlinarith
      linarith
    have h2 : cN * Q * B ^ K + 2 * Q * B ^ K ≤ (cN + 2) * B ^ K * (Q + 1) := by
      have : 0 ≤ (cN + 2) * B ^ K := by positivity
      nlinarith
    linarith
  have hlog : Real.log (1 / ζ) ≤ (Real.log (2 * (cN + 2)) + K + 1) * B := by
    have hpos : 0 < 1 / ζ := by positivity
    have h1 := Real.log_le_log hpos hinv
    rw [Real.log_mul (x := 2 * (cN + 2)) (y := B ^ K * ((Q + 1) / ε)) (by positivity)
      (by positivity), Real.log_mul (x := B ^ K) (y := (Q + 1) / ε) (by positivity)
      (by positivity), Real.log_pow] at h1
    have hlogB : Real.log B ≤ B := by
      have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < B)
      linarith
    have hlogY : Real.log ((Q + 1) / ε) ≤ B := (log_le_logb _ hY1).trans hY
    have hl0 : 0 ≤ Real.log (2 * (cN + 2)) := Real.log_nonneg (by linarith)
    have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    have h2 : Real.log (2 * (cN + 2)) ≤ Real.log (2 * (cN + 2)) * B :=
      le_mul_of_one_le_right hl0 hB
    have h3 : (K : ℝ) * Real.log B ≤ K * B := mul_le_mul_of_nonneg_left hlogB hK0
    nlinarith
  have hLz : (L ζ : ℝ) ≤ cL * B := by
    have h1 := hL ζ hζ0 hζ1
    have h2 : c₁ * Real.log (1 / ζ) ≤ c₁ * ((Real.log (2 * (cN + 2)) + K + 1) * B) :=
      mul_le_mul_of_nonneg_left hlog hc₁
    have h3 : c₀ ≤ c₀ * B := le_mul_of_one_le_right hc₀ hB
    have e : cL * B = c₁ * ((Real.log (2 * (cN + 2)) + K + 1) * B) + c₀ * B := by rw [hcL]; ring
    rw [e]
    linarith
  -- the total
  have hcL0 : 0 ≤ cL := by
    have : 0 ≤ Real.log (2 * (cN + 2)) := Real.log_nonneg (by linarith)
    positivity
  push_cast
  have hGnC : (G : ℝ) * nC * (1 + L ζ) ≤ 64 * B * (4 * C₀ * Q) * (1 + cL * B) := by
    apply mul_le_mul (mul_le_mul hG hnC (Nat.cast_nonneg _) (by positivity)) (by linarith)
      (by positivity) (by positivity)
  have h4 : 64 * B * (4 * C₀ * Q) * (1 + cL * B) ≤ 256 * (1 + cL) * C₀ * Q * B ^ K := by
    have e : 64 * B * (4 * C₀ * Q) * (1 + cL * B) = 256 * C₀ * Q * (B + cL * B ^ 2) := by ring
    rw [e]
    have h5 : B + cL * B ^ 2 ≤ (1 + cL) * B ^ K := by
      have : cL * B ^ 2 ≤ cL * B ^ K := mul_le_mul_of_nonneg_left hB2K hcL0
      nlinarith
    calc 256 * C₀ * Q * (B + cL * B ^ 2) ≤ 256 * C₀ * Q * ((1 + cL) * B ^ K) :=
          mul_le_mul_of_nonneg_left h5 (by positivity)
      _ = 256 * (1 + cL) * C₀ * Q * B ^ K := by ring
  linarith

end Real

/-! ### Theorem `hs:thm:gates` in general sizes -/

universe u w

set_option maxHeartbeats 4000000 in
/-- **Theorem `hs:thm:gates`, eq. `hs:eq:gate-binary`, for sparse access of
general size.** For a finite gate set admitting single-qubit synthesis of length at most
`c₁ log(1/ζ) + c₀` and an exact decomposition of its controlled one-qubit gates, there is a
constant `C` such that: for sparse data of general size (`GeneralSparseAccess.QData`: an `N × N`
matrix with `s`-sparse lists, `1 ≤ s ≤ N`, on `k = ⌈log₂ N⌉`-qubit index registers, locators
prescribed on valid list inputs only, the value oracle XOR-writing a stored word on every pair of
index words) whose words are decoded as `c0 (X + iY)` (`formal_binaryDecoder`), whose stored
components have at most `b_data` bits and whose decoder scale `c0` and norm bound `η > 0` have
`b_data`-bit descriptions (`comp_bits`), every time `t` and `0 < ε ≤ 1/2`, one circuit over the
gate set and the supplied sparse oracles, fixed before the instance, uses at most
`6635520 Q_base` primitive sparse queries (an absolute constant), at most `C Q_base (𝔟 + 1)⁴`
gates with `Q_base = √s η|t| + √(s η|t| log(1/ε)) + log(1/ε)` and
`𝔟 = b_data + log₂(N+1) + log₂((Q_base+1)/ε)`, and
on every instance whose matrix is Hermitian with row and column Euclidean norms at most `η` has
full-output error at most `ε` on the clean embedding of the index register, against the evolution
of the matrix extended by zero to the index words `≥ N`, with an untouched reference. As in
eq. `hs:eq:gate-binary`, the work-qubit count of eq. `hs:eq:gate-total` is not stated. Formal
restrictions: `formal_binaryDecoder` (review item B2). -/
theorem hs_thm_gates_general {c₀ c₁ : ℝ} (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁) (Kd : ℕ) {𝒢 : Set Kind}
    {X₁ X₂ : Type} [Fintype X₁] [DecidableEq X₁] [Fintype X₂] [DecidableEq X₂] {L : ℝ → ℕ}
    (ext_singleQubitSynthesis : OneQubitSynthesis 𝒢 X₁ L)
    (ext_singleQubitLength : ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 → (L ζ : ℝ) ≤ c₁ * Real.log (1 / ζ) + c₀)
    (ext_controlDecomposition : ControlDecomposition 𝒢 X₂ Kd) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {X : Type u} {N s k b : ℕ} (D : GeneralSparseAccess.QData X N s k b) (bd : ℕ)
        (c0 η t ε : ℝ),
        2 ^ k < 2 * N → formal_binaryDecoder D c0 → comp_bits b bd [c0, η] →
        0 < η → 0 < ε → ε ≤ 1 / 2 →
        ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (sys : Fin k ↪ W)
          (Cc : List (NInstr W (PY k b) NativeSparseBlockEncoding.Query)),
          (∀ i ∈ Cc, i.Valid) ∧ (∀ g, NInstr.gate g ∈ Cc → GateOf 𝒢 g) ∧
          (nCallsN (fun _ => true) Cc : ℝ) ≤ 6635520 * mainBound s (η * |t|) ε ∧
          (nGatesN Cc : ℝ) ≤ C * mainBound s (η * |t|) ε *
            (bitH bd N (mainBound s (η * |t|) ε) ε + 1) ^ 4 ∧
          ∀ {R : Type w} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
            (x : X),
            (D.matrix x).IsHermitian → (∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) →
            (∀ j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) →
            FullOutputError (nrun (D.prims (R := R) x) Cc) (cleanAlong sys)
              (NormedSpace.exp ((-Complex.I * (t : ℂ)) •
                qlift (R := R) (Equiv.refl _) (SparseStateOverlap.matrixOperator (D.padMat x)))) ε := by
  obtain ⟨L', c₀', c₁', hc₀', hc₁', hS, hL'⟩ := synthesis_of_parts hc₀ hc₁
    ext_singleQubitSynthesis ext_singleQubitLength ext_controlDecomposition
  obtain ⟨C₀', hC₀', hbin⟩ := hs_thm_gates.{u, 0, w} hc₀ hc₁ Kd ext_singleQubitSynthesis
    ext_singleQubitLength ext_controlDecomposition
  -- one constant for the gates and the calls of the circuit of the padded data
  set C₀ : ℝ := C₀' + 552960 with hC₀def
  have hC₀ : 0 < C₀ := by rw [hC₀def]; linarith
  have hC₀le : C₀' ≤ C₀ := by rw [hC₀def]; linarith
  have hC₀c : (552960 : ℝ) ≤ C₀ := by rw [hC₀def]; linarith
  set a : ℝ := 4 * 6 ^ 4 with ha
  set cG : ℝ := (a + 256 * (1 + (c₁' * (Real.log (2 * ((a + 256) * C₀ + 2)) + ((4 : ℕ) : ℝ) + 1) +
    c₀'))) * C₀ with hcG
  have hcG0 : 0 ≤ cG := by
    have : 0 ≤ Real.log (2 * ((a + 256) * C₀ + 2)) := Real.log_nonneg (by nlinarith)
    positivity
  set C : ℝ := cG + 1 with hC
  refine ⟨C, by rw [hC]; linarith, ?_⟩
  intro X N s k b D bd c0 η t ε hk hF hbits hη hε hε2
  have hz₀ := hF.zero
  have hεh : 0 < ε / 2 := by positivity
  have hε1 : ε ≤ 1 := by linarith
  obtain ⟨W, _, _, sys, Cc, hv, hg, hcalls, hgates, herr⟩ :=
    hbin (D.padData (fun _ => false) hz₀) (Equiv.refl _) (sbP s) bd c0 η t (ε / 2)
      (padFormat D _ hz₀ hF.hb hF.hc0 hF.dec) hbits hη hεh (by linarith)
  -- the parameters
  set τ : ℝ := η * |t| with hτdef
  have hτ : 0 ≤ τ := by positivity
  set q := mainBound s τ ε with hqdef
  have hq2 : 1 / 2 ≤ q := by rw [hqdef, ← shape_eq_mainBound]; exact shape_ge_half s hτ hε hε2
  have hq0 : 0 < q := by linarith
  set q' := mainBound (sP s) τ (ε / 2) with hq'def
  have hq'q : q' ≤ 4 * q := mainBound_pad_le D.slots_pos hτ hε hε2
  have hq'0 : 0 ≤ q' := by
    have := shape_ge_half (sP s) hτ hεh (by linarith)
    rw [shape_eq_mainBound] at this
    linarith
  set B := bitH bd N q ε + 1 with hBdef
  have hY1 : 1 ≤ (q + 1) / ε := by rw [le_div_iff₀ hε]; linarith
  have hlogY : 0 ≤ Real.logb 2 ((q + 1) / ε) := Real.logb_nonneg one_lt_two hY1
  have hlogN : 0 ≤ Real.logb 2 ((N : ℝ) + 1) :=
    Real.logb_nonneg one_lt_two (by have := Nat.cast_nonneg (α := ℝ) N; linarith)
  have hbd0 : (0 : ℝ) ≤ bd := Nat.cast_nonneg _
  have hB1 : 1 ≤ B := by rw [hBdef]; unfold bitH; linarith
  have hBY : Real.logb 2 ((q + 1) / ε) ≤ B := by rw [hBdef]; unfold bitH; linarith
  have hBk : (k : ℝ) ≤ B := by
    have := k_le_logb hk
    rw [hBdef]; unfold bitH; linarith
  have hBb : (b : ℝ) ≤ B := by
    have : (b : ℝ) ≤ bd := by exact_mod_cast hbits.1
    rw [hBdef]; unfold bitH; linarith
  -- the word of the padded data
  have hcard : Fintype.card (Cfg (Fin (k + 1))) = 2 ^ (k + 1) := card_eq_two_pow (Equiv.refl _)
  have hB' : bitH bd (Fintype.card (Cfg (Fin (k + 1)))) q' (ε / 2) + 1 ≤ 6 * B := by
    rw [hcard]
    have h1 := logb_pow_succ_le hk
    have h2 := logb_scale_le hq'0 hq'q hε
    rw [hBdef]
    unfold bitH
    linarith
  have hB'0 : 0 ≤ bitH bd (Fintype.card (Cfg (Fin (k + 1)))) q' (ε / 2) + 1 := by
    have := bitH_nonneg bd (Fintype.card (Cfg (Fin (k + 1)))) hq'0 hεh (by linarith)
    linarith
  -- the counts of the circuit of the padded data
  have hq'c : (552960 : ℝ) * q' ≤ 552960 * (4 * q) := mul_le_mul_of_nonneg_left hq'q (by norm_num)
  have hnC : (nCallsN (fun _ => true) Cc : ℝ) ≤ 4 * C₀ * q := by
    have h1 : (552960 : ℝ) * (4 * q) ≤ C₀ * (4 * q) :=
      mul_le_mul_of_nonneg_right hC₀c (by linarith)
    linarith
  have hnG : (nGatesN Cc : ℝ) ≤ a * C₀ * q * B ^ 4 := by
    have h1 : (bitH bd (Fintype.card (Cfg (Fin (k + 1)))) q' (ε / 2) + 1) ^ 4 ≤ (6 * B) ^ 4 :=
      pow_le_pow_left₀ hB'0 hB' 4
    have h2 : C₀' * q' * (bitH bd (Fintype.card (Cfg (Fin (k + 1)))) q' (ε / 2) + 1) ^ 4 ≤
        C₀ * (4 * q) * (6 * B) ^ 4 :=
      mul_le_mul (mul_le_mul hC₀le hq'q hq'0 hC₀.le) h1 (by positivity) (by positivity)
    have e : C₀ * (4 * q) * (6 * B) ^ 4 = a * C₀ * q * B ^ 4 := by rw [ha]; ring
    linarith
  have hG : (implG k b : ℝ) ≤ 64 * B := by
    unfold implG
    push_cast
    linarith
  -- the accuracy of the synthesis
  set n := nGatesN (subst (implP N s (fun _ => false)) Cc) with hn
  set ζ : ℝ := ε / 2 / ((n : ℝ) + 1) with hζ
  have hζ0 : 0 < ζ := by positivity
  obtain ⟨hv', hg', hcalls', hgates', hn'⟩ :=
    genCirc_spec (N := N) (s := s) (fun _ => false) hS hζ0 Cc hv hg
  refine ⟨(W ⊕ GeneralSparseAccess.AW k b) ⊕ (X₂ ⊕ X₁), inferInstance, inferInstance,
    genSys (X₂ ⊕ X₁) sys, genCirc hS ζ N s (fun _ => false) Cc, hv', hg', ?_, ?_, ?_⟩
  · -- the calls
    have h1 : (nCallsN (fun _ => true) (genCirc hS ζ N s (fun _ => false) Cc) : ℝ) ≤
        3 * nCallsN (fun _ => true) Cc := by exact_mod_cast hcalls'
    linarith
  · -- the gates
    have h1 : (nGatesN (genCirc hS ζ N s (fun _ => false) Cc) : ℝ) ≤
        ((nGatesN Cc + implG k b * nCallsN (fun _ => true) Cc * (1 + L' ζ) : ℕ) : ℝ) := by
      exact_mod_cast hgates'
    have h2 : ((nGatesN Cc + implG k b * nCallsN (fun _ => true) Cc * (1 + L' ζ) : ℕ) : ℝ) ≤
        (a + 256 * (1 + (c₁' * (Real.log (2 * ((a + 256) * C₀ + 2)) + ((4 : ℕ) : ℝ) + 1) +
          c₀'))) * C₀ * q * B ^ 4 :=
      gen_gates_le (K := 4) (by norm_num) hq2 hB1 hC₀.le (by positivity) hc₀' hc₁' hε hε1
        hBY hnG hnC hG hn' hL'
    have h3 : cG * q * B ^ 4 ≤ C * q * B ^ 4 := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ hq0.le
      linarith
    have e : (a + 256 * (1 + (c₁' * (Real.log (2 * ((a + 256) * C₀ + 2)) + ((4 : ℕ) : ℝ) + 1) +
        c₀'))) * C₀ * q * B ^ 4 = cG * q * B ^ 4 := by rw [hcG]
    linarith
  · -- the error
    intro R _ _ _ x hH hrow hcol
    have h1 := herr (R := R) x (D.padData_isHermitian _ hz₀ x hH) (D.padData_row_le _ hz₀ x hrow)
      (D.padData_col_le _ hz₀ x hcol)
    have h2 := genCirc_error D (fun _ => false) hz₀ hS hζ0 sys Cc hv x t (ε / 2) hεh.le h1
    intro ψ hψ
    refine (h2 ψ hψ).trans ?_
    have h3 : (n : ℝ) * ζ ≤ ε / 2 := by
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
      rw [hζ, mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith
    linarith

/-! ### Theorem `gate:thm:main` in general sizes -/

section Main

/-- The arithmetic bound of the computational assumptions grows with the index width. -/
theorem arith_bound_succ {cA : ℝ} {dA bd k : ℕ} (hcA : 0 ≤ cA) {ξ : ℝ} (hξ : 0 < ξ)
    (hξ1 : ξ ≤ 1) :
    cA * ((bd : ℝ) + k + Real.logb 2 (1 / ξ) + 1) ^ dA ≤
      cA * ((bd : ℝ) + ((k + 1 : ℕ) : ℝ) + Real.logb 2 (1 / ξ) + 1) ^ dA := by
  have hl : 0 ≤ Real.logb 2 (1 / ξ) :=
    Real.logb_nonneg one_lt_two (by rw [le_div_iff₀ hξ]; linarith)
  apply mul_le_mul_of_nonneg_left _ hcA
  apply pow_le_pow_left₀ (by positivity) _ dA
  push_cast
  linarith

/-- The scalar arithmetic of the signed-factor regime at index width `k` serves width `k + 1`. -/
theorem comp_signedArith_succ {cA : ℝ} {dA bd k b : ℕ} {κ : ℝ} (hcA : 0 ≤ cA)
    (h : comp_signedArith cA dA bd k b κ) : comp_signedArith cA dA bd (k + 1) b κ := by
  intro ξ hξ hξ1
  obtain ⟨bT, bP, A, ar, har⟩ := h ξ hξ hξ1
  exact ⟨bT, bP, A, ar, har.trans (arith_bound_succ hcA hξ hξ1)⟩

/-- The scalar arithmetic of the clipped regime at index width `k` serves width `k + 1`. -/
theorem comp_clipArith_succ {cA : ℝ} {dA bd k b : ℕ} {μ β q c0 : ℝ} (hcA : 0 ≤ cA)
    (h : comp_clipArith cA dA bd k b μ β q c0) : comp_clipArith cA dA bd (k + 1) b μ β q c0 := by
  intro ξ hξ hξ1
  obtain ⟨bT, bP, A, af, aa, haf⟩ := h ξ hξ hξ1
  exact ⟨bT, bP, A, af, aa, haf.trans (arith_bound_succ hcA hξ hξ1)⟩

/-- **The clipping parameter of the general-size construction**: the clipped construction runs on
the padded data at accuracy `ε/2`. -/
def genClipBeta (η μ t ε : ℝ) : ℝ := clipBeta η μ t (ε / 2)

/-- **The Cayley scale of the general-size construction**: the clipped construction runs on the
padded data, with `2^⌈log₂ s⌉` slots, at accuracy `ε/2`. -/
def genClipScale (s : ℕ) (η μ t ε : ℝ) : ℝ := clipScale (sP s) η μ t (ε / 2)

/-- The first term `√s η|t|` of the query scale `Q_μ`. -/
theorem le_twoNormBound {s η μ t ε : ℝ} (_hs : 0 ≤ s) (_hη : 0 ≤ η) (hμ : 0 ≤ μ) (hε : 0 < ε)
    (hε1 : ε ≤ 1) : Real.sqrt s * η * |t| ≤ twoNormBound s η μ t ε := by
  unfold twoNormBound
  have hL := logInv_nonneg hε hε1
  have hh0 : 0 < Real.log (Real.exp 1 + μ * logInv ε / (η ^ 2 * |t|)) := by
    apply Real.log_pos
    have he : 1 < Real.exp 1 := by
      have := Real.add_one_le_exp 1
      linarith
    have : 0 ≤ μ * logInv ε / (η ^ 2 * |t|) := by positivity
    linarith
  have h1 := Real.sqrt_nonneg (s * μ * |t| * logInv ε /
    Real.log (Real.exp 1 + μ * logInv ε / (η ^ 2 * |t|)))
  have h2 : 0 ≤ logInv ε / Real.log (Real.exp 1 + μ * logInv ε / (η ^ 2 * |t|)) := by positivity
  linarith

set_option maxHeartbeats 8000000 in
/-- **Theorem `gate:thm:main` for sparse access of general size.** Fix the
computational assumptions (scalar arithmetic with gates and work at most
`c_A (b_data + k + log₂(1/ξ) + 1)^{d_A}` at accuracy `ξ`) and a finite gate set admitting
single-qubit synthesis of length at most `c₁ log(1/ζ) + c₀` at accuracy `ζ`, with an exact
decomposition of its controlled one-qubit gates. There are constants `C` and `K` such that: for
sparse data of general size (`GeneralSparseAccess.QData`: an `N × N` matrix with `s`-sparse lists,
`1 ≤ s ≤ N`, on `k = ⌈log₂ N⌉`-qubit index registers, locators prescribed on valid list inputs
only, the value oracle XOR-writing a stored word on every pair of index words) whose words are
decoded as `c0 (X + iY)` (`formal_binaryDecoder`), whose stored components have at most `b_data`
bits and whose decoder scale `c0` and parameters `η`, `μ` have `b_data`-bit descriptions
(`comp_bits`), with the arithmetic assumption at the public scales of the signed-factor and
clipped constructions (the clipped construction runs on the padded data, with `2^⌈log₂ s⌉` slots,
at accuracy `ε/2`: `genClipBeta`, `genClipScale`), `μ ≤ η ≤ √s μ`, `η²|t|/μ ≥ 1` and
`0 < ε ≤ 1/64`, one circuit over the gate set and the supplied sparse oracles, fixed before the
instance, uses at most `288·10¹² Q_μ` primitive sparse queries (an absolute constant), at most
`C Q_μ (𝔟 + 1)^K` gates with `𝔟 = b_data + log₂(N+1) + log₂(s+1) + log₂((Q_μ+1)/ε)`, at most
`k + C (𝔟 + 1)^K` qubits, and on every instance whose matrix is Hermitian with row and column
Euclidean norms at most `η` and entries of modulus at most `μ` has full-output error at most `ε`
on the clean embedding of the index register, against the evolution of the matrix extended by zero
to the index words `≥ N`, with an untouched reference of any finite dimension. `K = max(K₀, 2)`
for the exponent `K₀` supplied by `gate_thm_main`. Formal restrictions: `formal_binaryDecoder`
(review item B2). -/
theorem gate_thm_main_general (cA : ℝ) (dA : ℕ) (hcA : 0 ≤ cA) {c₀ c₁ : ℝ} (hc₀ : 0 ≤ c₀)
    (hc₁ : 0 ≤ c₁) (Kd : ℕ) {𝒢 : Set Kind} {X₁ X₂ : Type} [Fintype X₁] [DecidableEq X₁]
    [Fintype X₂] [DecidableEq X₂] {L : ℝ → ℕ}
    (ext_singleQubitSynthesis : OneQubitSynthesis 𝒢 X₁ L)
    (ext_singleQubitLength : ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 → (L ζ : ℝ) ≤ c₁ * Real.log (1 / ζ) + c₀)
    (ext_controlDecomposition : ControlDecomposition 𝒢 X₂ Kd) :
    ∃ (C : ℝ) (K : ℕ), 0 < C ∧
      ∀ {X : Type u} {N s k b : ℕ} (D : GeneralSparseAccess.QData X N s k b) (bd : ℕ)
        (c0 η μ t ε : ℝ),
        2 ^ k < 2 * N → formal_binaryDecoder D c0 → comp_bits b bd [c0, η, μ] →
        comp_signedArith cA dA bd k b (c0 / μ) →
        comp_clipArith cA dA bd k b μ (genClipBeta η μ t ε) (genClipScale s η μ t ε) c0 →
        μ ≤ η → η ≤ Real.sqrt s * μ → 1 ≤ η ^ 2 * |t| / μ → 0 < ε → ε ≤ 1 / 64 →
        ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (sys : Fin k ↪ W)
          (Cc : List (NInstr W (PY k b) NativeSparseBlockEncoding.Query)),
          (∀ i ∈ Cc, i.Valid) ∧ (∀ g, NInstr.gate g ∈ Cc → GateOf 𝒢 g) ∧
          (nCallsN (fun _ => true) Cc : ℝ) ≤ 288 * 10 ^ 12 * twoNormBound s η μ t ε ∧
          (nGatesN Cc : ℝ) ≤ C * twoNormBound s η μ t ε *
            (gateWord bd N s (twoNormBound s η μ t ε) ε + 1) ^ K ∧
          (Fintype.card W : ℝ) ≤
            k + C * (gateWord bd N s (twoNormBound s η μ t ε) ε + 1) ^ K ∧
          ∀ {R : Type w} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
            [FiniteDimensional ℂ R] (x : X),
            (D.matrix x).IsHermitian → (∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) →
            (∀ j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) → (∀ i j, ‖D.matrix x i j‖ ≤ μ) →
            FullOutputError (nrun (D.prims (R := R) x) Cc) (cleanAlong sys)
              (NormedSpace.exp ((-Complex.I * (t : ℂ)) •
                qlift (R := R) (Equiv.refl _) (SparseStateOverlap.matrixOperator (D.padMat x)))) ε := by
  obtain ⟨L', c₀', c₁', hc₀', hc₁', hS, hL'⟩ := synthesis_of_parts hc₀ hc₁
    ext_singleQubitSynthesis ext_singleQubitLength ext_controlDecomposition
  obtain ⟨C₀', K, hC₀', hbin⟩ := gate_thm_main.{u, 0, w} cA dA hcA hc₀ hc₁ Kd
    ext_singleQubitSynthesis ext_singleQubitLength ext_controlDecomposition
  -- one constant for the gates, the qubits and the calls of the circuit of the padded data
  set C₀ : ℝ := C₀' + 24 * 10 ^ 12 with hC₀def
  have hC₀ : 0 < C₀ := by rw [hC₀def]; linarith
  have hC₀le : C₀' ≤ C₀ := by rw [hC₀def]; linarith
  have hC₀c : (24 * 10 ^ 12 : ℝ) ≤ C₀ := by rw [hC₀def]; linarith
  set K' := max K 2 with hK'
  set a : ℝ := 4 * 7 ^ K' with ha
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  set cG : ℝ := (a + 256 * (1 + (c₁' * (Real.log (2 * ((a + 256) * C₀ + 2)) + (K' : ℝ) + 1) +
    c₀'))) * C₀ with hcG
  have hcG0 : 0 ≤ cG := by
    have h0 : 0 ≤ (a + 256) * C₀ := by positivity
    have : 0 ≤ Real.log (2 * ((a + 256) * C₀ + 2)) := Real.log_nonneg (by linarith)
    positivity
  set C : ℝ := cG + 7 ^ K' * C₀ + 16 + Fintype.card (X₂ ⊕ X₁) with hC
  have hX0 : (0 : ℝ) ≤ Fintype.card (X₂ ⊕ X₁) := Nat.cast_nonneg _
  have h7C : 0 ≤ 7 ^ K' * C₀ := by positivity
  refine ⟨C, K', by rw [hC]; linarith, ?_⟩
  intro X N s k b D bd c0 η μ t ε hk hF hbits hsa hca hμη hηs hθ hε hε64
  have hz₀ := hF.zero
  have hεh : 0 < ε / 2 := by positivity
  have hε1 : ε ≤ 1 := by linarith
  have hε2 : ε ≤ 1 / 2 := by linarith
  -- the parameters
  have hμ0 : 0 < μ := by
    by_contra h
    have h' : μ ≤ 0 := not_lt.mp h
    have : η ^ 2 * |t| / μ ≤ 0 :=
      div_nonpos_of_nonneg_of_nonpos (mul_nonneg (sq_nonneg η) (abs_nonneg t)) h'
    linarith
  have hη0 : 0 < η := lt_of_lt_of_le hμ0 hμη
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  have hsP : ((sP s : ℕ) : ℝ) ≤ 2 * (s : ℝ) := by
    have h' : ((sP s : ℕ) : ℝ) ≤ ((2 * s : ℕ) : ℝ) := by exact_mod_cast (sP_lt D.slots_pos).le
    push_cast at h'
    exact h'
  have hηs' : η ≤ Real.sqrt (sP s) * μ := by
    have h1 : Real.sqrt s ≤ Real.sqrt (sP s) :=
      Real.sqrt_le_sqrt (by exact_mod_cast le_sP s)
    have := mul_le_mul_of_nonneg_right h1 hμ0.le
    linarith
  obtain ⟨W, _, _, sys, Cc, hv, hg, hcalls, hgates, hwires, herr⟩ :=
    hbin (D.padData (fun _ => false) hz₀) (Equiv.refl _) (sbP s) bd c0 η μ t (ε / 2)
      (padFormat D _ hz₀ hF.hb hF.hc0 hF.dec) hbits (comp_signedArith_succ hcA hsa)
      (comp_clipArith_succ hcA hca) hμη hηs' hθ hεh (by linarith)
  set Q := twoNormBound s η μ t ε with hQdef
  set Q' := twoNormBound (sP s) η μ t (ε / 2) with hQ'def
  have hQ1 : 1 ≤ Q := by
    have h1 : η / μ ≤ Real.sqrt s := by rw [div_le_iff₀ hμ0]; linarith
    have h2 : η ^ 2 * |t| / μ = η / μ * (η * |t|) := by field_simp
    have h3 : η / μ * (η * |t|) ≤ Real.sqrt s * (η * |t|) :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    have h4 := le_twoNormBound (s := s) (t := t) hs0 hη0.le hμ0.le hε hε1
    nlinarith
  have hQ'0 : 0 ≤ Q' := by
    have := le_twoNormBound (s := sP s) (t := t) (Nat.cast_nonneg _) hη0.le hμ0.le hεh (by linarith)
    have : 0 ≤ Real.sqrt (sP s) * η * |t| := by positivity
    linarith
  have hQ'Q : Q' ≤ 4 * Q := by
    have h1 := twoNormBound_le_of_le (t := t) hs0 (Nat.cast_nonneg _) hsP hη0.le hμ0.le hεh
      (by linarith)
    have h2 : twoNormBound s η μ t (ε / 2) ≤ 2 * twoNormBound s η μ t ε := by
      rw [← qmu_eq, ← qmu_eq]
      exact GateOptimalPrecision.Qmu_half_le hη0.le hμ0 (by linarith) hε hε2
    linarith
  -- the budget word
  set B := gateWord bd N s Q ε + 1 with hBdef
  have hY1 : 1 ≤ (Q + 1) / ε := by rw [le_div_iff₀ hε]; linarith
  have hlogY : 0 ≤ Real.logb 2 ((Q + 1) / ε) := Real.logb_nonneg one_lt_two hY1
  have hlogN : 0 ≤ Real.logb 2 ((N : ℝ) + 1) :=
    Real.logb_nonneg one_lt_two (by have := Nat.cast_nonneg (α := ℝ) N; linarith)
  have hlogs : 0 ≤ Real.logb 2 ((s : ℝ) + 1) := Real.logb_nonneg one_lt_two (by linarith)
  have hbd0 : (0 : ℝ) ≤ bd := Nat.cast_nonneg _
  have hB1 : 1 ≤ B := by rw [hBdef]; unfold gateWord; linarith
  have hBY : Real.logb 2 ((Q + 1) / ε) ≤ B := by rw [hBdef]; unfold gateWord; linarith
  have hBk : (k : ℝ) ≤ B := by
    have := k_le_logb hk
    rw [hBdef]; unfold gateWord; linarith
  have hBb : (b : ℝ) ≤ B := by
    have : (b : ℝ) ≤ bd := by exact_mod_cast hbits.1
    rw [hBdef]; unfold gateWord; linarith
  have hBK : 1 ≤ B ^ K' := one_le_pow₀ hB1
  have hB1K : B ≤ B ^ K' := le_self_pow₀ hB1 (by omega)
  -- the word of the padded data
  have hcard : Fintype.card (Cfg (Fin (k + 1))) = 2 ^ (k + 1) := card_eq_two_pow (Equiv.refl _)
  have hB' : gateWord bd (Fintype.card (Cfg (Fin (k + 1)))) (sP s) Q' (ε / 2) + 1 ≤ 7 * B := by
    rw [hcard]
    have h1 := logb_pow_succ_le hk
    have h2 := logb_scale_le hQ'0 hQ'Q hε
    have h3 := logb_sP_le D.slots_pos
    rw [hBdef]
    unfold gateWord
    linarith
  have hB'0 : 0 ≤ gateWord bd (Fintype.card (Cfg (Fin (k + 1)))) (sP s) Q' (ε / 2) + 1 := by
    have hY' : 1 ≤ (Q' + 1) / (ε / 2) := by rw [le_div_iff₀ hεh]; linarith
    have h1 := Real.logb_nonneg one_lt_two hY'
    have hc0 : (0 : ℝ) ≤ ((Fintype.card (Cfg (Fin (k + 1))) : ℕ) : ℝ) := Nat.cast_nonneg _
    have h2 : 0 ≤ Real.logb 2 (((Fintype.card (Cfg (Fin (k + 1))) : ℕ) : ℝ) + 1) :=
      Real.logb_nonneg one_lt_two (by linarith)
    have hs0' : (0 : ℝ) ≤ ((sP s : ℕ) : ℝ) := Nat.cast_nonneg _
    have h3 : 0 ≤ Real.logb 2 (((sP s : ℕ) : ℝ) + 1) :=
      Real.logb_nonneg one_lt_two (by linarith)
    unfold gateWord
    linarith
  have hpow : (gateWord bd (Fintype.card (Cfg (Fin (k + 1)))) (sP s) Q' (ε / 2) + 1) ^ K ≤
      7 ^ K' * B ^ K' := by
    calc (gateWord bd (Fintype.card (Cfg (Fin (k + 1)))) (sP s) Q' (ε / 2) + 1) ^ K
        ≤ (7 * B) ^ K := pow_le_pow_left₀ hB'0 hB' K
      _ = 7 ^ K * B ^ K := mul_pow _ _ _
      _ ≤ 7 ^ K' * B ^ K' :=
          mul_le_mul (pow_le_pow_right₀ (by norm_num) (le_max_left K 2))
            (pow_le_pow_right₀ hB1 (le_max_left K 2)) (by positivity) (by positivity)
  -- the counts of the circuit of the padded data
  have hQ'c : (24 * 10 ^ 12 : ℝ) * Q' ≤ 24 * 10 ^ 12 * (4 * Q) :=
    mul_le_mul_of_nonneg_left hQ'Q (by norm_num)
  have hnC : (nCallsN (fun _ => true) Cc : ℝ) ≤ 4 * C₀ * Q := by
    have h1 : (24 * 10 ^ 12 : ℝ) * (4 * Q) ≤ C₀ * (4 * Q) :=
      mul_le_mul_of_nonneg_right hC₀c (by linarith)
    linarith
  have hnG : (nGatesN Cc : ℝ) ≤ a * C₀ * Q * B ^ K' := by
    have h2 : C₀' * Q' * (gateWord bd (Fintype.card (Cfg (Fin (k + 1)))) (sP s) Q' (ε / 2) + 1) ^ K ≤
        C₀ * (4 * Q) * (7 ^ K' * B ^ K') :=
      mul_le_mul (mul_le_mul hC₀le hQ'Q hQ'0 hC₀.le) hpow (by positivity) (by positivity)
    have e : C₀ * (4 * Q) * (7 ^ K' * B ^ K') = a * C₀ * Q * B ^ K' := by rw [ha]; ring
    linarith
  have hG : (implG k b : ℝ) ≤ 64 * B := by
    unfold implG
    push_cast
    linarith
  -- the accuracy of the synthesis
  set n := nGatesN (subst (implP N s (fun _ => false)) Cc) with hn
  set ζ : ℝ := ε / 2 / ((n : ℝ) + 1) with hζ
  have hζ0 : 0 < ζ := by positivity
  obtain ⟨hv', hg', hcalls', hgates', hn'⟩ :=
    genCirc_spec (N := N) (s := s) (fun _ => false) hS hζ0 Cc hv hg
  refine ⟨(W ⊕ GeneralSparseAccess.AW k b) ⊕ (X₂ ⊕ X₁), inferInstance, inferInstance,
    genSys (X₂ ⊕ X₁) sys, genCirc hS ζ N s (fun _ => false) Cc, hv', hg', ?_, ?_, ?_, ?_⟩
  · -- the calls
    have h1 : (nCallsN (fun _ => true) (genCirc hS ζ N s (fun _ => false) Cc) : ℝ) ≤
        3 * nCallsN (fun _ => true) Cc := by exact_mod_cast hcalls'
    linarith
  · -- the gates
    have h1 : (nGatesN (genCirc hS ζ N s (fun _ => false) Cc) : ℝ) ≤
        ((nGatesN Cc + implG k b * nCallsN (fun _ => true) Cc * (1 + L' ζ) : ℕ) : ℝ) := by
      exact_mod_cast hgates'
    have h2 : ((nGatesN Cc + implG k b * nCallsN (fun _ => true) Cc * (1 + L' ζ) : ℕ) : ℝ) ≤
        (a + 256 * (1 + (c₁' * (Real.log (2 * ((a + 256) * C₀ + 2)) + (K' : ℝ) + 1) +
          c₀'))) * C₀ * Q * B ^ K' :=
      gen_gates_le (K := K') (le_max_right K 2) (by linarith) hB1 hC₀.le (by positivity) hc₀'
        hc₁' hε hε1 hBY hnG hnC hG hn' hL'
    have h3 : cG * Q * B ^ K' ≤ C * Q * B ^ K' := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (by linarith)
      linarith
    have e : (a + 256 * (1 + (c₁' * (Real.log (2 * ((a + 256) * C₀ + 2)) + (K' : ℝ) + 1) +
        c₀'))) * C₀ * Q * B ^ K' = cG * Q * B ^ K' := by rw [hcG]
    linarith
  · -- the qubits
    have hcW : Fintype.card ((W ⊕ GeneralSparseAccess.AW k b) ⊕ (X₂ ⊕ X₁)) =
        Fintype.card W + (6 * k + 6 + 2 * b) + Fintype.card (X₂ ⊕ X₁) := by
      rw [Fintype.card_sum, Fintype.card_sum, card_AW]
    rw [hcW]
    push_cast
    have h1 : (Fintype.card W : ℝ) ≤ ((k + 1 : ℕ) : ℝ) + C₀ * (7 ^ K' * B ^ K') := by
      have h1a := mul_le_mul_of_nonneg_left hpow hC₀'.le
      have h1b : C₀' * (7 ^ K' * B ^ K') ≤ C₀ * (7 ^ K' * B ^ K') :=
        mul_le_mul_of_nonneg_right hC₀le (by positivity)
      linarith
    push_cast at h1
    have h2 : 6 * (k : ℝ) + 7 + 2 * b ≤ 15 * B ^ K' := by nlinarith
    have h3 : (Fintype.card (X₂ ⊕ X₁) : ℝ) ≤ Fintype.card (X₂ ⊕ X₁) * B ^ K' :=
      le_mul_of_one_le_right hX0 hBK
    have h4 : C₀ * (7 ^ K' * B ^ K') + 15 * B ^ K' + Fintype.card (X₂ ⊕ X₁) * B ^ K' ≤
        C * B ^ K' := by
      have e : C₀ * (7 ^ K' * B ^ K') + 15 * B ^ K' + Fintype.card (X₂ ⊕ X₁) * B ^ K' =
          (7 ^ K' * C₀ + 15 + Fintype.card (X₂ ⊕ X₁)) * B ^ K' := by ring
      rw [e]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      linarith
    linarith
  · -- the error
    intro R _ _ _ _ x hH hrow hcol hent
    have h1 := herr (R := R) x (D.padData_isHermitian _ hz₀ x hH) (D.padData_row_le _ hz₀ x hrow)
      (D.padData_col_le _ hz₀ x hcol) (D.padData_entry_le _ hz₀ x hμ0.le hent)
    have h2 := genCirc_error D (fun _ => false) hz₀ hS hζ0 sys Cc hv x t (ε / 2) hεh.le h1
    intro ψ hψ
    refine (h2 ψ hψ).trans ?_
    have h3 : (n : ℝ) * ζ ≤ ε / 2 := by
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
      rw [hζ, mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith
    linarith

end Main

end

end ManuscriptConformance
