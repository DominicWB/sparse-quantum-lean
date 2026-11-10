import ManuscriptConformance.GateMain
import GateEfficientBitBudget.HamiltonianGates

/-!
# Conformance: Theorem `hs:thm:gates` (gate-efficient sparse simulation), binary form

Theorem `hs:thm:gates` ends with its concrete conclusion for efficiently
decoded binary entries (eq. `hs:eq:gate-binary`): with
`Q_base = √s η T + √(s η T log(1/ε)) + log(1/ε)`, `T = |t|`, the additional gates are
`Q_base poly(b_data, log(N+1), log((Q_base+1)/ε))`, with full-output error `ε` and the query
order of
`hs:thm:main`. This file states that conclusion over a finite gate set, for every real `t` and every
`η > 0`, derived from the package's binary budget `GateBinary.binary_simulation_budget` (the native
circuit of normalised data, `NativeSparseRescaling.normalize`), the inverse circuit for negative
time, and the synthesis of `GateEfficientSynthesis`.

**Hypotheses, as in the manuscript.** The assumptions of `hs:thm:main` (Hermitian `H` with row and
column Euclidean norms at most `η > 0`, `0 < ε ≤ 1/2`), entries and known parameters of bit length
at most `b_data` (`comp_bits`: stored bits `b ≤ b_data`, the decoder scale `c₀` and `η` of bit length
`b_data` in the fixed-point model `GateBitBudget.HasBits`; the decoding and reversible arithmetic are
the package's CORDIC circuit, whose polynomial cost is proved), and single-qubit synthesis of length
`O(log(1/ζ))` with an exact decomposition of the controlled gates (`ext_…`). Formal restriction:
`formal_binaryInput` (the binary format, review item B).

**Scope.** The general accounting of the theorem for arbitrary implementations of the private
Cayley operation (eqs. `hs:eq:gate-known`, `hs:eq:gate-Gzero`, `hs:eq:gate-total` with the costs
`G_C(ξ)`, `A_C(ξ)`) is not restated here: in the package it is proved for an abstract private
operation and boundary given by their clock promises (`GateCircuit.Sim.gate_efficient_simulation`,
`GateNative.native_simulation`, `GateSynth.native_simulation_synth`), and derived from sparse oracles
only in the binary model used below.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4096

namespace ManuscriptConformance

noncomputable section
open ContinuousLinearMap SparseHamiltonian SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
  SparseHamiltonian.GateSynth SparseHamiltonian.GateBinary SparseHamiltonian.GateBitBudget
open SparseHamiltonian.GateCircuit.Sim (fDeg simM simR)
open CayleyClockInterface (width time moment)
open scoped InnerProduct

/-! ### Real estimates -/

/-- `q(ε/2) ≤ 2 q(ε)` for the query shape `q = √s τ + √(sτ log(1/ε)) + log(1/ε)`. -/
theorem shape_half_le (s : ℕ) {τ ε : ℝ} (hτ : 0 ≤ τ) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    ImprovedPrecisionBudget.shape s τ (Real.log (1 / (ε / 2))) ≤
      2 * ImprovedPrecisionBudget.shape s τ (Real.log (1 / ε)) := by
  unfold ImprovedPrecisionBudget.shape
  have hL2 : Real.log 2 ≤ Real.log (1 / ε) :=
    Real.log_le_log (by norm_num) (by rw [le_div_iff₀ hε]; linarith)
  have e : Real.log (1 / (ε / 2)) = Real.log 2 + Real.log (1 / ε) := by
    rw [one_div_div, Real.log_div (by norm_num) hε.ne', one_div, Real.log_inv]; ring
  have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hle : Real.log (1 / (ε / 2)) ≤ 2 * Real.log (1 / ε) := by rw [e]; linarith
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  have h0 : 0 ≤ (s : ℝ) * τ * Real.log (1 / (ε / 2)) := by
    have : 0 ≤ Real.log (1 / (ε / 2)) := by rw [e]; linarith
    positivity
  have hsq : Real.sqrt ((s : ℝ) * τ * Real.log (1 / (ε / 2))) ≤
      2 * Real.sqrt ((s : ℝ) * τ * Real.log (1 / ε)) := by
    have h1 : Real.sqrt ((s : ℝ) * τ * Real.log (1 / (ε / 2))) ≤
        Real.sqrt (4 * ((s : ℝ) * τ * Real.log (1 / ε))) := by
      apply Real.sqrt_le_sqrt
      have : 0 ≤ (s : ℝ) * τ := by positivity
      nlinarith
    have h4 : Real.sqrt (4 * ((s : ℝ) * τ * Real.log (1 / ε))) =
        2 * Real.sqrt ((s : ℝ) * τ * Real.log (1 / ε)) := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
      congr 1
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [h4] at h1
    exact h1
  have hst : 0 ≤ Real.sqrt s * τ := by positivity
  linarith

/-- The query shape is at least `log 2 > 1/2` for `ε ≤ 1/2`. -/
theorem shape_ge_half (s : ℕ) {τ ε : ℝ} (hτ : 0 ≤ τ) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    1 / 2 ≤ ImprovedPrecisionBudget.shape s τ (Real.log (1 / ε)) := by
  have hℓ : 1 / 2 ≤ Real.log (1 / ε) := by
    have h1 : Real.log 2 ≤ Real.log (1 / ε) :=
      Real.log_le_log (by norm_num) (by rw [le_div_iff₀ hε]; linarith)
    have h2 := Real.log_two_gt_d9
    norm_num at h2
    linarith
  exact hℓ.trans (le_shape _ _ _ hτ)

/-- **The synthesis factor**, for a count parameter `Q > 0` with `Q c_N ≥ 1`. -/
theorem synth_factor' {M Q cN B ε c₀ c₁ : ℝ} {K : ℕ} (hM0 : 0 ≤ M) (hQ0 : 0 < Q)
    (hQcN : 1 ≤ Q * cN) (hcN : 1 ≤ cN) (hB1 : 1 ≤ B) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hB : Real.logb 2 ((Q + 1) / ε) ≤ B) (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁)
    (hM : M ≤ Q * cN * B ^ K) :
    M * (c₁ * Real.log ((M + 1) / (ε / 2)) + c₀) ≤
      Q * cN * (c₁ * (Real.log (4 * cN) + K + 2) + c₀) * B ^ (K + 1) := by
  set M' := Q * cN * B ^ K with hM'
  have hBK : 1 ≤ B ^ K := one_le_pow₀ hB1
  have hM'1 : 1 ≤ M' := by
    rw [hM']
    calc (1 : ℝ) ≤ Q * cN := hQcN
      _ ≤ Q * cN * B ^ K := le_mul_of_one_le_right (by linarith) hBK
  have hY1 : 1 ≤ (Q + 1) / ε := one_le_div_of_le hQ0.le hε hε1
  have hlogY : Real.log ((Q + 1) / ε) ≤ B := (log_le_logb _ hY1).trans hB
  have hlogQ : Real.log Q ≤ B := by
    refine le_trans ?_ hlogY
    apply Real.log_le_log hQ0
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

/-! ### The CORDIC words of the normalised data -/

/-- **The CORDIC words** for the decoder scale `κ = γ √s c₀/η` of the normalised data
(`γ ≤ 1 ≤ γ √s`) and the accuracy `ζ = (ε/2)/(221184 q_n)`, `q_n ≤ 2q`: at most `34 B` for
`B ≥ max(1, k, b_data, log₂((q+1)/ε))` (`B ≥ b_data + log₂(N+1) + log₂((q+1)/ε)` in use). -/
theorem hs_words_le {k b σ s bd : ℕ} {γ c0 η qn q ε B : ℝ} (hs : s = 2 ^ σ) (hσ : σ ≤ k)
    (hbd : b ≤ bd) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hγs : 1 ≤ γ * Real.sqrt s) (hc0 : HasBits bd c0)
    (hc0p : 0 < c0) (hηb : HasBits bd η) (hηp : 0 < η) (hqn : 0 < qn) (hqnq : qn ≤ 2 * q)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hB1 : 1 ≤ B) (hBk : (k : ℝ) ≤ B) (hBd : (bd : ℝ) ≤ B)
    (hB : Real.logb 2 ((q + 1) / ε) ≤ B) :
    (cordicWords k b (γ * Real.sqrt s * (c0 / η)) (ε / 2 / (221184 * qn)) : ℝ) ≤ 34 * B := by
  set κ := γ * Real.sqrt s * (c0 / η) with hκ
  have hs1 : (1 : ℝ) ≤ s := by rw [hs]; exact_mod_cast Nat.one_le_two_pow
  have hsk : (s : ℝ) ≤ 2 ^ k := by
    rw [hs]; exact_mod_cast Nat.pow_le_pow_right (by norm_num) hσ
  have hsq0 : 0 < Real.sqrt (s : ℝ) := Real.sqrt_pos.2 (by linarith)
  have hsq : Real.sqrt (s : ℝ) ≤ 2 ^ k := (sqrt_le_self_of_one_le hs1).trans hsk
  have hc0' : c0 ≤ 2 ^ bd := hc0.lt.le
  have hη' : η ≤ 2 ^ bd := hηb.lt.le
  have hηi : 1 / η ≤ 2 ^ bd := by
    rw [div_le_iff₀ hηp]; have := hηb.one_le_mul hηp; linarith
  have hc0i : 1 / c0 ≤ 2 ^ bd := by
    rw [div_le_iff₀ hc0p]; have := hc0.one_le_mul hc0p; linarith
  have hκp : 0 < κ := by rw [hκ]; positivity
  have hκu : κ ≤ 2 ^ (k + 2 * bd) := by
    rw [hκ]
    have h1 : c0 / η ≤ 2 ^ bd * 2 ^ bd := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul hc0' hηi (by positivity) (by positivity)
    have h2 : γ * Real.sqrt s ≤ 2 ^ k := by
      have := mul_le_mul_of_nonneg_right hγ1 hsq0.le
      linarith
    calc γ * Real.sqrt s * (c0 / η) ≤ 2 ^ k * (2 ^ bd * 2 ^ bd) :=
          mul_le_mul h2 h1 (by positivity) (by positivity)
      _ = 2 ^ (k + 2 * bd) := by ring
  have hκi : 1 / κ ≤ 2 ^ (2 * bd) := by
    have hκl : c0 / η ≤ κ := by
      rw [hκ]; exact le_mul_of_one_le_left (by positivity) hγs
    have h1 : 1 / κ ≤ η / c0 := by
      rw [div_le_div_iff₀ hκp hc0p]
      have := mul_le_mul_of_nonneg_left hκl hηp.le
      have e : η * (c0 / η) = c0 := by field_simp
      linarith
    have h2 : η / c0 ≤ 2 ^ bd * 2 ^ bd := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul hη' hc0i (by positivity) (by positivity)
    calc 1 / κ ≤ 2 ^ bd * 2 ^ bd := h1.trans h2
      _ = 2 ^ (2 * bd) := by ring
  have wκ : (Nat.clog 2 ⌈κ⌉₊ : ℝ) ≤ k + 2 * bd := by
    have := clog_ceil_le_nat _ _ hκu; exact_mod_cast this
  have wκi : (Nat.clog 2 ⌈1 / κ⌉₊ : ℝ) ≤ 2 * bd := by
    have := clog_ceil_le_nat _ _ hκi; exact_mod_cast this
  -- the CORDIC steps
  set Y := (q + 1) / ε with hY
  have hq0 : 0 ≤ q := by linarith
  have hY1 : 1 ≤ Y := one_le_div_of_le hq0 hε hε1
  have hz : 8 / (ε / 2 / (221184 * qn)) ≤ 2 ^ 23 * Y ^ 1 := by
    have e : 8 / (ε / 2 / (221184 * qn)) = 3538944 * qn * (1 / ε) := by
      field_simp; ring
    rw [e, pow_one, hY]
    have h1 : 3538944 * qn * (1 / ε) ≤ 3538944 * (2 * (q + 1)) * (1 / ε) :=
      mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
    have e2 : 3538944 * (2 * (q + 1)) * (1 / ε) = 7077888 * ((q + 1) / ε) := by ring
    have h3 : 7077888 * ((q + 1) / ε) ≤ 2 ^ 23 * ((q + 1) / ε) :=
      mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    linarith
  have wn : (Cordic.nOf (ε / 2 / (221184 * qn)) : ℝ) ≤ 26 + B := by
    have h := clog_le_mul_pow _ (2 ^ 23) Y 23 1 hY1 le_rfl hz
    unfold Cordic.nOf
    push_cast at h ⊢
    linarith
  have hw : (cordicWords k b κ (ε / 2 / (221184 * qn)) : ℝ) = k + b +
      (Cordic.nOf (ε / 2 / (221184 * qn)) : ℝ) + (Nat.clog 2 ⌈κ⌉₊ : ℝ) +
        (Nat.clog 2 ⌈1 / κ⌉₊ : ℝ) := by
    unfold cordicWords; push_cast; ring
  have hb' : (b : ℝ) ≤ bd := by exact_mod_cast hbd
  rw [hw]
  linarith

/-! ### Theorem `hs:thm:gates`, eq. `hs:eq:gate-binary` -/

/-- **Negative time by the adjoint circuit**, on the registers of the native model: if `U` is
unitary and `‖U E - E e^{-i|t|H}‖ ≤ δ` for a self-adjoint `H`, then `‖U† E - E e^{-itH}‖ ≤ δ` for
`t < 0`. -/
theorem neg_time_error {V S : Type*} [Fintype V] [DecidableEq V] [Fintype S] [DecidableEq S]
    {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
    (U : Reg V R →L[ℂ] Reg V R) (hU : OracleCircuit.IsUnitary U) (E : Reg S R →L[ℂ] Reg V R)
    (H : Reg S R →L[ℂ] Reg S R) (hH : star H = H) {t δ : ℝ} (ht : t < 0)
    (h : ‖U ∘L E - E ∘L NormedSpace.exp ((-Complex.I * ((|t| : ℝ) : ℂ)) • H)‖ ≤ δ) :
    ‖U† ∘L E - E ∘L NormedSpace.exp ((-Complex.I * (t : ℂ)) • H)‖ ≤ δ := by
  have hV := LabeledAdjointSimulation.evolution_unitary _ hH |t|
  have hadj := LabeledAdjointSimulation.evolution_adjoint _ hH |t|
  have ht' : ((-|t| : ℝ) : ℂ) = (t : ℂ) := by rw [abs_of_neg ht, neg_neg]
  rw [ht'] at hadj
  rw [← hadj, LabeledAdjointSimulation.adjoint_error_eq _ _ hU hV]
  exact h


universe u v w

/-- The query shape of the package is the manuscript's `Q_base` (eq. `hs:eq:mainbound`). -/
theorem shape_eq_mainBound (s : ℕ) (τ ε : ℝ) :
    ImprovedPrecisionBudget.shape s τ (Real.log (1 / ε)) = mainBound s τ ε := rfl

set_option maxHeartbeats 8000000 in
/-- **Theorem `hs:thm:gates`, eq. `hs:eq:gate-binary`.** For a finite gate
set admitting single-qubit synthesis of length at most `c₁ log(1/ζ) + c₀` and an exact decomposition
of its controlled one-qubit gates, there is a constant `C` such that: for sparse data in the binary
format (`formal_binaryInput`) whose stored components have at most `b_data` bits and whose decoder
scale `c0` and norm bound `η > 0` have `b_data`-bit descriptions (`comp_bits`), every time `t` and
`0 < ε ≤ 1/2`, one circuit over the gate set and the primitive sparse oracles, fixed before the
instance, uses at most `552960 Q_base` primitive sparse queries (the query order of `hs:thm:main`,
with an absolute constant), at most `C Q_base (𝔟 + 1)⁴` gates with
`Q_base = √s η|t| + √(s η|t| log(1/ε)) + log(1/ε)` and
`𝔟 = b_data + log₂(N+1) + log₂((Q_base+1)/ε)`
(`G_additional = Q_base poly(b_data, log(N+1), log((Q_base+1)/ε))`), and on every instance whose
matrix is
Hermitian with row and column Euclidean norms at most `η` has full-output error at most `ε` on the
clean embedding, with an untouched reference. Formal restrictions: `formal_binaryInput`
(review item B). -/
theorem hs_thm_gates {c₀ c₁ : ℝ} (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁) (Kd : ℕ) {𝒢 : Set Kind}
    {X₁ X₂ : Type} [Fintype X₁] [DecidableEq X₁] [Fintype X₂] [DecidableEq X₂] {L : ℝ → ℕ}
    (ext_singleQubitSynthesis : OneQubitSynthesis 𝒢 X₁ L)
    (ext_singleQubitLength : ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 → (L ζ : ℝ) ≤ c₁ * Real.log (1 / ζ) + c₀)
    (ext_controlDecomposition : ControlDecomposition 𝒢 X₂ Kd) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {X : Type u} {n : Type v} [Fintype n] [DecidableEq n] {s k b : ℕ}
        (D : NativeSparseBlockEncoding.Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n)
        (sb bd : ℕ) (c0 η t ε : ℝ),
        formal_binaryInput D en sb c0 → comp_bits b bd [c0, η] →
        0 < η → 0 < ε → ε ≤ 1 / 2 →
        ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (sys : Fin k ↪ W)
          (Cc : List (NInstr W (PY k b) NativeSparseBlockEncoding.Query)),
          (∀ i ∈ Cc, i.Valid) ∧ (∀ g, NInstr.gate g ∈ Cc → GateOf 𝒢 g) ∧
          (nCallsN (fun _ => true) Cc : ℝ) ≤ 552960 * mainBound s (η * |t|) ε ∧
          (nGatesN Cc : ℝ) ≤ C * mainBound s (η * |t|) ε *
            (bitH bd (Fintype.card n) (mainBound s (η * |t|) ε) ε + 1) ^ 4 ∧
          ∀ {R : Type w} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
            (x : X),
            (D.matrix x).IsHermitian → (∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) →
            (∀ j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) →
            FullOutputError (nrun (prims (R := R) D en x) Cc) (cleanAlong sys)
              (NormedSpace.exp ((-Complex.I * (t : ℂ)) •
                qlift (R := R) en (SparseStateOverlap.matrixOperator (D.matrix x)))) ε := by
  obtain ⟨L', c₀', c₁', hc₀', hc₁', hS, hL'⟩ := synthesis_of_parts hc₀ hc₁
    ext_singleQubitSynthesis ext_singleQubitLength ext_controlDecomposition
  set cN : ℝ := 200 * 9218 * (57000 * 35 ^ 3 + 36) with hcN
  set Cg : ℝ := cN * (c₁' * (Real.log (4 * cN) + (3 : ℕ) + 2) + c₀') with hCg
  have hcN1 : 1 ≤ cN := by rw [hcN]; norm_num
  have hCg0 : 0 ≤ Cg := by
    have : 0 ≤ Real.log (4 * cN) := Real.log_nonneg (by linarith)
    positivity
  set C : ℝ := 552960 + Cg with hC
  refine ⟨C, by positivity, ?_⟩
  intro X n _ _ s k b D en sb bd c0 η t ε hF hbits hη hε hε2
  obtain ⟨hbd, hc0b, hηb⟩ := hbits
  have hs1 : 1 ≤ s := by rw [hF.hs]; exact Nat.one_le_two_pow
  set τ : ℝ := η * |t| with hτdef
  have hτ : 0 ≤ τ := by positivity
  set q := mainBound s τ ε with hqdef
  have hq2 : 1 / 2 ≤ q := shape_ge_half s hτ hε hε2
  have hq0 : 0 < q := by linarith
  set εn : ℝ := ε / 2 with hεn
  have hεn0 : 0 < εn := by positivity
  have hεn2 : εn ≤ 1 / 2 := by linarith
  have hε1 : ε ≤ 1 := by linarith
  set qn := ImprovedPrecisionBudget.shape s τ (Real.log (1 / εn)) with hqndef
  have hqnq : qn ≤ 2 * q := shape_half_le s hτ hε hε2
  have hqn2 : 1 / 2 ≤ qn := shape_ge_half s hτ hεn0 hεn2
  have hqn0 : 0 < qn := by linarith
  -- the budget word
  set B := bitH bd (Fintype.card n) q ε + 1 with hBdef
  have hcard : Fintype.card n = 2 ^ k := card_eq_two_pow en
  have hY1 : 1 ≤ (q + 1) / ε := one_le_div_of_le hq0.le hε hε1
  have hlogN : (k : ℝ) ≤ Real.logb 2 ((Fintype.card n : ℝ) + 1) := by
    rw [hcard]; exact nat_le_logb k
  have hlogY : 0 ≤ Real.logb 2 ((q + 1) / ε) := logb_nonneg_of_one_le hY1
  have hbd0 : (0 : ℝ) ≤ bd := Nat.cast_nonneg _
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hB1 : 1 ≤ B := by rw [hBdef]; unfold bitH; linarith
  have hBk : (k : ℝ) ≤ B := by rw [hBdef]; unfold bitH; linarith
  have hBd : (bd : ℝ) ≤ B := by rw [hBdef]; unfold bitH; linarith
  have hBY : Real.logb 2 ((q + 1) / ε) ≤ B := by rw [hBdef]; unfold bitH; linarith
  have hσk : (sb : ℝ) ≤ k := by exact_mod_cast hF.hsb
  have hB3 : B ≤ B ^ 3 := le_self_pow₀ hB1 (by norm_num)
  -- the word `log₂((q_n+1)/ε_n) ≤ 2 + B`
  have hYn : Real.logb 2 ((qn + 1) / εn) ≤ 2 + B := by
    have h1 : (qn + 1) / εn ≤ 2 ^ 2 * ((q + 1) / ε) ^ 1 := by
      rw [pow_one, hεn, div_le_iff₀ (by positivity)]
      have : 2 ^ 2 * ((q + 1) / ε) * (ε / 2) = 2 * (q + 1) := by field_simp
      rw [this]; linarith
    have h2 := logb_le_mul_pow _ (2 ^ 2) ((q + 1) / ε) 2 1 (by positivity) hY1 le_rfl h1
    push_cast at h2
    linarith
  -- the rescaling and the released budget
  obtain ⟨γ, hγ, hγ1, hγs, hdeg, hτq, hm, hr, hall⟩ :=
    binary_simulation_budget.{u, v, w} s hs1 τ εn hτ hεn0 hεn2
  set ζ : ℝ := εn / (221184 * qn) with hζdef
  have hζ0 : 0 < ζ := by positivity
  have hζ1 : ζ ≤ 1 := by
    rw [hζdef, div_le_one (by positivity)]; linarith
  have hζε : 221184 * qn * ζ ≤ εn := by
    have : 221184 * qn * ζ = εn := by rw [hζdef]; field_simp
    exact this.le
  have hζε' : 48 * (fDeg (width (s : ℝ) γ) (time (s : ℝ) τ γ) (moment γ) (εn / 2) : ℝ) * ζ ≤
      εn := by
    have h1 : 48 * (fDeg (width (s : ℝ) γ) (time (s : ℝ) τ γ) (moment γ) (εn / 2) : ℝ) * ζ ≤
        48 * (4608 * qn) * ζ := by
      apply mul_le_mul_of_nonneg_right _ hζ0.le
      linarith
    linarith
  set D' := NativeSparseRescaling.normalize D η hη with hD'
  have hdec' : ∀ e z, D'.decode e z = ((c0 / η : ℝ) : ℂ) * gauss z := by
    intro e z
    change ((η⁻¹ : ℝ) : ℂ) * D.decode e z = _
    rw [hF.dec]; push_cast; ring
  have hc0η : 0 < c0 / η := div_pos hF.hc0 hη
  set Cn := binarySim k b sb hF.hsb s γ (c0 / η) τ εn ζ with hCn
  -- the per-call cost
  have hU := hs_words_le hF.hs hF.hsb hbd hγ hγ1 hγs hc0b hF.hc0 hηb hη hqn0 hqnq hε hε1 hB1 hBk
    hBd hBY
  set U := cordicWords k b (γ * Real.sqrt s * (c0 / η)) ζ with hUdef
  have hU0 : (0 : ℝ) ≤ U := Nat.cast_nonneg _
  have hU3 : ((U : ℝ) + 1) ^ 3 ≤ 35 ^ 3 * B ^ 3 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by linarith) (by linarith) 3
  have hpriv : (privGates (sparseOp k b (γ * Real.sqrt s * (c0 / η)))
      (binArith k b (γ * Real.sqrt s * (c0 / η)) ζ) : ℝ) ≤ 57000 * 35 ^ 3 * B ^ 3 := by
    have h1 : (privGates (sparseOp k b (γ * Real.sqrt s * (c0 / η)))
        (binArith k b (γ * Real.sqrt s * (c0 / η)) ζ) : ℝ) ≤ 57000 * ((U : ℝ) + 1) ^ 3 := by
      exact_mod_cast privGates_binary k b (γ * Real.sqrt s * (c0 / η)) ζ
    linarith
  -- the simulator words
  have hs1' : (1 : ℝ) ≤ s := by exact_mod_cast hs1
  have hsk : (s : ℝ) ≤ 2 ^ k := by
    rw [hF.hs]; exact_mod_cast Nat.pow_le_pow_right (by norm_num) hF.hsb
  have htime0 : 0 ≤ time (s : ℝ) τ γ := by unfold CayleyClockInterface.time; positivity
  have hmW := simM_word _ k hs1' hsk htime0 hτq hqn0.le hεn0 (by linarith) hm
  have hrW := simR_word _ hqn0.le hεn0 (by linarith) hr
  have hinner : (privGates (sparseOp k b (γ * Real.sqrt s * (c0 / η)))
      (binArith k b (γ * Real.sqrt s * (c0 / η)) ζ) : ℝ) + (sb + 1) + (k + 1) +
      simM (time (s : ℝ) τ γ) (εn / 2) +
      simR (width (s : ℝ) γ) (time (s : ℝ) τ γ) (moment γ) (εn / 2) + 1 ≤
      (57000 * 35 ^ 3 + 36) * B ^ 3 := by
    linarith
  have hinner0 : 0 ≤ (privGates (sparseOp k b (γ * Real.sqrt s * (c0 / η)))
      (binArith k b (γ * Real.sqrt s * (c0 / η)) ζ) : ℝ) + (sb + 1) + (k + 1) +
      simM (time (s : ℝ) τ γ) (εn / 2) +
      simR (width (s : ℝ) γ) (time (s : ℝ) τ γ) (moment γ) (εn / 2) + 1 := by positivity
  set Nb : ℝ := 200 * (4608 * qn + 1) * ((privGates (sparseOp k b (γ * Real.sqrt s * (c0 / η)))
      (binArith k b (γ * Real.sqrt s * (c0 / η)) ζ) : ℝ) + (sb + 1) + (k + 1) +
      simM (time (s : ℝ) τ γ) (εn / 2) +
      simR (width (s : ℝ) γ) (time (s : ℝ) τ γ) (moment γ) (εn / 2) + 1) with hNb
  have hNb0 : 0 ≤ Nb := by positivity
  have hNbq : Nb ≤ q * cN * B ^ 3 := by
    have h1 : 200 * (4608 * qn + 1) ≤ 200 * 9218 * q := by linarith
    have h2 : Nb ≤ (200 * 9218 * q) * ((57000 * 35 ^ 3 + 36) * B ^ 3) :=
      mul_le_mul h1 hinner hinner0 (by positivity)
    have e : (200 * 9218 * q) * ((57000 * 35 ^ 3 + 36) * B ^ 3) = q * cN * B ^ 3 := by
      rw [hcN]; ring
    exact h2.trans e.le
  -- the final gate bound
  have hfin : ∀ N : ℕ, (N : ℝ) ≤ Nb → ((N * L' (ε / 2 / (N + 1)) : ℕ) : ℝ) ≤ C * q * B ^ 4 := by
    intro N hN
    have h1 := gates_log_le hc₀' hc₁' hL' (ε' := ε / 2) (by positivity) (by linarith) N Nb hN
    have hqcN : 1 ≤ q * cN := by rw [hcN]; linarith
    have h2 := synth_factor' (K := 3) hNb0 hq0 hqcN hcN1 hB1 hε hε1 hBY hc₀' hc₁' hNbq
    have h3 : q * cN * (c₁' * (Real.log (4 * cN) + (3 : ℕ) + 2) + c₀') * B ^ (3 + 1) ≤
        C * q * B ^ 4 := by
      have e : q * cN * (c₁' * (Real.log (4 * cN) + (3 : ℕ) + 2) + c₀') * B ^ (3 + 1) =
          Cg * (q * B ^ 4) := by rw [hCg]; ring
      rw [e]
      have : 0 ≤ q * B ^ 4 := by positivity
      have hle : Cg ≤ C := by rw [hC]; linarith
      calc Cg * (q * B ^ 4) ≤ C * (q * B ^ 4) := mul_le_mul_of_nonneg_right hle this
        _ = C * q * B ^ 4 := by ring
    exact h1.trans (h2.trans h3)
  -- the promises
  let Prom : X → Prop := fun x => (D.matrix x).IsHermitian ∧
    (∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) ∧ (∀ j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2)
  by_cases hx : ∃ x, Prom x
  swap
  · refine ⟨Fin k, inferInstance, inferInstance, Function.Embedding.refl _, [], by simp, by simp,
      ?_, ?_, fun x hH hrow hcol => absurd ⟨x, hH, hrow, hcol⟩ hx⟩
    · simp only [nCallsN, List.countP_nil, Nat.cast_zero]; positivity
    · simp only [nGatesN, List.countP_nil, Nat.cast_zero]; positivity
  obtain ⟨x₀, hx₀⟩ := hx
  -- the native facts
  have hnat : ∀ {R : Type w} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
      (x : X), Prom x →
      (∀ i ∈ Cn, i.Valid) ∧
      (∀ p : NativeSparseBlockEncoding.Query → Bool, (nCallsN p Cn : ℝ) ≤
        55296 * qn * (2 * (if p NativeSparseBlockEncoding.Query.rowLocation then 1 else 0) +
          2 * (if p NativeSparseBlockEncoding.Query.columnLocation then 1 else 0) +
          (if p NativeSparseBlockEncoding.Query.value then 1 else 0))) ∧
      (nGatesN Cn : ℝ) ≤ Nb ∧
      ‖nrun (prims (R := R) D' en x) Cn ∘L sysEmb (Sim.io (P := Reg (Fin k) R)) -
          sysEmb (Sim.io (P := Reg (Fin k) R)) ∘L NormedSpace.exp ((-Complex.I * (τ : ℂ)) •
            qlift (R := R) en (SparseStateOverlap.matrixOperator (D'.matrix x)))‖ ≤ εn := by
    intro R _ _ _ x hxp
    have hH' := NativeSparseRescaling.normalize_hermitian D η hη x hxp.1
    have hrow' := fun i => NativeSparseRescaling.normalized_row_energy D η hη x i (hxp.2.1 i)
    have hcol' := fun j => NativeSparseRescaling.normalized_column_energy D η hη x j (hxp.2.2 j)
    obtain ⟨hv, -⟩ := binary_simulation (R := R) D' en sb hF.hsb hF.hs hF.range hF.hb (c0 / η)
      hc0η hdec' x hH' hrow' hcol' γ τ εn ζ hγ hγ1 hτ hεn0 (by linarith) hζ0 hζ1 hζε'
    obtain ⟨hc, hg, he⟩ := hall (R := R) D' en sb hF.hsb hF.hs hF.range hF.hb (c0 / η) hc0η hdec'
      x hH' hrow' hcol' ζ hζ0 hζ1 hζε
    -- fold the local definitions syntactically (unfolding them by `whnf` is too slow)
    rw [← hCn] at hv hc hg he
    rw [← hqndef] at hc hg
    rw [← hNb] at hg
    exact ⟨hv, hc, hg, he⟩
  -- the normalised data have the same oracles, and `e^{-iτH/η} = e^{-i|t|H}`
  have hprims : ∀ {R : Type w} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
      (x : X), prims (R := R) D' en x = prims (R := R) D en x := by
    intro R _ _ _ x
    funext j; cases j <;> rfl
  have hexp : ∀ {R : Type w} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
      (x : X), (-Complex.I * (τ : ℂ)) •
        qlift (R := R) en (SparseStateOverlap.matrixOperator (D'.matrix x)) =
        (-Complex.I * ((|t| : ℝ) : ℂ)) •
          qlift (R := R) en (SparseStateOverlap.matrixOperator (D.matrix x)) := by
    intro R _ _ _ x
    have h1 := NativeSparseRescaling.exponent_cancel D η hη x |t|
    have h2 := congrArg (qlift (R := R) en) h1
    rw [qlift, qlift, map_smul, map_smul] at h2
    rw [hτdef]
    push_cast at h2 ⊢
    exact h2
  obtain ⟨hv0, hc0, hg0, -⟩ := hnat (R := EuclideanSpace ℂ (ULift.{w} (Fin 1))) x₀ hx₀
  have hcalls5 : ∀ p : NativeSparseBlockEncoding.Query → Bool,
      (2 * (if p NativeSparseBlockEncoding.Query.rowLocation then 1 else 0) +
        2 * (if p NativeSparseBlockEncoding.Query.columnLocation then 1 else 0) +
        (if p NativeSparseBlockEncoding.Query.value then 1 else 0) : ℝ) ≤ 5 := by
    intro p
    split_ifs <;> norm_num
  -- the signed native circuit: the inverse circuit for negative time
  set Cs := if 0 ≤ t then Cn else ninv Cn with hCs
  have hCs_valid : ∀ i ∈ Cs, i.Valid := by
    rw [hCs]; split_ifs
    · exact hv0
    · exact valid_ninv _ hv0
  have hCs_calls : ∀ p, nCallsN p Cs = nCallsN p Cn := by
    intro p; rw [hCs]; split_ifs
    · rfl
    · exact nCallsN_ninv p Cn
  have hCs_gates : nGatesN Cs = nGatesN Cn := by
    rw [hCs]; split_ifs
    · rfl
    · exact nGatesN_ninv Cn
  have hε2' : (0 : ℝ) < ε / 2 := by positivity
  obtain ⟨hsv, hsk', hsg, hsc⟩ := synthBudget_spec hS hε2' Cs hCs_valid
  refine ⟨_, inferInstance, inferInstance, sysWire _ _ _ _ _ _ _ _, synthBudget hS (ε / 2) Cs,
    hsv, hsk', ?_, ?_, ?_⟩
  · -- the primitive calls
    rw [hsc, hCs_calls]
    have h1 := hc0 (fun _ => true)
    have h5 := hcalls5 (fun _ => true)
    have h2 := mul_le_mul_of_nonneg_left h5 (show (0 : ℝ) ≤ 55296 * qn by positivity)
    have h3 : 55296 * qn * 5 ≤ 552960 * q := by linarith
    exact h1.trans (h2.trans h3)
  · -- the gates
    have h1 : (nGatesN (synthBudget hS (ε / 2) Cs) : ℝ) ≤
        ((nGatesN Cs * L' (ε / 2 / (nGatesN Cs + 1)) : ℕ) : ℝ) := by exact_mod_cast hsg
    have h2 := hfin (nGatesN Cs) (by rw [hCs_gates]; exact hg0)
    linarith
  · -- the full-output error
    intro R _ _ _ x hH hrow hcol
    obtain ⟨hv, -, -, he⟩ := hnat (R := R) x ⟨hH, hrow, hcol⟩
    rw [hprims x, hexp x] at he
    have hprim := prims_isUnitary (R := R) D en x
    have hU : OracleCircuit.IsUnitary (nrun (prims (R := R) D en x) Cn) :=
      nrun_isUnitary _ hprim _ hv
    have hHs : star (qlift (R := R) en (SparseStateOverlap.matrixOperator (D.matrix x))) =
        qlift (R := R) en (SparseStateOverlap.matrixOperator (D.matrix x)) :=
      GateOptimalBinary.sysH_star D en x hH
    have herr' : ‖nrun (prims (R := R) D en x) Cs ∘L sysEmb (Sim.io (P := Reg (Fin k) R)) -
        sysEmb (Sim.io (P := Reg (Fin k) R)) ∘L NormedSpace.exp ((-Complex.I * (t : ℂ)) •
          qlift (R := R) en (SparseStateOverlap.matrixOperator (D.matrix x)))‖ ≤ εn := by
      rw [hCs]
      split_ifs with ht
      · rw [show ((|t| : ℝ) : ℂ) = (t : ℂ) by rw [abs_of_nonneg ht]] at he
        exact he
      · push Not at ht
        rw [nrun_ninv]
        exact neg_time_error _ hU _ _ hHs ht he
    have h := synthBudget_error hS hε2' Cs hCs_valid (prims (R := R) D en x) hprim _
      (by intro p; exact (norm_sysEmb _ (fun φ => by rw [Sim.io_apply, norm_bas]) p).le) _ herr'
    rw [cleanEmb_sysEmb_io] at h
    have e : εn + ε / 2 = ε := by rw [hεn]; ring
    rw [e] at h
    exact fullOutputError_of_norm h

end

end ManuscriptConformance
