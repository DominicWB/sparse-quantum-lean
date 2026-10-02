import SparseHamiltonian.ScheduledAmplifierSynthesis

/-!
# Constructive native sparse amplitude amplification

The public matrix and precision bounds determine an explicit polynomial.
The completion and phase-synthesis theorems discharge every polynomial and
phase-existence premise before constructing the counted native sparse circuit.
The theorem below needs only native locator/value access and matrix promises.
-/

namespace SparseHamiltonian.ActualSparseAmplifier

noncomputable section
open ContinuousLinearMap NativeSparseAttenuation
open NativeSparseBlockEncoding (Data Query)
open NativeSparseAmplifierCertificate (successBound)
open scoped BigOperators InnerProduct
set_option maxRecDepth 2000
set_option maxHeartbeats 800000

variable {X n Z : Type*} [Fintype n] [DecidableEq n] {s : ℕ}

/-- The reciprocal signal bound is exactly the desired sparse query factor. -/
theorem inverse_successBound (D : Data X n Z s) (β : ℝ) (hβ : 0 < β) :
    1 / successBound D β = Real.sqrt (((s : ℝ) * D.scale) / β) := by
  have hp := NativeSparseAmplifierCertificate.successBound_pos D β hβ
  have hsq := NativeSparseAmplifierCertificate.norm_target_sq D β hβ
  rw [NativeSparseAmplifierCertificate.norm_target D β hβ] at hsq
  have hnonneg : 0 ≤ ((s : ℝ) * D.scale) / β :=
    div_nonneg (NativeSparseAmplifierCertificate.sparseScale_pos D).le hβ.le
  have hroot := Real.sq_sqrt hnonneg
  nlinarith [Real.sqrt_nonneg (((s : ℝ) * D.scale) / β), one_div_pos.2 hp]

/-- The spectral/sparsity regime used in the amplitude scheduler. -/
theorem successBound_le_one (D : Data X n Z s) (β : ℝ)
    (hβ : β ≤ (s : ℝ) * D.scale) : successBound D β ≤ 1 := by
  have h := NativeSparseAmplifierCertificate.threshold_le_half D β hβ
  unfold NativeSparseAmplifierCertificate.threshold at h
  linarith

/-- A public absolute-sum bound at least the entry bound gives the square-root
sparsity budget directly. -/
theorem sparseFactor_le_sqrt (D : Data X n Z s) (β : ℝ) (hβ : D.scale ≤ β) :
    Real.sqrt (((s : ℝ) * D.scale) / β) ≤ Real.sqrt s := by
  have hp := lt_of_lt_of_le D.scale_pos hβ
  rw [← inverse_successBound D β hp,
    ← NativeSparseAmplifierCertificate.norm_target D β hp]
  exact NativeSparseAmplifierCertificate.norm_target_le_sqrt D β hβ

variable [Fintype Z] [AddCommGroup Z] [DecidableEq Z]

/-- One actual sparse-oracle program achieves normalization `Θ(β)`,
relative operator error `O(β δ)`, and square-root sparse query complexity.
There is no approximation-polynomial or phase-existence premise. -/
theorem exists_program (D : Data X n Z s) (β : ℝ) (hβ : 0 < β)
    (hβupper : β ≤ (s : ℝ) * D.scale)
    (hH : ∀ x, (D.matrix x).IsHermitian)
    (hRow : ∀ x i, ∑ j, ‖D.matrix x i j‖ ≤ β)
    (hCol : ∀ x j, ∑ i, ‖D.matrix x i j‖ ≤ β)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ α : ℝ, ∃ p : MultiOracleCircuit.Program (oracles D),
      0 < α ∧ (64 / 9) * β ≤ α ∧ α ≤ 1024 * β ∧
      (p.count : ℝ) < 24 * Real.sqrt (((s : ℝ) * D.scale) / β) *
        (Real.log (2 / δ) / Real.log 4 + 1) ∧
      (∀ x, OracleCircuit.IsUnitary (p.eval x)) ∧
      (∀ x, ((input D).toContinuousLinearMap† ∘L p.eval x ∘L
        (input D).toContinuousLinearMap)† =
        (input D).toContinuousLinearMap† ∘L p.eval x ∘L (input D).toContinuousLinearMap) ∧
      ∀ x, ‖(α : ℂ) • ((input D).toContinuousLinearMap† ∘L p.eval x ∘L
        (input D).toContinuousLinearMap) - SparseStateOverlap.matrixOperator (D.matrix x)‖ ≤
          β * (2 * δ + δ ^ 2) := by
  let A := successBound D β
  have hA : 0 < A := NativeSparseAmplifierCertificate.successBound_pos D β hβ
  have hA1 : A ≤ 1 := successBound_le_one D β hβupper
  let g := ScheduledAmplifierSynthesis.gain A δ
  have hg : 0 < g := ScheduledAmplifierSynthesis.gain_pos A δ hδ hδ1
  have hgain := ScheduledAmplifierSynthesis.gain_bounds A δ hA hA1 hδ hδ1
  obtain ⟨B, hnorm, hb, hB⟩ := ScheduledAmplifierSynthesis.completion A δ hδ hδ1
  obtain ⟨p, hcount, hunitary, hselfadjoint, herror⟩ :=
    NativeVariableGainCertificate.exists_program_of_pair D β g hβ hg
      (ScheduledFractionalAmplifier.phaseBudget A δ)
      ((ScheduledAmplifierSynthesis.polynomial A δ).map (algebraMap ℝ ℂ)) B
      (ScheduledAmplifierSynthesis.complex_degree A δ)
      hB (ScheduledAmplifierSynthesis.complex_parity A δ) hb hnorm hH hRow hCol δ hδ.le
      (fun z hz => ScheduledAmplifierSynthesis.relative_error A δ hA hA1 hδ hδ1 z hz)
  have hα := NativeVariableGainCertificate.normalization_bounds D β g hβ.le hg hgain.1 hgain.2
  refine ⟨NativeVariableGainCertificate.normalization D g, p,
    NativeVariableGainCertificate.normalization_pos D g hg, hα.1, hα.2, ?_,
    hunitary, hselfadjoint, ?_⟩
  · rw [hcount]
    have hq := ScheduledFractionalAmplifier.query_budget A δ hA hA1 hδ hδ1
    have he : 24 / A = 24 * Real.sqrt (((s : ℝ) * D.scale) / β) := by
      change 24 / successBound D β = _
      rw [show 24 / successBound D β = 24 * (1 / successBound D β) by ring,
        inverse_successBound D β hβ]
    rwa [he] at hq
  · intro x
    exact NativeVariableGainCertificate.rescaled_error D β g hg x _ _ (herror x)

/-- In the usual public-bound regime `a ≤ β ≤ s a`, the primitive query
budget is explicitly `O(sqrt s log(1/δ))`. -/
theorem exists_sqrt_s_program (D : Data X n Z s) (β : ℝ)
    (hβlower : D.scale ≤ β) (hβupper : β ≤ (s : ℝ) * D.scale)
    (hH : ∀ x, (D.matrix x).IsHermitian)
    (hRow : ∀ x i, ∑ j, ‖D.matrix x i j‖ ≤ β)
    (hCol : ∀ x j, ∑ i, ‖D.matrix x i j‖ ≤ β)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ α : ℝ, ∃ p : MultiOracleCircuit.Program (oracles D),
      0 < α ∧ (64 / 9) * β ≤ α ∧ α ≤ 1024 * β ∧
      (p.count : ℝ) < 24 * Real.sqrt s * (Real.log (2 / δ) / Real.log 4 + 1) ∧
      (∀ x, OracleCircuit.IsUnitary (p.eval x)) ∧
      (∀ x, ((input D).toContinuousLinearMap† ∘L p.eval x ∘L
        (input D).toContinuousLinearMap)† =
        (input D).toContinuousLinearMap† ∘L p.eval x ∘L (input D).toContinuousLinearMap) ∧
      ∀ x, ‖(α : ℂ) • ((input D).toContinuousLinearMap† ∘L p.eval x ∘L
        (input D).toContinuousLinearMap) - SparseStateOverlap.matrixOperator (D.matrix x)‖ ≤
          β * (2 * δ + δ ^ 2) := by
  have hβ : 0 < β := lt_of_lt_of_le D.scale_pos hβlower
  obtain ⟨α, p, hα, hαl, hαu, hcount, hunitary, hselfadjoint, herror⟩ :=
    exists_program D β hβ hβupper hH hRow hCol δ hδ hδ1
  refine ⟨α, p, hα, hαl, hαu, ?_, hunitary, hselfadjoint, herror⟩
  have hlog : 0 ≤ Real.log (2 / δ) :=
    Real.log_nonneg ((le_div_iff₀ hδ).2 (by linarith))
  have hL : 0 ≤ Real.log (2 / δ) / Real.log 4 + 1 := by
    have hd : 0 < Real.log 4 := Real.log_pos (by norm_num)
    positivity
  exact hcount.trans_le (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (sparseFactor_le_sqrt D β hβlower) (by norm_num)) hL)

end
end SparseHamiltonian.ActualSparseAmplifier
