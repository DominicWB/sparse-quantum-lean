import SparseODE.ODECompleteSuccess

/-!
# Perturbing the trials of the four-attempt protocol

The released four-attempt protocol (`ODERepeatProtocol.fourTrials`) draws a uniform trial `j`,
measures a clean-output herald and keeps the decoded amplitude `a j` on success. Its success
probability and conditional output depend only on the decoded amplitudes. If every amplitude is
moved by at most `η ≤ 1/400` (amplitudes of norm at most one), a mean Born success of at least
`1/4` keeps the four-attempt success probability at least `2/3`, and a phase-free direction
error `δ` of the unperturbed amplitudes becomes a trace distance of at most `6 δ + 12 η` of the
perturbed conditional output (`perturb_four`). No per-trial direction bound is needed for the
perturbed amplitudes: a branch is weighted by its Born probability, so small amplitudes of
uncontrolled direction contribute only `O(η)`.
-/

set_option autoImplicit false

namespace SparseHamiltonian.GateSynth

noncomputable section
open ContinuousLinearMap
open ODEStateNormalization (unitDirection unitDirection_norm)
open scoped InnerProduct BigOperators

section Perturb

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- A vector is its norm times its direction. -/
theorem norm_smul_unitDirection (x : E) : ‖x‖ • unitDirection x = x := by
  by_cases hx : x = 0
  · subst hx
    simp [unitDirection]
  · rw [unitDirection, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx), one_smul]

/-- A phase-free direction error in unnormalised form. -/
theorem norm_smul_sub_norm_smul (x v : E) (ω : ℂ) :
    ‖ω • x - ‖x‖ • v‖ = ‖x‖ * ‖ω • unitDirection x - v‖ := by
  have e : ω • x - ‖x‖ • v = ‖x‖ • (ω • unitDirection x - v) := by
    rw [smul_sub, smul_comm, norm_smul_unitDirection]
  rw [e, norm_smul, Real.norm_eq_abs, abs_norm]

/-- The direction bound of an amplitude, in unnormalised form, also for the zero amplitude. -/
theorem exists_phase_le (x v : E) {δ : ℝ}
    (h : x ≠ 0 → ∃ ω : ℂ, ‖ω‖ = 1 ∧ ‖ω • unitDirection x - v‖ ≤ δ) :
    ∃ ω : ℂ, ‖ω‖ = 1 ∧ ‖ω • x - ‖x‖ • v‖ ≤ ‖x‖ * δ := by
  by_cases hx : x = 0
  · refine ⟨1, norm_one, ?_⟩
    subst hx
    simp
  · obtain ⟨ω, hω, hd⟩ := h hx
    refine ⟨ω, hω, ?_⟩
    rw [norm_smul_sub_norm_smul]
    exact mul_le_mul_of_nonneg_left hd (norm_nonneg _)

/-- **One perturbed branch**: Born weight times the diagonal mass of its deviation from the
target state. -/
theorem branch_le (a a' v : E) (hv : ‖v‖ = 1) {δ η : ℝ} (hδ : 0 ≤ δ) (ha : ‖a‖ ≤ 1)
    (ha' : ‖a'‖ ≤ 1) (hclose : ‖a' - a‖ ≤ η)
    (hdir : a ≠ 0 → ∃ ω : ℂ, ‖ω‖ = 1 ∧ ‖ω • unitDirection a - v‖ ≤ δ)
    {α : Type*} [Fintype α] (b : OrthonormalBasis α ℂ E) :
    ‖a'‖ ^ 2 * ODEMixedOutput.diagonalMass b
      (ODEMixedOutput.pureOperator (unitDirection a') - ODEMixedOutput.pureOperator v) ≤
      2 * (δ + 2 * η) := by
  have hη : 0 ≤ η := (norm_nonneg _).trans hclose
  by_cases h0 : a' = 0
  · rw [h0, norm_zero]
    have : 0 ≤ δ + 2 * η := by linarith
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul]
    linarith
  obtain ⟨ω, hω, hd⟩ := exists_phase_le a v hdir
  have hu : ‖ω • unitDirection a'‖ = 1 := by
    rw [norm_smul, hω, unitDirection_norm a' h0, one_mul]
  have hD : ODEMixedOutput.diagonalMass b
      (ODEMixedOutput.pureOperator (unitDirection a') - ODEMixedOutput.pureOperator v) ≤
      2 * ‖ω • unitDirection a' - v‖ := by
    rw [← ODEMixedOutput.pureOperator_phase ω hω (unitDirection a')]
    exact ODEMixedOutput.diagonalMass_pure_sub_le b _ _ hu hv
  have hvec : ‖ω • a' - ‖a'‖ • v‖ ≤ 2 * η + δ := by
    have e : ω • a' - ‖a'‖ • v =
        ω • (a' - a) + (ω • a - ‖a‖ • v) + (‖a‖ - ‖a'‖) • v := by
      rw [smul_sub, sub_smul]
      abel
    have h1 : ‖ω • (a' - a)‖ ≤ η := by rw [norm_smul, hω, one_mul]; exact hclose
    have h3 : ‖(‖a‖ - ‖a'‖) • v‖ ≤ η := by
      rw [norm_smul, hv, mul_one, Real.norm_eq_abs]
      exact (abs_norm_sub_norm_le a a').trans (by rw [norm_sub_rev]; exact hclose)
    have h2 : ‖ω • a - ‖a‖ • v‖ ≤ δ :=
      hd.trans (mul_le_of_le_one_left hδ ha)
    rw [e]
    refine (norm_add_le _ _).trans ?_
    refine (add_le_add (norm_add_le _ _) h3).trans ?_
    linarith
  rw [norm_smul_sub_norm_smul] at hvec
  have hn := norm_nonneg a'
  have hD0 : 0 ≤ ‖ω • unitDirection a' - v‖ := norm_nonneg _
  calc ‖a'‖ ^ 2 * ODEMixedOutput.diagonalMass b
        (ODEMixedOutput.pureOperator (unitDirection a') - ODEMixedOutput.pureOperator v)
      ≤ ‖a'‖ ^ 2 * (2 * ‖ω • unitDirection a' - v‖) :=
        mul_le_mul_of_nonneg_left hD (sq_nonneg _)
    _ = 2 * ‖a'‖ * (‖a'‖ * ‖ω • unitDirection a' - v‖) := by ring
    _ ≤ 2 * 1 * (2 * η + δ) := by
        apply mul_le_mul (by linarith) hvec (by positivity) (by norm_num)
    _ = 2 * (δ + 2 * η) := by ring

variable [FiniteDimensional ℂ E]

/-- **Perturbation of the four-attempt protocol.** Let `a j` be the decoded amplitudes of the
trials, with mean Born success at least `1/4` and every nonzero amplitude within `δ` of the
target direction `v` up to a phase, and let `a' j` be amplitudes within `η ≤ 1/400` of them,
all of norm at most one. Then the four-attempt success probability of the amplitudes `a'` is at
least `2/3`, and their conditional output is a density operator within trace distance
`6 δ + 12 η` of `v`. -/
theorem perturb_four {M : ℕ} (hM : 0 < M) (a a' : Fin M → E) (v : E) (hv : ‖v‖ = 1)
    {δ η : ℝ} (hδ : 0 ≤ δ) (hη1 : η ≤ 1 / 400)
    (ha : ∀ j, ‖a j‖ ≤ 1) (ha' : ∀ j, ‖a' j‖ ≤ 1) (hclose : ∀ j, ‖a' j - a j‖ ≤ η)
    (hmean : 1 / 4 ≤ ODERepeatProbability.mean (fun j => ‖a j‖ ^ 2))
    (hdir : ∀ j, a j ≠ 0 → ∃ ω : ℂ, ‖ω‖ = 1 ∧ ‖ω • unitDirection (a j) - v‖ ≤ δ) :
    (2 : ℝ) / 3 ≤ ODERepeatProbability.successProbability (fun j => ‖a' j‖ ^ 2) ∧
    ODEMixedOutput.IsDensity (ODEMixedOutput.ensemble
      (ODERepeatProbability.conditionalWeight (fun j => ‖a' j‖ ^ 2))
      (fun b : Fin 4 × Fin M => unitDirection (a' b.2))) ∧
    ∃ h : (ODEMixedOutput.ensemble
        (ODERepeatProbability.conditionalWeight (fun j => ‖a' j‖ ^ 2))
        (fun b : Fin 4 × Fin M => unitDirection (a' b.2)) -
        ODEMixedOutput.pureOperator v).toLinearMap.IsSymmetric,
      ODEMixedOutput.hermitianTraceDistance (ODEMixedOutput.ensemble
        (ODERepeatProbability.conditionalWeight (fun j => ‖a' j‖ ^ 2))
        (fun b : Fin 4 × Fin M => unitDirection (a' b.2)))
        (ODEMixedOutput.pureOperator v) h ≤ 6 * δ + 12 * η := by
  set p' : Fin M → ℝ := fun j => ‖a' j‖ ^ 2 with hp'
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hη : 0 ≤ η := (norm_nonneg _).trans (hclose ⟨0, hM⟩)
  -- the mean success moves by at most `2 η`
  have hpt : ∀ j, ‖a j‖ ^ 2 - 2 * η ≤ p' j := by
    intro j
    have h1 : ‖a j‖ - ‖a' j‖ ≤ η := by
      have := norm_sub_norm_le (a j) (a' j)
      rw [norm_sub_rev] at this
      linarith [hclose j]
    have h0 := norm_nonneg (a j)
    have h0' := norm_nonneg (a' j)
    have k1 : 0 ≤ (η - (‖a j‖ - ‖a' j‖)) * (‖a j‖ + ‖a' j‖) :=
      mul_nonneg (by linarith) (by linarith)
    have k2 : 0 ≤ η * (2 - ‖a j‖ - ‖a' j‖) := mul_nonneg hη (by linarith [ha j, ha' j])
    simp only [hp']
    nlinarith
  have hmean' : 1 / 4 - 2 * η ≤ ODERepeatProbability.mean p' := by
    have hs : ∑ j, (‖a j‖ ^ 2 - 2 * η) ≤ ∑ j, p' j :=
      Finset.sum_le_sum (fun j _ => hpt j)
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] at hs
    have hm := hmean
    unfold ODERepeatProbability.mean at hm ⊢
    rw [le_div_iff₀ hMr] at hm ⊢
    nlinarith
  have hupper : ODERepeatProbability.mean p' ≤ 1 :=
    ODERepeatProbability.mean_le_one p' hM
      (fun j => pow_le_one₀ (norm_nonneg _) (ha' j))
  -- the success probability
  have hS : (2 : ℝ) / 3 ≤ ODERepeatProbability.successProbability p' := by
    rw [ODERepeatProbability.successProbability_eq]
    have h0 : 0 ≤ 1 - ODERepeatProbability.mean p' := sub_nonneg.mpr hupper
    have h1 : 1 - ODERepeatProbability.mean p' ≤ 151 / 200 := by linarith
    have hp := pow_le_pow_left₀ h0 h1 4
    norm_num at hp ⊢
    linarith
  have hSpos : 0 < ODERepeatProbability.successProbability p' := by linarith
  -- the conditional mixture is a density operator
  set w := ODERepeatProbability.conditionalWeight p' with hw_def
  set u : Fin 4 × Fin M → E := fun b => unitDirection (a' b.2) with hu_def
  have hw : ∀ b, 0 ≤ w b := fun b =>
    div_nonneg (ODERepeatProbability.firstSuccessWeight_nonneg p' (fun j => sq_nonneg _)
      hupper b.1 b.2) hSpos.le
  have hsum : ∑ b, w b = 1 := by
    simp only [hw_def, ODERepeatProbability.conditionalWeight, ← Finset.sum_div,
      Fintype.sum_prod_type]
    exact div_self hSpos.ne'
  have hne : ∀ b, w b ≠ 0 → a' b.2 ≠ 0 := by
    intro b hb hz
    apply ODERepeatProbability.conditionalWeight_ne_zero_implies p' b hb
    simp only [hp', hz, norm_zero]
    norm_num
  have hu : ∀ b, w b ≠ 0 → ‖u b‖ = 1 := fun b hb => unitDirection_norm _ (hne b hb)
  have hdensity := ODEMixedOutput.ensemble_isDensity w u hw hsum hu
  have hherm :
      (ODEMixedOutput.ensemble w u - ODEMixedOutput.pureOperator v).toLinearMap.IsSymmetric :=
    hdensity.1.isSymmetric.sub (ODEMixedOutput.pureOperator_positive v).isSymmetric
  refine ⟨hS, hdensity, hherm, ?_⟩
  -- the trace distance
  rw [ODEMixedOutput.hermitianTraceDistance_eq_diagonalMass]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
  set bas := hherm.eigenvectorBasis (n := Module.finrank ℂ E) rfl
  have hterm : ∀ b : Fin 4 × Fin M, w b * ODEMixedOutput.diagonalMass bas
      (ODEMixedOutput.pureOperator (u b) - ODEMixedOutput.pureOperator v) ≤
      2 * (δ + 2 * η) / (M * ODERepeatProbability.successProbability p') := by
    intro b
    have hc0 : 0 ≤ (1 - ODERepeatProbability.mean p') ^ b.1.val :=
      pow_nonneg (sub_nonneg.mpr hupper) _
    have hc1 : (1 - ODERepeatProbability.mean p') ^ b.1.val ≤ 1 :=
      pow_le_one₀ (sub_nonneg.mpr hupper) (by linarith)
    have hB := branch_le (a b.2) (a' b.2) v hv hδ (ha b.2) (ha' b.2) (hclose b.2) (hdir b.2) bas
    have hD0 : 0 ≤ ODEMixedOutput.diagonalMass bas
        (ODEMixedOutput.pureOperator (u b) - ODEMixedOutput.pureOperator v) :=
      Finset.sum_nonneg (fun i _ => norm_nonneg _)
    have e : w b * ODEMixedOutput.diagonalMass bas
        (ODEMixedOutput.pureOperator (u b) - ODEMixedOutput.pureOperator v) =
        (1 - ODERepeatProbability.mean p') ^ b.1.val *
          (‖a' b.2‖ ^ 2 * ODEMixedOutput.diagonalMass bas
            (ODEMixedOutput.pureOperator (unitDirection (a' b.2)) -
              ODEMixedOutput.pureOperator v)) /
          (M * ODERepeatProbability.successProbability p') := by
      simp only [hw_def, hu_def, ODERepeatProbability.conditionalWeight,
        ODERepeatProbability.firstSuccessWeight_eq, hp']
      field_simp
    rw [e]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have hB0 : 0 ≤ ‖a' b.2‖ ^ 2 * ODEMixedOutput.diagonalMass bas
        (ODEMixedOutput.pureOperator (unitDirection (a' b.2)) -
          ODEMixedOutput.pureOperator v) := mul_nonneg (sq_nonneg _) hD0
    calc (1 - ODERepeatProbability.mean p') ^ b.1.val *
          (‖a' b.2‖ ^ 2 * ODEMixedOutput.diagonalMass bas
            (ODEMixedOutput.pureOperator (unitDirection (a' b.2)) -
              ODEMixedOutput.pureOperator v))
        ≤ 1 * (2 * (δ + 2 * η)) := mul_le_mul hc1 hB hB0 zero_le_one
      _ = 2 * (δ + 2 * η) := one_mul _
  rw [ODEMixedOutput.ensemble_sub_pureOperator w u v hsum]
  calc ODEMixedOutput.diagonalMass bas
        (∑ b, (w b : ℂ) • (ODEMixedOutput.pureOperator (u b) - ODEMixedOutput.pureOperator v))
      ≤ ∑ b, ODEMixedOutput.diagonalMass bas
          ((w b : ℂ) • (ODEMixedOutput.pureOperator (u b) - ODEMixedOutput.pureOperator v)) :=
        ODEMixedOutput.diagonalMass_sum_le bas _
    _ = ∑ b, w b * ODEMixedOutput.diagonalMass bas
          (ODEMixedOutput.pureOperator (u b) - ODEMixedOutput.pureOperator v) := by
        apply Finset.sum_congr rfl
        intro b _
        rw [ODEMixedOutput.diagonalMass_smul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (hw b)]
    _ ≤ ∑ _b : Fin 4 × Fin M,
          2 * (δ + 2 * η) / (M * ODERepeatProbability.successProbability p') :=
        Finset.sum_le_sum (fun b _ => hterm b)
    _ = 4 * M * (2 * (δ + 2 * η) / (M * ODERepeatProbability.successProbability p')) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
          Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring
    _ = 8 * (δ + 2 * η) / ODERepeatProbability.successProbability p' := by
        field_simp
        ring
    _ ≤ (6 * δ + 12 * η) * 2 := by
        rw [div_le_iff₀ hSpos]
        nlinarith

end Perturb

end

end SparseHamiltonian.GateSynth
