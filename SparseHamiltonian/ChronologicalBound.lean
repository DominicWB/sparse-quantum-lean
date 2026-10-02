import SparseHamiltonian.FiniteChronologicalInverse

/-!
# Weighted chronological response bound

The aggregate bound depends on the weighted product `T*w*qbar`, rather than
on the time discretisation size alone. All local inputs are genuine operator
norm inequalities; the underlying finite block operator is explicitly defined.
-/

namespace SparseHamiltonian.ChronologicalBound

open ContinuousLinearMap
open SparseHamiltonian.ChronologicalResolvent

variable {P V : Type*}
  [NormedAddCommGroup P] [NormedSpace ℂ P]
  [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- The two local endpoint bounds give the required product of coupling norms. -/
theorem coupling_norm_product_le (A : P →L[ℂ] V) (B : V →L[ℂ] P)
    (σ : ℂ) {w b qbar : ℝ} (hw : 0 ≤ w) (hb : 0 ≤ b)
    (hσ : ‖σ‖ ^ 2 ≤ 2 * w) (hbq : b ^ 2 ≤ qbar / 2)
    (hA : ‖A‖ ≤ 12 * b / 7) (hB : ‖B‖ ≤ 12 * b / 7) :
    ‖σ • A‖ * ‖(-σ) • B‖ ≤ (144 / 49 : ℝ) * w * qbar := by
  have hProduct : ‖A‖ * ‖B‖ ≤ (12 * b / 7) ^ 2 := by
    simpa only [pow_two] using
      mul_le_mul hA hB (norm_nonneg B) (by positivity : 0 ≤ 12 * b / 7)
  calc
    _ = ‖σ‖ ^ 2 * (‖A‖ * ‖B‖) := by rw [norm_smul, norm_smul, norm_neg]; ring
    _ ≤ (2 * w) * (12 * b / 7) ^ 2 :=
      mul_le_mul hσ hProduct (mul_nonneg (norm_nonneg A) (norm_nonneg B)) (by positivity)
    _ = ((288 / 49 : ℝ) * w) * b ^ 2 := by ring
    _ ≤ ((288 / 49 : ℝ) * w) * (qbar / 2) :=
      mul_le_mul_of_nonneg_left hbq (by positivity)
    _ = (144 / 49 : ℝ) * w * qbar := by ring

/-- The weighted chronological bound has no independent exponential dependence
on the number of time slots. Its premises are the local norm and transfer bounds. -/
theorem chronological_norm_le_weighted
    (R : V →L[ℂ] V) (A : P →L[ℂ] V) (u : P →L[ℂ] P) (B : V →L[ℂ] P)
    (T : ℕ) {Q w qbar : ℝ} (hQ : 0 < Q) (hw : 0 ≤ w) (hq : 0 ≤ qbar)
    (hR : ‖R‖ ≤ 2 * Q)
    (hCoupling : ‖A‖ * ‖B‖ ≤ (144 / 49 : ℝ) * w * qbar)
    (hu : ‖u‖ ≤ 1 + 3 * w * qbar / (4 * Q)) :
    ‖chronologicalOperator R A u B T‖ ≤
      3 * (Q + (T : ℝ) * w * qbar) *
        Real.exp (3 * ((T : ℝ) * w * qbar) / (4 * Q)) := by
  have hTotal : (T : ℝ) * (‖A‖ * ‖B‖) ≤
      (144 / 49 : ℝ) * ((T : ℝ) * w * qbar) := by
    calc
      _ ≤ (T : ℝ) * ((144 / 49 : ℝ) * w * qbar) :=
        mul_le_mul_of_nonneg_left hCoupling (Nat.cast_nonneg _)
      _ = _ := by ring
  have hExp : 1 ≤ Real.exp (3 * ((T : ℝ) * w * qbar) / (4 * Q)) :=
    Real.one_le_exp_iff.mpr (by positivity)
  have hBound := chronologicalOperator_norm_le_of_local_bounds R A u B
    (by positivity : 0 ≤ 3 * w * qbar / (4 * Q)) hu T hR hTotal
    (le_of_eq (by ring :
      (T : ℝ) * (3 * w * qbar / (4 * Q)) =
        3 * ((T : ℝ) * w * qbar) / (4 * Q)))
  calc
    _ ≤ 2 * Q + (144 / 49 : ℝ) * ((T : ℝ) * w * qbar) *
        Real.exp (3 * ((T : ℝ) * w * qbar) / (4 * Q)) := hBound
    _ ≤ _ := by
      have hW : 0 ≤ (T : ℝ) * w * qbar := by positivity
      have hQE := mul_nonneg hQ.le (sub_nonneg.mpr hExp)
      have hWE := mul_nonneg hW
        (Real.exp_pos (3 * ((T : ℝ) * w * qbar) / (4 * Q))).le
      nlinarith

/-- Specialization using the explicit scaled incoming and outgoing endpoints. -/
theorem chronological_norm_le_of_endpoints
    (R : V →L[ℂ] V) (A : P →L[ℂ] V) (u : P →L[ℂ] P) (B : V →L[ℂ] P)
    (σ : ℂ) (T : ℕ) {Q w qbar b : ℝ}
    (hQ : 0 < Q) (hw : 0 ≤ w) (hq : 0 ≤ qbar) (hb : 0 ≤ b)
    (hR : ‖R‖ ≤ 2 * Q) (hσ : ‖σ‖ ^ 2 ≤ 2 * w) (hbq : b ^ 2 ≤ qbar / 2)
    (hA : ‖A‖ ≤ 12 * b / 7) (hB : ‖B‖ ≤ 12 * b / 7)
    (hu : ‖u‖ ≤ 1 + 3 * w * qbar / (4 * Q)) :
    ‖chronologicalOperator R (σ • A) u ((-σ) • B) T‖ ≤
      3 * (Q + (T : ℝ) * w * qbar) *
        Real.exp (3 * ((T : ℝ) * w * qbar) / (4 * Q)) :=
  chronological_norm_le_weighted R (σ • A) u ((-σ) • B) T hQ hw hq hR
    (coupling_norm_product_le A B σ hw hb hσ hbq hA hB) hu

/-- Local inverses and weighted local bounds produce a two-sided inverse of
the explicitly constructed chronological private block, with its uniform norm
estimate. The inverse of the global block is constructed, not a premise. -/
theorem exists_chronological_resolvent
    (Dloc R : V →L[ℂ] V) (A : P →L[ℂ] V)
    (c : P →L[ℂ] P) (B : V →L[ℂ] P) (T : ℕ) (z : ℂ)
    {Q w qbar : ℝ} (hQ : 0 < Q) (hw : 0 ≤ w) (hq : 0 ≤ qbar)
    (hRight : (z • 1 - Dloc) ∘L R = 1) (hLeft : R ∘L (z • 1 - Dloc) = 1)
    (hR : ‖R‖ ≤ 2 * Q)
    (hCoupling : ‖R ∘L A‖ * ‖B ∘L R‖ ≤ (144 / 49 : ℝ) * w * qbar)
    (hu : ‖c + B ∘L R ∘L A‖ ≤ 1 + 3 * w * qbar / (4 * Q)) :
    ∃ S : BlockOperator.H T V →L[ℂ] BlockOperator.H T V,
      (z • 1 - chronologicalOperator Dloc A c B T) ∘L S = 1 ∧
      S ∘L (z • 1 - chronologicalOperator Dloc A c B T) = 1 ∧
      ‖S‖ ≤ 3 * (Q + (T : ℝ) * w * qbar) *
        Real.exp (3 * ((T : ℝ) * w * qbar) / (4 * Q)) := by
  obtain ⟨hRinv, hLinv⟩ := FiniteChronologicalInverse.resolvent_two_sided_inverse
    Dloc R A c B T z hRight hLeft
  refine ⟨FiniteChronologicalInverse.inverseOperator R A c B T, hRinv, hLinv, ?_⟩
  exact chronological_norm_le_weighted R (R ∘L A) (c + B ∘L R ∘L A)
    (B ∘L R) T hQ hw hq hR hCoupling hu

end SparseHamiltonian.ChronologicalBound
