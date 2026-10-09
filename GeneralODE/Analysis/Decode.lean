import GeneralODE.Analysis.Accuracy
import GeneralODE.Block.Standard
import SparseHamiltonian.ODEStateNormalization

/-!
# Decoding the final time from the history state

The decoder is the isometry `v ↦ (uniform superposition of the final slots
m+1, …, 2m) ⊗ v`.  Its adjoint sends the history solution to `√m` times the
common final copy.  An output whose direction is within `δ` of the
direction of the history solution decodes, up to a phase, to within `2δ/θ`
of the direction of the final copy, where `θ` is the decoded fraction of the
exact history; the decoded amplitude is at least `(θ - δ)` times the output
norm.
-/

namespace SparseHamiltonian.GeneralODE.Decode

noncomputable section
open ContinuousLinearMap History ODEStateNormalization Registers
open scoped InnerProduct BigOperators ComplexConjugate

section Geometry

variable {P Q : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] [CompleteSpace Q]

omit [CompleteSpace Q] in
/-- Directions of complex multiples. -/
theorem unitDirection_smul (c : ℂ) (hc : c ≠ 0) (w : Q) :
    unitDirection (c • w) = (c / (‖c‖ : ℂ)) • unitDirection w := by
  unfold unitDirection
  have hc' : 0 < ‖c‖ := norm_pos_iff.mpr hc
  rw [norm_smul, ← Complex.coe_smul, ← Complex.coe_smul, smul_smul, smul_smul]
  have : (‖c‖ : ℂ) ≠ 0 := by exact_mod_cast hc'.ne'
  congr 1
  push_cast
  field_simp

omit [CompleteSpace Q] in
theorem unitDirection_real_smul (r : ℝ) (hr : 0 < r) (w : Q) :
    unitDirection (r • w) = unitDirection w := by
  unfold unitDirection
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, smul_smul]
  congr 1
  field_simp

theorem norm_adjoint_le_one (Dc : P →L[ℂ] Q) (hDc : Dc† ∘L Dc = 1) : ‖Dc†‖ ≤ 1 := by
  rw [ContinuousLinearMap.adjoint.norm_map]
  exact norm_le_one_of_isometry Dc hDc

/-- Decoding a nearly parallel output. -/
theorem decode (Dc : P →L[ℂ] Q) (hDc : Dc† ∘L Dc = 1) (y z : Q) (hy : y ≠ 0)
    (θ δ : ℝ) (hθ0 : 0 < θ) (hθ : θ * ‖y‖ ≤ ‖(Dc†) y‖) (hδθ : δ < θ)
    (ω : ℂ) (hω : ‖ω‖ = 1) (hz : ‖ω • unitDirection z - unitDirection y‖ ≤ δ) :
    ‖z‖ * (θ - δ) ≤ ‖(Dc†) z‖ ∧
      ‖ω • unitDirection ((Dc†) z) - unitDirection ((Dc†) y)‖ ≤ 2 * δ / θ := by
  have hy0 : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hDcn := norm_adjoint_le_one Dc hDc
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans hz
  -- `z ≠ 0`
  have hz0 : z ≠ 0 := by
    intro h
    rw [h] at hz
    simp only [unitDirection, norm_zero, inv_zero, smul_zero, zero_sub, norm_neg] at hz
    rw [show ‖‖y‖⁻¹ • y‖ = 1 from unitDirection_norm y hy] at hz
    have hθ1 : θ ≤ 1 := by
      have := hθ.trans (((Dc†).le_opNorm y).trans (mul_le_mul_of_nonneg_right hDcn (norm_nonneg _)))
      nlinarith
    linarith
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  set u := unitDirection y with hu
  set v := ω • unitDirection z with hv
  have hu' : (Dc†) u = ((‖y‖⁻¹ : ℝ) : ℂ) • (Dc†) y := by
    rw [hu, unitDirection, ← Complex.coe_smul, map_smul]
  have hv' : (Dc†) v = (ω / (‖z‖ : ℂ)) • (Dc†) z := by
    rw [hv, unitDirection, ← Complex.coe_smul, smul_smul, map_smul]
    congr 1
    push_cast
    ring
  have hdiff : ‖(Dc†) v - (Dc†) u‖ ≤ δ := by
    rw [← map_sub]
    exact ((Dc†).le_opNorm _).trans (by
      calc ‖Dc†‖ * ‖v - u‖ ≤ 1 * δ := mul_le_mul hDcn hz (norm_nonneg _) zero_le_one
        _ = δ := one_mul δ)
  have hun : θ ≤ ‖(Dc†) u‖ := by
    rw [hu', norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hy0)]
    rw [le_inv_mul_iff₀ hy0]
    linarith [mul_comm θ ‖y‖]
  have hvn : θ - δ ≤ ‖(Dc†) v‖ := by
    have := norm_sub_norm_le ((Dc†) u) ((Dc†) v)
    rw [norm_sub_rev] at this
    linarith
  have hωz : ‖ω / (‖z‖ : ℂ)‖ = ‖z‖⁻¹ := by
    rw [norm_div, hω, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hzn, one_div]
  constructor
  · rw [hv', norm_smul, hωz] at hvn
    exact (le_inv_mul_iff₀ hzn).mp hvn
  · have hu0 : (Dc†) u ≠ 0 := by
      intro h; rw [h, norm_zero] at hun; linarith
    have hv0 : (Dc†) v ≠ 0 := by
      intro h; rw [h, norm_zero] at hvn; linarith
    have herr := unitDirection_error_le ((Dc†) u) ((Dc†) v) hu0 hv0
    have hdu : unitDirection ((Dc†) u) = unitDirection ((Dc†) y) := by
      rw [hu', Complex.coe_smul]; exact unitDirection_real_smul _ (inv_pos.mpr hy0) _
    have hdv : unitDirection ((Dc†) v) = ω • unitDirection ((Dc†) z) := by
      have hc : ω / (‖z‖ : ℂ) ≠ 0 := by
        intro h
        have := congrArg norm h
        rw [hωz, norm_zero] at this
        exact (inv_pos.mpr hzn).ne' this
      rw [hv', unitDirection_smul _ hc, hωz]
      congr 1
      have hz' : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast hzn.ne'
      push_cast
      field_simp
    rw [hdu, hdv] at herr
    refine herr.trans ?_
    rw [div_le_div_iff₀ (by linarith) hθ0]
    have h1 : 2 * ‖(Dc†) v - (Dc†) u‖ * θ ≤ 2 * δ * θ :=
      mul_le_mul_of_nonneg_right (by linarith) hθ0.le
    have h2 : 2 * δ * θ ≤ 2 * δ * ‖(Dc†) u‖ :=
      mul_le_mul_of_nonneg_left hun (by positivity)
    linarith

end Geometry

section FinalSlots

variable {n : Type} [Fintype n] [DecidableEq n]

/-- Uniform superposition of the final slots `m + 1, …, 2m`. -/
def finalSlots (m : ℕ) : EuclideanSpace ℂ (Slot m) :=
  WithLp.toLp 2 (fun s => match s with
    | none => 0
    | some j => if m < j.val then (((Real.sqrt m)⁻¹ : ℝ) : ℂ) else 0)

theorem sum_final {M : Type*} [AddCommMonoid M] (m : ℕ) (f : ℕ → M) :
    ∑ j : Fin (2 * m + 1), (if m < j.val then f j.val else 0) =
      ∑ x ∈ Finset.range m, f (m + 1 + x) := by
  rw [Fin.sum_univ_eq_sum_range (fun j => if m < j then f j else 0) (2 * m + 1),
    show 2 * m + 1 = (m + 1) + m by ring, Finset.sum_range_add]
  have h1 : ∑ x ∈ Finset.range (m + 1), (if m < x then f x else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    have : ¬ m < x := by have := Finset.mem_range.mp hx; omega
    simp [this]
  rw [h1, zero_add]
  apply Finset.sum_congr rfl
  intro x _
  rw [if_pos (by omega)]

theorem finalSlots_norm (m : ℕ) (hm : 1 ≤ m) : ‖finalSlots m‖ = 1 := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hsq : ‖finalSlots m‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq, Fintype.sum_option]
    have hterm : ∀ j : Fin (2 * m + 1), ‖finalSlots m (some j)‖ ^ 2 =
        (if m < j.val then (1 / m : ℝ) else 0) := by
      intro j
      change ‖(if m < j.val then (((Real.sqrt m)⁻¹ : ℝ) : ℂ) else 0)‖ ^ 2 = _
      split_ifs
      · rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, inv_pow, Real.sq_sqrt hm0.le, one_div]
      · simp
    simp only [hterm]
    rw [sum_final m (fun _ => (1 / m : ℝ)), Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    change ‖(0 : ℂ)‖ ^ 2 + _ = 1
    rw [norm_zero]
    field_simp
    ring
  have h0 : 0 ≤ ‖finalSlots m‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖finalSlots m‖ - 1)]

/-- The final-time decoder `v ↦ |final⟩ ⊗ v`. -/
def decoder (m : ℕ) : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ (Slot m × n) :=
  ketL (finalSlots m)

omit [DecidableEq n] in
theorem decoder_isometry (m : ℕ) (hm : 1 ≤ m) : (decoder (n := n) m)† ∘L decoder m = 1 :=
  ketL_isometry _ (finalSlots_norm m hm)

omit [DecidableEq n] in
/-- The decoder applied to the history solution gives `√m` times its final copy. -/
theorem decoder_adjoint_solution (m : ℕ) (hm : 1 ≤ m)
    (V Φ Q0 : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) (μ : ℝ) (x0 b : EuclideanSpace ℂ n) :
    ((decoder (n := n) m)†) (RegisterEquivalences.productFlatten (Slot m) n
        (History.solution m V Φ Q0 μ x0 b)) =
      ((Real.sqrt m : ℝ) : ℂ) • solSeq m V Φ Q0 μ x0 b m := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  unfold decoder
  rw [ketL_adjoint]
  ext i
  rw [braL_apply, Fintype.sum_option]
  have hterm : ∀ j : Fin (2 * m + 1),
      conj (finalSlots m (some j)) *
        (RegisterEquivalences.productFlatten (Slot m) n (History.solution m V Φ Q0 μ x0 b))
          (some j, i) =
      (if m < j.val then (((Real.sqrt m)⁻¹ : ℝ) : ℂ) * solSeq m V Φ Q0 μ x0 b m i else 0) := by
    intro j
    change conj (if m < j.val then (((Real.sqrt m)⁻¹ : ℝ) : ℂ) else 0) *
      (History.solution m V Φ Q0 μ x0 b (some j)) i = _
    split_ifs with hj
    · rw [solution_copy m V Φ Q0 μ x0 b j hj.le, Complex.conj_ofReal]
    · simp
  simp only [hterm]
  rw [sum_final m (fun _ => (((Real.sqrt m)⁻¹ : ℝ) : ℂ) * solSeq m V Φ Q0 μ x0 b m i),
    Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  change conj (0 : ℂ) * _ + _ = _
  rw [map_zero, zero_mul, zero_add, PiLp.smul_apply, smul_eq_mul]
  have hs : Real.sqrt m ≠ 0 := (Real.sqrt_pos.mpr hm0).ne'
  have hsq : Real.sqrt m * Real.sqrt m = m := Real.mul_self_sqrt hm0.le
  have hsC : ((Real.sqrt m : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs
  rw [← mul_assoc]
  congr 1
  push_cast
  field_simp
  have : ((Real.sqrt m : ℝ) : ℂ) * ((Real.sqrt m : ℝ) : ℂ) = (m : ℂ) := by
    rw [← Complex.ofReal_mul, hsq]; push_cast; rfl
  linear_combination -this

end FinalSlots

end

end SparseHamiltonian.GeneralODE.Decode
