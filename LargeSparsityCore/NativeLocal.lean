import NativeSignedFactor.Factor

set_option autoImplicit false

/-!
# Clipping and the local frame of the joint representation

The large-sparsity core clips the entries (`opt:eq:clip`, with `β = h`): a decoded entry `z`
is split as `z/η = c₁ + c₂` with the clipped part `c₁ = (z/η)/(1 + β|z|/η)` (`cclip`) and the
correction `c₂ = z/η - c₁` (`ccorr`, clipped to the unit disk so that every value word gives a
unitary local gate). Then `β |c₁| ≤ 1`, `|c₂| ≤ β |z|²/η²` and, for `|z| ≤ η`, `c₁ + c₂ = z/η`.

Both parts are nonnegative multiples of `z`, so they have the same phase (`phase_ccorr`); the
orientation change `V(c)†` of the native factor (`NativeSignedFactor.orient`) therefore
diagonalises the edge generators `E(c₁)` and `E(c₂)` at the same time. This is what allows one
local frame, the local gate `NativeSignedFactor.localOp c₂` of the correction factor, to carry
the whole joint generator: on the flags `0, 1` it is the signed correction factor, on flag `2`
the orientation change of the clipped entry (`inner_Ocl_sign`).
-/

namespace LargeSparsityCore.Native

noncomputable section

open ContinuousLinearMap SparseHamiltonian NativeSignedFactor
open scoped InnerProduct ComplexConjugate

/-! ### Clipped and correction entries -/

/-- The clipped entry `c₁ = (z/η)/(1 + β|z|/η)` (`opt:eq:clip`). -/
def cclip (η β : ℝ) (z : ℂ) : ℂ := (((1 + β * ‖z‖ / η)⁻¹ : ℝ) : ℂ) * (z / η)

/-- The correction entry `c₂ = z/η - c₁`, radially clipped to the unit disk. -/
def ccorr (η β : ℝ) (z : ℂ) : ℂ := clip (z / η - cclip η β z)

variable {η β : ℝ}

theorem one_add_pos (hη : 0 < η) (hβ : 0 ≤ β) (z : ℂ) : 0 < 1 + β * ‖z‖ / η := by positivity

theorem sub_cclip (hη : 0 < η) (hβ : 0 ≤ β) (z : ℂ) :
    z / η - cclip η β z = (((β * ‖z‖ / η) / (1 + β * ‖z‖ / η) : ℝ) : ℂ) * (z / η) := by
  have h := one_add_pos hη hβ z
  have e : (1 : ℝ) - (1 + β * ‖z‖ / η)⁻¹ = (β * ‖z‖ / η) / (1 + β * ‖z‖ / η) := by
    field_simp
    ring
  unfold cclip
  rw [← e]
  push_cast
  ring

theorem norm_div_eta (hη : 0 < η) (z : ℂ) : ‖z / (η : ℂ)‖ = ‖z‖ / η := by
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hη]

theorem norm_cclip (hη : 0 < η) (hβ : 0 ≤ β) (z : ℂ) :
    ‖cclip η β z‖ = (1 + β * ‖z‖ / η)⁻¹ * (‖z‖ / η) := by
  have h := one_add_pos hη hβ z
  unfold cclip
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr h),
    norm_div_eta hη]

/-- `|c₁| ≤ |z|/η`. -/
theorem norm_cclip_le (hη : 0 < η) (hβ : 0 ≤ β) (z : ℂ) : ‖cclip η β z‖ ≤ ‖z‖ / η := by
  have h := one_add_pos hη hβ z
  rw [norm_cclip hη hβ]
  have h1 : (1 + β * ‖z‖ / η)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by
    have : 0 ≤ β * ‖z‖ / η := by positivity
    linarith)
  have h2 : 0 ≤ ‖z‖ / η := by positivity
  calc (1 + β * ‖z‖ / η)⁻¹ * (‖z‖ / η) ≤ 1 * (‖z‖ / η) := mul_le_mul_of_nonneg_right h1 h2
    _ = ‖z‖ / η := one_mul _

/-- `β |c₁| ≤ 1`. -/
theorem mul_norm_cclip_le (hη : 0 < η) (hβ : 0 ≤ β) (z : ℂ) : β * ‖cclip η β z‖ ≤ 1 := by
  have h := one_add_pos hη hβ z
  rw [norm_cclip hη hβ]
  have e : β * ((1 + β * ‖z‖ / η)⁻¹ * (‖z‖ / η)) =
      (β * ‖z‖ / η) / (1 + β * ‖z‖ / η) := by
    field_simp
  rw [e, div_le_one h]
  linarith

theorem norm_sub_cclip (hη : 0 < η) (hβ : 0 ≤ β) (z : ℂ) :
    ‖z / η - cclip η β z‖ = (β * ‖z‖ / η) / (1 + β * ‖z‖ / η) * (‖z‖ / η) := by
  have h := one_add_pos hη hβ z
  rw [sub_cclip hη hβ, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity), norm_div_eta hη]

/-- `|z/η - c₁| ≤ |z|/η`. -/
theorem norm_sub_cclip_le (hη : 0 < η) (hβ : 0 ≤ β) (z : ℂ) :
    ‖z / η - cclip η β z‖ ≤ ‖z‖ / η := by
  have h := one_add_pos hη hβ z
  rw [norm_sub_cclip hη hβ]
  have h1 : (β * ‖z‖ / η) / (1 + β * ‖z‖ / η) ≤ 1 := by
    rw [div_le_one h]
    linarith
  have h2 : 0 ≤ ‖z‖ / η := by positivity
  calc (β * ‖z‖ / η) / (1 + β * ‖z‖ / η) * (‖z‖ / η) ≤ 1 * (‖z‖ / η) :=
        mul_le_mul_of_nonneg_right h1 h2
    _ = ‖z‖ / η := one_mul _

/-- `|z/η - c₁| ≤ β |z|²/η²`. -/
theorem norm_sub_cclip_le_sq (hη : 0 < η) (hβ : 0 ≤ β) (z : ℂ) :
    ‖z / η - cclip η β z‖ ≤ β * ‖z‖ ^ 2 / η ^ 2 := by
  have h := one_add_pos hη hβ z
  rw [norm_sub_cclip hη hβ]
  have h1 : (β * ‖z‖ / η) / (1 + β * ‖z‖ / η) ≤ β * ‖z‖ / η := by
    apply div_le_self (by positivity)
    have : 0 ≤ β * ‖z‖ / η := by positivity
    linarith
  calc (β * ‖z‖ / η) / (1 + β * ‖z‖ / η) * (‖z‖ / η) ≤ (β * ‖z‖ / η) * (‖z‖ / η) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = β * ‖z‖ ^ 2 / η ^ 2 := by ring

theorem ccorr_eq (hη : 0 < η) (hβ : 0 ≤ β) {z : ℂ} (hz : ‖z‖ ≤ η) :
    ccorr η β z = z / η - cclip η β z := by
  apply clip_of_norm_le
  refine (norm_sub_cclip_le hη hβ z).trans ?_
  rw [div_le_one hη]
  exact hz

theorem norm_ccorr_le_one (z : ℂ) : ‖ccorr η β z‖ ≤ 1 := norm_clip_le _

/-- `|c₂| ≤ β |z|²/η²`. -/
theorem norm_ccorr_le (hη : 0 < η) (hβ : 0 ≤ β) (z : ℂ) :
    ‖ccorr η β z‖ ≤ β * ‖z‖ ^ 2 / η ^ 2 :=
  (norm_clip_le_norm _).trans (norm_sub_cclip_le_sq hη hβ z)

/-- For an entry in the disk of radius `η`: `c₁ + c₂ = z/η`. -/
theorem cclip_add_ccorr (hη : 0 < η) (hβ : 0 ≤ β) {z : ℂ} (hz : ‖z‖ ≤ η) :
    cclip η β z + ccorr η β z = z / η := by
  rw [ccorr_eq hη hβ hz]
  ring

theorem cclip_zero : cclip η β 0 = 0 := by simp [cclip]

/-! ### Phases -/

theorem phase_real_mul {r : ℝ} (hr : 0 < r) (w : ℂ) : phase ((r : ℂ) * w) = phase w := by
  unfold phase
  by_cases hw : w = 0
  · simp [hw]
  · have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    have hrw : (r : ℂ) * w ≠ 0 := mul_ne_zero hr' hw
    rw [if_neg hrw, if_neg hw, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    have hn : (‖w‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.mpr hw).ne'
    push_cast
    field_simp

theorem phase_clip (w : ℂ) : phase (clip w) = phase w := by
  unfold clip
  split_ifs with h
  · rfl
  · have hpos : 0 < ‖w‖ := lt_trans zero_lt_one (lt_of_not_ge h)
    have e : w / (‖w‖ : ℂ) = ((‖w‖⁻¹ : ℝ) : ℂ) * w := by
      push_cast
      ring
    rw [e, phase_real_mul (inv_pos.mpr hpos)]

/-- The clipped part and the correction have the same phase. -/
theorem phase_ccorr (hη : 0 < η) (hβ : 0 < β) (z : ℂ) :
    phase (ccorr η β z) = phase (cclip η β z) := by
  by_cases hz : z = 0
  · subst hz
    simp [ccorr, cclip_zero, clip]
  · have hz' : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have h := one_add_pos hη hβ.le z
    unfold ccorr
    rw [phase_clip, sub_cclip hη hβ.le, phase_real_mul (by positivity), cclip,
      phase_real_mul (inv_pos.mpr h)]

/-! ### The orientation change -/

/-- The orientation change `V(c)†` as an operator on the orientation qubit. -/
def Ocl (c : ℂ) : Qubit →L[ℂ] Qubit := Matrix.toEuclideanCLM (𝕜 := ℂ) (orient c)

theorem Ocl_apply (c : ℂ) (y : Qubit) (b : Bool) : Ocl c y b = ∑ b', orient c b b' * y b' := by
  change Matrix.mulVec (orient c) (WithLp.ofLp y) b = _
  simp only [Matrix.mulVec, dotProduct]

theorem Ocl_false (c : ℂ) (y : Qubit) : Ocl c y false = r2 * y false + r2 * phase c * y true := by
  rw [Ocl_apply, Fintype.sum_bool]
  simp [orient]
  ring

theorem Ocl_true (c : ℂ) (y : Qubit) : Ocl c y true = r2 * y false - r2 * phase c * y true := by
  rw [Ocl_apply, Fintype.sum_bool]
  simp [orient]
  ring

theorem Ocl_congr {c c' : ℂ} (h : phase c = phase c') : Ocl c = Ocl c' := by
  unfold Ocl orient
  rw [h]

theorem Ocl_isometry (c : ℂ) : (Ocl c)† ∘L Ocl c = 1 := by
  obtain ⟨h1, _⟩ := orient_unitary c
  change star (Ocl c) * Ocl c = 1
  rw [Ocl, ← map_star, ← map_mul, h1, map_one]

theorem norm_Ocl (c : ℂ) (y : Qubit) : ‖Ocl c y‖ = ‖y‖ :=
  (norm_map_iff_adjoint_comp_self (Ocl c)).mpr (Ocl_isometry c) y

/-- The local success factor is `√|c| V(c)†`. -/
theorem facQ_eq (c : ℂ) : facQ c = ((amp c : ℝ) : ℂ) • Ocl c := by
  ext y b
  cases b
  · simp only [facQ_false, smul_apply, PiLp.smul_apply, smul_eq_mul, Ocl_false]
    ring
  · simp only [facQ_true, smul_apply, PiLp.smul_apply, smul_eq_mul, Ocl_true]
    ring

/-- `|c| ⟨V y, σ V y'⟩ = ⟨y, E(c) y'⟩`: the orientation change diagonalises `E(c)`. -/
theorem inner_Ocl_sign (c : ℂ) (y y' : Qubit) :
    (‖c‖ : ℂ) * inner ℂ (Ocl c y) (signQ (Ocl c y')) =
      inner ℂ y (ExactEdgeCayley.generator c y') := by
  have h := congrArg (fun T : Qubit →L[ℂ] Qubit => inner ℂ y (T y')) (facQ_sign c)
  simp only [comp_apply, adjoint_inner_right] at h
  rw [← h, facQ_eq, smul_apply, smul_apply, map_smul, inner_smul_left, inner_smul_right,
    Complex.conj_ofReal, ← mul_assoc, ← Complex.ofReal_mul, ← amp_sq c]
  push_cast
  ring

end

end LargeSparsityCore.Native
