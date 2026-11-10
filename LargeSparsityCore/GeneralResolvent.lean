import SparseHamiltonian.GlobalResolvent
import SparseHamiltonian.CayleyTransfer

set_option autoImplicit false

/-!
# The finite-clock resolvent at a general spectral parameter

This module proves the resolvent estimate `opt:eq:global-resolvent` of the large-sparsity core for
the actual finite chronological private block `D_g` of the baseline
(`SparseHamiltonian.GlobalResolvent.globalPrivateBlock`), at any point `z` where the private
operator `D` has a resolvent `R = (z - D)⁻¹`:

`‖(z - D_g)⁻¹‖ ≤ r + (4/3) w ρ + (32/9) a ρ exp((16/9) a m_z)`,

where `‖R‖ ≤ r`, `ρ` bounds both squared endpoint norms `‖R J‖²` and `‖J† D R‖²`, `w` is the
slot weight, `a = T w` is the total weight, `m_z = (1 - |z|²)₊ ρ`, and the small-step condition
`w (1 + 2 r) ≤ 1/2` holds (`exists_global_resolvent`). The inverse is constructed; it is not
assumed.

The local inverse is the Woodbury correction of `R` with the public feedback
`K = (1 + κ F)⁻¹`, `F = J† D R J`. With `Ω = 1 + 2F` and `G = 1 + (w/2) Ω`,
`(1 + w/2)(1 + κ F) = G` (`feedback_scaling`), the forced public transfer is
`u = (1 - (w/2) Ω) G⁻¹` (`exists_local_certificate`), and the exact identity
`Re ⟨y, Ω y⟩ = (|z|² - 1) ‖R J y‖²` (`re_inner_omega`, `opt:eq:real-transfer`) gives
`‖u‖ ≤ 1 + (16/9) w m_z` without accumulated quadratic error. Only the isometry of `D` and `J` is
used.
-/

namespace LargeSparsityCore.GeneralResolvent

noncomputable section

open ContinuousLinearMap SparseHamiltonian GlobalResolvent ChronologicalResolvent
open scoped InnerProduct

variable {P V : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

omit [CompleteSpace V] in
/-- A Neumann inverse of `1 + X` for `‖X‖ ≤ 1/4`, of norm at most `4/3`. -/
theorem exists_inverse_one_add (X : P →L[ℂ] P) (hX : ‖X‖ ≤ 1 / 4) :
    ∃ Y : P →L[ℂ] P, (1 + X) ∘L Y = 1 ∧ Y ∘L (1 + X) = 1 ∧ ‖Y‖ ≤ 4 / 3 := by
  let T : P →L[ℂ] P := -X
  have hT : ‖T‖ ≤ 1 / 4 := by simpa only [T, norm_neg] using hX
  have hLt : ‖T‖ < 1 := by linarith
  refine ⟨∑' n : ℕ, T ^ n, ?_, ?_, ?_⟩
  · simpa only [T, sub_neg_eq_add, mul_def] using mul_neg_geom_series T hLt
  · simpa only [T, sub_neg_eq_add, mul_def] using geom_series_mul_neg T hLt
  · have hSeries := tsum_geometric_le_of_norm_lt_one T hLt
    have hOne : ‖(1 : P →L[ℂ] P)‖ ≤ 1 := by
      simpa only [one_def] using (norm_id_le (𝕜 := ℂ) (E := P))
    have hInv : (1 - ‖T‖)⁻¹ ≤ (4 : ℝ) / 3 := by
      rw [inv_le_iff_one_le_mul₀ (by linarith : 0 < 1 - ‖T‖)]
      linarith
    exact hSeries.trans (by linarith)

/-- The compressed private resolvent `F = J† D R J`. -/
def feedback (D R : V →L[ℂ] V) (J : P →L[ℂ] V) : P →L[ℂ] P := (J† ∘L D) ∘L R ∘L J

theorem norm_isometry_apply (J : P →L[ℂ] V) (hJ : J† ∘L J = 1) (y : P) : ‖J y‖ = ‖y‖ :=
  (J.norm_map_iff_adjoint_comp_self.mpr hJ) y

theorem norm_isometry_le (J : P →L[ℂ] V) (hJ : J† ∘L J = 1) : ‖J‖ ≤ 1 :=
  opNorm_le_bound _ zero_le_one fun y => by rw [norm_isometry_apply J hJ, one_mul]

theorem norm_feedback_le (D R : V →L[ℂ] V) (J : P →L[ℂ] V) (hD : D† ∘L D = 1)
    (hJ : J† ∘L J = 1) : ‖feedback D R J‖ ≤ ‖R‖ := by
  have hJ1 := norm_isometry_le J hJ
  have hJa : ‖adjoint J‖ ≤ 1 := by rw [LinearIsometryEquiv.norm_map]; exact hJ1
  have hD1 := norm_isometry_le D hD
  unfold feedback
  calc ‖(J† ∘L D) ∘L R ∘L J‖ ≤ ‖J† ∘L D‖ * ‖R ∘L J‖ := opNorm_comp_le _ _
    _ ≤ (‖J†‖ * ‖D‖) * (‖R‖ * ‖J‖) := mul_le_mul (opNorm_comp_le _ _) (opNorm_comp_le _ _)
        (norm_nonneg _) (by positivity)
    _ ≤ (1 * 1) * (‖R‖ * 1) := by gcongr
    _ = ‖R‖ := by ring

/-- **Real-transfer identity** (`opt:eq:real-transfer`): for an isometry `D`, an isometry `J`
and `(z - D) R = 1`, `Re ⟨y, (1 + 2F) y⟩ = (|z|² - 1) ‖R J y‖²`. -/
theorem re_inner_omega (D R : V →L[ℂ] V) (J : P →L[ℂ] V) (hD : D† ∘L D = 1)
    (hJ : J† ∘L J = 1) (z : ℂ) (hRight : (z • (1 : V →L[ℂ] V) - D) ∘L R = 1) (y : P) :
    (inner ℂ y ((1 + (2 : ℂ) • feedback D R J) y)).re = (‖z‖ ^ 2 - 1) * ‖R (J y)‖ ^ 2 := by
  set v := R (J y)
  have hJy : J y = z • v - D v := by
    have h := congrArg (fun X : V →L[ℂ] V => X (J y)) hRight
    simpa [v] using h.symm
  have hDv : ‖D v‖ = ‖v‖ := norm_isometry_apply D hD v
  have hyJ : ‖y‖ = ‖J y‖ := (norm_isometry_apply J hJ y).symm
  have hinner : inner ℂ y (feedback D R J y) = inner ℂ (J y) (D v) := by
    change inner ℂ y ((adjoint J) (D (R (J y)))) = _
    rw [adjoint_inner_right]
  have hexp : inner ℂ y ((1 + (2 : ℂ) • feedback D R J) y) =
      inner ℂ y y + 2 * inner ℂ y (feedback D R J y) := by
    simp only [add_apply, one_apply_eq_self, smul_apply, inner_add_right, inner_smul_right]
  have hre2 : ∀ w : ℂ, (2 * w).re = 2 * w.re := fun w => by simp [Complex.mul_re]
  have hsq : ‖y‖ ^ 2 = ‖z‖ ^ 2 * ‖v‖ ^ 2 - 2 * (inner ℂ (z • v) (D v)).re + ‖v‖ ^ 2 := by
    rw [hyJ, hJy, norm_sub_sq (𝕜 := ℂ), norm_smul, mul_pow, hDv, RCLike.re_to_complex]
  have hself : ∀ x : V, (inner ℂ x x).re = ‖x‖ ^ 2 := fun x => by
    rw [← RCLike.re_to_complex]
    exact inner_self_eq_norm_sq x
  have hselfP : (inner ℂ y y).re = ‖y‖ ^ 2 := by
    rw [← RCLike.re_to_complex]
    exact inner_self_eq_norm_sq y
  have hre : (inner ℂ (J y) (D v)).re = (inner ℂ (z • v) (D v)).re - ‖v‖ ^ 2 := by
    rw [hJy, inner_sub_left, Complex.sub_re, hself, hDv]
  rw [hexp, Complex.add_re, hselfP, hinner, hre2, hre, hsq]
  ring

section Scalars

open CayleyTransfer

theorem kappa_mul (w : ℝ) (hw : 0 ≤ w) :
    (kappa w : ℂ) * (1 + (w : ℂ) / 2) = w := by
  have h : kappa w * (1 + w / 2) = w := by
    unfold kappa
    field_simp
  exact_mod_cast h

theorem c_mul (w : ℝ) (hw : 0 ≤ w) :
    (c w : ℂ) * (1 + (w : ℂ) / 2) = 1 - (w : ℂ) / 2 := by
  have h : c w * (1 + w / 2) = 1 - w / 2 := by
    unfold c
    field_simp
  exact_mod_cast h

theorem sigma_sq_mul (w : ℝ) (hw : 0 ≤ w) :
    (sigma w : ℂ) ^ 2 * (1 + (w : ℂ) / 2) ^ 2 = 2 * w := by
  have h : sigma w ^ 2 * (1 + w / 2) ^ 2 = 2 * w := by
    rw [sigma_sq w hw]
    field_simp
  exact_mod_cast h

/-- The scalar identity behind the closed form of the transfer. -/
theorem c_sigma_identity (w : ℝ) (hw : 0 ≤ w) :
    (c w : ℂ) * w - (sigma w : ℂ) ^ 2 * (1 + (w : ℂ) / 2) = -w := by
  have h : c w * w - sigma w ^ 2 * (1 + w / 2) = -w := by
    rw [sigma_sq w hw]
    unfold c
    field_simp
    ring
  exact_mod_cast h

end Scalars

/-- The public denominator `G = 1 + (w/2) Ω` with `Ω = 1 + 2F`. -/
def denominator (D R : V →L[ℂ] V) (J : P →L[ℂ] V) (w : ℝ) : P →L[ℂ] P :=
  1 + ((w : ℂ) / 2) • (1 + (2 : ℂ) • feedback D R J)

theorem feedback_scaling (D R : V →L[ℂ] V) (J : P →L[ℂ] V) (w : ℝ) (hw : 0 ≤ w) :
    (1 + (w : ℂ) / 2) • (1 + (CayleyTransfer.kappa w : ℂ) • feedback D R J) =
      denominator D R J w := by
  have hk := kappa_mul w hw
  unfold denominator
  rw [smul_add, smul_smul, mul_comm, hk]
  module

/-- **Local certificate at a general point.** A two-sided inverse `S` of `z - D_loc` with the
diagonal, coupling and transfer bounds of the paper's local analysis. -/
theorem exists_local_certificate (D R : V →L[ℂ] V) (J : P →L[ℂ] V) (hD : D† ∘L D = 1)
    (hJ : J† ∘L J = 1) (z : ℂ) (hRight : (z • (1 : V →L[ℂ] V) - D) ∘L R = 1)
    (hLeft : R ∘L (z • (1 : V →L[ℂ] V) - D) = 1) {w r ρ : ℝ} (hw : 0 ≤ w)
    (hR : ‖R‖ ≤ r) (hstep : w * (1 + 2 * r) ≤ 1 / 2)
    (hRJ : ‖R ∘L J‖ ^ 2 ≤ ρ) (hJDR : ‖(J† ∘L D) ∘L R‖ ^ 2 ≤ ρ) :
    ∃ S : V →L[ℂ] V,
      (z • 1 - localPrivateBlock D J (CayleyTransfer.kappa w)) ∘L S = 1 ∧
      S ∘L (z • 1 - localPrivateBlock D J (CayleyTransfer.kappa w)) = 1 ∧
      ‖S‖ ≤ r + 4 / 3 * w * ρ ∧
      ‖S ∘L ((CayleyTransfer.sigma w : ℂ) • J)‖ *
        ‖((-(CayleyTransfer.sigma w : ℂ)) • (J† ∘L D)) ∘L S‖ ≤ 32 / 9 * w * ρ ∧
      ‖(CayleyTransfer.c w : ℂ) • 1 + ((-(CayleyTransfer.sigma w : ℂ)) • (J† ∘L D)) ∘L S ∘L
        ((CayleyTransfer.sigma w : ℂ) • J)‖ ≤ 1 + 16 / 9 * w * (max (1 - ‖z‖ ^ 2) 0 * ρ) := by
  set κ := CayleyTransfer.kappa w with hκdef
  set σ := CayleyTransfer.sigma w with hσdef
  set F := feedback D R J with hFdef
  set B := J† ∘L D with hBdef
  have hr : 0 ≤ r := (norm_nonneg _).trans hR
  have hρ : 0 ≤ ρ := (sq_nonneg _).trans hRJ
  have hκ0 : 0 ≤ κ := by rw [hκdef, CayleyTransfer.kappa]; positivity
  have hσ0 : 0 ≤ σ := CayleyTransfer.sigma_nonneg w hw
  have hF : ‖F‖ ≤ r := (norm_feedback_le D R J hD hJ).trans hR
  -- The public denominator and its Neumann inverse.
  set X : P →L[ℂ] P := ((w : ℂ) / 2) • (1 + (2 : ℂ) • F) with hXdef
  have hX : ‖X‖ ≤ 1 / 4 := by
    have hOne : ‖(1 : P →L[ℂ] P)‖ ≤ 1 := by
      simpa only [one_def] using (norm_id_le (𝕜 := ℂ) (E := P))
    have hw2 : ‖((w : ℂ) / 2)‖ = w / 2 := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw]
      norm_num
    calc ‖X‖ = w / 2 * ‖1 + (2 : ℂ) • F‖ := by rw [hXdef, norm_smul, hw2]
      _ ≤ w / 2 * (1 + 2 * r) := by
          gcongr
          calc ‖1 + (2 : ℂ) • F‖ ≤ ‖(1 : P →L[ℂ] P)‖ + ‖(2 : ℂ) • F‖ := norm_add_le _ _
            _ ≤ 1 + 2 * r := by
                rw [norm_smul]
                gcongr
                · norm_num
      _ ≤ 1 / 4 := by linarith
  obtain ⟨Gi, hGi1, hGi2, hGi⟩ := exists_inverse_one_add X hX
  have hG : (1 : P →L[ℂ] P) + X = denominator D R J w := rfl
  -- The public feedback inverse `K = (1 + w/2) G⁻¹`.
  set K : P →L[ℂ] P := (1 + (w : ℂ) / 2) • Gi with hKdef
  have hscale := feedback_scaling D R J w hw
  have hK1 : (1 + (κ : ℂ) • (B ∘L R ∘L J)) ∘L K = 1 := by
    change (1 + (κ : ℂ) • F) ∘L K = 1
    rw [hKdef, comp_smul, ← smul_comp, hscale, ← hG, hGi1]
  have hK2 : K ∘L (1 + (κ : ℂ) • (B ∘L R ∘L J)) = 1 := by
    change K ∘L (1 + (κ : ℂ) • F) = 1
    rw [hKdef, smul_comp, ← comp_smul, hscale, ← hG, hGi2]
  have hnorm2 : ‖(1 + (w : ℂ) / 2)‖ = 1 + w / 2 := by
    have : (1 + (w : ℂ) / 2) = ((1 + w / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hK : ‖K‖ ≤ (1 + w / 2) * (4 / 3) := by
    rw [hKdef, norm_smul, hnorm2]
    gcongr
  have hκK : κ * ‖K‖ ≤ 4 / 3 * w := by
    have hκw : κ * (1 + w / 2) = w := by rw [hκdef, CayleyTransfer.kappa]; field_simp
    calc κ * ‖K‖ ≤ κ * ((1 + w / 2) * (4 / 3)) := mul_le_mul_of_nonneg_left hK hκ0
      _ = 4 / 3 * w := by rw [← mul_assoc, hκw]; ring
  -- The two endpoints.
  set a := ‖R ∘L J‖
  set b := ‖B ∘L R‖
  have hab : a * b ≤ ρ := by
    have ha : 0 ≤ a := norm_nonneg _
    have hb : 0 ≤ b := norm_nonneg _
    nlinarith [sq_nonneg (a - b)]
  -- The local inverse.
  refine ⟨woodburyInverse R J K B (κ : ℂ), ?_, ?_, ?_, ?_, ?_⟩
  · rw [localPrivateBlock_denominator]
    exact woodbury_right_inverse _ R J K B (κ : ℂ) hRight hK1
  · rw [localPrivateBlock_denominator]
    exact woodbury_left_inverse _ R J K B (κ : ℂ) hLeft hK2
  · calc ‖woodburyInverse R J K B (κ : ℂ)‖ ≤ ‖R‖ + κ * (a * ‖K‖ * b) :=
          norm_woodburyInverse_le R J K B hκ0
      _ = ‖R‖ + (κ * ‖K‖) * (a * b) := by ring
      _ ≤ r + (4 / 3 * w) * ρ := by
          gcongr
      _ = r + 4 / 3 * w * ρ := by ring
  · have hSJ := woodbury_inclusion_endpoint R J K B (κ : ℂ) hK2
    have hBS := woodbury_observation_endpoint R J K B (κ : ℂ) hK1
    have hσn : ‖(σ : ℂ)‖ = σ := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hσ0]
    have hσn' : ‖(-(σ : ℂ))‖ = σ := by rw [norm_neg, hσn]
    have h1 : ‖woodburyInverse R J K B (κ : ℂ) ∘L ((σ : ℂ) • J)‖ ≤ σ * (a * ‖K‖) := by
      rw [comp_smul, norm_smul, hσn, hSJ]
      gcongr
      rw [← comp_assoc]
      exact opNorm_comp_le _ _
    have h2 : ‖((-(σ : ℂ)) • B) ∘L woodburyInverse R J K B (κ : ℂ)‖ ≤ σ * (‖K‖ * b) := by
      rw [smul_comp, norm_smul, hσn', hBS]
      gcongr
      exact opNorm_comp_le _ _
    have hσsq : σ ^ 2 * (1 + w / 2) ^ 2 = 2 * w := by
      rw [hσdef, CayleyTransfer.sigma_sq w hw]
      field_simp
    calc _ ≤ (σ * (a * ‖K‖)) * (σ * (‖K‖ * b)) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = σ ^ 2 * ‖K‖ ^ 2 * (a * b) := by ring
      _ ≤ σ ^ 2 * ((1 + w / 2) * (4 / 3)) ^ 2 * ρ := by
          gcongr
      _ = (σ ^ 2 * (1 + w / 2) ^ 2) * (16 / 9) * ρ := by ring
      _ = 32 / 9 * w * ρ := by rw [hσsq]; ring
  · -- The transfer `u = c - σ² F K = (1 - X) G⁻¹`.
    set S := woodburyInverse R J K B (κ : ℂ) with hSdef
    have hSJ := woodbury_inclusion_endpoint R J K B (κ : ℂ) hK2
    have hBSJ : B ∘L S ∘L J = F ∘L K := by
      rw [hSJ, hFdef, feedback]
      simp only [hBdef, comp_assoc]
    set u := (CayleyTransfer.c w : ℂ) • (1 : P →L[ℂ] P) +
      ((-(σ : ℂ)) • B) ∘L S ∘L ((σ : ℂ) • J) with hudef
    have hu : u = (CayleyTransfer.c w : ℂ) • 1 - ((σ : ℂ) ^ 2) • (F ∘L K) := by
      rw [hudef, smul_comp, comp_smul, comp_smul, smul_smul, hBSJ]
      rw [sub_eq_add_neg, ← neg_smul]
      congr 2
      ring
    have hKX : K ∘L (1 + X) = (1 + (w : ℂ) / 2) • 1 := by rw [hKdef, smul_comp, hGi2]
    have huX : u ∘L (1 + X) = 1 - X := by
      have hF1 : F ∘L (1 : P →L[ℂ] P) = F := by ext; rfl
      have h1X : (1 : P →L[ℂ] P) ∘L (1 + X) = 1 + X := by ext; rfl
      rw [hu, sub_comp, smul_comp, smul_comp, comp_assoc, hKX, comp_smul, hF1, h1X]
      have hc := c_mul w hw
      have hcs : (CayleyTransfer.c w : ℂ) * w - (σ : ℂ) ^ 2 * (1 + (w : ℂ) / 2) = -w :=
        c_sigma_identity w hw
      rw [hXdef]
      match_scalars
      · linear_combination hc
      · linear_combination hcs
    have huform : u = (1 - X) ∘L Gi := by
      have h := congrArg (fun T : P →L[ℂ] P => T ∘L Gi) huX
      simp only [comp_assoc, hGi1] at h
      rw [← h]
      ext
      rfl
    -- Growth of the transfer.
    set m := max (1 - ‖z‖ ^ 2) 0 * ρ with hmdef
    have hm : 0 ≤ m := mul_nonneg (le_max_right _ _) hρ
    apply opNorm_le_bound _ (by positivity)
    intro x
    set y := Gi x with hydef
    have hxy : x = y + X y := by
      have h := congrArg (fun T : P →L[ℂ] P => T x) hGi1
      simpa [hydef] using h.symm
    have huxy : u x = y - X y := by
      rw [huform]
      simp [hydef]
    have hreX : (inner ℂ y (X y)).re = w / 2 * ((‖z‖ ^ 2 - 1) * ‖R (J y)‖ ^ 2) := by
      rw [← re_inner_omega D R J hD hJ z hRight y, hXdef, smul_apply, inner_smul_right]
      have : ((w : ℂ) / 2) = ((w / 2 : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.re_ofReal_mul]
    have hux : ‖u x‖ ^ 2 = ‖x‖ ^ 2 + 2 * w * (1 - ‖z‖ ^ 2) * ‖R (J y)‖ ^ 2 := by
      have h1 : ‖y - X y‖ ^ 2 = ‖y‖ ^ 2 - 2 * (inner ℂ y (X y)).re + ‖X y‖ ^ 2 := by
        rw [norm_sub_sq (𝕜 := ℂ), RCLike.re_to_complex]
      have h2 : ‖y + X y‖ ^ 2 = ‖y‖ ^ 2 + 2 * (inner ℂ y (X y)).re + ‖X y‖ ^ 2 := by
        rw [norm_add_sq (𝕜 := ℂ), RCLike.re_to_complex]
      have hx2 : ‖x‖ ^ 2 = ‖y + X y‖ ^ 2 := by rw [← hxy]
      rw [huxy, h1, hx2, h2, hreX]
      ring
    have hRJy : ‖R (J y)‖ ^ 2 ≤ ρ * ‖y‖ ^ 2 := by
      have h : ‖R (J y)‖ ≤ ‖R ∘L J‖ * ‖y‖ := (R ∘L J).le_opNorm y
      calc ‖R (J y)‖ ^ 2 ≤ (‖R ∘L J‖ * ‖y‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
        _ = ‖R ∘L J‖ ^ 2 * ‖y‖ ^ 2 := by ring
        _ ≤ ρ * ‖y‖ ^ 2 := by gcongr
    have hy : ‖y‖ ^ 2 ≤ 16 / 9 * ‖x‖ ^ 2 := by
      have h : ‖y‖ ≤ 4 / 3 * ‖x‖ :=
        (Gi.le_opNorm x).trans (mul_le_mul_of_nonneg_right hGi (norm_nonneg _))
      calc ‖y‖ ^ 2 ≤ (4 / 3 * ‖x‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
        _ = 16 / 9 * ‖x‖ ^ 2 := by ring
    have hgrow : ‖u x‖ ^ 2 ≤ (1 + 32 / 9 * w * m) * ‖x‖ ^ 2 := by
      rw [hux]
      have hmax : 1 - ‖z‖ ^ 2 ≤ max (1 - ‖z‖ ^ 2) 0 := le_max_left _ _
      have hmax0 : 0 ≤ max (1 - ‖z‖ ^ 2) 0 := le_max_right _ _
      have hRJy0 : 0 ≤ ‖R (J y)‖ ^ 2 := sq_nonneg _
      calc ‖x‖ ^ 2 + 2 * w * (1 - ‖z‖ ^ 2) * ‖R (J y)‖ ^ 2 ≤
            ‖x‖ ^ 2 + 2 * w * max (1 - ‖z‖ ^ 2) 0 * (ρ * (16 / 9 * ‖x‖ ^ 2)) := by
            gcongr
            calc ‖R (J y)‖ ^ 2 ≤ ρ * ‖y‖ ^ 2 := hRJy
              _ ≤ ρ * (16 / 9 * ‖x‖ ^ 2) := by gcongr
        _ = (1 + 32 / 9 * w * m) * ‖x‖ ^ 2 := by rw [hmdef]; ring
    have hfin : ‖u x‖ ^ 2 ≤ ((1 + 16 / 9 * w * m) * ‖x‖) ^ 2 := by
      calc ‖u x‖ ^ 2 ≤ (1 + 32 / 9 * w * m) * ‖x‖ ^ 2 := hgrow
        _ ≤ (1 + 16 / 9 * w * m) ^ 2 * ‖x‖ ^ 2 := by
            apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
            have hsq : (1 + 16 / 9 * w * m) ^ 2 = 1 + 32 / 9 * w * m + (16 / 9 * w * m) ^ 2 := by
              ring
            rw [hsq]
            exact le_add_of_nonneg_right (sq_nonneg _)
        _ = ((1 + 16 / 9 * w * m) * ‖x‖) ^ 2 := by ring
    have hpos : 0 ≤ (1 + 16 / 9 * w * m) * ‖x‖ := by positivity
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hpos (by norm_num)).mp hfin

/-- **Global resolvent at a general point** (`opt:eq:global-resolvent`). The actual finite
chronological private block has a constructed two-sided resolvent at `z`, with
`‖(z - D_g)⁻¹‖ ≤ r + (4/3) w ρ + (32/9) a ρ exp((16/9) a m_z)`, `a = T w`,
`m_z = (1 - |z|²)₊ ρ`. -/
theorem exists_global_resolvent (D R : V →L[ℂ] V) (J : P →L[ℂ] V) (hD : D† ∘L D = 1)
    (hJ : J† ∘L J = 1) (z : ℂ) (hRight : (z • (1 : V →L[ℂ] V) - D) ∘L R = 1)
    (hLeft : R ∘L (z • (1 : V →L[ℂ] V) - D) = 1) {w r ρ : ℝ} (hw : 0 ≤ w)
    (hR : ‖R‖ ≤ r) (hstep : w * (1 + 2 * r) ≤ 1 / 2)
    (hRJ : ‖R ∘L J‖ ^ 2 ≤ ρ) (hJDR : ‖(J† ∘L D) ∘L R‖ ^ 2 ≤ ρ) (T : ℕ) :
    ∃ S : BlockOperator.H T V →L[ℂ] BlockOperator.H T V,
      (z • 1 - globalPrivateBlock D J (CayleyTransfer.c w) (CayleyTransfer.kappa w)
        (CayleyTransfer.sigma w) T) ∘L S = 1 ∧
      S ∘L (z • 1 - globalPrivateBlock D J (CayleyTransfer.c w) (CayleyTransfer.kappa w)
        (CayleyTransfer.sigma w) T) = 1 ∧
      ‖S‖ ≤ r + 4 / 3 * w * ρ + 32 / 9 * ((T : ℝ) * w) * ρ *
        Real.exp (16 / 9 * ((T : ℝ) * w) * (max (1 - ‖z‖ ^ 2) 0 * ρ)) := by
  obtain ⟨S, hS1, hS2, hSn, hcoup, hu⟩ :=
    exists_local_certificate D R J hD hJ z hRight hLeft hw hR hstep hRJ hJDR
  obtain ⟨hinv1, hinv2⟩ := FiniteChronologicalInverse.resolvent_two_sided_inverse
    (localPrivateBlock D J (CayleyTransfer.kappa w)) S ((CayleyTransfer.sigma w : ℂ) • J)
    ((CayleyTransfer.c w : ℂ) • 1) ((-(CayleyTransfer.sigma w : ℂ)) • (J† ∘L D)) T z hS1 hS2
  refine ⟨_, hinv1, hinv2, ?_⟩
  have hρ : 0 ≤ ρ := (sq_nonneg _).trans hRJ
  have hm : 0 ≤ max (1 - ‖z‖ ^ 2) 0 * ρ := mul_nonneg (le_max_right _ _) hρ
  have h := chronologicalOperator_norm_le_of_local_bounds S
    (S ∘L ((CayleyTransfer.sigma w : ℂ) • J))
    ((CayleyTransfer.c w : ℂ) • 1 + ((-(CayleyTransfer.sigma w : ℂ)) • (J† ∘L D)) ∘L S ∘L
      ((CayleyTransfer.sigma w : ℂ) • J))
    (((-(CayleyTransfer.sigma w : ℂ)) • (J† ∘L D)) ∘L S)
    (a := 16 / 9 * w * (max (1 - ‖z‖ ^ 2) 0 * ρ)) (by positivity) hu T hSn
    (b := 32 / 9 * ((T : ℝ) * w) * ρ)
    (by
      calc (T : ℝ) * (_ * _) ≤ (T : ℝ) * (32 / 9 * w * ρ) :=
            mul_le_mul_of_nonneg_left hcoup (Nat.cast_nonneg _)
        _ = 32 / 9 * ((T : ℝ) * w) * ρ := by ring)
    (e := 16 / 9 * ((T : ℝ) * w) * (max (1 - ‖z‖ ^ 2) 0 * ρ)) (le_of_eq (by ring))
  exact h

end

end LargeSparsityCore.GeneralResolvent
