import LargeSparsityCore.FilterBound
import LargeSparsityCore.CayleyBlocks
import SparseHamiltonian.GlobalResolventContinuation2

set_option autoImplicit false

/-!
# The product filter on the actual global private block

This module combines the Cayley block resolvent (`LargeSparsityCore.CayleyBlocks`), the global
resolvent at general points (`LargeSparsityCore.GeneralResolvent`) and the abstract filter bound
(`LargeSparsityCore.FilterBound`) into the bound `opt:eq:filter-small` for the actual finite
chronological private block `D_g` of the baseline:

`‖g_B(D_g)^m g_p(D_g)^k‖ ≤ 2 ζ F M₁ + (2/(Bρ₀))^m ρ₀ M₂ (1 + 2 ζ M₁)` (`filter_bound`),

where `M₁` (`isoBound`) bounds the resolvent of `D_g` on the two isolated circles
`|z - λ_±| = ζ`, `M₂` (`bulkBound`) bounds it on the circle `|z - 1| = ρ₀`, and `F` bounds the
scalar filter on the isolated circles. Invertibility of `z - D_g` in the whole gap region (the
spectral enclosure of the manuscript) follows from the same construction: the small-step condition
`w (1 + 2 (2/ζ + 4Q₀/3)) ≤ 1/2` gives the global inverse at every `z` with `|z - 1| ≤ ρ₀` outside
the two isolated disks (`exists_global_resolvent_gap`).
-/

namespace LargeSparsityCore.CoreFilter

noncomputable section

open ContinuousLinearMap Complex Metric SparseHamiltonian GlobalResolvent ChronologicalResolvent
open CayleyBlocks
open scoped InnerProduct

variable {P V : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- The resolvent bound of the global block at a point `z`, from the Cayley block bounds. -/
def pointBound (Q₀ sw sm w a ip im ζ2 : ℝ) : ℝ :=
  let r := ip + im + 4 / 3 * Q₀
  let X := sw * (ip + im) + 2 / 3 * (1 + sm)
  r + 4 / 3 * w * X ^ 2 + 32 / 9 * a * X ^ 2 * Real.exp (16 / 9 * a * (ζ2 * X ^ 2))

theorem pointBound_mono {Q₀ sw sm w a ip im ζ2 ip' im' ζ2' : ℝ} (hsw : 0 ≤ sw) (hsm : 0 ≤ sm)
    (hw : 0 ≤ w) (ha : 0 ≤ a) (hip : 0 ≤ ip) (him : 0 ≤ im) (hζ2 : 0 ≤ ζ2) (hip' : ip ≤ ip')
    (him' : im ≤ im') (hζ2' : ζ2 ≤ ζ2') :
    pointBound Q₀ sw sm w a ip im ζ2 ≤ pointBound Q₀ sw sm w a ip' im' ζ2' := by
  unfold pointBound
  simp only
  have hX : sw * (ip + im) + 2 / 3 * (1 + sm) ≤ sw * (ip' + im') + 2 / 3 * (1 + sm) := by
    gcongr
  have hX0 : 0 ≤ sw * (ip + im) + 2 / 3 * (1 + sm) := by positivity
  have hX2 : (sw * (ip + im) + 2 / 3 * (1 + sm)) ^ 2 ≤ (sw * (ip' + im') + 2 / 3 * (1 + sm)) ^ 2 :=
    pow_le_pow_left₀ hX0 hX 2
  have hζ2'' : 0 ≤ ζ2' := hζ2.trans hζ2'
  gcongr

theorem pointBound_comm (Q₀ sw sm w a ip im ζ2 : ℝ) :
    pointBound Q₀ sw sm w a ip im ζ2 = pointBound Q₀ sw sm w a im ip ζ2 := by
  unfold pointBound
  simp only [add_comm ip im]

/-- The resolvent bound on the isolated circles. -/
def isoBound (Q₀ sw sm w a ζ g : ℝ) : ℝ := pointBound Q₀ sw sm w a ζ⁻¹ g⁻¹ (2 * ζ)

/-- The resolvent bound on the bulk circle `|z - 1| = ρ₀`. -/
def bulkBound (Q₀ sw sm w a ρ₀ : ℝ) : ℝ :=
  pointBound Q₀ sw sm w a (2 / ρ₀) (2 / ρ₀) (2 * ρ₀)

variable {K D Pp Pm : V →L[ℂ] V} {q : ℝ}

/-- **The global resolvent in the gap region.** At every `z` with `|z - 1| ≤ ρ₀` and
`|z - λ_±| ≥ ζ`, the global block has a two-sided resolvent bounded by `pointBound` with the
actual inverse distances. -/
theorem exists_global_resolvent_gap (h : Spectral K D Pp Pm q) (hD : D† ∘L D = 1)
    (J : P →L[ℂ] V) (hJ : J† ∘L J = 1) {Q₀ sw sm ρ₀ ζ w : ℝ}
    (hQ : ‖R1 K ∘L bulk Pp Pm‖ ≤ Q₀) (hPpJ : ‖Pp ∘L J‖ ≤ sw) (hPmJ : ‖Pm ∘L J‖ ≤ sw)
    (hKJ : ‖K ∘L bulk Pp Pm ∘L J‖ ≤ sm) (hρQ : ρ₀ * Q₀ ≤ 1 / 4) (hζ : 0 < ζ) (hw : 0 ≤ w)
    (hstep : w * (1 + 2 * (2 / ζ + 4 / 3 * Q₀)) ≤ 1 / 2) (T : ℕ) (z : ℂ)
    (hz1 : ‖z - 1‖ ≤ ρ₀) (hzp : ζ ≤ ‖z - lamp q‖) (hzm : ζ ≤ ‖z - lamm q‖) :
    ∃ S : BlockOperator.H T V →L[ℂ] BlockOperator.H T V,
      (z • 1 - globalPrivateBlock D J (CayleyTransfer.c w) (CayleyTransfer.kappa w)
        (CayleyTransfer.sigma w) T) ∘L S = 1 ∧
      S ∘L (z • 1 - globalPrivateBlock D J (CayleyTransfer.c w) (CayleyTransfer.kappa w)
        (CayleyTransfer.sigma w) T) = 1 ∧
      ‖S‖ ≤ pointBound Q₀ sw sm w ((T : ℝ) * w) ‖z - lamp q‖⁻¹ ‖z - lamm q‖⁻¹
        (max (1 - ‖z‖ ^ 2) 0) := by
  have hQ0 : 0 ≤ Q₀ := (norm_nonneg _).trans hQ
  have hzp0 : z ≠ lamp q := fun he => by rw [he, sub_self, norm_zero] at hzp; linarith
  have hzm0 : z ≠ lamm q := fun he => by rw [he, sub_self, norm_zero] at hzm; linarith
  have hz : ‖z - 1‖ * Q₀ ≤ 1 / 4 :=
    (mul_le_mul_of_nonneg_right hz1 hQ0).trans hρQ
  obtain ⟨R, hR1, hR2, hRn, hRJ, hJDR⟩ :=
    exists_resolvent_bounds h J hJ hQ hPpJ hPmJ hKJ z hz hzp0 hzm0
  set ip := ‖z - lamp q‖⁻¹
  set im := ‖z - lamm q‖⁻¹
  have hip : ip ≤ ζ⁻¹ := inv_anti₀ hζ hzp
  have him : im ≤ ζ⁻¹ := inv_anti₀ hζ hzm
  have hsw : 0 ≤ sw := (norm_nonneg _).trans hPpJ
  have hsm : 0 ≤ sm := (norm_nonneg _).trans hKJ
  set X := sw * (ip + im) + 2 / 3 * (1 + sm)
  have hX0 : 0 ≤ X := by positivity
  have hstep' : w * (1 + 2 * (ip + im + 4 / 3 * Q₀)) ≤ 1 / 2 := by
    refine le_trans ?_ hstep
    gcongr
    calc ip + im ≤ ζ⁻¹ + ζ⁻¹ := add_le_add hip him
      _ = 2 / ζ := by ring
  have hRJ2 : ‖R ∘L J‖ ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hRJ 2
  have hJDR2 : ‖(J† ∘L D) ∘L R‖ ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hJDR 2
  obtain ⟨S, hS1, hS2, hSn⟩ := GeneralResolvent.exists_global_resolvent D R J hD hJ z hR1 hR2
    hw hRn hstep' hRJ2 hJDR2 T
  refine ⟨S, hS1, hS2, ?_⟩
  refine hSn.trans (le_of_eq ?_)
  unfold pointBound
  simp only [X]

theorem ring_inverse_eq {A : Type*} [Ring A] {x y : A} (h1 : x * y = 1) (h2 : y * x = 1) :
    Ring.inverse x = y :=
  Ring.inverse_unit ⟨x, y, h1, h2⟩

theorem one_sub_sq_le {z c : ℂ} {ζ : ℝ} (hc : ‖c‖ = 1) (hz : ‖z - c‖ ≤ ζ) (hζ : 0 ≤ ζ) :
    max (1 - ‖z‖ ^ 2) 0 ≤ 2 * ζ := by
  apply max_le _ (by positivity)
  have h1 : 1 - ζ ≤ ‖z‖ := by
    have := norm_sub_norm_le c z
    rw [hc, norm_sub_rev] at this
    linarith
  rcases le_or_gt 0 (1 - ζ) with h0 | h0
  · have h2 : (1 - ζ) ^ 2 ≤ ‖z‖ ^ 2 := pow_le_pow_left₀ h0 h1 2
    nlinarith
  · nlinarith [sq_nonneg ‖z‖]

/-- **The product filter on the global block** (`opt:eq:filter-small`). -/
theorem filter_bound [FiniteDimensional ℂ V] (h : Spectral K D Pp Pm q) (hD : D† ∘L D = 1)
    (J : P →L[ℂ] V) (hJ : J† ∘L J = 1) {Q₀ sw sm ρ₀ ζ w F : ℝ}
    (hQ : ‖R1 K ∘L bulk Pp Pm‖ ≤ Q₀) (hPpJ : ‖Pp ∘L J‖ ≤ sw) (hPmJ : ‖Pm ∘L J‖ ≤ sw)
    (hKJ : ‖K ∘L bulk Pp Pm ∘L J‖ ≤ sm) (hρQ : ρ₀ * Q₀ ≤ 1 / 4) (hζ : 0 < ζ) (hρ : 0 < ρ₀)
    (hw : 0 ≤ w) (hstep : w * (1 + 2 * (2 / ζ + 4 / 3 * Q₀)) ≤ 1 / 2)
    (hsep : 2 * ζ ≤ ‖lamp q - lamm q‖) (hp1 : ‖lamp q - 1‖ + ζ ≤ ρ₀ / 2)
    (hm1 : ‖lamm q - 1‖ + ζ ≤ ρ₀ / 2) (T : ℕ) (B m p k : ℕ) (hB : 1 ≤ B) (hp : 1 ≤ p)
    (hm : 1 ≤ m)
    (hF₁ : ∀ z : ℂ, ‖z - lamp q‖ = ζ → ‖FilterCoefficients.geometricAverage B z ^ m *
      FilterCoefficients.geometricAverage p z ^ k‖ ≤ F)
    (hF₂ : ∀ z : ℂ, ‖z - lamm q‖ = ζ → ‖FilterCoefficients.geometricAverage B z ^ m *
      FilterCoefficients.geometricAverage p z ^ k‖ ≤ F) :
    ‖∑ j ∈ Finset.range (ProductFilter.degree B m p k + 1), (ProductFilter.poly B m p k).coeff j •
      (globalPrivateBlock D J (CayleyTransfer.c w) (CayleyTransfer.kappa w)
        (CayleyTransfer.sigma w) T) ^ j‖ ≤
      2 * (ζ * (F * isoBound Q₀ sw sm w ((T : ℝ) * w) ζ (‖lamp q - lamm q‖ - ζ))) +
        (2 / ((B : ℝ) * ρ₀)) ^ m * ρ₀ * (bulkBound Q₀ sw sm w ((T : ℝ) * w) ρ₀ *
          (1 + 2 * (ζ * isoBound Q₀ sw sm w ((T : ℝ) * w) ζ (‖lamp q - lamm q‖ - ζ)))) := by
  set Dg := globalPrivateBlock D J (CayleyTransfer.c w) (CayleyTransfer.kappa w)
    (CayleyTransfer.sigma w) T with hDgdef
  obtain ⟨_hκ, _hκU, hκc, hσc, _hσw⟩ : 0 ≤ CayleyTransfer.kappa w ∧ True ∧
      CayleyTransfer.kappa w = 1 - CayleyTransfer.c w ∧
      CayleyTransfer.sigma w ^ 2 = 1 - CayleyTransfer.c w ^ 2 ∧ True := by
    refine ⟨by unfold CayleyTransfer.kappa; positivity, trivial, ?_, ?_, trivial⟩
    · unfold CayleyTransfer.kappa CayleyTransfer.c
      field_simp
      ring
    · rw [CayleyTransfer.sigma_sq w hw]
      unfold CayleyTransfer.c
      field_simp
      ring
  have hDg : ‖Dg‖ ≤ 1 := globalPrivateBlock_norm_le_one D J _ _ _ T hκc hσc hD hJ
  have hsw : 0 ≤ sw := (norm_nonneg _).trans hPpJ
  have hsm : 0 ≤ sm := (norm_nonneg _).trans hKJ
  have ha : 0 ≤ (T : ℝ) * w := mul_nonneg (Nat.cast_nonneg _) hw
  have hlp : ‖lamp q‖ = 1 := norm_lamp q
  have hlm : ‖lamm q‖ = 1 := norm_lamm q
  set g := ‖lamp q - lamm q‖ - ζ with hgdef
  have hg : ζ ≤ g := by rw [hgdef]; linarith
  have hgpos : 0 < g := hζ.trans_le hg
  -- The gap region and the three circles.
  have hgap := fun z hz1 hzp hzm =>
    exists_global_resolvent_gap (T := T) h hD J hJ hQ hPpJ hPmJ hKJ hρQ hζ hw hstep z hz1 hzp hzm
  have hunit : ∀ z : ℂ, ‖z - 1‖ ≤ ρ₀ → ζ ≤ ‖z - lamp q‖ → ζ ≤ ‖z - lamm q‖ →
      IsUnit (z • (1 : BlockOperator.H T V →L[ℂ] BlockOperator.H T V) - Dg) := by
    intro z hz1 hzp hzm
    obtain ⟨S, hS1, hS2, _⟩ := hgap z hz1 hzp hzm
    exact ⟨⟨_, S, hS1, hS2⟩, rfl⟩
  have hres : ∀ z : ℂ, ∀ (hz1 : ‖z - 1‖ ≤ ρ₀) (hzp : ζ ≤ ‖z - lamp q‖) (hzm : ζ ≤ ‖z - lamm q‖),
      ‖Riesz.resolvent Dg z‖ ≤ pointBound Q₀ sw sm w ((T : ℝ) * w) ‖z - lamp q‖⁻¹
        ‖z - lamm q‖⁻¹ (max (1 - ‖z‖ ^ 2) 0) := by
    intro z hz1 hzp hzm
    obtain ⟨S, hS1, hS2, hSn⟩ := hgap z hz1 hzp hzm
    rw [Riesz.resolvent, ring_inverse_eq hS1 hS2]
    exact hSn
  have hiso : ∀ z : ℂ, ∀ c c' : ℂ, ‖c‖ = 1 → ‖c - 1‖ + ζ ≤ ρ₀ / 2 → 2 * ζ ≤ ‖c - c'‖ →
      ‖z - c‖ = ζ → ‖z - 1‖ ≤ ρ₀ ∧ ζ ≤ ‖z - c'‖ ∧ ‖z - c'‖⁻¹ ≤ (‖c - c'‖ - ζ)⁻¹ ∧
        max (1 - ‖z‖ ^ 2) 0 ≤ 2 * ζ := by
    intro z c c' hc hc1 hcc' hz
    have h1 : ‖z - 1‖ ≤ ρ₀ := by
      have := norm_sub_le_norm_sub_add_norm_sub z c 1
      linarith
    have h2 : ‖c - c'‖ - ζ ≤ ‖z - c'‖ := by
      have := norm_sub_le_norm_sub_add_norm_sub c z c'
      rw [norm_sub_rev c z] at this
      linarith
    exact ⟨h1, by linarith, inv_anti₀ (by linarith) h2, one_sub_sq_le hc hz.le hζ.le⟩
  have hinv0 : ∀ z c : ℂ, 0 ≤ ‖z - c‖⁻¹ := fun z c => inv_nonneg.mpr (norm_nonneg _)
  have hM₁ : ∀ z : ℂ, ‖z - lamp q‖ = ζ →
      ‖Riesz.resolvent Dg z‖ ≤ isoBound Q₀ sw sm w ((T : ℝ) * w) ζ g := by
    intro z hz
    obtain ⟨h1, h2, h3, h4⟩ := hiso z (lamp q) (lamm q) hlp hp1 hsep hz
    refine (hres z h1 hz.ge h2).trans ?_
    unfold isoBound
    exact pointBound_mono hsw hsm hw ha (hinv0 _ _) (hinv0 _ _) (le_max_right _ _)
      (by rw [hz]) h3 h4
  have hM₂ : ∀ z : ℂ, ‖z - lamm q‖ = ζ →
      ‖Riesz.resolvent Dg z‖ ≤ isoBound Q₀ sw sm w ((T : ℝ) * w) ζ g := by
    intro z hz
    have hsep' : 2 * ζ ≤ ‖lamm q - lamp q‖ := by rwa [norm_sub_rev]
    obtain ⟨h1, h2, h3, h4⟩ := hiso z (lamm q) (lamp q) hlm hm1 hsep' hz
    rw [norm_sub_rev (lamm q) (lamp q)] at h3
    refine (hres z h1 h2 hz.ge).trans ?_
    unfold isoBound
    rw [pointBound_comm Q₀ sw sm w _ ζ⁻¹ g⁻¹]
    exact pointBound_mono hsw hsm hw ha (hinv0 _ _) (hinv0 _ _) (le_max_right _ _) h3
      (by rw [hz]) h4
  have hζρ : ζ ≤ ρ₀ / 2 := by linarith [norm_nonneg (lamp q - 1)]
  have hMb : ∀ z : ℂ, ‖z - 1‖ = ρ₀ →
      ‖Riesz.resolvent Dg z‖ ≤ bulkBound Q₀ sw sm w ((T : ℝ) * w) ρ₀ := by
    intro z hz
    have hp2 : ρ₀ / 2 ≤ ‖z - lamp q‖ := by
      have := norm_sub_le_norm_sub_add_norm_sub z (lamp q) 1
      rw [norm_sub_rev (lamp q) 1] at hp1
      linarith [norm_sub_rev (1 : ℂ) (lamp q)]
    have hm2 : ρ₀ / 2 ≤ ‖z - lamm q‖ := by
      have := norm_sub_le_norm_sub_add_norm_sub z (lamm q) 1
      linarith [norm_sub_rev (1 : ℂ) (lamm q)]
    have hinv : ∀ c : ℂ, ρ₀ / 2 ≤ ‖z - c‖ → ‖z - c‖⁻¹ ≤ 2 / ρ₀ := fun c hc => by
      have := inv_anti₀ (by positivity) hc
      rwa [inv_div] at this
    refine (hres z hz.le (hζρ.trans hp2) (hζρ.trans hm2)).trans ?_
    unfold bulkBound
    exact pointBound_mono hsw hsm hw ha (hinv0 _ _) (hinv0 _ _) (le_max_right _ _)
      (hinv _ hp2) (hinv _ hm2) (one_sub_sq_le (by simp) hz.le hρ.le)
  rw [ProductFilter.operator_eq]
  exact FilterBound.filter_norm_le Dg hDg (lamp q) (lamm q) hζ hρ hsep (by linarith)
    (by linarith) hunit hM₁ hM₂ hMb B m p k hB hp hm hF₁ hF₂

end

end LargeSparsityCore.CoreFilter
