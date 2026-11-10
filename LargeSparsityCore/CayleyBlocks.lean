import LargeSparsityCore.GeneralResolvent

set_option autoImplicit false

/-!
# The resolvent of the Cayley private operator from its block structure

The private generator `K` of the large-sparsity core (`opt:eq:joint-lift`) has two exact
eigenspaces with eigenvalues `±2q` (the successful correction factor, projections `P₊`, `P₋`) and a
bulk complement `P₀ = 1 - P₊ - P₋` on which `‖K P₀‖ ≤ κ_b`. The private operator `D` is its Cayley
transform, specified exactly as in the baseline by `(1 - D) R₁ = R₁ (1 - D) = 1` with
`R₁ = (1 + iK)/2`. This module derives (`Spectral`)

* `D P_± = λ_± P_±` with `λ_± = 1 - 2/(1 ± 2qi)` (`D_mul_Pp`, `D_mul_Pm`);
* for `|z - 1| ≤ 1/(4Q₀)` with `‖R₁ P₀‖ ≤ Q₀` and `z ≠ λ_±`, an explicit two-sided resolvent
  `R_z = (z - λ₊)⁻¹ P₊ + (z - λ₋)⁻¹ P₋ + (1 + (z - 1) R₁ P₀)⁻¹ R₁ P₀` (`exists_resolvent`) with
  `‖R_z‖ ≤ |z - λ₊|⁻¹ + |z - λ₋|⁻¹ + (4/3) Q₀`, and the endpoint bounds
  `‖R_z J‖, ‖J† D R_z‖ ≤ √w (|z - λ₊|⁻¹ + |z - λ₋|⁻¹) + (2/3)(1 + √μ)` when
  `‖P_± J‖² ≤ w` and `‖K P₀ J‖² ≤ μ`.

No spectral theorem is used: the decomposition is the given one.
-/

namespace LargeSparsityCore.CayleyBlocks

noncomputable section

open ContinuousLinearMap Complex
open scoped InnerProduct

variable {V P : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

section CompOne

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F]
  [NormedSpace ℂ F]

@[simp] theorem comp_one (A : E →L[ℂ] F) : A ∘L (1 : E →L[ℂ] E) = A := by ext; rfl

@[simp] theorem one_comp (A : E →L[ℂ] F) : (1 : F →L[ℂ] F) ∘L A = A := by ext; rfl

end CompOne

/-- The Cayley denominator inverse `R₁ = (1 + iK)/2`. -/
def R1 (K : V →L[ℂ] V) : V →L[ℂ] V := (2 : ℂ)⁻¹ • (1 + I • K)

/-- The bulk projection `P₀ = 1 - P₊ - P₋`. -/
def bulk (Pp Pm : V →L[ℂ] V) : V →L[ℂ] V := 1 - Pp - Pm

/-- The isolated Cayley phases `λ_± = 1 - 2/(1 ± 2qi)`. -/
def lamp (q : ℝ) : ℂ := 1 - 2 / (1 + 2 * q * I)

def lamm (q : ℝ) : ℂ := 1 - 2 / (1 - 2 * q * I)

omit [CompleteSpace V] in
theorem commute_R1 (K X : V →L[ℂ] V) (hX : X ∘L K = K ∘L X) :
    X ∘L R1 K = R1 K ∘L X := by
  simp only [R1, comp_smul, smul_comp, comp_add, add_comp, comp_one, one_comp, hX]

/-- The block structure of the private generator and its Cayley transform. -/
structure Spectral (K D Pp Pm : V →L[ℂ] V) (q : ℝ) : Prop where
  self : IsSelfAdjoint K
  pp_idem : Pp ∘L Pp = Pp
  pm_idem : Pm ∘L Pm = Pm
  pp_adj : IsSelfAdjoint Pp
  pm_adj : IsSelfAdjoint Pm
  pp_pm : Pp ∘L Pm = 0
  pm_pp : Pm ∘L Pp = 0
  k_pp : K ∘L Pp = ((2 * q : ℝ) : ℂ) • Pp
  k_pm : K ∘L Pm = ((-(2 * q) : ℝ) : ℂ) • Pm
  cayley_right : (1 - D) ∘L R1 K = 1
  cayley_left : R1 K ∘L (1 - D) = 1

namespace Spectral

variable {K D Pp Pm : V →L[ℂ] V} {q : ℝ}

theorem adjoint_comp_self_adjoint {A B : V →L[ℂ] V} (hA : IsSelfAdjoint A)
    (hB : IsSelfAdjoint B) : (A ∘L B)† = B ∘L A := by
  rw [adjoint_comp, hA.adjoint_eq, hB.adjoint_eq]

theorem pp_k (h : Spectral K D Pp Pm q) : Pp ∘L K = ((2 * q : ℝ) : ℂ) • Pp := by
  have h1 := congrArg adjoint h.k_pp
  rw [adjoint_comp, h.self.adjoint_eq, h.pp_adj.adjoint_eq, map_smulₛₗ,
    h.pp_adj.adjoint_eq, Complex.conj_ofReal] at h1
  simpa using h1

theorem pm_k (h : Spectral K D Pp Pm q) : Pm ∘L K = ((-(2 * q) : ℝ) : ℂ) • Pm := by
  have h1 := congrArg adjoint h.k_pm
  rw [adjoint_comp, h.self.adjoint_eq, h.pm_adj.adjoint_eq, map_smulₛₗ,
    h.pm_adj.adjoint_eq, Complex.conj_ofReal] at h1
  simpa using h1

theorem commute_pp_k (h : Spectral K D Pp Pm q) : Pp ∘L K = K ∘L Pp := by
  rw [h.pp_k, h.k_pp]

theorem commute_pm_k (h : Spectral K D Pp Pm q) : Pm ∘L K = K ∘L Pm := by
  rw [h.pm_k, h.k_pm]


/-- `D` commutes with `R₁`. -/
theorem commute_D_R1 (h : Spectral K D Pp Pm q) : D ∘L R1 K = R1 K ∘L D := by
  have h1 := h.cayley_right
  have h2 := h.cayley_left
  rw [sub_comp, one_comp] at h1
  rw [comp_sub, comp_one] at h2
  have : R1 K - D ∘L R1 K = R1 K - R1 K ∘L D := by rw [h1, h2]
  exact sub_right_injective this

/-- Every operator commuting with `K` commutes with `D`. -/
theorem commute_D (h : Spectral K D Pp Pm q) (X : V →L[ℂ] V) (hX : X ∘L K = K ∘L X) :
    X ∘L D = D ∘L X := by
  have hXR := commute_R1 K X hX
  -- `(1 - D) X = X (1 - D)` using `R₁ (1 - D) = (1 - D) R₁ = 1`.
  have key : (1 - D) ∘L X = X ∘L (1 - D) := by
    calc (1 - D) ∘L X = (1 - D) ∘L X ∘L (R1 K ∘L (1 - D)) := by rw [h.cayley_left, comp_one]
      _ = (1 - D) ∘L (X ∘L R1 K) ∘L (1 - D) := by simp only [comp_assoc]
      _ = (1 - D) ∘L (R1 K ∘L X) ∘L (1 - D) := by rw [hXR]
      _ = ((1 - D) ∘L R1 K) ∘L X ∘L (1 - D) := by simp only [comp_assoc]
      _ = X ∘L (1 - D) := by rw [h.cayley_right, one_comp]
  rw [sub_comp, comp_sub, one_comp, comp_one] at key
  exact (sub_right_injective key).symm

theorem bulk_idem (h : Spectral K D Pp Pm q) : bulk Pp Pm ∘L bulk Pp Pm = bulk Pp Pm := by
  rw [← sub_eq_zero]
  have e : bulk Pp Pm ∘L bulk Pp Pm - bulk Pp Pm =
      (Pp ∘L Pp - Pp) + (Pm ∘L Pm - Pm) + Pp ∘L Pm + Pm ∘L Pp := by
    simp only [bulk, ← mul_def]
    noncomm_ring
  rw [e, h.pp_idem, h.pm_idem, h.pp_pm, h.pm_pp, sub_self, sub_self, add_zero, add_zero, add_zero]

theorem bulk_adj (h : Spectral K D Pp Pm q) : IsSelfAdjoint (bulk Pp Pm) := by
  unfold bulk
  exact ((IsSelfAdjoint.one _).sub h.pp_adj).sub h.pm_adj

theorem commute_bulk_k (h : Spectral K D Pp Pm q) : bulk Pp Pm ∘L K = K ∘L bulk Pp Pm := by
  simp only [bulk, sub_comp, comp_sub, one_comp, comp_one, h.commute_pp_k, h.commute_pm_k]

omit [CompleteSpace V] in
theorem sum_proj : Pp + Pm + bulk Pp Pm = 1 := by
  simp only [bulk]
  abel

theorem R1_mul_Pp (h : Spectral K D Pp Pm q) : R1 K ∘L Pp = ((1 + 2 * q * I) / 2) • Pp := by
  rw [R1, smul_comp, add_comp, one_comp, smul_comp, h.k_pp, smul_smul]
  match_scalars
  ring

theorem R1_mul_Pm (h : Spectral K D Pp Pm q) : R1 K ∘L Pm = ((1 - 2 * q * I) / 2) • Pm := by
  rw [R1, smul_comp, add_comp, one_comp, smul_comp, h.k_pm, smul_smul]
  match_scalars
  ring_nf

theorem one_add_ne_zero (q : ℝ) : (1 + 2 * q * I) ≠ 0 := by
  intro h0
  have := congrArg Complex.re h0
  simp at this

theorem one_sub_ne_zero (q : ℝ) : (1 - 2 * q * I) ≠ 0 := by
  intro h0
  have := congrArg Complex.re h0
  simp at this

omit [CompleteSpace V] in
theorem eigen_of_R1 {X : V →L[ℂ] V} {a : ℂ} (ha : a ≠ 0) (hR : (1 - D) ∘L R1 K = 1)
    (hX : R1 K ∘L X = (a / 2) • X) : D ∘L X = (1 - 2 / a) • X := by
  have h1 : (1 - D) ∘L (R1 K ∘L X) = X := by rw [← comp_assoc, hR, one_comp]
  rw [hX, comp_smul, sub_comp, one_comp] at h1
  have h2 : X - D ∘L X = (a / 2)⁻¹ • X := by
    have h := congrArg (fun Y : V →L[ℂ] V => (a / 2)⁻¹ • Y) h1
    simp only [smul_smul, inv_mul_cancel₀ (div_ne_zero ha two_ne_zero), one_smul] at h
    exact h
  have h3 : D ∘L X = X - (a / 2)⁻¹ • X :=
    calc D ∘L X = X - (X - D ∘L X) := (sub_sub_cancel _ _).symm
      _ = X - (a / 2)⁻¹ • X := by rw [h2]
  rw [h3, sub_smul, one_smul, inv_div]

/-- `D P₊ = λ₊ P₊`. -/
theorem D_mul_Pp (h : Spectral K D Pp Pm q) : D ∘L Pp = lamp q • Pp :=
  eigen_of_R1 (one_add_ne_zero q) h.cayley_right h.R1_mul_Pp

/-- `D P₋ = λ₋ P₋`. -/
theorem D_mul_Pm (h : Spectral K D Pp Pm q) : D ∘L Pm = lamm q • Pm :=
  eigen_of_R1 (one_sub_ne_zero q) h.cayley_right h.R1_mul_Pm

end Spectral

/-- A self-adjoint idempotent has norm at most one. -/
theorem norm_proj_le_one {X : V →L[ℂ] V} (hX : X ∘L X = X) (hXa : IsSelfAdjoint X) :
    ‖X‖ ≤ 1 :=
  IsStarProjection.norm_le X ⟨hX, hXa⟩

/-- The norm of `A† B` for self-adjoint `B` is the norm of `B A`. -/
theorem norm_adjoint_comp {A : P →L[ℂ] V} {B : V →L[ℂ] V} (hB : IsSelfAdjoint B) :
    ‖A† ∘L B‖ = ‖B ∘L A‖ := by
  rw [← LinearIsometryEquiv.norm_map (adjoint (𝕜 := ℂ) (E := V) (F := P)), adjoint_comp,
    adjoint_adjoint, hB.adjoint_eq]

theorem norm_lamp (q : ℝ) : ‖lamp q‖ = 1 := by
  have hne := Spectral.one_add_ne_zero q
  have h : lamp q = (2 * q * I - 1) / (1 + 2 * q * I) := by
    rw [lamp]
    field_simp
    ring
  rw [h, norm_div, div_eq_one_iff_eq (norm_ne_zero_iff.mpr hne)]
  have e1 : ‖2 * q * I - 1‖ ^ 2 = 1 + 4 * q ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  have e2 : ‖1 + 2 * q * I‖ ^ 2 = 1 + 4 * q ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  have := e1.trans e2.symm
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp this

theorem norm_lamm (q : ℝ) : ‖lamm q‖ = 1 := by
  have h : lamm q = lamp (-q) := by
    simp only [lamm, lamp, Complex.ofReal_neg]
    ring_nf
  rw [h, norm_lamp]

section Resolvent

variable {K D Pp Pm : V →L[ℂ] V} {q : ℝ}

/-- **The resolvent of the Cayley operator near one.** For `|z - 1| ≤ 1/(4Q₀)` with
`‖R₁ P₀‖ ≤ Q₀` and `z ≠ λ_±`, the operator `z - D` has the explicit inverse
`(z - λ₊)⁻¹ P₊ + (z - λ₋)⁻¹ P₋ + U⁻¹ R₁ P₀`, where `U = 1 + (z - 1) R₁ P₀` and `‖U⁻¹‖ ≤ 4/3`. -/
theorem exists_resolvent (h : Spectral K D Pp Pm q) {Q₀ : ℝ}
    (hQ : ‖R1 K ∘L bulk Pp Pm‖ ≤ Q₀) (z : ℂ) (hz : ‖z - 1‖ * Q₀ ≤ 1 / 4)
    (hzp : z ≠ lamp q) (hzm : z ≠ lamm q) :
    ∃ Ui : V →L[ℂ] V, ‖Ui‖ ≤ 4 / 3 ∧
      Ui ∘L (R1 K ∘L bulk Pp Pm) = (R1 K ∘L bulk Pp Pm) ∘L Ui ∧
      Ui ∘L D = D ∘L Ui ∧
      (z • (1 : V →L[ℂ] V) - D) ∘L ((z - lamp q)⁻¹ • Pp + (z - lamm q)⁻¹ • Pm +
        Ui ∘L (R1 K ∘L bulk Pp Pm)) = 1 ∧
      ((z - lamp q)⁻¹ • Pp + (z - lamm q)⁻¹ • Pm + Ui ∘L (R1 K ∘L bulk Pp Pm)) ∘L
        (z • (1 : V →L[ℂ] V) - D) = 1 := by
  set B0 := bulk Pp Pm with hB0
  set N := R1 K ∘L B0 with hN
  have hX : ‖(z - 1) • N‖ ≤ 1 / 4 := by
    rw [norm_smul]
    calc ‖z - 1‖ * ‖N‖ ≤ ‖z - 1‖ * Q₀ := mul_le_mul_of_nonneg_left hQ (norm_nonneg _)
      _ ≤ 1 / 4 := hz
  obtain ⟨Ui, hU1, hU2, hUn⟩ := GeneralResolvent.exists_inverse_one_add ((z - 1) • N) hX
  -- Commutation facts.
  have hBK := h.commute_bulk_k
  have hDR := h.commute_D_R1
  have hDB : B0 ∘L D = D ∘L B0 := h.commute_D B0 hBK
  have hDN : N ∘L D = D ∘L N := by
    rw [hN, comp_assoc, hDB, ← comp_assoc, ← hDR, comp_assoc]
  have hcomm_inv : ∀ X : V →L[ℂ] V, X ∘L N = N ∘L X → Ui ∘L X = X ∘L Ui := by
    intro X hXN
    have hXU : X ∘L (1 + (z - 1) • N) = (1 + (z - 1) • N) ∘L X := by
      rw [comp_add, add_comp, comp_one, one_comp, comp_smul, smul_comp, hXN]
    calc Ui ∘L X = Ui ∘L X ∘L ((1 + (z - 1) • N) ∘L Ui) := by rw [hU1, comp_one]
      _ = Ui ∘L (X ∘L (1 + (z - 1) • N)) ∘L Ui := by simp only [comp_assoc]
      _ = Ui ∘L ((1 + (z - 1) • N) ∘L X) ∘L Ui := by rw [hXU]
      _ = (Ui ∘L (1 + (z - 1) • N)) ∘L X ∘L Ui := by simp only [comp_assoc]
      _ = X ∘L Ui := by rw [hU2, one_comp]
  have hUN : Ui ∘L N = N ∘L Ui := hcomm_inv N rfl
  have hUD : Ui ∘L D = D ∘L Ui := hcomm_inv D hDN.symm
  -- The bulk part inverts `z - D` on the bulk.
  have hB2 := h.bulk_idem
  have hzDN : (z • (1 : V →L[ℂ] V) - D) ∘L N = (1 + (z - 1) • N) ∘L B0 := by
    have hR := h.cayley_right
    have e : (z • (1 : V →L[ℂ] V) - D) = (z - 1) • (1 : V →L[ℂ] V) + (1 - D) := by
      rw [sub_smul, one_smul]
      abel
    rw [e, add_comp, smul_comp, one_comp, hN, ← comp_assoc (1 - D), hR, one_comp, add_comp,
      one_comp, smul_comp, comp_assoc, hB2]
    abel
  have hNzD : N ∘L (z • (1 : V →L[ℂ] V) - D) = (1 + (z - 1) • N) ∘L B0 := by
    have hc : N ∘L (z • (1 : V →L[ℂ] V) - D) = (z • (1 : V →L[ℂ] V) - D) ∘L N := by
      rw [comp_sub, sub_comp, comp_smul, smul_comp, comp_one, one_comp, hDN]
    rw [hc, hzDN]
  have hDp := h.D_mul_Pp
  have hDm := h.D_mul_Pm
  have hpD : Pp ∘L D = D ∘L Pp := h.commute_D Pp h.commute_pp_k
  have hmD : Pm ∘L D = D ∘L Pm := h.commute_D Pm h.commute_pm_k
  have hp0 : z - lamp q ≠ 0 := sub_ne_zero.mpr hzp
  have hm0 : z - lamm q ≠ 0 := sub_ne_zero.mpr hzm
  have hzp' : (z • (1 : V →L[ℂ] V) - D) ∘L Pp = (z - lamp q) • Pp := by
    rw [sub_comp, smul_comp, one_comp, hDp, sub_smul]
  have hzm' : (z • (1 : V →L[ℂ] V) - D) ∘L Pm = (z - lamm q) • Pm := by
    rw [sub_comp, smul_comp, one_comp, hDm, sub_smul]
  have hpz : Pp ∘L (z • (1 : V →L[ℂ] V) - D) = (z - lamp q) • Pp := by
    rw [comp_sub, comp_smul, comp_one, hpD, hDp, sub_smul]
  have hmz : Pm ∘L (z • (1 : V →L[ℂ] V) - D) = (z - lamm q) • Pm := by
    rw [comp_sub, comp_smul, comp_one, hmD, hDm, sub_smul]
  refine ⟨Ui, hUn, hUN, hUD, ?_, ?_⟩
  · have hUzD : (z • (1 : V →L[ℂ] V) - D) ∘L Ui = Ui ∘L (z • (1 : V →L[ℂ] V) - D) := by
      rw [sub_comp, comp_sub, smul_comp, comp_smul, one_comp, comp_one, hUD]
    rw [comp_add, comp_add, comp_smul, comp_smul, hzp', hzm', smul_smul, smul_smul,
      inv_mul_cancel₀ hp0, inv_mul_cancel₀ hm0, one_smul, one_smul, ← comp_assoc, hUzD,
      comp_assoc, hzDN, ← comp_assoc, hU2, one_comp, hB0]
    exact Spectral.sum_proj
  · rw [add_comp, add_comp, smul_comp, smul_comp, hpz, hmz, smul_smul, smul_smul,
      inv_mul_cancel₀ hp0, inv_mul_cancel₀ hm0, one_smul, one_smul, comp_assoc, hNzD,
      ← comp_assoc, hU2, one_comp, hB0]
    exact Spectral.sum_proj

theorem isSelfAdjoint_K_bulk (h : Spectral K D Pp Pm q) :
    IsSelfAdjoint (K ∘L bulk Pp Pm) := by
  show star (K ∘L bulk Pp Pm) = K ∘L bulk Pp Pm
  rw [star_eq_adjoint, adjoint_comp, h.self.adjoint_eq, h.bulk_adj.adjoint_eq, h.commute_bulk_k]

theorem D_mul_R1 (h : Spectral K D Pp Pm q) : D ∘L R1 K = R1 K - 1 := by
  have hR := h.cayley_right
  rw [sub_comp, one_comp] at hR
  rw [← hR]
  abel

/-- **Norm and endpoint bounds for the Cayley resolvent.** -/
theorem exists_resolvent_bounds (h : Spectral K D Pp Pm q) (J : P →L[ℂ] V) (hJ : J† ∘L J = 1)
    {Q₀ sw sm : ℝ} (hQ : ‖R1 K ∘L bulk Pp Pm‖ ≤ Q₀) (hPpJ : ‖Pp ∘L J‖ ≤ sw)
    (hPmJ : ‖Pm ∘L J‖ ≤ sw) (hKJ : ‖K ∘L bulk Pp Pm ∘L J‖ ≤ sm) (z : ℂ)
    (hz : ‖z - 1‖ * Q₀ ≤ 1 / 4) (hzp : z ≠ lamp q) (hzm : z ≠ lamm q) :
    ∃ R : V →L[ℂ] V, (z • (1 : V →L[ℂ] V) - D) ∘L R = 1 ∧ R ∘L (z • (1 : V →L[ℂ] V) - D) = 1 ∧
      ‖R‖ ≤ ‖z - lamp q‖⁻¹ + ‖z - lamm q‖⁻¹ + 4 / 3 * Q₀ ∧
      ‖R ∘L J‖ ≤ sw * (‖z - lamp q‖⁻¹ + ‖z - lamm q‖⁻¹) + 2 / 3 * (1 + sm) ∧
      ‖(J† ∘L D) ∘L R‖ ≤ sw * (‖z - lamp q‖⁻¹ + ‖z - lamm q‖⁻¹) + 2 / 3 * (1 + sm) := by
  obtain ⟨Ui, hUn, hUN, hUD, h1, h2⟩ := exists_resolvent h hQ z hz hzp hzm
  set B0 := bulk Pp Pm with hB0
  set N := R1 K ∘L B0 with hN
  have hPp1 : ‖Pp‖ ≤ 1 := norm_proj_le_one h.pp_idem h.pp_adj
  have hPm1 : ‖Pm‖ ≤ 1 := norm_proj_le_one h.pm_idem h.pm_adj
  have hB1 : ‖B0‖ ≤ 1 := norm_proj_le_one h.bulk_idem h.bulk_adj
  have hJ1 : ‖J‖ ≤ 1 := GeneralResolvent.norm_isometry_le J hJ
  have hB0J : ‖B0 ∘L J‖ ≤ 1 :=
    (opNorm_comp_le _ _).trans (by nlinarith [norm_nonneg B0, norm_nonneg J])
  have hsw : 0 ≤ sw := (norm_nonneg _).trans hPpJ
  have hsm : 0 ≤ sm := (norm_nonneg _).trans hKJ
  have hQ0 : 0 ≤ Q₀ := (norm_nonneg _).trans hQ
  have hhalf : ‖(2 : ℂ)⁻¹‖ = 1 / 2 := by norm_num
  -- `R₁ P₀ J` and `J† D R₁ P₀`.
  have hNJ : ‖N ∘L J‖ ≤ 1 / 2 * (1 + sm) := by
    have e : N ∘L J = (2 : ℂ)⁻¹ • (B0 ∘L J + I • (K ∘L B0 ∘L J)) := by
      rw [hN, R1]
      simp only [smul_comp, add_comp, one_comp, comp_assoc]
    rw [e, norm_smul, hhalf]
    gcongr
    calc ‖B0 ∘L J + I • (K ∘L B0 ∘L J)‖ ≤ ‖B0 ∘L J‖ + ‖I • (K ∘L B0 ∘L J)‖ := norm_add_le _ _
      _ ≤ 1 + sm := by
          rw [norm_smul, Complex.norm_I, one_mul]
          exact add_le_add hB0J hKJ
  have hJDN : ‖(J† ∘L D) ∘L N‖ ≤ 1 / 2 * (1 + sm) := by
    have e : (J† ∘L D) ∘L N = (2 : ℂ)⁻¹ • (I • (J† ∘L (K ∘L B0)) - J† ∘L B0) := by
      rw [hN, comp_assoc, ← comp_assoc D, D_mul_R1 h, R1]
      simp only [sub_comp, smul_comp, add_comp, one_comp, comp_sub, comp_smul, comp_add]
      module
    rw [e, norm_smul, hhalf]
    gcongr
    calc ‖I • (J† ∘L (K ∘L B0)) - J† ∘L B0‖ ≤ ‖I • (J† ∘L (K ∘L B0))‖ + ‖J† ∘L B0‖ :=
          norm_sub_le _ _
      _ = ‖(K ∘L B0) ∘L J‖ + ‖B0 ∘L J‖ := by
          rw [norm_smul, Complex.norm_I, one_mul, norm_adjoint_comp (isSelfAdjoint_K_bulk h),
            norm_adjoint_comp h.bulk_adj]
      _ ≤ sm + 1 := by
          rw [comp_assoc]
          exact add_le_add hKJ hB0J
      _ = 1 + sm := by ring
  refine ⟨_, h1, h2, ?_, ?_, ?_⟩
  · calc ‖(z - lamp q)⁻¹ • Pp + (z - lamm q)⁻¹ • Pm + Ui ∘L N‖ ≤
          ‖(z - lamp q)⁻¹ • Pp‖ + ‖(z - lamm q)⁻¹ • Pm‖ + ‖Ui ∘L N‖ := norm_add₃_le
      _ ≤ ‖z - lamp q‖⁻¹ * 1 + ‖z - lamm q‖⁻¹ * 1 + 4 / 3 * Q₀ := by
          rw [norm_smul, norm_smul, norm_inv, norm_inv]
          gcongr
          exact (opNorm_comp_le _ _).trans (mul_le_mul hUn hQ (norm_nonneg _) (by norm_num))
      _ = _ := by ring
  · rw [add_comp, add_comp, smul_comp, smul_comp, comp_assoc]
    calc ‖(z - lamp q)⁻¹ • (Pp ∘L J) + (z - lamm q)⁻¹ • (Pm ∘L J) + Ui ∘L (N ∘L J)‖ ≤
          ‖(z - lamp q)⁻¹ • (Pp ∘L J)‖ + ‖(z - lamm q)⁻¹ • (Pm ∘L J)‖ + ‖Ui ∘L (N ∘L J)‖ :=
          norm_add₃_le
      _ ≤ ‖z - lamp q‖⁻¹ * sw + ‖z - lamm q‖⁻¹ * sw + 4 / 3 * (1 / 2 * (1 + sm)) := by
          rw [norm_smul, norm_smul, norm_inv, norm_inv]
          gcongr
          exact (opNorm_comp_le _ _).trans (mul_le_mul hUn hNJ (norm_nonneg _) (by norm_num))
      _ = _ := by ring
  · have hDp := h.D_mul_Pp
    have hDm := h.D_mul_Pm
    have e : (J† ∘L D) ∘L ((z - lamp q)⁻¹ • Pp + (z - lamm q)⁻¹ • Pm + Ui ∘L N) =
        ((z - lamp q)⁻¹ * lamp q) • (J† ∘L Pp) + ((z - lamm q)⁻¹ * lamm q) • (J† ∘L Pm) +
          ((J† ∘L D) ∘L N) ∘L Ui := by
      rw [comp_add, comp_add, comp_smul, comp_smul, comp_assoc, hDp,
        comp_assoc (adjoint J) D Pm, hDm,
        comp_smul, comp_smul, smul_smul, smul_smul, hUN, ← comp_assoc]
    rw [e]
    calc _ ≤ ‖((z - lamp q)⁻¹ * lamp q) • (J† ∘L Pp)‖ +
          ‖((z - lamm q)⁻¹ * lamm q) • (J† ∘L Pm)‖ + ‖((J† ∘L D) ∘L N) ∘L Ui‖ := norm_add₃_le
      _ ≤ ‖z - lamp q‖⁻¹ * sw + ‖z - lamm q‖⁻¹ * sw + (1 / 2 * (1 + sm)) * (4 / 3) := by
          rw [norm_smul, norm_smul, norm_mul, norm_mul, norm_inv, norm_inv, norm_lamp, norm_lamm,
            mul_one, mul_one, norm_adjoint_comp h.pp_adj, norm_adjoint_comp h.pm_adj]
          gcongr
          exact (opNorm_comp_le _ _).trans (mul_le_mul hJDN hUn (norm_nonneg _) (by positivity))
      _ = _ := by ring

end Resolvent

end

end LargeSparsityCore.CayleyBlocks
