import ODELowerBoundExtensions.Psd.Matrices

/-!
# Parity amplitudes and the readout correlation of the PSD families

Manuscript lines 4048-4053 (common gauge, endpoint
amplitude `σ(X) a` on the alternating vector `v`), 4083-4084 (`a' ≥ 7a/8`) and 4086-4095 (start
vector, `P ∈ [1/2, 1]`, observable `M_0`, parity-corrected expectation `a'/P ≥ 7a/8`).

* `psd_searchChain_amp`, `psd_scalarChain_amp`: the gauge identities
  `Hamiltonian.searchChain_eq_conj` and `Hamiltonian.scalarChain_eq_conj` carried through
  `psdCore` (`psdCore_unitary_conj`) and the flow (`heat_unitary_conj`) give
  `⟨n, v| e^{-t(1-H'_X)/2} |0, v⟩ = σ(X) ⟨n| e^{-t(1-B')/2} |0⟩`.
* The start vector is the Hamiltonian lower bound's `(|r₀⟩ + |0, v⟩)/√2`
  (`Hamiltonian.searchInput`, `Hamiltonian.scalarInput`); the observable is
  `M_0 = |r₀⟩⟨n, v| + |n, v⟩⟨r₀|`, i.e. `Hamiltonian.readoutObs 0` (`psdSearchObs`,
  `psdScalarObs`). Since `r₀` is fixed (`heat_fullMatrix_refZero`) and the core flows on its own,
  `x(T) = (|r₀⟩ + e^{-T D_core} |0, v⟩)/√2` (`heat_readoutInput`), `P = ‖x(T)‖² ∈ [1/2, 1]`
  (`norm_sq_heat_readoutInput`, contraction) and `⟨x(T), M_0 x(T)⟩ = Re⟨n, v| e^{-T D} |0, v⟩`
  (`heat_readout_expectation`).
* `psd_search_corr`, `psd_scalar_corr`: for the normalised solution `x(T)/‖x(T)‖` the
  parity-corrected expectation of `M_0` is `a'/P ≥ a' ≥ 7a/8` (line 4093).
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

namespace ODELowerBoundExtensions.Psd

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.Hamiltonian
open scoped Matrix InnerProductSpace Matrix.Norms.L2Operator

/-! ### Parity amplitudes (lines 4048-4053) -/

/-- **Gadget-family parity amplitude** (lines 4048-4053): for even `m > 0` and every real `t`,
`⟨n, v| e^{-t(1-H_X)/2} |0, v⟩ = σ(X) ⟨n| e^{-t(1-B)/2} |0⟩`. -/
theorem psd_searchChain_amp {n m : ℕ} (hm : Even m) (hm0 : 0 < m) (c : ℕ → ℝ)
    (j : Fin n → Fin m) (t : ℝ) :
    ⟪chainVec n m (Fin.last n), heat (psdCore (searchChain n m c j)) t (chainVec n m 0)⟫_ℂ =
      (parity j : ℂ) * heatEndAmp n c t := by
  have hkron : psdCore (Matrix.kronecker (pathMatrix n c) (1 : Matrix (Fin m) (Fin m) ℂ)) =
      Matrix.kronecker (psdCore (pathMatrix n c)) (1 : Matrix (Fin m) (Fin m) ℂ) := by
    have hsub : ∀ {S : Type} [Fintype S] [DecidableEq S] (K : Matrix S S ℂ),
        (1 : Matrix S S ℂ) - K = 1 + (-1 : ℂ) • K := fun K => by
      rw [neg_one_smul, sub_eq_add_neg]
    rw [psdCore, psdCore, hsub, hsub]
    unfold Matrix.kronecker
    rw [Matrix.smul_kronecker, Matrix.add_kronecker, Matrix.smul_kronecker,
      Matrix.one_kronecker_one]
  rw [searchChain_eq_conj, psdCore_unitary_conj (searchGauge_mem_unitaryGroup j),
    heat_unitary_conj (searchGauge_mem_unitaryGroup j) _ t,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    conjTranspose_searchGauge_chainVec hm j 0, ← ContinuousLinearMap.adjoint_inner_left,
    ← ContinuousLinearMap.star_eq_adjoint, ← Helpers.Chains.mO_conjTranspose,
    conjTranspose_searchGauge_chainVec hm j (Fin.last n), inner_smul_left, map_smul,
    inner_smul_right, hkron, inner_chainVec_heat_kronecker hm0, Fin.val_last, Fin.val_zero,
    gaugeSign_zero, one_mul, starRingEnd_apply, star_gaugeSign, gaugeSign_of_le j le_rfl]
  rfl

/-- **Scalar-family parity amplitude** (lines 4120-4121, diagonal sign gauge):
`⟨n| e^{-t(1-H_x)/2} |0⟩ = σ(x) ⟨n| e^{-t(1-B)/2} |0⟩` for every real `t`. -/
theorem psd_scalarChain_amp {n : ℕ} (c : ℕ → ℝ) (x : Fin n → Bool) (t : ℝ) :
    heat (psdCore (scalarChain n c x)) t (EuclideanSpace.single 0 1) (Fin.last n) =
      (BitDegree.bitParity x : ℂ) * heatEndAmp n c t := by
  have h0 : (fun k : Fin (n + 1) => bitGaugeSign x k) 0 = 1 := by
    show bitGaugeSign x ((0 : Fin (n + 1)) : ℕ) = 1
    rw [Fin.val_zero, bitGaugeSign_zero]
  rw [scalarChain_eq_conj, psdCore_unitary_conj (signGauge_mem_unitaryGroup x),
    heat_unitary_conj (signGauge_mem_unitaryGroup x) _ t,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, signGauge_conjTranspose,
    signGauge, Helpers.Chains.mO_diagonal_single (fun k : Fin (n + 1) => bitGaugeSign x k) 0 h0,
    Helpers.Chains.mO_diagonal_apply, Fin.val_last, bitGaugeSign_of_le x le_rfl]
  rfl

/-! ### The readout of the evolved start vector (lines 4086-4093) -/

section Readout

variable {C : Type} [Fintype C] [DecidableEq C] {s : ℕ}

/-- `x(t) = (|r₀⟩ + coreVec (e^{-tH} v₀))/√2` for the start vector `(|r₀⟩ + v₀)/√2`, every
real `t`. -/
theorem heat_readoutInput (H : Matrix C C ℂ) (t : ℝ) (v₀ : EuclideanSpace ℂ C) :
    heat (fullMatrix H s) t (readoutInput v₀) =
      ((Real.sqrt 2 : ℂ))⁻¹ • (EuclideanSpace.single refZero 1 + coreVec (heat H t v₀)) := by
  rw [readoutInput, map_smul, map_add, heat_fullMatrix_refZero, heat_fullMatrix_coreVec]

/-- `P = ‖x(t)‖² = (1 + ‖e^{-tH} v₀‖²)/2`. -/
theorem norm_sq_heat_readoutInput (H : Matrix C C ℂ) (t : ℝ) (v₀ : EuclideanSpace ℂ C) :
    ‖heat (fullMatrix H s) t (readoutInput v₀)‖ ^ 2 = (1 + ‖heat H t v₀‖ ^ 2) / 2 := by
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _
    (inner_single_refZero_coreVec (s := s) (heat H t v₀))
  rw [norm_coreVec, PiLp.norm_single, norm_one] at h
  have hs : ‖((Real.sqrt 2 : ℂ))⁻¹‖ ^ 2 = 1 / 2 := by
    rw [norm_inv, Complex.norm_of_nonneg (Real.sqrt_nonneg 2), inv_pow,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), one_div]
  rw [heat_readoutInput, norm_smul, mul_pow, hs, sq, h]
  ring

/-- **The readout expectation** (lines 4089-4093): `⟨x(t), M_0 x(t)⟩ = Re⟨w| e^{-tH} |v₀⟩` for
`M_0 = |r₀⟩⟨w| + |w⟩⟨r₀|` (`readoutObs 0 w`), every real `t`. -/
theorem heat_readout_expectation (H : Matrix C C ℂ) (v₀ w : EuclideanSpace ℂ C) (t : ℝ) :
    ⟪heat (fullMatrix H s) t (readoutInput v₀),
        readoutObs 0 w (heat (fullMatrix H s) t (readoutInput v₀))⟫_ℂ =
      ((⟪w, heat H t v₀⟫_ℂ).re : ℂ) := by
  set c : ℂ := ((Real.sqrt 2 : ℂ))⁻¹ with hc_def
  have h1 : ⟪coreVec (s := s) w,
      c • (EuclideanSpace.single refZero 1 + coreVec (heat H t v₀))⟫_ℂ =
      c * ⟪w, heat H t v₀⟫_ℂ := by
    have hcte : ⟪coreVec (s := s) w, EuclideanSpace.single refZero 1⟫_ℂ = 0 := by
      rw [← inner_conj_symm, inner_single_refZero_coreVec, map_zero]
    rw [inner_smul_right, inner_add_right, hcte, zero_add, inner_coreVec]
  have h2 : ((c • (EuclideanSpace.single (refZero : FullIndex C s) 1 +
      coreVec (heat H t v₀)) : EuclideanSpace ℂ (FullIndex C s))) refZero = c := by
    show c * ((EuclideanSpace.single (refZero : FullIndex C s) (1 : ℂ)) refZero +
      coreVec (s := s) (heat H t v₀) (Sum.inr (Sum.inl 0))) = c
    rw [coreVec_apply_inr, PiLp.single_apply, if_pos rfl, add_zero, mul_one]
  have hstar : star c = c := by
    rw [hc_def, star_inv₀, Complex.star_def, Complex.conj_ofReal]
  have hcc : c * c = ((1 / 2 : ℝ) : ℂ) := by
    rw [hc_def, ← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    push_cast; ring
  rw [heat_readoutInput, inner_readoutObs_self, h1, h2, hstar, pow_zero, one_mul]
  have : c * ⟪w, heat H t v₀⟫_ℂ * c = ((1 / 2 : ℝ) : ℂ) * ⟪w, heat H t v₀⟫_ℂ := by
    linear_combination ⟪w, heat H t v₀⟫_ℂ * hcc
  rw [this, Complex.re_ofReal_mul]
  congr 1
  ring

/-- **`P ∈ [1/2, 1]`** for a PSD core `(1 - H)/2` of a Hermitian contraction `H` and a unit
start vector `v₀`: `x(t) = e^{-t fullMatrix ((1-H)/2) s} (|r₀⟩ + v₀)/√2` has
`1/2 ≤ ‖x(t)‖²` and `‖x(t)‖ ≤ 1` for `t ≥ 0` (lines 4087-4088). -/
theorem endpoint_norm_psdCore {H : Matrix C C ℂ} (hH : H.IsHermitian) (h1 : ‖H‖ ≤ 1)
    {v₀ : EuclideanSpace ℂ C} (hv : ‖v₀‖ = 1) {t : ℝ} (ht : 0 ≤ t) :
    1 / 2 ≤ ‖heat (fullMatrix (psdCore H) s) t (readoutInput v₀)‖ ^ 2 ∧
      ‖heat (fullMatrix (psdCore H) s) t (readoutInput v₀)‖ ≤ 1 := by
  have hc : ‖heat (psdCore H) t v₀‖ ≤ 1 := by
    calc ‖heat (psdCore H) t v₀‖ ≤ ‖heat (psdCore H) t‖ * ‖v₀‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * 1 := by
          rw [hv]
          exact mul_le_mul_of_nonneg_right
            (norm_heat_le _ (accretive_of_posSemidef (posSemidef_psdCore hH h1)) t ht) zero_le_one
      _ = 1 := one_mul 1
  have hP := norm_sq_heat_readoutInput (s := s) (psdCore H) t v₀
  have hc0 := norm_nonneg (heat (psdCore H) t v₀)
  have hx0 := norm_nonneg (heat (fullMatrix (psdCore H) s) t (readoutInput (s := s) v₀))
  refine ⟨by rw [hP]; nlinarith, ?_⟩
  have hP1 : ‖heat (fullMatrix (psdCore H) s) t (readoutInput (s := s) v₀)‖ ^ 2 ≤ 1 := by
    rw [hP]; nlinarith
  nlinarith

end Readout

/-- **The normalisation step** (line 4093): if `x ≠ 0` has `‖x‖ ≤ 1` and
`⟨x, M x⟩ = σ R` with `σ² = 1` and `R ≥ 7a/8 > 0`, then the unit direction `ψ = x/‖x‖` has
`σ ⟨ψ, M ψ⟩ = R/‖x‖² ≥ 7a/8`. -/
theorem seven_eighths_le_corr_unitDirection {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (M : E →L[ℂ] E) {x : E} {σ R a : ℝ} (hx0 : 0 < ‖x‖)
    (hx1 : ‖x‖ ≤ 1) (hσ : σ * σ = 1) (hxM : ⟪x, M x⟫_ℂ = ((σ * R : ℝ) : ℂ))
    (hR : 7 * a / 8 ≤ R) (ha : 0 < a) :
    7 * a / 8 ≤ σ * (⟪ODEStateNormalization.unitDirection x,
      M (ODEStateNormalization.unitDirection x)⟫_ℂ).re := by
  have hu : ODEStateNormalization.unitDirection x = ((‖x‖⁻¹ : ℝ) : ℂ) • x := by
    rw [ODEStateNormalization.unitDirection, Complex.coe_smul]
  have hψ : ⟪ODEStateNormalization.unitDirection x, M (ODEStateNormalization.unitDirection x)⟫_ℂ =
      ((‖x‖⁻¹ * ‖x‖⁻¹ * (σ * R) : ℝ) : ℂ) := by
    rw [hu, map_smul, inner_smul_left, inner_smul_right, hxM, Complex.conj_ofReal]
    push_cast; ring
  have hinv : 1 ≤ ‖x‖⁻¹ * ‖x‖⁻¹ := by
    have : 1 ≤ ‖x‖⁻¹ := (one_le_inv₀ hx0).mpr hx1
    nlinarith
  rw [hψ, Complex.ofReal_re]
  have hR0 : 0 ≤ R := by linarith
  calc 7 * a / 8 ≤ R := hR
    _ ≤ ‖x‖⁻¹ * ‖x‖⁻¹ * R := le_mul_of_one_le_left hR0 hinv
    _ = σ * (‖x‖⁻¹ * ‖x‖⁻¹ * (σ * R)) := by
      linear_combination (-(‖x‖⁻¹ * ‖x‖⁻¹ * R)) * hσ

/-! ### The hard families -/

/-- **The gadget-family observable** `M_0 = |r₀⟩⟨n, v| + |n, v⟩⟨r₀|` (lines 4089-4092). -/
def psdSearchObs (n μ s : ℕ) :
    EuclideanSpace ℂ (SearchIndex n μ s) →L[ℂ] EuclideanSpace ℂ (SearchIndex n μ s) :=
  readoutObs 0 (chainVec n (2 ^ μ) (Fin.last n))

/-- **The scalar-family observable** `M_0 = |r₀⟩⟨n| + |n⟩⟨r₀|`. -/
def psdScalarObs (n s : ℕ) :
    EuclideanSpace ℂ (ScalarIndex n s) →L[ℂ] EuclideanSpace ℂ (ScalarIndex n s) :=
  readoutObs 0 (EuclideanSpace.single (Fin.last n) 1)

/-- `M_0` is a Hermitian contraction. -/
theorem psdSearchObs_contraction (n μ s : ℕ) :
    IsSelfAdjoint (psdSearchObs n μ s) ∧ ‖psdSearchObs n μ s‖ ≤ 1 := by
  exact ⟨isSelfAdjoint_readoutObs _ _, norm_readoutObs_le _
      (norm_chainVec (Nat.pos_of_ne_zero (pow_ne_zero μ two_ne_zero)) _).le⟩

/-- `M_0` is a Hermitian contraction. -/
theorem psdScalarObs_contraction (n s : ℕ) :
    IsSelfAdjoint (psdScalarObs n s) ∧ ‖psdScalarObs n s‖ ≤ 1 := by
  exact ⟨isSelfAdjoint_readoutObs _ _, norm_readoutObs_le _ (by rw [PiLp.norm_single, norm_one])⟩

variable {n μ s : ℕ} {τ : ℝ}

/-- **`P ∈ [1/2, 1]`** for the gadget family (lines 4087-4088), at `T = τ ≥ 0`, `u = τ/2`. -/
theorem psdSearch_endpoint_norm (hτ : 0 ≤ τ) (j : Fin n → Fin (2 ^ μ)) :
    1 / 2 ≤ ‖heat (psdSearchMat n μ s (τ / 2) j) τ (searchInput n μ s)‖ ^ 2 ∧
      ‖heat (psdSearchMat n μ s (τ / 2) j) τ (searchInput n μ s)‖ ≤ 1 := by
  have hm0 : 0 < 2 ^ μ := Nat.pos_of_ne_zero (pow_ne_zero μ two_ne_zero)
  exact endpoint_norm_psdCore (isHermitian_searchChain _ _ _ _)
    ((norm_searchChain hm0 _ j).trans_le (norm_pathMatrix_psdWeight_le n _))
    (norm_chainVec hm0 0) hτ

/-- **`P ∈ [1/2, 1]`** for the scalar family. -/
theorem psdScalar_endpoint_norm (hτ : 0 ≤ τ) (x : Fin n → Bool) :
    1 / 2 ≤ ‖heat (psdScalarMat n s (τ / 2) x) τ (scalarInput n s)‖ ^ 2 ∧
      ‖heat (psdScalarMat n s (τ / 2) x) τ (scalarInput n s)‖ ≤ 1 := by
  exact endpoint_norm_psdCore (isHermitian_scalarChain _ _ _)
    ((norm_scalarChain _ x).trans_le (norm_pathMatrix_psdWeight_le n _))
    (by rw [PiLp.norm_single, norm_one]) hτ

/-- **Gadget-family correlation** (lines 4083-4093): for `n ≥ 1`, `μ ≥ 1`, `τ > 0`, the
normalised solution `x(T)/‖x(T)‖` has parity-corrected `M_0`-expectation `a'/P ≥ 7a/8`,
`a = psdAmp n (τ/2)`. -/
theorem psd_search_corr (hn : 1 ≤ n) (hμ : 1 ≤ μ) (hτ : 0 < τ) (j : Fin n → Fin (2 ^ μ)) :
    7 * psdAmp n (τ / 2) / 8 ≤ parity j *
      (⟪ODEStateNormalization.unitDirection
          (heat (psdSearchMat n μ s (τ / 2) j) τ (searchInput n μ s)),
        psdSearchObs n μ s (ODEStateNormalization.unitDirection
          (heat (psdSearchMat n μ s (τ / 2) j) τ (searchInput n μ s)))⟫_ℂ).re := by
  have hm0 : 0 < 2 ^ μ := Nat.pos_of_ne_zero (pow_ne_zero μ two_ne_zero)
  have hm : Even (2 ^ μ) := (Nat.even_pow' (by omega)).mpr even_two
  obtain ⟨hP, hx1⟩ := psdSearch_endpoint_norm (s := s) hτ.le j
  have hx0 : 0 < ‖heat (psdSearchMat n μ s (τ / 2) j) τ (searchInput n μ s)‖ := by
    by_contra h
    have h0 : ‖heat (psdSearchMat n μ s (τ / 2) j) τ (searchInput n μ s)‖ = 0 :=
      le_antisymm (not_lt.mp h) (norm_nonneg _)
    rw [h0] at hP; norm_num at hP
  have hσ : parity j * parity j = 1 := by rw [← abs_mul_abs_self, abs_parity, one_mul]
  have hR := seven_eighths_le_heatEndAmp hn (half_pos hτ)
  rw [show 2 * (τ / 2) = τ by ring] at hR
  refine seven_eighths_le_corr_unitDirection _ hx0 hx1 hσ ?_ hR (psdAmp_pos hn (half_pos hτ))
  have h := heat_readout_expectation (s := s)
    (psdCore (searchChain n (2 ^ μ) (psdWeight n (τ / 2)) j)) (chainVec n (2 ^ μ) 0)
    (chainVec n (2 ^ μ) (Fin.last n)) τ
  rw [psd_searchChain_amp hm hm0 _ j τ, Complex.re_ofReal_mul] at h
  exact h

/-- **Scalar-family correlation** (lines 4119-4121): the same positive endpoint correlation
`a'/P ≥ 7a/8` with the parity `σ(x) = (-1)^{Σ_k x_k}`. -/
theorem psd_scalar_corr (hn : 1 ≤ n) (hτ : 0 < τ) (x : Fin n → Bool) :
    7 * psdAmp n (τ / 2) / 8 ≤ BitDegree.bitParity x *
      (⟪ODEStateNormalization.unitDirection
          (heat (psdScalarMat n s (τ / 2) x) τ (scalarInput n s)),
        psdScalarObs n s (ODEStateNormalization.unitDirection
          (heat (psdScalarMat n s (τ / 2) x) τ (scalarInput n s)))⟫_ℂ).re := by
  obtain ⟨hP, hx1⟩ := psdScalar_endpoint_norm (s := s) hτ.le x
  have hx0 : 0 < ‖heat (psdScalarMat n s (τ / 2) x) τ (scalarInput n s)‖ := by
    by_contra h
    have h0 : ‖heat (psdScalarMat n s (τ / 2) x) τ (scalarInput n s)‖ = 0 :=
      le_antisymm (not_lt.mp h) (norm_nonneg _)
    rw [h0] at hP; norm_num at hP
  have hσ : BitDegree.bitParity x * BitDegree.bitParity x = 1 := by
    rw [← abs_mul_abs_self, BitDegree.abs_bitParity, one_mul]
  have hR := seven_eighths_le_heatEndAmp hn (half_pos hτ)
  rw [show 2 * (τ / 2) = τ by ring] at hR
  refine seven_eighths_le_corr_unitDirection _ hx0 hx1 hσ ?_ hR (psdAmp_pos hn (half_pos hτ))
  have h := heat_readout_expectation (s := s)
    (psdCore (scalarChain n (psdWeight n (τ / 2)) x)) (EuclideanSpace.single 0 1)
    (EuclideanSpace.single (Fin.last n) 1) τ
  rw [EuclideanSpace.inner_single_left, map_one, one_mul, psd_scalarChain_amp _ x τ,
    Complex.re_ofReal_mul] at h
  exact h

end

end ODELowerBoundExtensions.Psd
