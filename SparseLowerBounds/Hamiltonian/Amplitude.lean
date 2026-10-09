import SparseLowerBounds.Hamiltonian.Instance

set_option synthInstance.maxHeartbeats 400000

section
/-!
# Reading the amplitude as a correlation

Manuscript lines 2291-2306 (eq. `hsl:eq:readout`). For a core start vector
`v₀` and target `t`, the known input and observable are

  `ψ_in = (|r₀⟩ + |v₀⟩)/√2`,  `M = iⁿ |r₀⟩⟨t| + (-i)ⁿ |t⟩⟨r₀|`.

Because `r₀` is an isolated zero-energy vertex, the expectation of `M` in
`e^{-iτH} ψ_in` is `Re(iⁿ ⟨t| e^{-iτH_core} |v₀⟩)` (`readout_expectation`); no
global phase convention or controlled simulation is involved. `M` is
Hermitian with `‖M‖ = ‖t‖` (`norm_readoutObs_le`).

For the hard families (`v₀ = |0, v⟩`, `t = |n, v⟩` for the search chains;
`v₀ = |0⟩`, `t = |n⟩` for the scalar chain) the parity-corrected ideal
expectation is at least `7A/8` after dyadic rounding (lines 2299-2301;
`search_corr`, `scalar_corr`), where `A = chainAmp n a τ = sin(aτ/n)^n`.
-/

namespace SparseLowerBounds.Hamiltonian

noncomputable section
open scoped Matrix InnerProductSpace

variable {C : Type} [Fintype C] [DecidableEq C] {s : ℕ}

/-- A core vector placed in the full space (zero on references and padding). -/
def coreVec (v : EuclideanSpace ℂ C) : EuclideanSpace ℂ (FullIndex C s) :=
  WithLp.toLp 2 fun i => Sum.elim (fun c => v c) (fun _ => 0) i

/-- The known input `(|r₀⟩ + |v₀⟩)/√2` (eq. `hsl:eq:readout`). -/
def readoutInput (v₀ : EuclideanSpace ℂ C) : EuclideanSpace ℂ (FullIndex C s) :=
  ((Real.sqrt 2 : ℂ))⁻¹ • (EuclideanSpace.single refZero 1 + coreVec v₀)

/-- The matrix of `M = iⁿ |r₀⟩⟨t| + (-i)ⁿ |t⟩⟨r₀|`. -/
def readoutMatrix (n : ℕ) (t : EuclideanSpace ℂ C) : Matrix (FullIndex C s) (FullIndex C s) ℂ :=
  Matrix.of fun i i' =>
    Complex.I ^ n * (if i = refZero then 1 else 0) * star ((coreVec (s := s) t) i') +
      (-Complex.I) ^ n * (coreVec (s := s) t) i * (if i' = refZero then 1 else 0)

/-- The readout observable `M` (eq. `hsl:eq:readout`). -/
def readoutObs (n : ℕ) (t : EuclideanSpace ℂ C) :
    EuclideanSpace ℂ (FullIndex C s) →L[ℂ] EuclideanSpace ℂ (FullIndex C s) :=
  SparseHamiltonian.SparseStateOverlap.matrixOperator (readoutMatrix n t)

/-! ### Core vectors and the reference vertex -/

omit [Fintype C] [DecidableEq C] in
theorem coreVec_apply_inl (v : EuclideanSpace ℂ C) (c : C) :
    coreVec (s := s) v (Sum.inl c) = v c := rfl

omit [Fintype C] [DecidableEq C] in
theorem coreVec_apply_inr (v : EuclideanSpace ℂ C) (r : Fin 2 ⊕ Fin s) :
    coreVec (s := s) v (Sum.inr r) = 0 := rfl

omit [DecidableEq C] in
/-- The core embedding is isometric. -/
theorem inner_coreVec (u v : EuclideanSpace ℂ C) :
    ⟪coreVec (s := s) u, coreVec (s := s) v⟫_ℂ = ⟪u, v⟫_ℂ := by
  simp only [PiLp.inner_apply, Fintype.sum_sum_type, coreVec_apply_inl, coreVec_apply_inr,
    inner_zero_left, Finset.sum_const_zero, add_zero]

omit [DecidableEq C] in
theorem norm_coreVec (v : EuclideanSpace ℂ C) : ‖coreVec (s := s) v‖ = ‖v‖ := by
  have h := inner_coreVec (s := s) v v
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have h2 : ‖coreVec (s := s) v‖ ^ 2 = ‖v‖ ^ 2 := by exact_mod_cast h
  have h3 := congrArg Real.sqrt h2
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h3

/-- `r₀` is orthogonal to the core. -/
theorem inner_single_refZero_coreVec (v : EuclideanSpace ℂ C) :
    ⟪EuclideanSpace.single (refZero : FullIndex C s) (1 : ℂ), coreVec (s := s) v⟫_ℂ = 0 := by
  rw [EuclideanSpace.inner_single_left]
  show (starRingEnd ℂ) 1 * coreVec (s := s) v (Sum.inr (Sum.inl 0)) = 0
  rw [coreVec_apply_inr, mul_zero]

/-- The core block evolves on its own (`evolve_fullMatrix_core`). -/
theorem evolve_coreVec (H : Matrix C C ℂ) (τ : ℝ) (v : EuclideanSpace ℂ C) :
    evolve (fullMatrix H s) τ (coreVec v) = coreVec (evolve H τ v) :=
  evolve_fullMatrix_core H s τ v

/-- **`r₀` is a fixed zero-energy vertex** (line 2281):
`e^{-iτ fullMatrix H s} |r₀⟩ = |r₀⟩` for every core `H`. -/
theorem evolve_refZero (H : Matrix C C ℂ) (τ : ℝ) :
    evolve (fullMatrix H s) τ (EuclideanSpace.single refZero 1) =
      EuclideanSpace.single refZero 1 := by
  have h0 : (WithLp.toLp 2 fun c => (EuclideanSpace.single (refZero : FullIndex C s) (1 : ℂ))
      (Sum.inl c) : EuclideanSpace ℂ C) = 0 := by
    ext c; simp [refZero]
  have h1 : (WithLp.toLp 2 fun r => (EuclideanSpace.single (refZero : FullIndex C s) (1 : ℂ))
      (Sum.inr r) : EuclideanSpace ℂ (Fin 2 ⊕ Fin s)) = EuclideanSpace.single (Sum.inl 0) 1 := by
    ext r; rcases r with k | p <;> simp [refZero]
  have h2 : (WithLp.toLp 2 fun k => (EuclideanSpace.single (Sum.inl 0 : Fin 2 ⊕ Fin s) (1 : ℂ))
      (Sum.inl k) : EuclideanSpace ℂ (Fin 2)) = EuclideanSpace.single 0 1 := by
    ext k; simp
  have h3 : (WithLp.toLp 2 fun p => (EuclideanSpace.single (Sum.inl 0 : Fin 2 ⊕ Fin s) (1 : ℂ))
      (Sum.inr p) : EuclideanSpace ℂ (Fin s)) = 0 := by
    ext p; simp
  unfold fullMatrix
  rw [evolve_fromBlocks_zero, h0, h1, evolve_fromBlocks_zero, h2, h3, evolve_refBlock_single_zero]
  ext i
  rcases i with c | k | p <;> simp [refZero]

/-- The evolved known input: `(|r₀⟩ + e^{-iτH} |v₀⟩)/√2`. -/
theorem evolve_readoutInput (H : Matrix C C ℂ) (τ : ℝ) (v₀ : EuclideanSpace ℂ C) :
    evolve (fullMatrix H s) τ (readoutInput v₀) =
      ((Real.sqrt 2 : ℂ))⁻¹ • (EuclideanSpace.single refZero 1 + coreVec (evolve H τ v₀)) := by
  rw [readoutInput, map_smul, map_add, evolve_refZero, evolve_coreVec]

/-! ### The observable -/

/-- `M w = iⁿ ⟨t, w⟩ |r₀⟩ + (-i)ⁿ w_{r₀} |t⟩`. -/
theorem readoutObs_apply (n : ℕ) (t : EuclideanSpace ℂ C) (w : EuclideanSpace ℂ (FullIndex C s)) :
    readoutObs n t w =
      (Complex.I ^ n * ⟪coreVec (s := s) t, w⟫_ℂ) • EuclideanSpace.single refZero 1 +
        ((-Complex.I) ^ n * w refZero) • coreVec t := by
  ext i
  simp only [readoutObs, SparseHamiltonian.SparseStateOverlap.matrixOperator_apply, readoutMatrix,
    Matrix.of_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, PiLp.single_apply,
    PiLp.inner_apply, RCLike.inner_apply, add_mul, Finset.sum_add_distrib]
  congr 1
  · rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i' _ => ?_
    rw [Complex.star_def]
    ring
  · simp only [mul_assoc, ite_mul, one_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    ring

/-- `⟨w, M w⟩ = 2 Re(iⁿ ⟨t, w⟩ \overline{w_{r₀}})`. -/
theorem inner_readoutObs_self (n : ℕ) (t : EuclideanSpace ℂ C)
    (w : EuclideanSpace ℂ (FullIndex C s)) :
    ⟪w, readoutObs n t w⟫_ℂ =
      ((2 * (Complex.I ^ n * ⟪coreVec (s := s) t, w⟫_ℂ * star (w refZero)).re : ℝ) : ℂ) := by
  have hw : ⟪w, coreVec (s := s) t⟫_ℂ = (starRingEnd ℂ) ⟪coreVec (s := s) t, w⟫_ℂ :=
    (inner_conj_symm _ _).symm
  rw [readoutObs_apply, inner_add_right, inner_smul_right, inner_smul_right,
    EuclideanSpace.inner_single_right, hw, ← Complex.add_conj]
  simp only [map_mul, map_pow, Complex.conj_I, Complex.star_def, Complex.conj_conj]
  ring

theorem isSelfAdjoint_readoutObs (n : ℕ) (t : EuclideanSpace ℂ C) :
    IsSelfAdjoint (readoutObs (s := s) n t) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric,
    LinearMap.isSymmetric_iff_inner_map_self_real]
  intro w
  simp only [ContinuousLinearMap.coe_coe]
  rw [← inner_conj_symm (readoutObs n t w) w, inner_readoutObs_self, Complex.conj_conj,
    Complex.conj_ofReal]

theorem norm_readoutObs_le (n : ℕ) {t : EuclideanSpace ℂ C} (ht : ‖t‖ ≤ 1) :
    ‖readoutObs (s := s) n t‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => ?_
  rw [one_mul]
  set e : EuclideanSpace ℂ (FullIndex C s) := EuclideanSpace.single refZero 1 with he_def
  set w' : EuclideanSpace ℂ (FullIndex C s) := w - w refZero • e with hw'_def
  have hee : ⟪e, e⟫_ℂ = 1 := by
    rw [he_def, EuclideanSpace.inner_single_left]; simp
  have hew : ⟪e, w⟫_ℂ = w refZero := by
    rw [he_def, EuclideanSpace.inner_single_left]; simp
  have hew' : ⟪e, w'⟫_ℂ = 0 := by
    rw [hw'_def, inner_sub_right, inner_smul_right, hee, hew, mul_one, sub_self]
  have hect : ⟪e, coreVec (s := s) t⟫_ℂ = 0 := inner_single_refZero_coreVec t
  have hcte : ⟪coreVec (s := s) t, e⟫_ℂ = 0 := by
    rw [← inner_conj_symm, hect, map_zero]
  have hct : ⟪coreVec (s := s) t, w⟫_ℂ = ⟪coreVec (s := s) t, w'⟫_ℂ := by
    rw [hw'_def, inner_sub_right, inner_smul_right, hcte, mul_zero, sub_zero]
  -- `‖w‖² = ‖w'‖² + |w_{r₀}|²`
  have hw2 : ‖w‖ * ‖w‖ = ‖w'‖ * ‖w'‖ + ‖w refZero‖ * ‖w refZero‖ := by
    have hsplit : w = w' + w refZero • e := by rw [hw'_def, sub_add_cancel]
    have h0 : ⟪w', w refZero • e⟫_ℂ = 0 := by
      rw [inner_smul_right, ← inner_conj_symm, hew', map_zero, mul_zero]
    have := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ h0
    rw [← hsplit, norm_smul, he_def, PiLp.norm_single, norm_one, mul_one] at this
    exact this
  -- `‖M w‖² = |⟨t, w⟩|² + |w_{r₀}|² ‖t‖²`
  have hM : ‖readoutObs (s := s) n t w‖ * ‖readoutObs (s := s) n t w‖ =
      ‖⟪coreVec (s := s) t, w⟫_ℂ‖ * ‖⟪coreVec (s := s) t, w⟫_ℂ‖ +
        (‖w refZero‖ * ‖t‖) * (‖w refZero‖ * ‖t‖) := by
    have h0 : ⟪(Complex.I ^ n * ⟪coreVec (s := s) t, w⟫_ℂ) • e,
        ((-Complex.I) ^ n * w refZero) • coreVec (s := s) t⟫_ℂ = 0 := by
      rw [inner_smul_left, inner_smul_right, hect, mul_zero, mul_zero]
    rw [readoutObs_apply, ← he_def, norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ h0,
      norm_smul, norm_smul, norm_mul, norm_mul, norm_pow, norm_pow, norm_neg, Complex.norm_I,
      one_pow, one_mul, one_mul, he_def, PiLp.norm_single, norm_one, mul_one, norm_coreVec]
  have hcs : ‖⟪coreVec (s := s) t, w⟫_ℂ‖ ≤ ‖w'‖ := by
    rw [hct]
    calc ‖⟪coreVec (s := s) t, w'⟫_ℂ‖ ≤ ‖coreVec (s := s) t‖ * ‖w'‖ := norm_inner_le_norm _ _
      _ ≤ 1 * ‖w'‖ := by
        rw [norm_coreVec]; exact mul_le_mul_of_nonneg_right ht (norm_nonneg _)
      _ = ‖w'‖ := one_mul _
  rw [mul_self_le_mul_self_iff (norm_nonneg _) (norm_nonneg _), hM, hw2]
  have h1 : ‖⟪coreVec (s := s) t, w⟫_ℂ‖ * ‖⟪coreVec (s := s) t, w⟫_ℂ‖ ≤ ‖w'‖ * ‖w'‖ :=
    mul_self_le_mul_self (norm_nonneg _) hcs
  have h2 : (‖w refZero‖ * ‖t‖) * (‖w refZero‖ * ‖t‖) ≤ ‖w refZero‖ * ‖w refZero‖ := by
    have : ‖w refZero‖ * ‖t‖ ≤ ‖w refZero‖ :=
      mul_le_of_le_one_right (norm_nonneg _) ht
    exact mul_self_le_mul_self (mul_nonneg (norm_nonneg _) (norm_nonneg _)) this
  linarith

theorem norm_readoutInput {v₀ : EuclideanSpace ℂ C} (hv : ‖v₀‖ = 1) :
    ‖readoutInput (s := s) v₀‖ = 1 := by
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _
    (inner_single_refZero_coreVec (s := s) v₀)
  rw [norm_coreVec, hv, PiLp.norm_single, norm_one] at h
  have h2 : ‖EuclideanSpace.single (refZero : FullIndex C s) (1 : ℂ) + coreVec v₀‖ =
      Real.sqrt 2 := by
    rw [← Real.sqrt_mul_self (norm_nonneg _), h]; norm_num
  have hs : (0 : ℝ) < Real.sqrt 2 := by positivity
  rw [readoutInput, norm_smul, h2, norm_inv, Complex.norm_of_nonneg hs.le, inv_mul_cancel₀ hs.ne']

/-- **The readout expectation** (lines 2293-2300): with `r₀` isolated at zero
energy, `⟨M⟩ = Re(iⁿ ⟨t| e^{-iτH} |v₀⟩)` in the evolved known input. -/
theorem readout_expectation (H : Matrix C C ℂ) (n : ℕ) (v₀ t : EuclideanSpace ℂ C) (τ : ℝ) :
    ⟪evolve (fullMatrix H s) τ (readoutInput v₀),
        readoutObs n t (evolve (fullMatrix H s) τ (readoutInput v₀))⟫_ℂ =
      ((Complex.I ^ n * ⟪t, evolve H τ v₀⟫_ℂ).re : ℂ) := by
  set c : ℂ := ((Real.sqrt 2 : ℂ))⁻¹ with hc_def
  have h1 : ⟪coreVec (s := s) t,
      c • (EuclideanSpace.single refZero 1 + coreVec (evolve H τ v₀))⟫_ℂ =
      c * ⟪t, evolve H τ v₀⟫_ℂ := by
    have hcte : ⟪coreVec (s := s) t, EuclideanSpace.single refZero 1⟫_ℂ = 0 := by
      rw [← inner_conj_symm, inner_single_refZero_coreVec, map_zero]
    rw [inner_smul_right, inner_add_right, hcte, zero_add, inner_coreVec]
  have h2 : ((c • (EuclideanSpace.single (refZero : FullIndex C s) 1 +
      coreVec (evolve H τ v₀)) : EuclideanSpace ℂ (FullIndex C s))) refZero = c := by
    show c * ((EuclideanSpace.single (refZero : FullIndex C s) (1 : ℂ)) refZero +
      coreVec (s := s) (evolve H τ v₀) (Sum.inr (Sum.inl 0))) = c
    rw [coreVec_apply_inr, PiLp.single_apply, if_pos rfl, add_zero, mul_one]
  have hstar : star c = c := by
    rw [hc_def, star_inv₀, Complex.star_def, Complex.conj_ofReal]
  have hcc : c * c = ((1 / 2 : ℝ) : ℂ) := by
    rw [hc_def, ← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    push_cast; ring
  rw [evolve_readoutInput, inner_readoutObs_self, h1, h2, hstar]
  have : Complex.I ^ n * (c * ⟪t, evolve H τ v₀⟫_ℂ) * c =
      ((1 / 2 : ℝ) : ℂ) * (Complex.I ^ n * ⟪t, evolve H τ v₀⟫_ℂ) := by
    linear_combination (Complex.I ^ n * ⟪t, evolve H τ v₀⟫_ℂ) * hcc
  rw [this, Complex.re_ofReal_mul]
  congr 1
  ring

/-! ### The hard families -/

/-- The search families' input `(|r₀⟩ + |0, v⟩)/√2`. -/
def searchInput (n μ s : ℕ) : EuclideanSpace ℂ (SearchIndex n μ s) :=
  readoutInput (chainVec n (2 ^ μ) 0)

/-- The search families' observable `iⁿ |r₀⟩⟨n, v| + (-i)ⁿ |n, v⟩⟨r₀|`. -/
def searchObs (n μ s : ℕ) :
    EuclideanSpace ℂ (SearchIndex n μ s) →L[ℂ] EuclideanSpace ℂ (SearchIndex n μ s) :=
  readoutObs n (chainVec n (2 ^ μ) (Fin.last n))

/-- The precision family's input `(|r₀⟩ + |0⟩)/√2`. -/
def scalarInput (n s : ℕ) : EuclideanSpace ℂ (ScalarIndex n s) :=
  readoutInput (EuclideanSpace.single 0 1)

/-- The precision family's observable `iⁿ |r₀⟩⟨n| + (-i)ⁿ |n⟩⟨r₀|`. -/
def scalarObs (n s : ℕ) :
    EuclideanSpace ℂ (ScalarIndex n s) →L[ℂ] EuclideanSpace ℂ (ScalarIndex n s) :=
  readoutObs n (EuclideanSpace.single (Fin.last n) 1)

variable {n μ : ℕ}

theorem norm_searchInput (n μ s : ℕ) : ‖searchInput n μ s‖ = 1 :=
  norm_readoutInput (norm_chainVec (Nat.pos_of_ne_zero (pow_ne_zero μ two_ne_zero)) 0)

theorem norm_scalarInput (n s : ℕ) : ‖scalarInput n s‖ = 1 :=
  norm_readoutInput (by rw [PiLp.norm_single, norm_one])

theorem searchObs_contraction (n μ s : ℕ) :
    IsSelfAdjoint (searchObs n μ s) ∧ ‖searchObs n μ s‖ ≤ 1 :=
  ⟨isSelfAdjoint_readoutObs _ _, norm_readoutObs_le _
    (norm_chainVec (Nat.pos_of_ne_zero (pow_ne_zero μ two_ne_zero)) _).le⟩

theorem scalarObs_contraction (n s : ℕ) :
    IsSelfAdjoint (scalarObs n s) ∧ ‖scalarObs n s‖ ≤ 1 :=
  ⟨isSelfAdjoint_readoutObs _ _, norm_readoutObs_le _ (by rw [PiLp.norm_single, norm_one])⟩

/-- The 7/8 step (lines 2299-2301): if `z` is within `A/8` of `(-i)ⁿ A`, then
`Re(iⁿ z) ≥ 7A/8` (`iⁿ (-i)ⁿ = 1`, `|iⁿ| = 1`). -/
theorem seven_eighths_le_re_I_pow_mul (n : ℕ) {z : ℂ} {A : ℝ}
    (h : ‖z - (-Complex.I) ^ n * (A : ℂ)‖ ≤ A / 8) : 7 * A / 8 ≤ (Complex.I ^ n * z).re := by
  have hI : Complex.I ^ n * (-Complex.I) ^ n = 1 := by
    rw [← mul_pow, mul_neg, Complex.I_mul_I, neg_neg, one_pow]
  have hsplit : Complex.I ^ n * z =
      Complex.I ^ n * (z - (-Complex.I) ^ n * (A : ℂ)) + (A : ℂ) := by
    linear_combination (A : ℂ) * hI
  have hre : -(A / 8) ≤ (Complex.I ^ n * (z - (-Complex.I) ^ n * (A : ℂ))).re := by
    have h1 := Complex.abs_re_le_norm (Complex.I ^ n * (z - (-Complex.I) ^ n * (A : ℂ)))
    rw [norm_mul, norm_pow, Complex.norm_I, one_pow, one_mul] at h1
    linarith [neg_abs_le (Complex.I ^ n * (z - (-Complex.I) ^ n * (A : ℂ))).re]
  rw [hsplit, Complex.add_re, Complex.ofReal_re]
  linarith

/-- The search-family expectation before the parity correction:
`Re(iⁿ σ(X) ⟨n| e^{-iτB'} |0⟩)` (`readout_expectation`, `searchChain_amp`;
`2^μ` is even for `μ ≥ 1`). -/
theorem search_expectation (hμ : 1 ≤ μ) (a τ : ℝ) (j : Fin n → Fin (2 ^ μ)) :
    ⟪evolve (searchHam n μ s a τ j) τ (searchInput n μ s),
        searchObs n μ s (evolve (searchHam n μ s a τ j) τ (searchInput n μ s))⟫_ℂ =
      (((Complex.I ^ n * ((parity j : ℂ) * endAmp n (chainWeight n a τ) τ)).re : ℝ) : ℂ) := by
  have hm : Even (2 ^ μ) := (Nat.even_pow' (by omega)).2 even_two
  have hm0 : 0 < 2 ^ μ := Nat.pos_of_ne_zero (pow_ne_zero μ two_ne_zero)
  rw [searchHam, searchInput, searchObs, readout_expectation, searchChain_amp hm hm0]

/-- The precision-family expectation before the parity correction
(`readout_expectation`, `scalarChain_amp`). -/
theorem scalar_expectation (τ : ℝ) (x : Fin n → Bool) :
    ⟪evolve (scalarHam n s τ x) τ (scalarInput n s),
        scalarObs n s (evolve (scalarHam n s τ x) τ (scalarInput n s))⟫_ℂ =
      (((Complex.I ^ n * ((BitDegree.bitParity x : ℂ) * endAmp n (chainWeight n 1 τ) τ)).re : ℝ) :
        ℂ) := by
  rw [scalarHam, scalarInput, scalarObs, readout_expectation, EuclideanSpace.inner_single_left,
    map_one, one_mul, scalarChain_amp]

/-- Parity correction: a real sign `σ = ±1` cancels against itself,
`σ Re(iⁿ (σ E)) = Re(iⁿ E)`. -/
theorem Amplitude.mul_re_I_pow_sign {σ : ℝ} (hσ : |σ| = 1) (n : ℕ) (E : ℂ) :
    σ * (Complex.I ^ n * ((σ : ℂ) * E)).re = (Complex.I ^ n * E).re := by
  have hσσ : σ * σ = 1 := by rw [← abs_mul_abs_self, hσ, one_mul]
  rw [← Complex.re_ofReal_mul]
  congr 1
  calc (σ : ℂ) * (Complex.I ^ n * ((σ : ℂ) * E)) = ((σ * σ : ℝ) : ℂ) * (Complex.I ^ n * E) := by
        push_cast; ring
    _ = Complex.I ^ n * E := by rw [hσσ, Complex.ofReal_one, one_mul]

/-- **Search-family readout** (lines 2299-2301): after rounding, the
parity-corrected ideal expectation is at least `7A/8`. -/
theorem search_corr (hn : 1 ≤ n) (hμ : 1 ≤ μ) {a τ : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hτ : 0 < τ) (hA : 0 < chainAmp n a τ) (j : Fin n → Fin (2 ^ μ)) :
    7 * chainAmp n a τ / 8 ≤ parity j *
      (⟪evolve (searchHam n μ s a τ j) τ (searchInput n μ s),
        searchObs n μ s (evolve (searchHam n μ s a τ j) τ (searchInput n μ s))⟫_ℂ).re := by
  rw [search_expectation hμ a τ j, Complex.ofReal_re,
    Amplitude.mul_re_I_pow_sign (abs_parity j)]
  exact seven_eighths_le_re_I_pow_mul n (norm_endAmp_chainWeight_sub_le hn ha ha1 hτ hA)

/-- **Precision-family readout**: the same with the bit parity. -/
theorem scalar_corr (hn : 1 ≤ n) {τ : ℝ} (hτ : 0 < τ) (hA : 0 < chainAmp n 1 τ)
    (x : Fin n → Bool) :
    7 * chainAmp n 1 τ / 8 ≤ BitDegree.bitParity x *
      (⟪evolve (scalarHam n s τ x) τ (scalarInput n s),
        scalarObs n s (evolve (scalarHam n s τ x) τ (scalarInput n s))⟫_ℂ).re := by
  rw [scalar_expectation τ x, Complex.ofReal_re,
    Amplitude.mul_re_I_pow_sign (BitDegree.abs_bitParity x)]
  exact seven_eighths_le_re_I_pow_mul n
    (norm_endAmp_chainWeight_sub_le hn one_pos le_rfl hτ hA)

end

end SparseLowerBounds.Hamiltonian
end
