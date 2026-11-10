import SignedFactorSimulation.Cascade
import OptimalPrecision.Taylor.Estimates

/-!
# The uniform finite mesh (`opt:eq:finite-mesh`)

For the factor interface with private unitary `P = U† G U`, let the cascade have `m` slots of
step `v = a/m`. On `|w| = ρ < 1` the generator satisfies `‖Ω(w)‖ ≤ M_ρ = (1 + ρ)/(1 - ρ)`
(`norm_Omega_factor_le`): `Ω = E†U† (ξ (I - Π) + μ_+ Π_+ + μ_- Π_-) U E` is the compression of
a spectral sum with `|ξ|, |μ_±| ≤ M_ρ`. If `v M_ρ ≤ 1/2`, then

  `‖u(w) - e^{-vΩ(w)}‖ ≤ (v M_ρ)³`   (`norm_cayStep_sub_exp_le`),

both factors are contractions (`norm_cayStep_le_one`, `norm_exp_neg_le_one`), and telescoping
gives `‖F_m(w) - e^{-aΩ(w)}‖ ≤ m (v M_ρ)³`. Cauchy's estimate on `|w| = ρ = 1 - 1/(2n)`, with
`M_ρ ≤ 4n` and `ρ^{-(n-1)} ≤ 2`, then proves

  `m ≥ 8an  ⟹  ‖∑_j λ_j Ces_j(F_m) - ∑_j λ_j Ces_j(e^{-aΩ})‖ ≤ 128 A a³ n⁴ / m²`

for weights with `∑ |λ_j| ≤ A` (`finite_mesh`).
-/

set_option autoImplicit false

namespace SignedFactorSimulation

noncomputable section

open Complex ContinuousLinearMap OptimalPrecision OptimalPrecision.Tail Finset
open SparseHamiltonian
open scoped InnerProduct InnerProductSpace ComplexOrder Nat

variable {P W : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]

/-! ### Scalar bounds on the disk -/

theorem norm_xi_le {w : ℂ} (hw : ‖w‖ < 1) : ‖xi w‖ ≤ (1 + ‖w‖) / (1 - ‖w‖) := by
  rw [xi, norm_div]
  have h1 : 1 - ‖w‖ ≤ ‖1 + w‖ := by
    have := norm_sub_norm_le (1 : ℂ) (-w)
    simpa [sub_neg_eq_add] using this
  have h2 : ‖1 - w‖ ≤ 1 + ‖w‖ := by
    have := norm_sub_le (1 : ℂ) w
    simpa using this
  exact div_le_div₀ (by positivity) h2 (by linarith) h1

theorem norm_mobius_le {ζ : ℂ} (hζ : ‖ζ‖ = 1) {w : ℂ} (hw : ‖w‖ < 1) :
    ‖(1 + ζ * w) / (1 - ζ * w)‖ ≤ (1 + ‖w‖) / (1 - ‖w‖) := by
  rw [norm_div]
  have hz : ‖ζ * w‖ = ‖w‖ := by rw [norm_mul, hζ, one_mul]
  have h1 : 1 - ‖w‖ ≤ ‖1 - ζ * w‖ := by
    have := norm_sub_norm_le (1 : ℂ) (ζ * w)
    rw [norm_one, hz] at this
    linarith
  have h2 : ‖1 + ζ * w‖ ≤ 1 + ‖w‖ := by
    have := norm_add_le (1 : ℂ) (ζ * w)
    rw [norm_one, hz] at this
    exact this
  exact div_le_div₀ (by positivity) h2 (by linarith) h1

/-! ### The norm of a spectral sum and of the generator -/

namespace Known

variable (K : Known P W)

/-- `‖a (I - Π) + b Π_+ + c Π_-‖ ≤ M` when `|a|, |b|, |c| ≤ M`. -/
theorem norm_spec_le {a b c : ℂ} {M : ℝ} (ha : ‖a‖ ≤ M) (hb : ‖b‖ ≤ M) (hc : ‖c‖ ≤ M) :
    ‖K.spec a b c‖ ≤ M := by
  have hM : 0 ≤ M := (norm_nonneg a).trans ha
  -- the three projections are self-adjoint idempotents with orthogonal ranges
  have hP0 : (1 - K.proj)† = 1 - K.proj := by rw [map_sub, adjoint_one, K.proj_adjoint]
  have inner_orth : ∀ (S T : W →L[ℂ] W), S† = S → T† = T → S * T = 0 → ∀ x y : W,
      ⟪S x, T y⟫_ℂ = 0 := by
    intro S T hS hT hST x y
    rw [← adjoint_inner_right, hS]
    change ⟪x, (S * T) y⟫_ℂ = 0
    rw [hST, zero_apply, inner_zero_right]
  refine ContinuousLinearMap.opNorm_le_bound _ hM fun x => ?_
  set x0 := (1 - K.proj) x
  set xp := K.plus x
  set xm := K.minus x
  have hx : x = x0 + xp + xm := by
    simp only [x0, xp, xm]
    rw [add_assoc, ← add_apply K.plus, K.plus_add_minus, ← add_apply, sub_add_cancel,
      one_apply_eq_self]
  have h0p := inner_orth _ _ hP0 K.plus_adjoint K.compl_mul_plus x x
  have h0m := inner_orth _ _ hP0 K.minus_adjoint K.compl_mul_minus x x
  have hpm := inner_orth _ _ K.plus_adjoint K.minus_adjoint K.plus_mul_minus x x
  have hspec : K.spec a b c x = a • x0 + b • xp + c • xm := by
    simp only [spec, add_apply, smul_apply, x0, xp, xm]
  -- Pythagoras for the decomposition
  have pyth : ∀ (α β γ : ℂ), ‖α • x0 + β • xp + γ • xm‖ ^ 2 =
      ‖α‖ ^ 2 * ‖x0‖ ^ 2 + ‖β‖ ^ 2 * ‖xp‖ ^ 2 + ‖γ‖ ^ 2 * ‖xm‖ ^ 2 := by
    intro α β γ
    have e1 : ⟪α • x0 + β • xp, γ • xm⟫_ℂ = 0 := by
      rw [inner_add_left, inner_smul_left, inner_smul_left, inner_smul_right, inner_smul_right,
        h0m, hpm]
      simp
    have e2 : ⟪α • x0, β • xp⟫_ℂ = 0 := by
      rw [inner_smul_left, inner_smul_right, h0p]
      simp
    rw [sq, norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ e1,
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ e2, norm_smul, norm_smul,
      norm_smul]
    ring
  have hxx : ‖x‖ ^ 2 = ‖x0‖ ^ 2 + ‖xp‖ ^ 2 + ‖xm‖ ^ 2 := by
    have := pyth 1 1 1
    simpa only [one_smul, norm_one, one_pow, one_mul, ← hx] using this
  have hsq : ‖K.spec a b c x‖ ^ 2 ≤ (M * ‖x‖) ^ 2 := by
    rw [hspec, pyth, mul_pow, hxx]
    have h1 : ‖a‖ ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (norm_nonneg _) ha 2
    have h2 : ‖b‖ ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
    have h3 : ‖c‖ ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hc 2
    nlinarith [sq_nonneg ‖x0‖, sq_nonneg ‖xp‖, sq_nonneg ‖xm‖]
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hM (norm_nonneg _))).mp hsq

/-- The compression by an isometry does not increase norms. -/
theorem norm_compress_le {U : W →L[ℂ] W} (hU : OracleCircuit.IsUnitary U) (X : W →L[ℂ] W) :
    ‖K.compress U X‖ ≤ ‖X‖ := by
  have hUE : ∀ x, ‖(U ∘L K.E) x‖ = ‖x‖ := by
    intro x
    have h1 : (U ∘L K.E)† ∘L (U ∘L K.E) = 1 := by
      rw [adjoint_comp]
      change K.E† ∘L (U† * U) ∘L K.E = 1
      have hU1 : U† * U = 1 := hU.1
      rw [hU1]; exact K.E_isometry
    exact (U ∘L K.E).norm_map_iff_adjoint_comp_self.mpr h1 x
  have hadj : ‖(U ∘L K.E)†‖ ≤ 1 := by
    rw [LinearIsometryEquiv.norm_map]
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
    rw [hUE, one_mul]
  have hfwd : ‖U ∘L K.E‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by rw [hUE, one_mul]
  have e : K.compress U X = (U ∘L K.E)† ∘L X ∘L (U ∘L K.E) := by
    simp only [compress, adjoint_comp]
    rfl
  rw [e]
  calc ‖(U ∘L K.E)† ∘L X ∘L (U ∘L K.E)‖ ≤ ‖(U ∘L K.E)†‖ * (‖X‖ * ‖U ∘L K.E‖) :=
        (opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left (opNorm_comp_le _ _)
          (norm_nonneg _))
    _ ≤ 1 * (‖X‖ * 1) := by gcongr
    _ = ‖X‖ := by ring

/-- `‖Ω(w)‖ ≤ (1 + |w|)/(1 - |w|)` on the unit disk. -/
theorem norm_Omega_factor_le {q : ℝ} (hq : 0 < q) {U : W →L[ℂ] W}
    (hU : OracleCircuit.IsUnitary U) {w : ℂ} (hw : ‖w‖ < 1) :
    ‖Omega q (K.Cop U) (K.Dop U) w‖ ≤ (1 + ‖w‖) / (1 - ‖w‖) := by
  have e : Omega q (K.Cop U) (K.Dop U) w = K.compress U (K.spec (xi w) (muP q w) (muM q w)) := by
    rw [K.compress_spec U hU.1, Omega_eq hq hw]
  rw [e]
  refine (K.norm_compress_le hU _).trans (K.norm_spec_le (norm_xi_le hw) ?_ ?_)
  · rw [← muP_eq hw]; exact norm_mobius_le (norm_zetaP q) hw
  · rw [← muM_eq hw]; exact norm_mobius_le (norm_zetaM q) hw

end Known

/-! ### The Cayley step against the exponential -/

section Pointwise

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem norm_one_le_one : ‖(1 : H →L[ℂ] H)‖ ≤ 1 := norm_id_le

theorem isUnit_one_add_of_norm_lt {Y : H →L[ℂ] H} (hY : ‖Y‖ < 1) : IsUnit (1 + Y) := by
  have h : ‖-Y‖ < 1 := by rwa [norm_neg]
  have hu := (Units.oneSub (-Y) h).isUnit
  rwa [Units.val_oneSub, sub_neg_eq_add] at hu

omit [CompleteSpace H] in
/-- `‖(1 + Y)⁻¹‖ ≤ 1/(1 - ‖Y‖)` from a right inverse. -/
theorem norm_right_inverse_le {Y Dinv : H →L[ℂ] H} (hY : ‖Y‖ < 1) (hD : (1 + Y) * Dinv = 1) :
    ‖Dinv‖ ≤ 1 / (1 - ‖Y‖) := by
  have e : Dinv = 1 - Y * Dinv := by
    rw [add_mul, one_mul] at hD
    rw [← hD]; abel
  have h1 : ‖Dinv‖ ≤ 1 + ‖Y‖ * ‖Dinv‖ := by
    calc ‖Dinv‖ = ‖1 - Y * Dinv‖ := by rw [← e]
      _ ≤ ‖(1 : H →L[ℂ] H)‖ + ‖Y * Dinv‖ := norm_sub_le _ _
      _ ≤ 1 + ‖Y‖ * ‖Dinv‖ := add_le_add norm_id_le (norm_mul_le _ _)
  rw [le_div_iff₀ (by linarith)]
  nlinarith [norm_nonneg Dinv]

omit [CompleteSpace H] in
/-- The rational remainder: with `D (1 + X/2) = 1`,
`(1 - X/2) D - (1 - X + X²/2) = -(X³/4) D`. -/
theorem cayley_remainder (X Dinv : H →L[ℂ] H) (hD : (1 + (2⁻¹ : ℂ) • X) * Dinv = 1) :
    (1 - (2⁻¹ : ℂ) • X) * Dinv - (1 - X + (2⁻¹ : ℂ) • (X * X)) =
      -((4⁻¹ : ℂ) • (X * (X * X))) * Dinv := by
  have key : (1 - X + (2⁻¹ : ℂ) • (X * X)) * (1 + (2⁻¹ : ℂ) • X) =
      (1 - (2⁻¹ : ℂ) • X) + (4⁻¹ : ℂ) • (X * (X * X)) := by
    simp only [mul_add, add_mul, sub_mul, smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
      mul_assoc]
    module
  calc (1 - (2⁻¹ : ℂ) • X) * Dinv - (1 - X + (2⁻¹ : ℂ) • (X * X))
      = (1 - (2⁻¹ : ℂ) • X) * Dinv -
          (1 - X + (2⁻¹ : ℂ) • (X * X)) * ((1 + (2⁻¹ : ℂ) • X) * Dinv) := by rw [hD, mul_one]
    _ = ((1 - (2⁻¹ : ℂ) • X) - (1 - X + (2⁻¹ : ℂ) • (X * X)) * (1 + (2⁻¹ : ℂ) • X)) * Dinv := by
        rw [sub_mul ((1 - (2⁻¹ : ℂ) • X)), mul_assoc]
    _ = -((4⁻¹ : ℂ) • (X * (X * X))) * Dinv := by rw [key]; abel_nf

omit [CompleteSpace H] in
/-- The exponential's second-order Taylor polynomial. -/
theorem exp_taylor_two (X : H →L[ℂ] H) :
    ∑ m ∈ range (2 + 1), ((m ! : ℂ)⁻¹) • (-X) ^ m = 1 - X + (2⁻¹ : ℂ) • (X * X) := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one,
    pow_two, Nat.factorial_zero, Nat.factorial_one, Nat.factorial_two, Nat.cast_one,
    Nat.cast_ofNat, inv_one, one_smul, neg_mul_neg]
  abel

/-- **The pointwise mesh estimate**: for `‖vG‖ ≤ 1/2`,
`‖(I - (v/2)G)(I + (v/2)G)⁻¹ - e^{-vG}‖ ≤ ‖vG‖³`. -/
theorem norm_cayStep_sub_exp_le (v : ℝ) (G : H →L[ℂ] H)
    (hG : ‖(v : ℂ) • G‖ ≤ 1 / 2) :
    ‖cayStep v G - NormedSpace.exp ((-(v : ℂ)) • G)‖ ≤ ‖(v : ℂ) • G‖ ^ 3 := by
  set X : H →L[ℂ] H := (v : ℂ) • G with hX
  have hYX : ((v / 2 : ℝ) : ℂ) • G = (2⁻¹ : ℂ) • X := by
    rw [hX, smul_smul]; congr 1; push_cast; ring
  have hYn : ‖(2⁻¹ : ℂ) • X‖ = ‖X‖ / 2 := by
    rw [norm_smul, norm_inv, Complex.norm_ofNat]; ring
  have hY1 : ‖(2⁻¹ : ℂ) • X‖ < 1 := by rw [hYn]; linarith
  set Dinv := Ring.inverse (1 + (2⁻¹ : ℂ) • X) with hDinv
  have hD : (1 + (2⁻¹ : ℂ) • X) * Dinv = 1 :=
    Ring.mul_inverse_cancel _ (isUnit_one_add_of_norm_lt hY1)
  have hDn : ‖Dinv‖ ≤ 4 / 3 := by
    have := norm_right_inverse_le hY1 hD
    rw [hYn] at this
    calc ‖Dinv‖ ≤ 1 / (1 - ‖X‖ / 2) := this
      _ ≤ 4 / 3 := by rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  have hcay : cayStep v G = (1 - (2⁻¹ : ℂ) • X) * Dinv := by
    rw [cayStep, hYX]; rfl
  have hexp : NormedSpace.exp ((-(v : ℂ)) • G) = NormedSpace.exp (-X) := by rw [hX, neg_smul]
  set T := 1 - X + (2⁻¹ : ℂ) • (X * X) with hT
  -- the two remainders
  have hR1 : ‖(1 - (2⁻¹ : ℂ) • X) * Dinv - T‖ ≤ ‖X‖ ^ 3 / 3 := by
    rw [cayley_remainder X Dinv hD]
    calc ‖-((4⁻¹ : ℂ) • (X * (X * X))) * Dinv‖ ≤ ‖(4⁻¹ : ℂ) • (X * (X * X))‖ * ‖Dinv‖ := by
          rw [← norm_neg ((4⁻¹ : ℂ) • (X * (X * X)))]; exact norm_mul_le _ _
      _ ≤ (‖X‖ ^ 3 / 4) * (4 / 3) := by
          apply mul_le_mul _ hDn (norm_nonneg _) (by positivity)
          rw [norm_smul, norm_inv, Complex.norm_ofNat]
          have h3 : ‖X * (X * X)‖ ≤ ‖X‖ ^ 3 := by
            calc ‖X * (X * X)‖ ≤ ‖X‖ * (‖X‖ * ‖X‖) :=
                  (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (norm_mul_le _ _)
                    (norm_nonneg _))
              _ = ‖X‖ ^ 3 := by ring
          linarith
      _ = ‖X‖ ^ 3 / 3 := by ring
  have hR2 : ‖NormedSpace.exp (-X) - T‖ ≤ ‖X‖ ^ 3 / 2 := by
    have h := norm_exp_sub_sum_le' (-X) 2
    rw [exp_taylor_two, norm_neg] at h
    have he : Real.exp ‖X‖ ≤ 3 := by
      calc Real.exp ‖X‖ ≤ Real.exp 1 := Real.exp_le_exp.mpr (by linarith)
        _ ≤ 3 := by have := Real.exp_one_lt_d9; norm_num at this; linarith
    have hf : ((2 + 1) ! : ℝ) = 6 := by norm_num [Nat.factorial]
    rw [hf] at h
    calc ‖NormedSpace.exp (-X) - T‖ ≤ ‖X‖ ^ (2 + 1) / 6 * Real.exp ‖X‖ := h
      _ ≤ ‖X‖ ^ 3 / 6 * 3 := by
          apply mul_le_mul_of_nonneg_left he (by positivity)
      _ = ‖X‖ ^ 3 / 2 := by ring
  rw [hcay, hexp]
  calc ‖(1 - (2⁻¹ : ℂ) • X) * Dinv - NormedSpace.exp (-X)‖ =
      ‖((1 - (2⁻¹ : ℂ) • X) * Dinv - T) - (NormedSpace.exp (-X) - T)‖ := by congr 1; abel
    _ ≤ ‖(1 - (2⁻¹ : ℂ) • X) * Dinv - T‖ + ‖NormedSpace.exp (-X) - T‖ := norm_sub_le _ _
    _ ≤ ‖X‖ ^ 3 / 3 + ‖X‖ ^ 3 / 2 := add_le_add hR1 hR2
    _ ≤ ‖X‖ ^ 3 := by nlinarith [pow_nonneg (norm_nonneg X) 3]

/-- The Cayley step of an accretive operator is a contraction. -/
theorem norm_cayStep_le_one {v : ℝ} (hv : 0 ≤ v) (G : H →L[ℂ] H)
    (hG : ∀ x, 0 ≤ (⟪x, G x⟫_ℂ).re) (hGn : ‖(v : ℂ) • G‖ ≤ 1 / 2) : ‖cayStep v G‖ ≤ 1 := by
  set Y : H →L[ℂ] H := ((v / 2 : ℝ) : ℂ) • G with hY
  have hYn : ‖Y‖ < 1 := by
    have : Y = (2⁻¹ : ℂ) • ((v : ℂ) • G) := by rw [hY, smul_smul]; congr 1; push_cast; ring
    rw [this, norm_smul, norm_inv, Complex.norm_ofNat]
    linarith
  set Dinv := Ring.inverse (1 + Y)
  have hD : (1 + Y) * Dinv = 1 := Ring.mul_inverse_cancel _ (isUnit_one_add_of_norm_lt hYn)
  have hYacc : ∀ x, 0 ≤ (⟪x, Y x⟫_ℂ).re := by
    intro x
    rw [hY, smul_apply, inner_smul_right, re_ofReal_mul]
    exact mul_nonneg (by positivity) (hG x)
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => ?_
  set z := Dinv y
  have hy : y = z + Y z := by
    have := congrArg (fun T : H →L[ℂ] H => T y) hD
    change ((1 + Y) ∘L Dinv) y = (1 : H →L[ℂ] H) y at this
    rw [comp_apply, add_apply, one_apply_eq_self, one_apply_eq_self] at this
    exact this.symm
  have hcay : cayStep v G y = z - Y z := by
    change ((1 - Y) ∘L Dinv) y = _
    rw [comp_apply, sub_apply, one_apply_eq_self]
  rw [hcay, one_mul]
  have h1 := @norm_sub_sq ℂ _ _ _ _ z (Y z)
  have h2 := @norm_add_sq ℂ _ _ _ _ z (Y z)
  have hz := hYacc z
  have hsq : ‖z - Y z‖ ^ 2 ≤ ‖y‖ ^ 2 := by
    rw [hy, h2, ← sub_nonneg]
    rw [h1]
    simp only [RCLike.re_to_complex] at hz ⊢
    linarith
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

/-- The exponential of minus an accretive operator is a contraction. -/
theorem norm_exp_neg_le_one {v : ℝ} (hv : 0 ≤ v) (G : H →L[ℂ] H)
    (hG : ∀ x, 0 ≤ (⟪x, G x⟫_ℂ).re) : ‖NormedSpace.exp ((-(v : ℂ)) • G)‖ ≤ 1 := by
  have hdiss : SparseHamiltonian.ODEDissipative.Dissipative (-G) := by
    intro x
    rw [neg_apply, inner_neg_right, neg_re]
    linarith [hG x]
  have h := SparseHamiltonian.ODEDissipative.exp_norm_le_one _ hdiss v hv
  have e : (-(v : ℂ)) • G = v • (-G) := by rw [neg_smul, smul_neg, ← Complex.coe_smul]
  rw [e]
  exact h

omit [CompleteSpace H] in
/-- Telescoping powers of contractions: `‖A^m - B^m‖ ≤ m ‖A - B‖`. -/
theorem norm_pow_sub_pow_le {A B : H →L[ℂ] H} (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) (m : ℕ) :
    ‖A ^ m - B ^ m‖ ≤ m * ‖A - B‖ := by
  have hBm : ∀ k : ℕ, ‖B ^ k‖ ≤ 1 := by
    intro k
    induction k with
    | zero => simpa using norm_one_le_one
    | succ k ih =>
      rw [pow_succ]
      calc ‖B ^ k * B‖ ≤ ‖B ^ k‖ * ‖B‖ := norm_mul_le _ _
        _ ≤ 1 * 1 := mul_le_mul ih hB (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1
  induction m with
  | zero => simp
  | succ m ih =>
    have e : A ^ (m + 1) - B ^ (m + 1) = A * (A ^ m - B ^ m) + (A - B) * B ^ m := by
      rw [pow_succ', pow_succ']; noncomm_ring
    rw [e]
    calc ‖A * (A ^ m - B ^ m) + (A - B) * B ^ m‖ ≤
        ‖A * (A ^ m - B ^ m)‖ + ‖(A - B) * B ^ m‖ := norm_add_le _ _
      _ ≤ ‖A‖ * ‖A ^ m - B ^ m‖ + ‖A - B‖ * ‖B ^ m‖ :=
          add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ 1 * (m * ‖A - B‖) + ‖A - B‖ * 1 :=
          add_le_add (mul_le_mul hA ih (norm_nonneg _) zero_le_one)
            (mul_le_mul_of_nonneg_left (hBm m) (norm_nonneg _))
      _ = ((m + 1 : ℕ) : ℝ) * ‖A - B‖ := by push_cast; ring

end Pointwise

/-! ### Assembly -/

/-- `e^{-aG} = (e^{-vG})^m` for `a = m v`. -/
theorem exp_neg_eq_pow {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (G : H →L[ℂ] H) (m : ℕ) (v : ℝ) :
    NormedSpace.exp ((-((m * v : ℝ) : ℂ)) • G) = NormedSpace.exp ((-(v : ℂ)) • G) ^ m := by
  letI : NormedAlgebra ℚ (H →L[ℂ] H) := .restrictScalars ℚ ℂ _
  rw [← NormedSpace.exp_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  congr 2
  push_cast
  ring

/-- Bernoulli: `(1 - 1/(2n))^k ≥ 1/2` for `k ≤ n - 1`. -/
theorem half_le_rho_pow {n : ℕ} (hn : 1 ≤ n) {k : ℕ} (hk : k + 1 ≤ n) :
    (1 / 2 : ℝ) ≤ (1 - 1 / (2 * n)) ^ k := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h := one_add_mul_le_pow (a := -(1 / (2 * (n : ℝ)))) (by
    have : 1 / (2 * (n : ℝ)) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    linarith) k
  rw [← sub_eq_add_neg] at h
  have hk' : (k : ℝ) + 1 ≤ n := by exact_mod_cast hk
  have : (1 / 2 : ℝ) ≤ 1 + k * -(1 / (2 * (n : ℝ))) := by
    rw [mul_neg, ← sub_eq_add_neg, mul_one_div, le_sub_comm, div_le_iff₀ (by positivity)]
    nlinarith
  linarith

namespace Known

variable (K : Known P W)

/-- **The pointwise mesh error** on `|w| = ρ`: `‖F_m(w) - e^{-aΩ(w)}‖ ≤ m (v M_ρ)³` for
`a = m v` and `v M_ρ ≤ 1/2`. -/
theorem norm_cascTransfer_sub_Fop_le [FiniteDimensional ℂ P] {q : ℝ} (hq : 0 < q)
    {U : W →L[ℂ] W} (hU : OracleCircuit.IsUnitary U) {v : ℝ} (hv : 0 ≤ v) (m : ℕ) {w : ℂ}
    (hw : ‖w‖ < 1) (hvM : v * ((1 + ‖w‖) / (1 - ‖w‖)) ≤ 1 / 2) :
    ‖cascTransfer (K.priv q U) K.E v m w - Fop (m * v) q (K.Cop U) (K.Dop U) w‖ ≤
      m * (v * ((1 + ‖w‖) / (1 - ‖w‖))) ^ 3 := by
  set G := Omega q (K.Cop U) (K.Dop U) w with hG
  have hacc : ∀ x, 0 ≤ (⟪x, G x⟫_ℂ).re := fun x =>
    re_inner_Omega_nonneg hq (K.one_sub_Dop_isPositive hU.1) (K.Dop_add_Cop_isPositive U)
      (K.Dop_sub_Cop_isPositive U) hw x
  have hGn : ‖(v : ℂ) • G‖ ≤ v * ((1 + ‖w‖) / (1 - ‖w‖)) := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hv]
    exact mul_le_mul_of_nonneg_left (K.norm_Omega_factor_le hq hU hw) hv
  have hGh : ‖(v : ℂ) • G‖ ≤ 1 / 2 := hGn.trans hvM
  rw [K.transfer_cascade_factor hq hU hv m hw, Fop, ← hG, exp_neg_eq_pow G m v]
  calc ‖cayStep v G ^ m - NormedSpace.exp ((-(v : ℂ)) • G) ^ m‖ ≤
      m * ‖cayStep v G - NormedSpace.exp ((-(v : ℂ)) • G)‖ :=
        norm_pow_sub_pow_le (norm_cayStep_le_one hv G hacc hGh) (norm_exp_neg_le_one hv G hacc) m
    _ ≤ m * ‖(v : ℂ) • G‖ ^ 3 :=
        mul_le_mul_of_nonneg_left (norm_cayStep_sub_exp_le v G hGh) (Nat.cast_nonneg m)
    _ ≤ m * (v * ((1 + ‖w‖) / (1 - ‖w‖))) ^ 3 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hGn 3) (Nat.cast_nonneg m)

/-- **The finite mesh** (`opt:eq:finite-mesh`): for `m ≥ 8an` slots of step `v = a/m` and
weights with `∑ |λ_j| ≤ A`,
`‖∑_j λ_j Ces_j(F_m) - ∑_j λ_j Ces_j(e^{-aΩ})‖ ≤ 128 A a³ n⁴ / m²`. -/
theorem finite_mesh [FiniteDimensional ℂ P] {q : ℝ} (hq : 0 < q) {U : W →L[ℂ] W}
    (hU : OracleCircuit.IsUnitary U) {a : ℝ} (ha : 0 ≤ a) {m n : ℕ} (hn : 1 ≤ n) (hm0 : 0 < m)
    (hm : 8 * a * n ≤ m) {lam : ℕ → ℝ} {A : ℝ} (hlam : ∑ j ∈ Icc 1 n, |lam j| ≤ A) :
    ‖∑ j ∈ Icc 1 n, (lam j : ℂ) • ces (cascTransfer (K.priv q U) K.E (a / m) m) j -
        ∑ j ∈ Icc 1 n, (lam j : ℂ) • ces (Fop a q (K.Cop U) (K.Dop U)) j‖ ≤
      128 * A * a ^ 3 * n ^ 4 / m ^ 2 := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm0
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set v : ℝ := a / m with hvdef
  have hv : 0 ≤ v := div_nonneg ha hm'.le
  have hav : (m : ℝ) * v = a := by rw [hvdef]; field_simp
  set ρ : ℝ := 1 - 1 / (2 * n) with hρ
  have hρ0 : 0 < ρ := by
    have : 1 / (2 * (n : ℝ)) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    linarith
  have hinv : 0 < 1 / (2 * (n : ℝ)) := by positivity
  have hρ1 : ρ < 1 := by linarith
  have h1ρ : 1 - ρ = 1 / (2 * n) := by rw [hρ]; ring
  set M : ℝ := (1 + ρ) / (1 - ρ) with hMdef
  have hM : M ≤ 4 * n := by
    rw [hMdef, h1ρ, div_le_iff₀ hinv, hρ]
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    field_simp
    nlinarith
  have hM0 : 0 ≤ M := by rw [hMdef]; exact div_nonneg (by linarith) (by linarith)
  have hv4 : v * (4 * n) ≤ 1 / 2 := by
    rw [hvdef, div_mul_eq_mul_div, div_le_iff₀ hm']
    nlinarith
  have hvM : v * M ≤ 1 / 2 := (mul_le_mul_of_nonneg_left hM hv).trans hv4
  set B : ℝ := m * (v * M) ^ 3 with hB
  have hB0 : 0 ≤ B := by positivity
  -- the error function and its Cauchy bounds
  set g : ℂ → P →L[ℂ] P := fun w =>
    cascTransfer (K.priv q U) K.E v m w - Fop a q (K.Cop U) (K.Dop U) w with hg
  have hFa : AnalyticAt ℂ (cascTransfer (K.priv q U) K.E v m) 0 := by
    unfold cascTransfer; exact analyticAt_transfer _ _ _ _
  have hGa : AnalyticAt ℂ (Fop a q (K.Cop U) (K.Dop U)) 0 := analyticAt_Fop hq (by simp)
  have hgd : DifferentiableOn ℂ g (Metric.ball 0 1) :=
    (differentiableOn_cascTransfer (K.priv_adjoint_comp hU) K.E_isometry hv m).sub
      (differentiableOn_Fop hq _ _)
  have hcircle : ∀ z : ℂ, ‖z‖ = ρ → ‖g z‖ ≤ B := by
    intro z hz
    have hz1 : ‖z‖ < 1 := by rw [hz]; exact hρ1
    have h := K.norm_cascTransfer_sub_Fop_le hq hU hv m hz1 (by rw [hz]; exact hvM)
    rw [hav, hz] at h
    exact h
  have hcoeff : ∀ k, ‖coeff g k‖ ≤ B / ρ ^ k := fun k =>
    norm_coeff_le_of_ball hρ0 hρ1 hgd hcircle k
  -- the clock functionals
  have hces : ∀ j, j ≤ n → ‖ces (cascTransfer (K.priv q U) K.E v m) j -
      ces (Fop a q (K.Cop U) (K.Dop U)) j‖ ≤ n * (2 * B) := by
    intro j hj
    rw [← ces_sub hFa hGa]
    change ‖ces g j‖ ≤ _
    rw [ces]
    calc ‖∑ k ∈ range j, ((1 : ℂ) - (k : ℂ) / (j : ℂ)) • coeff g k‖ ≤
        ∑ k ∈ range j, ‖((1 : ℂ) - (k : ℂ) / (j : ℂ)) • coeff g k‖ := norm_sum_le _ _
      _ ≤ ∑ _k ∈ range j, 2 * B := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hkj := Finset.mem_range.mp hk
          have hj0 : (0 : ℝ) < j := by exact_mod_cast (Nat.zero_lt_of_lt hkj)
          have hc : ‖(1 : ℂ) - (k : ℂ) / (j : ℂ)‖ ≤ 1 := by
            rw [show (1 : ℂ) - (k : ℂ) / (j : ℂ) = ((1 - (k : ℝ) / j : ℝ) : ℂ) by push_cast; ring,
              Complex.norm_real, Real.norm_eq_abs]
            have hkj' : (k : ℝ) < j := by exact_mod_cast hkj
            have h1 : 0 ≤ 1 - (k : ℝ) / j := by
              rw [sub_nonneg, div_le_one hj0]; linarith
            rw [abs_of_nonneg h1]
            have : 0 ≤ (k : ℝ) / j := by positivity
            linarith
          have hρk : (1 / 2 : ℝ) ≤ ρ ^ k := half_le_rho_pow hn (by omega)
          rw [norm_smul]
          calc ‖(1 : ℂ) - (k : ℂ) / (j : ℂ)‖ * ‖coeff g k‖ ≤ 1 * (B / ρ ^ k) :=
                mul_le_mul hc (hcoeff k) (norm_nonneg _) zero_le_one
            _ ≤ 2 * B := by
                rw [one_mul, div_le_iff₀ (by positivity)]
                nlinarith
      _ = j * (2 * B) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ n * (2 * B) := by
          apply mul_le_mul_of_nonneg_right (by exact_mod_cast hj) (by positivity)
  -- the weighted sum
  have hA0 : 0 ≤ A := (Finset.sum_nonneg fun j _ => abs_nonneg (lam j)).trans hlam
  rw [← Finset.sum_sub_distrib]
  calc ‖∑ j ∈ Icc 1 n, ((lam j : ℂ) • ces (cascTransfer (K.priv q U) K.E v m) j -
        (lam j : ℂ) • ces (Fop a q (K.Cop U) (K.Dop U)) j)‖ ≤
      ∑ j ∈ Icc 1 n, |lam j| * (n * (2 * B)) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj => ?_)
        rw [← smul_sub, norm_smul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hces j (Finset.mem_Icc.mp hj).2) (abs_nonneg _)
    _ = (∑ j ∈ Icc 1 n, |lam j|) * (n * (2 * B)) := by rw [Finset.sum_mul]
    _ ≤ A * (n * (2 * B)) := mul_le_mul_of_nonneg_right hlam (by positivity)
    _ ≤ A * (n * (2 * (m * (v * (4 * n)) ^ 3))) := by
        apply mul_le_mul_of_nonneg_left _ hA0
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact pow_le_pow_left₀ (mul_nonneg hv hM0) (mul_le_mul_of_nonneg_left hM hv) 3
    _ = 128 * A * a ^ 3 * n ^ 4 / m ^ 2 := by
        rw [hvdef]; field_simp; ring

end Known

end

end SignedFactorSimulation
