import SparseLowerBounds.LinearSystems.OpenClock

set_option synthInstance.maxHeartbeats 400000

section
/-!
# Helper: clock vectors and the actual conditioning of the open clock

Vector-level facts about `clockShift`, `clockMatrix`, `atClock`, `sectorVec` and
`dilation`, and the lower bound `‖A⁻¹‖ > R/2` of eq. `qlsl:eq:actualconditioning`
for the dilation of the open clock with unitary transitions. Used by
`SparseLowerBounds.LinearSystems.Instance` and `.Decoder`.
-/

namespace SparseLowerBounds.Helpers.InstanceDecoder

noncomputable section
open SparseLowerBounds.LinearSystems
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Pointwise action of the clock shift on a clock-indexed family. -/
theorem clockShift_mulVec_apply (T : ℕ) (L : ℕ → Matrix ι ι ℂ) (g : ℕ → ι → ℂ)
    (p : Fin T × ι) :
    (clockShift T L *ᵥ fun q => g q.1 q.2) p =
      if (p.1 : ℕ) = 0 then 0 else (L ((p.1 : ℕ) - 1) *ᵥ g ((p.1 : ℕ) - 1)) p.2 := by
  simp only [Matrix.mulVec, dotProduct, clockShift, Matrix.of_apply, Fintype.sum_prod_type]
  have h : ∀ s : Fin T, (∑ b : ι, (if (p.1 : ℕ) = s + 1 then L s p.2 b else 0) * g s b) =
      if (p.1 : ℕ) = s + 1 then ∑ b, L s p.2 b * g s b else 0 := by
    intro s; split_ifs <;> simp
  simp only [h]
  split_ifs with hp
  · apply Finset.sum_eq_zero
    intro s _
    rw [if_neg]
    omega
  · rw [Finset.sum_eq_single ⟨(p.1 : ℕ) - 1, by omega⟩]
    · simp only
      rw [if_pos (by omega)]
    · intro s _ hs
      rw [if_neg]
      intro h'
      apply hs
      ext
      simp only
      omega
    · intro h'
      exact absurd (Finset.mem_univ _) h'

omit [Fintype ι] [DecidableEq ι] in
/-- A finite sum of clock states, evaluated pointwise. -/
theorem sum_atClock_apply (T : ℕ) (c : ℕ → ℂ) (φ : ℕ → ι → ℂ) (p : Fin T × ι) :
    (∑ t ∈ Finset.range T, c t • atClock T t (φ t)) p = c p.1 * φ p.1 p.2 := by
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, atClock, smul_eq_mul, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq]
  simp [p.1.isLt]

omit [Fintype ι] [DecidableEq ι] in
theorem sum_atClock_eq (T : ℕ) (c : ℕ → ℂ) (φ : ℕ → ι → ℂ) :
    (∑ t ∈ Finset.range T, c t • atClock T t (φ t)) = fun p => c p.1 * φ p.1 p.2 := by
  funext p
  exact sum_atClock_apply T c φ p

omit [DecidableEq ι] in
/-- The squared norm of a clock-indexed product vector. -/
theorem norm_sq_clockVec (T : ℕ) (c : ℕ → ℂ) (φ : ℕ → ι → ℂ) :
    ‖WithLp.toLp 2 (fun p : Fin T × ι => c p.1 * φ p.1 p.2)‖ ^ 2 =
      ∑ t ∈ Finset.range T, ‖c t‖ ^ 2 * ‖WithLp.toLp 2 (φ t)‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, norm_mul,
    mul_pow, ← Finset.mul_sum]
  exact Fin.sum_univ_eq_sum_range (fun t => ‖c t‖ ^ 2 * ∑ a, ‖φ t a‖ ^ 2) T

omit [DecidableEq ι] in
/-- `‖|t⟩ ⊗ ψ‖ = ‖ψ‖` for `t < T`. -/
theorem norm_atClock (T t : ℕ) (ht : t < T) (ψ : ι → ℂ) :
    ‖WithLp.toLp 2 (atClock T t ψ)‖ = ‖WithLp.toLp 2 ψ‖ := by
  have h : atClock T t ψ = ∑ s ∈ Finset.range T, (if s = t then (1 : ℂ) else 0) • atClock T s ψ := by
    rw [Finset.sum_eq_single t]
    · simp
    · intro s _ hs; simp [hs]
    · intro h; exact absurd (Finset.mem_range.2 ht) h
  rw [h, sum_atClock_eq]
  have h2 := norm_sq_clockVec T (fun s => if s = t then (1 : ℂ) else 0) (fun _ => ψ)
  rw [Finset.sum_eq_single t] at h2
  · simp only [↓reduceIte, norm_one, one_pow, one_mul] at h2
    have := norm_nonneg (WithLp.toLp 2 (fun p : Fin T × ι =>
      (if (p.1 : ℕ) = t then (1 : ℂ) else 0) * ψ p.2))
    have := norm_nonneg (WithLp.toLp 2 ψ)
    nlinarith
  · intro s _ hs; simp [hs]
  · intro h; exact absurd (Finset.mem_range.2 ht) h

section Sector

variable {β : Type*} [Fintype β] [DecidableEq β]

omit [DecidableEq β] in
theorem norm_sq_sectorVec (u v : β → ℂ) :
    ‖WithLp.toLp 2 (sectorVec u v)‖ ^ 2 = ‖WithLp.toLp 2 u‖ ^ 2 + ‖WithLp.toLp 2 v‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, Fin.sum_univ_two,
    sectorVec]
  simp

omit [DecidableEq β] in
theorem norm_sectorVec_zero_left (v : β → ℂ) :
    ‖WithLp.toLp 2 (sectorVec 0 v)‖ = ‖WithLp.toLp 2 v‖ := by
  have h := norm_sq_sectorVec (0 : β → ℂ) v
  have h0 : ‖WithLp.toLp 2 (0 : β → ℂ)‖ = 0 := by simp
  rw [h0] at h
  have := norm_nonneg (WithLp.toLp 2 (sectorVec 0 v))
  have := norm_nonneg (WithLp.toLp 2 v)
  nlinarith

omit [DecidableEq β] in
theorem norm_sectorVec_zero_right (u : β → ℂ) :
    ‖WithLp.toLp 2 (sectorVec u 0)‖ = ‖WithLp.toLp 2 u‖ := by
  have h := norm_sq_sectorVec u (0 : β → ℂ)
  have h0 : ‖WithLp.toLp 2 (0 : β → ℂ)‖ = 0 := by simp
  rw [h0] at h
  have := norm_nonneg (WithLp.toLp 2 (sectorVec u 0))
  have := norm_nonneg (WithLp.toLp 2 u)
  nlinarith

omit [DecidableEq β] in
theorem dilation_mulVec_sectorVec_zero_left (C : Matrix β β ℂ) (w : β → ℂ) :
    dilation C *ᵥ sectorVec 0 w = sectorVec (C *ᵥ w) 0 := by
  funext p
  obtain ⟨i, b⟩ := p
  simp only [Matrix.mulVec, dotProduct, dilation, sectorVec, Matrix.of_apply,
    Fintype.sum_prod_type, Fin.sum_univ_two]
  fin_cases i <;> simp

end Sector

/-! ### Matrices as operators -/

theorem ringInverse_toEuclideanCLM {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : IsUnit A) :
    Ring.inverse (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := n) A) =
      Matrix.toEuclideanCLM (𝕜 := ℂ) (n := n) A⁻¹ := by
  have hU : IsUnit (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := n) A) := hA.map _
  rw [← Ring.inverse_mul_cancel_left _ (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := n) A⁻¹) hU,
    ← map_mul, Matrix.nonsing_inv_eq_ringInverse, Ring.mul_inverse_cancel _ hA, map_one, mul_one]

theorem norm_le_one_of_mem_unitaryGroup {n : Type*} [Fintype n] [DecidableEq n]
    {U : Matrix n n ℂ} (hU : U ∈ Matrix.unitaryGroup n ℂ) : ‖U‖ ≤ 1 := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self U
  have hU' : Uᴴ * U = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff'.mp hU
  rw [hU'] at h
  have h1 : ‖(1 : Matrix n n ℂ)‖ ≤ 1 := by
    rw [Matrix.cstar_norm_def, map_one]
    exact ContinuousLinearMap.norm_id_le
  nlinarith [norm_nonneg U]

/-- If `c ‖X x‖ < ‖x‖` for an invertible `X`, then `c < ‖X⁻¹‖`. -/
theorem lt_norm_ringInverse_of {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (X : E →L[ℂ] E) (hX : IsUnit X) (c : ℝ) (x : E) (h : c * ‖X x‖ < ‖x‖) :
    c < ‖Ring.inverse X‖ := by
  have h1 : Ring.inverse X (X x) = x := by
    rw [← mul_apply_eq_comp, Ring.inverse_mul_cancel _ hX]
    rfl
  have h2 : ‖x‖ ≤ ‖Ring.inverse X‖ * ‖X x‖ := by
    conv_lhs => rw [← h1]
    exact (Ring.inverse X).le_opNorm _
  by_contra hc
  push Not at hc
  nlinarith [norm_nonneg (X x)]

/-! ### The actual conditioning (eq. `qlsl:eq:actualconditioning`) -/

/-- The real inequality: for `R = 2^ρ ≤ 2n`, `n/8 < Σ_{t<2n} (1 - r^{t+1})²`. -/
theorem sum_sq_one_sub_pow_gt {ρ n : ℕ} (hn : 2 ^ ρ ≤ 2 * n) :
    (n : ℝ) / 8 < ∑ t ∈ Finset.range (2 * n), (1 - clockRatio ρ ^ (t + 1)) ^ 2 := by
  set r := clockRatio ρ with hr
  have hr0 : 0 ≤ r := clockRatio_nonneg ρ
  have hr1 : r ≤ 1 := (clockRatio_lt_one ρ).le
  have hR : (2 : ℝ) ^ ρ ≤ 2 * n := by exact_mod_cast hn
  have hRpos : (0 : ℝ) < 2 ^ ρ := by positivity
  have hn1 : 1 ≤ n := by have := Nat.one_le_two_pow (n := ρ); omega
  have hexp : r ≤ Real.exp (-(1 / 2 ^ ρ)) := by
    have := Real.add_one_le_exp (-(1 / (2 : ℝ) ^ ρ))
    simp only [hr, clockRatio]
    linarith
  have hpow : r ^ (n + 1) ≤ Real.exp (-(1 / 2)) := by
    calc r ^ (n + 1) ≤ Real.exp (-(1 / 2 ^ ρ)) ^ (n + 1) := pow_le_pow_left₀ hr0 hexp _
      _ = Real.exp (((n + 1 : ℕ) : ℝ) * (-(1 / 2 ^ ρ))) := (Real.exp_nat_mul _ _).symm
      _ ≤ Real.exp (-(1 / 2)) := by
          apply Real.exp_le_exp.mpr
          have h3 : (1 : ℝ) / 2 ≤ ((n + 1 : ℕ) : ℝ) * (1 / 2 ^ ρ) := by
            rw [mul_one_div, le_div_iff₀ hRpos]
            push_cast
            linarith
          linarith
  have he : Real.exp (-(1 / 2)) ≤ 8 / 13 := by
    have h1 := Real.quadratic_le_exp_of_nonneg (x := 1 / 2) (by norm_num)
    have h2 : Real.exp (-(1 / 2)) * Real.exp (1 / 2) = 1 := by
      rw [← Real.exp_add]; simp
    have h3 := Real.exp_pos (-(1 / 2))
    nlinarith
  have hterm : ∀ t ∈ Finset.Ico n (2 * n), (25 : ℝ) / 169 ≤ (1 - r ^ (t + 1)) ^ 2 := by
    intro t ht
    rw [Finset.mem_Ico] at ht
    have h4 : r ^ (t + 1) ≤ r ^ (n + 1) := pow_le_pow_of_le_one hr0 hr1 (by omega)
    have h5 : 0 ≤ r ^ (t + 1) := pow_nonneg hr0 _
    nlinarith
  calc (n : ℝ) / 8 < ∑ t ∈ Finset.Ico n (2 * n), (25 : ℝ) / 169 := by
        rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, show 2 * n - n = n by omega]
        have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
        nlinarith
    _ ≤ ∑ t ∈ Finset.Ico n (2 * n), (1 - r ^ (t + 1)) ^ 2 := Finset.sum_le_sum hterm
    _ ≤ ∑ t ∈ Finset.range (2 * n), (1 - r ^ (t + 1)) ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro t; simp only [Finset.mem_Ico, Finset.mem_range]; omega
        · intro _ _ _; exact sq_nonneg _

/-- The open clock maps the ramp `w = Σ_t (1 - r^{t+1}) |t⟩ ⊗ ψ_t` to the flat history
`(1-r)/2 Σ_t |t⟩ ⊗ ψ_t`. -/
theorem clockMatrix_mulVec_ramp (T : ℕ) (r : ℝ) (L : ℕ → Matrix ι ι ℂ) (ψ : ι → ℂ) :
    clockMatrix T r L *ᵥ (fun p : Fin T × ι => ((1 - r ^ ((p.1 : ℕ) + 1) : ℝ) : ℂ) *
        walk L ψ p.1 p.2) =
      fun p => (((1 - r) / 2 : ℝ) : ℂ) * walk L ψ p.1 p.2 := by
  funext p
  have hs := clockShift_mulVec_apply T L
    (fun t a => ((1 - r ^ (t + 1) : ℝ) : ℂ) * walk L ψ t a) p
  simp only [clockMatrix, Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec,
    Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at hs ⊢
  rw [hs]
  split_ifs with hp
  · rw [hp]; push_cast; ring
  · obtain ⟨k, hk⟩ : ∃ k, (p.1 : ℕ) = k + 1 := ⟨(p.1 : ℕ) - 1, by omega⟩
    rw [hk, Nat.add_sub_cancel]
    have hw : (L k *ᵥ fun a => ((1 - r ^ (k + 1) : ℝ) : ℂ) * walk L ψ k a) =
        ((1 - r ^ (k + 1) : ℝ) : ℂ) • walk L ψ (k + 1) := by
      rw [show (fun a => ((1 - r ^ (k + 1) : ℝ) : ℂ) * walk L ψ k a) =
        ((1 - r ^ (k + 1) : ℝ) : ℂ) • walk L ψ k from rfl, Matrix.mulVec_smul]
      rfl
    rw [hw, Pi.smul_apply, smul_eq_mul]
    push_cast
    ring

/-- **Eq. `qlsl:eq:actualconditioning`** for the dilation of the open clock with unitary
transitions: `R/2 < ‖A⁻¹‖` once `R = 2^ρ ≤ 2n`. -/
theorem lt_norm_ringInverse_dilation [Nonempty ι] {ρ n : ℕ} (hn : 2 ^ ρ ≤ 2 * n)
    (L : ℕ → Matrix ι ι ℂ) (hL : ∀ t, L t ∈ Matrix.unitaryGroup ι ℂ)
    (hU : IsUnit (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2 × Fin (2 * n) × ι)
      (dilation (clockMatrix (2 * n) (clockRatio ρ) L)))) :
    (2 : ℝ) ^ ρ / 2 < ‖Ring.inverse (Matrix.toEuclideanCLM (𝕜 := ℂ)
      (n := Fin 2 × Fin (2 * n) × ι) (dilation (clockMatrix (2 * n) (clockRatio ρ) L)))‖ := by
  classical
  obtain ⟨a₀⟩ := ‹Nonempty ι›
  set r := clockRatio ρ with hr
  set ψ : ι → ℂ := Pi.single a₀ 1 with hψ
  have hψn : ‖WithLp.toLp 2 ψ‖ = 1 := by
    change ‖EuclideanSpace.single a₀ (1 : ℂ)‖ = 1
    simp
  have hwalk : ∀ t, ‖WithLp.toLp 2 (walk L ψ t)‖ = 1 := fun t => by
    rw [norm_walk hL ψ t, hψn]
  set w : Fin (2 * n) × ι → ℂ := fun p => ((1 - r ^ ((p.1 : ℕ) + 1) : ℝ) : ℂ) * walk L ψ p.1 p.2
    with hw
  set x : EuclideanSpace ℂ (Fin 2 × Fin (2 * n) × ι) := WithLp.toLp 2 (sectorVec 0 w) with hx
  apply lt_norm_ringInverse_of _ hU _ x
  have hAx : Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2 × Fin (2 * n) × ι)
      (dilation (clockMatrix (2 * n) r L)) x =
      WithLp.toLp 2 (sectorVec (fun p : Fin (2 * n) × ι => (((1 - r) / 2 : ℝ) : ℂ) *
        walk L ψ p.1 p.2) 0) := by
    rw [hx, Matrix.toEuclideanCLM_toLp, dilation_mulVec_sectorVec_zero_left, hw,
      clockMatrix_mulVec_ramp]
  rw [hAx, hx, norm_sectorVec_zero_right, norm_sectorVec_zero_left]
  have h1 := norm_sq_clockVec (2 * n) (fun t => (((1 - r) / 2 : ℝ) : ℂ)) (walk L ψ)
  have h2 := norm_sq_clockVec (2 * n) (fun t => ((1 - r ^ (t + 1) : ℝ) : ℂ)) (walk L ψ)
  simp only [hwalk, one_pow, mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs] at h1 h2
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h1
  set A := ‖WithLp.toLp 2 (fun p : Fin (2 * n) × ι => (((1 - r) / 2 : ℝ) : ℂ) *
    walk L ψ p.1 p.2)‖
  set B := ‖WithLp.toLp 2 (fun p : Fin (2 * n) × ι => ((1 - r ^ ((p.1 : ℕ) + 1) : ℝ) : ℂ) *
    walk L ψ p.1 p.2)‖
  have hgt := sum_sq_one_sub_pow_gt (ρ := ρ) hn
  rw [← hr, ← h2] at hgt
  have hRr : (2 : ℝ) ^ ρ * (1 - r) = 1 := by
    rw [hr, clockRatio]; field_simp; ring
  have hA0 : 0 ≤ A := norm_nonneg _
  have hB0 : 0 ≤ B := norm_nonneg _
  have hsq : (2 ^ ρ / 2 * A) ^ 2 < B ^ 2 := by
    have : (2 ^ ρ / 2 * A) ^ 2 = (n : ℝ) / 8 := by
      rw [mul_pow, h1]
      have : ((2 : ℝ) ^ ρ / 2) ^ 2 * (((2 * n : ℕ) : ℝ) * ((1 - r) / 2) ^ 2) =
          (2 ^ ρ * (1 - r)) ^ 2 * n / 8 := by push_cast; ring
      rw [this, hRr]; ring
    rw [this]; exact hgt
  have hpos : 0 ≤ (2 : ℝ) ^ ρ / 2 * A := by positivity
  exact lt_of_pow_lt_pow_left₀ 2 hB0 hsq

/-- `‖A‖ ≥ 1/2` for the dilation of the open clock: the last clock column of `C` is `1/2`. -/
theorem half_le_norm_dilation [Nonempty ι] {T : ℕ} (hT : 0 < T) (r : ℝ)
    (L : ℕ → Matrix ι ι ℂ) :
    (1 : ℝ) / 2 ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2 × Fin T × ι)
      (dilation (clockMatrix T r L))‖ := by
  classical
  obtain ⟨a₀⟩ := ‹Nonempty ι›
  set last : Fin T := ⟨T - 1, by omega⟩
  set j : Fin 2 × Fin T × ι := (1, last, a₀)
  set i₀ : Fin 2 × Fin T × ι := (0, last, a₀)
  set X := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2 × Fin T × ι) (dilation (clockMatrix T r L))
  have hXe : (X (EuclideanSpace.single j (1 : ℂ))) i₀ = 1 / 2 := by
    change (dilation (clockMatrix T r L) *ᵥ (WithLp.ofLp (EuclideanSpace.single j (1 : ℂ)))) i₀ = _
    rw [show WithLp.ofLp (EuclideanSpace.single j (1 : ℂ)) = Pi.single j 1 from rfl,
      Matrix.mulVec_single_one]
    simp only [Matrix.col_apply, dilation, Matrix.of_apply, i₀, j, clockMatrix, clockShift,
      Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply_eq, smul_eq_mul]
    simp
  calc (1 : ℝ) / 2 = ‖(X (EuclideanSpace.single j (1 : ℂ))) i₀‖ := by rw [hXe]; norm_num
    _ ≤ ‖X (EuclideanSpace.single j (1 : ℂ))‖ := PiLp.norm_apply_le _ _
    _ ≤ ‖X‖ * ‖EuclideanSpace.single j (1 : ℂ)‖ := X.le_opNorm _
    _ = ‖X‖ := by simp

end

end SparseLowerBounds.Helpers.InstanceDecoder
end
