import OptimalPrecision.Tail.Transfer

/-!
# Word expansion of the transfer and the matching jets

At homogeneous degree `m`, `e^{-aRX}` contributes `(-a)^m R^m X^m / m!` with
`X = iqC + q²ξD`. Expanding `X^m` into ordered words without commuting `C` and
`D`, every word with `s` letters `D` carries the scalar `ξ^s`:

  `X(w)^m = ∑_{s ≤ m} ξ(w)^s W_{m,s}`,

where `W_{m,s}` is the sum of the ordered words (`word`). Hence

  `Ces_j(F) = ∑_{m < j} ((-a)^m/m!) ∑_{s ≤ m} Ces_j(V R^m ξ^s) W_{m,s}`

(`ces_Fop`), the clock is a polynomial in a common scaling of `C` and `D`
(`clock_smul`), and the moment identities of Theorem `opt:thm:weights` keep only
the pure `C` words below degree `M` (`opt:eq:matching-jets`).
-/

namespace OptimalPrecision.Tail

noncomputable section

open Complex Metric Finset Nat ContinuousLinearMap
open scoped Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {q : ℝ}

/-! ### Ordered words -/

/-- `W_{m,s}`: the sum of the ordered words of length `m` in the letters `iqC` and
`q²D` containing exactly `s` letters `q²D`. -/
def word (q : ℝ) (C D : H →L[ℂ] H) : ℕ → ℕ → (H →L[ℂ] H)
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | m + 1, 0 => word q C D m 0 * ((I * q) • C)
  | m + 1, s + 1 => word q C D m (s + 1) * ((I * q) • C) + word q C D m s * (((q : ℂ) ^ 2) • D)

omit [CompleteSpace H] in
theorem word_zero_right (C D : H →L[ℂ] H) (m : ℕ) : word q C D m 0 = ((I * q) • C) ^ m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [word, ih, pow_succ]

omit [CompleteSpace H] in
theorem word_eq_zero (C D : H →L[ℂ] H) {m s : ℕ} (h : m < s) : word q C D m s = 0 := by
  induction m generalizing s with
  | zero =>
    obtain ⟨s, rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
    rfl
  | succ m ih =>
    obtain ⟨s, rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
    rw [word, ih (by omega), ih (by omega), zero_mul, zero_mul, add_zero]

omit [CompleteSpace H] in
/-- **Expansion of `X(w)^m` into ordered words.** -/
theorem Xop_pow (C D : H →L[ℂ] H) (w : ℂ) (m : ℕ) :
    Xop q C D w ^ m = ∑ s ∈ range (m + 1), xi w ^ s • word q C D m s := by
  induction m with
  | zero => simp [word]
  | succ m ih =>
    rw [pow_succ, ih, Xop, Finset.sum_mul]
    have hX : ∀ s, (xi w ^ s • word q C D m s) * ((I * q) • C + ((q : ℂ) ^ 2 * xi w) • D) =
        xi w ^ s • (word q C D m s * ((I * q) • C)) +
          xi w ^ (s + 1) • (word q C D m s * (((q : ℂ) ^ 2) • D)) := by
      intro s
      simp only [mul_add, smul_mul_assoc, mul_smul_comm]
      rw [pow_succ]
      module
    simp only [hX, Finset.sum_add_distrib]
    -- right side: split off `s = 0` and reindex
    rw [Finset.sum_range_succ' _ (m + 1)]
    simp only [word, pow_zero, one_smul, smul_add, Finset.sum_add_distrib]
    rw [Finset.sum_range_succ (fun s => xi w ^ (s + 1) • (word q C D m (s + 1) * ((I * q) • C))) m,
      word_eq_zero C D (show m < m + 1 by omega), zero_mul, smul_zero, add_zero]
    rw [Finset.sum_range_succ' (fun s => xi w ^ s • (word q C D m s * ((I * q) • C))) m]
    simp only [pow_zero, one_smul]
    abel

omit [CompleteSpace H] in
/-- Homogeneity of the words under a common scaling of `C` and `D`. -/
theorem word_smul (t : ℂ) (C D : H →L[ℂ] H) (m s : ℕ) :
    word q (t • C) (t • D) m s = t ^ m • word q C D m s := by
  induction m generalizing s with
  | zero => cases s <;> simp [word]
  | succ m ih =>
    cases s with
    | zero =>
      simp only [word, ih, smul_mul_assoc, mul_smul_comm, pow_succ]
      module
    | succ s =>
      simp only [word, ih, smul_mul_assoc, mul_smul_comm, smul_add, pow_succ]
      module

/-! ### Scalar clock functions -/

/-- `V R^m ξ^s` with `V = e^{-aξ}`. -/
def vRx (a q : ℝ) (m s : ℕ) (w : ℂ) : ℂ := vt (a : ℂ) w * Rfun q w ^ m * xi w ^ s

theorem analyticAt_vRx (hq : 0 < q) (a : ℝ) (m s : ℕ) {w : ℂ} (hw : ‖w‖ < 1) :
    AnalyticAt ℂ (vRx a q m s) w :=
  ((analyticAt_vt_of_norm_lt (a : ℂ) hw).mul ((analyticAt_Rfun_of_norm_lt hq hw).pow m)).mul
    ((analyticAt_xi_of_norm_lt hw).pow s)

theorem differentiableOn_vRx (hq : 0 < q) (a : ℝ) (m s : ℕ) :
    DifferentiableOn ℂ (vRx a q m s) (ball 0 1) :=
  fun w hw => (analyticAt_vRx hq a m s (by simpa using hw)).differentiableAt.differentiableWithinAt

/-- `V R^m ξ^s` vanishes to order `m` at the origin. -/
theorem coeff_vRx_eq_zero (hq : 0 < q) (a : ℝ) {m k : ℕ} (s : ℕ) (hk : k < m) :
    coeff (vRx a q m s) k = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hR := (analyticAt_Rfun_of_norm_lt hq (by simp : ‖(0 : ℂ)‖ < 1)).differentiableAt
  obtain ⟨r₁, hr₁, K, hK⟩ := exists_norm_le_mul_of_differentiableAt hR (Rfun_zero q)
  have hV := (analyticAt_vt (a : ℂ)).mul ((analyticAt_xi).pow s)
  obtain ⟨r₂, hr₂, B, hB⟩ := exists_norm_le_of_continuousAt hV.continuousAt
  set ρ := min 1 (min r₁ r₂)
  have hρ : 0 < ρ := lt_min one_pos (lt_min hr₁ hr₂)
  have hdiff : DifferentiableOn ℂ (vRx a q (m + 1) s) (ball 0 ρ) :=
    (differentiableOn_vRx hq a (m + 1) s).mono (ball_subset_ball (min_le_left _ _))
  refine coeff_eq_zero_of_norm_le_pow (C := max B 0 * (max K 0) ^ (m + 1)) hρ hdiff ?_
    (Nat.lt_succ_iff.mp hk)
  intro w hw
  have hw₁ : ‖w‖ < r₁ := lt_of_lt_of_le hw ((min_le_right _ _).trans (min_le_left _ _))
  have hw₂ : ‖w‖ < r₂ := lt_of_lt_of_le hw ((min_le_right _ _).trans (min_le_right _ _))
  have h1 : ‖Rfun q w‖ ≤ max K 0 * ‖w‖ :=
    (hK w hw₁).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  have h2 : ‖vt (a : ℂ) w * xi w ^ s‖ ≤ max B 0 := (hB w hw₂).trans (le_max_left _ _)
  have e : vRx a q (m + 1) s w = (vt (a : ℂ) w * xi w ^ s) * Rfun q w ^ (m + 1) := by
    simp only [vRx]; ring
  rw [e, norm_mul, norm_pow]
  calc ‖vt (a : ℂ) w * xi w ^ s‖ * ‖Rfun q w‖ ^ (m + 1) ≤
      max B 0 * (max K 0 * ‖w‖) ^ (m + 1) :=
        mul_le_mul h2 (pow_le_pow_left₀ (norm_nonneg _) h1 _) (by positivity) (le_max_right _ _)
    _ = max B 0 * max K 0 ^ (m + 1) * ‖w‖ ^ (m + 1) := by ring

theorem ces_vRx_eq_zero (hq : 0 < q) (a : ℝ) {m j : ℕ} (s : ℕ) (hj : j ≤ m) :
    ces (vRx a q m s) j = 0 := by
  unfold ces
  refine Finset.sum_eq_zero fun k hk => ?_
  rw [coeff_vRx_eq_zero hq a s (lt_of_lt_of_le (Finset.mem_range.mp hk) hj), smul_zero]

/-! ### Coefficients of the transfer -/

/-- **Taylor coefficients of the transfer in ordered words.** -/
theorem coeff_Fop (hq : 0 < q) (a : ℝ) (C D : H →L[ℂ] H) (k : ℕ) :
    coeff (Fop a q C D) k = ∑ m ∈ range (k + 1), ∑ s ∈ range (m + 1),
      (((-(a : ℂ)) ^ m / m !) * coeff (vRx a q m s) k) • word q C D m s := by
  have hF : Fop a q C D = fun w =>
      vt (a : ℂ) w • NormedSpace.exp ((-(a : ℂ) * Rfun q w) • Xop q C D w) :=
    funext (Fop_eq a q C D)
  have hY : DifferentiableOn ℂ (fun w => (-(a : ℂ) * Rfun q w) • Xop q C D w) (ball 0 1) :=
    fun w hw => (((analyticAt_const.mul
      (analyticAt_Rfun_of_norm_lt hq (by simpa using hw))).fun_smul
      (analyticAt_Xop (by simpa using hw))).differentiableAt).differentiableWithinAt
  have hV : DifferentiableOn ℂ (vt (a : ℂ)) (ball 0 1) := differentiableOn_vt (a : ℂ)
  have hY0 : (-(a : ℂ) * Rfun q 0) • Xop q C D 0 = 0 := by rw [Rfun_zero, mul_zero, zero_smul]
  rw [hF, coeff_smul_exp one_pos hV hY hY0 k]
  refine Finset.sum_congr rfl fun m _ => ?_
  -- `V Y^m = ∑_s ((-a)^m V R^m ξ^s) W_{m,s}`
  have hfun : (fun w => vt (a : ℂ) w • ((-(a : ℂ) * Rfun q w) • Xop q C D w) ^ m) =
      fun w => ∑ s ∈ range (m + 1), ((-(a : ℂ)) ^ m * vRx a q m s w) • word q C D m s := by
    funext w
    rw [smul_pow, Xop_pow, Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [smul_smul, smul_smul, vRx]
    congr 1
    ring
  have hsc : ∀ s, AnalyticAt ℂ (fun w => (-(a : ℂ)) ^ m * vRx a q m s w) 0 := fun s =>
    analyticAt_const.mul (analyticAt_vRx hq a m s (by simp : ‖(0 : ℂ)‖ < 1))
  have han : ∀ s ∈ range (m + 1),
      AnalyticAt ℂ (fun w => ((-(a : ℂ)) ^ m * vRx a q m s w) • word q C D m s) 0 :=
    fun s _ => (hsc s).smul analyticAt_const
  rw [hfun, coeff_sum _ han, Finset.smul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  have hcm : coeff (fun w => (-(a : ℂ)) ^ m * vRx a q m s w) k =
      (-(a : ℂ)) ^ m * coeff (vRx a q m s) k := by
    simpa only [smul_eq_mul] using coeff_const_smul_field ((-(a : ℂ)) ^ m) (vRx a q m s) k
  rw [coeff_smul_const (hsc s), hcm, smul_smul]
  congr 1
  field_simp

/-- Coefficients below the horizon `j` only involve words of length `< j`. -/
theorem coeff_Fop_of_lt (hq : 0 < q) (a : ℝ) (C D : H →L[ℂ] H) {k j : ℕ} (hk : k < j) :
    coeff (Fop a q C D) k = ∑ m ∈ range j, ∑ s ∈ range (m + 1),
      (((-(a : ℂ)) ^ m / m !) * coeff (vRx a q m s) k) • word q C D m s := by
  rw [coeff_Fop hq a C D k]
  apply Finset.sum_subset
  · intro m hm; simp only [Finset.mem_range] at hm ⊢; omega
  · intro m _ hm
    simp only [Finset.mem_range, not_lt] at hm
    refine Finset.sum_eq_zero fun s _ => ?_
    rw [coeff_vRx_eq_zero hq a s (by omega), mul_zero, zero_smul]

/-- **The uniform clocks of the transfer in ordered words.** -/
theorem ces_Fop (hq : 0 < q) (a : ℝ) (C D : H →L[ℂ] H) (j : ℕ) :
    ces (Fop a q C D) j = ∑ m ∈ range j, ∑ s ∈ range (m + 1),
      (((-(a : ℂ)) ^ m / m !) * ces (vRx a q m s) j) • word q C D m s := by
  unfold ces
  rw [Finset.sum_congr rfl fun k hk => by rw [coeff_Fop_of_lt hq a C D (Finset.mem_range.mp hk)]]
  simp only [Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.mul_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_smul]
  congr 1
  rw [smul_eq_mul]
  ring

/-! ### The clock as a polynomial in the scaling -/

/-- The signed clock `Q(C, D) = ∑_j λ_j Ces_j(F)`. -/
def clock (a q : ℝ) (n : ℕ) (lam : ℕ → ℝ) (C D : H →L[ℂ] H) : H →L[ℂ] H :=
  ∑ j ∈ Icc 1 n, (lam j : ℂ) • ces (Fop a q C D) j

/-- The scalar moments `∑_j λ_j Ces_j(V R^m ξ^s)`. -/
def mom (a q : ℝ) (n : ℕ) (lam : ℕ → ℝ) (m s : ℕ) : ℂ :=
  ∑ j ∈ Icc 1 n, (lam j : ℂ) * ces (vRx a q m s) j

/-- The operator coefficients of the clock polynomial. -/
def clockCoeff (a q : ℝ) (n : ℕ) (lam : ℕ → ℝ) (C D : H →L[ℂ] H) (m : ℕ) : H →L[ℂ] H :=
  ∑ s ∈ range (m + 1), (((-(a : ℂ)) ^ m / m !) * mom a q n lam m s) • word q C D m s

/-- **The clock is a polynomial in a common scaling** `z` of `C` and `D`. -/
theorem clock_smul (hq : 0 < q) (a : ℝ) (n : ℕ) (lam : ℕ → ℝ) (C D : H →L[ℂ] H) (z : ℂ) :
    clock a q n lam (z • C) (z • D) = ∑ m ∈ range n, z ^ m • clockCoeff a q n lam C D m := by
  unfold clock clockCoeff mom
  simp only [ces_Fop hq, word_smul, Finset.smul_sum]
  -- extend every inner range `m < j` to `m < n`
  have hext : ∀ j ∈ Icc 1 n, ∑ m ∈ range j, ∑ s ∈ range (m + 1),
      (lam j : ℂ) • ((((-(a : ℂ)) ^ m / m !) * ces (vRx a q m s) j) • (z ^ m • word q C D m s)) =
      ∑ m ∈ range n, ∑ s ∈ range (m + 1),
      (lam j : ℂ) • ((((-(a : ℂ)) ^ m / m !) * ces (vRx a q m s) j) •
        (z ^ m • word q C D m s)) := by
    intro j hj
    have hjn := (Finset.mem_Icc.mp hj).2
    apply Finset.sum_subset
    · intro m hm; simp only [Finset.mem_range] at hm ⊢; omega
    · intro m _ hm
      simp only [Finset.mem_range, not_lt] at hm
      refine Finset.sum_eq_zero fun s _ => ?_
      rw [ces_vRx_eq_zero hq a s hm, mul_zero, zero_smul, smul_zero]
  rw [Finset.sum_congr rfl hext, Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.mul_sum, Finset.sum_smul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_smul, smul_smul, smul_comm, smul_smul]
  congr 1
  ring

omit [CompleteSpace H] in
/-- **Matching jets** (`opt:eq:matching-jets`): if the moments are `δ_{s0}` at degree
`m`, the `m`-th clock coefficient is `(-iaq C)^m / m!`. -/
theorem clockCoeff_eq (a : ℝ) (n : ℕ) (lam : ℕ → ℝ) (C D : H →L[ℂ] H) {m : ℕ}
    (hmom : ∀ s, s ≤ m → mom a q n lam m s = if s = 0 then 1 else 0) :
    clockCoeff a q n lam C D m = ((m ! : ℂ)⁻¹) • ((-(I * (a * q : ℝ))) • C) ^ m := by
  unfold clockCoeff
  rw [Finset.sum_eq_single 0]
  · rw [hmom 0 (Nat.zero_le m), if_pos rfl, mul_one, word_zero_right, smul_pow, smul_pow]
    simp only [smul_smul]
    congr 1
    push_cast
    ring
  · intro s hs hs0
    rw [hmom s (Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)), if_neg hs0, mul_zero, zero_smul]
  · intro h; simp at h

end

end OptimalPrecision.Tail
