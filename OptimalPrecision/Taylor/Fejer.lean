import OptimalPrecision.Taylor.Estimates

/-!
# The uniform clock is a contraction on bounded holomorphic functions

For `f` holomorphic on the open unit disk with `‖f‖ ≤ B` there,

  `‖Ces_j f‖ = ‖∑_{k<j} (1 - k/j) [w^k] f‖ ≤ B`

(`opt:eq:interval-bound`). The proof averages `f(ρ ω^r)` over the `N`-th roots
of unity with the nonnegative Fejér weights `|∑_{a<j} ω^{ra}|² / j`. Their
discrete Fourier coefficients are exactly `1 - k/j` for `k < j` and vanish for
`j ≤ k ≤ N - j`, so the average differs from the radius-`ρ` clock functional
by a geometric tail; letting `N → ∞` and then `ρ → 1` gives the bound.
-/

namespace OptimalPrecision

noncomputable section

open Nat Finset Filter Metric Complex
open scoped Topology Real

/-! ### Roots of unity -/

section Roots

/-- The primitive `N`-th root of unity `exp(2πi/N)`. -/
def rootN (N : ℕ) : ℂ := Complex.exp (2 * π * I / N)

theorem rootN_isPrimitiveRoot {N : ℕ} (hN : N ≠ 0) : IsPrimitiveRoot (rootN N) N :=
  Complex.isPrimitiveRoot_exp N hN

theorem norm_rootN {N : ℕ} (hN : N ≠ 0) : ‖rootN N‖ = 1 :=
  (rootN_isPrimitiveRoot hN).norm'_eq_one hN

theorem rootN_ne_zero {N : ℕ} (hN : N ≠ 0) : rootN N ≠ 0 := by
  intro h
  have := norm_rootN hN
  rw [h, norm_zero] at this
  exact zero_ne_one this

/-- Orthogonality of characters of `ℤ/Nℤ`. -/
theorem sum_rootN_zpow {N : ℕ} (hN : N ≠ 0) (m : ℤ) :
    ∑ r ∈ range N, (rootN N ^ m) ^ r = if (N : ℤ) ∣ m then (N : ℂ) else 0 := by
  have hprim := rootN_isPrimitiveRoot hN
  split_ifs with hdvd
  · have h1 : rootN N ^ m = 1 := (hprim.zpow_eq_one_iff_dvd m).mpr hdvd
    simp [h1]
  · have h1 : rootN N ^ m ≠ 1 := fun h => hdvd ((hprim.zpow_eq_one_iff_dvd m).mp h)
    rw [geom_sum_eq h1]
    have hN' : (rootN N ^ m) ^ N = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hprim.pow_eq_one, one_zpow]
    rw [hN', sub_self, zero_div]

end Roots

/-! ### Discrete Fejér weights -/

section Weights

/-- The Fejér weight `|∑_{a<j} ω^{ra}|² / j` at the `r`-th root, as a complex number. -/
def fejerWeight (N j r : ℕ) : ℂ :=
  ((‖∑ a ∈ range j, rootN N ^ (r * a)‖ ^ 2 / j : ℝ) : ℂ)

theorem fejerWeight_nonneg (N j r : ℕ) : 0 ≤ (‖∑ a ∈ range j, rootN N ^ (r * a)‖ ^ 2 / j : ℝ) := by
  positivity

/-- Expansion of the Fejér weight as a double sum of characters. -/
theorem fejerWeight_eq {N : ℕ} (hN : N ≠ 0) (j r : ℕ) :
    fejerWeight N j r = (j : ℂ)⁻¹ *
      ∑ a ∈ range j, ∑ b ∈ range j, (rootN N ^ ((a : ℤ) - b)) ^ r := by
  have hω := rootN_ne_zero hN
  have hnorm := norm_rootN hN
  unfold fejerWeight
  push_cast
  rw [← Complex.mul_conj', map_sum, Finset.sum_mul_sum, div_eq_inv_mul]
  congr 1
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  have hconj : (starRingEnd ℂ) (rootN N ^ (r * b)) = (rootN N ^ (r * b))⁻¹ := by
    have h1 : Complex.normSq (rootN N ^ (r * b)) = 1 := by
      rw [Complex.normSq_eq_norm_sq, norm_pow, hnorm, one_pow, one_pow]
    rw [Complex.inv_def, h1]
    simp
  rw [hconj, ← zpow_natCast, ← zpow_natCast, ← zpow_neg, ← zpow_add₀ hω, ← zpow_natCast,
    ← zpow_mul]
  congr 1
  push_cast
  ring

/-- The discrete Fourier coefficient `(1/N) ∑_r K(r) ω^{rk}` of the Fejér
weights counts the pairs `(a, b)` with `a - b + k ≡ 0 (mod N)`. -/
theorem fejer_coeff_eq {N : ℕ} (hN : N ≠ 0) (j k : ℕ) :
    (N : ℂ)⁻¹ * ∑ r ∈ range N, fejerWeight N j r * rootN N ^ (r * k) =
      (j : ℂ)⁻¹ * ∑ a ∈ range j, ∑ b ∈ range j,
        if (N : ℤ) ∣ ((a : ℤ) - b + k) then (1 : ℂ) else 0 := by
  have hω := rootN_ne_zero hN
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  have hterm : ∀ r : ℕ, fejerWeight N j r * rootN N ^ (r * k) = (j : ℂ)⁻¹ *
      ∑ a ∈ range j, ∑ b ∈ range j, (rootN N ^ ((a : ℤ) - b + k)) ^ r := by
    intro r
    rw [fejerWeight_eq hN, mul_assoc, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← zpow_natCast, ← zpow_mul, ← zpow_natCast (rootN N) (r * k), ← zpow_add₀ hω,
      ← zpow_natCast, ← zpow_mul]
    congr 1
    push_cast
    ring
  rw [Finset.sum_congr rfl fun r _ => hterm r, ← Finset.mul_sum, Finset.sum_comm]
  have hinner : ∀ a ∈ range j, ∑ r ∈ range N, ∑ b ∈ range j,
      (rootN N ^ ((a : ℤ) - b + k)) ^ r =
      ∑ b ∈ range j, (if (N : ℤ) ∣ ((a : ℤ) - b + k) then (N : ℂ) else 0) := by
    intro a _
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => sum_rootN_zpow hN _
  rw [Finset.sum_congr rfl hinner, ← mul_assoc, mul_comm (N : ℂ)⁻¹, mul_assoc, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  split_ifs <;> simp [hN']

/-- For `k < j ≤ N/2` the count is `j - k`. -/
theorem fejer_count_lt {N j k : ℕ} (hjN : 2 * j ≤ N) (hk : k < j) :
    (∑ a ∈ range j, ∑ b ∈ range j,
      if (N : ℤ) ∣ ((a : ℤ) - b + k) then (1 : ℂ) else 0) = ((j - k : ℕ) : ℂ) := by
  have key : ∀ a ∈ range j, ∀ b ∈ range j,
      ((N : ℤ) ∣ ((a : ℤ) - b + k) ↔ b = a + k) := by
    intro a ha b hb
    simp only [Finset.mem_range] at ha hb
    constructor
    · intro hd
      have h0 : (a : ℤ) - b + k = 0 := by
        apply Int.eq_zero_of_abs_lt_dvd hd
        rw [abs_lt]
        constructor <;> omega
      omega
    · intro h
      subst h
      simp
  have hcount : ∀ a ∈ range j, (∑ b ∈ range j,
      if (N : ℤ) ∣ ((a : ℤ) - b + k) then (1 : ℂ) else 0) = if a + k < j then 1 else 0 := by
    intro a ha
    rw [Finset.sum_congr rfl fun b hb => if_congr (key a ha b hb) rfl rfl]
    rw [Finset.sum_ite_eq']
    simp [Finset.mem_range]
  rw [Finset.sum_congr rfl hcount, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  congr 1
  have : (range j).filter (fun a => a + k < j) = range (j - k) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [this, Finset.card_range]

/-- For `j ≤ k` and `k + j ≤ N` the count vanishes. -/
theorem fejer_count_mid {N j k : ℕ} (hjk : j ≤ k) (hkN : k + j ≤ N) :
    (∑ a ∈ range j, ∑ b ∈ range j,
      if (N : ℤ) ∣ ((a : ℤ) - b + k) then (1 : ℂ) else 0) = 0 := by
  apply Finset.sum_eq_zero
  intro a ha
  apply Finset.sum_eq_zero
  intro b hb
  simp only [Finset.mem_range] at ha hb
  rw [if_neg]
  intro hd
  obtain ⟨c, hc⟩ := hd
  have hpos : 0 < (a : ℤ) - b + k := by omega
  have hlt : (a : ℤ) - b + k < N := by omega
  have hc0 : 0 < c := by
    by_contra h
    push Not at h
    have : (N : ℤ) * c ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) h
    omega
  have : (N : ℤ) ≤ N * c := le_mul_of_one_le_right (by positivity) hc0
  omega

/-- The count never exceeds `j²`. -/
theorem norm_fejer_count_le (N j k : ℕ) :
    ‖(∑ a ∈ range j, ∑ b ∈ range j,
      if (N : ℤ) ∣ ((a : ℤ) - b + k) then (1 : ℂ) else 0)‖ ≤ (j : ℝ) * j := by
  calc _ ≤ ∑ a ∈ range j, ‖∑ b ∈ range j,
          if (N : ℤ) ∣ ((a : ℤ) - b + k) then (1 : ℂ) else 0‖ := norm_sum_le _ _
    _ ≤ ∑ a ∈ range j, ∑ b ∈ range j,
          ‖if (N : ℤ) ∣ ((a : ℤ) - b + k) then (1 : ℂ) else 0‖ :=
        Finset.sum_le_sum fun a _ => norm_sum_le _ _
    _ ≤ ∑ _a ∈ range j, ∑ _b ∈ range j, (1 : ℝ) := by
        refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
        split_ifs <;> simp
    _ = (j : ℝ) * j := by simp

end Weights

/-! ### The contraction -/

section Contraction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- The clock functional at radius `ρ`. -/
def cesAt (f : ℂ → E) (j : ℕ) (ρ : ℝ) : E :=
  ∑ k ∈ range j, (((1 : ℂ) - (k : ℂ) / (j : ℂ)) * (ρ : ℂ) ^ k) • coeff f k

omit [CompleteSpace E] in
theorem cesAt_one (f : ℂ → E) (j : ℕ) : cesAt f j 1 = ces f j := by
  simp [cesAt, ces]

omit [CompleteSpace E] in
theorem continuous_cesAt (f : ℂ → E) (j : ℕ) : Continuous (cesAt f j) := by
  unfold cesAt
  fun_prop

/-- The radius-`ρ` clock functional is bounded by the supremum on the disk. -/
theorem norm_cesAt_le {f : ℂ → E} {B : ℝ} (hf : DifferentiableOn ℂ f (ball 0 1))
    (hB : ∀ w : ℂ, ‖w‖ < 1 → ‖f w‖ ≤ B) (j : ℕ) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    ‖cesAt f j ρ‖ ≤ B := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (by simp))
    simpa [cesAt] using hB0
  -- a larger radius for the Cauchy estimates
  obtain ⟨ρ', hρ'def⟩ : ∃ x : ℝ, x = (1 + ρ) / 2 := ⟨_, rfl⟩
  have hρ'0 : 0 < ρ' := by linarith
  have hρρ' : ρ < ρ' := by linarith
  have hρ'1 : ρ' < 1 := by linarith
  have hcoeff : ∀ k, ‖coeff f k‖ ≤ B / ρ' ^ k := fun k =>
    norm_coeff_le_of_ball hρ'0 hρ'1 hf (fun z hz => hB z (hz ▸ hρ'1)) k
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (by simp))
  obtain ⟨s, hsdef⟩ : ∃ x : ℝ, x = ρ / ρ' := ⟨_, rfl⟩
  have hs0 : 0 ≤ s := by rw [hsdef]; positivity
  have hs1 : s < 1 := by rw [hsdef]; exact (div_lt_one hρ'0).mpr hρρ'
  have hsq0 : 0 ≤ Real.sqrt s := Real.sqrt_nonneg s
  have hsq1 : Real.sqrt s < 1 := by
    rw [Real.sqrt_lt' (by norm_num)]; simpa using hs1
  -- the discrete averages
  have hjpos : (0 : ℝ) < j := by exact_mod_cast hj
  have hj0 : (j : ℂ) ≠ 0 := by exact_mod_cast hj.ne'
  have key : ∀ N : ℕ, 2 * j ≤ N →
      ‖cesAt f j ρ‖ ≤ B + (j : ℝ) * j * B * Real.sqrt s ^ (N - j + 1) /
        (1 - Real.sqrt s) := by
    intro N hN
    have hN0 : N ≠ 0 := by omega
    have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN0
    set w : ℕ → ℂ := fun k => (N : ℂ)⁻¹ * ∑ r ∈ range N, fejerWeight N j r * rootN N ^ (r * k)
      with hwdef
    -- the average and its expansion
    set A : E := ∑ r ∈ range N, ((N : ℂ)⁻¹ * fejerWeight N j r) • f ((ρ : ℂ) * rootN N ^ r)
      with hAdef
    have hpt : ∀ r : ℕ, ‖(ρ : ℂ) * rootN N ^ r‖ < 1 := by
      intro r
      rw [norm_mul, norm_pow, norm_rootN hN0, one_pow, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hρ0]
      exact hρ1
    have hsum : HasSum (fun k => ((ρ : ℂ) ^ k * w k) • coeff f k) A := by
      have h1 : ∀ r ∈ range N, HasSum (fun k => ((N : ℂ)⁻¹ * fejerWeight N j r) •
          (((ρ : ℂ) * rootN N ^ r) ^ k • coeff f k))
          (((N : ℂ)⁻¹ * fejerWeight N j r) • f ((ρ : ℂ) * rootN N ^ r)) :=
        fun r _ => (hasSum_coeff hf (hpt r)).const_smul _
      have h2 := hasSum_sum h1
      convert h2 using 1
      funext k
      simp_rw [smul_smul]
      rw [← Finset.sum_smul]
      congr 1
      simp only [hwdef, Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [mul_pow, ← pow_mul]
      ring
    -- the average is bounded by `B`
    have hAle : ‖A‖ ≤ B := by
      have hw0 : w 0 = 1 := by
        have h := fejer_coeff_eq hN0 j 0
        simp only [hwdef] at h ⊢
        rw [h]
        have hc := fejer_count_lt (N := N) hN hj
        simp only [Nat.cast_zero, add_zero, Nat.sub_zero] at hc
        simp only [Nat.cast_zero, add_zero]
        rw [hc]
        field_simp
      have hweights : ∑ r ∈ range N, ((N : ℝ)⁻¹ *
          (‖∑ a ∈ range j, rootN N ^ (r * a)‖ ^ 2 / j)) = 1 := by
        have h := hw0
        simp only [hwdef, mul_zero, pow_zero, mul_one, fejerWeight] at h
        have h' : ((∑ r ∈ range N, ((N : ℝ)⁻¹ *
            (‖∑ a ∈ range j, rootN N ^ (r * a)‖ ^ 2 / j)) : ℝ) : ℂ) = 1 := by
          rw [← h]; push_cast; rw [Finset.mul_sum]
        exact_mod_cast h'
      calc ‖A‖ ≤ ∑ r ∈ range N, ‖((N : ℂ)⁻¹ * fejerWeight N j r) •
            f ((ρ : ℂ) * rootN N ^ r)‖ := norm_sum_le _ _
        _ ≤ ∑ r ∈ range N, ((N : ℝ)⁻¹ *
            (‖∑ a ∈ range j, rootN N ^ (r * a)‖ ^ 2 / j)) * B := by
          refine Finset.sum_le_sum fun r _ => ?_
          rw [norm_smul]
          have hw : ‖(N : ℂ)⁻¹ * fejerWeight N j r‖ =
              (N : ℝ)⁻¹ * (‖∑ a ∈ range j, rootN N ^ (r * a)‖ ^ 2 / j) := by
            rw [fejerWeight, norm_mul, norm_inv, RCLike.norm_natCast, Complex.norm_real,
              Real.norm_eq_abs, abs_of_nonneg (fejerWeight_nonneg N j r)]
          rw [hw]
          exact mul_le_mul_of_nonneg_left (hB _ (hpt r)) (by positivity)
        _ = B := by rw [← Finset.sum_mul, hweights, one_mul]
    -- split off the first `j` terms
    have hsplit := (hasSum_nat_add_iff' j).mpr hsum
    have hfirst : ∑ k ∈ range j, ((ρ : ℂ) ^ k * w k) • coeff f k = cesAt f j ρ := by
      unfold cesAt
      refine Finset.sum_congr rfl fun k hk => ?_
      have hkj : k < j := Finset.mem_range.mp hk
      have hwk : w k = 1 - (k : ℂ) / j := by
        simp only [hwdef]
        rw [fejer_coeff_eq hN0 j k, fejer_count_lt hN hkj]
        have : ((j - k : ℕ) : ℂ) = (j : ℂ) - k := by push_cast [hkj.le]; ring
        rw [this]
        field_simp
      rw [hwk, mul_comm]
    rw [hfirst] at hsplit
    -- bound the tail
    have htail_le : ∀ k : ℕ, ‖((ρ : ℂ) ^ (k + j) * w (k + j)) • coeff f (k + j)‖ ≤
        ((j : ℝ) * j * B * Real.sqrt s ^ (N - j + 1)) * Real.sqrt s ^ k := by
      intro k
      by_cases hk : k + j + j ≤ N
      · have hw0 : w (k + j) = 0 := by
          simp only [hwdef]
          rw [fejer_coeff_eq hN0 j (k + j), fejer_count_mid (by omega) hk, mul_zero]
        rw [hw0, mul_zero, zero_smul, norm_zero]
        positivity
      · push Not at hk
        have hwle : ‖w (k + j)‖ ≤ (j : ℝ) := by
          simp only [hwdef]
          rw [fejer_coeff_eq hN0 j (k + j), norm_mul, norm_inv, RCLike.norm_natCast]
          have := norm_fejer_count_le N j (k + j)
          calc (j : ℝ)⁻¹ * _ ≤ (j : ℝ)⁻¹ * ((j : ℝ) * j) :=
                mul_le_mul_of_nonneg_left this (by positivity)
            _ = j := by field_simp
        rw [norm_smul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hρ0]
        calc ρ ^ (k + j) * ‖w (k + j)‖ * ‖coeff f (k + j)‖
            ≤ ρ ^ (k + j) * j * (B / ρ' ^ (k + j)) := by
              apply mul_le_mul (mul_le_mul_of_nonneg_left hwle (by positivity)) (hcoeff _)
                (norm_nonneg _) (by positivity)
          _ = (j : ℝ) * B * s ^ (k + j) := by
              have hp : ρ' ^ (k + j) ≠ 0 := pow_ne_zero _ hρ'0.ne'
              rw [hsdef, div_pow]; field_simp
          _ = (j : ℝ) * B * (Real.sqrt s ^ (k + j) * Real.sqrt s ^ (k + j)) := by
              rw [← mul_pow, Real.mul_self_sqrt hs0]
          _ ≤ (j : ℝ) * B * (Real.sqrt s ^ (N - j + 1) * Real.sqrt s ^ k) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              apply mul_le_mul (pow_le_pow_of_le_one hsq0 hsq1.le (by omega))
                (pow_le_pow_of_le_one hsq0 hsq1.le (by omega)) (by positivity) (by positivity)
          _ ≤ ((j : ℝ) * j * B * Real.sqrt s ^ (N - j + 1)) * Real.sqrt s ^ k := by
              have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
              have h0 : 0 ≤ B * (Real.sqrt s ^ (N - j + 1) * Real.sqrt s ^ k) := by positivity
              have hjj : (j : ℝ) ≤ j * j := by nlinarith
              calc (j : ℝ) * B * (Real.sqrt s ^ (N - j + 1) * Real.sqrt s ^ k)
                  = (j : ℝ) * (B * (Real.sqrt s ^ (N - j + 1) * Real.sqrt s ^ k)) := by ring
                _ ≤ ((j : ℝ) * j) * (B * (Real.sqrt s ^ (N - j + 1) * Real.sqrt s ^ k)) :=
                    mul_le_mul_of_nonneg_right hjj h0
                _ = _ := by ring
    have hgeom : HasSum (fun k : ℕ => ((j : ℝ) * j * B * Real.sqrt s ^ (N - j + 1)) *
        Real.sqrt s ^ k) (((j : ℝ) * j * B * Real.sqrt s ^ (N - j + 1)) *
          (1 - Real.sqrt s)⁻¹) :=
      (hasSum_geometric_of_lt_one hsq0 hsq1).mul_left _
    have htail : ‖A - cesAt f j ρ‖ ≤ ((j : ℝ) * j * B * Real.sqrt s ^ (N - j + 1)) *
        (1 - Real.sqrt s)⁻¹ := by
      rw [← hsplit.tsum_eq]
      exact tsum_of_norm_bounded hgeom htail_le
    calc ‖cesAt f j ρ‖ = ‖A - (A - cesAt f j ρ)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖A‖ + ‖A - cesAt f j ρ‖ := norm_sub_le _ _
      _ ≤ B + ((j : ℝ) * j * B * Real.sqrt s ^ (N - j + 1)) * (1 - Real.sqrt s)⁻¹ :=
          add_le_add hAle htail
      _ = B + (j : ℝ) * j * B * Real.sqrt s ^ (N - j + 1) / (1 - Real.sqrt s) := by
          rw [div_eq_mul_inv]
  -- let `N → ∞`
  have hlim : Tendsto (fun N : ℕ => B + (j : ℝ) * j * B * Real.sqrt s ^ (N - j + 1) /
      (1 - Real.sqrt s)) atTop (𝓝 (B + (j : ℝ) * j * B * 0 / (1 - Real.sqrt s))) := by
    apply Tendsto.add tendsto_const_nhds
    apply Tendsto.div_const
    apply Tendsto.const_mul
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one hsq0 hsq1
    exact h.comp (Filter.tendsto_atTop_atTop.mpr fun b => ⟨b + j, fun a ha => by omega⟩)
  simp only [mul_zero, zero_div, add_zero] at hlim
  exact ge_of_tendsto hlim (eventually_atTop.mpr ⟨2 * j, key⟩)

/-- **Fejér contraction of the uniform clock** (`opt:eq:interval-bound`). -/
theorem norm_ces_le {f : ℂ → E} {B : ℝ} (hf : DifferentiableOn ℂ f (ball 0 1))
    (hB : ∀ w : ℂ, ‖w‖ < 1 → ‖f w‖ ≤ B) (j : ℕ) : ‖ces f j‖ ≤ B := by
  rw [← cesAt_one]
  have hcont : Tendsto (fun ρ => ‖cesAt f j ρ‖) (𝓝[<] 1) (𝓝 ‖cesAt f j 1‖) :=
    ((continuous_cesAt f j).norm.tendsto 1).mono_left nhdsWithin_le_nhds
  apply le_of_tendsto hcont
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with ρ hρ
  exact norm_cesAt_le hf hB j hρ.1 hρ.2

end Contraction

end

end OptimalPrecision
