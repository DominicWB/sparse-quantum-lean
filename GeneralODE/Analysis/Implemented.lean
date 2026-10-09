import GeneralODE.Analysis.HistorySolution

/-!
# The implemented Taylor step and source

The history matrix uses the powers `P_k = B₀^{K-k} B_U^k` of two blocks of
one unitary: `B_U ≈ A/α` and `B₀ ≈ I`.  With `τ = α h ≤ 1` the implemented
step is `V = ∑_k τ^k/k! P_k` and the source polynomial `Φ = ∑_k τ^k/(k+1)! P_k`.
We prove that `P₀ = B₀^K` is invertible, and bound

* `‖P₀⁻¹ V - e^{hA}‖ ≤ 3e Kε₀ + e hαδ_U + 3 (Λh)^{K+1}/(K+1)!`,
* `‖h P₀⁻¹ Φ P₀⁻¹ b - ∫₀ʰ e^{uA} b du‖ ≤ (7e Kε₀ + e hαδ_U + 3 (Λh)^{K+1}/(K+1)!) h ‖b‖`,

where `δ_U = ‖B_U - A/α‖`, `ε₀ = ‖B₀ - I‖`.  Only norms of the blocks enter;
no closeness of the underlying unitaries is used.
-/

namespace SparseHamiltonian.GeneralODE.Implemented

noncomputable section
open NormedSpace ContinuousLinearMap History ExpBounds ODEConstantForcing
open scoped BigOperators Nat

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [Nontrivial V]

local notation "Op" => V →L[ℂ] V

/-- A linear combination of `K + 1` operators with real coefficients. -/
def poly {K : ℕ} (c : ℕ → ℝ) (P : Fin (K + 1) → Op) : Op :=
  ∑ k : Fin (K + 1), ((c k : ℝ) : ℂ) • P k

/-- Taylor coefficients of the step, `τ^k / k!`. -/
def taylorCoef (τ : ℝ) (k : ℕ) : ℝ := τ ^ k / (k ! : ℝ)

/-- Coefficients of the source polynomial, `τ^k / (k+1)!`. -/
def phiCoef (τ : ℝ) (k : ℕ) : ℝ := τ ^ k / ((k + 1) ! : ℝ)

theorem taylorCoef_nonneg (τ : ℝ) (hτ : 0 ≤ τ) (k : ℕ) : 0 ≤ taylorCoef τ k := by
  unfold taylorCoef; positivity

theorem phiCoef_nonneg (τ : ℝ) (hτ : 0 ≤ τ) (k : ℕ) : 0 ≤ phiCoef τ k := by
  unfold phiCoef; positivity

theorem phiCoef_le_taylorCoef (τ : ℝ) (hτ : 0 ≤ τ) (k : ℕ) : phiCoef τ k ≤ taylorCoef τ k := by
  unfold phiCoef taylorCoef
  apply div_le_div_of_nonneg_left (by positivity) (by exact_mod_cast Nat.factorial_pos k)
  exact_mod_cast Nat.factorial_le (Nat.le_succ k)

theorem sum_taylorCoef_le (τ : ℝ) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) (K : ℕ) :
    ∑ k ∈ Finset.range (K + 1), taylorCoef τ k ≤ Real.exp 1 := by
  calc ∑ k ∈ Finset.range (K + 1), taylorCoef τ k
      ≤ ∑ k ∈ Finset.range (K + 1), (1 : ℝ) ^ k / (k ! : ℝ) := by
        apply Finset.sum_le_sum; intro k _
        unfold taylorCoef
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact pow_le_pow_left₀ hτ hτ1 k
    _ ≤ Real.exp 1 := Real.sum_le_exp_of_nonneg zero_le_one (K + 1)

theorem sum_phiCoef_le (τ : ℝ) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) (K : ℕ) :
    ∑ k ∈ Finset.range (K + 1), phiCoef τ k ≤ Real.exp 1 :=
  (Finset.sum_le_sum (fun k _ => phiCoef_le_taylorCoef τ hτ k)).trans
    (sum_taylorCoef_le τ hτ hτ1 K)

/-- The powers `B₀^{K-k} B_U^k`. -/
def powers (BU B0 : Op) (K : ℕ) (k : Fin (K + 1)) : Op := B0 ^ (K - k.val) * BU ^ k.val

omit [CompleteSpace V] [Nontrivial V] in
theorem norm_smul_sub_smul (r : ℂ) (x y : Op) : ‖r • x - r • y‖ = ‖r‖ * ‖x - y‖ := by
  rw [show r • x - r • y = r • (x - y) from (smul_sub r x y).symm, norm_smul]

omit [CompleteSpace V] in
theorem norm_pow_le_one (B : Op) (hB : ‖B‖ ≤ 1) (j : ℕ) : ‖B ^ j‖ ≤ 1 :=
  (norm_pow_le_pow B j).trans (pow_le_one₀ (norm_nonneg _) hB)

omit [CompleteSpace V] in
theorem norm_pow_sub_one_le (B : Op) (hB : ‖B‖ ≤ 1) :
    ∀ j : ℕ, ‖B ^ j - 1‖ ≤ j * ‖B - 1‖
  | 0 => by simp
  | j + 1 => by
      have h : B ^ (j + 1) - 1 = B ^ j * (B - 1) + (B ^ j - 1) := by
        rw [pow_succ, mul_sub, mul_one]; abel
      rw [h]
      calc ‖B ^ j * (B - 1) + (B ^ j - 1)‖ ≤ ‖B ^ j‖ * ‖B - 1‖ + ‖B ^ j - 1‖ :=
            (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) le_rfl)
        _ ≤ 1 * ‖B - 1‖ + j * ‖B - 1‖ :=
            add_le_add (mul_le_mul_of_nonneg_right (norm_pow_le_one B hB j) (norm_nonneg _))
              (norm_pow_sub_one_le B hB j)
        _ = ((j + 1 : ℕ) : ℝ) * ‖B - 1‖ := by push_cast; ring

omit [CompleteSpace V] in
theorem norm_powers_le (BU B0 : Op) (hU : ‖BU‖ ≤ 1) (h0 : ‖B0‖ ≤ 1) (K : ℕ) (k : Fin (K + 1)) :
    ‖powers BU B0 K k‖ ≤ 1 :=
  (norm_mul_le _ _).trans (by
    have := mul_le_mul (norm_pow_le_one B0 h0 (K - k.val)) (norm_pow_le_one BU hU k.val)
      (norm_nonneg _) zero_le_one
    linarith)

omit [CompleteSpace V] in
theorem norm_powers_sub_le (BU B0 : Op) (hU : ‖BU‖ ≤ 1) (h0 : ‖B0‖ ≤ 1) (K : ℕ)
    (k : Fin (K + 1)) : ‖powers BU B0 K k - BU ^ k.val‖ ≤ K * ‖B0 - 1‖ := by
  have h : powers BU B0 K k - BU ^ k.val = (B0 ^ (K - k.val) - 1) * BU ^ k.val := by
    unfold powers; rw [sub_mul, one_mul]
  rw [h]
  calc ‖(B0 ^ (K - k.val) - 1) * BU ^ k.val‖ ≤ ‖B0 ^ (K - k.val) - 1‖ * ‖BU ^ k.val‖ :=
        norm_mul_le _ _
    _ ≤ ((K - k.val : ℕ) : ℝ) * ‖B0 - 1‖ * 1 :=
        mul_le_mul (norm_pow_sub_one_le B0 h0 _) (norm_pow_le_one BU hU _) (norm_nonneg _)
          (by positivity)
    _ ≤ K * ‖B0 - 1‖ := by
        rw [mul_one]
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        exact_mod_cast Nat.sub_le K k.val

omit [CompleteSpace V] [Nontrivial V] in
theorem powers_zero (BU B0 : Op) (K : ℕ) : powers BU B0 K 0 = B0 ^ K := by
  simp [powers]

omit [CompleteSpace V] in
/-- A polynomial in the powers is close to the same polynomial in `B_U`. -/
theorem norm_poly_sub_le (BU B0 : Op) (hU : ‖BU‖ ≤ 1) (h0 : ‖B0‖ ≤ 1) (K : ℕ)
    (c : ℕ → ℝ) (hc : ∀ k, 0 ≤ c k) :
    ‖poly c (powers BU B0 K) -
        ∑ k ∈ Finset.range (K + 1), ((c k : ℝ) : ℂ) • BU ^ k‖ ≤
      (∑ k ∈ Finset.range (K + 1), c k) * (K * ‖B0 - 1‖) := by
  unfold poly
  rw [← Fin.sum_univ_eq_sum_range (fun k => ((c k : ℝ) : ℂ) • BU ^ k) (K + 1),
    ← Finset.sum_sub_distrib,
    ← Fin.sum_univ_eq_sum_range (fun k => c k) (K + 1), Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun k _ => ?_))
  rw [norm_smul_sub_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hc k)]
  exact mul_le_mul_of_nonneg_left (norm_powers_sub_le BU B0 hU h0 K k) (hc k)

omit [CompleteSpace V] in
theorem norm_poly_le (BU B0 : Op) (hU : ‖BU‖ ≤ 1) (h0 : ‖B0‖ ≤ 1) (K : ℕ)
    (c : ℕ → ℝ) (hc : ∀ k, 0 ≤ c k) :
    ‖poly c (powers BU B0 K)‖ ≤ ∑ k ∈ Finset.range (K + 1), c k := by
  unfold poly
  rw [← Fin.sum_univ_eq_sum_range (fun k => c k) (K + 1)]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun k _ => ?_))
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hc k)]
  exact (mul_le_mul_of_nonneg_left (norm_powers_le BU B0 hU h0 K k) (hc k)).trans (by simp)

/-- An explicit inverse of an operator close to the identity. -/
theorem exists_inverse (P0 : Op) (h : ‖P0 - 1‖ ≤ 1 / 2) :
    ∃ Q0 : Op, Q0 * P0 = 1 ∧ P0 * Q0 = 1 ∧ ‖Q0 - 1‖ ≤ 2 * ‖P0 - 1‖ ∧ ‖Q0‖ ≤ 2 := by
  have ht : ‖1 - P0‖ < 1 := by rw [norm_sub_rev]; linarith
  let u := Units.oneSub (1 - P0) ht
  have hu : (u : Op) = P0 := by simp [u, Units.val_oneSub]
  set Q : Op := (↑u⁻¹ : Op) with hQdef
  have hQP : Q * P0 = 1 := by rw [hQdef, ← hu]; exact u.inv_mul
  have hPQ : P0 * Q = 1 := by rw [hQdef, ← hu]; exact u.mul_inv
  have hQ : Q - 1 = Q * (1 - P0) := by rw [mul_sub, mul_one, hQP]
  have hQn : ‖Q‖ ≤ 1 + ‖Q - 1‖ := by
    calc ‖Q‖ = ‖1 + (Q - 1)‖ := by rw [add_sub_cancel]
      _ ≤ ‖(1 : Op)‖ + ‖Q - 1‖ := norm_add_le _ _
      _ = 1 + ‖Q - 1‖ := by rw [norm_one]
  have hb : ‖Q - 1‖ ≤ (1 + ‖Q - 1‖) * ‖P0 - 1‖ := by
    calc ‖Q - 1‖ = ‖Q * (1 - P0)‖ := by rw [hQ]
      _ ≤ ‖Q‖ * ‖1 - P0‖ := norm_mul_le _ _
      _ ≤ (1 + ‖Q - 1‖) * ‖P0 - 1‖ := by
          rw [norm_sub_rev 1 P0]
          exact mul_le_mul_of_nonneg_right hQn (norm_nonneg _)
  have h1 : ‖Q - 1‖ ≤ 2 * ‖P0 - 1‖ := by
    nlinarith [norm_nonneg (Q - 1), norm_nonneg (P0 - 1)]
  refine ⟨Q, hQP, hPQ, h1, ?_⟩
  linarith

omit [CompleteSpace V] in
/-- Termwise comparison of two polynomials with coefficients dominated by `1/k!`. -/
theorem norm_sum_pow_sub_le (y z : Op) (hy : ‖y‖ ≤ 1) (hz : ‖z‖ ≤ 1) (K : ℕ)
    (a : ℕ → ℝ) (ha0 : ∀ k, 0 ≤ a k) (ha : ∀ k, a k ≤ ((k ! : ℝ))⁻¹) :
    ‖∑ k ∈ Finset.range (K + 1), ((a k : ℝ) : ℂ) • y ^ k -
        ∑ k ∈ Finset.range (K + 1), ((a k : ℝ) : ℂ) • z ^ k‖ ≤ ‖y - z‖ * Real.exp 1 := by
  rw [← Finset.sum_sub_distrib, Finset.sum_range_succ']
  simp only [pow_zero, sub_self, add_zero]
  calc ‖∑ j ∈ Finset.range K, (((a (j + 1) : ℝ) : ℂ) • y ^ (j + 1) -
          ((a (j + 1) : ℝ) : ℂ) • z ^ (j + 1))‖
      ≤ ∑ j ∈ Finset.range K, ‖((a (j + 1) : ℝ) : ℂ) • y ^ (j + 1) -
          ((a (j + 1) : ℝ) : ℂ) • z ^ (j + 1)‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range K, ‖y - z‖ * (1 ^ j / (j ! : ℝ)) := by
        apply Finset.sum_le_sum; intro j _
        rw [norm_smul_sub_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ha0 _)]
        have h := norm_pow_sub_pow_le y z 1 hy hz (j + 1)
        rw [one_pow, mul_one] at h
        have hfac : ((j + 1) ! : ℝ) = (j + 1 : ℝ) * (j ! : ℝ) := by
          rw [Nat.factorial_succ]; push_cast; ring
        have hpos : (0 : ℝ) < (j ! : ℝ) := by exact_mod_cast Nat.factorial_pos j
        calc a (j + 1) * ‖y ^ (j + 1) - z ^ (j + 1)‖
            ≤ (((j + 1) ! : ℝ))⁻¹ * (((j + 1 : ℕ) : ℝ) * ‖y - z‖) :=
              mul_le_mul (ha _) h (norm_nonneg _) (by positivity)
          _ = ‖y - z‖ * (1 ^ j / (j ! : ℝ)) := by
              rw [hfac, one_pow]; push_cast; field_simp
    _ = ‖y - z‖ * ∑ j ∈ Finset.range K, 1 ^ j / (j ! : ℝ) := (Finset.mul_sum _ _ _).symm
    _ ≤ ‖y - z‖ * Real.exp 1 :=
        mul_le_mul_of_nonneg_left (Real.sum_le_exp_of_nonneg zero_le_one K) (norm_nonneg _)

omit [CompleteSpace V] [Nontrivial V] in
theorem taylorCoef_scale (α h : ℝ) (BU : Op) (k : ℕ) :
    ((taylorCoef (α * h) k : ℝ) : ℂ) • BU ^ k =
      (((k ! : ℝ))⁻¹ : ℂ) • ((((α * h : ℝ) : ℂ)) • BU) ^ k := by
  rw [smul_pow, smul_smul]
  unfold taylorCoef
  congr 1
  push_cast
  ring

omit [CompleteSpace V] [Nontrivial V] in
theorem phiCoef_scale (α h : ℝ) (BU : Op) (k : ℕ) :
    ((phiCoef (α * h) k : ℝ) : ℂ) • BU ^ k =
      ((((k + 1) ! : ℝ))⁻¹ : ℂ) • ((((α * h : ℝ) : ℂ)) • BU) ^ k := by
  rw [smul_pow, smul_smul]
  unfold phiCoef
  congr 1
  push_cast
  ring

/-- Bounds for the implemented step and source operators. -/
theorem implemented_bounds (A BU B0 : Op) (Λ α δU ε0 h : ℝ) (K : ℕ)
    (hU : ‖BU‖ ≤ 1) (h0 : ‖B0‖ ≤ 1) (hα : 0 < α)
    (hUerr : ‖BU - ((α⁻¹ : ℝ) : ℂ) • A‖ ≤ δU) (h0err : ‖B0 - 1‖ ≤ ε0)
    (hK : K * ε0 ≤ 1 / 2) (hh : 0 ≤ h) (hτ : α * h ≤ 1)
    (hA : ‖A‖ ≤ Λ) (hΛh : Λ * h ≤ 1) :
    ∃ Q0 : Op, Q0 * powers BU B0 K 0 = 1 ∧ powers BU B0 K 0 * Q0 = 1 ∧
      ‖Q0 - 1‖ ≤ 2 * (K * ε0) ∧ ‖Q0‖ ≤ 2 ∧
      ‖poly (phiCoef (α * h)) (powers BU B0 K)‖ ≤ Real.exp 1 ∧
      ‖Q0 * poly (taylorCoef (α * h)) (powers BU B0 K) - exp (h • A)‖ ≤
        3 * Real.exp 1 * (K * ε0) + Real.exp 1 * (h * α * δU) +
          3 * ((Λ * h) ^ (K + 1) / ((K + 1) ! : ℝ)) ∧
      ∀ b : V,
        ‖(h : ℂ) • (Q0 * poly (phiCoef (α * h)) (powers BU B0 K) * Q0) b - response A b h‖ ≤
          (7 * Real.exp 1 * (K * ε0) + Real.exp 1 * (h * α * δU) +
            3 * ((Λ * h) ^ (K + 1) / ((K + 1) ! : ℝ))) * h * ‖b‖ := by
  set e := Real.exp 1 with he
  have he0 : 0 ≤ e := (Real.exp_pos 1).le
  have hε00 : 0 ≤ ε0 := (norm_nonneg _).trans h0err
  have hδ0 : 0 ≤ δU := (norm_nonneg _).trans hUerr
  have hKε0 : 0 ≤ K * ε0 := by positivity
  have hτ0 : 0 ≤ α * h := mul_nonneg hα.le hh
  have hΛ0 : 0 ≤ Λ := (norm_nonneg _).trans hA
  -- invertibility of `P₀ = B₀^K`
  have hP0 : ‖powers BU B0 K 0 - 1‖ ≤ K * ε0 := by
    rw [powers_zero]
    exact (norm_pow_sub_one_le B0 h0 K).trans (mul_le_mul_of_nonneg_left h0err (Nat.cast_nonneg K))
  obtain ⟨Q0, hQP, hPQ, hQ1, hQ2⟩ := exists_inverse (powers BU B0 K 0) (hP0.trans hK)
  have hQ1' : ‖Q0 - 1‖ ≤ 2 * (K * ε0) := hQ1.trans (by linarith)
  -- the step and source polynomials in `B_U`
  set V := poly (taylorCoef (α * h)) (powers BU B0 K) with hV
  set Φ := poly (phiCoef (α * h)) (powers BU B0 K) with hΦ
  have hVn : ‖V‖ ≤ e :=
    (norm_poly_le BU B0 hU h0 K _ (taylorCoef_nonneg _ hτ0)).trans
      (sum_taylorCoef_le _ hτ0 hτ K)
  have hΦn : ‖Φ‖ ≤ e :=
    (norm_poly_le BU B0 hU h0 K _ (phiCoef_nonneg _ hτ0)).trans (sum_phiCoef_le _ hτ0 hτ K)
  -- the two arguments of the Taylor polynomials
  set y : Op := (((α * h : ℝ) : ℂ)) • BU with hy
  set z : Op := (h : ℂ) • A with hz
  have hyn : ‖y‖ ≤ 1 := by
    rw [hy, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hτ0]
    calc α * h * ‖BU‖ ≤ 1 * 1 := mul_le_mul hτ hU (norm_nonneg _) zero_le_one
      _ = 1 := by norm_num
  have hzn : ‖z‖ ≤ Λ * h := by
    rw [hz, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hh, mul_comm]
    exact mul_le_mul_of_nonneg_right hA hh
  have hyz : ‖y - z‖ ≤ h * α * δU := by
    have : y - z = (((h * α : ℝ) : ℂ)) • (BU - ((α⁻¹ : ℝ) : ℂ) • A) := by
      rw [hy, hz, smul_sub, smul_smul]
      congr 1
      · push_cast; ring_nf
      · congr 1
        have hα' : (α : ℂ) ≠ 0 := by exact_mod_cast hα.ne'
        push_cast
        field_simp
    rw [this, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left hUerr (by positivity)
  -- Taylor remainder of the exponential at `hA`
  have hTail : ‖taylorExp K z - exp (h • A)‖ ≤ 3 * ((Λ * h) ^ (K + 1) / ((K + 1) ! : ℝ)) := by
    have hzA : (h : ℝ) • A = z := by rw [hz]; exact (Complex.coe_smul h A).symm
    rw [hzA, norm_sub_rev]
    refine (norm_exp_sub_taylorExp_le z K).trans ?_
    have h1 : ‖z‖ ^ (K + 1) / ((K + 1) ! : ℝ) ≤ (Λ * h) ^ (K + 1) / ((K + 1) ! : ℝ) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact pow_le_pow_left₀ (norm_nonneg _) hzn _
    have h2 : Real.exp ‖z‖ ≤ 3 := by
      have := Real.exp_le_exp.mpr (hzn.trans hΛh)
      linarith [Real.exp_one_lt_d9]
    calc ‖z‖ ^ (K + 1) / ((K + 1) ! : ℝ) * Real.exp ‖z‖
        ≤ (Λ * h) ^ (K + 1) / ((K + 1) ! : ℝ) * 3 :=
          mul_le_mul h1 h2 (Real.exp_pos _).le (by positivity)
      _ = 3 * ((Λ * h) ^ (K + 1) / ((K + 1) ! : ℝ)) := by ring
  -- `V` versus the Taylor polynomial of `hA`
  have hVW : ‖V - taylorExp K y‖ ≤ e * (K * ε0) := by
    have h1 := norm_poly_sub_le BU B0 hU h0 K _ (taylorCoef_nonneg _ hτ0)
    have hW : ∑ k ∈ Finset.range (K + 1), ((taylorCoef (α * h) k : ℝ) : ℂ) • BU ^ k =
        taylorExp K y := by
      unfold taylorExp
      apply Finset.sum_congr rfl
      intro k _
      rw [taylorCoef_scale, hy]
      push_cast
      rfl
    rw [hW] at h1
    refine h1.trans ?_
    exact mul_le_mul (sum_taylorCoef_le _ hτ0 hτ K)
      (mul_le_mul_of_nonneg_left h0err (Nat.cast_nonneg K)) (by positivity) he0
  have hWW : ‖taylorExp K y - taylorExp K z‖ ≤ (h * α * δU) * e := by
    have := norm_taylorExp_sub_le y z 1 hyn (hzn.trans hΛh) K
    exact this.trans (mul_le_mul_of_nonneg_right hyz he0)
  refine ⟨Q0, hQP, hPQ, hQ1', hQ2, hΦn, ?_, ?_⟩
  · -- the step
    have hsplit : Q0 * V - exp (h • A) = (Q0 - 1) * V + (V - taylorExp K y) +
        (taylorExp K y - taylorExp K z) + (taylorExp K z - exp (h • A)) := by noncomm_ring
    rw [hsplit]
    have h1 : ‖(Q0 - 1) * V‖ ≤ 2 * (K * ε0) * e :=
      (norm_mul_le _ _).trans (mul_le_mul hQ1' hVn (norm_nonneg _) (by positivity))
    calc ‖(Q0 - 1) * V + (V - taylorExp K y) + (taylorExp K y - taylorExp K z) +
          (taylorExp K z - exp (h • A))‖
        ≤ ‖(Q0 - 1) * V‖ + ‖V - taylorExp K y‖ + ‖taylorExp K y - taylorExp K z‖ +
            ‖taylorExp K z - exp (h • A)‖ := norm_add₄_le
      _ ≤ 2 * (K * ε0) * e + e * (K * ε0) + (h * α * δU) * e +
            3 * ((Λ * h) ^ (K + 1) / ((K + 1) ! : ℝ)) := by gcongr
      _ = 3 * e * (K * ε0) + e * (h * α * δU) + 3 * ((Λ * h) ^ (K + 1) / ((K + 1) ! : ℝ)) := by
          ring
  · -- the source
    intro b
    -- the source polynomial in `B_U` and in `hA`
    set Ψ : Op := ∑ k ∈ Finset.range (K + 1), ((phiCoef (α * h) k : ℝ) : ℂ) • BU ^ k with hΨ
    set Ψh : Op := ∑ k ∈ Finset.range (K + 1), ((((k + 1) ! : ℝ))⁻¹ : ℂ) • z ^ k with hΨh
    have hΦΨ : ‖Φ - Ψ‖ ≤ e * (K * ε0) := by
      have h1 := norm_poly_sub_le BU B0 hU h0 K _ (phiCoef_nonneg _ hτ0)
      refine h1.trans ?_
      exact mul_le_mul (sum_phiCoef_le _ hτ0 hτ K)
        (mul_le_mul_of_nonneg_left h0err (Nat.cast_nonneg K)) (by positivity) he0
    have hΨΨ : ‖Ψ - Ψh‖ ≤ (h * α * δU) * e := by
      have hΨ' : Ψ = ∑ k ∈ Finset.range (K + 1), ((((((k + 1) ! : ℝ))⁻¹ : ℝ)) : ℂ) • y ^ k := by
        rw [hΨ]
        apply Finset.sum_congr rfl
        intro k _
        rw [phiCoef_scale, hy]
        push_cast
        rfl
      have hΨh' : Ψh = ∑ k ∈ Finset.range (K + 1), ((((((k + 1) ! : ℝ))⁻¹ : ℝ)) : ℂ) • z ^ k := by
        rw [hΨh]
        push_cast
        rfl
      rw [hΨ', hΨh']
      refine (norm_sum_pow_sub_le y z hyn (hzn.trans hΛh) K (fun k => (((k + 1) ! : ℝ))⁻¹)
        (fun k => by positivity) (fun k => ?_)).trans (mul_le_mul_of_nonneg_right hyz he0)
      apply inv_anti₀ (by exact_mod_cast Nat.factorial_pos k)
      exact_mod_cast Nat.factorial_le (Nat.le_succ k)
    have hphi : (h : ℂ) • Ψh = phiTaylor K h A := by
      rw [hΨh, phiTaylor, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [hz, smul_pow, smul_smul, smul_smul]
      congr 1
      push_cast
      ring
    have hresp := norm_response_sub_phiTaylor_le A b h hh K
    have hresp' : ‖phiTaylor K h A b - response A b h‖ ≤
        h * (3 * ((Λ * h) ^ (K + 1) / ((K + 1) ! : ℝ))) * ‖b‖ := by
      rw [norm_sub_rev]
      refine hresp.trans ?_
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      apply mul_le_mul_of_nonneg_left _ hh
      have hAh : ‖A‖ * h ≤ Λ * h := mul_le_mul_of_nonneg_right hA hh
      have h1 : (‖A‖ * h) ^ (K + 1) / ((K + 1) ! : ℝ) ≤ (Λ * h) ^ (K + 1) / ((K + 1) ! : ℝ) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact pow_le_pow_left₀ (by positivity) hAh _
      have h2 : Real.exp (‖A‖ * h) ≤ 3 := by
        have := Real.exp_le_exp.mpr (hAh.trans hΛh)
        linarith [Real.exp_one_lt_d9]
      calc (‖A‖ * h) ^ (K + 1) / ((K + 1) ! : ℝ) * Real.exp (‖A‖ * h)
          ≤ (Λ * h) ^ (K + 1) / ((K + 1) ! : ℝ) * 3 :=
            mul_le_mul h1 h2 (Real.exp_pos _).le (by positivity)
        _ = 3 * ((Λ * h) ^ (K + 1) / ((K + 1) ! : ℝ)) := by ring
    -- split the error
    have hsplit : (h : ℂ) • (Q0 * Φ * Q0) b - response A b h =
        (h : ℂ) • ((Q0 * Φ * Q0 - Φ) b + (Φ - Ψ) b + (Ψ - Ψh) b) +
          (phiTaylor K h A b - response A b h) := by
      rw [← hphi]
      simp only [sub_apply, smul_apply, smul_add, smul_sub]
      abel
    have hQΦQ : ‖Q0 * Φ * Q0 - Φ‖ ≤ 6 * e * (K * ε0) := by
      have hid : Q0 * Φ * Q0 - Φ = (Q0 - 1) * Φ * Q0 + Φ * (Q0 - 1) := by noncomm_ring
      rw [hid]
      calc ‖(Q0 - 1) * Φ * Q0 + Φ * (Q0 - 1)‖ ≤ ‖Q0 - 1‖ * ‖Φ‖ * ‖Q0‖ + ‖Φ‖ * ‖Q0 - 1‖ :=
            (norm_add_le _ _).trans (add_le_add
              ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)))
              (norm_mul_le _ _))
        _ ≤ (2 * (K * ε0)) * e * 2 + e * (2 * (K * ε0)) := by gcongr
        _ = 6 * e * (K * ε0) := by ring
    rw [hsplit]
    have hb0 := norm_nonneg b
    have hinner : ‖(Q0 * Φ * Q0 - Φ) b + (Φ - Ψ) b + (Ψ - Ψh) b‖ ≤
        (6 * e * (K * ε0) + e * (K * ε0) + (h * α * δU) * e) * ‖b‖ := by
      calc ‖(Q0 * Φ * Q0 - Φ) b + (Φ - Ψ) b + (Ψ - Ψh) b‖
          ≤ ‖(Q0 * Φ * Q0 - Φ) b‖ + ‖(Φ - Ψ) b‖ + ‖(Ψ - Ψh) b‖ := norm_add₃_le
        _ ≤ ‖Q0 * Φ * Q0 - Φ‖ * ‖b‖ + ‖Φ - Ψ‖ * ‖b‖ + ‖Ψ - Ψh‖ * ‖b‖ := by
            gcongr <;> exact le_opNorm _ _
        _ ≤ 6 * e * (K * ε0) * ‖b‖ + e * (K * ε0) * ‖b‖ + (h * α * δU) * e * ‖b‖ := by gcongr
        _ = _ := by ring
    calc ‖(h : ℂ) • ((Q0 * Φ * Q0 - Φ) b + (Φ - Ψ) b + (Ψ - Ψh) b) +
          (phiTaylor K h A b - response A b h)‖
        ≤ h * ‖(Q0 * Φ * Q0 - Φ) b + (Φ - Ψ) b + (Ψ - Ψh) b‖ +
            ‖phiTaylor K h A b - response A b h‖ := by
          refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
          rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hh]
      _ ≤ h * ((6 * e * (K * ε0) + e * (K * ε0) + (h * α * δU) * e) * ‖b‖) +
            h * (3 * ((Λ * h) ^ (K + 1) / ((K + 1) ! : ℝ))) * ‖b‖ := by gcongr
      _ = (7 * e * (K * ε0) + e * (h * α * δU) + 3 * ((Λ * h) ^ (K + 1) / ((K + 1) ! : ℝ))) *
            h * ‖b‖ := by ring

omit [CompleteSpace V] [Nontrivial V] in
/-- The implemented one-step source equals `h P₀⁻¹ Φ P₀⁻¹ b` when `μ = T/√m`. -/
theorem stepSource_eq (m : ℕ) (hm : 1 ≤ m) (Φ Q0 : Op) (T : ℝ) (b : V) :
    stepSource m Φ Q0 (T / Real.sqrt m) b = ((T / m : ℝ) : ℂ) • (Q0 * Φ * Q0) b := by
  unfold stepSource coupling
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hs : Real.sqrt m ≠ 0 := (Real.sqrt_pos.mpr hm').ne'
  simp only [map_smul, mul_apply_eq_comp, smul_smul]
  congr 1
  have hsq : Real.sqrt m * Real.sqrt m = m := Real.mul_self_sqrt hm'.le
  push_cast
  field_simp
  rw [← Complex.ofReal_pow, Real.sq_sqrt hm'.le]
  push_cast
  ring

end

end SparseHamiltonian.GeneralODE.Implemented
