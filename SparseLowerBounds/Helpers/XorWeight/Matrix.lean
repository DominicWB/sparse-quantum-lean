import SparseLowerBounds.Query.Adversary

set_option synthInstance.maxHeartbeats 400000

section
/-!
# Matrix facts for `SparseLowerBounds.Query.XorWeight`

Helper module of group xor-weight. On one register `ℂ^m` with the L2 operator
norm: `P = |u⟩⟨u|` (every entry `1/m`), `D_a = 1 - 2|a⟩⟨a|` and the parity
`Z = diag((-1)^b)`. The definitions here are the same terms as `XorWeight.Pu`,
`Adversary.reflect` and `Adversary.parityZ`.
-/

namespace SparseLowerBounds.Helpers.XorWeight

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator

/-- `P_u = |u⟩⟨u|`: every entry is `1/m`. -/
def P (m : ℕ) : Matrix (Fin m) (Fin m) ℂ := Matrix.of fun _ _ => (m : ℂ)⁻¹

/-- `D_a = 1 - 2|a⟩⟨a|`. -/
def D {m : ℕ} (a : Fin m) : Matrix (Fin m) (Fin m) ℂ :=
  Matrix.diagonal fun b => if b = a then -1 else 1

/-- The parity `Z = Σ_b (-1)^b |b⟩⟨b|`. -/
def Z (m : ℕ) : Matrix (Fin m) (Fin m) ℂ := Matrix.diagonal fun b => (-1) ^ (b : ℕ)

/-! ### Generic algebra -/

theorem two_sub_mul_inv {A : Type*} [Ring A] [Algebra ℂ A] (p : A) (hp : p * p = p) :
    ((2 : ℂ) • 1 - p) * ((2 : ℂ)⁻¹ • (1 + p)) = 1 := by
  have h : ((2 : ℂ) • 1 - p) * ((2 : ℂ)⁻¹ • (1 + p)) =
      (2 : ℂ)⁻¹ • ((2 : ℂ) • (1 : A) + (2 : ℂ) • p - p - p * p) := by
    simp only [mul_smul_comm, sub_mul, mul_add, smul_mul_assoc, one_mul, mul_one]
    module
  rw [h, hp]
  module

theorem inv_mul_two_sub {A : Type*} [Ring A] [Algebra ℂ A] (p : A) (hp : p * p = p) :
    ((2 : ℂ)⁻¹ • (1 + p)) * ((2 : ℂ) • 1 - p) = 1 := by
  have h : ((2 : ℂ)⁻¹ • (1 + p)) * ((2 : ℂ) • 1 - p) =
      (2 : ℂ)⁻¹ • ((2 : ℂ) • (1 : A) + (2 : ℂ) • p - p - p * p) := by
    simp only [smul_mul_assoc, mul_sub, add_mul, mul_smul_comm, one_mul, mul_one]
    module
  rw [h, hp]
  module

/-- `(1+P) Z (1+P) (1+P) Z (1+P) = 1 + 3 (P + Z P Z)` when `P² = P`, `Z² = 1`,
`P Z P = 0`. -/
theorem conj_sq_eq {A : Type*} [Ring A] (p z : A) (hp : p * p = p) (hz : z * z = 1)
    (hpzp : p * z * p = 0) :
    (1 + p) * z * (1 + p) * ((1 + p) * z * (1 + p)) =
      1 + (p + z * p * z) + (p + z * p * z) + (p + z * p * z) := by
  have hp' : ∀ x, p * (p * x) = p * x := fun x => by rw [← mul_assoc, hp]
  have hz' : ∀ x, z * (z * x) = x := fun x => by rw [← mul_assoc, hz, one_mul]
  have hpzp1 : p * (z * p) = 0 := by rw [← mul_assoc, hpzp]
  have hpzp' : ∀ x, p * (z * (p * x)) = 0 := fun x => by
    rw [← mul_assoc z, ← mul_assoc, hpzp1, zero_mul]
  simp only [add_mul, mul_add, one_mul, mul_one, mul_assoc, hp, hz, hp', hz', hpzp1, hpzp',
    mul_zero, add_zero]
  abel

theorem idem_eq {A : Type*} [Ring A] (p z : A) (hp : p * p = p) (hz : z * z = 1)
    (hpzp : p * z * p = 0) :
    (p + z * p * z) * (p + z * p * z) = p + z * p * z := by
  have hp' : ∀ x, p * (p * x) = p * x := fun x => by rw [← mul_assoc, hp]
  have hz' : ∀ x, z * (z * x) = x := fun x => by rw [← mul_assoc, hz, one_mul]
  have hpzp1 : p * (z * p) = 0 := by rw [← mul_assoc, hpzp]
  have hpzp' : ∀ x, p * (z * (p * x)) = 0 := fun x => by
    rw [← mul_assoc z, ← mul_assoc, hpzp1, zero_mul]
  simp only [add_mul, mul_add, mul_assoc, hp, hp', hz', hpzp1, hpzp', mul_zero, add_zero,
    zero_add]

/-! ### Concrete facts -/

theorem P_mul_P (m : ℕ) : P m * P m = P m := by
  ext i j
  have hm : (m : ℂ) ≠ 0 := by exact_mod_cast (Fin.pos i).ne'
  simp only [P, Matrix.mul_apply, Matrix.of_apply, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp

theorem star_P (m : ℕ) : star (P m) = P m := by
  ext i j
  simp [P, Matrix.star_apply]

theorem isStarProjection_P (m : ℕ) : IsStarProjection (P m) := ⟨P_mul_P m, star_P m⟩

theorem norm_P_le (m : ℕ) : ‖P m‖ ≤ 1 := IsStarProjection.norm_le _ (isStarProjection_P m)

theorem norm_one_le (m : ℕ) : ‖(1 : Matrix (Fin m) (Fin m) ℂ)‖ ≤ 1 :=
  IsStarProjection.norm_le _ (IsStarProjection.one _)

theorem P_mulVec_one (m : ℕ) : P m *ᵥ (fun _ => 1) = fun _ => 1 := by
  funext i
  have hm : (m : ℂ) ≠ 0 := by exact_mod_cast (Fin.pos i).ne'
  simp only [P, Matrix.mulVec, dotProduct, Matrix.of_apply, mul_one, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

theorem norm_wInv_le (m : ℕ) : ‖(2 : ℂ)⁻¹ • (1 + P m)‖ ≤ 1 := by
  calc ‖(2 : ℂ)⁻¹ • (1 + P m)‖ ≤ ‖(2 : ℂ)⁻¹‖ * ‖1 + P m‖ := norm_smul_le _ _
    _ ≤ ‖(2 : ℂ)⁻¹‖ * (1 + 1) := by
        gcongr
        exact (norm_add_le _ _).trans (add_le_add (norm_one_le m) (norm_P_le m))
    _ = 1 := by norm_num

theorem norm_D_le {m : ℕ} (a : Fin m) : ‖D a‖ ≤ 1 := by
  rw [D, Matrix.l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => ?_
  split_ifs <;> simp

theorem norm_Z_le (m : ℕ) : ‖Z m‖ ≤ 1 := by
  rw [Z, Matrix.l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => ?_
  simp

/-- An L2 operator-norm bound from a coordinate bound. -/
theorem norm_le_of_sum_sq {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ x : Fin m → ℂ, ∑ i, ‖(A *ᵥ x) i‖ ^ 2 ≤ c ^ 2 * ∑ i, ‖x i‖ ^ 2) : ‖A‖ ≤ c := by
  rw [Matrix.cstar_norm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ hc fun x => ?_
  refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp ?_
  rw [EuclideanSpace.norm_sq_eq, mul_pow, EuclideanSpace.norm_sq_eq]
  simpa using h (WithLp.ofLp x)

/-- `‖[P, D_a]‖ ≤ 2/√m`. -/
theorem norm_commutator_le {m : ℕ} (a : Fin m) :
    ‖P m * D a - D a * P m‖ ≤ 2 / Real.sqrt m := by
  have hm : 0 < m := Fin.pos a
  have hN : (0 : ℝ) < m := by exact_mod_cast hm
  refine norm_le_of_sum_sq _ (by positivity) fun x => ?_
  set y : Fin m → ℂ := fun j => if j = a then 0 else x j with hy
  have hPv : ∀ (v : Fin m → ℂ) i, (P m *ᵥ v) i = (m : ℂ)⁻¹ * ∑ j, v j := by
    intro v i
    simp only [P, Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.mul_sum]
  have hDv : ∀ (v : Fin m → ℂ), D a *ᵥ v = fun i => (if i = a then -1 else 1) * v i := by
    intro v
    funext i
    rw [D, Matrix.mulVec_diagonal]
  have hentry : ∀ i, ((P m * D a - D a * P m) *ᵥ x) i =
      if i = a then 2 * (m : ℂ)⁻¹ * ∑ j, y j else -(2 * (m : ℂ)⁻¹ * x a) := by
    intro i
    rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Pi.sub_apply,
      hDv, hDv]
    simp only [hPv]
    split_ifs with hi
    · have hS : ∑ j, (if j = a then -1 else 1) * x j + ∑ j, x j = 2 * ∑ j, y j := by
        rw [← Finset.sum_add_distrib, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases hj : j = a
        · simp [hj, hy]
        · simp [hj, hy]
          ring
      linear_combination (m : ℂ)⁻¹ * hS
    · have hS : ∑ j, (if j = a then -1 else 1) * x j - ∑ j, x j = -2 * x a := by
        rw [← Finset.sum_sub_distrib, Finset.sum_eq_single a]
        · simp
          ring
        · intro j _ hj
          simp [hj]
        · simp
      linear_combination (m : ℂ)⁻¹ * hS
  have hnorm : ∀ z : ℂ, ‖2 * (m : ℂ)⁻¹ * z‖ = 2 / m * ‖z‖ := by
    intro z
    rw [norm_mul, norm_mul, norm_inv]
    simp [div_eq_mul_inv]
  have hcs : ‖∑ j, y j‖ ^ 2 ≤ m * ∑ j, ‖y j‖ ^ 2 := by
    calc ‖∑ j, y j‖ ^ 2 ≤ (∑ j, ‖y j‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
      _ ≤ (Finset.univ.card : ℝ) * ∑ j, ‖y j‖ ^ 2 := sq_sum_le_card_mul_sum_sq
      _ = m * ∑ j, ‖y j‖ ^ 2 := by simp
  have hsplit : ∑ j, ‖x j‖ ^ 2 = ∑ j, ‖y j‖ ^ 2 + ‖x a‖ ^ 2 := by
    have : ∀ j, ‖x j‖ ^ 2 = ‖y j‖ ^ 2 + if j = a then ‖x a‖ ^ 2 else 0 := by
      intro j
      by_cases hj : j = a
      · subst hj; simp [hy]
      · simp [hy, hj]
    rw [Finset.sum_congr rfl fun j _ => this j, Finset.sum_add_distrib, Finset.sum_ite_eq']
    simp only [Finset.mem_univ, if_true]
  calc ∑ i, ‖((P m * D a - D a * P m) *ᵥ x) i‖ ^ 2
      = ∑ i, (if i = a then (2 / m * ‖∑ j, y j‖) ^ 2 else (2 / m * ‖x a‖) ^ 2) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hentry]
        split_ifs <;> simp only [norm_neg, hnorm]
    _ ≤ ∑ i, ((if i = a then (2 / m * ‖∑ j, y j‖) ^ 2 else 0) + (2 / m * ‖x a‖) ^ 2) := by
        refine Finset.sum_le_sum fun i _ => ?_
        split_ifs
        · linarith [sq_nonneg (2 / (m : ℝ) * ‖x a‖)]
        · simp
    _ = (2 / m * ‖∑ j, y j‖) ^ 2 + m * (2 / m * ‖x a‖) ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
        simp
    _ ≤ (2 / m) ^ 2 * (m * ∑ j, ‖y j‖ ^ 2) + m * (2 / m * ‖x a‖) ^ 2 := by
        rw [mul_pow]
        gcongr
    _ = (2 / Real.sqrt m) ^ 2 * (∑ j, ‖y j‖ ^ 2 + ‖x a‖ ^ 2) := by
        rw [div_pow, div_pow, Real.sq_sqrt hN.le]
        field_simp
    _ = (2 / Real.sqrt m) ^ 2 * ∑ j, ‖x j‖ ^ 2 := by rw [hsplit]

theorem Z_mul_Z (m : ℕ) : Z m * Z m = 1 := by
  rw [Z, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext b
  rw [← mul_pow]
  simp

theorem star_Z (m : ℕ) : star (Z m) = Z m := by
  rw [Z, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
  congr 1
  funext b
  simp

theorem sum_neg_one_pow {m : ℕ} (hm : Even m) : ∑ k : Fin m, (-1 : ℂ) ^ (k : ℕ) = 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun k => (-1 : ℂ) ^ k) m]
  obtain ⟨r, rfl⟩ := hm
  induction r with
  | zero => simp
  | succ r ih =>
    rw [show r + 1 + (r + 1) = r + r + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, pow_succ]
    ring

theorem P_Z_P {m : ℕ} (hm : Even m) : P m * Z m * P m = 0 := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [Z, P, Matrix.mul_diagonal, Matrix.of_apply, Matrix.zero_apply]
  rw [← Finset.sum_mul, ← Finset.mul_sum, sum_neg_one_pow hm]
  simp

/-- **Eq. `qlsl:eq:paritynorm`**: `‖w⁻¹ Z w⁻¹‖ ≤ 1/2` for even `m`, with
`w⁻¹ = (1 + P)/2`. -/
theorem norm_conj_Z_le {m : ℕ} (hm : Even m) :
    ‖(2 : ℂ)⁻¹ • (1 + P m) * Z m * ((2 : ℂ)⁻¹ • (1 + P m))‖ ≤ 1 / 2 := by
  set N := (2 : ℂ)⁻¹ • (1 + P m) * Z m * ((2 : ℂ)⁻¹ • (1 + P m)) with hNdef
  set R := P m + Z m * P m * Z m with hR
  have hstarA : star ((2 : ℂ)⁻¹ • (1 + P m)) = (2 : ℂ)⁻¹ • (1 + P m) := by
    rw [star_smul, star_add, star_one, star_P]
    congr 1
    simp
  have hNsa : star N = N := by
    rw [hNdef, star_mul, star_mul, hstarA, star_Z, mul_assoc]
  have hNN : N * N = ((2 : ℂ)⁻¹ * (2 : ℂ)⁻¹ * ((2 : ℂ)⁻¹ * (2 : ℂ)⁻¹)) • (1 + R + R + R) := by
    have h1 : N = ((2 : ℂ)⁻¹ * (2 : ℂ)⁻¹) • ((1 + P m) * Z m * (1 + P m)) := by
      rw [hNdef]
      simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
    rw [h1]
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
    rw [hR,
      conj_sq_eq _ _ (P_mul_P m) (Z_mul_Z m) (P_Z_P hm)]
  have hRp : IsStarProjection R := by
    refine ⟨idem_eq _ _ (P_mul_P m) (Z_mul_Z m) (P_Z_P hm), ?_⟩
    show star R = R
    rw [hR, star_add, star_mul, star_mul, star_Z, star_P, mul_assoc]
  have hRn : ‖R‖ ≤ 1 := IsStarProjection.norm_le _ hRp
  have hsum : ‖1 + R + R + R‖ ≤ 4 := by
    calc ‖1 + R + R + R‖ ≤ ‖1 + R + R‖ + ‖R‖ := norm_add_le _ _
      _ ≤ ‖1 + R‖ + ‖R‖ + ‖R‖ := by gcongr; exact norm_add_le _ _
      _ ≤ ‖(1 : Matrix (Fin m) (Fin m) ℂ)‖ + ‖R‖ + ‖R‖ + ‖R‖ := by
          gcongr; exact norm_add_le _ _
      _ ≤ 4 := by linarith [norm_one_le m]
  have hsq : ‖N‖ * ‖N‖ ≤ 1 / 4 := by
    rw [← CStarRing.norm_star_mul_self, hNsa, hNN]
    calc _ ≤ ‖((2 : ℂ)⁻¹ * (2 : ℂ)⁻¹ * ((2 : ℂ)⁻¹ * (2 : ℂ)⁻¹))‖ * ‖1 + R + R + R‖ :=
          norm_smul_le _ _
      _ ≤ ‖((2 : ℂ)⁻¹ * (2 : ℂ)⁻¹ * ((2 : ℂ)⁻¹ * (2 : ℂ)⁻¹))‖ * 4 := by gcongr
      _ = 1 / 4 := by norm_num
  nlinarith [norm_nonneg N]

end

end SparseLowerBounds.Helpers.XorWeight
end
