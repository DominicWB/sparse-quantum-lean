import SparseLowerBounds.Query.XorWeight

set_option synthInstance.maxHeartbeats 400000

section
/-!
# Projector algebra for `SparseLowerBounds.Query.SearchWeight`

Helper module of group search-weight. On one register `ℂ^m`, with
`P = P_u` (`Helpers.XorWeight.P`, every entry `1/m`) and the parity
`Z = diag((-1)^b)` (`Helpers.XorWeight.Z`): `V = Z P Z = P_v` (entries
`(-1)^{a+b}/m`), `R = 1 - P - V`, and the weight `W = P + a² V + a R` with
inverse `P + a⁻² V + a⁻¹ R`. The definitions are the same terms as
`SearchWeight.Pv`, `SearchWeight.Rest`, `SearchWeight.w` and
`SearchWeight.wInv`. Evenness of `m` gives `P Z P = 0`, hence `P V = V P = 0`.
-/

namespace SparseLowerBounds.Helpers.SearchWeight

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator

/-- `P_v = |v⟩⟨v|`: entries `(-1)^{a+b}/m`. -/
def V (m : ℕ) : Matrix (Fin m) (Fin m) ℂ :=
  Matrix.of fun a b => (-1 : ℂ) ^ ((a : ℕ) + b) / m

/-- `R = I - P_u - P_v`. -/
def R (m : ℕ) : Matrix (Fin m) (Fin m) ℂ := 1 - XorWeight.P m - V m

/-- The search weight `P_u + a² P_v + a R`. -/
def W (m : ℕ) (a : ℝ) : Matrix (Fin m) (Fin m) ℂ :=
  XorWeight.P m + ((a : ℂ) ^ 2) • V m + (a : ℂ) • R m

/-- The explicit inverse `P_u + a⁻² P_v + a⁻¹ R`. -/
def WInv (m : ℕ) (a : ℝ) : Matrix (Fin m) (Fin m) ℂ :=
  XorWeight.P m + ((a : ℂ) ^ 2)⁻¹ • V m + (a : ℂ)⁻¹ • R m

/-- Three pairwise orthogonal idempotents multiply coefficientwise. -/
theorem orth_combo_mul3 {A : Type*} [Ring A] [Algebra ℂ A] {p q r : A}
    (hp : p * p = p) (hq : q * q = q) (hr : r * r = r)
    (hpq : p * q = 0) (hqp : q * p = 0) (hpr : p * r = 0) (hrp : r * p = 0)
    (hqr : q * r = 0) (hrq : r * q = 0) (c₁ c₂ c₃ d₁ d₂ d₃ : ℂ) :
    (c₁ • p + c₂ • q + c₃ • r) * (d₁ • p + d₂ • q + d₃ • r) =
      (c₁ * d₁) • p + (c₂ * d₂) • q + (c₃ * d₃) • r := by
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul, hp, hq, hr, hpq, hqp,
    hpr, hrp, hqr, hrq, smul_zero, add_zero, zero_add]
  module

variable {m : ℕ}

/-- `Z P_u Z = P_v`. -/
theorem Z_P_Z (m : ℕ) : XorWeight.Z m * XorWeight.P m * XorWeight.Z m = V m := by
  ext i j
  simp only [XorWeight.Z, XorWeight.P, V, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Matrix.of_apply]
  ring

theorem Z_V_Z (m : ℕ) : XorWeight.Z m * V m * XorWeight.Z m = XorWeight.P m := by
  rw [← Z_P_Z]
  calc XorWeight.Z m * (XorWeight.Z m * XorWeight.P m * XorWeight.Z m) * XorWeight.Z m
      = (XorWeight.Z m * XorWeight.Z m) * XorWeight.P m * (XorWeight.Z m * XorWeight.Z m) := by
        simp only [mul_assoc]
    _ = XorWeight.P m := by rw [XorWeight.Z_mul_Z, one_mul, mul_one]

theorem Z_mul_P (m : ℕ) : XorWeight.Z m * XorWeight.P m = V m * XorWeight.Z m := by
  rw [← Z_P_Z]
  calc XorWeight.Z m * XorWeight.P m
      = XorWeight.Z m * XorWeight.P m * (XorWeight.Z m * XorWeight.Z m) := by
        rw [XorWeight.Z_mul_Z, mul_one]
    _ = _ := by simp only [mul_assoc]

theorem Z_mul_V (m : ℕ) : XorWeight.Z m * V m = XorWeight.P m * XorWeight.Z m := by
  rw [← Z_P_Z]
  calc XorWeight.Z m * (XorWeight.Z m * XorWeight.P m * XorWeight.Z m)
      = (XorWeight.Z m * XorWeight.Z m) * XorWeight.P m * XorWeight.Z m := by
        simp only [mul_assoc]
    _ = _ := by rw [XorWeight.Z_mul_Z, one_mul]

theorem V_mul_V (m : ℕ) : V m * V m = V m := by
  rw [← Z_P_Z]
  calc XorWeight.Z m * XorWeight.P m * XorWeight.Z m *
        (XorWeight.Z m * XorWeight.P m * XorWeight.Z m)
      = XorWeight.Z m * XorWeight.P m * (XorWeight.Z m * XorWeight.Z m) * XorWeight.P m *
        XorWeight.Z m := by simp only [mul_assoc]
    _ = XorWeight.Z m * (XorWeight.P m * XorWeight.P m) * XorWeight.Z m := by
        rw [XorWeight.Z_mul_Z, mul_one]
        simp only [mul_assoc]
    _ = _ := by rw [XorWeight.P_mul_P]

theorem P_mul_V (hm : Even m) : XorWeight.P m * V m = 0 := by
  rw [← Z_P_Z]
  calc XorWeight.P m * (XorWeight.Z m * XorWeight.P m * XorWeight.Z m)
      = XorWeight.P m * XorWeight.Z m * XorWeight.P m * XorWeight.Z m := by
        simp only [mul_assoc]
    _ = 0 := by rw [XorWeight.P_Z_P hm, zero_mul]

theorem V_mul_P (hm : Even m) : V m * XorWeight.P m = 0 := by
  rw [← Z_P_Z]
  calc XorWeight.Z m * XorWeight.P m * XorWeight.Z m * XorWeight.P m
      = XorWeight.Z m * (XorWeight.P m * XorWeight.Z m * XorWeight.P m) := by
        simp only [mul_assoc]
    _ = 0 := by rw [XorWeight.P_Z_P hm, mul_zero]

theorem star_V (m : ℕ) : star (V m) = V m := by
  rw [← Z_P_Z, star_mul, star_mul, XorWeight.star_Z, XorWeight.star_P, mul_assoc]

theorem P_add_V_add_R (m : ℕ) : XorWeight.P m + V m + R m = 1 := by
  rw [R]
  abel

theorem P_mul_R (hm : Even m) : XorWeight.P m * R m = 0 := by
  rw [R, mul_sub, mul_sub, mul_one, XorWeight.P_mul_P, P_mul_V hm, sub_self, sub_zero]

theorem R_mul_P (hm : Even m) : R m * XorWeight.P m = 0 := by
  rw [R, sub_mul, sub_mul, one_mul, XorWeight.P_mul_P, V_mul_P hm, sub_self, sub_zero]

theorem V_mul_R (hm : Even m) : V m * R m = 0 := by
  rw [R, mul_sub, mul_sub, mul_one, V_mul_P hm, V_mul_V, sub_zero, sub_self]

theorem R_mul_V (hm : Even m) : R m * V m = 0 := by
  rw [R, sub_mul, sub_mul, one_mul, P_mul_V hm, V_mul_V, sub_zero, sub_self]

theorem R_mul_R (hm : Even m) : R m * R m = R m := by
  calc R m * R m = R m * (1 - XorWeight.P m - V m) := rfl
    _ = R m := by rw [mul_sub, mul_sub, mul_one, R_mul_P hm, R_mul_V hm, sub_zero, sub_zero]

theorem star_R (m : ℕ) : star (R m) = R m := by
  rw [R, star_sub, star_sub, star_one, XorWeight.star_P, star_V]

theorem V_mulVec_one (hm : Even m) : V m *ᵥ (fun _ => 1) = 0 := by
  funext i
  simp only [V, Matrix.mulVec, dotProduct, Matrix.of_apply, mul_one, Pi.zero_apply]
  have h : ∀ c : Fin m, (-1 : ℂ) ^ ((i : ℕ) + c) / m = (-1) ^ (i : ℕ) / m * (-1) ^ (c : ℕ) :=
    fun c => by rw [pow_add]; ring
  rw [Finset.sum_congr rfl fun c _ => h c, ← Finset.mul_sum, XorWeight.sum_neg_one_pow hm,
    mul_zero]

theorem R_mulVec_one (hm : Even m) : R m *ᵥ (fun _ => 1) = 0 := by
  rw [R, Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, XorWeight.P_mulVec_one,
    V_mulVec_one hm, sub_self, sub_zero]

theorem Z_mul_R (m : ℕ) : XorWeight.Z m * R m = R m * XorWeight.Z m := by
  rw [R, mul_sub, mul_sub, sub_mul, sub_mul, mul_one, one_mul, Z_mul_P, Z_mul_V]
  abel

/-- The coefficientwise product for combinations of `P`, `V`, `R`. -/
theorem combo_mul (hm : Even m) (c₁ c₂ c₃ d₁ d₂ d₃ : ℂ) :
    (c₁ • XorWeight.P m + c₂ • V m + c₃ • R m) * (d₁ • XorWeight.P m + d₂ • V m + d₃ • R m) =
      (c₁ * d₁) • XorWeight.P m + (c₂ * d₂) • V m + (c₃ * d₃) • R m :=
  orth_combo_mul3 (XorWeight.P_mul_P m) (V_mul_V m) (R_mul_R hm) (P_mul_V hm) (V_mul_P hm)
    (P_mul_R hm) (R_mul_P hm) (V_mul_R hm) (R_mul_V hm) c₁ c₂ c₃ d₁ d₂ d₃

theorem W_mul_WInv (hm : Even m) {a : ℝ} (ha : a ≠ 0) : W m a * WInv m a = 1 := by
  have ha' : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha
  have h := combo_mul hm 1 ((a : ℂ) ^ 2) (a : ℂ) 1 ((a : ℂ) ^ 2)⁻¹ (a : ℂ)⁻¹
  simp only [one_smul, one_mul] at h
  rw [W, WInv, h, mul_inv_cancel₀ (pow_ne_zero 2 ha'), mul_inv_cancel₀ ha', one_smul, one_smul,
    P_add_V_add_R]

theorem WInv_mul_W (hm : Even m) {a : ℝ} (ha : a ≠ 0) : WInv m a * W m a = 1 := by
  have ha' : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha
  have h := combo_mul hm 1 ((a : ℂ) ^ 2)⁻¹ (a : ℂ)⁻¹ 1 ((a : ℂ) ^ 2) (a : ℂ)
  simp only [one_smul, one_mul] at h
  rw [W, WInv, h, inv_mul_cancel₀ (pow_ne_zero 2 ha'), inv_mul_cancel₀ ha', one_smul, one_smul,
    P_add_V_add_R]

theorem inv_W (hm : Even m) {a : ℝ} (ha : a ≠ 0) : (W m a)⁻¹ = WInv m a :=
  Matrix.inv_eq_right_inv (W_mul_WInv hm ha)

theorem star_ofReal (a : ℝ) : star (a : ℂ) = a := Complex.conj_ofReal a

theorem star_W (m : ℕ) (a : ℝ) : star (W m a) = W m a := by
  rw [W, star_add, star_add, star_smul, star_smul, XorWeight.star_P, star_V, star_R, star_pow,
    star_ofReal]

theorem star_WInv (m : ℕ) (a : ℝ) : star (WInv m a) = WInv m a := by
  rw [WInv, star_add, star_add, star_smul, star_smul, XorWeight.star_P, star_V, star_R,
    star_inv₀, star_inv₀, star_pow, star_ofReal]

theorem W_mulVec_one (hm : Even m) (a : ℝ) : W m a *ᵥ (fun _ => 1) = fun _ => 1 := by
  rw [W, Matrix.add_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
    XorWeight.P_mulVec_one, V_mulVec_one hm, R_mulVec_one hm, smul_zero, smul_zero, add_zero,
    add_zero]

/-- `W⁻¹ Z W⁻¹ = a⁻² Z`. -/
theorem WInv_Z_WInv (hm : Even m) (a : ℝ) :
    WInv m a * XorWeight.Z m * WInv m a = ((a : ℂ) ^ 2)⁻¹ • XorWeight.Z m := by
  have h1 : XorWeight.Z m * WInv m a =
      (((a : ℂ) ^ 2)⁻¹ • XorWeight.P m + (1 : ℂ) • V m + (a : ℂ)⁻¹ • R m) * XorWeight.Z m := by
    rw [WInv, mul_add, mul_add, mul_smul_comm, mul_smul_comm, Z_mul_P, Z_mul_V, Z_mul_R,
      add_mul, add_mul, smul_mul_assoc, smul_mul_assoc, smul_mul_assoc, one_smul]
    abel
  have h2 := combo_mul hm 1 ((a : ℂ) ^ 2)⁻¹ (a : ℂ)⁻¹ ((a : ℂ) ^ 2)⁻¹ 1 (a : ℂ)⁻¹
  rw [one_smul] at h2
  have h3 : (a : ℂ)⁻¹ * (a : ℂ)⁻¹ = ((a : ℂ) ^ 2)⁻¹ := by rw [sq, mul_inv]
  rw [mul_assoc, h1, ← mul_assoc, WInv, h2, one_mul, mul_one, h3, ← smul_add, ← smul_add,
    P_add_V_add_R, smul_one_mul]

end

end SparseLowerBounds.Helpers.SearchWeight
end
