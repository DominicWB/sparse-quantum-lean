import SparseLowerBounds.Helpers.SearchWeight.Vectors

set_option synthInstance.maxHeartbeats 400000

section
/-!
# The conjugated query block for `SparseLowerBounds.Query.SearchWeight`

Helper module of group search-weight (proof of Lemma `hsl:lem:search`). With
`e = (W/a - I)|b⟩` and `f = (a W⁻¹ - I)|b⟩` (`E`, `F`, the same terms as
`SearchWeight.eVec`, `SearchWeight.fVec`):
`W D_b W⁻¹ = D_b - 2(e⟨b| + |b⟩f† + e f†)` and
`‖W D_b W⁻¹‖ ≤ 1 + 4√2 a/√m + 4a²/m` for `a ≥ 1`.
-/

namespace SparseLowerBounds.Helpers.SearchWeight

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator

variable {m : ℕ}

/-- `e = (W/a - I)|b⟩`. -/
def E (m : ℕ) (a : ℝ) (b : Fin m) : Fin m → ℂ :=
  ((a : ℂ)⁻¹ • W m a - 1) *ᵥ (Pi.single b (1 : ℂ) : Fin m → ℂ)

/-- `f = (a W⁻¹ - I)|b⟩`. -/
def F (m : ℕ) (a : ℝ) (b : Fin m) : Fin m → ℂ :=
  ((a : ℂ) • WInv m a - 1) *ᵥ (Pi.single b (1 : ℂ) : Fin m → ℂ)

theorem E_eq {a : ℝ} (ha : a ≠ 0) (b : Fin m) :
    E m a b = (((a : ℂ)⁻¹ - 1) • XorWeight.P m + ((a : ℂ) - 1) • V m) *ᵥ
      (Pi.single b (1 : ℂ) : Fin m → ℂ) := by
  have ha' : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha
  have h1 : (a : ℂ)⁻¹ • W m a = (a : ℂ)⁻¹ • XorWeight.P m + (a : ℂ) • V m + R m := by
    rw [W, smul_add, smul_add, smul_smul, smul_smul,
      show (a : ℂ)⁻¹ * (a : ℂ) ^ 2 = a by rw [sq, ← mul_assoc, inv_mul_cancel₀ ha', one_mul],
      inv_mul_cancel₀ ha', one_smul]
  rw [E, h1, R]
  congr 1
  module

theorem F_eq {a : ℝ} (ha : a ≠ 0) (b : Fin m) :
    F m a b = (((a : ℂ) - 1) • XorWeight.P m + ((a : ℂ)⁻¹ - 1) • V m) *ᵥ
      (Pi.single b (1 : ℂ) : Fin m → ℂ) := by
  have ha' : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha
  have h1 : (a : ℂ) • WInv m a = (a : ℂ) • XorWeight.P m + (a : ℂ)⁻¹ • V m + R m := by
    rw [WInv, smul_add, smul_add, smul_smul, smul_smul,
      show (a : ℂ) * ((a : ℂ) ^ 2)⁻¹ = (a : ℂ)⁻¹ by
        rw [sq, mul_inv, ← mul_assoc, mul_inv_cancel₀ ha', one_mul],
      mul_inv_cancel₀ ha', one_smul]
  rw [F, h1, R]
  congr 1
  module

/-- The entries of `x P_u|b⟩ + y P_v|b⟩`. -/
theorem combo_mulVec_single (b : Fin m) (x y : ℂ) :
    (x • XorWeight.P m + y • V m) *ᵥ (Pi.single b (1 : ℂ) : Fin m → ℂ) =
      fun i : Fin m => x * (m : ℂ)⁻¹ + y * ((-1 : ℂ) ^ ((i : ℕ) + b) / m) := by
  rw [Matrix.mulVec_single_one]
  funext i
  simp [XorWeight.P, V]

/-- `‖x P_u|b⟩ + y P_v|b⟩‖² = (|x|² + |y|²)/m` for even `m`. -/
theorem norm_combo_sq (hm : Even m) (b : Fin m) (x y : ℂ) :
    ‖(WithLp.toLp 2 ((x • XorWeight.P m + y • V m) *ᵥ (Pi.single b (1 : ℂ) : Fin m → ℂ)) :
      EuclideanSpace ℂ (Fin m))‖ ^ 2 = (‖x‖ ^ 2 + ‖y‖ ^ 2) / m := by
  rw [combo_mulVec_single]
  exact norm_alt_combo_sq hm b x y

theorem norm_combo_le (hm : Even m) (b : Fin m) {x y : ℂ} {a : ℝ} (ha : 0 ≤ a)
    (hx : ‖x‖ ≤ a) (hy : ‖y‖ ≤ a) :
    ‖(WithLp.toLp 2 ((x • XorWeight.P m + y • V m) *ᵥ (Pi.single b (1 : ℂ) : Fin m → ℂ)) :
      EuclideanSpace ℂ (Fin m))‖ ≤ Real.sqrt 2 * a / Real.sqrt m := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast Fin.pos b
  have hsq : (Real.sqrt 2 * a / Real.sqrt m) ^ 2 = 2 * a ^ 2 / m := by
    rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt hm0.le]
  refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp ?_
  rw [norm_combo_sq hm b x y, hsq]
  gcongr
  nlinarith [pow_le_pow_left₀ (norm_nonneg x) hx 2, pow_le_pow_left₀ (norm_nonneg y) hy 2]

theorem norm_inv_sub_one_le {a : ℝ} (ha : 1 ≤ a) : ‖(a : ℂ)⁻¹ - 1‖ ≤ a := by
  have ha0 : 0 < a := by linarith
  rw [show (a : ℂ)⁻¹ - 1 = ((a⁻¹ - 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
    Real.norm_eq_abs, abs_le]
  have h1 : a⁻¹ ≤ 1 := inv_le_one_of_one_le₀ ha
  have h2 : 0 < a⁻¹ := inv_pos.mpr ha0
  constructor <;> linarith

theorem norm_sub_one_le {a : ℝ} (ha : 1 ≤ a) : ‖(a : ℂ) - 1‖ ≤ a := by
  rw [show (a : ℂ) - 1 = ((a - 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
    Real.norm_eq_abs, abs_le]
  constructor <;> linarith

theorem norm_E_le (hm : Even m) {a : ℝ} (ha : 1 ≤ a) (b : Fin m) :
    ‖(WithLp.toLp 2 (E m a b) : EuclideanSpace ℂ (Fin m))‖ ≤ Real.sqrt 2 * a / Real.sqrt m := by
  rw [E_eq (by linarith : (0 : ℝ) < a).ne' b]
  exact norm_combo_le hm b (by linarith) (norm_inv_sub_one_le ha) (norm_sub_one_le ha)

theorem norm_F_le (hm : Even m) {a : ℝ} (ha : 1 ≤ a) (b : Fin m) :
    ‖(WithLp.toLp 2 (F m a b) : EuclideanSpace ℂ (Fin m))‖ ≤ Real.sqrt 2 * a / Real.sqrt m := by
  rw [F_eq (by linarith : (0 : ℝ) < a).ne' b]
  exact norm_combo_le hm b (by linarith) (norm_sub_one_le ha) (norm_inv_sub_one_le ha)

/-- `D_b = 1 - 2|b⟩⟨b|`. -/
theorem D_eq (b : Fin m) :
    XorWeight.D b = 1 - (2 : ℂ) • Matrix.vecMulVec (Pi.single b (1 : ℂ)) (Pi.single b 1) := by
  ext i j
  rw [XorWeight.D, Matrix.diagonal_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply,
    Matrix.vecMulVec_apply, Pi.single_apply, Pi.single_apply]
  by_cases hib : i = b
  · subst hib
    by_cases hji : j = i
    · subst hji
      norm_num
    · simp [hji, Ne.symm hji]
  · by_cases hij : i = j
    · subst hij
      simp [hib]
    · simp [hib, hij]

theorem star_single (b : Fin m) : star (Pi.single b (1 : ℂ) : Fin m → ℂ) = Pi.single b 1 := by
  funext i
  by_cases hib : i = b <;> simp [hib]

/-- **The conjugated query block** (proof of Lemma `hsl:lem:search`). -/
theorem conj_D_eq (hm : Even m) {a : ℝ} (ha : a ≠ 0) (b : Fin m) :
    W m a * XorWeight.D b * (W m a)⁻¹ = XorWeight.D b - (2 : ℂ) •
      (Matrix.vecMulVec (E m a b) (Pi.single b (1 : ℂ) : Fin m → ℂ) +
        Matrix.vecMulVec (Pi.single b (1 : ℂ) : Fin m → ℂ) (star (F m a b)) +
        Matrix.vecMulVec (E m a b) (star (F m a b))) := by
  have ha' : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha
  rw [inv_W hm ha]
  have hWe : W m a *ᵥ (Pi.single b (1 : ℂ) : Fin m → ℂ) =
      (a : ℂ) • (E m a b + Pi.single b (1 : ℂ)) := by
    rw [E, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, sub_add_cancel, smul_smul,
      mul_inv_cancel₀ ha', one_smul]
  have hWInve : WInv m a *ᵥ (Pi.single b (1 : ℂ) : Fin m → ℂ) =
      (a : ℂ)⁻¹ • (F m a b + Pi.single b (1 : ℂ)) := by
    rw [F, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, sub_add_cancel, smul_smul,
      inv_mul_cancel₀ ha', one_smul]
  have hH : (WInv m a)ᴴ = WInv m a := star_WInv m a
  have hrow : (Pi.single b (1 : ℂ) : Fin m → ℂ) ᵥ* WInv m a =
      (a : ℂ)⁻¹ • (star (F m a b) + Pi.single b (1 : ℂ)) := by
    calc (Pi.single b (1 : ℂ) : Fin m → ℂ) ᵥ* WInv m a
        = (Pi.single b (1 : ℂ) : Fin m → ℂ) ᵥ* (WInv m a)ᴴ := by rw [hH]
      _ = star (WInv m a *ᵥ star (Pi.single b (1 : ℂ) : Fin m → ℂ)) :=
          Matrix.vecMul_conjTranspose _ _
      _ = _ := by
          rw [star_single, hWInve, star_smul, star_add, star_single, star_inv₀, star_ofReal]
  calc W m a * XorWeight.D b * WInv m a
      = W m a * (1 - (2 : ℂ) • Matrix.vecMulVec (Pi.single b (1 : ℂ)) (Pi.single b 1)) *
          WInv m a := by rw [D_eq]
    _ = 1 - (2 : ℂ) • Matrix.vecMulVec (W m a *ᵥ (Pi.single b (1 : ℂ) : Fin m → ℂ))
          ((Pi.single b (1 : ℂ) : Fin m → ℂ) ᵥ* WInv m a) := by
        rw [mul_sub, sub_mul, mul_one, W_mul_WInv hm ha, mul_smul_comm, smul_mul_assoc,
          Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
    _ = 1 - (2 : ℂ) • Matrix.vecMulVec (E m a b + Pi.single b (1 : ℂ))
          (star (F m a b) + Pi.single b (1 : ℂ)) := by
        rw [hWe, hrow, Matrix.smul_vecMulVec, Matrix.vecMulVec_smul, smul_smul (a : ℂ),
          mul_inv_cancel₀ ha', one_smul]
    _ = _ := by
        rw [D_eq, Matrix.add_vecMulVec, Matrix.vecMulVec_add, Matrix.vecMulVec_add]
        module

/-- The display bound of the proof of Lemma `hsl:lem:search`:
`‖W D_b W⁻¹‖ ≤ 1 + 4√2 a/√m + 4a²/m`. -/
theorem norm_conj_D_le_fine (hm : Even m) {a : ℝ} (ha : 1 ≤ a) (b : Fin m) :
    ‖W m a * XorWeight.D b * (W m a)⁻¹‖ ≤
      1 + 4 * Real.sqrt 2 * a / Real.sqrt m + 4 * a ^ 2 / m := by
  have ha0 : 0 < a := by linarith
  have hm0 : (0 : ℝ) < m := by exact_mod_cast Fin.pos b
  rw [conj_D_eq hm ha0.ne' b]
  have he := norm_E_le hm ha b
  have hfs : ‖(WithLp.toLp 2 (star (F m a b)) : EuclideanSpace ℂ (Fin m))‖ ≤
      Real.sqrt 2 * a / Real.sqrt m := by
    rw [norm_toLp_star]
    exact norm_F_le hm ha b
  have h1 := norm_toLp_single b
  set c := Real.sqrt 2 * a / Real.sqrt m with hc
  have hc0 : 0 ≤ c := by positivity
  have hA : ‖Matrix.vecMulVec (E m a b) (Pi.single b (1 : ℂ) : Fin m → ℂ)‖ ≤ c :=
    (norm_vecMulVec_le _ _).trans (by rw [h1, mul_one]; exact he)
  have hB : ‖Matrix.vecMulVec (Pi.single b (1 : ℂ) : Fin m → ℂ) (star (F m a b))‖ ≤ c :=
    (norm_vecMulVec_le _ _).trans (by rw [h1, one_mul]; exact hfs)
  have hC : ‖Matrix.vecMulVec (E m a b) (star (F m a b))‖ ≤ c * c :=
    (norm_vecMulVec_le _ _).trans (mul_le_mul he hfs (norm_nonneg _) hc0)
  have hcc : c * c = 2 * a ^ 2 / m := by
    rw [hc, ← sq, div_pow, mul_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt hm0.le]
  have hD : ‖XorWeight.D b‖ ≤ 1 := XorWeight.norm_D_le b
  have hsum := norm_add₃_le (a := Matrix.vecMulVec (E m a b) (Pi.single b (1 : ℂ) : Fin m → ℂ))
    (b := Matrix.vecMulVec (Pi.single b (1 : ℂ) : Fin m → ℂ) (star (F m a b)))
    (c := Matrix.vecMulVec (E m a b) (star (F m a b)))
  calc _ ≤ ‖XorWeight.D b‖ + ‖(2 : ℂ)‖ *
        ‖Matrix.vecMulVec (E m a b) (Pi.single b (1 : ℂ) : Fin m → ℂ) +
          Matrix.vecMulVec (Pi.single b (1 : ℂ) : Fin m → ℂ) (star (F m a b)) +
          Matrix.vecMulVec (E m a b) (star (F m a b))‖ :=
        (norm_sub_le _ _).trans (add_le_add le_rfl (norm_smul_le _ _))
    _ ≤ 1 + 2 * (c + c + c * c) := by
        rw [Complex.norm_ofNat]
        gcongr
        linarith
    _ = 1 + 4 * Real.sqrt 2 * a / Real.sqrt m + 4 * a ^ 2 / m := by
        rw [hcc, hc]
        ring

end

end SparseLowerBounds.Helpers.SearchWeight
end
