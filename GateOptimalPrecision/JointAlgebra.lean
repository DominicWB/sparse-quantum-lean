import GateOptimalPrecision.LocalFactor
import GateEfficientNative.Native.Edge
import SignedFactorSimulation.Factor

/-!
# The joint private operation (Section `gate:sec:native`): clipping, the bulk Cayley rotation and the correction phases

The local identities of the joint private operation of the clipped regime ("Sparse preparation
and the joint private operation"), with `z = H_{ij}/μ`, `x = |z|` and the clipping parameter
`β ≥ 0` (the manuscript's `β = h_a`, eq. `gate:eq:clip`):

* `clipE_add_corrE`, `clip_split`: the clipped entry `z/(1 + βx)` and the correction entry
  `zβx/(1 + βx)` add up to `z`, so `H = H_c + C_H` (`gate:eq:clip`);
* `norm_corrE`, `norm_corrE_le_one`: the correction magnitude is `βx²/(1 + βx) ≤ 1` (for `x ≤ 1`),
  which "permits" eq. `gate:eq:dilation`;
* `norm_clipE_le`, `norm_bulk_le`: the bulk value `y = 2qz/(1 + βx)` has `|y| ≤ 2q/β` ("a bulk
  with `|K_b| ≤ 2q/h_a`" at `β = h_a`);
* `edgeMat_cayley`, `edgeMat_unitary`: the bulk private operation `D(y)` (`gate:eq:cayley`, the
  released edge rotation `SparseHamiltonian.GateNative.edgeMat`) is the Cayley transform
  `(E(y) + i)(E(y) - i)⁻¹` of `E(y) = [[0, y], [ȳ, 0]]`, a unitary;
* `edgeMat_zero`: `D(0) = -I`; `norm_edgeMat_add_one_le`: `‖D(y) - D(0)‖ ≤ 2|y|` ("near zero its
  phase can also be avoided by using `D(0) = -I` and the continuity bound on the matrix itself");
* `hMat_edgeMat_hMat`: the correction success phases `(±2q + i)/(±2q - i)` are the edge rotation of
  the real value `2q` in the Hadamard basis, and the failure phase `-1` is `D(0)`; the same holds
  for the signed-factor phases `ζ_± = (±q + i)/(±q - i)` (`SignedFactorSimulation.Known.zetaP`,
  `zetaM`) of `gate:eq:factor-private`, so all private phases are realised by the released
  bit-controlled edge rotation.
-/

set_option autoImplicit false

namespace GateOptimalPrecision

noncomputable section

open Matrix Complex
open SparseHamiltonian.GateNative (edgeMat)
open SignedFactorSimulation.Known (zetaP zetaM)
open scoped ComplexConjugate Matrix

/-! ### Clipping -/

/-- The clipped entry `z/(1 + β|z|)` (`gate:eq:clip`, normalised by `μ`). -/
def clipE (β : ℝ) (z : ℂ) : ℂ := z * (((1 + β * ‖z‖)⁻¹ : ℝ) : ℂ)

/-- The correction entry `z β|z|/(1 + β|z|)`. -/
def corrE (β : ℝ) (z : ℂ) : ℂ := z * ((β * ‖z‖ / (1 + β * ‖z‖) : ℝ) : ℂ)

theorem one_add_pos {β : ℝ} (hβ : 0 ≤ β) (z : ℂ) : 0 < 1 + β * ‖z‖ := by
  have := mul_nonneg hβ (norm_nonneg z)
  linarith

/-- `z/(1 + βx) + zβx/(1 + βx) = z`. -/
theorem clipE_add_corrE {β : ℝ} (hβ : 0 ≤ β) (z : ℂ) : clipE β z + corrE β z = z := by
  have h := (one_add_pos hβ z).ne'
  unfold clipE corrE
  rw [← mul_add, ← Complex.ofReal_add]
  have e : (1 + β * ‖z‖)⁻¹ + β * ‖z‖ / (1 + β * ‖z‖) = 1 := by field_simp
  rw [e, Complex.ofReal_one, mul_one]

/-- `H = H_c + C_H` entrywise, for the entry scale `μ ≠ 0`. -/
theorem clip_split {n : Type*} {β μ : ℝ} (hβ : 0 ≤ β) (hμ : μ ≠ 0) (H : Matrix n n ℂ) :
    H.map (fun h => (μ : ℂ) * clipE β (h / μ)) + H.map (fun h => (μ : ℂ) * corrE β (h / μ)) =
      H := by
  ext i j
  simp only [Matrix.add_apply, Matrix.map_apply]
  rw [← mul_add, clipE_add_corrE hβ]
  have : (μ : ℂ) ≠ 0 := by exact_mod_cast hμ
  field_simp

/-- The correction magnitude `βx²/(1 + βx)`. -/
theorem norm_corrE {β : ℝ} (hβ : 0 ≤ β) (z : ℂ) :
    ‖corrE β z‖ = β * ‖z‖ ^ 2 / (1 + β * ‖z‖) := by
  have h := one_add_pos hβ z
  unfold corrE
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (mul_nonneg hβ (norm_nonneg z)) h.le)]
  ring

/-- The correction magnitude is at most one, which permits `gate:eq:dilation`. -/
theorem norm_corrE_le_one {β : ℝ} (hβ : 0 ≤ β) {z : ℂ} (hz : ‖z‖ ≤ 1) : ‖corrE β z‖ ≤ 1 := by
  have h := one_add_pos hβ z
  rw [norm_corrE hβ, div_le_one h]
  have := mul_nonneg hβ (norm_nonneg z)
  have : β * ‖z‖ ^ 2 ≤ β * ‖z‖ := by
    have := mul_le_mul_of_nonneg_left hz (mul_nonneg hβ (norm_nonneg z))
    nlinarith
  linarith

theorem norm_clipE {β : ℝ} (hβ : 0 ≤ β) (z : ℂ) : ‖clipE β z‖ = ‖z‖ / (1 + β * ‖z‖) := by
  have h := one_add_pos hβ z
  unfold clipE
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr h.le),
    div_eq_mul_inv]

/-- Clipping never increases the modulus. -/
theorem norm_clipE_le {β : ℝ} (hβ : 0 ≤ β) (z : ℂ) : ‖clipE β z‖ ≤ ‖z‖ := by
  have h := one_add_pos hβ z
  rw [norm_clipE hβ, div_le_iff₀ h]
  have := mul_nonneg (norm_nonneg z) (mul_nonneg hβ (norm_nonneg z))
  nlinarith

/-- **The bulk bound** `|y| ≤ 2q/β` for `y = 2qz/(1 + β|z|)`. -/
theorem norm_bulk_le {β q : ℝ} (hβ : 0 < β) (hq : 0 ≤ q) (z : ℂ) :
    ‖((2 * q : ℝ) : ℂ) * clipE β z‖ ≤ 2 * q / β := by
  have h := one_add_pos hβ.le z
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith), norm_clipE hβ.le,
    le_div_iff₀ hβ]
  have hz : β * (‖z‖ / (1 + β * ‖z‖)) ≤ 1 := by
    rw [mul_div_assoc', div_le_one h]
    linarith
  calc 2 * q * (‖z‖ / (1 + β * ‖z‖)) * β = 2 * q * (β * (‖z‖ / (1 + β * ‖z‖))) := by ring
    _ ≤ 2 * q * 1 := mul_le_mul_of_nonneg_left hz (by linarith)
    _ = 2 * q := mul_one _

/-! ### The bulk Cayley rotation -/

theorem mul_conj_norm (y : ℂ) : y * conj y = ((‖y‖ : ℝ) : ℂ) ^ 2 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring

theorem conj_mul_norm (y : ℂ) : conj y * y = ((‖y‖ : ℝ) : ℂ) ^ 2 := by
  rw [mul_comm]
  exact mul_conj_norm y

theorem one_add_norm_sq_ne (y : ℂ) : (1 + ((‖y‖ : ℝ) : ℂ) ^ 2) ≠ 0 := by
  have h : (0 : ℝ) < 1 + ‖y‖ ^ 2 := by positivity
  exact_mod_cast h.ne'

/-- **`D(y)` is the Cayley transform of `E(y)`**: `D(y)(E(y) - i) = E(y) + i`. -/
theorem edgeMat_cayley (y : ℂ) :
    edgeMat y * (eMat y - Complex.I • (1 : Matrix Bool Bool ℂ)) =
      eMat y + Complex.I • (1 : Matrix Bool Bool ℂ) := by
  have hy := mul_conj_norm y
  have hy' := conj_mul_norm y
  have hd := one_add_norm_sq_ne y
  ext b d
  cases b <;> cases d <;>
    simp [edgeMat, eMat, Matrix.mul_apply, Matrix.one_apply] <;>
    field_simp <;>
    (try simp only [Complex.I_sq]) <;>
    first
      | ring1
      | linear_combination (-2 : ℂ) * hy'
      | linear_combination (-2 : ℂ) * hy
      | linear_combination (2 : ℂ) * hy'

theorem edgeMat_conjTranspose (y : ℂ) : (edgeMat y)ᴴ = Matrix.of fun b d =>
    ((1 + ((‖y‖ : ℝ) : ℂ) ^ 2)⁻¹) *
      (if b = d then ((‖y‖ : ℝ) : ℂ) ^ 2 - 1 else if b then -(2 * I * conj y) else -(2 * I * y)) := by
  ext b d
  cases b <;> cases d <;> simp [edgeMat, Matrix.conjTranspose_apply]

/-- `D(y)` is unitary. -/
theorem edgeMat_unitary (y : ℂ) : (edgeMat y)ᴴ * edgeMat y = 1 := by
  have hy := mul_conj_norm y
  have hy' := conj_mul_norm y
  have hd := one_add_norm_sq_ne y
  rw [edgeMat_conjTranspose]
  ext b d
  cases b <;> cases d <;>
    simp [edgeMat, Matrix.mul_apply] <;>
    field_simp <;>
    (try simp only [Complex.I_sq]) <;>
    first
      | ring1
      | linear_combination (4 : ℂ) * hy

/-- `D(0) = -I`: the failure and zero-padding phase. -/
theorem edgeMat_zero : edgeMat 0 = -1 := by
  ext b d
  cases b <;> cases d <;> simp [edgeMat]

/-- `(D(y) + I)†(D(y) + I) = (4|y|²/(1 + |y|²)) I`. -/
theorem edgeMat_add_one_gram (y : ℂ) :
    (edgeMat y + 1)ᴴ * (edgeMat y + 1) =
      ((4 * ‖y‖ ^ 2 / (1 + ‖y‖ ^ 2) : ℝ) : ℂ) • (1 : Matrix Bool Bool ℂ) := by
  have hy := mul_conj_norm y
  have hy' := conj_mul_norm y
  have hd := one_add_norm_sq_ne y
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one, edgeMat_conjTranspose]
  ext b d
  cases b <;> cases d <;>
    simp [edgeMat, Matrix.mul_apply, Matrix.one_apply] <;>
    field_simp <;>
    (try simp only [Complex.I_sq]) <;>
    first
      | ring1
      | linear_combination (4 : ℂ) * hy

section Norm

open scoped Matrix.Norms.L2Operator

/-- **Continuity at zero**: `‖D(y) - D(0)‖ ≤ 2|y|` on all inputs. -/
theorem norm_edgeMat_add_one_le (y : ℂ) : ‖edgeMat y - edgeMat 0‖ ≤ 2 * ‖y‖ := by
  rw [edgeMat_zero, sub_neg_eq_add]
  have h := CStarRing.norm_star_mul_self (x := edgeMat y + 1)
  rw [Matrix.star_eq_conjTranspose, edgeMat_add_one_gram, norm_smul, norm_one, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at h
  have h1 : 4 * ‖y‖ ^ 2 / (1 + ‖y‖ ^ 2) ≤ (2 * ‖y‖) ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg ‖y‖, sq_nonneg (‖y‖ ^ 2)]
  have h2 : ‖edgeMat y + 1‖ ^ 2 ≤ (2 * ‖y‖) ^ 2 := by
    rw [sq, ← h]
    exact h1
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp h2

end Norm

/-! ### The correction phases -/

theorem ofReal_add_I_ne (x : ℝ) : (x : ℂ) + I ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this

theorem ofReal_sub_I_ne (x : ℝ) : (x : ℂ) - I ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this

theorem hMat_mul_self : hMat * hMat = 1 := by
  have hr := sqrt2_inv_sq_c
  ext b d
  cases b <;> cases d <;> simp [hMat, Matrix.mul_apply] <;>
    first
      | linear_combination 2 * hr

theorem hMat_xMat_hMat :
    hMat * xMat * hMat = Matrix.diagonal (fun b => if b then (-1 : ℂ) else 1) := by
  have hr := sqrt2_inv_sq_c
  ext b d
  cases b <;> cases d <;>
    simp [hMat, xMat, Matrix.mul_apply] <;>
    first
      | linear_combination 2 * hr
      | linear_combination -2 * hr

/-- For real `x`, `D(x) = a I + b X` with `a = (x² - 1)/(1 + x²)` and `b = 2ix/(1 + x²)`. -/
theorem edgeMat_real (x : ℝ) :
    edgeMat (x : ℂ) = (((x : ℂ) ^ 2 - 1) / (1 + (x : ℂ) ^ 2)) • (1 : Matrix Bool Bool ℂ) +
      ((2 * I * x) / (1 + (x : ℂ) ^ 2)) • xMat := by
  have hx2 : ((|x| : ℝ) : ℂ) ^ 2 = (x : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow, sq_abs, Complex.ofReal_pow]
  ext b d
  cases b <;> cases d <;>
    simp [edgeMat, xMat, hx2, Complex.conj_ofReal] <;> ring

theorem one_add_sq_eq (x : ℝ) : 1 + (x : ℂ) ^ 2 = ((x : ℂ) + I) * ((x : ℂ) - I) := by
  ring_nf
  rw [Complex.I_sq]
  ring

theorem zetaP_eq (x : ℝ) :
    zetaP x = ((x : ℂ) ^ 2 - 1) / (1 + (x : ℂ) ^ 2) + (2 * I * x) / (1 + (x : ℂ) ^ 2) := by
  have h1 := ofReal_add_I_ne x
  have h2 := ofReal_sub_I_ne x
  rw [zetaP, ← add_div, one_add_sq_eq, div_eq_div_iff h2 (mul_ne_zero h1 h2)]
  first
    | linear_combination ((x : ℂ) - I) * Complex.I_sq

theorem zetaM_eq (x : ℝ) :
    zetaM x = ((x : ℂ) ^ 2 - 1) / (1 + (x : ℂ) ^ 2) - (2 * I * x) / (1 + (x : ℂ) ^ 2) := by
  have h1 := ofReal_add_I_ne x
  have h2 := ofReal_sub_I_ne x
  have h4 : -(x : ℂ) - I ≠ 0 := by
    rw [show -(x : ℂ) - I = -((x : ℂ) + I) by ring]
    exact neg_ne_zero.mpr h1
  rw [zetaM, ← sub_div, one_add_sq_eq, div_eq_div_iff h4 (mul_ne_zero h1 h2)]
  first
    | linear_combination (-((x : ℂ) + I)) * Complex.I_sq

/-- **The private phases in the Hadamard basis**: `H D(x) H = diag((x + i)/(x - i),
(-x + i)/(-x - i))` for real `x`. With `x = 2q` these are the correction success phases; with
`x = q` the signed-factor phases `ζ_±`. -/
theorem hMat_edgeMat_hMat (x : ℝ) :
    hMat * edgeMat (x : ℂ) * hMat = Matrix.diagonal (fun b => if b then zetaM x else zetaP x) := by
  rw [edgeMat_real, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hMat_mul_self, hMat_xMat_hMat, zetaP_eq,
    zetaM_eq]
  ext b d
  cases b <;> cases d <;> simp
  ring

/-- The failure phase is the edge rotation of zero. -/
theorem failure_phase : edgeMat 0 = (-1 : ℂ) • (1 : Matrix Bool Bool ℂ) := by
  rw [edgeMat_zero, neg_one_smul]

end

end GateOptimalPrecision
