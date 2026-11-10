import SparseLinearSystems.Separate.Algebra
import SparseLinearSystems.Circuit.Facts

/-!
# The enlarged system for native sparse input: inverse bound, solution and estimate

Corollary `qls:cor:separate`, proof. For native sparse data `D` with `‖A‖ ≤ 1` the public split
boundary `J = SplitBoundary.fixedSplit D.slot`, the edge generator `K` of the native Cayley
circuit and `α = √s` satisfy the hypotheses of Lemma `qls:lem:walk` for the Hermitian dilation
`H = [[0, A], [A†, 0]]` with `μ = 1` and `k₀ = √s` (`hyp`). The general matrix is covered
directly; no Hermitian case is treated separately.

* `enlarged_inverse`: if `‖v‖ ≤ κ ‖A v‖` for every `v` (`κ ≥ 1`), then
  `‖v‖ ≤ κ_B ‖B v‖` on the whole edge space, `κ_B = 4 √s κ` (eq. `qls:eq:separate-inverse`).
* `solution`: for `‖b‖ = 1` and `A z = b`, the vector `y = -2i√s R₀ J (0, z)` solves
  `B y = J (b, 0)`, with `√s ‖z‖ ≤ ‖y‖ ≤ √2 √s ‖z‖` (eq. `qls:eq:separate-norm`).
* `decode_solution`: the decoder `T = π₂ J† C` maps `y` to `-i√s z` and is a contraction.
* `estimate_transfer`: if `‖z‖/2 ≤ ν̂ ≤ 2‖z‖`, then `ν̂_B = (9/8) √s ν̂` satisfies
  `(3/8) ‖y‖ ≤ ν̂_B ≤ (5/2) ‖y‖` (eq. `qls:eq:separate-transferred-estimate`).
* `ratio_bound`: `1 + κ_B/ν̂_B ≤ (73/9) κ/‖z‖`.
-/

set_option autoImplicit false

namespace SparseLinearSystems.Separate

noncomputable section
open SparseHamiltonian ContinuousLinearMap
open scoped InnerProduct

variable {X n Z : Type*} [Fintype n] [DecidableEq n] {s : ℕ}

local notation "V0" => EuclideanSpace ℂ n
local notation "Dbl" => HilbertRegularization.Double (EuclideanSpace ℂ n)

/-- The public split boundary `J`. -/
abbrev bdry (D : NativeSparseBlockEncoding.Data X n Z s) :
    Dbl →L[ℂ] SparseEdgeMoments.OrientedSpace n :=
  SplitBoundary.fixedSplit D.slot

/-- The Hermitian dilation of the input matrix. -/
abbrev dil (D : NativeSparseBlockEncoding.Data X n Z s) (x : X) : Dbl →L[ℂ] Dbl :=
  HilbertRegularization.dilation (SparseStateOverlap.matrixOperator (D.matrix x))

/-- **The walk-lemma hypotheses for the dilation** (`α = √s`, `μ = 1`, `k₀ = √s`). -/
theorem hyp (D : NativeSparseBlockEncoding.Data X n Z s) (x : X)
    (hA1 : ‖SparseStateOverlap.matrixOperator (D.matrix x)‖ ≤ 1) :
    WalkGap.Hyp (bdry D) (FixedNativeCayleySimulation.generator D x) (dil D x)
      (Real.sqrt (s : ℝ)) 1 (Real.sqrt (s : ℝ)) where
  isometry := SplitBoundary.fixedSplit_isometry D.slot D.slots_pos
  selfAdjoint := by
    have h := FixedNativeCayleySimulation.generator_self_adjoint D x
    rwa [star_eq_adjoint] at h
  alpha_pos := Real.sqrt_pos.mpr (by exact_mod_cast D.slots_pos)
  compression := SplitBoundary.split_compression D x
  moment := fun u => by
    rw [one_mul]
    exact SplitBoundary.split_moment D x (Facts.row_energy _ hA1) (Facts.column_energy _ hA1) u
  mu_nonneg := zero_le_one
  bound := fun v => (le_opNorm _ v).trans (mul_le_mul_of_nonneg_right
    (FixedNativeCayleySimulation.generator_norm_le D x (Facts.row_energy _ hA1)) (norm_nonneg v))
  k0_nonneg := Real.sqrt_nonneg _

/-- The lower singular bound of the dilation from `‖v‖ ≤ κ ‖A v‖`. -/
theorem dil_lower (D : NativeSparseBlockEncoding.Data X n Z s) (x : X) (κ : ℝ) (hκ : 1 ≤ κ)
    (hlow : ∀ v, ‖v‖ ≤ κ * ‖SparseStateOverlap.matrixOperator (D.matrix x) v‖) (w : Dbl) :
    (1 / κ) ^ 2 * ‖w‖ ^ 2 ≤ ‖dil D x w‖ ^ 2 := by
  have h := InputInverseBounds.dilation_lower_sq
    (Facts.equivOfLower (SparseStateOverlap.matrixOperator (D.matrix x)) κ hlow) κ hκ
    (Facts.equivOfLower_symm_norm _ κ (by linarith) hlow) w
  rwa [Facts.equivOfLower_coe] at h

theorem dil_injective (D : NativeSparseBlockEncoding.Data X n Z s) (x : X) (κ : ℝ) (hκ : 1 ≤ κ)
    (hlow : ∀ v, ‖v‖ ≤ κ * ‖SparseStateOverlap.matrixOperator (D.matrix x) v‖) (w : Dbl)
    (hw : dil D x w = 0) : w = 0 := by
  have h := dil_lower D x κ hκ hlow w
  rw [hw, norm_zero] at h
  have hk : 0 < (1 / κ) ^ 2 := by positivity
  have : ‖w‖ ^ 2 ≤ 0 := by nlinarith
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg w])

/-- Every nonzero eigenvalue of the dilation has modulus at least `1/κ`. -/
theorem dil_gap (D : NativeSparseBlockEncoding.Data X n Z s) (x : X) (κ : ℝ) (hκ : 1 ≤ κ)
    (hlow : ∀ v, ‖v‖ ≤ κ * ‖SparseStateOverlap.matrixOperator (D.matrix x) v‖) (w : Dbl) (c : ℂ)
    (hw : w ≠ 0) (hHw : dil D x w = c • w) (_hc : c ≠ 0) : 1 / κ ≤ ‖c‖ := by
  have h := dil_lower D x κ hκ hlow w
  rw [hHw, norm_smul, mul_pow] at h
  have hw2 : 0 < ‖w‖ ^ 2 := by positivity
  have h2 : (1 / κ) ^ 2 ≤ ‖c‖ ^ 2 := le_of_mul_le_mul_right h hw2
  exact (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).mp h2

/-- The threshold of Lemma `qls:lem:walk` for this instance: `t* = 1/(√s (2κ + 1))`. -/
theorem tStar_eq (κ : ℝ) (hκ : 1 ≤ κ) (hs : 0 < (s : ℝ)) :
    WalkGap.tStar (Real.sqrt (s : ℝ)) 1 (Real.sqrt (s : ℝ)) (1 / κ) =
      1 / (Real.sqrt (s : ℝ) * (2 * κ + 1)) := by
  have hq : 0 < Real.sqrt (s : ℝ) := Real.sqrt_pos.mpr hs
  have hk : 0 < κ := by linarith
  unfold WalkGap.tStar
  field_simp
  ring

/-- **The inverse bound of the enlarged matrix** (eq. `qls:eq:separate-inverse`):
`‖v‖ ≤ 4 √s κ ‖B v‖` for every `v`. -/
theorem enlarged_inverse (D : NativeSparseBlockEncoding.Data X n Z s) (x : X)
    (hA1 : ‖SparseStateOverlap.matrixOperator (D.matrix x)‖ ≤ 1) (κ : ℝ) (hκ : 1 ≤ κ)
    (hlow : ∀ v, ‖v‖ ≤ κ * ‖SparseStateOverlap.matrixOperator (D.matrix x) v‖)
    (v : SparseEdgeMoments.OrientedSpace n) :
    ‖v‖ ≤ 4 * Real.sqrt (s : ℝ) * κ * ‖enlarged (hyp D x hA1) v‖ := by
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast D.slots_pos
  have hs : (0 : ℝ) < s := by linarith
  have hq : 0 < Real.sqrt (s : ℝ) := Real.sqrt_pos.mpr hs
  have hq2 : Real.sqrt (s : ℝ) ^ 2 = s := Real.sq_sqrt hs.le
  have hk : 0 < κ := by linarith
  have hlower := enlarged_lower (hyp D x hA1) (1 / κ) (by positivity)
    (dil_gap D x κ hκ hlow) (dil_injective D x κ hκ hlow) v
  rw [tStar_eq κ hκ hs] at hlower
  set t := 1 / (Real.sqrt (s : ℝ) * (2 * κ + 1)) with ht
  have htpos : 0 < t := by positivity
  have ht2 : t ^ 2 * (s * (2 * κ + 1) ^ 2) = 1 := by
    rw [ht, div_pow, one_pow, mul_pow, hq2]
    field_simp
  have hroot : 0 < Real.sqrt (1 + t ^ 2) := Real.sqrt_pos.mpr (by positivity)
  -- `√(1 + t²) ≤ 4 √s κ t`
  have hsq : Real.sqrt (1 + t ^ 2) ≤ 4 * Real.sqrt (s : ℝ) * κ * t := by
    rw [Real.sqrt_le_left (by positivity)]
    have h4 : (4 * Real.sqrt (s : ℝ) * κ * t) ^ 2 = 16 * s * κ ^ 2 * t ^ 2 := by
      rw [mul_pow, mul_pow, mul_pow, hq2]; ring
    rw [h4]
    nlinarith [mul_le_mul_of_nonneg_left hs1 (sq_nonneg (t * κ)), sq_nonneg (κ - 1),
      mul_nonneg (sq_nonneg t) (sub_nonneg.mpr hκ), sq_nonneg t]
  have hb : 1 ≤ 4 * Real.sqrt (s : ℝ) * κ * (t / Real.sqrt (1 + t ^ 2)) := by
    rw [← mul_div_assoc, le_div_iff₀ hroot, one_mul]
    exact hsq
  calc ‖v‖ = 1 * ‖v‖ := (one_mul _).symm
    _ ≤ 4 * Real.sqrt (s : ℝ) * κ * (t / Real.sqrt (1 + t ^ 2)) * ‖v‖ :=
        mul_le_mul_of_nonneg_right hb (norm_nonneg v)
    _ = 4 * Real.sqrt (s : ℝ) * κ * (t / Real.sqrt (1 + t ^ 2) * ‖v‖) := by ring
    _ ≤ 4 * Real.sqrt (s : ℝ) * κ * ‖enlarged (hyp D x hA1) v‖ :=
        mul_le_mul_of_nonneg_left hlower (by positivity)

/-- The dilated solution `(0, z)`. -/
def lift (z : V0) : Dbl := WithLp.toLp 2 (0, z)

/-- The dilated right-hand side `(b, 0)`. -/
def rhs (b : V0) : Dbl := WithLp.toLp 2 (b, 0)

omit [DecidableEq n] in
theorem norm_lift (z : V0) : ‖lift z‖ = ‖z‖ := by
  rw [lift, WithLp.prod_norm_eq_of_L2]
  simp

omit [DecidableEq n] in
theorem norm_rhs (b : V0) : ‖rhs b‖ = ‖b‖ := by
  rw [rhs, WithLp.prod_norm_eq_of_L2]
  simp

/-- `H (0, z) = (A z, 0)`. -/
theorem dil_lift (D : NativeSparseBlockEncoding.Data X n Z s) (x : X) (z : V0) :
    dil D x (lift z) = rhs (SparseStateOverlap.matrixOperator (D.matrix x) z) := by
  simp [dil, lift, rhs]

/-- The enlarged solution `y = -2i√s R₀ J (0, z)`. -/
def solution (D : NativeSparseBlockEncoding.Data X n Z s) (x : X) (z : V0) :
    SparseEdgeMoments.OrientedSpace n :=
  solScale (Real.sqrt (s : ℝ)) •
    WalkGap.resolvent (FixedNativeCayleySimulation.generator D x) (bdry D (lift z))

/-- **The enlarged solution** solves `B y = J (A z, 0)`. -/
theorem enlarged_solution_eq (D : NativeSparseBlockEncoding.Data X n Z s) (x : X)
    (hA1 : ‖SparseStateOverlap.matrixOperator (D.matrix x)‖ ≤ 1) (z : V0) :
    enlarged (hyp D x hA1) (solution D x z) =
      bdry D (rhs (SparseStateOverlap.matrixOperator (D.matrix x) z)) := by
  rw [solution, enlarged_solution, dil_lift]

/-- **The enlarged solution norm**: `s ‖z‖² ≤ ‖y‖² ≤ 2 s ‖z‖²`. -/
theorem solution_norm_bounds (D : NativeSparseBlockEncoding.Data X n Z s) (x : X)
    (hA1 : ‖SparseStateOverlap.matrixOperator (D.matrix x)‖ ≤ 1) (z : V0) :
    (s : ℝ) * ‖z‖ ^ 2 ≤ ‖solution D x z‖ ^ 2 ∧ ‖solution D x z‖ ^ 2 ≤ 2 * (s : ℝ) * ‖z‖ ^ 2 := by
  have h := hyp D x hA1
  have hn := solution_norm_sq h (lift z)
  have hm := h.moment (lift z)
  have hq2 : Real.sqrt (s : ℝ) ^ 2 = s := Real.sq_sqrt (Nat.cast_nonneg s)
  rw [hq2, norm_lift] at hn
  rw [norm_lift, one_mul] at hm
  rw [solution, hn]
  have hs : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  constructor
  · nlinarith [sq_nonneg ‖FixedNativeCayleySimulation.generator D x (bdry D (lift z))‖]
  · nlinarith

theorem solution_norm_lower (D : NativeSparseBlockEncoding.Data X n Z s) (x : X)
    (hA1 : ‖SparseStateOverlap.matrixOperator (D.matrix x)‖ ≤ 1) (z : V0) :
    Real.sqrt (s : ℝ) * ‖z‖ ≤ ‖solution D x z‖ := by
  have h := (solution_norm_bounds D x hA1 z).1
  have hq2 : Real.sqrt (s : ℝ) ^ 2 = s := Real.sq_sqrt (Nat.cast_nonneg s)
  apply le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _)
  rw [mul_pow, hq2]
  exact h

theorem solution_norm_upper (D : NativeSparseBlockEncoding.Data X n Z s) (x : X)
    (hA1 : ‖SparseStateOverlap.matrixOperator (D.matrix x)‖ ≤ 1) (z : V0) :
    ‖solution D x z‖ ≤ Real.sqrt 2 * (Real.sqrt (s : ℝ) * ‖z‖) := by
  have h := (solution_norm_bounds D x hA1 z).2
  have hq2 : Real.sqrt (s : ℝ) ^ 2 = s := Real.sq_sqrt (Nat.cast_nonneg s)
  have h22 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  apply le_of_pow_le_pow_left₀ two_ne_zero (by positivity)
  rw [mul_pow, mul_pow, hq2, h22]
  linarith

/-- The final decoder `T = π₂ J† C`: undo `J`, select the lower data block. -/
def decodeMap (D : NativeSparseBlockEncoding.Data X n Z s) (x : X)
    (hA1 : ‖SparseStateOverlap.matrixOperator (D.matrix x)‖ ≤ 1) :
    SparseEdgeMoments.OrientedSpace n →L[ℂ] V0 :=
  WithLp.sndL 2 ℂ V0 V0 ∘L (bdry D)† ∘L decoder (hyp D x hA1)

/-- **The decoded solution**: `T y = -i√s z`. -/
theorem decode_solution (D : NativeSparseBlockEncoding.Data X n Z s) (x : X)
    (hA1 : ‖SparseStateOverlap.matrixOperator (D.matrix x)‖ ≤ 1) (z : V0) :
    decodeMap D x hA1 (solution D x z) = (-Complex.I * (Real.sqrt (s : ℝ) : ℂ)) • z := by
  rw [decodeMap, comp_apply, comp_apply, solution, decoder_solution, map_smul,
    WalkGap.isometry_apply (hyp D x hA1).isometry, map_smul]
  rfl

/-- The decoder `T` is a contraction. -/
theorem decode_norm_le (D : NativeSparseBlockEncoding.Data X n Z s) (x : X)
    (hA1 : ‖SparseStateOverlap.matrixOperator (D.matrix x)‖ ≤ 1)
    (v : SparseEdgeMoments.OrientedSpace n) : ‖decodeMap D x hA1 v‖ ≤ ‖v‖ := by
  have h := hyp D x hA1
  rw [decodeMap, comp_apply, comp_apply]
  set w := ((bdry D)†) (decoder h v)
  have h1 : ‖WithLp.sndL 2 ℂ V0 V0 w‖ ≤ ‖w‖ := by
    change ‖w.snd‖ ≤ ‖w‖
    rw [WithLp.prod_norm_eq_of_L2]
    exact Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg ‖w.fst‖])
  have h2 : ‖w‖ ≤ ‖decoder h v‖ := by
    have hJ : ‖(bdry D)†‖ ≤ 1 := by
      rw [adjoint.norm_map]
      exact (bdry D).opNorm_le_bound zero_le_one (fun u => by
        rw [WalkGap.isometry_norm h.isometry, one_mul])
    exact (le_opNorm _ _).trans (by nlinarith [norm_nonneg (decoder h v)])
  exact h1.trans (h2.trans (decoder_norm_le h v))

/-- **Estimate transfer** (eq. `qls:eq:separate-transferred-estimate`). If
`‖z‖/2 ≤ ν̂ ≤ 2 ‖z‖`, then `ν̂_B = (9/8) √s ν̂` lies in `[3/8, 5/2] · ‖y‖`. -/
theorem estimate_transfer (D : NativeSparseBlockEncoding.Data X n Z s) (x : X)
    (hA1 : ‖SparseStateOverlap.matrixOperator (D.matrix x)‖ ≤ 1) (z : V0) (νh : ℝ)
    (hlo : ‖z‖ / 2 ≤ νh) (hhi : νh ≤ 2 * ‖z‖) :
    3 / 8 * ‖solution D x z‖ ≤ 9 / 8 * Real.sqrt (s : ℝ) * νh ∧
      9 / 8 * Real.sqrt (s : ℝ) * νh ≤ 5 / 2 * ‖solution D x z‖ := by
  have hlower := solution_norm_lower D x hA1 z
  have hupper := solution_norm_upper D x hA1 z
  have hq : 0 ≤ Real.sqrt (s : ℝ) := Real.sqrt_nonneg _
  have hz : 0 ≤ ‖z‖ := norm_nonneg z
  have h2 : Real.sqrt 2 ≤ 3 / 2 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  constructor
  · have : 3 / 8 * ‖solution D x z‖ ≤ 3 / 8 * (Real.sqrt 2 * (Real.sqrt (s : ℝ) * ‖z‖)) := by
      linarith
    nlinarith [mul_nonneg hq hz]
  · nlinarith [mul_nonneg hq hz]

/-- **The ratio bound**: `1 + κ_B/ν̂_B ≤ (73/9) κ/‖z‖` when `‖z‖/2 ≤ ν̂` and `‖z‖ ≤ κ`. -/
theorem ratio_bound (κ νh ν : ℝ) (hs : (1 : ℝ) ≤ s) (hν : 0 < ν) (hνκ : ν ≤ κ)
    (hlo : ν / 2 ≤ νh) :
    1 + 4 * Real.sqrt (s : ℝ) * κ / (9 / 8 * Real.sqrt (s : ℝ) * νh) ≤ 73 / 9 * (κ / ν) := by
  have hq : 0 < Real.sqrt (s : ℝ) := Real.sqrt_pos.mpr (by linarith)
  have hνh : 0 < νh := by linarith
  have hk : 0 < κ := by linarith
  have e : 4 * Real.sqrt (s : ℝ) * κ / (9 / 8 * Real.sqrt (s : ℝ) * νh) = 32 / 9 * (κ / νh) := by
    field_simp
    ring
  rw [e]
  have h1 : κ / νh ≤ 2 * (κ / ν) := by
    rw [div_le_iff₀ hνh]
    have : κ / ν * ν = κ := div_mul_cancel₀ κ hν.ne'
    nlinarith [div_pos hk hν]
  have h2 : 1 ≤ κ / ν := by rw [le_div_iff₀ hν]; linarith
  nlinarith

end

end SparseLinearSystems.Separate
