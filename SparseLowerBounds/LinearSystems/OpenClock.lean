import SparseLowerBounds.Helpers.OpenClock.MatrixNorm

set_option synthInstance.maxHeartbeats 400000

section
/-!
# The open computation clock and its Hermitian dilation

Manuscript: the proof of Theorem `qlsl:thm:main`. On clock states `|0⟩, …, |T-1⟩` and a register
`ℂ^ι`, transitions `L_t` (`L : ℕ → Matrix ι ι ℂ`; only `t ≤ T - 2` is used)
define

  `T_L = Σ_{t=0}^{T-2} |t+1⟩⟨t| ⊗ L_t`   (`clockShift`),
  `C = (I - r T_L)/2`                    (`clockMatrix`, eq. `qlsl:eq:C`).

For the hard instance `T = 2n`, `L_t = U_{j_t}` for `t < n` and `L_t = I`
afterwards (`Instance`). Facts proved here hold for arbitrary contractive or
unitary transitions:

* `‖C‖ ≤ (1+r)/2` and `‖(I - rT)v‖ ≥ (1-r)‖v‖`, hence `‖C⁻¹‖ ≤ 2/(1-r) = 2R`
  (eq. `qlsl:eq:Cpromise`);
* `T^T = 0`, so `C` is invertible with the finite Neumann series
  `C⁻¹ = 2 Σ_{k<T} r^k T^k`, and the history state
  `C⁻¹ (|0⟩ ⊗ ψ) = 2 Σ_t r^t |t⟩ ⊗ ψ_t`, `ψ_t = L_{t-1} ⋯ L_0 ψ`
  (`walk`, eq. `qlsl:eq:history`);
* the answer-region weight `Σ_{t=n}^{2n-1} r^{2t} / Σ_{t<2n} r^{2t} = r^{2n}/(1+r^{2n})`
  (eq. `qlsl:eq:p`);
* the Hermitian dilation `A = [[0, C], [Cᴴ, 0]]` (`dilation`, eq.
  `qlsl:eq:hermitian`): Hermitian, `‖A‖ = ‖C‖`, `‖A⁻¹‖ = ‖C⁻¹‖`,
  `A⁻¹ (b₀, 0) = (0, C⁻¹ b₀)`. For real `C`, `Cᴴ = Cᵀ` as in the manuscript.

Matrices carry the `L²` operator norm (`Matrix.Norms.L2Operator`).
-/

namespace SparseLowerBounds.LinearSystems

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `T_L = Σ_t |t+1⟩⟨t| ⊗ L_t` on `Fin T × ι` (proof of Theorem `qlsl:thm:main`). -/
def clockShift (T : ℕ) (L : ℕ → Matrix ι ι ℂ) : Matrix (Fin T × ι) (Fin T × ι) ℂ :=
  Matrix.of fun p q => if (p.1 : ℕ) = q.1 + 1 then L q.1 p.2 q.2 else 0

/-- **Eq. `qlsl:eq:C`** (eq. `qlsl:eq:C`): `C = (I - r T_L)/2`. -/
def clockMatrix (T : ℕ) (r : ℝ) (L : ℕ → Matrix ι ι ℂ) : Matrix (Fin T × ι) (Fin T × ι) ℂ :=
  (2 : ℂ)⁻¹ • (1 - (r : ℂ) • clockShift T L)

/-- The vector `|t⟩ ⊗ ψ` (zero if `t ≥ T`). -/
def atClock (T t : ℕ) (ψ : ι → ℂ) : Fin T × ι → ℂ :=
  fun p => if (p.1 : ℕ) = t then ψ p.2 else 0

/-- The register state after `t` transitions, `ψ_t = L_{t-1} ⋯ L_0 ψ`. -/
def walk (L : ℕ → Matrix ι ι ℂ) (ψ : ι → ℂ) : ℕ → ι → ℂ
  | 0 => ψ
  | t + 1 => L t *ᵥ walk L ψ t

open OpenClock

variable {T : ℕ} {L : ℕ → Matrix ι ι ℂ}

/-! ### The clock shift -/

namespace OpenClock

/-- `T_L^k` only moves the clock forward by exactly `k`. -/
theorem clockShift_pow_apply_eq_zero (k : ℕ) (p q : Fin T × ι)
    (h : (p.1 : ℕ) ≠ q.1 + k) : (clockShift T L ^ k) p q = 0 := by
  induction k generalizing p with
  | zero =>
    rw [pow_zero, Matrix.one_apply_ne]
    rintro rfl
    exact h rfl
  | succ k ih =>
    rw [pow_succ', Matrix.mul_apply]
    refine Finset.sum_eq_zero fun s _ => ?_
    by_cases hs : (p.1 : ℕ) = s.1 + 1
    · rw [ih s (by omega), mul_zero]
    · simp [clockShift, hs]

omit [DecidableEq ι] in
/-- One step of the clock: `T_L (|t⟩ ⊗ ψ) = |t+1⟩ ⊗ L_t ψ`. -/
theorem clockShift_mulVec_atClock (t : ℕ) (ψ : ι → ℂ) :
    clockShift T L *ᵥ atClock T t ψ = atClock T (t + 1) (L t *ᵥ ψ) := by
  funext p
  simp only [Matrix.mulVec, dotProduct, clockShift, atClock, Matrix.of_apply,
    Fintype.sum_prod_type]
  by_cases hp : (p.1 : ℕ) = t + 1
  · have ht : t < T := by have := p.1.isLt; omega
    rw [if_pos hp, Finset.sum_eq_single (⟨t, ht⟩ : Fin T)]
    · simp [hp]
    · intro s _ hs
      have hs' : (s : ℕ) ≠ t := fun h => hs (Fin.ext h)
      simp [hs']
    · simp
  · rw [if_neg hp]
    refine Finset.sum_eq_zero fun s _ => Finset.sum_eq_zero fun j _ => ?_
    by_cases hs : (s : ℕ) = t
    · simp [hs, hp]
    · simp [hs]

/-- The clock-`t` block of a vector (zero for `t ≥ T`). -/
def blk (x : Fin T × ι → ℂ) (t : ℕ) : ι → ℂ :=
  fun i => if h : t < T then x (⟨t, h⟩, i) else 0

omit [DecidableEq ι] in
theorem norm_sq_eq_sum_blk (x : Fin T × ι → ℂ) :
    ‖WithLp.toLp 2 x‖ ^ 2 = ∑ t ∈ Finset.range T, ‖WithLp.toLp 2 (blk x t)‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type,
    ← Fin.sum_univ_eq_sum_range (fun t => ‖WithLp.toLp 2 (blk x t)‖ ^ 2)]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [EuclideanSpace.norm_sq_eq]
  simp [blk, t.isLt]

omit [DecidableEq ι] in
theorem blk_clockShift_zero (x : Fin T × ι → ℂ) : blk (clockShift T L *ᵥ x) 0 = 0 := by
  funext i
  simp only [blk]
  split_ifs with h
  · simp [Matrix.mulVec, dotProduct, clockShift]
  · rfl

omit [DecidableEq ι] in
theorem blk_clockShift_succ (x : Fin T × ι → ℂ) (t : ℕ) (ht : t + 1 < T) :
    blk (clockShift T L *ᵥ x) (t + 1) = L t *ᵥ blk x t := by
  funext i
  have ht' : t < T := by omega
  simp only [blk, dif_pos ht]
  simp only [Matrix.mulVec, dotProduct, clockShift, Matrix.of_apply, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single (⟨t, ht'⟩ : Fin T)]
  · simp [blk, ht']
  · intro s _ hs
    have hs' : t ≠ (s : ℕ) := fun h => hs (Fin.ext h.symm)
    simp [hs']
  · simp

theorem norm_toLp_clockShift_mulVec_le (hL : ∀ t, ‖L t‖ ≤ 1) (x : Fin T × ι → ℂ) :
    ‖WithLp.toLp 2 (clockShift T L *ᵥ x)‖ ≤ ‖WithLp.toLp 2 x‖ := by
  refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
  rw [norm_sq_eq_sum_blk, norm_sq_eq_sum_blk]
  cases T with
  | zero => simp
  | succ T' =>
    rw [Finset.sum_range_succ', Finset.sum_range_succ, blk_clockShift_zero]
    have hle : ∑ t ∈ Finset.range T', ‖WithLp.toLp 2 (blk (clockShift (T' + 1) L *ᵥ x) (t + 1))‖ ^ 2
        ≤ ∑ t ∈ Finset.range T', ‖WithLp.toLp 2 (blk x t)‖ ^ 2 := by
      refine Finset.sum_le_sum fun t ht => ?_
      have ht' : t + 1 < T' + 1 := by simp at ht; omega
      rw [blk_clockShift_succ x t ht']
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_toLp_mulVec_le_self (hL t) _) 2
    have h0 : ‖WithLp.toLp 2 (0 : ι → ℂ)‖ ^ 2 = 0 := by simp
    rw [h0, add_zero]
    exact hle.trans (le_add_of_nonneg_right (sq_nonneg _))

end OpenClock

/-- The clock is open: `T_L^T = 0` (proof of Theorem `qlsl:thm:main`). -/
theorem clockShift_pow_self : clockShift T L ^ T = 0 := by
  ext p q
  rw [clockShift_pow_apply_eq_zero T p q (by have := p.1.isLt; omega)]
  rfl

/-- `T_L^k (|0⟩ ⊗ ψ) = |k⟩ ⊗ ψ_k` (zero once `k ≥ T`). -/
theorem clockShift_pow_mulVec_atClock (k : ℕ) (ψ : ι → ℂ) :
    clockShift T L ^ k *ᵥ atClock T 0 ψ = atClock T k (walk L ψ k) := by
  induction k with
  | zero => simp [walk]
  | succ k ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih, clockShift_mulVec_atClock]
    rfl

/-- `‖T_L‖ ≤ 1` for contractive transitions (a partial isometry for unitary ones). -/
theorem norm_clockShift_le (hL : ∀ t, ‖L t‖ ≤ 1) : ‖clockShift T L‖ ≤ 1 := by
  exact norm_le_of_mulVec zero_le_one fun w =>
    (norm_toLp_clockShift_mulVec_le hL w).trans_eq (one_mul _).symm

/-- **Eq. `qlsl:eq:Cpromise`**, first part: `‖C‖ ≤ (1+r)/2`. -/
theorem norm_clockMatrix_le {r : ℝ} (hr : 0 ≤ r) (hL : ∀ t, ‖L t‖ ≤ 1) :
    ‖clockMatrix T r L‖ ≤ (1 + r) / 2 := by
  rw [clockMatrix, norm_smul]
  have h2 : ‖(2 : ℂ)⁻¹‖ = 1 / 2 := by simp
  have hsub : ‖(1 : Matrix (Fin T × ι) (Fin T × ι) ℂ) - (r : ℂ) • clockShift T L‖ ≤ 1 + r := by
    refine (norm_sub_le _ _).trans (add_le_add norm_one_le ?_)
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hr]
    exact (mul_le_mul_of_nonneg_left (norm_clockShift_le hL) hr).trans_eq (mul_one r)
  rw [h2]
  linarith

/-- `‖(I - r T_L) v‖ ≥ (1 - r) ‖v‖` (proof of Theorem `qlsl:thm:main`). -/
theorem le_norm_one_sub_smul_clockShift {r : ℝ} (hr : 0 ≤ r) (hL : ∀ t, ‖L t‖ ≤ 1)
    (v : EuclideanSpace ℂ (Fin T × ι)) :
    (1 - r) * ‖v‖ ≤ ‖Matrix.toEuclideanLin (1 - (r : ℂ) • clockShift T L) v‖ := by
  have hcoe : Matrix.toEuclideanLin (1 - (r : ℂ) • clockShift T L) v =
      Matrix.toEuclideanCLM (n := Fin T × ι) (𝕜 := ℂ) (1 - (r : ℂ) • clockShift T L) v := rfl
  rw [hcoe, map_sub, map_one, map_smul, _root_.sub_apply, one_apply_eq_self, _root_.smul_apply]
  have hT : ‖Matrix.toEuclideanCLM (n := Fin T × ι) (𝕜 := ℂ) (clockShift T L) v‖ ≤ ‖v‖ := by
    have := norm_toLp_mulVec_le_self (norm_clockShift_le hL) (WithLp.ofLp v)
    rwa [WithLp.toLp_ofLp] at this
  have hs : ‖(r : ℂ) • Matrix.toEuclideanCLM (n := Fin T × ι) (𝕜 := ℂ) (clockShift T L) v‖
      ≤ r * ‖v‖ := by
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hr]
    exact mul_le_mul_of_nonneg_left hT hr
  have := norm_sub_norm_le v ((r : ℂ) • Matrix.toEuclideanCLM (n := Fin T × ι) (𝕜 := ℂ)
    (clockShift T L) v)
  linarith

namespace OpenClock

/-- `(I - r T_L) · Σ_{k<T} r^k T_L^k = I`. -/
theorem one_sub_mul_neumann (r : ℝ) :
    (1 - (r : ℂ) • clockShift T L) *
      ∑ k ∈ Finset.range T, (r : ℂ) ^ k • clockShift T L ^ k = 1 := by
  simp_rw [← smul_pow]
  rw [mul_neg_geom_sum, smul_pow, clockShift_pow_self, smul_zero, sub_zero]

theorem clockMatrix_mul_neumann (r : ℝ) :
    clockMatrix T r L *
      ((2 : ℂ) • ∑ k ∈ Finset.range T, (r : ℂ) ^ k • clockShift T L ^ k) = 1 := by
  rw [clockMatrix, Matrix.smul_mul, Matrix.mul_smul, one_sub_mul_neumann, smul_smul]
  norm_num

end OpenClock

/-- The finite Neumann series `C⁻¹ = 2 Σ_{k<T} r^k T_L^k`, valid for every `r`. -/
theorem inv_clockMatrix (r : ℝ) :
    (clockMatrix T r L)⁻¹ = (2 : ℂ) • ∑ k ∈ Finset.range T, (r : ℂ) ^ k • clockShift T L ^ k := by
  exact Matrix.inv_eq_right_inv (clockMatrix_mul_neumann r)

/-- `C` is invertible for every `r` (its shift part is nilpotent). -/
theorem isUnit_clockMatrix (r : ℝ) : IsUnit (clockMatrix T r L) := by
  exact (Matrix.isUnit_iff_isUnit_det _).mpr
    (Matrix.isUnit_det_of_right_inverse (clockMatrix_mul_neumann r))

/-- **Eq. `qlsl:eq:Cpromise`**, second part:
`σ_min(C) ≥ (1-r)/2`, i.e. `‖C⁻¹‖ ≤ 2/(1-r)` (`= 2R` for `r = 1 - 1/R`). -/
theorem norm_inv_clockMatrix_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (hL : ∀ t, ‖L t‖ ≤ 1) :
    ‖(clockMatrix T r L)⁻¹‖ ≤ 2 / (1 - r) := by
  rw [inv_clockMatrix, norm_smul, show ‖(2 : ℂ)‖ = 2 by simp]
  have hsum : ‖∑ k ∈ Finset.range T, (r : ℂ) ^ k • clockShift T L ^ k‖ ≤ 1 / (1 - r) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ k ∈ Finset.range T, ‖(r : ℂ) ^ k • clockShift T L ^ k‖
        ≤ ∑ k ∈ Finset.range T, r ^ k := by
          refine Finset.sum_le_sum fun k _ => ?_
          rw [norm_smul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hr0]
          exact (mul_le_mul_of_nonneg_left (norm_pow_le_one (norm_clockShift_le hL) k)
            (pow_nonneg hr0 k)).trans_eq (mul_one _)
      _ ≤ 1 / (1 - r) := by
          rw [le_div_iff₀ (by linarith), mul_comm, mul_neg_geom_sum]
          linarith [pow_nonneg hr0 T]
  exact (mul_le_mul_of_nonneg_left hsum zero_le_two).trans_eq (mul_one_div _ _)

/-- **Eq. `qlsl:eq:history`** (proof of Theorem `qlsl:thm:main`):
`C⁻¹ (|0⟩ ⊗ ψ) = 2 Σ_{t<T} r^t |t⟩ ⊗ ψ_t`. -/
theorem history (r : ℝ) (ψ : ι → ℂ) :
    (clockMatrix T r L)⁻¹ *ᵥ atClock T 0 ψ =
      (2 : ℂ) • ∑ t ∈ Finset.range T, (r : ℂ) ^ t • atClock T t (walk L ψ t) := by
  rw [inv_clockMatrix, Matrix.smul_mulVec, Matrix.sum_mulVec]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by rw [Matrix.smul_mulVec, clockShift_pow_mulVec_atClock]

/-- Unitary transitions keep every `ψ_t` normalised (proof of Theorem `qlsl:thm:main`). -/
theorem norm_walk (hL : ∀ t, L t ∈ Matrix.unitaryGroup ι ℂ) (ψ : ι → ℂ) (t : ℕ) :
    ‖WithLp.toLp 2 (walk L ψ t)‖ = ‖WithLp.toLp 2 ψ‖ := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [← ih]
    have hU : Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) (L t) ∈
        unitary (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) :=
      Unitary.map_mem _ (hL t)
    exact ContinuousLinearMap.norm_map_of_mem_unitary hU (WithLp.toLp 2 (walk L ψ t))

/-- **Eq. `qlsl:eq:p`** (proof of Theorem `qlsl:thm:main`), the geometric-sum identity behind it:
`Σ_{t=n}^{2n-1} r^{2t} = r^{2n}/(1+r^{2n}) · Σ_{t<2n} r^{2t}`. -/
theorem answer_weight (r : ℝ) (n : ℕ) :
    ∑ t ∈ Finset.Ico n (2 * n), r ^ (2 * t) =
      r ^ (2 * n) / (1 + r ^ (2 * n)) * ∑ t ∈ Finset.range (2 * n), r ^ (2 * t) := by
  have hshift : ∀ k, r ^ (2 * (n + k)) = r ^ (2 * n) * r ^ (2 * k) := fun k => by
    rw [mul_add, pow_add]
  have hIco : ∑ t ∈ Finset.Ico n (2 * n), r ^ (2 * t) =
      r ^ (2 * n) * ∑ t ∈ Finset.range n, r ^ (2 * t) := by
    rw [Finset.sum_Ico_eq_sum_range, Finset.mul_sum]
    rw [show 2 * n - n = n by omega]
    exact Finset.sum_congr rfl fun k _ => hshift k
  have hrange : ∑ t ∈ Finset.range (2 * n), r ^ (2 * t) =
      (1 + r ^ (2 * n)) * ∑ t ∈ Finset.range n, r ^ (2 * t) := by
    rw [two_mul n, Finset.sum_range_add, add_mul, one_mul, Finset.mul_sum, ← two_mul n]
    congr 1
    exact Finset.sum_congr rfl fun k _ => hshift k
  have hpos : 0 < 1 + r ^ (2 * n) := by rw [pow_mul]; positivity
  rw [hIco, hrange]
  field_simp

/-! ### The Hermitian dilation (eq. `qlsl:eq:hermitian`) -/

variable {β : Type*} [Fintype β] [DecidableEq β]

/-- **Eq. `qlsl:eq:hermitian`** (proof of Theorem `qlsl:thm:main`): `A = [[0, C], [Cᴴ, 0]]`, the
first `Fin 2` index being the sector. -/
def dilation (C : Matrix β β ℂ) : Matrix (Fin 2 × β) (Fin 2 × β) ℂ :=
  Matrix.of fun p q =>
    if p.1 = 0 ∧ q.1 = 1 then C p.2 q.2
    else if p.1 = 1 ∧ q.1 = 0 then star (C q.2 p.2) else 0

/-- The sector vector `(u, v)`. -/
def sectorVec (u v : β → ℂ) : Fin 2 × β → ℂ := fun p => if p.1 = 0 then u p.2 else v p.2

namespace OpenClock

omit [Fintype β] [DecidableEq β] in
theorem sectorVec_eta (x : Fin 2 × β → ℂ) :
    sectorVec (fun b => x (0, b)) (fun b => x (1, b)) = x := by
  funext p
  rcases p with ⟨a, b⟩
  fin_cases a <;> simp [sectorVec]

omit [DecidableEq β] in
theorem dilation_mulVec_sectorVec (C : Matrix β β ℂ) (u v : β → ℂ) :
    dilation C *ᵥ sectorVec u v = sectorVec (C *ᵥ v) (Cᴴ *ᵥ u) := by
  funext p
  rcases p with ⟨a, b⟩
  fin_cases a <;>
    simp [Matrix.mulVec, dotProduct, dilation, sectorVec, Fintype.sum_prod_type,
      Fin.sum_univ_two, Matrix.conjTranspose_apply]

omit [DecidableEq β] in
theorem norm_sq_sectorVec (u v : β → ℂ) :
    ‖WithLp.toLp 2 (sectorVec u v)‖ ^ 2 =
      ‖WithLp.toLp 2 u‖ ^ 2 + ‖WithLp.toLp 2 v‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
    Fintype.sum_prod_type, Fin.sum_univ_two]
  simp [sectorVec]

theorem dilation_mul_dilation_inv {C : Matrix β β ℂ} (hC : IsUnit C) :
    dilation C * dilation (Cᴴ)⁻¹ = 1 := by
  have hCH : IsUnit Cᴴ := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_conjTranspose]
    exact ((Matrix.isUnit_iff_isUnit_det C).mp hC).star
  have h1 : C * ((Cᴴ)⁻¹)ᴴ = 1 := by
    rw [Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_conjTranspose]
    exact Matrix.mul_nonsing_inv C ((Matrix.isUnit_iff_isUnit_det C).mp hC)
  have h2 : Cᴴ * (Cᴴ)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hCH)
  refine Matrix.ext_of_mulVec_single fun i => ?_
  rw [← Matrix.mulVec_mulVec, ← sectorVec_eta (Pi.single i 1), dilation_mulVec_sectorVec,
    dilation_mulVec_sectorVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h1, h2,
    Matrix.one_mulVec, Matrix.one_mulVec, Matrix.one_mulVec]

end OpenClock

omit [Fintype β] [DecidableEq β] in
theorem isHermitian_dilation (C : Matrix β β ℂ) : Matrix.IsHermitian (dilation C) := by
  ext p q
  rcases p with ⟨a, i⟩
  rcases q with ⟨b, j⟩
  fin_cases a <;> fin_cases b <;> simp [dilation, Matrix.conjTranspose_apply]

/-- The dilation has the singular values of `C`, each twice (proof of Theorem `qlsl:thm:main`). -/
theorem norm_dilation (C : Matrix β β ℂ) : ‖dilation C‖ = ‖C‖ := by
  refine le_antisymm (norm_le_of_mulVec (norm_nonneg _) fun x => ?_) ?_
  · rw [← sectorVec_eta x, dilation_mulVec_sectorVec]
    set u : β → ℂ := fun b => x (0, b)
    set v : β → ℂ := fun b => x (1, b)
    refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp ?_
    rw [mul_pow, norm_sq_sectorVec, norm_sq_sectorVec, mul_add]
    have hv := norm_toLp_mulVec_le C v
    have hu := norm_toLp_mulVec_le Cᴴ u
    rw [Matrix.l2_opNorm_conjTranspose] at hu
    have hv2 := pow_le_pow_left₀ (norm_nonneg _) hv 2
    have hu2 := pow_le_pow_left₀ (norm_nonneg _) hu 2
    rw [mul_pow] at hv2 hu2
    linarith
  · refine norm_le_of_mulVec (norm_nonneg _) fun w => ?_
    have h := norm_toLp_mulVec_le (dilation C) (sectorVec 0 w)
    rw [dilation_mulVec_sectorVec, Matrix.mulVec_zero] at h
    have e : ∀ u : β → ℂ, ‖WithLp.toLp 2 (sectorVec u 0)‖ = ‖WithLp.toLp 2 u‖ ∧
        ‖WithLp.toLp 2 (sectorVec 0 u)‖ = ‖WithLp.toLp 2 u‖ := fun u => by
      constructor <;> rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), norm_sq_sectorVec] <;> simp
    rwa [(e _).1, (e _).2] at h

theorem isUnit_dilation {C : Matrix β β ℂ} (hC : IsUnit C) : IsUnit (dilation C) := by
  exact (Matrix.isUnit_iff_isUnit_det _).mpr
    (Matrix.isUnit_det_of_right_inverse (dilation_mul_dilation_inv hC))

theorem inv_dilation {C : Matrix β β ℂ} (hC : IsUnit C) : (dilation C)⁻¹ = dilation (Cᴴ)⁻¹ := by
  exact Matrix.inv_eq_right_inv (dilation_mul_dilation_inv hC)

theorem norm_inv_dilation {C : Matrix β β ℂ} (hC : IsUnit C) : ‖(dilation C)⁻¹‖ = ‖C⁻¹‖ := by
  rw [inv_dilation hC, norm_dilation, ← Matrix.conjTranspose_nonsing_inv,
    Matrix.l2_opNorm_conjTranspose]

/-- `A⁻¹ (b₀, 0) = (0, C⁻¹ b₀)` (proof of Theorem `qlsl:thm:main`). -/
theorem inv_dilation_mulVec_sectorVec {C : Matrix β β ℂ} (hC : IsUnit C) (b₀ : β → ℂ) :
    (dilation C)⁻¹ *ᵥ sectorVec b₀ 0 = sectorVec 0 (C⁻¹ *ᵥ b₀) := by
  rw [inv_dilation hC, dilation_mulVec_sectorVec, Matrix.mulVec_zero,
    Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_conjTranspose]

end

end SparseLowerBounds.LinearSystems
end
