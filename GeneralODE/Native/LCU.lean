import GeneralODE.Native.Spectral
import SparseHamiltonian.WeightedClock

/-!
# Linear combinations of a selected family

For complex coefficients `c` with `∑ ‖c_i‖ = 1` the unit vectors
`a_i = √‖c_i‖` and `b_i = conj(c_i)/√‖c_i‖` satisfy `conj(b_i) a_i = c_i`.
With the branch states `v ↦ ∑_i a_i |i⟩ ⊗ v`, the block of a branch-diagonal
operator `diag(G_i)` is `∑_i conj(b_i) a_i G_i`.
-/

namespace SparseHamiltonian.GeneralODE.LCU

noncomputable section
open ContinuousLinearMap
open scoped BigOperators InnerProduct ComplexConjugate

variable {ι : Type*} [Fintype ι]

/-- Input amplitudes `√‖c_i‖`. -/
def lcuIn (c : ι → ℂ) : EuclideanSpace ℂ ι :=
  WithLp.toLp 2 (fun i => ((Real.sqrt ‖c i‖ : ℝ) : ℂ))

/-- Output amplitudes `conj(c_i)/√‖c_i‖`. -/
def lcuOut (c : ι → ℂ) : EuclideanSpace ℂ ι :=
  WithLp.toLp 2 (fun i => if c i = 0 then 0 else conj (c i) / ((Real.sqrt ‖c i‖ : ℝ) : ℂ))

omit [Fintype ι] in
theorem lcu_pair (c : ι → ℂ) (i : ι) : conj (lcuOut c i) * lcuIn c i = c i := by
  change conj (if c i = 0 then 0 else conj (c i) / ((Real.sqrt ‖c i‖ : ℝ) : ℂ)) *
    ((Real.sqrt ‖c i‖ : ℝ) : ℂ) = c i
  split_ifs with h
  · simp [h]
  · have hs : 0 < Real.sqrt ‖c i‖ := Real.sqrt_pos.mpr (norm_pos_iff.mpr h)
    have hs' : ((Real.sqrt ‖c i‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    rw [map_div₀, Complex.conj_conj, Complex.conj_ofReal]
    field_simp

theorem norm_sq_lcuIn (c : ι → ℂ) : ‖lcuIn c‖ ^ 2 = ∑ i, ‖c i‖ := by
  rw [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro i _
  simp only [lcuIn, PiLp.toLp_apply, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  exact Real.sq_sqrt (norm_nonneg _)

theorem norm_sq_lcuOut (c : ι → ℂ) : ‖lcuOut c‖ ^ 2 = ∑ i, ‖c i‖ := by
  rw [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro i _
  simp only [lcuOut, PiLp.toLp_apply]
  split_ifs with h
  · simp [h]
  · have hs : 0 < Real.sqrt ‖c i‖ := Real.sqrt_pos.mpr (norm_pos_iff.mpr h)
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs, RCLike.norm_conj, div_pow,
      Real.sq_sqrt (norm_nonneg _), sq]
    field_simp

theorem norm_lcuIn (c : ι → ℂ) (hc : ∑ i, ‖c i‖ = 1) : ‖lcuIn c‖ = 1 := by
  have h := norm_sq_lcuIn c
  rw [hc] at h
  have h0 := norm_nonneg (lcuIn c)
  nlinarith [sq_nonneg (‖lcuIn c‖ - 1)]

theorem norm_lcuOut (c : ι → ℂ) (hc : ∑ i, ‖c i‖ = 1) : ‖lcuOut c‖ = 1 := by
  have h := norm_sq_lcuOut c
  rw [hc] at h
  have h0 := norm_nonneg (lcuOut c)
  nlinarith [sq_nonneg (‖lcuOut c‖ - 1)]

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [FiniteDimensional ℂ P]

/-- Branch state `v ↦ (a_i v)_i`. -/
def branchState (a : EuclideanSpace ℂ ι) : P →L[ℂ] PiLp 2 (fun _ : ι => P) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => WithLp.toLp 2 (fun i => a i • v)
      map_add' := by intro v w; ext i; simp [smul_add]
      map_smul' := by intro z v; ext i; simp [smul_smul, mul_comm] }

@[simp] theorem branchState_apply (a : EuclideanSpace ℂ ι) (v : P) (i : ι) :
    branchState a v i = a i • v := rfl

/-- The adjoint of a branch state. -/
def branchCostate (a : EuclideanSpace ℂ ι) : PiLp 2 (fun _ : ι => P) →L[ℂ] P :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => ∑ i, conj (a i) • w i
      map_add' := by intro v w; simp [smul_add, Finset.sum_add_distrib]
      map_smul' := by intro z v; simp [Finset.smul_sum, smul_smul, mul_comm] }

theorem branchCostate_apply (a : EuclideanSpace ℂ ι) (w : PiLp 2 (fun _ : ι => P)) :
    branchCostate a w = ∑ i, conj (a i) • w i := rfl

theorem branchState_adjoint (a : EuclideanSpace ℂ ι) :
    (branchState (P := P) a)† = branchCostate a := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro w v
  rw [branchCostate_apply, PiLp.inner_apply, sum_inner]
  apply Finset.sum_congr rfl
  intro i _
  rw [branchState_apply, inner_smul_left, inner_smul_right, Complex.conj_conj]

theorem branchState_isometry (a : EuclideanSpace ℂ ι) (ha : ‖a‖ = 1) :
    (branchState (P := P) a)† ∘L branchState a = 1 := by
  rw [branchState_adjoint]
  ext1 v
  rw [comp_apply, branchCostate_apply, one_apply_eq_self]
  simp only [branchState_apply, smul_smul]
  rw [← Finset.sum_smul]
  have h : ∑ i, conj (a i) * a i = 1 := by
    have hsq : ‖a‖ ^ 2 = 1 := by rw [ha]; norm_num
    rw [EuclideanSpace.norm_sq_eq] at hsq
    have : ∑ i, conj (a i) * a i = ((∑ i, ‖a i‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      apply Finset.sum_congr rfl
      intro i _
      rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
      push_cast
      ring
    rw [this, hsq]
    simp
  rw [h, one_smul]

/-- The block of a branch-diagonal operator between branch states. -/
theorem branch_block (a b : EuclideanSpace ℂ ι) (G : ι → (P →L[ℂ] P)) :
    (branchState (P := P) b)† ∘L WeightedClock.diagonal (V := fun _ : ι => P) G ∘L
        branchState a =
      ∑ i, (conj (b i) * a i) • G i := by
  rw [branchState_adjoint]
  ext1 v
  rw [comp_apply, comp_apply, branchCostate_apply, sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [WeightedClock.diagonal_apply, branchState_apply, map_smul, smul_smul, smul_apply]

end

end SparseHamiltonian.GeneralODE.LCU
