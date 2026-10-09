import SparseLowerBounds.Helpers.Ode.JointFamily.Defs

set_option synthInstance.maxHeartbeats 400000

section
/-!
# Dilation stages, candidate states and the half indicator

Helper of `ODE/JointInstance` (manuscript lines 3800-3824, 3849-3850, 3887-3888).
`H_k` is a direct sum of reindexed copies of the dilation
`LinearSystems.dilation` (sector index `Bool`, see `stageHam`).

* `H_k = ⊕_a S_{j_{ak}}` is real symmetric, hence Hermitian
  (`stageHam_isHermitian`), and every row and column has squared Euclidean
  norm at most one, because the gadget `U_j` is unitary
  (`sum_norm_sq_stageHam_row`, `sum_norm_sq_stageHam_col`); its nonzero
  entries join `(a, β, b)` to `(a, ¬β, c)` (`stageHam_support`);
* each `|a, ω⟩` is an eigenvector: `H_k |a, ω⟩ = (-1)^{j_{ak}} |a, ω⟩`
  (`matrixOperator_stageHam_candState`, eq. `odel:eq:dilation`), from
  `U_j v = U_j† v = (-1)^j v` (`Hamiltonian.gadget_mulVec_alt`);
* the states `|a, ω⟩` are orthonormal, `‖x₀‖ = ‖b‖ = 1`;
* the half indicator is a self-adjoint contraction with
  `halfObs |a, ω⟩ = halfSign(a) |a, ω⟩`.
-/

namespace SparseLowerBounds.ODE

noncomputable section
open SparseHamiltonian
open scoped InnerProductSpace Matrix ComplexConjugate

variable {M n μ s : ℕ}

/-- Row `b` of `U_j v = (-1)^j v`. -/
theorem sum_gadget_mul_alt {m : ℕ} (hm : Even m) (j b : Fin m) :
    ∑ c, LinearSystems.gadget m j b c * Hamiltonian.alt m c =
      (-1 : ℂ) ^ (j : ℕ) * Hamiltonian.alt m b := by
  simpa [Matrix.mulVec, dotProduct] using congrFun (Hamiltonian.gadget_mulVec_alt hm j) b

/-- Row `b` of `U_j† v = (-1)^j v` (`U_j` is real). -/
theorem sum_gadget_mul_alt' {m : ℕ} (hm : Even m) (j b : Fin m) :
    ∑ c, LinearSystems.gadget m j c b * Hamiltonian.alt m c =
      (-1 : ℂ) ^ (j : ℕ) * Hamiltonian.alt m b := by
  have h := congrFun (Hamiltonian.conjTranspose_gadget_mulVec_alt hm j) b
  simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply,
    LinearSystems.star_gadget_apply, Pi.smul_apply, smul_eq_mul] at h
  exact h

theorem candState_inl (a a' : Fin M) (β : Bool) (c : Fin (2 ^ μ)) :
    candState M μ s a (Sum.inl (a', β, c)) =
      if a' = a then ((Real.sqrt 2 : ℂ))⁻¹ * Hamiltonian.alt (2 ^ μ) c else 0 := rfl

theorem candState_inr (a : Fin M) (t : Fin s) : candState M μ s a (Sum.inr t) = 0 := rfl

/-! ### The stage Hamiltonian -/

/-- A core row of `H_k` meets only the opposite dilation block of its candidate. -/
theorem sum_stageHam_row {R : Type*} [AddCommMonoid R] (j : Positions M n (2 ^ μ)) (k : Fin n)
    (g : JointIndex M μ s → ℂ → R) (hg : ∀ i, g i 0 = 0) (a : Fin M) (β : Bool)
    (b : Fin (2 ^ μ)) :
    ∑ i', g i' (stageHam j k (Sum.inl (a, β, b)) i') =
      ∑ c, g (Sum.inl (a, !β, c)) (if β then LinearSystems.gadget (2 ^ μ) (j a k) c b
        else LinearSystems.gadget (2 ^ μ) (j a k) b c) := by
  rw [Fintype.sum_sum_type]
  have h2 : ∑ t : Fin s, g (Sum.inr t) (stageHam j k (Sum.inl (a, β, b)) (Sum.inr t)) = 0 :=
    Finset.sum_eq_zero fun t _ => by simp [stageHam, hg]
  rw [h2, add_zero, Fintype.sum_prod_type, Finset.sum_eq_single a]
  · rw [Fintype.sum_prod_type, Fintype.sum_bool]
    cases β <;> simp [stageHam, hg]
  · intro a' _ ha'
    exact Finset.sum_eq_zero fun p _ => by simp [stageHam, Ne.symm ha', hg]
  · simp

/-- `H_k` is symmetric. -/
theorem stageHam_symm (j : Positions M n (2 ^ μ)) (k : Fin n) (i i' : JointIndex M μ s) :
    stageHam j k i' i = stageHam j k i i' := by
  rcases i with ⟨a, β, b⟩ | t <;> rcases i' with ⟨a', β', c⟩ | t'
  · by_cases ha : a = a'
    · subst ha; cases β <;> cases β' <;> simp [stageHam]
    · simp [stageHam, ha, Ne.symm ha]
  all_goals simp [stageHam]

/-- `H_k` is real. -/
theorem star_stageHam (j : Positions M n (2 ^ μ)) (k : Fin n) (i i' : JointIndex M μ s) :
    star (stageHam j k i i') = stageHam j k i i' := by
  rcases i with ⟨a, β, b⟩ | t <;> rcases i' with ⟨a', β', c⟩ | t'
  · simp only [stageHam, Matrix.of_apply]
    split_ifs <;> simp [LinearSystems.star_gadget_apply]
  all_goals simp [stageHam]

/-- `H_k` is Hermitian (real symmetric). -/
theorem stageHam_isHermitian (j : Positions M n (2 ^ μ)) (k : Fin n) :
    (stageHam (s := s) j k).IsHermitian := by
  ext i i'
  rw [Matrix.conjTranspose_apply, stageHam_symm j k i i', star_stageHam]

/-- The nonzero entries of `H_k` join `(a, β, b)` to `(a, ¬β, c)`. -/
theorem stageHam_support {j : Positions M n (2 ^ μ)} {k : Fin n} {i i' : JointIndex M μ s}
    (h : stageHam j k i i' ≠ 0) :
    ∃ a β b c, i = Sum.inl (a, β, b) ∧ i' = Sum.inl (a, !β, c) := by
  rcases i with ⟨a, β, b⟩ | t <;> rcases i' with ⟨a', β', c⟩ | t'
  · by_cases h1 : a = a' ∧ β ≠ β'
    · obtain ⟨rfl, h2⟩ := h1
      refine ⟨a, β, b, c, rfl, ?_⟩
      cases β <;> cases β' <;> simp_all
    · exact absurd (by simp [stageHam, h1]) h
  all_goals exact absurd (by simp [stageHam]) h

/-- Every row of `H_k` has squared Euclidean norm at most one. -/
theorem sum_norm_sq_stageHam_row (j : Positions M n (2 ^ μ)) (k : Fin n)
    (i : JointIndex M μ s) : ∑ i', ‖stageHam j k i i'‖ ^ 2 ≤ 1 := by
  rcases i with ⟨a, β, b⟩ | t
  · rw [sum_stageHam_row j k (fun _ z => ‖z‖ ^ 2) (fun _ => by simp)]
    cases β
    · exact (Hamiltonian.HsInstance.sum_norm_sq_row_of_unitary
        (LinearSystems.gadget_mem_unitaryGroup _) b).le
    · exact (Hamiltonian.HsInstance.sum_norm_sq_col_of_unitary
        (LinearSystems.gadget_mem_unitaryGroup _) b).le
  · simp [stageHam]

/-- Every column of `H_k` has squared Euclidean norm at most one. -/
theorem sum_norm_sq_stageHam_col (j : Positions M n (2 ^ μ)) (k : Fin n)
    (i' : JointIndex M μ s) : ∑ i, ‖stageHam j k i i'‖ ^ 2 ≤ 1 := by
  rw [Finset.sum_congr rfl fun i _ => by rw [← stageHam_symm j k i i']]
  exact sum_norm_sq_stageHam_row j k i'

/-- **The eigen relation** `H_k |a, ω⟩ = (-1)^{j_{ak}} |a, ω⟩` (eq. `odel:eq:dilation`). -/
theorem matrixOperator_stageHam_candState (hμ : 1 ≤ μ) (j : Positions M n (2 ^ μ)) (k : Fin n)
    (a : Fin M) :
    SparseStateOverlap.matrixOperator (stageHam (s := s) j k) (candState M μ s a) =
      ((-1 : ℂ) ^ (j a k : ℕ)) • candState M μ s a := by
  have hm : Even (2 ^ μ) := Nat.even_pow.mpr ⟨even_two, by omega⟩
  ext i
  rcases i with ⟨a', β, b⟩ | t
  · rw [SparseStateOverlap.matrixOperator_apply,
      sum_stageHam_row j k (fun i' z => z * candState M μ s a i') (fun _ => zero_mul _)]
    simp only [candState_inl, PiLp.smul_apply, smul_eq_mul]
    by_cases ha : a' = a
    · subst ha
      simp only [if_true, mul_left_comm _ ((Real.sqrt 2 : ℂ))⁻¹, ← Finset.mul_sum]
      cases β
      · simp only [Bool.false_eq_true, if_false]
        rw [sum_gadget_mul_alt hm]
      · simp only [if_true]
        rw [sum_gadget_mul_alt' hm]
    · simp [ha]
  · simp [SparseStateOverlap.matrixOperator_apply, stageHam, candState_inr]

/-! ### The stage generators -/

/-- The nonzero entries of `G_k` join `(a, β, b)` to `(a, ¬β, c)`. -/
theorem jointGen_support {j : Positions M n (2 ^ μ)} {k : Fin (n + 2)}
    {i i' : JointIndex M μ s} (h : jointGen j k i i' ≠ 0) :
    ∃ a β b c, i = Sum.inl (a, β, b) ∧ i' = Sum.inl (a, !β, c) := by
  unfold jointGen at h
  split_ifs at h with hk
  · rw [Matrix.smul_apply, smul_eq_mul] at h
    exact stageHam_support (right_ne_zero_of_mul h)
  · exact absurd rfl h

/-- Every stage generator `i H_k` (or `0`) is accretive (`D = 0`). -/
theorem accretive_jointGen (j : Positions M n (2 ^ μ)) (k : Fin (n + 2)) :
    TimeDependentODE.Accretive (SparseStateOverlap.matrixOperator (jointGen (s := s) j k)) := by
  unfold jointGen
  split_ifs with hk
  · exact accretive_I_smul (stageHam_isHermitian j _)
  · rw [← smul_zero Complex.I]
    exact accretive_I_smul Matrix.isHermitian_zero

theorem sum_norm_sq_jointGen_row (j : Positions M n (2 ^ μ)) (k : Fin (n + 2))
    (i : JointIndex M μ s) : ∑ i', ‖jointGen j k i i'‖ ^ 2 ≤ 1 := by
  unfold jointGen
  split_ifs with hk
  · simp only [Matrix.smul_apply, smul_eq_mul, norm_mul, Complex.norm_I, one_mul]
    exact sum_norm_sq_stageHam_row j _ i
  · simp

theorem sum_norm_sq_jointGen_col (j : Positions M n (2 ^ μ)) (k : Fin (n + 2))
    (i' : JointIndex M μ s) : ∑ i, ‖jointGen j k i i'‖ ^ 2 ≤ 1 := by
  unfold jointGen
  split_ifs with hk
  · simp only [Matrix.smul_apply, smul_eq_mul, norm_mul, Complex.norm_I, one_mul]
    exact sum_norm_sq_stageHam_col j _ i'
  · simp

/-! ### Candidate states -/

theorem sum_norm_sq_alt {m : ℕ} (hm : 0 < m) : ∑ c, ‖Hamiltonian.alt m c‖ ^ 2 = 1 := by
  have h := Hamiltonian.norm_alt hm
  rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one] at h
  simpa using h

/-- `‖|a, ω⟩‖ = 1`. -/
theorem norm_candState (a : Fin M) : ‖candState M μ s a‖ = 1 := by
  rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one, Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, candState_inl, candState_inr, norm_zero,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero, add_zero]
  rw [Finset.sum_eq_single a (fun b _ hb => by simp [hb]) (by simp)]
  have h2 : ‖((Real.sqrt 2 : ℂ))⁻¹‖ ^ 2 = 1 / 2 := by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), inv_pow,
      Real.sq_sqrt zero_le_two, one_div]
  simp only [if_true, norm_mul, mul_pow, ← Finset.mul_sum,
    sum_norm_sq_alt (Nat.two_pow_pos μ), h2]
  norm_num

theorem inner_candState_of_ne {a a' : Fin M} (h : a ≠ a') :
    ⟪candState M μ s a, candState M μ s a'⟫_ℂ = 0 := by
  rw [PiLp.inner_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  rcases i with ⟨a'', β, c⟩ | t
  · simp only [candState_inl]
    by_cases h1 : a'' = a
    · subst h1; simp [h]
    · simp [h1]
  · simp [candState_inr]

theorem inner_candState (a a' : Fin M) :
    ⟪candState M μ s a, candState M μ s a'⟫_ℂ = if a = a' then 1 else 0 := by
  split_ifs with h
  · subst h; rw [inner_self_eq_norm_sq_to_K, norm_candState]; simp
  · exact inner_candState_of_ne h

/-- `‖Σ_a |a, ω⟩‖ = √M`. -/
theorem norm_sum_candState : ‖∑ a, candState M μ s a‖ = Real.sqrt M := by
  have h2 : ‖∑ a, candState M μ s a‖ ^ 2 = M := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
    simp only [sum_inner, inner_sum, inner_candState, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
    simp
  rw [← h2, Real.sqrt_sq (norm_nonneg _)]

/-- `‖x₀‖ = 1`. -/
theorem norm_jointInit (hM : 1 ≤ M) : ‖jointInit M μ s‖ = 1 := by
  have hs : Real.sqrt M ≠ 0 := Real.sqrt_ne_zero'.mpr (by exact_mod_cast hM)
  rw [jointInit, norm_smul, norm_sum_candState, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _), inv_mul_cancel₀ hs]

theorem norm_neg_negI_pow (n : ℕ) : ‖-(-Complex.I) ^ n‖ = 1 := by
  simp

/-- `‖b‖ = 1`. -/
theorem norm_jointSrc (hM : 1 ≤ M) : ‖jointSrc M n μ s‖ = 1 := by
  rw [jointSrc, norm_smul, norm_neg_negI_pow, norm_jointInit hM, one_mul]

/-! ### The half indicator -/

theorem halfObs_inl (v : EuclideanSpace ℂ (JointIndex M μ s)) (a : Fin M) (β : Bool)
    (c : Fin (2 ^ μ)) :
    halfObs M μ s v (Sum.inl (a, β, c)) = (halfSign M a : ℂ) * v (Sum.inl (a, β, c)) := by
  simp [halfObs, SparseStateOverlap.matrixOperator_apply, Matrix.diagonal_apply]

theorem halfObs_inr (v : EuclideanSpace ℂ (JointIndex M μ s)) (t : Fin s) :
    halfObs M μ s v (Sum.inr t) = 0 := by
  simp [halfObs, SparseStateOverlap.matrixOperator_apply, Matrix.diagonal_apply]

theorem halfObs_candState (a : Fin M) :
    halfObs M μ s (candState M μ s a) = (halfSign M a : ℂ) • candState M μ s a := by
  ext i
  rcases i with ⟨a', β, c⟩ | t
  · rw [halfObs_inl, PiLp.smul_apply, smul_eq_mul, candState_inl]
    split_ifs with h
    · subst h; rfl
    · simp
  · rw [halfObs_inr, PiLp.smul_apply, candState_inr, smul_zero]

/-- The half indicator is self-adjoint. -/
theorem halfObs_isSelfAdjoint : IsSelfAdjoint (halfObs M μ s) := by
  refine Hamiltonian.star_matrixOperator_of_isHermitian ?_
  refine Matrix.isHermitian_diagonal_of_self_adjoint _ ?_
  ext i
  rcases i with ⟨a, β, c⟩ | t <;> simp [Complex.conj_ofReal]

/-- The half indicator is a contraction. -/
theorem norm_halfObs_le : ‖halfObs M μ s‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
  rw [one_mul, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
  rcases i with ⟨a, β, c⟩ | t
  · rw [halfObs_inl, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_halfSign, one_mul]
  · rw [halfObs_inr, norm_zero, zero_pow two_ne_zero]; exact sq_nonneg _

end

end SparseLowerBounds.ODE
end
