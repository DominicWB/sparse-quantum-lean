import ODELowerBoundExtensions.Homogeneous.Defs

set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false
-- The flag-extended joint index exceeds the default instance size.
set_option synthInstance.maxSize 1024

/-!
# Remark `odel:rem:homogeneous`: the stage generators

Manuscript lines 3911-3929. Facts about the generators `homGen` of
`ODELowerBoundExtensions.Homogeneous.Defs`:

* **the promise** (lines 3922-3929): every generator is accretive (`D ⪰ 0`; `accretive_homGen`:
  `i H` with `H` Hermitian on all stages but the dissipative one, where `D = P_reject ⪰ 0`), and
  every row and column has Euclidean norm at most `η = 1` (`sum_norm_sq_homGen_row`,
  `sum_norm_sq_homGen_col`; "each pulse Hamiltonian is one-sparse, has norm one", the hidden
  stages by `sum_norm_sq_stageHam_row`);
* **the action on the candidate states** `|f, a, ω⟩` (`flagCand`), from the eigen relation
  `H_k |a, ω⟩ = (-1)^{j_{ak}} |a, ω⟩` (`matrixOperator_stageHam_candState`): the hidden stage
  multiplies flag one by `i(-1)^{j_{ak}}` and kills flag zero; the pulse multiplies flag one by
  `-i`; `iY` sends `|0⟩ ↦ -|1⟩`, `|1⟩ ↦ |0⟩`; `P_reject` keeps flag zero and kills flag one;
  the idle generator is `0`.
-/

namespace ODELowerBoundExtensions.Homogeneous

noncomputable section
open SparseLowerBounds SparseLowerBounds.ODE SparseHamiltonian
open scoped InnerProductSpace

variable {M n μ s : ℕ}

/-! ### Generator formulas -/

/-- A vector with at most one entry of modulus at most one has squared norm at most one. -/
theorem sum_norm_sq_le_one_of_single {ι : Type*} [Fintype ι] (g : ι → ℂ) (i₀ : ι)
    (h0 : ∀ i, i ≠ i₀ → g i = 0) (h1 : ‖g i₀‖ ≤ 1) : ∑ i, ‖g i‖ ^ 2 ≤ 1 := by
  rw [Finset.sum_eq_single i₀ (fun i _ hi => by rw [h0 i hi, norm_zero]; ring) (by simp)]
  exact pow_le_one₀ (norm_nonneg _) h1

/-- The generator on a hidden stage. -/
theorem homGen_of_lt (j : Positions M n (2 ^ μ)) (k : Fin (n + 4)) (hk : (k : ℕ) < n) :
    homGen (s := s) j k = Complex.I • flagHam j ⟨k, hk⟩ := by
  unfold homGen homHam
  rw [if_neg (by omega), dif_pos hk]

/-- The generator on the merged phase pulse. -/
theorem homGen_of_eq_n (j : Positions M n (2 ^ μ)) (k : Fin (n + 4)) (hk : (k : ℕ) = n) :
    homGen (s := s) j k = Complex.I • pulseHam M μ s := by
  unfold homGen homHam
  rw [if_neg (by omega), dif_neg (by omega), if_pos hk]

/-- The generator on the `Y` pulse. -/
theorem homGen_of_eq_succ (j : Positions M n (2 ^ μ)) (k : Fin (n + 4)) (hk : (k : ℕ) = n + 1) :
    homGen (s := s) j k = Complex.I • yHam M μ s := by
  unfold homGen homHam
  rw [if_neg (by omega), dif_neg (by omega), if_neg (by omega), if_pos hk]

/-- The generator on the dissipative stage. -/
theorem homGen_of_eq_damp (j : Positions M n (2 ^ μ)) (k : Fin (n + 4)) (hk : (k : ℕ) = n + 2) :
    homGen (s := s) j k = rejectProj M μ s := by
  unfold homGen
  rw [if_pos hk]

/-! ### The promise -/

/-- The stage Hamiltonians are Hermitian. -/
theorem homHam_isHermitian (j : Positions M n (2 ^ μ)) (k : Fin (n + 4)) :
    (homHam (s := s) j k).IsHermitian := by
  unfold homHam
  split_ifs with h0 h1 h2
  · ext x y
    rw [Matrix.conjTranspose_apply]
    simp only [flagHam, Matrix.of_apply]
    by_cases h : x.1 = true ∧ y.1 = true
    · rw [if_pos ⟨h.2, h.1⟩, if_pos h, star_stageHam, stageHam_symm]
    · rw [if_neg (fun h' => h ⟨h'.2, h'.1⟩), if_neg h, star_zero]
  · ext x y
    rw [Matrix.conjTranspose_apply]
    simp only [pulseHam, Matrix.diagonal_apply]
    by_cases h : x = y
    · subst h; split_ifs <;> simp
    · rw [if_neg (Ne.symm h), if_neg h, star_zero]
  · ext ⟨f, x⟩ ⟨g, y⟩
    rw [Matrix.conjTranspose_apply]
    simp only [yHam, Matrix.of_apply]
    by_cases h : x = y
    · subst h
      cases f <;> cases g <;> simp [Complex.conj_I]
    · rw [if_neg (fun h' => h h'.1.symm), if_neg (fun h' => h h'.1), star_zero]
  · exact Matrix.isHermitian_zero

/-- **The dissipative promise** (lines 3925-3927): every stage generator is accretive. -/
theorem accretive_homGen (j : Positions M n (2 ^ μ)) (k : Fin (n + 4)) :
    TimeDependentODE.Accretive (SparseStateOverlap.matrixOperator (homGen (s := s) j k)) := by
  unfold homGen
  split_ifs with hk
  · intro v
    rw [PiLp.inner_apply, Complex.re_sum]
    refine Finset.sum_nonneg fun i _ => ?_
    simp only [SparseStateOverlap.matrixOperator_apply, rejectProj, Matrix.diagonal_apply,
      ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    split_ifs
    · simp
    · rw [one_mul, RCLike.inner_apply', Complex.conj_mul', ← Complex.ofReal_pow,
        Complex.ofReal_re]
      positivity
  · exact accretive_I_smul (homHam_isHermitian j k)

/-- Rows of the stage Hamiltonians have squared norm at most one. -/
theorem sum_norm_sq_homHam_row (j : Positions M n (2 ^ μ)) (k : Fin (n + 4))
    (i : HomIndex M μ s) : ∑ i', ‖homHam j k i i'‖ ^ 2 ≤ 1 := by
  obtain ⟨f, i⟩ := i
  unfold homHam
  split_ifs with h0 h1 h2
  · rw [Fintype.sum_prod_type, Fintype.sum_bool]
    cases f
    · simp [flagHam]
    · simpa [flagHam] using sum_norm_sq_stageHam_row j ⟨k, h0⟩ i
  · refine sum_norm_sq_le_one_of_single _ (f, i) (fun i' hi' => ?_) ?_
    · simp [pulseHam, Matrix.diagonal_apply_ne _ (Ne.symm hi')]
    · simp only [pulseHam, Matrix.diagonal_apply_eq]
      split_ifs <;> simp
  · refine sum_norm_sq_le_one_of_single _ (!f, i) (fun ⟨g, i'⟩ hi' => ?_) ?_
    · simp only [yHam, Matrix.of_apply]
      rw [if_neg]
      rintro ⟨rfl, hfg⟩
      apply hi'
      cases f <;> cases g <;> simp_all
    · simp only [yHam, Matrix.of_apply]
      cases f <;> simp
  · simp

/-- Columns of the stage Hamiltonians have squared norm at most one. -/
theorem sum_norm_sq_homHam_col (j : Positions M n (2 ^ μ)) (k : Fin (n + 4))
    (i' : HomIndex M μ s) : ∑ i, ‖homHam j k i i'‖ ^ 2 ≤ 1 := by
  obtain ⟨f, i'⟩ := i'
  unfold homHam
  split_ifs with h0 h1 h2
  · rw [Fintype.sum_prod_type, Fintype.sum_bool]
    cases f
    · simp [flagHam]
    · simpa [flagHam] using sum_norm_sq_stageHam_col j ⟨k, h0⟩ i'
  · refine sum_norm_sq_le_one_of_single _ (f, i') (fun i hi => ?_) ?_
    · simp [pulseHam, Matrix.diagonal_apply_ne _ hi]
    · simp only [pulseHam, Matrix.diagonal_apply_eq]
      split_ifs <;> simp
  · refine sum_norm_sq_le_one_of_single _ (!f, i') (fun ⟨g, i⟩ hi => ?_) ?_
    · simp only [yHam, Matrix.of_apply]
      rw [if_neg]
      rintro ⟨rfl, hfg⟩
      apply hi
      cases f <;> cases g <;> simp_all
    · simp only [yHam, Matrix.of_apply]
      cases f <;> simp
  · simp

/-- **Row norm bound** `η = 1` (lines 3928-3929). -/
theorem sum_norm_sq_homGen_row (j : Positions M n (2 ^ μ)) (k : Fin (n + 4))
    (i : HomIndex M μ s) : ∑ i', ‖homGen j k i i'‖ ^ 2 ≤ 1 := by
  unfold homGen
  split_ifs with h2
  · refine sum_norm_sq_le_one_of_single _ i (fun i' hi' => ?_) ?_
    · simp [rejectProj, Matrix.diagonal_apply_ne _ (Ne.symm hi')]
    · simp only [rejectProj, Matrix.diagonal_apply_eq]
      split_ifs <;> simp
  · simp only [Matrix.smul_apply, smul_eq_mul, norm_mul, Complex.norm_I, one_mul]
    exact sum_norm_sq_homHam_row j k i

/-- **Column norm bound** `η = 1` (lines 3928-3929). -/
theorem sum_norm_sq_homGen_col (j : Positions M n (2 ^ μ)) (k : Fin (n + 4))
    (i' : HomIndex M μ s) : ∑ i, ‖homGen j k i i'‖ ^ 2 ≤ 1 := by
  unfold homGen
  split_ifs with h2
  · refine sum_norm_sq_le_one_of_single _ i' (fun i hi => ?_) ?_
    · simp [rejectProj, Matrix.diagonal_apply_ne _ hi]
    · simp only [rejectProj, Matrix.diagonal_apply_eq]
      split_ifs <;> simp
  · simp only [Matrix.smul_apply, smul_eq_mul, norm_mul, Complex.norm_I, one_mul]
    exact sum_norm_sq_homHam_col j k i'

/-! ### The action on the candidate states -/

/-- **Hidden stage, flag one** (line 3911): `G_k |1, a, ω⟩ = i(-1)^{j_{ak}} |1, a, ω⟩`. -/
theorem homGen_hidden_true (hμ : 1 ≤ μ) (j : Positions M n (2 ^ μ)) (k : Fin (n + 4))
    (hk : (k : ℕ) < n) (a : Fin M) :
    SparseStateOverlap.matrixOperator (homGen j k) (flagCand M μ s true a) =
      (Complex.I * (-1 : ℂ) ^ (j a ⟨k, hk⟩ : ℕ)) • flagCand M μ s true a := by
  rw [homGen_of_lt j k hk, matrixOperator_I_smul, smul_apply, mul_smul]
  congr 1
  ext ⟨f, i⟩
  have he := congrArg (fun v => v i)
    (matrixOperator_stageHam_candState (s := s) hμ j ⟨k, hk⟩ a)
  simp only [SparseStateOverlap.matrixOperator_apply, PiLp.smul_apply, smul_eq_mul] at he ⊢
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  cases f <;> simp [flagHam, flagCand_apply, he]

/-- **Hidden stage, flag zero**: the flag-zero branch is idle, `G_k |0, a, ω⟩ = 0`. -/
theorem homGen_hidden_false (j : Positions M n (2 ^ μ)) (k : Fin (n + 4)) (hk : (k : ℕ) < n)
    (a : Fin M) :
    SparseStateOverlap.matrixOperator (homGen j k) (flagCand M μ s false a) = 0 := by
  rw [homGen_of_lt j k hk, matrixOperator_I_smul, smul_apply]
  convert smul_zero Complex.I using 2
  ext ⟨f, i⟩
  simp only [SparseStateOverlap.matrixOperator_apply, PiLp.zero_apply]
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  simp [flagHam, flagCand_apply]

/-- **The merged phase pulse** (lines 3911-3914): `G = -i|1⟩⟨1| ⊗ 1`. -/
theorem homGen_pulse (j : Positions M n (2 ^ μ)) (k : Fin (n + 4)) (hk : (k : ℕ) = n)
    (f : Bool) (a : Fin M) :
    SparseStateOverlap.matrixOperator (homGen j k) (flagCand M μ s f a) =
      (if f then -Complex.I else 0) • flagCand M μ s f a := by
  rw [homGen_of_eq_n j k hk, matrixOperator_I_smul, smul_apply]
  ext ⟨g, i⟩
  simp only [SparseStateOverlap.matrixOperator_apply, PiLp.smul_apply, smul_eq_mul, pulseHam,
    Matrix.diagonal_apply, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    flagCand_apply]
  cases f <;> cases g <;> simp

/-- **The `Y` pulse** (line 3914): `G = iY ⊗ 1` sends `|0, a, ω⟩ ↦ -|1, a, ω⟩` and
`|1, a, ω⟩ ↦ |0, a, ω⟩`. -/
theorem homGen_y (j : Positions M n (2 ^ μ)) (k : Fin (n + 4)) (hk : (k : ℕ) = n + 1)
    (f : Bool) (a : Fin M) :
    SparseStateOverlap.matrixOperator (homGen j k) (flagCand M μ s f a) =
      (if f then (1 : ℂ) else -1) • flagCand M μ s (!f) a := by
  rw [homGen_of_eq_succ j k hk, matrixOperator_I_smul, smul_apply]
  ext ⟨g, i⟩
  simp only [SparseStateOverlap.matrixOperator_apply, PiLp.smul_apply, smul_eq_mul]
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  cases f <;> cases g <;> simp [yHam, flagCand_apply, ← mul_assoc]

/-- **The dissipation** (lines 3925-3927): `G = P_reject = |0⟩⟨0| ⊗ 1`. -/
theorem homGen_reject (j : Positions M n (2 ^ μ)) (k : Fin (n + 4)) (hk : (k : ℕ) = n + 2)
    (f : Bool) (a : Fin M) :
    SparseStateOverlap.matrixOperator (homGen j k) (flagCand M μ s f a) =
      (if f then (0 : ℂ) else 1) • flagCand M μ s f a := by
  rw [homGen_of_eq_damp j k hk]
  ext ⟨g, i⟩
  simp only [SparseStateOverlap.matrixOperator_apply, PiLp.smul_apply, smul_eq_mul, rejectProj,
    Matrix.diagonal_apply, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    flagCand_apply]
  cases f <;> cases g <;> simp

/-- **The idle stage** (line 3946): `G = 0`. -/
theorem homGen_idle (j : Positions M n (2 ^ μ)) (k : Fin (n + 4)) (hk : (k : ℕ) = n + 3) :
    homGen (s := s) j k = 0 := by
  unfold homGen homHam
  rw [if_neg (by omega), dif_neg (by omega), if_neg (by omega), if_neg (by omega), smul_zero]

end

end ODELowerBoundExtensions.Homogeneous
