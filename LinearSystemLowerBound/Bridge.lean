import LinearSystemLowerBound.Theorem
import SparseLowerBounds.LinearSystems.Instance

/-!
# The hard family through `SparseLowerBounds`: actual condition number and dimension

The `SparseLowerBounds` library has its own copy of the hard family of Theorem
`qlsl:thm:main` (`SparseLowerBounds.LinearSystems.hardMatrix`).  The two copies are the same
matrices after relabelling the sector (`Bool ≃ Fin 2`) and the clock register
(`Fin (2n - 1 + 1) ≃ Fin (2n)`), so two facts proved there hold for `A_X`:

* `gadgetPos_eq`, `gadget_eq`: both gadget entry formulas query the bit at position
  `a - b - 1`;
* `hardMatrix_eq_submatrix`, `family_eq_submatrix`: `A_X` is
  `SparseLowerBounds.LinearSystems.hardMatrix` reindexed by `bridge`;
* `matrixOperator_submatrix`, `norm_matrixOperator_submatrix`,
  `norm_inverse_matrixOperator_submatrix`: reindexing by a bijection is conjugation by a
  permutation unitary, which preserves the operator norm and the norm of the inverse;
* `family_cond`: the actual condition number satisfies `κ/16 < ‖A_X‖ ‖A_X⁻¹‖ ≤ κ` (the
  remark after Theorem `qlsl:thm:main`, eq. `qlsl:eq:actualconditioning`), from
  `SparseLowerBounds.LinearSystems.quarter_lt_cond`;
* `family_dimension_le`, `family_dimension_sharp`: the dimension satisfies
  `s κ ln(1/ε) / 32 < N ≤ (s - 1) κ ln(1/ε)`, the upper half from
  `SparseLowerBounds.LinearSystems.dim_bounds` (`family_dimension` has `N < s κ ln(1/ε)`).
-/

namespace LinearSystemLowerBound

noncomputable section
open SparseHamiltonian LinearSystemLowerBound.Hard LinearSystemLowerBound.Params

/-! ### The two gadget formulas agree -/

/-- The queried position `gadgetPos a b` of the `SparseLowerBounds` gadget is `a - b - 1`. -/
theorem gadgetPos_eq {m : ℕ} [NeZero m] (a b : Fin m) :
    SparseLowerBounds.LinearSystems.gadgetPos a b = a - b - 1 := by
  rw [eq_sub_iff_add_eq, eq_sub_iff_add_eq, Fin.ext_iff, Fin.val_add, Fin.val_add]
  simp only [SparseLowerBounds.LinearSystems.gadgetPos]
  have ha := a.isLt
  have hb := b.isLt
  have hm : 1 ≤ m := Nat.pos_of_ne_zero (NeZero.ne m)
  rcases Nat.lt_or_ge 1 m with h1 | h1
  · rw [Fin.val_one', Nat.mod_eq_of_lt h1]
    simp only [Nat.mod_add_mod]
    have : (a : ℕ) + (m - 1 - b) + 1 + b = a + m := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt ha]
  · have hm1 : m = 1 := by omega
    subst hm1
    omega

theorem gadget_eq {m : ℕ} [NeZero m] (j : Fin m) :
    SparseLowerBounds.LinearSystems.gadget m j = Hard.gadget j := by
  ext a b
  simp only [SparseLowerBounds.LinearSystems.gadget, Hard.gadget, Matrix.of_apply, gadgetPos_eq]
  by_cases h : j = a - b - 1
  · rw [if_pos h.symm, if_pos h]
  · rw [if_neg (Ne.symm h), if_neg h]

/-! ### The two hard matrices agree -/

/-- Relabelling of the index set: sector `Bool ≃ Fin 2` (`false ↦ 0`) and clock
`Fin (2n - 1 + 1) ≃ Fin (2n)`. -/
def bridge (n m : ℕ) (hn : 0 < n) :
    Idx (2 * n - 1) m ≃ SparseLowerBounds.LinearSystems.HardIndex n m :=
  Equiv.prodCongr finTwoEquiv.symm (Equiv.prodCongr (finCongr (by omega)) (Equiv.refl _))

@[simp] theorem bridge_fst (n m : ℕ) (hn : 0 < n) (b : Bool) (p : Fin (2 * n - 1 + 1) × Fin m) :
    (bridge n m hn (b, p)).1 = if b then 1 else 0 := by
  cases b <;> rfl

@[simp] theorem bridge_snd_fst (n m : ℕ) (hn : 0 < n) (b : Bool) (p : Fin (2 * n - 1 + 1) × Fin m) :
    ((bridge n m hn (b, p)).2.1 : ℕ) = p.1 := rfl

@[simp] theorem bridge_snd_snd (n m : ℕ) (hn : 0 < n) (b : Bool) (p : Fin (2 * n - 1 + 1) × Fin m) :
    (bridge n m hn (b, p)).2.2 = p.2 := rfl

theorem bridge_snd_inj (n m : ℕ) (hn : 0 < n) (b b' : Bool) (p q : Fin (2 * n - 1 + 1) × Fin m) :
    (bridge n m hn (b, p)).2 = (bridge n m hn (b', q)).2 ↔ p = q := by
  constructor
  · intro h
    have h1 := congrArg (fun z => (z.1 : ℕ)) h
    have h2 := congrArg Prod.snd h
    simp only [bridge_snd_fst, bridge_snd_snd] at h1 h2
    exact Prod.ext (Fin.ext h1) h2
  · rintro rfl
    rfl

/-- **The hard matrices agree**: `A_X` is the `SparseLowerBounds` hard matrix, reindexed. -/
theorem hardMatrix_eq_submatrix {n μ ρ : ℕ} (hn : 0 < n) (x : Fin n → Fin (2 ^ μ)) :
    Hard.hardMatrix (T := 2 * n - 1) (SparseLowerBounds.LinearSystems.clockRatio ρ) x =
      (SparseLowerBounds.LinearSystems.hardMatrix n μ ρ x).submatrix
        (bridge n (2 ^ μ) hn) (bridge n (2 ^ μ) hn) := by
  have key : ∀ (p q : Fin (2 * n - 1 + 1) × Fin (2 ^ μ)),
      Hard.hardMatrix (T := 2 * n - 1) (SparseLowerBounds.LinearSystems.clockRatio ρ) x
          (false, p) (true, q) =
        SparseLowerBounds.LinearSystems.hardMatrix n μ ρ x
          (bridge n (2 ^ μ) hn (false, p)) (bridge n (2 ^ μ) hn (true, q)) := by
    intro p q
    simp only [Hard.hardMatrix, swapM, dil, clock, step, Matrix.smul_apply, Matrix.sub_apply,
      Matrix.of_apply, smul_eq_mul, SparseLowerBounds.LinearSystems.hardMatrix,
      SparseLowerBounds.LinearSystems.dilation, SparseLowerBounds.LinearSystems.hardC,
      SparseLowerBounds.LinearSystems.clockMatrix, SparseLowerBounds.LinearSystems.clockShift,
      SparseLowerBounds.LinearSystems.hardTransition, Matrix.one_apply, bridge_fst,
      bridge_snd_fst, bridge_snd_snd, bridge_snd_inj, gadget_eq]
    simp only [Bool.not_true, true_and, and_self, ↓reduceIte, Bool.false_eq_true, one_div]
    by_cases h1 : (p.1 : ℕ) = q.1 + 1
    · rw [dif_pos h1, if_pos h1]
    · rw [dif_neg h1, if_neg h1]
  ext ⟨b, p⟩ ⟨b', q⟩
  cases b <;> cases b'
  · simp [Hard.hardMatrix, swapM, dil, SparseLowerBounds.LinearSystems.hardMatrix,
      SparseLowerBounds.LinearSystems.dilation]
  · exact key p q
  · rw [hard_symm, key q p, Matrix.submatrix_apply]
    have h := congrFun (congrFun (SparseLowerBounds.LinearSystems.hardMatrix_transpose (ρ := ρ) x)
      (bridge n (2 ^ μ) hn (true, p))) (bridge n (2 ^ μ) hn (false, q))
    rw [Matrix.transpose_apply] at h
    exact h
  · simp [Hard.hardMatrix, swapM, dil, SparseLowerBounds.LinearSystems.hardMatrix,
      SparseLowerBounds.LinearSystems.dilation]

theorem rpar_eq_clockRatio (κ : ℝ) :
    rpar κ = SparseLowerBounds.LinearSystems.clockRatio (Nat.log 2 ⌊κ / 2⌋₊) := by
  simp [rpar, Rpar, SparseLowerBounds.LinearSystems.clockRatio]

/-- **The hard family is the `SparseLowerBounds` family**, reindexed. -/
theorem family_eq_submatrix (κ ε : ℝ) (s : ℕ) (hκ : 32 ≤ κ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 64)
    (x : Inp κ ε s) :
    family κ ε s x =
      (SparseLowerBounds.LinearSystems.hardMatrix (npar κ ε) (Nat.log 2 (s - 1))
          (Nat.log 2 ⌊κ / 2⌋₊) x).submatrix
        (bridge (npar κ ε) (mpar s) (npar_pos κ ε hκ hε hε1))
        (bridge (npar κ ε) (mpar s) (npar_pos κ ε hκ hε hε1)) := by
  rw [family, rpar_eq_clockRatio]
  exact hardMatrix_eq_submatrix (μ := Nat.log 2 (s - 1)) (npar_pos κ ε hκ hε hε1) x

/-! ### Reindexing preserves norms -/

/-- Reindexing a matrix by a bijection is conjugation by the permutation unitary. -/
theorem matrixOperator_submatrix {ι ι' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι']
    [DecidableEq ι'] (e : ι ≃ ι') (A : Matrix ι' ι' ℂ) :
    SparseStateOverlap.matrixOperator (A.submatrix e e) =
      (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).symm.conjStarAlgEquiv
        (SparseStateOverlap.matrixOperator A) := by
  ext v i
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]
  simp only [SparseStateOverlap.matrixOperator_apply, Matrix.submatrix_apply,
    LinearIsometryEquiv.piLpCongrLeft_apply,
    Equiv.piCongrLeft'_apply, LinearIsometryEquiv.piLpCongrLeft_symm]
  rw [← e.sum_comp]
  simp

theorem norm_conjStarAlgEquiv {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (U : E ≃ₗᵢ[ℂ] F) (A : E →L[ℂ] E) : ‖U.conjStarAlgEquiv A‖ = ‖A‖ := by
  apply le_antisymm
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => ?_
    rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, U.norm_map]
    calc ‖A (U.symm v)‖ ≤ ‖A‖ * ‖U.symm v‖ := A.le_opNorm _
      _ = ‖A‖ * ‖v‖ := by rw [U.symm.norm_map]
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => ?_
    have h := (U.conjStarAlgEquiv A).le_opNorm (U v)
    rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, U.symm_apply_apply, U.norm_map,
      U.norm_map] at h
    exact h

/-- A ring isomorphism commutes with `Ring.inverse`. -/
theorem ringInverse_map {R S F : Type*} [Ring R] [Ring S] [EquivLike F R S]
    [RingEquivClass F R S] (f : F) (a : R) : Ring.inverse (f a) = f (Ring.inverse a) := by
  by_cases h : IsUnit a
  · have hf : IsUnit (f a) := h.map f
    rw [Ring.inverse_of_isUnit hf]
    apply Units.inv_eq_of_mul_eq_one_left
    rw [IsUnit.unit_spec, ← map_mul, Ring.inverse_mul_cancel _ h, map_one]
  · have hf : ¬ IsUnit (f a) := fun hf => h ((isUnit_map_iff f a).mp hf)
    rw [Ring.inverse_non_unit _ hf, Ring.inverse_non_unit _ h, map_zero]

theorem norm_matrixOperator_submatrix {ι ι' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι']
    [DecidableEq ι'] (e : ι ≃ ι') (A : Matrix ι' ι' ℂ) :
    ‖SparseStateOverlap.matrixOperator (A.submatrix e e)‖ =
      ‖SparseStateOverlap.matrixOperator A‖ := by
  rw [matrixOperator_submatrix, norm_conjStarAlgEquiv]

theorem norm_inverse_matrixOperator_submatrix {ι ι' : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype ι'] [DecidableEq ι'] (e : ι ≃ ι') (A : Matrix ι' ι' ℂ) :
    ‖Ring.inverse (SparseStateOverlap.matrixOperator (A.submatrix e e))‖ =
      ‖Ring.inverse (SparseStateOverlap.matrixOperator A)‖ := by
  rw [matrixOperator_submatrix, ringInverse_map, norm_conjStarAlgEquiv]

/-! ### The condition number -/

theorem log_64_ge_four : (4 : ℝ) ≤ Real.log 64 := by
  have h : Real.log 64 = 6 * Real.log 2 := by
    rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]
    norm_num
  rw [h]
  have := Real.log_two_gt_d9
  linarith

/-- `R ≤ 2n`: at least `R/2` clock steps carry gadgets. -/
theorem Rpar_le_two_npar (κ ε : ℝ) (hκ : 32 ≤ κ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 64) :
    Rpar κ ≤ 2 * npar κ ε := by
  have h := npar_ge κ ε hκ hε hε1
  have hL := L_ge ε hε hε1
  have h4 := log_64_ge_four
  have hR := sixteen_le_Rpar κ hκ
  have : (Rpar κ : ℝ) ≤ 2 * npar κ ε := by nlinarith
  exact_mod_cast this

/-- **Actual condition number** (remark after Theorem `qlsl:thm:main`, eq.
`qlsl:eq:actualconditioning`): `κ/16 < ‖A_X‖ ‖A_X⁻¹‖ ≤ κ`. -/
theorem family_cond (κ ε : ℝ) (s : ℕ) (hκ : 32 ≤ κ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 64)
    (x : Inp κ ε s) :
    κ / 16 < ‖SparseStateOverlap.matrixOperator (family κ ε s x)‖ *
        ‖Ring.inverse (SparseStateOverlap.matrixOperator (family κ ε s x))‖ ∧
      ‖SparseStateOverlap.matrixOperator (family κ ε s x)‖ *
        ‖Ring.inverse (SparseStateOverlap.matrixOperator (family κ ε s x))‖ ≤ κ := by
  obtain ⟨h1, -, h3⟩ := family_promise κ ε s hκ x
  refine ⟨?_, ?_⟩
  · have hcond : ‖SparseStateOverlap.matrixOperator (family κ ε s x)‖ *
          ‖Ring.inverse (SparseStateOverlap.matrixOperator (family κ ε s x))‖ =
        ‖SparseStateOverlap.matrixOperator (SparseLowerBounds.LinearSystems.hardMatrix (npar κ ε)
            (Nat.log 2 (s - 1)) (Nat.log 2 ⌊κ / 2⌋₊) x)‖ *
          ‖Ring.inverse (SparseStateOverlap.matrixOperator
            (SparseLowerBounds.LinearSystems.hardMatrix (npar κ ε) (Nat.log 2 (s - 1))
              (Nat.log 2 ⌊κ / 2⌋₊) x))‖ := by
      rw [family_eq_submatrix κ ε s hκ hε hε1 x]
      exact congrArg₂ (· * ·) (norm_matrixOperator_submatrix _ _)
        (norm_inverse_matrixOperator_submatrix _ _)
    rw [hcond]
    have hc := SparseLowerBounds.LinearSystems.quarter_lt_cond (μ := Nat.log 2 (s - 1))
      (Rpar_le_two_npar κ ε hκ hε hε1) x
    have hR := lt_Rpar κ
    have hR' : ((Rpar κ : ℕ) : ℝ) = (2 : ℝ) ^ Nat.log 2 ⌊κ / 2⌋₊ := by
      simp [Rpar]
    rw [hR'] at hR
    linarith
  · calc _ ≤ 1 * κ := mul_le_mul h1 h3 (norm_nonneg _) zero_le_one
      _ = κ := one_mul κ

/-! ### The dimension -/

/-- **Dimension**, upper half: `N ≤ (s - 1) κ ln(1/ε)`
(`SparseLowerBounds.LinearSystems.dim_bounds`). -/
theorem family_dimension_le (κ ε : ℝ) (s : ℕ) (hκ : 32 ≤ κ) (hs : 5 ≤ s) (hε : 0 < ε)
    (hε1 : ε ≤ 1 / 64) :
    (Fintype.card (Ind κ ε s) : ℝ) ≤ ((s : ℝ) - 1) * κ * Real.log (1 / ε) := by
  have h := (SparseLowerBounds.LinearSystems.dim_bounds ⟨hκ, hs, hε, hε1⟩).2
  have hm : SparseLowerBounds.LinearSystems.hardM s = mpar s := rfl
  have hn : SparseLowerBounds.LinearSystems.hardN κ ε = npar κ ε := rfl
  rw [hm, hn] at h
  rw [(family_dimension κ ε s hκ hs hε hε1).1]
  push_cast
  linarith

/-- **Dimension** `N = 4 n m` with `s κ ln(1/ε) / 32 < N ≤ (s - 1) κ ln(1/ε)`. -/
theorem family_dimension_sharp (κ ε : ℝ) (s : ℕ) (hκ : 32 ≤ κ) (hs : 5 ≤ s) (hε : 0 < ε)
    (hε1 : ε ≤ 1 / 64) :
    Fintype.card (Ind κ ε s) = 4 * npar κ ε * mpar s ∧
      s * κ * Real.log (1 / ε) / 32 < Fintype.card (Ind κ ε s) ∧
      (Fintype.card (Ind κ ε s) : ℝ) ≤ ((s : ℝ) - 1) * κ * Real.log (1 / ε) :=
  ⟨(family_dimension κ ε s hκ hs hε hε1).1, (family_dimension κ ε s hκ hs hε hε1).2.1,
    family_dimension_le κ ε s hκ hs hε hε1⟩

end

end LinearSystemLowerBound
