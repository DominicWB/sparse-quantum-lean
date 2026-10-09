import LinearSystemLowerBound.Hard.Clock

/-!
# Norms, invertibility, symmetry and support of the hard matrices

* `norm_act_dil_le`: `‖Q_X v‖ ≤ ‖v‖` (the clock is a partial isometry in each sector).
* `hard_norm_le`, `hard_norm_ge`: `(1 - r)/2 ‖v‖ ≤ ‖A_X v‖ ≤ (1 + r)/2 ‖v‖`
  (paper, equation `qlsl:eq:Cpromise`).
* `hard_opNorm_le`, `hard_isUnit`, `hard_inverse_norm_le`: the promise data `‖A_X‖ ≤ 1`,
  invertibility and `‖A_X⁻¹‖ ≤ 2/(1 - r) = 2R`.
* `hard_symm`, `hard_im`: `A_X` is real symmetric.
* `bitDetermined_hard`: every entry of `A_X` is a fixed function of at most one bit
  `[x_c = q₀]` of the input.
* `hard_support`, `card_support_le`: every row has at most `m + 1` possible nonzero
  positions, independently of the input.
-/

namespace LinearSystemLowerBound.Hard

noncomputable section
open scoped BigOperators Matrix InnerProductSpace
open LinearSystemLowerBound SparseHamiltonian

variable {n m T : ℕ} [NeZero m]

/-! ### Unitary blocks -/

omit [NeZero m] in
theorem sum_norm_sq_mulVec (M : Matrix (Fin m) (Fin m) ℂ) (hM : Mᴴ * M = 1)
    (φ : Fin m → ℂ) : ∑ a, ‖∑ b, M a b * φ b‖ ^ 2 = ∑ b, ‖φ b‖ ^ 2 := by
  have h := norm_act_of_unitary M hM (WithLp.toLp 2 φ : Fam (Fin m) ℂ)
  have h2 := congrArg (fun z : ℝ => z ^ 2) h
  simp only [norm_sq_fam, act_apply, smul_eq_mul] at h2
  exact h2

omit [NeZero m] in
theorem sum_norm_sq_vecMul (M : Matrix (Fin m) (Fin m) ℂ) (hM : M * Mᴴ = 1)
    (φ : Fin m → ℂ) : ∑ b, ‖∑ a, M a b * φ a‖ ^ 2 = ∑ a, ‖φ a‖ ^ 2 := by
  have hT : (Mᵀ)ᴴ * Mᵀ = 1 := by
    have : (Mᵀ)ᴴ * Mᵀ = (M * Mᴴ)ᵀ := by
      ext i k
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.transpose_apply]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [this, hM, Matrix.transpose_one]
  have h := sum_norm_sq_mulVec Mᵀ hT φ
  simpa only [Matrix.transpose_apply] using h

/-! ### Norm bounds -/

/-- **The clock is a contraction in each sector.** -/
theorem norm_act_dil_le (x : Fin n → Fin m) (v : EuclideanSpace ℂ (Idx T m)) :
    ‖act (dil x) v‖ ≤ ‖v‖ := by
  have hsq : ‖act (dil x) v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [norm_sq_fam, norm_sq_fam]
    simp only [Fintype.sum_prod_type, Fintype.sum_bool]
    simp only [act_dil_true, act_dil_false]
    -- the `false` rows (the clock applied to the `true` sector)
    have h1 : ∑ t : Fin (T + 1), ∑ a, ‖∑ q, clock x (t, a) q * v (true, q)‖ ^ 2 ≤
        ∑ t : Fin (T + 1), ∑ b, ‖v (true, t, b)‖ ^ 2 := by
      rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc (f := fun t => ∑ b, ‖v (true, t, b)‖ ^ 2)]
      simp only [sum_clock_zero, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, Finset.sum_const_zero, zero_add, sum_clock_succ]
      have hlast : 0 ≤ ∑ b, ‖v (true, Fin.last T, b)‖ ^ 2 :=
        Finset.sum_nonneg fun b _ => sq_nonneg _
      have heq : ∑ i : Fin T, ∑ a, ‖∑ b, step x i a b * v (true, i.castSucc, b)‖ ^ 2 =
          ∑ i : Fin T, ∑ b, ‖v (true, i.castSucc, b)‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        exact sum_norm_sq_mulVec (step x i) (step_unitary x i) (fun b => v (true, i.castSucc, b))
      linarith
    -- the `true` rows (the transposed clock applied to the `false` sector)
    have h2 : ∑ t : Fin (T + 1), ∑ b, ‖∑ p, clock x p (t, b) * v (false, p)‖ ^ 2 ≤
        ∑ t : Fin (T + 1), ∑ a, ‖v (false, t, a)‖ ^ 2 := by
      rw [Fin.sum_univ_castSucc, Fin.sum_univ_succ (f := fun t => ∑ a, ‖v (false, t, a)‖ ^ 2)]
      simp only [sum_clock_last, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, Finset.sum_const_zero, add_zero, sum_clock_castSucc]
      have hzero : 0 ≤ ∑ a, ‖v (false, 0, a)‖ ^ 2 := Finset.sum_nonneg fun a _ => sq_nonneg _
      have heq : ∑ i : Fin T, ∑ b, ‖∑ a, step x i a b * v (false, i.succ, a)‖ ^ 2 =
          ∑ i : Fin T, ∑ a, ‖v (false, i.succ, a)‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        exact sum_norm_sq_vecMul (step x i) (step_unitary' x i) (fun a => v (false, i.succ, a))
      linarith
    simp only [Fintype.sum_prod_type] at h1 h2 ⊢
    linarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hsq

omit [NeZero m] in
theorem norm_act_swapM (v : EuclideanSpace ℂ (Idx T m)) : ‖act swapM v‖ = ‖v‖ := by
  have h : ‖act swapM v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [norm_sq_fam, norm_sq_fam]
    simp only [act_swapM_apply]
    let e : Idx T m ≃ Idx T m :=
      { toFun := fun p => (!p.1, p.2)
        invFun := fun p => (!p.1, p.2)
        left_inv := fun p => by simp
        right_inv := fun p => by simp }
    exact e.sum_comp (fun p => ‖v p‖ ^ 2)
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

theorem hard_norm_le (r : ℝ) (hr0 : 0 ≤ r) (x : Fin n → Fin m) (v : EuclideanSpace ℂ (Idx T m)) :
    ‖act (hardMatrix r x) v‖ ≤ (1 + r) / 2 * ‖v‖ := by
  rw [act_hard, norm_smul]
  have h1 := norm_act_dil_le x v
  have h2 := norm_act_swapM v
  calc ‖(1 / 2 : ℂ)‖ * ‖act swapM v - (r : ℂ) • act (dil x) v‖
      ≤ 1 / 2 * (‖act swapM v‖ + ‖(r : ℂ) • act (dil x) v‖) := by
        rw [show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
        exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by norm_num)
    _ ≤ 1 / 2 * (‖v‖ + r * ‖v‖) := by
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0, h2]
        gcongr
    _ = (1 + r) / 2 * ‖v‖ := by ring

theorem hard_norm_ge (r : ℝ) (hr0 : 0 ≤ r) (x : Fin n → Fin m) (v : EuclideanSpace ℂ (Idx T m)) :
    (1 - r) / 2 * ‖v‖ ≤ ‖act (hardMatrix r x) v‖ := by
  rw [act_hard, norm_smul]
  have h1 := norm_act_dil_le x v
  have h2 := norm_act_swapM v
  have h3 : ‖act swapM v‖ - ‖(r : ℂ) • act (dil x) v‖ ≤
      ‖act swapM v - (r : ℂ) • act (dil x) v‖ := norm_sub_norm_le _ _
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0, h2] at h3
  rw [show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
  nlinarith [mul_le_mul_of_nonneg_left h1 hr0]

/-! ### The promise data -/

omit [NeZero m] in
theorem matrixOperator_eq_act (M : Matrix (Idx T m) (Idx T m) ℂ)
    (v : EuclideanSpace ℂ (Idx T m)) : SparseStateOverlap.matrixOperator M v = act M v := by
  ext i
  simp [SparseStateOverlap.matrixOperator_apply, act_apply, smul_eq_mul]

theorem hard_opNorm_le (r : ℝ) (hr0 : 0 ≤ r) (x : Fin n → Fin m) :
    ‖SparseStateOverlap.matrixOperator (hardMatrix (T := T) r x)‖ ≤ (1 + r) / 2 :=
  ContinuousLinearMap.opNorm_le_bound _ (by linarith) fun v => by
    rw [matrixOperator_eq_act]; exact hard_norm_le r hr0 x v

theorem hard_lower (r : ℝ) (hr0 : 0 ≤ r) (x : Fin n → Fin m) (v : EuclideanSpace ℂ (Idx T m)) :
    (1 - r) / 2 * ‖v‖ ≤ ‖SparseStateOverlap.matrixOperator (hardMatrix (T := T) r x) v‖ := by
  rw [matrixOperator_eq_act]; exact hard_norm_ge r hr0 x v

theorem hard_isUnit (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (x : Fin n → Fin m) :
    IsUnit (SparseStateOverlap.matrixOperator (hardMatrix (T := T) r x)) := by
  set A := SparseStateOverlap.matrixOperator (hardMatrix (T := T) r x)
  have hinj : Function.Injective A := by
    intro v w hvw
    have h := hard_lower r hr0 x (v - w)
    rw [show SparseStateOverlap.matrixOperator (hardMatrix (T := T) r x) (v - w) = A v - A w
      from map_sub A v w, hvw, sub_self, norm_zero] at h
    have hpos : 0 < (1 - r) / 2 := by linarith
    have : ‖v - w‖ ≤ 0 := by nlinarith [norm_nonneg (v - w)]
    exact sub_eq_zero.mp (norm_le_zero_iff.mp this)
  have hsurj : Function.Surjective A := by
    have := LinearMap.injective_iff_surjective
      (f := (A : EuclideanSpace ℂ (Idx T m) →ₗ[ℂ] EuclideanSpace ℂ (Idx T m)))
    exact this.mp hinj
  exact (ContinuousLinearMap.isUnit_iff_bijective).mpr ⟨hinj, hsurj⟩

theorem hard_inverse_norm_le (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (x : Fin n → Fin m) :
    ‖Ring.inverse (SparseStateOverlap.matrixOperator (hardMatrix (T := T) r x))‖ ≤ 2 / (1 - r) := by
  set A := SparseStateOverlap.matrixOperator (hardMatrix (T := T) r x)
  have hU := hard_isUnit (T := T) r hr0 hr1 x
  have hpos : 0 < 1 - r := by linarith
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  have hAA : A (Ring.inverse A v) = v := by
    have e := congrArg (fun f : EuclideanSpace ℂ (Idx T m) →L[ℂ] _ => f v)
      (Ring.mul_inverse_cancel A hU)
    simpa only [mul_apply_eq_comp, one_apply_eq_self] using e
  have h := hard_lower r hr0 x (Ring.inverse A v)
  rw [hAA] at h
  rw [div_mul_eq_mul_div, le_div_iff₀ hpos]
  nlinarith [norm_nonneg (Ring.inverse A v)]

/-! ### Real symmetry -/

omit [NeZero m] in
theorem swapM_symm (p q : Idx T m) : (swapM : Matrix (Idx T m) (Idx T m) ℂ) p q = swapM q p := by
  simp only [swapM, Matrix.of_apply]
  congr 1
  apply propext
  rcases p with ⟨σ, t⟩
  rcases q with ⟨τ, t'⟩
  cases σ <;> cases τ <;> simp [eq_comm]

theorem dil_symm (x : Fin n → Fin m) (p q : Idx T m) : dil x p q = dil x q p := by
  rcases p with ⟨σ, t⟩
  rcases q with ⟨τ, t'⟩
  cases σ <;> cases τ <;> simp [dil]

theorem hard_symm (r : ℝ) (x : Fin n → Fin m) (p q : Idx T m) :
    hardMatrix r x p q = hardMatrix r x q p := by
  simp only [hardMatrix, Matrix.smul_apply, Matrix.sub_apply, swapM_symm p q, dil_symm x p q]

theorem gadget_im (j a b : Fin m) : (gadget j a b).im = 0 := by
  simp only [gadget, Matrix.of_apply]
  split_ifs <;> simp [Complex.div_im]

theorem step_im (x : Fin n → Fin m) (i : Fin T) (a b : Fin m) : (step x i a b).im = 0 := by
  unfold step
  split_ifs
  · exact gadget_im _ _ _
  · simp [Matrix.one_apply]; split_ifs <;> simp

theorem clock_im (x : Fin n → Fin m) (p q : Fin (T + 1) × Fin m) : (clock x p q).im = 0 := by
  simp only [clock, Matrix.of_apply]
  split_ifs
  · exact step_im _ _ _ _
  · simp

theorem hard_im (r : ℝ) (x : Fin n → Fin m) (p q : Idx T m) : (hardMatrix r x p q).im = 0 := by
  have hd : (dil x p q).im = 0 := by
    simp only [dil, Matrix.of_apply]
    split_ifs
    · exact clock_im _ _ _
    · exact clock_im _ _ _
    · simp
  have hs : ((swapM : Matrix (Idx T m) (Idx T m) ℂ) p q).im = 0 := by
    simp only [swapM, Matrix.of_apply]
    split_ifs <;> simp
  simp only [hardMatrix, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, Complex.mul_im,
    Complex.sub_im, Complex.sub_re, Complex.ofReal_im, Complex.ofReal_re, hd, hs]
  norm_num

/-! ### Entries depend on at most one bit -/

/-- A function of the input which is constant or depends only on one bit `[x_c = q₀]`. -/
def BitDetermined {α : Type*} (f : (Fin n → Fin m) → α) : Prop :=
  (∃ e, ∀ x, f x = e) ∨ ∃ (c : Fin n) (q₀ : Fin m) (e₀ e₁ : α),
    ∀ x, f x = if x c = q₀ then e₁ else e₀

omit [NeZero m] in
theorem BitDetermined.comp {α β : Type*} {f : (Fin n → Fin m) → α} (hf : BitDetermined f)
    (g : α → β) : BitDetermined (fun x => g (f x)) := by
  rcases hf with ⟨e, he⟩ | ⟨c, q₀, e₀, e₁, he⟩
  · exact Or.inl ⟨g e, fun x => by show g (f x) = g e; rw [he]⟩
  · refine Or.inr ⟨c, q₀, g e₀, g e₁, fun x => ?_⟩
    show g (f x) = _
    rw [he]
    split_ifs <;> rfl

theorem bitDetermined_clock (p q : Fin (T + 1) × Fin m) :
    BitDetermined (fun x : Fin n → Fin m => clock x p q) := by
  by_cases h : p.1.val = q.1.val + 1
  · by_cases hn : q.1.val < n
    · refine Or.inr ⟨⟨q.1.val, hn⟩, p.2 - q.2 - 1, (2 / m : ℂ), (2 / m : ℂ) - 1, fun x => ?_⟩
      simp only [clock, Matrix.of_apply, dif_pos h, step, dif_pos hn, gadget, eq_comm (a := x _)]
      split_ifs <;> simp
    · refine Or.inl ⟨(1 : Matrix (Fin m) (Fin m) ℂ) p.2 q.2, fun x => ?_⟩
      simp only [clock, Matrix.of_apply, dif_pos h, step, dif_neg hn]
  · exact Or.inl ⟨0, fun x => by simp only [clock, Matrix.of_apply, dif_neg h]⟩

theorem bitDetermined_hard (r : ℝ) (p q : Idx T m) :
    BitDetermined (fun x : Fin n → Fin m => hardMatrix r x p q) := by
  have hd : BitDetermined (fun x : Fin n → Fin m => dil x p q) := by
    rcases p with ⟨σ, t⟩
    rcases q with ⟨τ, t'⟩
    cases σ <;> cases τ
    · exact Or.inl ⟨0, fun x => by simp [dil]⟩
    · simpa [dil] using bitDetermined_clock (n := n) t t'
    · simpa [dil] using bitDetermined_clock (n := n) t' t
    · exact Or.inl ⟨0, fun x => by simp [dil]⟩
  exact hd.comp (fun z => (1 / 2 : ℂ) * ((swapM : Matrix (Idx T m) (Idx T m) ℂ) p q - (r : ℂ) * z))

/-! ### Input-independent support -/

/-- The clock block of a row: `t - 1` in the `false` sector rows, `t + 1` in the `true`
sector rows. -/
def blockRel (p q : Idx T m) : Prop :=
  if p.1 then q.2.1.val = p.2.1.val + 1 else p.2.1.val = q.2.1.val + 1

instance (p q : Idx T m) : Decidable (blockRel p q) := by
  unfold blockRel; split_ifs <;> infer_instance

/-- Possible nonzero positions of a row: the swapped diagonal and one clock block. -/
def support (p : Idx T m) : Finset (Idx T m) :=
  insert (!p.1, p.2) (Finset.univ.filter fun q : Idx T m => q.1 = !p.1 ∧ blockRel p q)

theorem hard_support (r : ℝ) (x : Fin n → Fin m) (p q : Idx T m) (h : hardMatrix r x p q ≠ 0) :
    q ∈ support p := by
  rw [support, Finset.mem_insert, Finset.mem_filter]
  by_contra hq
  push Not at hq
  obtain ⟨hne, hq⟩ := hq
  apply h
  have hs : (swapM : Matrix (Idx T m) (Idx T m) ℂ) p q = 0 := by
    simp only [swapM, Matrix.of_apply]
    rw [if_neg]
    rintro ⟨h1, h2⟩
    apply hne
    rcases p with ⟨σ, t⟩
    rcases q with ⟨τ, t'⟩
    simp only at h1 h2 ⊢
    rw [h1, h2]
    simp
  have hd : dil x p q = 0 := by
    rcases p with ⟨σ, t, a⟩
    rcases q with ⟨τ, t', b⟩
    have hq' := hq (Finset.mem_univ _)
    cases σ <;> cases τ <;> simp only [dil, Matrix.of_apply, blockRel] at hq' ⊢ <;>
      simp at hq' ⊢
    · simp only [clock, Matrix.of_apply]
      rw [dif_neg hq']
    · simp only [clock, Matrix.of_apply]
      rw [dif_neg hq']
  simp [hardMatrix, hs, hd]

omit [NeZero m] in
theorem card_support_le (p : Idx T m) : (support p).card ≤ m + 1 := by
  rw [support]
  apply (Finset.card_insert_le _ _).trans
  apply Nat.add_le_add_right
  have hinj : Set.InjOn (fun q : Idx T m => q.2.2)
      ((Finset.univ.filter fun q : Idx T m => q.1 = !p.1 ∧ blockRel p q : Finset (Idx T m)) :
        Set (Idx T m)) := by
    intro q hq q' hq' heq
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hq hq'
    obtain ⟨h1, h2⟩ := hq
    obtain ⟨h1', h2'⟩ := hq'
    rcases q with ⟨τ, t, b⟩
    rcases q' with ⟨τ', t', b'⟩
    simp only at h1 h1' heq ⊢
    have ht : t = t' := by
      unfold blockRel at h2 h2'
      split_ifs at h2 h2' <;> ext <;> simp only at h2 h2' <;> omega
    rw [h1, h1', ht, heq]
  have := Finset.card_le_card_of_injOn (fun q : Idx T m => q.2.2)
    (fun q _ => Finset.mem_univ _) hinj
  simpa using this

end

end LinearSystemLowerBound.Hard
