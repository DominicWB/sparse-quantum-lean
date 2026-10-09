import SparseLowerBounds.Helpers.InstanceDecoder.Clock

set_option synthInstance.maxHeartbeats 400000

section
/-!
# Helper: shape of the dilated open clock

Reality, symmetry and sparsity of `dilation (clockMatrix T r L)` for real transitions.
Used by `SparseLowerBounds.LinearSystems.Instance`.
-/

namespace SparseLowerBounds.Helpers.InstanceDecoder

noncomputable section
open SparseLowerBounds.LinearSystems
open scoped Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
/-- The open clock has real entries when every transition does. -/
theorem star_clockMatrix_apply (T : ℕ) (r : ℝ) (L : ℕ → Matrix ι ι ℂ)
    (hL : ∀ t a b, star (L t a b) = L t a b) (p q : Fin T × ι) :
    star (clockMatrix T r L p q) = clockMatrix T r L p q := by
  have hL' : ∀ t a b, (starRingEnd ℂ) (L t a b) = L t a b := hL
  simp only [clockMatrix, clockShift, Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply,
    Matrix.of_apply, smul_eq_mul, Complex.star_def, map_mul, map_sub, map_inv₀, map_ofNat,
    Complex.conj_ofReal]
  split_ifs <;> simp [hL']

/-- The dilation of a real matrix is symmetric. -/
theorem dilation_transpose {β : Type*} (C : Matrix β β ℂ) (hC : ∀ x y, star (C x y) = C x y) :
    (dilation C)ᵀ = dilation C := by
  ext p q
  obtain ⟨i, x⟩ := p
  obtain ⟨k, y⟩ := q
  simp only [Matrix.transpose_apply, dilation, Matrix.of_apply]
  fin_cases i <;> fin_cases k <;> simp [hC]

/-- The dilation of a real matrix is real. -/
theorem star_dilation_apply {β : Type*} (C : Matrix β β ℂ) (hC : ∀ x y, star (C x y) = C x y)
    (p q : Fin 2 × β) : star (dilation C p q) = dilation C p q := by
  obtain ⟨i, x⟩ := p
  obtain ⟨k, y⟩ := q
  simp only [dilation, Matrix.of_apply]
  fin_cases i <;> fin_cases k <;> simp [hC]

omit [Fintype ι] in
/-- Support of the open clock: the diagonal and the subdiagonal clock block. -/
theorem clockMatrix_apply_ne_zero {T : ℕ} {r : ℝ} {L : ℕ → Matrix ι ι ℂ} {x y : Fin T × ι}
    (h : clockMatrix T r L x y ≠ 0) : x = y ∨ (x.1 : ℕ) = y.1 + 1 := by
  by_contra hc
  push Not at hc
  apply h
  simp [clockMatrix, clockShift, Matrix.one_apply_ne hc.1, hc.2]

omit [Fintype ι] in
/-- Support of a row of the dilated open clock. -/
theorem dilation_clockMatrix_ne_zero {T : ℕ} {r : ℝ} {L : ℕ → Matrix ι ι ℂ}
    {p q : Fin 2 × Fin T × ι} (h : dilation (clockMatrix T r L) p q ≠ 0) :
    q.1 ≠ p.1 ∧ (q.2 = p.2 ∨
      (if p.1 = 0 then (q.2.1 : ℕ) + 1 = p.2.1 else (q.2.1 : ℕ) = p.2.1 + 1)) := by
  obtain ⟨i, x⟩ := p
  obtain ⟨k, y⟩ := q
  simp only [dilation, Matrix.of_apply] at h
  fin_cases i <;> fin_cases k
  · simp at h
  · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, true_and, if_true] at h
    rcases clockMatrix_apply_ne_zero h with h' | h'
    · exact ⟨by simp, Or.inl h'.symm⟩
    · exact ⟨by simp, Or.inr (by simp only [Fin.zero_eta, Fin.isValue, if_true]; omega)⟩
  · simp only [Fin.mk_one, Fin.isValue, Fin.zero_eta, one_ne_zero, false_and, if_false,
      true_and, if_true, ne_eq, star_eq_zero] at h
    rcases clockMatrix_apply_ne_zero h with h' | h'
    · exact ⟨by simp, Or.inl h'⟩
    · exact ⟨by simp, Or.inr (by simp only [Fin.mk_one, Fin.isValue, one_ne_zero, if_false]; omega)⟩
  · simp at h

/-- Row sparsity `card ι + 1` of the dilated open clock. -/
theorem dilation_clockMatrix_row_sparse (T : ℕ) (r : ℝ) (L : ℕ → Matrix ι ι ℂ)
    (p : Fin 2 × Fin T × ι) :
    (Finset.univ.filter fun q => dilation (clockMatrix T r L) p q ≠ 0).card ≤
      Fintype.card ι + 1 := by
  classical
  have h2 : ∀ a b c : Fin 2, a ≠ c → b ≠ c → a = b := by decide
  calc (Finset.univ.filter fun q => dilation (clockMatrix T r L) p q ≠ 0).card
      ≤ (Finset.univ : Finset (Option ι)).card := by
        apply Finset.card_le_card_of_injOn
          (fun q : Fin 2 × Fin T × ι => if q.2.1 = p.2.1 then none else some q.2.2)
        · intro _ _; simp
        · intro q hq q' hq' heq
          simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hq hq'
          obtain ⟨hq1, hq2⟩ := dilation_clockMatrix_ne_zero hq
          obtain ⟨hq1', hq2'⟩ := dilation_clockMatrix_ne_zero hq'
          have e1 : q.1 = q'.1 := h2 _ _ _ hq1 hq1'
          simp only at heq
          by_cases hc : q.2.1 = p.2.1
          · by_cases hc' : q'.2.1 = p.2.1
            · have hA : q.2 = p.2 := by
                rcases hq2 with h | h
                · exact h
                · exfalso; rw [hc] at h; split_ifs at h <;> omega
              have hB : q'.2 = p.2 := by
                rcases hq2' with h | h
                · exact h
                · exfalso; rw [hc'] at h; split_ifs at h <;> omega
              exact Prod.ext e1 (hA.trans hB.symm)
            · rw [if_pos hc, if_neg hc'] at heq; exact absurd heq (by simp)
          · by_cases hc' : q'.2.1 = p.2.1
            · rw [if_neg hc, if_pos hc'] at heq; exact absurd heq (by simp)
            · rw [if_neg hc, if_neg hc'] at heq
              have e3 : q.2.2 = q'.2.2 := Option.some_injective _ heq
              have hA : (if p.1 = 0 then (q.2.1 : ℕ) + 1 = p.2.1 else (q.2.1 : ℕ) = p.2.1 + 1) := by
                rcases hq2 with h | h
                · exact absurd (congrArg Prod.fst h) hc
                · exact h
              have hB : (if p.1 = 0 then (q'.2.1 : ℕ) + 1 = p.2.1 else (q'.2.1 : ℕ) = p.2.1 + 1) := by
                rcases hq2' with h | h
                · exact absurd (congrArg Prod.fst h) hc'
                · exact h
              have e2 : q.2.1 = q'.2.1 := by
                apply Fin.ext
                split_ifs at hA hB <;> omega
              exact Prod.ext e1 (Prod.ext e2 e3)
    _ = Fintype.card ι + 1 := by simp

end

end SparseLowerBounds.Helpers.InstanceDecoder
end
