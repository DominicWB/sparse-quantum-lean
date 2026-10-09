import GeneralODE.Analysis.Recursion

/-!
# The augmented history system

Slots are `none` (the forcing slot) and `some j`, `0 ≤ j ≤ 2m`.  The implemented
history matrix has diagonal `P₀`, subdiagonal `V` on the first `m` steps and
`P₀` on the padded copies, and one source column `Φ/√m` from the forcing slot to
the slots `1, …, m`.  For the right-hand side `(μ b, x₀, 0, …)` with
`μ/√m = h`, its solution follows `y_j = Ê y_{j-1} + ŝ`, `Ê = P₀⁻¹ V`,
`ŝ = h P₀⁻¹ Φ P₀⁻¹ b`, and the padded copies equal `y_m` exactly.  We bound the
inverse of the residual map by `O(m c)`, `c` a bound for the powers of `Ê`.
-/

namespace SparseHamiltonian.GeneralODE.History

noncomputable section
open scoped BigOperators InnerProduct
open NormedSpace

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P]

/-- History slots: `none` carries the forcing, `some j` the time slot `j ≤ 2m`. -/
abbrev Slot (m : ℕ) := Option (Fin (2 * m + 1))

/-- History vectors. -/
abbrev Space (m : ℕ) (P : Type*) [NormedAddCommGroup P] [InnerProductSpace ℂ P] :=
  PiLp 2 (fun _ : Slot m => P)

/-- Time-slot coordinates as a sequence, zero beyond `2m`. -/
def seq {m : ℕ} (y : Space m P) (j : ℕ) : P :=
  if h : j < 2 * m + 1 then y (some ⟨j, h⟩) else 0

theorem seq_some {m : ℕ} (y : Space m P) (j : Fin (2 * m + 1)) : seq y j.val = y (some j) := by
  simp [seq, j.isLt]

theorem seq_of_lt {m : ℕ} (y : Space m P) (j : ℕ) (h : j < 2 * m + 1) :
    seq y j = y (some ⟨j, h⟩) := by
  simp [seq, h]

/-- Coupling of the source column. -/
def coupling (m : ℕ) : ℂ := ((Real.sqrt m)⁻¹ : ℝ)

/-- Residual of the implemented history equations. -/
def residual (m : ℕ) (P0 V Φ : P →L[ℂ] P) (y : Space m P) : Space m P :=
  WithLp.toLp 2 fun s => match s with
    | none => P0 (y none)
    | some j => P0 (y (some j)) -
        (if 1 ≤ j.val ∧ j.val ≤ m then V (seq y (j.val - 1)) + coupling m • Φ (y none)
         else if m < j.val then P0 (seq y (j.val - 1)) else 0)

@[simp] theorem residual_none (m : ℕ) (P0 V Φ : P →L[ℂ] P) (y : Space m P) :
    residual m P0 V Φ y none = P0 (y none) := rfl

theorem residual_some (m : ℕ) (P0 V Φ : P →L[ℂ] P) (y : Space m P) (j : Fin (2 * m + 1)) :
    residual m P0 V Φ y (some j) = P0 (y (some j)) -
        (if 1 ≤ j.val ∧ j.val ≤ m then V (seq y (j.val - 1)) + coupling m • Φ (y none)
         else if m < j.val then P0 (seq y (j.val - 1)) else 0) := rfl

/-- The residual is linear. -/
theorem residual_sub (m : ℕ) (P0 V Φ : P →L[ℂ] P) (y z : Space m P) :
    residual m P0 V Φ (y - z) = residual m P0 V Φ y - residual m P0 V Φ z := by
  ext s
  rcases s with _ | j
  · simp [residual]
  · have hseq (k : ℕ) : seq (y - z) k = seq y k - seq z k := by
      unfold seq; split_ifs <;> simp
    simp only [residual, PiLp.sub_apply, WithLp.ofLp_toLp, map_sub, hseq]
    split_ifs <;> (try simp only [smul_sub, sub_zero]) <;> abel

section Norms

theorem norm_coord_le {m : ℕ} (y : Space m P) (s : Slot m) : ‖y s‖ ≤ ‖y‖ :=
  PiLp.norm_apply_le y s

theorem norm_seq_le {m : ℕ} (y : Space m P) (j : ℕ) : ‖seq y j‖ ≤ ‖y‖ := by
  unfold seq; split_ifs
  · exact norm_coord_le y _
  · simp

/-- Squared norm splits into the forcing slot and the time slots. -/
theorem norm_sq_eq {m : ℕ} (y : Space m P) :
    ‖y‖ ^ 2 = ‖y none‖ ^ 2 + ∑ j ∈ Finset.range (2 * m + 1), ‖seq y j‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, Fintype.sum_option]
  congr 1
  rw [← Fin.sum_univ_eq_sum_range (fun j => ‖seq y j‖ ^ 2)]
  apply Finset.sum_congr rfl
  intro j _
  rw [seq_some]

/-- Cauchy–Schwarz for the time slots. -/
theorem sum_norm_seq_le {m : ℕ} (y : Space m P) :
    ∑ j ∈ Finset.range (2 * m + 1), ‖seq y j‖ ≤ Real.sqrt (2 * m + 1) * ‖y‖ := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range (2 * m + 1))
    (fun _ => (1 : ℝ)) (fun j => ‖seq y j‖)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    mul_one] at hcs
  have hsq : ∑ j ∈ Finset.range (2 * m + 1), ‖seq y j‖ ^ 2 ≤ ‖y‖ ^ 2 := by
    rw [norm_sq_eq y]; nlinarith [sq_nonneg ‖y none‖]
  have hnn : 0 ≤ ∑ j ∈ Finset.range (2 * m + 1), ‖seq y j‖ :=
    Finset.sum_nonneg (fun j _ => norm_nonneg _)
  have h2 : (∑ j ∈ Finset.range (2 * m + 1), ‖seq y j‖) ^ 2 ≤
      ((2 * m + 1 : ℕ) : ℝ) * ‖y‖ ^ 2 :=
    hcs.trans (mul_le_mul_of_nonneg_left hsq (by positivity))
  have h3 : Real.sqrt ((2 * m + 1 : ℕ) : ℝ) * ‖y‖ =
      Real.sqrt ((2 * m + 1 : ℕ) * ‖y‖ ^ 2) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]
  push_cast at h3
  rw [h3]
  exact Real.le_sqrt_of_sq_le (by push_cast at h2; linarith)

end Norms

section Inverse

variable {m : ℕ} (P0 V Φ Q0 : P →L[ℂ] P)

/-- Explicit inverse bound for the residual map. -/
def kappaH (m : ℕ) (q φ c : ℝ) : ℝ := q + c * (2 * m + 1) * (q + q ^ 2 * φ)

theorem coupling_norm (hm : 1 ≤ m) : ‖coupling m‖ = (Real.sqrt m)⁻¹ := by
  have hpos : 0 < Real.sqrt m := Real.sqrt_pos.mpr (by exact_mod_cast hm)
  simp [coupling]

/-- The time-slot recursion satisfied by any vector, in terms of its residual. -/
theorem seq_step (hQ : Q0 * P0 = 1) (y : Space m P) (j : ℕ) (hj1 : 1 ≤ j) (hjm : j ≤ m) :
    seq y j = (Q0 * V) (seq y (j - 1)) +
      (coupling m • (Q0 (Φ (y none))) + Q0 (seq (residual m P0 V Φ y) j)) := by
  have hlt : j < 2 * m + 1 := by omega
  have hres := residual_some m P0 V Φ y ⟨j, hlt⟩
  rw [if_pos (show 1 ≤ (⟨j, hlt⟩ : Fin (2 * m + 1)).val ∧ (⟨j, hlt⟩ : Fin (2 * m + 1)).val ≤ m
    from ⟨hj1, hjm⟩)] at hres
  have hQv (v : P) : Q0 (P0 v) = v := by
    have := congrArg (fun T : P →L[ℂ] P => T v) hQ; simpa using this
  have hP : P0 (y (some ⟨j, hlt⟩)) = residual m P0 V Φ y (some ⟨j, hlt⟩) +
      (V (seq y (j - 1)) + coupling m • Φ (y none)) := by
    rw [hres]; abel
  rw [seq_of_lt y j hlt, seq_of_lt (residual m P0 V Φ y) j hlt, ← hQv (y (some ⟨j, hlt⟩)), hP,
    map_add, map_add, map_smul]
  simp only [mul_apply_eq_comp]
  abel

/-- Padded slots copy their predecessor up to the residual. -/
theorem seq_copy (hQ : Q0 * P0 = 1) (y : Space m P) (j : ℕ) (hj : m < j) (hj2 : j ≤ 2 * m) :
    seq y j = seq y (j - 1) + Q0 (seq (residual m P0 V Φ y) j) := by
  have hlt : j < 2 * m + 1 := by omega
  have hres := residual_some m P0 V Φ y ⟨j, hlt⟩
  have hn : ¬ (1 ≤ j ∧ j ≤ m) := by omega
  simp only [hn, if_false, show m < j from hj, if_true] at hres
  have hQv (v : P) : Q0 (P0 v) = v := by
    have := congrArg (fun T : P →L[ℂ] P => T v) hQ; simpa using this
  rw [seq_of_lt y j hlt, seq_of_lt (residual m P0 V Φ y) j hlt]
  have h2 : y (some ⟨j, hlt⟩) = Q0 (P0 (y (some ⟨j, hlt⟩))) := (hQv _).symm
  rw [h2]
  have h3 : P0 (y (some ⟨j, hlt⟩)) = residual m P0 V Φ y (some ⟨j, hlt⟩) +
      P0 (seq y (j - 1)) := by rw [hres]; abel
  rw [h3, map_add, hQv]
  abel

theorem seq_zero (hQ : Q0 * P0 = 1) (y : Space m P) :
    seq y 0 = Q0 (seq (residual m P0 V Φ y) 0) := by
  have hlt : 0 < 2 * m + 1 := by omega
  have hres := residual_some m P0 V Φ y ⟨0, hlt⟩
  simp only [show ¬ (1 ≤ 0 ∧ 0 ≤ m) by omega, if_false, show ¬ m < 0 by omega,
    sub_zero] at hres
  have hQv (v : P) : Q0 (P0 v) = v := by
    have := congrArg (fun T : P →L[ℂ] P => T v) hQ; simpa using this
  rw [seq_of_lt y 0 hlt, seq_of_lt (residual m P0 V Φ y) 0 hlt, hres, hQv]

theorem none_eq (hQ : Q0 * P0 = 1) (y : Space m P) :
    y none = Q0 (residual m P0 V Φ y none) := by
  have hQv (v : P) : Q0 (P0 v) = v := by
    have := congrArg (fun T : P →L[ℂ] P => T v) hQ; simpa using this
  rw [residual_none, hQv]

set_option maxHeartbeats 1000000 in
/-- The inverse of the residual map has norm `O(m c)`. -/
theorem norm_le_kappaH (hm : 1 ≤ m) (hQ : Q0 * P0 = 1) (q φ c : ℝ)
    (hq : ‖Q0‖ ≤ q) (hφ : ‖Φ‖ ≤ φ) (hc1 : 1 ≤ c)
    (hc : ∀ k, k ≤ m → ‖(Q0 * V) ^ k‖ ≤ c) (y : Space m P) :
    ‖y‖ ≤ kappaH m q φ c * ‖residual m P0 V Φ y‖ := by
  set r := residual m P0 V Φ y with hr
  set R := ‖r‖
  have hq0 : 0 ≤ q := (norm_nonneg _).trans hq
  have hφ0 : 0 ≤ φ := (norm_nonneg _).trans hφ
  have hR0 : 0 ≤ R := norm_nonneg _
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.mpr (by linarith)
  -- forcing slot
  have hw : ‖y none‖ ≤ q * R := by
    rw [none_eq P0 V Φ Q0 hQ y]
    exact (Q0.le_opNorm _).trans (mul_le_mul hq (norm_coord_le r none) (norm_nonneg _) hq0)
  -- the sum of residual time slots
  set S := ∑ j ∈ Finset.range (2 * m + 1), ‖seq r j‖ with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun j _ => norm_nonneg _)
  -- the coupled source term
  set g0 : P := coupling m • Q0 (Φ (y none)) with hg0
  have hg0n : ‖g0‖ ≤ (Real.sqrt m)⁻¹ * (q * (φ * (q * R))) := by
    rw [hg0, norm_smul, coupling_norm hm]
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hsm.le)
    refine (Q0.le_opNorm _).trans (mul_le_mul hq ?_ (norm_nonneg _) hq0)
    exact (Φ.le_opNorm _).trans (mul_le_mul hφ hw (norm_nonneg _) hφ0)
  -- first segment
  have hfirst : ∀ j, j ≤ m → ‖seq y j‖ ≤
      c * (q * ‖seq r 0‖ + ∑ i ∈ Finset.range j, (‖g0‖ + q * ‖seq r (i + 1)‖)) := by
    intro j hj
    have hrec : ∀ k, k < m → seq y (k + 1) =
        (Q0 * V) (seq y k) + (g0 + Q0 (seq r (k + 1))) := by
      intro k hk
      have := seq_step P0 V Φ Q0 hQ y (k + 1) (by omega) (by omega)
      simpa using this
    have h := Recursion.norm_le_of_unroll_le (Q0 * V) (seq y)
      (fun k => g0 + Q0 (seq r k)) m hrec c hc j hj
    refine h.trans (mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (by linarith))
    · rw [seq_zero P0 V Φ Q0 hQ y]
      exact (Q0.le_opNorm _).trans (mul_le_mul_of_nonneg_right hq (norm_nonneg _))
    · apply Finset.sum_le_sum
      intro i _
      exact (norm_add_le _ _).trans (add_le_add le_rfl
        ((Q0.le_opNorm _).trans (mul_le_mul_of_nonneg_right hq (norm_nonneg _))))
  -- uniform bound on every time slot
  have hall : ∀ j, j ≤ 2 * m → ‖seq y j‖ ≤
      c * (q * S + m * ((Real.sqrt m)⁻¹ * (q * (φ * (q * R))))) := by
    have hmain : ∀ j, j ≤ m → ‖seq y j‖ ≤
        c * (q * (∑ i ∈ Finset.range (j + 1), ‖seq r i‖) +
          j * ((Real.sqrt m)⁻¹ * (q * (φ * (q * R))))) := by
      intro j hj
      refine (hfirst j hj).trans (mul_le_mul_of_nonneg_left ?_ (by linarith))
      rw [Finset.sum_add_distrib, Finset.sum_range_succ', ← Finset.mul_sum]
      have hsum : ∑ i ∈ Finset.range j, ‖g0‖ ≤
          j * ((Real.sqrt m)⁻¹ * (q * (φ * (q * R)))) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_left hg0n (by positivity)
      nlinarith [hsum]
    intro j hj
    by_cases hjm : j ≤ m
    · refine (hmain j hjm).trans (mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (by linarith))
      · apply mul_le_mul_of_nonneg_left _ hq0
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_subset_range.mpr (by omega)) (fun _ _ _ => norm_nonneg _)
      · apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast hjm
    · -- padded copies
      have hcopy : ∀ k, k ≤ j - m → ‖seq y (m + k)‖ ≤ ‖seq y m‖ +
          q * ∑ i ∈ Finset.range k, ‖seq r (m + i + 1)‖ := by
        intro k
        induction k with
        | zero => intro _; simp
        | succ k ih =>
            intro hk
            have hst := seq_copy P0 V Φ Q0 hQ y (m + (k + 1)) (by omega) (by omega)
            rw [show m + (k + 1) - 1 = m + k by omega] at hst
            rw [hst, Finset.sum_range_succ, mul_add]
            refine (norm_add_le _ _).trans ?_
            have h1 := ih (by omega)
            have h2 : ‖Q0 (seq r (m + (k + 1)))‖ ≤ q * ‖seq r (m + k + 1)‖ := by
              rw [show m + (k + 1) = m + k + 1 by omega]
              exact (Q0.le_opNorm _).trans (mul_le_mul_of_nonneg_right hq (norm_nonneg _))
            linarith
      have hj' := hcopy (j - m) le_rfl
      rw [show m + (j - m) = j by omega] at hj'
      refine hj'.trans ?_
      have hm' := hmain m le_rfl
      have hsplit : ∑ i ∈ Finset.range (m + 1), ‖seq r i‖ +
          ∑ i ∈ Finset.range (j - m), ‖seq r (m + i + 1)‖ ≤ S := by
        rw [hS]
        have : ∑ i ∈ Finset.range (j - m), ‖seq r (m + i + 1)‖ =
            ∑ i ∈ Finset.range (j - m), ‖seq r (m + 1 + i)‖ := by
          apply Finset.sum_congr rfl; intro i _; rw [show m + i + 1 = m + 1 + i by omega]
        rw [this, ← Finset.sum_range_add]
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_subset_range.mpr (by omega)) (fun _ _ _ => norm_nonneg _)
      have hpos : 0 ≤ ∑ i ∈ Finset.range (j - m), ‖seq r (m + i + 1)‖ :=
        Finset.sum_nonneg (fun _ _ => norm_nonneg _)
      have hcq : q ≤ c * q := by nlinarith
      nlinarith [hm', hsplit, hpos, hcq,
        mul_le_mul_of_nonneg_left hsplit (mul_nonneg (by linarith : (0 : ℝ) ≤ c) hq0)]
  -- convert to the norm of r
  have hSR : S ≤ Real.sqrt (2 * m + 1) * R := sum_norm_seq_le r
  set sq := Real.sqrt (2 * m + 1) with hsq
  have hs2 : sq * sq = 2 * m + 1 := Real.mul_self_sqrt (by positivity)
  have hs0 : 0 ≤ sq := Real.sqrt_nonneg _
  have hmsq : (m : ℝ) * (Real.sqrt m)⁻¹ ≤ sq := by
    have : (m : ℝ) * (Real.sqrt m)⁻¹ = Real.sqrt m := by
      field_simp
      rw [Real.sq_sqrt (by linarith)]
    rw [this, hsq]
    exact Real.sqrt_le_sqrt (by linarith)
  set B := c * (q * (sq * R) + sq * (q * (φ * (q * R)))) with hB
  have hslot : ∀ j, j ≤ 2 * m → ‖seq y j‖ ≤ B := by
    intro j hj
    refine (hall j hj).trans (mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (by linarith))
    · exact mul_le_mul_of_nonneg_left hSR hq0
    · have h1 : (m : ℝ) * ((Real.sqrt m)⁻¹ * (q * (φ * (q * R)))) =
          ((m : ℝ) * (Real.sqrt m)⁻¹) * (q * (φ * (q * R))) := by ring
      rw [h1]
      exact mul_le_mul_of_nonneg_right hmsq (by positivity)
  -- total norm
  have hnorm : ‖y‖ ^ 2 ≤ (q * R) ^ 2 + (2 * m + 1) * B ^ 2 := by
    rw [norm_sq_eq y]
    have h1 : ‖y none‖ ^ 2 ≤ (q * R) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hw 2
    have h2 : ∑ j ∈ Finset.range (2 * m + 1), ‖seq y j‖ ^ 2 ≤
        ∑ j ∈ Finset.range (2 * m + 1), B ^ 2 :=
      Finset.sum_le_sum (fun j hj =>
        pow_le_pow_left₀ (norm_nonneg _) (hslot j (by have := Finset.mem_range.mp hj; omega)) 2)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h2
    push_cast at h2
    linarith
  have hB0 : 0 ≤ B := by positivity
  have hsB : sq * B = c * (2 * m + 1) * (q + q ^ 2 * φ) * R := by
    have : sq * B = c * (sq * sq) * (q + q ^ 2 * φ) * R := by rw [hB]; ring
    rw [this, hs2]
  have hsq2 : (2 * m + 1) * B ^ 2 = (sq * B) ^ 2 := by
    rw [mul_pow, ← hs2]; ring
  have hk : kappaH m q φ c * R = q * R + sq * B := by
    rw [hsB]; unfold kappaH; ring
  have hsum0 : 0 ≤ q * R + sq * B := by positivity
  rw [hk]
  have hfin : ‖y‖ ^ 2 ≤ (q * R + sq * B) ^ 2 := by
    rw [hsq2] at hnorm
    nlinarith [mul_nonneg (mul_nonneg hq0 hR0) (mul_nonneg hs0 hB0)]
  nlinarith [norm_nonneg y, hfin, hsum0]

end Inverse

end

end SparseHamiltonian.GeneralODE.History
