import GeneralODE.Analysis.History

/-!
# The history solution and its accuracy

For the right-hand side `(μ b, x₀, 0, …, 0)` the implemented history system
has the explicit solution `ŷ_w = P₀⁻¹ μ b`, `ŷ_j = s_{min j m}` with
`s_0 = P₀⁻¹ x₀`, `s_{j+1} = Ê s_j + ŝ`.  The exact samples `x_j = x(jh)` obey
`x_{j+1} = e^{hA} x_j + ∫₀ʰ e^{uA} b du`.  Comparing the two recursions with the
discrete Gronwall bound gives the accuracy of the final copies.  The forcing
mass is controlled by the samples themselves: `T‖b‖ ≤ (3 + 2ΛT) max_j ‖x_j‖`
when `Λ h ≤ 1/8`.
-/

namespace SparseHamiltonian.GeneralODE.History

noncomputable section
open scoped BigOperators InnerProduct
open NormedSpace ODEDissipative ODEConstantForcing ExpBounds

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P]

section Solution

variable (m : ℕ) (P0 V Φ Q0 : P →L[ℂ] P)

/-- The implemented one-step source `ŝ = (μ/√m) P₀⁻¹ Φ P₀⁻¹ b`. -/
def stepSource (μ : ℝ) (b : P) : P := coupling m • Q0 (Φ (Q0 ((μ : ℂ) • b)))

/-- The implemented trajectory on the first `m + 1` slots. -/
def solSeq (μ : ℝ) (x0 b : P) : ℕ → P
  | 0 => Q0 x0
  | j + 1 => (Q0 * V) (solSeq μ x0 b j) + stepSource m Φ Q0 μ b

/-- The history right-hand side `(μ b, x₀, 0, …)`. -/
def rhs (μ : ℝ) (x0 b : P) : Space m P :=
  WithLp.toLp 2 fun s => match s with
    | none => (μ : ℂ) • b
    | some j => if j.val = 0 then x0 else 0

/-- The explicit solution vector. -/
def solution (μ : ℝ) (x0 b : P) : Space m P :=
  WithLp.toLp 2 fun s => match s with
    | none => Q0 ((μ : ℂ) • b)
    | some j => solSeq m V Φ Q0 μ x0 b (min j.val m)

theorem seq_solution (μ : ℝ) (x0 b : P) (j : ℕ) (hj : j < 2 * m + 1) :
    seq (solution m V Φ Q0 μ x0 b) j = solSeq m V Φ Q0 μ x0 b (min j m) := by
  rw [seq_of_lt _ j hj]; rfl

theorem solution_none (μ : ℝ) (x0 b : P) :
    solution m V Φ Q0 μ x0 b none = Q0 ((μ : ℂ) • b) := rfl

/-- The explicit vector solves the implemented history system. -/
theorem residual_solution (hQ : P0 * Q0 = 1) (μ : ℝ) (x0 b : P) :
    residual m P0 V Φ (solution m V Φ Q0 μ x0 b) = rhs m μ x0 b := by
  have hPQ (v : P) : P0 (Q0 v) = v := by
    have := congrArg (fun T : P →L[ℂ] P => T v) hQ; simpa using this
  ext s
  rcases s with _ | ⟨j, hj⟩
  · simp [residual, rhs, solution, hPQ]
  · simp only [residual_some, rhs]
    change P0 (solSeq m V Φ Q0 μ x0 b (min j m)) - _ = if j = 0 then x0 else 0
    by_cases h0 : j = 0
    · subst h0
      simp [solSeq, hPQ]
    · simp only [h0, if_false]
      by_cases hjm : j ≤ m
      · have hcond : 1 ≤ j ∧ j ≤ m := ⟨by omega, hjm⟩
        rw [if_pos hcond, seq_solution m V Φ Q0 μ x0 b (j - 1) (by omega)]
        rw [min_eq_left hjm, min_eq_left (by omega : j - 1 ≤ m)]
        obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
        rw [Nat.add_sub_cancel, solution_none]
        change P0 ((Q0 * V) (solSeq m V Φ Q0 μ x0 b k) + stepSource m Φ Q0 μ b) -
          (V (solSeq m V Φ Q0 μ x0 b k) + coupling m • Φ (Q0 ((μ : ℂ) • b))) = 0
        rw [map_add, mul_apply_eq_comp, hPQ, stepSource, map_smul, hPQ, sub_self]
      · have hcond : ¬ (1 ≤ j ∧ j ≤ m) := by omega
        rw [if_neg hcond, if_pos (by omega : m < j),
          seq_solution m V Φ Q0 μ x0 b (j - 1) (by omega)]
        rw [min_eq_right (by omega : m ≤ j), min_eq_right (by omega : m ≤ j - 1)]
        exact sub_self _

/-- The padded copies are exact copies of the final step. -/
theorem solution_copy (μ : ℝ) (x0 b : P) (j : Fin (2 * m + 1)) (hj : m ≤ j.val) :
    solution m V Φ Q0 μ x0 b (some j) = solSeq m V Φ Q0 μ x0 b m := by
  change solSeq m V Φ Q0 μ x0 b (min j.val m) = _
  rw [min_eq_right hj]

/-- Squared norm of the history solution. -/
theorem norm_sq_solution (μ : ℝ) (x0 b : P) :
    ‖solution m V Φ Q0 μ x0 b‖ ^ 2 = ‖Q0 ((μ : ℂ) • b)‖ ^ 2 +
      ∑ j ∈ Finset.range (2 * m + 1), ‖solSeq m V Φ Q0 μ x0 b (min j m)‖ ^ 2 := by
  rw [norm_sq_eq]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [seq_solution m V Φ Q0 μ x0 b j (Finset.mem_range.mp hj)]

end Solution

section Samples

variable [CompleteSpace P]

/-- Exact samples of the solution on the uniform mesh. -/
def samples (A : P →L[ℂ] P) (x0 b : P) (h : ℝ) (j : ℕ) : P :=
  ODEConstantForcing.solution A x0 b (j * h)

theorem samples_succ (A : P →L[ℂ] P) (x0 b : P) (h : ℝ) (j : ℕ) :
    samples A x0 b h (j + 1) = exp (h • A) (samples A x0 b h j) + response A b h := by
  unfold samples
  rw [show ((j + 1 : ℕ) : ℝ) * h = j * h + h by push_cast; ring, solution_add]

omit [CompleteSpace P] in
@[simp] theorem samples_zero (A : P →L[ℂ] P) (x0 b : P) (h : ℝ) :
    samples A x0 b h 0 = x0 := by
  simp [samples]

/-- Powers of the exact one-step propagator are samples of `exp (tA)`. -/
theorem exp_pow (A : P →L[ℂ] P) (h : ℝ) (k : ℕ) :
    exp (h • A) ^ k = exp (((k : ℝ) * h) • A) := by
  letI : NormedAlgebra ℚ (P →L[ℂ] P) := .restrictScalars ℚ ℂ _
  rw [← exp_nsmul, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]

variable [Nontrivial P]

/-- `e^{1/8} < 8/7`. -/
theorem exp_eighth_lt : Real.exp (1 / 8) < 8 / 7 := by
  have h := Real.exp_bound_div_one_sub_of_interval' (x := 1 / 8) (by norm_num) (by norm_num)
  norm_num at h ⊢
  linarith

/-- The forcing mass is bounded by the samples: `T ‖b‖ ≤ (3 + 2ΛT) G`. -/
theorem forcing_le (A : P →L[ℂ] P) (x0 b : P) (Λ T : ℝ) (m : ℕ) (hm : 1 ≤ m)
    (hA : ‖A‖ ≤ Λ) (hT : 0 ≤ T) (hstep : Λ * (T / m) ≤ 1 / 8) (G : ℝ)
    (hG : ∀ j, j ≤ m → ‖samples A x0 b (T / m) j‖ ≤ G) :
    T * ‖b‖ ≤ (3 + 2 * Λ * T) * G := by
  set h := T / m with hh
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hh0 : 0 ≤ h := div_nonneg hT (by linarith)
  have hΛ0 : 0 ≤ Λ := (norm_nonneg _).trans hA
  have hmh : (m : ℝ) * h = T := by rw [hh]; field_simp
  have hG0 : 0 ≤ G := (norm_nonneg _).trans (hG 0 (Nat.zero_le _))
  set E := exp (h • A) with hE
  set s := response A b h with hs
  -- telescoping
  have htel : ∀ k, k ≤ m → (k : ℂ) • s = samples A x0 b h k - x0 -
      ∑ j ∈ Finset.range k, (E - 1) (samples A x0 b h j) := by
    intro k _
    induction k with
    | zero => simp
    | succ k ih =>
        have hk := ih (by omega)
        have hsum : ∑ j ∈ Finset.range k, (E - 1) (samples A x0 b h j) =
            samples A x0 b h k - x0 - (k : ℂ) • s := by rw [hk]; abel
        have hE1 : (E - 1) (samples A x0 b h k) = E (samples A x0 b h k) - samples A x0 b h k := by
          simp
        rw [Finset.sum_range_succ, hsum, hE1, samples_succ]
        push_cast
        rw [add_smul, one_smul]
        abel
  -- norms of E - 1 and of s
  have hAh : ‖h • A‖ ≤ Λ * h := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hh0, mul_comm]
    exact mul_le_mul_of_nonneg_right hA hh0
  have hexp : Real.exp (Λ * h) ≤ 8 / 7 :=
    (Real.exp_le_exp.mpr hstep).trans exp_eighth_lt.le
  have hE1 : ‖E - 1‖ ≤ Λ * h * (8 / 7) := by
    refine (norm_exp_sub_one_le (h • A)).trans ?_
    exact mul_le_mul hAh ((Real.exp_le_exp.mpr hAh).trans hexp) (Real.exp_pos _).le
      (by positivity)
  have hs_lower : h * ‖b‖ * (6 / 7) ≤ ‖s‖ := by
    have h1 := norm_response_ge A b h hh0
    have hAh' : ‖A‖ * h ≤ Λ * h := mul_le_mul_of_nonneg_right hA hh0
    have h2 : ‖A‖ * h * Real.exp (‖A‖ * h) ≤ 1 / 8 * (8 / 7) :=
      mul_le_mul (hAh'.trans hstep) ((Real.exp_le_exp.mpr (hAh'.trans hstep)).trans
        exp_eighth_lt.le) (Real.exp_pos _).le (by norm_num)
    have h3 : 0 ≤ h * ‖b‖ := mul_nonneg hh0 (norm_nonneg _)
    nlinarith
  -- bound the telescoped identity at k = m
  have hm_eq := htel m le_rfl
  have hnorm : (m : ℝ) * ‖s‖ ≤ 2 * G + m * (Λ * h * (8 / 7) * G) := by
    have h1 : ‖(m : ℂ) • s‖ = m * ‖s‖ := by
      rw [norm_smul, Complex.norm_natCast]
    rw [← h1, hm_eq]
    have h2 : ‖∑ j ∈ Finset.range m, (E - 1) (samples A x0 b h j)‖ ≤
        m * (Λ * h * (8 / 7) * G) := by
      refine (norm_sum_le _ _).trans ?_
      have : ∑ j ∈ Finset.range m, ‖(E - 1) (samples A x0 b h j)‖ ≤
          ∑ j ∈ Finset.range m, Λ * h * (8 / 7) * G := by
        apply Finset.sum_le_sum
        intro j hj
        exact ((E - 1).le_opNorm _).trans (mul_le_mul hE1
          (hG j (by have := Finset.mem_range.mp hj; omega)) (norm_nonneg _) (by positivity))
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
      exact this
    have h3 : ‖samples A x0 b h m - x0‖ ≤ 2 * G := by
      have := hG m le_rfl
      have h0 := hG 0 (Nat.zero_le _)
      rw [samples_zero] at h0
      exact (norm_sub_le _ _).trans (by linarith)
    exact (norm_sub_le _ _).trans (add_le_add h3 h2)
  have hfinal : T * ‖b‖ * (6 / 7) ≤ (2 + Λ * T * (8 / 7)) * G := by
    have e1 : (m : ℝ) * (h * ‖b‖ * (6 / 7)) = T * ‖b‖ * (6 / 7) := by rw [← hmh]; ring
    have e2 : (m : ℝ) * (Λ * h * (8 / 7) * G) = Λ * T * (8 / 7) * G := by rw [← hmh]; ring
    have := mul_le_mul_of_nonneg_left hs_lower (by linarith : (0 : ℝ) ≤ m)
    nlinarith
  nlinarith [mul_nonneg hΛ0 hT]

/-- `e^{1/2} < 2`. -/
theorem exp_half_lt : Real.exp (1 / 2) < 2 := by
  have h := Real.exp_bound_div_one_sub_of_interval' (x := 1 / 2) (by norm_num) (by norm_num)
  norm_num at h ⊢
  linarith

omit [Nontrivial P] in
/-- Powers of the implemented step stay within `2 C̄`. -/
theorem step_pow_le (A : P →L[ℂ] P) (F : P →L[ℂ] P) (T Cbar ηE : ℝ) (m : ℕ)
    (hC : ∀ k, k ≤ m → ‖exp (((k : ℝ) * (T / m)) • A)‖ ≤ Cbar)
    (hηE : ‖F - exp ((T / m) • A)‖ ≤ ηE) (hsmall : Cbar * m * ηE ≤ 1 / 2) :
    ∀ k, k ≤ m → ‖F ^ k‖ ≤ 2 * Cbar := by
  intro k hk
  have hX : ∀ j, j ≤ m → ‖exp ((T / m) • A) ^ j‖ ≤ Cbar := by
    intro j hj
    rw [exp_pow]
    exact hC j hj
  have hC0 : 0 ≤ Cbar := (norm_nonneg _).trans (hX 0 (Nat.zero_le _))
  have h := Runs.norm_add_pow_le_of_exp (exp ((T / m) • A)) (F - exp ((T / m) • A)) Cbar m hX k hk
  rw [add_sub_cancel] at h
  refine h.trans ?_
  have h1 : Cbar * ‖F - exp ((T / m) • A)‖ * m ≤ 1 / 2 := by
    have := mul_le_mul_of_nonneg_left hηE (mul_nonneg hC0 (Nat.cast_nonneg m))
    nlinarith
  have h2 : Real.exp (Cbar * ‖F - exp ((T / m) • A)‖ * m) ≤ 2 :=
    (Real.exp_le_exp.mpr h1).trans exp_half_lt.le
  nlinarith

/-- Accuracy of the implemented trajectory against the exact samples. -/
theorem trajectory_accuracy (A : P →L[ℂ] P) (V Φ Q0 : P →L[ℂ] P) (x0 b : P)
    (Λ T Cbar G η0 ηE ρS : ℝ) (m : ℕ) (hm : 1 ≤ m)
    (hA : ‖A‖ ≤ Λ) (hT : 0 ≤ T) (hstep : Λ * (T / m) ≤ 1 / 8)
    (hC : ∀ k, k ≤ m → ‖exp (((k : ℝ) * (T / m)) • A)‖ ≤ Cbar)
    (hG : ∀ j, j ≤ m → ‖samples A x0 b (T / m) j‖ ≤ G)
    (hη0 : ‖Q0 - 1‖ ≤ η0)
    (hηE : ‖Q0 * V - exp ((T / m) • A)‖ ≤ ηE) (hsmall : Cbar * m * ηE ≤ 1 / 2)
    (hρ : 0 ≤ ρS)
    (hρS : ‖stepSource m Φ Q0 (T / Real.sqrt m) b - response A b (T / m)‖ ≤
      ρS * (T / m) * ‖b‖) :
    ∀ j, j ≤ m → ‖solSeq m V Φ Q0 (T / Real.sqrt m) x0 b j - samples A x0 b (T / m) j‖ ≤
      2 * Cbar * ((η0 + m * ηE) * G + ρS * (3 + 2 * Λ * T) * G) := by
  intro j hj
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hG0 : 0 ≤ G := (norm_nonneg _).trans (hG 0 (Nat.zero_le _))
  have hpow := step_pow_le A (Q0 * V) T Cbar ηE m hC hηE hsmall
  have hC0 : 0 ≤ Cbar := (norm_nonneg _).trans (hC 0 (Nat.zero_le _))
  have hη00 : 0 ≤ η0 := (norm_nonneg _).trans hη0
  have hηE0 : 0 ≤ ηE := (norm_nonneg _).trans hηE
  have hρS0 : 0 ≤ ρS * (T / m) * ‖b‖ := (norm_nonneg _).trans hρS
  have hrec := Recursion.norm_sub_le_of_recursions_le (Q0 * V) (exp ((T / m) • A))
    (solSeq m V Φ Q0 (T / Real.sqrt m) x0 b) (samples A x0 b (T / m))
    (stepSource m Φ Q0 (T / Real.sqrt m) b) (response A b (T / m)) m
    (fun k _ => rfl) (fun k _ => samples_succ A x0 b (T / m) k) (2 * Cbar) hpow j hj
  refine hrec.trans (mul_le_mul_of_nonneg_left ?_ (by linarith))
  have h0 : ‖solSeq m V Φ Q0 (T / Real.sqrt m) x0 b 0 - samples A x0 b (T / m) 0‖ ≤ η0 * G := by
    change ‖Q0 x0 - samples A x0 b (T / m) 0‖ ≤ η0 * G
    rw [samples_zero]
    have : Q0 x0 - x0 = (Q0 - 1) x0 := by simp
    rw [this]
    refine ((Q0 - 1).le_opNorm _).trans (mul_le_mul hη0 ?_ (norm_nonneg _) hη00)
    have := hG 0 (Nat.zero_le _)
    rwa [samples_zero] at this
  have hsum : ∑ i ∈ Finset.range j, (‖Q0 * V - exp ((T / m) • A)‖ * ‖samples A x0 b (T / m) i‖ +
      ‖stepSource m Φ Q0 (T / Real.sqrt m) b - response A b (T / m)‖) ≤
      m * (ηE * G) + m * (ρS * (T / m) * ‖b‖) := by
    have hterm : ∀ i ∈ Finset.range j, (‖Q0 * V - exp ((T / m) • A)‖ *
        ‖samples A x0 b (T / m) i‖ +
        ‖stepSource m Φ Q0 (T / Real.sqrt m) b - response A b (T / m)‖) ≤
        ηE * G + ρS * (T / m) * ‖b‖ := by
      intro i hi
      have hi' : i ≤ m := by have := Finset.mem_range.mp hi; omega
      exact add_le_add (mul_le_mul hηE (hG i hi') (norm_nonneg _) hηE0) hρS
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hjm : (j : ℝ) ≤ m := by exact_mod_cast hj
    nlinarith [mul_le_mul_of_nonneg_right hjm (add_nonneg (mul_nonneg hηE0 hG0) hρS0)]
  have hforce := forcing_le A x0 b Λ T m hm hA hT hstep G hG
  have hmsrc : (m : ℝ) * (ρS * (T / m) * ‖b‖) ≤ ρS * (3 + 2 * Λ * T) * G := by
    have e : (m : ℝ) * (ρS * (T / m) * ‖b‖) = ρS * (T * ‖b‖) := by field_simp
    rw [e]
    calc ρS * (T * ‖b‖) ≤ ρS * ((3 + 2 * Λ * T) * G) := mul_le_mul_of_nonneg_left hforce hρ
      _ = _ := by ring
  linarith [h0, hsum, hmsrc]

end Samples

end

end SparseHamiltonian.GeneralODE.History
