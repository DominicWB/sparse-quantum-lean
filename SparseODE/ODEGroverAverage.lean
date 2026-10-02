import SparseODE.ODEGroverPlane

/-!
# Randomized Grover iteration: a finite average and a linear cutoff

This is scalar analysis of the actual two-reflection success formula.  It
does not assume a constant average success probability.  A telescoping sine
identity proves that probability, and the ODE amplitude promises determine
one cutoff independent of the unknown amplitude.  Connecting the formula to
the physical reflection program is a separate lemma.
-/

namespace SparseHamiltonian.ODEGroverAverage

noncomputable section
open scoped BigOperators

/-- Success after `j` Grover steps at initial amplitude `sin theta`. -/
def successProbability (theta : ℝ) (j : ℕ) : ℝ :=
  Real.sin ((2 * (j : ℝ) + 1) * theta) ^ 2

/-- Uniform choice among the iteration counts `0, ..., M - 1`. -/
def meanSuccess (theta : ℝ) (M : ℕ) : ℝ :=
  (∑ j ∈ Finset.range M, successProbability theta j) / (M : ℝ)

/-- Each summand is a genuine probability. -/
theorem successProbability_bounds (theta : ℝ) (j : ℕ) :
    0 ≤ successProbability theta j ∧ successProbability theta j ≤ 1 := by
  unfold successProbability
  refine ⟨sq_nonneg _, ?_⟩
  have h := Real.abs_sin_le_one ((2 * (j : ℝ) + 1) * theta)
  have hsq := mul_self_le_mul_self (abs_nonneg _) h
  simpa only [← sq, sq_abs, one_pow] using hsq

/-- The local identity that makes the finite success sum telescope. -/
theorem sine_increment (x h : ℝ) :
    Real.sin (2 * x + h) - Real.sin (2 * x - h) =
      2 * Real.sin h - 4 * Real.sin h * Real.sin x ^ 2 := by
  have hcircle := Real.sin_sq_add_cos_sq x
  calc
    Real.sin (2 * x + h) - Real.sin (2 * x - h) =
        2 * Real.sin h * (Real.cos x ^ 2 - Real.sin x ^ 2) := by
      rw [Real.sin_add, Real.sin_sub,
        show 2 * x = x + x by ring, Real.cos_add]
      ring
    _ = 2 * Real.sin h - 4 * Real.sin h * Real.sin x ^ 2 := by
      nlinarith [congrArg (fun z : ℝ => 2 * Real.sin h * z) hcircle]

/-- Exact finite sum, without any nonzero denominator premise. -/
theorem sum_identity (theta : ℝ) (M : ℕ) :
    4 * Real.sin (2 * theta) *
        (∑ j ∈ Finset.range M, successProbability theta j) =
      2 * (M : ℝ) * Real.sin (2 * theta) -
        Real.sin (4 * (M : ℝ) * theta) := by
  induction M with
  | zero => simp
  | succ M ih =>
    have hstep := sine_increment ((2 * (M : ℝ) + 1) * theta) (2 * theta)
    have hplus : 2 * ((2 * (M : ℝ) + 1) * theta) + 2 * theta =
        4 * ((M : ℝ) + 1) * theta := by ring
    have hminus : 2 * ((2 * (M : ℝ) + 1) * theta) - 2 * theta =
        4 * (M : ℝ) * theta := by ring
    rw [hplus, hminus] at hstep
    rw [Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
    change 4 * Real.sin (2 * theta) *
        ((∑ j ∈ Finset.range M, successProbability theta j) +
          Real.sin ((2 * (M : ℝ) + 1) * theta) ^ 2) = _
    nlinarith

/-- A cutoff with `M sin(2 theta) >= 1` gives constant average success. -/
theorem meanSuccess_lower (theta : ℝ) (M : ℕ) (hM : 0 < M)
    (hs : 0 < Real.sin (2 * theta))
    (hbudget : 1 ≤ (M : ℝ) * Real.sin (2 * theta)) :
    (1 : ℝ) / 4 ≤ meanSuccess theta M := by
  have hsum := sum_identity theta M
  have hsin := Real.sin_le_one (4 * (M : ℝ) * theta)
  have hmass : (M : ℝ) ≤
      4 * (∑ j ∈ Finset.range M, successProbability theta j) := by
    apply (mul_le_mul_iff_right₀ hs).mp
    nlinarith
  have hMr : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  unfold meanSuccess
  apply (le_div_iff₀ hMr).mpr
  linarith

/-- The average also satisfies the probability upper bound. -/
theorem meanSuccess_bounds (theta : ℝ) (M : ℕ) :
    0 ≤ meanSuccess theta M ∧ meanSuccess theta M ≤ 1 := by
  have hsum0 : 0 ≤ ∑ j ∈ Finset.range M, successProbability theta j :=
    Finset.sum_nonneg (fun j _ => (successProbability_bounds theta j).1)
  have hsum1 : (∑ j ∈ Finset.range M, successProbability theta j) ≤ (M : ℝ) := by
    calc
      _ ≤ ∑ _j ∈ Finset.range M, (1 : ℝ) :=
        Finset.sum_le_sum (fun j _ => (successProbability_bounds theta j).2)
      _ = (M : ℝ) := by simp
  unfold meanSuccess
  refine ⟨div_nonneg hsum0 (Nat.cast_nonneg M), ?_⟩
  by_cases hM : M = 0
  · simp [hM]
  · have hMr : (0 : ℝ) < (M : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hM
    apply (div_le_iff₀ hMr).mpr
    simpa only [one_mul] using hsum1

/-- In the ODE amplitude range, the doubled-angle sine is at least `a`. -/
theorem amplitude_le_sin_two_arcsin (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 2) :
    a ≤ Real.sin (2 * Real.arcsin a) := by
  have hs : Real.sin (Real.arcsin a) = a :=
    Real.sin_arcsin (by linarith) (by linarith)
  have hc0 := Real.cos_arcsin_nonneg a
  have hcircle := Real.sin_sq_add_cos_sq (Real.arcsin a)
  rw [hs] at hcircle
  have hc : (1 : ℝ) / 2 ≤ Real.cos (Real.arcsin a) := by
    by_contra hn
    have hc1 : Real.cos (Real.arcsin a) ≤ (1 : ℝ) / 2 :=
      (lt_of_not_ge hn).le
    nlinarith [mul_self_le_mul_self ha0 ha1, mul_self_le_mul_self hc0 hc1]
  rw [show 2 * Real.arcsin a = Real.arcsin a + Real.arcsin a by ring,
    Real.sin_add, hs]
  nlinarith [mul_nonneg ha0 (sub_nonneg.mpr hc)]

/-- One public cutoff serves every amplitude in the promised interval. -/
def chosenIterations (g : ℝ) : ℕ := ⌈4 * g⌉₊

/-- Both the lower coverage bound and the linear iteration upper bound. -/
theorem chosenIterations_bounds (g : ℝ) (hg : 1 ≤ g) :
    0 < chosenIterations g ∧
      4 * g ≤ (chosenIterations g : ℝ) ∧
      (chosenIterations g : ℝ) ≤ 5 * g := by
  have hlo : 4 * g ≤ (chosenIterations g : ℝ) := Nat.le_ceil _
  have hhi : (chosenIterations g : ℝ) < 4 * g + 1 :=
    Nat.ceil_lt_add_one (by linarith)
  have hpos : (0 : ℝ) < (chosenIterations g : ℝ) := by linarith
  refine ⟨?_, hlo, ?_⟩
  · exact_mod_cast hpos
  · linarith

/-- The promised ODE amplitude yields average success at least `1/4` using
only the public bound `g`; the cutoff is at most `5 g`. -/
theorem promised_amplitude (g a : ℝ) (hg : 1 ≤ g)
    (ha0 : 1 / (4 * g) ≤ a) (ha1 : a ≤ 1 / 2) :
    0 < chosenIterations g ∧
      (chosenIterations g : ℝ) ≤ 5 * g ∧
      (1 : ℝ) / 4 ≤ meanSuccess (Real.arcsin a) (chosenIterations g) := by
  have hgpos : 0 < g := by linarith
  have hden : 0 < 4 * g := by positivity
  have hapos : 0 < a := lt_of_lt_of_le (one_div_pos.mpr hden) ha0
  have hslo := amplitude_le_sin_two_arcsin a hapos.le ha1
  have hspos : 0 < Real.sin (2 * Real.arcsin a) := hapos.trans_le hslo
  obtain ⟨hM, hlo, hhi⟩ := chosenIterations_bounds g hg
  have hprod : 1 ≤ a * (4 * g) := (div_le_iff₀ hden).mp ha0
  have hcoverage : 1 ≤ (chosenIterations g : ℝ) * Real.sin (2 * Real.arcsin a) := by
    have hmul1 := mul_le_mul_of_nonneg_right hlo hapos.le
    have hmul2 := mul_le_mul_of_nonneg_left hslo (Nat.cast_nonneg (chosenIterations g))
    nlinarith
  exact ⟨hM, hhi, meanSuccess_lower (Real.arcsin a) (chosenIterations g)
    hM hspos hcoverage⟩

end
end SparseHamiltonian.ODEGroverAverage
