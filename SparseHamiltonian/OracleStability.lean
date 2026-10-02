import SparseHamiltonian.OracleCircuit

/-!
# Stability of uniform oracle programs

Replacing the primitive oracle by an approximate unitary changes the program by
at most the number of calls times the primitive error. Fixed gates are retained
exactly. This is an error-accounting theorem; it assumes no implementation cost
for the approximate primitive itself.
-/

namespace SparseHamiltonian.OracleCircuit

noncomputable section

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {X : Type*}

theorem IsUnitary.norm_le_one {U : K →L[ℂ] K} (hU : IsUnitary U) : ‖U‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound U zero_le_one
  intro v
  have h := (ContinuousLinearMap.norm_map_iff_adjoint_comp_self U).mpr hU.1 v
  simpa only [one_mul] using h.le

omit [CompleteSpace K] in
/-- The elementary telescoping bound uses only contraction of the outside
factors, and is therefore valid without a nonzero-dimensionality assumption. -/
theorem product_error_le (A B C D : K →L[ℂ] K) (hB : ‖B‖ ≤ 1) (hC : ‖C‖ ≤ 1) :
    ‖A * B - C * D‖ ≤ ‖A - C‖ + ‖B - D‖ := by
  have hsplit : A * B - C * D = (A - C) * B + C * (B - D) := by
    rw [sub_mul, mul_sub, sub_add_sub_cancel]
  calc
    ‖A * B - C * D‖ = ‖(A - C) * B + C * (B - D)‖ := congrArg norm hsplit
    _ ≤ ‖(A - C) * B‖ + ‖C * (B - D)‖ := norm_add_le _ _
    _ ≤ ‖A - C‖ * ‖B‖ + ‖C‖ * ‖B - D‖ :=
      add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ ≤ ‖A - C‖ + ‖B - D‖ :=
      add_le_add (mul_le_of_le_one_right (norm_nonneg _) hB)
        (mul_le_of_le_one_left (norm_nonneg _) hC)

namespace Program

variable {O : X → K →L[ℂ] K}

/-- Reinterpret the identical syntax with a new primitive oracle. -/
def retarget (p : Program O) (O' : X → K →L[ℂ] K) : Program O' :=
  match p with
  | .fixed U hU => .fixed U hU
  | .query => .query
  | .queryAdjoint => .queryAdjoint
  | .seq p q => .seq (p.retarget O') (q.retarget O')

@[simp] theorem count_retarget (p : Program O) (O' : X → K →L[ℂ] K) :
    (p.retarget O').count = p.count := by
  induction p with
  | fixed U hU => rfl
  | query => rfl
  | queryAdjoint => rfl
  | seq p q hp hq => simp only [retarget, count_seq, hp, hq]

/-- Primitive error accumulates at most linearly in the number of queries.
Adjoint calls have the same error as forward calls. -/
theorem eval_retarget_error (p : Program O) (O' : X → K →L[ℂ] K)
    (hO : ∀ x, IsUnitary (O x)) (hO' : ∀ x, IsUnitary (O' x))
    {η : ℝ} (hError : ∀ x, ‖O x - O' x‖ ≤ η) (x : X) :
    ‖p.eval x - (p.retarget O').eval x‖ ≤ (p.count : ℝ) * η := by
  induction p with
  | fixed U hU => simp [retarget]
  | query => simpa only [retarget, eval_query, count_query, Nat.cast_one, one_mul] using hError x
  | queryAdjoint =>
      simpa only [retarget, eval_queryAdjoint, count_queryAdjoint, Nat.cast_one, one_mul,
        ← star_sub, norm_star] using hError x
  | seq p q hp hq =>
      calc
        ‖(.seq p q : Program O).eval x - ((.seq p q : Program O).retarget O').eval x‖ ≤
            ‖p.eval x - (p.retarget O').eval x‖ +
              ‖q.eval x - (q.retarget O').eval x‖ :=
          product_error_le _ _ _ _ (q.eval_unitary hO x).norm_le_one
            ((p.retarget O').eval_unitary hO' x).norm_le_one
        _ ≤ (p.count : ℝ) * η + (q.count : ℝ) * η := add_le_add hp hq
        _ = ((.seq p q : Program O).count : ℝ) * η := by
          rw [count_seq, Nat.cast_add, add_mul]

end Program

namespace Implements

variable {O F : X → K →L[ℂ] K} {q : ℕ}

/-- An implementation yields an approximate implementation using the same
program and budget when the primitive oracle is replaced. -/
theorem perturbation (h : Implements O F q) (O' : X → K →L[ℂ] K)
    (hO : ∀ x, IsUnitary (O x)) (hO' : ∀ x, IsUnitary (O' x))
    {η : ℝ} (hη : 0 ≤ η) (hError : ∀ x, ‖O x - O' x‖ ≤ η) :
    ∃ F' : X → K →L[ℂ] K, Implements O' F' q ∧
      (∀ x, IsUnitary (F' x)) ∧ ∀ x, ‖F x - F' x‖ ≤ (q : ℝ) * η := by
  obtain ⟨p, hp, hq⟩ := h
  refine ⟨(p.retarget O').eval, ⟨p.retarget O', fun _ => rfl, ?_⟩,
    fun x => (p.retarget O').eval_unitary hO' x, ?_⟩
  · simpa only [Program.count_retarget] using hq
  · intro x
    rw [← hp x]
    exact (p.eval_retarget_error O' hO hO' hError x).trans
      (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hq) hη)

end Implements

section CleanInput

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-- Preparing a clean isometric input does not magnify a workspace error. -/
theorem clean_input_error_le (A B : K →L[ℂ] K) (I : P →L[ℂ] K)
    (hI : I.adjoint ∘L I = 1) :
    ‖A ∘L I - B ∘L I‖ ≤ ‖A - B‖ := by
  have hInorm : ‖I‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound I zero_le_one
    intro v
    have h := (ContinuousLinearMap.norm_map_iff_adjoint_comp_self I).mpr hI v
    simpa only [one_mul] using h.le
  calc
    ‖A ∘L I - B ∘L I‖ = ‖(A - B) ∘L I‖ := by rw [ContinuousLinearMap.sub_comp]
    _ ≤ ‖A - B‖ * ‖I‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖A - B‖ := mul_le_of_le_one_right (norm_nonneg _) hInorm

/-- The same linear error budget holds for the full output from a clean input. -/
theorem Program.eval_retarget_clean_error {O : X → K →L[ℂ] K}
    (p : Program O) (O' : X → K →L[ℂ] K)
    (hO : ∀ x, IsUnitary (O x)) (hO' : ∀ x, IsUnitary (O' x))
    {η : ℝ} (hError : ∀ x, ‖O x - O' x‖ ≤ η)
    (I : P →L[ℂ] K) (hI : I.adjoint ∘L I = 1) (x : X) :
    ‖p.eval x ∘L I - (p.retarget O').eval x ∘L I‖ ≤ (p.count : ℝ) * η :=
  (clean_input_error_le _ _ I hI).trans (p.eval_retarget_error O' hO hO' hError x)

/-- A uniform implementation remains close on every clean input, with no
success-probability loss hidden in the error measure. -/
theorem Implements.perturbation_clean {O F : X → K →L[ℂ] K} {q : ℕ}
    (h : Implements O F q) (O' : X → K →L[ℂ] K)
    (hO : ∀ x, IsUnitary (O x)) (hO' : ∀ x, IsUnitary (O' x))
    {η : ℝ} (hη : 0 ≤ η) (hError : ∀ x, ‖O x - O' x‖ ≤ η)
    (I : P →L[ℂ] K) (hI : I.adjoint ∘L I = 1) :
    ∃ F' : X → K →L[ℂ] K, Implements O' F' q ∧
      (∀ x, IsUnitary (F' x)) ∧
        ∀ x, ‖F x ∘L I - F' x ∘L I‖ ≤ (q : ℝ) * η := by
  obtain ⟨F', hF', hU, hErr⟩ := h.perturbation O' hO hO' hη hError
  exact ⟨F', hF', hU, fun x => (clean_input_error_le _ _ I hI).trans (hErr x)⟩

/-- Combining algorithmic approximation and oracle approximation gives the
sum of the ideal algorithm error and the explicit query error budget. -/
theorem Implements.perturbation_clean_target {O F : X → K →L[ℂ] K} {q : ℕ}
    (h : Implements O F q) (O' : X → K →L[ℂ] K)
    (hO : ∀ x, IsUnitary (O x)) (hO' : ∀ x, IsUnitary (O' x))
    {η δ : ℝ} (hη : 0 ≤ η) (hError : ∀ x, ‖O x - O' x‖ ≤ η)
    (I : P →L[ℂ] K) (hI : I.adjoint ∘L I = 1)
    (G : X → P →L[ℂ] K) (hTarget : ∀ x, ‖F x ∘L I - G x‖ ≤ δ) :
    ∃ F' : X → K →L[ℂ] K, Implements O' F' q ∧
      (∀ x, IsUnitary (F' x)) ∧
        ∀ x, ‖F' x ∘L I - G x‖ ≤ δ + (q : ℝ) * η := by
  obtain ⟨F', hF', hU, hErr⟩ := h.perturbation_clean O' hO hO' hη hError I hI
  refine ⟨F', hF', hU, fun x => ?_⟩
  calc
    ‖F' x ∘L I - G x‖ ≤ ‖F' x ∘L I - F x ∘L I‖ + ‖F x ∘L I - G x‖ :=
      by simpa only [dist_eq_norm] using dist_triangle (F' x ∘L I) (F x ∘L I) (G x)
    _ ≤ (q : ℝ) * η + δ :=
      add_le_add (by simpa only [norm_sub_rev] using hErr x) (hTarget x)
    _ = δ + (q : ℝ) * η := add_comm _ _

end CleanInput

end

end SparseHamiltonian.OracleCircuit
