import SparseHamiltonian.BoundaryCompression

/-!
# Chronological expansion and transfer growth

This module solves the forced public recurrence exactly and identifies the
resulting private response as a lower-triangular block operator. Its block
estimates use genuine continuous-linear-map operator norms. The local inverse
and transfer operators are inputs to this module; their construction is a
separate obligation.
-/

namespace SparseHamiltonian
namespace ChronologicalResolvent

open ContinuousLinearMap
open scoped BigOperators

variable {P Q : Type*}
  [NormedAddCommGroup P] [NormedSpace ℂ P]
  [NormedAddCommGroup Q] [NormedSpace ℂ Q]

/-- Powers of a transfer operator have exponential growth controlled by its
distance above contractivity. The estimate in fact holds for any real `a`
satisfying the displayed norm bound. -/
theorem transfer_pow_norm_le_exp (u : P →L[ℂ] P) {a : ℝ}
    (hu : ‖u‖ ≤ 1 + a) (n : ℕ) :
    ‖u ^ n‖ ≤ Real.exp ((n : ℝ) * a) := by
  have huExp : ‖u‖ ≤ Real.exp a := by
    linarith [Real.add_one_le_exp a]
  induction n with
  | zero =>
      simp only [pow_zero, Nat.cast_zero, zero_mul, Real.exp_zero]
      exact ContinuousLinearMap.norm_id_le
  | succ n hn =>
      calc
        ‖u ^ (n + 1)‖ = ‖u ^ n * u‖ := by rw [pow_succ]
        _ ≤ ‖u ^ n‖ * ‖u‖ := norm_mul_le _ _
        _ ≤ Real.exp ((n : ℝ) * a) * Real.exp a :=
          mul_le_mul hn huExp (norm_nonneg u) (Real.exp_pos _).le
        _ = Real.exp (((n + 1 : ℕ) : ℝ) * a) := by
          rw [← Real.exp_add]
          congr 1
          push_cast
          ring

/-- The public auxiliary state, indexed so that the zero initial state occurs
before the first private time slot. -/
def forcedPublicState (u : P →L[ℂ] P) (B : Q →L[ℂ] P) (y : ℕ → Q) : ℕ → P
  | 0 => 0
  | n + 1 => u (forcedPublicState u B y n) + B (y n)

@[simp] theorem forcedPublicState_zero (u : P →L[ℂ] P) (B : Q →L[ℂ] P)
    (y : ℕ → Q) : forcedPublicState u B y 0 = 0 := rfl

@[simp] theorem forcedPublicState_succ (u : P →L[ℂ] P) (B : Q →L[ℂ] P)
    (y : ℕ → Q) (n : ℕ) :
    forcedPublicState u B y (n + 1) = u (forcedPublicState u B y n) + B (y n) := rfl

/-- Any solution of the forced recurrence agrees with the explicit construction. -/
theorem forcedPublicState_unique (u : P →L[ℂ] P) (B : Q →L[ℂ] P)
    (y : ℕ → Q) (v : ℕ → P) (hzero : v 0 = 0)
    (hstep : ∀ n, v (n + 1) = u (v n) + B (y n)) :
    ∀ n, v n = forcedPublicState u B y n := by
  intro n
  induction n with
  | zero => exact hzero
  | succ n hn => rw [hstep, forcedPublicState_succ, hn]

/-- The forced chronological recurrence has the usual finite convolution
solution, without a diagonalizability or commutation assumption. -/
theorem forcedPublicState_eq_sum (u : P →L[ℂ] P) (B : Q →L[ℂ] P)
    (y : ℕ → Q) (n : ℕ) :
    forcedPublicState u B y n =
      ∑ k ∈ Finset.range n, (u ^ (n - 1 - k)) (B (y k)) := by
  induction n with
  | zero => simp
  | succ n hn =>
      rw [forcedPublicState_succ, hn, map_sum, Finset.sum_range_succ]
      congr 1
      · apply Finset.sum_congr rfl
        intro k hk
        have hklt : k < n := Finset.mem_range.mp hk
        have hexp : n - 1 - k + 1 = n + 1 - 1 - k := by omega
        rw [← mul_apply_eq_comp, ← pow_succ', hexp]
      · simp

/-- The private response recovered from the local inverse and the public state. -/
def chronologicalPrivateState (R : Q →L[ℂ] Q) (A : P →L[ℂ] Q)
    (u : P →L[ℂ] P) (B : Q →L[ℂ] P) (y : ℕ → Q) (n : ℕ) : Q :=
  R (y n) + A (forcedPublicState u B y n)

/-- Explicit private response: the local inverse forms the diagonal term and
all earlier forcing terms propagate through powers of the public transfer. -/
theorem chronologicalPrivateState_eq_sum (R : Q →L[ℂ] Q) (A : P →L[ℂ] Q)
    (u : P →L[ℂ] P) (B : Q →L[ℂ] P) (y : ℕ → Q) (n : ℕ) :
    chronologicalPrivateState R A u B y n =
      R (y n) + ∑ k ∈ Finset.range n, (A ∘L ((u ^ (n - 1 - k)) ∘L B)) (y k) := by
  rw [chronologicalPrivateState, forcedPublicState_eq_sum, map_sum]
  rfl

/-- The blocks of the chronological private response. -/
noncomputable def chronologicalBlock (R : Q →L[ℂ] Q) (A : P →L[ℂ] Q)
    (u : P →L[ℂ] P) (B : Q →L[ℂ] P) (r k : ℕ) : Q →L[ℂ] Q :=
  if k = r then R else if k < r then A ∘L ((u ^ (r - 1 - k)) ∘L B) else 0

@[simp] theorem chronologicalBlock_diagonal (R : Q →L[ℂ] Q) (A : P →L[ℂ] Q)
    (u : P →L[ℂ] P) (B : Q →L[ℂ] P) (r : ℕ) :
    chronologicalBlock R A u B r r = R := by simp [chronologicalBlock]

theorem chronologicalBlock_below (R : Q →L[ℂ] Q) (A : P →L[ℂ] Q)
    (u : P →L[ℂ] P) (B : Q →L[ℂ] P) {r k : ℕ} (hkr : k < r) :
    chronologicalBlock R A u B r k = A ∘L ((u ^ (r - 1 - k)) ∘L B) := by
  simp [chronologicalBlock, ne_of_lt hkr, hkr]

theorem chronologicalBlock_above (R : Q →L[ℂ] Q) (A : P →L[ℂ] Q)
    (u : P →L[ℂ] P) (B : Q →L[ℂ] P) {r k : ℕ} (hrk : r < k) :
    chronologicalBlock R A u B r k = 0 := by
  simp [chronologicalBlock, ne_of_gt hrk, not_lt_of_ge hrk.le]

/-- The actual private response is the finite lower-triangular block action. -/
theorem chronologicalPrivateState_eq_blocks (R : Q →L[ℂ] Q) (A : P →L[ℂ] Q)
    (u : P →L[ℂ] P) (B : Q →L[ℂ] P) (y : ℕ → Q) (n : ℕ) :
    chronologicalPrivateState R A u B y n =
      ∑ k ∈ Finset.range (n + 1), chronologicalBlock R A u B n k (y k) := by
  rw [chronologicalPrivateState_eq_sum, Finset.sum_range_succ,
    chronologicalBlock_diagonal, add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [chronologicalBlock_below R A u B (Finset.mem_range.mp hk)]

/-- A below-diagonal block has the norm bound dictated by transfer growth. -/
theorem chronologicalBlock_below_norm_le (R : Q →L[ℂ] Q) (A : P →L[ℂ] Q)
    (u : P →L[ℂ] P) (B : Q →L[ℂ] P) {a : ℝ} (hu : ‖u‖ ≤ 1 + a)
    {r k : ℕ} (hkr : k < r) :
    ‖chronologicalBlock R A u B r k‖ ≤
      ‖A‖ * Real.exp (((r - 1 - k : ℕ) : ℝ) * a) * ‖B‖ := by
  rw [chronologicalBlock_below R A u B hkr]
  calc
    _ ≤ ‖A‖ * ‖(u ^ (r - 1 - k)) ∘L B‖ := opNorm_comp_le _ _
    _ ≤ ‖A‖ * (‖u ^ (r - 1 - k)‖ * ‖B‖) :=
      mul_le_mul_of_nonneg_left (opNorm_comp_le _ _) (norm_nonneg A)
    _ ≤ ‖A‖ * (Real.exp (((r - 1 - k : ℕ) : ℝ) * a) * ‖B‖) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (transfer_pow_norm_le_exp u hu _) (norm_nonneg B))
        (norm_nonneg A)
    _ = _ := by ring

/-- Over a horizon of `T` slots, all strictly lower blocks share one exponential
bound. This estimate is independent of the global chronological operator's
normality. -/
theorem chronologicalBlock_uniform_norm_le (R : Q →L[ℂ] Q) (A : P →L[ℂ] Q)
    (u : P →L[ℂ] P) (B : Q →L[ℂ] P) {a : ℝ}
    (ha : 0 ≤ a) (hu : ‖u‖ ≤ 1 + a) {T r k : ℕ} (hr : r < T) (hkr : k < r) :
    ‖chronologicalBlock R A u B r k‖ ≤ ‖A‖ * Real.exp ((T : ℝ) * a) * ‖B‖ := by
  have hexp : ((r - 1 - k : ℕ) : ℝ) * a ≤ (T : ℝ) * a := by
    apply mul_le_mul_of_nonneg_right _ ha
    exact_mod_cast (show r - 1 - k ≤ T by omega)
  calc
    _ ≤ ‖A‖ * Real.exp (((r - 1 - k : ℕ) : ℝ) * a) * ‖B‖ :=
      chronologicalBlock_below_norm_le R A u B hu hkr
    _ ≤ ‖A‖ * Real.exp ((T : ℝ) * a) * ‖B‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (norm_nonneg A))
        (norm_nonneg B)

/-! The following finite block-operator estimate is proved on the actual ℓ²
direct sum. In particular it does not use the entrywise norm of a matrix. -/

namespace BlockOperator

variable {T : ℕ}

abbrev H (T : ℕ) (Q : Type*) := PiLp 2 (fun _ : Fin T => Q)

omit [NormedSpace ℂ Q] in
lemma norm_bound_of_coordinate_bound (y x : H T Q) (r : ℝ) (hr : 0 ≤ r)
    (h : ∀ i, ‖y i‖ ≤ r * ‖x i‖) : ‖y‖ ≤ r * ‖x‖ := by
  have hsq : ‖y‖ ^ 2 ≤ (r * ‖x‖) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    calc
      ∑ i, ‖y i‖ ^ 2 ≤ ∑ i, (r * ‖x i‖) ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        exact pow_le_pow_left₀ (norm_nonneg _) (h i) 2
      _ = (r * ‖x‖) ^ 2 := by
        simp_rw [mul_pow]
        rw [← Finset.mul_sum, ← PiLp.norm_sq_eq_of_L2]
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hr (norm_nonneg _))).mp hsq

lemma norm_bound_of_coordinate_sum (B : H T Q →L[ℂ] H T Q) (b : ℝ) (hb : 0 ≤ b)
    (hB : ∀ x i, ‖B x i‖ ≤ b * ∑ j, ‖x j‖) : ‖B‖ ≤ (T : ℝ) * b := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (Nat.cast_nonneg _) hb)
  intro x
  have hsum : (∑ j, ‖x j‖) ^ 2 ≤ (T : ℝ) * ‖x‖ ^ 2 := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun _ : Fin T => (1 : ℝ)) (fun j => ‖x j‖)
    simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one, PiLp.norm_sq_eq_of_L2] using hcs
  have hout : ‖B x‖ ^ 2 ≤ (T : ℝ) * (b * ∑ j, ‖x j‖) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    calc
      ∑ i, ‖B x i‖ ^ 2 ≤ ∑ _ : Fin T, (b * ∑ j, ‖x j‖) ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        exact pow_le_pow_left₀ (norm_nonneg _) (hB x i) 2
      _ = _ := by simp
  have hsq : ‖B x‖ ^ 2 ≤ ((T : ℝ) * b * ‖x‖) ^ 2 := by
    calc
      ‖B x‖ ^ 2 ≤ (T : ℝ) * (b * ∑ j, ‖x j‖) ^ 2 := hout
      _ = ((T : ℝ) * b ^ 2) * (∑ j, ‖x j‖) ^ 2 := by ring
      _ ≤ ((T : ℝ) * b ^ 2) * ((T : ℝ) * ‖x‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = _ := by ring
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hsq

noncomputable def blocks (A : Fin T → Fin T → Q →L[ℂ] Q) : H T Q →L[ℂ] H T Q :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin T => Q)).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.pi (fun i => ∑ j, (A i j).comp (ContinuousLinearMap.proj j))).comp
      (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin T => Q)).toContinuousLinearMap)

lemma blocks_apply (A : Fin T → Fin T → Q →L[ℂ] Q) (x : H T Q) (i : Fin T) :
    blocks A x i = ∑ j, A i j (x j) := by
  simp [blocks]

lemma norm_blocks_le (A : Fin T → Fin T → Q →L[ℂ] Q) (b : ℝ) (hb : 0 ≤ b)
    (hA : ∀ i j, ‖A i j‖ ≤ b) : ‖blocks A‖ ≤ (T : ℝ) * b := by
  apply norm_bound_of_coordinate_sum _ b hb
  intro x i
  rw [blocks_apply]
  calc
    ‖∑ j, A i j (x j)‖ ≤ ∑ j, ‖A i j (x j)‖ := norm_sum_le _ _
    _ ≤ ∑ j, b * ‖x j‖ := by
      apply Finset.sum_le_sum
      intro j hj
      exact ((A i j).le_opNorm (x j)).trans
        (mul_le_mul_of_nonneg_right (hA i j) (norm_nonneg _))
    _ = _ := by rw [Finset.mul_sum]

noncomputable def diagonal (A : Fin T → Fin T → Q →L[ℂ] Q) (i j : Fin T) : Q →L[ℂ] Q :=
  if i = j then A i i else 0

noncomputable def offDiagonal (A : Fin T → Fin T → Q →L[ℂ] Q) (i j : Fin T) : Q →L[ℂ] Q :=
  if i = j then 0 else A i j

lemma blocks_diagonal_apply (A : Fin T → Fin T → Q →L[ℂ] Q)
    (x : H T Q) (i : Fin T) : blocks (diagonal A) x i = A i i (x i) := by
  rw [blocks_apply]
  rw [Finset.sum_eq_single i]
  · simp [diagonal]
  · intro j hj hji
    simp [diagonal, Ne.symm hji]
  · simp

lemma blocks_decompose (A : Fin T → Fin T → Q →L[ℂ] Q) :
    blocks A = blocks (diagonal A) + blocks (offDiagonal A) := by
  ext x i
  simp only [_root_.add_apply, PiLp.add_apply, blocks_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases h : i = j
  · subst j
    simp [diagonal, offDiagonal]
  · simp [diagonal, offDiagonal, h]

lemma norm_blocks_diagonal_le (A : Fin T → Fin T → Q →L[ℂ] Q)
    (r : ℝ) (hr : 0 ≤ r) (hA : ∀ i, ‖A i i‖ ≤ r) : ‖blocks (diagonal A)‖ ≤ r := by
  apply ContinuousLinearMap.opNorm_le_bound _ hr
  intro x
  apply norm_bound_of_coordinate_bound _ _ r hr
  intro i
  rw [blocks_diagonal_apply]
  exact ((A i i).le_opNorm (x i)).trans
    (mul_le_mul_of_nonneg_right (hA i) (norm_nonneg _))

lemma norm_blocks_triangular_le (A : Fin T → Fin T → Q →L[ℂ] Q)
    (r b : ℝ) (hr : 0 ≤ r) (hb : 0 ≤ b)
    (hdiag : ∀ i, ‖A i i‖ ≤ r)
    (hupper : ∀ i j, i < j → A i j = 0)
    (hlower : ∀ i j, j < i → ‖A i j‖ ≤ b) :
    ‖blocks A‖ ≤ r + (T : ℝ) * b := by
  have hoff : ∀ i j, ‖offDiagonal A i j‖ ≤ b := by
    intro i j
    rcases lt_trichotomy i j with hij | hij | hij
    · simp [offDiagonal, ne_of_lt hij, hupper i j hij, hb]
    · simp [offDiagonal, hij, hb]
    · simpa [offDiagonal, ne_of_gt hij] using hlower i j hij
  calc
    ‖blocks A‖ = ‖blocks (diagonal A) + blocks (offDiagonal A)‖ := by rw [blocks_decompose]
    _ ≤ ‖blocks (diagonal A)‖ + ‖blocks (offDiagonal A)‖ := _root_.norm_add_le (blocks (diagonal A)) (blocks (offDiagonal A))
    _ ≤ r + (T : ℝ) * b := add_le_add (norm_blocks_diagonal_le A r hr hdiag)
      (norm_blocks_le (offDiagonal A) b hb hoff)

end BlockOperator

/-- The complete finite-horizon private response, as a bounded operator on the
ℓ² direct sum of the private time slots. -/
noncomputable def chronologicalOperator (R : Q →L[ℂ] Q) (A : P →L[ℂ] Q)
    (u : P →L[ℂ] P) (B : Q →L[ℂ] P) (T : ℕ) :
    BlockOperator.H T Q →L[ℂ] BlockOperator.H T Q :=
  BlockOperator.blocks fun r k => chronologicalBlock R A u B r k

/-- The finite block operator agrees exactly with the chronological recurrence
at every private time slot. -/
theorem chronologicalOperator_apply (R : Q →L[ℂ] Q) (A : P →L[ℂ] Q)
    (u : P →L[ℂ] P) (B : Q →L[ℂ] P) (y : ℕ → Q) {T : ℕ} (r : Fin T) :
    chronologicalOperator R A u B T (WithLp.toLp 2 (fun k : Fin T => y k)) r =
      chronologicalPrivateState R A u B y r := by
  simp only [chronologicalOperator, BlockOperator.blocks_apply]
  rw [Fin.sum_univ_eq_sum_range (fun k => chronologicalBlock R A u B r k (y k)),
    chronologicalPrivateState_eq_blocks]
  symm
  apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_of_lt r.isLt))
  intro k _hkT hkn
  have hrk : (r : ℕ) < k := by
    have hk : ¬ k < (r : ℕ) + 1 := by simpa using hkn
    omega
  rw [chronologicalBlock_above R A u B hrk]
  simp

/-- The chronological response estimate follows from genuine ℓ² operator
bounds on its diagonal and propagating blocks. -/
theorem chronologicalOperator_norm_le (R : Q →L[ℂ] Q) (A : P →L[ℂ] Q)
    (u : P →L[ℂ] P) (B : Q →L[ℂ] P) {a : ℝ}
    (ha : 0 ≤ a) (hu : ‖u‖ ≤ 1 + a) (T : ℕ) :
    ‖chronologicalOperator R A u B T‖ ≤
      ‖R‖ + (T : ℝ) * (‖A‖ * Real.exp ((T : ℝ) * a) * ‖B‖) := by
  apply BlockOperator.norm_blocks_triangular_le _ _ _ (norm_nonneg R) (by positivity)
  · intro i
    simp
  · intro i j hij
    exact chronologicalBlock_above R A u B hij
  · intro i j hji
    exact chronologicalBlock_uniform_norm_le R A u B ha hu i.isLt hji

/-- Local diagonal and coupling estimates give an aggregate chronological
bound. Only the local operator norms and transfer growth are premises. -/
theorem chronologicalOperator_norm_le_of_local_bounds
    (R : Q →L[ℂ] Q) (A : P →L[ℂ] Q) (u : P →L[ℂ] P) (B : Q →L[ℂ] P)
    {a r b e : ℝ} (ha : 0 ≤ a) (hu : ‖u‖ ≤ 1 + a) (T : ℕ)
    (hR : ‖R‖ ≤ r) (hCoupling : (T : ℝ) * (‖A‖ * ‖B‖) ≤ b)
    (hGrowth : (T : ℝ) * a ≤ e) :
    ‖chronologicalOperator R A u B T‖ ≤ r + b * Real.exp e := by
  calc
    _ ≤ ‖R‖ + (T : ℝ) * (‖A‖ * Real.exp ((T : ℝ) * a) * ‖B‖) :=
      chronologicalOperator_norm_le R A u B ha hu T
    _ = ‖R‖ + ((T : ℝ) * (‖A‖ * ‖B‖)) * Real.exp ((T : ℝ) * a) := by ring
    _ ≤ r + b * Real.exp e := by
      apply add_le_add hR
      exact mul_le_mul hCoupling (Real.exp_le_exp.mpr hGrowth)
        (Real.exp_pos _).le (le_trans (by positivity) hCoupling)

end ChronologicalResolvent
end SparseHamiltonian
