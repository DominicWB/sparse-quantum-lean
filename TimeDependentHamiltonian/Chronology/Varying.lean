import SparseHamiltonian.SharpClockSimulation

/-!
# Chronological feedback with slot-dependent local blocks

The released chronological resolvent uses one local private block, coupling
and transfer at every time slot. Time-dependent simulation needs a different
private operation at each sampled time. This module repeats the forced public
recurrence, its lower-triangular block operator, the two-sided inversion by
local elimination and the weighted norm estimate with slot-dependent blocks
`R k`, `A k`, `u k`, `B k`. Every estimate uses genuine operator norms on the
finite `ℓ²` direct sum `BlockOperator.H T V`.
-/

namespace SparseHamiltonian.TimeDependent

open ContinuousLinearMap
open SparseHamiltonian.ChronologicalResolvent
open SparseHamiltonian.FiniteChronologicalInverse
open scoped BigOperators

section Normed

variable {P V : Type*}
  [NormedAddCommGroup P] [NormedSpace ℂ P]
  [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- The ordered product `u (k + m - 1) ∘ ⋯ ∘ u k` of `m` successive public
transfers, starting at slot `k`. The empty product is the identity. -/
def orderedProduct (u : ℕ → P →L[ℂ] P) (k : ℕ) : ℕ → P →L[ℂ] P
  | 0 => 1
  | m + 1 => u (k + m) * orderedProduct u k m

@[simp] theorem orderedProduct_zero (u : ℕ → P →L[ℂ] P) (k : ℕ) :
    orderedProduct u k 0 = 1 := rfl

theorem orderedProduct_succ (u : ℕ → P →L[ℂ] P) (k m : ℕ) :
    orderedProduct u k (m + 1) = u (k + m) * orderedProduct u k m := rfl

/-- A constant transfer gives its ordinary power. -/
theorem orderedProduct_const (u : P →L[ℂ] P) (k m : ℕ) :
    orderedProduct (fun _ => u) k m = u ^ m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [orderedProduct_succ, ih, pow_succ']

/-- Ordered products of transfers obeying a common growth bound grow at most
exponentially in their length. -/
theorem orderedProduct_norm_le (u : ℕ → P →L[ℂ] P) {a : ℝ}
    (hu : ∀ j, ‖u j‖ ≤ 1 + a) (k m : ℕ) :
    ‖orderedProduct u k m‖ ≤ Real.exp ((m : ℝ) * a) := by
  induction m with
  | zero =>
      simp only [orderedProduct_zero, Nat.cast_zero, zero_mul, Real.exp_zero]
      exact ContinuousLinearMap.norm_id_le
  | succ m ih =>
      have huExp : ‖u (k + m)‖ ≤ Real.exp a :=
        (hu (k + m)).trans (by linarith [Real.add_one_le_exp a])
      calc
        ‖orderedProduct u k (m + 1)‖ = ‖u (k + m) * orderedProduct u k m‖ := rfl
        _ ≤ ‖u (k + m)‖ * ‖orderedProduct u k m‖ := norm_mul_le _ _
        _ ≤ Real.exp a * Real.exp ((m : ℝ) * a) :=
          mul_le_mul huExp ih (norm_nonneg _) (Real.exp_pos _).le
        _ = Real.exp (((m + 1 : ℕ) : ℝ) * a) := by
          rw [← Real.exp_add]
          congr 1
          push_cast
          ring

/-- The forced public state, with the zero public state before the first slot. -/
def forcedState (u : ℕ → P →L[ℂ] P) (B : ℕ → V →L[ℂ] P) (y : ℕ → V) : ℕ → P
  | 0 => 0
  | n + 1 => u n (forcedState u B y n) + B n (y n)

@[simp] theorem forcedState_zero (u : ℕ → P →L[ℂ] P) (B : ℕ → V →L[ℂ] P)
    (y : ℕ → V) : forcedState u B y 0 = 0 := rfl

@[simp] theorem forcedState_succ (u : ℕ → P →L[ℂ] P) (B : ℕ → V →L[ℂ] P)
    (y : ℕ → V) (n : ℕ) :
    forcedState u B y (n + 1) = u n (forcedState u B y n) + B n (y n) := rfl

/-- The forced recurrence has the ordered convolution solution. No commutation
of the transfers is used. -/
theorem forcedState_eq_sum (u : ℕ → P →L[ℂ] P) (B : ℕ → V →L[ℂ] P)
    (y : ℕ → V) (n : ℕ) :
    forcedState u B y n =
      ∑ k ∈ Finset.range n, (orderedProduct u (k + 1) (n - 1 - k)) (B k (y k)) := by
  induction n with
  | zero => simp
  | succ n hn =>
      rw [forcedState_succ, hn, map_sum, Finset.sum_range_succ]
      congr 1
      · apply Finset.sum_congr rfl
        intro k hk
        have hklt : k < n := Finset.mem_range.mp hk
        have hexp : n + 1 - 1 - k = (n - 1 - k) + 1 := by omega
        have hidx : k + 1 + (n - 1 - k) = n := by omega
        rw [hexp, orderedProduct_succ, hidx]
        rfl
      · simp

/-- The private response at slot `n`. -/
def privateState (R : ℕ → V →L[ℂ] V) (A : ℕ → P →L[ℂ] V)
    (u : ℕ → P →L[ℂ] P) (B : ℕ → V →L[ℂ] P) (y : ℕ → V) (n : ℕ) : V :=
  R n (y n) + A n (forcedState u B y n)

/-- The blocks of the slot-dependent chronological response. -/
noncomputable def block (R : ℕ → V →L[ℂ] V) (A : ℕ → P →L[ℂ] V)
    (u : ℕ → P →L[ℂ] P) (B : ℕ → V →L[ℂ] P) (r k : ℕ) : V →L[ℂ] V :=
  if k = r then R r else
    if k < r then A r ∘L (orderedProduct u (k + 1) (r - 1 - k) ∘L B k) else 0

@[simp] theorem block_diagonal (R : ℕ → V →L[ℂ] V) (A : ℕ → P →L[ℂ] V)
    (u : ℕ → P →L[ℂ] P) (B : ℕ → V →L[ℂ] P) (r : ℕ) :
    block R A u B r r = R r := by simp [block]

theorem block_below (R : ℕ → V →L[ℂ] V) (A : ℕ → P →L[ℂ] V)
    (u : ℕ → P →L[ℂ] P) (B : ℕ → V →L[ℂ] P) {r k : ℕ} (hkr : k < r) :
    block R A u B r k = A r ∘L (orderedProduct u (k + 1) (r - 1 - k) ∘L B k) := by
  simp [block, ne_of_lt hkr, hkr]

theorem block_above (R : ℕ → V →L[ℂ] V) (A : ℕ → P →L[ℂ] V)
    (u : ℕ → P →L[ℂ] P) (B : ℕ → V →L[ℂ] P) {r k : ℕ} (hrk : r < k) :
    block R A u B r k = 0 := by
  simp [block, ne_of_gt hrk, not_lt_of_ge hrk.le]

/-- The private response is the finite lower-triangular block action. -/
theorem privateState_eq_blocks (R : ℕ → V →L[ℂ] V) (A : ℕ → P →L[ℂ] V)
    (u : ℕ → P →L[ℂ] P) (B : ℕ → V →L[ℂ] P) (y : ℕ → V) (n : ℕ) :
    privateState R A u B y n =
      ∑ k ∈ Finset.range (n + 1), block R A u B n k (y k) := by
  rw [privateState, forcedState_eq_sum, map_sum, Finset.sum_range_succ,
    block_diagonal, add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [block_below R A u B (Finset.mem_range.mp hk)]
  rfl

/-- The complete finite-horizon slot-dependent private response. -/
noncomputable def operator (R : ℕ → V →L[ℂ] V) (A : ℕ → P →L[ℂ] V)
    (u : ℕ → P →L[ℂ] P) (B : ℕ → V →L[ℂ] P) (T : ℕ) :
    BlockOperator.H T V →L[ℂ] BlockOperator.H T V :=
  BlockOperator.blocks fun r k => block R A u B r k

/-- The block operator agrees with the chronological recurrence at every slot. -/
theorem operator_apply (R : ℕ → V →L[ℂ] V) (A : ℕ → P →L[ℂ] V)
    (u : ℕ → P →L[ℂ] P) (B : ℕ → V →L[ℂ] P) (y : ℕ → V) {T : ℕ} (r : Fin T) :
    operator R A u B T (WithLp.toLp 2 (fun k : Fin T => y k)) r =
      privateState R A u B y r := by
  simp only [operator, BlockOperator.blocks_apply]
  rw [Fin.sum_univ_eq_sum_range (fun k => block R A u B r k (y k)),
    privateState_eq_blocks]
  symm
  apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_of_lt r.isLt))
  intro k _hkT hkn
  have hrk : (r : ℕ) < k := by
    have hk : ¬ k < (r : ℕ) + 1 := by simpa using hkn
    omega
  rw [block_above R A u B hrk]
  simp

/-- Weighted operator-norm bound from uniform local estimates. -/
theorem operator_norm_le (R : ℕ → V →L[ℂ] V) (A : ℕ → P →L[ℂ] V)
    (u : ℕ → P →L[ℂ] P) (B : ℕ → V →L[ℂ] P) {ρ β a : ℝ}
    (hρ : 0 ≤ ρ) (hβ : 0 ≤ β) (ha : 0 ≤ a)
    (hR : ∀ k, ‖R k‖ ≤ ρ) (hAB : ∀ r k, ‖A r‖ * ‖B k‖ ≤ β)
    (hu : ∀ k, ‖u k‖ ≤ 1 + a) (T : ℕ) :
    ‖operator R A u B T‖ ≤ ρ + (T : ℝ) * (β * Real.exp ((T : ℝ) * a)) := by
  apply BlockOperator.norm_blocks_triangular_le _ _ _ hρ (by positivity)
  · intro i
    simpa using hR i
  · intro i j hij
    exact block_above R A u B hij
  · intro i j hji
    rw [block_below R A u B hji]
    have hexp : ((((i : ℕ) - 1 - (j : ℕ) : ℕ) : ℝ)) * a ≤ (T : ℝ) * a := by
      apply mul_le_mul_of_nonneg_right _ ha
      exact_mod_cast (show (i : ℕ) - 1 - (j : ℕ) ≤ T by omega)
    calc
      ‖A i ∘L (orderedProduct u ((j : ℕ) + 1) ((i : ℕ) - 1 - (j : ℕ)) ∘L B j)‖ ≤
          ‖A i‖ * (‖orderedProduct u ((j : ℕ) + 1) ((i : ℕ) - 1 - (j : ℕ))‖ * ‖B j‖) :=
        (opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (opNorm_comp_le _ _) (norm_nonneg _))
      _ ≤ ‖A i‖ * (Real.exp ((T : ℝ) * a) * ‖B j‖) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        exact (orderedProduct_norm_le u hu _ _).trans (Real.exp_le_exp.mpr hexp)
      _ = (‖A i‖ * ‖B j‖) * Real.exp ((T : ℝ) * a) := by ring
      _ ≤ β * Real.exp ((T : ℝ) * a) :=
        mul_le_mul_of_nonneg_right (hAB i j) (Real.exp_pos _).le

/-! ### Two-sided inversion by local elimination -/

/-- Forward chronological equations after moving each local diagonal term
to the left side. -/
def forwardResponse (X : ℕ → V →L[ℂ] V) (A : ℕ → P →L[ℂ] V)
    (u : ℕ → P →L[ℂ] P) (B : ℕ → V →L[ℂ] P) (x : ℕ → V) (n : ℕ) : V :=
  X n (x n) - A n (forcedState u B x n)

/-- Slotwise eliminated coupling, transfer and exit blocks. -/
def elimCoupling (S : ℕ → V →L[ℂ] V) (A : ℕ → P →L[ℂ] V) (k : ℕ) : P →L[ℂ] V :=
  S k ∘L A k

def elimTransfer (S : ℕ → V →L[ℂ] V) (A : ℕ → P →L[ℂ] V)
    (u : ℕ → P →L[ℂ] P) (B : ℕ → V →L[ℂ] P) (k : ℕ) : P →L[ℂ] P :=
  u k + B k ∘L S k ∘L A k

def elimExit (S : ℕ → V →L[ℂ] V) (B : ℕ → V →L[ℂ] P) (k : ℕ) : V →L[ℂ] P :=
  B k ∘L S k

/-- The inverse obtained by local elimination of each private slot. -/
def inverseResponse (S : ℕ → V →L[ℂ] V) (A : ℕ → P →L[ℂ] V)
    (u : ℕ → P →L[ℂ] P) (B : ℕ → V →L[ℂ] P) (y : ℕ → V) (n : ℕ) : V :=
  privateState S (elimCoupling S A) (elimTransfer S A u B) (elimExit S B) y n

/-- The reconstructed private trajectory drives the eliminated public trajectory. -/
theorem inverse_public_state (S : ℕ → V →L[ℂ] V) (A : ℕ → P →L[ℂ] V)
    (u : ℕ → P →L[ℂ] P) (B : ℕ → V →L[ℂ] P) (y : ℕ → V) (n : ℕ) :
    forcedState u B (inverseResponse S A u B y) n =
      forcedState (elimTransfer S A u B) (elimExit S B) y n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [forcedState_succ, inverseResponse, privateState, ih, elimTransfer,
        elimExit, elimCoupling, comp_apply, add_apply, map_add]
      abel

/-- Slotwise right inverses give a right inverse of the chronological equations. -/
theorem forward_inverse (X S : ℕ → V →L[ℂ] V) (A : ℕ → P →L[ℂ] V)
    (u : ℕ → P →L[ℂ] P) (B : ℕ → V →L[ℂ] P)
    (hXS : ∀ k, X k ∘L S k = 1) (y : ℕ → V) (n : ℕ) :
    forwardResponse X A u B (inverseResponse S A u B y) n = y n := by
  have hXSv (k : ℕ) (v : V) : X k (S k v) = v := by
    simpa using congrArg (fun M : V →L[ℂ] V => M v) (hXS k)
  simp only [forwardResponse, inverse_public_state, inverseResponse, privateState,
    elimCoupling, map_add, comp_apply, hXSv, add_sub_cancel_right]

/-- Slotwise left inverses make the chronological equations injective. -/
theorem forwardResponse_injective (X S : ℕ → V →L[ℂ] V) (A : ℕ → P →L[ℂ] V)
    (u : ℕ → P →L[ℂ] P) (B : ℕ → V →L[ℂ] P) (hSX : ∀ k, S k ∘L X k = 1) :
    Function.Injective (forwardResponse X A u B) := by
  intro x y hxy
  have hSXv (k : ℕ) (v : V) : S k (X k v) = v := by
    simpa using congrArg (fun M : V →L[ℂ] V => M v) (hSX k)
  have hpair : ∀ n, forcedState u B x n = forcedState u B y n ∧ x n = y n := by
    intro n
    induction n with
    | zero =>
        constructor
        · rfl
        · have h := congrFun hxy 0
          simp only [forwardResponse, forcedState_zero, map_zero, sub_zero] at h
          simpa only [hSXv] using congrArg (S 0) h
    | succ n ih =>
        have hp : forcedState u B x (n + 1) = forcedState u B y (n + 1) := by
          rw [forcedState_succ, forcedState_succ, ih.1, ih.2]
        refine ⟨hp, ?_⟩
        have h := congrFun hxy (n + 1)
        simp only [forwardResponse, hp, sub_left_inj] at h
        simpa only [hSXv] using congrArg (S (n + 1)) h
  funext n
  exact (hpair n).2

theorem inverse_forward (X S : ℕ → V →L[ℂ] V) (A : ℕ → P →L[ℂ] V)
    (u : ℕ → P →L[ℂ] P) (B : ℕ → V →L[ℂ] P)
    (hXS : ∀ k, X k ∘L S k = 1) (hSX : ∀ k, S k ∘L X k = 1) (x : ℕ → V) :
    inverseResponse S A u B (forwardResponse X A u B x) = x := by
  apply forwardResponse_injective X S A u B hSX
  funext n
  exact forward_inverse X S A u B hXS (forwardResponse X A u B x) n

/-- The finite forward chronological equations. -/
noncomputable def forwardOperator (X : ℕ → V →L[ℂ] V) (A : ℕ → P →L[ℂ] V)
    (u : ℕ → P →L[ℂ] P) (B : ℕ → V →L[ℂ] P) (T : ℕ) :
    BlockOperator.H T V →L[ℂ] BlockOperator.H T V :=
  operator X (fun k => -A k) u B T

/-- The finite inverse obtained by local elimination. -/
noncomputable def inverseOperator (S : ℕ → V →L[ℂ] V) (A : ℕ → P →L[ℂ] V)
    (u : ℕ → P →L[ℂ] P) (B : ℕ → V →L[ℂ] P) (T : ℕ) :
    BlockOperator.H T V →L[ℂ] BlockOperator.H T V :=
  operator S (elimCoupling S A) (elimTransfer S A u B) (elimExit S B) T

theorem forwardOperator_restrict (X : ℕ → V →L[ℂ] V) (A : ℕ → P →L[ℂ] V)
    (u : ℕ → P →L[ℂ] P) (B : ℕ → V →L[ℂ] P) (T : ℕ) (x : ℕ → V) :
    forwardOperator X A u B T (restrictSequence T x) =
      restrictSequence T (forwardResponse X A u B x) := by
  ext k
  change operator X (fun k => -A k) u B T (WithLp.toLp 2 (fun j : Fin T => x j)) k =
    forwardResponse X A u B x k
  rw [operator_apply]
  simp [privateState, forwardResponse, sub_eq_add_neg]

theorem inverseOperator_restrict (S : ℕ → V →L[ℂ] V) (A : ℕ → P →L[ℂ] V)
    (u : ℕ → P →L[ℂ] P) (B : ℕ → V →L[ℂ] P) (T : ℕ) (y : ℕ → V) :
    inverseOperator S A u B T (restrictSequence T y) =
      restrictSequence T (inverseResponse S A u B y) := by
  ext k
  exact operator_apply S (elimCoupling S A) (elimTransfer S A u B) (elimExit S B) y k

/-- The forward equations with local diagonals `z I - R k` are the resolvent
denominator of the slot-dependent block operator. -/
theorem forwardOperator_resolvent_denominator (R : ℕ → V →L[ℂ] V)
    (A : ℕ → P →L[ℂ] V) (u : ℕ → P →L[ℂ] P) (B : ℕ → V →L[ℂ] P) (T : ℕ) (z : ℂ) :
    forwardOperator (fun k => z • 1 - R k) A u B T = z • 1 - operator R A u B T := by
  have hseq (x : ℕ → V) :
      forwardOperator (fun k => z • 1 - R k) A u B T (restrictSequence T x) =
        (z • 1 - operator R A u B T) (restrictSequence T x) := by
    rw [forwardOperator_restrict]
    ext k
    change forwardResponse (fun k => z • 1 - R k) A u B x k =
      z • x k - operator R A u B T (WithLp.toLp 2 (fun j : Fin T => x j)) k
    rw [operator_apply]
    simp [forwardResponse, privateState, sub_add_eq_sub_sub]
  apply ContinuousLinearMap.ext
  intro x
  simpa using hseq (extendSequence x)

theorem forwardOperator_inverse (X S : ℕ → V →L[ℂ] V) (A : ℕ → P →L[ℂ] V)
    (u : ℕ → P →L[ℂ] P) (B : ℕ → V →L[ℂ] P) (T : ℕ) (hXS : ∀ k, X k ∘L S k = 1) :
    forwardOperator X A u B T ∘L inverseOperator S A u B T = 1 := by
  have hseq (y : ℕ → V) :
      forwardOperator X A u B T (inverseOperator S A u B T (restrictSequence T y)) =
        restrictSequence T y := by
    rw [inverseOperator_restrict, forwardOperator_restrict]
    congr 1
    funext n
    exact forward_inverse X S A u B hXS y n
  apply ContinuousLinearMap.ext
  intro y
  simpa using hseq (extendSequence y)

theorem inverseOperator_forward (X S : ℕ → V →L[ℂ] V) (A : ℕ → P →L[ℂ] V)
    (u : ℕ → P →L[ℂ] P) (B : ℕ → V →L[ℂ] P) (T : ℕ)
    (hXS : ∀ k, X k ∘L S k = 1) (hSX : ∀ k, S k ∘L X k = 1) :
    inverseOperator S A u B T ∘L forwardOperator X A u B T = 1 := by
  have hseq (x : ℕ → V) :
      inverseOperator S A u B T (forwardOperator X A u B T (restrictSequence T x)) =
        restrictSequence T x := by
    rw [forwardOperator_restrict, inverseOperator_restrict,
      inverse_forward X S A u B hXS hSX]
  apply ContinuousLinearMap.ext
  intro x
  simpa using hseq (extendSequence x)

/-- Slotwise local inversion at `z` inverts the actual finite resolvent
denominator of the slot-dependent private block. -/
theorem resolvent_two_sided_inverse (R S : ℕ → V →L[ℂ] V) (A : ℕ → P →L[ℂ] V)
    (u : ℕ → P →L[ℂ] P) (B : ℕ → V →L[ℂ] P) (T : ℕ) (z : ℂ)
    (hRight : ∀ k, (z • 1 - R k) ∘L S k = 1) (hLeft : ∀ k, S k ∘L (z • 1 - R k) = 1) :
    (z • 1 - operator R A u B T) ∘L inverseOperator S A u B T = 1 ∧
      inverseOperator S A u B T ∘L (z • 1 - operator R A u B T) = 1 := by
  rw [← forwardOperator_resolvent_denominator]
  exact ⟨forwardOperator_inverse _ S A u B T hRight,
    inverseOperator_forward _ S A u B T hRight hLeft⟩

/-- Weighted resolvent bound with uniform slotwise estimates: the bound depends
on the weighted product `T * w * qbar` exactly as in the uniform clock. -/
theorem exists_resolvent (R S : ℕ → V →L[ℂ] V) (A : ℕ → P →L[ℂ] V)
    (u : ℕ → P →L[ℂ] P) (B : ℕ → V →L[ℂ] P) (T : ℕ) (z : ℂ)
    {Q w qbar : ℝ} (hQ : 0 < Q) (hw : 0 ≤ w) (hq : 0 ≤ qbar)
    (hRight : ∀ k, (z • 1 - R k) ∘L S k = 1) (hLeft : ∀ k, S k ∘L (z • 1 - R k) = 1)
    (hS : ∀ k, ‖S k‖ ≤ 2 * Q)
    (hCoupling : ∀ r k, ‖S r ∘L A r‖ * ‖B k ∘L S k‖ ≤ (144 / 49 : ℝ) * w * qbar)
    (hu : ∀ k, ‖u k + B k ∘L S k ∘L A k‖ ≤ 1 + 3 * w * qbar / (4 * Q)) :
    ∃ G : BlockOperator.H T V →L[ℂ] BlockOperator.H T V,
      (z • 1 - operator R A u B T) ∘L G = 1 ∧
      G ∘L (z • 1 - operator R A u B T) = 1 ∧
      ‖G‖ ≤ 3 * (Q + (T : ℝ) * w * qbar) *
        Real.exp (3 * ((T : ℝ) * w * qbar) / (4 * Q)) := by
  obtain ⟨hRinv, hLinv⟩ := resolvent_two_sided_inverse R S A u B T z hRight hLeft
  refine ⟨inverseOperator S A u B T, hRinv, hLinv, ?_⟩
  have hBound := operator_norm_le S (elimCoupling S A) (elimTransfer S A u B)
    (elimExit S B) (ρ := 2 * Q) (β := (144 / 49 : ℝ) * w * qbar)
    (a := 3 * w * qbar / (4 * Q)) (by positivity) (by positivity) (by positivity)
    hS hCoupling hu T
  have hExp : 1 ≤ Real.exp (3 * ((T : ℝ) * w * qbar) / (4 * Q)) :=
    Real.one_le_exp_iff.mpr (by positivity)
  have hExpEq : Real.exp ((T : ℝ) * (3 * w * qbar / (4 * Q))) =
      Real.exp (3 * ((T : ℝ) * w * qbar) / (4 * Q)) := by
    congr 1
    ring
  rw [hExpEq] at hBound
  calc
    ‖inverseOperator S A u B T‖ ≤ 2 * Q + (T : ℝ) * ((144 / 49 : ℝ) * w * qbar *
        Real.exp (3 * ((T : ℝ) * w * qbar) / (4 * Q))) := hBound
    _ ≤ _ := by
      have hW : 0 ≤ (T : ℝ) * w * qbar := by positivity
      have hQE := mul_nonneg hQ.le (sub_nonneg.mpr hExp)
      have hWE := mul_nonneg hW
        (Real.exp_pos (3 * ((T : ℝ) * w * qbar) / (4 * Q))).le
      nlinarith

end Normed

end SparseHamiltonian.TimeDependent
