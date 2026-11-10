import SignedFactorSimulation.Extension
import SparseHamiltonian.SmoothingLCU
import Mathlib.Algebra.Order.Interval.Finset.SuccPred

/-!
# The signed linear combination of reuse circuits

Theorem `opt:thm:signed` combines the uniform clocks `Ces_j(F_m)`, `j = 1, …, n`, with real weights
`λ_j` by a coherent linear combination of unitaries (the paragraph "Combining and amplifying the
finite blocks": "Linear combination of unitaries gives the successful block"). Branch `j` runs `j`
reuses of the cascade; two further branches with opposite coefficients pad the absolute weight to
two (`CoherentLCU.paddedCoefficient`). Each branch keeps its own private register and public slots
(`BrSpace`), all of size `W`, and starts from the system state `E ψ` copied into uniform public
slots with a zero private register (`brInj`).

* `lcu_block`: the successful block of the LCU is `s ∑_{j=1}^n λ_j E† Ces_j E`, for any
  colligation with public space `W`;
* `lcuIn_isometry`, `lcuOut_isometry`: the preparations are isometries when
  `s ∑ |λ_j| ≤ 1`;
* `lcuSign_comp_lcuOut`: a known diagonal sign unitary maps the output preparation to the input
  preparation;
* `cascade_block`: for the cascade with public registers of size `W` (`wA`, `wB`, `wC`), the
  successful block is `s ∑_j λ_j Ces_j(F_m)`.
-/

set_option autoImplicit false

namespace SignedFactorSimulation

noncomputable section

open ContinuousLinearMap Finset OptimalPrecision SparseHamiltonian
  SparseHamiltonian.CoherentReuse SparseHamiltonian.ChronologicalResolvent
open scoped InnerProduct InnerProductSpace

/-! ### Branches -/

/-- The LCU branch labels: `n` reuse lengths and two padding labels. -/
abbrev Br (n : ℕ) := Fin n ⊕ Bool

/-- The number of reuses on each branch: `k + 1` on branch `k`, one on the padding branches. -/
def brLen (n : ℕ) : Br n → ℕ
  | .inl k => (k : ℕ) + 1
  | .inr _ => 1

theorem brLen_ne_zero (n : ℕ) (i : Br n) : brLen n i ≠ 0 := by
  cases i <;> simp [brLen]

theorem brLen_le {n : ℕ} (hn : 1 ≤ n) (i : Br n) : brLen n i ≤ n := by
  cases i with
  | inl k => simp only [brLen]; omega
  | inr _ => simpa [brLen] using hn

theorem sum_fin_succ_eq_Icc {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∑ k : Fin n, f ((k : ℕ) + 1) = ∑ j ∈ Icc 1 n, f j := by
  rw [Fin.sum_univ_eq_sum_range (fun k => f (k + 1)) n, ← Finset.Ico_add_one_right_eq_Icc,
    Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  exact Finset.sum_congr rfl fun k _ => by rw [add_comm]

variable {P W V : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

variable (W V) in
/-- The Hilbert space of one branch: the private register and `brLen n i` public slots. -/
abbrev BrSpace (n : ℕ) (i : Br n) := ReuseSchedule.Space (brLen n i) W V

/-- The input of a branch: `E ψ` in every public slot (uniformly), the private register zero. -/
def brInj (E : P →L[ℂ] W) (n : ℕ) (i : Br n) : P →L[ℂ] BrSpace W V n i :=
  initialEmbedding (brLen n i) ∘L E

theorem brInj_isometry {E : P →L[ℂ] W} (hE : E† ∘L E = 1) (n : ℕ) (i : Br n) :
    (brInj (V := V) E n i)† ∘L brInj E n i = 1 := by
  have h := initialEmbedding_adjoint_comp (P := W) (V := V) (brLen n i) (brLen_ne_zero n i)
  calc (brInj (V := V) E n i)† ∘L brInj E n i =
      E† ∘L ((initialEmbedding (P := W) (V := V) (brLen n i))† ∘L
        initialEmbedding (brLen n i)) ∘L E := by
        rw [brInj, adjoint_comp]; simp only [comp_assoc]
    _ = 1 := by rw [h, one_comp', hE]

/-- The signed LCU coefficients `2 s λ_j`, padded to absolute mass two. -/
def lcuCoeff (s : ℝ) (lam : ℕ → ℝ) (n : ℕ) : Br n → ℝ :=
  CoherentLCU.paddedCoefficient (fun k : Fin n => 2 * s * lam ((k : ℕ) + 1))

theorem lcuCoeff_mass {s : ℝ} (hs : 0 ≤ s) {lam : ℕ → ℝ} {n : ℕ}
    (h : s * ∑ j ∈ Icc 1 n, |lam j| ≤ 1) : ∑ i, |lcuCoeff s lam n i| = 2 := by
  apply CoherentLCU.padded_absolute_mass_two
  have h2 : ∀ k : Fin n, |2 * s * lam ((k : ℕ) + 1)| = 2 * s * |lam ((k : ℕ) + 1)| := by
    intro k
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * s)]
  simp only [h2]
  rw [← Finset.mul_sum, sum_fin_succ_eq_Icc (fun j => |lam j|) n]
  linarith

/-- The input preparation of the LCU. -/
def lcuIn (E : P →L[ℂ] W) (s : ℝ) (lam : ℕ → ℝ) (n : ℕ) : P →L[ℂ] PiLp 2 (BrSpace W V n) :=
  CoherentLCU.branchInput (lcuCoeff s lam n) (brInj E n)

/-- The output preparation of the LCU, carrying the signs of the coefficients. -/
def lcuOut (E : P →L[ℂ] W) (s : ℝ) (lam : ℕ → ℝ) (n : ℕ) : P →L[ℂ] PiLp 2 (BrSpace W V n) :=
  CoherentLCU.branchOutput (lcuCoeff s lam n) (brInj E n)

/-- SELECT: branch `i` runs `brLen n i` reuses of the colligation `(A, B, C, D)`. -/
def lcuSelect (A : W →L[ℂ] W) (B : V →L[ℂ] W) (C : W →L[ℂ] V) (D : V →L[ℂ] V) (n : ℕ) :
    PiLp 2 (BrSpace W V n) →L[ℂ] PiLp 2 (BrSpace W V n) :=
  WeightedClock.diagonal (fun i => fullReuse A B C D (brLen n i))

theorem lcuIn_isometry {E : P →L[ℂ] W} (hE : E† ∘L E = 1) {s : ℝ} (hs : 0 ≤ s) {lam : ℕ → ℝ}
    {n : ℕ} (h : s * ∑ j ∈ Icc 1 n, |lam j| ≤ 1) :
    (lcuIn (V := V) E s lam n)† ∘L lcuIn E s lam n = 1 :=
  CoherentLCU.branchInput_isometry _ (lcuCoeff_mass hs h) _ (brInj_isometry hE n)

theorem lcuOut_isometry {E : P →L[ℂ] W} (hE : E† ∘L E = 1) {s : ℝ} (hs : 0 ≤ s) {lam : ℕ → ℝ}
    {n : ℕ} (h : s * ∑ j ∈ Icc 1 n, |lam j| ≤ 1) :
    (lcuOut (V := V) E s lam n)† ∘L lcuOut E s lam n = 1 :=
  CoherentLCU.branchOutput_isometry _ (lcuCoeff_mass hs h) _ (brInj_isometry hE n)

/-- **The successful block of the LCU**: `s ∑_{j=1}^n λ_j E† Ces_j E`, where `Ces_j` is the
uniform clock of `j` reuses. -/
theorem lcu_block (E : P →L[ℂ] W) (A : W →L[ℂ] W) (B : V →L[ℂ] W) (C : W →L[ℂ] V)
    (D : V →L[ℂ] V) (s : ℝ) (lam : ℕ → ℝ) (n : ℕ) :
    (lcuOut (V := V) E s lam n)† ∘L lcuSelect A B C D n ∘L lcuIn E s lam n =
      (s : ℂ) • ∑ j ∈ Icc 1 n, (lam j : ℂ) • (E† ∘L successfulBlock A B C D j ∘L E) := by
  unfold lcuOut lcuSelect lcuIn
  rw [CoherentLCU.branch_successful_compression]
  have hbr : ∀ i : Br n, (brInj (V := V) E n i)† ∘L (fullReuse A B C D (brLen n i) ∘L
      brInj E n i) = E† ∘L successfulBlock A B C D (brLen n i) ∘L E := by
    intro i
    rw [← fullReuse_compression A B C D (brLen n i), brInj, adjoint_comp]
    simp only [comp_assoc]
  simp only [hbr]
  rw [Fintype.sum_sum_type, Fintype.sum_bool]
  simp only [lcuCoeff, CoherentLCU.paddedCoefficient, brLen, Complex.ofReal_neg, neg_smul,
    neg_add_cancel, add_zero]
  rw [← sum_fin_succ_eq_Icc (fun j => (lam j : ℂ) • (E† ∘L successfulBlock A B C D j ∘L E)) n,
    Finset.smul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_smul, smul_smul]
  congr 1
  push_cast
  ring

/-! ### Aligning the output with the input -/

/-- The known diagonal sign unitary of the coefficient signs. -/
def lcuSign (s : ℝ) (lam : ℕ → ℝ) (n : ℕ) :
    PiLp 2 (BrSpace W V n) →L[ℂ] PiLp 2 (BrSpace W V n) :=
  WeightedClock.diagonal (fun i => CoherentLCU.coefficientPhase (lcuCoeff s lam n i) •
    (1 : BrSpace W V n i →L[ℂ] BrSpace W V n i))

omit [CompleteSpace P] [CompleteSpace W] [CompleteSpace V] in
theorem lcuSign_comp_lcuOut (E : P →L[ℂ] W) (s : ℝ) (lam : ℕ → ℝ) (n : ℕ) :
    lcuSign s lam n ∘L lcuOut (V := V) E s lam n = lcuIn E s lam n := by
  unfold lcuSign lcuOut lcuIn CoherentLCU.branchOutput CoherentLCU.branchInput
  rw [WeightedClock.diagonal_boundary]
  congr 1
  funext i
  rw [smul_comp, comp_smul, smul_smul, CoherentLCU.coefficientPhase_sq, one_smul,
    one_comp']

theorem lcuSign_adjoint (s : ℝ) (lam : ℕ → ℝ) (n : ℕ) :
    (lcuSign (W := W) (V := V) s lam n)† = lcuSign s lam n := by
  unfold lcuSign
  rw [WeightedClock.diagonal_adjoint]
  congr 1
  funext i
  rw [map_smulₛₗ, CoherentLCU.coefficientPhase_conj, adjoint_one]

omit [CompleteSpace W] [CompleteSpace V] in
theorem lcuSign_mul_self (s : ℝ) (lam : ℕ → ℝ) (n : ℕ) :
    lcuSign (W := W) (V := V) s lam n ∘L lcuSign s lam n = 1 := by
  unfold lcuSign
  rw [WeightedClock.diagonal_comp]
  have h : ∀ i : Br n, (CoherentLCU.coefficientPhase (lcuCoeff s lam n i) •
      (1 : BrSpace W V n i →L[ℂ] BrSpace W V n i)) ∘L
      (CoherentLCU.coefficientPhase (lcuCoeff s lam n i) •
        (1 : BrSpace W V n i →L[ℂ] BrSpace W V n i)) = 1 := by
    intro i
    rw [smul_comp, comp_smul, smul_smul, CoherentLCU.coefficientPhase_sq, one_smul,
      one_comp']
  simp only [h]
  exact WeightedClock.diagonal_one

theorem lcuSign_unitary (s : ℝ) (lam : ℕ → ℝ) (n : ℕ) :
    OracleCircuit.IsUnitary (lcuSign (W := W) (V := V) s lam n) := by
  constructor
  · change (lcuSign (W := W) (V := V) s lam n)† ∘L lcuSign s lam n = 1
    rw [lcuSign_adjoint, lcuSign_mul_self]
  · change lcuSign (W := W) (V := V) s lam n ∘L (lcuSign s lam n)† = 1
    rw [lcuSign_adjoint, lcuSign_mul_self]

/-! ### The cascade with public registers of size `W` -/

/-- The public block of the cascade on `W`. -/
def wA (E : P →L[ℂ] W) (v : ℝ) (m : ℕ) : W →L[ℂ] W := extA E (cascA v m)

/-- The private-to-public block of the cascade on `W`. -/
def wB (Pr : W →L[ℂ] W) (E : P →L[ℂ] W) (v : ℝ) (m : ℕ) : BlockOperator.H m W →L[ℂ] W :=
  extB E (cascB Pr E v m)

/-- The public-to-private block of the cascade on `W`. -/
def wC (E : P →L[ℂ] W) (v : ℝ) (m : ℕ) : W →L[ℂ] BlockOperator.H m W := extC E (cascC E v m)

/-- **The successful block for the cascade**: `s ∑_{j=1}^n λ_j Ces_j(F_m)`. -/
theorem cascade_block {E : P →L[ℂ] W} (hE : E† ∘L E = 1) (Pr : W →L[ℂ] W) (v : ℝ) (m : ℕ)
    (s : ℝ) (lam : ℕ → ℝ) (n : ℕ) :
    (lcuOut E s lam n)† ∘L lcuSelect (wA E v m) (wB Pr E v m) (wC E v m) (cascD Pr E v m) n ∘L
        lcuIn E s lam n =
      (s : ℂ) • ∑ j ∈ Icc 1 n, (lam j : ℂ) • ces (cascTransfer Pr E v m) j := by
  rw [lcu_block]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [wA, wB, wC, successfulBlock_ext hE, successfulBlock_cascade]

end

end SignedFactorSimulation
