import OptimalPrecision.Taylor.Basic
import SparseHamiltonian.FullCoherentReuse
import Mathlib.Analysis.Normed.Algebra.Spectrum

/-!
# Causal transfers and the uniform clock

A colligation `(A, B, C, D)` with public space `P` and private space `V` has the causal transfer
`F(w) = A + w B (1 - wD)⁻¹ C`. Its Taylor coefficients are `[w⁰]F = A` and `[w^{k+1}]F = B D^k C`.
The uniform clock of the released `n`-slot reuse circuit (`CoherentReuse.successfulBlock`) is
exactly the Cesàro functional `Ces_n(F)` of `opt:eq:cesaro` (Appendix A: "This finite Cesàro
functional is exactly what a uniform public reuse clock selects").

* `coeff_inverse_one_sub_smul`: `[z^n] (1 - z a)⁻¹ = a^n` in a complete normed algebra;
* `transfer`, `coeff_transfer_zero`, `coeff_transfer_succ`: the transfer and its coefficients;
* `successfulBlock_eq_sum`, `successfulBlock_eq_ces`: the clock identity, with no
  catalyst (no inverse of `1 - D` is needed).
-/

set_option autoImplicit false

namespace SignedFactorSimulation

noncomputable section

open ContinuousLinearMap OptimalPrecision Finset
open SparseHamiltonian SparseHamiltonian.CoherentReuse SparseHamiltonian.ChronologicalResolvent
open scoped InnerProduct Nat

/-! ### Coefficients through continuous linear maps -/

section Linear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace F] in
/-- Taylor coefficients commute with a fixed continuous linear map. -/
theorem coeff_clm (L : E →L[ℂ] F) {g : ℂ → E} (hg : AnalyticAt ℂ g 0) (k : ℕ) :
    coeff (fun w => L (g w)) k = L (coeff g k) := by
  have h := L.iteratedFDeriv_comp_left (hg.contDiffAt (n := k)) (i := k) le_rfl
  have h' : iteratedDeriv k (fun w => L (g w)) 0 = L (iteratedDeriv k g 0) := by
    simp only [iteratedDeriv_eq_iteratedFDeriv]
    change iteratedFDeriv ℂ k (L ∘ g) 0 (fun _ => 1) = _
    rw [h]
    rfl
  simp only [coeff, h', map_smul]

omit [CompleteSpace F] in
theorem ces_clm (L : E →L[ℂ] F) {g : ℂ → E} (hg : AnalyticAt ℂ g 0) (j : ℕ) :
    ces (fun w => L (g w)) j = L (ces g j) := by
  simp only [ces, coeff_clm L hg, map_sum, map_smul]

/-- `[w^{k+1}] (w g(w)) = [w^k] g`. -/
theorem coeff_smul_X {g : ℂ → E} (hg : AnalyticAt ℂ g 0) (k : ℕ) :
    coeff (fun w => w • g w) (k + 1) = coeff g k := by
  rw [coeff_smul (f := fun w : ℂ => w) analyticAt_id hg, Finset.sum_eq_single 1]
  · have h1 : coeff (fun w : ℂ => w) 1 = 1 := by simpa using coeff_pow 1 1
    simp [h1]
  · intro i _ hi
    have : coeff (fun w : ℂ => w) i = 0 := by
      simpa [pow_one, hi] using coeff_pow 1 i
    rw [this, zero_smul]
  · intro h
    simp at h

omit [CompleteSpace E] in
theorem coeff_smul_X_zero (g : ℂ → E) : coeff (fun w => w • g w) 0 = 0 := by
  simp [coeff_zero_eq]

omit [CompleteSpace E] in
/-- The coefficients of a constant. -/
theorem coeff_const_vec (v : E) (k : ℕ) :
    coeff (fun _ : ℂ => v) k = if k = 0 then v else 0 := by
  rcases k with _ | k
  · simp [coeff_zero_eq]
  · simp [coeff, iteratedDeriv_const]

end Linear

/-! ### The geometric series in a Banach algebra -/

section Algebra

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

theorem analyticAt_inverse_one_sub_smul (a : A) :
    AnalyticAt ℂ (fun z : ℂ => Ring.inverse (1 - z • a)) 0 :=
  (spectrum.hasFPowerSeriesOnBall_inverse_one_sub_smul ℂ a).analyticAt

/-- `[z^n] (1 - z a)⁻¹ = a^n`. -/
theorem coeff_inverse_one_sub_smul (a : A) (n : ℕ) :
    coeff (fun z : ℂ => Ring.inverse (1 - z • a)) n = a ^ n := by
  have h := (spectrum.hasFPowerSeriesOnBall_inverse_one_sub_smul ℂ a).factorial_smul (1 : ℂ) n
  simp only [ContinuousMultilinearMap.mkPiRing_apply, Finset.prod_const_one, one_smul] at h
  have hd : iteratedDeriv n (fun z : ℂ => Ring.inverse (1 - z • a)) 0 = (n ! : ℂ) • a ^ n := by
    rw [iteratedDeriv_eq_iteratedFDeriv, ← h, Nat.cast_smul_eq_nsmul]
  have hn : (n ! : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
  simp only [coeff, hd, smul_smul, inv_mul_cancel₀ hn, one_smul]

end Algebra

/-! ### The causal transfer of a colligation -/

variable {P V : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- Right and left composition with fixed operators, `X ↦ B X C`. -/
def sandwich (B : V →L[ℂ] P) (C : P →L[ℂ] V) : (V →L[ℂ] V) →L[ℂ] (P →L[ℂ] P) :=
  (compL ℂ P V P B).comp ((compL ℂ P V V).flip C)

omit [CompleteSpace P] [CompleteSpace V] in
@[simp] theorem sandwich_apply (B : V →L[ℂ] P) (C : P →L[ℂ] V) (X : V →L[ℂ] V) :
    sandwich B C X = B ∘L X ∘L C := rfl

/-- The causal transfer `F(w) = A + w B (1 - wD)⁻¹ C` of the colligation `(A, B, C, D)`. -/
def transfer (A : P →L[ℂ] P) (B : V →L[ℂ] P) (C : P →L[ℂ] V) (D : V →L[ℂ] V) (w : ℂ) :
    P →L[ℂ] P :=
  A + w • (B ∘L Ring.inverse (1 - w • D) ∘L C)

omit [CompleteSpace P] in
theorem analyticAt_resolventPart (B : V →L[ℂ] P) (C : P →L[ℂ] V) (D : V →L[ℂ] V) :
    AnalyticAt ℂ (fun w : ℂ => B ∘L Ring.inverse (1 - w • D) ∘L C) 0 :=
  ((sandwich B C).analyticAt _).comp (analyticAt_inverse_one_sub_smul D)

omit [CompleteSpace P] in
theorem analyticAt_transfer (A : P →L[ℂ] P) (B : V →L[ℂ] P) (C : P →L[ℂ] V)
    (D : V →L[ℂ] V) : AnalyticAt ℂ (transfer A B C D) 0 :=
  analyticAt_const.add ((analyticAt_id : AnalyticAt ℂ (fun w : ℂ => w) 0).fun_smul
    (analyticAt_resolventPart B C D))

omit [CompleteSpace P] in
theorem coeff_resolventPart (B : V →L[ℂ] P) (C : P →L[ℂ] V) (D : V →L[ℂ] V) (k : ℕ) :
    coeff (fun w : ℂ => B ∘L Ring.inverse (1 - w • D) ∘L C) k = B ∘L (D ^ k) ∘L C := by
  have h := coeff_clm (sandwich B C) (analyticAt_inverse_one_sub_smul D) k
  simp only [sandwich_apply] at h
  rw [h, coeff_inverse_one_sub_smul]

omit [CompleteSpace P] [CompleteSpace V] in
@[simp] theorem coeff_transfer_zero (A : P →L[ℂ] P) (B : V →L[ℂ] P) (C : P →L[ℂ] V)
    (D : V →L[ℂ] V) : coeff (transfer A B C D) 0 = A := by
  simp [coeff_zero_eq, transfer]

theorem coeff_transfer_succ (A : P →L[ℂ] P) (B : V →L[ℂ] P) (C : P →L[ℂ] V)
    (D : V →L[ℂ] V) (k : ℕ) :
    coeff (transfer A B C D) (k + 1) = B ∘L (D ^ k) ∘L C := by
  have hR := analyticAt_resolventPart B C D
  have hS : AnalyticAt ℂ (fun w : ℂ => w • (B ∘L Ring.inverse (1 - w • D) ∘L C)) 0 :=
    (analyticAt_id : AnalyticAt ℂ (fun w : ℂ => w) 0).fun_smul hR
  have h := coeff_add (f := fun _ : ℂ => A)
    (g := fun w : ℂ => w • (B ∘L Ring.inverse (1 - w • D) ∘L C)) analyticAt_const hS (k + 1)
  change coeff (fun w => A + w • (B ∘L Ring.inverse (1 - w • D) ∘L C)) (k + 1) = _
  rw [h, coeff_smul_X hR, coeff_const_vec, if_neg (Nat.succ_ne_zero k), zero_add,
    coeff_resolventPart]

/-- The block coefficients `T₀ = A`, `T_{k+1} = B D^k C` of the transfer. -/
def transferCoeff (A : P →L[ℂ] P) (B : V →L[ℂ] P) (C : P →L[ℂ] V) (D : V →L[ℂ] V) :
    ℕ → P →L[ℂ] P
  | 0 => A
  | k + 1 => B ∘L (D ^ k) ∘L C

theorem coeff_transfer (A : P →L[ℂ] P) (B : V →L[ℂ] P) (C : P →L[ℂ] V) (D : V →L[ℂ] V)
    (k : ℕ) : coeff (transfer A B C D) k = transferCoeff A B C D k := by
  rcases k with _ | k
  · exact coeff_transfer_zero A B C D
  · exact coeff_transfer_succ A B C D k

/-! ### The uniform clock -/

/-- Exchanging the order of a triangular double sum. -/
theorem sum_range_sum_range_succ {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∑ r ∈ range n, ∑ m ∈ range (r + 1), f m = ∑ m ∈ range n, (n - m) • f m := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ (fun m => (n + 1 - m) • f m),
      show n + 1 - n = 1 by omega, one_smul, Finset.sum_range_succ f, ← add_assoc,
      ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun m hm => ?_
    have := Finset.mem_range.mp hm
    rw [show n + 1 - m = (n - m) + 1 by omega, add_smul, one_smul]

omit [CompleteSpace P] [CompleteSpace V] in
/-- The public output of slot `r` of the reuse circuit on the uniform clock state. -/
theorem publicReuse_uniform_slot (A : P →L[ℂ] P) (B : V →L[ℂ] P) (C : P →L[ℂ] V)
    (D : V →L[ℂ] V) (n : ℕ) (p : P) (r : Fin n) :
    publicReuse A B C D n (uniformEmbedding n p) r =
      (uniformAmplitude n : ℂ) • ∑ m ∈ range ((r : ℕ) + 1),
        transferCoeff A B C D m p := by
  change chronologicalOperator A B D C n
    (WithLp.toLp 2 (fun _ : Fin n => (uniformAmplitude n : ℂ) • p)) r = _
  rw [chronologicalOperator_apply A B D C (fun _ => (uniformAmplitude n : ℂ) • p) r,
    chronologicalPrivateState_eq_sum, Finset.sum_range_succ']
  have hrefl : ∑ k ∈ range (r : ℕ),
      (B ∘L ((D ^ ((r : ℕ) - 1 - k)) ∘L C)) ((uniformAmplitude n : ℂ) • p) =
      ∑ m ∈ range (r : ℕ), (B ∘L ((D ^ m) ∘L C)) ((uniformAmplitude n : ℂ) • p) :=
    Finset.sum_range_reflect (fun m => (B ∘L ((D ^ m) ∘L C)) ((uniformAmplitude n : ℂ) • p)) r
  rw [hrefl]
  simp only [transferCoeff, map_smul, smul_add, Finset.smul_sum]
  rw [add_comm]

omit [CompleteSpace V] in
/-- **The clock identity**: the uniform clock of the `n`-slot reuse circuit is
`∑_{m<n} (1 - m/n) T_m`. -/
theorem successfulBlock_eq_sum (A : P →L[ℂ] P) (B : V →L[ℂ] P) (C : P →L[ℂ] V)
    (D : V →L[ℂ] V) (n : ℕ) :
    successfulBlock A B C D n =
      ∑ m ∈ range n, ((1 : ℂ) - (m : ℂ) / (n : ℂ)) • transferCoeff A B C D m := by
  ext p
  simp only [successfulBlock, comp_apply, uniformEmbedding_adjoint_apply,
    publicReuse_uniform_slot, smul_smul, uniformAmplitude_complex_sq, _root_.sum_apply, smul_apply]
  rw [← Finset.smul_sum, Fin.sum_univ_eq_sum_range
    (fun r => ∑ m ∈ range (r + 1), transferCoeff A B C D m p) n,
    sum_range_sum_range_succ, Finset.smul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmn : m < n := Finset.mem_range.mp hm
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.zero_lt_of_lt hmn).ne'
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, Nat.cast_sub hmn.le]
  congr 1
  field_simp

/-- The uniform clock of the reuse circuit is the Cesàro functional of its transfer. -/
theorem successfulBlock_eq_ces (A : P →L[ℂ] P) (B : V →L[ℂ] P) (C : P →L[ℂ] V)
    (D : V →L[ℂ] V) (n : ℕ) :
    successfulBlock A B C D n = ces (transfer A B C D) n := by
  rw [successfulBlock_eq_sum, ces]
  simp only [coeff_transfer]

end

end SignedFactorSimulation
