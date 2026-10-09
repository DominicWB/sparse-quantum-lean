import SparseLinearSystems.WalkGap
import SparseLinearSystems.Spectral.UnitaryFilter
import SparseHamiltonian.MaskedProgram
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# The averaging filter as a counter-controlled walk sequence

`f_N(W)^k = (N⁻¹ Σ_{i<N} W^i)^k = Σ_j c_j W^j` is a polynomial in `W` with
nonnegative coefficients summing to one (`coef_nonneg`, `sum_coef`) and degree
at most `k (N - 1)`.  It is implemented with one counter register of size
`T + 1 ≥ k (N - 1) + 1`:

* the seed is `ψ ⊗ v`, `ψ_j = √c_j` (`WeightedClock.boundary`);
* step `t = 1, …, T` applies `W` on the counter values `j ≥ t`
  (`MaskedProgram.masked (stepMask T t) W`), so all steps together act as
  `W^j` on counter value `j` (`steps_eq`);
* projecting the counter back onto `ψ` gives exactly `f_N(W)^k`
  (`counter_compression`).

No counter preparation unitary is needed: the seed and the success projector
are fixed public data.  Only the walk itself is ever queried, `T` times.
-/

namespace SparseLinearSystems.CounterFilter

noncomputable section
open ContinuousLinearMap Polynomial SparseHamiltonian
open scoped InnerProduct

/-! ### The filter polynomial -/

/-- `q_N = N⁻¹ Σ_{i<N} X^i` over the reals. -/
def avgPoly (N : ℕ) : ℝ[X] := C ((N : ℝ)⁻¹) * ∑ i ∈ Finset.range N, X ^ i

/-- The same polynomial over `ℂ`. -/
def avgPolyC (N : ℕ) : ℂ[X] := C ((N : ℂ)⁻¹) * ∑ i ∈ Finset.range N, X ^ i

theorem avgPolyC_eq_map (N : ℕ) : avgPolyC N = (avgPoly N).map (algebraMap ℝ ℂ) := by
  simp [avgPolyC, avgPoly, Polynomial.map_mul, Polynomial.map_sum, Polynomial.map_pow]

/-- The coefficient `c_j` of `q_N^k`. -/
def coef (N k j : ℕ) : ℝ := (avgPoly N ^ k).coeff j

theorem avgPoly_coeff_nonneg (N j : ℕ) : 0 ≤ (avgPoly N).coeff j := by
  rw [avgPoly, coeff_C_mul, finsetSum_coeff]
  apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N))
  apply Finset.sum_nonneg
  intro i _
  rw [coeff_X_pow]
  split_ifs <;> norm_num

theorem coeff_mul_nonneg {p q : ℝ[X]} (hp : ∀ j, 0 ≤ p.coeff j) (hq : ∀ j, 0 ≤ q.coeff j)
    (j : ℕ) : 0 ≤ (p * q).coeff j := by
  rw [coeff_mul]
  exact Finset.sum_nonneg fun x _ => mul_nonneg (hp _) (hq _)

theorem coef_nonneg (N k j : ℕ) : 0 ≤ coef N k j := by
  unfold coef
  induction k generalizing j with
  | zero =>
    rw [pow_zero, coeff_one]
    split_ifs <;> norm_num
  | succ k ih =>
    rw [pow_succ]
    exact coeff_mul_nonneg ih (avgPoly_coeff_nonneg N) j

theorem avgPoly_natDegree_le (N : ℕ) : (avgPoly N).natDegree ≤ N - 1 := by
  unfold avgPoly
  refine (natDegree_C_mul_le _ _).trans ?_
  apply natDegree_sum_le_of_forall_le
  intro i hi
  refine (natDegree_X_pow_le i).trans ?_
  have := Finset.mem_range.mp hi
  omega

theorem filterPoly_natDegree_le (N k : ℕ) : (avgPoly N ^ k).natDegree ≤ k * (N - 1) :=
  natDegree_pow_le.trans (Nat.mul_le_mul_left k (avgPoly_natDegree_le N))

theorem coef_eq_zero (N k j : ℕ) (hj : k * (N - 1) < j) : coef N k j = 0 := by
  unfold coef
  apply coeff_eq_zero_of_natDegree_lt
  exact lt_of_le_of_lt (filterPoly_natDegree_le N k) hj

theorem avgPoly_eval_one (N : ℕ) (hN : 0 < N) : (avgPoly N).eval 1 = 1 := by
  simp only [avgPoly, eval_mul, eval_C, eval_finsetSum, eval_pow, eval_X, one_pow,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  exact inv_mul_cancel₀ (by exact_mod_cast hN.ne')

/-- The coefficients sum to one over any range covering the degree. -/
theorem sum_coef (N k T : ℕ) (hN : 0 < N) (hT : k * (N - 1) ≤ T) :
    ∑ j ∈ Finset.range (T + 1), coef N k j = 1 := by
  have h := eval_eq_sum_range' (p := avgPoly N ^ k) (n := T + 1)
    (lt_of_le_of_lt (filterPoly_natDegree_le N k) (Nat.lt_succ_of_le hT)) 1
  simp only [one_pow, mul_one] at h
  rw [eval_pow, avgPoly_eval_one N hN, one_pow] at h
  exact h.symm

theorem sum_coef_fin (N k T : ℕ) (hN : 0 < N) (hT : k * (N - 1) ≤ T) :
    ∑ j : Fin (T + 1), coef N k j.val = 1 := by
  rw [Fin.sum_univ_eq_sum_range (fun j => coef N k j), sum_coef N k T hN hT]

/-! ### Operator evaluation -/

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

omit [CompleteSpace V] in
theorem aeval_avgPolyC (W : V →L[ℂ] V) (N : ℕ) :
    aeval W (avgPolyC N) = UnitaryFilter.avg W N := by
  simp only [avgPolyC, map_mul, aeval_C, map_sum, map_pow, aeval_X, UnitaryFilter.avg,
    Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]

omit [CompleteSpace V] in
/-- `Σ_j c_j W^j = f_N(W)^k` when the range covers the degree. -/
theorem sum_coef_pow (W : V →L[ℂ] V) (N k T : ℕ) (hT : k * (N - 1) ≤ T) :
    ∑ j : Fin (T + 1), ((coef N k j.val : ℝ) : ℂ) • W ^ j.val =
      UnitaryFilter.filter W N k := by
  rw [Fin.sum_univ_eq_sum_range (fun j => ((coef N k j : ℝ) : ℂ) • W ^ j)]
  have hdeg : (avgPolyC N ^ k).natDegree < T + 1 := by
    rw [avgPolyC_eq_map, ← Polynomial.map_pow]
    exact lt_of_le_of_lt (natDegree_map_le.trans (filterPoly_natDegree_le N k))
      (Nat.lt_succ_of_le hT)
  have h := aeval_eq_sum_range' hdeg W
  rw [map_pow, aeval_avgPolyC] at h
  rw [UnitaryFilter.filter, h]
  apply Finset.sum_congr rfl
  intro j _
  rw [avgPolyC_eq_map, ← Polynomial.map_pow, coeff_map]
  rfl

/-! ### The counter register -/

/-- The counter register `ℂ^{T+1} ⊗ V`. -/
abbrev Ctr (T : ℕ) (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℂ V] :=
  PiLp 2 (fun _ : Fin (T + 1) => V)

/-- Step `t` is active on counter values `j ≥ t`. -/
def stepMask (T t : ℕ) : Fin (T + 1) → Bool := fun j => decide (t ≤ j.val)

/-- Steps `1, …, t`, the first applied first. -/
def steps (T : ℕ) (W : V →L[ℂ] V) : ℕ → (Ctr T V →L[ℂ] Ctr T V)
  | 0 => 1
  | t + 1 => MaskedProgram.masked (stepMask T (t + 1)) W * steps T W t

omit [CompleteSpace V] in
/-- All steps act as `W^{min(j, t)}` on counter value `j`. -/
theorem steps_eq (T : ℕ) (W : V →L[ℂ] V) (t : ℕ) :
    steps T W t = WeightedClock.diagonal (fun j : Fin (T + 1) => W ^ (min j.val t)) := by
  induction t with
  | zero =>
    simp only [steps, Nat.min_zero, pow_zero]
    exact WeightedClock.diagonal_one.symm
  | succ t ih =>
    rw [steps, ih, MaskedProgram.masked, mul_def, WeightedClock.diagonal_comp]
    congr 1
    funext j
    by_cases hj : t + 1 ≤ j.val
    · have h1 : min j.val (t + 1) = min j.val t + 1 := by omega
      simp only [stepMask, hj, decide_true, if_true, h1, pow_succ']
      rfl
    · have h1 : min j.val (t + 1) = min j.val t := by omega
      simp only [stepMask, hj, decide_false, Bool.false_eq_true, if_false, h1]
      ext v
      simp

/-- The counter seed `ψ ⊗ v` with `ψ_j = √c_j`. -/
def seedMap (N k T : ℕ) : V →L[ℂ] Ctr T V :=
  WeightedClock.boundary (fun j : Fin (T + 1) => coef N k j.val) (fun _ => 1)

theorem seedMap_isometry (N k T : ℕ) (hN : 0 < N) (hT : k * (N - 1) ≤ T) :
    ((seedMap (V := V) N k T)†) ∘L seedMap N k T = 1 := by
  have hJ : ∀ _ : Fin (T + 1), ((1 : V →L[ℂ] V).adjoint).comp (1 : V →L[ℂ] V) = 1 :=
    fun _ => by rw [WalkGap.adjoint_one']; rfl
  unfold seedMap
  exact WeightedClock.boundary_isometry (fun j : Fin (T + 1) => coef N k j.val)
    (fun j => coef_nonneg N k j.val) (sum_coef_fin N k T hN hT) _ hJ

/-- **Counter compression.**  The `T` masked steps, compressed to the counter
state `ψ`, give exactly the filter `f_N(W)^k`. -/
theorem counter_compression (W : V →L[ℂ] V) (N k T : ℕ) (hT : k * (N - 1) ≤ T) :
    ((seedMap (V := V) N k T)†) ∘L (steps T W T ∘L seedMap N k T) =
      UnitaryFilter.filter W N k := by
  rw [seedMap, steps_eq, WeightedClock.boundary_compression (fun j : Fin (T + 1) => coef N k j.val)
    (fun j => coef_nonneg N k j.val),
    ← sum_coef_pow W N k T hT]
  apply Finset.sum_congr rfl
  intro j _
  rw [min_eq_left (Nat.lt_succ_iff.mp j.isLt), WalkGap.adjoint_one']
  ext v
  simp

/-- **Counter compression with a padded register.**  Running only the first
`t ≥ k (N - 1)` steps on a register of `T + 1 ≥ t + 1` counter values also gives
exactly `f_N(W)^k`: counter values beyond the degree carry zero weight. -/
theorem counter_compression_le (W : V →L[ℂ] V) (N k T t : ℕ) (ht : k * (N - 1) ≤ t)
    (htT : t ≤ T) :
    ((seedMap (V := V) N k T)†) ∘L (steps T W t ∘L seedMap N k T) =
      UnitaryFilter.filter W N k := by
  rw [seedMap, steps_eq, WeightedClock.boundary_compression (fun j : Fin (T + 1) => coef N k j.val)
    (fun j => coef_nonneg N k j.val),
    ← sum_coef_pow W N k T (ht.trans htT)]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j.val ≤ t
  · rw [min_eq_left hj, WalkGap.adjoint_one']
    ext v
    simp
  · rw [coef_eq_zero N k j.val (by omega)]
    ext v
    simp

end

end SparseLinearSystems.CounterFilter
