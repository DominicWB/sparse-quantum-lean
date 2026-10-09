import ChebyshevFilter.Circuit
import SparseLinearSystems.Circuit.CounterFilter

set_option autoImplicit false

/-!
# The Chebyshev LCU circuit on a padded counter register

All runs of the algorithm share one physical workspace, with one counter register
`ℂ^{T+1} ⊗ V` (`CounterFilter.Ctr T V`). A filter of degree `d` with `2d ≤ T` uses it as
follows (register value `j` carries the power `j - d`, `powT`):

* the seed is `v ↦ ∑_j √p_{j-d} |j⟩ ⊗ v` (`seedT`, the released `WeightedClock.boundary`),
  where `p` are the Laurent coefficients of Proposition `qls:prop:chebyshev`
  (`ChebyshevFilter.filterCoeff`); register values `j > 2d` carry weight zero, and the seed is
  an isometry (`seedT_isometry`);
* signed step `l = 1, …, d` applies `W` on the branches with `j - d ≥ l`, `W†` on those with
  `j - d ≤ -l` and nothing on the others (`dirT`, `signedStepT`);
* after the `d` steps branch `j` carries `W^{clamp_d(j - d)}` (`signedStepsT_eq`), so the
  compression to the seed is exactly `F_{b,d}(W) = ∑_{|z| ≤ d} p_z W^z` (`lcuT_compression`).

This is the circuit of `ChebyshevFilter.lcu_compression` on a register padded with zero
weights; for `T = 2d` the seed and the signed steps are those of `ChebyshevFilter`
(`seedT_two_mul`, `signedStepsT_two_mul`).
-/

namespace ChebyshevLinearSystem

noncomputable section
open ContinuousLinearMap SparseHamiltonian SparseLinearSystems ChebyshevFilter CounterFilter
open scoped InnerProduct

/-! ### Powers carried by the register -/

/-- The power `j - d` carried by counter value `j` of a register with `T + 1` values. -/
def powT {T : ℕ} (d : ℕ) (j : Fin (T + 1)) : ℤ := (j : ℤ) - d

/-- The direction of signed step `l` on a branch with target power `z`: `W` (`some true`) if
`z ≥ l`, `W†` (`some false`) if `z ≤ -l`, inactive (`none`) otherwise. -/
def dirOfPow (l : ℕ) (z : ℤ) : Option Bool :=
  if (l : ℤ) ≤ z then some true else if z ≤ -(l : ℤ) then some false else none

/-- The direction register of signed step `l` of the degree-`d` filter. -/
def dirT (T d l : ℕ) (j : Fin (T + 1)) : Option Bool := dirOfPow l (powT d j)

/-- Register sums are sums over the powers `-d, …, T - d`. -/
theorem sum_powT {M : Type*} [AddCommMonoid M] (f : ℤ → M) (T d : ℕ) :
    ∑ j : Fin (T + 1), f (powT d j) = ∑ z ∈ Finset.Icc (-(d : ℤ)) ((T : ℤ) - d), f z := by
  apply Finset.sum_bij (fun j _ => powT d j)
  · intro j _
    have := j.isLt
    rw [Finset.mem_Icc, powT]
    omega
  · intro a _ c _ h
    rw [powT, powT] at h
    exact Fin.ext (by omega)
  · intro z hz
    rw [Finset.mem_Icc] at hz
    refine ⟨⟨(z + d).toNat, by omega⟩, Finset.mem_univ _, ?_⟩
    rw [powT]
    simp only
    omega
  · intro j _
    rfl

/-- For `2d ≤ T`, a function supported on `[-d, d]` has the same sum over the register. -/
theorem sum_powT_of_support {M : Type*} [AddCommMonoid M] (f : ℤ → M) (T d : ℕ)
    (hT : 2 * d ≤ T) (hf : ∀ z, z ∉ Finset.Icc (-(d : ℤ)) d → f z = 0) :
    ∑ j : Fin (T + 1), f (powT d j) = ∑ z ∈ Finset.Icc (-(d : ℤ)) d, f z := by
  rw [sum_powT]
  symm
  apply Finset.sum_subset
  · intro z hz
    rw [Finset.mem_Icc] at hz ⊢
    omega
  · intro z _ hz
    exact hf z hz

/-- The Laurent coefficients sum to one over a register with `2d ≤ T`. -/
theorem sum_filterCoeff_powT {b : ℝ} (hb : b ∈ Set.Ioo (-1 : ℝ) 1) {T d : ℕ}
    (hT : 2 * d ≤ T) : ∑ j : Fin (T + 1), filterCoeff b d (powT d j) = 1 := by
  rw [sum_powT_of_support _ T d hT (fun z hz => filterCoeff_eq_zero hb hz), sum_filterCoeff hb]

/-! ### Signed steps -/

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- Signed step `l` of the degree-`d` filter on the register `ℂ^{T+1} ⊗ V`. -/
def signedStepT (W : V →L[ℂ] V) (T d l : ℕ) : Ctr T V →L[ℂ] Ctr T V :=
  WeightedClock.diagonal (fun j => dirOp W (dirT T d l j))

/-- Signed steps `1, …, l`, the first applied first. -/
def signedStepsT (W : V →L[ℂ] V) (T d : ℕ) : ℕ → (Ctr T V →L[ℂ] Ctr T V)
  | 0 => 1
  | l + 1 => signedStepT W T d (l + 1) * signedStepsT W T d l

/-- One more signed step on a branch with target power `z`. -/
theorem dirOp_comp_wpow_pow (W : V →L[ℂ] V) (l : ℕ) (z : ℤ) :
    (dirOp W (dirOfPow (l + 1) z)).comp (wpow W (clampPow l z)) =
      wpow W (clampPow (l + 1) z) := by
  rw [dirOfPow]
  by_cases h1 : ((l + 1 : ℕ) : ℤ) ≤ z
  · have e1 : clampPow l z = (l : ℤ) := by rw [clampPow]; omega
    have e2 : clampPow (l + 1) z = ((l + 1 : ℕ) : ℤ) := by rw [clampPow]; omega
    rw [if_pos h1, e1, e2, dirOp, wpow_natCast, wpow_natCast, pow_succ']
    rfl
  · rw [if_neg h1]
    by_cases h2 : z ≤ -((l + 1 : ℕ) : ℤ)
    · have e1 : clampPow l z = -(l : ℤ) := by rw [clampPow]; omega
      have e2 : clampPow (l + 1) z = -((l + 1 : ℕ) : ℤ) := by rw [clampPow]; omega
      rw [if_pos h2, e1, e2, dirOp, wpow_neg_natCast, wpow_neg_natCast, pow_succ']
      rfl
    · have e : clampPow (l + 1) z = clampPow l z := by rw [clampPow, clampPow]; omega
      rw [if_neg h2, e, dirOp]
      exact ContinuousLinearMap.id_comp _

/-- **After `l` signed steps** branch `j` carries `W^{clamp_l(j - d)}`. -/
theorem signedStepsT_eq (W : V →L[ℂ] V) (T d l : ℕ) :
    signedStepsT W T d l =
      WeightedClock.diagonal (fun j : Fin (T + 1) => wpow W (clampPow l (powT d j))) := by
  induction l with
  | zero =>
    have h : ∀ j : Fin (T + 1), wpow W (clampPow 0 (powT d j)) = 1 := by
      intro j
      rw [show clampPow 0 (powT d j) = 0 by rw [clampPow]; omega, wpow_zero']
    simp only [signedStepsT, h]
    exact WeightedClock.diagonal_one.symm
  | succ l ih =>
    rw [signedStepsT, ih, signedStepT, mul_def, WeightedClock.diagonal_comp]
    congr 1
    funext j
    exact dirOp_comp_wpow_pow W l (powT d j)

/-! ### The seed and the compression -/

/-- **The seed** `v ↦ ∑_j √p_{j-d} |j⟩ ⊗ v` of the degree-`d` filter with parameter `b`. -/
def seedT (b : ℝ) (T d : ℕ) : V →L[ℂ] Ctr T V :=
  WeightedClock.boundary (fun j : Fin (T + 1) => filterCoeff b d (powT d j)) (fun _ => 1)

/-- **Normalisation one**: the seed is an isometry. -/
theorem seedT_isometry {b : ℝ} (hb : b ∈ Set.Ioo (-1 : ℝ) 1) {T d : ℕ} (hT : 2 * d ≤ T) :
    ((seedT (V := V) b T d)†) ∘L seedT b T d = 1 := by
  have hJ : ∀ _ : Fin (T + 1), ((1 : V →L[ℂ] V)†).comp (1 : V →L[ℂ] V) = 1 :=
    fun _ => by rw [adjoint_one_eq]; rfl
  exact WeightedClock.boundary_isometry _ (fun j => filterCoeff_nonneg hb d _)
    (sum_filterCoeff_powT hb hT) _ hJ

/-- **The LCU circuit on the padded register**: the `d` signed steps, compressed to the
seed, give exactly `F_{b,d}(W)`. -/
theorem lcuT_compression (W : V →L[ℂ] V) {b : ℝ} (hb : b ∈ Set.Ioo (-1 : ℝ) 1) {T d : ℕ}
    (hT : 2 * d ≤ T) :
    ((seedT (V := V) b T d)†) ∘L (signedStepsT W T d d ∘L seedT b T d) = filterOp W b d := by
  have hsupp : ∀ z, z ∉ Finset.Icc (-(d : ℤ)) d →
      ((filterCoeff b d z : ℝ) : ℂ) • wpow W z = 0 := by
    intro z hz
    rw [filterCoeff_eq_zero hb hz, Complex.ofReal_zero, zero_smul]
  rw [seedT, signedStepsT_eq, WeightedClock.boundary_compression _
    (fun j => filterCoeff_nonneg hb d _), filterOp,
    ← sum_powT_of_support (fun z => ((filterCoeff b d z : ℝ) : ℂ) • wpow W z) T d hT hsupp]
  apply Finset.sum_congr rfl
  intro j _
  rw [adjoint_one_eq]
  by_cases hj : powT d j ∈ Finset.Icc (-(d : ℤ)) d
  · rw [Finset.mem_Icc] at hj
    rw [show clampPow d (powT d j) = powT d j by rw [clampPow]; omega]
    rfl
  · rw [filterCoeff_eq_zero hb hj, Complex.ofReal_zero, zero_smul, zero_smul]

omit [CompleteSpace V] in
/-- For `T = 2d` the seed is the seed of `ChebyshevFilter`. -/
theorem seedT_two_mul (b : ℝ) (d : ℕ) : seedT (V := V) b (2 * d) d = seed b d := rfl

/-- For `T = 2d` the signed steps are those of `ChebyshevFilter`. -/
theorem signedStepsT_two_mul (W : V →L[ℂ] V) (d l : ℕ) :
    signedStepsT W (2 * d) d l = signedSteps W d l := by
  induction l with
  | zero => rfl
  | succ l ih => rw [signedStepsT, signedSteps, ih]; rfl

/-- After the `d` signed steps, the compression of any vector of the seed. -/
theorem lcuT_apply (W : V →L[ℂ] V) {b : ℝ} (hb : b ∈ Set.Ioo (-1 : ℝ) 1) {T d : ℕ}
    (hT : 2 * d ≤ T) (v : V) :
    ((seedT (V := V) b T d)†) (signedStepsT W T d d (seedT b T d v)) = filterOp W b d v := by
  have h := congrArg (fun A : V →L[ℂ] V => A v) (lcuT_compression W hb hT)
  simpa only [comp_apply] using h

end

end ChebyshevLinearSystem
